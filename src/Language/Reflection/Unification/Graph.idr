module Language.Reflection.Unification.Graph

import public Language.Reflection.Unification.Engine

record DependencyGraph where
  constructor MkDG
  dependsOn : SortedMap Nat $ SortedMap Nat $ SortedSet Name
  dependedBy : SortedMap Nat $ SortedMap Nat $ SortedSet Name

Show DependencyGraph where
  show (MkDG dO dB) = "MkDG \{show dO} \{show dB}"

emptyDG : DependencyGraph
emptyDG = MkDG empty empty

addDep : Nat -> Nat -> Name -> DependencyGraph -> DependencyGraph
addDep a b name =
    { dependsOn $= update (addIfExists' b) a
    , dependedBy $= update (addIfExists' a) b
    }
  where
  addIfExists : Name -> Maybe (SortedSet Name) -> Maybe (SortedSet Name)
  addIfExists n = Just . insert n . fromMaybe empty

  addIfExists' :
       Nat ->
       Maybe (SortedMap Nat (SortedSet Name)) ->
       Maybe (SortedMap Nat (SortedSet Name))
  addIfExists' n = Just . update (addIfExists name) n . fromMaybe empty

delDep : Nat -> Nat -> DependencyGraph -> DependencyGraph
delDep a b =
  { dependsOn $= update (map (delete b)) a
  , dependedBy $= update (map (delete a)) b
  }

-- delDepN : Nat -> Nat -> Name -> DependencyGraph -> DependencyGraph
-- delDepN = ?delDepN_rhs

detectCycle1 : Nat -> SortedSet Nat -> DependencyGraph -> Bool
detectCycle1 idx prev dg =
  if contains idx prev
    then True
    else fromMaybe False $ searchChildBuckets . keys <$> lookup idx dg.dependsOn
  where
  searchChildBuckets : List Nat -> Bool
  searchChildBuckets [] = False
  searchChildBuckets (child::rest) =
    if detectCycle1 child (insert idx prev) dg
      then True
      else searchChildBuckets rest

detectCycleDumb : List Nat -> DependencyGraph -> Bool
detectCycleDumb [] dg = False
detectCycleDumb (x :: xs) dg =
  if detectCycle1 x empty dg then True else detectCycleDumb xs dg

parameters {auto task : UnificationTask}
  getDepGraph : UnificationState -> DependencyGraph
  getDepGraph state = foldl addBucketDependencies emptyDG $ kvList state.buckets
    where
    addByName :
      SortedSet (Nat, Name) -> Tag Name -> SortedSet (Nat, Name)
    addByName s n with (state.nameToBucket `lookup'` n)
      addByName s n | (Just id) = insert (id, n.data) s
      addByName s n | Nothing = s

    getBucketDependencies : BucketData -> SortedSet (Nat, Name)
    getBucketDependencies bd with (bd.expr)
      getBucketDependencies bd | (Nothing) = empty
      getBucketDependencies bd | (Just expr) = do
        let dep_vars = expr.dependencies
        foldl addByName empty (map expr.same (Prelude.toList dep_vars))

    addBucketDependencies :
      DependencyGraph -> (Nat, BucketData) -> DependencyGraph
    addBucketDependencies dg (bId, bucket) =
      foldr (\(x,y)=> addDep bId x y) dg $ getBucketDependencies bucket

  dumpUStateG : UnificationState -> String
  dumpUStateG s = dumpUState s ++ "\n" ++ show (getDepGraph s)

  getContent : Nat -> UnificationState -> Maybe TTImp
  getContent id state = do
    bd <- lookup id state.buckets
    expr <- bd.expr
    Just expr.data

  subDep :
       Nat
    -> Nat
    -> UnificationState
    -> DependencyGraph
    -> (UnificationState, DependencyGraph)
  subDep a b state dg with (getContent a state)
    subDep a b state dg | Nothing = (state, dg)
    subDep a b state dg | (Just expr) = do
      let newState : UnificationState =
        {buckets $= updateExisting updateBucket b} state
      let newGraph = delDep b a dg
      (newState, newGraph)
      where
        subName' : Name -> BucketData -> BucketData
        subName' n = {expr $= map $ map $ substituteVariable n expr}

        updateBucket : BucketData -> BucketData
        updateBucket bd =
          Prelude.foldr subName' bd
            $ fromMaybe empty
              $ lookup a
                =<< lookup b dg.dependsOn

  subLeaf :
       Nat
    -> UnificationState
    -> DependencyGraph
    -> (UnificationState, DependencyGraph)
  subLeaf l state dg with (lookup l dg.dependedBy)
    subLeaf l state dg | Nothing = (state, dg)
    subLeaf l state dg | (Just ds) = foldl subOneDep (state, dg) $ keys ds
      where
      subOneDep :
           (UnificationState, DependencyGraph)
        -> Nat
        -> (UnificationState, DependencyGraph)
      subOneDep (s, g) n = subDep l n s g

  subLeaves :
       List Nat
    -> UnificationState
    -> DependencyGraph
    -> (UnificationState, DependencyGraph)
  subLeaves leaves st dg = foldl subOneLeaf (st, dg) leaves
    where
    subOneLeaf :
         (UnificationState, DependencyGraph)
      -> Nat
      -> (UnificationState, DependencyGraph)
    subOneLeaf (s,g) l = subLeaf l s g

isLeaf : Nat -> DependencyGraph -> Bool
isLeaf n dg = isDependedOn && hasNoChildren
  where
  isDependedOn : Bool
  isDependedOn = fromMaybe False $ (/= empty) <$> lookup n dg.dependedBy

  hasNoChildren : Bool
  hasNoChildren = fromMaybe True $ (== empty) <$> lookup n dg.dependsOn

findLeaves : List Nat -> DependencyGraph -> List Nat
findLeaves nodes dg = filter (flip isLeaf dg) nodes

parameters {auto task: UnificationTask}
  fillIn :
       UnificationState
    -> DependencyGraph
    -> (UnificationState, DependencyGraph)
  fillIn state dg = do
    let leaves = findLeaves (keys state.buckets) dg
    case leaves of
      [] => (state, dg)
      leaves => do
        let (nState, nDg) = subLeaves leaves state dg
        fillIn nState nDg

  fillInOnce :
       UnificationState
    -> DependencyGraph
    -> (UnificationState, DependencyGraph)
  fillInOnce state dg = do
    let leaves = findLeaves (keys state.buckets) dg
    case leaves of
      [] => (state, dg)
      leaves => do
        subLeaves leaves state dg

  public export
  consolidateUState :
    UnificationState -> (SortedMap Name TTImp, SortedMap Name TTImp)
  consolidateUState ustate = do
    let dg = getDepGraph ustate
    let (ns, ndg) = fillIn ustate dg
    let lhs_r = foldl (searchNameByOrigin ns Left) empty (keys task.lhsVars)
    let rhs_r = foldl (searchNameByOrigin ns Right) empty (keys task.rhsVars)
    (lhs_r, rhs_r)
    where
      searchNameByOrigin :
           UnificationState
        -> Origin
        -> SortedMap Name TTImp -> Name -> SortedMap Name TTImp
      searchNameByOrigin ust o sm n = fromMaybe sm found
        where
        found : Maybe $ SortedMap Name TTImp
        found = do
          bid <- lookup (MkTag o empty n) ust.nameToBucket
          bd <- lookup bid ust.buckets
          expr <- bd.expr
          Just $ insert n expr.data sm

