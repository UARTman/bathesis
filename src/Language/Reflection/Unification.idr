module Language.Reflection.Unification

import public Language.Reflection
import public Language.Reflection.Syntax
import public Language.Reflection.Types
import public Language.Reflection.Pretty
import public Language.Reflection.Util
import public Language.Reflection.Types
import public Language.Reflection.TT
import public Language.Reflection.TTImp
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops
import public Language.Reflection.VarSubst
import public Data.SortedSet
import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.String

import public Derive.Prelude
import public Deriving.Show
import public Text.PrettyPrint.Bernardy.Core
import public Language.Reflection.Pretty
import public Text.PrettyPrint.Bernardy.Interface

import public PrimIO

%language ElabReflection
-- %auto_lazy off

-- %default total

(.toList) : SortedSet t -> List t
(.toList) = Prelude.toList

||| The top-level unification operation context
public export
record UnificationContext where
  constructor MkUC
  ||| Free variables in left-hand-side expression
  lhsVars : SortedSet Name
  ||| Left-hand-side expression
  lhs : TTImp
  ||| Free variables in right-hand-side expression
  rhsVars : SortedSet Name
  ||| Left-hand-side expression
  rhs : TTImp

%runElab derive "UnificationContext" [Show, Eq]

||| Origin of data (left- or right-hand side)
public export
data Origin = Left | Right

Eq Origin where
  (==) Left Left = True
  (==) Right Right = True
  (==) _ _ = False

%runElab derive "Origin" [Show, Eq]

parameters {auto uc: UnificationContext}
  ||| Metadata container for keeping track of the data's origin
  public export
  data WithOrigin : (t : Type) -> Type where
    MkOriginData: Origin -> t -> WithOrigin t

  Eq t => Eq (WithOrigin t) where
    (==) (MkOriginData o t) (MkOriginData o' t') = o == o' && t == t'

  Show t => Show (WithOrigin t) where
    show (MkOriginData Left t) = "withLeft \{show t}"
    show (MkOriginData Right t) = "withRight \{show t}"

  Ord t => Ord (WithOrigin t) where
    compare (MkOriginData Left x) (MkOriginData Left y) = compare x y
    compare (MkOriginData Left y) (MkOriginData Right w) = LT
    compare (MkOriginData Right y) (MkOriginData Left w) = GT
    compare (MkOriginData Right x) (MkOriginData Right y) = compare x y

  -- Shorthand constructors
  ||| Construct LHS data
  public export
  withLeft : t -> WithOrigin t
  withLeft x = MkOriginData Left x

  ||| Construct RHS data
  public export
  withRight : t -> WithOrigin t
  withRight x = MkOriginData Right x

  -- Mapping functions
  ||| Construct data of same origin
  public export
  (.same) : WithOrigin t -> g -> WithOrigin g
  (.same) (MkOriginData d _) y = MkOriginData d y

  ||| Map
  mapInner : (t->u) -> WithOrigin t -> WithOrigin u
  mapInner f (MkOriginData x y) = MkOriginData x $ f y

  -- Extractors
  ||| Access underlying data
  public export
  (.data) : WithOrigin t -> t
  (.data) (MkOriginData _ x) = x

  ||| Access origin
  public export
  (.origin) : WithOrigin t -> Origin
  (.origin) (MkOriginData x _) = x

  -- Free variables
  ||| Access free variables, available from the context
  public export
  (.freeVars) : WithOrigin t -> SortedSet Name
  (.freeVars) (MkOriginData Left _) = uc.lhsVars
  (.freeVars) (MkOriginData Right _) = uc.rhsVars

  ||| Check if a name with origin metadata refers to a free variable
  public export
  (.isFreeVar) : WithOrigin Name -> Bool
  (.isFreeVar) dt = dt.freeVars `contains'` dt.data

  ||| Check if an expression with origin metadata is a free variable invocation
  public export
  (.isFreeVar') : WithOrigin TTImp -> Bool
  (.isFreeVar') dt@(MkOriginData _ (IVar _ y)) = dt.freeVars `contains'` y
  (.isFreeVar') _ = False

  ||| List all the free variables an origin-tagged expression depends on
  public export
  dependencies : WithOrigin TTImp -> SortedSet Name
  dependencies dt =
    fromList .
    filter (\n => containsVariable n dt.data) .
    Prelude.toList .
    (.freeVars) $
    dt

  ||| List all the free variables an origin-tagged expression depends on
  public export
  (.dependencies) : WithOrigin TTImp -> SortedSet Name
  (.dependencies) = dependencies

||| Infomration on a set of equivalent free variables
public export
record BucketData {auto uc: UnificationContext} where
  constructor MkBD
  ||| All free variables in the set
  names : SortedSet $ WithOrigin Name
  ||| The expression the set is equal to
  expr : Maybe $ WithOrigin TTImp

||| Intermediate unification state
public export
record UnificationState {auto uc: UnificationContext} where
  constructor MkUS
  ||| Bucket id counter (incremented every new bucket)
  nextBucket : Nat
  ||| Variable sets
  buckets : SortedMap Nat BucketData
  ||| Name to set id map
  nameToBucket : SortedMap (WithOrigin Name) Nat

parameters {auto uc: UnificationContext}

  public export
  Show BucketData where
    show (MkBD n e) = "MkBD \{show n} \{show e}"


  public export
  Show UnificationState where
    show (MkUS n b nb) = "MkUS \{show n} \{show b} \{show nb}"

  empty : UnificationState
  empty = MkUS Z empty empty

  ||| Refer all the variables in a list to the variable set
  transferVariables : List t -> Nat -> SortedMap t Nat -> SortedMap t Nat
  transferVariables vars bucket m
    = foldr (flip insert bucket) m vars

  ||| Find var set associtated with name, if any
  queryName : WithOrigin Name -> UnificationState -> Maybe BucketData
  queryName n b = lookup n b.nameToBucket >>= flip lookup b.buckets

  setDataByName : 
       WithOrigin Name 
    -> BucketData 
    -> UnificationState 
    -> UnificationState
  setDataByName n d state with (state.nameToBucket `lookup'` n)
    setDataByName _ _ state | Nothing = state
    setDataByName _ d state | (Just bid) = {buckets $= insert bid d} state


  addNewBucket : BucketData -> UnificationState -> UnificationState
  addNewBucket bd state =
    { nextBucket $= S
    , nameToBucket $= transferVariables bd.names.toList state.nextBucket
    , buckets $= flip insert bd state.nextBucket
    } state

  -- Redirect all variables listed in names to point at a instead of b, 
  -- update a with newAData and delete b
  mergeIntoAndUpdate : 
       Nat -> Nat 
    -> List (WithOrigin Name) 
    -> BucketData 
    -> UnificationState 
    -> UnificationState
  mergeIntoAndUpdate a b names newAData = 
    { nameToBucket $= transferVariables names a
    , buckets $= insert a newAData . delete b
    }


  unifyOver : 
       WithOrigin TTImp 
    -> WithOrigin TTImp 
    -> UnificationState 
    -> Elab $ Either String UnificationState

  -- TODO: tersify
  tryMergeBuckets : 
       Nat 
    -> Nat 
    -> UnificationState 
    -> Elab $ Either String UnificationState
  tryMergeBuckets a b state
    = if a == b 
      then pure $ pure $ state
      else case (state.buckets `lookup'` a, state.buckets `lookup'` b) of
        (Just a', Just b') => do
          let mkBucket = MkBD (union a'.names b'.names)
          let merge' = mergeIntoAndUpdate a b b'.names.toList
          let mkNewState = (\x => merge' (mkBucket x) state)
          case (a'.expr, b'.expr) of
            (Just ae, Just be) =>
              unifyOver ae be $ mkNewState $ Just ae
            (Just ae, Nothing) =>
              pure $ pure $ mkNewState $ Just ae
            (Nothing, Just be) =>
              pure $ pure $ mkNewState $ Just be
            (Nothing, Nothing) =>
              pure $ pure $ mkNewState $ Nothing
        _ => pure $ pure $ state


  tryAddVarEqVar : 
       WithOrigin Name 
    -> WithOrigin Name 
    -> UnificationState 
    -> Elab $ Either String UnificationState
  tryAddVarEqVar x y state
    = do
      logMsg "unifier" 0 "tryAddVarEqVar"
      handleBuckets 
        (state.nameToBucket `lookup'` x) 
        (state.nameToBucket `lookup'` y)
      where
      handleBuckets : 
           Maybe Nat -> Maybe Nat 
        -> Elab $ Either String UnificationState
      handleBuckets (Just n) (Just n') = 
        if (n == n') 
          then pure $ pure $ state 
          else tryMergeBuckets n n' state
      handleBuckets (Just n) Nothing = 
        pure $ pure $ 
          { nameToBucket $= insert y n
          , buckets $= updateExisting {names $= insert y} n
          } state
      handleBuckets (Nothing) (Just n) = 
        pure $ pure $ 
          {nameToBucket $= insert x n
          , buckets $= updateExisting {names $= insert x} n
          } state
      handleBuckets Nothing Nothing = 
        pure $ pure $ addNewBucket (MkBD (fromList [x, y]) empty) state



  tryAddVarEqExpr : 
       WithOrigin Name 
    -> WithOrigin TTImp 
    -> UnificationState 
    -> Elab $ Either String UnificationState
  tryAddVarEqExpr n e state
    = case (queryName n state) of
      (Just bd) => case bd.expr of
        Just e' => do
          let emptiedData = {expr := Just e} bd
          let emptiedState = setDataByName n emptiedData state
          unifyOver e e' emptiedState
        Nothing => pure $ pure $ setDataByName n ({expr := Just e} bd) state
      Nothing => pure $ pure $ addNewBucket (MkBD (singleton n) (Just e)) state


  unifyImp : TTImp -> TTImp -> String -> Either String t
  unifyImp lhs rhs s = 
    Left "\{s} (when unifying \{show lhs} and \{show rhs})"

  unifyImp' : TTImp -> TTImp -> String -> Elab $ Either String t
  unifyImp' lhs rhs s = 
    pure $ Left "\{s} (when unifying \{show lhs} and \{show rhs})"

  %inline
  (===) : 
       {auto state: UnificationState} 
    -> WithOrigin Name 
    -> WithOrigin Name 
    -> Elab $ Either String UnificationState
  (===) a b = tryAddVarEqVar a b state

  %inline
  (:==) : 
       {auto state: UnificationState} 
    -> WithOrigin Name 
    -> WithOrigin TTImp 
    -> Elab $ Either String UnificationState
  (:==) a b = tryAddVarEqExpr a b state
  private infixr 1 :==

  matches : 
       {auto state: UnificationState} 
    -> Elab $ Either String UnificationState
  matches = pure $ pure $ state

  unifyOver' : 
       WithOrigin TTImp 
    -> WithOrigin TTImp 
    -> UnificationState 
    -> Elab $ Either String UnificationState
  unifyOver' lhs rhs state with (lhs.data, rhs.data)
    unifyOver' lhs rhs state | (lhs'@(IVar _ nmL), rhs'@(IVar _ nmR))
      = do
        unifyVars lhs.isFreeVar' rhs.isFreeVar'
        where
        -- Check the result of type equality expr search.
        checkTypeEq : Maybe t -> Elab $ Either String UnificationState
        checkTypeEq (Just _) = matches
        checkTypeEq Nothing = 
          unifyImp' lhs' rhs' "Can't find proof of type equality"

        -- Unify two variables with known types.
        unifyWithTypes : TTImp -> TTImp -> Elab $ Either String UnificationState
        unifyWithTypes (IType _) (IType _) = do
          lhs'' : Type <- check lhs'
          rhs'' : Type <- check rhs'
          res : Maybe (lhs'' = rhs'') <- search (lhs''=rhs'')
          checkTypeEq res
        unifyWithTypes (IType _) rrr = unifyImp' lhs' rhs' "Can't unify a type with \{show rrr}"
        unifyWithTypes lll (IType _) = unifyImp' lhs' rhs' "Can't unify a type with \{show lll}"
        unifyWithTypes lhsType@(IPi _ _ _ _ _ _ ) rhsType@(IPi _ _ _ _ _ _) =
          if (lhsType == rhsType && nmL == nmR) then
            matches
          else
            unifyImp' lhs' rhs' "Generic type invocations don't match"
        unifyWithTypes lhsT rhsT = unifyImp' lhs' rhs' "Trying to unify variables with unsupported types: \n (\{show lhs'} : \{show lhsT}) and (\{show rhs'} : \{show rhsT})"

        -- Unify non-free variables.
        unifyNFVars : Elab $ Either String UnificationState
        unifyNFVars = do
          (_, lhsType) <- lookupName nmL
          (_, rhsType) <- lookupName nmR
          unifyWithTypes lhsType rhsType

        -- Unify variables. First arguments correspond to whether a variable is free.
        unifyVars : Bool -> Bool -> Elab $ Either String UnificationState
        unifyVars True True = lhs.same nmL === rhs.same nmR
        unifyVars True False = lhs.same nmL :== rhs
        unifyVars False True = rhs.same nmR :== lhs
        unifyVars False False = unifyNFVars
    unifyOver' lhs rhs state | (lhs'@(IVar _ nm), rhs') = do
      if (lhs.isFreeVar')
        then lhs.same nm :== rhs
        else unifyImp' lhs' rhs' "Trying to unify a variable (\{show nm}) with a dependent value (\{show rhs'})"
    unifyOver' lhs rhs state | (lhs', rhs'@(IVar _ nm)) = do
      logMsg "unifier" 0 "IVar on the right"
      if (rhs.isFreeVar')
        then do
          logMsg "unifier" 0 "Same"
          rhs.same nm :== lhs
        else do
          logMsg "unifier" 0 "Not same"
          unifyImp' lhs' rhs' "Trying to unify a variable (\{show nm}) with a dependent value (\{show lhs'})"
    unifyOver' lhs rhs state | (lhs'@(IApp _ a b), rhs'@(IApp _ a' b')) = do
      state' <- unifyOver (lhs.same a) (rhs.same a') state
      case state' of
        Left s => pure $ Left s
        Right s' => do
          unifyOver (lhs.same b) (rhs.same b') s'
    unifyOver' lhs rhs state | (lhs'@(IPrimVal _ cL), rhs'@(IPrimVal _ cR)) = do
      if (cL == cR)
        then matches
        else unifyImp' lhs' rhs' $ show cL ++ " != " ++ show cR
    unifyOver' lhs rhs state | (lhs', rhs') = do
      unifyImp' lhs' rhs' "Unsupported unification"

  unifyOver lhs rhs state = do
    logMsg "unifier" 0 "unifyOver \{show lhs} \{show rhs}"
    unifyOver' lhs rhs state

  dumpBucket : BucketData -> String
  dumpBucket (MkBD names Nothing) = 
    joinBy " == " $ map show names.toList
  dumpBucket (MkBD names (Just s)) = 
    joinBy " == " $ map show names.toList ++ [show s]

  dumpUState : UnificationState -> String
  dumpUState s = joinBy "\n" $ dumpBucket <$> values s.buckets

tryUnify' : 
     List Name 
  -> TTImp 
  -> List Name 
  -> TTImp 
  -> Elab (uc: UnificationContext ** Either String UnificationState)
tryUnify' ln lhs rn rhs = do
  let uc = MkUC (fromList ln) lhs (fromList rn) rhs
  r <- unifyOver (withLeft lhs) (withRight rhs) empty
  pure (uc ** r)

public export
%macro
tryUnify : 
     List Name 
  -> TTImp 
  -> List Name 
  -> TTImp 
  -> Elab (uc: UnificationContext ** Either String UnificationState)
tryUnify = tryUnify'

dumpUnify' : List Name -> TTImp -> List Name -> TTImp -> Elab $ IO ()
dumpUnify' ln lhs rn rhs = do
  (uc ** ucr) <- tryUnify' ln lhs rn rhs
  case ucr of
    Left e => pure $ putStrLn "Unification error: \{e}"
    Right s => pure $ putStrLn $ dumpUState s

public export
%macro
dumpUnify : List Name -> TTImp -> List Name -> TTImp -> Elab $ IO ()
dumpUnify = dumpUnify'

fancyDPair : 
     (uc : UnificationContext ** Either String UnificationState) 
  -> String
fancyDPair (uc ** Left e) = "Unification error: \{e}"
fancyDPair (uc ** Right s) = dumpUState s

dumpDPair : 
     (uc : UnificationContext ** Either String UnificationState) 
  -> IO ()
dumpDPair = putStrLn . fancyDPair

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

delDepN : Nat -> Nat -> Name -> DependencyGraph -> DependencyGraph
delDepN = ?delDepN_rhs

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

parameters {auto uc: UnificationContext}
  getDepGraph : UnificationState -> DependencyGraph
  getDepGraph state = foldl addBucketDependencies emptyDG $ kvList state.buckets
    where
    addByName : 
      SortedSet (Nat, Name) -> WithOrigin Name -> SortedSet (Nat, Name)
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
        subName' n = {expr $= map $ mapInner {uc} $ substituteVariable n expr}

        updateBucket : BucketData -> BucketData
        updateBucket bd =
          foldr subName' bd 
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

parameters {auto uc: UnificationContext}
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

  consolidateUState : 
    UnificationState -> (SortedMap Name TTImp, SortedMap Name TTImp)
  consolidateUState ustate = do
    let dg = getDepGraph ustate
    let (ns, ndg) = fillIn ustate dg
    let lhs_r = foldl (searchNameByOrigin ns Left) empty uc.lhsVars
    let rhs_r = foldl (searchNameByOrigin ns Right) empty uc.rhsVars
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
          bid <- lookup (MkOriginData o n) ust.nameToBucket
          bd <- lookup bid ust.buckets
          expr <- bd.expr
          Just $ insert n expr.data sm
  
testCUS' : 
     List Name 
  -> TTImp 
  -> List Name 
  -> TTImp 
  -> Elab (SortedMap Name TTImp, SortedMap Name TTImp)
testCUS' lhsVars lhs rhsVars rhs = do
  logMsg "unifier" 0 "Unifying (\{show lhsVars}) => \{show lhs} and (\{show rhsVars}) => \{show rhs}"
  (uc ** ustate) <- tryUnify' lhsVars lhs rhsVars rhs
  handleState ustate
  where
  handleState : 
       {auto uc : UnificationContext} 
    -> Either String UnificationState 
    -> Elab (SortedMap Name TTImp, SortedMap Name TTImp) 
  handleState (Left e) = do
    logMsg "unifier" 0 "Unification error: \{e}"
    pure (empty, empty)
  handleState (Right ustate) = do
    logMsg "unifier" 0 "Unification state: \n\{dumpUState ustate}"
    let (lhsR, rhsR) = consolidateUState ustate
    logMsg "unifier" 0 "LHS variables: \{show lhsR}"
    logMsg "unifier" 0 "RHS variables: \{show rhsR}"
    pure (lhsR, rhsR)

testFI' : 
     List Name 
  -> TTImp 
  -> List Name 
  -> TTImp 
  -> Elab (uc : UnificationContext ** (Either String UnificationState))
testFI' lhsVars lhs rhsVars rhs = do
  logMsg "unifier" 0 "Unifying (\{show lhsVars}) => \{show lhs} and (\{show rhsVars}) => \{show rhs}"
  (uc ** ustate) <- tryUnify' lhsVars lhs rhsVars rhs
  state' <- handleState ustate
  pure (uc ** state')
  where
  handleState : 
       {auto uc : UnificationContext} 
    -> Either String UnificationState 
    -> Elab $ Either String UnificationState
  handleState (Left e) = do
    logMsg "unifier" 0 "Unification error: \{e}"
    pure $ Left e
  handleState (Right ustate) = do
    logMsg "unifier" 0 "Unification state: \n\{dumpUState ustate}"
    let dg = getDepGraph ustate
    logMsg "unifier" 0 "Dependency graph: \{show dg}"
    let (ns, ndg) = fillInOnce ustate dg
    logMsg "unifier" 0 "Filled in state: \n\{dumpUState ns}"
    logMsg "unifier" 0 "Filled in dg: \n\{show ndg}"
    pure $ Right ns

fancyDPairG : 
  (uc : UnificationContext ** Either String UnificationState) -> String
fancyDPairG (uc ** Left e) = "Unification error: \{e}"
fancyDPairG (uc ** Right s) = dumpUStateG s

dumpDPairG : 
  (uc : UnificationContext ** Either String UnificationState) -> IO ()
dumpDPairG = putStrLn . fancyDPairG

dumpUnifyG' : List Name -> TTImp -> List Name -> TTImp -> Elab $ IO ()
dumpUnifyG' ln lhs rn rhs = do
  (uc ** result) <- tryUnify' ln lhs rn rhs
  case result of
    Left e => pure $ putStrLn "Unification error: \{e}"
    Right s => pure $ putStrLn $ dumpUStateG s

%macro
dumpUnifyG : List Name -> TTImp -> List Name -> TTImp -> Elab $ IO ()
dumpUnifyG = dumpUnifyG'

public export
%macro
testFI : 
     List Name -> TTImp -> List Name -> TTImp 
  -> Elab (uc : UnificationContext ** (Either String UnificationState))
testFI = testFI'


public export
%macro
testCUS : 
     List Name -> TTImp -> List Name -> TTImp 
  -> Elab (SortedMap Name TTImp, SortedMap Name TTImp)
testCUS = testCUS'

public export
runUnification :
     List Name -> TTImp -> List Name -> TTImp 
  -> Elab $ Either String (SortedMap Name TTImp, SortedMap Name TTImp)
runUnification lhsVars lhs rhsVars rhs = do
  (uc ** ustate) <- tryUnify' lhsVars lhs rhsVars rhs
  pure $ consolidateUState <$> ustate
