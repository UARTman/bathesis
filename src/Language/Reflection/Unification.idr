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
import public Control.Monad.State
import public Control.Monad.Either

import public Derive.Prelude
import public Deriving.Show
import public Text.PrettyPrint.Bernardy.Core
import public Language.Reflection.Pretty
import public Text.PrettyPrint.Bernardy.Interface

import public Deriving.DepTyCheck.Util.Reflection

%language ElabReflection

(.toList) : SortedSet t -> List t
(.toList) = Prelude.toList

public export
record UnificationCtx where
  constructor MkUC
  lhs : TTImp
  lhsVars : SortedSet Name
  rhs : TTImp
  rhsVars : SortedSet Name

%runElab derive "UnificationCtx" [Show, Eq]

||| Origin of data (left- or right-hand side)
public export
data Origin = Left | Right

public export
Eq Origin where
  (==) Left Left = True
  (==) Right Right = True
  (==) _ _ = False

%runElab derive "Origin" [Show, Eq]

public export
record Tag {auto uc: UnificationCtx} (t : Type) where
  constructor MkTag
  origin: Origin
  inner: t

parameters {auto uc: UnificationCtx}
  public export
  Eq t => Eq (Tag t) where
    (==) (MkTag o x) (MkTag o' y) = o == o' && x == y

  public export
  Show t => Show (Tag t) where
    show (MkTag Left x) = "tagLeft \{show x}"
    show (MkTag Right x) = "tagRight \{show x}"

  public export
  Ord t => Ord (Tag t) where
    compare (MkTag Left x) (MkTag Left y) = compare x y
    compare (MkTag Left _) (MkTag Right _) = LT
    compare (MkTag Right _) (MkTag Left _) = GT
    compare (MkTag Right x) (MkTag Right y) = compare x y

  public export
  Functor Tag where
    map f (MkTag o x) = MkTag o $ f x

  public export
  tagLeft : t -> Tag t
  tagLeft = MkTag Left

  public export
  tagRight : t -> Tag t
  tagRight = MkTag Right

  public export
  (.same) : Tag t -> g -> Tag g
  (.same) (MkTag o _) x = MkTag o x

  public export
  (-|>) : Tag t -> g -> Tag g
  (-|>) = (.same)

  public export
  (.data) : Tag t -> t
  (.data) = (.inner)

  -- Free variables
  ||| Access free variables, available from the context
  public export
  (.freeVars) : Tag t -> SortedSet Name
  (.freeVars) (MkTag Left _) = uc.lhsVars
  (.freeVars) (MkTag Right _) = uc.rhsVars

  ||| Check if a name with origin metadata refers to a free variable
  public export
  (.isFreeVar) : Tag Name -> Bool
  (.isFreeVar) dt = dt.freeVars `contains'` dt.data

  ||| Check if an expression with origin metadata is a free variable invocation
  public export
  (.isFreeVar') : Tag TTImp -> Bool
  (.isFreeVar') dt@(MkTag _ (IVar _ y)) = dt.freeVars `contains'` y
  (.isFreeVar') _ = False

  ||| List all the free variables an origin-tagged expression depends on
  public export
  dependencies : Tag TTImp -> SortedSet Name
  dependencies dt =
    fromList .
    filter (\n => containsVariable n dt.data) .
    Prelude.toList .
    (.freeVars) $
    dt

  ||| List all the free variables an origin-tagged expression depends on
  public export
  (.dependencies) : Tag TTImp -> SortedSet Name
  (.dependencies) = dependencies

||| Infomration on a set of equivalent free variables
public export
record BucketData {auto uc: UnificationCtx} where
  constructor MkBD
  ||| All free variables in the set
  names : SortedSet $ Tag Name
  ||| The expression the set is equal to
  expr : Maybe $ Tag TTImp

public export
record UnificationState {auto uc: UnificationCtx} where
  constructor MkUS
  ||| Bucket id counter (incremented every new bucket)
  nextBucket : Nat
  ||| Variable sets
  buckets : SortedMap Nat BucketData
  ||| Name to set id map
  nameToBucket : SortedMap (Tag Name) Nat

parameters {auto uc: UnificationCtx}
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
  queryName : Tag Name -> UnificationState -> Maybe BucketData
  queryName n b = lookup n b.nameToBucket >>= flip lookup b.buckets

  setDataByName :
       Tag Name
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
    -> List (Tag Name)
    -> BucketData
    -> UnificationState
    -> UnificationState
  mergeIntoAndUpdate a b names newAData =
    { nameToBucket $= transferVariables names a
    , buckets $= insert a newAData . delete b
    }

  public export
  UnificationT : (m : Type -> Type) -> Elaboration m => Type -> Type
  UnificationT m = EitherT String $ StateT UnificationState m

  public export
  Unification : Type -> Type
  Unification = UnificationT Elab

  public export
  liftElab : Elab t -> Unification t
  liftElab = lift . lift

  public export
  tryElab : Elaboration m => String -> Elab t -> UnificationT m t
  tryElab errMsg e = do
    elabRes <- catch e
    case elabRes of
      Nothing => left errMsg
      Just r => pure r

  public export
  runUni : Elaboration m => UnificationState -> UnificationT m t -> m (UnificationState, Either String t)
  runUni s = runStateT s . runEitherT

  public export
  evalUni : Elaboration m => UnificationState -> UnificationT m t -> m $ Either String t
  evalUni s = evalStateT s . runEitherT

  unifyExpr : Elaboration m => Tag TTImp -> Tag TTImp -> UnificationT m ()

  tryMergeBuckets : Elaboration m => Nat -> Nat -> UnificationT m ()
  tryMergeBuckets a b = if a == b then pure () else do
    state <- get
    case (lookup a state.buckets, lookup b state.buckets) of
      (Just a', Just b') => do
        let mkBucket = MkBD (union a'.names b'.names)
        let merge' = mergeIntoAndUpdate a b b'.names.toList
        let mkNewState = (\x => merge' (mkBucket x) state)
        case (a'.expr, b'.expr) of
          (Just ae, Just be) => do
            put $ mkNewState $ Just ae
            unifyExpr ae be
          (Just ae, Nothing) =>
            put $ mkNewState $ Just ae
          (Nothing, Just be) =>
            put $ mkNewState $ Just be
          (Nothing, Nothing) =>
            put $ mkNewState $ Nothing
      _ => pure ()
  
  tryAddVarEqVar : Elaboration m => Tag Name -> Tag Name -> UnificationT m ()
  tryAddVarEqVar x y = do
    state <- get
    case (lookup x state.nameToBucket, lookup y state.nameToBucket) of
      (Just n, Just n') => if (n == n') then pure () else tryMergeBuckets n n'
      (Just n, Nothing) => lift $ modify
        { nameToBucket $= insert y n
        , buckets $= updateExisting {names $= insert y} n
        }
      (Nothing, Just n) => lift $ modify
        { nameToBucket $= insert x n
        , buckets $= updateExisting {names $= insert x} n
        }
      (Nothing, Nothing) => lift $ modify $ addNewBucket $ MkBD (fromList [x,y]) empty

  tryAddVarEqExpr : Elaboration m => Tag Name -> Tag TTImp -> UnificationT m ()
  tryAddVarEqExpr n e = do
    state <- get
    case (queryName n state) of
      Just bd => do
        let emptiedData = {expr := Just e} bd
        case bd.expr of
          Just e' => do
            modify $ setDataByName n emptiedData
            unifyExpr e e'
          Nothing => modify $ setDataByName n emptiedData
      Nothing => modify $ addNewBucket (MkBD (singleton n) (Just e))

uFail : MonadError String m => TTImp -> TTImp -> String -> m t
uFail lhs rhs s = throwError "\{s} (when unifying \{show lhs} and \{show rhs})"

parameters {auto uc: UnificationCtx}

  data MyArg = Explicit (Tag TTImp) | Auto (Tag TTImp)
  
  Eq MyArg where
    (==) (Explicit a) (Explicit b) = a == b
    (==) (Auto a) (Auto b) = a == b
    (==) _ _ = False

record AppData {auto uc: UnificationCtx} where
  constructor MkAppData
  fn : Tag TTImp
  positionals : List MyArg
  nameds : SortedMap (Tag Name) (Tag TTImp) 
  withs : List $ Tag TTImp
    -- defaults : SortedSet $ Tag TTImp

parameters {auto uc: UnificationCtx}

  addArg : Origin -> AnyApp -> AppData -> AppData
  addArg o (PosApp s) = {positionals $= (Explicit {uc} (MkTag {uc} o s) ::)}
  addArg o (NamedApp nm s) = {nameds $= insert (MkTag {uc} o nm) (MkTag {uc} o s)}
  addArg o (AutoApp s) = {positionals $= (Auto {uc} (MkTag {uc} o s) ::)}
  addArg o (WithApp s) = {withs $= ((MkTag {uc} o s) ::)}

  unrollIApp : Tag TTImp -> AppData
  unrollIApp t = do
    let (fn, args) = Deriving.DepTyCheck.Util.Reflection.unAppAny t.data
    foldl (flip (addArg t.origin)) (MkAppData (t.same fn) [] empty []) args

  unifyMyArg : Elaboration m => MyArg -> MyArg -> UnificationT m ()
  unifyMyArg (Explicit x) (Explicit y) = unifyExpr x y
  unifyMyArg (Auto x) (Auto y) = unifyExpr x y
  unifyMyArg _ _ = left "IApp unify: explicit argument kind mismatch"

  unifyNameds : Elaboration m => (Tag Name, Tag TTImp) -> (Tag Name, Tag TTImp) -> UnificationT m ()
  unifyNameds (n, t) (n', t') =
    if n.data == n'.data
       then unifyExpr t t'
       else left "IApp unify: named argument name mismatch"

  unifyAppData : Elaboration m => AppData -> AppData -> UnificationT m ()
  unifyAppData ad ad' = do
    if length ad.positionals /= length ad'.positionals
      then left "IApp unify: positionals length mismatch"
      else pure ()
    if (map (.data) (keys ad.nameds)) /= (map (.data) (keys ad'.nameds))
      then left "IApp unify: nameds keys mismatch"
      else pure ()
    if length ad.withs /= length ad'.withs
      then left "IApp unify: withs length mismatch"
      else pure ()
    unifyExpr ad.fn ad'.fn
    for_ (zip ad.positionals ad'.positionals) $ uncurry unifyMyArg
    for_ (zip ad.withs ad'.withs) $ uncurry unifyExpr
    let adNs : List (Tag Name, Tag TTImp) = toList ad.nameds
    let adNs' : List (Tag Name, Tag TTImp) = toList ad'.nameds
    for_ (zip adNs adNs') $ uncurry unifyNameds
    pure ()


  unifyIApp : Elaboration m => Tag TTImp -> Tag TTImp -> UnificationT m ()
  unifyIApp lhs@(MkTag _ lhs') rhs@(MkTag _ rhs') = do
    let lData = unrollIApp lhs
    let rData = unrollIApp rhs
    unifyAppData lData rData

  tryElab' : Elaboration m => TTImp -> TTImp -> String -> Elab t -> UnificationT m t
  tryElab' lhs rhs s op = do
    res <- catch op
    tquote <- quote op
    case res of
      Nothing => throwError "Reflection error when \{s} (\{show tquote}) (when unifying \{show lhs} and \{show rhs})"
      Just e => pure e

  %inline
  (===) : Elaboration m => Tag Name -> Tag Name -> UnificationT m ()
  (===) = tryAddVarEqVar

  %inline
  (:==) : Elaboration m => Tag Name -> Tag TTImp -> UnificationT m ()
  (:==) = tryAddVarEqExpr
  private infixr 1 :==

  unifyVars : Elaboration m => Tag TTImp -> Tag TTImp -> UnificationT m ()
  unifyVars lhs rhs with (lhs.data, rhs.data)
    unifyVars lhs rhs | (lhs'@(IVar _ nmL), rhs'@(IVar _ nmR))
      = case (lhs.isFreeVar', rhs.isFreeVar') of
        (True, True) => lhs.same nmL === rhs.same nmR
        (True, False) => lhs.same nmL :== rhs
        (False, True) => rhs.same nmR :== lhs
        (False, False) => do
          (_, lhsType) <- tryElab' lhs' rhs' "looking up \{nmL}" $ lookupName nmL
          (_, rhsType) <- tryElab' lhs' rhs' "looking up \{nmR}" $ lookupName nmR
          case (lhsType, rhsType) of
            (IType _, IType _) => do
              lhs'' : Type <- tryElab' lhs' rhs' "typechecking \{show lhs'}" $ check lhs'
              rhs'' : Type <- tryElab' lhs' rhs' "typechecking \{show rhs'}" $ check rhs'
              res <- search (lhs'' = rhs'')
              case res of
                Just _ => pure ()
                Nothing => uFail lhs' rhs' "Can't find proof of type equality between \{show lhs'} and \{show rhs'}"
            (IType _, rrr) => uFail lhs' rhs' "Can't unify a type with \{show rrr}"
            (lll, IType _) => uFail lhs' rhs' "Can't unify a type with \{show lll}"
            (IPi _ _ _ _ _ _, IPi _ _ _ _ _ _ ) =>
              if (lhsType == rhsType && nmL == nmR) then
                pure ()
              else
                uFail lhs' rhs' "Generic type invocations don't match"
            (_, _) =>
              if (lhsType == rhsType && lhs' == rhs') then
                pure ()
              else 
                uFail lhs' rhs' "Trying to unify variables with unsupported types: \n (\{show lhs'} : \{show lhsType}) and (\{show rhs'} : \{show rhsType})"
    unifyVars lhs rhs | (lhs', rhs') = uFail lhs' rhs' "Impossible (unifyVars)"

  unifyVarOther : Elaboration m => Tag TTImp -> Tag TTImp -> UnificationT m ()
  unifyVarOther lhs@(MkTag _ (IVar _ nm)) rhs = 
    if (lhs.isFreeVar')
      then lhs.same nm :== rhs
      else uFail lhs.data rhs.data "Trying to unify a non-free variable (\{show nm}) with a non-variable value (\{show rhs.data})"
  unifyVarOther lhs rhs = uFail lhs.data rhs.data "Impossible (unifyVarOther)"

  unifyPrim : Elaboration m => Tag TTImp -> Tag TTImp -> UnificationT m ()
  unifyPrim lhs@(MkTag _ (IPrimVal _ cL)) rhs@(MkTag _ (IPrimVal _ cR)) = 
    if (cL == cR)
       then pure ()
       else uFail lhs.data rhs.data "\{show cL} != \{show cR}"
  unifyPrim lhs rhs = uFail lhs.data rhs.data "Impossible (unifyPrim)"

  unifyImpl : Elaboration m => Tag TTImp -> Tag TTImp -> UnificationT m ()
  unifyImpl lhs rhs with (lhs.data, rhs.data)
    unifyImpl lhs rhs | (lhs'@(IVar _ nmL), rhs'@(IVar _ nmR))
      = unifyVars lhs rhs
    unifyImpl lhs rhs | (lhs'@(IVar _ _), rhs') = unifyVarOther lhs rhs
    unifyImpl lhs rhs | (lhs', rhs'@(IVar _ _)) = unifyVarOther rhs lhs
    unifyImpl lhs rhs | (lhs'@(IPrimVal _ _), rhs'@(IPrimVal _ _)) = unifyPrim lhs rhs
    unifyImpl lhs rhs | (lhs'@(IApp _ _ _), rhs'@(IApp _ _ _)) = unifyIApp lhs rhs
    unifyImpl lhs rhs | (lhs'@(INamedApp _ _ _ _), rhs'@(INamedApp _ _ _ _)) = unifyIApp lhs rhs
    unifyImpl lhs rhs | (lhs'@(IWithApp _ _ _), rhs'@(IWithApp _ _ _)) = unifyIApp lhs rhs
    unifyImpl lhs rhs | (lhs'@(IAutoApp _ _ _), rhs'@(IAutoApp _ _ _)) = unifyIApp lhs rhs
    unifyImpl lhs rhs | (rhs', lhs') = uFail lhs' rhs' "Unsupported unification"

  unifyExpr lhs rhs = do
    unifyImpl lhs rhs 

  dumpBucket : BucketData -> String
  dumpBucket (MkBD names Nothing) =
    joinBy " == " $ show <$> names.toList
  dumpBucket (MkBD names (Just s)) =
    joinBy " == " $ map show names.toList ++ [show s]

  dumpUState : UnificationState -> String
  dumpUState s = joinBy "\n" $ dumpBucket <$> values s.buckets

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

parameters {auto uc: UnificationCtx}
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

parameters {auto uc: UnificationCtx}
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
          bid <- lookup (MkTag o n) ust.nameToBucket
          bd <- lookup bid ust.buckets
          expr <- bd.expr
          Just $ insert n expr.data sm



public export
doUnification' : (uc : UnificationCtx) -> Unification $ (SortedMap Name TTImp, SortedMap Name TTImp)
doUnification' uc = do
  unifyExpr (tagLeft uc.lhs) (tagRight uc.rhs)
  state <- get
  pure $ consolidateUState state

public export
doUnification : List Name -> TTImp -> List Name -> TTImp -> Elab $ Either String (SortedMap Name TTImp, SortedMap Name TTImp)
doUnification lhsV lhs rhsV rhs = do
  let uc = MkUC lhs (fromList lhsV) rhs (fromList rhsV)
  evalUni empty $ doUnification' uc
