module Language.Reflection.Unification.Engine

import public Language.Reflection.Unification.Monad
import public Language.Reflection.Expr

(.toList) : SortedSet t -> List t
(.toList) = Prelude.toList

lookupNInfo : Elaboration m => Name -> m NameInfo
lookupNInfo n = do
  results <- getInfo n
  case results of
    [] => fail "No variables with this name!"
    ((_, ni) :: _) => pure ni

Eq NameType where
  Bound == Bound = True
  Func == Func = True
  DataCon a b == DataCon a' b' = a == a && b == b'
  TyCon a b == TyCon a' b' = a == a && b == b'
  _ == _ = False


parameters {auto task: UnificationTask}
  logStep : Elaboration m => UStep -> m ()
  logStep step = logMsg "unifier" 1 $ show step

  uStep : Elaboration m => MonadReader UStack m => UStep -> m t -> m t
  uStep step m = do
    logStep step
    local (step ::) m

  public export
  unifyExpr : MonadUni m => Tag TTImp -> Tag TTImp -> m ()

  mergeBuckets : MonadUni m => Nat -> Nat -> m ()
  mergeBuckets a b = if a == b then pure () else uStep (MergeBuckets a b) $ do
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

  addNameBuck : Tag Name -> Nat -> UnificationState -> UnificationState
  addNameBuck x n = 
    { nameToBucket $= insert x n
    , buckets $= updateExisting {names $= insert x} n
    }

  varEqVar : MonadUni m => Tag Name -> Tag Name -> m ()
  varEqVar x y = uStep (VarEqVar x y) $ do
    state <- get
    case (lookup x state.nameToBucket, lookup y state.nameToBucket) of
      (Just n, Just n') => if (n == n') then pure () else mergeBuckets n n'
      (Just n, Nothing) => modify $ addNameBuck x n
      (Nothing, Just n) => modify $ addNameBuck y n
      (Nothing, Nothing) => modify $ addNewBucket $ MkBD (fromList [x,y]) empty

  varEqExpr : MonadUni m => Tag Name -> Tag TTImp -> m ()
  varEqExpr n e = uStep (VarEqExpr n e) $ do
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

  data MyArg : Type where
    Explicit : Tag TTImp -> MyArg
    Auto : Tag TTImp -> MyArg

  Eq MyArg where
    Explicit a == Explicit b = a == b
    Auto a     == Auto b     = a == b
    _          == _          = False

record AppData {auto task: UnificationTask} where
  constructor MkAppData
  fn : Tag TTImp
  positionals : List $ MyArg
  nameds : SortedMap (Tag Name) (Tag TTImp) 
  withs : List $ Tag TTImp

parameters {auto task: UnificationTask}
  addArg : MonadReader UStack m => Origin -> AliasMap -> AnyApp -> AppData -> m AppData
  addArg @{mr} o amap (PosApp s) d = do 
    s' <- mkTag @{task} @{mr} o amap s
    pure $ {positionals $= (Explicit {task} s' ::)} d
  addArg @{mr} o amap (NamedApp nm s) d = do
    nm' <- mkTag @{task} @{mr} o amap nm
    s' <- mkTag @{task} @{mr} o amap s
    pure $ {nameds $= insert nm' s'} d
  addArg @{mr} o amap (AutoApp s) d = do
    s' <- mkTag @{task} @{mr} o amap s
    pure $ {positionals $= (Auto {task} s' ::)} d
  addArg @{mr} o amap (WithApp s) d = do
    s' <- mkTag @{task} @{mr} o amap s
    pure $ {withs $= (s' ::)} d

  unrollIApp : MonadReader UStack m => Tag TTImp -> m AppData
  unrollIApp t = do
    let (fn, args) = Expr.unAppAny t.data
    foldlM (flip (addArg t.origin t.aliasMap)) (MkAppData (t.same fn) [] empty []) args

  unifyMyArg : MonadUni m => MyArg -> MyArg -> m ()
  unifyMyArg (Explicit x) (Explicit y) = unifyExpr x y
  unifyMyArg (Auto x) (Auto y) = unifyExpr x y
  unifyMyArg _ _ = throwUErr ArgExplicitnessMismatch

  unifyNameds : MonadUni m => (Tag Name, Tag TTImp) -> (Tag Name, Tag TTImp) -> m ()
  unifyNameds (n, t) (n', t') =
    if n.data == n'.data
       then unifyExpr t t'
       else throwUErr $ ArgNameMismatch n n'

  unifyAppData : MonadUni m => AppData -> AppData -> m ()
  unifyAppData ad ad' = do
    if length ad.positionals /= length ad'.positionals
      then throwUErr AppPositionalMismatch
      else pure ()
    if (map (.data) (keys ad.nameds)) /= (map (.data) (keys ad'.nameds))
      then throwUErr $ AppNamedMismatch (keys ad.nameds) (keys ad'.nameds)
      else pure ()
    if length ad.withs /= length ad'.withs
      then throwUErr AppWithMismatch
      else pure ()
    unifyExpr ad.fn ad'.fn
    for_ (zip ad.positionals ad'.positionals) $ uncurry unifyMyArg
    for_ (zip ad.withs ad'.withs) $ uncurry unifyExpr
    let adNs : List (Tag Name, Tag TTImp) = toList ad.nameds
    let adNs' : List (Tag Name, Tag TTImp) = toList ad'.nameds
    for_ (zip adNs adNs') $ uncurry unifyNameds
    pure ()

  ford : MonadUni m => Tag TTImp -> Tag TTImp -> m ()
  ford a b = modify {fords $= ((a, b) ::)}

  shouldFordVar : MonadUni m => Tag Name -> m Bool
  shouldFordVar tn = do
    if tn.isFreeVar then
      pure False else do
      let name = tn.data
      (_, nType) <- tryElab "looking up \{name}" $ lookupName name
      nInfo <- tryElab "looking up \{name}'s info" $ lookupNInfo name
      case nInfo.nametype of
        Bound => throwUErr UnsupportedUnification
        Func => pure True
        TyCon _ _ => pure False
        DataCon _ _ => pure False

  shouldFordApp : MonadUni m => Tag TTImp -> m Bool
  shouldFordApp te = do
    appData <- unrollIApp te
    case appData.fn.data of
      IVar _ varN => do
        shouldFordVar $ appData.fn.same varN
      _ => pure True

  shouldFord : MonadUni m => Tag TTImp -> m Bool
  shouldFord t@(MkTag _ _ (IVar fc nm)) = shouldFordVar $ t.same nm
  shouldFord (MkTag _ _ (IPi fc rig pinfo mnm argTy retTy)) = pure True
  shouldFord (MkTag _ _ (ILam fc rig pinfo mnm argTy lamTy)) = pure True
  shouldFord (MkTag _ _ (ILet fc lhsFC rig nm nTy nVal scope)) = pure False
  shouldFord (MkTag _ _ (ICase fc xs s ty cls)) = pure True
  shouldFord (MkTag _ _ (ILocal fc decls s)) = pure True
  shouldFord (MkTag _ _ (IUpdate fc upds s)) = pure True
  shouldFord t@(MkTag _ _ (IApp fc s _)) = shouldFordApp t
  shouldFord t@(MkTag _ _ (INamedApp fc s nm _)) = shouldFordApp t
  shouldFord t@(MkTag _ _ (IAutoApp fc s _)) = shouldFordApp t
  shouldFord t@(MkTag _ _ (IWithApp fc s _)) = shouldFordApp t
  shouldFord (MkTag _ _ (ISearch fc depth)) = throwUErr UnsupportedUnification
  shouldFord (MkTag _ _ (IAlternative fc x ss)) = pure False
  shouldFord (MkTag _ _ (IRewrite fc s t)) = pure True
  shouldFord (MkTag _ _ (IBindHere fc bm s)) = throwUErr UnsupportedUnification
  shouldFord (MkTag _ _ (IBindVar fc str)) = throwUErr UnsupportedUnification
  shouldFord (MkTag _ _ (IAs fc nameFC side nm s)) = throwUErr UnsupportedUnification
  shouldFord (MkTag _ _ (IMustUnify fc dr s)) = throwUErr UnsupportedUnification
  shouldFord (MkTag _ _ (IDelayed fc lr s)) = pure True
  shouldFord (MkTag _ _ (IDelay fc s)) = pure True
  shouldFord (MkTag _ _ (IForce fc s)) = pure True
  shouldFord (MkTag _ _ (IQuote fc s)) = pure False
  shouldFord (MkTag _ _ (IQuoteName fc nm)) = pure False
  shouldFord (MkTag _ _ (IQuoteDecl fc decls)) = pure False
  shouldFord (MkTag _ _ (IUnquote fc s)) = pure False
  shouldFord (MkTag _ _ (IPrimVal fc c)) = pure False
  shouldFord (MkTag _ _ (IType fc)) = pure False
  shouldFord (MkTag _ _ (IHole fc str)) = throwUErr UnsupportedUnification
  shouldFord (MkTag _ _ (Implicit fc bindIfUnsolved)) = throwUErr UnsupportedUnification
  shouldFord (MkTag _ _ (IWithUnambigNames fc xs s)) = pure True

  unifyIApp : MonadUni m => Tag TTImp -> Tag TTImp -> m ()
  unifyIApp lhs rhs = do
    lData <- unrollIApp lhs
    rData <- unrollIApp rhs
    unifyAppData lData rData

  %inline
  (===) : MonadUni m => Tag Name -> Tag Name -> m ()
  (===) = varEqVar

  %inline
  (:==) : MonadUni m => Tag Name -> Tag TTImp -> m ()
  (:==) = varEqExpr
  private infixr 1 :==

  unifyVars : MonadUni m => Tag TTImp -> Tag TTImp -> m ()
  unifyVars lhs rhs with (lhs.data, rhs.data)
    unifyVars lhs rhs | (lhs'@(IVar _ nmL), rhs'@(IVar _ nmR))
      = case (lhs.isFreeVar', rhs.isFreeVar') of
        (True, True) => lhs.same nmL === rhs.same nmR
        (True, False) => lhs.same nmL :== rhs
        (False, True) => rhs.same nmR :== lhs
        (False, False) => do
          (_, lhsType) <- tryElab "looking up \{nmL}" $ lookupName nmL
          (_, rhsType) <- tryElab "looking up \{nmR}" $ lookupName nmR
          lhsInfo <- tryElab "looking up \{nmL}'s info" $ lookupNInfo nmL
          rhsInfo <- tryElab "looking up \{nmR}'s info" $ lookupNInfo nmR

          if (lhsInfo.nametype /= rhsInfo.nametype) 
             then throwUErr NameTypeMismatch
             else do
               lhsT : Maybe Type <- catch $ check lhsType
               rhsT : Maybe Type <- catch $ check rhsType
               case (lhsT, rhsT) of
                (Just lhsT', Just rhsT') => do
                  lhs'' : lhsT' <- tryElab "typechecking \{show lhs'}" $ check lhs'
                  rhs'' : rhsT' <- tryElab "typechecking \{show rhs'}" $ check rhs'
                  res <- search (lhs'' = rhs'')
                  case res of
                    Just _ => pure ()
                    Nothing => throwUErr $ NoTypeEqProof lhs rhs
                (_, _) => do
                  -- unifyExpr (lhs.same lhsType) (rhs.same rhsType)
                  if (lhs' == rhs' && lhsType == rhsType) then pure () else ford lhs rhs
                    
    unifyVars lhs rhs | (lhs', rhs') = throwUErr BrokenInvariant

  unifyVarOther : MonadUni m => Tag TTImp -> Tag TTImp -> m ()
  unifyVarOther lhs@(MkTag _ _ (IVar _ nm)) rhs = 
    if (lhs.isFreeVar')
      then lhs.same nm :== rhs
      else ford lhs rhs
  unifyVarOther lhs rhs = throwUErr BrokenInvariant

  unifyPrim : MonadUni m => Tag TTImp -> Tag TTImp -> m ()
  unifyPrim lhs@(MkTag _ _ (IPrimVal _ cL)) rhs@(MkTag _ _ (IPrimVal _ cR)) = 
    if (cL == cR)
       then pure ()
       else throwUErr $ PrimNE cL cR
  unifyPrim lhs rhs = throwUErr $ BrokenInvariant

  unifyImpl : MonadUni m => Tag TTImp -> Tag TTImp -> m ()
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
    unifyImpl lhs rhs | (rhs', lhs') = throwUErr $ UnsupportedUnification

  unifyExpr lhs rhs = uStep (SubUnification lhs rhs) $ do
    foldLHS <- shouldFord lhs
    foldRHS <- shouldFord rhs
    case (foldLHS, foldRHS) of
      (False, False) => unifyImpl lhs.unalias rhs.unalias
      _ => ford lhs rhs
