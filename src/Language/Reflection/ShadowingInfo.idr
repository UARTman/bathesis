module Language.Reflection.ShadowingInfo

import public Language.Reflection
import public Language.Reflection.Pretty
import public Language.Reflection.Util
import public Language.Reflection.Types
import public Language.Reflection.TT
import public Language.Reflection.TTImp
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops
import public Language.Reflection.QuoteInfo
import public Control.Monad.Identity
import public Control.Monad.Trans
import public Control.Monad.Reader
import public Control.Monad.State
import public Data.SortedSet
import public Data.SortedMap

%default total

public export
NameSet : Type
NameSet = SortedSet Name

export
data ShadowingInfoT : (m : Type -> Type) -> (a : Type) -> Type where
  MkShadowingInfoT : (ReaderT NameSet m a) -> ShadowingInfoT m a

unwrapShadowingInfoT : (ShadowingInfoT m a) -> (ReaderT NameSet m a)
unwrapShadowingInfoT (MkShadowingInfoT r) = r

public export
runShadowingInfoT : NameSet -> ShadowingInfoT m a -> m a
runShadowingInfoT s (MkShadowingInfoT r) = runReaderT s r

public export
implementation Functor m => Functor (ShadowingInfoT m) where
  map f (MkShadowingInfoT g) = MkShadowingInfoT $ map f g

public export
implementation Applicative f => Applicative (ShadowingInfoT f) where
  pure x = MkShadowingInfoT $ MkReaderT $ \_ => pure x

  MkShadowingInfoT f <*> MkShadowingInfoT a = MkShadowingInfoT $ f <*> a

helper : (a -> ShadowingInfoT m b) -> a -> ReaderT NameSet m b
helper f a = unwrapShadowingInfoT $ f a

public export
implementation Monad m => Monad (ShadowingInfoT m) where
  MkShadowingInfoT (MkReaderT f) >>= k =
    let k' = helper k in MkShadowingInfoT $ MkReaderT $ \st => f st >>= runReaderT st . k'

public export
implementation MonadTrans (ShadowingInfoT) where
  lift x = MkShadowingInfoT $ MkReaderT $ \_ => x

public export
implementation HasIO m => HasIO (ShadowingInfoT m) where
  liftIO f = MkShadowingInfoT $ MkReaderT $ \_ => liftIO f

public export
implementation Alternative f => Alternative (ShadowingInfoT f) where
  empty = MkShadowingInfoT $ MkReaderT $ const empty

  MkShadowingInfoT (MkReaderT f) <|> mg = MkShadowingInfoT $ MkReaderT $ \st => f st <|> runReaderT' (unwrapShadowingInfoT mg) st

public export
interface Monad m => MonadReadShadowingInfo m where
  varIsShadowed : Name -> m Bool
  shadowedVars : m NameSet

export
implementation Monad m => MonadReadShadowingInfo (ShadowingInfoT m) where
  varIsShadowed name = MkShadowingInfoT ask <&> contains name
  shadowedVars = MkShadowingInfoT ask

public export
implementation Monad m => MonadWriteQuoteInfo (ShadowingInfoT (QuoteInfoT m)) where
  setIsQuote b (MkShadowingInfoT x) = lift $ setIsQuote b $ runReaderT !shadowedVars x

export
implementation MonadState t m => MonadState t (ShadowingInfoT m) where
  get = lift get
  put x = lift (put x)


localSI : Monad m => (NameSet -> NameSet) -> ShadowingInfoT m a -> ShadowingInfoT m a
localSI f (MkShadowingInfoT s) = MkShadowingInfoT $ local f s

countBVHelper : MonadState (SortedSet Name) m => TTImp -> m TTImp -> m TTImp
countBVHelper (IBindVar _ s) m = do
  modify (insert (UN (Basic s)))
  m
countBVHelper (IAs _ _ _ n _) m = do
  modify (insert n)
  m
countBVHelper t m = m

countBV : TTImp -> SortedSet Name
countBV t = execState empty $ mapATTImp' countBVHelper t

whatParamsListBinds : List (Name, (Count, (PiInfo TTImp, TTImp))) -> SortedSet Name
whatParamsListBinds l = fromList . map (\(x,y)=>x) $ l

-- isDeclPublic : Decl
isDeclPrivate : Decl -> Bool
isDeclPrivate (IClaim (MkFCVal fc (MkIClaimData rig Private xs sig))) = True
isDeclPrivate (IClaim (MkFCVal fc (MkIClaimData rig _ xs sig))) = False
isDeclPrivate (IData fc DefaultedValue mtreq dt) = True
isDeclPrivate (IData fc (SpecifiedValue Private) mtreq dt) = True
isDeclPrivate (IRecord fc mstr DefaultedValue mtreq rec) = True
isDeclPrivate (IRecord fc mstr (SpecifiedValue Private) mtreq rec) = True
isDeclPrivate _ = False

whatDeclExports : Decl -> SortedSet Name
whatDeclDeclares : Decl -> SortedSet Name


whatDeclExports (IParameters fc params decls) = assert_total foldl (\x, y => union (whatDeclExports y) x) empty decls
whatDeclExports d = if (isDeclPrivate d) then empty else whatDeclDeclares d

whatDeclDeclares (IClaim (MkFCVal fc (MkIClaimData rig vis xs (MkTy fc1 (MkFCVal nameFC n) ty)))) = insert n empty
whatDeclDeclares (IData fc x mtreq (MkData fc1 n tycon opts datacons)) = do
  let datacons' = Data.SortedSet.fromList $ map (\(MkTy fc (MkFCVal nameFC n) ty) => n) datacons
  insert n datacons'
whatDeclDeclares (IData fc x mtreq (MkLater fc1 n tycon)) = insert n empty
whatDeclDeclares (IDef fc nm cls) = empty
whatDeclDeclares (IParameters fc params decls) = assert_total foldl (\x, y => union (whatDeclDeclares y) x) empty decls
whatDeclDeclares (IRecord fc mstr x mtreq (MkRecord fc1 n params opts conName fields)) = do
  let fields' = Data.SortedSet.fromList $ map (\(MkIField fc rig pinfo nm s) => nm) fields
  insert n fields'
whatDeclDeclares (INamespace fc ns decls) = do
  let addNS = NS ns
  let allDeclared = assert_total foldl (\x, y => union (whatDeclExports y) x) empty decls
  let allDeclared' = fromList . map (NS ns) . Prelude.toList $ allDeclared
  union allDeclared allDeclared'
whatDeclDeclares (ITransform fc nm s t) = empty
whatDeclDeclares (IRunElabDecl fc s) = empty
whatDeclDeclares (ILog x) = empty
whatDeclDeclares (IBuiltin fc bty nm) = insert nm empty



whatPiBinds' : TTImp -> SortedSet Name
whatPiBinds' (IPi fc rig pinfo Nothing argTy retTy) = whatPiBinds' retTy
whatPiBinds' (IPi fc rig pinfo (Just x) argTy retTy) = insert x $ whatPiBinds' retTy
whatPiBinds' _ =  empty

whatPiBinds : TTImp -> SortedSet Name
whatPiBinds t = union (countBV t) (whatPiBinds' t)

whatDeclBinds : Decl -> SortedMap Name $ SortedSet Name
whatDeclBinds (IClaim (MkFCVal fc (MkIClaimData rig vis xs (MkTy fc1 (MkFCVal nameFC n) ty)))) = insert n (union (whatPiBinds ty) (countBV ty)) empty
whatDeclBinds (IParameters fc params decls) = do
  let bs = foldl (mergeWith union) Data.SortedMap.empty $ map (assert_total whatDeclBinds) decls
  let pb = whatParamsListBinds params
  map (union pb) bs
whatDeclBinds (INamespace fc ns decls)
  = foldl (mergeWith union) Data.SortedMap.empty $ map (assert_total whatDeclBinds) decls
whatDeclBinds _ = empty

mutual
  doClause :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    Clause -> ShadowingInfoT m Clause
  doClause f (PatClause fc lhs rhs) = do
    let lhs_names = countBV lhs
    lhs' <- assert_total mapATTImp' (provideShadowingInfo f) lhs
    rhs' <- localSI (union lhs_names) $ assert_total mapATTImp' (provideShadowingInfo f) rhs
    pure $ PatClause fc lhs' rhs'
  doClause f (WithClause fc lhs rig wval prf flags cls) = do
    let lhs_names = countBV lhs
    lhs' <- assert_total mapATTImp' (provideShadowingInfo f) lhs
    wval' <- assert_total mapATTImp' (provideShadowingInfo f) wval
    let newNs = fromMaybe lhs_names $ map (\(_, x) => insert x lhs_names) prf
    cls' <- localSI (union newNs) $ assert_total traverse (doClause f) cls
    pure $ WithClause fc lhs' rig wval' prf flags cls'
  doClause f (ImpossibleClause fc lhs) = do
    lhs' <- assert_total mapATTImp' (provideShadowingInfo f) lhs
    pure $ ImpossibleClause fc lhs'

  doDeclList' :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    SortedMap Name (SortedSet Name) -> List Decl -> ShadowingInfoT m (List Decl)
  doDeclList' f bs [] = pure []
  doDeclList' f bs (x@(IDef fc nm cls) :: xs) = do
    let bound = fromMaybe empty $ lookup nm bs
    x' <- localSI (union bound) $ doDecl f x
    let xDecl = whatDeclDeclares x
    let xB = whatDeclBinds x
    xs' <- localSI (union xDecl) $ doDeclList' f (mergeWith union xB bs) xs
    pure $ x' :: xs'
  doDeclList' f bs (x :: xs) = do
    x' <- doDecl f x
    let xDecl = whatDeclDeclares x
    let xB = whatDeclBinds x
    xs' <- localSI (union xDecl) $ doDeclList' f (mergeWith union xB bs) xs
    pure $ x' :: xs'

  doDeclList :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    List Decl -> ShadowingInfoT m (List Decl)
  doDeclList f ds = doDeclList' f empty ds

  doParamList :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    List (Name, (Count, (PiInfo TTImp, TTImp))) ->
    ShadowingInfoT m (List (Name, (Count, (PiInfo TTImp, TTImp))))
  doParamList f [] = pure []
  doParamList f ((nm, (cnt, (pinfo, t))) :: xs) = do
    t' <- assert_total mapATTImp' (provideShadowingInfo f) t
    xs' <- localSI (insert nm) $ assert_total doParamList f xs
    pure $ (nm, (cnt, (pinfo, t'))) :: xs'

  doIField :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    IField -> ShadowingInfoT m IField
  doIField f (MkIField fc rig pinfo nm s) = do
    s' <- assert_total mapATTImp' (provideShadowingInfo f) s
    pure $ MkIField fc rig pinfo nm s'

  doRecord :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    Record -> ShadowingInfoT m Record
  doRecord f (MkRecord fc n params opts conName fields) = do
    fields' <- assert_total traverse (doIField f) fields
    pure $ MkRecord fc n params opts conName fields'

  doITy :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    ITy -> ShadowingInfoT m ITy
  doITy f (MkTy fc (MkFCVal nameFC n) ty) = do
    ty' <- assert_total $ mapATTImp' (provideShadowingInfo f) ty
    pure $ MkTy fc (MkFCVal nameFC n) ty'

  doDecl :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    Decl -> ShadowingInfoT m Decl
  doDecl f (IClaim (MkFCVal fc (MkIClaimData rig vis xs ty))) =
    pure $ IClaim (MkFCVal fc (MkIClaimData rig vis xs !(doITy f ty)))
  doDecl f (IData fc x mtreq (MkData fc1 n Nothing opts datacons)) = do
    dcs' <- localSI (insert n) $ assert_total traverse (doITy f) datacons
    pure $ IData fc x mtreq (MkData fc1 n Nothing opts dcs')
  doDecl f (IData fc x mtreq (MkData fc1 n (Just y) opts datacons)) = do
    y' <- assert_total mapATTImp' (provideShadowingInfo f) y
    dcs' <- localSI (insert n) $ assert_total traverse (doITy f) datacons
    pure $ IData fc x mtreq (MkData fc1 n (Just y') opts dcs')
  doDecl f (IData fc x mtreq (MkLater fc1 n tycon)) = do
    tc' <- assert_total mapATTImp' (provideShadowingInfo f) tycon
    pure $ IData fc x mtreq (MkLater fc1 n tc')
  doDecl f (IDef fc nm cls) = do
    cls' <- localSI (insert nm) $ assert_total traverse (doClause f) cls
    pure $ IDef fc nm cls'
  doDecl f (IParameters fc params decls) = do
    params' <- doParamList f params
    let pl_binds = whatParamsListBinds params
    decls' <- localSI (union pl_binds) $ doDeclList f decls
    pure $ IParameters fc params' decls'
  doDecl f (IRecord fc mstr x mtreq rec) = do
    rec' <- doRecord f rec
    pure $ IRecord fc mstr x mtreq rec'
  doDecl f (INamespace fc ns1 decls) = do
    decls' <- doDeclList f decls
    pure $ INamespace fc ns1 decls'
  doDecl f d = mapMDecl f d

  public export
  provideShadowingInfo :
    Monad m =>
    (TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp) ->
    TTImp -> ShadowingInfoT m TTImp -> ShadowingInfoT m TTImp
  provideShadowingInfo f b@(IPi fc count piinfo n argTy retTy) newM = do
    let bound = countBV argTy
    let bound = fromMaybe bound $ map (\x => insert x bound) n
    argTy' <- assert_total mapATTImp' (provideShadowingInfo f) argTy
    retTy' <- localSI (union bound) $ assert_total mapATTImp' (provideShadowingInfo f) retTy
    f b $ pure $ IPi fc count piinfo n argTy' retTy'
  provideShadowingInfo f b@(ILam fc count piinfo n argTy retTy) newM = do
    let bound = countBV argTy
    let bound = fromMaybe bound $ map (\x => insert x bound) n
    argTy' <- assert_total mapATTImp' (provideShadowingInfo f) argTy
    retTy' <- localSI (union bound) $ assert_total mapATTImp' (provideShadowingInfo f) retTy
    f b $ pure $ ILam fc count piinfo n argTy' retTy'
  provideShadowingInfo f b@(ILet fc lhsFC count n nTy nVal scope) newM = do
    -- Study if bind are necessary
    nTy' <- assert_total mapATTImp' (provideShadowingInfo f) nTy
    nVal' <- assert_total mapATTImp' (provideShadowingInfo f) nVal
    scope' <- localSI (insert n) $ assert_total mapATTImp' (provideShadowingInfo f) scope
    f b $ pure $ ILet fc lhsFC count n nTy' nVal' scope'
  provideShadowingInfo f b@(ICase fc xs t ty cls) newM = do
    t' <- assert_total mapATTImp' (provideShadowingInfo f) t
    ty' <- assert_total mapATTImp' (provideShadowingInfo f) ty
    cls' <- traverse (doClause f) cls
    f b $ pure $ ICase fc xs t' ty' cls'
  provideShadowingInfo f b@(ILocal fc decls t) newM = do
    decls' <- assert_total doDeclList f decls
    let declared = foldl union empty $ map whatDeclDeclares decls
    t' <- localSI (union declared) $ assert_total mapATTImp' (provideShadowingInfo f) t
    f b $ pure $ ILocal fc decls' t'
  provideShadowingInfo f b newM = f b newM
