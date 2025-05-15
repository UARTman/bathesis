module Language.Reflection.Monomorphisation

import public Data.SnocList
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
import public Data.List1
import public Data.Vect
import public Data.List
import public Data.Either
import public Data.SortedMap
import public Data.SortedSet
import public Data.SortedMap.Dependent
import public Text.PrettyPrint.Bernardy.Interface
import public Text.PrettyPrint.Bernardy.Core
import public Language.Reflection.Unification

%language ElabReflection

public export
interface TypeTask (t : Type) where

public export
TypeTask Type

public export
TypeTask b => TypeTask (a -> b)

logDebug : String -> Elab ()
logDebug = logMsg "monomorphiser" 1

logTrace : String -> Elab ()
logTrace = logMsg "monomorphiser" 2

taskToInvocation : TTImp -> Elab TTImp
taskToInvocation (ILam _ _ _ _ _ r) = taskToInvocation r
taskToInvocation x@(IApp _ _ _) = pure x
taskToInvocation x@(INamedApp _ _ _ _) = pure x
taskToInvocation x@(IAutoApp _ _ _) = pure x
taskToInvocation x@(IWithApp _ _ _) = pure x
taskToInvocation x@(IVar _ _) = pure x
taskToInvocation x = failAt (getFC x) "Failed to extract invocation from lambda"

getTName : TTImp -> Elab Name
getTName (IVar _ n) = pure n
getTName t = failAt (getFC t) "Couldn't get type name"

freeVarsLambda : TTImp -> SortedMap Name TTImp
freeVarsLambda (ILam _ _ _ (Just n) a r) = insert n a $ freeVarsLambda r
freeVarsLambda (ILam _ _ _ Nothing _ r) = freeVarsLambda r
freeVarsLambda _ = empty

unfreeVarsNamed : List AnyApp -> SortedSet Name
unfreeVarsNamed [] = empty
unfreeVarsNamed ((NamedApp nm s) :: xs) = insert nm $ unfreeVarsNamed xs
unfreeVarsNamed (_ :: xs) = unfreeVarsNamed xs

data PosArg = ExplArg TTImp | AutoArg TTImp

%runElab derive "PosArg" [Show, Eq]

record AppData where
  constructor MkAppData
  fn : TTImp
  positional : List PosArg
  named : SortedMap Name TTImp
  withs : List TTImp

%runElab derive "AppData" [Show, Eq]

extractAppData : TTImp -> AppData
extractAppData t = extract' $ Expr.unAppAny t
  where
    extract' : (TTImp, List AnyApp) -> AppData
    extract' (fn, []) = MkAppData fn [] empty []
    extract' (fn, ((PosApp s) :: xs)) = {positional $= (ExplArg s ::)} $ extract' (fn, xs)
    extract' (fn, ((NamedApp nm s) :: xs)) = {named $= insert nm s} $ extract' (fn, xs)
    extract' (fn, ((AutoApp s) :: xs)) = {positional $= (AutoArg s ::)} $ extract' (fn, xs)
    extract' (fn, ((WithApp s) :: xs)) = {withs $= (s ::)} $ extract' (fn, xs)

isPositional' : AnyApp -> Bool
isPositional' (PosApp s) = True
isPositional' (NamedApp nm s) = False
isPositional' (AutoApp s) = True
isPositional' (WithApp s) = False

isPositional : Arg -> Bool
isPositional (MkArg count ImplicitArg name type) = False
isPositional (MkArg count ExplicitArg name type) = True
isPositional (MkArg count AutoImplicit name type) = True
isPositional (MkArg count (DefImplicit x) name type) = False

excise : Ord t => SortedSet t -> SortedMap t k -> SortedMap t k
excise x = doit $ Prelude.toList x
  where
    doit : List t -> SortedMap t k -> SortedMap t k
    doit [] x = x
    doit (x :: xs) m = delete x $ doit xs m

freeVarsApp : AppData -> Types.TypeInfo -> SortedMap Name TTImp
freeVarsApp ad tinfo = do
  let tinfo_tuplist = toList $ zip tinfo.args tinfo.argNames
  let tuplistPos = filter (\(x, n) => isPositional x) tinfo_tuplist
  let tuplistNamed = filter (\(x, n) => not $ isPositional x) tinfo_tuplist
  let tlNames : SortedMap Name TTImp = fromList $ map (\(a,n)=>(n, a.type)) $ tuplistNamed
  let unfreeNames : SortedSet Name = fromList $ keys ad.named
  let freePositional = fromList $ map (\(a,n)=>(n, a.type)) $ drop (length ad.positional) tuplistPos
  excise unfreeNames $ mergeLeft freePositional tlNames

freeVars'' : TTImp -> AppData -> Types.TypeInfo -> SortedMap Name TTImp
freeVars'' t ad ti = mergeLeft (freeVarsLambda t) $ freeVarsApp ad ti

traverseTupList : List (Arg, Name) -> (SortedMap Name TTImp, List TTImp)
traverseTupList [] = (empty, [])
traverseTupList (((MkArg _ pinfo _ _), nm) :: xs) with (pinfo, traverseTupList xs)
  traverseTupList (((MkArg _ _ _ _), nm) :: xs) | (ImplicitArg, named, positionals) =
    (insert nm (IVar emptyFC nm) named, positionals)
  traverseTupList (((MkArg _ _ _ _), nm) :: xs) | (ExplicitArg, named, positionals) =
    (named, IVar emptyFC nm :: positionals)
  traverseTupList (((MkArg _ _ _ _), nm) :: xs) | (AutoImplicit, named, positionals) =
    (insert nm (IVar emptyFC nm) named, positionals)
  traverseTupList (((MkArg _ _ _ _), nm) :: xs) | (DefImplicit def, named, positionals) =
    (insert nm ?x_replaced_3 named, positionals)

getExplicits : AppData -> List TTImp
getExplicits ad = ge ad.positional
  where
    ge : List PosArg -> List TTImp
    ge [] = []
    ge ((ExplArg s) :: xs) = s :: ge xs
    ge ((AutoArg s) :: xs) = ge xs

fINamed : TTImp -> List (Name, TTImp) -> TTImp
fINamed t [] = t
fINamed t ((n, a) :: xs) = INamedApp emptyFC (fINamed t xs) n a

traverseTupList' : List (Arg, Name) -> (SortedMap Name TTImp, List Name)
traverseTupList' [] = (empty, [])
traverseTupList' (((MkArg _ pinfo _ _), nm) :: xs) with (pinfo, traverseTupList' xs)
  traverseTupList' (((MkArg _ _ _ _), nm) :: xs) | (ImplicitArg, named, positionals) =
    (insert nm (IVar emptyFC nm) named, positionals)
  traverseTupList' (((MkArg _ _ _ _), nm) :: xs) | (ExplicitArg, named, positionals) =
    (named, nm :: positionals)
  traverseTupList' (((MkArg _ _ _ _), nm) :: xs) | (AutoImplicit, named, positionals) =
    (insert nm (IVar emptyFC nm) named, positionals)
  traverseTupList' (((MkArg _ _ _ _), nm) :: xs) | (DefImplicit def, named, positionals) =
    (insert nm ?x_replaced_4 named, positionals)

acc_positionals : SortedMap Name Name -> (TTImp, Name) -> SortedMap Name Name
acc_positionals a (IVar _ n, n') = insert n n' a
acc_positionals a _ = a

acc_nameds : SortedMap Name Name -> (Name, TTImp) -> SortedMap Name Name
acc_nameds a (n', IVar _ n) = insert n n' a
acc_nameds a _ = a

aliases : AppData -> Types.TypeInfo -> SortedMap Name Name
aliases ad tinfo = do
  let (tyNamed, tyPositional) = traverseTupList' $ toList $ zip tinfo.args tinfo.argNames
  let explicits = getExplicits ad
  let a = foldl acc_positionals empty $ zip explicits tyPositional
  let b = foldl acc_nameds a $ SortedMap.toList ad.named
  b


fullInvocation' : AppData -> Types.TypeInfo -> TTImp
fullInvocation' ad tinfo = do
  let (tyNamed, tyPositional) = traverseTupList $ toList $ zip tinfo.args tinfo.argNames
  let explicits = getExplicits ad
  let fullExplicits = explicits ++ (drop (length explicits) tyPositional)
  let fullNamed = mergeWith (\_,a=>a) tyNamed ad.named
  let nameApplied = fINamed ad.fn (toList fullNamed)
  foldl app nameApplied fullExplicits

record TaskData where
  constructor MkTaskData
  taskQuote : TTImp
  taskQuoteType : TTImp
  typeName : Name
  outputName : Name
  outputInvocation : TTImp
  appData : AppData
  typeInfo : Types.TypeInfo
  freeVars : SortedMap Name TTImp
  fullInvocation : TTImp

Show Types.TypeInfo where
  show ti = "<typeinfo>"

%runElab derive "TaskData" [Show]

||| Restore IApp from a reverse list of args
restoreApp : Name -> SnocList Arg -> TTImp
restoreApp nm [<] = IVar EmptyFC nm
restoreApp nm (sx :< (MkArg count ExplicitArg name type)) =
  IApp emptyFC (restoreApp nm sx) $ IVar EmptyFC $ fromMaybe "n" name
restoreApp nm (sx :< (MkArg count _ name type)) =
  INamedApp emptyFC (restoreApp nm sx) (fromMaybe "n" name) $ IVar EmptyFC $ fromMaybe "n" name

||| Restore IApp from a reverse list of args, doing a back-and-forth string name conversion
|||
||| Useful in referring to bound compiler-generated variables
restoreApp' : Name -> SnocList Arg -> TTImp
restoreApp' nm [<] = IVar EmptyFC nm
restoreApp' nm (sx :< (MkArg count ExplicitArg name type)) =
  IApp emptyFC (restoreApp' nm sx) $ IVar EmptyFC $ fromString $ nameStr $ fromMaybe "n" name
restoreApp' nm (sx :< (MkArg count _ name type)) =
  INamedApp emptyFC (restoreApp' nm sx) (fromMaybe "n" name) $ IVar EmptyFC $ fromString $ nameStr $ fromMaybe "n" name

||| Restore IApp from a reverse list of args, binding variables
restoreBind : Name -> SnocList Arg -> TTImp
restoreBind nm [<] = IVar EmptyFC nm
restoreBind nm (sx :< (MkArg count ExplicitArg name type)) =
  IApp emptyFC (restoreBind nm sx) $ IBindVar EmptyFC $ nameStr $ fromMaybe "n" name
restoreBind nm (sx :< (MkArg count _ name type)) =
  INamedApp emptyFC (restoreBind nm sx) (fromMaybe "n" name) $ IBindVar EmptyFC $ nameStr $ fromMaybe "n" name

||| Restore IApp from a reverse list of args, binding variables, doing a back-and-forth string name conversion
restoreBind' : Name -> SnocList Arg -> SnocList Name -> TTImp
restoreBind' nm [<] [<] = IVar EmptyFC nm
restoreBind' nm _ [<] = IVar EmptyFC nm
restoreBind' nm [<] _ = IVar EmptyFC nm
restoreBind' nm (sx :< (MkArg count ExplicitArg name type)) (sx' :< vname) =
  IApp emptyFC (restoreBind' nm sx sx') $ IBindVar EmptyFC $ nameStr $ vname
restoreBind' nm (sx :< _) (sx' :< _) = restoreBind' nm sx sx'
-- restoreBind' nm (sx :< (MkArg count _ name type)) (sx' :< vname) =
--   INamedApp emptyFC (restoreBind' nm sx sx') (fromMaybe "n" name) $ IBindVar EmptyFC $ nameStr $ vname

||| Extract task data from lambda and name
getTaskData : TypeTask l => l -> Name -> Elab TaskData
getTaskData l' outputName = do
  taskQuote <- quote l'
  taskQuoteType <- quote l
  invocation <- taskToInvocation taskQuote
  let appData = extractAppData invocation
  typeName <- getTName appData.fn
  typeInfo <- Types.getInfo' typeName
  let freeVars = freeVars'' taskQuote appData typeInfo
  let fullInvocation = fullInvocation' appData typeInfo
  let outputInvocation = restoreApp outputName $ cast $ fst $ unPi taskQuoteType
  pure $ MkTaskData
    { taskQuote
    , taskQuoteType
    , typeName
    , outputName
    , outputInvocation
    , appData
    , typeInfo
    , freeVars
    , fullInvocation
    }

gan : Arg -> Maybe (Name, TTImp)
gan (MkArg count piInfo Nothing type) = Nothing
gan (MkArg count piInfo (Just x) type) = Just (x, type)

||| Restore constructor argument names and return types
conInvocation : Con na va -> Elab (List (Name, TTImp), TTImp)
conInvocation con = do
  (_, conSig) <- lookupName con.name
  let (conArgs, conRetTy) = unPi conSig
  let conArgNames = mapMaybe gan conArgs
  pure (conArgNames, conRetTy)

||| Run unification on given constructor
unifyCon : TaskData -> Con na va -> Elab $ Either UnificationError UnificationResult
unifyCon td con = do
  (conArgNames, conRetTy) <- conInvocation con
  let freeVars' = SortedMap.toList td.freeVars
  logDebug $ joinBy "\n"
    [ "For constructor \{show con.name}:"
    , "Unifying \{show freeVars'} : \{show td.fullInvocation}"
    , "     and \{show conArgNames} : \{show conRetTy}"
    ]
  doUnification freeVars' td.fullInvocation conArgNames conRetTy

||| Constructor monomorphisation results
record ConMono where
  constructor MkConMono
  subL : SortedMap Name TTImp
  subR : SortedMap Name TTImp
  sig : TTImp

||| Information about the constructor post-unification
record ConInfo (na : Nat) (va : Vect na Arg) where
  constructor MkConInfo
  con : Con na va
  sig : TTImp
  mono : Maybe ConMono

||| Run a (ConMono -> t) operation on ConInfo, returning Nothing if unification failed
mapMono : (ConMono -> t) -> ConInfo na va -> Maybe t
mapMono f (MkConInfo _ _ (Just mi)) = Just $ f mi
mapMono _ _ = Nothing

mapMonoA : Monad f => (ConMono -> f t) -> ConInfo na va -> f $ Maybe t
mapMonoA f' (MkConInfo _ _ (Just mi)) = do
  fmi <- f' mi
  pure $ Just fmi
mapMonoA f (MkConInfo _ _ Nothing) = pure $ Nothing

subInArgs' : SortedMap Name TTImp -> SortedMap Name TTImp -> List Arg -> List Arg
subInArgs' _ _ [] = []
subInArgs' vMap inScope ((MkArg _ _ Nothing _) :: xs) =
  subInArgs' vMap inScope xs
subInArgs' vMap inScope ((MkArg count piInfo (Just nm) type) :: xs) =
  case lookup nm vMap of
    Just t => subInArgs' vMap (insert nm t inScope) xs
    Nothing =>
      (MkArg count piInfo (Just nm) (substituteVariables inScope type))
        :: subInArgs' vMap inScope xs

||| Remove specified arguments from a list, substituting them everywhere else.
subInArgs : SortedMap Name TTImp -> List Arg -> List Arg
subInArgs vMap = subInArgs' vMap empty

||| Assemble information about a constructor post-invocation
assembleInfo : TaskData -> Con na va -> Either UnificationError (SortedMap Name TTImp, SortedMap Name TTImp) -> Elab $ ConInfo na va
assembleInfo td con (Left _) = do
  (_, conSig) <- conInvocation con
  pure $ MkConInfo con conSig $ Nothing
assembleInfo td con (Right (subL, subR)) = do
  (_, conSig) <- lookupName con.name
  let retType = substituteVariables subL td.outputInvocation
  let mSig = piAll retType $ subInArgs subR $ toList con.args
  pure $ MkConInfo con conSig $ Just $ MkConMono subL subR mSig

||| Assemble information about all constructors
(.assembleInfo) :
     (td: TaskData)
  -> List (Either UnificationError (SortedMap Name TTImp, SortedMap Name TTImp))
  -> Elab $ List $ ConInfo td.typeInfo.arty td.typeInfo.args
(.assembleInfo) td ur = traverse (uncurry (assembleInfo td)) $ zip td.typeInfo.cons ur

||| Generate monomorphic constructor
(.constructor) : TaskData -> ConInfo na va -> Maybe ITy
(.constructor) td conInfo = mapMono inner conInfo
  where
    inner : ConMono -> ITy
    inner mCon = mkTy (dropNS conInfo.con.name) mCon.sig

||| Generate monomorphic type declaration
monoTypeDeclaration' : TaskData -> List (ConInfo na va) -> Decl
monoTypeDeclaration' td conIs =
  iData Public td.outputName td.taskQuoteType [] $ mapMaybe ((.constructor) td) conIs

||| Substitute IPi's return type
rewireIPi : TTImp -> TTImp -> TTImp
rewireIPi (IPi fc count pinfo mn arg ret) y = IPi fc count pinfo mn arg $ rewireIPi ret y
rewireIPi x y = y

||| Substitute IPis' return type and set all arguments to implicit
rewireIPiImplicit : TTImp -> TTImp -> TTImp
rewireIPiImplicit (IPi fc count pinfo mn arg ret) y = IPi fc count ImplicitArg mn arg $ rewireIPiImplicit ret y
rewireIPiImplicit x y = y

||| Generate IPi with implicit type arguments and given return
genericSig : TaskData -> TTImp -> TTImp
genericSig td = rewireIPiImplicit td.taskQuoteType

-- ========================
-- = Cast auto-derivation =
-- ========================

castToPolySig : TaskData -> TTImp
castToPolySig td = genericSig td `(Cast ~(td.outputInvocation) ~(td.fullInvocation))

castToMonoSig : TaskData -> TTImp
castToMonoSig td = genericSig td `(Cast ~(td.fullInvocation) ~(td.outputInvocation))

implToPolySig : TaskData -> TTImp
implToPolySig td = genericSig td `(~(td.outputInvocation) -> ~(td.fullInvocation))

implToMonoSig : TaskData -> TTImp
implToMonoSig td = genericSig td `(~(td.fullInvocation) -> ~(td.outputInvocation))

implToPolyClause' : Name -> TaskData -> ConInfo na va -> Maybe Clause
implToPolyClause' nm td conI = mapMono inner conI
  where
    inner : ConMono -> Clause
    inner conM = do
      let (a, b) = unPi conM.sig
      let monoInv = IApp emptyFC (IVar emptyFC nm) $
        restoreBind (NS (MkNS [(nameStr td.outputName)]) (dropNS conI.con.name)) $ cast a
      let (a', b') = unPi conI.sig
      let conInv' = substituteVariables conM.subR $ restoreApp' conI.con.name $ cast a'
      PatClause emptyFC monoInv conInv'

implToMonoClause' : Name -> TaskData -> ConInfo na va -> Maybe Clause
implToMonoClause' nm td conI = mapMono inner conI
  where
    inner : ConMono -> Clause
    inner conM = do
      let (a, b) = unPi conM.sig
      let (a', b') = unPi conI.sig
      let monoInv = IApp emptyFC (IVar emptyFC nm) $
        substituteBind conM.subR $ restoreBind conI.con.name $ cast a'
      let conInv' = restoreApp' (NS (MkNS [(nameStr td.outputName)]) (dropNS conI.con.name)) $ cast a
      PatClause emptyFC monoInv conInv'

defForConstructors :
  Name -> TaskData -> (ConInfo na va -> Maybe Clause) -> List (ConInfo na va) -> Decl
defForConstructors nm td f = IDef emptyFC nm . mapMaybe f

implToPolyDef' : Name -> TaskData -> List (ConInfo na va) -> Decl
implToPolyDef' nm td = defForConstructors nm td $ implToPolyClause' nm td

implToMonoDef' : Name -> TaskData -> List (ConInfo na va) -> Decl
implToMonoDef' nm td = defForConstructors nm td $ implToMonoClause' nm td

-- ======================
-- = Eq auto-derivation =
-- ======================

implEqSig : TaskData -> TTImp
implEqSig td = genericSig td
  `(Eq ~(td.fullInvocation) => ~(td.outputInvocation) -> ~(td.outputInvocation) -> Bool)

eqSig : TaskData -> TTImp
eqSig td = genericSig td
  `((eqI' : Eq ~(td.fullInvocation)) => Eq ~(td.outputInvocation))

implEqDef : Name -> Name -> Decl
implEqDef n castN = IDef emptyFC n $ singleton $ PatClause emptyFC
  `(~(IVar emptyFC n) a b) `((cast @{~(IVar emptyFC castN)} a) == (cast b))

eqDef : Name -> Name -> Decl
eqDef n n' = IDef emptyFC n $ singleton $ PatClause emptyFC (IVar emptyFC n)
  `(MkEq ~(IVar emptyFC n') (\x,y => not $ ~(IVar emptyFC n') x y))

-- ========================
-- = Show auto-derivation =
-- ========================

implShowSig : TaskData -> TTImp
implShowSig td = genericSig td
  `(Show ~(td.fullInvocation) => ~(td.outputInvocation) -> String)

showSig : TaskData -> TTImp
showSig td = rewireIPiImplicit td.taskQuoteType
  `(Show ~(td.fullInvocation) => Show ~(td.outputInvocation))

implShowDef : Name -> Name -> Decl
implShowDef n castN = IDef emptyFC n $ singleton $ PatClause emptyFC
  `(~(IVar emptyFC n) a) `(show (cast @{~(IVar emptyFC castN)} a))

showDef : Name -> Name -> Decl
showDef n n' = IDef emptyFC n $ singleton $ PatClause emptyFC (IVar emptyFC n)
  `(MkShow ~(IVar emptyFC n') (\_ => ~(IVar emptyFC n')))

castDef : Name -> Name -> Decl
castDef n n' = IDef emptyFC n $ singleton $ PatClause emptyFC (IVar emptyFC n) `(MkCast ~(IVar emptyFC n'))

-- =========================
-- = DecEq auto-derivation =
-- =========================

argEqTuple : List Name -> TTImp
argEqTuple [] = `(_)
argEqTuple (x :: []) = `(~(IVar emptyFC x) ~=~ ~(IVar emptyFC x))
argEqTuple (x :: (y :: [])) = `(Builtin.Pair (~(IVar emptyFC x) ~=~ ~(IVar emptyFC x)) (~(IVar emptyFC y) ~=~ ~(IVar emptyFC y)))
argEqTuple (x :: xs) = `(Builtin.Pair (~(IVar emptyFC x) ~=~ ~(IVar emptyFC x)) ~(argEqTuple xs))

argFn : List Arg -> TTImp -> TTImp
argFn [] t = t
argFn ((MkArg count ExplicitArg Nothing type) :: xs) t = argFn xs t
argFn ((MkArg count ExplicitArg (Just x) type) :: xs) t = `(~(IVar emptyFC x) ~=~ ~(IVar emptyFC x) -> ~(argFn xs t))
argFn (_ :: xs) t = argFn xs t

argBindTuple : List Name -> TTImp
argBindTuple [] = `(())
argBindTuple (x :: []) = IBindVar emptyFC $ nameStr x
argBindTuple (x :: (y :: [])) = `(MkPair ~(IBindVar emptyFC $ nameStr x) ~(IBindVar emptyFC $ nameStr y))
argBindTuple (x :: xs) = `(MkPair ~(IBindVar emptyFC $ nameStr x) ~(argBindTuple xs))

fnClaim : Name -> TTImp -> Decl
fnClaim nm =
  IClaim . MkFCVal EmptyFC .
    MkIClaimData MW Private [] .
      MkTy EmptyFC (MkFCVal EmptyFC nm)

pubFnClaim : Name -> TTImp -> Decl
pubFnClaim nm =
  IClaim . MkFCVal EmptyFC .
    MkIClaimData MW Public [] .
      MkTy EmptyFC (MkFCVal EmptyFC nm)

interfaceClaim : Name -> TTImp -> Decl
interfaceClaim nm =
  IClaim . MkFCVal EmptyFC .
    MkIClaimData MW Public [Hint True] .
      MkTy EmptyFC (MkFCVal EmptyFC nm)

remapNameArg : Arg -> Elab Arg
remapNameArg arg@(MkArg count piInfo (Just x) type) = do
  newN <- genSym $ nameStr x
  pure $ MkArg count piInfo (Just newN) type
remapNameArg arg = pure arg

genTuple : List TTImp -> TTImp
genTuple [] = `(_)
genTuple (x :: []) = x
genTuple (x :: xs) = `(MkPair ~x ~(genTuple xs))

makeImplicit : Arg -> Arg
makeImplicit (MkArg count piInfo name type) = MkArg count ImplicitArg name type

||| Restore IApp from a reverse list of args
restoreAppRename : Name -> SnocList (Arg, Arg) -> TTImp
restoreAppRename nm [<] = IVar EmptyFC nm
restoreAppRename nm (sx :< ((MkArg count _ name type), (MkArg _ _ n' _))) =
  INamedApp emptyFC (restoreAppRename nm sx) (fromMaybe "n" name) $ IVar EmptyFC $ fromMaybe "n" n'

piAllRename' : List (Arg, Arg) -> TTImp -> SortedMap Name TTImp -> TTImp
piAllRename' [] t s = substituteVariables s t
piAllRename' (((MkArg count piInfo (Just name) type), (MkArg _ _ (Just mnm) _)) :: xs) t s =
  IPi EmptyFC count piInfo (Just mnm) (substituteVariables s type) $
    piAllRename' xs t $ insert name (IVar EmptyFC mnm) s
piAllRename' (_ :: xs) t s = piAllRename' xs t s

piAllRename : List (Arg, Arg) -> TTImp -> TTImp
piAllRename a b = piAllRename' a b empty


unpackPolySig' : TaskData -> ConInfo na va -> Elab $ Maybe TTImp
unpackPolySig' td conI = mapMonoA inner conI
  where
    inner : ConMono -> Elab TTImp
    inner conM = do
      let conArgs = toList conI.con.args
      lhsArgs <- traverse remapNameArg conArgs
      rhsArgs <- traverse remapNameArg conArgs
      let lhsApp = restoreAppRename conI.con.name $ cast $ zip conArgs lhsArgs
      let rhsApp = restoreAppRename conI.con.name $ cast $ zip conArgs rhsArgs
      let lhsNames = IVar emptyFC <$> mapMaybe (.name) lhsArgs
      let rhsNames = IVar emptyFC <$> mapMaybe (.name) rhsArgs
      let argTup = genTuple $ map (\(a,b)=>`(~a ~=~ ~b)) $ zip lhsNames rhsNames
      let core = `(~lhsApp ~=~ ~rhsApp -> ~(argTup))
      let pa1 = piAllRename (zip (map makeImplicit conArgs) lhsArgs) core
      let pa2 = piAllRename (zip (map makeImplicit conArgs) rhsArgs) pa1
      pure pa2

unpackMonoSig' : TaskData -> ConInfo na va -> Elab $ Maybe TTImp
unpackMonoSig' td conI = mapMonoA inner conI
  where
    inner : ConMono -> Elab TTImp
    inner conM = do
      let (monoArgs, _) = unPi conM.sig
      let conName = (NS (MkNS [(nameStr td.outputName)]) (dropNS conI.con.name))
      lhsArgs <- traverse remapNameArg $ toList monoArgs
      rhsArgs <- traverse remapNameArg $ toList monoArgs
      let lhsApp = restoreAppRename conName $ cast $ zip monoArgs lhsArgs
      let rhsApp = restoreAppRename conName $ cast $ zip monoArgs rhsArgs
      let lhsNames = IVar emptyFC <$> mapMaybe (.name) lhsArgs
      let rhsNames = IVar emptyFC <$> mapMaybe (.name) rhsArgs
      let argTup = genTuple $ map (\(a,b)=>`(~a ~=~ ~b)) $ zip lhsNames rhsNames
      let core = `(~lhsApp ~=~ ~rhsApp -> ~(argTup))
      let pa1 = piAllRename (zip (map makeImplicit monoArgs) lhsArgs) core
      let pa2 = piAllRename (zip (map makeImplicit monoArgs) rhsArgs) pa1
      pure pa2

genPiEq : List (TTImp, TTImp) -> TTImp -> TTImp
genPiEq [] t = t
genPiEq ((x, y) :: xs) t =
  IPi emptyFC MW ExplicitArg Nothing `(~x ~=~ ~y) $ genPiEq xs t


packPolySig' : TaskData -> ConInfo na va -> Elab $ Maybe TTImp
packPolySig' td conI = mapMonoA inner conI
  where
    inner : ConMono -> Elab TTImp
    inner comM = do
      let conArgs = toList conI.con.args
      lhsArgs <- traverse remapNameArg $ toList conI.con.args
      rhsArgs <- traverse remapNameArg $ toList conI.con.args
      let lhsApp = restoreAppRename conI.con.name $ cast $ zip conArgs lhsArgs
      let rhsApp = restoreAppRename conI.con.name $ cast $ zip conArgs rhsArgs
      let lhsNames = IVar emptyFC <$> mapMaybe (.name) lhsArgs
      let rhsNames = IVar emptyFC <$> mapMaybe (.name) rhsArgs
      let namePairs = zip lhsNames rhsNames
      let core = genPiEq namePairs `(~lhsApp ~=~ ~rhsApp)
      let pa1 = piAllRename (zip (map makeImplicit conArgs) lhsArgs) core
      let pa2 = piAllRename (zip (map makeImplicit conArgs) rhsArgs) pa1
      pure pa2

packMonoSig' : TaskData -> ConInfo na va -> Elab $ Maybe TTImp
packMonoSig' td conI = mapMonoA inner conI
  where
    inner : ConMono -> Elab TTImp
    inner comM = do
      let (conArgs, _) = unPi comM.sig
      let conName = (NS (MkNS [(nameStr td.outputName)]) (dropNS conI.con.name))
      lhsArgs <- traverse remapNameArg $ toList conArgs
      rhsArgs <- traverse remapNameArg $ toList conArgs
      let lhsApp = restoreAppRename conName $ cast $ zip conArgs lhsArgs
      let rhsApp = restoreAppRename conName $ cast $ zip conArgs rhsArgs
      let lhsNames = IVar emptyFC <$> mapMaybe (.name) lhsArgs
      let rhsNames = IVar emptyFC <$> mapMaybe (.name) rhsArgs
      let namePairs = zip lhsNames rhsNames
      let core = genPiEq namePairs `(~lhsApp ~=~ ~rhsApp)
      let pa1 = piAllRename (zip (map makeImplicit conArgs) lhsArgs) core
      let pa2 = piAllRename (zip (map makeImplicit conArgs) rhsArgs) pa1
      pure pa2

unpackPolyClaim' : Name -> TaskData -> ConInfo na va -> Elab $ Maybe Decl
unpackPolyClaim' nm td ci = pure $ pubFnClaim nm <$> !(unpackPolySig' td ci)

unpackMonoClaim' : Name -> TaskData -> ConInfo na va -> Elab $ Maybe Decl
unpackMonoClaim' nm td ci = pure $ pubFnClaim nm <$> !(unpackMonoSig' td ci)

packPolyClaim' : Name -> TaskData -> ConInfo na va -> Elab $ Maybe Decl
packPolyClaim' nm td ci = pure $ pubFnClaim nm <$> !(packPolySig' td ci)

packMonoClaim' : Name -> TaskData -> ConInfo na va -> Elab $ Maybe Decl
packMonoClaim' nm td ci = pure $ pubFnClaim nm <$> !(packMonoSig' td ci)


reflTuple : Nat -> TTImp
reflTuple 0 = `(_)
reflTuple 1 = `(Builtin.Refl)
reflTuple (S n) = `(MkPair Builtin.Refl ~(reflTuple n))

reflApp : Nat -> TTImp -> TTImp
reflApp 0 t = t
reflApp (S n) t = `(~(reflApp n t) Builtin.Refl)

unpackPolyDef' : Name -> TaskData -> ConInfo na va -> Maybe Decl
unpackPolyDef' nm td ci = mapMono inner ci
  where
    inner : ConMono -> Decl
    inner cm = IDef emptyFC nm $ singleton $ PatClause emptyFC `(~(IVar emptyFC nm) Builtin.Refl) $ reflTuple $ length $ toList ci.con.args

unpackMonoDef' : Name -> TaskData -> ConInfo na va -> Maybe Decl
unpackMonoDef' nm td ci = mapMono inner ci
  where
    inner : ConMono -> Decl
    inner cm = do
      let monoArgs = fst $ unPi cm.sig
      IDef emptyFC nm $ singleton $ PatClause emptyFC `(~(IVar emptyFC nm) Builtin.Refl) $ reflTuple $ length $ monoArgs

packPolyDef' : Name -> TaskData -> ConInfo na va -> Maybe Decl
packPolyDef' nm td ci = mapMono inner ci
  where
    inner : ConMono -> Decl
    inner cm = IDef emptyFC nm $ singleton $ PatClause emptyFC (reflApp (length $ toList ci.con.args) (IVar emptyFC nm)) `(Builtin.Refl)

packMonoDef' : Name -> TaskData -> ConInfo na va -> Maybe Decl
packMonoDef' nm td ci = mapMono inner ci
  where
    inner : ConMono -> Decl
    inner cm = do
      let monoArgs = fst $ unPi cm.sig
      IDef emptyFC nm $ singleton $ PatClause emptyFC (reflApp (length monoArgs) (IVar emptyFC nm)) `(Builtin.Refl)


genUnpack' : TaskData -> ConInfo na va -> Elab $ List $ Decl
genUnpack' td ci = do
  nsName <- genSym "MonoNS"
  let monoT = fromMaybe [] $ singleton <$> !(unpackMonoClaim' "unpack" td ci)
  let monoD = fromMaybe [] $ singleton <$> unpackMonoDef' "unpack" td ci
  let monoT' = fromMaybe [] $ singleton <$> !(packMonoClaim' "pack" td ci)
  let monoD' = fromMaybe [] $ singleton <$> packMonoDef' "pack" td ci
  let nsDecl = INamespace emptyFC (MkNS [nameStr nsName]) $ monoT ++ monoD ++ monoT' ++ monoD'
  nsName' <- genSym "PolyNS"
  let polyT = fromMaybe [] $ singleton <$> !(unpackPolyClaim' "unpack" td ci)
  let polyD = fromMaybe [] $ singleton <$> unpackPolyDef' "unpack" td ci
  let polyT' = fromMaybe [] $ singleton <$> !(packPolyClaim' "pack" td ci)
  let polyD' = fromMaybe [] $ singleton <$> packPolyDef' "pack" td ci
  let nsDecl' = INamespace emptyFC (MkNS [nameStr nsName']) $ polyT ++ polyD ++ polyT' ++ polyD'

  pure $ [nsDecl, nsDecl']

castInjImplSig : Name -> TaskData -> Elab TTImp
castInjImplSig convN td = genericSig td <$> inner
  where
    inner : Elab TTImp
    inner = do
      xSym <- genSym "x"
      ySym <- genSym "y"
      let xVar = IVar emptyFC xSym
      let yVar = IVar emptyFC ySym
      let convVar = IVar emptyFC convN
      pure $
        IPi emptyFC MW ExplicitArg (Just xSym) td.outputInvocation $
          IPi emptyFC MW ExplicitArg (Just ySym) td.outputInvocation $
            `((~convVar ~xVar) ~=~ (~convVar ~yVar) -> ~xVar ~=~ ~yVar)

castInjImplClaim : Name -> Name -> TaskData -> Elab Decl
castInjImplClaim n convN td = do
  sig <- castInjImplSig convN td
  pure $ fnClaim n sig

countExplicits : List Arg -> Nat
countExplicits [] = 0
countExplicits ((MkArg count ExplicitArg name type) :: xs) = S $ countExplicits xs
countExplicits (_ :: xs) = countExplicits xs



castInjImplDef : Name -> TaskData -> List (ConInfo na va)-> Elab Decl
castInjImplDef nm td cis = do
  clauses <- mapMaybe id <$> traverse (\x => mapMonoA (castInjClause x) x) cis
  pure $ IDef emptyFC nm clauses
  where
    castInjClause : ConInfo na va -> ConMono -> Elab Clause
    castInjClause conI conM = do
      let nmVar = IVar emptyFC nm
      let (conArgs, _) = unPi conM.sig
      let conName = NS (MkNS [(nameStr td.outputName)]) $ dropNS conI.con.name
      let conVar = IVar emptyFC conName
      lArgs <- traverse remapNameArg conArgs
      rArgs <- traverse remapNameArg conArgs
      tupArgs <- traverse remapNameArg conArgs
      prfSym <- genSym "proof"
      let prfBind = IBindVar emptyFC $ nameStr prfSym
      let prfVar = IVar emptyFC $ fromString $ nameStr $ prfSym
      let lBind = restoreBind' conName (cast $ filter isExplicit $ conArgs) $ cast $ mapMaybe (.name) $ filter isExplicit $ lArgs
      let rBind = restoreBind' conName (cast $ filter isExplicit $ conArgs) $ cast $ mapMaybe (.name) $ filter isExplicit $ rArgs
      let tBind = argBindTuple $ mapMaybe (.name) $ filter isExplicit $ tupArgs
      let lhsApp = `(~nmVar ~lBind ~rBind ~prfBind)
      let rhsApp = restoreApp' "pack" $ cast $ filter isExplicit $ tupArgs
      -- let nmBigApp = `(~nmVar ~conAppB ~conAppB')
      if (countExplicits conArgs) == 0 then
        pure $ PatClause EmptyFC `(~nmVar ~conVar ~conVar _) `(Builtin.Refl) else
        pure $ WithClause EmptyFC lhsApp MW `(unpack ~prfVar) Nothing []
          [ PatClause EmptyFC `(~lhsApp | ~tBind) rhsApp
          ]



monoNSDeclaration : TaskData -> List Decl -> Decl
monoNSDeclaration td = INamespace emptyFC (MkNS [nameStr td.outputName])

||| Monomorphiser options
public export
record MonoOpts where
  constructor MkMonoOpts
  ||| Derive Monomorphic to Polymorphic Cast
  deriveCastMToP : Bool
  ||| Derive Polymorphic to Monomorphic Cast
  deriveCastPToM : Bool

||| Default options
public export
DefaultOpts : MonoOpts
DefaultOpts = MkMonoOpts
  { deriveCastMToP = True
  , deriveCastPToM = True
  }

||| Run elaborator if condition, else fallback
featureGated : Bool -> t -> Elab t -> Elab t
featureGated False t _ = pure t
featureGated True _ x = x

||| Run elaborator and log result if condition, else fallback
gatedLog : Show t => Bool -> t -> String -> Elab t -> Elab t
gatedLog g d s e = featureGated g d $ do
  e' <- e
  logDebug "\{s}: \{show e'}"
  pure e'

||| Log and return expr if condition, else fallback
gatedLog' : Show t => Bool -> t -> String -> t -> Elab t
gatedLog' g d s e = gatedLog g d s $ pure e


showUR : Show t => Either UnificationError t -> String
showUR (Left _) = "<error>"
showUR (Right r) = show r


||| Monomorphise a type based on a lambda and a name
public export
monomorphise : {default DefaultOpts opts : MonoOpts} -> TypeTask l => l -> Name -> Elab ()
monomorphise l outputName = do
  taskData <- getTaskData l outputName
  logDebug "Monomorphising \{show taskData.taskQuote}."

  unifyResults <- traverse (unifyCon taskData) taskData.typeInfo.cons
  logDebug "Unification results: \{joinBy "," $ map showUR unifyResults}"

  conIs <- taskData.assembleInfo $ map (map (\x => (x.lhsVars, x.rhsVars))) unifyResults

  let typeDecl = monoTypeDeclaration' taskData conIs
  logDebug "Type declaration : \{show typeDecl}"

  castMToP <- gatedLog' opts.deriveCastMToP [] "M->P Cast" $ do
    [ fnClaim "mToP" $ implToPolySig taskData
    , implToPolyDef' "mToP" taskData conIs
    , interfaceClaim "mToPCast" $ castToPolySig taskData
    , castDef "mToPCast" "mToP"
    ]

  castPToM <- gatedLog' opts.deriveCastPToM [] "P->M Cast" $ do
    [ fnClaim "pToM" $ implToMonoSig taskData
    , implToMonoDef' "pToM" taskData conIs
    , interfaceClaim "pToMCast" $ castToMonoSig taskData
    , castDef "pToMCast" "pToM"]

  eqImpl <- gatedLog' opts.deriveCastMToP [] "Eq" $ do
    [ fnClaim "eqImpl" $ implEqSig taskData
    , implEqDef "eqImpl" "mToPCast"
    , interfaceClaim "dEq" $ eqSig taskData
    , eqDef "dEq" "eqImpl"
    ]

  showImpl <- gatedLog' opts.deriveCastMToP [] "Show" $ do
    [ fnClaim "showImpl" $ implShowSig taskData
    , implShowDef "showImpl" "mToPCast"
    , interfaceClaim "dShow" $ showSig taskData
    , showDef "dShow" "showImpl"]


  let nsDecl = monoNSDeclaration taskData $
    typeDecl :: castMToP ++ castPToM ++ eqImpl ++ showImpl

  logDebug "Declaring: \{show nsDecl}"
  declare [nsDecl]

  pure ()

%macro
public export
monomorphise' : {default DefaultOpts opts : MonoOpts} -> TypeTask l => l -> Name -> Elab ()
monomorphise' = monomorphise {opts=opts}
