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

freeVarsLambda : TTImp -> SortedSet Name
freeVarsLambda (ILam _ _ _ (Just n) _ r) = insert n $ freeVarsLambda r
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
extractAppData t = extract' $ Reflection.unAppAny t
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

freeVarsApp : AppData -> Types.TypeInfo -> SortedSet Name
freeVarsApp ad tinfo = do
  let tinfo_tuplist = toList $ zip tinfo.args tinfo.argNames
  let tuplistPos = filter (\(x, n) => isPositional x) tinfo_tuplist
  let tuplistNamed = filter (\(x, n) => not $ isPositional x) tinfo_tuplist
  let tlNames : SortedSet Name = fromList $ map snd $ tuplistNamed
  let unfreeNames : SortedSet Name = fromList $ keys ad.named
  let freePositional = fromList $ map snd $ drop (length ad.positional) tuplistPos
  flip difference unfreeNames $ union freePositional tlNames

freeVars'' : TTImp -> AppData -> Types.TypeInfo -> SortedSet Name
freeVars'' t ad ti = union (freeVarsLambda t) $ freeVarsApp ad ti

traverseTupList : List (Arg, Name) -> (SortedMap Name TTImp, List TTImp)
traverseTupList [] = (empty, [])
traverseTupList (((MkArg _ ImplicitArg _ _), nm) :: xs) = 
  let
    (named, positionals) = traverseTupList xs
  in (insert nm (IVar emptyFC nm) named, positionals)
traverseTupList (((MkArg _ ExplicitArg _ _), nm) :: xs) = 
  let
    (named, positionals) = traverseTupList xs
  in (named, IVar emptyFC nm :: positionals)
traverseTupList (((MkArg _ AutoImplicit _ _), nm) :: xs) =   
  let
    (named, positionals) = traverseTupList xs
  in (insert nm (IVar emptyFC nm) named, positionals)
traverseTupList (((MkArg _ (DefImplicit x) _ _), nm) :: xs) =
  let
    (named, positionals) = traverseTupList xs
  in (insert nm ?x_replaced named, positionals)

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
traverseTupList' (((MkArg _ ImplicitArg _ _), nm) :: xs) = 
  let
    (named, positionals) = traverseTupList' xs
  in (insert nm (IVar emptyFC nm) named, positionals)
traverseTupList' (((MkArg _ ExplicitArg _ _), nm) :: xs) = 
  let
    (named, positionals) = traverseTupList' xs
  in (named, nm :: positionals)
traverseTupList' (((MkArg _ AutoImplicit _ _), nm) :: xs) =   
  let
    (named, positionals) = traverseTupList' xs
  in (insert nm (IVar emptyFC nm) named, positionals)
traverseTupList' (((MkArg _ (DefImplicit x) _ _), nm) :: xs) =
  let
    (named, positionals) = traverseTupList' xs
  in (insert nm ?x_replaced_2 named, positionals)

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
  freeVars : SortedSet Name
  fullInvocation : TTImp

Show Types.TypeInfo where
  show ti = "<typeinfo>"

%runElab derive "TaskData" [Show]

restoreApp : Name -> SnocList Arg -> TTImp
restoreApp nm [<] = IVar EmptyFC nm
restoreApp nm (sx :< (MkArg count ExplicitArg name type)) = 
  IApp emptyFC (restoreApp nm sx) $ IVar EmptyFC $ fromMaybe "n" name
restoreApp nm (sx :< (MkArg count _ name type)) = 
  INamedApp emptyFC (restoreApp nm sx) (fromMaybe "n" name) $ IVar EmptyFC $ fromMaybe "n" name

restoreApp' : Name -> SnocList Arg -> TTImp
restoreApp' nm [<] = IVar EmptyFC nm
restoreApp' nm (sx :< (MkArg count ExplicitArg name type)) = 
  IApp emptyFC (restoreApp' nm sx) $ IVar EmptyFC $ fromString $ nameStr $ fromMaybe "n" name
restoreApp' nm (sx :< (MkArg count _ name type)) = 
  INamedApp emptyFC (restoreApp' nm sx) (fromMaybe "n" name) $ IVar EmptyFC $ fromString $ nameStr $ fromMaybe "n" name



restoreBind : Name -> SnocList Arg -> TTImp
restoreBind nm [<] = IVar EmptyFC nm
restoreBind nm (sx :< (MkArg count ExplicitArg name type)) = 
  IApp emptyFC (restoreBind nm sx) $ IBindVar EmptyFC $ nameStr $ fromMaybe "n" name
restoreBind nm (sx :< (MkArg count _ name type)) = 
  INamedApp emptyFC (restoreBind nm sx) (fromMaybe "n" name) $ IBindVar EmptyFC $ nameStr $ fromMaybe "n" name
  
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

conInvocation : Con na va -> Elab (List Name, TTImp)
conInvocation con = do
  (_, conSig) <- lookupName con.name
  let (conArgs, conRetTy) = unPi conSig
  let conArgNames = mapMaybe (.name) conArgs
  pure (conArgNames, conRetTy)

unifyCon : TaskData -> Con na va -> Elab $ Either String (SortedMap Name TTImp, SortedMap Name TTImp)
unifyCon td con = do
  (conArgNames, conRetTy) <- conInvocation con
  let freeVars' = Prelude.toList td.freeVars
  logDebug $ joinBy "\n" 
    [ "For constructor \{show con.name}:"
    , "Unifying \{show freeVars'} : \{show td.fullInvocation}"
    , "     and \{show conArgNames} : \{show conRetTy}"
    ]
  doUnification freeVars' td.fullInvocation conArgNames conRetTy

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

monoConSig : TaskData -> Con na va -> (SortedMap Name TTImp, SortedMap Name TTImp) -> TTImp
monoConSig td con (leftS, rightS) = do
  let retType = substituteVariables leftS td.outputInvocation
  piAll retType $ subInArgs rightS $ toList con.args

monoConstructor : TaskData -> Con na va -> Either String (SortedMap Name TTImp, SortedMap Name TTImp) -> Elab $ Maybe ITy
monoConstructor td con (Right (leftS, rightS)) =
  pure $ Just $ mkTy (dropNS con.name) $ monoConSig td con (leftS, rightS)
monoConstructor _ _ _ = pure $ Nothing

monoTypeDeclaration : TaskData -> List (Either String (SortedMap Name TTImp, SortedMap Name TTImp)) -> Elab Decl
monoTypeDeclaration td uniRs = do
  let l = zip (toList td.typeInfo.cons) uniRs
  conITys <- traverse (uncurry $ monoConstructor td) l
  let conITys' = mapMaybe id conITys

  pure $ iData Public td.outputName td.taskQuoteType [] conITys'

rewireIPi : TTImp -> TTImp -> TTImp
rewireIPi (IPi fc count pinfo mn arg ret) y = IPi fc count pinfo mn arg $ rewireIPi ret y
rewireIPi x y = y

rewireIPiImplicit : TTImp -> TTImp -> TTImp
rewireIPiImplicit (IPi fc count pinfo mn arg ret) y = IPi fc count ImplicitArg mn arg $ rewireIPiImplicit ret y
rewireIPiImplicit x y = y

castToPolySig : TaskData -> TTImp
castToPolySig td =
  rewireIPiImplicit td.taskQuoteType `(Cast ~(td.outputInvocation) ~(td.fullInvocation))

implToPolySig : TaskData -> TTImp
implToPolySig td = 
  rewireIPiImplicit td.taskQuoteType `(~(td.outputInvocation) -> ~(td.fullInvocation))

implToPolyClause : Name -> TaskData -> (Con vs cs, TTImp, Either String (SortedMap Name TTImp, SortedMap Name TTImp)) -> Maybe Clause
implToPolyClause nm td (con, conInv, Left _) = Nothing
implToPolyClause nm td (con, conInv, Right (subL, subR)) = do
  let conSig = monoConSig td con (subL, subR)
  let (a, b) = unPi conSig
  let monoInv = IApp emptyFC (IVar emptyFC nm) $ restoreBind (dropNS con.name) $ cast a
  let (a', b') = unPi conInv
  let conInv' = substituteVariables subR $ restoreApp' con.name $ cast a'
  Just $ PatClause emptyFC monoInv conInv'

implToPolyDef : Name -> TaskData -> List (Con vs cs, TTImp, Either String (SortedMap Name TTImp, SortedMap Name TTImp)) -> Decl
implToPolyDef nm td lcons = IDef emptyFC nm $ mapMaybe (implToPolyClause nm td) lcons

castDef : Name -> Name -> Decl
castDef n n' = IDef emptyFC n $ singleton $ PatClause emptyFC (IVar emptyFC n) `(MkCast ~(IVar emptyFC n'))

fnClaim : Name -> TTImp -> Decl
fnClaim nm = 
  IClaim . MkFCVal EmptyFC .
    MkIClaimData MW Private [] .
      MkTy EmptyFC (MkFCVal EmptyFC nm)

interfaceClaim : Name -> TTImp -> Decl
interfaceClaim nm = 
  IClaim . MkFCVal EmptyFC .
    MkIClaimData MW Public [Hint True] .
      MkTy EmptyFC (MkFCVal EmptyFC nm)

monoNSDeclaration : TaskData -> List Decl -> Decl
monoNSDeclaration td = INamespace emptyFC (MkNS [nameStr td.outputName])

public export
record MonoOpts where
  constructor MkMonoOpts
  deriveCastMToP : Bool

public export
DefaultOpts : MonoOpts
DefaultOpts = MkMonoOpts
  { deriveCastMToP = True
  }

public export
monomorphise : {default DefaultOpts opts : MonoOpts} -> TypeTask l => l -> Name -> Elab ()
monomorphise l outputName = do
  taskData <- getTaskData l outputName
  logDebug "Monomorphising \{show taskData.taskQuote}."
  conSigs <- traverse (\x => pure $ snd $ !(lookupName x.name)) taskData.typeInfo.cons
  unifyResults <- traverse (unifyCon taskData) taskData.typeInfo.cons
  logDebug "Unification results: \{show unifyResults}"
  
  typeDecl <- monoTypeDeclaration taskData unifyResults

  logDebug "deriveCast = \{show opts.deriveCastMToP}"

  let castMToP = 
    if opts.deriveCastMToP then [ fnClaim "mToP" $ implToPolySig taskData 
      , implToPolyDef "mToP" taskData $ zip taskData.typeInfo.cons $ zip conSigs unifyResults
      , interfaceClaim "mToPCast" $ castToPolySig taskData
      , castDef "mToPCast" "mToP" ] else []

  logDebug "castMToP = \{show castMToP}"

  let nsDecl = monoNSDeclaration taskData $ typeDecl :: castMToP

  logDebug "Declaring: \{show nsDecl}"
  declare [nsDecl]

  pure ()

%macro
public export
monomorphise' : {default DefaultOpts opts : MonoOpts} -> TypeTask l => l -> Name -> Elab ()
monomorphise' = monomorphise {opts=opts}
