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

-- %default total
%language ElabReflection

%logging "unifier" 0
-- %auto_lazy off


verifyZippedArgs : (Maybe Name, (Maybe Type, Maybe (t : Type ** t))) -> Elab ()
verifyZippedArgs (_, (_, Nothing)) = pure ()
verifyZippedArgs (_, (Nothing, _)) = pure ()
verifyZippedArgs (n, (Just x, (Just ((fst ** snd))))) = do
  r : Maybe x <- catch $ check !(quote snd)
  let n' = fromMaybe "<unnamed>" n
  case r of
    Just x => pure ()
    Nothing => failAt (getFC !(quote fst)) $
      "Wrong type of value given for argument " ++ show n' ++
      ". Got " ++ show !(quote fst) ++
      " while expecting " ++ show !(quote x) ++ "."
  pure ()

verifyZippedArgs' : (Arg, (t: Type ** t)) -> Elab ()
verifyZippedArgs' (arg, (givenTy ** val)) = do
  realParamTy : Type <- check arg.type
  typesMatch <- catch $ search (givenTy = realParamTy)
  givenTyQ <- quote givenTy
  let aName = fromMaybe "<unnamed>" arg.name
  case typesMatch of
    Just _ => pure ()
    Nothing => failAt (getFC !(quote givenTy)) "Wrong type fo value given for argument \{aName}. Got \{show givenTyQ} instead of \{show arg.type}."
  pure ()


validateTypeInvocation : TTImp -> Elab ()
validateTypeInvocation expr = do
  logMsg "monomorphiser" 0 "Validating \{show expr}"
  let (tname_ttimp, args) = unApp expr
  validateNamed tname_ttimp args
  
  where
    validateAppArgs : {auto tps: Vect l Arg} -> Either String (AppArgs tps, TTImp) -> Elab ()
    validateAppArgs (Left err) = fail err
    validateAppArgs {tps=tps} (Right (appArgs, remainder)) = do
      -- logMsg "monomorphiser" 0 "appArgs = \{show appArgs}"
      logMsg "monomorphiser" 0 "remainder = \{show remainder}"
      pure ()

    validateNamed : TTImp -> List TTImp -> Elab ()
    validateNamed (IVar _ tname) args = do
      -- Get the type of monomorphised type
      (_, tty) <- lookupName tname
      logMsg "monomorphiser" 0 $ "Type invoked signature: \{show tty}"
      -- Extract the type parameters
      let (typeParams, typeReturn) = unPi tty
      -- Check if it's even a type
      if typeReturn == `(Type) then pure () else do
        fail "Can't monomorphise \{tname} because it isn't a type and is instead \{show tty}."

      let tps : Vect _ Arg = fromList typeParams
      let appArgs = getArgs tps expr

      validateAppArgs appArgs

      pure ()
    validateNamed tn _ = fail "\{show tn} is not a type name."

--%runElab validateTypeInvocation `(Vect 5 a)

-- %runElab validateTypeInvocation `(MkTag @{uc} Left 10)

||| Handle absent name by generating unique name
makeArgName : Maybe Name -> Elab Name
makeArgName Nothing = genSym "n"
makeArgName (Just n) = pure n

||| Create a type invocation in style of compiler-provided ones based on argument's PiInfo and name
makeLHSApp : PiInfo TTImp -> Maybe Name -> TTImp -> TTImp -> TTImp
makeLHSApp ExplicitArg _ f x = IApp emptyFC f x
makeLHSApp _ Nothing f x = IAutoApp emptyFC f x
makeLHSApp _ (Just n) f x = INamedApp emptyFC f n x

||| Given a typename and an inverse list of argument data, produce a unification LHS (free variables and a type invocation)
makeUnifyLHS : Name -> SnocList (Arg, Maybe (t : Type ** t)) -> Elab (List Name, TTImp)
makeUnifyLHS typename [<] = pure ([], IVar EmptyFC typename)
makeUnifyLHS typename (sx :< ((MkArg _ (DefImplicit def) name _), Nothing)) = do
  (names, rest) <- makeUnifyLHS typename sx
  let app = makeLHSApp (DefImplicit def) name rest def
  pure (names, app)
makeUnifyLHS typename (sx :< ((MkArg _ piInfo name _), Nothing)) = do
  freeName <- genSym "x"
  (names, rest) <- makeUnifyLHS typename sx
  pure (freeName :: names, makeLHSApp piInfo name rest (IVar emptyFC freeName))
makeUnifyLHS typename (sx :< ((MkArg _ piInfo name _), (Just (t ** arg)))) = do
  quotedArg <- quote arg 
  (names, rest) <- makeUnifyLHS typename sx
  pure (names, makeLHSApp piInfo name rest quotedArg)

appArgsToList : (ngs : Vect argn Arg) -> AppArgs ngs -> List (arg: Arg ** AppArg arg)
appArgsToList [] [] = []
appArgsToList (x :: xs) (y :: ys) = (x ** y) :: appArgsToList xs ys

snocArgsToUnifyRHS : Name -> SnocList (arg: Arg ** AppArg arg) -> TTImp
snocArgsToUnifyRHS nm [<] = IVar EmptyFC nm
snocArgsToUnifyRHS nm (sx :< ((_ ** snd))) = appArg (snocArgsToUnifyRHS nm sx) snd

||| Find free variables in constructor's return type
conArgsToFreeVars : Con n vs -> List Name
conArgsToFreeVars (MkCon name arty args typeArgs) = do
  let (fn ** filtered) = filter (\x => isJust x.name) args
  toList . map (\x => fromMaybe "" x.name) $ filtered

||| Generate a unification RHS (free variables and a generic type invocation) for a given constructor and typename
conToUnifyRHS : Name -> (vs : Vect n Arg) => Con n vs -> (List Name, TTImp)
conToUnifyRHS nm @{vs} x = (conArgsToFreeVars x, snocArgsToUnifyRHS nm $ cast $ appArgsToList vs x.typeArgs)

||| Evaluate TTImp to type, allowing for holes
checkExceptHole : TTImp -> Elab (Maybe Type)
checkExceptHole (IHole _ _) = pure Nothing
checkExceptHole t = pure $ Just !(check t)

||| Remove specified variables from a dependent function signature 
|||
||| TODO: Check for bizarre dependent type failures (removed argument used in other argument's type signature)
reduceArgs : TTImp -> List (Maybe x) -> TTImp
reduceArgs x [] = x
reduceArgs (IPi fc c pt mn argTy retTy) (Nothing :: xs) = IPi fc c pt mn argTy $ reduceArgs retTy xs
reduceArgs (IPi fc c pt mn argTy retTy) (Just _ :: xs) = reduceArgs retTy xs
reduceArgs x _ = x

||| Restore AppArgs into a function call, ignoring specified variables
|||
||| Useful in generating constructors
restoreApp : AppArgs vs -> List (Maybe x) -> TTImp -> TTImp
restoreApp [] xs s = s
restoreApp (y :: z) [] s = s
restoreApp (y :: z) (Nothing :: xs) s = appArg (restoreApp z xs s) y
restoreApp (y :: z) ((Just w) :: xs) s = restoreApp z xs s


||| Remove specified arguments from a list, substituting them everywhere else.
|||
||| TODO: this may lead to nasty collisions, new version should ideally take order of args into account
subInArgs : SortedMap Name TTImp -> List Arg -> List Arg
subInArgs vMap = map {type $= substituteVariables vMap} . filter (\x => isNothing $ lookup' vMap =<< x.name)

||| Generate a single constructor ITy value
produceConstructor : Name -> List (Maybe dp) -> (Con aty cas, SortedMap Name TTImp) -> ITy 
produceConstructor outputName args (con, vMap) = do
  --- Generate a monomorphic type invocation from constructor's type args and specified arg data
  let retur = restoreApp con.typeArgs args $ IVar emptyFC outputName
  --- Generate a function signature for the constructor
  --- TODO: check what happens when it runs into implicits
  let pa' = piAll (substituteVariables vMap retur) $ subInArgs vMap $ toList con.args
  --- Produce a type 
  mkTy (fromString con.name.nameStr) pa'

||| Generate a list of constructor ITy values
produceConstructors : Name -> List (Maybe (t : Type ** t)) -> List (Con aty cas, Either String $ (SortedMap Name TTImp, SortedMap Name TTImp)) -> List ITy
produceConstructors _ _ [] = []
produceConstructors n args ((con, Left _) :: xs) = produceConstructors n args xs
produceConstructors n args ((con, Right (_, sm)) :: xs) = produceConstructor n args (con, sm) :: produceConstructors n args xs

||| Perform a unification task
runUniTask : (List Name, TTImp) -> (List Name, TTImp) -> Elab $ Either String $ (SortedMap Name TTImp, SortedMap Name TTImp)
runUniTask (freeLHS, lhs) (freeRHS, rhs) = doUnification freeLHS lhs freeRHS rhs

public export
monoVariant : Name -> List (Maybe (t : Type ** t)) -> Name -> Elab ()
monoVariant tname args outputName = do
  logMsg "monomorphiser" 0 $ "Monomorphising type " ++ show tname
  -- Get type info
  tinfo <- getInfo' tname
  (n, tsig) <- lookupName tname
  let (targs, _) = unPi tsig
  -- Check argument list length
  if tinfo.arty == (length args) then pure () else do
    args' <- quote args
    let argsFC = getFC args'
    failAt argsFC $
      "Argument list length (" ++ show (length args)
      ++ ") doesn't match argument count of " ++ show tname
      ++ " (" ++ show tinfo.arty ++ ")."
  -- Check if given arguments are of correct types
  let type_args_names = (.name) <$> targs
  let type_args_ttimp = (.type) <$> targs
  type_args_types : List (Maybe Type)  <- traverse checkExceptHole type_args_ttimp
  let type_args_zipped : List (Maybe Name, (Maybe Type, Maybe (t : Type ** t))) = zip3 type_args_names type_args_types args
  _ <- traverse verifyZippedArgs type_args_zipped
  -- Formulate matching taskst
  let zippedULTask : SnocList (Arg, Maybe (t: Type ** t)) = zip (cast targs) (cast args)
  unifyTarget <- makeUnifyLHS tname zippedULTask
  logMsg "monomorphiser" 0 $ "Unify LHS: " ++ show unifyTarget
  let consTargets = conToUnifyRHS tname @{tinfo.args} <$> tinfo.cons
  logMsg "monomorphiser" 0 $ "Constructors unify RHSes:" ++ show consTargets
  -- Run unification
  consUniResult <- traverse (runUniTask unifyTarget) consTargets  

  logMsg "monomorphiser" 0 $ "Unification results:" ++ show consUniResult

  let contys = produceConstructors outputName args $ zip tinfo.cons consUniResult

  let nsDecl = INamespace emptyFC (MkNS [nameStr outputName]) [
    iData Public outputName (reduceArgs tsig args) [] $ contys
  ]
  logMsg "monomorphiser" 0 $ "Going to declare \{show nsDecl}"

  declare [nsDecl]
  pure ()

--%runElab monoVariant "Vect" [Nothing, Just (Type ** String)] "VectString"
--
--vs : VectString 3
--vs = ["x", "y", "z"]
--
--failing
--  vs' : VectString 4
--  vs' = ["only one"]
--
--failing
--  vs'' : VectString 1
--  vs'' = ["x", "y"]
--
--%runElab monoVariant "Tag" [Nothing, Just (Type ** String)] "TagString"

public export
%macro
monoVariant' : Name -> List (Maybe (t : Type ** t)) -> Name -> Elab ()
monoVariant' = monoVariant
