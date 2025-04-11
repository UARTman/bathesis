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

--verifyZArgsList' : List (Arg, (t : Type ** t)) -> Elab ()
--verifyZArgsList' = []
--verifyZArgsList' = 



validateTypeInvocation : TTImp -> Elab ()
validateTypeInvocation expr = do
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
      logMsg "monomorphiser" 0 $ "tty = \{show tty}"
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



      

%runElab validateTypeInvocation `(Vect 5 a)

%runElab validateTypeInvocation `(WithOrigin Left 10)

makeUnifyLHS' : Name -> SnocList (Maybe (t : Type ** t)) -> Elab (List Name, TTImp)
makeUnifyLHS' typename [<] = pure ([], IVar EmptyFC typename)
makeUnifyLHS' typename (sx :< Nothing) = do
  freeVarName <- genSym "a"
  (names, rest) <- makeUnifyLHS' typename sx
  pure (freeVarName :: names, IApp EmptyFC rest (IVar EmptyFC freeVarName))
makeUnifyLHS' typename (sx :< (Just ((argt ** arg)))) = do
  quotedArg <- quote arg
  (names, rest) <- makeUnifyLHS' typename sx
  pure (names, IApp EmptyFC rest quotedArg)


appArgsToList : (ngs : Vect argn Arg) -> AppArgs ngs -> List (arg: Arg ** AppArg arg)
appArgsToList [] [] = []
appArgsToList (x :: xs) (y :: ys) = (x ** y) :: appArgsToList xs ys

snocArgsToUnifyRHS : Name -> SnocList (arg: Arg ** AppArg arg) -> TTImp
snocArgsToUnifyRHS nm [<] = IVar EmptyFC nm
snocArgsToUnifyRHS nm (sx :< ((_ ** snd))) = appArg (snocArgsToUnifyRHS nm sx) snd

conArgsToFreeVars : Con n vs -> List Name
conArgsToFreeVars (MkCon name arty args typeArgs) = do
  let (fn ** filtered) = filter (\x => isJust x.name) args
  toList . map (\x => fromMaybe "" x.name) $ filtered

conToUnifyRHS : Name -> (vs : Vect n Arg) => Con n vs -> (List Name, TTImp)
conToUnifyRHS nm @{vs} x = (conArgsToFreeVars x, snocArgsToUnifyRHS nm $ cast $ appArgsToList vs x.typeArgs)

checkExceptHole : TTImp -> Elab (Maybe Type)
checkExceptHole (IHole _ _) = pure Nothing
checkExceptHole t = pure $ Just !(check t)

reduceArgs : TTImp -> List (Maybe x) -> TTImp
reduceArgs x [] = x
reduceArgs (IPi fc c pt mn argTy retTy) (Nothing :: xs) = IPi fc c pt mn argTy $ reduceArgs retTy xs
reduceArgs (IPi fc c pt mn argTy retTy) (Just _ :: xs) = reduceArgs retTy xs
reduceArgs x _ = x

-- hasRightConVal : Name -> List Constraint -> Bool
-- hasRightConVal n [] = False
-- hasRightConVal n ((VarEqVar x y) :: xs) = hasRightConVal n xs
-- hasRightConVal n ((VarEqExpr (Left nm) y) :: xs) = hasRightConVal n xs
-- hasRightConVal n ((VarEqExpr (Right nm) y) :: xs) = n == nm || hasRightConVal n xs

-- filterConArgs : List Arg -> List Constraint -> List Arg
-- filterConArgs [] ys = []
-- filterConArgs (x@(MkArg count piInfo (Just name) type) :: xs) ys = if hasRightConVal name ys then filterConArgs xs ys else x :: filterConArgs xs ys
-- filterConArgs (x@(MkArg count piInfo Nothing type) :: xs) ys = x :: filterConArgs xs ys

aaToTI : AppArgs vs -> List (Maybe x) -> TTImp -> TTImp
aaToTI [] xs s = s
aaToTI (y :: z) [] s = s
aaToTI (y :: z) (Nothing :: xs) s = appArg (aaToTI z xs s) y
aaToTI (y :: z) ((Just w) :: xs) s = aaToTI z xs s

appArgs : AppArgs vs -> TTImp -> TTImp
appArgs [] t = t
appArgs (x :: xs) t = flip appArg x $ appArgs xs t

hasName : List Arg -> Name -> Bool
hasName [] n = False
hasName ((MkArg count piInfo Nothing type) :: xs) n = hasName xs n
hasName ((MkArg count piInfo (Just name) type) :: xs) n = n == name || hasName xs n

extractTnamesFromAA : AppArgs vs -> List Arg -> List Name
extractTnamesFromAA [] xs = []
extractTnamesFromAA ((NamedApp n' (IVar _ n)) :: y) xs = if (hasName xs n) then n :: extractTnamesFromAA y xs else extractTnamesFromAA y xs
extractTnamesFromAA ((AutoApp (IVar _ n)) :: y) xs = if (hasName xs n) then n :: extractTnamesFromAA y xs else extractTnamesFromAA y xs
extractTnamesFromAA ((Regular (IVar _ n)) :: y) xs = if (hasName xs n) then n :: extractTnamesFromAA y xs else extractTnamesFromAA y xs
extractTnamesFromAA (_ :: y) xs = extractTnamesFromAA y xs

genConSig : List Arg -> TTImp -> TTImp
genConSig [] final = final
genConSig ((MkArg count piInfo name type) :: xs) final = IPi emptyFC count piInfo name type $ genConSig xs final

dumpUTR : Either String (SortedMap Name TTImp, SortedMap Name TTImp) -> Elab ()
dumpUTR (Left err) = logMsg "monomorphiser" 0 $ "Unifier failed with error:\n" ++ err
dumpUTR (Right (rhsR, lhsR)) = do
  logMsg "monomorphiser" 0 "Unifier returned:"
  logMsg "monomorphiser" 0 "LHS:"
  _ <- traverse dumpEntry $ kvList lhsR
  logMsg "monomorphiser" 0 "RHS:"
  _ <- traverse dumpEntry $ kvList rhsR
  pure ()
  where
    dumpEntry : (Name, TTImp) -> Elab ()
    -- dumpEntry (k, Nothing) = logMsg "monomorphiser" 0 $ show k ++ " unassigned."
    dumpEntry (k, x) = logMsg "monomorphiser" 0 $ show k ++ " = " ++ show x

monoVariant2 : Name -> List (Maybe (t : Type ** t)) -> Name -> Elab ()
monoVariant2 tname args outputName = do
  logMsg "monomorphiser" 0 $ "Monomorphising \{show tname}"
  -- Get the type of monomorphised type
  (_, tty) <- lookupName tname
  logMsg "monomorphiser" 0 $ "tty = \{show tty}"
  -- Extract the type parameters
  let (typeParams, typeReturn) = unPi tty
  -- Check if it's even a type
  if typeReturn == `(Type) then pure () else do
    fail "Can't monomorphise \{tname} because it isn't a type and is instead \{show tty}."
  -- Get auxiliary information about the type
  -- NOTE: The parameters info is not to be trusted because records have holes.
  tinfo : TypeInfo <- getInfo' tname
  -- Check that parameter list length is correct
  if length args == length typeParams then pure () else 
    fail "Type \{tname} has \{show $ length typeParams} arguments, yet only \{show $ length args} were provided."
  -- 
  let typeParamsTTImp = (.type) <$> typeParams
  typeParamsTypes : List Type <- traverse check typeParamsTTImp

  pure ()

-- %runElab monoVariant2 "List" [Just (Type ** String)] "ListString"
--%runElab monoVariant2 "SortedSet" [Just (Type ** String)] "SSString"
--
--data TestX : (a : Type) -> a -> Type where
--  TestXA : TestX String "Lol"

-- %runElab monoVariant2 "TestX" [Just (Type ** String), Just (String ** "Lol")] "JustSL"
--
--failing
--  %runElab monoVariant2 "monoVariant2" [] "mvmv"
--

subInArgs : SortedMap Name TTImp -> List Arg -> List Arg
subInArgs vMap = map {type $= substituteVariables vMap} . filter (\x => isNothing $ lookup' vMap =<< x.name)

produceConstructor : Name -> List (Maybe (t : Type ** t))->  (Con aty cas, SortedMap Name TTImp) -> ITy 
produceConstructor outputName args (con, vMap) = do
  --let retur = appArgs con.typeArgs $ var tname
  let retur = (aaToTI con.typeArgs args (IVar emptyFC outputName))
  let pa' = piAll (substituteVariables vMap retur) $ subInArgs vMap $ toList con.args
  mkTy (fromString con.name.nameStr) pa'

produceConstructors : Name -> List (Maybe (t : Type ** t)) -> List (Con aty cas, Either String $ (SortedMap Name TTImp, SortedMap Name TTImp)) -> List ITy
produceConstructors _ _ [] = []
produceConstructors n args ((con, Left _) :: xs) = produceConstructors n args xs
produceConstructors n args ((con, Right (_, sm)) :: xs) = produceConstructor n args (con, sm) :: produceConstructors n args xs

runUniTask : (List Name, TTImp) -> (List Name, TTImp) -> Elab $ Either String $ (SortedMap Name TTImp, SortedMap Name TTImp)
runUniTask (freeLHS, lhs) (freeRHS, rhs) = runUnification freeLHS lhs freeRHS rhs

public export
monoVariant : Name -> List (Maybe (t : Type ** t)) -> Name -> Elab ()
monoVariant tname args outputName = do
  logMsg "monomorphiser" 0 $ "Monomorphising type " ++ show tname
  -- Get type info
  tinfo <- getInfo' tname
  -- Check argument list length
  if tinfo.arty == (length args) then pure () else do
    args' <- quote args
    let argsFC = getFC args'
    failAt argsFC $
      "Argument list length (" ++ show (length args)
      ++ ") doesn't match argument count of " ++ show tname
      ++ " (" ++ show tinfo.arty ++ ")."
  -- Check if given arguments are of correct types
  let type_args_list : List Arg = toList $ tinfo.args
  let type_args_names : List (Maybe Name) = map (.name) type_args_list
  let type_args_ttimp : List TTImp = map (.type) type_args_list
  type_args_types : List (Maybe Type)  <- traverse checkExceptHole type_args_ttimp
  let type_args_zipped : List (Maybe Name, (Maybe Type, Maybe (t : Type ** t))) = zip3 type_args_names type_args_types args
  _ <- traverse verifyZippedArgs type_args_zipped
  -- Formulate matching taskst
  unifyTarget <- makeUnifyLHS' tname $ cast args
  logMsg "monomorphiser" 0 $ "Unify LHS: " ++ show unifyTarget
  let consTargets = map (conToUnifyRHS tname @{tinfo.args}) tinfo.cons
  logMsg "monomorphiser" 0 $ "Constructors unify RHSes:" ++ show consTargets
  -- Run unification (for now)
  consUniResult <- traverse (runUniTask unifyTarget) consTargets
  --for_ (zip tinfo.cons consUniResult) (\(con, uniR) => do
  --  let retur = appArgs con.typeArgs $ var tname
  --  let pa = piAll retur $ toList con.args
  --  logMsg "monomorphiser" 0 $ "Constructor \{show con.name}: \{show pa}"
  --  case uniR of
  --    Left _ => pure ()
  --    Right (_, vMap) => do
  --      logMsg "monomorphiser" 0 $ "Unification succeeded."
  --      let pa' = piAll (substituteVariables vMap retur) $ subInArgs vMap $ toList con.args
  --      logMsg "monomorphiser" 0 $ "New constructor type \{show pa'}"
  --      pure ()
  --  --?conUniRRR
  --  pure ())

  (n, tsig) <- lookupName tname

  let contys = produceConstructors outputName args $ zip tinfo.cons consUniResult


  let nsDecl = INamespace emptyFC (MkNS [nameStr outputName]) [
    iData Public outputName (reduceArgs tsig args) [] $ contys    --iData Public (Just $ reduceArgs tsig args) [] []
  ]
  logMsg "monomorphiser" 0 $ "Going to declare \{show nsDecl}"
    -- let ((freeLHS, lhs), (freeRHS, rhs)) = (unifyTarget, consTarget)
    -- -- let csrts = ""
    -- -- csrts <- unifyTypeExprs freeLHS lhs freeRHS rhs
    -- -- dumpUTR csrts
    -- -- csrts <- unifyTypeExprs (fromList freeLHS) (ELeft lhs) (fromList freeRHS) (ERight rhs)
    -- -- logMsg "monomorphiser" 0 $ "Results: " ++ show csrts
    -- pure csrts)
  -- Acquire target signature
  -- (n, tsig) <- lookupName tname
  -- logMsg "monomorphiser" 0 $ "tsig = " ++ show tsig
  -- -- Generate constructor types
  -- let contys = map (\(con, uniR) => MkTy emptyFC (MkFCVal emptyFC (fromString (con.name.nameStr))) (genConSig (toList con.args) (aaToTI con.typeArgs args (IVar emptyFC outputName)))) $ zip tinfo.cons consUniResult
  -- -- Declare new type with namespace
  -- let nsDecl = INamespace emptyFC (MkNS [nameStr outputName]) [
  --   IData emptyFC (SpecifiedValue Public) Nothing (MkData emptyFC outputName (Just $ reduceArgs tsig args) [] contys)
  -- ]
  -- logMsg "monomorphiser" 0 $ "Declaring: " ++ show nsDecl
  declare [nsDecl]
  pure ()

%runElab monoVariant "List" [Just (Type ** Nat)] "ListNat"

ln : ListNat
ln = [1,2,3]

failing
  ln' : ListNat
  ln' = ["x", "y", "z"]

%runElab monoVariant "Vect" [Nothing, Just (Type ** String)] "VectString"

vs : VectString 3
vs = ["x", "y", "z"]

failing
  vs' : VectString 4
  vs' = ["only one"]

failing
  vs'' : VectString 1
  vs'' = ["x", "y"]

public export
%macro
monoVariant' : Name -> List (Maybe (t : Type ** t)) -> Name -> Elab ()
monoVariant' = monoVariant
