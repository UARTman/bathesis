module Language.Reflection.Unification.Error

import public Control.Monad.Either
import public Control.Monad.Reader
import public Language.Reflection.Unification.Context

parameters {auto task: UnificationTask}
  public export
  data ErrorKind : Type where
    ||| Elaboration failed with string explanation
    ElabFailed : String -> ErrorKind
    ||| Two positional arguments have different explicitness
    ArgExplicitnessMismatch : ErrorKind
    ||| Two named arguments that should have the same name have different ones
    ArgNameMismatch : Tag Name -> Tag Name -> ErrorKind
    ||| Two IApp have different amount of positional arguments
    AppPositionalMismatch : ErrorKind
    ||| Two IApp have different amount of with arguments
    AppWithMismatch : ErrorKind
    ||| Two IApp have different sets of named arguments
    AppNamedMismatch : List (Tag Name) -> List (Tag Name) -> ErrorKind
    ||| Can't find proof of type equality
    NoTypeEqProof : Tag TTImp -> Tag TTImp -> ErrorKind
    ||| Can't unify type variable with non-type variable
    CantUnifyTypeWith : Name -> TTImp -> ErrorKind
    ||| Trying to unify two different functions
    FuncVarMismatch : ErrorKind
    ||| Trying to unify two different bounds
    BoundVarMismatch : ErrorKind
    ||| Trying to unify two different types
    TypeConMismatch : ErrorKind
    ||| Trying to unify two different constructors
    DataConMismatch : ErrorKind
    ||| Trying to unify two variables of different kinds
    NameTypeMismatch : ErrorKind
    ||| Unifying variables of unsupported types
    UnsupportedVars : Name -> TTImp -> Name -> TTImp -> ErrorKind
    ||| Trying to unify variable with non-variable
    VarNonVar : ErrorKind
    ||| Trying to unify different primitive values
    PrimNE : Constant -> Constant -> ErrorKind
    ||| Internal invariant was broken
    BrokenInvariant : ErrorKind
    ||| Unifying unsupported expr types
    UnsupportedUnification : ErrorKind
  
  public export
  prettyError : ErrorKind -> String
  prettyError (ElabFailed str) = "Elaboration \{str} failed"
  prettyError ArgExplicitnessMismatch = "Tried to unify explicit and implicit positional arguments"
  prettyError (ArgNameMismatch x y) = "Named argument mismatch (\{show x}, \{show y})"
  prettyError AppPositionalMismatch = "Different amount of positional arguments"
  prettyError AppWithMismatch = "Different amount of with arguments"
  prettyError (AppNamedMismatch xs ys) = "Different sets of named arguments: \{show xs} and \{show ys}"
  prettyError (NoTypeEqProof x y) = "No proof of equality found between \{show x} and \{show y}"
  prettyError (CantUnifyTypeWith nm s) = "Can't unify a type variable \{show nm} with non-type variable \{show s}"
  prettyError FuncVarMismatch = "Trying to unify different functions"
  prettyError BoundVarMismatch = "Trying to unify different bounds"
  prettyError TypeConMismatch = "Trying to unify different types"
  prettyError DataConMismatch = "Trying to unify different constructors"
  prettyError NameTypeMismatch = "Trying to unify variables of different kinds"
  prettyError (UnsupportedVars nm s nm1 t) = "Unsupported variable unification between \{show nm}: \{show s} and \{show nm1}: \{show t}"
  prettyError VarNonVar = "Trying to unify local variable with non-variable"
  prettyError (PrimNE c c1) = "Trying to unify two non-equal constants: {show c} and {show c1}"
  prettyError BrokenInvariant = "Broken invariant (this should never appear)"
  prettyError UnsupportedUnification = "Unsupported unification"

  dumpStack : UStack -> String
  dumpStack [] = ""
  dumpStack (x :: xs) = "\{show x}\n" ++ dumpStack xs


public export
record UnificationError where
  constructor MkUniE
  task : UnificationTask
  stack : UStack
  kind : ErrorKind


public export
dumpError : UnificationError -> String
dumpError ue = "Error: \{prettyError @{ue.task} ue.kind}.\nStack trace: \n\{dumpStack @{ue.task} ue.stack}"

public export
UMonadError : (Type -> Type) -> Type
UMonadError = MonadError UnificationError

public export
UEitherT :  (Type -> Type) -> Type -> Type
UEitherT = EitherT UnificationError

public export
UnificationResult : Type -> Type
UnificationResult = Either UnificationError

parameters {auto task: UnificationTask}
  public export
  mkErr : MonadReader UStack m => ErrorKind -> m UnificationError
  mkErr kind = pure $ MkUniE task !(ask) kind

  public export
  throwUErr : MonadReader UStack m => UMonadError m => ErrorKind -> m t
  throwUErr kind = throwError =<< mkErr kind
