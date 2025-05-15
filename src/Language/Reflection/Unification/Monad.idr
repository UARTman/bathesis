module Language.Reflection.Unification.Monad

import public Language.Reflection
import public Language.Reflection.Unification.Context
import public Language.Reflection.Unification.Error
import public Language.Reflection.Unification.State
import public Control.Monad.Reader
import public Control.Monad.State

parameters {auto task: UnificationTask}
  public export
  UnificationT : (m : Type -> Type) -> Type -> Type
  UnificationT m = UEitherT $ ReaderT UStack $ UStateT m

  public export
  Unification : Type -> Type
  Unification = UnificationT Elab

  public export
  MonadUni : (Type -> Type) -> Type
  MonadUni m = (UMonadError m, MonadReader UStack m, MonadUState m, Elaboration m)

  public export
  tryElab : MonadUni m => String -> Elab t -> m t
  tryElab errMsg e = do
    elabRes <- catch e
    case elabRes of
      Nothing => throwUErr $ ElabFailed errMsg
      Just r => pure r

  public export
  runUni : UnificationState -> UnificationT m t -> m (UnificationState, Either UnificationError t)
  runUni s = runStateT s . runReaderT [] . runEitherT

  public export
  evalUni : Functor m => UnificationState -> UnificationT m t -> m $ Either UnificationError t
  evalUni s = evalStateT s . runReaderT [] . runEitherT

