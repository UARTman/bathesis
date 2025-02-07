module Language.Reflection.QuoteInfo

import Language.Reflection
import Language.Reflection.Pretty
import Language.Reflection.Util
import Language.Reflection.Types
import Language.Reflection.TT
import Language.Reflection.TTImp
import Language.Reflection.Syntax
import Language.Reflection.Syntax.Ops
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Reader

%default total

export
data QuoteInfoT : (m : Type -> Type) -> (a : Type) -> Type where
  MkQuoteInfoT : (ReaderT Bool m a) -> QuoteInfoT m a

unwrapQuoteInfoT : QuoteInfoT m a -> ReaderT Bool m a
unwrapQuoteInfoT (MkQuoteInfoT r) = r


public export
runQuoteInfoT : Bool -> QuoteInfoT m a -> m a
runQuoteInfoT b (MkQuoteInfoT r) = runReaderT b r

public export
implementation Functor m => Functor (QuoteInfoT m) where
  map f (MkQuoteInfoT g) = MkQuoteInfoT $ map f g


public export
implementation Applicative f => Applicative (QuoteInfoT f) where
  pure x = MkQuoteInfoT $ MkReaderT $ \_ => pure x

  MkQuoteInfoT f <*> MkQuoteInfoT a = MkQuoteInfoT $ f <*> a


helper : (a -> QuoteInfoT m b) -> a -> ReaderT Bool m b
helper f a = unwrapQuoteInfoT $ f a

public export
implementation Monad m => Monad (QuoteInfoT m) where
  MkQuoteInfoT (MkReaderT f) >>= k =
    let k' = helper k in MkQuoteInfoT $ MkReaderT $ \st => f st >>= runReaderT st . k'

public export
implementation MonadTrans (QuoteInfoT) where
  lift x = MkQuoteInfoT $ MkReaderT $ \_ => x

public export
implementation HasIO m => HasIO (QuoteInfoT m) where
  liftIO f = MkQuoteInfoT $ MkReaderT $ \_ => liftIO f

public export
implementation Alternative f => Alternative (QuoteInfoT f) where
  empty = MkQuoteInfoT $ MkReaderT $ const empty

  MkQuoteInfoT (MkReaderT f) <|> mg = MkQuoteInfoT $ MkReaderT $ \st => f st <|> runReaderT' (unwrapQuoteInfoT mg) st

public export
interface Monad m => MonadReadQuoteInfo m | m where
  isQuote : m Bool

export
implementation Monad m => MonadReadQuoteInfo (QuoteInfoT m) where
  isQuote = MkQuoteInfoT ask

public export
interface MonadReadQuoteInfo m => MonadWriteQuoteInfo m where
    setIsQuote : Bool -> m a -> m a

export
implementation Monad m => MonadWriteQuoteInfo (QuoteInfoT m) where
    setIsQuote b (MkQuoteInfoT r) = MkQuoteInfoT $ local (\_ => b) r

export
implementation MonadTrans m => MonadReadQuoteInfo m'  => Monad (m m') => MonadReadQuoteInfo (m m') where
    isQuote = lift isQuote

-- export
-- implementation MonadTrans m => MonadWriteQuoteInfo m' => Monad (m m') => MonadWriteQuoteInfo (m m') where
--     setIsQuote b q = lift ?rhs

public export
provideQuoteInfo :
  MonadWriteQuoteInfo m =>
  (TTImp -> m TTImp -> m TTImp) ->
  TTImp -> m TTImp -> m TTImp
provideQuoteInfo f b@(IQuote fc t) newM = f b $ setIsQuote True newM
provideQuoteInfo f b@(IQuoteDecl fc decls) newM = f b $ setIsQuote True newM
provideQuoteInfo f b@(IUnquote fc t) newM = f b $ setIsQuote False newM
provideQuoteInfo f b newM = f b newM
