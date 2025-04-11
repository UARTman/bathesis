module Language.Reflection.VarSubst

import public Language.Reflection.QuoteInfo
import public Language.Reflection.ShadowingInfo
import public Language.Reflection.TTImp
import public Control.Monad.Identity
import public Control.Monad.State
import public Data.SortedSet


public export
containsVariableImpl : MonadReadQuoteInfo m => MonadReadShadowingInfo m => MonadState Bool m => Name -> TTImp -> m TTImp -> m TTImp
containsVariableImpl n (IVar _ n') m =
  if (n == n') then do
    put True
    m
  else m
containsVariableImpl n tt m = m

public export
containsVariableN : Name -> TTImp -> ShadowingInfoT (QuoteInfoT (State Bool)) TTImp -> ShadowingInfoT (QuoteInfoT (State Bool)) TTImp
containsVariableN n = provideShadowingInfo $ provideQuoteInfo $ containsVariableImpl n

public export
containsVariable : Name -> TTImp -> Bool
containsVariable n = fst . runState False . runQuoteInfoT False . runShadowingInfoT empty . mapATTImp' (containsVariableN n)

substituteVariablesImpl :
  MonadReadQuoteInfo m => MonadReadShadowingInfo m =>
  SortedMap Name TTImp -> TTImp -> m TTImp -> m TTImp
substituteVariablesImpl vMap (IVar fc nm1) m = 
  if ((not !isQuote) && (not !(varIsShadowed nm1))) then fromMaybe m $ pure <$> lookup nm1 vMap else m
substituteVariablesImpl _ _ m = m

--substituteVariablesImpl :
--  MonadReadQuoteInfo m => MonadReadShadowingInfo m =>
--  Name -> TTImp -> TTImp -> m TTImp -> m TTImp
--substituteVariablesImpl nm r (IVar fc nm1) m =
--  if ((not !isQuote)
--    && (not !(varIsShadowed nm1))
--    && (nm == nm1))
--    then pure r
--    else m
--substituteVariablesImpl nm r t m = m

substituteVariableN :
  Name -> TTImp -> TTImp ->
  ShadowingInfoT (QuoteInfoT (Identity)) TTImp ->
  ShadowingInfoT (QuoteInfoT (Identity)) TTImp
substituteVariableN n t =
  provideShadowingInfo $
  provideQuoteInfo $
  substituteVariablesImpl $ insert n t $ empty

substituteVariablesN : SortedMap Name TTImp -> TTImp -> ShadowingInfoT (QuoteInfoT Identity) TTImp -> ShadowingInfoT (QuoteInfoT Identity) TTImp
substituteVariablesN  = provideShadowingInfo . provideQuoteInfo . substituteVariablesImpl 

public export
substituteVariable : Name -> TTImp -> TTImp -> TTImp
substituteVariable n t =
  runIdentity .
  runQuoteInfoT False .
  runShadowingInfoT empty .
  mapATTImp' (substituteVariableN n t)

public export
substituteVariables : SortedMap Name TTImp -> TTImp -> TTImp
substituteVariables vMap =
  runIdentity .
  runQuoteInfoT False .
  runShadowingInfoT empty .
  mapATTImp' (substituteVariablesN vMap)

public export
substituteVariable' : (isQuote : Bool) -> (shadowedNames : SortedSet Name) -> Name -> TTImp -> TTImp -> TTImp
substituteVariable' isQuote shadowedNames n t =
  runIdentity . runQuoteInfoT isQuote . runShadowingInfoT shadowedNames . mapATTImp' (substituteVariableN n t)

public export
substituteVariables' : (isQuote : Bool) -> (shadowedNames : SortedSet Name) -> SortedMap Name TTImp -> TTImp -> TTImp
substituteVariables' isQuote shadowedNames vMap =
  runIdentity . runQuoteInfoT isQuote . runShadowingInfoT shadowedNames . mapATTImp' (substituteVariablesN vMap)


tSimpleTest : TTImp
tSimpleTest = substituteVariable `{a} `(x - 1) `(a + b + (let a = 10 in (x - a)))
