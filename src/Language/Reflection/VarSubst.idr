module Language.Reflection.VarSubst

import Language.Reflection.QuoteInfo
import Language.Reflection.ShadowingInfo
import Language.Reflection.TTImp
import Control.Monad.Identity
import Data.SortedSet

substituteVariablesImpl :
  MonadReadQuoteInfo m => MonadReadShadowingInfo m =>
  Name -> TTImp -> TTImp -> m TTImp -> m TTImp
substituteVariablesImpl nm r (IVar fc nm1) m =
  if ((not !isQuote)
    && (not !(varIsShadowed nm1))
    && (nm == nm1))
    then pure r
    else m
substituteVariablesImpl nm r t m = m

substituteVariablesN :
  Name -> TTImp -> TTImp ->
  ShadowingInfoT (QuoteInfoT (Identity)) TTImp ->
  ShadowingInfoT (QuoteInfoT (Identity)) TTImp
substituteVariablesN n t =
  provideShadowingInfo $
  provideQuoteInfo $
  substituteVariablesImpl n t

public export
substituteVariables : Name -> TTImp -> TTImp -> TTImp
substituteVariables n t =
  runIdentity .
  runQuoteInfoT False .
  runShadowingInfoT empty .
  mapATTImp' (substituteVariablesN n t)

public export
substituteVariables' : (isQuote : Bool) -> (shadowedNames : SortedSet Name) -> Name -> TTImp -> TTImp -> TTImp
substituteVariables' isQuote shadowedNames n t =
  runIdentity . runQuoteInfoT isQuote . runShadowingInfoT shadowedNames . mapATTImp' (substituteVariablesN n t)


tSimpleTest : TTImp
tSimpleTest = substituteVariables `{a} `(x - 1) `(a + b + (let a = 10 in (x - a)))
