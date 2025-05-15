module Spec

import Language.Reflection.Monomorphisation
%logging "monomorphiser" 10

%language ElabReflection

data TestCtx : Type where
  TCE : TestCtx
  

data Tag' : (uc: TestCtx) => (t : Type) -> Type where
  MkTag' : (uc: TestCtx) => Origin -> t -> Tag' t
--
--
%runElab monomorphise (\uc=>Tag' @{uc} Nat) "TagNat"

Tc : TestCtx
Tc = TCE

t1 : TagNat Tc
t1 = MkTag' Left @{Tc} 1

failing
  t5 : TagNat Tc
  t5 = MkTag' @{Tc} Left "5"
--
main : IO ()
main = putStrLn "ok"
