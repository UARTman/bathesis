module Spec

import Language.Reflection.Monomorphisation

%language ElabReflection

%runElab monomorphise (\uc=>Tag @{uc} Nat) "TagNat"

uc : UnificationCtx
uc = MkUC `(Type) empty `(Type) empty

t1 : TagNat uc
t1 = MkTag {uc} Left 1

t2 : TagNat {uc}
t2 = MkTag {uc} Right 10

parameters {uc : UnificationCtx}
  t3 : TagNat uc
  t3 = MkTag Right 45

failing
  t5 : TagNat uc
  t5 = MkTag Left "5"

main : IO ()
main = putStrLn "ok"
