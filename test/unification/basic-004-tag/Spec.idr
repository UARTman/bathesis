module Spec

import Language.Reflection.Monomorphisation

%language ElabReflection


%runElab monoVariant "Tag" [Nothing, Just (Type ** Nat)] "TagNat"

uc : UnificationCtx
uc = MkUC `(Type) empty `(Type) empty

t1 : TagNat {uc}
t1 = MkTag {uc} Left 1

t2 : TagNat {uc}
t2 = MkTag {uc} Right 10

parameters {uc : UnificationCtx}
  t3 : TagNat
  t3 = MkTag Right 45

%hint
uc' : UnificationCtx
uc' = MkUC `(String) empty `(String) empty

t4 : TagNat
t4 = MkTag Left 5

failing
  t5 : TagNat
  t5 = MkTag Left "5"

main : IO ()
main = putStrLn "ok"
