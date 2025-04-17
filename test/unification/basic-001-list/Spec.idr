module Spec

import Language.Reflection.Monomorphisation

%language ElabReflection


%runElab monoVariant "List" [Just (Type ** Nat)] "ListNat"

ln : ListNat
ln = [1,2,3]

failing
  ln' : ListNat
  ln' = ["x", "y", "z"]

failing
  ln' : ListNat
  ln' = [1, "2", "3"]

main : IO ()
main = putStrLn "ok"
