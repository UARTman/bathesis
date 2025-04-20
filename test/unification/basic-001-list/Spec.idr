module Spec

import Language.Reflection.Monomorphisation

%language ElabReflection


%runElab monomorphise (List Nat) "ListNat"

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
