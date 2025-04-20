module Spec

import Language.Reflection.Monomorphisation
import Data.Vect

%language ElabReflection


%runElab monomorphise (\x=>Vect x Nat) "VectNat"

ln : VectNat 3
ln = [1,2,3]

ln' : VectNat 0
ln' = []

failing
  ln'' : VectNat 3
  ln'' = ["x", "y", "z"]

failing
  ln'' : VectNat 2
  ln'' = [1]

failing
  ln'' : VectNat 2
  ln'' = [1,2,3]

main : IO ()
main = putStrLn "foo"
