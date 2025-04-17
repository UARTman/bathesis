module Spec

import Language.Reflection.Monomorphisation

import Data.SortedSet

%language ElabReflection


%runElab monoVariant "SortedSet" [Just (Type ** Nat)] "SortedSetNat"


main : IO ()
main = putStrLn "ok"
