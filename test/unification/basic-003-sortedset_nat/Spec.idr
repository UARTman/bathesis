module Spec

import Language.Reflection.Monomorphisation

import Data.SortedSet

%language ElabReflection

failing
  %runElab monomorphise (SortedSet Nat) "SortedSetNat"

NoCast : MonoOpts
NoCast = { deriveCastMToP := False, deriveCastPToM := False } DefaultOpts

%runElab monomorphise {opts=NoCast} (SortedSet Nat) "SortedSetNat"


main : IO ()
main = putStrLn "ok"
