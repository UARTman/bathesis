module Monomorphisation

import Language.Reflection.Monomorphisation

%language ElabReflection

%runElab monoVariant "List" [Just (Type ** String)] "ListString"

-- t : ()
-- t = %runElab monoVariant "List" [Just (Type ** String)] "ListString"

-- ls : ListString
-- ls =  ["1", "2", "3"]

-- %runElab monoVariant "Vect" [Nothing, Just (Type ** String)] "Vect_String"

-- -- lk : Vect_String 2
-- -- lk = ["4", "5"]

-- failing
--   lk' : Vect_String 3
--   lk' = []

-- failing
--   lk'' : Vect_String 3
--   lk'' = ["1", "2", "3", "4", "5"]

-- failing
--   lk''' : Vect_String 1
--   lk''' = [1,2,3]

-- %runElab monoVariant "Vect" [Just (Nat ** 3), Nothing] "Vect3"

-- %runElab monoVariant "SortedMap" [Just (Type ** String), Nothing] "SortedMapString"

-- ns : List Decl
-- ns = `[
--   data MyType : Type -> Type where
--     A : MyType Int
--     B : x -> MyType x
-- ]

-- nsd : List (Name, TTImp)
-- nsd = %runElab getType "SortedMap"
