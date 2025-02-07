module Main

import Language.Reflection
import Language.Reflection.Pretty
import Language.Reflection.Util
import Language.Reflection.TTImp

import Language.Reflection.VarSubst

import Hedgehog

%language ElabReflection


justSubst : Property
justSubst = property1 $ do
  substituteVariables `{a} `(b) `(a) === `(b)

substOneButNotTheOther : Property
substOneButNotTheOther = property1 $ do
  substituteVariables `{a} `(b)
    `((x + a - 1) / (2 * a)) ===
    `((x + b - 1) / (2 * b))

substBigExpr : Property
substBigExpr = property1 $ do
  substituteVariables `{a} `(let a : Int; a = 10 in if a == 10 then x else y)
    `(a) === `(let a : Int; a = 10 in if a == 10 then x else y)

basicStuff : Group
basicStuff = MkGroup "Basic substitute functionality" [
  ("simplest substitution", justSubst),
  ("substitution in basic expressions", substOneButNotTheOther),
  ("variables can be substituted for big expressions", substBigExpr)
]

iPiArg : Property
iPiArg = property1 $ do
  substituteVariables `{a} `(b)
    `((a : Type) -> (x : a) -> Type) ===
    `((a : Type) -> (x : a) -> Type)

iPiArgImplicit : Property
iPiArgImplicit = property1 $ do
  substituteVariables `{a} `(b)
    `((a : Type) => (x : a) -> Type) ===
    `((a : Type) => (x : a) -> Type)

iPiArg' : Property
iPiArg' = property1 $ do
  substituteVariables `{a} `(b)
    `(Type -> (x : a) -> Type) ===
    `(Type -> (x : b) -> Type)

iLamN : Property
iLamN = property1 $ do
  substituteVariables `{x} `(z)
    `(\x: List x=>x+y) === `(\x: List z=>x+y)

iLet : Property
iLet = property1 $ do
  substituteVariables `{a} `(b)
    `(let a : List a = a in a) === `(let a : List b = b in a)

iCase: Property
iCase = property1 $ do
  substituteVariables `{a} `(b) `(case a of
    (Cat a b) => a b c d
    (Cat' d e) => a b c d
  ) === `(case b of
    (Cat a b) => a b c d
    (Cat' d e) => b b c d
  )

iLocalBasic: Property
iLocalBasic = property1 $ do
  substituteVariables `{a} `(b) `(
    let
      x : Int
      x = a 10
    in a x
  ) === `(
    let
      x : Int
      x = b 10
    in b x
  )
  substituteVariables `{a} `(b) `(
    let
      a : Int
      a = 10
    in a
  ) === `(
    let
      a : Int
      a = 10
    in a
  )

iDeclsFollowing : Property
iDeclsFollowing = property1 $ do
  substituteVariables `{a} `(b) `(
    let
      a : Nat
      a = 100

      b : Nat
      b = a
    in a
  ) === `(
    let
      a : Nat
      a = 100

      b : Nat
      b = a
    in a
  )

iPrivateDeclsLocal : Property
iPrivateDeclsLocal = property1 $ do
  substituteVariables `{a} `(b) `(
    let
      private
      a : Nat
      a = 100
    in a
  ) === `(
    let
      private
      a : Nat
      a = 100
    in a
  )


iPrivateDeclsInNS : Property
iPrivateDeclsInNS = property1 $ do
  substituteVariables `{a} `(b) `(
    let
    namespace Q
      private
      a : Nat
      a = 100
    in a
  ) === `(
    let
    namespace Q
      private
      a : Nat
      a = 100
    in b
  )

argsInDef : Property
argsInDef = property1 $ do
  substituteVariables `{a} `(b) `(
    let
      f : List a -> Type
      f _ = a
    in ?t
  ) === `(
    let
      f : List a -> Type
      f _ = a
    in ?t
  )


withClause : Property
withClause = property1 $ do
  substituteVariables `{a} `(b) `(
    let
      f : List t -> Nat
      f [] = 0
      f (x :: xs) with (x + a)
        f x | a = a
    in f [a]
  ) === `(
    let
      f : List t -> Nat
      f [] = 0
      f (x :: xs) with (x + b)
        f x | a = a
    in f [b]
  )


quoteSingle : Property
quoteSingle = property1 $ do
  substituteVariables `{a} `(b) `(`(a)) === `(`(a))

quoteMultiple : Property
quoteMultiple = property1 $ do
  substituteVariables `{a} `(b) `(`(`(a))) === `(`(`(a)))

quoteDecl : Property
quoteDecl = property1 $ do
  substituteVariables `{a} `(b) `(`[
    x : Nat
    x = a
  ]) === `(`[
    x : Nat
    x = a
  ])

unquoteInSingle : Property
unquoteInSingle = property1 $ do
  substituteVariables `{a} `(b)
    `(`(x + ~(IUnquote emptyFC `(a)))) ===
    `(`(x + ~(IUnquote emptyFC `(b))))


unquoteInMultiple : Property
unquoteInMultiple = property1 $ do
  substituteVariables `{a} `(b)
    `(`(`(x + ~(IUnquote emptyFC `(a))))) ===
    `(`(`(x + ~(IUnquote emptyFC `(b)))))

ttImpQualities : Group
ttImpQualities = MkGroup "TTImp"
  [ ("IPi explicit named argument shadows", iPiArg)
  , ("IPi implicit named argument shadows", iPiArgImplicit)
  , ("IPi unnamed argument doesn't shadow", iPiArg')
  , ("ILam shadowing works", iLamN)
  , ("ILet shadowing works", iLet)
  , ("ICase shadowing works", iCase)
  , ("ILocal's basic properties work", iLocalBasic)
  ]

declQualities : Group
declQualities = MkGroup "Decl"
  [ ("Pubic/private in local", iPrivateDeclsLocal)
  , ("Public/private in namespace", iPrivateDeclsInNS)
  , ("Visible in following decls", iDeclsFollowing)
  , ("Arguments in signature shadow IDef", argsInDef)
  ]

clauseQualities : Group
clauseQualities = MkGroup "Clause"
  [ ("With clause shadowing works", withClause)
  ]

quoteQualities : Group
quoteQualities = MkGroup "Quote"
  [ ("Single quote", quoteSingle)
  , ("Multiple quote", quoteMultiple)
  , ("Declaration quote", quoteDecl)
  , ("Unquote in single quote", unquoteInSingle)
  , ("Unquote in multiple quotes", unquoteInMultiple)
  ]

main : IO ()
main = do
  putStrLn "Running hedgehog tests..."
  test
    [ basicStuff
    , ttImpQualities
    , declQualities
    , clauseQualities
    , quoteQualities
    ]
