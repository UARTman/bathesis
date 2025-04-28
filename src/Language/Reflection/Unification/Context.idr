module Language.Reflection.Unification.Context

import public Language.Reflection
import public Language.Reflection.VarSubst -- TODO: refactor that too
import public Data.SortedSet
import public Data.SortedMap
import public Control.Monad.Reader

import public Derive.Prelude

%language ElabReflection

public export
FreeVars : Type
FreeVars = SortedMap Name TTImp

public export
record UnificationTask where
  constructor MkTask
  lhs : TTImp
  lhsVars : FreeVars
  rhs : TTImp
  rhsVars : SortedMap Name TTImp

%name UnificationTask task

%runElab derive "UnificationTask" [Show, Eq]

||| Origin of data (left- or right-hand side)
public export
data Origin = Left | Right

%runElab derive "Origin" [Show, Eq]

public export
record Tag {auto task: UnificationTask} (t : Type) 

parameters {auto task: UnificationTask}
  public export
  Show t => Show (Tag t)

  public export
  data UStep : Type where
    SubUnification : (lhs : Tag TTImp) -> (rhs : Tag TTImp) -> UStep
    MergeBuckets : Nat -> Nat -> UStep
    VarEqVar : Tag Name -> Tag Name -> UStep
    VarEqExpr : Tag Name -> Tag TTImp -> UStep

  public export
  Show UStep where
    show (SubUnification lhs rhs) = "Unifying sub-expressions: \{show lhs} = \{show rhs}"
    show (MergeBuckets k j) = "Merging buckets: \{show k} <- \{show j}" -- TODO: Bucket merging should show bucket data
    show (VarEqVar x y) = "Adding equation: \{show x} === \{show y}"
    show (VarEqExpr x y) = "Adding equation: \{show x} :== \{show y}"

  public export
  UStack : {auto task: UnificationTask} -> Type
  UStack = List UStep

public export
record Tag {auto task: UnificationTask} (t : Type) where
  constructor MkTag
  origin: Origin
  stack : UStack
  inner: t

parameters {auto task: UnificationTask}
  public export
  Eq t => Eq (Tag t) where
    (==) (MkTag o _ x) (MkTag o' _ y) = o == o' && x == y

  public export
  Show t => Show (Tag t) where
    show (MkTag Left _ x) = "tagLeft \{show x}"
    show (MkTag Right _ x) = "tagRight \{show x}"

  public export
  Ord t => Ord (Tag t) where
    compare (MkTag Left _ x) (MkTag Left _ y) = compare x y
    compare (MkTag Left _ _) (MkTag Right _ _) = LT
    compare (MkTag Right _ _) (MkTag Left _ _) = GT
    compare (MkTag Right _ x) (MkTag Right _ y) = compare x y

  public export
  Functor Tag where
    map f (MkTag o st x) = MkTag o st $ f x

  public export
  tagLeft : MonadReader UStack m => t -> m $ Tag t
  tagLeft x = pure $ MkTag Left !(ask) x

  public export
  tagRight : MonadReader UStack m => t -> m $ Tag t
  tagRight x = pure $ MkTag Right !(ask) x

  public export
  mkTag : MonadReader UStack m => Origin -> t -> m $ Tag t
  mkTag o x = pure $ MkTag o !(ask) x

  public export
  tagLeft': t -> Tag t
  tagLeft' = MkTag Left []

  public export
  tagRight' : t -> Tag t
  tagRight' = MkTag Right []

  public export
  (.same) : Tag t -> g -> Tag g
  (.same) (MkTag o st _) x = MkTag o st x

  public export
  (-|>) : Tag t -> g -> Tag g
  (-|>) = (.same)

  public export
  (.data) : Tag t -> t
  (.data) = (.inner)

  -- Free variables
  ||| Access free variables, available from the context
  public export
  (.freeVars) : Tag t -> FreeVars
  (.freeVars) (MkTag Left _ _) = task.lhsVars
  (.freeVars) (MkTag Right _ _) = task.rhsVars

  ||| Check if a name with origin metadata refers to a free variable
  public export
  (.isFreeVar) : Tag Name -> Bool
  (.isFreeVar) dt = isJust $ lookup dt.data dt.freeVars

  ||| Check if an expression with origin metadata is a free variable invocation
  public export
  (.isFreeVar') : Tag TTImp -> Bool
  (.isFreeVar') dt@(MkTag __ (IVar _ y)) = isJust $ lookup y dt.freeVars
  (.isFreeVar') _ = False

  ||| List all the free variables an origin-tagged expression depends on
  public export
  dependencies : Tag TTImp -> SortedSet Name
  dependencies dt =
    fromList .
    filter (\a => containsVariable a dt.data) .
    keys .
    (.freeVars) $
    dt

  ||| List all the free variables an origin-tagged expression depends on
  public export
  (.dependencies) : Tag TTImp -> SortedSet Name
  (.dependencies) = dependencies
