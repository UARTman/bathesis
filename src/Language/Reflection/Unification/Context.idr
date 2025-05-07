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
  UStack : Type
  UStack = List UStep

  public export
  AliasMap : Type
  AliasMap = SortedMap Name TTImp

public export
record Tag {auto task: UnificationTask} (t : Type) where
  constructor MkTag
  origin: Origin
  -- stack : UStack
  aliasMap : AliasMap
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
    map f (MkTag o am x) = MkTag o am $ f x

  public export
  tagLeft : MonadReader UStack m => t -> m $ Tag t
  tagLeft x = pure $ MkTag Left empty x

  public export
  tagRight : MonadReader UStack m => t -> m $ Tag t
  tagRight x = pure $ MkTag Right empty x

  public export
  mkTag : MonadReader UStack m => Origin -> AliasMap -> t -> m $ Tag t
  mkTag o am x = pure $ MkTag o am x

  public export
  tagLeft': t -> Tag t
  tagLeft' = MkTag Left empty

  public export
  tagRight' : t -> Tag t
  tagRight' = MkTag Right empty

  public export
  (.same) : Tag t -> g -> Tag g
  (.same) (MkTag o am _) x = MkTag o am x

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
  (.isFreeVar') dt@(MkTag _ _ (IVar _ y)) = isJust $ lookup y dt.freeVars
  (.isFreeVar') _ = False

  public export
  (.isAlias') : Tag TTImp -> Bool
  (.isAlias') dt@(MkTag _ am (IVar _ n)) = isJust $ lookup n am
  (.isAlias') _ = False

  public export
  (.unalias) : Tag TTImp -> Tag TTImp
  (.unalias) dt@(MkTag _ am (IVar _ n)) = 
    fromMaybe dt $ (.unalias) <$> dt.same <$> lookup n am
  (.unalias) dt@(MkTag t am (ILet _ _ _ n _ val scope)) = 
    (.unalias) $ MkTag t (insert n val am) scope
  (.unalias) dt = dt

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
