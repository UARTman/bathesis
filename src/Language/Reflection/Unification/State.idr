module Language.Reflection.Unification.State

import public Language.Reflection.Unification.Context
import public Language.Reflection.Unification.Error
import public Syntax.IHateParens
import public Control.Monad.State

(.toList) : SortedSet t -> List t
(.toList) = Prelude.toList

||| Infomration on a set of equivalent free variables
public export
record BucketData {auto task: UnificationTask} where
  constructor MkBD
  ||| All free variables in the set
  names : SortedSet $ Tag Name
  ||| The expression the set is equal to
  expr : Maybe $ Tag TTImp

public export
record UnificationState {auto task: UnificationTask} where
  constructor MkUS
  ||| Bucket id counter (incremented every new bucket)
  nextBucket : Nat
  ||| Variable sets
  buckets : SortedMap Nat BucketData
  ||| Name to set id map
  nameToBucket : SortedMap (Tag Name) Nat
  ||| Pairs of expressions equal to each other that we can't handle
  fords : List ((Tag TTImp, Tag TTImp))

parameters {auto task: UnificationTask}
  public export
  Show BucketData where
    show (MkBD n e) = "MkBD \{show n} \{show e}"

  public export
  Show UnificationState where
    show (MkUS n b nb fds) = "MkUS \{show n} \{show b} \{show nb} \{show fds}"

  public export
  empty : UnificationState
  empty = MkUS Z empty empty []

  ||| Refer all the variables in a list to the variable set
  public export
  transferVariables : List t -> Nat -> SortedMap t Nat -> SortedMap t Nat
  transferVariables vars bucket m
    = foldr (flip insert bucket) m vars

  ||| Find var set associtated with name, if any
  public export
  queryName : Tag Name -> UnificationState -> Maybe BucketData
  queryName n b = lookup n b.nameToBucket >>= flip lookup b.buckets

  public export
  setDataByName :
       Tag Name
    -> BucketData
    -> UnificationState
    -> UnificationState
  setDataByName n d state with (state.nameToBucket `lookup'` n)
    setDataByName _ _ state | Nothing = state
    setDataByName _ d state | (Just bid) = {buckets $= insert bid d} state


  public export
  addNewBucket : BucketData -> UnificationState -> UnificationState
  addNewBucket bd state =
    { nextBucket $= S
    , nameToBucket $= transferVariables bd.names.toList state.nextBucket
    , buckets $= flip insert bd state.nextBucket
    } state

  -- Redirect all variables listed in names to point at a instead of b,
  -- update a with newAData and delete b
  public export
  mergeIntoAndUpdate :
       Nat -> Nat
    -> List (Tag Name)
    -> BucketData
    -> UnificationState
    -> UnificationState
  mergeIntoAndUpdate a b names newAData =
    { nameToBucket $= transferVariables names a
    , buckets $= insert a newAData . delete b
    }

  public export
  MonadUState: (Type -> Type) -> Type
  MonadUState = MonadState UnificationState

  public export
  UStateT: (Type -> Type) -> Type -> Type
  UStateT = StateT UnificationState


  public export
  dumpBucket : BucketData -> String
  dumpBucket (MkBD names Nothing) =
    joinBy " == " $ show <$> names.toList
  dumpBucket (MkBD names (Just s)) =
    joinBy " == " $ map show names.toList ++ [show s]

  public export
  dumpUState : UnificationState -> String
  dumpUState s = joinBy "\n" $ dumpBucket <$> values s.buckets
