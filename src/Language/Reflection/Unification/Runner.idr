module Language.Reflection.Unification.Runner

import public Language.Reflection.Unification.Graph

public export
doUnification' : (task : UnificationTask) -> Unification $ (SortedMap Name TTImp, SortedMap Name TTImp)
doUnification' task = do
  unifyExpr (tagLeft' task.lhs) (tagRight' task.rhs)
  state <- get
  pure $ consolidateUState state

public export
doUnification : Elaboration m => List (Name, TTImp) -> TTImp -> List (Name, TTImp) -> TTImp -> m $ Either UnificationError (SortedMap Name TTImp, SortedMap Name TTImp)
doUnification lhsV lhs rhsV rhs = do
  let task = MkTask lhs (fromList lhsV) rhs (fromList rhsV)
  try (fail "") $ evalUni empty $ doUnification' task

doPretty : Elaboration m => List (Name, TTImp) -> TTImp -> List (Name, TTImp) -> TTImp -> m ()
doPretty lhsV lhs rhsV rhs = do 
  uniR <- doUnification lhsV lhs rhsV rhs
  case uniR of
    Left e => logMsg "unifier" 0 "Error: \{dumpError e}"
    Right res => logMsg "unifier" 0 "Success: \{show res}"
