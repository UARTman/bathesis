module GoldenRunner

import Control.ANSI

import Data.Colist
import Data.Cotree
import Data.Either
import Data.Maybe
import Data.List
import Data.List1
import Data.String
import Data.String.Extra


import System
import System.Clock
import System.Directory
import System.File
import System.Info
import System.Path
import System.Concurrency

import public Test.Golden
import public Language.Reflection

import Hedgehog.Internal.Config
import Hedgehog.Internal.Gen
import Hedgehog.Internal.Options
import Hedgehog.Internal.Property
import Hedgehog.Internal.Range
import Hedgehog.Internal.Report
import Hedgehog.Internal.Terminal
import Hedgehog.Internal.Runner

import System.Random.Pure
import System.Random.Pure.StdGen

export
test' : HasIO io => List Group -> io Bool
test' gs = do
  args    <- getArgs
  Right c <- pure $ applyArgs args
    | Left errs => do
        putStrLn "Errors when parsing command line args:"
        traverse_ putStrLn errs
        exitFailure
  if c.printHelp
     then putStrLn info >> exitSuccess
     else
       let gs2 := map (applyConfig c) gs
        in do
             res <- foldlM (\b,g => map (b &&) (checkGroup g)) True gs2
             pure $ not res

export
runnerWith' : Options -> List TestPool -> IO Nat
runnerWith' opts tests = do

         -- if no CG has been set, find a sensible default based on what is available
         opts <- case codegen opts of
                   Nothing => pure $ { codegen := !findCG } opts
                   Just _ => pure opts

         -- run the tests
         res <- concat <$> traverse (poolRunner opts) tests

         -- report the result
         let nsucc  = length res.success
         let nfail  = length res.failure
         let ntotal = nsucc + nfail
         putStrLn (show nsucc ++ "/" ++ show ntotal ++ " tests successful")

         -- deal with failures
         let list = fastUnlines res.failure
         when (nfail > 0) $
           do putStrLn "Failing tests:"
              putStr list
         -- always overwrite the failure file, if it is given
         whenJust opts.failureFile $ \ path =>
           do Right _ <- writeFile path list
                | Left err => die (show err)
              pure ()

         pure nfail

-- ||| A runner for a whole test suite
-- export
-- runner' : List TestPool -> IO ()
-- runner' tests
--     = do args <- getArgs
--          Just opts <- options args
--             | _ => do printLn args
--                       putStrLn usage
--          runnerWith' opts tests


public export
record BuildDir where
  constructor MkBuildDir
  buildDir : String

||| Determines which string will be passed as the first argument
||| to the `run` script of each test.
public export
interface RunScriptArg where
  constructor MkRunScriptArg
  runScriptArg : BuildDir => String

||| When no default argument is given, is passes a filename for "pack lock",
||| a file to be locked over when running `pack -q install-deps test.ipkg` using `flock`.
||| This is most useful when testing libraries, when only `pack` or `idris2` commands are used in tests.
public export
%defaulthint
DefaultRunScriptArg : RunScriptArg
DefaultRunScriptArg = R where
  [R] RunScriptArg where
    runScriptArg = buildDir %search ++ "/.pack_lock"

--- Options management ---

nproc : IO $ Maybe Nat
nproc = do
  rawThreads <- getEnv "NUM_THREADS"
  let Nothing = rawThreads >>= parsePositive
    | Just n => pure $ Just n
  (str, 0) <- run "nproc"
    | _ => pure Nothing
  pure $ parsePositive str

nproc' : IO Nat
nproc' = fromMaybe 1 . filter (> 0) <$> nproc

fitsPattern : (pattern, test : String) -> Bool
fitsPattern = isInfixOf

testOptions : RunScriptArg => BuildDir => IO Options
testOptions = do
  onlies <- filter (not . null) . tail' <$> getArgs
  pure $
    { color := isNothing !(getEnv "NO_COLOR")
    , timing := True
    , interactive := !((Just "true" /=) <$> getEnv "CI")
    , failureFile := Just "failures"
    , onlyNames := onlies <&> \patterns, test => any (`fitsPattern` test) patterns
    , threads := !nproc'
    } (initOptions runScriptArg True)

--- A universal way to set test pools from different origins ---

export
interface TestPoolLike a where
  toTestPool : a -> IO $ List TestPool

export
TestPoolLike (IO TestPool) where
  toTestPool = map pure

export
TestPoolLike TestPool where
  toTestPool = pure @{Compose}

export
TestPoolLike (List TestPool) where
  toTestPool = pure

export
TestPoolLike (IO $ List TestPool) where
  toTestPool = id

export
TestPoolLike (List $ IO TestPool) where
  toTestPool = sequence

export
data TestPools = MkTestPools (IO $ List TestPool)

namespace TestPools

  export
  Nil : TestPools
  Nil = MkTestPools $ pure []

  export
  (::) : TestPoolLike a => a -> TestPools -> TestPools
  x :: MkTestPools xs = MkTestPools [| toTestPool x ++ xs |]

  export
  (++) : TestPools -> TestPools -> TestPools
  MkTestPools xs ++ MkTestPools ys = MkTestPools [| xs ++ ys |]

toList : TestPools -> IO $ List TestPool
toList $ MkTestPools xs = xs

--- Facilities for user's convenience ---

export
atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = do
  True <- exists dir
    | False => emptyPool
  Right (_::_) <- listDir dir
    | _ => emptyPool
  testsInDir dir poolName {pred=not . isPrefixOf "_"}

  where
    emptyPool : IO TestPool
    emptyPool = pure $ MkTestPool poolName [] Nothing []

--- Toplevel running ---

export
goldenRunner' : RunScriptArg => (projectDir, buildDir : String) -> TestPools -> List Group -> IO ()
goldenRunner' projectDir buildDir tps lg = do
  putStrLn "Running hedgehog tests..."
  hedgehogFailed <- test' lg
  putStrLn "Running golden tests..."
  let _ = MkBuildDir buildDir
  ignore $ changeDir projectDir
  nGoldenFailed <- runnerWith' !testOptions !(toList tps)
  if hedgehogFailed 
    then putStrLn "Some hedgehog tests failed."
    else pure ()
  if not $ nGoldenFailed == 0
    then putStrLn "\{show nGoldenFailed} golden tests failed."
    else pure ()
  if hedgehogFailed || not (nGoldenFailed == 0)
    then exitFailure
    else exitSuccess
    


export %macro
goldenRunner : RunScriptArg => TestPools -> List Group -> Elab $ IO ()
goldenRunner tps lg = pure $ goldenRunner' !(idrisDir ProjectDir) !(idrisDir BuildDir) tps lg