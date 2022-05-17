module Generic where

import Data.Map as Map
import qualified Data.HashMap.Strict as HMap

import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.Except

import qualified Agda.Utils.Pretty as P
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Syntax.Builtin
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Pretty

import Agda.Interaction.Options
import Agda.Compiler.Backend
-- import Agda.Compiler.JS.Pretty (render)
import Agda.Main


-- | checks the agda file spec in argument. We are now in a nice TCState.
beInNiceTCState :: String -> TCM ()
beInNiceTCState afilepath = do
  conf <- liftIO $ runExceptT $ do
    (bs, opts) <- ExceptT $ runOptM $ parseBackendOptions [] [] $ defaultOptions {optInputFile = Just afilepath}
    -- The absolute path of the input file, if provided
    inputFile <- liftIO $ mapM absolute $ optInputFile opts
    mode      <- getMainMode [] inputFile opts
    return (opts, mode)
  case conf of
    Left err -> liftIO $ optionError err
    Right (opts, mode) -> do
      case mode of
        MainModePrintHelp hp   -> liftIO $ printUsage [] hp
        MainModePrintVersion   -> liftIO $ printVersion []
        MainModePrintAgdaDir   -> liftIO $ printAgdaDir
        MainModeRun interactor -> do
          setTCLens stBackends []
          runAgdaWithOptions interactor "myscript" opts

{-
Tools for displaying internal info

- @import Agda.Utils.Pretty as P@ contains functions for pure Doc s.
  For instance text :: String -> Doc. Or render :: Doc -> String.

- @import Agda.TypeChecking.Pretty@ contains functions with effectful Doc s
  prettyTCM :: a -> m Doc
-}

printInTCM :: Doc -> TCM ()
printInTCM adoc = do
  liftIO $ putStrLn $ P.render adoc

endOfMain :: TCM ()
endOfMain = do
  printInTCM $ P.text "\nend of main"


-- | there are nice lenses to inspect TCState, near Monad.Base.stTokens
main :: IO ()
main = runTCMPrettyErrors $ do
  beInNiceTCState "/home/antva/Documents/repos/agda-fork/test/bridges/All.agda"

  showTheImports
  
  endOfMain




-------------- what we can put in main.

showThePragmaOptions :: TCM ()
showThePragmaOptions = do
  tcs <- getTCState
  let pragmas = tcs ^. stPragmaOptions
  liftIO $ putStrLn $ show $ pragmas


tryGetBasicBuiltin :: TCM ()
tryGetBasicBuiltin = do
  levelTm <- getBuiltin builtinLevel
  levelDoc <- prettyTCM levelTm
  printInTCM $ levelDoc

tryShowBasicTerm :: TCM ()
tryShowBasicTerm = do
  smTm <- primBPartial <@> primByes
  printInTCM =<< prettyTCM smTm

-- | the functions defined and imported by checked agda files. 
showTheImports :: TCM ()
showTheImports = do
  tcs <- getTCState
  let qnames = HMap.keys (tcs ^. stImports ^. sigDefinitions)
  printInTCM $ P.pretty qnames 
