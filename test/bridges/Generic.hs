module Generic where

import Data.Map as Map
import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.Except

import Agda.Utils.Pretty
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Syntax.Builtin
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Primitive

import Agda.Interaction.Options
import Agda.Compiler.Backend
import Agda.Compiler.JS.Pretty (render)
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

-- | there are nice lenses to inspect TCState, near Monad.Base.stTokens
main :: IO ()
main = runTCMPrettyErrors $ do
  beInNiceTCState "/home/antva/Documents/repos/agda-fork/test/bridges/BridgePrims.agda"
  tcs <- getTCState
  let pOpts = tcs ^. stPragmaOptions
  liftIO $ putStrLn $ show $ pOpts




main3 :: IO()
main3 = do
  _ <- runTCM initEnv initState $ do
    smth <- getBuiltin builtinLevel
    -- levb <- getBuiltin builtinLevel
    -- levq <- getPrimitiveName' builtinLevel
    -- stImportedBuiltins `modifyTCLens` Map.insert builtinLevel (Prim pf
    -- stPragmaOptions `modifyTCLens` \ o -> o { optBridges = True }
    -- pi <- lookupPrimitiveFunction "primBPartial"
    return ()
  return ()

main2 :: IO ()
main2 = do
  -- setTCLens stImportedBuiltins
  _ <- runTCM initEnv initState $ do
    -- setBuiltinTHings $
    --   insert keyy elemm empty where
    --     keyy :: String
    --     keyy = builtinBHolds
    --     elemm :: Builtin PrimFun
    --     elemm = Prim
    q <- getPrimitiveName'  builtinBHolds
    atm <- primBHolds
    --string <- prettyShow atm
    return ()
  return ()
