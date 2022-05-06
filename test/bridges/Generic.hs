module Generic where

import Data.Map as Map


import Agda.Utils.Pretty
import Agda.Syntax.Builtin
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Primitive

import Agda.Interaction.Options

-- runTCM ::
--   Control.Monad.IO.Class.MonadIO m =>
--   TCEnv -> TCState ->     TCMT m a     -> m (a, TCState)
--                           TCM a


        -- builtin = Map.toAscList $ iBuiltin i      :: [( String , Builtin (String, QName))]
        -- prim    = [ x | (_,Prim x) <- builtin ]   :: [(String, QName)]

        -- rebind (x, q) = do
        --     PrimImpl _ pf <- lookupPrimitiveFunction x
        --     stImportedBuiltins `modifyTCLens` Map.insert x (Prim pf{ primFunName = q })

main :: IO()
main = do
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
