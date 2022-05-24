module Generic where

import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Text hiding (filter, head, map, last)

import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.Except

import qualified Agda.Utils.Pretty as P
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Syntax.Common
import Agda.Syntax.Builtin
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Conversion

import Agda.Interaction.Options
-- import Agda.Interaction.Options.Base
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

printInTCMnice :: PrettyTCM a => a -> TCM ()
printInTCMnice x = do
  tmp <- prettyTCM x -- ::Doc. may use the context to render.
  printInTCM tmp

endOfMain :: TCM ()
endOfMain = do
  printInTCM $ P.text "\nend of main"

-- | the functions defined and imported by checked agda files. 
showTheImports :: TCM ()
showTheImports = do
  tcs <- getTCState
  let qnames = HMap.keys (tcs ^. stImports ^. sigDefinitions)
  printInTCM $ P.pretty qnames



showThePragmaOptions :: TCM ()
showThePragmaOptions = do
  tcs <- getTCState
  let pragmas = tcs ^. stPragmaOptions
  liftIO $ putStrLn $ show $ pragmas


-- | we specify part of the unqualified agda name. It yields a qname of an import containing the former.
--   case wordsBy (`elem` (":." :: String)) s
getQNameFromHuman :: String -> TCM QName
getQNameFromHuman hname = do
  tcs <- getTCState
  let qnames = HMap.keys (tcs ^. stImports ^. sigDefinitions)
      qnames' = map (\qnam -> (last $ wordsBy (`elem` ("." :: String)) (P.prettyShow qnam)) == hname) qnames
  return $ head $ filter (\qnam -> (last $ wordsBy (`elem` ("." :: String)) (P.prettyShow qnam)) == hname) qnames
                            -- (pack hname) `isSuffixOf` (pack $ P.render $ P.pretty q)) qnames

getDefFromQName :: QName -> TCM Definition
getDefFromQName qnam = do
  tcs <- getTCState
  let qsToDefs = tcs ^. stImports ^. sigDefinitions
  case HMap.lookup qnam qsToDefs of
    Just def -> return def
    _        -> typeError $ GenericError "no defs for that Qname!!"

getDefFromHuman :: String -> TCM Definition
getDefFromHuman hname = getDefFromQName =<< getQNameFromHuman hname

getDefnFromHuman :: String -> TCM Defn
getDefnFromHuman hname = do
  hnameDef <- getDefFromQName =<< getQNameFromHuman hname
  return $ theDef hnameDef


-- | from human name, we pretty print the bound-in-imports Defn
printDefn :: String -> TCM ()
printDefn hname = do
  hnameDef <- getDefFromQName =<< getQNameFromHuman hname
  printInTCM $ P.pretty $ P.text $ "Printing Defn..."
  printInTCM $ P.pretty $ defName hnameDef
  printInTCM $ P.text ""
  printInTCM $ P.pretty $ defType hnameDef
  printInTCM $ P.text ""
  printInTCM $ P.pretty $ theDef hnameDef

printTheEnvCtx :: TCM ()
printTheEnvCtx = do
  tce <- askTC
  let ctx = tce ^. eContext
  printInTCM $ P.pretty ctx

newline :: TCM ()
newline = do
 printInTCM $ P.text $ ""



-- | from a human name we get a @Monad.Base.Defn@ which may contain clauses and @Term@s.
getDefn :: String -> TCM Defn
getDefn hname = do
  hnameDef0 <- getDefFromQName =<< getQNameFromHuman hname -- ::Definition
  return $ hnameDef0 ^. theDefLens -- ::Defn

-- | from human name, gets you a @Internal.Clause@ if input is one line function.
getOnlyClause :: String -> TCM (Maybe Clause)
getOnlyClause hname = do
  hnameDefn <- getDefn hname
  case hnameDefn of
    Function{funClauses = [onlyCs]} -> return $ Just onlyCs
    _ -> do
      typeError $ GenericError $ "The human name " ++ hname ++ " does not map to a 1clause Function ::Defn."
      return $ Nothing
      -- printInTCM $ "The human name " <+> hname <+> " does not map to a 1clause Function ::Defn."

-- | tc.conv.comparebdgface:30
addVerb :: String -> TCM ()
addVerb verb = do
  tcs <- getTCState
  let theopts = tcs ^. stPragmaOptions -- ::PragmaOptions
      mopt = runExcept $ verboseFlag verb theopts -- Either String PragmaOptions
  case mopt of
    Left s -> typeError $ GenericError s
    Right o ->
      setTCLens stPragmaOptions o --we overwrite but @o@ is just an extended dic.
  return ()



---------------------- main



-- | there are nice lenses to inspect TCState, near Monad.Base.stTokens. (first: getTCState)
--   and lenses to inspect TCEnv, near eContext. (first: askTC)
--   seems that @Internal.Term@s resulting from tc can be inspected via stPostScopeState
main :: IO ()
main = runTCMPrettyErrors $ do
  beInNiceTCState "./All.agda"

  printDefn "premulti1"
  newline
  printDefn "premulti2"
  newline
  
  testingConversion3
  
  endOfMain







-------------- random testing

-- @Monad.Base.PragmaOptions@ has a field @optVerbose :: Verbosity@
-- can manipulate this with @verboseFlag :: String -> Flag PragmaOptions@ ?




tryGetBasicBuiltin :: TCM ()
tryGetBasicBuiltin = do
  levelTm <- getBuiltin builtinLevel
  levelDoc <- prettyTCM levelTm
  printInTCM $ levelDoc

tryShowBasicTerm :: TCM ()
tryShowBasicTerm = do
  smTm <- primBPartial <@> primByes
  printInTCM =<< prettyTCM smTm



showTheImports' :: TCM ()
showTheImports' = do
  tcs <- getTCState
  let qnames = HMap.keys (tcs ^. stImports ^. sigDefinitions)
      keyQ :: QName
      keyQ = head $ filter (\q -> (pack "toDec") `isSuffixOf` (pack $ P.render $ P.pretty q)) qnames
  printInTCM $ P.text $ show keyQ


showTheConcreteNames :: TCM ()
showTheConcreteNames = do
  tcs <- getTCState
  let themap = tcs ^. stConcreteNames -- Map Name C.Name
  printInTCM $ P.text $ show $  themap

  

experimentWithToDec :: TCM ()
experimentWithToDec = do
  toDecQ <- getQNameFromHuman "toDec"
  toDecDef <- getDefFromQName toDecQ
  printInTCM =<< prettyTCM (defName toDecDef)
  printInTCM =<< prettyTCM (defType toDecDef)
  printInTCM $ P.pretty $ theDef toDecDef


-- | it is stated that TCEnv is read only. Is that really true?
--   yes. locallyTC gives a new TCM, instead of mutating somehting.
understandLocallyTC :: TCM ()
understandLocallyTC = do
  toDecQ <- getQNameFromHuman "toDec"
  let
    nam = head $ qnameToList0 toDecQ
    somedom = defaultDom (nam , __DUMMY_TYPE__)
  bconj' <- locallyTC eContext (\ctx -> somedom : ctx ) primBConj
  printInTCM =<< prettyTCM bconj' --the showed term remains the same. what if we ask for db variable 0?

understandLocallyTC' :: TCM ()
understandLocallyTC' = do
  toDecQ <- getQNameFromHuman "toDec"
  let
    nam = head $ qnameToList0 toDecQ
    somedom = defaultDom (nam , __DUMMY_TYPE__)
    vartm = Var 0 []
  vartm' <- locallyTC eContext (somedom :) $ return vartm
  printInTCM =<< prettyTCM vartm'


petitTest :: TCM ()
petitTest = do
  Just toDecClause <- getOnlyClause "toDec"
  addContext (clauseTel toDecClause) $ do
    -- printTheEnvCtx
    printInTCM =<< prettyTCM (clauseBody toDecClause)
    printInTCM $ P.pretty $ ""
    printInTCMnice $ clauseBody toDecClause
    printInTCM $ P.pretty $ ""
    reduced <- reduce $ maybe __IMPOSSIBLE__ id $ clauseBody toDecClause
    printInTCMnice reduced

testingConversion :: TCM()
testingConversion = do
  addVerb "tc.conv.comparebdgface:30"

  cs2pre <-  getOnlyClause "bpartial2" 
  let cs2 = maybe __IMPOSSIBLE__ id $ cs2pre
  printInTCM $ P.pretty cs2
  printInTCM $ P.pretty $ clauseTel cs2

  cs1pre <- getOnlyClause "bpartial1"
  let cs1 = maybe __IMPOSSIBLE__ id $ cs1pre

  newline

  let thetype = maybe __IMPOSSIBLE__ unArg $ clauseType cs2
      cs1tm = maybe __IMPOSSIBLE__ id $ clauseBody cs1
      cs2tm = maybe __IMPOSSIBLE__ id $ clauseBody cs2

  addContext (clauseTel cs2) $ do
    printInTCMnice thetype
    printInTCMnice cs1tm
    printInTCMnice cs2tm

    equalTerm thetype cs1tm cs2tm

testingConversion2 :: TCM ()
testingConversion2 = do
  addVerb "tc.conv.comparebdgface:30"

  cs1pre <- getOnlyClause "hey"
  let cs1 = maybe __IMPOSSIBLE__ id $ cs1pre

  cs2pre <-  getOnlyClause "hey2" 
  let cs2 = maybe __IMPOSSIBLE__ id $ cs2pre

  let thetype = maybe __IMPOSSIBLE__ unArg $ clauseType cs2
      cs1tm = maybe __IMPOSSIBLE__ id $ clauseBody cs1
      cs2tm = maybe __IMPOSSIBLE__ id $ clauseBody cs2

  addContext (clauseTel cs2) $ do
    printInTCMnice thetype
    printInTCMnice cs1tm
    printInTCMnice cs2tm

    equalTerm thetype cs1tm cs2tm

testingConversion3 :: TCM ()
testingConversion3 = do
  addVerb "tc.conv.comparebdgface:30"

  cs1pre <- getOnlyClause "multi1"
  let cs1 = maybe __IMPOSSIBLE__ id $ cs1pre

  cs2pre <-  getOnlyClause "multi2" 
  let cs2 = maybe __IMPOSSIBLE__ id $ cs2pre  

  let thetype = maybe __IMPOSSIBLE__ unArg $ clauseType cs2
      cs1tm = maybe __IMPOSSIBLE__ id $ clauseBody cs1
      cs2tm = maybe __IMPOSSIBLE__ id $ clauseBody cs2

  addContext (clauseTel cs2) $ do
    printInTCMnice thetype
    printInTCMnice cs1tm
    printInTCMnice cs2tm
    printInTCM $ P.text ""

    equalTerm thetype cs1tm cs2tm







  --note: @underAbstractionAbs@ updates the ctx but also consider terms up to a certain substitution
  -- check out @TC.Monad.Context@, @TC.Substitute.Class@

-- -- | Modify the lens-indicated part of the @TCEnv@ in a subcomputation.
-- locallyTC :: MonadTCEnv m => Lens' a TCEnv -> (a -> a) -> m b -> m b
-- locallyTC l = localTC . over l

  

{-
best short at "declaring in .agda, working in .hs"

I can already be in a nice TCState with @beInNiceTCState@ above.
I can obtain a realistic QName (this include the file and position of the name ie "range") with @getGNameFromHuman@

But where are stored @Syntax.Internal.Term@'s once they have been typechecked??
I feel like they are in fact not stored anywhere and I have to retypecheck them. But then I need an @Syntax.Abstract.Expr@
and I don't know if I can obtain that based on the QName??
Also, @stImports@ ultimately gives @Definitions@. Can I obtain @Expr@'s from Definitions?
-}
