module Generic where

import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Text hiding (filter, head, map, last, elem)

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
import Agda.TypeChecking.Substitute

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

getTheClause :: String -> TCM Clause
getTheClause hname = do
  mbCs <- getOnlyClause hname
  let cs = maybe __IMPOSSIBLE__ id $ mbCs
  return cs

getTheCtx :: String -> TCM Telescope
getTheCtx hname = do
  cs <- getTheClause hname
  return $ clauseTel cs


-- | from human name, gets you the term t :: Term
getTheTerm :: String -> TCM Term
getTheTerm hname = do
  mbCs <- getOnlyClause hname
  let mbTm = case mbCs of
        Nothing -> __IMPOSSIBLE__
        Just cs ->
          clauseBody cs
  return $ maybe __IMPOSSIBLE__ id $ mbTm

getTheType :: String -> TCM Type
getTheType hname = do
 cs <- (getTheClause hname)
 return $  maybe __IMPOSSIBLE__ unArg (clauseType cs)


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
  addVerb "antvascript:0"

  refoldingMhocom
  
  -- hocomGlue
  -- testMixedMeet
  -- decIntervalBotTop
  -- testMixedForall
  -- mpartialJudgEqu3
  
  endOfMain



-- main = runTCMPrettyErrors $ do
--   beInNiceTCState "./All.agda"

--   -- judgEquMixedCstr
--   bz <- primBIZero
--   case bz of
--     Def q es -> printInTCMnice "its a def"
--     Con h i es -> printInTCMnice "its a con"
--     _ -> __IMPOSSIBLE__
  
--   endOfMain



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

-- decomposeInterval :: HasBuiltins m => Term -> m [ (IntMap Bool, [Term]) ]
-- EX1: xyz ⊢ ~ x ∨ (y ∧ ~ z) ∨ i1
--      [  ([(2,False)],[])  , ([(0,False), (1,True)],[])  , ([],[])  ]
-- EX2: xyz ⊢ x ∧ (y ∨ z)
--      [  ([(1,True), (2,True)],[])  , ([(0,True), (2,True)],[])  ]
--      because x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)
understandDecomposeInterval :: TCM ()
understandDecomposeInterval = do
  mbToDecClause <- getOnlyClause "toDec2"
  case mbToDecClause of
    Nothing -> typeError $ GenericError "failed..."
    Just toDecClause -> do
      addContext (clauseTel toDecClause) $ do
        -- printTheEnvCtx
        let todectm :: Term
            todectm = maybe __IMPOSSIBLE__ id $ clauseBody toDecClause
        printInTCM $ P.pretty todectm
        newline
        decomp <- decomposeInterval todectm
        doc <- prettyTCM decomp
        printInTCM doc
    
    -- reduced <- reduce $ maybe __IMPOSSIBLE__ id $ clauseBody toDecClause
    -- printInTCMnice reduced
    
  -- todecPre <-  getOnlyClause "todec" 
  -- let todec = maybe __IMPOSSIBLE__ id $ todecPre
  -- printInTCM $ P.pretty todec
  -- printInTCM $ P.pretty $ clauseTel todec
  -- let todecTm = maybe __IMPOSSIBLE__ id $ clauseBody todec
  -- res <- decomposeInterval todecTm
  -- printInTCM $ P.pretty $ res
  -- return ()


-- understandDecomposeInterval2 :: TCM ()
--   view   <- intervalView'
--   unview <- intervalUnview'
--   let f :: IntervalView -> [[Either (Int,Bool) Term]]
--     f IZero = mzero -- []
--     f IOne  = return [] -- [[]]
--     f (IMin x y) = do xs <- (f . view . unArg) x; ys <- (f . view . unArg) y; return (xs ++ ys)
--     f (IMax x y) = msum $ map (f . view . unArg) [x,y]
--     f (INeg x)   = map (either (\ (x,y) -> Left (x,not y)) (Right . unview . INeg . argN)) <$> (f . view . unArg) x
--     f (OTerm (Var i [])) = return [Left (i,True)]
--     f (OTerm t)          = return [Right t]
      


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


reduceMixedCstr :: TCM ()
reduceMixedCstr = do
  printDefn "amixcstr"
  newline

  cs1pre <- getOnlyClause "amixcstr"
  let cs1 = maybe __IMPOSSIBLE__ id $ cs1pre

  let thetype = maybe __IMPOSSIBLE__ unArg $ clauseType cs1
      cs1tm = maybe __IMPOSSIBLE__ id $ clauseBody cs1

  addContext (clauseTel cs1) $ do
    printInTCMnice thetype
    printInTCMnice cs1tm
    newline

    red <- reduce cs1tm
    printInTCMnice red


judgEquMixedCstr :: TCM ()
judgEquMixedCstr = do
  printDefn "amixcstr"
  newline
  printDefn "mixcstr2"
  newline

  cs1pre <- getOnlyClause "amixcstr"
  let cs1 = maybe __IMPOSSIBLE__ id $ cs1pre
  cs2pre <- getOnlyClause "mixcstr2"
  let cs2 = maybe __IMPOSSIBLE__ id $ cs2pre

  let thetype = maybe __IMPOSSIBLE__ unArg $ clauseType cs1
      cs1tm = maybe __IMPOSSIBLE__ id $ clauseBody cs1
      cs2tm = maybe __IMPOSSIBLE__ id $ clauseBody cs2

  addContext (clauseTel cs1) $ do
    printInTCMnice thetype
    printInTCMnice cs1tm
    printInTCMnice cs2tm
    newline

    equalTerm  thetype cs1tm cs2tm

  --note: @underAbstractionAbs@ updates the ctx but also consider terms up to a certain substitution
  -- check out @TC.Monad.Context@, @TC.Substitute.Class@

-- -- | Modify the lens-indicated part of the @TCEnv@ in a subcomputation.
-- locallyTC :: MonadTCEnv m => Lens' a TCEnv -> (a -> a) -> m b -> m b
-- locallyTC l = localTC . over l


whatIsMzero :: [Bool]
whatIsMzero = mzero -- []


testMixedMeet :: TCM ()
testMixedMeet = do
  addVerb "tc.prim.bridges.hasEmptyMeet:50"
  
  m1Tel <- clauseTel <$> getTheClause "mcstr1"
  m1 <- getTheTerm "mcstr1"
  m2 <- getTheTerm "mcstr2"
  oppositeKind <- addContext m1Tel $ hasEmptyMeet m1 m2
  printInTCM $ (P.<+>)
    (P.text  "Pure constraints of oppositve kind have empty meet (expecting False): ")
    (P.pretty oppositeKind)

  notj <- getTheTerm "notj"
  yesi <- getTheTerm "yesi"
  notjyesi <- addContext m1Tel $ hasEmptyMeet notj yesi
  printInTCM $ (P.<+>)
    (P.text  "Pure constraints of same kind whose comp. intersect, have empty meet (expecting False): ")
    (P.pretty notjyesi)

  notr <- getTheTerm "notr"
  yess <- getTheTerm "yess"
  notryess <- addContext m1Tel $ hasEmptyMeet notr yess
  printInTCM $ (P.<+>)
    (P.text  "Same but with bridge kind (expecting False): ")
    (P.pretty notryess)

  noti <- getTheTerm "noti"
  yesr <- getTheTerm "yesr"

  notryesr <- addContext m1Tel $ hasEmptyMeet notr yesr
  notiyesi <- addContext m1Tel $ hasEmptyMeet noti yesi
  printInTCM $ (P.<+>)
    (P.text  "Pure constraints of same kind whose comp. dont intersect, have empty meet (expecting True): ")
    (P.pretty notiyesi)
  printInTCM $ (P.<+>)
    (P.text  "Same but with bridge kind (expecting True): ")
    (P.pretty notryesr)

decIntervalBotTop :: TCM ()
decIntervalBotTop = do
  i0 <- primIZero
  i1 <- primIOne
  dnfList0 <- decomposeInterval' i0
  dnfList1 <- decomposeInterval' i1
  reportSDocDocs "antvascript" 0
    (text "DNF of i0 and i1...")
    [ prettyTCM dnfList0 , prettyTCM dnfList1 ]
  return () --printInTCM


testMixedForall :: TCM ()
testMixedForall = do
  addVerb "tc.conv.forallmixed:40"
  complex <- getTheTerm "complex"
  gamma <- getTheCtx "complex"
  mno <- primMno
  myes <- primMyes
  addContext gamma $ do
    reportSDoc "antvascript:0" 0 $ text "DNF of complex zeta"
    _ <- forallMixedFaces complex (\ _ _ _ -> __IMPOSSIBLE__) $ \ sigma -> do
      return ()
    newline
    reportSDoc "antvascript:0" 0 $ text "DNF of mno"  
    _ <- forallMixedFaces mno (\ _ _ _ -> __IMPOSSIBLE__) $ \ sigma -> do
      return ()
    newline
    reportSDoc "antvascript:0" 0 $ text "DNF of myes"  
    _ <- forallMixedFaces myes (\ _ _ _ -> __IMPOSSIBLE__) $ \ sigma -> do
      return ()
    return ()

mpartialJudgEqu1 :: TCM ()
mpartialJudgEqu1 = do
  addVerb "tc.conv.forallmixed:40"
  addVerb "tc.conv.mixedFace:40"
  
  ctx <- getTheCtx "mpartial1"
  typ <- getTheType "mpartial1"
  mp1 <- getTheTerm "mpartial1"
  mp2 <- getTheTerm "mpartial2"

  reportSDocDocs "antvascript" 0
    (text "-----------------------")
    [ text "MP1 VS MP2" ]
  addContext ctx $ equalTerm typ mp1 mp2


mpartialJudgEqu2 :: TCM ()
mpartialJudgEqu2 = do
  addVerb "tc.conv.forallmixed:40"
  addVerb "tc.conv.mixedFace:40"
  
  ctx <- getTheCtx "mmulti1"
  typ <- getTheType "mmulti1"
  mp1 <- getTheTerm "mmulti1"
  mp2 <- getTheTerm "mmulti2"

  reportSDocDocs "antvascript" 0
    (text "-----------------------")
    [ text "MMULTI1 VS MMULTI2" ]
  addContext ctx $ equalTerm typ mp1 mp2

mpartialJudgEqu3 :: TCM ()
mpartialJudgEqu3 = do
  addVerb "tc.conv.forallmixed:40"
  addVerb "tc.conv.mixedFace:40"
  
  ctx <- getTheCtx "am1"
  typ <- getTheType "am1"
  mp1 <- getTheTerm "am1"
  mp2 <- getTheTerm "am2"

  reportSDocDocs "antvascript" 0
    (text "-----------------------")
    [ text "AM1 VS AM2" ]
  addContext ctx $ equalTerm typ mp1 mp2


hocomGlue :: TCM ()
hocomGlue = do
  ctx <- getTheCtx "anchor"
  -- reportSDoc "antvascript" 0 $ prettyTCM ctx
  addContext ctx $ do
    args <- getContextArgs
    -- [{_}, {_}, φ, ψ, A, T, e, u, u0]
    -- [l=lB,bA= Gel A T e,phi,u,u0 : Gel A T e]
    pgel <- primGel
    let
      give n = (args Prelude.!! n)
      l = args Prelude.!! 1
      bA = pgel `apply ` [give 4, give 5, give 6]
      argsForHcom = [give 1, argN bA , give 2 , give 7 , give 8]

    -- :: Reduced MaybeReducedArgs Term
    reportSDoc "antvascript" 0 $ prettyTCM argsForHcom
    thingy <- liftReduce  $  primTransHComp DoHComp argsForHcom 5
    case thingy of
      NoReduction tm -> reportSDocDocs "antvascript" 0
        (text "noreduction") [ prettyTCM tm ]
      YesReduction _ tm -> reportSDocDocs "antvascript" 0
        (text "yesreduction") [ prettyTCM tm ]      
    return ()

  -- how to make an [Arg Term] 
  -- primTransHComp DoHComp (_ : Arg Term)


refoldingMhocom :: TCM ()
refoldingMhocom = do
  addVerb "tc.prim.bridges.refold:30"
  addVerb "tc.prim.hcomp:20"

  hole <- getTheTerm "hole"

  printInTCM $ P.text "refold (mhocom), unsimpl"
  printInTCM $ P.pretty $ hole

  printInTCM $ P.text ""
  printInTCM $ P.text "simplified:"
  shole <- simplify hole
  printInTCM $ P.pretty shole


  hole2 <- getTheTerm "hole2"

  printInTCM $ P.text "refold (mhocom), unsimpl"
  printInTCM $ P.pretty $ hole2

  printInTCM $ P.text ""
  printInTCM $ P.text "simplified:"
  shole2 <- simplify hole2
  printInTCM $ P.pretty shole2
  
-- testMixedMeet :: TCM ()
-- testMixedMeet = do
--   addVerb "tc.prim.bridges.hasEmptyMeet:50"
  
--   m1Tel <- clauseTel <$> getTheClause "mcstr1"
--   m1 <- getTheTerm "mcstr1"
--   m2 <- getTheTerm "mcstr2"
--   oppositeKind <- addContext m1Tel $ hasEmptyMeet m1 m2
--   printInTCM $ (P.<+>)
--     (P.text  "Pure constraints of oppositve kind have empty meet (expecting False): ")
--     (P.pretty oppositeKind)

--   notj <- getTheTerm "notj"
--   yesi <- getTheTerm "yesi"
--   notjyesi <- addContext m1Tel $ hasEmptyMeet notj yesi
--   printInTCM $ (P.<+>)
--     (P.text  "Pure constraints of same kind whose comp. intersect, have empty meet (expecting False): ")
--     (P.pretty notjyesi)

--   notr <- getTheTerm "notr"
--   yess <- getTheTerm "yess"
--   notryess <- addContext m1Tel $ hasEmptyMeet notr yess
--   printInTCM $ (P.<+>)
--     (P.text  "Same but with bridge kind (expecting False): ")
--     (P.pretty notryess)

--   noti <- getTheTerm "noti"
--   yesr <- getTheTerm "yesr"

--   notryesr <- addContext m1Tel $ hasEmptyMeet notr yesr
--   notiyesi <- addContext m1Tel $ hasEmptyMeet noti yesi
--   printInTCM $ (P.<+>)
--     (P.text  "Pure constraints of same kind whose comp. dont intersect, have empty meet (expecting True): ")
--     (P.pretty notiyesi)
--   printInTCM $ (P.<+>)
--     (P.text  "Same but with bridge kind (expecting True): ")
--     (P.pretty notryesr)

{-
best short at "declaring in .agda, working in .hs"
see All.agda for Agda declarations.

sometimes you have to runghc twice on this file in order for it to work.


OLD JUNK
I can already be in a nice TCState with @beInNiceTCState@ above.
I can obtain a realistic QName (this include the file and position of the name ie "range") with @getGNameFromHuman@

But where are stored @Syntax.Internal.Term@'s once they have been typechecked??
I feel like they are in fact not stored anywhere and I have to retypecheck them. But then I need an @Syntax.Abstract.Expr@
and I don't know if I can obtain that based on the QName??
Also, @stImports@ ultimately gives @Definitions@. Can I obtain @Expr@'s from Definitions?
-}
