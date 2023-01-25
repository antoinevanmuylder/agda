{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Description : Primitive definitions (formation/computation). Inspired from `TypeChecking/Primitive/Cubical.hs`.

-}
module Agda.TypeChecking.Primitive.Bridges where

import Prelude hiding (null, (!!))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Maybe
import Control.Exception
import Data.Typeable
import Data.String

import Data.Either ( partitionEithers )
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Agda.Utils.BoolSet as BoolSet
import Agda.Utils.BoolSet (BoolSet)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Foldable hiding (null)

import Agda.Interaction.Options ( optBridges )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
-- import Agda.Syntax.Translation.InternalToAbstract (reify)
-- import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Primitive.Cubical.Base
import Agda.TypeChecking.Monad

import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Lock
-- import Agda.TypeChecking.Primitive.Cubical ( headStop , TermPosition(..) ) --TODO-antva move to Primitive.Base, maybe.

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Function (applyUnless)

import Agda.Utils.Impossible
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Tuple
import Agda.Utils.Size
import qualified Agda.Utils.Pretty as P
import Agda.Utils.VarSet as VSet hiding (null)


-- * Prelude

-- | Generates error if --bridges pragma option was not set
requireBridges :: String -> TCM ()
requireBridges s = do
  bridges <- optBridges <$> pragmaOptions
  unless bridges $
    typeError $ GenericError $ "Missing option --bridges " ++ s

-- | Bridge interval as a type, i.e. as a term and a sort annotation
--   We use the LockUniv sort because bridge variables x : BI should be treated affinely
primBridgeIntervalType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primBridgeIntervalType = El LockUniv <$> primBridgeInterval

primBCstrType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primBCstrType = El CstrUniv <$> primBCstr

primMCstrType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primMCstrType = El CstrUniv <$> primMCstr

-- | two functions to fill implementations holes
dummyRedTerm0 :: ReduceM( Reduced MaybeReducedArgs Term)
dummyRedTerm0 = do
  return $ YesReduction NoSimplification $ Dummy "something" []

dummyRedTerm :: Term -> ReduceM( Reduced MaybeReducedArgs Term)
dummyRedTerm t = return $ YesReduction NoSimplification t

psh :: P.Pretty a => a -> String
psh = P.prettyShow


-- | The first doc is printed. The subsequent list of docs is printed below, with 2 space nesting.
{-# SPECIALIZE reportSDocDocs :: VerboseKey -> VerboseLevel -> TCM Doc -> [TCM Doc] -> TCM () #-}
reportSDocDocs :: MonadDebug m
               => VerboseKey -> VerboseLevel -> TCM Doc  -> [TCM Doc] -> m ()
reportSDocDocs key lvl doc1 docList = do
  reportSDoc key lvl $ doc1
  reportSDoc key lvl $ nest 2 $ vcat docList


      -- reportSDoc "tc.prim.bridges.hasEmptyMeet" 50 $ nest 2 $ vcat
      --   [ "phi1     = " <+> prettyTCM phi1
      --   , "phi2     = " <+> prettyTCM phi2
      --   , "rphi12   = " <+> prettyTCM rphi12 ]



data CorBsplit
  = CSPLIT
  | BSPLIT
  deriving (Eq, Ord, Show)

instance PrettyTCM CorBsplit where prettyTCM = text . show

-- | @dnfMixedCstr zeta@ builds a list of dnf clauses of zeta
--   For each clause we get to know: if its a path or bridge clause
--   The conjunction as an IntMap Bool
--   The remaining blocked terms
--
--   /!\ what if zeta is a Var dbi []. precond: zeta is mkmc, mno or myes?
dnfMixedCstr :: (HasBuiltins m , MonadDebug m, MonadReduce m) => Term -> m [ (CorBsplit, IntMap Bool, [Term]) ]
dnfMixedCstr zeta = do
  viewZeta <- mcstrView zeta
  case viewZeta of
    Mno -> return [] -- there are 0 DNF clauses.
    Myes -> return [ (CSPLIT , IntMap.empty , [] ) ]
    OtherMCstr tm -> return [ (BSPLIT, IntMap.empty, [tm]) ] -- TODO-antva: fixed that for data types. is it sound
    Mkmc (Arg _ phi) (Arg _ psi) -> do
      dnfPhi_0 <- decomposeInterval phi
      -- :: [ (IntMap Bool, [Term]) ]
      -- bs :: IntMap Bool is 1 non incositent conjunction within path DNF
      let dnfPhi = flip map dnfPhi_0 $ \ (dbToB, ts) -> (CSPLIT, dbToB, ts)
      reportSDoc "tc.conv.dnfmixed" 40 $ "dnfPhi  = " <+> prettyTCM dnfPhi
      Just canPsi <- mbAsCanBCstr =<< reduce psi
      dnfPsi <- case canPsi of
        CanBno -> return []
        CanByes -> __IMPOSSIBLE__ -- because we felt in Myes case above
        CanMap dbToDir -> -- ≈ the list of  b∨ clauses
          (\ base trav cont -> foldM cont base trav) [] (IntMap.toList dbToDir) $ \ done (bvar,fcs) -> do
          -- (Bsplit :: CorBsplit,
          --  ? :: IntMap Bool
          --  [])  to match ts above.
          return $ (++) done $ flip map (BoolSet.toList fcs) $ \ fc -> (BSPLIT, IntMap.singleton bvar (fc), [] :: [Term])
      reportSDoc "tc.conv.dnfmixed" 40 $ "dnfPsi  = " <+> prettyTCM dnfPsi
      return $ dnfPhi ++ dnfPsi

data CanBCstr
  = CanBno
  | CanMap (IntMap (BoolSet))
  | CanByes
  deriving (Eq, Show)

-- | precond: psi has been reduced. "as canonical bcstr"
asCanBCstr :: (HasBuiltins m , MonadTCEnv m , ReadTCState m, MonadError TCErr m) => Term -> m CanBCstr
asCanBCstr psi = do
  psiView <- bcstrView psi
  case psiView of
    Bno -> return CanBno
    Byes -> return CanByes
    Bisone (Arg _ (Var i [])) -> return $ CanMap $ IntMap.singleton i (BoolSet.singleton True)
    Biszero (Arg _ (Var i [])) -> return $ CanMap $ IntMap.singleton i (BoolSet.singleton False)
    Bconj (Arg _ psi1) (Arg _ psi2) -> do
      psi1' <- asCanBCstr psi1 ; psi2' <- asCanBCstr psi2
      case (psi1' , psi2') of
        (CanBno, _) -> typeError $ GenericDocError "asCanBCstr expects a reduced arg"
        (_ , CanBno) -> typeError $ GenericDocError "asCanBCstr expects a reduced arg"
        (CanByes, _) -> typeError $ GenericDocError "asCanBCstr expects a reduced arg"
        (_ , CanByes) -> typeError $ GenericDocError "asCanBCstr expects a reduced arg"
        (CanMap psi1map , CanMap psi2map) -> do
          return $ CanMap $ IntMap.unionWith (BoolSet.union) psi1map psi2map
    _ -> typeError $ GenericDocError "asCanBCstr expects a reduced arg/no metas"

mbAsCanBCstr :: (HasBuiltins m) => Term -> m (Maybe CanBCstr)
mbAsCanBCstr psi = do
  psiView <- bcstrView psi
  case psiView of
    Bno -> return $ Just CanBno
    Byes -> return $ Just CanByes
    Bisone (Arg _ (Var i [])) -> return $ Just $ CanMap $ IntMap.singleton i (BoolSet.singleton True)
    Biszero (Arg _ (Var i [])) -> return $ Just $ CanMap $ IntMap.singleton i (BoolSet.singleton False)
    Bconj (Arg _ psi1) (Arg _ psi2) -> do
      psi1' <- mbAsCanBCstr psi1 ; psi2' <- mbAsCanBCstr psi2
      case (psi1' , psi2') of
        (Just ( CanMap psi1map ), Just ( CanMap psi2map )) -> do
          return $ Just $ CanMap $ IntMap.unionWith (BoolSet.union) psi1map psi2map
        _ -> return Nothing
    _ -> return Nothing
    
-- -- | pretty Doc's of terms, with implicit arguments.
-- prettyTermImpl :: Term  -> TCM Doc
-- prettyTermImpl t = do
--   expr <- reify t -- Abstract.Expr
--   smth <- abstractToConcrete_ expr -- Concrete.Expr
--   -- P.pretty
  
--   return $ P.text "hello"




-- * extent primitive


-- | Type for extent primitive.
--   We use hoas style functions like hPi' to specifiy types in internal syntax.
--   primExtent : ∀ {ℓA ℓB} {A : @(tick x : BI) → Set ℓA} {B : (tick x : BI) (a : A x) → Set ℓB}
--                (N0 : (a0 : A bi0) → B bi0 a0)
--                (N1 : (a1 : A bi1) → B bi1 a1)
--                (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) →
--                      BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1))
--                (@tick r : BI) (M : A r)
--                B r M
extentType :: TCM Type
extentType = do
  t <- runNamesT [] $
       hPi' "lA" (el $ cl primLevel) (\ lA ->
       hPi' "lB" (el $ cl primLevel) $ \ lB ->
       -- We want lines A B to use their bridge var affinely, hence the tick annotation lPi' vs nPi'
       hPi' "A"  (lPi' "x" primBridgeIntervalType $ \x -> (sort . tmSort <$> lA)) $ \ bA ->
       hPi' "B" (lPi' "x" primBridgeIntervalType $ \ x -> (el' lA (bA <@> x)) --> (sort . tmSort <$> lB) ) $ \bB ->
       nPi' "N0" (nPi' "a0" (el' lA (bA <@> cl primBIZero)) $ \a0 -> (el' lB (bB <@> cl primBIZero <@> a0))) $ \n0 ->
       nPi' "N1" (nPi' "a1" (el' lA (bA <@> cl primBIOne)) $ \a1 -> (el' lB (bB <@> cl primBIOne <@> a1))) $ \n1 ->
       nPi' "NN"
        (nPi' "a0" (el' lA (bA <@> cl primBIZero)) $ \a0 ->
         nPi' "a1" (el' lA (bA <@> cl primBIOne)) $ \a1 ->
         nPi' "aa" (el' lA $ cl primBridgeP <#> lA <@> bA <@> a0 <@> a1) $ \aa ->
         (el' lB $ cl primBridgeP <#> lB <@> newBline bB aa a0 a1 <@> (n0 <@> a0) <@> (n1 <@> a1)) ) $ \nn ->
       lPi' "r" primBridgeIntervalType $ \ r ->
       nPi' "M" (el' lA (bA <@> r)) $ \bM ->
       el' lB $ bB <@> r <@> bM )
  return t
  where
    newBline bB aa a0 a1 = glam lkDefaultArgInfo "i" (\i -> bB <@> i <@> (aa <@@> (a0, a1, i) )) -- i is a bridge elim hence the double "at".
    lkDefaultArgInfo = setLock IsLock defaultArgInfo


-- | @semiFreshForFvars fvs lk@ checks whether the following condition holds:
--   forall j in fvs, lk <=_time j -> timeless(j,lk) where <=_time is left to right context order
--   need lk as arg of timeless for the case j has type BCstr
semiFreshForFvars :: PureTCM m => VarSet -> Int -> m Bool
semiFreshForFvars fvs lki = do
  let lkLaters = filter (<= lki) (VSet.toList fvs) -- lk-laters, including lk itself and timeless vars
  timefullLkLaters <- flip filterM lkLaters $ \ j -> do
    tyj <- typeOfBV j --problem: can yield dummy type when it should not
    resj <- isTimeless' tyj lki -- for instance (@j : MHolds (zeta(@lki:BI)) is bad (resj=false)
    return $ not resj
  reportSLn "tc.freshness" 40 $ "semiFreshForFvars, timefullLkLaters: " ++ P.prettyShow timefullLkLaters
  return $ null timefullLkLaters

-- | Formation rule (extentType) and computation rule for the extent primitive.
--   For extent this include a boundary (BIZero, BIOne case) and beta rule.
primExtent' :: TCM PrimitiveImpl
primExtent' = do
  requireBridges "in primExtent'"
  typ <- extentType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 9 $ \extentArgs@[lA, lB, bA, bB,
                                                      n0@(Arg n0info n0tm), n1@(Arg n1info n1tm),
                                                      nn@(Arg nninfo nntm),
                                                      r@(Arg rinfo rtm0), bM] -> do
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    r' <- reduceB' r
    viewr <- bridgeIntervalView $ unArg $ ignoreBlocking r'
    case viewr of
      BIZero ->  redReturn $ n0tm `apply` [bM] -- YesReduction, YesSimplification
      BIOne ->   redReturn $ n1tm `apply` [bM]
      -- QST: no need to check that #occ of r in M <= 1 because this will be checked later?
      -- in order to reduce extent_r(M ; ..) we need to check that M has no timefull r-laters
      BOTerm rtm@(Var ri []) -> do
        reportSLn "tc.prim.extent" 30 $ "Trying to reduce extent of bvar. all args:  " ++ psh extentArgs
        reportSLn "tc.prim.extent" 30 $ "About to reduce principal (last) argument: " ++ psh bM
        bM' <- reduceB' bM --because some timefull r-laters may disappear
        -- TODO-antva. by default the above reduction could be disabled
        -- this reduction would happen only if shouldRedExtent (of bM, not bM') below is False
        -- This way the reduction would still yield human readable stuff 
        reportSLn "tc.prim.extent" 30 $ "Result of reduction is " ++ (psh $ ignoreBlocking bM')
        let bMtm' = unArg $ ignoreBlocking $ bM'
        let fvM0 = freeVarsIgnore IgnoreNot $ bMtm' -- correct ignore flag?
        -- let rigidFvM = rigidVars fvM0
        -- let flexFvM = flexibleVars fvM0 --free vars appearing under a meta
        let fvM = allVars fvM0
        shouldRedExtent <- semiFreshForFvars fvM ri
        case shouldRedExtent of
          False -> do
            reportSLn "tc.prim.extent" 30 $
              P.prettyShow rtm ++ " NOT semifresh for princ arg (showed unreduced): " ++ psh bM
            reportSLn "tc.prim.extent" 30 $
              "Its bridge var argument has " ++ show (getAnnotation rinfo) ++ ".It should be locked."
            reportSLn "tc.prim.extent" 30 $ "because fvs are " ++ P.prettyShow fvM
            return $ NoReduction $ map notReduced [lA, lB, bA, bB, n0, n1, nn]  ++ map reduced [ r', bM'] --should throw error?
          True -> do
            reportSLn "tc.prim.extent" 30 $ P.prettyShow rtm ++ " is semifresh for princ arg (showed unreduced): " ++ psh bM
            bi0 <- getTerm "primExtent" builtinBIZero
            bi1 <- getTerm "primExtent" builtinBIOne
            let lamM = captureIn bMtm' ri   -- λ r. M (where M has been reduced = weak head normalized)
            sbMtm <- simplify $ unArg bM 
            let sLamM = captureIn sbMtm ri  -- λ r. M (where M has been simplified)
            let readableLamM = captureIn (unArg bM) ri --  λ r. M (where M is untouched)
            reportSLn "tc.prim.extent" 30 $ "captureIn (( " ++ psh bM ++" )) (( " ++ psh ri ++ " ))"
            reportSLn "tc.prim.extent" 30 $ "captureIn ((M)) ((r)) is " ++ psh lamM
            lamMBi0 <- reduce' $ readableLamM `apply` [argN bi0]
            reportSLn "tc.prim.extent" 30 $ "lamM bi0 is: " ++ psh lamMBi0
            redReturn $ nntm `applyE` [Apply $ argN $ readableLamM `apply` [argN bi0],
                                   Apply $ argN $ readableLamM `apply` [argN bi1],
                                   Apply $ argN $ sLamM,
                                   IApply n0tm n1tm rtm  ]
      _ -> do
        reportSLn "tc.prim.extent" 30 $ "awkward bridge var as extent argument: " ++ psh ( unArg $ ignoreBlocking r' )
        return $ NoReduction $ map notReduced [lA, lB, bA, bB, n0, n1, nn] ++ [reduced r' , notReduced bM]
  where
    -- | captures r in M, ie returns λ r. M. This is sound thanks to the fv-analysis. (semiFreshForFvars M @r)
    --  Γ0 , r:BI , Γ1, r''   --σ-->   Γ0 , r:BI , Γ1 ⊢ M   where    r[σ] = r''
    -- idea: sigma is a stack of :# (see Substitution'). leaves of sigma:
    -- Γ0, r:BI , Γ1, r'' ⊢ r''        Γ0, r:BI , Γ1, r'' ⊢ Γ0
    -- --------------------------------------------------------
    -- Γ0, r:BI , Γ1, r'' ⊢ Γ0, r    where r mapsto r''
    --
    -- precond: Γ0 , r:BI , Γ1 ⊢ M : ... and (semiFreshForFvars M @r) then
    -- postcond      Γ0, r:BI, Γ1 ⊢ (captureIn M @r) : (@tick r'' : BI) -> ...
    captureIn m ri =
      let sigma = ([var (i+1) | i <- [0 .. ri - 1] ] ++ [var 0]) ++# raiseS (ri + 2) in
      Lam ldArgInfo $ Abs "r" $ applySubst sigma m
    ldArgInfo = setLock IsLock defaultArgInfo
    fallback lA lB bA bB r bM' n0 n1 nn =
      return $ NoReduction $ map notReduced [lA, lB, bA, bB, n0, n1, nn, r] ++ [reduced bM']

       -- sphi <- reduceB' phi
       -- case view $ unArg $ ignoreBlocking $ sphi of
       --   IOne -> redReturn $ unArg t `apply` [argN one]
       --   _    -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,e,t,a])



-- * Gel type primitives: Gel, gel, ungel

--   We take inspiration from the cubical Glue types and primitives.
--   In their case, the type, the intro and elim primitives are really agda primitives.
--   the boundary rules are part of the various PrimitiveImpl.
--   the Glue beta rule is part of the unglue PrimitiveImpl
--   the Glue eta rule is specified elsewhere (Conversion.hs)


-- | Gel : ∀ {ℓ} (A0 : Set ℓ) (A1 : Set ℓ) (R : A0 → A1 → Set ℓ) (@tick r : BI) → Set ℓ
gelType :: TCM Type
gelType = do
  t <- runNamesT [] $
       hPi' "l" (el primLevel) $ \l ->
       nPi' "A0" (sort . tmSort <$> l) $ \bA0 ->
       nPi' "A1" (sort . tmSort <$> l) $ \bA1 ->
       nPi' "R" ( (el' l bA0) --> (el' l bA1) --> (sort . tmSort <$> l) ) $ \bR ->
       lPi' "r" primBridgeIntervalType $ \r ->
       sort . tmSort <$> l
  return t


-- | Formation rule for Gel type + boundary rule
primGel' :: TCM PrimitiveImpl
primGel' = do
  requireBridges "in primGel'"
  typ <- gelType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 5 $ \gelTypeArgs@[l, bA0@(Arg ainfo0 bA0tm),
                                                      bA1@(Arg ainfo1 bA1tm), bR, r@(Arg rinfo rtm)]-> do
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    viewr <- bridgeIntervalView rtm --should reduceB because of metas
    case viewr of
      BIZero -> redReturn bA0tm
      BIOne -> redReturn bA1tm
      BOTerm rtm@(Var ri []) -> return $ NoReduction $ map notReduced gelTypeArgs
      _ -> __IMPOSSIBLE__ --metas...


-- | prim^gel : ∀ {ℓ} {A0 A1 : Set ℓ} {R : A0 → A1 → Set ℓ}
--              (M0 : A0) (M1 : A1) (P : R M0 M1) (@tick r : BI) →
--              Gel A0 A1 R r
-- pblm: R can not be inferred if implicit
prim_gelType :: TCM Type
prim_gelType = do
  t <- runNamesT [] $
       hPi' "l" (el primLevel) $ \l ->
       hPi' "A0" (sort . tmSort <$> l) $ \bA0 ->
       hPi' "A1" (sort . tmSort <$> l) $ \bA1 ->
       hPi' "R" ( (el' l bA0) --> (el' l bA1) --> (sort . tmSort <$> l) ) $ \bR ->
       nPi' "M0" (el' l bA0) $ \bM0 ->
       nPi' "M1" (el' l bA1) $ \bM1 ->
       nPi' "P" (el' l $ bR <@> bM0 <@> bM1) $ \bP ->
       lPi' "r" primBridgeIntervalType $ \r -> 
       el' l $ cl primGel <#> l <@> bA0 <@> bA1 <@> bR <@> r
  return t
  

-- | introduction term for Gel is gel (sometimes also called prim_gel - prim_gel' - prim^gel)
prim_gel' :: TCM PrimitiveImpl
prim_gel' = do
  requireBridges "in prim_gel'"
  typ <- prim_gelType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 8 $ \gelArgs@[l, bA0, bA1, bR, bM0@(Arg _ bM0tm),
                                                     bM1@(Arg _ bM1tm), bP, r@(Arg rinfo rtm)]-> do
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    viewr <- bridgeIntervalView rtm --should reduceB because of metas
    case viewr of
      BIZero -> redReturn bM0tm
      BIOne -> redReturn bM1tm
      BOTerm rtm@(Var ri []) -> return $ NoReduction $ map notReduced gelArgs
      _ -> __IMPOSSIBLE__ --metas...


-- | prim^ungel : ∀ {ℓ} {A0 A1 : Set ℓA} {R : A0 → A1 → Set ℓ}
--                (absQ : (@tick x : BI) → primGel x A0 A1 R) →
--                R (absQ bi0) (absQ bi1)
prim_ungelType :: TCM Type
prim_ungelType = do
  t <- runNamesT [] $
       hPi' "l" (el primLevel) $ \l ->
       hPi' "A0" (sort . tmSort <$> l) $ \bA0 ->
       hPi' "A1" (sort . tmSort <$> l) $ \bA1 ->
       hPi' "R" ( (el' l bA0) --> (el' l bA1) --> (sort . tmSort <$> l) ) $ \bR ->
       nPi' "absQ" ( lPi' "x" primBridgeIntervalType $ \x ->
                          (el' l $ cl primGel <#> l <@> bA0 <@> bA1 <@> bR <@> x)) $ \absQ ->
       el' l $ bR <@> (absQ <@> primBIZero) <@> (absQ <@> primBIOne)
  return t


-- | Eliminator for Gel types called ungel (sometimes prim_ungel' - prim_ungel - prim^ungel)
--   We encode the Gel beta rule in it
prim_ungel' :: TCM PrimitiveImpl
prim_ungel' = do
  requireBridges "in prim_ungel'"
  typ <- prim_ungelType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 5 $ \gelArgs@[l, bA0, bA1,
                                                               bR, absQ]-> do
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    reportSLn "tc.prim.ungel" 30 $ "in prim_ungel': beginning of primImpl"
    mgel <- getPrimitiveName' builtin_gel
    bintervalTm <- getTerm "prim_ungel" builtinBridgeInterval
    let bintervalTyp = El LockUniv bintervalTm
    absQ' <- reduceB' absQ
    let absQtm' = unArg $ ignoreBlocking $ absQ' --should care for metas, as usual
    case absQtm' of
      Lam qinfo qbody -> do --case: λ x → bla x.  we do hit that case sometimes
        logInContext "prim_ungel', lam case, reduced absQ" (absQtm')
        -- reportSLn "tc.prim.ungel" 30 $ "in prim_ungel'. lam case. here is absQ :" ++ psh absQtm'
        underAbstractionAbs (defaultNamedArgDom qinfo (absName qbody) bintervalTyp) qbody $ \body -> do
          --body already comes wkn
          body' <- reduceB' body --should care for metas as usual
          case ignoreBlocking body' of
            Def qnm [Apply _, Apply _, Apply _, Apply _,Apply _, Apply _, Apply bP, Apply _]
             | Just qnm == mgel -> do

              logInContext "prim_ungel', \\x -> gel case, reduced body" (ignoreBlocking body')
              logInContext "just P arg before str"  (bP)
              
              -- reportSLn "tc.prim.ungel" 30 $ "in prim_ungel': lam mgel case."
              -- reportSLn "tc.prim.ungel" 30 $ "in prim_ungel': here is absQ local body: " ++ psh (ignoreBlocking body')
              -- reportSLn "tc.prim.ungel" 30 $ "in prim_ungel'. absQ is x.gel, here is P before str: " ++ psh bP

              -- were about to strenghten P. But it might contain easily solvable metas
              -- that have a vaccuous dependency on db var @0 (bridge var from underAbstractionAbs).
              -- So we first solve everything that can be, and then proceed to strengthening.
              instaP <- traverseF instantiateFull bP

              logInContext "instantiated P" (unArg instaP)
              
              -- reportSDoc "tc.prim.ungel" 30 $ "instaP ctx: " <+> (prettyTCM ctx)
              -- reportSLn "tc.prim.ungel" 30 $ "instaP: " ++ psh instaP
              -- reportSDoc "tc.prim.ungel" 30 $ "instaP pretty: " <+> (prettyTCM instaP)

              let strP = applySubst (strengthenS __IMPOSSIBLE__ 1) $ unArg instaP

              logInContext "P after strenghtening" (strP)
              
              redReturn strP
              
            _ -> do
              reportSLn "tc.prim.ungel" 30 $ "in prim_ungel': lam no-mgel case."
              let lamBody' :: Blocked (Arg Term)
                  lamBody' = case body' of
                    Blocked blkBody' ignBody' -> Blocked blkBody' $ Arg defaultArgInfo $ Lam qinfo $ Abs (absName qbody) ignBody'
                    NotBlocked nblkBody' ignBody' -> NotBlocked nblkBody'  $ Arg defaultArgInfo $ Lam qinfo $ Abs (absName qbody) ignBody'
              fallback l bA0 bA1 bR lamBody' --we fallback and specify the blocking info from body' instead of absQ'
      Def qnm [Apply _, Apply _, Apply _, Apply _,Apply _, Apply _, Apply bP] | Just qnm == mgel -> do
        reportSLn "tc.prim.ungel" 30 $ "in prim_ungel'. no-lam mgel case. here is absQ :" ++ psh absQtm'
        reportSLn "tc.prim.ungel" 30 $ "  and here is the qname: " ++ psh qnm
        redReturn $ unArg bP
      _ -> do
        reportSLn "tc.prim.ungel" 30 $ "in prim_ungel'. no-lam no-mgel case. here is absQ :" ++ psh absQtm'
        fallback l bA0 bA1 bR absQ'
  where
    fallback l bA0 bA1 bR absQ' =
      return $ NoReduction $ map notReduced [l, bA0, bA1, bR] ++ [reduced absQ']

    logInContext descr toLog = do
      ctx <- getContextTelescope
      reportSDocDocs "tc.prim.ungel" 30
        (text $ descr ++ " in context:")
        [ prettyTCM ctx
        , prettyTCM toLog ]
        


-- in unglue:
-- begin by reduceB' the variable phi. we don't have such a variable anyway
-- then they reduceB' the principal argument b

-- * BCstr primitives

-- next the 'constructors' of BCstr. Typically ψ:BCstr is x1=ε1 ∨ ... ∨ xn=εn
-- There are also bottom and top constructors in BCstr.

-- | bottom element in BCstr
primBno' :: TCM PrimitiveImpl
primBno' = do
  requireBridges "in primBno'"
  bcstr <- primBCstr
  return $ PrimImpl (El CstrUniv bcstr) $ primFun __IMPOSSIBLE__ 0 $ \ _ ->
    return $ NoReduction []

-- | top element in BCstr
primByes' :: TCM PrimitiveImpl
primByes' = do
  requireBridges "in primByes'"
  bcstr <- primBCstr
  return $ PrimImpl (El CstrUniv bcstr) $ primFun __IMPOSSIBLE__ 0 $ \ _ ->
    return $ NoReduction []

-- | primBisone : BI -> BCstr       constraint "r=1" for some bvar r.
primBisone' :: TCM PrimitiveImpl
primBisone' = do
  requireBridges "in primBisone'"
  typ <- (primBridgeIntervalType --> primBCstrType)
  return $ PrimImpl typ  $ primFun __IMPOSSIBLE__ 1 $ \args@[ r ] -> do
    bno <- getTerm builtinBisone builtinBno
    byes <- getTerm builtinBisone builtinByes
    r' <- reduceB' r
    viewr <- bridgeIntervalView $ unArg $ ignoreBlocking r'
    case viewr of
      BIZero -> redReturn $ bno
      BIOne -> redReturn $ byes
      _ -> return $ NoReduction $ [reduced r'] --what about metas
      
-- | primBiszero : BI -> BCstr       constraint "r=0" for some bvar r.
primBiszero' :: TCM PrimitiveImpl
primBiszero' = do
  requireBridges "in primBisone'"
  typ <- (primBridgeIntervalType --> primBCstrType)
  return $ PrimImpl typ  $ primFun __IMPOSSIBLE__ 1 $ \args@[ r ] -> do
    bno <- getTerm builtinBisone builtinBno
    byes <- getTerm builtinBisone builtinByes
    r' <- reduceB' r
    viewr <- bridgeIntervalView $ unArg $ ignoreBlocking r'
    case viewr of
      BIZero -> redReturn $ byes
      BIOne -> redReturn $ bno
      _ -> return $ NoReduction $ [reduced r'] --what about metas

data BCstrView
  = Bno
  | Byes
  | Bisone (Arg Term)
  | Biszero (Arg Term)
  | Bconj (Arg Term) (Arg Term)
  | OtherBCstr Term

bcstrView' :: HasBuiltins m => m (Term -> BCstrView)
bcstrView' = do
  bno <- getPrimitiveName' builtinBno
  byes <- getPrimitiveName' builtinByes
  biszero <- getPrimitiveName' builtinBiszero
  bisone <- getPrimitiveName' builtinBisone
  bconj <- getPrimitiveName' builtinBconj
  return $ \ t ->
    case t of
      Def q es ->
        case es of
          [] | Just q == bno -> Bno
          [] | Just q == byes -> Byes
          [Apply x]         | Just q == bisone -> Bisone x
          [Apply x]         | Just q == biszero -> Biszero x          
          [Apply x,Apply y] | Just q == bconj -> Bconj x y
          _                 -> OtherBCstr t
      _ -> OtherBCstr t

bcstrView :: HasBuiltins m => Term -> m BCstrView
bcstrView t = do
  f <- bcstrView'
  return (f t)      

-- | conjunction of bridge var constraints. primBconj : BCstr -> BCstr -> BCstr
primBconj' :: TCM PrimitiveImpl
primBconj' = do
  requireBridges "in primBconj'"
  typ <- (primBCstrType --> primBCstrType --> primBCstrType)
  return $ PrimImpl typ  $ primFun __IMPOSSIBLE__ 2 $ \args@[ psi1 , psi2 ] -> do
    bno <- getTerm builtinBconj builtinBno
    byes <- getTerm builtinBconj builtinByes
    bisone <- getTerm builtinBconj builtinBisone
    biszero <- getTerm builtinBconj builtinBiszero
    psi1' <- reduceB' psi1
    psi2' <- reduceB' psi2
    viewPsi1 <- bcstrView $ unArg $ ignoreBlocking psi1'
    viewPsi2 <- bcstrView $ unArg $ ignoreBlocking psi2'
    case (viewPsi1 , viewPsi2) of
      -- absorption/identity
      (Byes , _) -> redReturn byes
      (_ , Byes) -> redReturn byes
      (Bno , _) -> redReturn $ unArg $ ignoreBlocking $ psi2'
      (_ , Bno) -> redReturn $ unArg $ ignoreBlocking $ psi1'
      _ -> return $ NoReduction $ map reduced [ psi1' , psi2'] -- /!\ metas


-- BPartial type former  (old. the correct notion is mixed partial elements MPartial)

primBPartial' :: TCM PrimitiveImpl
primBPartial' = do
  requireBridges ""
  t <- runNamesT [] $
       hPi' "l" (el $ cl primLevel) (\ l ->
        nPi' "ψ" primBCstrType $ \ _ ->
        nPi' "A" (sort . tmSort <$> l) $ \ bA ->
        (sort . tmSSort <$> l))
  tbholds <- primBHolds
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 3 $ \ ts -> do
    case ts of
      [l,psi,a] -> do
          (El s (Pi d b)) <- runNamesT [] $ do
                             [l,a,psi] <- mapM (open . unArg) [l,a,psi]
                             elSSet (pure tbholds <@> psi) --> el' l a
          redReturn $ Pi (setRelevance Irrelevant $ d { domFinite = True }) b
      _ -> __IMPOSSIBLE__


-- * MCstr primitives, and MPartial type former

-- Constructors for the type of mixed constraints MCstr.
-- A Mcstr is a pair (φ : I, ψ : BCstr) up to "top identification":
--   any pair with a top constraint on either side, beta-reduces to myes:MCstr
-- For convenience we also have a bottom (mno : MCstr), the normal form of (no,no)

-- | bottom element in MCstr
primMno' :: TCM PrimitiveImpl
primMno' = do
  requireBridges "in primMno'"
  mcstr <- primMCstr
  return $ PrimImpl (El CstrUniv mcstr) $ primFun __IMPOSSIBLE__ 0 $ \ _ ->
    return $ NoReduction []

-- | top element in MCstr
primMyes' :: TCM PrimitiveImpl
primMyes' = do
  requireBridges "in primMyes'"
  mcstr <- primMCstr
  return $ PrimImpl (El CstrUniv mcstr) $ primFun __IMPOSSIBLE__ 0 $ \ _ ->
    return $ NoReduction []

-- | Make mixed constraint by pairing a path and a bridge constraint.
--   This pairing may be understood as a union of cubes:
--   Let φ and ψ be approriate subcubes of a path/bridge cube.
--   Then mkmc φ ψ can be parsed as (φ x PSI) U (PHI x ψ)
--   where capital greek letters denote entire bridge/path cubes.
--   The equational thy on MCstr induced by the present constructor
--   corresponds to the computational behaviour of this union of subcubes.
primMkmc' :: TCM PrimitiveImpl
primMkmc' = do
  requireBridges "in primMkmc'"
  mcstr <- primMCstr
  -- t <- runNamesT [] $
  --       nPi' "φ" primIntervalType $ \ _ ->
  --       nPi' "ψ" primBCstrType $ \ _ ->
  --       primMCstrType
  typ <- (primIntervalType --> primBCstrType --> primMCstrType)
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 2 $  \args@[ φ , ψ ] -> do
    bno <- getTerm "primMkmc'" builtinBno
    byes <- getTerm "primMkmc'" builtinByes
    iz <- getTerm "primMkmc'" builtinIZero
    io <- getTerm "primMkmc'" builtinIOne
    mno <- getTerm "primMKmc'" "primMno"
    myes <- getTerm "primMKmc'" "primMyes"
    φ' <- reduceB' φ
    ψ' <- reduceB' ψ
    viewφ <- intervalView $ unArg $ ignoreBlocking φ'
    viewψ <- bcstrView $ unArg $ ignoreBlocking ψ'
    case (viewφ, viewψ) of
      -- A top constraint on either side makes the pair reduce to the top mixed constraint
      (IOne, _) -> redReturn $ myes
      (_ , Byes) -> redReturn $ myes
      (IZero, Bno) -> redReturn $ mno
      _ -> return $ NoReduction $ map reduced [ φ' , ψ'] --metas?..


data MCstrView
  = Mno
  | Myes
  | Mkmc (Arg Term) (Arg Term)
  | OtherMCstr Term

mcstrView' :: HasBuiltins m => m (Term -> MCstrView)
mcstrView' = do
  mno <- getPrimitiveName' "primMno"
  myes <- getPrimitiveName' "primMyes"
  mkmc <- getPrimitiveName' "primMkmc"
  return $ \ t ->
    case t of
      Def q es ->
        case es of
          [] | Just q == mno -> Mno
          [] | Just q == myes -> Myes
          [ Apply phi , Apply psi ] | Just q == mkmc -> Mkmc phi psi
          _                 -> OtherMCstr t
      _ -> OtherMCstr t

mcstrView :: HasBuiltins m => Term -> m MCstrView
mcstrView t = do
  f <- mcstrView'
  return (f t)


-- | pre: the two inputs zeta1 zeta2 type in MCstr, and have no metas.
--        and their bcstr components (psi1, psi2 below) consist of 1 single face (x = biε) (b∨ atomic)
--        their I components (phi1, phi2) are ∨-atomic, ie are conjunctive clauses like i ∧ ~ i
--   Assume zeta1 = phi1 m∨ psi1 and zeta2 = phi2 m∨ psi2
--   zeta1,zeta2 have an empty meet (those mixed constraints are never sat together) iff
--     phi1, phi2 do not meet AND
--     psi1, psi2 do not meet AND
--     phi1 × psi2 = empty   and    phi2 × psi1 = empty
--   Note: if zeta1, zeta2 are non empty but have empty meet then zeta1 and zeta2 are pure (either path or bridge)
--         and have the same kind (path or bridge)
--         If theyre embedded path constraints, theyre just non-intersecting sub-path-cubes (we basically can say nothing)
--         If theyre embedded bridge constraints, theyre opposite hyperplanes (assuming the precondition holds)
hasEmptyMeet :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m, MonadReduce m, MonadDebug m)
             => Term -> Term -> m Bool
hasEmptyMeet zeta1 zeta2 = do
  rzeta1 <- reduce zeta1
  rzeta2 <- reduce zeta2
  viewZeta1 <- mcstrView rzeta1
  viewZeta2 <- mcstrView rzeta2
  imin <- primIMin
  mbno <- getPrimitiveName' builtinBno
  mBiszero <- getPrimitiveName' builtinBiszero
  mBisone <- getPrimitiveName' builtinBisone  
  case (viewZeta1, viewZeta2) of
    (OtherMCstr _,  _) -> __IMPOSSIBLE__
    (_, OtherMCstr _) -> __IMPOSSIBLE__    
    (Mno, _) -> return True
    (_ , Mno) -> return True -- else if
    (Myes, _) -> return False
    (_, Myes) -> return False
    (Mkmc (Arg phi1Inf phi1) (Arg psi1Inf psi1) , Mkmc (Arg phi2Inf phi2) (Arg psi2Inf psi2) ) -> do
      rphi12 <- reduce $ imin `apply` [argN phi1, argN phi2]
      -- ~ i ∧ i != 0 as interval value but should be as constraint.
      -- below, rphi12 = 0 iff ans = []
      --        rphi12 = 1 iff ans = [([],[])]
      cubDNFAnalysis <- decomposeInterval' rphi12 -- :: [(IntMap BoolSet, [Term])]
      notphi1meetsphi2 <- case cubDNFAnalysis of
        [] -> return True -- but this is not the only case where phi1 does not meet phi2 (see comment above)
        [ (varToDirset, [] ) ] -> do
          let morethan1dir = flip filter (IntMap.toList varToDirset) $ \ (v,dset) ->
                (BoolSet.size dset) > 1
          return $ not (length morethan1dir == 0) -- ex: true if phi12 = i ∧ (~ i ∧ j)
        [ (_ , _) ] -> typeError $ GenericError $ "Not authorized: metas in lhs of path clauses of mpartial element"
        _ -> return False
        

      -- phi1meetsphi2_0 <- (intervalView rphi12)
      -- let phi1meetsphi2 = case phi1meetsphi2_0 of
      --       IZero -> False
      --       _ -> True

      reportSDoc "tc.prim.bridges.hasEmptyMeet" 50 $ "In hasEmptyMeet, analysing phi1 and phi2"
      reportSDoc "tc.prim.bridges.hasEmptyMeet" 50 $ nest 2 $ vcat
        [ "phi1     = " <+> prettyTCM phi1
        , "phi2     = " <+> prettyTCM phi2
        , "rphi12   = " <+> prettyTCM rphi12 ]
      
      psi1View <- bcstrView psi1
      psi2View <- bcstrView psi2
      let psi1isEmpty = case psi1View of
            Bno -> True
            _ -> False
      let psi2isEmpty = case psi2View of
            Bno -> True
            _ -> False
      let psi12oppositeFaces = case (psi1View, psi2View) of
            (Bno, _) -> True
            (_, Bno) -> True
            (Bisone (Arg _ (Var v1 [])), Biszero (Arg _ (Var v2 []))) | v1 == v2 -> True
            (Biszero (Arg _ (Var v1 [])), Bisone (Arg _ (Var v2 []))) | v1 == v2 -> True        
            _ -> False

      phi1View <- intervalView phi1
      phi2View <- intervalView phi2
      let phi1isEmpty = case phi1View of
            IZero -> True
            _ -> False
      let phi2isEmpty = case phi2View of
            IZero -> True
            _ -> False
                        
      
      let notpsi1meetspsi2 =
            psi1isEmpty || psi2isEmpty || psi12oppositeFaces

      reportSDoc "tc.prim.bridges.hasEmptyMeet" 40 $ "hasEmptyMeet results"
      reportSDoc "tc.prim.bridges.hasEmptyMeet" 40 $ nest 2 $ vcat $
        [ "input zeta1         =" <+> prettyTCM zeta1
        , "input zeta2         =" <+> prettyTCM zeta2
        , "phi1 meets phi2     =" <+> prettyTCM (not notphi1meetsphi2)
        , "psi1 meets psi2     =" <+> prettyTCM (not notpsi1meetspsi2)
        , "phi1isEmpty         =" <+> prettyTCM phi1isEmpty
        , "phi2isEmpty         =" <+> prettyTCM phi2isEmpty
        , "psi1isEmpty         =" <+> prettyTCM psi1isEmpty
        , "psi2isEmpty         =" <+> prettyTCM psi2isEmpty ]

      return $ (notphi1meetsphi2) && (notpsi1meetspsi2) && (phi1isEmpty || psi2isEmpty) && (phi2isEmpty || psi1isEmpty)      


-- MPartial type former.
-- example: (_ : MPartial (i0 ∨ (~ i ∧ j) m∨ (x =bi0) b∨ (x =bi1)) Bool)

primMPartial' :: TCM PrimitiveImpl
primMPartial' = do
  requireBridges ""
  t <- runNamesT [] $
       hPi' "l" (el $ cl primLevel) (\ l ->
        nPi' "ζ" primMCstrType $ \ _ ->
        nPi' "A" (sort . tmSort <$> l) $ \ bA ->
        (sort . tmSSort <$> l))
  mholds <- primMHolds
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 3 $ \ ts -> do
    case ts of
      [l, ζ, bA] -> do
          (El s (Pi d b)) <- runNamesT [] $ do
                             [l, bA, ζ] <- mapM (open . unArg) [l, bA, ζ]
                             elSSet (pure mholds <@> ζ) --> el' l bA
          redReturn $ Pi (setRelevance Irrelevant $ d { domFinite = True }) b
      _ -> __IMPOSSIBLE__



-- * reflecting pure path mixed cstrs as path constraint

-- reflectMCstr : {φ : I} -> .(MHolds φ m∨ bno) -> IsOne φ
primReflectMCstr' :: TCM PrimitiveImpl
primReflectMCstr' = do
  requireBridges "in primReflectMCstr'"
  typ <- runNamesT [] $
    hPi' "φ" primIntervalType $ \ phi ->
    mpPi' "o" (iota phi) $ \ _ ->
    elSSet $ cl isOne <@> phi
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 2 $ \ [phi , dot ] -> do
    sphi <- reduceB phi
    vphi <- intervalView $ unArg $ ignoreBlocking sphi
    yes <- getTerm "" builtinItIsOne    
    case vphi of
      IOne -> redReturn yes
      _ -> return $ NoReduction [ reduced sphi , notReduced dot ]
  where
    isOne = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOne
    iota phi = cl primMkmc <@> phi <@> cl primBno

-- | used to convert a MPartial defined on path cstr, into a Partial.
--   preserve : ∀ {φ : I} → .(IsOne φ) → MHolds (φ m∨ bno)
primPrsvMCstr' :: TCM PrimitiveImpl
primPrsvMCstr' = do
  requireBridges "in primPrsvMCstr'"
  typ <- runNamesT [] $
    hPi' "φ" primIntervalType $ \ phi ->
    pPi' "o" phi $ \ _ ->
    elSSet $ cl mholds <@> (iota phi)
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 2 $ \ [phi , dot] -> do
    sphi <- reduceB phi
    vphi <- intervalView $ unArg $ ignoreBlocking sphi
    yes <- getTerm "" builtinMitHolds
    case vphi of
      IOne -> redReturn yes
      _ -> return $ NoReduction [ reduced sphi , notReduced dot ]
  where
    mholds = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinMHolds
    iota phi = cl primMkmc <@> phi <@> cl primBno
    
-- (elSSet $ cl isOne <@> phi)
-- isOne = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOne



-- \extentArgs@[lA, lB, bA, bB,
--    n0@(Arg n0info n0tm), n1@(Arg n1info n1tm),
--    nn@(Arg nninfo nntm),
--    r@(Arg rinfo rtm0), bM] -> do

-- * auxiliary primitives for mix Kan ops.
--   primEmbd, primMixedOr, primMPartialP prim_mpor

-- | I -> MCstr : φ maps to (φ m∨ bno)
primEmbd' :: TCM PrimitiveImpl
primEmbd' = do
  requireBridges "in primEmbd'"
  typ <- (primIntervalType --> primMCstrType)
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 1 $ \ [ aphi ] -> do
    mkmc <- getTerm "in primEmbd'" builtinMkmc
    bno <- getTerm "in primEmbd'" builtinBno
    redReturn $ mkmc `apply` [ aphi , argN bno ]

-- | MCstr -> MCstr -> MCstr : ζ1 ζ2 map to ζ1 ∨∨ ζ2
--   (disjunction in both the path and the bdg components)
primMixedOr' :: TCM PrimitiveImpl
primMixedOr' = do
  requireBridges "in primMixedOr'"
  typ <- (primMCstrType --> primMCstrType --> primMCstrType)
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 2 $ \ [ azeta1 , azeta2 ] -> do
    myes <- getTerm "in primMixedOr'" builtinMyes
    mkmc <- getTerm "in primMixedOr'" builtinMkmc
    cor <- getTerm "in primMixedOr'" builtinIMax
    bor <- getTerm "in primMixedOr'" builtinBconj
    szeta1 <- reduceB azeta1
    szeta2 <- reduceB azeta2
    case (szeta1 , szeta2) of
      (Blocked{} , _) -> return $ NoReduction $ map reduced [ szeta1 , szeta2 ]
      (_ , Blocked{}) -> return $ NoReduction $ map reduced [ szeta1 , szeta2 ]
      (_, _) -> do
        vzeta1 <- mcstrView $ unArg $ ignoreBlocking szeta1
        vzeta2 <- mcstrView $ unArg $ ignoreBlocking szeta2
        case (vzeta1 , vzeta2) of
          (Mno, _) -> redReturn $ unArg $ ignoreBlocking szeta2
          (_, Mno) -> redReturn $ unArg $ ignoreBlocking szeta1
          (Myes, _) -> redReturn $ myes
          (_, Myes) -> redReturn $ myes
          (Mkmc aphi1 apsi1, Mkmc aphi2 apsi2) -> do
            res <- reduce $ mkmc `apply` [ argN $ cor `apply` [aphi1 , aphi2] , argN $ bor `apply` [apsi1, apsi2] ]
            redReturn $ res
          _ -> return $ NoReduction $ map reduced [ szeta1 , szeta2 ]

-- | MPartialP : ∀ {ℓ} (ζ : MCstr) ≈(A : MPartial ζ (Type ℓ)) → Type ℓ
primMPartialP' :: TCM PrimitiveImpl
primMPartialP' = do
  requireBridges "in primPartialP'"
  t <- runNamesT [] $
       hPi' "l" (el $ cl primLevel) (\ l ->
        nPi' "ζ" primMCstrType $ \ zeta ->
        nPi' "A" (mpPi' "o" zeta $ \ _ -> el' (cl primLevelSuc <@> l) (Sort . tmSort <$> l)) $ \ bA ->
        (sort . tmSSort <$> l))
  let toFinitePi :: Type -> Term
      toFinitePi (El _ (Pi d b)) = Pi (setRelevance Irrelevant $ d { domFinite = True }) b
      toFinitePi _               = __IMPOSSIBLE__
  v <- runNamesT [] $
        lam "l" $ \ l ->
        lam "ζ" $ \ zeta ->
        lam "A" $ \ a ->
        toFinitePi <$> nPi' "p" (elSSet $ cl primMHolds <@> zeta) (\ p -> el' l (a <@> p))
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \ _ -> redReturn v


prim_mpor' :: TCM PrimitiveImpl
prim_mpor' = do
  requireBridges "in prim_mpor'"
  t    <- runNamesT [] $
          hPi' "l" (el $ cl primLevel)    $ \ l  ->
          nPi' "ζ1" primMCstrType $ \ z1  ->
          nPi' "ζ2" primMCstrType $ \ z2  ->
          hPi' "A" (mpPi' "o" (cl primMixedOr <@> z1 <@> z2) $ \o -> el' (cl primLevelSuc <@> l) (Sort . tmSort <$> l)) $ \ bA ->
          (mpPi' "o1" z1 $ \ o1 -> el' l $ bA <..> (cl primMHolds1 <@> z1 <@> z2 <..> o1)) -->
          (mpPi' "o2" z2 $ \ o2 -> el' l $ bA <..> (cl primMHolds2 <@> z1 <@> z2 <..> o2)) -->
          mpPi' "o" (cl primMixedOr <@> z1 <@> z2) (\ o -> el' l $ bA <..> o)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ ts@[l,z1,z2,bA,u,v] -> do
    sz1 <- reduceB' z1
    vz1 <- mcstrView $ unArg $ ignoreBlocking sz1
    case vz1 of
     Myes -> redReturn (unArg u)
     Mno -> redReturn (unArg v)
     _ -> do
       sz2 <- reduceB' z2
       vz2 <- mcstrView $ unArg $ ignoreBlocking sz1
       case vz2 of
         Myes -> redReturn (unArg v)
         Mno -> redReturn (unArg u)
         _ -> return $ NoReduction [notReduced l,reduced sz1,reduced sz2,notReduced bA,notReduced u,notReduced v]

-- (cl primMkmc <@> (cl primIZero) <@> (cl primBno))
primTestPrim' :: TCM PrimitiveImpl
primTestPrim' = do
  requireBridges "in primTestPrim'"
  t    <- runNamesT [] $
          hPi' "l" (el $ cl primLevel)    $ \ l  ->
          nPi' "ζ1" primMCstrType $ \ z1  ->
          nPi' "ζ2" primMCstrType $ \ z2  ->
          hPi' "A" (mpPi' "o" (cl primMixedOr <@> z1 <@> z2) $ \o -> el' (cl primLevelSuc <@> l) (Sort . tmSort <$> l)) $ \ bA ->
          (mpPi' "o1" z1 $ \ o1 -> el' l $ bA <..> (cl primMHolds1 <@> z1 <@> z2 <..> o1)) -->
          (mpPi' "o2" z2 $ \ o2 -> el' l $ bA <..> (cl primMHolds2 <@> z1 <@> z2 <..> o2)) -->
          mpPi' "o" (cl primMixedOr <@> z1 <@> z2) (\ o -> el' l $ bA <..> o)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ ts@[l,z1,z2,bA,u,v] -> do
    sz1 <- reduceB' z1
    vz1 <- mcstrView $ unArg $ ignoreBlocking sz1
    case vz1 of
     Myes -> redReturn (unArg u)
     Mno -> redReturn (unArg v)
     _ -> do
       sz2 <- reduceB' z2
       vz2 <- mcstrView $ unArg $ ignoreBlocking sz1
       case vz2 of
         Myes -> redReturn (unArg v)
         Mno -> redReturn (unArg u)
         _ -> return $ NoReduction [notReduced l,reduced sz1,reduced sz2,notReduced bA,notReduced u,notReduced v]



-- * Kan operations with mixed constraints.

-- primMHComp : ∀ {ℓ} {A : Type ℓ} {ζ : MCstr} (u : ∀ i → MPartial ζ A) (u0 : A) → A
primMHComp' :: TCM PrimitiveImpl
primMHComp' = do
  requireBridges "in primMHComp'"
  t    <- runNamesT [] $
          hPi' "l" (el $ cl primLevel) $ \ l ->
          hPi' "A" (sort . tmSort <$> l) $ \ bA ->
          hPi' "ζ" primMCstrType $ \ zeta ->
          nPi' "i" primIntervalType (\ i -> mpPi' "o" zeta $ \ _ -> el' l bA) -->
          (el' l bA --> el' l bA)
  -- nelims = # of additional elims (ie after u0)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts@[l, bA, zeta@(Arg infZeta zetatm), u@(Arg infU utm), u0] nelims -> do
  reportSDocDocs "tc.prim.mhcomp" 40
    (text "reducing in primMHComp with args...")
    [ "l    = " <+> prettyTCM (unArg l)
    , "A    = " <+> prettyTCM (unArg bA)
    , "zeta = " <+> prettyTCM (unArg zeta)
    , "u    = " <+> prettyTCM (unArg u)
    , "u0   = " <+> prettyTCM (unArg u0)
    , "nelims=" <+> (return $ P.pretty nelims) ]
  sZeta <- reduceB' zeta
  vZeta <- mcstrView $ unArg $ ignoreBlocking sZeta
  let clP s = getTerm (builtinMHComp) s

  case vZeta of
    Myes -> do -- adjusting u0 everywhere.
      ret <- runNamesT [] $ do
               u <- open (unArg u)
               u <@> clP builtinIOne <..> clP builtinMitHolds
      redReturn ret
    _ -> do
      let fallback' :: (Blocked (Arg Term)) -> ReduceM (Reduced MaybeReducedArgs Term)
          fallback' btyp = do
            u' <- case vZeta of
                    -- expect ReduceM (MaybeReduced (Arg Term))
                    -- a nowhere defined adjustement u reduces to canonical u'
                    Mno -> fmap (reduced . notBlocked . argN) . runNamesT [] $ do
                      [l,typ] <- mapM (open . unArg) [l, ignoreBlocking btyp] 
                      lam "i" $ \ i -> clP builtinMHoldsEmpty <#> l
                                             <#> ilam "o" (\ _ -> typ)
                    _     -> return (notReduced u)
            return $ NoReduction $ [notReduced l , reduced btyp , reduced sZeta] ++ [ u' ] ++ [notReduced u0]
      sbA <- reduceB' bA -- :: Blocked (Arg Term)
      let fallback = fallback' (sbA)
          t = ignoreBlocking sbA
      mHComp <- getPrimitiveName' builtinHComp
      mMhocom <- getPrimitiveName' builtinMHComp
      mGlue <- getPrimitiveName' builtinGlue
      mGel <- getPrimitiveName' builtinGel
      mId   <- getBuiltinName' builtinId
      pathV <- pathView'
      bridgeV <- bridgeView'
      case (unArg $ ignoreBlocking sbA) of
        
        MetaV m _ -> do
          reportSLn "tc.prim.mhcomp" 40 $ "in primMHComp, matched type has meta"
          fallback' (blocked_ m *> sbA)
        
        Pi a b
          | nelims > 0  -> do
              reportSLn "tc.prim.mhcomp" 40 $ "in primMHComp, type matched Pi and nelims > 0"
              maybe fallback redReturn =<< mhcompPi (a,b) (ignoreBlocking sZeta) u u0
          | otherwise -> do
              reportSLn "tc.prim.mhcomp" 40 $ "in primMHComp, type matched Pi and nelims == 0"
              fallback
        -- Glue {ℓA ℓB} (A : Set ℓA) {φ' : I} (T : Partial φ' (Set ℓB)) (e: PartialP φ' (λ o → T o ≃ A)) : Set ℓB
        Def q [Apply la, Apply lb, Apply bA, Apply phi', Apply bT, Apply e] | Just q == mGlue -> do
          maybe fallback redReturn =<< mhcompGlue zeta u u0 (la, lb, bA, phi', bT, e) Head

        -- mhocom {ℓ} {Gel A0 A1 R x} {ζ} u u0
        Def q [Apply lgel, Apply bA0, Apply bA1, Apply bR, Apply x] | Just q == mGel -> do
          maybe fallback redReturn =<< mhcompGel (lgel, bA0, bA1, bR, x) sZeta u u0

        -- total (cubical) call is
        -- hcomp {ℓ} {hcomp {-} {Type ℓ} {φ'} (T : ∀ i → Partial φ' (Type ℓ))(A : Type ℓ)} {φ}
        --   (u : ∀ i → Partial φ (hcomp T A) )
        --   (u0 : hcomp T A)
        --  : Type ℓ
        -- u0 is in an adjusted type (along T, on φ'). And we adjust it along u, on φ.
        -- This call should be impossible? the inner hcomp reduces to a mix hcomp.
        Def q [Apply _, Apply s, Apply phi', Apply bT, Apply bA]
          | Just q == mHComp, Sort (Type la) <- unArg s  -> do
          maybe fallback redReturn =<< mhcompHCompU zeta u u0 (argH $ Level la, phi', bT, bA) Head

        -- mhocom {} { mhocom {}{Type ℓ}{φ' = embd φ''} } {ζ}
        Def q [Apply _, Apply s, Apply phi', Apply bT, Apply bA]
          | Just q == mMhocom, Sort (Type la) <- unArg s  -> do
              maybe fallback redReturn =<< mhcompMixHCompU zeta u u0 (argH $ Level la, phi', bT, bA) Head

        -- Path/PathP
        d | PathType _ _ _ bA x y <- pathV (El __DUMMY_SORT__ d) -> do
          reportSLn "tc.prim.mhcomp" 40 "in mhocom reduction, type casing matched PathP"
          if nelims > 0 then mhcompPathP sZeta u u0 l (bA, x, y) else fallback

        -- BridgeP
        d | BridgeType _ _ _ bA x y <- bridgeV (El __DUMMY_SORT__ d) -> do
          reportSLn "tc.prim.mhcomp" 40 "in mhocom reduction, type casing matched BridgeP"
          if nelims > 0 then mhcompBridgeP sZeta u u0 l (bA, x, y) else fallback

        -- for now, it only reduces if zeta is path pure.
        Def q [Apply _ , Apply bA , Apply x , Apply y] | Just q == mId -> do
          maybe fallback return =<< mhcompId sZeta u u0 l (bA, x, y)

        Def q es -> do
          info <- getConstInfo q
          let   lam_i = Lam defaultArgInfo . Abs "i"
            
          case theDef info of
            r@Record{recComp = kit}
                | nelims > 0, Just as <- allApplyElims es, Just mhocomR <- nameOfMHComp kit -> do
                    reportSDoc "tc.prim.mhcomp.rec" 40 $ text "about to compute mhocom at record"
                    redReturn $ (Def mhocomR []) `apply`
                                      (as ++ [ignoreBlocking sZeta, u, u0])
                | Just as <- allApplyElims es, [] <- recFields r -> mhcompData l as sbA sZeta u u0

            Datatype{dataPars = pars, dataIxs = ixs, dataPathCons = pcons, dataTransp = mtrD}
              | null pcons && ixs == 0, Just as <- allApplyElims es -> do
                reportSLn "tc.prim.mhcomp" 40 $ "rule for mhocom at data type (no hit, no index) fired"
                mhcompData l as sbA sZeta u u0

            _ -> fallback

        _ -> fallback
        


mhcompPi :: (Dom Type, Abs Type)
         -- ^ Γ ⊢ a, b. dom and cod of the Pi type at hand.
         -> Arg Term
         -- ^ Γ ⊢ ζ : MCstr
         -> Arg Term
         -- ^ Γ ⊢ u : (i:I) -> MPartial ζ (Pi a b)
         -> Arg Term
         -- ^ Γ ⊢ u0 : Pi a b
         -> ReduceM (Maybe Term)
mhcompPi {- cmd t -} ab zeta u u0 = do
 reportSLn "tc.prim.mhcomp" 40 $ "in primMHComp, reduction for Pi type fired."
 let getTermLocal = getTerm $ builtinMHComp ++ " for function types"
 -- tTrans <- getTermLocal builtinTrans
 tMHComp <- getTermLocal builtinMHComp
 -- tINeg <- getTermLocal builtinINeg
 -- tIMax <- getTermLocal builtinIMax
 -- iz    <- getTermLocal builtinIZero
 let
   toLevel' t = do
     s <- reduce $ getSort t
     case s of
       (Type l) -> return (Just l)
       _        -> return Nothing
   toLevel t = fromMaybe __IMPOSSIBLE__ <$> toLevel' t
 -- make sure the codomain has a level.
 caseMaybeM (toLevel' . absBody . snd $ ab) (return Nothing) $ \ _ -> do
 runNamesT [] $ do
  keepGoing <- do
    s <- reduce $ getSort (fst ab)
    case s of
      Type lx -> return True
      LockUniv -> return True
      IntervalUniv -> do
        a' <- reduceB $ unDom (fst ab)
        mInterval <- getBuiltinName' builtinInterval
        case unEl $ ignoreBlocking a' of
          Def q [] | Just q == mInterval -> return True
          _ -> return False
      _ -> return False
  case keepGoing of
    False -> return Nothing
    True -> Just <$> do --expct NamesT ReduceM Term
      [zeta, u , u0] <- mapM (open . unArg) [zeta, u, u0]
      let a = fst ab
          b = snd ab          
      glam (getArgInfo a) (absName b) $ \ x -> do --x : A
        bT <- (raise 1 b `absApp`) <$> x
        pure tMHComp <#> (Level <$> toLevel bT)
                    <#> pure (unEl                      $ bT)
                    <#> zeta
                    <@> lam "i" (\ i -> ilam "o" $ \ o -> gApply (getHiding a) (u <@> i <..> o) x)
                    <@> (gApply (getHiding a) u0 x)

-- | used for reduction of
--   mhocom {} {Glue A {φ : I} T e} {ψ : MCstr} u u0
mhcompGlue :: PureTCM m =>
           Arg Term
           -- ^ ψ : MCstr, comes from primMHComp call.
           -> Arg Term
           -- ^ u : ∀ i → MPartial ψ (Glue A T e)
           -> Arg Term
           -- ^ u0 : Glue A T e
           -> (Arg Term, Arg Term, Arg Term, Arg Term, Arg Term, Arg Term)
           -- ^ glue args: {ℓA ℓB} (A : Type ℓA) {phi : I} (T : Partial φ (Type ℓB)) (e : PartialP φ (o ↦ T o ≃ A))
           -> TermPosition
           -> m (Maybe Term)
mhcompGlue psi u u0 glueArgs@(la, lb, bA, phi, bT, e) tpos = do
  reportSLn "tc.prim.mhcomp.glue" 40 $ "mhcompGlue was fired"
  let getTermLocal = getTerm $ (builtinMHComp ++ " for " ++ builtinGlue)
  tmpor <- getTermLocal builtin_mpor
  tEmbd <- getTermLocal "primEmbd"
  tMixedOr <- getTermLocal "primMixedOr"
  tIMax <- getTermLocal builtinIMax
  tIMin <- getTermLocal builtinIMin
  tINeg <- getTermLocal builtinINeg
  tMHComp <- getTermLocal builtinMHComp
  tEFun  <- getTermLocal builtinEquivFun
  tglue   <- getTermLocal builtin_glue
  tunglue <- getTermLocal builtin_unglue
  io      <- getTermLocal builtinIOne
  tItIsOne <- getTermLocal builtinItIsOne
  view <- intervalView'
  runNamesT [] $ do
    [psi, u, u0] <- mapM (open . unArg) [psi, u, u0]                         -- psi = ambient MCstr, from mhocom call.
    [la, lb, bA, phi, bT, e] <- mapM (open . unArg) [la, lb, bA, phi, bT, e] -- phi = path cstr :I from Glue call.
    -- headStop tpos phi <-> tpos == Head and φ != i1.
    -- ?we keep going with φ!= 1 only in prim_unglue
    let
      -- la:Lvl, A:Ty l, phi:MCstr, u: ∀ i → MPartial psi A, u0 : A, i:I
      hfill la bA phi u u0 i = pure tMHComp <#> la
                                           <#> bA
                                           <#> (pure tMixedOr <@> phi <@> (pure tEmbd <@> (pure tINeg <@> i)))
                                           <@> lam "j" (\ j -> pure tmpor <#> la <@> phi <@> (pure tEmbd <@> (pure tINeg <@> i)) <@> ilam "o" (\ a -> bA)
                                                 <@> ilam "o" (\ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                 <@> ilam "o" (\ _ -> u0))
                                           <@> u0
      -- i:I, o:.(IsOne phi)
      tf i o = hfill lb (bT <..> o) psi u u0 i
      unglue g = pure tunglue <#> la <#> lb <#> bA <#> phi <#> bT <#> e <@> g
      a1 = pure tMHComp <#> la <#> bA <#> (pure tMixedOr <@> psi <@> (pure tEmbd <@> phi))
                       <@> lam "i" (\ i -> pure tmpor <#> la <@> psi <@> (pure tEmbd <@> phi) <@> ilam "_" (\ _ -> bA)
                             <@> ilam "o" (\ o -> unglue (u <@> i <..> o))
                             <@> ilam "o" (\ o -> pure tEFun <#> lb <#> la <#> (bT <..> o) <#> bA <@> (e <..> o) <@> tf i o))
                       <@> (unglue u0)
      t1 = tf (pure io)
    -- pure tglue <#> la <#> lb <#> bA <#> phi <#> bT <#> e <@> (ilam "o" $ \ o -> t1 o) <@> a1
    
    hres <- t1 (pure tItIsOne)
    eres <- a1 -- PureTCM m => NamesT m ((Term))
    stop <- headStop tpos phi
    reportSDocDocs "tc.prim.mhcomp.glue" 40
      (text $ "mhcompGlue results")
      [ text $ "TermPos was " ++ (show tpos)
      , text $ "returned Nothing (Head, φ ≠ 1): " ++ (show stop)
      , "If somehting was returned, it is one of those:"
      , "Head " <+> (prettyTCM $ toExplicitArgs hres)
      , "Eliminated " <+> (prettyTCM $ toExplicitArgs eres) ]
    
    ifM (headStop tpos phi) (return Nothing) $ Just <$> do
    case tpos of
      Head -> t1 (pure tItIsOne)
      Eliminated -> a1  



mhcompHCompU :: PureTCM m =>
           Arg Term
           -- ^ ψ : MCstr, ambient mixed cstr, comes from primMHComp call.
           -> Arg Term
           -- ^ u : ∀ i → MPartial ψ (hcomp {φ : I} T A)
           -> Arg Term
           -- ^ u0 : hcomp {φ : I} T A
           -> (Arg Term, Arg Term, Arg Term, Arg Term)
           -- ^ inner hcomp args: {ℓ} {φ : I} (T : ∀ i → Partial φ (Type ℓ)) (A : Type ℓ)
           -> TermPosition
           -> m (Maybe Term)
mhcompHCompU psi u u0 (la, phi, bT, bA) tpos = do
  reportSLn "tc.prim.mhcomp.hcomp" 40
    "In primMHComp: case mhocom at hocom type. The inner one should have been reduced to a mhocom (lifted hocom)"
  __IMPOSSIBLE__

-- | reduces only if the inner mhcomp is a ≈lifted hcomp (φ pure-path)
mhcompMixHCompU :: PureTCM m =>
           Arg Term
           -- ^ ψ : MCstr, ambient mixed cstr, comes from primMHComp call.
           -> Arg Term
           -- ^ u : ∀ i → MPartial ψ (mhocom {φ : MCstr} T A)
           -> Arg Term
           -- ^ u0 : mhocom {φ : MCstr} T A
           -> (Arg Term, Arg Term, Arg Term, Arg Term)
           -- ^ inner mhocom args: {ℓ} {φ : MCstr} (T : ∀ i → MPartial φ (Type ℓ)) (A : Type ℓ)
           -> TermPosition
           -> m (Maybe Term)
mhcompMixHCompU psi u u0 inrArgs@(la, mphi, mbT, bA) tpos = do
  reportSDocDocs "tc.prim.mhcomp.mhcomp" 40
    (text "mhcomp at mhcomp rule fired with args")
    [ "ψ = " <+> prettyTCM (unArg psi)
    , "u = " <+> prettyTCM (unArg u)
    , "u0 = " <+> prettyTCM (unArg u0)
    , "innter args (ℓ,φ:MCstr,T,A) are: " <+> prettyTCM (unArg la, unArg mphi, unArg mbT, unArg bA)
    , "tpos :: TermPosition is: " <+> (text $ show tpos) ]
  
  let getTermLocal = getTerm $ (builtinMHComp ++ " for " ++ builtinMHComp ++ "(lifted hcomp)" ++ " of Set")
  io      <- getTermLocal builtinIOne
  iz      <- getTermLocal builtinIZero

  smphi <- reduce mphi
  vmphi <- mcstrView (unArg smphi)
  (keepGoing, phi) <- case vmphi of
    Mno -> return (True, argN iz)
    Myes -> __IMPOSSIBLE__ -- return (True, argN io) --TODO-antva: what if mphi is byes...
    Mkmc pth bdg -> do
      vbdg <- bcstrView (unArg bdg)
      case vbdg of
        Bno -> return (True, pth)
        _ -> return (False, pth)
    _ -> __IMPOSSIBLE__
  if (not keepGoing) then (return Nothing) else do

  tmpor <- getTermLocal builtin_mpor
  tmixOr <- getTermLocal builtinMixedOr
  tEmbd <- getTermLocal builtinEmbd
  tIMax <- getTermLocal builtinIMax
  tIMin <- getTermLocal builtinIMin
  tINeg <- getTermLocal builtinINeg
  -- tHComp <- getTermLocal builtinHComp
  tMHComp <- getTermLocal builtinMHComp
  tTransp  <- getTermLocal builtinTrans
  tglue   <- getTermLocal builtin_glueU
  tunglue <- getTermLocal builtin_unglueU
  tLSuc   <- getTermLocal builtinLevelSuc
  tSubIn <- getTermLocal builtinSubIn
  tItIsOne <- getTermLocal builtinItIsOne
  tPrsvMCstr <- getTermLocal builtinPrsvMCstr
  
  runNamesT [] $ do
    [psi, u, u0] <- mapM (open . unArg) [psi, u, u0]
    [la, mphi, phi, mbT, bA] <- mapM (open . unArg) [la, mphi, phi, mbT, bA]

    let
      -- input phi:MCstr
      hfill la bA phi u u0 i = pure tMHComp <#> la
                                           <#> bA
                                           <#> (pure tmixOr <@> phi <@> (pure tEmbd <@> (pure tINeg <@> i)))
                                           <@> lam "j" (\ j -> pure tmpor <#> la <@> phi <@> (pure tEmbd <@> (pure tINeg <@> i)) <@> ilam "o" (\ _ -> bA)
                                                 <@> ilam "o" (\ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                 <@> ilam "o" (\ _ -> u0))
                                           <@> u0

      tf i o = hfill la (mbT <@> pure io <..> o) psi u u0 i
      -- bAS is (inS A : Type ℓ [ φ ↦ _.A ] )
      bAS = pure tSubIn <#> (pure tLSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <@> bA
      -- why does it not unify ambiguous m0 type var and ambient PureTCM m??
      transp la bA a0 = (pure tTransp) <#> (lam "i" (const la)) <@> (lam "i" bA) <@> (pure iz) <@> a0
      bT = lam "i" (\ i -> ilam "o" (\ o -> mbT <@> i <..> (pure tPrsvMCstr <#> phi <..> o)))
      unglue g = pure tunglue <#> la <#> phi <#> bT <#> bAS <@> g
      a1 = pure tMHComp <#> la <#> bA <#> (pure tmixOr <@> psi <@> mphi)
                       <@> lam "i" (\ i -> pure tmpor <#> la <@> psi <@> mphi <@> ilam "_" (\ _ -> bA)
                             <@> ilam "o" (\ o -> unglue (u <@> i <..> o))
                             <@> ilam "o" (\ o -> transp la (\ i -> mbT <@> (pure tINeg <@> i) <..> o) (tf i o)))
                       <@> unglue u0
      t1 = tf (pure io)
      -- pure tglue <#> la <#> phi <#> bT <#> bAS <@> (ilam "o" $ \ o -> t1 o) <@> a1      

    hres <- t1 (pure tItIsOne)
    eres <- a1
    flag <- headStop tpos phi
    reportSDocDocs "tc.prim.mhcomp.mhcomp" 40
      (text "mhcomp at mhcomp type, results")
      [ "tpos :: TermPos = " <+> (text $ show tpos)
      , "?returned Nothing ( <-> Head, φ ≠ 1): " <+> (text $ show flag)
      , "If smth was returned, it is one of those:"
      , "Head: " <+> (prettyTCM $ toExplicitArgs hres)
      , "Eliminated: " <+> (prettyTCM $ toExplicitArgs eres) ]

    ifM (headStop tpos phi) (return Nothing) $ Just <$> do
    case tpos of
      Eliminated -> a1
      Head       -> t1 (pure tItIsOne)

mhcompPathP ::
        Blocked (Arg Term) -- ^ ψ:MCstr, ambient cstr of mhocom {PathP} call.
        -> Arg Term -- ^ u : (i : I) → MPartial ψ (PathP A x y)
        -> Arg Term -- ^ u0 : PathP A x y
        -> Arg Term -- ^ l : Lvl
        -> (Arg Term, Arg Term, Arg Term)
        -- ^ A : (i:I) → Type ℓ, x : A i0, y : A i1
        -> ReduceM (Reduced MaybeReducedArgs Term)
mhcompPathP spsi u u0 l (bA,x,y) = do
  reportSLn "tc.prim.mhcomp.pathp" 40 "Rule for mhocom at PathP fired."
  let getTermLocal = getTerm $ builtinMHComp ++ " for path types"
  iz <- getTermLocal builtinIZero
  tmhocom <- getTermLocal builtinMHComp
  tINeg <- getTermLocal builtinINeg
  tIMax <- getTermLocal builtinIMax
  tMixedOr <- getTermLocal builtinMixedOr
  tEmbd <- getTermLocal builtinEmbd
  tmpor   <- getTermLocal builtin_mpor
  let
    ineg j = pure tINeg <@> j
    imax i j = pure tIMax <@> i <@> j

    res j psi u u0 l bA x y = 
          pure tmhocom <#> l
                       <#> (bA <@> j)
                       <#> (pure tMixedOr <@> psi <@> (pure tEmbd <@> (ineg j `imax` j)))
                       <@> lam "i'" (\ i ->
                            let or f1 f2 = pure tmpor <#> l <@> f1 <@> f2 <#> lam "_" (\ _ -> bA <@> i) --f1,2 : mcstr
                            in or psi (pure tEmbd <@> (ineg j `imax` j))
                                          <@> ilam "o" (\ o -> u <@> i <..> o <@@> (x, y, j)) -- a0 <@@> (x <@> i, y <@> i, j)
                                          <@> (or (pure tEmbd <@> ineg j) (pure tEmbd <@> j) <@> ilam "_" (const x)
                                                                  <@> ilam "_" (const y)))
                       <@> (u0 <@@> (x, y, j))

  runNamesT [] $ do -- NamesT ReduceM (Reduced MaybeReducedArgs Term)
    [l,u,u0] <- mapM (open . unArg) [l,u,u0]
    psi      <- open . unArg . ignoreBlocking $ spsi
    [bA, x, y] <- mapM (open . unArg) [bA, x, y]

    lamres <- lam "j" (\ j -> res j psi u u0 l bA x y)
    reportSDocDocs "tc.prim.mhcomp.pathp" 40
      (text "mhocom at pathp type, results")
      [ prettyTCM $ toExplicitArgs lamres ]

    YesReduction YesSimplification <$> lam "j" (\ j -> res j psi u u0 l bA x y)

-- | for now, reduces iff φ:MCstr is pure path
--   Please preserve the commented code below.
mhcompId ::
        Blocked (Arg Term) -- ^ φ:MCstr, ambient cstr of mhocom {Id} call.
        -> Arg Term -- ^ u : (i : I) → MPartial φ (Id A x y)
        -> Arg Term -- ^ a0 : Id A x y
        -> Arg Term -- ^ l : Lvl
        -> (Arg Term, Arg Term, Arg Term)
        -- ^ A : Type ℓ, x y : A
        -> ReduceM (Maybe (Reduced MaybeReducedArgs Term))
mhcompId sphi u a0 l (bA , x , y) = do
  let getTermLocal = getTerm $ builtinMHComp ++ " for " ++ builtinId
  vsphi <- mcstrView $ unArg $ ignoreBlocking sphi
  io <- getTermLocal builtinBIZero
  mbno <- getName' builtinBno
  unmix <- case vsphi of
    Mno -> return $ Just io
    Mkmc (Arg _ phi) (Arg _ (Def q [])) | Just q == mbno -> return $ Just phi
    _ -> return Nothing
  case unmix of
    Nothing -> return Nothing
    Just phi -> do
      tHComp <- getTermLocal builtinHComp
      tId <- getTermLocal builtinId
      tPres <- getTermLocal builtinPrsvMCstr
      runNamesT [] $ do
        -- NamesT ReduceM (Maybe (Reduced MaybeReducedArgs Term))
        [l , bA , x , y , phi , u , a0] <- mapM (open . unArg) [l , bA , x , y , argN phi, u , a0]
        let unmix u i o = u <@> i <..> (pure tPres <#> phi <..> o)
            -- NamesT ReduceM Term
            res = pure tHComp <#> l <#> (pure tId <#> l <#> bA <@> x <@> y) <#> phi
               <@> (lam "i" ( \ i -> ilam "o" (\ o -> unmix u i o)))
               <@> a0
        Just <$> YesReduction YesSimplification <$> res
        
  -- unview <- intervalUnview'
  -- mConId <- getName' builtinConId
  -- cview <- conidView'
  -- let isConId t = isJust $ cview __DUMMY_TERM__ t
  -- sa0 <- reduceB' a0
  -- -- wasteful to compute b even when cheaper checks might fail
  -- b <- allComponents (unArg . ignoreBlocking $ sphi) (unArg u) isConId
  -- case mConId of
  --   Just conid | isConId (unArg . ignoreBlocking $ sa0) , b -> (Just <$>) . (redReturn =<<) $ do
  --     tMHComp <- getTermLocal builtinMHComp
  --     -- tTrans <- getTermLocal builtinTrans
  --     tIMin <- getTermLocal "primDepIMin"
  --     tFace <- getTermLocal "primIdFace"
  --     tPath <- getTermLocal "primIdPath"
  --     tPathType <- getTermLocal builtinPath
  --     tConId <- getTermLocal builtinConId
  --     runNamesT [] $ do
  --       let io = pure $ unview IOne
  --           iz = pure $ unview IZero
  --           conId = pure $ tConId
  --       l <- open (Lam defaultArgInfo $ NoAbs "_" $ unArg l)
  --       [p0] <- mapM (open . unArg) [a0]
  --       p <- do
  --         u <- open . unArg $ u
  --         return $ \ i o -> u <@> i <..> o
  --       phi      <- open . unArg . ignoreBlocking $ sphi
  --       [bA, x, y] <- forM [bA,x,y] $ \ a -> open (Lam defaultArgInfo $ NoAbs "_" $ unArg a)
  --       let
  --         eval DoHComp l bA phi u u0 = pure tMHComp <#> (l <@> io) <#> (bA <@> io) <#> phi
  --                                                  <@> u <@> u0
  --       conId <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
  --       -- TODO-antva: primDepIMin (phi : MCstr) ...
  --             <@> (pure tIMin <@> phi
  --                             <@> ilam "o" (\ o -> pure tFace <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
  --                                                              <@> (p io o)))
  --             <@> (eval cmd l
  --                           (lam "i" $ \ i -> pure tPathType <#> (l <@> i) <#> (bA <@> i) <@> (x <@> i) <@> (y <@> i))
  --                           phi
  --                           (lam "i" $ \ i -> ilam "o" $ \ o -> pure tPath <#> (l <@> i) <#> (bA <@> i)
  --                                                                               <#> (x <@> i) <#> (y <@> i)
  --                                                                               <@> (p i o)
  --                                 )
  --                           (pure tPath <#> (l <@> iz) <#> (bA <@> iz) <#> (x <@> iz) <#> (y <@> iz)
  --                                             <@> p0)
  --                 )
  --   _ -> return $ Nothing

  -- where
  --   allComponents phi u p = do
  --     [i0 , i1, bi0, bi1] <- mapM (getTerm "mhocom at Id") [builtinIZero, builtinIOne, builtinBIZero, builtinBIOne]
  --     let boolToInt :: CorBsplit -> Bool -> Term --bool to interval
  --         boolToInt skind = case skind of
  --           CSPLIT -> \ bl -> case bl of
  --             False -> i0
  --             True -> i1
  --           BSPLIT -> \ bl -> case bl of
  --             False -> bi0
  --             True -> bi1
  --     as <- dnfMixedCstr phi
  --     andM . for as $ \ (skind, bs,ts) -> do
  --          let u' = listS (IntMap.toAscList $ IntMap.map (boolToInt skind) bs) `applySubst` u
  --          t <- reduce2Lam u'
  --          return $! p $ ignoreBlocking t
  --   reduce2Lam t = do
  --         t <- reduce' t
  --         case lam2Abs Relevant t of
  --           t -> underAbstraction_ t $ \ t -> do
  --              t <- reduce' t
  --              case lam2Abs Irrelevant t of
  --                t -> underAbstraction_ t reduceB'
  --        where
  --          lam2Abs rel (Lam _ t) = absBody t <$ t
  --          lam2Abs rel t         = Abs "y" (raise 1 t `apply` [setRelevance rel $ argN $ var 0])  
                                   
-- | if u0 / u are not literals, reduce to (applied) auxiliary mhcomp-at-data primitive.
--   The QName of the latter is stored in Defn.Contructor.conComp field.
--   Computational behaviour for this prim is spec. in Rules/Data.hs
mhcompData ::
      -- Maybe QName -- ^ transport-at-data aux prim
      -- -> Bool -- ^ is HIT
      -- -> Nat -- ^ pars + idxs
      -- -> TranspOrHComp
      Arg Term -- ^ lvl
      -> [Arg Term] -- ^ more elims
      -> Blocked (Arg Term) -- ^ data type, simplified
      -> Blocked (Arg Term) -- ^ ambient hcomp constraint, simplified
      -> Arg Term -- ^ u adjustement
      -> Arg Term -- ^ u0
      -> ReduceM (Reduced MaybeReducedArgs Term)
mhcompData l ps sc sphi u a0 = do
  reportSDoc "tc.prim.mhcomp.data" 40 $ text "mhcompData with args"
  reportSDoc "tc.prim.mhcomp.data" 40 $ nest 2 $ vcat
    [ "lvl" <+> (return $ P.pretty l)
    , "extra elims" <+> (return $ P.pretty ps)
    , "the data type" <+> (return $ P.pretty $ ignoreBlocking sc)
    , "the constraint" <+> (return $ P.pretty $ ignoreBlocking $ sphi)
    , "u adjustement " <+> (return $ P.pretty $ u)
    , "base " <+> (return $ P.pretty $ a0) ]
  
  let getTermLocal = getTerm $ builtinMHComp ++ " for data types"
  -- tPOr   <- getTermLocal builtinPOr
  mempty <- getTermLocal builtinMHoldsEmpty
  mpor <- getTermLocal builtin_mpor
  embd <- getTermLocal builtinEmbd
  mixedOr <- getTermLocal builtinMixedOr
  myes <- getTermLocal builtinMyes
  biszero <- getTermLocal builtinBiszero
  bisone <- getTermLocal builtinBisone
  
  iO   <- getTermLocal builtinIOne
  iZ   <- getTermLocal builtinIZero
  mno  <- getTermLocal builtinMno
  tMin <- getTermLocal builtinIMin
  tNeg <- getTermLocal builtinINeg
  let iNeg t = tNeg `apply` [argN t]
      iMin t u = tMin `apply` [argN t, argN u]
      -- iz = pure iZ
  constrForm <- do
    mz <- getTerm' builtinZero
    ms <- getTerm' builtinSuc
    return $ \ t -> fromMaybe t (constructorForm' mz ms t)
  su  <- reduceB' u
  sa0 <- reduceB' a0
  view   <- mcstrView'
  -- unview <- intervalUnview'
  let f = unArg . ignoreBlocking
      phi = f sphi
      a0 = f sa0
      isLit t@(Lit lt) = Just t
      isLit _ = Nothing
      isCon (Con h _ _) = Just h
      isCon _           = Nothing
      combine l ty d [] = d
      combine l ty d [(psi,u)] = u
      combine l ty d ((psi,u):xs)
        = pure mpor <#> l <@> psi <@> foldr (mixmax . fst) (pure mno) xs
                    <#> ilam "o" (\ _ -> ty) -- the type
                    <@> u <@> (combine l ty d xs)
        where
          mixmax zeta1 zeta2 = do
            z1 <- zeta1
            z2 <- zeta2
            return $ mixedOr `apply` [argN z1, argN z2] 
              
      noRed' su = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced su', reduced sa0]
        where
          su' = case view phi of
                 Mno -> notBlocked $ argN $ runNames [] $ do
                             [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
                             lam "i" $ \ i -> pure mempty <#> l
                                                          <#> ilam "o" (\ _ -> c)
                 _     -> su

      sameConHeadBack :: Maybe Term             -- ^ base @a0@ is a literal, in a data type
                         -> Maybe ConHead       -- ^ base @a0@ is instead a constructor
                         -> Blocked (Arg Term)          -- ^ adjustement u, simplified.
                         -> (ConHead
                             -> Blocked (Arg Term)
                             -> ReduceM (Reduced MaybeReducedArgs Term))
                         -- ^ continuation.
                         -> ReduceM (Reduced MaybeReducedArgs Term)
      sameConHeadBack Nothing Nothing su k = noRed' su
      sameConHeadBack lt h su k = do
        reportSDoc "tc.prim.mhcomp.data" 45 $ text "sameConHeadBack with args"
        reportSDoc "tc.prim.mhcomp.data" 45 $ nest 2 $ vcat
          [ "literal? = " <+> (return $ P.pretty lt)
          , "constructor head? = " <+>  (return $ P.pretty h)
          , "simpl. u " <+> (return $ P.pretty $ ignoreBlocking su) ]                                 
        let u = unArg . ignoreBlocking $ su
        -- 3 lists of size #(dnf phi).
        -- b  ≈ [ u[sigma] == (λ i → literal/constructor) | sigma clause subst ]
        -- ts ≈ [ if blocked then Just ( u[sigma] , boolmapof(sigma) ) else Nothing | sigma clause subst ]
        -- skinds = [ kind of clause. cubical or bridge? | clause ]
        (b, ts, skinds) <- allComponentsBack  phi u $ \ t ->
                    (isLit t == lt, isCon (constrForm t) == h)

        let treat mBtIMap = case  mBtIMap of -- Maybe (Blocked Term, IntMap Bool)
              Nothing -> Nothing
              Just (bt,imap) -> Just (ignoreBlocking bt , imap)
        reportSDoc "tc.prim.mhcomp.data" 45 $ text "allComponentBack unview phi u <cont> ="
        reportSDoc "tc.prim.mhcomp.data" 45 $ nest 2 $ vcat
          [ "flag list = " <+> (return $ P.pretty b)
          , "zip us bools = " <+> (return $ P.pretty $ map treat ts )
          , "skinds = " <+> (text $ show skinds) ]
        
        let
          (lit,hd) = unzip b

        if isJust lt && and lit then redReturn a0 else do
        -- if sequence ts == Nothing, return su. else
        su <- caseMaybe (sequence ts) (return su) $ \ ts -> do
          let (us,bools) = unzip ts
          fmap ((sequenceA_ us $>) . argN) $ do
          let
            phis :: [Term]
            phis = for (zip bools skinds) $ \ (m,skind) -> case skind of
                     CSPLIT ->
                       embd `apply` [argN $ foldr (iMin . (\(i,b) -> applyUnless b iNeg $ var i)) iO (IntMap.toList m)]
                     BSPLIT ->
                       case (IntMap.toList m) of
                         [] -> myes
                         [ (i,True) ] -> bisone `apply` [argN $ var i]
                         [ (i,False) ] -> biszero `apply` [argN $ var i]
                         _ -> __IMPOSSIBLE__

          runNamesT [] $ do
            u <- open u
            [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
            phis <- mapM open phis
            us   <- mapM (open . ignoreBlocking) us
            lam "i" $ \ i -> do
              combine l c (u <@> i) $ zip phis (map (\ t -> t <@> i) us)

        reportSDocDocs "tc.prim.mhcomp.data" 45
          (text "sameConHeadBack, before calling <cont>")
          [ "h = " <+> (return $ P.pretty h)
          , "hd = " <+> (return $ P.pretty hd)
          , "isJust h && and hd = " <+> (prettyTCM (isJust h && and hd)) ]
        -- work if base "a0" is a constructor, and adjustment u is a line
        -- along the same constructor.
        if isJust h && and hd then k (fromMaybe __IMPOSSIBLE__ h) su
                  else noRed' su

  sameConHeadBack (isLit a0) (isCon a0) su $ \ h su -> do
        let u = unArg . ignoreBlocking $ su
        Constructor{ conComp = cm } <- theDef <$> getConstInfo (conName h)
        case nameOfMHComp cm of
          Just mhcompD -> redReturn $ Def mhcompD [] `apply`
                                      (ps ++ map argN [phi,u,a0])
          Nothing        -> noRed' su
  where

    -- | second component of result is a list of size #(dnf phi)
    --   For 1 clause, elem :: Maybe (u-restr:: Blocked Term,dirs:: IntMap Bool)
    --   u-restr is u where the current clause has been substituted, using the dirs.
    --
    --   the third arg @p@ is a continuation to produce flags for each clause.
    allComponentsBack :: Term
                      -> Term
                      -> (Term -> a)
                      -> ReduceM ([a], [Maybe (Blocked Term, IntMap Bool)], [CorBsplit])
    allComponentsBack phi u p = do
      [i0 , i1, bi0, bi1] <- mapM (getTerm "mhocom at Id") [builtinIZero, builtinIOne, builtinBIZero, builtinBIOne]
      let
        boolToInt :: CorBsplit -> Bool -> Term --bool to interval
        boolToInt skind = case skind of
          CSPLIT -> \ bl -> case bl of
            False -> i0
            True -> i1
          BSPLIT -> \ bl -> case bl of
            False -> bi0
            True -> bi1
        -- boolToI b = if b then unview IOne else unview IZero
        lamlam t = Lam defaultArgInfo (Abs "i" (Lam (setRelevance Irrelevant defaultArgInfo) (Abs "o" t)))
      -- as :: [ (CorBsplit, IntMap Bool, [Term]) ]
      as <- dnfMixedCstr phi
      (flags,t_alphas, splitKinds) <- fmap unzip3 . forM as $ \ (skind, bs ,ts) -> do
           -- u' is u with current clause bs substituted
           let u' = listS bs' `applySubst` u
               bs' = IntMap.toAscList $ IntMap.map (boolToInt skind) bs
               -- Γ₁, i : I, Γ₂, j : I, Γ₃  ⊢ weaken : Γ₁, Γ₂, Γ₃   for bs' = [(j,_),(i,_)]
               -- ordering of "j,i,.." matters.
           let weaken = foldr (\ j s -> s `composeS` raiseFromS j 1) idS (map fst bs')
           t <- reduce2Lam u'
           reportSDoc "tc.prim.mhcomp.data" 45 $ "allCompoonentsBack, t = " <+> (return $ P.pretty $ ignoreBlocking t)
           constrForm <- do --TODO-antva: constrFrom redefined here just for testing
             mz <- getTerm' builtinZero
             ms <- getTerm' builtinSuc
             return $ \ t -> fromMaybe t (constructorForm' mz ms t)
           reportSDoc "tc.prim.mhcomp.data" 45 $
             "allComponentsBack, constrForm t = " <+> (return $ P.pretty $ constrForm $ ignoreBlocking t)
           return $ (p $ ignoreBlocking t, listToMaybe [ (weaken `applySubst` (lamlam <$> t),bs) | null ts ], skind)
      return $ (flags,t_alphas, splitKinds)

    reduce2Lam t = do
      t <- reduce' t
      case lam2Abs Relevant t of
        t -> underAbstraction_ t $ \ t -> do
           t <- reduce' t
           case lam2Abs Irrelevant t of
             t -> underAbstraction_ t reduceB'
      where
        lam2Abs rel (Lam _ t) = absBody t <$ t
        lam2Abs rel t         = Abs "y" (raise 1 t `apply` [setRelevance rel $ argN $ var 0])  


mhcompBridgeP ::
        Blocked (Arg Term) -- ^ ψ:MCstr, ambient cstr of mhocom {BridgeP} call.
        -> Arg Term -- ^ u : (i : I) → MPartial ψ (BridgeP A x y)
        -> Arg Term -- ^ u0 : BridgeP A x y
        -> Arg Term -- ^ l : Lvl
        -> (Arg Term, Arg Term, Arg Term)
        -- ^ A : (\@tick x:BI) → Type ℓ, x : A bi0, y : A bi1
        -> ReduceM (Reduced MaybeReducedArgs Term)
mhcompBridgeP spsi u u0 l (bA,x,y) = do
  reportSLn "tc.prim.mhcomp.bridgep" 40 "Rule for mhocom at BridgeP fired."
  let getTermLocal = getTerm $ builtinMHComp ++ " for BridgeP types"
  iz <- getTermLocal builtinIZero
  biz <- getTermLocal builtinBIZero
  tmhocom <- getTermLocal builtinMHComp
  bconj <- getTermLocal builtinBconj
  biszero <- getTermLocal builtinBiszero
  bisone <- getTermLocal builtinBisone
  -- tINeg <- getTermLocal builtinINeg
  -- tIMax <- getTermLocal builtinIMax
  tMixedOr <- getTermLocal builtinMixedOr
  mkmc <- getTermLocal builtinMkmc
  -- tEmbd <- getTermLocal builtinEmbd
  tmpor   <- getTermLocal builtin_mpor
  let
    -- ineg j = pure tINeg <@> j
    -- imax i j = pure tIMax <@> i <@> j
    
    -- auxCstr (x:BI) = (x =bi0 b∨ x =bi1)
    auxCstr bvar = pure mkmc <@> (pure iz) <@> (pure bconj <@>  (pure biszero <@> bvar) <@> (pure bisone <@> bvar))
    cstrZero bvar = pure mkmc <@> (pure iz) <@> (pure biszero <@> bvar)
    cstrOne bvar = pure mkmc <@> (pure iz) <@> (pure bisone  <@> bvar)

    res j psi u u0 l bA x y = 
          pure tmhocom <#> l
                       <#> (bA <@> j)
                       <#> (pure tMixedOr <@> psi <@> auxCstr j)
                       <@> lam "i'" (\ i ->
                            let or f1 f2 = pure tmpor <#> l <@> f1 <@> f2 <#> lam "_" (\ _ -> bA <@> i) --f1,2 : mcstr
                            in or psi (auxCstr j)
                                          <@> ilam "o" (\ o -> u <@> i <..> o <@@> (x, y, j)) -- a0 <@@> (x <@> i, y <@> i, j)
                                          <@> (or (cstrZero j) (cstrOne j) <@> ilam "_" (const x)
                                                                  <@> ilam "_" (const y)))
                       <@> (u0 <@@> (x, y, j))

  runNamesT [] $ do -- NamesT ReduceM (Reduced MaybeReducedArgs Term)
    [l,u,u0] <- mapM (open . unArg) [l,u,u0]
    psi      <- open . unArg . ignoreBlocking $ spsi
    [bA, x, y] <- mapM (open . unArg) [bA, x, y]

    lamres <- lam "j" (\ j -> res j psi u u0 l bA x y)
    reportSDocDocs "tc.prim.mhcomp.bridgep" 40
      (text "mhocom at bridgep type, results")
      [ prettyTCM $ toExplicitArgs lamres ]

    YesReduction YesSimplification <$> lam "j" (\ j -> res j psi u u0 l bA x y)


transpBridgeP :: Arg Term -- ^ l : I→Level
              -> (Arg Term, Arg Term, Arg Term)
              -- ^ (bA : I → BI → Type, x : (i:I) → A(i,bi0), y : (i:I) → A(i,bi1))
              --   Arguments of a line of bridges i ↦ BridgeP (λ r → A(i,r)) x(i) y(i)
              -> Blocked (Arg Term) -- ^ reduced transport (path) cofib φ
              -> Arg Term -- ^ base bridge u0
              -> ReduceM (Reduced MaybeReducedArgs Term)
-- transpBridgeP _ _ _ _ = __IMPOSSIBLE__              
transpBridgeP l (bA, x , y) phi u0 = do
  reportSDocDocs "tc.prim.transp.bridge" 40
    (text "rule for transporting at BridgeP fired with args...")
    [ "level l = " <+> (return $ P.pretty l)
    , "A : I → BI → Type is " <+> (return $ P.pretty  bA)
    , "x : i:I → A (i, bi0) = " <+> (return $ P.pretty x)
    , "y : i:I → A (i, bi0) = " <+> (return $ P.pretty y)
    , "path cofib φ is " <+> (prettyTCM phi)
    , "base u0 is " <+> (prettyTCM u0) ]
  
  let getTermLocal = getTerm "transport for bridge types"
  iz <- getTermLocal builtinIZero
  io <- getTermLocal builtinIOne
  mixedOr <- getTermLocal builtinMixedOr
  mkmc <- getTermLocal builtinMkmc
  bno <- getTermLocal builtinBno
  biszero <- getTermLocal builtinBiszero
  bisone <- getTermLocal builtinBisone

  -- Transport in bridge types becomes mixed /CCHM/ composition in the
  -- underlying line of spaces. The intuition is that not only do we
  -- have to fix the endpoints (using composition) but also actually
  -- transport. mixed CCHM composition conveniently does that for us!
  -- rem. : CCHM = heterogeneous.

  redReturn <=< runNamesT [] $ do
    -- In reality to avoid a round-trip between primComp we use mkComp
    -- here.
    comp <- mkMhecom $ "transport for bridge types"
    [l, u0, phi] <- traverse (open . unArg) [l, u0, ignoreBlocking phi]
    [bA, x, y] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [bA, x, y]

    let phiAsMixed phi = pure mkmc <@> phi <@> (pure bno)
        bvarZero bvar = pure mkmc <@> (pure iz) <@> (pure biszero <@> bvar)
        bvarOne bvar = pure mkmc <@> (pure iz) <@> (pure bisone <@> bvar)
        -- embdI φ ∨∨ (iz m∨ (j =bi1)) ∨∨  (iz m∨ (j =bi0))
        combineCstrs phi bvar = (pure mixedOr) <@> (phiAsMixed phi) <@> ((pure mixedOr) <@> (bvarOne bvar) <@> (bvarZero bvar))

    let res = 
          lam "j" $ \ j -> -- j:BI
            comp l (lam "i" $ \ i -> bA <@> i <@> j)
              (combineCstrs (phi) j)
              (lam "i'" $ \i -> mixCombineSys l (bA <@> i <@> j) -- i : I
                [ (phiAsMixed phi, ilam "o" (\o -> u0 <@@> (x <@> pure iz, y <@> pure iz, j)))
                -- Note that here we have lines of endpoints which we must
                -- apply to fix the endpoints:
                , (bvarOne j, ilam "_" (const (y <@> i))) -- pure bisone <@> j
                , (bvarZero j, ilam "_" (const (x <@> i))) -- pure biszero <@> j
                ])
              (u0 <@@> (x <@> pure iz, y <@> pure iz, j))

    rres <- res
    reportSDocDocs "tc.prim.transp.bridge" 40
      (text "transport at bridgep type, results")
      [ prettyTCM $ toExplicitArgs rres ]
    res


-- | Constructs a helper for heterogeneous, mixed composition, with a string indicating
--   what function uses it.
mkMhecom :: HasBuiltins m => String -> NamesT m (NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term)
mkMhecom s = do
  let getTermLocal = getTerm s
  tIMax  <- getTermLocal builtinIMax
  tINeg  <- getTermLocal builtinINeg
  -- tHComp <- getTermLocal builtinHComp
  mhocom <- getTermLocal builtinMHComp
  tTrans <- getTermLocal builtinTrans
  iz     <- getTermLocal builtinIZero
  io     <- getTermLocal builtinIOne

  let
    forward la bA r u = pure tTrans
      <#> (lam "i" $ \i -> la <@> (i `imax` r))
      <@> (lam "i" $ \i -> bA <@> (i `imax` r))
      <@> r
      <@> u

  -- phi : MCstr, u : ∀i → MPartial φ (A i), u0 : A i0
  pure $ \la bA phi u u0 ->
    pure mhocom <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                <@> lam "i" (\i -> ilam "o" $ \o ->
                        forward la bA i (u <@> i <..> o))
                <@> forward la bA (pure iz) u0


-- | Builds a mixed partial element. The type of the resulting partial element
-- can depend on the computed extent, which we denote by @φ@ here. Note
-- that @φ@ is the n-ary disjunction of all the @ψ@s.
mixCombineSys
  :: HasBuiltins m
  => NamesT m Term -- The level @l : Level@
  -> NamesT m Term -- The type @A : Partial φ (Type l)@.
  -> [(NamesT m Term, NamesT m Term)]
  -- ^ A list of @(ψ, PartialP ψ λ o → A (... o ...))@ mappings. Note
  -- that by definitional proof-irrelevance of @IsOne@, the actual
  -- injection can not matter here.
  -> NamesT m Term
mixCombineSys l ty xs = snd <$> mixCombineSys' l ty xs

-- | Builds a mixed partial element, and compute its extent. See 'combineSys'
-- for the details.
mixCombineSys'
  :: forall m. HasBuiltins m
  => NamesT m Term -- The level @l@
  -> NamesT m Term -- The type @A@
  -> [(NamesT m Term, NamesT m Term)]
  -> NamesT m (Term,Term)
mixCombineSys' l ty xs = do
  -- tPOr <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPOr
  mpor <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtin_mpor
  mixedOr <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinMixedOr
  mempty <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinMHoldsEmpty
  mno <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinMno
  -- tMax <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIMax
  -- iz <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIZero
  -- tEmpty <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIsOneEmpty

  let
    -- phi, psi : MCstr
    mkMpor l ty phi psi u0 u1 = pure mpor
      <#> l <@> phi <@> psi <#> (ilam "o" $ \ _ -> ty)
      <@> u0 <@> u1

    -- In one pass, compute the disjunction of all the cofibrations and
    -- compute the prim^mpor expression.
    combine :: [(NamesT m Term, NamesT m Term)] -> NamesT m (Term, Term)
    combine [] = (mno,) <$> (pure mempty <#> l <#> (ilam "o" $ \ _ -> ty))
    combine [(psi, u)] = (,) <$> psi <*> u
    combine ((psi, u):xs) = do
      (phi, c) <- combine xs
      (,) <$>  (pure mixedOr <@> psi <@> (pure phi) )<*> mkMpor l ty psi (pure phi) u (pure c)
  combine xs


transpGel ::
          PureTCM m
          => Arg Term -- ^ l : I → Level
          -> (Arg Term, Arg Term, Arg Term, Arg Term, Arg Term)
          -- ^ lgel = i.l i, bA0 bA1 : i.Type(lgel), R : i. A0(i)→A1(i)→Type(lgel), i.r : BI
          -> Blocked (Arg Term) -- ^ path cofib for transport
          -> Arg Term -- ^ base u0 : Gel A0 A1 R r [i0/i]. may mention r.
          -> m (Maybe Term)
transpGel l (lgel, bA0, bA1, bR, r@(Arg rinfo rtm@(Var ri [])) ) phi u0 = do -- 
  
  reportSDocDocs "tc.prim.transp.gel" 40 (text "rule for transporting at Gel fired with args...") $
    [ "transp __l__ :" <+> (return $ P.pretty l)
    , "lgel = " <+> (return $ P.pretty lgel)
    , "A0 is " <+> (return $ P.pretty bA0)
    , "A1 is " <+> (return $ P.pretty bA1)
    , "R is " <+> (return $ P.pretty bR)
    , "r is " <+> (return $ P.pretty r)
    , "phi is " <+> (return $ P.pretty $ ignoreBlocking phi)
    , "base u0 is " <+> (return $ P.pretty u0) ]

  let getTermLocal = getTerm "transport for Gel"
  gel <- getTermLocal builtin_gel
  ungel <- getTermLocal builtin_ungel
  neg <- getTermLocal builtinINeg
  max <- getTermLocal builtinIMax
  bi0 <- getTermLocal builtinBIZero
  bi1 <- getTermLocal builtinBIOne
  trsp <- getTermLocal builtinTrans
  i0 <- getTermLocal builtinIZero
  i1 <- getTermLocal builtinIOne


  
  -- will be used for u0
  let
    ldArgInfo = setLock IsLock defaultArgInfo
    -- | precond: Γ0 , r:BI , Γ1 ⊢ M : ... and (semiFreshForFvars M @r) then
    --   postcond      Γ0, r:BI, Γ1 ⊢ (captureIn M @r) : (@tick r'' : BI) -> ...    
    captureIn m ri =
      let sigma = ([var (i+1) | i <- [0 .. ri - 1] ] ++ [var 0]) ++# raiseS (ri + 2) in
      Lam ldArgInfo $ Abs "r" $ applySubst sigma m

  -- TODO-antva: we capture r in u0. Hence some freshness condition must be checked (Γ \ r , r ⊢ u0)
  -- TODO-antva: we check freshness in whnf(u0). this is sound but not complete. something similar happens
  --             in extent (although extent return a less computed term? sound??)
  su0 <- reduceB u0
  let fvu0 = allVars $ freeVarsIgnore IgnoreNot $ ignoreBlocking su0
  reportSDocDocs "tc.prim.transp.gel" 40 (text "about to check semifreshness at fvu0 (ri - 1)")
    [ "fv u0 = " <+> (return $ P.pretty fvu0)
    , "ri = " <+> (return $ P.pretty ri)
    , "ri -1 = " <+> (return $ P.pretty (ri - 1)) ]  
  fresh <- semiFreshForFvars fvu0 (ri - 1) -- r must be shifted because it was under a path variable
  case fresh of
    False -> do
      reportSDoc "tc.prim.transp.gel" 40 $ text "transport at Gel, semifreshness check failed"
      return Nothing -- TODO-antva: how about returning warnings when freshness fails?
      
    True -> do
      reportSDoc "tc.prim.transp.gel" 40 $ text "transport at Gel, semifreshness check passed"
      
      -- TODO-antva su0 instead? (same dilemma in extent)
      let rBindsU0 = captureIn (unArg u0) (ri - 1)

      -- res :: Term
      res <- runNamesT [] $ do

        [l, phi, u0] <- mapM (open . unArg) [l, ignoreBlocking phi, u0]
        [lgel, bA0, bA1, bR, r] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [lgel, bA0, bA1, bR, r]
        [gel, trsp, rU0, bi0, bi1, neg, max, ungel, i0, i1] <- mapM (open) [gel, trsp, rBindsU0, bi0, bi1, neg, max, ungel, i0, i1]

        let gelLHS = trsp <#> l <@> bA0 <@> phi <@> (rU0 <@> bi0)
            gelRHS = trsp <#> l <@> bA1 <@> phi <@> (rU0 <@> bi1)
            gelRelPrf =
              trsp <#> l <@> lam "y" (\y -> bR <@> y
                                <@> ( trsp <#> l <@> bA0 <@> (max <@> (neg <@> y) <@> phi) <@> (rU0 <@> bi0) )
                                <@> ( trsp <#> l <@> bA1 <@> (max <@> (neg <@> y) <@> phi) <@> (rU0 <@> bi1) ) )
                         <@> phi
                         <@> (ungel <@> rU0)

        gel <#> (lgel <@> i1) <#> (bA0 <@> i1) <#> (bA1 <@> i1) <#> (bR <@> i1) -- TODO-antva: one day R will be an explicit arg of gel?
            <@> gelLHS <@> gelRHS <@> gelRelPrf <@> (r <@> i1)

      reportSDocDocs "tc.prim.transp.gel" 40
        (text "transport at gel, results...")
        [ prettyTCM $ toExplicitArgs res
        , "r binds u is " <+> (return $ P.pretty rBindsU0)]

      return $ Just res
  
transpGel _ _ _ _ = do
  return Nothing


getMCstrBack :: PureTCM m => String -> [ (CorBsplit, IntMap Bool) ] -> m Term
getMCstrBack msg clauses = do
  zeta <- getMCstrBack' msg clauses
  szeta <- reduce zeta
  return szeta

-- | Converts a list of clauses to an MCstr term. IntMap Bool denotes a conjunction.
--   You may want to reduce the resulting constraint (see getMCstrBack)
getMCstrBack' :: PureTCM m => String -> [ (CorBsplit, IntMap Bool) ] -> m Term
getMCstrBack' msg [] = do
  let getTermLocal = getTerm msg
  mno <- getTermLocal builtinMno
  return mno
getMCstrBack' msg  ( (skind, conjBools) : rest ) = do
  let getTermLocal = getTerm msg
  i1 <- getTermLocal builtinIOne
  i0 <- getTermLocal builtinIZero
  bi0 <- getTermLocal builtinBIZero
  mkmc <- getTermLocal builtinMkmc
  mixedOr <- getTermLocal builtinMixedOr
  neg <- getTermLocal builtinINeg
  iand <- getTermLocal builtinIMin
  bisone <- getTermLocal builtinBisone
  biszero <- getTermLocal builtinBiszero
  byes <- getTermLocal builtinByes
  bno <- getTermLocal builtinBno

  let
    -- gives j, or ~j for j db index, in CSPLIT case
    -- else: j =bi1 or j =bi0
    keyBoolAsCstr :: CorBsplit -> (Int, Bool) -> Term
    keyBoolAsCstr CSPLIT ( dbi , bl ) = 
      case bl of
        True -> Var dbi []
        False -> neg `apply` [argN $ Var dbi [] ]
    keyBoolAsCstr BSPLIT ( dbi , bl ) = 
      case bl of
        True -> bisone `apply` [argN $ Var dbi [] ]
        False -> biszero `apply` [argN $ Var dbi [] ]

    -- neutral of conjunction
    neutral :: CorBsplit -> Term
    neutral CSPLIT = i1
    neutral BSPLIT = byes

    -- for foldr call below
    builderCsplit :: (Int,Bool) -> Term -> Term
    builderCsplit  (dbi, bl) prev =
      iand `apply` [argN prev, argN $ keyBoolAsCstr CSPLIT (dbi , bl)]

    iota :: CorBsplit -> Term -> Term
    iota CSPLIT phi = mkmc `apply` [argN phi, argN bno]
    iota BSPLIT psi = mkmc `apply` [argN i0, argN psi]

    -- foldr :: ( (Int, Bool)  -> Term -> Term) -> Term -> [(Int, Bool)] -> Term
    conjBoolsAsCstr =
      case skind of
        CSPLIT -> foldr builderCsplit (neutral CSPLIT) (IntMap.toList conjBools)
        BSPLIT -> case (IntMap.toList conjBools) of
          [] -> neutral BSPLIT
          [ (dbi , bl) ] -> keyBoolAsCstr BSPLIT (dbi, bl)
          _ -> __IMPOSSIBLE__

    asMCstr = iota skind conjBoolsAsCstr

  restMCstr <- getMCstrBack' msg rest
  return $ mixedOr `apply` [argN asMCstr, argN $ restMCstr]         
      
  

-- | ∀-mcstr : ((@tick x : BI) → MCstr) → MCstr
--   deletes all clauses mentionning x:BI from input.
primAllMCstr' :: TCM PrimitiveImpl
primAllMCstr' = do
  requireBridges "in primAllMCstr'"
  typ <- (primBridgeIntervalType -->* primMCstrType) --> primMCstrType
  
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 1 $ \ [ absZeta ]  -> do
    let getTermLocal = getTerm "in primAllMCstr'"
    biType <- getTermLocal builtinBridgeInterval

    mMkmc <- getPrimitiveName' builtinMkmc
    mMno <- getPrimitiveName' builtinMno
    mMyes <- getPrimitiveName' builtinMyes -- Maybe QName
    
    sAbsZeta <- reduceB absZeta
    
    ctx <- getContext
    reportSDocDocs "tc.prim.allmcstr" 30 (text "Calling ∀-mcstr reduction  with args...")
      [ "absZeta is  " <+> (return $ P.pretty absZeta)
      , "sAbsZeta is " <+> (return $ P.pretty (ignoreBlocking sAbsZeta))
      , "ambient ctx " <+> (return $ P.pretty ctx) ]
    
    case (unArg $ ignoreBlocking sAbsZeta) of
      
      Lam inf bod -> underAbstractionAbs (defaultNamedArgDom inf (absName bod) (El LockUniv biType)) bod $ \ body -> do
        sBody <- reduceB body

        ctx <- getContext
        reportSDocDocs "tc.prim.allmcstr" 30 (text "absZeta is a lambda")
          [ "ambient ctx " <+> (return $ P.pretty ctx)
          , "sBody       " <+> (return $ P.pretty $ ignoreBlocking sBody) ]
        
        case sBody of
          Blocked{} -> fallback sAbsZeta
          _ -> do
            case (ignoreBlocking sBody) of
              Def q [ _ , _ ] | Just q == mMkmc || Just q == mMno || Just q == mMyes -> do
                clauses <- dnfMixedCstr $ ignoreBlocking sBody
                -- the res should retain the clauses:
                --   whose conjBools do not mention db var @0
                --   :: [ (CorBsplit, IntMap Bool, [Term]) ]
                let remainingClauses =
                      flip filter clauses $ \ (skind, conjBools, blks) ->
                        if not (blks == []) then __IMPOSSIBLE__ else
                          case (IntMap.lookup 0 conjBools) of
                            Just _ -> False -- current clause mentions db var @0
                            Nothing -> True

                reportSDocDocs "tc.prim.allmcstr" 30 (text "remainingClauses") $
                  flip map remainingClauses $ \ (skind, conjBools, blks) -> (text $ show skind) <+> " ; "  <+> (return $ P.pretty conjBools) <+> " ; " <+>  (return $ P.pretty blks)
                -- we have to strengthen the resulting MCstr (which does not mention @0 bvar by construction)
                res0 <- getMCstrBack "in primAllMCstr'" (map (\ (skind, conjBools, blks) -> (skind, conjBools)) remainingClauses)
                let res  = strengthenS impossible 1 `applySubst` res0
                reportSDoc "tc.prim.allmcstr" 30 $ "reduction result is " <+> (return $ P.pretty res)
                redReturn res

              mcstrVar@(Var dbj []) | dbj > 0 -> do -- body does not depend on db var @0
                redReturn $ strengthenS impossible 1 `applySubst` mcstrVar

              _ -> fallback sAbsZeta

      _ -> fallback sAbsZeta

  where

    fallback sabszeta = return $ NoReduction [reduced sabszeta]


-- | ∀-mcstr-ε : {absζ : @BI → MCstr} → .MHolds (∀-mcstr absζ) → (x : @BI) → MHolds (absζ x)
primAllMCstrCounit' :: TCM PrimitiveImpl
primAllMCstrCounit' = do
  requireBridges "in primAllMCstrCounit'"
  typ <- runNamesT [] $
    hPi' "absζ" (cl $ primBridgeIntervalType -->* primMCstrType) $ \absZeta ->
    mpPi' "oall" ((cl  primAllMCstr) <@> absZeta) $ \oall ->
    lPi' "x" (cl primBridgeIntervalType) $ \x -> --NamesT _ Type
    elSSet $ (cl mholds) <@> (absZeta <@*> x)
    
  -- TODO-antva: prsv, reflect, and this prim. sound impl?
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 3 $ \ [ absZeta , oall , x ] -> do
    mitholds <- getTerm "in primAllMCstrCounit'" builtinMitHolds
    sAbsZeta <- reduceB absZeta
    sAbsZetaX <- reduce $ (unArg $ ignoreBlocking sAbsZeta) `apply` [x]
    v <- mcstrView sAbsZetaX
    case v of
      Myes -> redReturn mitholds
      _ -> return $ NoReduction [reduced sAbsZeta, notReduced oall, notReduced x]
      
  where
    mholds = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinMHolds

-- |  Γ (\ x) ⊢ (l:Level), (A0, A1 : Type), (R : A0 -> A1 ->Type l)
--    Γ ⊢ (x:BI)
--    Γ (\x, x) ⊢ (ζ : MCstr)
--    Γ (\x, x) ⊢ u0 : Gel A0 A1 R x
--    Γ  ⊢ u : ∀ i -> MPartial ζ (Gel A0 A1 R x) + ?semifreshness cond.
mhcompGel :: PureTCM m =>
          (Arg Term, Arg Term, Arg Term, Arg Term, Arg Term)
          -- ^ gel args: l, A0, A1, R, x
          -> Blocked (Arg Term) -- ^ simplified ambient constraint zeta
          -> Arg Term -- ^ adjustment u : ∀ i -> MPartial zeta (Gel A0 A1 R x)
          -> Arg Term -- ^ u0 : Gel A0 A1 R x
          -> m (Maybe Term)
mhcompGel (l, bA0, bA1, bR, x@(Arg _ (Var dbi []))) szeta u u0 = do
  ctx <- getContext
  reportSDocDocs "tc.prim.mhcomp.gel" 30 (text "rule for mhocom at Gel (maybe) firing with args...")
    [ "l  = " <+> (prettyTCM $ toExplicitArgs $ unArg l)
    , "A0 = " <+> prettyTCM bA0
    , "A1 = " <+> prettyTCM bA1
    , "bR = " <+> prettyTCM bR
    , "x  = " <+> prettyTCM x
    , "zeta=" <+> (prettyTCM $ toExplicitArgs $ unArg (ignoreBlocking szeta))
    , "u  = " <+> prettyTCM u
    , "u0 = " <+> prettyTCM u0
    , "ambient ctx" <+> prettyTCM ctx]

  -- we need to capture x in tm = zeta, u0 and u applied to various stuff, in various contexts
  -- we can soundly do this only if x is semifresh in tm
  -- TODO-antva: as usual, we soundly check semifreshness in whnf(tm), but this is not
  -- computationally complete wrt CH type thy.
  -- also if tm is reduced a certain way (tm -> tm'), then only tm' should be used
  -- in reduction results(?). TODO-antva: the latter is often not respected in reduction rules
  -- where semifreshness checks occur.

  su0 <- reduceB u0

  let [fvZeta, fvU0] = map (allVars . (freeVarsIgnore IgnoreNot) . unArg . ignoreBlocking) [szeta, su0]

  semiFreshZeta <- semiFreshForFvars fvZeta dbi
  semiFreshU0   <- semiFreshForFvars fvU0 dbi

  reportSDocDocs "tc.prim.mhcomp.gel" 30 (text "in mhocom at Gel, semifreshness analyses of zeta, u0...")
    [ text "----"
    , "szeta  = " <+> (return $ P.pretty $ ignoreBlocking szeta)
    , "fvZeta = " <+> (return $ P.pretty fvZeta)
    , "semiFreshZeta = " <+> (text $ show semiFreshZeta)
    , text "----"
    , "su0  = " <+> (return $ P.pretty $ ignoreBlocking su0)
    , "fvU0 = " <+> (return $ P.pretty fvU0)
    , "semiFreshU0 = " <+> (text $ show semiFreshU0) ]


  case (semiFreshZeta && semiFreshU0) of -- local semifreshness checks of @u smth smth@ may still fail
    False -> return Nothing
    True -> do -- m (Maybe Term)

      -- I think its easier to do all local semifreshenss checks here, and build captured applied-u terms as well.

      let
        -- | Pure function used for (now sound) capturing in zeta, u0. Another function will be used for capturing in u applied to some elims.
        --   precond: Γ0 , r:BI , Γ1 ⊢ M : ... and (semiFreshForFvars M @r) then
        --   postcond      Γ0, r:BI, Γ1 ⊢ (captureIn M @r) : (@tick r'' : BI) -> ...
        captureIn m ri =
          let sigma = ([var (i+1) | i <- [0 .. ri - 1] ] ++ [var 0]) ++# raiseS (ri + 2) in
          Lam lkDefaultArgInfo $ Abs "r" $ applySubst sigma m

        -- precond respected thanks to previous semifreshness analyses.
        xBindedZeta = captureIn (unArg $ ignoreBlocking szeta) dbi
        xBindedU0 = captureIn (unArg $ ignoreBlocking su0) dbi


        -- | Let Γ = Γ0, x ,Γ1 the ambient ctx when starting mhcompGel. We have Γ ⊢ u (ie vars in u refers to things in Gamma)
        --   The present func returns a term with capture:
        --     Γ, Γ' ⊢ <x>(u arg1) or
        --     Γ, Γ' ⊢ <x>(u arg1 arg2) if there is a second arg
        --   where Γ, Γ' ⊢ arg1, arg2.
        --
        --   Pre: Γ, Γ' ⊢ arg1, arg2.
        --   Pre: appropriate semifreshness checks have been performed (required for sound capturing)
        --   Post: This function does not alter the current context
        captureU :: PureTCM m =>
             Int -- ^ size of Γ'
          -> NamesT  m Term -- ^ arg1
          -> Maybe (NamesT m Term) -- ^ marg2
          -> NamesT m Term
        captureU n arg1 marg2 = do
          cur <- currentCxt
          let wku = inCxt [] (unArg u) -- Γ, Γ' ⊢ u --TODO-antva I think dumb wk can not be mixed with NamesT m monad.
              uApp0 = runNamesT cur $ case marg2 of --uApp :: PureTCM m => m Term
                Nothing -> wku <@> arg1
                Just arg2 -> wku <@> arg1 <..> arg2 --only need irrelevant arg if isJust marg2
          uApp <- lift $ uApp0
          let res = captureIn uApp (dbi + n)
          reportSDocDocs "tc.prim.mhcomp.gel" 30 (text "captureU results..")
            [ "cur = " <+> (return $ P.pretty cur)
            , "res = " <+> (return $ P.pretty res) ]      
          return res

      
      --   -- some useful monadic operations in PureTCM m => NamesT ( MaybeT m )
      --   -- Semifreshness checks for applied u must be performed in context
      --   -- This may result in a failure, hence the Maybe layer.
      --   getTermLocal :: PureTCM m => String -> NamesT (MaybeT m) (NamesT (MaybeT m) Term)
      --   getTermLocal str = do
      --     res <- getTerm "in mhocom at Gel" str
      --     open res            
          

      -- resNew <- runMaybeT $ runNamesT [] $ do -- NamesT (MaybeT m) Term
      --   gel <- getTermLocal builtin_gel
      --   mhocom <- getTermLocal builtinMHComp
      --   l <- open $ unArg l
      --   bA0 <- open $ unArg bA0
      --   bA1 <- open $ unArg bA1
      --   bR <- open $ unArg bR
      --   xBindedZeta <- open $ xBindedZeta
      --   bi0 <- getTermLocal builtinBIZero
      --   bi1 <- getTermLocal builtinBIOne
      --   u <- open $ unArg $ u
      --   xBindedU0 <- open $ xBindedU0
      --   mhecom <- mkMhecom "in mhocom at Gel"
      --   allMCstr <- getTermLocal builtinAllMCstr
      --   embd <- getTermLocal builtinEmbd
      --   ineg <- getTermLocal builtinINeg
      --   mpor <- getTermLocal builtin_mpor
      --   iand <- getTermLocal builtinIMin
      --   ungel <- getTermLocal builtin_ungel
      --   epsi <- getTermLocal builtinAllMCstrCounit
      --   mor <- getTermLocal builtinMixedOr --different than mkmc. mor : MCstr -> MCstr -> MCstr
      --   x <- open $ unArg x        
      --   return $ Dummy "" []


      reportSDocDocs "tc.prim.mhcomp.gel" 30 (text "capturing in constraint zeta and base u0...")
        [ "Γ(\\x) ⊢ <x>zeta is  " <+> (return $ P.pretty xBindedZeta)
        , "Γ(\\x) ⊢ <x>u0 is "   <+> (return $ P.pretty xBindedU0) ]       

      res <- runNamesT [] $ do --PureTCM m => namesT m (Maybe Term)
        let getTermLocal = \ str -> do
              res <- getTerm "in mhocom at Gel" str
              open res
        gel <- getTermLocal builtin_gel
        mhocom <- getTermLocal builtinMHComp
        l <- open $ unArg l
        bA0 <- open $ unArg bA0
        bA1 <- open $ unArg bA1
        bR <- open $ unArg bR
        xBindedZeta <- open $ xBindedZeta
        bi0 <- getTermLocal builtinBIZero
        bi1 <- getTermLocal builtinBIOne
        -- u <- open $ unArg $ u
        xBindedU0 <- open $ xBindedU0
        mhecom <- mkMhecom "in mhocom at Gel"
        allMCstr <- getTermLocal builtinAllMCstr
        embd <- getTermLocal builtinEmbd
        ineg <- getTermLocal builtinINeg
        mpor <- getTermLocal builtin_mpor
        iand <- getTermLocal builtinIMin
        ungel <- getTermLocal builtin_ungel
        epsi <- getTermLocal builtinAllMCstrCounit
        mor <- getTermLocal builtinMixedOr --different than mkmc. mor : MCstr -> MCstr -> MCstr
        x <- open $ unArg x
              
              
        -- -- assume Γ0,x , Γ1 ⊢ u (ctx = Γ)
        -- --  Γ, i:I ⊢ i:I. This function returns Γ, i ⊢ <x> (u i)
        -- -- lamn = size Γ' - size Γ, ie under how many extra lambdas are we applying u
        -- -- TODO-antva: must do the semifreshness check for u here instead (see captureIn precond)
        -- let captureUat i lamn = do
        --       -- u makes sense in Γ. i in Γ'. therefore its meaningless to simply apply u to i
        --       ui <- u <@> i -- Term
        --       return $ captureIn ui (dbi + lamn)


        --     -- needed for gelPrf adjustment
        --     captureUat' i o lamn = do
        --       uio <- u <@> i <..> o
        --       return $  captureIn uio (dbi + lamn)
        let

            bA bl = case bl of
              False -> bA0              
              True -> bA1

            bi bl = case bl of
              False -> bi0
              True -> bi1

            -- mhocom {} {Gel A0 A1 R x} {zeta} u u0 = gel (gelSide False) (gelSide True) gelPrf x
            -- where gelPrf is a mixed het. comp along λ y . R (Pline0 y) (Pline1 y)  and where
            -- Pline0, Pline1 are mhocom fillers at y

            -- Γ ⊢ gelSide bl : Aeps
            gelSide (bl :: Bool) = mhocom <#> l <#> (bA bl) <#> (xBindedZeta <@> (bi bl))
              <@> (lam "i" $ \i -> (captureU 1 i Nothing) <@> (bi bl))
              <@> (xBindedU0 <@> (bi bl))



            -- pline (y:I) defines a path from (<x>u0 biε) to gelSide (which is mhocom ... (<x>u0 biε))
            -- hence pline is a mhocom filler.
            pline (bl :: Bool) y =
              mhocom <#> l <#> (bA bl) <#> (mor <@> (xBindedZeta <@> (bi bl)) <@> (embd <@> (ineg <@> y)))
              <@> (lam "z" $ \z -> mpor <#> l <@> (xBindedZeta <@> (bi bl)) <@> (embd <@> (ineg <@> y))
                                     <#> (ilam "o" $ \ _ -> bA bl)
                                     <@> ( (captureU 2 (iand <@> y <@> z) Nothing) <@> (bi bl) )
                                     <@> (ilam "o" $ \ _ -> xBindedU0 <@> (bi bl)) )
              <@> ( xBindedU0 <@> (bi bl) )

            gelPrf = mhecom
              (lam "il" $ \ _ -> l)
              (lam "y" $ \ y -> bR <@> (pline False y) <@> (pline True y))
              (allMCstr <@> xBindedZeta)
              (lam "i" $ \ i -> ilam "oall" $ \ oall -> ungel <#> l <#> bA0 <#> bA1 <#> bR
                    <@> (captureU 2 i (Just $ epsi <#> xBindedZeta <..> oall <@> x))  ) -- i, oall ⊢ <x>  u i ε(oall)
              (ungel <#> l <#> bA0 <#> bA1 <#> bR <@> xBindedU0)

        -- mzer <- gelSide False
        -- mone <- gelSide True
        -- plineZer <- lam "y" $ \y -> pline False <@> y
        -- plineOne <- lam "y" $ \y -> pline True <@> y
        -- u0P <- (ungel <#> l <#> bA0 <#> bA1 <#> bR <@> xBindedU0) -- modify this if you modify gelPrf
        -- uP <- (lam "i" $ \ i -> ilam "oall" $ \ oall -> ungel <#> l <#> bA0 <#> bA1 <#> bR
        --             <@> (captureUat' i (epsi <#> xBindedZeta <..> oall <@> x) 2) )
        -- gp <- gelPrf
        -- reportSDocDocs "tc.prim.mhcomp.gel" 30 (text "gelSide's ...")
        --   [ "ctx = " <+> {- TCM Telescope -> TCM Doc -} ((getContextTelescope) >>= prettyTCM)
        --   , "mzer = " <+> (prettyTCM $ toExplicitArgs mzer)
        --   , "mone = " <+> (prettyTCM $ toExplicitArgs mone)
        --   , "pline0 = " <+> (prettyTCM $ toExplicitArgs plineZer)
        --   , "pline1 = " <+> (prettyTCM $ toExplicitArgs plineOne)
        --   , "u0P = " <+> (prettyTCM $ toExplicitArgs u0P)
        --   , "uP = " <+> (prettyTCM $ toExplicitArgs uP)
        --   , "gelPrf " <+> (prettyTCM $ toExplicitArgs gp) ]

        gel <#> l <#> bA0 <#> bA1 <#> bR <@> (gelSide False) <@> (gelSide True) <@> gelPrf <@> x

      reportSDocDocs "tc.prim.mhcomp.gel" 30 (text "mhocom at Gel, results...") [ prettyTCM $ toExplicitArgs res ]

      return $ Just res
  
mhcompGel _ _ _ _ = do
  return Nothing


-- | Explains how to reduce
--   @transp {l:I→Level} (λ iLn . line iLn) (psi:I) (u0:line i0)@ where line is
--   @λ iLn . mhocom {l iLn} {Set (l iLn)} {φ iLn} (T iLn) (A iLn)@
transpMHComp :: PureTCM m =>
                (Arg Term) -- ^ l:I->Lvl,
                -> (Arg Term, Arg Term, Arg Term, Arg Term)
                -- ^ mhocom args:  iLn ⊢ s:sSet(li), phi:I, T:∀i→..., A:line(i0)
                --   iLn ⊢ mhocom {l iLn} {Set (l iLn)} {φ iLn} (T iLn) (A iLn)
                -> (Blocked (Arg Term), Arg Term)
                -- ^ transport path cofib psi, transport base u0                
                -> m (Maybe Term)
transpMHComp l (s, phi, bT, bA) (spsi, u0) = do
  cint0 <- getTerm "" builtinInterval
  i1    <- getTerm "" builtinIOne
  let cint :: Type
      cint = El IntervalUniv cint0
  ctx <- getContext
  reportSDocDocs "tc.prim.transp.mhcomp" 30 (text "transporting along mhocom line. args:")
    [ text "transp {l:I→Level} (λ iLn . line iLn) (psi:I) (u0:line i0)"
    , "psi  = " <+> (prettyTCM $ ignoreBlocking spsi)
    , "u0   = " <+> prettyTCM u0
    , "l   = " <+> (prettyTCM $ unArg l)
    , "_ctx_⊢transp = "  <+> (return $ P.pretty ctx)
    , text "line = λ iLn . mhocom {l iLn} {Set (l iLn)} {φ iLn} (T iLn) (A iLn)"
    , "iLn⊢s(l iLn) = " <+> (addContext ("iLn" :: String, defaultDom cint) $ prettyTCM $ unArg s)
    , "iLn⊢phi    = " <+> (addContext ("iLn" :: String, defaultDom cint) $ prettyTCM $ unArg phi)
    , "iLn⊢T      = " <+> (addContext ("iLn" :: String, defaultDom cint) $ prettyTCM $ unArg bT)
    , "iLn⊢A      = " <+> (addContext ("iLn" :: String, defaultDom cint) $ prettyTCM $ unArg bA) ]

    -- , "headStop Head (phi i1) = " <+> ((return . P.pretty) =<< (headStop Head $ pure (unArg phi) <@> pure i1)) ] /!\ headStop works for path cstr

  return Nothing

-- | phi m∨ bno ↦ Just phi
unEmbd :: PureTCM m => Term -> m (Maybe Term)
unEmbd zeta = do
  szeta <- reduce zeta
  i0 <- getTerm "" builtinIZero
  i1 <- getTerm "" builtinIOne      
  vzeta <- mcstrView zeta
  case vzeta of
    Mno ->  return $ Just i0
    Myes -> return $ Just i1
    Mkmc aphi apsi -> do
      vpsi <- bcstrView $ unArg apsi
      case vpsi of
        Bno -> return $ Just $ unArg aphi
        _ -> return Nothing
    _ -> return Nothing


-- | primRefoldMhocom : ∀ {ℓ} {T : Type ℓ} → T → T
--   helper primitive to refold pure path mhocom into hcomps.
--   Judgementally, its the identity. Syntactically it is not.
--   Typically, terms that have such a head should be simplified in order to
--   porentially obtain an hcomp, not mhocom again.
primRefoldMhocom' :: TCM PrimitiveImpl
primRefoldMhocom' = do
  requireBridges "in primRefoldMhocom'"  
  typ :: Type <- runNamesT [] $
         hPi' "l" (el $ cl primLevel) $ \ l ->
         hPi' "T" (sort . tmSort <$> l) $ \ bT ->
         (el' l bT) --> (el' l bT)
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 3 $ \args@[l, bT, x] -> do
    sx <- reduceB x
    mhocom <- getPrimitiveName' builtinMHComp
    reportSDocDocs "tc.prim.bridges.refold" 30 (text "Entering primRefoldMhocom'")
      [ "l  = " <+> (prettyTCM l)
      , "bT = " <+> (prettyTCM bT)
      , "sx = " <+> (prettyTCM $ unArg $ ignoreBlocking sx) ]
    case (unArg $ ignoreBlocking sx) of
      Def q [Apply l, Apply bA, Apply zeta, Apply u, Apply u0] | Just q == mhocom -> do
        i0 <- getTerm "" builtinIZero
        i1 <- getTerm "" builtinIOne
        prsv <- getTerm "" builtinPrsvMCstr
        hcomp <- getTerm "" builtinHComp
        mPhi <- unEmbd $ unArg zeta
        caseMaybe mPhi (fallback sx) $ \ phi -> runNamesT [] $ do --pure path cstr
          u <- open $ unArg u
          phi <- open phi
          prsv <- open prsv
          l <- open $ unArg l
          bA <- open $ unArg bA
          u0 <- open $ unArg u0
          hcomp <- open $ hcomp

          let refoldU =
                lam "i" $ \ i -> ilam "o" $ \ o -> u <@> i <..> (prsv <#> phi <..> o)

          res <- hcomp <#> l <#> bA <#> phi <@> refoldU <@> u0
          reportSDocDocs "tc.prim.bridges.refold" 30 (text "In refoldMhocom, hcomp res")
            [ "res       = " <+> (prettyTCM $ toExplicitArgs res) ]

          return $ YesReduction YesSimplification $ res   
        
      _ -> do
        reportSDoc "tc.prim.bridges.refold" 30 (text "In refoldMhocom, we did not return hcomp")
        fallback sx

  where

    fallback sx = redReturn $ unArg $ ignoreBlocking sx
