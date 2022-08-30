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

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Monad

import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Lock
import Agda.TypeChecking.Primitive.Cubical -- ( primIntervalType , decomposeInterval', TranspOrHComp(..) , requireCubical, FamilyOrNot(..) , cmdToName )

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Maybe

import Agda.Utils.Function
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
    resj <- isTimeless' tyj lki
    return $ not resj
  reportSLn "tc.prim" 60 $ "semiFreshForFvars, timefullLkLaters: " ++ P.prettyShow timefullLkLaters
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
            sbMtm <- simplify' $ unArg bM 
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
    -- | captures r in M, ie returns λ r. M. This is sound thanks to the fv-analysis.
    --  Γ0 , r:BI , Γ1, r''   --σ-->   Γ0 , r:BI , Γ1 ⊢ M   where    r[σ] = r''
    -- idea: sigma is a stack of :# (see Substitution'). leaves of sigma:
    -- Γ0, r:BI , Γ1, r'' ⊢ r''        Γ0, r:BI , Γ1, r'' ⊢ Γ0
    -- --------------------------------------------------------
    -- Γ0, r:BI , Γ1, r'' ⊢ Γ0, r    where r mapsto r''
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
        reportSLn "tc.prim.ungel" 30 $ "in prim_ungel'. lam case. here is absQ :" ++ psh absQtm'
        underAbstractionAbs (defaultNamedArgDom qinfo (absName qbody) bintervalTyp) qbody $ \body -> do
          --body already comes wkn
          body' <- reduceB' body --should care for metas as usual
          case ignoreBlocking body' of
            Def qnm [Apply _, Apply _, Apply _, Apply _,Apply _, Apply _, Apply bP, Apply _]
             | Just qnm == mgel -> do
              reportSLn "tc.prim.ungel" 30 $ "in prim_ungel': lam mgel case."
              reportSLn "tc.prim.ungel" 30 $ "in prim_ungel': here is absQ local body: " ++ psh (ignoreBlocking body')
              reportSLn "tc.prim.ungel" 30 $ "in prim_ungel'. absQ is x.gel, here is P before str: " ++ psh bP
              let strP = applySubst (strengthenS impossible 1) $ unArg bP
              reportSLn "tc.prim.ungel" 30 $ "in prim_ungel'. absQ is x.gel, here is P after str: " ++ psh strP
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


-- in unglue:
-- begin by reduceB' the variable phi. we don't have such a variable anyway
-- then they reduceB' the principal argument b

-- * BCstr primitives

-- next the 'constructors' of BCstr. Typically ψ:BCstr is x1=ε1 ∨ ... ∨ xn=εn
-- There are also bottom and top constructors in BCstr.

-- | bottom element in BCstr
primBno' :: TCM PrimitiveImpl
primBno' = do
  requireCubical CErased "" --flag downgrade.
  bcstr <- primBCstr
  return $ PrimImpl (El CstrUniv bcstr) $ primFun __IMPOSSIBLE__ 0 $ \ _ ->
    return $ NoReduction []

-- | top element in BCstr
primByes' :: TCM PrimitiveImpl
primByes' = do
  requireCubical CErased "" -- flag downgrade.
  bcstr <- primBCstr
  return $ PrimImpl (El CstrUniv bcstr) $ primFun __IMPOSSIBLE__ 0 $ \ _ ->
    return $ NoReduction []

-- | primBisone : BI -> BCstr       constraint "r=1" for some bvar r.
primBisone' :: TCM PrimitiveImpl
primBisone' = do
  requireCubical CErased "" --flag downgrade
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
  requireCubical CErased "" --flag downgrade.
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
  requireCubical CErased "" --flag downgrade.
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
  requireCubical CErased "" --flag downgrade
  mcstr <- primMCstr
  return $ PrimImpl (El CstrUniv mcstr) $ primFun __IMPOSSIBLE__ 0 $ \ _ ->
    return $ NoReduction []

-- | top element in MCstr
primMyes' :: TCM PrimitiveImpl
primMyes' = do
  requireCubical CErased "" --flag downgrade.
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
  requireCubical CErased "" -- flag downgrade
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
  requireCubical CErased "" --flag downgrade
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
  requireCubical CErased ""
  -- reflectMCstr is used to define std Kan op in terms of mixed ones
  -- hence using them in --cubical only environment is reasonnable.
  typ <- runNamesT [] $
    hPi' "φ" primIntervalType $ \ phi ->
    mpPi' "o" (iota phi) $ \ _ -> --todo: replace phi by phi embedded in MCstr. phi :: NamesT m Term
    elSSet $ cl isOne <@> phi
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 2 $ \ args -> do
    return $ NoReduction $ map notReduced args
  where
    isOne = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOne
    iota phi = cl primMkmc <@> phi <@> cl primBno
    
-- (elSSet $ cl isOne <@> phi)
-- isOne = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOne

-- a primitive with the same type than primHComp
-- by def, it reduces to something using primMHComp via primReflectMCstr.
primTestPrim' :: TCM PrimitiveImpl
primTestPrim' = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel) $ \ a ->
          hPi' "A" (sort . tmSort <$> a) $ \ bA ->
          hPi' "φ" primIntervalType $ \ phi ->
          nPi' "i" primIntervalType (\ i -> pPi' "o" phi $ \ _ -> el' a bA) -->
          (el' a bA --> el' a bA)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ [l, bA, phi@(Arg infPhi phitm), u@(Arg infU utm), u0] nelims -> do
    mixhcomp <- getTerm "" builtinMHComp
    mkmc <- getTerm "" builtinMkmc
    bno <- getTerm "" builtinBno
    reflct <- getTerm "" builtinReflectMCstr
    let iotaPhi :: Term
        iotaPhi = mkmc `apply` [ argN phitm, argN bno ]
    liftReflectU <- runNamesT [] $ -- :: Term
                    lam "i" $ \ i ->
                    lam "mprf" $ \ mprf -> --write reflectMCstr mprf
                    -- i:I, mprf:MHolds (i m∨ bno) ⊢ u i (reflect {phi} mprf)
                    (pure $ raise 2 utm) <@> i <@> ( (pure reflct) <#> (pure $ raise 2 phitm) <@> mprf )
    redReturn $ mixhcomp `apply` [l, bA, Arg infPhi iotaPhi, Arg infU liftReflectU, u0] -- defaultArgInfo


-- \extentArgs@[lA, lB, bA, bB,
--    n0@(Arg n0info n0tm), n1@(Arg n1info n1tm),
--    nn@(Arg nninfo nntm),
--    r@(Arg rinfo rtm0), bM] -> do



-- * Kan operations with mixed constraints.

-- such mixed operations requireCubical (instead of requireBridges)
-- But they check that if --bridges is disabled then the input mixed constraint is pure-path.

-- | primMHComp : ∀ {ℓ} {A : Set ℓ} {ζ : MCstr} (u : ∀ i → MPartial ζ A) (a0 : A) → A
--   This primitive only @requireCubical@ as std cubical Kan ops should ultimatetly
--   be defined in terms of
--   the mixed versions implemented here (such as the current function).
--   In order to preserve --cubical logical expressiveness,
--   this primitive has to check that, if --bridges is disabled, then its zeta argument is
--   a pure-path constraint (ie zeta = phi m∨ psi, and psi = bno).
primMHComp' :: TCM PrimitiveImpl
primMHComp' = do
  requireCubical CErased "" -- flag downgrade.
  bridgesEnabled <- optBridges <$> pragmaOptions  
  t    <- runNamesT [] $
          hPi' "l" (el $ cl primLevel) $ \ l ->
          hPi' "A" (sort . tmSort <$> l) $ \ bA ->
          hPi' "ζ" primMCstrType $ \ zeta ->
          nPi' "i" primIntervalType (\ i -> mpPi' "o" zeta $ \ _ -> el' l bA) -->
          (el' l bA --> el' l bA)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts@[l, bA, zeta, u, a0] nelims -> do
    -- we have to check that (no --bridges) -> zeta is path pure.
    -- then we reduce iff the above implication is true.
    -- TODO-antva: it would be cleaner (and sound-er?) to raise
    -- an error if zeta is not pure but --bridges is disabled.
    -- Unfortunately, ReduceM can not raise tc errors.
    -- solution: replace the above primMCstrType type with something
    -- dynamic wrt --bridges? {zeta:MCstr s.t. zeta path pure}
    bridges <- optBridges <$> pragmaOptions
    mbno <- getPrimitiveName' builtinBno
    pathPure <- do
      viewZeta <- mcstrView (unArg zeta)
      case viewZeta of
        Mno -> return True
        Myes -> return True
        OtherMCstr _ -> return True --TODO-antva metas ..
        Mkmc (Arg _ phi) (Arg _ psi@(Def q []))
          | Just q == mbno  -> return True
        _ -> return False
    case (bridges) || pathPure of
      False -> return $ NoReduction $ map notReduced ts
      True -> primMTransMHComp DoHComp ts nelims

cmdToMixName :: TranspOrHComp -> String
cmdToMixName DoTransp = builtinMTrans
cmdToMixName DoHComp  = builtinMHComp

primMTransMHComp :: TranspOrHComp -> [Arg Term] -> Int -> ReduceM (Reduced MaybeReducedArgs Term)
primMTransMHComp cmd ts nelims = dummyRedTerm0
-- primMTransMHComp :: TranspOrHComp -> [Arg Term] -> Int -> ReduceM (Reduced MaybeReducedArgs Term)
-- primMTransMHComp cmd ts nelims = do
--   (l,bA,zeta,u,u0) <- case (cmd,ts) of
--         (DoTransp, [l,bA,zeta,  u0]) -> do
--           --TODO-antva: not sure wheter primMTransp takes a path or mixed cstr.
--           -- here we assume it takes mixed cstr zeta.
          
--           -- u <- runNamesT [] $ do
--           --       u0 <- open $ unArg u0
--           --       defaultArg <$> (ilam "o" $ \ _ -> u0)
--           return $ (IsFam l,IsFam bA,phi,Nothing,u0) -- no adjustement @u@, and a line of types (family) bA
--         (DoHComp, [l,bA,phi,u,u0]) -> do
--           -- [l,bA] <- runNamesT [] $ do
--           --   forM [l,bA] $ \ a -> do
--           --     let info = argInfo a
--           --     a <- open $ unArg a
--           --     Arg info <$> (lam "i" $ \ _ -> a)
--           return $ (IsNot l,IsNot bA,zeta,Just u,u0) -- a single type bA, adjustement given by u.
--         _                          -> __IMPOSSIBLE__
--   sZeta <- reduceB' zeta
--   vZeta <- mcstrView $ unArg $ ignoreBlocking sZeta
--   let clP s = getTerm (cmdToMixName cmd) s -- 1st argument only for errors.

--   -- WORK
--   case vZeta of
--      Myes -> redReturn =<< case u of
--                             -- cmd == DoComp
--                             --adjusting u0 everywhere with u.                             
--                             Just u -> runNamesT [] $ do
--                                        u <- open (unArg u)
                                       
--                                        u <@> clP builtinIOne <..> clP builtinMitHolds
--                             -- cmd == DoTransp
--                             Nothing -> return $ unArg u0
--      _    -> do
--        let fallback' sc = do
--              u' <- case u of
--                             -- cmd == DoComp
--                      Just u ->
--                               (:[]) <$> case vZeta of
--                                           Mno -> return (notReduced u)
--                                             -- TODO-antva: in cubical they replace the u adjustement
--                                             -- for a "nowhere" (phi = IZero) constraint
--                                             -- by a canonical one: an adjustment built by eliminating
--                                             -- the inconsistent constraint IsOne i0
                                          
--                                             --      fmap (reduced . notBlocked . argN) . runNamesT [] $ do
--                                             -- [l,c] <- mapM (open . unArg) [famThing l, ignoreBlocking sc]
--                                             -- lam "i" $ \ i -> clP builtinIsOneEmpty <#> l
--                                             --                        <#> ilam "o" (\ _ -> c)
--                                           _     -> return (notReduced u)
--                             -- cmd == DoTransp
--                      Nothing -> return []
--              return $ NoReduction $ [notReduced (famThing l), reduced sc, reduced sphi] ++ u' ++ [notReduced u0]
--        sbA <- reduceB' bA
--        t <- case unArg <$> ignoreBlocking sbA of -- return type is (Maybe $ Blocked $ FamilyOrNot Term)
--               IsFam (Lam _info t) -> Just . fmap IsFam <$> reduceB' (absBody t)
--               IsFam _             -> return Nothing
--               IsNot t             -> return . Just . fmap IsNot $ (t <$ sbA)
--        case t of -- primMTransp, primMHComp reduce by casing on their type (line) argument.
--          Nothing -> fallback' (famThing <$> sbA)
--          Just st  -> do --st :: Blocked $ FamilyOrNot Term
--                let
--                    fallback = fallback' (fmap famThing $ st *> sbA)
--                    t = ignoreBlocking st -- t :: FamilyOrNot Term.
--                mMHComp <- getPrimitiveName' builtinMHComp --not Nothing in --cubical.
--                mGlue <- getPrimitiveName' builtinGlue
--                mGel <- getPrimitiveName' builtinGel  --Nothing in --cubical.
--                mId   <- getBuiltinName' builtinId
--                pathV <- pathView' --TODO-antva. why do we need this, do we need more (wrt bridges)
               
--                case famThing t of
--                  MetaV m _ -> fallback' (fmap famThing $ blocked_ m *> sbA)
--                  -- absName t instead of "i"
--                  Pi a b | nelims > 0  -> maybe fallback redReturn =<< compPi cmd "i" ((a,b) <$ t) (ignoreBlocking sZeta) u u0
--                           -- (a,b) <$ t :: FamOrNot (Dom Ty, Abs Ty). basically (a,b) with the family label of t.
--                           -- ignoreBlocking sZeta  :: Arg Tm, u : Maybe (Arg Term), u0 :: Arg Term.
--                         | otherwise -> fallback

--                  Sort (Type l) | DoTransp <- cmd -> compSort cmd fallback phi u u0 (l <$ t)

--                  Def q [Apply la, Apply lb, Apply bA, Apply phi', Apply bT, Apply e] | Just q == mGlue -> do
--                    maybe fallback redReturn =<< compGlue cmd phi u u0 ((la, lb, bA, phi', bT, e) <$ t) Head

--                  Def q [Apply _, Apply s, Apply phi', Apply bT, Apply bA]
--                    | Just q == mHComp, Sort (Type la) <- unArg s  -> do
--                    maybe fallback redReturn =<< compHCompU cmd phi u u0 ((Level la <$ s, phi', bT, bA) <$ t) Head

--                  -- Path/PathP
--                  d | PathType _ _ _ bA x y <- pathV (El __DUMMY_SORT__ d) -> do
--                    if nelims > 0 then compPathP cmd sphi u u0 l ((bA, x, y) <$ t) else fallback

--                  Def q [Apply _ , Apply bA , Apply x , Apply y] | Just q == mId -> do
--                    maybe fallback return =<< compId cmd sphi u u0 l ((bA, x, y) <$ t)

--                  Def q es -> do
--                    info <- getConstInfo q
--                    let   lam_i = Lam defaultArgInfo . Abs "i"

--                    case theDef info of
--                      r@Record{recComp = kit} | nelims > 0, Just as <- allApplyElims es, DoTransp <- cmd, Just transpR <- nameOfTransp kit
--                                 -> if recPars r == 0
--                                    then redReturn $ unArg u0
--                                    else redReturn $ (Def transpR []) `apply`
--                                                (map (fmap lam_i) as ++ [ignoreBlocking sphi,u0])
--                          | nelims > 0, Just as <- allApplyElims es, DoHComp <- cmd, Just hCompR <- nameOfHComp kit
--                                 -> redReturn $ (Def hCompR []) `apply`
--                                                (as ++ [ignoreBlocking sphi,fromMaybe __IMPOSSIBLE__ u,u0])

--                          | Just as <- allApplyElims es, [] <- recFields r -> compData Nothing False (recPars r) cmd l (as <$ t) sbA sphi u u0
--                      Datatype{dataPars = pars, dataIxs = ixs, dataPathCons = pcons, dataTransp = mtrD}
--                        | and [null pcons && ixs == 0 | DoHComp  <- [cmd]], Just as <- allApplyElims es ->
--                          compData mtrD ((not $ null $ pcons) || ixs > 0) (pars+ixs) cmd l (as <$ t) sbA sphi u u0
--                      Axiom constTransp | constTransp, [] <- es, DoTransp <- cmd -> redReturn $ unArg u0
--                      _          -> fallback

--                  _ -> fallback
--   where
--     compSort DoTransp fallback phi Nothing u0 (IsFam l) = do
--       -- TODO should check l is constant
--       redReturn $ unArg u0
--     -- compSort DoHComp fallback phi (Just u) u0 (IsNot l) = -- hcomp for Set is a whnf, handled above.
--     compSort _ fallback phi u u0 _ = __IMPOSSIBLE__
--     compPi :: TranspOrHComp -> ArgName
--             -> FamilyOrNot (Dom Type, Abs Type)
--             -- ^ were reducing mixed transp or mixed hcomp on a Pi with those args.
--             --   cmd = DoTransp, then domain and cod of Pi depend on a path var
--             -> Arg Term -- ^ zeta:MCstr argument of mix transp/hocom
--             -> Maybe (Arg Term) -- ^ if cmd = DoHComp, an adjustement u
--             -> Arg Term -- ^ pcpl argument u0
--             -> ReduceM (Maybe Term)
--     compPi cmd nam ab zeta u u0 = do
--      let getTermLocal = getTerm $ cmdToName cmd ++ " for function types"

--      tMTrans <- getTermLocal builtinMTrans
--      tMHComp <- getTermLocal builtinMHComp
--      tINeg <- getTermLocal builtinINeg
--      tIMax <- getTermLocal builtinIMax
--      iz    <- getTermLocal builtinIZero
--      let
--       toLevel' t = do
--         s <- reduce $ getSort t
--         case s of
--           (Type l) -> return (Just l)
--           _        -> return Nothing
--       toLevel t = fromMaybe __IMPOSSIBLE__ <$> toLevel' t
--      -- make sure the codomain has a level.
--      caseMaybeM (toLevel' . absBody . snd . famThing $ ab) (return Nothing) $ \ _ -> do
--      runNamesT [] $ do       
--       labA <- do -- :: (typeof iOrNot-cont) -> ?MCstr -> A((i0)) -> Term
--         let (x,f) = case ab of --f auxiliary func to treat hocom and transp together
--               IsFam (a,_) -> (a, \ a -> runNames [] $ lam "i" (const (pure a)))
--               IsNot (a,_) -> (a, id)
--         s <- reduce $ getSort x
--         case s of --dom:s
--           Type lx -> do
--             [la,bA] <- mapM (open . f) [Level lx, unEl . unDom $ x] -- ::[Term]
--             pure $ Just $ \ iOrNot zeta a0 -> pure tMTrans <#> lam "j" (\ j -> la <@> iOrNot j) 
--                                                          <@> lam "j" (\ j -> bA <@> iOrNot j) --type line, mb cst
--                                                          <@> zeta --TODO-antva: I or MCstr arg for mtransp?
--                                                          <@> a0
--           LockUniv -> return $ Just $ \ _ _ a0 -> a0
--           IntervalUniv -> do --dom = interval
--             x' <- reduceB $ unDom x
--             mInterval <- getBuiltinName' builtinInterval
--             case unEl $ ignoreBlocking x' of
--               Def q [] | Just q == mInterval -> return $ Just $ \ _ _ a0 -> a0
--               _ -> return Nothing
--           -- TODO-antva: more cases to consider?
--           _ -> return Nothing

--       caseMaybe labA (return Nothing) $ \ trA -> Just <$> do
--       [zeta, u0] <- mapM (open . unArg) [zeta, u0]
--       u <- traverse open (unArg <$> u)
--       -- unsurprinsingly, mix hocom/transp on a Pi type reduces to a certain lambda
--       -- for transport, the argument u1 must be transported back first
--       glam (getArgInfo (fst $ famThing ab)) (absName $ snd $ famThing ab) $ \ u1 -> do -- λ (u1 : dom((i1))) → ...
--         case (cmd, ab, u) of
--           (DoHComp, IsNot (a , b), Just u) -> do
--             bT <- (raise 1 b `absApp`) <$> u1 -- "T = cod u1"
--             let v = u1
--             --mhocomp {} {T} {zeta} (λ i .o → u i o v) (u0 v)
--             pure tMHComp <#> (Level <$> toLevel bT)
--                         <#> pure (unEl                      $ bT)
--                         <#> zeta
--                         <@> lam "i" (\ i -> ilam "o" $ \ o -> gApply (getHiding a) (u <@> i <..> o) v)
--                         <@> (gApply (getHiding a) u0 v)
--           (DoTransp, IsFam (a , b), Nothing) -> do
--             let v i = do -- we have u1 : dom((i1)). so we have to transport it back to i0. v i : A i.
--                        let
--                          iOrNot j = pure tIMax <@> i <@> (pure tINeg <@> j)
--                        trA iOrNot (pure tIMax <@> zeta <@> i) -- TODO-antva: mtransp cstr type debate
--                                   u1
--                 -- Γ , u1 : A[i1] , i : I
--                 bB v = consS v (liftS 1 $ raiseS 1) `applySubst` (absBody b {- Γ , i : I , x : A[i] -})
--                 tLam = Lam defaultArgInfo
--             bT <- bind "i" $ \ x -> fmap bB . v $ x
--             -- Γ , u1 : A[i1]
--             (pure tMTrans <#> (tLam <$> traverse (fmap Level . toLevel) bT)
--                          <@> (pure . tLam $ unEl                      <$> bT)
--                          <@> zeta -- TODO-antva: mtransp cstr arg debate
--                          <@> gApply (getHiding a) u0 (v (pure iz)))
--           (_,_,_) -> __IMPOSSIBLE__
--     compPathP cmd@DoHComp sphi (Just u) u0 (IsNot l) (IsNot (bA,x,y)) = do
--       let getTermLocal = getTerm $ cmdToName cmd ++ " for path types"
--       tHComp <- getTermLocal builtinHComp
--       tINeg <- getTermLocal builtinINeg
--       tIMax <- getTermLocal builtinIMax
--       tOr   <- getTermLocal "primPOr"
--       let
--         ineg j = pure tINeg <@> j
--         imax i j = pure tIMax <@> i <@> j

--       redReturn . runNames [] $ do
--          [l,u,u0] <- mapM (open . unArg) [l,u,u0]
--          phi      <- open . unArg . ignoreBlocking $ sphi
--          [bA, x, y] <- mapM (open . unArg) [bA, x, y]
--          lam "j" $ \ j ->
--            pure tHComp <#> l
--                        <#> (bA <@> j)
--                        <#> (phi `imax` (ineg j `imax` j))
--                        <@> lam "i'" (\ i ->
--                             let or f1 f2 = pure tOr <#> l <@> f1 <@> f2 <#> lam "_" (\ _ -> bA <@> i)
--                             in or phi (ineg j `imax` j)
--                                           <@> ilam "o" (\ o -> u <@> i <..> o <@@> (x, y, j)) -- a0 <@@> (x <@> i, y <@> i, j)
--                                           <@> (or (ineg j) j <@> ilam "_" (const x)
--                                                                   <@> ilam "_" (const y)))
--                        <@> (u0 <@@> (x, y, j))
--     compPathP cmd@DoTransp sphi Nothing u0 (IsFam l) (IsFam (bA,x,y)) = do
--       -- Γ    ⊢ l
--       -- Γ, i ⊢ bA, x, y
--       let getTermLocal = getTerm $ cmdToName cmd ++ " for path types"
--       tINeg <- getTermLocal builtinINeg
--       tIMax <- getTermLocal builtinIMax
--       tOr   <- getTermLocal "primPOr"
--       iz <- getTermLocal builtinIZero
--       io <- getTermLocal builtinIOne
--       let
--         ineg j = pure tINeg <@> j
--         imax i j = pure tIMax <@> i <@> j
--       comp <- do
--         tHComp <- getTermLocal builtinHComp
--         tTrans <- getTermLocal builtinTrans
--         let forward la bA r u = pure tTrans <#> lam "i" (\ i -> la <@> (i `imax` r))
--                                             <@> lam "i" (\ i -> bA <@> (i `imax` r))
--                                             <@> r
--                                             <@> u
--         return $ \ la bA phi u u0 ->
--           pure tHComp <#> (la <@> pure io)
--                       <#> (bA <@> pure io)
--                       <#> phi
--                       <@> lam "i" (\ i -> ilam "o" $ \ o ->
--                               forward la bA i (u <@> i <..> o))
--                       <@> forward la bA (pure iz) u0
--       redReturn . runNames [] $ do
--         [l,u0] <- mapM (open . unArg) [l,u0]
--         phi      <- open . unArg . ignoreBlocking $ sphi
--         [bA, x, y] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [bA, x, y]
--         lam "j" $ \ j ->
--           comp l (lam "i" $ \ i -> bA <@> i <@> j) (phi `imax` (ineg j `imax` j))
--                       (lam "i'" $ \ i ->
--                             let or f1 f2 = pure tOr <#> l <@> f1 <@> f2 <#> lam "_" (\ _ -> bA <@> i <@> j) in
--                                        or phi (ineg j `imax` j)
--                                           <@> ilam "o" (\ o -> u0 <@@> (x <@> pure iz, y <@> pure iz, j))
--                                           <@> (or (ineg j) j <@> ilam "_" (const (x <@> i))
--                                                                   <@> ilam "_" (const (y <@> i))))
--                       (u0 <@@> (x <@> pure iz, y <@> pure iz, j))
--     compPathP _ sphi u a0 _ _ = __IMPOSSIBLE__
--     compId cmd sphi u a0 l bA_x_y = do
--       let getTermLocal = getTerm $ cmdToName cmd ++ " for " ++ builtinId
--       unview <- intervalUnview'
--       mConId <- getName' builtinConId
--       cview <- conidView'
--       let isConId t = isJust $ cview __DUMMY_TERM__ t
--       sa0 <- reduceB' a0
--       -- wasteful to compute b even when cheaper checks might fail
--       b <- case u of
--              Nothing -> return True
--              Just u  -> allComponents unview (unArg . ignoreBlocking $ sphi) (unArg u) isConId
--       case mConId of
--         Just conid | isConId (unArg . ignoreBlocking $ sa0) , b -> (Just <$>) . (redReturn =<<) $ do
--           tHComp <- getTermLocal builtinHComp
--           tTrans <- getTermLocal builtinTrans
--           tIMin <- getTermLocal "primDepIMin"
--           tFace <- getTermLocal "primIdFace"
--           tPath <- getTermLocal "primIdPath"
--           tPathType <- getTermLocal builtinPath
--           tConId <- getTermLocal builtinConId
--           runNamesT [] $ do
--             let io = pure $ unview IOne
--                 iz = pure $ unview IZero
--                 conId = pure $ tConId
--             l <- case l of
--                    IsFam l -> open . unArg $ l
--                    IsNot l -> do
--                      open (Lam defaultArgInfo $ NoAbs "_" $ unArg l)
--             [p0] <- mapM (open . unArg) [a0]
--             p <- case u of
--                    Just u -> do
--                      u <- open . unArg $ u
--                      return $ \ i o -> u <@> i <..> o
--                    Nothing -> do
--                      return $ \ i o -> p0
--             phi      <- open . unArg . ignoreBlocking $ sphi
--             [bA, x, y] <-
--               case bA_x_y of
--                 IsFam (bA,x,y) -> mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [bA, x, y]
--                 IsNot (bA,x,y) -> forM [bA,x,y] $ \ a -> open (Lam defaultArgInfo $ NoAbs "_" $ unArg a)
--             let
--               eval DoTransp l bA phi _ u0 = pure tTrans <#> l <@> bA <@> phi <@> u0
--               eval DoHComp l bA phi u u0 = pure tHComp <#> (l <@> io) <#> (bA <@> io) <#> phi
--                                                        <@> u <@> u0
--             conId <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
--                   <@> (pure tIMin <@> phi
--                                   <@> ilam "o" (\ o -> pure tFace <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
--                                                                    <@> (p io o)))
--                   <@> (eval cmd l
--                                 (lam "i" $ \ i -> pure tPathType <#> (l <@> i) <#> (bA <@> i) <@> (x <@> i) <@> (y <@> i))
--                                 phi
--                                 (lam "i" $ \ i -> ilam "o" $ \ o -> pure tPath <#> (l <@> i) <#> (bA <@> i)
--                                                                                     <#> (x <@> i) <#> (y <@> i)
--                                                                                     <@> (p i o)
--                                       )
--                                 (pure tPath <#> (l <@> iz) <#> (bA <@> iz) <#> (x <@> iz) <#> (y <@> iz)
--                                                   <@> p0)
--                       )
--         _ -> return $ Nothing
--     allComponents unview phi u p = do
--             let
--               boolToI b = if b then unview IOne else unview IZero
--             as <- decomposeInterval phi
--             andM . for as $ \ (bs,ts) -> do
--                  let u' = listS (IntMap.toAscList $ IntMap.map boolToI bs) `applySubst` u
--                  t <- reduce2Lam u'
--                  return $! p $ ignoreBlocking t
--     reduce2Lam t = do
--           t <- reduce' t
--           case lam2Abs Relevant t of
--             t -> underAbstraction_ t $ \ t -> do
--                t <- reduce' t
--                case lam2Abs Irrelevant t of
--                  t -> underAbstraction_ t reduceB'
--          where
--            lam2Abs rel (Lam _ t) = absBody t <$ t
--            lam2Abs rel t         = Abs "y" (raise 1 t `apply` [setRelevance rel $ argN $ var 0])
--     allComponentsBack unview phi u p = do
--             let
--               boolToI b = if b then unview IOne else unview IZero
--               lamlam t = Lam defaultArgInfo (Abs "i" (Lam (setRelevance Irrelevant defaultArgInfo) (Abs "o" t)))
--             as <- decomposeInterval phi
--             (flags,t_alphas) <- fmap unzip . forM as $ \ (bs,ts) -> do
--                  let u' = listS bs' `applySubst` u
--                      bs' = IntMap.toAscList $ IntMap.map boolToI bs
--                      -- Γ₁, i : I, Γ₂, j : I, Γ₃  ⊢ weaken : Γ₁, Γ₂, Γ₃   for bs' = [(j,_),(i,_)]
--                      -- ordering of "j,i,.." matters.
--                  let weaken = foldr (\ j s -> s `composeS` raiseFromS j 1) idS (map fst bs')
--                  t <- reduce2Lam u'
--                  return $ (p $ ignoreBlocking t, listToMaybe [ (weaken `applySubst` (lamlam <$> t),bs) | null ts ])
--             return $ (flags,t_alphas)
--     compData mtrD False _ cmd@DoHComp (IsNot l) (IsNot ps) fsc sphi (Just u) a0 = do
--       let getTermLocal = getTerm $ cmdToName cmd ++ " for data types"

--       let sc = famThing <$> fsc
--       tEmpty <- getTermLocal builtinIsOneEmpty
--       tPOr   <- getTermLocal builtinPOr
--       iO   <- getTermLocal builtinIOne
--       iZ   <- getTermLocal builtinIZero
--       tMin <- getTermLocal builtinIMin
--       tNeg <- getTermLocal builtinINeg
--       let iNeg t = tNeg `apply` [argN t]
--           iMin t u = tMin `apply` [argN t, argN u]
--           iz = pure iZ
--       constrForm <- do
--         mz <- getTerm' builtinZero
--         ms <- getTerm' builtinSuc
--         return $ \ t -> fromMaybe t (constructorForm' mz ms t)
--       su  <- reduceB' u
--       sa0 <- reduceB' a0
--       view   <- intervalView'
--       unview <- intervalUnview'
--       let f = unArg . ignoreBlocking
--           phi = f sphi
--           a0 = f sa0
--           isLit t@(Lit lt) = Just t
--           isLit _ = Nothing
--           isCon (Con h _ _) = Just h
--           isCon _           = Nothing
--           combine l ty d [] = d
--           combine l ty d [(psi,u)] = u
--           combine l ty d ((psi,u):xs)
--             = pure tPOr <#> l <@> psi <@> foldr (imax . fst) iz xs
--                         <#> ilam "o" (\ _ -> ty) -- the type
--                         <@> u <@> (combine l ty d xs)
--           noRed' su = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced su', reduced sa0]
--             where
--               su' = case view phi of
--                      IZero -> notBlocked $ argN $ runNames [] $ do
--                                  [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
--                                  lam "i" $ \ i -> pure tEmpty <#> l
--                                                               <#> ilam "o" (\ _ -> c)
--                      _     -> su
--           sameConHeadBack Nothing Nothing su k = noRed' su
--           sameConHeadBack lt h su k = do
--             let u = unArg . ignoreBlocking $ su
--             (b, ts) <- allComponentsBack unview phi u $ \ t ->
--                         (isLit t == lt, isCon (constrForm t) == h)
--             let
--               (lit,hd) = unzip b

--             if isJust lt && and lit then redReturn a0 else do
--             su <- caseMaybe (sequence ts) (return su) $ \ ts -> do
--               let (us,bools) = unzip ts
--               fmap ((sequenceA_ us $>) . argN) $ do
--               let
--                 phis :: [Term]
--                 phis = for bools $ \ m ->
--                             foldr (iMin . (\(i,b) -> applyUnless b iNeg $ var i)) iO (IntMap.toList m)
--               runNamesT [] $ do
--                 u <- open u
--                 [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
--                 phis <- mapM open phis
--                 us   <- mapM (open . ignoreBlocking) us
--                 lam "i" $ \ i -> do
--                   combine l c (u <@> i) $ zip phis (map (\ t -> t <@> i) us)

--             if isJust h && and hd then k (fromMaybe __IMPOSSIBLE__ h) su
--                       else noRed' su

--       sameConHeadBack (isLit a0) (isCon a0) su $ \ h su -> do
--             let u = unArg . ignoreBlocking $ su
--             Constructor{ conComp = cm } <- theDef <$> getConstInfo (conName h)
--             case nameOfHComp cm of
--               Just hcompD -> redReturn $ Def hcompD [] `apply`
--                                           (ps ++ map argN [phi,u,a0])
--               Nothing        -> noRed' su

--     compData mtrD        _     0     DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = redReturn $ unArg a0
--     compData (Just trD) isHIT _ cmd@DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = do
--       let sc = famThing <$> fsc
--       let f = unArg . ignoreBlocking
--           phi :: Term
--           phi = f $ sphi
--       let lam_i = Lam defaultArgInfo . Abs "i"
--       redReturn $ Def trD [] `apply` (map (fmap lam_i) ps ++ map argN [phi,unArg a0])

--     compData mtrD isHIT _ cmd@DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = do
--       let getTermLocal = getTerm $ cmdToName cmd ++ " for data types"
--       let sc = famThing <$> fsc
--       mhcompName <- getName' builtinHComp
--       constrForm <- do
--         mz <- getTerm' builtinZero
--         ms <- getTerm' builtinSuc
--         return $ \ t -> fromMaybe t (constructorForm' mz ms t)
--       sa0 <- reduceB' a0
--       let f = unArg . ignoreBlocking
--           phi = f sphi
--           a0 = f sa0
--           noRed = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced sa0]
--       let lam_i = Lam defaultArgInfo . Abs "i"
--       case constrForm a0 of
--         Con h _ args -> do
--           Constructor{ conComp = cm } <- theDef <$> getConstInfo (conName h)
--           case nameOfTransp cm of
--               Just transpD -> redReturn $ Def transpD [] `apply`
--                                           (map (fmap lam_i) ps ++ map argN [phi,a0])
--               Nothing        -> noRed
--         Def q es | isHIT, Just q == mhcompName, Just [_l0,_c0,psi,u,u0] <- allApplyElims es -> do
--            let bC = ignoreBlocking sc
--            hcomp <- getTermLocal builtinHComp
--            transp <- getTermLocal builtinTrans
--            io <- getTermLocal builtinIOne
--            iz <- getTermLocal builtinIZero
--            redReturn <=< runNamesT [] $ do
--              [l,bC,phi,psi,u,u0] <- mapM (open . unArg) [l,bC,ignoreBlocking sphi,psi,u,u0]
--              -- hcomp (sc 1) [psi |-> transp sc phi u] (transp sc phi u0)
--              pure hcomp <#> (l <@> pure io) <#> (bC <@> pure io) <#> psi
--                    <@> lam "j" (\ j -> ilam "o" $ \ o ->
--                         pure transp <#> l <@> bC <@> phi <@> (u <@> j <..> o))
--                    <@> (pure transp <#> l <@> bC <@> phi <@> u0)
--         _ -> noRed
--     compData mtrX isHITorIx nargs cmd l t sbA sphi u u0 = do
--       () <- reportSDoc "impossible" 10 $ "compData" <+> (nest 2 . vcat)
--        [ "mtrX:       " <+> pretty mtrX
--        , "isHITorIx:  " <+> pretty isHITorIx
--        , "nargs:      " <+> pretty nargs
--        , "cmd:        " <+> text (show cmd)
--        , "l:          " <+> familyOrNot l
--        , "t:          " <+> familyOrNot t <+> pretty (famThing t)
--        , "sbA:          " <+> familyOrNot (ignoreBlocking $ sbA)
--        , "sphi:       " <+> pretty (ignoreBlocking sphi)
--        , "isJust u:   " <+> pretty (isJust u)
--        , "u0:         " <+> pretty u0
--        ]
--       __IMPOSSIBLE__

