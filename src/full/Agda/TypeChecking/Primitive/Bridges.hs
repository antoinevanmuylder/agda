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
import Agda.TypeChecking.Primitive.Cubical ( primIntervalType , decomposeInterval', TranspOrHComp(..) , requireCubical )

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Maybe

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
  requireCubical CErased ""
  -- reflectMCstr is used to define std Kan op in terms of mixed ones
  -- hence using them in --cubical only environment is reasonnable.
  typ <- runNamesT [] $
    hPi' "φ" primIntervalType $ \ phi ->
    mpPi' "o" (iota phi) $ \ _ -> --todo: replace phi by phi embedded in MCstr. phi :: NamesT m Term
    elSSet $ cl isOne <@> phi
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 1 $ \ [Arg _ phi , _] -> do
    yes <- getTerm "" builtinItIsOne --reflectMCstr is a constant function.
    redReturn yes
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
    let iotaPhi :: Term
        iotaPhi = mkmc `apply` [ phi, argN bno ]
    liftReflectU <- runNamesT [] $ -- :: Term
                    lam "i" $ \ i ->
                    lam "mprf" $ \ mprf -> --write reflectMCstr mprf
                    cl primReflectMCstr <#> (pure phitm) <@> mprf
    redReturn $ mixhcomp `apply` [l, bA, Arg infPhi iotaPhi, Arg infU liftReflectU, u0] -- defaultArgInfo


-- \extentArgs@[lA, lB, bA, bB,
--    n0@(Arg n0info n0tm), n1@(Arg n1info n1tm),
--    nn@(Arg nninfo nntm),
--    r@(Arg rinfo rtm0), bM] -> do



-- * Kan operations with mixed constraints.


primMHComp' :: TCM PrimitiveImpl
primMHComp' = do
  -- requireCubical CErased "" -- ??
  t    <- runNamesT [] $
          hPi' "l" (el $ cl primLevel) $ \ l ->
          hPi' "A" (sort . tmSort <$> l) $ \ bA ->
          hPi' "ζ" primMCstrType $ \ zeta ->
          nPi' "i" primIntervalType (\ i -> mpPi' "o" zeta $ \ _ -> el' l bA) -->
          (el' l bA --> el' l bA)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts nelims -> do
    primMTransMHComp DoHComp ts nelims
  where
    primMTransMHComp _ _ _ = dummyRedTerm0


