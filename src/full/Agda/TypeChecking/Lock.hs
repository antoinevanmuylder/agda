{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Lock
  ( isTimeless
  , isTimeless'
  , timelessThings
  , checkLockedVars
  , checkEarlierThan
  )
where

import Control.Monad            ( filterM, forM, forM_ )

import qualified Data.IntMap as IMap
import qualified Data.IntSet as ISet
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Constraints () -- instance MonadConstraint TCM
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Free

import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.VarSet as VSet
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size

checkLockedVars
  :: Term
     -- ^ term to check
  -> Type
     -- ^ its type
  -> Arg Term
     -- ^ the lock
  -> Type
     -- ^ type of the lock
  -> TCM ()
checkLockedVars t ty lk lk_ty = catchConstraint (CheckLockedVars t ty lk lk_ty) $ do
  -- Have to instantiate the lock, otherwise we might block on it even
  -- after it's been solved (e.g.: it's an interaction point, see #6528)
  -- Update (Andreas, 2023-10-23, issue #6913): need even full instantiation.
  -- Since @lk@ is typically just a variable, 'instantiateFull' is not expensive here.
  -- In #6913 it was a postulate applied to a meta, thus, 'instantiate' was not enough.
  lk <- instantiateFull lk
  reportSDoc "tc.term.lock" 40 $ "Checking locked vars.." <+> "lk    = " <+> (pretty lk) <+> " : " <+> (pretty lk_ty)
  reportSDoc "tc.term.lock" 50 $ nest 2 $ vcat
     [ text "t     = " <+> pretty t
     , text "ty    = " <+> pretty ty
     , text "lk    = " <+> pretty lk
     , text "lk_ty = " <+> pretty lk_ty
     ]

  -- Strategy: compute allowed variables, check that @t@ doesn't use more.
  mi <- getLockVar (unArg lk)
  caseMaybe mi (typeError (DoesNotMentionTicks t ty lk)) $ \ i -> do

  cxt <- getContext
  let toCheck = zip [0..] $ zipWith raise [1..] (take i cxt)
  reportSDoc "tc.term.lock" 70 $ vcat
     [ text "toCheck list is: "
     , nest 2 $ pretty toCheck
     ]

  let fv = freeVarsIgnore IgnoreInAnnotations (t,ty)
  let
    rigid = rigidVars fv
    -- flexible = IMap.keysSet $ flexibleVars fv
    termVars = allVars fv -- ISet.union rigid flexible
    earlierVars = ISet.fromList [i+1 .. size cxt - 1]
  reportSDoc "tc.term.lock" 50 $ vcat
     [ text "Displaying first fv analysis... holds iff termVars in earlierVars"
     , nest 2 $ text "rigid = " <+> pretty rigid
     , nest 2 $ text "termVars = " <+> pretty termVars
     , nest 2 $ text "earlierVars = " <+> pretty earlierVars
     ]
  if termVars `ISet.isSubsetOf` earlierVars then do
    reportSDoc "tc.term.lock" 40 $ "Above lk is for sure fresh in term"
    return ()
  else do
  checked <- fmap catMaybes . forM toCheck $ \ (j,dom) -> do
    ifM (isTimeless (snd . unDom $ dom) i)
        (return $ Just j)
        (return $ Nothing)

  reportSLn "tc.term.lock" 60 $ "display checks"
  reportSLn "tc.term.lock" 60 $ (show checked)

  let allowedVars = ISet.union earlierVars (ISet.fromList checked)

  if termVars `ISet.isSubsetOf` allowedVars then return () else do
  let
    illegalVars = rigid ISet.\\ allowedVars
    -- flexVars = flexibleVars fv
    -- blockingMetas = map (`lookupVarMap` flexVars) (ISet.toList $ termVars ISet.\\ allowedVars)
  if ISet.null illegalVars then  -- only flexible vars are infringing
    -- TODO: be more precise about which metas
    -- flexVars = flexibleVars fv
    -- blockingMetas = map (`lookupVarMap` flexVars) (ISet.toList $ termVars ISet.\\ allowedVars)
    patternViolation alwaysUnblock
  else
    typeError $ ReferencesFutureVariables t (List1.fromList (ISet.toList illegalVars)) lk i
    -- List1.fromList is guarded by not (null illegalVars)


-- | Precondition: 'Term' is fully instantiated.
getLockVar :: Term -> TCMT IO (Maybe Int)
getLockVar lk = do
  let
    fv = freeVarsIgnore IgnoreInAnnotations lk
    flex = flexibleVars fv

    isLock i = fmap (getLock . domInfo) (lookupBV i) <&> \case
      IsLock{} -> True
      IsNotLock{} -> False

  unless (IMap.null flex) $ do
    let metas = Set.unions $ map (foldrMetaSet Set.insert Set.empty) $ IMap.elems flex
    patternViolation $ unblockOnAnyMeta metas
      -- Andreas, 2023-10-23, issue #6913:
      -- We should not block on solved metas, so we need @lk@ to be fully instantiated,
      -- otherwise it may mention solved metas which end up here.

  is <- filterM isLock $ ISet.toList $ rigidVars fv

  -- Out of the lock variables that appear in @lk@ the one in the
  -- left-most position in the context is what will determine the
  -- available context for the head.
  let mi | Prelude.null is   = Nothing
         | otherwise = Just $ maximum is

  pure mi

-- | Types of variables that are anyway timeless
--   The cubical interval, cubical constraints, the bridge interval.
timelessThings :: [String]
timelessThings = map getBuiltinId [builtinInterval, builtinIsOne, builtinBridgeInterval]


isTimeless :: Type -> Int ->  TCM Bool
isTimeless t lki = do
  t <- abortIfBlocked t
  isTimeless' t lki
  -- timeless <- mapM getName' timelessThings
  -- case unEl t of
  --   Def q _ | Just q `elem` timeless -> return True
  --   _                                -> return False

-- | isTimeless' typ lki is true if
--   (typ ∈ timelessThings)   OR   typ is a bcstr/mcstr not mentionning lki.
isTimeless' :: PureTCM m => Type -> Int -> m Bool
isTimeless' typ lki = do -- @(El stype ttyp)
  -- t <- abortIfBlocked typ
  timeless <- mapM getName' timelessThings
  bholds <- getName' builtinBHolds
  mholds <- getName' builtinMHolds
  mkmc <- getName' builtinMkmc
  case (unEl typ) of
    Def q _ | Just q `elem` timeless -> return True
    Def q [Apply (Arg _ psi)] | Just q == bholds -> do
      psi' <- reduce psi
      let fvPsi = allVars $ freeVarsIgnore IgnoreAll $ psi'
      return $ not $ ISet.member lki fvPsi
    Def q [Apply (Arg _ zeta)] | Just q == mholds -> do
      zeta' <- reduce zeta
      case zeta' of
        Def q [Apply (Arg _ phi), Apply (Arg _ psi)] | Just q == mkmc -> do
          psi' <- reduce psi
          let fvPsi = allVars $ freeVarsIgnore IgnoreAll $ psi'
          return $ not $ ISet.member lki fvPsi
        _ -> return True -- zeta reduces to bot or top mixed cstr.
    _                                -> return False

notAllowedVarsError :: Term -> [Int] -> TCM b
notAllowedVarsError lk is = do
        typeError . GenericDocError =<<
         ("The following vars are not allowed in a later value applied to"
          <+> prettyTCM lk <+> ":" <+> prettyTCM (map var $ is))

checkEarlierThan :: Term -> VSet.VarSet -> TCM ()
checkEarlierThan lk fvs = do
  mv <- getLockVar lk
  caseMaybe mv (return ()) $ \ i -> do
    let problems = filter (<= i) $ VSet.toList fvs
    forM_ problems $ \ j -> do
      ty <- typeOfBV j
      unlessM (isTimeless ty i) $
        notAllowedVarsError lk [j]
