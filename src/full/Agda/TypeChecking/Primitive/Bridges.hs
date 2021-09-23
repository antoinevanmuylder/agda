{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Description : Auxiliary functions for internal syntax bridges. Inspired from `TypeChecking/Primitive/Cubical.hs`.

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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable hiding (null)

import Agda.Interaction.Options ( optCubical )

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


-- (|) Checks that the correct variant of Cubical Agda is activated.
-- Note that @--erased-cubical@ \"counts as\" @--cubical@ in erased
-- contexts.

-- requireCubical
--   :: Cubical -- ^ Which variant of Cubical Agda is required?
--   -> String -> TCM ()
-- requireCubical wanted s = do
--   cubical         <- optCubical <$> pragmaOptions
--   inErasedContext <- hasQuantity0 <$> getEnv
--   case cubical of
--     Just CFull -> return ()
--     Just CErased | wanted == CErased || inErasedContext -> return ()
--     _ -> typeError $ GenericError $ "Missing option " ++ opt ++ s
--   where
--   opt = case wanted of
--     CFull   -> "--cubical"
--     CErased -> "--cubical or --erased-cubical"

-- | Types are terms with a sort annotation.
-- Here we turn the bridge interval (informally: BI) into such a type by specifying a sort for it.
-- This sort is LockUniv. The intent is that bridge variables x : BI should be treated affinely,
-- as it is the case for tick variables.
primBridgeIntervalType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primBridgeIntervalType = El LockUniv <$> primBridgeInterval
