{-# LANGUAGE GADTs, TypeFamilies #-}

module Trafo where

import Data.Array.Accelerate
import Data.Array.Accelerate.Tuple
import qualified Data.Array.Accelerate.AST as AST
import Data.Array.Accelerate.AST hiding (Acc, Exp)

import Lower


-- map f (map g arr) = map (f . g) arr [using substitution]
--
map_map1 :: OpenAcc aenv arrs -> OpenAcc aenv arrs
map_map1 = error "Not implemented yet"

-- map f (map g arr) = map (f . g) arr [using a let binding]
--
map_map2 :: OpenAcc aenv arrs -> OpenAcc aenv arrs
map_map2 = error "Not implemented yet"

-- Apply 'lower_map2' and 'map_map2' to remove all occurences of 'Map' in the argument, while
-- producing the minimal number of 'Generate' operations without duplicating computations.
--
-- Hint: There is no need to descent into scalar expressions as all nested array computations
--       are guaranteed to merely be variables.
--
optimise :: OpenAcc aenv arrs -> OpenAcc aenv arrs
optimise = error "Not implemented yet"
