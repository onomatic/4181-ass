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
map_map1 (OpenAcc (Map f (OpenAcc (Map g arr) ) ) ) = (OpenAcc (Map (Lam . Body . app_fun' f $ get_body g) arr))
map_map1 acc = acc


get_body :: PreFun OpenAcc aenv (a -> t) -> PreOpenExp OpenAcc ((),a) aenv t 
get_body (Lam (Body b))  = b


-- map f (map g arr) = map (f . g) arr [using a let binding]
--
map_map2 :: OpenAcc aenv arrs -> OpenAcc aenv arrs
map_map2 = error "Not implemented yet"

-- Apply 'lower_map2' and 'map_map2' to remove all occurences of 'Map' in the argument, while
-- producing the minimal number of 'Generate' operations without duplicating computations.
--
-- Hint: There is no need to descent into scalar expressions as all nested array computations
--       are guaranteed to merely be variables.
{-
optuple :: ATuple (PreOpenExp OpenAcc env aenv) t
        -> ATuple (PreOpenExp OpenAcc env aenv) t
optuple NilTup = NilTup
optuple (SnocTup tup e) = SnocTup $ (optuple tup) (optimise e)-}
--
optimise :: OpenAcc aenv arrs -> OpenAcc aenv arrs
optimise (OpenAcc acc)
  = case acc of
      Alet bndr body
        -> OpenAcc $ Alet (optimise bndr) (optimise body)
      Avar idx       -> OpenAcc $ Avar idx
     -- Atuple tup     -> Atuple . optuple $ tup
      Aprj i acc     -> OpenAcc $ Aprj i (optimise acc)
--      Apply f a      -> OpenAcc $ Apply f (optimise . OpenAcc $ acc)
      Acond c t e
        -> OpenAcc $ Acond  c (optimise t) (optimise e)
      Use c          -> OpenAcc $ Use c
      Unit e         -> OpenAcc $ Unit e
      Reshape sh acc -> OpenAcc $ Reshape sh (optimise acc)
      Generate e f   -> OpenAcc $ Generate e f
      Replicate sidx e acc
        -> OpenAcc $ Replicate sidx e acc
      Index sidx acc e
        -> OpenAcc $ Index sidx (optimise acc) e
      Map f acc      -> lower_map2 . map_map2 . OpenAcc . Map f $ optimise acc
      ZipWith f acc1 acc2
                     -> OpenAcc $ ZipWith f (optimise acc1)
                         (optimise acc2) 
      Fold f e acc   -> OpenAcc $ Fold f e
                          (optimise acc) 
      Fold1 f acc    -> OpenAcc $ Fold1 f (optimise acc)
      FoldSeg f e acc segd   
                     -> OpenAcc $ FoldSeg f e
                          (optimise acc) (optimise segd)
      Fold1Seg f acc segd   
                     -> OpenAcc $ Fold1Seg f
                          (optimise acc) (optimise segd)
      Scanl f e acc  -> OpenAcc $ Scanl f e
                          (optimise acc)
      Scanl' f e acc -> OpenAcc $ Scanl' f e
                          (optimise acc) 
      Scanl1 f acc   -> OpenAcc $ Scanl1 f (optimise acc)
      Scanr f e acc  -> OpenAcc $ Scanr f e
                          (optimise acc)
      Scanr' f e acc -> OpenAcc $ Scanr' f e 
                          (optimise acc)
      Scanr1 f acc   -> OpenAcc $ Scanr1 f (optimise acc)
      Permute c dft p acc  
                     -> OpenAcc $ Permute c (optimise dft)
                          p (optimise acc)
      Backpermute e p acc  
                     -> OpenAcc $ Backpermute e
                          p (optimise acc) 
      Stencil s bdry acc
                     -> OpenAcc $ Stencil s bdry (optimise acc)
      Stencil2 s bdry1 acc1 bdry2 acc2
                     -> OpenAcc $ Stencil2 s bdry1 (optimise acc1)
                          bdry2 (optimise acc2)
    where optimise' =  optimise . OpenAcc

