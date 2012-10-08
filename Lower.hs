{-# LANGUAGE GADTs, TypeFamilies #-}

module Lower where

import Data.Array.Accelerate
import Data.Array.Accelerate.Tuple
import qualified Data.Array.Accelerate.AST as AST
import Data.Array.Accelerate.AST hiding (Acc, Exp)

-- map f arr = generate (shape arr) (\ix -> f (arr!ix))
--
map_lowered 
    :: (Shape ix, Elt a, Elt b)
    => (Exp a -> Exp b)
    -> Acc (Array ix a)
    -> Acc (Array ix b)
map_lowered f arr
  = generate (shape arr) (\ix -> f (arr!ix))

-- Lower 'map' into 'generate' as a AST rewrite. The array gets duplicated.
--
lower_map1 :: OpenAcc aenv arrs -> OpenAcc aenv arrs
lower_map1 (OpenAcc (Map f arr)) 
  = error "Implement this!"

-- Lower 'map' into 'generate' as a AST rewrite. The array is being shared.
--
lower_map2 :: OpenAcc aenv arrs -> OpenAcc aenv arrs
lower_map2 (OpenAcc (Map f arr)) 
  = error "Implement this!"


-- Utilities
-- ---------

-- Relation between the original environment, the environment of the substituted in term, and the
-- required environment of the result.
--
-- For example,
--
-- > Keep (Keep Subst) :: SubstEnv ((((), t2), t1), t) outer ((outer, t1), t)
--
-- Here the variable with index 2, which is of type 't2', is replaced by a term with the environment
-- 'outer', resulting in the final environment type '((outer, t1), t)'.
--
-- Note how it is always the leftmost type in the original environment that is replaced. This
-- implies that it is only the outermost binding of a term that can be substituted.
-- 
data SubstEnv inner outer final where
  Subst :: SubstEnv ((), t)    outer outer
  Keep  :: SubstEnv inner      outer final
        -> SubstEnv (inner, t) outer (final, t)

-- De Bruijn index substitution applied to a term.
--
-- The application
--
-- > subst idx e eT envRel
--
-- applies the substitution [idx |-> e] to the term 'eT'. All occurences of 'idx' in 'eT' are
-- replaced by 'e'.
--
-- Substitution is complicated by the environment of the result needing to be adjusted. The
-- environment relation 'envRel' relates the environments of 'idx' (same as that of 'eT') and 'e'
-- with the environment required for the result of the substitution.
--
-- Restriction: The substituted variable must be the leftmost in the environment (i.e., the one with
--              the largest index).
--
subst :: SubstEnv envInner envOuter envFinal
      -> Idx envInner t
      -> PreOpenExp OpenAcc envOuter aenv t
      -> PreOpenExp OpenAcc envInner aenv t'
      -> PreOpenExp OpenAcc envFinal aenv t'
subst envRel idx e (Var x) = case (substVar envRel idx e x) of 
                                    Left x' -> Var x'
                                    Right e' -> e'
subst envRel idx e (Let e' exp) =  Let (subst envRel idx e e') $ subst (Keep envRel) (shiftIdx Shift idx) e exp
subst envRel idx e (Const t) = (Const t)
subst envRel idx e (Tuple t') = Tuple $ substTuple envRel idx e t'
subst envRel idx e (Prj t e') = Prj t $ subst envRel idx e e'
subst envRel idx e IndexNil = IndexNil
subst envRel idx e (IndexCons e' sl) = IndexCons (subst envRel idx e e') (subst envRel idx e sl)      
subst envRel idx e (IndexHead e') = IndexHead $ subst envRel idx e e'
subst envRel idx e IndexAny = IndexAny
subst envRel idx e (Cond cnd thn els) = Cond (subst envRel idx e cnd) (subst envRel idx e thn) (subst envRel idx e els)
subst envRel idx e (PrimConst c) = PrimConst c
subst envRel idx e (PrimApp f x) = PrimApp f $ (subst envRel idx e x)
subst envRel idx e (ShapeSize s) = ShapeSize $ (subst envRel idx e s)   


-- HINT: To simplify matters, you do not need to implement this function for the
--       AST constructors 'IndexScalar' and 'Shape' (these are the only constructors
--       embedding arrays).

substTuple :: SubstEnv envInner envOuter envFinal
           -> Idx envInner t
           -> PreOpenExp OpenAcc envOuter aenv t
           -> Tuple (PreOpenExp OpenAcc envInner aenv) t'
           -> Tuple (PreOpenExp OpenAcc envFinal aenv) t'
substTuple envRel idx arg NilTup          = NilTup
substTuple envRel idx arg (SnocTup tup e) = SnocTup (substTuple envRel idx arg tup) (subst envRel idx arg e)

-- De Bruijn index substitution applied to one variable.
--
-- The application
--
-- > substVar idx e idxT envRel
--
-- applies the substitution [idx |-> e] to the variable represented by de Bruijn index 'idxT'. If
-- 'idx' and 'idxT' are the same, we return 'Right e'; otherwise 'Left idxT'.
--
-- Variable substitution is complicated by the environment of the result needing to be adjusted. In
-- particular, the environment must be the same, regardless of whether 'idx' and 'idxT' are the same
-- or not. The environment relation 'envRel' relates the environments of 'idx' and 'e' with the
-- environment required for the result of the substitution.
--
-- Restriction: The substituted variable must be the leftmost in the environment (i.e., the one with
--              the largest index).
--
substVar :: SubstEnv envInner envOuter envFinal
         -> Idx envInner t
         -> PreOpenExp OpenAcc envOuter aenv t
         -> Idx envInner t'
         -> Either (Idx envFinal t') (PreOpenExp OpenAcc envFinal aenv t')
--substVar = error "Implement this!"
substVar Subst ZeroIdx e ZeroIdx = Right e
substVar (Keep _) _ e ZeroIdx = Left ZeroIdx
--substVar (Keep _) idx e idxT = 
substVar (Keep envRel) idx e (SuccIdx idxT') = Left idxT'
substVar Subst idx e idxT = if (sameEnv idx idxT) 
    		then undefined --right
			else undefined --left


--this is for the environments
sameEnv :: Idx env t -> Idx env' t' -> Bool

sameEnv ZeroIdx ZeroIdx = True
sameEnv ZeroIdx _ = False
sameEnv _ ZeroIdx = False
sameEnv (SuccIdx idx) (SuccIdx idx') = sameEnv idx idx



-- Environment shifting
--

-- Shift the array environment one to the left, adding a new entry at index 0. Hence, the indicies
-- of all free variables need to be incremented by one (but bound variables, of course, stay the
-- same).
--
shiftAccAenv :: OpenAcc aenv          arrs 
             -> OpenAcc (aenv, arrs') arrs
shiftAccAenv = shiftAccAenv' Shift

shiftAccAenv' :: ShiftEnv aenv aenvShifted 
              -> OpenAcc aenv        arrs 
              -> OpenAcc aenvShifted arrs
shiftAccAenv' shiftRel (OpenAcc acc)
  = OpenAcc $ case acc of
      Alet bndr body
        -> Alet (shiftAccAenv' shiftRel bndr) (shiftAccAenv' (Bound shiftRel) body)
      Avar idx       -> Avar $ shiftIdx shiftRel idx
      Atuple tup     -> Atuple $ shiftTuple shiftRel tup
      Aprj i acc     -> Aprj i (shiftAccAenv' shiftRel acc)
      Apply f a      -> Apply f (shiftAccAenv' shiftRel a)
      Acond c t e
        -> Acond (shiftExpAenv' shiftRel c) (shiftAccAenv' shiftRel t) (shiftAccAenv' shiftRel e)
      Use c          -> Use c
      Unit e         -> Unit (shiftExpAenv' shiftRel e)
      Reshape sh acc -> Reshape (shiftExpAenv' shiftRel sh) (shiftAccAenv' shiftRel acc)
      Generate e f   -> Generate (shiftExpAenv' shiftRel e) (shiftFunAenv' shiftRel f)
      Replicate sidx e acc
        -> Replicate sidx (shiftExpAenv' shiftRel e) (shiftAccAenv' shiftRel acc)
      Index sidx acc e
        -> Index sidx (shiftAccAenv' shiftRel acc) (shiftExpAenv' shiftRel e)
      Map f acc      -> Map (shiftFunAenv' shiftRel f) (shiftAccAenv' shiftRel acc)
      ZipWith f acc1 acc2
                     -> ZipWith (shiftFunAenv' shiftRel f) (shiftAccAenv' shiftRel acc1)
                         (shiftAccAenv' shiftRel acc2)
      Fold f e acc   -> Fold (shiftFunAenv' shiftRel f) (shiftExpAenv' shiftRel e)
                          (shiftAccAenv' shiftRel acc)
      Fold1 f acc    -> Fold1 (shiftFunAenv' shiftRel f) (shiftAccAenv' shiftRel acc)
      FoldSeg f e acc segd   
                     -> FoldSeg (shiftFunAenv' shiftRel f) (shiftExpAenv' shiftRel e)
                          (shiftAccAenv' shiftRel acc) (shiftAccAenv' shiftRel segd)
      Fold1Seg f acc segd   
                     -> Fold1Seg (shiftFunAenv' shiftRel f)
                          (shiftAccAenv' shiftRel acc) (shiftAccAenv' shiftRel segd)
      Scanl f e acc  -> Scanl (shiftFunAenv' shiftRel f) (shiftExpAenv' shiftRel e)
                          (shiftAccAenv' shiftRel acc)
      Scanl' f e acc -> Scanl' (shiftFunAenv' shiftRel f) (shiftExpAenv' shiftRel e)
                          (shiftAccAenv' shiftRel acc)
      Scanl1 f acc   -> Scanl1 (shiftFunAenv' shiftRel f) (shiftAccAenv' shiftRel acc)
      Scanr f e acc  -> Scanr (shiftFunAenv' shiftRel f) (shiftExpAenv' shiftRel e)
                          (shiftAccAenv' shiftRel acc)
      Scanr' f e acc -> Scanr' (shiftFunAenv' shiftRel f) (shiftExpAenv' shiftRel e)
                          (shiftAccAenv' shiftRel acc)
      Scanr1 f acc   -> Scanr1 (shiftFunAenv' shiftRel f) (shiftAccAenv' shiftRel acc)
      Permute c dft p acc  
                     -> Permute (shiftFunAenv' shiftRel c) (shiftAccAenv' shiftRel dft)
                          (shiftFunAenv' shiftRel p) (shiftAccAenv' shiftRel acc)
      Backpermute e p acc  
                     -> Backpermute (shiftExpAenv' shiftRel e)
                          (shiftFunAenv' shiftRel p) (shiftAccAenv' shiftRel acc)
      Stencil s bdry acc
                     -> Stencil (shiftFunAenv' shiftRel s) bdry (shiftAccAenv' shiftRel acc)
      Stencil2 s bdry1 acc1 bdry2 acc2
                     -> Stencil2 (shiftFunAenv' shiftRel s) bdry1 (shiftAccAenv' shiftRel acc1)
                          bdry2 (shiftAccAenv' shiftRel acc2)
  where
    shiftTuple :: ShiftEnv aenv aenvShifted
               -> Atuple (OpenAcc aenv)        arrs
               -> Atuple (OpenAcc aenvShifted) arrs
    shiftTuple shiftRel NilAtup            = NilAtup
    shiftTuple shiftRel (SnocAtup tup arr) 
      = SnocAtup (shiftTuple shiftRel tup) (shiftAccAenv' shiftRel arr)

shiftFunAenv :: OpenFun env aenv         t 
             -> OpenFun env (aenv, arrs) t
shiftFunAenv = shiftFunAenv' Shift

shiftFunAenv' :: ShiftEnv aenv aenvShifted
              -> OpenFun env aenv        t 
              -> OpenFun env aenvShifted t
shiftFunAenv' shiftRel (Body e) = Body $ shiftExpAenv' shiftRel e
shiftFunAenv' shiftRel (Lam e)  = Lam  $ shiftFunAenv' shiftRel e

shiftExpAenv :: OpenExp env aenv         t
             -> OpenExp env (aenv, arrs) t
shiftExpAenv = shiftExpAenv' Shift

shiftExpAenv' :: ShiftEnv aenv aenvShifted
              -> OpenExp env aenv        t
              -> OpenExp env aenvShifted t
shiftExpAenv' shiftRel (Let bndr body)     
  = Let (shiftExpAenv' shiftRel bndr) (shiftExpAenv' shiftRel body)
shiftExpAenv' shiftRel (Var idx')          = Var idx'
shiftExpAenv' shiftRel (Const v)           = Const v
shiftExpAenv' shiftRel (Tuple tup)         = Tuple $ shiftTuple shiftRel tup
  where
    shiftTuple :: ShiftEnv aenv aenvShifted
               -> Tuple (OpenExp env aenv)        t
               -> Tuple (OpenExp env aenvShifted) t
    shiftTuple shiftRel NilTup          = NilTup
    shiftTuple shiftRel (SnocTup tup e) 
      = SnocTup (shiftTuple shiftRel tup) (shiftExpAenv' shiftRel e)
shiftExpAenv' shiftRel (Prj tidx e)        = Prj tidx (shiftExpAenv' shiftRel e)
shiftExpAenv' shiftRel IndexNil            = IndexNil
shiftExpAenv' shiftRel (IndexCons sl e)    
  = IndexCons (shiftExpAenv' shiftRel sl) (shiftExpAenv' shiftRel e)
shiftExpAenv' shiftRel (IndexHead e)       = IndexHead (shiftExpAenv' shiftRel e)
shiftExpAenv' shiftRel (IndexTail e)       = IndexTail (shiftExpAenv' shiftRel e)
shiftExpAenv' shiftRel IndexAny            = IndexAny
shiftExpAenv' shiftRel (Cond c t e)        
  = Cond (shiftExpAenv' shiftRel c) (shiftExpAenv' shiftRel t) (shiftExpAenv' shiftRel e)
shiftExpAenv' shiftRel (PrimConst c)       = PrimConst c
shiftExpAenv' shiftRel (PrimApp f a)       = PrimApp f (shiftExpAenv' shiftRel a)
shiftExpAenv' shiftRel (IndexScalar acc e) = IndexScalar (shiftAccAenv' shiftRel acc) (shiftExpAenv' shiftRel e)
shiftExpAenv' shiftRel (Shape acc)         = Shape (shiftAccAenv' shiftRel acc)
shiftExpAenv' shiftRel (ShapeSize e)       = ShapeSize (shiftExpAenv' shiftRel e)

-- Shift the scalar environment one to the left, adding a new entry at index 0. Hence, the indicies
-- of all free variables need to be incremented by one (but bound variables, of course, stay the
-- same).
--
shiftExpEnv :: OpenExp env       aenv t
            -> OpenExp (env, t') aenv t
shiftExpEnv = shift Shift
  where
    shift :: ShiftEnv env envShifted
          -> PreOpenExp OpenAcc env        aenv t
          -> PreOpenExp OpenAcc envShifted aenv t
    shift shiftRel (Let bndr body)     = Let (shift shiftRel bndr) (shift (Bound shiftRel) body)
    shift shiftRel (Var idx')          = Var $ shiftIdx shiftRel idx'
    shift shiftRel (Const v)           = Const v
    shift shiftRel (Tuple tup)         = Tuple $ shiftTuple shiftRel tup
    shift shiftRel (Prj tidx e)        = Prj tidx (shift shiftRel e)
    shift shiftRel IndexNil            = IndexNil
    shift shiftRel (IndexCons sl e)    = IndexCons (shift shiftRel sl) (shift shiftRel e)
    shift shiftRel (IndexHead e)       = IndexHead (shift shiftRel e)
    shift shiftRel (IndexTail e)       = IndexTail (shift shiftRel e)
    shift shiftRel IndexAny            = IndexAny
    shift shiftRel (Cond c t e)        = Cond (shift shiftRel c) (shift shiftRel t) (shift shiftRel e)
    shift shiftRel (PrimConst c)       = PrimConst c
    shift shiftRel (PrimApp f a)       = PrimApp f (shift shiftRel a)
    shift shiftRel (IndexScalar acc e) = IndexScalar acc (shift shiftRel e)
    shift shiftRel (Shape acc)         = Shape acc
    shift shiftRel (ShapeSize e)       = ShapeSize (shift shiftRel e)

    shiftTuple :: ShiftEnv env envShifted
               -> Tuple (PreOpenExp OpenAcc env        aenv) t
               -> Tuple (PreOpenExp OpenAcc envShifted aenv) t
    shiftTuple shiftRel NilTup          = NilTup
    shiftTuple shiftRel (SnocTup tup e) = SnocTup (shiftTuple shiftRel tup) (shift shiftRel e)

-- Relation between original and shifted environments.
--
-- Shifting below binders requires to keep track of the number of entries for bound variables that
-- appear above the insertion point of shifting. For example,
--
-- > Bound (Bound Shift) :: ShiftEnv ((env, t1), t) (((env, t2), t1), t)
--
-- indicates that 't' and 't1' are bound variables below which we introduce a new slot for 't2' by
-- shifting 'env'. We call 't2' the /insertion point/.
--
data ShiftEnv env envShifted where
  Shift :: ShiftEnv env      (env, t)
  Bound :: ShiftEnv env      envShifted 
        -> ShiftEnv (env, t) (envShifted, t)

-- Shift one de Bruijn index given an environment shifting relation.
--
-- If the de Bruijn index is above the insertion point (i.e., refers to a bound variable), it stays
-- the same. Otherwise, it gets incremented by one to make room for the new slot in the environment.
--
shiftIdx :: ShiftEnv env envShifted
         -> Idx env        t
         -> Idx envShifted t
shiftIdx Shift            idx           = SuccIdx idx
shiftIdx (Bound _)        ZeroIdx       = ZeroIdx
shiftIdx (Bound shiftRel) (SuccIdx idx) = SuccIdx $ shiftIdx shiftRel idx
