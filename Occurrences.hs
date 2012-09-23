{-# LANGUAGE GADTs, ScopedTypeVariables #-}

import Data.Array.Accelerate
import Data.Array.Accelerate.AST
data Counts env where
  NilCounts  :: Counts ()
  ConsCounts :: Counts env -> Int -> Counts (env, t)

instance Show (Counts env) where
  show NilCounts = "#"
  show (ConsCounts counts count) = show counts ++ " " ++ show count

class EmptyCounts env where
  emptyCounts :: env -> Counts env

instance EmptyCounts () where
  emptyCounts _ = NilCounts

instance EmptyCounts env => EmptyCounts (env, t) where
  emptyCounts = (flip $ ConsCounts . emptyCounts . (Prelude.fst)) 0 

-- HINT: In the definition of 'emptyCounts' don't change the left-hand sides of the definitions.
--       That is, leave the '_' in the pattern, effectively ignoring the argument value (we are
--       only interested in its type.

count :: Counts (env, t) -> Counts env 
count (ConsCounts c _ ) =  c

incCount :: Counts env -> Idx env t -> Counts env
incCount NilCounts _ = NilCounts
incCount (ConsCounts counts count) ZeroIdx = ConsCounts counts (count + 1)
incCount (ConsCounts counts count) (SuccIdx x) = (ConsCounts $ incCount counts x) count

fresh :: EmptyCounts env => Counts env
fresh = emptyCounts undefined 

extendCounts :: Counts env -> (Counts (env, t) -> Counts (env, t)) -> Counts env
extendCounts c f = count . f $ ConsCounts c 0

funOccurrences :: EmptyCounts aenv => OpenFun env aenv t -> Counts aenv -> Counts aenv
funOccurrences (Lam f)  c = funOccurrences f c
funOccurrences (Body b) c = expOccurences b c


expOccurences :: EmptyCounts aenv => OpenExp env aenv t -> Counts aenv ->  Counts aenv
expOccurences (Var x)   c = c
expOccurences (Let l x) c = expOccurences x c
expOccurences (Shape s) c = occurrences' s c

occurrences :: forall aenv arrs. EmptyCounts aenv => OpenAcc aenv arrs -> Counts aenv
occurrences ast = occurrences' ast fresh

occurrences' :: EmptyCounts aenv => OpenAcc aenv arrs -> Counts aenv -> Counts aenv
occurrences' (OpenAcc ast) counts = 
            case ast of 
                (Avar x) -> (incCount $ counts) x
                (Alet e x) -> extendCounts (occurrences' e counts) (occurrences' x)
                (Map f x) -> occurrences' x $ funOccurrences f counts
                (Acond cond athen aelse) -> occurrences' athen $ occurrences' aelse $ expOccurences cond counts 
                (Unit u) -> expOccurences u counts  
                (Reshape e x) -> occurrences' x $ expOccurences e counts
                (Generate e f) -> funOccurrences f $ expOccurences e counts
                (Use a) -> counts
                (ZipWith f x y) -> occurrences' x $ occurrences' y counts

      
             
-- HINT: You will need some local or global auxiliary functions in the definitions of 'occurrences'
--       to traverse the mutually recursive AST data types.

-- Some tests (invent more!)
--

var0 :: Arrays theArrs => OpenAcc (env, theArrs) theArrs
var0 = OpenAcc $ Avar ZeroIdx

var1 :: Arrays theArrs => OpenAcc ((env, theArrs), arrs) theArrs
var1 = OpenAcc $ Avar (SuccIdx ZeroIdx)

var2 :: Arrays theArrs => OpenAcc (((env, theArrs), arrs), brrs) theArrs
var2 = OpenAcc $ Avar (SuccIdx (SuccIdx ZeroIdx))

testVar :: OpenAcc ((), Vector Int) (Vector Int)
testVar = var0

testMap :: OpenAcc ((), Vector Int) (Vector Int)
testMap = OpenAcc $ Map (Lam (Body (Var ZeroIdx))) var0

testZipWith1 :: OpenAcc ((), Vector Int) (Vector Int)
testZipWith1 = OpenAcc $ ZipWith (Lam (Lam (Body (Var ZeroIdx)))) var0 var0

testZipWith2 :: (Elt a, Elt b) => OpenAcc ((env, Vector a), Vector b) (Vector b)
testZipWith2 = OpenAcc $ ZipWith (Lam (Lam (Body (Var ZeroIdx)))) var1 var0

testLet0 = OpenAcc $ Alet testVar var1

testLet1 :: OpenAcc ((((), Vector Int), Vector Float), Vector Float) (Vector Float)
testLet1 = OpenAcc $ Alet testZipWith2 testZipWith2

-- let z = zip (\x y -> y) x y
-- in zip (\x y -> y) y z 

testLet2 :: OpenAcc (((), Vector Int), Vector Float) (Vector DIM1)
testLet2 = OpenAcc $ Alet testZipWith2 $
             OpenAcc $ Map (Lam (Body (Shape var2))) var0

-- Let z = zip (\x y -> y) 1 2
-- in map (\x Shape y ) z
