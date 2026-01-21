{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}

module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--
initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      p1, p2 :: Exp Point
      p1 = error "TODO: locate the left-most point"
      p2 = error "TODO: locate the right-most point"

      isUpper :: Acc (Vector Bool)
      isUpper = error "TODO: determine which points lie above the line (p₁, p₂)"

      isLower :: Acc (Vector Bool)
      isLower = error "TODO: determine which points lie below the line (p₁, p₂)"

      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = error "TODO: number of points above the line and their relative index"

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = error "TODO: number of points below the line and their relative index"

      destination :: Acc (Vector (Maybe DIM1))
      destination = error "TODO: compute the index in the result array for each point (if it is present)"

      newPoints :: Acc (Vector Point)
      newPoints = error "TODO: place each point into its corresponding segment of the result"

      headFlags :: Acc (Vector Bool)
      headFlags = error "TODO: create head flags array demarcating the initial segments"
  in
  T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
--
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  error "TODO: partition"


-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull =
  error "TODO: quickhull"


-- Helper functions
-- ----------------

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ propagateL (use flags) (use values)
--
-- should be:
-- Vector (Z :. 9) [1,1,1,4,5,5,5,5,9]
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a) --NOTE: i think (later realization) that i can use the segmentedscan to make this work better. Might try to implement later but for now this works
propagateL flagsMat valuesMat = map snd scannedElements --return all second elements of scannedElements. This ignores the flags and just returns the values.
  where
    combined = zip flagsMat valuesMat

    scannedElements = scanl1 pickElement combined --scnal1 gives two elements. The accumulator and the current value that is being evaluated

    pickElement :: Elt a => Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
    pickElement (T2 flagAcc valAcc) (T2 flagEval valEval) = if flagEval then (T2 flagEval valEval) else (T2 flagAcc valAcc) --if the flag of the tuple we are currently evaluating is true, we have found a new segment and return this new segment. Otherwise we return the accumulator (which copies the last known true flag)

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ propagateR (use flags) (use values)
--
-- should be:
-- Vector (Z :. 9) [1,4,4,4,5,9,9,9,9]
propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a) 
propagateR flagsMat valuesMat = map snd scannedElements --return all second elements of scannedElements. This ignores the flags and just returns the values.
  where
    combined = zip flagsMat valuesMat

    scannedElements = scanr1 pickElement combined --DIFFERENCE FROM SCANL1 is that the accumulator and evaluated tuple are switched

    pickElement :: Elt a => Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
    pickElement (T2 flagEval valEval) (T2 flagAcc valAcc) = if flagEval then (T2 flagEval valEval) else (T2 flagAcc valAcc) --if the flag of the tuple we are currently evaluating is true, we have found a new segment and return this new segment. Otherwise we return the accumulator (which copies the last known true flag)

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> run $ shiftHeadFlagsL (use (fromList (Z :. 6) [False,False,False,True,False,True]))
--
-- should be:
-- Vector (Z :. 6) [False,False,True,False,True,True]
shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL mat = backpermute (shape mat) getIndex mat --backpermute is like a shuffle for a matrix, so it just creates a new matrix using a function that says at what index of the matrix it should get its data from
  where
    getIndex :: Exp DIM1 -> Exp DIM1
    getIndex ix = lift (Z :. sourceIndex) --we return a new index; the index where the data should come from
      where
        Z :. i = unlift ix

        len = length mat

        sourceIndex = if i == (len - 1) then i else i + 1 --the index is pretty much the next index (because we're shifting left, we need to look at the +1 index from the original array). If the index gets out of bounds it just copies the last index

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> run $ shiftHeadFlagsR (use (fromList (Z :. 6) [True,False,False,True,False,False]))
--
-- should be:
-- Vector (Z :. 6) [True,True,False,False,True,False]
shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool) --see shiftL
shiftHeadFlagsR mat = backpermute (shape mat) getIndex mat
  where
    getIndex :: Exp DIM1 -> Exp DIM1
    getIndex ix = lift (Z :. sourceIndex)
      where
        Z :. i = unlift ix

        sourceIndex = if i == 0 then i else i - 1 --see shiftL, with the difference that we copy the first element instead of the last for shifting right

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ segmentedScanl1 (+) (use flags) (use values)
--
-- Expected answer:
-- >>> fromList (Z :. 9) [1, 1+2, 1+2+3, 4, 5, 5+6, 5+6+7, 5+6+7+8, 9] :: Vector Int
-- Vector (Z :. 9) [1,3,6,4,5,11,18,26,9]
--
-- Mind that the interpreter evaluates scans and folds sequentially, so
-- non-associative combination functions may seem to work fine here -- only to
-- fail spectacularly when testing with a parallel backend on larger inputs. ;)
segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 func flagsMat valuesMat = map snd scannedElements --return all second elements of scannedElements. This ignores the flags and just returns the values.
  where
    combined = zip flagsMat valuesMat

    scannedElements = scanl1 (segmented func) combined --we use helper function segmented which already has the logic for looking if the flag is true or not.

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ segmentedScanr1 (+) (use flags) (use values)
--
-- Expected answer:
-- >>> fromList (Z :. 9) [1, 2+3+4, 3+4, 4, 5, 6+7+8+9, 7+8+9, 8+9, 9] :: Vector Int
-- Vector (Z :. 9) [1,9,7,4,5,30,24,17,9]
segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 func flagsMat valuesMat = map snd scannedElements --return all second elements of scannedElements. This ignores the flags and just returns the values.
  where
    combined = zip flagsMat valuesMat

    scannedElements = scanr1 (segmented func) combined --we use helper function segmented which already has the logic for looking if the flag is true or not.

-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (if bF then bV else f aV bV)

-- | Read a file (such as "inputs/1.dat") and return a vector of points,
-- suitable as input to 'quickhull' or 'initialPartition'. Not to be used in
-- your quickhull algorithm, but can be used to test your functions in ghci.
readInputFile :: P.FilePath -> P.IO (Vector Point)
readInputFile filename =
  (\l -> fromList (Z :. P.length l) l)
  P.. P.map (\l -> let ws = P.words l in (P.read (ws P.!! 0), P.read (ws P.!! 1)))
  P.. P.lines
  P.<$> P.readFile filename
