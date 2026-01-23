{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use guards" #-}

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
      p1 = the (fold1 (\point1@(T2 x1 _) point2@(T2 x2 _) -> if x1 < x2 then point1 else point2) points) --weird lambda function that compares two points and picks the one with the lowest x value. "the" is needed for type issues.
      p2 = the (fold1 (\point1@(T2 x1 _) point2@(T2 x2 _) -> if x1 > x2 then point1 else point2) points)

      isUpper :: Acc (Vector Bool)
      isUpper = map (pointIsLeftOfLine line) points
      --fold1 (\p acc -> pointIsLeftOfLine line p : acc) points --other try but not correct. Map is much easier xD
        where
          line = T2 p1 p2

      isLower :: Acc (Vector Bool) --first i tried map not isUpper, but i dont think this is right cuz points already on the convex hull shouldnt be placed in either partition and this way they do have that
      isLower = map (pointIsLeftOfLine line) points --using helper function
        where
          line = T2 p2 p1
      
      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = T2 offset count --we combine the offsets and total count as a tuple with T2
        where
          isUpper' = map boolToInt isUpper --need to convert all Trues and Falses to 1's and 0's

          array = scanl (+) 0 isUpper' --scan to build up an array
          offset = init array --delete the last element
          count = fold (+) 0 isUpper' --fold to count the total as one number

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = T2 offset count --pretty much the same as the function above, just for the lower points
        where
          isLower' = map boolToInt isLower

          array = scanl (+) 0 isLower'
          offset = init array
          count = fold (+) 0 isLower'

      destination :: Acc (Vector (Maybe DIM1))
      destination = zipWith4 calcIndex isUpper isLower offsetUpper offsetLower --because were using acc it knows the index. We zip the four arrays we need and we can calculate the new one using the index from Acc
        where
          totalUpperPoints = the countUpper --to prevent type issues. Countupper is technically an acc and we need the raw value

          calcIndex :: Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp (Maybe DIM1)
          calcIndex upperPoints lowerPoints upperOffset lowerOffset =
            if upperPoints
              then Just_ (I1 (upperOffset + 1)) -- +1 because we have to start (and end) the partition with p1 as the excercise says. Dont know why, but doing it anyway
              else if lowerPoints
                then Just_ (I1 (lowerOffset + totalUpperPoints + 2 )) --we have the loweroffset, plus the total amount of upperpoints, plus 2 for p1 and p2 on the line
                else Nothing_

      newPoints :: Acc (Vector Point)
      newPoints = permute const defaults (destination !) points --build a new array within defaults by taking all points and moving them to their destination index
        where
          totalUpper = the countUpper
          totalLower = the countLower

          arrayLength = totalUpper + totalLower + 3 --plus three because the assignment says to put p1 at the start and end and p2 in the middle

          defaults = generate (I1 arrayLength) check
            where
              check :: Exp DIM1 -> Exp Point
              check ix = result
                where
                  Z :. i = unlift ix

                  result = --just a small hardcoded check for placing p1 and p2 in the right places
                    if i == 0 || i == (totalUpper + totalLower + 2)
                      then p1
                      else if i == (totalUpper + 1)
                        then p2
                        else lift ((0,0) :: Point) --placeholder. Will get overwritten

      headFlags :: Acc (Vector Bool) --pretty much the same logic as for making the newpoints array. We just place a True at p1 and p2 and p1 again, and false everywhere else.
      headFlags = generate (I1 arrayLength) check
            where
              totalUpper = the countUpper
              totalLower = the countLower

              arrayLength = totalUpper + totalLower + 3

              check :: Exp DIM1 -> Exp Bool
              check ix = result
                where
                  Z :. i = unlift ix

                  result =
                    if i == 0 || i == (totalUpper + 1) || i == (totalUpper + totalLower + 2)
                      then lift (True :: Bool)
                      else lift (False :: Bool)
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
partition (T2 headFlags points) = T2 newFlags newPoints
  where    
    p1s = propagateL headFlags points
    p2s = propagateR headFlags points
    --now we have for every point the line to which they should calculate their distance
    
    distancesToLine :: Acc (Vector Int)
    distancesToLine = zipWith3 func p1s p2s points
      where
        func :: Exp Point -> Exp Point -> Exp Point -> Exp Int
        func p1 p2 = nonNormalizedDistance (T2 p1 p2)
    --distances is the non normalized distance to their respective line. Now we need to scan each segment with a function that looks for the max distance
    
    distancesToPoint :: Acc (Vector Int)
    distancesToPoint = zipWith func p1s points
      where
        func :: Exp Point -> Exp Point -> Exp Int
        func (T2 x1 y1) (T2 x y) = (x - x1) * (x - x1) + (y - y1) * (y - y1)

    tempMaximum = segmentedScanr1 func headFlags (zip3 distancesToLine points distancesToPoint)
      where
        func :: Exp (Int, Point, Int) -> Exp (Int, Point, Int) -> Exp (Int, Point, Int)
        func p1@(T3 d1 _ dp1) p2@(T3 d2 _ dp2) = if d1 > d2 || (d1 == d2 && dp1 < dp2) then p1 else p2 

    realMaximum = map (\(T3 _ p _) -> p) (propagateL headFlags tempMaximum) --now every point knows the furthest point in their segment
    maxDist = map (\(T3 d _ _) -> d) (propagateL headFlags tempMaximum)

    --we now have, for every point, the p1 and p2 in their segment (line) and the furthest away point in their segment.

    isUpper = zipWith3 func p1s realMaximum points
      where
        func :: Exp Point -> Exp Point -> Exp Point -> Exp Bool
        func p1 p3 = pointIsLeftOfLine (T2 p1 p3) 

    isLower = zipWith3 func p2s realMaximum points
      where
        func :: Exp Point -> Exp Point -> Exp Point -> Exp Bool
        func p2 p3 = pointIsLeftOfLine (T2 p3 p2) 

    isActive = map (>0) maxDist
    -- undecidedPoints = zipWith4 func p1s p2s realMaximum points 
    --   where
    --     func :: Exp Point -> Exp Point -> Exp Point -> Exp Point -> Exp Bool
    --     func p1 p2 p3 p = 
    --       if pointIsLeftOfLine (T2 p1 p3) p || pointIsLeftOfLine (T2 p3 p2) p
    --         then lift (True :: Bool)
    --         else lift (False :: Bool)

    --now all points with True still need to be handled.

    isFurthestPoint = zipWith4 func headFlags isActive points realMaximum --make an array that tells every point if they are the furthest point or not
      where
        func :: Exp Bool -> Exp Bool -> Exp Point -> Exp Point -> Exp Bool
        func hf isAct (T2 x1 y1) (T2 x2 y2) = not hf && isAct && x1 == x2 && y1 == y2

    upperKeep = zipWith4 func headFlags isActive isFurthestPoint isUpper --make an array that flags every point that is an upper point and that we need to keep. This means we exclude headflags and the furthest point 
      where
        func :: Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool
        func hf isAct furthest upper = not hf && isAct && not furthest && upper

    lowerKeep = zipWith4 func headFlags isActive isFurthestPoint isLower --same for lower
      where
        func :: Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool
        func hf isAct furthest lower = not hf && isAct && not furthest && lower

    upperLocalID = segmentedScanl1 (+) headFlags (map boolToInt upperKeep)
    lowerLocalID = segmentedScanl1 (+) headFlags (map boolToInt lowerKeep)

    upperCounts = propagateL headFlags (segmentedScanr1 (+) headFlags (map boolToInt upperKeep)) --for the offset
    lowerCounts = propagateL headFlags (segmentedScanr1 (+) headFlags (map boolToInt lowerKeep))

    newFlags = undefined
    newPoints = undefined


  --error "TODO: partition"
  --we have initial partition with p1 to p2 and p2 to p1. 
  --For both parts we calculate the point furthest from the line using nonNormalizedDistance
  --Then pretty much copy the logic of the initial partition



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
