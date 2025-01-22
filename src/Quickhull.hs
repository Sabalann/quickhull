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
      p1 = the $ fold1 (\a b -> fst a < fst b ? (a, b)) points
      p2 = the $ fold1 (\a b -> fst a > fst b ? (a, b)) points

      isUpper :: Acc (Vector Bool)
      isUpper = map (\p -> p /= p1 && p /= p2 && pointIsLeftOfLine (T2 p1 p2) p) points

      isLower :: Acc (Vector Bool)
      isLower = map (\p -> p /= p1 && p /= p2 && pointIsLeftOfLine (T2 p2 p1) p) points

      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = 
        let boolToInt = map (\b -> b ? (1, 0)) isUpper
            offsets = prescanl (+) 0 boolToInt
            count = fold (+) 0 boolToInt
        in T2 offsets count

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = 
        let boolToInt = map (\b -> b ? (1, 0)) isLower
            offsets = prescanl (+) 0 boolToInt
            count = fold (+) 0 boolToInt
        in T2 offsets count

      destination :: Acc (Vector (Maybe DIM1))
      destination = generate (shape points) $ \ix ->
        let i = unindex1 ix
        in isUpper ! ix ? (Just_ (index1 (1 + offsetUpper ! ix)),
          isLower ! ix ? (Just_ (index1 (2 + the countUpper + offsetLower ! ix)),
          Nothing_))

      newPoints :: Acc (Vector Point)
      newPoints = permute 
        const
        (fill (index1 (3 + the countUpper + the countLower)) p1) -- Initialize with p1
        (\ix -> let i = unindex1 ix
          in i == 1 + the countUpper  -- p2 position
             ? (Just_ (index1 1),      -- index of p2 in input
             destination ! ix))        -- other points
        points

      headFlags :: Acc (Vector Bool)
      headFlags = permute 
        (||)
        (fill (index1 (3 + the countUpper + the countLower)) (constant False))
        (\ix -> let i = unindex1 ix
          in (i == 0 ||                            -- Start (p1)
              i == (1 + the countUpper) ||         -- Middle (p2)
              i == (2 + the countUpper + the countLower)) -- End (p1)
             ? (Just_ ix, Nothing_))
        (fill (index1 1) (constant True))
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

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL flags values =
  let
    -- Combine flags and values for scanning
    combined = zip values flags
    
    -- Scan left keeping last True value
    scanned = scanl1 
      (\prev curr -> 
        let T2 prevVal _ = unlift prev
            T2 currVal currFlag = unlift curr
        in currFlag ? (curr, T2 prevVal currFlag))
      combined
      
    -- Extract final values
    result = map fst scanned
  in
  result

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR flags values =
  let
    -- Combine flags and values for scanning
    combined = zip values flags
    
    -- Scan right keeping last True value
    scanned = scanr1 
      (\curr prev -> 
        let T2 prevVal _ = unlift prev
            T2 currVal currFlag = unlift curr
        in currFlag ? (curr, T2 prevVal currFlag))
      combined
      
    -- Extract final values
    result = map fst scanned
  in
  result

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL flags = 
    generate (shape flags) (\ix -> 
        let i = unindex1 ix
        in i == (size flags - 1) ? 
           (constant True, 
            flags ! (index1 (i + 1))))

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags = 
    generate (shape flags) (\ix -> 
        let i = unindex1 ix
        in i == 0 ? 
           (constant True, 
            flags ! (index1 (i - 1))))

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 f flags arr = 
    -- Extract just the values from the scan result, using prescanl1 instead
    let pairs = zipWith (\flag val -> T2 flag val) flags arr
        -- Segment operation that applies f to values and respects segment boundaries
        segOp = \(T2 f1 v1) (T2 f2 v2) -> 
            T2 (f1 || f2) 
               (f2 ? (v2, f v1 v2))
    in
    -- Perform inclusive scan using segmented operator
    map (\(T2 _ v) -> v) (scanl1 segOp pairs)

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 f flags arr = 
    let pairs = zipWith (\flag val -> T2 flag val) flags arr
        -- Segment operation that applies f to values and respects segment boundaries
        segOp = \(T2 f1 v1) (T2 f2 v2) -> 
            T2 (f1 || f2) 
               (f1 ? (v1, f v1 v2))
    in
    -- Perform inclusive scan from right using segmented operator
    map (\(T2 _ v) -> v) (scanr1 segOp pairs)


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
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (bF ? (bV, f aV bV))

