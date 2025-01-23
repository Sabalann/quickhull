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
      -- determine letfmost and rightmost points
      p1, p2 :: Exp Point
      p1 = the $ fold1 (\a b -> 
          fst a < fst b ? (a, 
          fst a == fst b ? (snd a <= snd b ? (a, b), b)
          )) points
      p2 = the $ fold1 (\a b -> 
          fst a > fst b ? (a, 
          fst a == fst b ? (snd a >= snd b ? (a, b), b)
          )) points

      -- find points above line
      isUpper :: Acc (Vector Bool)
      isUpper = map (\p -> 
          p /= p1 && p /= p2 && 
          pointIsLeftOfLine (T2 p1 p2) p
        ) points

      -- find points below line
      isLower :: Acc (Vector Bool)
      isLower = map (\p -> 
          p /= p1 && p /= p2 && 
          pointIsLeftOfLine (T2 p2 p1) p
        ) points

      -- count points above and below line
      countUpper :: Acc (Scalar Int)
      countUpper = fold (+) 0 (map (\b -> b ? (1, 0)) isUpper)

      countLower :: Acc (Scalar Int)
      countLower = fold (+) 0 (map (\b -> b ? (1, 0)) isLower)

      -- p1 + upper points + p2 + lower points + p1
      totalSize = 3 + the countUpper + the countLower

      -- compute index in the result array
      destination :: Acc (Vector (Maybe DIM1))
      destination = generate (shape points) $ \ix ->
        let 
            point = points ! ix
            upperOffset = prescanl (+) 0 (map (\b -> b ? (1, 0)) isUpper)
            lowerOffset = prescanl (+) 0 (map (\b -> b ? (1, 0)) isLower)
        in
        point == p1 ? (Just_ (index1 0),                              -- p1 goes first
            point == p2 ? (Just_ (index1 (1 + the countUpper)),       -- p2 goes after upper points
            isUpper ! ix ? (Just_ (index1 (1 + upperOffset ! ix)),    -- upper points after p1
            isLower ! ix ? (Just_ (index1 (2 + the countUpper + lowerOffset ! ix)), 
            Nothing_)  -- invalid points
            )))

      -- new points array
      newPoints :: Acc (Vector Point)
      newPoints = permute 
        const
        (fill (index1 totalSize) p1) 
        (destination !)  -- use destination indices
        points

      -- head flags marking segment boundaries
      headFlags :: Acc (Vector Bool)
      headFlags = generate (index1 totalSize) $ \(I1 i) ->
        i == 0 ||                   -- first p1
        i == 1 + the countUpper ||  -- p2
        i == totalSize - 1          -- last p1
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
  let
      segStarts = propagateL headFlags points
      segEnds = rotate1 segStarts

      p3s = segmentedScanl1 
        (\a b -> 
          let p1 = head' segStarts
              p2 = last' segStarts
              d1 = nonNormalizedDistance (T2 p1 p2) a
              d2 = nonNormalizedDistance (T2 p1 p2) b
          in d1 > d2 ? (a, b)) 
        headFlags 
        points
      
      isLeft = zipWith3 
        (\p1 p3 p -> p /= p1 && p /= p3 && pointIsLeftOfLine (T2 p1 p3) p)
        segStarts p3s points
                
      isRight = zipWith3 
        (\p3 p2 p -> p /= p3 && p /= p2 && pointIsLeftOfLine (T2 p3 p2) p)
        p3s segEnds points

      T2 offsetLeft countLeft = 
        let boolToInt = map (\b -> b ? (1, 0)) isLeft
        in T2 (prescanl (+) 0 boolToInt) (fold (+) 0 boolToInt)

      T2 offsetRight countRight = 
        let boolToInt = map (\b -> b ? (1, 0)) isRight
        in T2 (prescanl (+) 0 boolToInt) (fold (+) 0 boolToInt)

      totalPoints = 3 + the countLeft + the countRight

      newPoints = permute const
        (fill (index1 totalPoints) (head' segStarts))
        (\ix -> let i = unindex1 ix
               in 
                  i == 0 ? (Just_ (index1 0),
                  i == 1 ? (Just_ (index1 1),
                  i == 2 + the countLeft ? (Just_ (index1 (2 + the countLeft)),
                  i == totalPoints - 1 ? (Just_ (index1 0),  -- Force last point to be first point
                  isLeft ! ix 
                  ? (Just_ (index1 (2 + offsetLeft ! ix)),
                  isRight ! ix 
                  ? (Just_ (index1 (3 + the countLeft + offsetRight ! ix)),
                  Nothing_)))))))
        points

      newHeadFlags = generate 
        (index1 totalPoints)
        (\ix -> let i = unindex1 ix
               in i == 0 || 
                  i == 1 || 
                  i == 2 + the countLeft ||
                  i == totalPoints - 1)
  in
  T2 newHeadFlags newPoints

  where 
    head' xs = the $ fold1 const xs
    last' xs = the $ fold1 (const P.id) xs


-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull =
  error "TODO: quickhull"


-- Helper functions
-- ----------------

rotate1 :: Elt a => Acc (Vector a) -> Acc (Vector a)
rotate1 arr = generate (shape arr) (\ix ->
    let i = unindex1 ix
    in i == 0 ? (arr ! index1 (size arr - 1), arr ! index1 (i - 1)))

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL flags values =
  let
    -- combine flags and values
    combined = zip values flags
    
    -- keep last true from the left
    scanned = scanl1 
      (\prev curr -> 
        let T2 prevVal _ = unlift prev
            T2 _ currFlag = unlift curr
        in currFlag ? (curr, T2 prevVal currFlag))
      combined
      
    result = map fst scanned
  in
  result

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR flags values =
  let
    -- combine flags and values
    combined = zip values flags
    
    -- keep last true from the right
    scanned = scanr1 
      (\curr prev -> 
        let T2 prevVal _ = unlift prev
            T2 _ currFlag = unlift curr
        in currFlag ? (curr, T2 prevVal currFlag))
      combined
      
    result = map fst scanned
  in
  result

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL flags = 
    generate (shape flags) (\ix -> 
        let i = unindex1 ix
        in i == (size flags - 1) ? 
           (constant True, 
            flags ! index1 (i + 1)))

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags = 
    generate (shape flags) (\ix -> 
        let i = unindex1 ix
        in i == 0 ? 
           (constant True, 
            flags ! index1 (i - 1)))

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 f flags arr = 
    let pairs = zipWith T2 flags arr
    in map (\(T2 _ v) -> v) (scanl1 (segmented f) pairs)

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 f flags arr =
    let 
        -- reverse flags and array
        revFlags = reverse flags
        revArr   = reverse arr

        pairs = zipWith T2 revFlags revArr
        scanned = scanl1 (segmented f) pairs
    in reverse $ map (\(T2 _ v) -> v) scanned -- reverse back to original


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

