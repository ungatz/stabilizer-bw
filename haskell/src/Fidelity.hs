-- | Closest-stabilizer-state fidelity via decoding.
--
-- Plain-language recap (narrative/04-prop-computes.md): scale the unit
-- state to the lattice's preferred length, snap to the grid over a small
-- range of global phases, keep snaps that land on the inner shell (minimal
-- vectors = stabilizer states), report the best overlap found.
--
--   * Always: a certified lower bound on @F_STAB@ and an explicit witness.
--   * Under the BDD promise @F_STAB >= 7/8 + eta@ (grid size
--     @O(eta^{-1/2})@): the exact maximum and the exact closest stabilizer
--     state.
module Fidelity
  ( fidelity
  , FidelityResult(..)
  ) where

import Data.Complex (magnitude, mkPolar)
import Data.List (maximumBy)
import Data.Ord (comparing)
import BW
import Decoder (decode)

data FidelityResult = FidelityResult
  { fidLowerBound :: Double        -- ^ certified: some stabilizer state has this overlap
  , fidWitness    :: Maybe CVec    -- ^ the (scaled) lattice witness, if any snap landed on the shell
  } deriving Show

-- | @fidelity gridSize psi@ for a unit-norm @psi@ of depth @n@.
fidelity :: Int -> CVec -> FidelityResult
fidelity grid psi =
  let n      = depth psi
      scale  = sqrt 2 ^ n                              -- 2^{n/2}
      minSq  = 2 ^ n :: Integer                        -- minimal-vector norm^2
      tol    = 1e-6
      tries  =
        [ (ov, z)
        | j <- [0 .. grid - 1]
        , let theta = (pi / 2) * fromIntegral j / fromIntegral grid
              -- units i^k cover quarter turns; the grid covers the rest
              t     = scaleT (mkPolar scale theta) psi
              z     = decode t
        , abs (normSqC z - fromInteger minSq) < tol    -- landed on the shell?
        , let ov = magnitude (dotC z psi) / scale      -- |<S|psi>|
        ]
  in case tries of
       [] -> FidelityResult 0 Nothing
       _  -> let (ov, z) = maximumBy (comparing fst) tries
             in FidelityResult ov (Just z)
