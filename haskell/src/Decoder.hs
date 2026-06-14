{-# LANGUAGE DeriveFunctor #-}
-- | The Micciancio-Nicolosi bounded-distance decoder, as a recursion scheme.
--
-- Contract (MN08, Theorem 1): if @dist^2(target, BW_n) < 2^n / 4@, the
-- decoder returns the unique closest lattice point.  Outside the promise it
-- still returns *a* lattice point (graceful degradation).
--
-- The categorical reading (narrative/04-prop-computes.md): the algorithm is
-- a hylomorphism.  The coalgebra splits a target into four half-size
-- subproblems
--
-- @
--      s  |-->  (s0, s1, (phi/2)(s0 - s1), (phi/2)(s0 + s1))
-- @
--
-- where the third and fourth components are the lattice automorphism @T@ of
-- Micciancio-Nicolosi, identified with the phased Clifford
-- @i * ((X * Ht) (x) I)@.  The unfold step is itself a prop morphism.  The
-- algebra reassembles four candidate lattice points and keeps the one
-- closest to the target; correctness of the reconciliation is the
-- free-module decomposition of "BW".
module Decoder
  ( decode
  , roundGauss
  , distSq
  , Fix(..), cata, ana, hylo, SplitF(..)   -- generic schemes
  ) where

import Data.Complex (Complex(..), realPart, imagPart)
import Data.List (minimumBy)
import Data.Ord (comparing)
import GaussianInt (phi, toComplex)
import BW

-- Generic recursion schemes (self-contained; no packages).

newtype Fix f = Fix (f (Fix f))

cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg (Fix f) = alg (fmap (cata alg) f)

ana :: Functor f => (a -> f a) -> a -> Fix f
ana coalg = Fix . fmap (ana coalg) . coalg

-- | @hylo = fold after unfold@, fused (no intermediate structure).
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo alg coalg = alg . fmap (hylo alg coalg) . coalg

-- | The decoder's base functor.  A problem either bottoms out at one
-- complex scalar, or splits into four half-size subproblems while
-- remembering the original target (needed by the algebra to choose among
-- candidates).
data SplitF r = Done (Complex Double)
              | Split CVec r r r r        -- target, s0, s1, s-, s+
  deriving Functor

-- The decoder.

-- | Round one complex number to the nearest Gaussian integer.  This is
-- @decode BW_0 = Z[i]@: the recursion's base case.
roundGauss :: Complex Double -> Complex Double
roundGauss z = fromIntegral (round (realPart z) :: Integer)
            :+ fromIntegral (round (imagPart z) :: Integer)

-- | Squared Euclidean distance between coordinate vectors.  This is the
-- decoder's distance: plain Euclidean on raw amplitudes.  The
-- fidelity-distance dictionary in "Fidelity" converts it to overlap.
distSq :: CVec -> CVec -> Double
distSq u v = normSqC (subT u v)

phiC, halfPhi, twoOverPhi :: Complex Double
phiC       = toComplex phi          -- 1 + i
halfPhi    = phiC / 2               -- phi/2
twoOverPhi = 1 :+ (-1)              -- 2/phi = 1 - i (a Gaussian integer!)

-- | The coalgebra: split a target into Micciancio-Nicolosi's four
-- subproblems.
splitStep :: CVec -> SplitF CVec
splitStep (Leaf z)        = Done z
splitStep s@(Node s0 s1)  =
  Split s s0 s1 (scaleT halfPhi (subT s0 s1))   -- s-  = (phi/2)(s0 - s1)
                (scaleT halfPhi (addT s0 s1))   -- s+  = (phi/2)(s0 + s1)

-- | The algebra: reconcile four decoded subproblems into four candidate
-- lattice points (inverting the linear maps that produced the subtargets),
-- then keep the candidate closest to the remembered target.
reconcile :: SplitF CVec -> CVec
reconcile (Done z)               = Leaf (roundGauss z)
reconcile (Split s z0 z1 zm zp)  =
  let w     = twoOverPhi
      cands = [ Node z0 (subT z0 (scaleT w zm))           -- [z0, z0 - (2/phi) z-]
              , Node z0 (subT (scaleT w zp) z0)           -- [z0, (2/phi) z+ - z0]
              , Node (addT (scaleT w zm) z1) z1           -- [(2/phi) z- + z1, z1]
              , Node (subT (scaleT w zp) z1) z1           -- [(2/phi) z+ - z1, z1]
              ]
  in snd (minimumBy (comparing fst) [ (distSq s c, c) | c <- cands ])

-- | The decoder is literally the hylomorphism of the two halves above.
decode :: CVec -> CVec
decode = hylo reconcile splitStep
