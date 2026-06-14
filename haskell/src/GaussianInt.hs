-- | Exact arithmetic in the Gaussian integers Z[i].
--
-- The ring of choice for the Barnes-Wall story: every Clifford gate in the
-- lattice-preserving normalization is a matrix over Z[i], and the only prime
-- that matters is phi = 1 + i, the ramified prime above 2.  All lattice
-- bookkeeping in this package is exact integer arithmetic in this ring;
-- floating point appears only at the boundary where the decoder reads a
-- noisy *target* (a complex vector to be snapped to the nearest lattice
-- point).  See narrative/01-bw-family.md for the geometric picture.
module GaussianInt
  ( GI(..)
  , phi
  , conjGI
  , normGI
  , divisibleByPhi
  , divPhi
  , toComplex
  ) where

import Data.Complex (Complex(..))

-- | A Gaussian integer @a + b*i@, exact.
data GI = GI !Integer !Integer
  deriving (Eq, Ord, Show)

instance Num GI where
  GI a b + GI c d = GI (a + c) (b + d)
  GI a b - GI c d = GI (a - c) (b - d)
  -- (a+bi)(c+di) = (ac - bd) + (ad + bc)i
  GI a b * GI c d = GI (a * c - b * d) (a * d + b * c)
  negate (GI a b) = GI (negate a) (negate b)
  abs    = error "GI: abs not used (no canonical absolute value in Z[i])"
  signum = error "GI: signum not used"
  fromInteger n   = GI n 0

-- | The dyadic prime @phi = 1 + i@.  @phi^2 = 2i@; the field norm is
-- @|phi|^2 = 2@, so phi is a prime above 2 in Z[i].
phi :: GI
phi = GI 1 1

-- | Complex conjugation, the nontrivial Galois symmetry of Q(i).
conjGI :: GI -> GI
conjGI (GI a b) = GI a (negate b)

-- | Field norm @N(a + bi) = a^2 + b^2 = (a+bi)(a-bi)@.  Multiplicative.
normGI :: GI -> Integer
normGI (GI a b) = a * a + b * b

-- | @z@ is divisible by @phi@ iff its real and imaginary parts have the
-- same parity (equivalently, @a + b@ is even).  This single predicate
-- powers the Barnes-Wall membership test in "BW".
divisibleByPhi :: GI -> Bool
divisibleByPhi (GI a b) = even (a + b)

-- | Exact division by @phi@ when possible.  Identity:
-- @(a + bi)/(1 + i) = ((a + b) + (b - a)i)/2@.
divPhi :: GI -> Maybe GI
divPhi z@(GI a b)
  | divisibleByPhi z = Just (GI ((a + b) `div` 2) ((b - a) `div` 2))
  | otherwise        = Nothing

-- | Forget exactness.  Used only at the boundary with the decoder's
-- floating-point targets.
toComplex :: GI -> Complex Double
toComplex (GI a b) = fromInteger a :+ fromInteger b
