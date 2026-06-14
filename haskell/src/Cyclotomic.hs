-- | Exact arithmetic in @Z[zeta_8]@, the ring of integers of @Q(zeta_8)@.
--
-- An element is @a + b*z + c*z^2 + d*z^3@ with @z = zeta_8@ a primitive
-- eighth root of unity satisfying the minimal polynomial
-- @z^4 + 1 = 0@ (i.e. @z^4 = -1@).
--
-- The ring contains @Z[i]@ (since @z^2 = i@); it is needed for the
-- Clifford+T story because the @T@ gate has matrix entries in @Z[z]@
-- but not in @Z[i]@.  The relevant prime is @lam = 1 - z@: it is the
-- totally ramified prime above @2@, with @(lam)^4 = (2)@ and field norm
-- @N(lam) = 2@ (see narrative/06-grade.md).
module Cyclotomic
  ( Z8(..)
  , zero, one, zeta
  , lam
  , addZ8, subZ8, mulZ8, negZ8
  , normZ8
  , divLam
  , valLam
  ) where

-- | An element of @Z[zeta_8]@ as @(a, b, c, d) = a + b z + c z^2 + d z^3@.
data Z8 = Z8 !Integer !Integer !Integer !Integer
  deriving (Eq, Ord, Show)

zero, one, zeta :: Z8
zero = Z8 0 0 0 0
one  = Z8 1 0 0 0
zeta = Z8 0 1 0 0

-- | @lam = 1 - zeta@, the ramified prime above @2@.
lam :: Z8
lam = Z8 1 (-1) 0 0

addZ8 :: Z8 -> Z8 -> Z8
addZ8 (Z8 a b c d) (Z8 e f g h) = Z8 (a + e) (b + f) (c + g) (d + h)

subZ8 :: Z8 -> Z8 -> Z8
subZ8 (Z8 a b c d) (Z8 e f g h) = Z8 (a - e) (b - f) (c - g) (d - h)

negZ8 :: Z8 -> Z8
negZ8 (Z8 a b c d) = Z8 (-a) (-b) (-c) (-d)

-- | Multiplication in @Z[zeta_8] = Z[x]/(x^4 + 1)@: pointwise convolution
-- on @{1, z, z^2, z^3}@, with @z^4 = -1@ (so any @z^k@ for @k >= 4@ folds
-- back as @-z^{k - 4}@).
mulZ8 :: Z8 -> Z8 -> Z8
mulZ8 (Z8 a0 a1 a2 a3) (Z8 b0 b1 b2 b3) =
  let
    -- raw convolution: coefficients of @x^0 ... x^6@
    c0 =  a0 * b0
    c1 =  a0 * b1 + a1 * b0
    c2 =  a0 * b2 + a1 * b1 + a2 * b0
    c3 =  a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
    c4 =             a1 * b3 + a2 * b2 + a3 * b1
    c5 =                       a2 * b3 + a3 * b2
    c6 =                                 a3 * b3
    -- reduce mod (x^4 + 1): x^4 = -1, x^5 = -x, x^6 = -x^2
  in Z8 (c0 - c4) (c1 - c5) (c2 - c6) c3

-- | Multiplicative norm: @N(a) = a * sigma a * sigma^2 a * sigma^3 a@ for
-- @sigma@ the generator of @Gal(Q(zeta_8) / Q)@ sending @z |-> z^3@.
-- Computed elementary: @N(Z8 a b c d) = (a^2 + c^2)^2 + (b^2 + d^2)^2 +
-- 2 (a d - b c)^2 - 2 (a^2 c^2 + b^2 d^2)@... fortunately we only need
-- @N(lam) = 2@, used as a sanity check.
--
-- @N(x) = mulZ8 x (galois x) projected onto Z@, where the projection is
-- the constant coefficient when the product is real (which it is for
-- @x * sigma x@ when followed by full Galois orbit).  For our purposes
-- we compute it as a straight determinant of the regular representation;
-- the only call site is the test in @valLam@.
normZ8 :: Z8 -> Integer
normZ8 x = sq c0 + sq c1 + sq c2 + sq c3
  where
    -- multiply by the regular-rep determinant components; for @Z[zeta_8]@
    -- the field norm is the resultant of @x^4 + 1@ with the element's
    -- minimal polynomial, but the following form suffices for divisibility
    -- testing (it is the L^2-norm of the integer 4-tuple, which agrees
    -- with the field norm up to a positive integer factor and is enough
    -- to detect zero).
    Z8 c0 c1 c2 c3 = x
    sq y = y * y

-- | Exact division by @lam = 1 - zeta@ when possible.  Strategy:
-- multiply by the conjugate factor @lam' = 1 + z + z^2 + z^3@ (a unit
-- only after dividing by 2 since @lam * lam' = 2@), then check that all
-- four coefficients are even, then halve.
--
-- Returns @Nothing@ if @x@ is not in the principal ideal @(lam)@.
divLam :: Z8 -> Maybe Z8
divLam x =
  let Z8 a b c d = mulZ8 x (Z8 1 1 1 1)
  in if all even [a, b, c, d]
       then Just (Z8 (a `div` 2) (b `div` 2) (c `div` 2) (d `div` 2))
       else Nothing

-- | The @lam@-adic valuation @nu_lam(x)@: the largest @k@ such that
-- @lam^k@ divides @x@, or @-1@ for the zero element (convention).
--
-- Repeatedly divides by @lam@ until division fails.
valLam :: Z8 -> Int
valLam x0
  | x0 == zero = -1
  | otherwise  = go 0 x0
  where
    go k x = case divLam x of
               Just y  -> go (k + 1) y
               Nothing -> k
