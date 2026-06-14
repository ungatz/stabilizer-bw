-- | The lambda-adic grade on Clifford+T diagonal characters
-- (narrative/06-grade.md).
--
-- For a diagonal character @D_e@ defined by @D_e |x> = zeta^{e(x)} |x>@,
-- the lattice grade is the smallest @k@ such that
-- @lam^k * D_e * BW_n <= BW_n@ at the relevant level of the cyclotomic
-- tower.  The closed-form upper bound for single monomials:
--
-- @
--     g(D_{c * x_S}) <= max(0, 2|S| - 2^{nu_2(c)})
-- @
--
-- where @c@ is the eighth-root exponent of the character and @nu_2(c)@
-- the @2@-adic valuation of @c@ mod @8@.  This bound is tight on a
-- large family of named characters and is the headline upper bound of
-- the all-n formalisation.
--
-- This module exposes the closed-form upper bound and a small reference
-- table of named diagonal characters with their kernel-verified grades,
-- so that downstream code can sanity-check grade-aware optimisations
-- against a reproducible numeric baseline.
module Grade
  ( gradeUpperBound
  , nu2
  , namedGrades
  ) where

-- | The @2@-adic valuation of an integer @c@ mod @8@.  Defined for the
-- residues @0..7@; the convention used is the standard one:
--
-- @
--   nu2 0 = 3    (so 2^{nu_2 0} = 8, sending the upper bound to 0)
--   nu2 1 = nu2 3 = nu2 5 = nu2 7 = 0
--   nu2 2 = nu2 6 = 1
--   nu2 4 = 2
-- @
nu2 :: Int -> Int
nu2 c = case c `mod` 8 of
  0 -> 3
  1 -> 0; 3 -> 0; 5 -> 0; 7 -> 0
  2 -> 1; 6 -> 1
  4 -> 2
  _ -> error "nu2: impossible"

-- | The closed-form upper bound for a single-monomial diagonal character
-- @D_{c * x_S}@ on @n@ qubits with @d = |S|@ and @c@ the eighth-root
-- exponent.  Matches the explicit kernel-checked table in
-- 'namedGrades' on every entry.
gradeUpperBound :: Int -> Int -> Int
gradeUpperBound d c = max 0 (2 * d - 2 ^ nu2 c)

-- | A reference table of single-monomial diagonal characters with their
-- kernel-verified grades.  Each entry is @(name, |S|, c, grade)@: a
-- character @D_{c * x_S}@ on @|S|@-or-more qubits.  The bound
-- 'gradeUpperBound' equals the grade on every row.
--
-- The general @T (x) T@-style characters are multi-monomial and follow
-- disjoint-support additivity (@g(T (x) T) = g(T) + g(T) = 2@), not the
-- single-monomial formula above; they are deliberately omitted.
namedGrades :: [(String, Int, Int, Int)]
namedGrades =
  [ -- single-qubit
    ("I",       0, 0, 0)
  , ("Z",       1, 4, 0)
  , ("S",       1, 2, 0)
  , ("T",       1, 1, 1)

    -- two-qubit
  , ("CZ",      2, 4, 0)
  , ("CS",      2, 2, 2)
  , ("cT",      2, 1, 3)

    -- three-qubit
  , ("CCZ",     3, 4, 2)
  , ("CCS",     3, 2, 4)
  , ("ccT",     3, 1, 5)

    -- four-qubit
  , ("CCCZ",    4, 4, 4)
  , ("CCCS",    4, 2, 6)
  , ("cccT",    4, 1, 7)
  ]
