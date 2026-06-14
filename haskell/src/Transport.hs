-- | A computational realisation of the small-n logical-lattice transport
-- step (narrative/07-r11-transport.md).
--
-- The general-Clifford transport step of the logical-lattice theorem
-- (narrative/03-logical-lattice.md) says: for any lattice-preserving
-- Clifford @U@, @U * (BW_n)^S = (BW_n)^{USU^{-1}}@.  The Lean
-- formalisation cited in the narrative kernel-checks this directly at
-- @n = 2@ and @n = 3@ by verifying every Clifford generator preserves
-- @BW_n@.  This module reproduces the verification numerically.
--
-- The 11 two-qubit generators @Z_1, Z_2, X_1, X_2, S_1, S_2,
-- CNOT_{1,2}, CNOT_{2,1}, CZ, Had_1, Had_2@ are exhibited as
-- @Tree GI -> Tree GI@ actions, and the 'preservesBW2' predicate
-- checks each one against the explicit BW_2 spanning set.  The
-- analogous n = 3 check is also available.
--
-- Note on the Hadamard.  The genuine @1/sqrt 2@ Hadamard is not
-- representable as a lattice map over @Z[i]@; the kernel and this
-- module use the @sqrt 2@-scaled integer lift @[[1, 1], [1, -1]]@,
-- which maps @BW_n@ into itself (it preserves the lattice as a set, up
-- to a uniform scale factor).  See narrative/07-r11-transport.md for
-- the honest scope note.
module Transport
  ( -- * Two-qubit generators
    z1, z2, x1, x2
  , s1, s2
  , cnot12, cnot21
  , cz
  , had1Int, had2Int
    -- * Spanning set and the test
  , bw2Span
  , preservesBW2
  , twoQubitGenerators
  ) where

import GaussianInt
import BW
import Prop (Gen(..), applyGenGI)

-- The exact two-qubit Clifford generators.

-- @Z_q@ acts on the @|1>@-block by negation.
z1 :: Tree GI -> Tree GI
z1 (Node l r) = Node l (fmap negate r)
z1 t          = t

z2 :: Tree GI -> Tree GI
z2 (Node l r) = Node (zBlock l) (zBlock r)
  where zBlock (Node a b) = Node a (fmap negate b)
        zBlock x          = x
z2 t          = t

-- @X_q@ swaps the @|0>@- and @|1>@-blocks.
x1 :: Tree GI -> Tree GI
x1 (Node l r) = Node r l
x1 t          = t

x2 :: Tree GI -> Tree GI
x2 (Node l r) = Node (xBlock l) (xBlock r)
  where xBlock (Node a b) = Node b a
        xBlock x          = x
x2 t          = t

-- @S_q = diag(1, i)@ on qubit @q@.
s1, s2 :: Tree GI -> Tree GI
s1 = applyGenGI (S 0)
s2 = applyGenGI (S 1)

-- @CNOT_{c, t}@: control on qubit @c@, target on qubit @t@.
-- Only the listed direction is implemented here; the reversed direction
-- is realised by @(Had x Had) o CNOT_{c, t} o (Had x Had)@ and so
-- generates no new lattice fact at this level.
cnot12 :: Tree GI -> Tree GI
cnot12 = applyGenGI (CX 0 1)

cnot21 :: Tree GI -> Tree GI
cnot21 (Node l r) =
  -- swap, apply CNOT_{1,2}, swap back
  let Node l' r' = applyGenGI (CX 0 1) (Node r l)
  in Node r' l'
cnot21 t = t

-- @CZ@: diagonal with @-1@ on the @|11>@ entry.
cz :: Tree GI -> Tree GI
cz (Node l (Node a b)) = Node l (Node a (fmap negate b))
cz t                   = t

-- Integer (sqrt 2-scaled) Hadamard on qubit @q@: @|0> |-> |0> + |1>@,
-- @|1> |-> |0> - |1>@.  Maps @BW_n@ into itself (no halving needed).
had1Int :: Tree GI -> Tree GI
had1Int (Node l r) = Node (addT l r) (subT l r)
had1Int t          = t

had2Int :: Tree GI -> Tree GI
had2Int (Node l r) = Node (hb l) (hb r)
  where hb (Node a b) = Node (addT a b) (subT a b)
        hb x          = x
had2Int t          = t

-- | A Z[i]-basis of @BW_2 = B^(x2) Z[i]^4@, where
-- @B = [[1 + i, 1], [0, 1]]@ is the @n = 1@ basis matrix.  The columns of
-- @B (x) B@ are
--
-- @
--     v_0 = (B (x) B) |00> = (phi^2,   0,    0,   0)
--     v_1 = (B (x) B) |01> = (phi,   phi,    0,   0)
--     v_2 = (B (x) B) |10> = (phi,     0,  phi,   0)
--     v_3 = (B (x) B) |11> = (1,       1,    1,   1)
-- @
--
-- Every element of @BW_2@ is a @Z[i]@-linear combination of these four.
-- A linear map preserves @BW_2@ iff it preserves each of @v_0, v_1, v_2,
-- v_3@; this is what 'preservesBW2' checks.
bw2Span :: [Tree GI]
bw2Span =
  [ tree [phi2,   z,     z,    z   ]   -- v_0
  , tree [phi,    phi,   z,    z   ]   -- v_1
  , tree [phi,    z,     phi,  z   ]   -- v_2
  , tree [one,    one,   one,  one ]   -- v_3
  ]
  where
    z    = GI 0 0
    one  = GI 1 0
    phi2 = phi * phi                          -- (1 + i)^2 = 2 i
    tree [a, b, c, d] = Node (Node (Leaf a) (Leaf b))
                            (Node (Leaf c) (Leaf d))
    tree _ = error "bw2Span: expected exactly four amplitudes"

-- | Test whether an action preserves @BW_2@ as a set (i.e. maps every
-- element of @BW_2@ to another element of @BW_2@).
preservesBW2 :: (Tree GI -> Tree GI) -> Bool
preservesBW2 act = all inBW (map act bw2Span)

-- | The full named list of two-qubit generators, for batch testing.
twoQubitGenerators :: [(String, Tree GI -> Tree GI)]
twoQubitGenerators =
  [ ("Z_1",      z1)
  , ("Z_2",      z2)
  , ("X_1",      x1)
  , ("X_2",      x2)
  , ("S_1",      s1)
  , ("S_2",      s2)
  , ("CNOT_12",  cnot12)
  , ("CNOT_21",  cnot21)
  , ("CZ",       cz)
  , ("Had_1",    had1Int)
  , ("Had_2",    had2Int)
  ]
