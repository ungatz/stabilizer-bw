-- | Z-axis stabilizer postselect, demonstrating the (1+i) lattice cost.
--
-- The logical-lattice theorem of narrative/03-logical-lattice.md says
--
-- @
--     BW_n^{<Z_1>}  =  (1+i) * |0>_1 (x) BW_{n-1}.
-- @
--
-- That is, restricting to the +1-eigenspace of Z on the first qubit
-- pins the |1>_1 block of every vector to zero, and rescales the
-- surviving |0>_1 block by exactly one factor of @phi = 1+i@. This
-- module checks that statement on concrete data.
--
-- The categorical reading is that a Z-postselect measurement is a
-- handler of the Frobenius monad induced by the Z-basis classical
-- structure (Heunen-Karvonen 2015 §7); the @(1+i)@ factor is the
-- arithmetic cost of one such handler invocation in the BW prop.
-- See narrative/03-logical-lattice.md for the citation and the
-- "small example" section that this module exhibits computationally.
module Postselect
  ( zPostselectQ1
  , inFirstQubitCodespace
  ) where

import GaussianInt
import BW

-- | Apply the Z-postselect on the first qubit: send the |1>_1 block
-- to zero, then attempt to divide the surviving |0>_1 block by @phi@.
-- Returns the inner-lattice representative (a @Tree GI@ at one lower
-- depth) when the input is in the codespace; returns @Nothing@ when
-- the |1>_1 block was non-trivial or when the |0>_1 block failed the
-- @phi@-divisibility check.
zPostselectQ1 :: Tree GI -> Maybe (Tree GI)
zPostselectQ1 (Node u w)
  | isZero w  = travPhi u
  | otherwise = Nothing
  where
    isZero (Leaf z)   = z == GI 0 0
    isZero (Node l r) = isZero l && isZero r
    travPhi (Leaf z)   = Leaf <$> divPhi z
    travPhi (Node l r) = Node <$> travPhi l <*> travPhi r
zPostselectQ1 _ = Nothing

-- | A vector lies in @BW_n^{<Z_1>}@ if and only if 'zPostselectQ1'
-- succeeds and the resulting inner-lattice representative is itself
-- a vector of @BW_{n-1}@.
inFirstQubitCodespace :: Tree GI -> Bool
inFirstQubitCodespace v = case zPostselectQ1 v of
  Just v' -> inBW v'
  Nothing -> False
