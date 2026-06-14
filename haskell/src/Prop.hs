-- | Clifford generators as prop morphisms acting on coordinate trees.
--
-- The Barnes-Wall prop has objects @n@ (standing for @BW_n@) and morphisms
-- the lattice-preserving unitaries; the presentation theorem identifies
-- these with the phased Cliffords (see narrative/02-presentation.md).
-- This module implements the generators in their lattice-preserving form:
--
-- @
--   S    = diag(1, i)                          (exact over Z[i])
--   Ht   = ((1 - i)/2) * [[1, 1], [1, -1]]     (rephased Hadamard;
--                                               exact on the Clifford orbit)
--   CX   = controlled-NOT                      (a permutation; exact)
-- @
--
-- Acting on a 'Tree', @qubit q@ means @the split at depth q@.  The same code
-- acts on exact lattice vectors @Tree GI@ and on floating-point targets
-- @CVec@; that polymorphism is the prop discipline paying rent.
-- Equivariance of the decoder (a property tested in Main) is a statement
-- relating the two instantiations.
module Prop
  ( Gen(..)
  , applyGenGI
  , applyGenC
  , applyWordGI
  , applyWordC
  , minimalVectors
  ) where

import Data.Complex (Complex(..))
import Data.List (foldl')
import qualified Data.Set as Set
import GaussianInt
import BW

-- | Clifford generator alphabet (qubits indexed from 0 = root split).
data Gen = S Int | Ht Int | CX Int Int
  deriving (Eq, Show)

-- Exact action on Z[i]-trees (used for lattice data and orbit enumeration).

iGI :: GI -> GI
iGI (GI a b) = GI (negate b) a              -- multiply by i

oneMinusI :: GI
oneMinusI = GI 1 (-1)

halveGI :: GI -> GI
halveGI (GI a b)
  | even a && even b = GI (a `div` 2) (b `div` 2)
  | otherwise        = error "halveGI: left the lattice orbit"

-- Descend to depth q, then act on that split.
atDepth :: Int -> (Tree a -> Tree a) -> Tree a -> Tree a
atDepth 0 f t          = f t
atDepth q f (Node l r) = Node (atDepth (q-1) f l) (atDepth (q-1) f r)
atDepth _ _ (Leaf _)   = error "atDepth: qubit index out of range"

applyGenGI :: Gen -> Tree GI -> Tree GI
applyGenGI (S q)    = atDepth q sGate
  where sGate (Node l r) = Node l (fmap iGI r)
        sGate t          = t
applyGenGI (Ht q)   = atDepth q hGate
  where hGate (Node l r) =
          Node (fmap halveGI (fmap (oneMinusI *) (addT l r)))
               (fmap halveGI (fmap (oneMinusI *) (subT l r)))
        hGate t          = t
applyGenGI (CX c t) = atDepth c cxGate
  where cxGate (Node l r) = Node l (atDepth (t - c - 1) xGate r)
        cxGate tr         = tr
        xGate (Node a b)  = Node b a
        xGate tr          = tr

applyWordGI :: [Gen] -> Tree GI -> Tree GI
applyWordGI w v = foldl' (flip applyGenGI) v w

-- Floating-point action (decoder targets); same shapes, Complex arithmetic.

applyGenC :: Gen -> CVec -> CVec
applyGenC (S q)    = atDepth q sGate
  where sGate (Node l r) = Node l (fmap ((0 :+ 1) *) r)
        sGate t          = t
applyGenC (Ht q)   = atDepth q hGate
  where c = (1 :+ (-1)) / 2
        hGate (Node l r) = Node (scaleT c (addT l r)) (scaleT c (subT l r))
        hGate t          = t
applyGenC (CX cq t) = atDepth cq cxGate
  where cxGate (Node l r) = Node l (atDepth (t - cq - 1) xGate r)
        cxGate tr         = tr
        xGate (Node a b)  = Node b a
        xGate tr          = tr

applyWordC :: [Gen] -> CVec -> CVec
applyWordC w v = foldl' (flip applyGenC) v w

-- | The minimal vectors of @BW_n@ enumerated as the Clifford orbit of
-- @phi^n |0...0>@.  Expected counts (kissing numbers of D_4, E_8, BW_16):
-- 24 at n=1, 240 at n=2, 4320 at n=3.
minimalVectors :: Int -> [Tree GI]
minimalVectors n = Set.toList (go (Set.singleton seed0) [seed0])
  where
    seed0 = basisState (replicate n False)
    -- c < t suffices: CX_{t,c} = (Ht (x) Ht) . CX_{c,t} . (Ht (x) Ht),
    -- so the generated group is the full Clifford group either way.
    gens  = [ S q | q <- [0 .. n-1] ] ++ [ Ht q | q <- [0 .. n-1] ]
         ++ [ CX c t | c <- [0 .. n-1], t <- [c+1 .. n-1] ]
    go seen []       = seen
    go seen (v:rest) =
      let nbrs = [ w | g <- gens, let w = applyGenGI g v
                     , not (Set.member w seen) ]
          seen' = foldl' (flip Set.insert) seen nbrs
      in go seen' (nbrs ++ rest)
