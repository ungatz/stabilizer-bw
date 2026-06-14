{-# LANGUAGE DeriveFunctor #-}
-- | The Barnes-Wall lattice tower @BW_n@, structurally.
--
-- The free-module decomposition (see narrative/01-bw-family.md and
-- narrative/03-logical-lattice.md) says every @w@ in @BW_n@ is uniquely
--
-- @
--     w = (1 + i)|0> (x) a  +  (|0> + |1>) (x) b,     a, b in BW_{n-1};
-- @
--
-- in coordinates (Micciancio-Nicolosi convention):
--
-- @
--     BW_{n+1} = { [u, u + phi*v] : u, v in BW_n }.
-- @
--
-- Read as data: an n-qubit coordinate vector is a balanced binary tree of
-- depth @n@, i.e. an element of the initial algebra of the pairing functor
-- over the leaf type.  Membership in @BW_n@ is then structural recursion
-- and nothing else.  This module is that sentence, compiled.
module BW
  ( Tree(..)
  , depth
  , zipTree
  , mapTree
  , foldTree
  , scaleT
  , addT, subT
  , CVec
  , toCVec
  , inBW
  , normSqGI
  , dotC
  , normSqC
  , basisState
  , stabFromGens
  ) where

import Data.Complex (Complex(..), conjugate, realPart)
import GaussianInt

-- | Balanced binary tree, the iterated-pair coordinate space @Q n@:
-- @Q 0 = GI@, @Q (n + 1) = Q n x Q n@.  The @|0>@-block is the left
-- child, the @|1>@-block the right child of the first qubit.
data Tree a = Leaf a | Node (Tree a) (Tree a)
  deriving (Eq, Ord, Show, Functor)

depth :: Tree a -> Int
depth (Leaf _)   = 0
depth (Node l _) = 1 + depth l

-- | Structural fold (catamorphism).  Everything in this module is either a
-- fold or a zip; the decoder (Decoder) is a hylomorphism refining this.
foldTree :: (a -> r) -> (r -> r -> r) -> Tree a -> r
foldTree leaf _    (Leaf a)   = leaf a
foldTree leaf node (Node l r) = node (foldTree leaf node l) (foldTree leaf node r)

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree = fmap

zipTree :: (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipTree f (Leaf a)   (Leaf b)   = Leaf (f a b)
zipTree f (Node l r) (Node l' r') = Node (zipTree f l l') (zipTree f r r')
zipTree _ _ _ = error "zipTree: shape mismatch (different qubit counts)"

addT, subT :: Num a => Tree a -> Tree a -> Tree a
addT = zipTree (+)
subT = zipTree (-)

scaleT :: Num a => a -> Tree a -> Tree a
scaleT c = fmap (c *)

-- | Floating-point coordinate vectors (decoder targets).
type CVec = Tree (Complex Double)

toCVec :: Tree GI -> CVec
toCVec = fmap toComplex

-- | Barnes-Wall membership, by the free-module decomposition alone:
--
-- @
--   Leaf z          : BW_0 = Z[i], always.
--   Node u w in BW  <=>  u in BW  and  (w - u) = phi * v  with  v in BW.
-- @
inBW :: Tree GI -> Bool
inBW (Leaf _)   = True
inBW (Node u w) =
  inBW u && case travPhi (subT w u) of
              Nothing -> False
              Just v  -> inBW v
  where
    travPhi :: Tree GI -> Maybe (Tree GI)
    travPhi (Leaf a)   = Leaf <$> divPhi a
    travPhi (Node l r) = Node <$> travPhi l <*> travPhi r

-- | Exact squared norm of a lattice vector.  The minimal vectors of @BW_n@
-- have @normSqGI == 2^n@ (the scaled stabilizer states).
normSqGI :: Tree GI -> Integer
normSqGI = foldTree normGI (+)

-- | Hermitian inner product and squared norm on targets.
dotC :: CVec -> CVec -> Complex Double
dotC u v = foldTree id (+) (zipTree (\a b -> conjugate a * b) u v)

normSqC :: CVec -> Double
normSqC v = realPart (dotC v v)

-- | @phi^n |x>@ for a bitstring @x@: the canonical scaled computational-basis
-- stabilizer vectors (lattice minimal vectors with trivial phases).
basisState :: [Bool] -> Tree GI
basisState bits = go bits amp0
  where
    amp0 = foldr (\_ acc -> phi * acc) (GI 1 0) bits   -- phi^n
    go []     amp = Leaf amp
    go (b:bs) amp =
      let sub  = go bs amp
          zero = fmap (const (GI 0 0)) sub
      in if b then Node zero sub else Node sub zero

-- | Apply a list of generator actions to a seed vector.  Used by "Prop" to
-- build stabilizer states as Clifford-orbit points.
stabFromGens :: [Tree GI -> Tree GI] -> Tree GI -> Tree GI
stabFromGens gens seedV = foldl (flip ($)) seedV gens
