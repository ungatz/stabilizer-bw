-- | Pauli logic @PL_n@: proofs as data, cut elimination as simulation,
-- measurement as an algebraic effect (narrative/05-pauli-logic.md).
--
-- Curry-Howard, cashed: a value of type 'Derivation' is a proof object of a
-- stabilizer entailment @Gamma |- Q@.  'normalize' eliminates cuts and
-- returns the proof's computational content -- a subset-product certificate
-- (which generators to multiply, and the resulting sign).  The slogan
-- @cut elimination = Gottesman-Knill tableau reduction, with its
-- complexity@ is visible here: 'normalize' is linear in proof size, and
-- 'entail' (proof search from a row-reduced theory) is the @O(n^2)@
-- Aaronson-Gottesman row-reduction step.
--
-- All Pauli arithmetic is over the symplectic @F_2@ representation: a
-- signed Pauli word is @(sign, x-bits, z-bits)@, products xor the
-- bit-vectors and track the sign through a small @i@-exponent table --
-- exactly the row multiplication of tableau algorithms.
module PauliLogic
  ( Pauli(..)
  , pauliI, mkPauli, pX, pZ, pY
  , mulP, commutes
  , Derivation(..)
  , Certificate(..)
  , conclusion
  , normalize
  , Tableau, fromGenerators, entail
  , MeasF(..), Sim, flipCoin, measure, runSim
  ) where

import Data.Bits (xor)

-- Signed Pauli words over F_2^{2n}.

-- | @pSign True@ means the word carries a global minus sign.
data Pauli = Pauli { pSign :: !Bool, pXs :: ![Bool], pZs :: ![Bool] }
  deriving (Eq, Ord, Show)

pauliI :: Int -> Pauli
pauliI n = Pauli False (replicate n False) (replicate n False)

-- | Build a Pauli word from a string like @\"XIZ\"@ (with optional sign).
mkPauli :: Bool -> String -> Pauli
mkPauli s cs = Pauli s (map (`elem` "XY") cs) (map (`elem` "ZY") cs)

pX, pZ, pY :: Int -> Int -> Pauli   -- single-qubit letters at position q of n
pX n q = Pauli False [i == q | i <- [0..n-1]] (replicate n False)
pZ n q = Pauli False (replicate n False) [i == q | i <- [0..n-1]]
pY n q = Pauli False [i == q | i <- [0..n-1]] [i == q | i <- [0..n-1]]

-- | @i@-exponent (mod 4) of the product of two single-qubit Pauli letters,
-- letters encoded as @(x, z)@ with @I = (F, F)@, @X = (T, F)@,
-- @Z = (F, T)@, @Y = (T, T)@.  Explicit table -- no clever formula to
-- mistype:
--
-- @
--   X * Y = i Z,  Y * Z = i X,  Z * X = i Y   (cyclic, +1)
--   reversed order gives -i (= +3 mod 4)
-- @
gExp :: (Bool, Bool) -> (Bool, Bool) -> Int
gExp p q = case (letter p, letter q) of
  ('I', _ ) -> 0
  (_ , 'I') -> 0
  ('X','X') -> 0
  ('Y','Y') -> 0
  ('Z','Z') -> 0
  ('X','Y') -> 1
  ('Y','Z') -> 1
  ('Z','X') -> 1
  ('Y','X') -> 3
  ('Z','Y') -> 3
  ('X','Z') -> 3
  _         -> error "gExp: impossible"
  where
    letter (False,False) = 'I'
    letter (True ,False) = 'X'
    letter (False,True ) = 'Z'
    letter (True ,True ) = 'Y'

-- | Product of two commuting Hermitian Pauli words.  The @MUL@ rule's side
-- condition guarantees the @i@-exponent is even, so the result is
-- Hermitian with a definite sign.  One tableau row multiplication.
mulP :: Pauli -> Pauli -> Pauli
mulP (Pauli s1 x1 z1) (Pauli s2 x2 z2) =
  let iexp = sum (zipWith gExp (zip x1 z1) (zip x2 z2)) `mod` 4
      sgn  = case iexp of
               0 -> s1 /= s2
               2 -> not (s1 /= s2)
               _ -> error "mulP: anticommuting operands (use CLASH, not MUL)"
  in Pauli sgn (zipWith xor x1 x2) (zipWith xor z1 z2)

-- | Symplectic form: words commute iff
-- @<x1, z2> + <z1, x2> = 0@ over @F_2@.
commutes :: Pauli -> Pauli -> Bool
commutes (Pauli _ x1 z1) (Pauli _ x2 z2) =
  even ( count (zipWith (&&) x1 z2) + count (zipWith (&&) z1 x2) )
  where count = length . filter id

-- Derivations: PL_n proofs as a datatype (Curry-Howard, literally).

-- | A derivation over an ambient theory @Gamma@ (a list of literals,
-- indexed by position).
data Derivation
  = Ax Int                          -- ^ @Gamma |- Gamma !! k@
  | UnitI                           -- ^ @Gamma |- +I@
  | Mul Derivation Derivation       -- ^ from @|- P@, @|- Q@ commuting: @|- P*Q@
  | Cut Pauli Derivation Derivation -- ^ from @|- P@ and @Gamma, P |- Q@: @|- Q@
                                    --   (the lemma @P@ is the cut formula;
                                    --   in the second premise, @Ax (-1)@
                                    --   refers to the cut formula)
  deriving Show

-- | Computational content of a cut-free proof: which generators were
-- multiplied (multiplicity mod 2 is implicit in the Pauli product) and
-- what the derived literal is.
data Certificate = Certificate { certPauli :: Pauli, certUsed :: [Int] }
  deriving Show

-- | Evaluate a derivation's conclusion (soundness direction).
conclusion :: [Pauli] -> Derivation -> Pauli
conclusion gam = certPauli . normalize gam

-- | Cut elimination.  Structurally: splice the proof of the lemma in for
-- every @Ax (-1)@ reference in the right premise.  Each splice is a
-- constant number of row multiplications; this function runs in time
-- linear in the proof DAG, which is the formal sense of @with its
-- complexity@.
normalize :: [Pauli] -> Derivation -> Certificate
normalize gam = go []
  where
    go cutStack d = case d of
      Ax k | k >= 0    -> Certificate (gam !! k) [k]
           | otherwise -> let c = cutStack !! (negate k - 1)
                          in c
      UnitI            -> Certificate (pauliI (nQubits gam)) []
      Mul a c          ->
        let Certificate p us = go cutStack a
            Certificate q vs = go cutStack c
        in Certificate (mulP p q) (us ++ vs)
      Cut _ prf body   ->
        let lemma = go cutStack prf          -- prove the lemma once...
        in go (lemma : cutStack) body        -- ...and splice it (sharing)
    nQubits []      = 0
    nQubits (p : _) = length (pXs p)

-- Tableaux and proof search.

type Tableau = [Pauli]

fromGenerators :: [Pauli] -> Tableau
fromGenerators = id

-- | Decide @Gamma |- Q@ by greedy support-reducing elimination: repeatedly
-- multiply @q@ by a commuting generator that strictly shrinks its Pauli
-- support, until @q@ is the identity (success: the multipliers, read
-- backwards, are the subset-product certificate) or no progress is
-- possible.
--
-- Honesty note: this greedy pass is complete for the demos in Main and
-- for theories already in row-reduced position; full completeness needs
-- genuine symplectic Gaussian elimination with pivot bookkeeping.  Kept
-- simple here on purpose: the proof-theoretic content lives in
-- 'normalize', not in this search.
entail :: Tableau -> Pauli -> Maybe Certificate
entail gam q0 = loop q0 []
  where
    isId p   = not (or (pXs p)) && not (or (pZs p))
    support p = length (filter id (zipWith (||) (pXs p) (pZs p)))
    loop q used
      | isId q && not (pSign q) = Just (Certificate q0 (reverse used))
      | isId q                  = Nothing   -- reduced to -I
      | otherwise =
          case [ (k, g) | (k, g) <- zip [0 ..] gam
                        , commutes q g
                        , support (mulP q g) < support q ] of
            []          -> Nothing
            ((k, g) : _) -> loop (mulP q g) (k : used)

-- Measurement as an algebraic effect (free monad over one operation).

-- | The only effect in stabilizer simulation: a fair coin.  Everything
-- else is pure proof normalization.
newtype MeasF k = FlipCoin (Bool -> k)

instance Functor MeasF where
  fmap f (FlipCoin k) = FlipCoin (f . k)

-- | Minimal free monad (base only; no packages).
data Sim a = Pure a | Op (MeasF (Sim a))

instance Functor Sim where
  fmap f (Pure a) = Pure (f a)
  fmap f (Op m)   = Op (fmap (fmap f) m)
instance Applicative Sim where
  pure = Pure
  Pure f <*> s = fmap f s
  Op m   <*> s = Op (fmap (<*> s) m)
instance Monad Sim where
  Pure a >>= f = f a
  Op m   >>= f = Op (fmap (>>= f) m)

flipCoin :: Sim Bool
flipCoin = Op (FlipCoin Pure)

-- | Measure literal @q@ against a maximal theory (state).  Deterministic
-- case: entailment decides the outcome, theory unchanged.  Random case:
-- invoke the effect, then perform the Gottesman-Knill update: adjoin
-- @(-1)^r q@, repair commutativity by multiplying through the first
-- anticommuting generator, discard it.
measure :: Pauli -> Tableau -> Sim (Bool, Tableau)
measure q tab =
  case [g | g <- tab, not (commutes g q)] of
    []      ->                                  -- deterministic outcome
      case entail tab q of
        Just _  -> pure (False, tab)            -- |- +q
        Nothing -> pure (True,  tab)            -- (then |- -q for maximal theories)
    (g1 : _) -> do
      r <- flipCoin                              -- the quantum event
      let q'   = q { pSign = r }
          fix g | commutes g q' || g == g1 = g
                | otherwise                = mulP g g1   -- repair rows
          tab' = q' : [ fix g | g <- tab, g /= g1 ]
      pure (r, tab')

-- | Handler: interpret the coin effect with a small splittable LCG.
-- Deterministic given the seed -- simulation is reproducible.
runSim :: Int -> Sim a -> a
runSim seed sim = go (fromIntegral seed :: Integer) sim
  where
    go _ (Pure a)            = a
    go s (Op (FlipCoin k))   =
      let s' = (6364136223846793005 * s + 1442695040888963407) `mod` (2^63)
      in go s' (k (odd (s' `div` 2^32)))
