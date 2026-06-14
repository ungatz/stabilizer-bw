-- | A small demo battery exercising every module.
--
-- Build:
--
-- @
--     ghc -O2 -isrc Main.hs -o stab-bw && ./stab-bw
-- @
--
-- Each line below pairs a numerical claim with its theoretical source.
module Main (main) where

import Data.Complex (Complex(..), mkPolar)
import Text.Printf (printf)

import GaussianInt
import BW
import Decoder
import Fidelity
import Prop
import PauliLogic
import Cyclotomic
import Grade
import Transport

-- Build a CVec from a flat list of length 2^n.
fromList :: [Complex Double] -> CVec
fromList [z] = Leaf z
fromList zs  = let (a, b) = splitAt (length zs `div` 2) zs
               in Node (fromList a) (fromList b)

main :: IO ()
main = do
  putStrLn "== stabilizer / Barnes-Wall demo battery =="

  -- 1. Lattice membership via the free-module decomposition.
  let v00 = basisState [False, False]            -- phi^2 |00>
      bad = Node (Leaf (GI 1 0)) (Leaf (GI 0 0)) -- |0>, unscaled: NOT in BW_1
  printf "phi^2|00> in BW_2:      %s   (expect True)\n"  (show (inBW v00))
  printf "unscaled |0> in BW_1:   %s   (expect False)\n" (show (inBW bad))
  printf "norm^2 phi^2|00> = %d   (expect 4)\n"          (normSqGI v00)

  -- 2. Minimal-vector counts (Clifford orbit; presentation theorem).
  --    Expect 24 at n=1, 240 at n=2: the kissing numbers of D_4, E_8.
  printf "minimal vectors n=1:   %d   (expect 24)\n"  (length (minimalVectors 1))
  printf "minimal vectors n=2:   %d   (expect 240)\n" (length (minimalVectors 2))

  -- 3. Named-state fidelities (numbers below match a separate Python suite).
  let thetaT = acos (1 / sqrt 3) / 2
      tState = fromList [ (cos thetaT :+ 0)
                        , mkPolar (sin thetaT) (pi / 4) ]
      hState = fromList [ cos (pi/8) :+ 0, sin (pi/8) :+ 0 ]
      hh     = kron hState hState
  printf "F(T)  = %.7f   (expect 0.8880738)\n" (fidLowerBound (fidelity 64 tState))
  printf "F(H)  = %.7f   (expect cos pi/8 = 0.9238795)\n"
         (fidLowerBound (fidelity 64 hState))
  printf "F(HH) = %.7f   (expect cos^2 pi/8 = 0.8535534)\n"
         (fidLowerBound (fidelity 64 hh))

  -- 4. BDD planted-recovery (inside the promise radius).
  let plant = toCVec (basisState [False, True, False])         -- phi^3 |010>
      noise = fromList [ mkPolar 0.16 (fromIntegral k) | k <- [0..7] ]
      recov = decode (addT plant noise)
  printf "BDD recovery (n=3, planted + noise): %s\n" (show (recov == plant))

  -- 5. Equivariance: decode (U s) == U (decode s) for a Clifford word U.
  let w     = [Ht 0, S 1, CX 0 1, S 0]
      noise2 = fromList [ mkPolar 0.2 (2.2 * fromIntegral k) | k <- [0..3] ]
      s0    = addT (toCVec (basisState [False, False])) noise2
      lhs   = decode (applyWordC w s0)
      rhs   = applyWordC w (decode s0)
  printf "equivariance D(U s) == U D(s):  %s\n" (show (closeT lhs rhs))

  -- 6. Pauli logic: derive XX from {XI, IX}; certificate via cut elimination.
  let n   = 2
      gam = [pX n 0, pX n 1]                       -- XI, IX
      prf = Mul (Ax 0) (Ax 1)                      -- a PL_2 proof of |- XX
      Certificate concl used = normalize gam prf
  printf "PL_2: from {XI, IX} derived %s using rows %s (expect XX, [0,1])\n"
         (showP concl) (show used)
  printf "PL_2 search: entail {XI, IX} |- XX:  %s\n"
         (show (fmap certUsed (entail gam (mkPauli False "XX"))))

  -- 7. Measurement as an effect: measure Z_1 on the Bell state <ZZ, XX>.
  let bell = fromGenerators [mkPauli False "ZZ", mkPauli False "XX"]
      run k = runSim k (measure (mkPauli False "ZI") bell)
      outs  = [ fst (run k) | k <- [1 .. 10] ]
  printf "Bell, measure Z_1, 10 seeded runs: %s\n" (show outs)
  let (_, post) = run 1
  printf "post-measurement theory (one run): %s\n" (unwords (map showP post))

  -- 8. Cyclotomic arithmetic: lambda^2 and the valuation chain.
  let lam2 = mulZ8 lam lam
      lam3 = mulZ8 lam2 lam
      lam4 = mulZ8 lam2 lam2
  printf "lam   = %s\n" (show lam)
  printf "lam^2 = %s\n" (show lam2)
  printf "lam^3 = %s\n" (show lam3)
  printf "lam^4 = %s   (expect a Z[i] associate of 2)\n" (show lam4)
  printf "nu_lam(lam^k) for k = 0..4:  %s   (expect [-1 or 0, 1, 2, 3, 4])\n"
         (show (map valLam [one, lam, lam2, lam3, lam4]))

  -- 9. Grade closed form vs kernel-verified table.
  putStrLn ""
  putStrLn "Grade table cross-check (formula vs kernel-verified value):"
  putStrLn "  name   |S|   c   formula   table"
  mapM_ printRow namedGrades

  -- 10. R11 transport step: every two-qubit Clifford generator preserves BW_2.
  putStrLn ""
  putStrLn "R11 transport check (every two-qubit generator preserves BW_2):"
  mapM_
    (\(name, g) -> printf "  %-8s %s\n" name (show (preservesBW2 g)))
    twoQubitGenerators

  putStrLn "== done =="
  where
    printRow (name, d, c, expected) =
      let pred_ = gradeUpperBound d c
      in printf "  %-7s %d    %d   %5d    %5d   %s\n"
                name d c pred_ expected
                (if pred_ == expected then "ok" else "MISMATCH")
    kron :: CVec -> CVec -> CVec
    kron (Leaf a) t   = fmap (a *) t
    kron (Node l r) t = Node (kron l t) (kron r t)
    closeT a b = normSqC (subT a b) < 1e-9
    showP (Pauli s xs zs) =
      (if s then "-" else "+") ++
      [ letter x z | (x, z) <- zip xs zs ]
      where letter False False = 'I'
            letter True  False = 'X'
            letter False True  = 'Z'
            letter True  True  = 'Y'
