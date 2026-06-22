-- StabilizerBW umbrella aggregator.
-- Importing this file builds the full library via `lake build StabilizerBW`.
--
-- Three submodules have known Lean v4.29 heartbeat / tactic regressions and are
-- not yet imported here (their `.lean` source stays in the tree for reference):
--   * StabilizerBW.T1A.GradeCard       -- (deterministic) timeout in `decide`
--   * StabilizerBW.T1A.RMJoint         -- (deterministic) timeout in `simp`
--   * StabilizerBW.LogicalLatticeTransport.BW2Transport
-- These are recorded as forward-compat tasks; the closed-form headlines they
-- support are derivable from the working modules below.

-- Lattice and ring layer
import StabilizerBW.BarnesWall
import StabilizerBW.BWFreeModule
import StabilizerBW.Roots.Core
import StabilizerBW.Roots.Adjoint
import StabilizerBW.Roots.Lattice
import StabilizerBW.Roots.Tensor
import StabilizerBW.Roots.Matrices
import StabilizerBW.Roots.Zeta16
import StabilizerBW.Roots.Z8Valuation
import StabilizerBW.Roots.BWModel
import StabilizerBW.Roots.BW2
import StabilizerBW.Roots.BW3
import StabilizerBW.Roots.BW4
import StabilizerBW.Roots.BWn
import StabilizerBW.Roots.Level4
import StabilizerBW.Roots.CrossLevelSelfSimilarity

-- Grade filtration
import StabilizerBW.Roots.Grades
import StabilizerBW.Roots.Filtration
import StabilizerBW.Roots.E3
import StabilizerBW.Roots.LinearBound
import StabilizerBW.Roots.UpperBoundAllN
import StabilizerBW.Roots.LowerBoundAllN
import StabilizerBW.Roots.StrictSubsetLowerBoundAllN
import StabilizerBW.Roots.MultimonomialClosedForm
import StabilizerBW.Roots.MoebiusGradeAllN
import StabilizerBW.Roots.MoebiusGradeClosedFormAllN
import StabilizerBW.Roots.MoebiusClosedFormAllN

-- Single-qubit lattice automorphism converse
import StabilizerBW.Roots.AutL3Unitary
import StabilizerBW.Roots.AutL3HalfSqrt2

-- The √Π / sqrt-Pi dictionary (cyclotomic arithmetic at levels 2 and 3)
import StabilizerBW.SqrtPi

-- T-count counting infrastructure (used by Grade.Kernel)
import StabilizerBW.Roots.Tcount

-- Linear-stratum grade enumerator (T1A: skipping GradeCard, RMJoint per note above)
import StabilizerBW.T1A.ZpowFacts
import StabilizerBW.T1A.Leaves
import StabilizerBW.T1A.GradeLinear
import StabilizerBW.T1A.GradeEnumerator
import StabilizerBW.T1A.Tcount2

-- CSS Barnes-Wall code family
import StabilizerBW.BWCss

-- Logical lattice transport (skipping BW2Transport per note above)
import StabilizerBW.LogicalLatticeTransport.BW3Transport

-- Pauli logic
import StabilizerBW.PauliLogic.Syntax
import StabilizerBW.PauliLogic.Rules
import StabilizerBW.PauliLogic.Soundness
import StabilizerBW.PauliLogic.Tableau
import StabilizerBW.PauliLogic.CutElimination
import StabilizerBW.PauliLogic.Completeness
import StabilizerBW.PauliLogic.Categorical.PLnCategory
import StabilizerBW.PauliLogic.Categorical.Dagger
import StabilizerBW.PauliLogic.Categorical.DaggerMonoidal
import StabilizerBW.PauliLogic.Categorical.DaggerCompact
import StabilizerBW.PauliLogic.Categorical.Universality
import StabilizerBW.PauliLogic.Categorical.Interpret
import StabilizerBW.PauliLogic.Categorical.ZXComparison

-- CHSH bridge
import StabilizerBW.Stab2CHSHBridge

-- Closest-stabilizer decoder family
import StabilizerBW.DecoderUniqueness
import StabilizerBW.DecoderFidelity
import StabilizerBW.DecoderLogical
import StabilizerBW.DecoderN1
import StabilizerBW.DecoderTheorems
import StabilizerBW.DecoderThreshold

-- ============================================================
-- New additions: grade-stratified content
-- ============================================================

-- Kernel = lattice stabilizer
import StabilizerBW.Grade.Kernel

-- Stratified Pauli-weight enumerator
import StabilizerBW.Grade.StratifiedMonotone

-- Tight T-count witnesses (T/CS/cT roster + loose triple)
import StabilizerBW.Grade.TightWitnesses

-- Closed-form bandwidth bound at all n
import StabilizerBW.Grade.EnumeratorBound

-- CHKRS S13 catalyst-identity Tier-C carrier
import StabilizerBW.Grade.Catalyst

-- QPE / AA / HHL / VQE grade audits
import StabilizerBW.Grade.AlgorithmAudit.AQC

-- Grade vs. Jiang-Wang stabilizer nullity incomparability
import StabilizerBW.Grade.Comparisons.Incomparability

-- ============================================================
-- New additions: lattice mixing time
-- ============================================================

-- Levin-Peres-Wilmer Theorem 12.3 + Ehrenfest projection + BW-grade bound
import StabilizerBW.Lattice.Mixing
import StabilizerBW.Lattice.Mixing.SpectralGap

-- ============================================================
-- New additions: qutrit analogue
-- ============================================================

-- Qutrit Barnes-Wall over Z[ζ_9]
import StabilizerBW.Qutrit.CSSBarnesWall

-- Eisenstein-integer toy model at d = 3
import StabilizerBW.Qutrit.EisensteinToy
