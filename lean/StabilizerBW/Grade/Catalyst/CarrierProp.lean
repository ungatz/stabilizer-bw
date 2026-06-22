import StabilizerBW.SqrtPi.Catalyst.Phi3General

/-!
# CHKRS S13 — the composite-level catalyst-identity carrier `CompositeS13Discharge`

This module introduces the single named `Prop` carrier of the development.  The literal
composite-level inequality
`grade₂(Φ₃ w) ≤ grade₃ w`  (CHKRS 2026 PNAS, SI Lemma S13, level `3 → 2` step)
is the arithmetic shadow of the catalyst identity.  The corpus already records (in
`Pi3.Headline_T3_general`) that the *naive* structural induction is invalid, because the
lattice grade is only **subadditive** under composition (`Pi3.gradeWrt2_mul`,
`Pi3.grade_mul`), not additive.  The genuinely-deep ingredient is therefore the composite
step, which we package as the `composite` field of the carrier below.

The carrier is a `Prop` *hypothesis*, **not** a Lean axiom: every downstream theorem that
uses it carries it as an explicit argument, so the axiom footprint stays inside
`{propext, Classical.choice, Quot.sound}`.
-/

namespace CHKRS_S13_CompositeCatalystGrade

open Pi3 SqWord

/-- **The composite-level CHKRS S13 discharge predicate.**

* `gen` packages the generator-level inequality `grade₂(Φ₃ g) ≤ grade₃ g` for the four
  single-qubit generators `X, V, S, T`.  This part is in fact *provable* unconditionally
  (see `gen_discharged`, via `Pi3.grade2_toPi2_gen_eq`); it is included so that the carrier's
  shape matches the structural induction on `SqWord`.
* `composite` is the genuinely-deep step: it lifts the inequality from the two
  sub-words of a composite `comp a b` to the composite itself.  This is the catalyst-identity
  content (CHKRS S13) and is the only field that is not already discharged in the corpus. -/
structure CompositeS13Discharge : Prop where
  gen :
    Pi2.grade2 (toPi2 .xg) ≤ grade2obj (toPi3 .xg) ∧
    Pi2.grade2 (toPi2 .vg) ≤ grade2obj (toPi3 .vg) ∧
    Pi2.grade2 (toPi2 .sg) ≤ grade2obj (toPi3 .sg) ∧
    Pi2.grade2 (toPi2 .tg) ≤ grade2obj (toPi3 .tg)
  composite : ∀ (a b : SqWord),
    Pi2.grade2 (toPi2 a) ≤ grade2obj (toPi3 a) →
    Pi2.grade2 (toPi2 b) ≤ grade2obj (toPi3 b) →
    Pi2.grade2 (toPi2 (.comp a b)) ≤ grade2obj (toPi3 (.comp a b))

end CHKRS_S13_CompositeCatalystGrade
