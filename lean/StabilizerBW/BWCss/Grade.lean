import StabilizerBW.BWCss.CSS

/-!
# Grade-to-logical-operator correspondence and the grade-refined enumerator

This module bridges diagonal Clifford+T *phase polynomials* on `m` qubits to the
logical-operator structure of the Reed–Muller-pair CSS code `CSSCode.ofRMPair`.

* `PhasePoly m` is a phase polynomial `P(x) = ∑_S c_S ∏_{i∈S} x_i` with
 coefficients `c_S ∈ ℤ/8`.
* `PhasePoly.f2Reduce` is the coefficient-wise reduction `ℤ/8 → 𝔽₂` followed by
 evaluation, landing in `Fin (2^m) → ZMod 2`.
* `grade_logical_correspondence` shows the operator is a nontrivial logical-X
 representative of the code iff its 𝔽₂-reduction lies in `RM(r₁,m) \ RM(r₂,m)`.

For the **grade-refined enumerator** we prove, for *all* `m`, the closed form
`G_m(z) = 8 · 4^m · (1 + z)^m` for the grade enumerator of degree-`≤ 1` phase
polynomials, where the grade is the T-count `#{i : b_i odd}`. The headline
`grade_refined_logical_enumerator` is an *interface theorem*: it carries the
literature-absent bridge from the CSS logical-operator enumerator to this
grade enumerator as a named hypothesis, and discharges the closed-form value
`8 · 4^m · (1 + X)^m` (which is the all-`m` Möbius/grade closed form, the analog
of the per-vector formula `Roots.MoebiusClosed.mobius_eq_grade_allN`).
-/

open scoped BigOperators
open Classical

namespace BWCss

/-- The coefficient-wise reduction `ℤ/8 → 𝔽₂`. -/
def reduce8to2 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

/-- A phase polynomial on `m` qubits: `P(x) = ∑_S c_S ∏_{i∈S} x_i`, given by its
coefficient function `c : Finset (Fin m) → ℤ/8`. -/
def PhasePoly (m : ℕ) := Finset (Fin m) → ZMod 8

/-- The (RM) degree of a phase polynomial: the largest size of a monomial with a
nonzero coefficient. -/
def PhasePoly.degree {m : ℕ} (P : PhasePoly m) : ℕ :=
 (Finset.univ.filter (fun S => P S ≠ 0)).sup Finset.card

/-- The 𝔽₂-reduction of a phase polynomial as a Boolean function. -/
noncomputable def PhasePoly.f2ReduceBool {m : ℕ} (P : PhasePoly m) : BoolFun m :=
 ∑ S, (reduce8to2 (P S)) • mono m S

/-- The 𝔽₂-reduction of a phase polynomial as a length-`2^m` codeword. -/
noncomputable def PhasePoly.f2Reduce {m : ℕ} (P : PhasePoly m) : Fin (2 ^ m) → ZMod 2 :=
 ptEquiv m P.f2ReduceBool

/-- The logical operator represented by a phase polynomial (its X-component). -/
noncomputable def PhasePoly.toLogicalOp {m : ℕ} (P : PhasePoly m) : Fin (2 ^ m) → ZMod 2 :=
 P.f2Reduce

/-- The set of nontrivial logical-X representatives of a CSS code: elements of
`C₁ = CZᗮ` outside the X-stabiliser `CX = C₂`. -/
def CSSCode.logicalX (code : CSSCode) : Set (Fin code.n → ZMod 2) :=
 {c | c ∈ dualCode code.CZ ∧ c ∉ code.CX}

/-
**Grade-to-logical-operator correspondence.** A degree-`≤ r₁` phase-polynomial
operator is a nontrivial logical-X representative of `CSSCode.ofRMPair m r₁ r₂`
iff its 𝔽₂-reduction lies in `RM(r₁,m)` but not `RM(r₂,m)`.
-/
theorem grade_logical_correspondence (m r₁ r₂ : ℕ) (h : r₂ < r₁)
 (hcss : r₁ + r₂ ≤ m - 1) (P : PhasePoly m) (hP : P.degree ≤ r₁) :
 let code := CSSCode.ofRMPair m r₁ r₂ h hcss
 (P.toLogicalOp ∈ code.logicalX) ↔
 (P.f2Reduce ∈ RM r₁ m ∧ P.f2Reduce ∉ RM r₂ m) := by
 unfold CSSCode.ofRMPair;
 unfold CSSCode.logicalX PhasePoly.toLogicalOp;
 grind +suggestions

/-! ### The grade-refined enumerator: closed form for all `m` -/

/-- The grade (T-count) of a degree-`≤ 1` phase polynomial `a + ∑ b_i x_i`,
namely the number of odd linear coefficients `#{i : b_i odd}`. -/
def phaseGrade {m : ℕ} (b : Fin m → ZMod 8) : ℕ :=
 (Finset.univ.filter (fun i => reduce8to2 (b i) = 1)).card

/-- The grade-refined enumerator of degree-`≤ 1` phase-polynomial operators on
`m` qubits: `∑_{a, b} X^{grade(a,b)}` over all constants `a ∈ ℤ/8` and linear
parts `b : Fin m → ℤ/8`. -/
noncomputable def gradeEnumerator (m : ℕ) : Polynomial ℕ :=
 ∑ _a : ZMod 8, ∑ b : Fin m → ZMod 8, (Polynomial.X) ^ (phaseGrade b)

/-
**All-`m` closed form of the grade enumerator** (Möbius/grade closed form
`G_m(z) = 8 · 4^m · (1 + z)^m`), proven from scratch for every `m`.
-/
theorem gradeEnumerator_closed_form (m : ℕ) :
 gradeEnumerator m = 8 * 4 ^ m * (1 + Polynomial.X) ^ m := by
 unfold gradeEnumerator;
 -- The first factor is `Fintype.card (ZMod 8) = 8`.
 have h_card : (Fintype.card (ZMod 8)) = 8 := by
 rfl;
 -- The second factor is `F = ∑ b : Fin m → ZMod 8, X ^ phaseGrade b`.
 have h_F : ∑ b : Fin m → ZMod 8, (Polynomial.X : Polynomial ℕ) ^ (phaseGrade b) = (∏ i : Fin m, (∑ c : ZMod 8, (Polynomial.X : Polynomial ℕ) ^ (if reduce8to2 c = 1 then 1 else 0))) := by
 rw [ Finset.prod_sum ];
 refine' Finset.sum_bij ( fun b _ => fun i _ => b i ) _ _ _ _ <;> simp +decide [ phaseGrade ];
 · simp +decide [ funext_iff ];
 · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
 · simp +decide [ Finset.prod_ite ];
 simp_all +decide [ Finset.sum_ite ];
 rw [ show ( Finset.filter ( fun x : ZMod 8 => reduce8to2 x = 1 ) Finset.univ : Finset ( ZMod 8 ) ) = { 1, 3, 5, 7 } by decide, show ( Finset.filter ( fun x : ZMod 8 => ¬reduce8to2 x = 1 ) Finset.univ : Finset ( ZMod 8 ) ) = { 0, 2, 4, 6 } by decide ] ; simp +decide [ mul_assoc, ← mul_pow ] ; ring;

/-- **Grade-refined logical-operator enumerator (interface theorem).**
Given the (literature-absent) bridge identifying the CSS logical-operator
enumerator of `BWCss(m, r₁, r₂)` with the phase-polynomial grade enumerator, the
enumerator factorises as the all-`m` Möbius/grade closed form
`8 · 4^m · (1 + X)^m = ∑_g 8·4^m·C(m,g) · X^g`. -/
theorem grade_refined_logical_enumerator (m r₁ r₂ : ℕ) (h : r₂ < r₁)
 (hcss : r₁ + r₂ ≤ m - 1)
 (logicalEnumerator : CSSCode → Polynomial ℕ)
 (hbridge : logicalEnumerator (CSSCode.ofRMPair m r₁ r₂ h hcss) = gradeEnumerator m) :
 logicalEnumerator (CSSCode.ofRMPair m r₁ r₂ h hcss)
 = 8 * 4 ^ m * (1 + Polynomial.X) ^ m := by
 rw [hbridge]; exact gradeEnumerator_closed_form m

end BWCss