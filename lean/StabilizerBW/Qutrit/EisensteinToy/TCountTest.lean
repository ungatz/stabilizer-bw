import StabilizerBW.Qutrit.EisensteinToy.BW3

/-!
# T6 — TEST 3: the qutrit T-gate vs the Eisenstein grade

The qubit story is clean *because the T-gate phase lives in the base ring*: `T = diag(1, ζ₈)`
with `ζ₈ ∈ ℤ[ζ₈]`, the very ring the Barnes–Wall lattice is built over.  The literature qutrit
T-gate (Howard–Vala 2012) is `T₃ = diag(1, ζ₉^{a}, ζ₉^{b})` whose phases are **9th roots of
unity** `ζ₉`.

The diagnostic question for TEST 3 is whether the analogous statement "`grade(T₃) = T_count(T₃)`"
even *makes sense* over the Eisenstein integers `ℤ[ω] = ℤ[ζ₃]`.  It does not, and the reason is
structural:

  **There is no primitive 9th root of unity in `ℤ[ω]`** (`no_isPrimitiveRoot_nine`).

Indeed the only roots of unity in `ℤ[ω]` are the six sixth-roots `{±1, ±ω, ±ω²}` (all of
norm `1`), so every root of unity `z` satisfies `z⁶ = 1`; a primitive 9th root would need order
`9 ∤ 6`.  Hence the Howard–Vala phase `ζ₉ ∉ ℤ[ω]`, and the qutrit T-gate is **not representable**
as a diagonal operator over the Eisenstein lattice of `BW3.lean` — unlike the qubit case.

**Conclusion: TEST 3 fails structurally.**  This pins down a genuinely `ℤ[ζ₈]`-specific
coincidence of the qubit chapter: the T-gate phase being an algebraic integer of the *base*
cyclotomic ring.  At `d = 3` the Clifford+T cyclotomic level (`ℤ[ζ₉]`) strictly exceeds the
Eisenstein level (`ℤ[ζ₃]`).

We also record the positive content that *is* representable over `ℤ[ω]`:
* `gradeEMat_diag_omega : grade(diag(1, ω)) = 0`  (the order-3 phase is an Eisenstein integer),
* `gradeEMat_diag_negOne : grade(diag(1, -1)) = 1`.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritEis
open Eis

/-! ## The roots of unity of `ℤ[ω]` are the six sixth-roots -/

/-- The norm is multiplicative across powers: `N(zⁿ) = (N z)ⁿ`. -/
theorem norm_pow (z : Eis) (n : ℕ) : Eis.norm (z ^ n) = (Eis.norm z) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, norm_mul, ih]

/-- An element of norm `1` is one of the six sixth-roots of unity. -/
theorem norm_one_cases {z : Eis} (h : Eis.norm z = 1) :
    z = ⟨1, 0⟩ ∨ z = ⟨-1, 0⟩ ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ ∨ z = ⟨1, 1⟩ ∨ z = ⟨-1, -1⟩ := by
  obtain ⟨z1, z2⟩ := z
  have hb : z2 ^ 2 ≤ 1 := by simp only [Eis.norm] at h; nlinarith [sq_nonneg (2 * z1 - z2)]
  have ha : z1 ^ 2 ≤ 1 := by simp only [Eis.norm] at h; nlinarith [sq_nonneg (2 * z2 - z1)]
  have hb1 : -1 ≤ z2 := by nlinarith
  have hb2 : z2 ≤ 1 := by nlinarith
  have ha1 : -1 ≤ z1 := by nlinarith
  have ha2 : z1 ≤ 1 := by nlinarith
  simp only [Eis.norm] at h
  interval_cases z1 <;> interval_cases z2 <;> simp_all

/-- Every norm-`1` element is a sixth root of unity. -/
theorem norm_one_pow_six {z : Eis} (h : Eis.norm z = 1) : z ^ 6 = 1 := by
  rcases norm_one_cases h with h | h | h | h | h | h <;> subst h <;> decide

/-- **No primitive 9th root of unity in `ℤ[ω]`:** any `z` with `z⁹ = 1` already satisfies
`z³ = 1`. -/
theorem ninth_root_is_cube_root (z : Eis) (h9 : z ^ 9 = 1) : z ^ 3 = 1 := by
  -- Eis.norm z = 1
  have hn : Eis.norm z = 1 := by
    have hp : (Eis.norm z) ^ 9 = 1 := by rw [← norm_pow, h9, norm_one]
    have hnn : 0 ≤ Eis.norm z := norm_nonneg z
    have hdvd : Eis.norm z ∣ 1 := ⟨(Eis.norm z) ^ 8, by rw [← pow_succ']; exact hp.symm⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h1 | h1 <;> omega
  have h6 : z ^ 6 = 1 := norm_one_pow_six hn
  have e : z ^ 9 = z ^ 6 * z ^ 3 := by ring
  rw [h6, one_mul] at e
  rw [← e, h9]

/-- **TEST 3 structural failure (headline).** There is no primitive 9th root of unity in
`ℤ[ω]`; hence the Howard–Vala qutrit T-gate phase `ζ₉` is not an Eisenstein integer, and the
qutrit T-gate is not representable over the `BW3` Eisenstein lattice. -/
theorem no_isPrimitiveRoot_nine : ¬ ∃ z : Eis, IsPrimitiveRoot z 9 := by
  rintro ⟨z, hz⟩
  have h9 : z ^ 9 = 1 := hz.pow_eq_one
  have h3 : z ^ 3 = 1 := ninth_root_is_cube_root z h9
  have hdvd : (9 : ℕ) ∣ 3 := hz.dvd_of_pow_eq_one 3 h3
  omega

/-! ## The representable (Eisenstein) phases and their grades -/

/-- The order-3 phase `ω` *is* an Eisenstein integer, and `diag(1, ω)` is grade `0`. -/
theorem T3_omega_grade : gradeEMat diagOmega = 0 := gradeEMat_diag_omega

/-- `diag(1, -1)` is grade `1` over the Eisenstein lattice. -/
theorem T3_negOne_grade : gradeEMat diagNegOne = 1 := gradeEMat_diag_negOne

end QutritEis
