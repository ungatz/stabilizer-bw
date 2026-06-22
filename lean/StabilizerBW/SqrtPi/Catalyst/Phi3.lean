import StabilizerBW.SqrtPi.Level2.Pi2
import StabilizerBW.SqrtPi.Clifford
import StabilizerBW.SqrtPi.OplusCost

/-!
# T3 — The catalytic embedding `Φ₃ : Π₃ → Π₂` and the grade-doubling verification

Following CHKRS SI Definition S12 (specialised to `k = 3 → 2`), the catalytic embedding doubles
objects (`n ↦ n + n`) and acts on generators by

* `Φ₃(id n) = id n ⊞ id n`,
* `Φ₃(σ_⊕) = σ_⊕ ⊞ σ_⊕`,
* `Φ₃(ζ₃)  = X ∘ (id ⊞ ζ₂)`   (the "X-conjugated" rule, with `ζ₂ = i`),
* `Φ₃(V)   = V ⊞ V`,
* `Φ₃(a ∘ b) = Φ₃(a) ∘ Φ₃(b)`,
* `Φ₃(a ⊕ b) = Φ₃(a) ⊞ Φ₃(b)` (regrouped, up to the `σ^⊗` coordinate permutation).

**Convention note.** The general functor `Phi3` below realises the `⊕` rule directly as
`Φ₃(a) ⊞ Φ₃(b)`; CHKRS S12 additionally conjugates by the tensor-swap `σ^⊗`, a grade-`0`
Clifford coordinate permutation that does **not** change the lattice grade.  We work with the
explicit images `phiT`, `phiS`, `phiV` of the three verification generators (single qubit, object
`2`), each a concrete `Π₂` morphism of object `4`.

## The kernel-computed result

The development conjectured the grade-doubling rule `Γ(g) = 2g`.  The kernel computation **refutes**
it on `T`: with the canonical level-2 grade (`λ₂`-adic, w.r.t. the level-2 Barnes–Wall lattice
`BW2L`),

* `grade₂(Φ₃ T) = 1`,  while  `2 · grade₃(T) = 2`  — **disagreement** (`Falsification_T3`);
* `grade₂(Φ₃ S) = 0 = 2 · grade₃(S)`,
* `grade₂(Φ₃ V) = 0 = 2 · grade₃(V)`.

The **corrected** rule, kernel-proved on all three generators, is `Γ(g) = g` (`Headline_T3`):
`Φ₃` *preserves* the lattice grade.  Mathematically: `Φ₃` doubles the `(1+i)`-adic content of a
phase (one `ζ₈` ↦ one `i`), but the ramification of the prime also doubles between level 3
(`(1+i) ~ λ₃²`) and level 2 (`(1+i) ~ λ₂`), so the two effects cancel and the grade is invariant.
-/

set_option maxRecDepth 4000

namespace Pi3

/-- The level-3 `T` gate `T = id₁ ⊕ ζ₃ = diag(1, ζ₈) : 2 → 2`. -/
def tGate : Pi3 2 2 := Pi3.idn 1 ⊞ Pi3.zet

/-- The level-3 `V` gate (just the generator `V`). -/
def vGate : Pi3 2 2 := Pi3.vv

end Pi3

namespace Pi2
open Pi3

/-- `Φ₃(ζ₃) = X ∘ (id₁ ⊕ ζ₂)` as a `Π₂` morphism `2 → 2`. -/
def phiZet : Pi2 2 2 := Pi2.swp ⊚₂ (Pi2.idn 1 ⊞₂ Pi2.zet)

/-- `Φ₃(T) = Φ₃(id₁) ⊞ Φ₃(ζ₃)` (object `4`). -/
def phiT : Pi2 4 4 := Pi2.opl (Pi2.idn 1 ⊞₂ Pi2.idn 1) phiZet

/-- `Φ₃(S) = Φ₃(id₁) ⊞ Φ₃(ζ₃²)` (object `4`). -/
def phiS : Pi2 4 4 := Pi2.opl (Pi2.idn 1 ⊞₂ Pi2.idn 1) (phiZet ⊚₂ phiZet)

/-- `Φ₃(V) = V ⊞ V` (object `4`). -/
def phiV : Pi2 4 4 := Pi2.vv ⊞₂ Pi2.vv

/-! ### The explicit denotation matrices -/

/-
`⟦Φ₃(T)⟧₂ = diag-block `I₂ ⊕ [[0,1],[i,0]]` (integral over `ℤ[i]`).
-/
lemma denote_phiT :
    Pi2.denote phiT =
      Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1],
                  ![0, 0, Q8.ofZ8 Z8.imag, 0]] := by
  convert congr_arg _ ?_;
  rotate_left;
  exact Pi2.opl ( Pi2.idn 1 ⊞₂ Pi2.idn 1 ) ( Pi2.swp ⊚₂ ( Pi2.idn 1 ⊞₂ Pi2.zet ) );
  · rfl;
  · decide +kernel

/-
`⟦Φ₃(S)⟧₂ = diag(1, 1, i, i)` (integral over `ℤ[i]`; no-`σ^⊗` convention).
-/
lemma denote_phiS :
    Pi2.denote phiS =
      Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, Q8.ofZ8 Z8.imag, 0],
                  ![0, 0, 0, Q8.ofZ8 Z8.imag]] := by
  convert congr_arg _ ?_
  rotate_left
  exact Pi2.opl (Pi2.idn 1 ⊞₂ Pi2.idn 1)
    ((Pi2.swp ⊚₂ (Pi2.idn 1 ⊞₂ Pi2.zet)) ⊚₂ (Pi2.swp ⊚₂ (Pi2.idn 1 ⊞₂ Pi2.zet)))
  · rfl
  · decide +kernel

end Pi2

/-! ### The three grade verifications -/

namespace Pi3
open Pi2 Pi3.Zi

/-- The integral (`ℤ[i]`) form of `⟦Φ₃(T)⟧₂`. -/
def NT : Matrix (Fin 4) (Fin 4) Zi :=
  Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![0, 0, Zi.imag, 0]]

/-- The integral (`ℤ[i]`) form of `⟦Φ₃(S)⟧₂`. -/
def NS : Matrix (Fin 4) (Fin 4) Zi :=
  Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, Zi.imag, 0], ![0, 0, 0, Zi.imag]]

lemma denote_phiT_map : Pi2.denote phiT = NT.map Zi.toQ8 := by
  rw [denote_phiT, NT]
  funext i j; fin_cases i <;> fin_cases j <;> rfl

lemma denote_phiS_map : Pi2.denote phiS = NS.map Zi.toQ8 := by
  rw [denote_phiS, NS]
  funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- **Level-2 grade of `Φ₃(T)` is `1`.** (Refuting `Γ(1) = 2`.) -/
theorem grade2_phiT : Pi2.grade2 phiT = 1 := by
  rw [Pi2.grade2, denote_phiT_map]
  have h := gradeWrt2_eq BW2L (NT.map Zi.toQ8) 1
    (pushesIn2_integral_of_mapsGen NT 1
      ((mem_BW2L_iff _).mpr (by decide)) ((mem_BW2L_iff _).mpr (by decide))
      ((mem_BW2L_iff _).mpr (by decide)) ((mem_BW2L_iff _).mpr (by decide)))
    (by
      intro k hk
      interval_cases k
      exact not_pushesIn2_integral_gen1 NT 0 (by rw [mem_BW2L_iff]; decide))
  simpa using h

/-- **Level-2 grade of `Φ₃(S)` is `0`.** -/
theorem grade2_phiS : Pi2.grade2 phiS = 0 := by
  rw [Pi2.grade2, denote_phiS_map]
  have h := gradeWrt2_eq BW2L (NS.map Zi.toQ8) 0
    (pushesIn2_integral_of_mapsGen NS 0
      ((mem_BW2L_iff _).mpr (by decide)) ((mem_BW2L_iff _).mpr (by decide))
      ((mem_BW2L_iff _).mpr (by decide)) ((mem_BW2L_iff _).mpr (by decide)))
    (by intro k hk; omega)
  simpa using h

/-- **Level-2 grade of `Φ₃(V)` is `0`.** The fractional generator `V = √X` (entries `(1±i)/2`)
still preserves the level-2 Barnes–Wall lattice. -/
theorem grade2_phiV : Pi2.grade2 phiV = 0 := by
  rw [Pi2.grade2]
  have h := gradeWrt2_eq BW2L (Pi2.denote phiV) 0
    (pushesIn2_of_gens (Pi2.denote phiV) 0
      ⟨![Zi.imag, -Zi.imag, Zi.imag, -Zi.imag], (mem_BW2L_iff _).mpr (by decide), by
        rw [pow_zero, one_smul]; funext i; fin_cases i <;> decide +kernel⟩
      ⟨![1, Zi.imag, 1, Zi.imag], (mem_BW2L_iff _).mpr (by decide), by
        rw [pow_zero, one_smul]; funext i; fin_cases i <;> decide +kernel⟩
      ⟨![0, 0, ⟨-1, 1⟩, ⟨1, -1⟩], (mem_BW2L_iff _).mpr (by decide), by
        rw [pow_zero, one_smul]; funext i; fin_cases i <;> decide +kernel⟩
      ⟨![0, 0, ⟨1, 1⟩, ⟨-1, 1⟩], (mem_BW2L_iff _).mpr (by decide), by
        rw [pow_zero, one_smul]; funext i; fin_cases i <;> decide +kernel⟩)
    (by intro k hk; omega)
  simpa using h

/-! ### The level-3 grades of the three generators -/

/-- `coeVec` (level-3 integral coercion) is injective. -/
lemma coeVec_injective {n : ℕ} {u v : Fin n → Z8} (h : coeVec u = coeVec v) : u = v := by
  funext i
  have := congrFun h i
  simp only [coeVec] at this
  exact Q8.ofZ8_injective this

/-- For an integral diagonal matrix, the `ℚ[ζ₈]`-level `pushesIn` reduces to the `ℤ[ζ₈]`-level
lattice-preservation condition. -/
lemma pushesIn_diag1_map_iff (A : Z8) (k : ℕ) :
    pushesIn L3 ((diag1 A).map Q8.ofZ8) k ↔
      (∀ v ∈ L3, Z8.lam ^ k • (diag1 A).mulVec v ∈ L3) := by
  have hpow : (Q8.ofZ8 Z8.lam) ^ k = Q8.ofZ8 (Z8.lam ^ k) := by
    rw [← Q8.ofZ8Hom_apply, ← map_pow]; rfl
  constructor
  · intro h v hv
    obtain ⟨w, hw, hwEq⟩ := h v hv
    rw [map_mulVec_coeVec, hpow, ← coeVec_smul] at hwEq
    rw [coeVec_injective hwEq]; exact hw
  · intro h v hv
    refine ⟨Z8.lam ^ k • (diag1 A).mulVec v, h v hv, ?_⟩
    rw [map_mulVec_coeVec, hpow, ← coeVec_smul]

/-- `grade₃(T) = 1`. -/
theorem grade3_T : grade2obj tGate = 1 := by
  have hden : denote tGate = (diag1 Z8.zeta).map Q8.ofZ8 := by
    funext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  unfold grade2obj
  rw [hden]
  apply gradeWrt_eq
  · rw [pushesIn_diag1_map_iff, mapsInto_diag1_iff]; decide
  · intro k hk
    interval_cases k
    rw [pushesIn_diag1_map_iff, mapsInto_diag1_iff]; decide

/-- `grade₃(S) = 0`. -/
theorem grade3_S : grade2obj sGate = 0 := grade2obj_sGate

/-- `grade₃(V) = 0`. -/
theorem grade3_V : grade2obj vGate = 0 := grade_V

/-! ### Headline and Falsification -/

/-- **Pi3.Falsification_T3.** The conjectured grade-doubling `Γ(g) = 2g` is FALSE:
on the `T` generator the level-2 grade of `Φ₃(T)` is `1`, whereas `2 · grade₃(T) = 2`. -/
theorem Falsification_T3 :
    Pi2.grade2 phiT = 1 ∧ Pi2.grade2 phiT ≠ 2 * grade2obj tGate := by
  refine ⟨grade2_phiT, ?_⟩
  rw [grade2_phiT, grade3_T]
  decide

/-- **Pi3.Headline_T3 (corrected rule `Γ(g) = g`).** The catalytic embedding `Φ₃` *preserves*
the lattice grade on all three verification generators `T, S, V`:
`grade₂(Φ₃ a) = grade₃ a`. -/
theorem Headline_T3 :
    Pi2.grade2 phiT = grade2obj tGate ∧
    Pi2.grade2 phiS = grade2obj sGate ∧
    Pi2.grade2 phiV = grade2obj vGate := by
  refine ⟨?_, ?_, ?_⟩
  · rw [grade2_phiT, grade3_T]
  · rw [grade2_phiS, grade3_S]
  · rw [grade2_phiV, grade3_V]

end Pi3