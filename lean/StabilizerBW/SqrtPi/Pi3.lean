import StabilizerBW.SqrtPi.Grade

/-!
# T1 — The graded free model `Π₃`: syntax, congruence, denotation, grade

We define the inductive type `Pi3 m n` of morphisms `m → n` of the free bipermutative
category at level `k = 3` (CHKRS SI Prop. S5), with constructors:

* `idn n`            — identity `n → n`;
* `swp`              — the additive symmetry `σ_⊕ : 2 → 2`;
* `zet`              — the phase generator `ζ₃ = ζ₈ : 1 → 1`;
* `vv`               — the square-root-of-swap generator `V : 2 → 2`;
* `cmp`              — composition;
* `opl`              — the additive monoidal product `⊕`.

The equational congruence `Cong` (`≈₃`) closes the three axioms (E1) `ζ₈⁸ = id`,
(E2) `V² = σ_⊕`, (E3) the `√Π` relation, under the categorical structural rules.

**Convention.** We use the *faithful CHKRS denotation* where an object `n` denotes the
coordinate space of dimension `n` (not `2ⁿ`): the structural strawman's `2ⁿ` reading conflicts with
`⟦ζ₃⟧ = ζ₈` being a `1×1` scalar matrix at object `1`. Thus
`⟦·⟧ : Pi3 m n → Matrix (Fin n) (Fin m) ℚ[ζ₈]`, a single qubit is the object `2`, and
the single-qubit lattice grade is taken with respect to `L₃ ⊆ (Fin 2 → ℤ[ζ₈])`.
-/

set_option maxRecDepth 4000

open Pi3

/-- Morphisms `m → n` of the free bipermutative category `Π₃` at level `k = 3`. -/
inductive Pi3 : ℕ → ℕ → Type
  | idn (n : ℕ) : Pi3 n n
  | swp : Pi3 2 2
  | zet : Pi3 1 1
  | vv : Pi3 2 2
  | cmp {m n p : ℕ} : Pi3 m n → Pi3 n p → Pi3 m p
  | opl {m n m' n' : ℕ} : Pi3 m n → Pi3 m' n' → Pi3 (m + m') (n + n')

namespace Pi3

open Z8

/-- Composition in `Π₃`. -/
infixr:70 " ⊚ " => Pi3.cmp
/-- Additive monoidal product `⊕` in `Π₃`. -/
infixr:65 " ⊞ " => Pi3.opl

/-- `ζ₈` composed `8` times, used to state axiom (E1). -/
def zetaPow8 : Pi3 1 1 := zet ⊚ zet ⊚ zet ⊚ zet ⊚ zet ⊚ zet ⊚ zet ⊚ zet

/-- The equational congruence `≈₃` of `Π₃`: the smallest congruence containing the
three defining axioms (E1), (E2), (E3). -/
inductive Cong : {m n : ℕ} → Pi3 m n → Pi3 m n → Prop
  | refl {m n} (a : Pi3 m n) : Cong a a
  | symm {m n} {a b : Pi3 m n} : Cong a b → Cong b a
  | trans {m n} {a b c : Pi3 m n} : Cong a b → Cong b c → Cong a c
  | cmp_congr {m n p} {a a' : Pi3 m n} {b b' : Pi3 n p} :
      Cong a a' → Cong b b' → Cong (a ⊚ b) (a' ⊚ b')
  | opl_congr {m n m' n'} {a a' : Pi3 m n} {b b' : Pi3 m' n'} :
      Cong a a' → Cong b b' → Cong (a ⊞ b) (a' ⊞ b')
  | id_cmp {m n} (a : Pi3 m n) : Cong (idn m ⊚ a) a
  | cmp_id {m n} (a : Pi3 m n) : Cong (a ⊚ idn n) a
  | cmp_assoc {m n p q} (a : Pi3 m n) (b : Pi3 n p) (c : Pi3 p q) :
      Cong ((a ⊚ b) ⊚ c) (a ⊚ (b ⊚ c))
  -- (E1): ζ₈⁸ = id
  | e1 : Cong zetaPow8 (idn 1)
  -- (E2): V² = σ_⊕
  | e2 : Cong (vv ⊚ vv) swp
  -- (E3): V ∘ S ∘ V = ω² · S ∘ V ∘ S  (the √Π relation, as a congruence axiom slot)
  | e3 : Cong (vv ⊚ (idn 1 ⊞ (zet ⊚ zet)) ⊚ vv)
             ((idn 1 ⊞ (zet ⊚ zet)) ⊚ vv ⊚ (idn 1 ⊞ (zet ⊚ zet)))

@[inherit_doc] infix:50 " ≈₃ " => Cong

/-! ### Denotation -/

/-- `ζ₈` as a `1×1` matrix over `ℚ[ζ₈]`. -/
def zetaMat : Matrix (Fin 1) (Fin 1) Q8 := Matrix.of ![![Q8.ofZ8 zeta]]

/-- The swap matrix `X = σ_⊕`. -/
def swapMat : Matrix (Fin 2) (Fin 2) Q8 := Matrix.of ![![0, 1], ![1, 0]]

/-- The `√X` matrix `V = (1/√2)·[[ζ, ζ⁷],[ζ⁷, ζ]]`. -/
def vMat : Matrix (Fin 2) (Fin 2) Q8 :=
  Q8.invSqrt2 • Matrix.of ![![Q8.ofZ8 zeta, Q8.ofZ8 ⟨0, 0, 0, -1⟩],
                           ![Q8.ofZ8 ⟨0, 0, 0, -1⟩, Q8.ofZ8 zeta]]

/-- Denotation `⟦·⟧ : Pi3 m n → Matrix (Fin n) (Fin m) ℚ[ζ₈]`. -/
def denote : {m n : ℕ} → Pi3 m n → Matrix (Fin n) (Fin m) Q8
  | _, _, .idn _ => 1
  | _, _, .swp => swapMat
  | _, _, .zet => zetaMat
  | _, _, .vv => vMat
  | _, _, .cmp a b => denote b * denote a
  | _, _, .opl a b =>
      (Matrix.fromBlocks (denote a) 0 0 (denote b)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm

@[simp] lemma denote_id (n : ℕ) : denote (Pi3.idn n) = 1 := rfl
@[simp] lemma denote_sigma : denote Pi3.swp = swapMat := rfl
@[simp] lemma denote_zeta3 : denote Pi3.zet = zetaMat := rfl
@[simp] lemma denote_V : denote Pi3.vv = vMat := rfl
@[simp] lemma denote_circ {m n p : ℕ} (a : Pi3 m n) (b : Pi3 n p) :
    denote (a ⊚ b) = denote b * denote a := rfl
lemma denote_oplus {m n m' n' : ℕ} (a : Pi3 m n) (b : Pi3 m' n') :
    denote (a ⊞ b) = (Matrix.fromBlocks (denote a) 0 0 (denote b)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := rfl

/-! ### Lattices and grade -/

/-- The full integral lattice at object `1` (`ℤ[ζ₈] ⊆ ℚ[ζ₈]`). -/
def L1 : Submodule Z8 (Fin 1 → Z8) := ⊤

/-- The grade of a `1 → 1` morphism (object `1`, full lattice `L₁`). -/
noncomputable def grade1obj (a : Pi3 1 1) : ℕ∞ := gradeWrt L1 (denote a)

/-- The grade of a `2 → 2` morphism (single qubit, lattice `L₃`). -/
noncomputable def grade2obj (a : Pi3 2 2) : ℕ∞ := gradeWrt L3 (denote a)

/-! ### Supporting grade lemmas (T1) -/

/-- `g(id) = 0` for the identity at object `n`. -/
lemma grade_id (n : ℕ) (L : Submodule Z8 (Fin n → Z8)) : gradeWrt L (denote (Pi3.idn n)) = 0 := by
  rw [denote_id]; exact gradeWrt_id L

/-- `g(a ∘ b) ≤ g(b) + g(a)` (subadditivity) at object `n`. -/
lemma grade_mul {n : ℕ} (L : Submodule Z8 (Fin n → Z8)) (a b : Pi3 n n) :
    gradeWrt L (denote (a ⊚ b)) ≤ gradeWrt L (denote b) + gradeWrt L (denote a) := by
  rw [denote_circ]; exact gradeWrt_mul L (denote b) (denote a)

/-- `g(ζ₃) = 0`: the bare scalar `ζ₈·I` is grade `0`. -/
lemma grade_zeta3 : grade1obj Pi3.zet = 0 := by
  unfold grade1obj
  have h0 : pushesIn L1 (denote Pi3.zet) 0 := by
    intro v _
    refine ⟨fun i => zeta * v i, Submodule.mem_top, ?_⟩
    funext i
    fin_cases i
    simp only [denote_zeta3, zetaMat, pow_zero, one_smul, Matrix.mulVec, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      coeVec_apply, dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    rw [← Q8.ofZ8Hom_apply, ← Q8.ofZ8Hom_apply, ← Q8.ofZ8Hom_apply, map_mul]
    rfl
  have : gradeWrt L1 (denote Pi3.zet) ≤ 0 := by simpa using gradeWrt_le_of_pushesIn h0
  exact le_antisymm this (by positivity)

/-- The integral matrix `√2·V = [[ζ, ζ⁷],[ζ⁷, ζ]]` over `ℤ[ζ₈]` (with `ζ⁷ = -ζ³`). -/
def WintMat : Matrix (Fin 2) (Fin 2) Z8 :=
  Matrix.of ![![zeta, ⟨0, 0, 0, -1⟩], ![⟨0, 0, 0, -1⟩, zeta]]

/-- `√2 = ζ - ζ³ ∈ ℤ[ζ₈]`. -/
def sqrt2Z8 : Z8 := ⟨0, 1, 0, -1⟩

lemma ofZ8_sqrt2Z8 : Q8.ofZ8 sqrt2Z8 = Q8.sqrt2 := rfl

/-- `V = (1/√2)·(√2·V)`, with the integral part coerced from `ℤ[ζ₈]`. -/
lemma vMat_eq : vMat = Q8.invSqrt2 • WintMat.map Q8.ofZ8 := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Coercion commutes with scalar multiplication on vectors. -/
lemma coeVec_smul {n : ℕ} (c : Z8) (w : Fin n → Z8) :
    coeVec (c • w) = Q8.ofZ8 c • coeVec w := by
  funext i
  simp only [coeVec_apply, Pi.smul_apply, smul_eq_mul, ← Q8.ofZ8Hom_apply, map_mul]

/-- Coercion commutes with `mulVec` for the coerced matrix. -/
lemma map_mulVec_coeVec (M : Matrix (Fin 2) (Fin 2) Z8) (v : Fin 2 → Z8) :
    (M.map Q8.ofZ8).mulVec (coeVec v) = coeVec (M.mulVec v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, coeVec_apply, Fin.sum_univ_two,
    ← Q8.ofZ8Hom_apply, ← map_mul, ← map_add]

/-- The two entries of `(√2·V)·v`. -/
lemma WintMat_mulVec (v : Fin 2 → Z8) :
    WintMat.mulVec v = ![zeta * v 0 + (⟨0, 0, 0, -1⟩ : Z8) * v 1,
                         (⟨0, 0, 0, -1⟩ : Z8) * v 0 + zeta * v 1] := by
  funext i
  fin_cases i <;> simp [WintMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Helper: `√2·V` entry-0 identity. -/
lemma Wint_entry0 (v : Fin 2 → Z8) (c : Z8) (hc : v 0 + v 1 = onePlusI * c) :
    zeta * v 0 + (⟨0, 0, 0, -1⟩ : Z8) * v 1 = sqrt2Z8 * (v 0 * imag + c) := by
  have hc' : v 1 = onePlusI * c - v 0 := by linear_combination hc
  rw [hc']
  ext <;> simp only [sqrt2Z8, zeta, imag, onePlusI, Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d,
    Z8.add_a, Z8.add_b, Z8.add_c, Z8.add_d,
    Z8.sub_a, Z8.sub_b, Z8.sub_c, Z8.sub_d] <;> ring

/-- Helper: `√2·V` entry-1 identity. -/
lemma Wint_entry1 (v : Fin 2 → Z8) (c : Z8) (hc : v 0 + v 1 = onePlusI * c) :
    (⟨0, 0, 0, -1⟩ : Z8) * v 0 + zeta * v 1 = sqrt2Z8 * (-(v 0 * imag) + c * imag) := by
  have hc' : v 1 = onePlusI * c - v 0 := by linear_combination hc
  rw [hc']
  ext <;> simp only [sqrt2Z8, zeta, imag, onePlusI, Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d,
    Z8.add_a, Z8.add_b, Z8.add_c, Z8.add_d, Z8.neg_a, Z8.neg_b, Z8.neg_c, Z8.neg_d,
    Z8.sub_a, Z8.sub_b, Z8.sub_c, Z8.sub_d] <;> ring

/-- The integral `√2`-cancellation: `(√2·V)·v = √2·w` for the explicit integral `w ∈ L₃`. -/
lemma Wint_mulVec_eq (v : Fin 2 → Z8) (c : Z8) (hc : v 0 + v 1 = onePlusI * c) :
    WintMat.mulVec v = sqrt2Z8 • (![v 0 * imag + c, -(v 0 * imag) + c * imag] : Fin 2 → Z8) := by
  rw [WintMat_mulVec]
  funext i
  fin_cases i
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact Wint_entry0 v c hc
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact Wint_entry1 v c hc

/-- `g(V) = 0`: the square-root-of-swap is a grade-`0` (Clifford) operator. -/
lemma grade_V : grade2obj Pi3.vv = 0 := by
  unfold grade2obj
  rw [denote_V]
  refine le_antisymm (gradeWrt_le_of_pushesIn (k := 0) ?_) (by positivity)
  intro v hv
  rw [mem_L3] at hv
  obtain ⟨c, hc⟩ := hv
  refine ⟨![v 0 * imag + c, -(v 0 * imag) + c * imag], ?_, ?_⟩
  · rw [mem_L3]
    refine ⟨c, ?_⟩
    show v 0 * imag + c + (-(v 0 * imag) + c * imag) = onePlusI * c
    have h1 : v 0 * imag + c + (-(v 0 * imag) + c * imag) = c * (1 + imag) := by ring
    rw [h1, show (1 : Z8) + imag = onePlusI from by decide, mul_comm]
  · rw [pow_zero, one_smul, vMat_eq, Matrix.smul_mulVec, map_mulVec_coeVec,
      Wint_mulVec_eq v c hc, coeVec_smul, ofZ8_sqrt2Z8, smul_smul, Q8.invSqrt2_mul_sqrt2,
      one_smul]

/-- **T1 (Headline).** The graded `Π₃` infrastructure: identities are grade `0`, the grade is
subadditive under composition, the bare phase generator `ζ₃` is grade `0`, and the
square-root-of-swap `V` is grade `0` (Clifford). -/
theorem Headline_T1 :
    (∀ (n : ℕ) (L : Submodule Z8 (Fin n → Z8)), gradeWrt L (denote (Pi3.idn n)) = 0) ∧
    (∀ (n : ℕ) (L : Submodule Z8 (Fin n → Z8)) (a b : Pi3 n n),
        gradeWrt L (denote (a ⊚ b)) ≤ gradeWrt L (denote b) + gradeWrt L (denote a)) ∧
    grade1obj Pi3.zet = 0 ∧ grade2obj Pi3.vv = 0 :=
  ⟨grade_id, fun _ L a b => grade_mul L a b, grade_zeta3, grade_V⟩

end Pi3
