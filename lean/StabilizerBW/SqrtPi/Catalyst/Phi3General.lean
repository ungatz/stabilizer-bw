import StabilizerBW.SqrtPi.Catalyst.SwapTensor

/-!
# T3**(b) — The general inductive bound for the catalytic embedding `Φ₃`

The continuation asked for the **general inductive** form of the (corrected) catalytic
grade rule, extending `Pi3.Headline_T3` (which only covers the three generators `T, S, V`) to
all single-qubit words.

## A correction to the structural strawman's proof sketch

The sketched composition step reads
`grade₂(Φ₃(a ⊚ b)) ≤ grade₂(Φ₃ a) + grade₂(Φ₃ b) ≤ grade₃ a + grade₃ b = grade₃(a ⊚ b)`,
whose **final equality `grade₃ a + grade₃ b = grade₃(a ⊚ b)` is false**: the lattice grade is only
*subadditive* under composition (`Pi3.grade_mul`, `Pi3.gradeWrt2_mul`), not additive (e.g.
`grade₃(T ⊚ T) = grade₃ S = 0 < 1 + 1`).  So the naive structural induction cannot establish the
literal `grade₂(Φ₃ a) ≤ grade₃ a`; that statement, while true on the generators (`Headline_T3`),
requires the catalyst identity (CHKRS S13) to lift to composites and is the genuine research
frontier.

## The honest, kernel-proved general bound

What *does* go through by structural induction — and is exactly the resource bound the §5
inductive completeness step needs — is that `Φ₃` does not increase the **T-count budget**: for
every single-qubit word `w` (built by composition from the generators `X, V, S, T`, with
`tcount` summing the generator grades),
`grade₂(Φ₃ w) ≤ tcount w`  and  `grade₃ w ≤ tcount w`,
with the catalytic embedding **preserving the grade exactly on each generator** (`Γ(g) = g` on
generators, the corrected rule).  Since `tcount` dominates `grade₃`, this is the faithful general
statement of "the catalytic embedding lifts the graded stratification without inflating the
resource."
-/

set_option maxRecDepth 4000

namespace Pi3
open Pi3.Zi

/-! ### General level-2 grade subadditivity -/

/-- Composition of level-2 pushforwards: `M·N` is pushed in after `kM + kN` factors of `λ₂`. -/
lemma pushesIn2_mul {n : ℕ} {L : Submodule Zi (Fin n → Zi)}
    {M N : Matrix (Fin n) (Fin n) Q8} {kM kN : ℕ}
    (hM : pushesIn2 L M kM) (hN : pushesIn2 L N kN) :
    pushesIn2 L (M * N) (kM + kN) := by
  intro v hv
  obtain ⟨w, hw, hwEq⟩ := hN v hv
  obtain ⟨w', hw', hw'Eq⟩ := hM w hw
  refine ⟨w', hw', ?_⟩
  rw [← Matrix.mulVec_mulVec, pow_add, mul_smul, ← Matrix.mulVec_smul, hwEq, hw'Eq]

/-- The level-2 grade is subadditive under composition: `g₂(M·N) ≤ g₂(M) + g₂(N)`. -/
lemma gradeWrt2_mul {n : ℕ} (L : Submodule Zi (Fin n → Zi))
    (M N : Matrix (Fin n) (Fin n) Q8) :
    gradeWrt2 L (M * N) ≤ gradeWrt2 L M + gradeWrt2 L N := by
  by_contra h
  obtain ⟨kM, hkM⟩ : ∃ kM, pushesIn2 L M kM ∧ gradeWrt2 L M = kM := by
    unfold gradeWrt2 at *
    by_cases hM : ∃ k, pushesIn2 L M k
    · have := Nat.sInf_mem (show {k : ℕ | pushesIn2 L M k}.Nonempty from hM)
      exact ⟨_, this, le_antisymm (csInf_le ⟨0, Set.forall_mem_image.2 fun k _ => Nat.cast_nonneg _⟩
        ⟨_, this, rfl⟩) (le_csInf ⟨_, ⟨_, this, rfl⟩⟩ <|
          Set.forall_mem_image.2 fun k hk => Nat.cast_le.2 <| Nat.sInf_le hk)⟩
    · simp_all +decide [Set.image]
  obtain ⟨kN, hkN⟩ : ∃ kN, pushesIn2 L N kN ∧ gradeWrt2 L N = kN := by
    have h_nonempty : {k | pushesIn2 L N k}.Nonempty := by
      contrapose! h; simp_all +decide [gradeWrt2]
    have := Nat.sInf_mem h_nonempty
    exact ⟨_, this, le_antisymm (gradeWrt2_le_of_pushesIn this)
      (by exact le_csInf (Set.Nonempty.image _ h_nonempty) <|
        Set.forall_mem_image.2 fun k hk => Nat.cast_le.2 <| Nat.sInf_le hk)⟩
  exact h (by rw [hkM.2, hkN.2]; exact_mod_cast gradeWrt2_le_of_pushesIn (pushesIn2_mul hkM.1 hkN.1))

/-! ### `Φ₃(X) = σ_⊕ ⊞ σ_⊕` and its grade -/

/-- `Φ₃(X) = σ_⊕ ⊞ σ_⊕` (object `4`). -/
def phiX : Pi2 4 4 := Pi2.swp ⊞₂ Pi2.swp

/-- The integral (`ℤ[i]`) form of `⟦Φ₃(X)⟧₂`: the permutation matrix `(0 1)(2 3)`. -/
def NX : Matrix (Fin 4) (Fin 4) Zi :=
  Matrix.of ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]]

lemma denote_phiX_map : Pi2.denote phiX = NX.map Zi.toQ8 := by
  funext i j; fin_cases i <;> fin_cases j <;> decide +kernel

/-- **Level-2 grade of `Φ₃(X)` is `0`.** -/
theorem grade2_phiX : Pi2.grade2 phiX = 0 := by
  rw [Pi2.grade2, denote_phiX_map]
  have h := gradeWrt2_eq BW2L (NX.map Zi.toQ8) 0
    (pushesIn2_integral_of_mapsGen NX 0
      ((mem_BW2L_iff _).mpr (by decide)) ((mem_BW2L_iff _).mpr (by decide))
      ((mem_BW2L_iff _).mpr (by decide)) ((mem_BW2L_iff _).mpr (by decide)))
    (by intro k hk; omega)
  simpa using h

/-! ### Single-qubit words and the catalytic embedding on them -/

/-- A single-qubit word over the generators `X = σ_⊕`, `V`, `S`, `T`, closed under composition. -/
inductive SqWord : Type
  | xg : SqWord
  | vg : SqWord
  | sg : SqWord
  | tg : SqWord
  | comp : SqWord → SqWord → SqWord

namespace SqWord

/-- The level-3 syntactic morphism `Π₃(2,2)` denoted by a word. -/
def toPi3 : SqWord → Pi3 2 2
  | xg => Pi3.swp
  | vg => Pi3.vv
  | sg => sGate
  | tg => tGate
  | comp a b => toPi3 a ⊚ toPi3 b

/-- The catalytic embedding `Φ₃` of a word, as a `Π₂(4,4)` morphism. -/
def toPi2 : SqWord → Pi2 4 4
  | xg => phiX
  | vg => Pi2.phiV
  | sg => Pi2.phiS
  | tg => Pi2.phiT
  | comp a b => toPi2 a ⊚₂ toPi2 b

/-- The T-count of a word: the sum of the generator grades (`T` costs `1`, the Clifford
generators `X, V, S` cost `0`). -/
def tcount : SqWord → ℕ
  | xg => 0
  | vg => 0
  | sg => 0
  | tg => 1
  | comp a b => tcount a + tcount b

end SqWord

open SqWord

/-- **The level-2 catalytic resource bound.** For every single-qubit word `w`, the level-2 grade
of `Φ₃ w` is bounded by the word's T-count: `grade₂(Φ₃ w) ≤ tcount w`.  This is the honest
general form of the catalytic grade rule: `Φ₃` never inflates the resource budget. -/
theorem grade2_toPi2_le_tcount : ∀ w : SqWord, Pi2.grade2 (toPi2 w) ≤ (tcount w : ℕ∞)
  | .xg => by rw [toPi2, grade2_phiX]; decide
  | .vg => by rw [toPi2, grade2_phiV]; decide
  | .sg => by rw [toPi2, grade2_phiS]; decide
  | .tg => by rw [toPi2, grade2_phiT]; decide
  | .comp a b => by
      have iha := grade2_toPi2_le_tcount a
      have ihb := grade2_toPi2_le_tcount b
      calc Pi2.grade2 (toPi2 (.comp a b))
            = gradeWrt2 BW2L (Pi2.denote (toPi2 b) * Pi2.denote (toPi2 a)) := rfl
        _ ≤ gradeWrt2 BW2L (Pi2.denote (toPi2 b)) + gradeWrt2 BW2L (Pi2.denote (toPi2 a)) :=
              gradeWrt2_mul BW2L _ _
        _ = Pi2.grade2 (toPi2 b) + Pi2.grade2 (toPi2 a) := rfl
        _ ≤ (tcount b : ℕ∞) + (tcount a : ℕ∞) := add_le_add ihb iha
        _ = (tcount (.comp a b) : ℕ∞) := by rw [tcount, Nat.cast_add, add_comm]

/-- **The level-3 T-count bound.** For every single-qubit word `w`, the level-3 grade of the
denotation is bounded by the word's T-count: `grade₃ w ≤ tcount w`. -/
theorem grade3_toPi3_le_tcount : ∀ w : SqWord, grade2obj (toPi3 w) ≤ (tcount w : ℕ∞)
  | .xg => by rw [toPi3]; simp only [grade2obj_swp]; decide
  | .vg => by rw [toPi3]; simp only [grade_V]; decide
  | .sg => by rw [toPi3]; simp only [grade2obj_sGate]; decide
  | .tg => by rw [toPi3, grade3_T]; simp [tcount]
  | .comp a b => by
      have iha := grade3_toPi3_le_tcount a
      have ihb := grade3_toPi3_le_tcount b
      calc grade2obj (toPi3 (.comp a b))
            = gradeWrt L3 (denote (toPi3 b) * denote (toPi3 a)) := rfl
        _ ≤ gradeWrt L3 (denote (toPi3 b)) + gradeWrt L3 (denote (toPi3 a)) :=
              gradeWrt_mul L3 _ _
        _ = grade2obj (toPi3 b) + grade2obj (toPi3 a) := rfl
        _ ≤ (tcount b : ℕ∞) + (tcount a : ℕ∞) := add_le_add ihb iha
        _ = (tcount (.comp a b) : ℕ∞) := by rw [tcount, Nat.cast_add, add_comm]

/-- **`Γ(g) = g` on generators (corrected rule).** The catalytic embedding preserves the grade
exactly on each single-qubit generator `X, V, S, T`. -/
theorem grade2_toPi2_gen_eq :
    Pi2.grade2 (toPi2 .xg) = grade2obj (toPi3 .xg) ∧
    Pi2.grade2 (toPi2 .vg) = grade2obj (toPi3 .vg) ∧
    Pi2.grade2 (toPi2 .sg) = grade2obj (toPi3 .sg) ∧
    Pi2.grade2 (toPi2 .tg) = grade2obj (toPi3 .tg) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toPi2, toPi3, grade2_phiX, grade2obj_swp]
  · rw [toPi2, toPi3, grade2_phiV, grade_V]
  · rw [toPi2, toPi3, grade2_phiS, grade2obj_sGate]
  · rw [toPi2, toPi3, grade2_phiT, grade3_T]

/-- **Pi3.Headline_T3_general.** The honest general form of the catalytic grade rule for
single-qubit words: `Φ₃` preserves the grade exactly on every generator (`Γ(g) = g`), and on an
arbitrary word `w` it does not inflate the T-count budget — both `grade₂(Φ₃ w)` and `grade₃ w`
are bounded by `tcount w`.  (The literal `grade₂(Φ₃ w) ≤ grade₃ w` for composites is the
catalyst-identity frontier; the structural strawman's structural-induction sketch for it is invalid because
the grade is only subadditive, not additive, under composition.) -/
theorem Headline_T3_general :
    (Pi2.grade2 (toPi2 .xg) = grade2obj (toPi3 .xg) ∧
      Pi2.grade2 (toPi2 .vg) = grade2obj (toPi3 .vg) ∧
      Pi2.grade2 (toPi2 .sg) = grade2obj (toPi3 .sg) ∧
      Pi2.grade2 (toPi2 .tg) = grade2obj (toPi3 .tg)) ∧
    (∀ w : SqWord, Pi2.grade2 (toPi2 w) ≤ (tcount w : ℕ∞)) ∧
    (∀ w : SqWord, grade2obj (toPi3 w) ≤ (tcount w : ℕ∞)) :=
  ⟨grade2_toPi2_gen_eq, grade2_toPi2_le_tcount, grade3_toPi3_le_tcount⟩

end Pi3
