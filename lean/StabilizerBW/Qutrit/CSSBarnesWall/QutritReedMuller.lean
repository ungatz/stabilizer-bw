import Mathlib

/-!
# T1 — Qutrit Reed–Muller codes `QRM(m, r)` over `𝔽₃`

The genuine qutrit-CSS Barnes–Wall lattice is built from a pair of **qutrit
Reed–Muller codes** over `𝔽₃ = ZMod 3`, the `q = 3` specialisation of the
Ashikhmin–Knill qudit RM family (AK 2001 §III) and the `q`-ary generalisation of
the chapter's binary `RM(r, m)` (`StabilizerBW.BWCss/ReedMuller.lean`).

We work in the **evaluation-point model** `QFun m := (Fin m → 𝔽₃) → 𝔽₃`, whose
`𝔽₃`-dimension is `3 ^ m = Fintype.card (Fin m → 𝔽₃)` (this is the CSS block
length `n`).  `QRM r m` is the span of the *reduced* monomials
`χ_e(x) = ∏ i, x i ^ (e i)`, `e : Fin m → Fin 3` (per-variable exponents
`0, 1, 2`, since `x³ = x` over `𝔽₃`), of total degree `∑ i, e i ≤ r`.

The single fact the CSS construction needs is the **orthogonality** of low-degree
monomial pairs under the evaluation pairing `⟨f, g⟩ = ∑ x, f x · g x`:

  `⟨χ_e, χ_f⟩ = ∏ i, (∑ t : 𝔽₃, t ^ (e i + f i))`,

and the per-coordinate sum `∑ t : 𝔽₃, t ^ k` vanishes whenever `k ≤ 1`.  Hence if
`deg e + deg f < 2 m` some coordinate has `e i + f i ≤ 1` and the pairing
vanishes.  This is the `q = 3` instance of the standard RM duality
`RM_q(r,m)^⊥ = RM_q(m(q−1)−1−r, m)`; with `q = 3` the duality partner of
`QRM(s)` is `QRM(2m−1−s)`, and orthogonality gives the CSS inclusion
`QRM(r₂) ⊆ QRM(s)^⊥` whenever `r₂ + s ≤ 2m − 1`.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

open scoped BigOperators
open Classical

namespace QutritCSSBarnesWall

/-- The qutrit evaluation-point model `𝔽₃^m → 𝔽₃`, of dimension `3 ^ m`. -/
abbrev QFun (m : ℕ) := (Fin m → ZMod 3) → ZMod 3

/-- A reduced monomial exponent vector: `e i ∈ {0, 1, 2}` for each variable. -/
abbrev Exp (m : ℕ) := Fin m → Fin 3

/-- The reduced monomial `χ_e(x) = ∏ i, x i ^ (e i)`. -/
def qmono {m : ℕ} (e : Exp m) : QFun m := fun x => ∏ i, (x i) ^ (e i : ℕ)

/-- Total degree of a reduced monomial. -/
def qdeg {m : ℕ} (e : Exp m) : ℕ := ∑ i, (e i : ℕ)

/-- The order-`r` qutrit Reed–Muller code in the evaluation-point model: the span
of the reduced monomials of total degree `≤ r`. -/
def QRM (r m : ℕ) : Submodule (ZMod 3) (QFun m) :=
  Submodule.span (ZMod 3) (qmono '' {e : Exp m | qdeg e ≤ r})

/-- Definitional unfolding of `QRM` (for rewriting). -/
theorem QRM_eq (r m : ℕ) :
    QRM r m = Submodule.span (ZMod 3) (qmono '' {e : Exp m | qdeg e ≤ r}) := rfl

/-! ## Monotonicity -/

theorem QRM_mono {r r' m : ℕ} (h : r ≤ r') : QRM r m ≤ QRM r' m := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro e he
  exact le_trans he h

/-! ## The evaluation pairing and the dual code -/

/-- The evaluation pairing `⟨f, g⟩ = ∑ x, f x · g x` on `QFun m`. -/
def qdot {m : ℕ} (f g : QFun m) : ZMod 3 := ∑ x, f x * g x

/-- The dual code of `C` under the evaluation pairing. -/
def dualQ {m : ℕ} (C : Submodule (ZMod 3) (QFun m)) : Submodule (ZMod 3) (QFun m) where
  carrier := {f | ∀ g ∈ C, qdot f g = 0}
  add_mem' {a b} ha hb := by
    intro g hg
    have ha' := ha g hg; have hb' := hb g hg
    simp only [qdot, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
    rw [ha', hb', add_zero]
  zero_mem' := by intro g hg; simp [qdot]
  smul_mem' c a ha := by
    intro g hg
    have ha' := ha g hg
    simp only [qdot, Pi.smul_apply, smul_eq_mul] at *
    rw [show (∑ x, c * a x * g x) = c * ∑ x, a x * g x by
      rw [Finset.mul_sum]; congr 1; ext x; ring, ha', mul_zero]

/-! ## The per-coordinate sum and the orthogonality of monomials -/

/-- The per-coordinate power sum `∑ t : 𝔽₃, t ^ k` vanishes for `k ≤ 1`. -/
theorem zmod3_powsum_eq_zero_of_le_one {k : ℕ} (hk : k ≤ 1) :
    (∑ t : ZMod 3, t ^ k) = 0 := by
  interval_cases k <;> decide

/-- The evaluation pairing of two reduced monomials factorises coordinate-wise:
`⟨χ_e, χ_f⟩ = ∏ i, (∑ t : 𝔽₃, t ^ (e i + f i))`. -/
theorem qdot_qmono {m : ℕ} (e f : Exp m) :
    qdot (qmono e) (qmono f) = ∏ i, (∑ t : ZMod 3, t ^ ((e i : ℕ) + (f i : ℕ))) := by
  unfold qdot qmono
  have : ∀ x : Fin m → ZMod 3,
      (∏ i, (x i) ^ (e i : ℕ)) * (∏ i, (x i) ^ (f i : ℕ))
        = ∏ i, (x i) ^ ((e i : ℕ) + (f i : ℕ)) := by
    intro x; rw [← Finset.prod_mul_distrib]; congr 1; ext i; rw [pow_add]
  simp_rw [this]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **Monomial orthogonality.** If `deg e + deg f < 2 m` then the monomials are
orthogonal under the evaluation pairing. -/
theorem qmono_orthogonal {m : ℕ} {e f : Exp m} (h : qdeg e + qdeg f < 2 * m) :
    qdot (qmono e) (qmono f) = 0 := by
  rw [qdot_qmono]
  -- some coordinate `i` has `e i + f i ≤ 1`
  have hex : ∃ i, (e i : ℕ) + (f i : ℕ) ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hge : ∀ i, 2 ≤ (e i : ℕ) + (f i : ℕ) := fun i => hcon i
    have : 2 * m ≤ qdeg e + qdeg f := by
      unfold qdeg
      rw [← Finset.sum_add_distrib]
      calc 2 * m = ∑ _i : Fin m, 2 := by rw [Finset.sum_const]; simp [mul_comm]
        _ ≤ ∑ i, ((e i : ℕ) + (f i : ℕ)) := Finset.sum_le_sum (fun i _ => hge i)
    omega
  obtain ⟨i, hi⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact zmod3_powsum_eq_zero_of_le_one hi

/-! ## The CSS dual inclusion -/

/-- **The CSS dual inclusion.** `QRM(r₂) ⊆ QRM(s)^⊥` whenever `r₂ + s ≤ 2m − 1`
(equivalently `r₂ + s < 2m`).  This is the `q = 3` instance of RM duality and is
the containment condition the qutrit-CSS code requires. -/
theorem QRM_dual_inclusion {m r₂ s : ℕ} (h : r₂ + s + 1 ≤ 2 * m) :
    QRM r₂ m ≤ dualQ (QRM s m) := by
  rw [QRM_eq r₂ m, Submodule.span_le]
  rintro _ ⟨e, he, rfl⟩
  -- goal: `qmono e ∈ dualQ (QRM s m)`, i.e. orthogonal to every `g ∈ QRM s m`
  -- it suffices to check orthogonality on the spanning monomials of `QRM s m`
  have hgen : QRM s m ≤ dualQ (Submodule.span (ZMod 3) {qmono e}) := by
    rw [QRM_eq s m, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    intro x hx
    -- `x ∈ span {qmono e}`, so `x = c • qmono e`
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    have horth : qdot (qmono f) (qmono e) = 0 := by
      apply qmono_orthogonal
      have : qdeg f ≤ s := hf
      have : qdeg e ≤ r₂ := he
      omega
    simp only [qdot, Pi.smul_apply, smul_eq_mul]
    rw [show (∑ y, qmono f y * (c * qmono e y)) = c * ∑ y, qmono f y * qmono e y by
      rw [Finset.mul_sum]; congr 1; ext y; ring]
    rw [show (∑ y, qmono f y * qmono e y) = qdot (qmono f) (qmono e) from rfl, horth, mul_zero]
  -- now derive membership in `dualQ (QRM s m)`
  intro g hg
  have hmem : qmono e ∈ Submodule.span (ZMod 3) {qmono e} :=
    Submodule.mem_span_singleton_self _
  have := hgen hg (qmono e) hmem
  -- `qdot g (qmono e) = 0`; rewrite to `qdot (qmono e) g = 0`
  rw [show qdot (qmono e) g = qdot g (qmono e) by
    simp only [qdot]; congr 1; ext y; ring]
  exact this

/-! ## Dimension -/

/-
The reduced monomials form a linearly independent family (in fact a basis of
`QFun m`, since there are `3 ^ m = dim (QFun m)` of them).  Equivalently, the
evaluation/interpolation Vandermonde over `𝔽₃` (nodes `0, 1, 2`) is invertible.
-/
theorem qmono_linearIndependent (m : ℕ) :
    LinearIndependent (ZMod 3) (qmono : Exp m → QFun m) := by
  -- Consider the polynomial \( f(x_1, \ldots, x_m) = \prod_{i=1}^m (1 - (x_i - a_i)^2) \).
  set f : (Fin m → ZMod 3) → (Fin m → ZMod 3) → ZMod 3 := fun a x => ∏ i, (1 - (x i - a i)^2);
  -- By definition of $f$, we know that $f(a, x) = \delta_{ax}$, where $\delta_{ax}$ is the Kronecker delta.
  have hf_delta : ∀ a b : Fin m → ZMod 3, f a b = if a = b then 1 else 0 := by
    intro a b
    simp [f];
    split_ifs with h;
    · aesop;
    · rw [ Finset.prod_eq_zero_iff ];
      obtain ⟨ i, hi ⟩ := Function.ne_iff.mp h; use i; simp +decide;
      have : ∀ x : ZMod 3, x ≠ 0 → 1 - x ^ 2 = 0 := by decide; ; exact this _ ( sub_ne_zero_of_ne <| Ne.symm hi ) ;
  -- By definition of $f$, we know that $f(a, x)$ can be written as a linear combination of the monomials $qmono e$.
  have hf_comb : ∀ a : Fin m → ZMod 3, ∃ c : Exp m → ZMod 3, f a = ∑ e : Exp m, c e • qmono e := by
    intro a
    have hf_comb_step : ∀ i : Fin m, ∃ c : Fin 3 → ZMod 3, ∀ x : ZMod 3, (1 - (x - a i)^2) = ∑ e : Fin 3, c e • x ^ (e : ℕ) := by
      intro i; use fun e => if e = 0 then 1 - a i ^ 2 else if e = 1 then 2 * a i else -1; simp +decide [ Fin.sum_univ_three ] ; ring;
      decide +kernel;
    choose c hc using hf_comb_step;
    -- By definition of $f$, we know that $f(a, x)$ can be written as a product of sums, which can be expanded into a sum of products.
    have hf_expand : ∀ x : Fin m → ZMod 3, f a x = ∑ e : Fin m → Fin 3, (∏ i, c i (e i)) • (∏ i, x i ^ (e i : ℕ)) := by
      intro x
      simp [f, hc];
      rw [ Finset.prod_sum ];
      refine' Finset.sum_bij ( fun p hp => fun i => p i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
      · simp +decide [ funext_iff ];
      · exact fun b => ⟨ fun i _ => b i, rfl ⟩;
    exact ⟨ _, funext fun x => by simpa [ qmono ] using hf_expand x ⟩;
  -- By definition of $f$, we know that $f(a, x)$ can be written as a linear combination of the monomials $qmono e$, and thus the monomials $qmono e$ span the entire space.
  have h_span : ∀ g : QFun m, ∃ c : Exp m → ZMod 3, g = ∑ e : Exp m, c e • qmono e := by
    intro g
    obtain ⟨c, hc⟩ : ∃ c : (Fin m → ZMod 3) → ZMod 3, g = ∑ a : Fin m → ZMod 3, c a • f a := by
      use fun a => g a; ext x; simp +decide [ hf_delta ] ;
    choose! c' hc' using hf_comb;
    use fun e => ∑ a, c a * c' a e;
    simp +decide [ hc, hc', Finset.sum_smul, Finset.smul_sum, Finset.sum_mul, smul_smul ];
    exact Finset.sum_comm;
  refine' linearIndependent_iff_card_eq_finrank_span.mpr _;
  rw [ Set.finrank ];
  rw [ show Submodule.span ( ZMod 3 ) ( Set.range qmono ) = ⊤ from _ ];
  · simp +decide [ Module.finrank ];
  · exact eq_top_iff.mpr fun g hg => by obtain ⟨ c, rfl ⟩ := h_span g; exact Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ ( Submodule.subset_span <| Set.mem_range_self _ ) ;

/-
**The dimension of `QRM(r, m)`** equals the number of reduced monomial
exponent vectors of total degree `≤ r`.
-/
theorem QRM_dim (r m : ℕ) :
    Module.finrank (ZMod 3) (QRM r m)
      = (Finset.univ.filter (fun e : Exp m => qdeg e ≤ r)).card := by
  rw [ show QRM r m = Submodule.span ( ZMod 3 ) ( Set.range ( fun e : { e : Fin m → Fin 3 // qdeg e ≤ r } => qmono e.val ) ) from ?_ ];
  · rw [ @finrank_span_eq_card ];
    · rw [ Fintype.subtype_card ];
    · exact qmono_linearIndependent m |> fun h => h.comp _ Subtype.val_injective;
  · simp +decide [ QRM_eq, Set.image ];
    congr with x ; aesop

/-- **Headline parameters of `QRM`.** The block length is `3 ^ m` and the
dimension is the count of degree-`≤ r` reduced monomials. -/
theorem QRM_params (r m : ℕ) :
    Fintype.card (Fin m → ZMod 3) = 3 ^ m ∧
    Module.finrank (ZMod 3) (QRM r m)
      = (Finset.univ.filter (fun e : Exp m => qdeg e ≤ r)).card := by
  refine ⟨?_, QRM_dim r m⟩
  simp

end QutritCSSBarnesWall