import StabilizerBW.BWCss.ReedMuller

/-!
# CSS codes from Reed–Muller pairs: the Barnes–Wall CSS family `BWCss(m, r₁, r₂)`

We package the *classical-code data* of a Calderbank–Shor–Steane (CSS) code as a
structure `CSSCode` (no quantum stabiliser formalism is needed at this layer),
and build the Reed–Muller-pair member `CSSCode.ofRMPair` whose quantum parameters
`[[n, k, d]]` are `n = 2^m`, `k = ∑_{r₂ < i ≤ r₁} C(m,i)`, `d = 2^(m-r₁)`.

## Distance convention

The `d` field is the **X-distance** of the CSS code: the minimum Hamming weight
of a nontrivial logical-X representative, i.e. a codeword of `C₁ = CZᗮ` that is
not in the X-stabiliser `CX = C₂`. For the Reed–Muller pair this equals
`2^(m - r₁)` (the minimum distance of `RM(r₁, m)`), which is exactly the
headline formula. (The full CSS distance is `min` of the X- and Z-distances;
we record the X-distance, which is the quantity the parameter formula `(n,k,d)`
names.)
-/

open scoped BigOperators
open Classical

namespace BWCss

/-- The classical-code data of a CSS quantum stabiliser code, with the parameter
equations the data must satisfy. No density matrices / Pauli group are needed:
the logical parameters are derived from the underlying binary linear codes. -/
structure CSSCode where
 /-- Block length. -/
 n : ℕ
 /-- The X-stabiliser code (the `C₂` of the standard literature). -/
 CX : Submodule (ZMod 2) (Fin n → ZMod 2)
 /-- The Z-stabiliser code (the `C₁^⊥` of the standard literature). -/
 CZ : Submodule (ZMod 2) (Fin n → ZMod 2)
 /-- The CSS containment condition `C₂ ⊆ C₁` (equivalently `CX ≤ CZᗮ`). -/
 css_condition : CX ≤ dualCode CZ
 /-- Number of logical qubits. -/
 k : ℕ
 /-- Code distance (here: the X-distance). -/
 d : ℕ
 /-- The logical-dimension equation `k = n - dim CX - dim CZ`. -/
 dim_eq : k = n - Module.finrank (ZMod 2) CX - Module.finrank (ZMod 2) CZ
 /-- The distance certificate: every nontrivial logical-X representative
 (an element of `C₁ = CZᗮ` outside the X-stabiliser `CX`) has weight `≥ d`. -/
 dist_eq : ∀ c ∈ dualCode CZ, c ∉ CX → d ≤ hammingNorm c

/-! ### The Reed–Muller pair CSS code -/

/-
Complementary-sum identity underlying the logical-dimension formula.
-/
theorem binom_dim_add (m r₁ r₂ : ℕ) (h : r₂ < r₁) (hcss : r₁ + r₂ ≤ m - 1) :
 (∑ i ∈ Finset.Iic r₂, Nat.choose m i) + (∑ i ∈ Finset.Iic (m - r₁ - 1), Nat.choose m i)
 + (∑ i ∈ Finset.Ioc r₂ r₁, Nat.choose m i) = 2 ^ m := by
 convert Iic_choose_add r₁ m ( by omega ) using 1;
 rw [ show Finset.Iic r₁ = Finset.Iic r₂ ∪ Finset.Ioc r₂ r₁ from ?_, Finset.sum_union ] <;> norm_num [ add_comm, add_left_comm, add_assoc ];
 · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => not_lt_of_ge ( Finset.mem_Iic.mp hx₁ ) ( Finset.mem_Ioc.mp hx₂ |>.1 );
 · grind

/-
The CSS containment condition for the Reed–Muller pair.
-/
theorem ofRMPair_css (m r₁ r₂ : ℕ) (h : r₂ < r₁) (hcss : r₁ + r₂ ≤ m - 1) :
 RM r₂ m ≤ dualCode (RM (m - r₁ - 1) m) := by
 -- By the properties of the Reed-Muller codes and their duals, we have that $RM r₂ m \leq RM r₁ m$.
 have h_RM_mono : RM r₂ m ≤ RM r₁ m := by
 exact RM_mono h.le;
 convert h_RM_mono using 1;
 convert RM_dual ( m - r₁ - 1 ) m _ using 1;
 · lia;
 · omega

/-
The logical-dimension equation for the Reed–Muller pair.
-/
theorem ofRMPair_dim (m r₁ r₂ : ℕ) (h : r₂ < r₁) (hcss : r₁ + r₂ ≤ m - 1) :
 (∑ i ∈ Finset.Ioc r₂ r₁, Nat.choose m i) =
 2 ^ m - Module.finrank (ZMod 2) (RM r₂ m) - Module.finrank (ZMod 2) (RM (m - r₁ - 1) m) := by
 rw [ RM_dim, RM_dim ];
 · rw [ Nat.sub_sub, eq_comm ];
 exact Nat.sub_eq_of_eq_add <| by linarith [ binom_dim_add m r₁ r₂ h hcss ] ;
 · omega;
 · omega

/-
The distance certificate for the Reed–Muller pair: nontrivial logical-X
representatives have weight at least `2^(m-r₁)`.
-/
theorem ofRMPair_dist (m r₁ r₂ : ℕ) (h : r₂ < r₁) (hcss : r₁ + r₂ ≤ m - 1) :
 ∀ c ∈ dualCode (RM (m - r₁ - 1) m), c ∉ RM r₂ m → 2 ^ (m - r₁) ≤ hammingNorm c := by
 intros c hc hc';
 have h_dual : c ∈ RM r₁ m := by
 convert RM_dual ( m - r₁ - 1 ) m ( by omega ) ▸ hc using 1;
 rw [ show m - ( m - r₁ - 1 ) - 1 = r₁ by omega ];
 apply BWCss.RM_min_dist r₁ m (by omega) c h_dual (by
 exact fun h => hc' <| h.symm ▸ Submodule.zero_mem _)

/-- The Reed–Muller-pair CSS code `BWCss(m, r₁, r₂)` with `C₁ = RM(r₁,m)`,
`C₂ = RM(r₂,m)` (so `CX = RM(r₂,m)` and `CZ = C₁^⊥ = RM(m-r₁-1,m)`). -/
noncomputable def CSSCode.ofRMPair (m r₁ r₂ : ℕ) (h : r₂ < r₁) (hcss : r₁ + r₂ ≤ m - 1) :
 CSSCode where
 n := 2 ^ m
 CX := RM r₂ m
 CZ := RM (m - r₁ - 1) m
 css_condition := ofRMPair_css m r₁ r₂ h hcss
 k := ∑ i ∈ Finset.Ioc r₂ r₁, Nat.choose m i
 d := 2 ^ (m - r₁)
 dim_eq := ofRMPair_dim m r₁ r₂ h hcss
 dist_eq := ofRMPair_dist m r₁ r₂ h hcss

@[simp] theorem CSSCode.ofRMPair_n (m r₁ r₂ : ℕ) (h : r₂ < r₁) (hcss : r₁ + r₂ ≤ m - 1) :
 (CSSCode.ofRMPair m r₁ r₂ h hcss).n = 2 ^ m := rfl

@[simp] theorem CSSCode.ofRMPair_k (m r₁ r₂ : ℕ) (h : r₂ < r₁) (hcss : r₁ + r₂ ≤ m - 1) :
 (CSSCode.ofRMPair m r₁ r₂ h hcss).k =
 ∑ i ∈ Finset.Ioc r₂ r₁, Nat.choose m i := rfl

@[simp] theorem CSSCode.ofRMPair_d (m r₁ r₂ : ℕ) (h : r₂ < r₁) (hcss : r₁ + r₂ ≤ m - 1) :
 (CSSCode.ofRMPair m r₁ r₂ h hcss).d = 2 ^ (m - r₁) := rfl

/-! ### The headline parameter formula -/

/-- The Barnes–Wall CSS code family, total in `(m, r₁, r₂)`. On valid parameters
(`r₂ < r₁` and `r₁ + r₂ ≤ m - 1`) it is `CSSCode.ofRMPair`; otherwise it falls
back to a fixed valid member. -/
noncomputable def BWCss (m r₁ r₂ : ℕ) : CSSCode :=
 if hp : r₂ < r₁ ∧ r₁ + r₂ ≤ m - 1 then CSSCode.ofRMPair m r₁ r₂ hp.1 hp.2
 else CSSCode.ofRMPair 2 1 0 (by decide) (by decide)

/-- **Headline parameter formula for the Barnes–Wall CSS family.** -/
theorem BWCss_params (m r₁ r₂ : ℕ) (h : r₁ + r₂ ≤ m - 1) (h1 : r₂ < r₁) :
 (BWCss m r₁ r₂).n = 2 ^ m ∧
 (BWCss m r₁ r₂).k = ∑ i ∈ Finset.Ioc r₂ r₁, Nat.choose m i ∧
 (BWCss m r₁ r₂).d = 2 ^ (m - r₁) := by
 have hp : r₂ < r₁ ∧ r₁ + r₂ ≤ m - 1 := ⟨h1, h⟩
 simp only [BWCss, dif_pos hp, CSSCode.ofRMPair_n, CSSCode.ofRMPair_k, CSSCode.ofRMPair_d,
 and_self]

/-! ### Narrative-spine theorem: canonical seed codes -/

/-- The Steane and Bravyi–Haah seed codes are punctures of canonical members of
the BWCss family. Here `d` is the X-distance convention `2^(m-r₁)` (see the
module docstring); under this convention both seeds have `d = 4`. -/
theorem BWCss_recovers_canonical_seeds :
 -- Steane lives over BWCss(3, 1, 0): [[8, 3, 4_X]]
 (CSSCode.ofRMPair 3 1 0 (by decide) (by decide)).n = 8 ∧
 (CSSCode.ofRMPair 3 1 0 (by decide) (by decide)).k = 3 ∧
 (CSSCode.ofRMPair 3 1 0 (by decide) (by decide)).d = 4 ∧
 -- Bravyi–Haah lives over BWCss(4, 2, 0): [[16, 10, 4]]
 (CSSCode.ofRMPair 4 2 0 (by decide) (by decide)).n = 16 ∧
 (CSSCode.ofRMPair 4 2 0 (by decide) (by decide)).k = 10 ∧
 (CSSCode.ofRMPair 4 2 0 (by decide) (by decide)).d = 4 := by
 refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
 simp only [CSSCode.ofRMPair_n, CSSCode.ofRMPair_k, CSSCode.ofRMPair_d] <;> decide

/-- Stretch instances (`r > 1`): the quantum first-order RM code `BWCss(4,2,1)`
is `[[16, 6, 4]]` and `BWCss(5,2,1)` is `[[32, 10, 8]]`. -/
theorem BWCss_extra_instances :
 (CSSCode.ofRMPair 4 2 1 (by decide) (by decide)).n = 16 ∧
 (CSSCode.ofRMPair 4 2 1 (by decide) (by decide)).k = 6 ∧
 (CSSCode.ofRMPair 4 2 1 (by decide) (by decide)).d = 4 ∧
 (CSSCode.ofRMPair 5 2 1 (by decide) (by decide)).n = 32 ∧
 (CSSCode.ofRMPair 5 2 1 (by decide) (by decide)).k = 10 ∧
 (CSSCode.ofRMPair 5 2 1 (by decide) (by decide)).d = 8 := by
 refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
 simp only [CSSCode.ofRMPair_n, CSSCode.ofRMPair_k, CSSCode.ofRMPair_d] <;> decide

end BWCss