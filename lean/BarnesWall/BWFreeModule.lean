import Mathlib

/-!
# The Barnes-Wall family: free-module decomposition and the pinned logical-lattice theorem

This file formalizes **Target 1** of the Arithmetic View chapter.

We represent the `n`-qubit coordinate space over the Gaussian integers `ℤ[i]`
recursively as nested pairs `Q n` (so `Q 0 = ℤ[i]` and `Q (n+1) = Q n × Q n`,
the `|0⟩`-block and the `|1⟩`-block of the first qubit). The `n`-qubit
Barnes-Wall lattice `BWₙ = B^{⊗n} ℤ[i]^{2ⁿ}` is captured recursively via the
fact `BW_{n+1} = BW₁ ⊗ BW_n`, i.e. every vector decomposes as
`(1+i)|0⟩ ⊗ a + (|0⟩+|1⟩) ⊗ b` with `a, b ∈ BW_n`.

## Main results

* `InBWn_succ_iff` / `freeModuleDecomp` — **Lemma 1.1**: the (existence half of the)
 free-module decomposition of `BWₙ`.
* `freeModuleDecomp_unique` — **Lemma 1.1** uniqueness.
* `pinned_one` — **Theorem 1.2** (pinned case, `m = 1`):
 `BWₙ ∩ {w : (Z⊗I)w = w} = (1+i)|0⟩ ⊗ BW_{n-1}`.
* `bell_theory` — the Bell theory `BW₂^{⟨ZZ,XX⟩} = ℤ[i]·(1+i)(|00⟩+|11⟩)`.
* `bell_minimal_iff` — its four minimal vectors are the units times the scaled Bell vector.
-/

open Zsqrtd

namespace BWArith

/-- The Gaussian integers `ℤ[i]`. -/
abbrev GI := GaussianInt

/-- The Gaussian integer `1 + i`. -/
abbrev oneI : GI := ⟨1, 1⟩

/-! ## The `n`-qubit coordinate space as nested pairs -/

/-- `n`-qubit coordinate space over `ℤ[i]`, as nested pairs.
 `Q 0 = ℤ[i]`, and `Q (n+1) = Q n × Q n` is the `|0⟩`-block paired with the
 `|1⟩`-block of the leading qubit. -/
def Q : ℕ → Type
 | 0 => GI
 | (n+1) => Q n × Q n

instance instACGQ : ∀ n, AddCommGroup (Q n)
 | 0 => inferInstanceAs (AddCommGroup GI)
 | (n+1) =>
 letI := instACGQ n
 inferInstanceAs (AddCommGroup (Q n × Q n))

instance instModQ : ∀ n, Module GI (Q n)
 | 0 => inferInstanceAs (Module GI GI)
 | (n+1) =>
 letI := instModQ n
 inferInstanceAs (Module GI (Q n × Q n))

/-- `Q n` is a torsion-free `ℤ[i]`-module (no zero `smul`-divisors), proved by
 induction: the base case is the domain `GI`, and products of torsion-free
 modules are torsion-free. -/
instance instNZSDQ : ∀ n, NoZeroSMulDivisors GI (Q n)
 | 0 => inferInstanceAs (NoZeroSMulDivisors GI GI)
 | (n+1) =>
 letI := instModQ n
 letI := instNZSDQ n
 { eq_zero_or_eq_zero_of_smul_eq_zero := by
 rintro c ⟨x1, x2⟩ h
 have h1 : c • x1 = 0 := congrArg Prod.fst h
 rcases eq_zero_or_eq_zero_of_smul_eq_zero h1 with hc | hx1
 · exact Or.inl hc
 · have h2 : c • x2 = 0 := congrArg Prod.snd h
 rcases eq_zero_or_eq_zero_of_smul_eq_zero h2 with hc | hx2
 · exact Or.inl hc
 · exact Or.inr (by
 rw [show ((x1, x2) : Q n × Q n) = ((0 : Q n), (0 : Q n)) from by
 rw [hx1, hx2]]; rfl) }

/-! ## Torsion-freeness helpers -/

/-- `Q n` has no `2`-torsion: `x + x = 0 → x = 0`. -/
theorem Q.add_self_eq_zero (n : ℕ) (x : Q n) (h : x + x = 0) : x = 0 := by
 have h2 : (2 : GI) • x = 0 := by rw [two_smul]; exact h
 exact (smul_eq_zero.mp h2).resolve_left (by decide)

/-- Multiplication by `1+i` is injective on `Q n` (the module is torsion-free). -/
theorem Q.oneI_smul_eq_zero (n : ℕ) (x : Q n) (h : oneI • x = 0) : x = 0 :=
 (smul_eq_zero.mp h).resolve_left (by decide)

/-- `1+i` acts injectively (cancellative) on `Q n`. -/
theorem Q.oneI_smul_inj (n : ℕ) {a b : Q n} (h : oneI • a = oneI • b) : a = b := by
 have : oneI • (a - b) = 0 := by rw [smul_sub, h, sub_self]
 have := Q.oneI_smul_eq_zero n _ this
 exact sub_eq_zero.mp this

/-! ## The Barnes-Wall lattice `BWₙ` -/

/-- Membership in the `n`-qubit Barnes-Wall lattice `BWₙ`.
 `BW₀ = ℤ[i]` is everything; and `w ∈ BW_{n+1}` iff its `|1⟩`-block `w.2`
 lies in `BW_n` and its `|0⟩`-block has the form `(1+i)·a + w.2` for some
 `a ∈ BW_n`. Equivalently `w = (1+i)|0⟩ ⊗ a + (|0⟩+|1⟩) ⊗ b` with
 `a = a`, `b = w.2 ∈ BW_n`. -/
def InBWn : (n : ℕ) → Q n → Prop
 | 0, _ => True
 | (n+1), w => InBWn n w.2 ∧ ∃ a : Q n, InBWn n a ∧ w.1 = oneI • a + w.2

/-- `BW₀` is all of `ℤ[i]`. -/
@[simp] theorem InBWn_zero (x : Q 0) : InBWn 0 x := trivial

/-- The zero vector lies in every `BWₙ`. -/
theorem InBWn_zero_vec : ∀ n, InBWn n (0 : Q n)
 | 0 => trivial
 | (n+1) => ⟨InBWn_zero_vec n, 0, InBWn_zero_vec n, by simp⟩

/-- **Lemma 1.1 (existence).** Every `w ∈ BW_{n+1}` is
 `w = (1+i)|0⟩ ⊗ a + (|0⟩+|1⟩) ⊗ b` with `a, b ∈ BW_n`. -/
theorem freeModuleDecomp (n : ℕ) (w : Q (n+1)) :
 InBWn (n+1) w ↔
 ∃ a b : Q n, InBWn n a ∧ InBWn n b ∧ w = (oneI • a + b, b) := by
 constructor
 · rintro ⟨hb, a, ha, hw1⟩
 exact ⟨a, w.2, ha, hb, Prod.ext hw1 rfl⟩
 · rintro ⟨a, b, ha, hb, rfl⟩
 exact ⟨hb, a, ha, rfl⟩

/-- **Lemma 1.1 (uniqueness).** The decomposition `w = (1+i)|0⟩⊗a + (|0⟩+|1⟩)⊗b`
 is unique. -/
theorem freeModuleDecomp_unique (n : ℕ) {a b a' b' : Q n}
 (h : ((oneI • a + b, b) : Q (n+1)) = (oneI • a' + b', b')) :
 a = a' ∧ b = b' := by
 have hb : b = b' := congrArg Prod.snd h
 have h1 : oneI • a + b = oneI • a' + b' := congrArg Prod.fst h
 subst hb
 have : oneI • a = oneI • a' := add_right_cancel h1
 exact ⟨Q.oneI_smul_inj n this, rfl⟩

/-! ## Theorem 1.2: the pinned case -/

/-- The action of `Z ⊗ I^{⊗(n-1)}` on `Q (n+1)`: it fixes the `|0⟩`-block and
 negates the `|1⟩`-block. -/
def pinZ (n : ℕ) (w : Q (n+1)) : Q (n+1) := (w.1, -w.2)

/-- The `Z`-eigenvalue-`+1` condition pins the `|1⟩`-block to zero. -/
theorem pinZ_eq_self_iff (n : ℕ) (w : Q (n+1)) : pinZ n w = w ↔ w.2 = 0 := by
 constructor
 · intro h
 have h2 : -w.2 = w.2 := congrArg Prod.snd h
 have : w.2 + w.2 = 0 := add_eq_zero_iff_eq_neg.mpr h2.symm
 exact Q.add_self_eq_zero n w.2 this
 · intro h
 exact Prod.ext rfl (by simp [pinZ, h])

/-- **Theorem 1.2 (pinned case, `m = 1`).**
 `BWₙ ∩ {w : (Z⊗I^{⊗(n-1)})w = w} = (1+i)|0⟩ ⊗ BW_{n-1}`:
 a vector in `BW_{n+1}` is fixed by `Z⊗I` iff its `|1⟩`-block vanishes and its
 `|0⟩`-block is `(1+i)·a` for some `a ∈ BW_n`. -/
theorem pinned_one (n : ℕ) (w : Q (n+1)) :
 (InBWn (n+1) w ∧ pinZ n w = w) ↔
 (w.2 = 0 ∧ ∃ a : Q n, InBWn n a ∧ w.1 = oneI • a) := by
 rw [pinZ_eq_self_iff]
 constructor
 · rintro ⟨⟨hb, a, ha, hw1⟩, hz⟩
 refine ⟨hz, a, ha, ?_⟩
 rw [hw1, hz, add_zero]
 · rintro ⟨hz, a, ha, hw1⟩
 refine ⟨⟨?_, a, ha, ?_⟩, hz⟩
 · rw [hz]; exact InBWn_zero_vec n
 · rw [hw1, hz, add_zero]

/-- **Concrete instance** (`n = 2`, `m = 1`).
 `BW₂ ∩ {w : (Z⊗I)w = w} = (1+i)|0⟩ ⊗ BW₁`. -/
theorem pinned_one_two (w : Q 2) :
 (InBWn 2 w ∧ pinZ 1 w = w) ↔
 (w.2 = 0 ∧ ∃ a : Q 1, InBWn 1 a ∧ w.1 = oneI • a) :=
 pinned_one 1 w

/-! ## Closure of `BWₙ` under `ℤ[i]`-scaling -/

/-- `BWₙ` is closed under scaling by any Gaussian integer: it is an `ℤ[i]`-lattice. -/
theorem InBWn_smul : ∀ (n : ℕ) (c : GI) (a : Q n), InBWn n a → InBWn n (c • a)
 | 0, _, _, _ => trivial
 | (n+1), c, a, ha => by
 obtain ⟨hb, x, hx, hx1⟩ := ha
 refine ⟨InBWn_smul n c a.2 hb, c • x, InBWn_smul n c x hx, ?_⟩
 have : (c • a).1 = c • a.1 := rfl
 rw [this, hx1, smul_add, smul_smul, smul_smul, mul_comm]
 rfl

/-! ## Theorem 1.2: the iterated (rank-`m`) pinned case

We pin the `m` *trailing* qubits (the recursion variable on the right makes the
nested-pair type reduce definitionally). By the tensor symmetry of `BWₙ` this is
the same rank-`m` pinned theorem: the constraint sublattice of `⟨m commuting Z's⟩`
is an isometrically `(1+i)^m`-scaled copy of `BW_k` (`k = n - m`). -/

/-- Embed a `k`-qubit vector into the all-`|0⟩` leaf of the `m` pinned qubits,
 zero everywhere else: this realizes `(·) ⊗ |0^m⟩`. -/
def embed : (k m : ℕ) → Q k → Q (k + m)
 | _, 0, v => v
 | k, (m+1), v => (embed k m v, 0)

/-- `embed` is `ℤ[i]`-linear in the embedded vector (scaling commutes with embedding). -/
theorem embed_smul (k m : ℕ) (c : GI) (v : Q k) :
 embed k m (c • v) = c • embed k m v := by
 induction m with
 | zero => rfl
 | succ m ih =>
 refine Prod.ext ?_ ?_
 · show embed k m (c • v) = c • embed k m v; exact ih
 · show (0 : Q (k+m)) = c • (0 : Q (k+m)); rw [smul_zero]

/-- The predicate "the `m` trailing qubits are `Z`-pinned to `+1`":
 each trailing qubit's `|1⟩`-block vanishes (descending into the `|0⟩`-block). -/
def Pinned : (k m : ℕ) → Q (k + m) → Prop
 | _, 0, _ => True
 | k, (m+1), w => w.2 = 0 ∧ Pinned k m w.1

/-- An embedded vector is `Z`-pinned on the `m` trailing qubits. -/
theorem embed_pinned (k m : ℕ) (v : Q k) : Pinned k m (embed k m v) := by
 induction m with
 | zero => trivial
 | succ m ih => exact ⟨rfl, ih⟩

/-- Pinning is invariant under scaling by `1+i` (used to strip a factor of `1+i`). -/
theorem Pinned_oneI_smul_iff (k m : ℕ) (w : Q (k + m)) :
 Pinned k m (oneI • w) ↔ Pinned k m w := by
 induction m with
 | zero => exact Iff.rfl
 | succ m ih =>
 constructor
 · rintro ⟨h2, h1⟩
 refine ⟨?_, ?_⟩
 · exact Q.oneI_smul_eq_zero (k+m) w.2 h2
 · exact ih w.1 |>.mp h1
 · rintro ⟨h2, h1⟩
 refine ⟨?_, ?_⟩
 · show oneI • w.2 = 0; rw [h2, smul_zero]
 · exact (ih w.1).mpr h1

/-- An embedded scaled BW-vector lies in `BW_{k+m}`. -/
theorem embed_mem (k m : ℕ) (a : Q k) (ha : InBWn k a) :
 InBWn (k + m) (embed k m (oneI ^ m • a)) := by
 induction m with
 | zero => simpa using ha
 | succ m ih =>
 refine ⟨InBWn_zero_vec (k + m), embed k m (oneI ^ m • a), ih, ?_⟩
 show embed k m (oneI ^ (m+1) • a) = oneI • embed k m (oneI ^ m • a) + 0
 rw [add_zero, pow_succ', mul_smul, embed_smul]

/-- **Theorem 1.2 (iterated case).**
 Pinning `m` qubits to `⟨Z's⟩` gives an isometrically `(1+i)^m`-scaled `BW_k`:
 `BW_{k+m}^{⟨pin⟩} = (1+i)^m · |0^m⟩ ⊗ BW_k`. -/
theorem pinned_iter (k : ℕ) : ∀ (m : ℕ) (w : Q (k + m)),
 (InBWn (k + m) w ∧ Pinned k m w) ↔
 ∃ a : Q k, InBWn k a ∧ w = embed k m (oneI ^ m • a)
 | 0, w => by
 constructor
 · rintro ⟨hw, _⟩
 exact ⟨w, hw, by simp [embed]⟩
 · rintro ⟨a, ha, rfl⟩
 exact ⟨by simpa [embed] using ha, trivial⟩
 | (m+1), w => by
 constructor
 · rintro ⟨hbw, hp2, hp1⟩
 obtain ⟨hb, x, hx, hx1⟩ := hbw
 have hw1 : w.1 = oneI • x := by rw [hx1, hp2, add_zero]
 have hxpinned : Pinned k m x :=
 (Pinned_oneI_smul_iff k m x).mp (by rw [← hw1]; exact hp1)
 obtain ⟨a, ha, hxeq⟩ := (pinned_iter k m x).mp ⟨hx, hxpinned⟩
 refine ⟨a, ha, ?_⟩
 show w = (embed k m (oneI ^ (m+1) • a), 0)
 refine Prod.ext ?_ hp2
 show w.1 = embed k m (oneI ^ (m+1) • a)
 rw [hw1, hxeq, ← embed_smul, ← mul_smul, ← pow_succ']
 · rintro ⟨a, ha, rfl⟩
 exact ⟨embed_mem k (m+1) a ha, embed_pinned k (m+1) _⟩

/-! ## The Bell theory `BW₂^{⟨ZZ,XX⟩}`

The two-qubit constraint sublattice of the stabilizer theory `⟨ZZ, XX⟩` is the
rank-one `ℤ[i]`-module generated by the scaled Bell vector `(1+i)(|00⟩+|11⟩)`,
and its four minimal vectors are the units times that generator (norm `4`). -/

/-- `Z ⊗ Z` acting on `Q 2 = ((|00⟩,|01⟩),(|10⟩,|11⟩))`: signs `(+,-,-,+)`. -/
def ZZ (w : Q 2) : Q 2 := ((w.1.1, -w.1.2), (-w.2.1, w.2.2))

/-- `X ⊗ X` acting on `Q 2`: the full bit-flip `(a,b,c,d) ↦ (d,c,b,a)`. -/
def XX (w : Q 2) : Q 2 := ((w.2.2, w.2.1), (w.1.2, w.1.1))

/-- The scaled Bell vector `(1+i)(|00⟩+|11⟩)`. -/
def bellGen : Q 2 := ((oneI, 0), (0, oneI))

/-- The squared Hermitian norm `Σ|·|²` of a two-qubit vector. -/
def normQ2 (w : Q 2) : ℤ :=
 Zsqrtd.norm w.1.1 + Zsqrtd.norm w.1.2 + Zsqrtd.norm w.2.1 + Zsqrtd.norm w.2.2

/-- **The Bell theory.** `BW₂^{⟨ZZ,XX⟩} = ℤ[i]·(1+i)(|00⟩+|11⟩)`:
 a vector of `BW₂` is fixed by both `ZZ` and `XX` iff it is a Gaussian-integer
 multiple of the scaled Bell vector. -/
theorem bell_theory (w : Q 2) :
 (InBWn 2 w ∧ ZZ w = w ∧ XX w = w) ↔ ∃ c : GI, w = c • bellGen := by
 constructor <;> intro h;
 · rcases w with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩;
 simp_all +decide [ ZZ, XX, bellGen ];
 -- From the equality of the pairs, we can deduce that $b = 0$, $c = 0$, and $d = a$.
 have hb : b = 0 := by
 have := Q.add_self_eq_zero 0 b; simp_all +decide ;
 grind
 have hc : c = 0 := by
 grind
 have hd : d = a := by
 grobner
 simp_all +decide [ Q ];
 obtain ⟨ x, hx ⟩ := h.2;
 rcases x with ⟨ x₁, x₂ ⟩ ; simp_all +decide [ Q ];
 exact ⟨ x₁, mul_comm _ _ ⟩;
 · rcases h with ⟨ c, rfl ⟩ ; simp +decide [ ZZ, XX,bellGen ] ;
 simp +decide [ InBWn ];
 simp [Q] at *;
 refine' ⟨ ⟨ -c, _ ⟩, ⟨ -c, _, _ ⟩ ⟩ <;> simp +decide [ mul_comm ];
 exact ⟨ c * ⟨ 1, -1 ⟩, by ext <;> norm_num <;> ring_nf ⟩

/-- The norm of `c · bellGen` is `4·|c|²`. -/
theorem normQ2_smul_bell (c : GI) : normQ2 (c • bellGen) = 4 * Zsqrtd.norm c := by
 unfold normQ2 bellGen; norm_num [ mul_comm, Zsqrtd.norm ] ; ring;
 erw [ Prod.smul_mk, Prod.smul_mk, Prod.smul_mk ] ; norm_num ; ring;

/-- **The four minimal vectors of the Bell theory.** A vector is a (nonzero,
 norm-`4`) minimal vector of `BW₂^{⟨ZZ,XX⟩}` iff it is a unit times the scaled
 Bell vector — the four units `{±1, ±i}` give the four minimal vectors. -/
theorem bell_minimal_iff (w : Q 2) :
 (InBWn 2 w ∧ ZZ w = w ∧ XX w = w ∧ w ≠ 0 ∧ normQ2 w = 4) ↔
 ∃ u : GI, IsUnit u ∧ w = u • bellGen := by
 constructor;
 · intro hw
 obtain ⟨c, hc⟩ := bell_theory w |>.1 ⟨hw.left, hw.right.left, hw.right.right.left⟩
 have hc_norm : Zsqrtd.norm c = 1 := by
 have := normQ2_smul_bell c; aesop;
 have hc_unit : IsUnit c := by
 rw [ isUnit_iff_exists_inv ] ; use ⟨ c.re, -c.im ⟩ ; ext <;> simp +decide [ Zsqrtd.norm ] at * <;> linarith;
 use c, hc_unit, hc;
 · intro h
 obtain ⟨u, hu, hw⟩ := h;
 have := normQ2_smul_bell u; simp_all +decide [ Zsqrtd.norm_eq_one_iff' ] ;
 exact ⟨ bell_theory _ |>.2 ⟨ u, rfl ⟩ |>.1, bell_theory _ |>.2 ⟨ u, rfl ⟩ |>.2.1, bell_theory _ |>.2 ⟨ u, rfl ⟩ |>.2.2, by rintro ⟨ ⟩ ⟩

end BWArith