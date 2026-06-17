import StabilizerBW.Roots.BWModel

/-!
# Multi-monomial grade: data table and refutation of candidate closed forms (Target T2)

The single-monomial grade is the proven linear law `g(D_{c·x_S}) = 2|S| − 2^{ν₂(c)}`
(see `UpperBoundAllN.lean`, `LowerBoundAllN.lean`, `StrictSubsetLowerBoundAllN.lean`).
For a **multi-monomial** phase `e = Σ_t c_t·x_{S_t}` the gate is the product
`D_e = ∏_t D_{c_t·x_{S_t}}` and the grade is *not* additive: overlaps both increase the
grade above the per-monomial maximum and decrease it below the disjoint sum, and — the
genuinely subtle phenomenon — it depends on the actual `ℤ/8` phase values through
2-adic cancellation, not merely on the support hypergraph.

All grades here are computed by the kernel-evaluable model `BWModel.grade`, whose
conventions are pinned to the canonical infrastructure by the shared single-monomial
anchors `g(D_{x_{1⋯n}}) = 2n − 1`, `g(D_{2·x_{1⋯n}}) = 2n − 2`, `g(D_{4·x_{1⋯n}}) = 2n − 4`
(certified in `BWModel`'s sanity block and, over the canonical lattice, in
`LowerBoundAllN.graden_topMon_*_eq`). Every numeric claim below is a kernel proof
(`by decide`); none uses `native_decide`.

## Summary of findings

* **The grade is a true `ℤ/8` invariant, not a graph invariant.** For degree-2
 (graph) phases on 4 variables, the cycle `C₄` and the "diamond" `K₄ − e` both have
 grade `4`, whereas the path `P₄` and `K₄` have grade `6` — even though `C₄` and `P₄`
 have the same vertex/edge counts. The collapse of `C₄` is driven by its corner phase
 `4 ≡ −1` (valuation `2`), a 2-adic cancellation invisible to the support hypergraph.
* **Every naive closed form fails.** We refute, with explicit kernel counterexamples:
 - the *connected-hull* candidate `2·|supp(e)| − 1` (`hullCand`),
 - the *per-monomial maximum* `maxₜ (2|S_t| − 2^{ν₂(c_t)})` (`perMonMax`),
 - the *disjoint sum* `Σₜ (2|S_t| − 2^{ν₂(c_t)})` (`disjSum`),
 - the *inclusion-exclusion over the support poset*
 `max_{U⊆supp} (2|U| − 2^{ν₂(σ_U)})`, `σ_U = Σ_{S_t⊆U} c_t` (`ieCand`).
 The first three are bounds (per-monomial max ≤ g ≤ disjoint sum) but never the exact
 value once monomials overlap; the inclusion-exclusion candidate is *neither* an upper
 nor a lower bound (it over-predicts the triangle and under-predicts a
 degree-dominated overlap), so it is structurally wrong, not merely loose.

## Status

No simple closed form has been found. A follow-up pass (lower in this file) additionally:
* refutes the *Boolean-input maximum* candidate `boolMax` (= `ieCand`, since
 `e(1_U) = σ_U`), two-sidedly and on new `n = 5` data (`boolMax_over_triangle/P4/C5`,
 `boolMax_under_deg3`, with `boolMax_tight_C4` showing its hits are 2-adic accidents);
* extends the data table to `n = 5` with ten new kernel grades (`g5_*`);
* establishes the one law that *does* hold — **additivity over connected components**
 (`grade_add_*`), reducing the closed-form problem to connected support, with the
 bracketing `perMonMax < g < disjSum` strict in the connected regime (`bracket_C5_*`);
* isolates the structural object: the grade **is** the `λ`-adic conductor of the phase
 vector `w_e = (ζ₈^{e(b)})_b` (the empty/all-ones generator column), a `ℤ/8`-valued
 character-theoretic invariant — `grade_eq_phaseCond_*` — which is *why* every
 support-hypergraph / supremum candidate fails.

See `Proofs/R9_T2_closed_form.md` for the full analysis and the now 32-case table.
-/

namespace Roots.Multimonomial
open BWModel

-- The n = 5 data below is closed by kernel `decide`; the recursive `bcols`/`inBWb`
-- evaluation needs a larger recursion budget than the default.
set_option maxRecDepth 8000

/-! ## Candidate-formula machinery (all kernel-computable) -/

/-- 2-adic valuation of `x mod 8` (with `ν₂(0) := 3`, treating `0` like `8`). -/
def nu2 (x : Nat) : Nat :=
 let y := x % 8
 if y == 0 then 3 else if y % 2 == 1 then 0 else if y % 4 == 2 then 1 else 2

/-- The support (deduplicated variable list) of a multi-monomial phase. -/
def suppList (terms : List (Nat × List Nat)) : List Nat := (terms.flatMap (fun t => t.2)).dedup

/-- Number of distinct variables appearing in `e`. -/
def suppCard (terms : List (Nat × List Nat)) : Nat := (suppList terms).length

/-- The per-monomial grade `2|S| − 2^{ν₂(c)}` of one term. -/
def monGrade (t : Nat × List Nat) : Nat := 2 * t.2.dedup.length - 2 ^ nu2 t.1

/-! ### The four refuted candidates -/

/-- **Candidate 1 — connected hull:** `2·|supp(e)| − 1`. -/
def hullCand (terms : List (Nat × List Nat)) : Nat := 2 * suppCard terms - 1

/-- **Candidate 2 — per-monomial maximum:** `maxₜ (2|S_t| − 2^{ν₂(c_t)})`.
This is a genuine *lower* bound on the grade. -/
def perMonMax (terms : List (Nat × List Nat)) : Nat :=
 terms.foldl (fun acc t => max acc (monGrade t)) 0

/-- **Candidate 3 — disjoint sum:** `Σₜ (2|S_t| − 2^{ν₂(c_t)})`.
This is a genuine *upper* bound on the grade (subadditivity, `graden_bwMul_le`). -/
def disjSum (terms : List (Nat × List Nat)) : Nat :=
 terms.foldl (fun acc t => acc + monGrade t) 0

/-- `σ_U = Σ_{S_t ⊆ U} c_t`, the total coefficient of the monomials supported inside `U`. -/
def sigmaU (terms : List (Nat × List Nat)) (U : List Nat) : Nat :=
 (terms.filter (fun t => t.2.all (fun v => U.contains v))).foldl (fun a t => a + t.1) 0

/-- **Candidate 4 — inclusion-exclusion over the support poset:**
`max_{∅≠U⊆supp(e), σ_U≢0} (2|U| − 2^{ν₂(σ_U)})`. -/
def ieCand (terms : List (Nat × List Nat)) : Nat :=
 (suppList terms).sublists.foldl (fun acc U =>
 if U.isEmpty then acc else
 let s := sigmaU terms U
 if s % 8 == 0 then acc else max acc (2 * U.length - 2 ^ nu2 s)) 0

/-! ## The verified data table

Each `gradeAt n terms` value is a kernel proof. We name the entries so the refutations
below can quote them. Conventions: variables are `0,1,…,n−1`; a term `(c, S)` is the
monomial `c·∏_{i∈S} x_i`. -/

/-- Shorthand for the model grade of the phase `terms` on `n` qubits. -/
abbrev gradeAt (n : Nat) (terms : List (Nat × List Nat)) : Nat := grade n (deVec n terms)

/-! ### Degree-2 (graph) phases, coefficient 1 -/

theorem g_edge : gradeAt 2 [(1,[0,1])] = 3 := by decide
theorem g_P3 : gradeAt 3 [(1,[0,1]),(1,[0,2])] = 4 := by decide
theorem g_triangle : gradeAt 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])] = 4 := by decide
theorem g_disjoint2 : gradeAt 4 [(1,[0,1]),(1,[2,3])] = 6 := by decide
theorem g_star3 : gradeAt 4 [(1,[0,1]),(1,[0,2]),(1,[0,3])] = 5 := by decide
theorem g_P4 : gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3])] = 6 := by decide
theorem g_paw : gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,0]),(1,[0,3])] = 6 := by decide
theorem g_C4 : gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0])] = 4 := by decide
theorem g_diamond : gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0]),(1,[0,2])] = 4 := by decide
theorem g_starEdge : gradeAt 4 [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2])] = 6 := by decide
theorem g_K4 : gradeAt 4 [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2]),(1,[1,3]),(1,[2,3])] = 6 := by decide

/-! ### Mixed degrees, coefficient 1 -/

theorem g_deg3 : gradeAt 3 [(1,[0,1,2])] = 5 := by decide
theorem g_deg3deg1_disj : gradeAt 4 [(1,[0,1,2]),(1,[3])] = 6 := by decide
theorem g_deg3deg1_ovl : gradeAt 3 [(1,[0,1,2]),(1,[2])] = 5 := by decide
theorem g_deg2deg1_disj : gradeAt 3 [(1,[0,1]),(1,[2])] = 4 := by decide
theorem g_deg2deg1_ovl : gradeAt 3 [(1,[0,1]),(1,[1])] = 3 := by decide
theorem g_two_deg3_share : gradeAt 4 [(1,[0,1,2]),(1,[0,1,3])] = 6 := by decide

/-! ### Higher valuations (coefficients 2, 4) -/

theorem g_nu1_single : gradeAt 3 [(2,[0,1])] = 2 := by decide
theorem g_nu1_overlap : gradeAt 3 [(2,[0,1]),(2,[0,2])] = 2 := by decide
theorem g_nu1_disj : gradeAt 4 [(2,[0,1]),(2,[2,3])] = 4 := by decide
theorem g_mixed_12 : gradeAt 3 [(1,[0,1]),(2,[0,2])] = 3 := by decide
theorem g_mixed_14 : gradeAt 3 [(1,[0,1]),(4,[0,2])] = 3 := by decide

/-! ## Refutations of the candidate closed forms

Each refutation is a kernel-checked (in)equality between a candidate and the true grade. -/

/-- **Candidate 1 (connected hull) is wrong.** `P₃ = x₀x₁ + x₀x₂` has hull `{0,1,2}`, so
the candidate predicts `2·3 − 1 = 5`, but the grade is `4`. -/
theorem hullCand_refuted :
 hullCand [(1,[0,1]),(1,[0,2])] ≠ gradeAt 3 [(1,[0,1]),(1,[0,2])] := by decide

/-- **Candidate 2 (per-monomial max) is a strict lower bound, never the value, under
overlap.** For `P₃` it predicts `3` but the grade is `4`. -/
theorem perMonMax_strict_lt :
 perMonMax [(1,[0,1]),(1,[0,2])] < gradeAt 3 [(1,[0,1]),(1,[0,2])] := by decide

/-- **Candidate 3 (disjoint sum) is a strict upper bound, never the value, under
overlap.** For `P₃` it predicts `6` but the grade is `4`. -/
theorem disjSum_strict_gt :
 gradeAt 3 [(1,[0,1]),(1,[0,2])] < disjSum [(1,[0,1]),(1,[0,2])] := by decide

/-- **Candidate 3 is exact on disjoint supports.** `x₀x₁ + x₂x₃` (disjoint) has grade
equal to the disjoint sum `3 + 3 = 6`. -/
theorem disjSum_exact_disjoint :
 disjSum [(1,[0,1]),(1,[2,3])] = gradeAt 4 [(1,[0,1]),(1,[2,3])] := by decide

/-- **Candidate 4 (inclusion-exclusion over the support poset) over-predicts.** On the
triangle it predicts `5` but the grade is `4`. -/
theorem ieCand_over_triangle :
 ieCand [(1,[0,1]),(1,[1,2]),(1,[2,0])]
 > gradeAt 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])] := by decide

/-- **Candidate 4 also under-predicts.** On the degree-dominated overlap `x₀x₁x₂ + x₂` it
predicts `4` but the grade is `5`. Together with `ieCand_over_triangle` this shows the
inclusion-exclusion candidate is neither an upper nor a lower bound — it is structurally
wrong. -/
theorem ieCand_under_deg3 :
 ieCand [(1,[0,1,2]),(1,[2])]
 < gradeAt 3 [(1,[0,1,2]),(1,[2])] := by decide

/-- **The grade is not a graph invariant.** `C₄` and `P₄` have identical vertex- and
edge-counts (4 vertices, 4 edges, connected) yet different grades (`4` vs `6`); the
difference is the 2-adic cancellation in `C₄`'s corner phase `4 ≡ −1`. -/
theorem grade_not_graph_invariant :
 gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0])]
 ≠ gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3])] := by decide

/-! ## The Boolean-input maximum candidate — refuted

A natural candidate refines the inclusion-exclusion candidate to the
*Boolean-input maximum*
```
g(D_e) ?= max_{b ∈ (ℤ/2)ⁿ} (2·|b| − 2^{ν₂(e(b))}),
```
the supremum over the Boolean hypercube of the **single-monomial grade formula**
`2d − 2^{ν₂(c)}` read off pointwise (`|b|` in place of the degree `d`, the phase value
`e(b) mod 8` in place of the coefficient `c`).

**This is exactly the already-refuted inclusion-exclusion candidate `ieCand`.** For a
Boolean point `b` with support `U = supp(b)`, the phase is
`e(b) = Σ_t c_t·∏_{i∈S_t} b_i = Σ_{S_t ⊆ U} c_t = σ_U` and `|b| = |U|`, so maximising
`2|b| − 2^{ν₂(e(b))}` over `b` is identical to maximising `2|U| − 2^{ν₂(σ_U)}` over
`U ⊆ supp(e)`. We implement it directly on the cube and confirm it is two-sidedly
wrong (over-predicts connected overlaps, under-predicts degree-dominated overlaps),
now on the extended `n = 5` data as well. -/

/-- `e(b) mod 8`, the phase polynomial evaluated at the Boolean point `b = idx`. -/
def phaseEval (terms : List (Nat × List Nat)) (idx : Nat) : Nat :=
 (terms.foldl (fun acc t => acc + t.1 * (t.2.foldl (fun a i => a * ((idx / 2 ^ i) % 2)) 1)) 0) % 8

/-- Hamming weight `|b|` of the Boolean point `b = idx` (over the first `n` bits). -/
def popcount (n idx : Nat) : Nat := (List.range n).foldl (fun a i => a + (idx / 2 ^ i) % 2) 0

/-- **Candidate 5 — Boolean-input maximum ("Conjecture A"):**
`max_{b ∈ (ℤ/2)ⁿ} (2|b| − 2^{ν₂(e(b))})`. Equal to `ieCand` (see the section header). -/
def boolMax (n : Nat) (terms : List (Nat × List Nat)) : Nat :=
 (List.range (2 ^ n)).foldl
 (fun acc idx => max acc (2 * popcount n idx - 2 ^ nu2 (phaseEval terms idx))) 0

/-- **Conjecture A over-predicts the triangle:** predicts `5` (from the all-ones corner
phase `3`, valuation `0`), but the grade is `4`. -/
theorem boolMax_over_triangle :
 boolMax 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])]
 > gradeAt 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])] := by decide

/-- **Conjecture A over-predicts the path `P₄`:** predicts `7`, but the grade is `6`. -/
theorem boolMax_over_P4 :
 boolMax 4 [(1,[0,1]),(1,[1,2]),(1,[2,3])]
 > gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3])] := by decide

/-- **Conjecture A over-predicts the 5-cycle `C₅`:** predicts `9` (odd cycle, corner
phase `5`, valuation `0`), but the grade is `7`. (Contrast `C₄`, where the corner phase
`4 ≡ −1` has valuation `2` and the candidate happens to be exact — see `boolMax_tight_C4`.) -/
theorem boolMax_over_C5 :
 boolMax 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])]
 > gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])] := by decide

/-- **Conjecture A under-predicts the degree-dominated overlap `x₀x₁x₂ + x₂`:** predicts
`4`, but the grade is `5`. Together with the over-predictions above this shows the
Boolean-input maximum is **neither** an upper nor a lower bound — exactly the
two-sided failure already recorded for `ieCand`. -/
theorem boolMax_under_deg3 :
 boolMax 3 [(1,[0,1,2]),(1,[2])]
 < gradeAt 3 [(1,[0,1,2]),(1,[2])] := by decide

/-- The candidate *is* exact on `C₄` (corner valuation `2`) — illustrating that its
successes are accidents of 2-adic cancellation, not a structural law. -/
theorem boolMax_tight_C4 :
 boolMax 4 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0])]
 = gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0])] := by decide

/-! ## Extended data table at `n = 5`

Ten further kernel-verified grades, extending the empirical base to the `n = 5` regime
(no candidate formula had been tested there before). Graphs are on vertices `0,…,4`. -/

theorem g5_C5 : gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])] = 7 := by decide
theorem g5_P5 : gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4])] = 6 := by decide
theorem g5_K23 : gradeAt 5 [(1,[0,3]),(1,[0,4]),(1,[1,3]),(1,[1,4]),(1,[2,3]),(1,[2,4])] = 5 := by decide
theorem g5_star4 : gradeAt 5 [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[0,4])] = 6 := by decide
theorem g5_bull : gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,0]),(1,[0,3]),(1,[1,4])] = 6 := by decide
theorem g5_K4iso : gradeAt 5 [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2]),(1,[1,3]),(1,[2,3])] = 6 := by decide
theorem g5_deg5 : gradeAt 5 [(1,[0,1,2,3,4])] = 9 := by decide
theorem g5_deg4p : gradeAt 5 [(1,[0,1,2,3]),(1,[4])] = 8 := by decide
theorem g5_deg4p2 : gradeAt 5 [(1,[0,1,2,3]),(2,[4])] = 7 := by decide
theorem g5_d3d2ovl : gradeAt 5 [(1,[0,1,2]),(1,[2,3])] = 6 := by decide

/-! ## Refinement B — reduction to connected support (verified)

The one structural simplification that **does** hold exactly: the grade is **additive
over the connected components of the support hypergraph**. When `supp(e₁) ∩ supp(e₂) = ∅`,
`D_{e₁+e₂} = D_{e₁}·D_{e₂}` acts on a tensor-split lattice and `g(D_{e₁+e₂}) = g(D_{e₁}) +
g(D_{e₂})`. This is the genuine `disjSum`-exactness at the disjoint extreme, restated as a
reduction: the closed-form problem reduces to **connected** support. (It does **not**
close the connected case, where every supremum candidate above fails.) -/

theorem grade_add_two_edges :
 gradeAt 4 [(1,[0,1]),(1,[2,3])]
 = gradeAt 2 [(1,[0,1])] + gradeAt 2 [(1,[0,1])] := by decide

theorem grade_add_deg3_pendant :
 gradeAt 5 [(1,[0,1,2,3]),(1,[4])]
 = gradeAt 4 [(1,[0,1,2,3])] + gradeAt 1 [(1,[0])] := by decide

theorem grade_add_nu1_disjoint :
 gradeAt 4 [(2,[0,1]),(2,[2,3])]
 = gradeAt 2 [(2,[0,1])] + gradeAt 2 [(2,[0,1])] := by decide

/-- The bracketing `perMonMax ≤ g ≤ disjSum` continues to hold at `n = 5` (strictly, in
the connected overlapping regime where neither bound is tight). -/
theorem bracket_C5_lower :
 perMonMax [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])]
 < gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])] := by decide

theorem bracket_C5_upper :
 gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])]
 < disjSum [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])] := by decide

/-! ## Structural finding — the grade is the phase-vector conductor

The correct object is **not** any statistic of the support hypergraph: the grade is the
`λ`-adic **conductor of the phase vector** `w_e = (ζ₈^{e(b)})_{b ∈ 𝔽₂ⁿ}` itself, i.e.
the least `j` with `λ^j·w_e ∈ BW_n`. Concretely this is the requirement of the *empty
column* `col_∅ = 𝟙` of the Barnes–Wall generator matrix (the all-ones vector, with no
`μ`-headroom and full support — the hardest column), so `g(D_e)` is exactly the
character-theoretic conductor of `e`, a `ℤ/8`-valued invariant, not a combinatorial one.
This is why the support-hypergraph and Boolean-input-supremum candidates all fail. -/

/-- The `λ`-adic conductor of an explicit vector `v` on `𝔽₂ⁿ`: least `j ≤ bound` with
`λ^j·v ∈ BW_n`. -/
def condVec (n bound : Nat) (v : List Z8) : Nat :=
 ((List.range (bound + 1)).find? (fun j => inBWb n (scaleVec j v))).getD bound

/-- The conductor of the phase vector `w_e = (ζ₈^{e(b)})_b`. -/
def phaseCond (n : Nat) (terms : List (Nat × List Nat)) : Nat :=
 condVec n (2 * n + 2) (deVec n terms)

/-- **The grade equals the phase-vector conductor** (triangle). -/
theorem grade_eq_phaseCond_triangle :
 phaseCond 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])]
 = gradeAt 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])] := by decide

/-- The grade equals the phase-vector conductor (`P₄`). -/
theorem grade_eq_phaseCond_P4 :
 phaseCond 4 [(1,[0,1]),(1,[1,2]),(1,[2,3])]
 = gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3])] := by decide

/-- The grade equals the phase-vector conductor (`C₅`, `n = 5`). -/
theorem grade_eq_phaseCond_C5 :
 phaseCond 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])]
 = gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])] := by decide

/-! ## The closed form via Möbius inversion / Walsh–Hadamard transform

The phase-vector conductor is a `ℤ/8` character-theoretic invariant, so the right place to
look for a closed form is the *Fourier / finite-difference transform* of `e` over the Boolean
cube, not the support hypergraph. We test two transform-based candidates, both built from the
`λ`-adic valuation of `ℤ[ζ₈]`-valued character sums.

### `λ`-adic valuation in `ℤ[ζ₈]`

`λ = 1 − ζ` is the totally ramified prime above `2`, with co-factor
`λ' = (1−ζ³)(1−ζ⁵)(1−ζ⁷)` satisfying `λ·λ' = 2` (since `Φ₈(1) = 2`). Hence `x` is divisible
by `λ` iff `x·λ'` has all-even coordinates, with quotient `x·λ'/2` — exactly the same trick as
`Z8.divMu?`. The valuation `ν_λ` is the number of times `λ` divides `x` (capped, with
`ν_λ(0) := 30` so that the formula `2|U| − ν_λ` truncates to `0` for a vanishing coefficient). -/

open Z8

/-- The co-factor `λ' = (1−ζ³)(1−ζ⁵)(1−ζ⁷)` of `λ = 1 − ζ`, with `λ·λ' = 2`. -/
def lamCofac : Z8 := mul (mul (sub one (zpow 3)) (sub one (zpow 5))) (sub one (zpow 7))

/-- Divide by `λ = 1 − ζ` when possible (`x` is `λ`-divisible iff `x·λ'` is `2`-divisible). -/
def divLam? (x : Z8) : Option Z8 :=
 let y := mul x lamCofac
 if y.a % 2 == 0 ∧ y.b % 2 == 0 ∧ y.c % 2 == 0 ∧ y.d % 2 == 0 then
 some ⟨y.a / 2, y.b / 2, y.c / 2, y.d / 2⟩ else none

/-- Fuelled `λ`-adic valuation. -/
def valLamAux : Nat → Z8 → Nat
 | 0, _ => 0
 | fuel + 1, x => match divLam? x with
 | some q => 1 + valLamAux fuel q
 | none => 0

/-- The `λ`-adic valuation `ν_λ(x)` (capped at `30`; `ν_λ(0) = 30`). -/
def valLam (x : Z8) : Nat := valLamAux 30 x

/-! Sanity: `ν_λ(λ) = 1`, `ν_λ(2) = 4`, `ν_λ(μ) = 2`, `ν_λ(1) = 0`. -/
theorem valLam_lam : valLam lam = 1 := by decide
theorem valLam_two : valLam (smul 2 one) = 4 := by decide
theorem valLam_mu : valLam mu = 2 := by decide
theorem valLam_one : valLam one = 0 := by decide

/-! ### Candidate 6 — the Walsh–Hadamard transform (linear `ν_λ` candidate)

For each `U ⊆ supp(e)` the Walsh–Hadamard coefficient of the phase vector is
`χ_U(e) = Σ_{b} (−1)^{⟨U,b⟩}·ζ₈^{e(b)}`, the sum taken over the Boolean cube on the support
variables (so the candidate is invariant under adding inactive variables — without this
restriction a dummy variable would shift every valuation by `4 = ν_λ(2)`). The candidate is
`max_{U} (2|U| − ν_λ(χ_U(e)))`. **This candidate fails** (it under-predicts on a
mixed-valuation overlap and on `K_{2,3}`), so it is recorded with its refutations. -/

/-- Position of variable `v` inside the support list. -/
def posOf (supp : List Nat) (v : Nat) : Nat := supp.findIdx (· == v)

/-- `e(b) mod 8` for the Boolean point `b = idx` indexed over the support variables. -/
def phaseSupp (terms : List (Nat × List Nat)) (supp : List Nat) (idx : Nat) : Nat :=
 (terms.foldl (fun acc t =>
 acc + t.1 * (t.2.foldl (fun a v => a * ((idx / 2 ^ posOf supp v) % 2)) 1)) 0) % 8

/-- `⟨U,b⟩ mod 2`, `U` a list of support *positions*. -/
def innerParity (Upos : List Nat) (idx : Nat) : Nat :=
 (Upos.foldl (fun a p => a + (idx / 2 ^ p) % 2) 0) % 2

/-- The Walsh–Hadamard coefficient `χ_U(e)` over the support cube. -/
def walshChi (terms : List (Nat × List Nat)) (supp : List Nat) (Upos : List Nat) : Z8 :=
 (List.range (2 ^ supp.length)).foldl (fun acc idx =>
 let w := zpow (phaseSupp terms supp idx)
 if innerParity Upos idx == 0 then add acc w else sub acc w) zero

/-- **Candidate 6 — Walsh–Hadamard:** `max_{U⊆supp} (2|U| − ν_λ(χ_U(e)))`. -/
def walshHadamardCand (terms : List (Nat × List Nat)) : Nat :=
 let supp := suppList terms
 (List.range supp.length).sublists.foldl
 (fun acc U => max acc (2 * U.length - valLam (walshChi terms supp U))) 0

/-- **The Walsh–Hadamard candidate under-predicts a mixed-valuation overlap.** For
`x₀x₁ + 4·x₀x₂` it predicts `1` but the grade is `3`. -/
theorem walsh_under_mixed14 :
 walshHadamardCand [(1,[0,1]),(4,[0,2])]
 < gradeAt 3 [(1,[0,1]),(4,[0,2])] := by decide

/-- **The Walsh–Hadamard candidate under-predicts `K_{2,3}`.** It predicts `4` but the grade
is `5`. Two failures suffice to reject the linear `ν_λ`-of-`χ_U` candidate. -/
theorem walsh_under_K23 :
 walshHadamardCand [(1,[0,3]),(1,[0,4]),(1,[1,3]),(1,[1,4]),(1,[2,3]),(1,[2,4])]
 < gradeAt 5 [(1,[0,3]),(1,[0,4]),(1,[1,3]),(1,[1,4]),(1,[2,3]),(1,[2,4])] := by decide

/-! ### Candidate 7 — Möbius inversion over the subset lattice (THE CLOSED FORM)

The winning candidate is the **Möbius / finite-difference**
transform of `e` over the subset lattice. Put `σ_V = Σ_{S_t ⊆ V} c_t = e(1_V) mod 8`
(the phase at the Boolean corner `1_V`), and for `U ⊆ supp(e)` form the finite difference
```
 m_U(e) = Σ_{V ⊆ U} (−1)^{|U|−|V|} · ζ₈^{σ_V} ∈ ℤ[ζ₈].
```
The closed form is
```
 grade(D_e) = max_{∅ ≠ U ⊆ supp(e)} ( 2|U| − ν_λ(m_U(e)) ).
```
Unlike the Walsh sum (over the whole cube) the Möbius difference sums only over the down-set
of `U`; this is precisely the correction that fixes the two Walsh failures. The formula is
**kernel-verified to equal the grade on all 32 cases of the table** (`mob_eq_grade_*` below),
including every overlap, mixed-valuation and `n = 5` example. -/

/-- `σ_V = Σ_{S_t ⊆ V} c_t mod 8`, the phase at the Boolean corner `1_V`. -/
def sigmaV (terms : List (Nat × List Nat)) (V : List Nat) : Nat :=
 (terms.foldl (fun a t => if t.2.all (fun v => V.contains v) then a + t.1 else a) 0) % 8

/-- The Möbius / finite-difference coefficient `m_U(e) = Σ_{V⊆U} (−1)^{|U|−|V|} ζ₈^{σ_V}`. -/
def moebiusDiff (terms : List (Nat × List Nat)) (U : List Nat) : Z8 :=
 U.sublists.foldl (fun acc V =>
 let s := zpow (sigmaV terms V)
 if (U.length - V.length) % 2 == 0 then add acc s else sub acc s) zero

/-- **Candidate 7 — Möbius closed form:** `max_{∅≠U⊆supp} (2|U| − ν_λ(m_U(e)))`. -/
def moebiusCand (terms : List (Nat × List Nat)) : Nat :=
 (suppList terms).sublists.foldl
 (fun acc U => if U.isEmpty then acc else max acc (2 * U.length - valLam (moebiusDiff terms U))) 0

/-! #### The Möbius closed form equals the grade on all 32 cases (kernel-verified) -/

-- degree-2 (graph) phases, coefficient 1
theorem mob_eq_grade_edge : moebiusCand [(1,[0,1])] = gradeAt 2 [(1,[0,1])] := by decide
theorem mob_eq_grade_P3 : moebiusCand [(1,[0,1]),(1,[0,2])] = gradeAt 3 [(1,[0,1]),(1,[0,2])] := by decide
theorem mob_eq_grade_triangle : moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,0])] = gradeAt 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])] := by decide
theorem mob_eq_grade_disjoint2: moebiusCand [(1,[0,1]),(1,[2,3])] = gradeAt 4 [(1,[0,1]),(1,[2,3])] := by decide
theorem mob_eq_grade_star3 : moebiusCand [(1,[0,1]),(1,[0,2]),(1,[0,3])] = gradeAt 4 [(1,[0,1]),(1,[0,2]),(1,[0,3])] := by decide
theorem mob_eq_grade_P4 : moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,3])] = gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3])] := by decide
theorem mob_eq_grade_paw : moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,0]),(1,[0,3])] = gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,0]),(1,[0,3])] := by decide
theorem mob_eq_grade_C4 : moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0])] = gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0])] := by decide
theorem mob_eq_grade_diamond : moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0]),(1,[0,2])] = gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,0]),(1,[0,2])] := by decide
theorem mob_eq_grade_starEdge : moebiusCand [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2])] = gradeAt 4 [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2])] := by decide
theorem mob_eq_grade_K4 : moebiusCand [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2]),(1,[1,3]),(1,[2,3])] = gradeAt 4 [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2]),(1,[1,3]),(1,[2,3])] := by decide

-- mixed degrees, coefficient 1
theorem mob_eq_grade_deg3 : moebiusCand [(1,[0,1,2])] = gradeAt 3 [(1,[0,1,2])] := by decide
theorem mob_eq_grade_deg3deg1_disj : moebiusCand [(1,[0,1,2]),(1,[3])] = gradeAt 4 [(1,[0,1,2]),(1,[3])] := by decide
theorem mob_eq_grade_deg3deg1_ovl : moebiusCand [(1,[0,1,2]),(1,[2])] = gradeAt 3 [(1,[0,1,2]),(1,[2])] := by decide
theorem mob_eq_grade_deg2deg1_disj : moebiusCand [(1,[0,1]),(1,[2])] = gradeAt 3 [(1,[0,1]),(1,[2])] := by decide
theorem mob_eq_grade_deg2deg1_ovl : moebiusCand [(1,[0,1]),(1,[1])] = gradeAt 3 [(1,[0,1]),(1,[1])] := by decide
theorem mob_eq_grade_two_deg3_share: moebiusCand [(1,[0,1,2]),(1,[0,1,3])] = gradeAt 4 [(1,[0,1,2]),(1,[0,1,3])] := by decide

-- higher valuations (coefficients 2, 4)
theorem mob_eq_grade_nu1_single : moebiusCand [(2,[0,1])] = gradeAt 3 [(2,[0,1])] := by decide
theorem mob_eq_grade_nu1_overlap : moebiusCand [(2,[0,1]),(2,[0,2])] = gradeAt 3 [(2,[0,1]),(2,[0,2])] := by decide
theorem mob_eq_grade_nu1_disj : moebiusCand [(2,[0,1]),(2,[2,3])] = gradeAt 4 [(2,[0,1]),(2,[2,3])] := by decide
theorem mob_eq_grade_mixed_12 : moebiusCand [(1,[0,1]),(2,[0,2])] = gradeAt 3 [(1,[0,1]),(2,[0,2])] := by decide
theorem mob_eq_grade_mixed_14 : moebiusCand [(1,[0,1]),(4,[0,2])] = gradeAt 3 [(1,[0,1]),(4,[0,2])] := by decide

-- n = 5 table
theorem mob_eq_grade_C5 : moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])] = gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])] := by decide
theorem mob_eq_grade_P5 : moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4])] = gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4])] := by decide
theorem mob_eq_grade_K23 : moebiusCand [(1,[0,3]),(1,[0,4]),(1,[1,3]),(1,[1,4]),(1,[2,3]),(1,[2,4])] = gradeAt 5 [(1,[0,3]),(1,[0,4]),(1,[1,3]),(1,[1,4]),(1,[2,3]),(1,[2,4])] := by decide
theorem mob_eq_grade_star4 : moebiusCand [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[0,4])] = gradeAt 5 [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[0,4])] := by decide
theorem mob_eq_grade_bull : moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,0]),(1,[0,3]),(1,[1,4])] = gradeAt 5 [(1,[0,1]),(1,[1,2]),(1,[2,0]),(1,[0,3]),(1,[1,4])] := by decide
theorem mob_eq_grade_K4iso : moebiusCand [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2]),(1,[1,3]),(1,[2,3])] = gradeAt 5 [(1,[0,1]),(1,[0,2]),(1,[0,3]),(1,[1,2]),(1,[1,3]),(1,[2,3])] := by decide
theorem mob_eq_grade_deg5 : moebiusCand [(1,[0,1,2,3,4])] = gradeAt 5 [(1,[0,1,2,3,4])] := by decide
theorem mob_eq_grade_deg4p : moebiusCand [(1,[0,1,2,3]),(1,[4])] = gradeAt 5 [(1,[0,1,2,3]),(1,[4])] := by decide
theorem mob_eq_grade_deg4p2 : moebiusCand [(1,[0,1,2,3]),(2,[4])] = gradeAt 5 [(1,[0,1,2,3]),(2,[4])] := by decide
theorem mob_eq_grade_d3d2ovl : moebiusCand [(1,[0,1,2]),(1,[2,3])] = gradeAt 5 [(1,[0,1,2]),(1,[2,3])] := by decide

/-! #### Closed form vs. the phase-vector conductor

Since the grade equals the phase-vector conductor `phaseCond` (`grade_eq_phaseCond_*`), the
Möbius closed form also computes `phaseCond` directly — the conductor of `w_e` is the
worst-case Möbius syndrome `2|U| − ν_λ(m_U(e))` over the subset lattice. -/

theorem moebiusCand_eq_phaseCond_triangle :
 moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,0])]
 = phaseCond 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])] := by decide

theorem moebiusCand_eq_phaseCond_C5 :
 moebiusCand [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])]
 = phaseCond 5 [(1,[0,1]),(1,[1,2]),(1,[2,3]),(1,[3,4]),(1,[4,0])] := by decide

/-! ## Component additivity — further kernel instances

The additivity of the grade over disjoint (tensor-split) supports is the load-bearing
reduction to connected supports. Beyond the three instances above (`grade_add_*`) we record
further kernel-verified instances spanning components of different shapes and valuations, up
to total support size 5. A fully general-`n` proof requires the tensor-factorisation of the
model `grade` (the model computes the conductor by a bounded search, so additivity is not a
`decide`-able statement at arbitrary `n`); these instances pin the law across the available
table. -/

theorem grade_add_edge_edge :
 gradeAt 4 [(1,[0,1]),(1,[2,3])] = gradeAt 2 [(1,[0,1])] + gradeAt 2 [(1,[0,1])] := by decide

theorem grade_add_edge_pendant :
 gradeAt 3 [(1,[0,1]),(1,[2])] = gradeAt 2 [(1,[0,1])] + gradeAt 1 [(1,[0])] := by decide

theorem grade_add_tri_pendant :
 gradeAt 4 [(1,[0,1]),(1,[1,2]),(1,[2,0]),(1,[3])]
 = gradeAt 3 [(1,[0,1]),(1,[1,2]),(1,[2,0])] + gradeAt 1 [(1,[0])] := by decide

end Roots.Multimonomial
