import StabilizerBW.Roots.BWn
import StabilizerBW.Roots.BW3

/-!
# The all-`n` upper bound of the linear closed form, for every `ν` (Target T1)

This file kernel-checks the hand-proved upper bound

  `g(D_{c·x_S}) ≤ max(0, 2|S| − 2^{ν₂(c mod 8)})`

at **every** `n` and for **every** valuation `ν`, complementing the `ν = 0` case
`bwT_graden_le` already in `BWn.lean`.  The proof is the two-step factorization argument
of `Proofs/UpperBoundAllN_HandProof.md`:

* **T1.1 (projector cost, `topProj_gradeLE`).**  For the rank-`2^{n−d}` coordinate
  projector `Q` requiring the leading `d` qubits to be `1`,
  `λ^{2d}·Q·v ∈ BW_n` for every `v ∈ BW_n`.  Proved by induction on the number of
  constrained qubits, peeling the outermost qubit through the free-module
  decomposition and converting each `λ²` into a `(1+i)` factor via `Z8.lam_sq`.

* **T1.2 (cyclotomic scalar valuation).**  `ζ₈^c − 1 = λ^{2^ν}·u_c` for an explicit
  unit `u_c` (`scalar_zeta`, `scalar_iu`, `scalar_negOne`).

* **T1.3 (upper bound, `topMon_gradeLE`).**  Factorize the monomial character
  `D = I + (ζ₈^c − 1)·Q`.  For `k = max(0, 2d − 2^ν)`, `λ^k·D·v` splits as
  `λ^k·v + u_c·λ^{k+2^ν}·Q·v`; the first term is in `BW_n` for `k ≥ 0`, and the second
  because `k + 2^ν ≥ 2d` and T1.1.

The monomial is placed canonically on the **leading** `d` qubits (`S = {1,…,d}`,
identity on the remaining `m = n − d`).  By Clifford bit-permutation symmetry the grade
depends only on `d` and `ν`, so this canonical placement is the general single-monomial
case.  This generalizes `BWn.bwT` (the all-qubits `ν = 0` monomial).

As a corollary we record the all-`n` product (disjoint-support sum) subadditivity bound
`graden (D·E) ≤ graden D + graden E` (`graden_bwMul_le`).
-/

namespace Roots
open Z8

/-! ## Extra algebraic helper lemmas on `BW_n` -/

/-- Scaling by `1` is the identity. -/
theorem bwSmul_one (n : ℕ) (v : BWVec n) : bwSmul n 1 v = v := by
  induction n with
  | zero => show (1 : Z8) * (show Z8 from v) = v; exact one_mul _
  | succ m ih => obtain ⟨a, b⟩ := v; simp only [bwSmul_succ, ih]

/-- Scaling by `0` gives the zero vector. -/
theorem bwSmul_zero_scalar (n : ℕ) (v : BWVec n) : bwSmul n 0 v = bwZero n := by
  induction n with
  | zero => show (0 : Z8) * (show Z8 from v) = (0 : Z8); exact zero_mul _
  | succ m ih => obtain ⟨a, b⟩ := v; simp only [bwSmul_succ, ih, bwZero_succ]

/-- The zero diagonal kills everything: `0 · v = 0`. -/
theorem bwMul_bwZero (n : ℕ) (v : BWVec n) : bwMul n (bwZero n) v = bwZero n := by
  induction n with
  | zero => show (0 : Z8) * (show Z8 from v) = (0 : Z8); exact zero_mul _
  | succ m ih => obtain ⟨a, b⟩ := v; simp only [bwMul_succ, bwZero_succ, ih]

/-- The zero vector lies in `BW_n`. -/
theorem bwZero_inBW (n : ℕ) : inBW n (bwZero n) := by
  induction n with
  | zero => trivial
  | succ m ih =>
      refine ⟨ih, ih, bwZero m, ih, ?_⟩
      rw [bwZero_succ, bwSub_self, bwSmul_bwZero]

/-- `bwSub (bwZero) Y = (-1) · Y`. -/
theorem bwSub_bwZero_left (n : ℕ) (Y : BWVec n) : bwSub n (bwZero n) Y = bwSmul n (-1) Y := by
  induction n with
  | zero =>
      show (0 : Z8) - (show Z8 from Y) = (-1 : Z8) * (show Z8 from Y)
      ring
  | succ m ih => obtain ⟨a, b⟩ := Y; simp only [bwZero_succ, bwSub_succ, bwSmul_succ, ih]

/-- `bwAdd (bwId) (bwZero) = bwId`. -/
theorem bwAdd_bwId_bwZero (n : ℕ) : bwAdd n (bwId n) (bwZero n) = bwId n := by
  induction n with
  | zero => show (1 : Z8) + (0 : Z8) = 1; ring
  | succ m ih => simp only [bwId_succ, bwZero_succ, bwAdd_succ, ih]

/-- The identity diagonal has grade `0`. -/
theorem bwId_gradeLE_zero (n : ℕ) : gradeLEn n (bwId n) 0 := by
  unfold gradeLEn
  rw [pow_zero, bwSmul_one]
  intro v hv
  rw [bwId_mul]
  exact hv

/-- `bwMul` distributes over `bwAdd` in the operator slot. -/
theorem bwMul_bwAdd_left (n : ℕ) (A B v : BWVec n) :
    bwMul n (bwAdd n A B) v = bwAdd n (bwMul n A v) (bwMul n B v) := by
  induction n with
  | zero => exact add_mul (show Z8 from A) (show Z8 from B) (show Z8 from v)
  | succ m ih =>
      obtain ⟨A1, A2⟩ := A; obtain ⟨B1, B2⟩ := B; obtain ⟨v1, v2⟩ := v
      simp only [bwAdd_succ, bwMul_succ, ih]

/-- `bwMul` is associative (diagonal-operator composition then action). -/
theorem bwMul_assoc (n : ℕ) (A B v : BWVec n) :
    bwMul n (bwMul n A B) v = bwMul n A (bwMul n B v) := by
  induction n with
  | zero => exact mul_assoc (show Z8 from A) (show Z8 from B) (show Z8 from v)
  | succ m ih =>
      obtain ⟨A1, A2⟩ := A; obtain ⟨B1, B2⟩ := B; obtain ⟨v1, v2⟩ := v
      simp only [bwMul_succ, ih]

/-- Scalars on both factors collect into the product: `(rD)·(sE) = (rs)·(D·E)`. -/
theorem bwSmul_bwMul_both (n : ℕ) (r s : Z8) (D E : BWVec n) :
    bwMul n (bwSmul n r D) (bwSmul n s E) = bwSmul n (r * s) (bwMul n D E) := by
  induction n with
  | zero =>
      show (r * (show Z8 from D)) * (s * (show Z8 from E))
            = (r * s) * ((show Z8 from D) * (show Z8 from E))
      ring
  | succ m ih =>
      obtain ⟨D1, D2⟩ := D; obtain ⟨E1, E2⟩ := E
      simp only [bwSmul_succ, bwMul_succ, ih]

/-! ## T1.1 — the projector and its cost lemma -/

/-- The leading-`d`-qubit "all-ones" coordinate projector on `BW_n`: requires the first
`d` qubits to be `1`, identity on the remaining `n − d` qubits.  Rank `2^{n−d}`. -/
def topProj : (n d : ℕ) → BWVec n
  | 0, _ => bwId 0
  | n + 1, 0 => bwId (n + 1)
  | n + 1, d + 1 => (bwZero n, topProj n d)

@[simp] theorem topProj_zero_d (d : ℕ) : topProj 0 d = bwId 0 := rfl
@[simp] theorem topProj_succ_zero (n : ℕ) : topProj (n + 1) 0 = bwId (n + 1) := rfl
@[simp] theorem topProj_succ_succ (n d : ℕ) :
    topProj (n + 1) (d + 1) = (bwZero n, topProj n d) := rfl

/-- **T1.1 (projector cost).** `λ^{2d}·Q·v ∈ BW_n` for the leading-`d` projector `Q`. -/
theorem topProj_gradeLE (n d : ℕ) : gradeLEn n (topProj n d) (2 * d) := by
  induction n generalizing d with
  | zero => intro v hv; trivial
  | succ m ih =>
      cases d with
      | zero => simpa using bwId_gradeLE_zero (m + 1)
      | succ d =>
          intro v hv
          obtain ⟨hv1, hv2, _w, _hw, _hwd⟩ := hv
          have ihd : gradeLEn m (topProj m d) (2 * d) := ih d
          have hR2 : inBW m (bwSmul m (Z8.lam ^ (2 * (d + 1)))
              (bwMul m (topProj m d) v.2)) := by
            have hmono : gradeLEn m (topProj m d) (2 * (d + 1)) :=
              gradeLEn_of_le ihd (by omega)
            have := hmono v.2 hv2
            rwa [bwSmul_bwMul_left] at this
          have hXmem : inBW m (bwSmul m (Z8.lam ^ (2 * d)) (bwMul m (topProj m d) v.2)) := by
            have := ihd v.2 hv2
            rwa [bwSmul_bwMul_left] at this
          have hpow : Z8.lam ^ (2 * (d + 1)) = oneI * uu * Z8.lam ^ (2 * d) := by
            have e : 2 * (d + 1) = 2 * d + 2 := by ring
            rw [e, pow_add, Z8.lam_sq]; ring
          refine ⟨?_, ?_, ?_⟩
          · -- component 1 is zero
            show inBW m (bwMul m (bwSmul m (Z8.lam ^ (2 * (d + 1))) (bwZero m)) v.1)
            rw [bwSmul_bwZero, bwMul_bwZero]
            exact bwZero_inBW m
          · -- component 2
            show inBW m (bwMul m (bwSmul m (Z8.lam ^ (2 * (d + 1))) (topProj m d)) v.2)
            rw [bwSmul_bwMul_left]
            exact hR2
          · -- syndrome
            refine ⟨bwSmul m (-Z8.uu) (bwSmul m (Z8.lam ^ (2 * d))
                (bwMul m (topProj m d) v.2)), bwSmul_inBW m _ hXmem, ?_⟩
            show bwSub m (bwMul m (bwSmul m (Z8.lam ^ (2 * (d + 1))) (bwZero m)) v.1)
                (bwMul m (bwSmul m (Z8.lam ^ (2 * (d + 1))) (topProj m d)) v.2)
              = bwSmul m oneI (bwSmul m (-Z8.uu)
                  (bwSmul m (Z8.lam ^ (2 * d)) (bwMul m (topProj m d) v.2)))
            rw [bwSmul_bwZero, bwMul_bwZero, bwSub_bwZero_left, bwSmul_bwMul_left]
            simp only [bwSmul_bwSmul]
            congr 1
            rw [hpow]; ring

/-! ## The monomial character and T1.3 -/

/-- The single-monomial diagonal character `D_{c·x_S}` on the leading `d` qubits, with
corner phase `s = ζ₈^c`: `D = I + (s − 1)·Q` where `Q = topProj n d`. -/
def topMon (n d : ℕ) (s : Z8) : BWVec n :=
  bwAdd n (bwId n) (bwSmul n (s - 1) (topProj n d))

/-- **T1.3 (general upper bound).** If `λ^p ∣ s − 1` (witnessed by `s − 1 = λ^p·u`),
then the leading-`d` monomial character with corner phase `s` has grade
`≤ max(0, 2d − p) = 2d − p`.  (Only divisibility is needed; when `u` is a unit the
valuation is exactly `p`, see `scalar_zeta`/`scalar_iu`/`scalar_negOne` and the
`isUnit_*` lemmas.) -/
theorem topMon_gradeLE (n d p : ℕ) (s u : Z8)
    (hs : s - 1 = Z8.lam ^ p * u) : gradeLEn n (topMon n d s) (2 * d - p) := by
  set k := 2 * d - p with hk
  intro v hv
  show inBW n (bwMul n (bwSmul n (Z8.lam ^ k) (topMon n d s)) v)
  unfold topMon
  rw [← bwSmul_bwAdd, bwMul_bwAdd_left]
  apply bwAdd_inBW
  · -- first term: λ^k · I · v = λ^k · v ∈ BW_n
    rw [bwSmul_bwMul_left, bwId_mul]
    exact bwSmul_inBW n _ hv
  · -- second term
    rw [bwSmul_bwSmul, bwSmul_bwMul_left, hs]
    have hcollect : (Z8.lam ^ k * (Z8.lam ^ p * u)) = u * Z8.lam ^ (k + p) := by
      rw [pow_add]; ring
    rw [hcollect, ← bwSmul_bwSmul]
    apply bwSmul_inBW
    have hmono : gradeLEn n (topProj n d) (k + p) :=
      gradeLEn_of_le (topProj_gradeLE n d) (by omega)
    have := hmono v hv
    rwa [bwSmul_bwMul_left] at this

/-- The grade of the leading-`d` monomial with corner phase `s = λ^p·u + 1` is
`≤ 2d − p`. -/
theorem topMon_graden_le (n d p : ℕ) (s u : Z8)
    (hs : s - 1 = Z8.lam ^ p * u) : graden n (topMon n d s) ≤ 2 * d - p :=
  graden_le (topMon_gradeLE n d p s u hs)

/-! ## T1.2 — the cyclotomic scalar valuations -/

/-- `ζ₈ − 1 = λ¹·(−1)` (`ν = 0`). -/
theorem scalar_zeta : Z8.zeta - 1 = Z8.lam ^ 1 * (-1) := by decide

/-- `i − 1 = λ²·u`, `u = i·u⁻¹` a unit (`ν = 1`). -/
theorem scalar_iu : Z8.iu - 1 = Z8.lam ^ 2 * (Z8.iu * Z8.uuInv) := by decide

/-- `(−1) − 1 = λ⁴·u`, `u = i·u⁻²` a unit (`ν = 2`). -/
theorem scalar_negOne : (-1 : Z8) - 1 = Z8.lam ^ 4 * (Z8.iu * Z8.uuInv * Z8.uuInv) := by decide

theorem isUnit_neg_one : IsUnit (-1 : Z8) := (isUnit_one).neg

theorem isUnit_iu_uuInv : IsUnit (Z8.iu * Z8.uuInv) :=
  ⟨⟨Z8.iu * Z8.uuInv, Z8.uu * (-Z8.iu), by decide, by decide⟩, rfl⟩

theorem isUnit_iu_uuInv_sq : IsUnit (Z8.iu * Z8.uuInv * Z8.uuInv) :=
  ⟨⟨Z8.iu * Z8.uuInv * Z8.uuInv, Z8.uu * Z8.uu * (-Z8.iu), by decide, by decide⟩, rfl⟩

/-! ## T1.3 — the named all-`n`, all-`ν` upper bounds -/

/-- **`ν = 0`:** the maximal `T`-type monomial `D_{x_S}` (corner phase `ζ₈`) on the
leading `d` qubits has grade `≤ 2d − 1`. -/
theorem graden_topMon_zeta (n d : ℕ) : graden n (topMon n d Z8.zeta) ≤ 2 * d - 1 :=
  topMon_graden_le n d 1 Z8.zeta (-1) scalar_zeta

/-- **`ν = 1`:** the `CS`-type monomial `D_{2·x_S}` (corner phase `i`) on the leading `d`
qubits has grade `≤ 2d − 2`. -/
theorem graden_topMon_iu (n d : ℕ) : graden n (topMon n d Z8.iu) ≤ 2 * d - 2 :=
  topMon_graden_le n d 2 Z8.iu (Z8.iu * Z8.uuInv) scalar_iu

/-- **`ν = 2`:** the `Z`-type monomial `D_{4·x_S}` (corner phase `−1`) on the leading `d`
qubits has grade `≤ 2d − 4`. -/
theorem graden_topMon_negOne (n d : ℕ) : graden n (topMon n d (-1)) ≤ 2 * d - 4 :=
  topMon_graden_le n d 4 (-1) (Z8.iu * Z8.uuInv * Z8.uuInv) scalar_negOne

/-- **`ν = ∞` (`c ≡ 0 mod 8`):** the trivial character (corner phase `1`) is the identity,
grade `0`. -/
theorem topMon_one (n d : ℕ) : topMon n d 1 = bwId n := by
  unfold topMon
  rw [show (1 : Z8) - 1 = 0 by ring, bwSmul_zero_scalar]
  exact bwAdd_bwId_bwZero n

theorem graden_topMon_one (n d : ℕ) : graden n (topMon n d 1) = 0 := by
  rw [topMon_one]
  exact Nat.le_zero.mp (graden_le (bwId_gradeLE_zero n))

/-- **The unified linear closed-form upper bound (`Roots.wFit`), all `n`, all `ν`.**
The single-monomial character `D_{c·x_S}` on the leading `d` qubits, with corner phase
`ζ₈^c` and `ν = ν₂(c mod 8)`, satisfies `g ≤ wFit d ν = max(0, 2d − 2^ν)` for each of
the four valuation classes. -/
theorem graden_topMon_wFit (n d : ℕ) :
    graden n (topMon n d Z8.zeta) ≤ wFit d 0 ∧
    graden n (topMon n d Z8.iu) ≤ wFit d 1 ∧
    graden n (topMon n d (-1)) ≤ wFit d 2 := by
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans (graden_topMon_zeta n d) ?_; simp only [wFit]; norm_num
  · refine le_trans (graden_topMon_iu n d) ?_; simp only [wFit]; norm_num
  · refine le_trans (graden_topMon_negOne n d) ?_; simp only [wFit]; norm_num

/-! ## Consistency: `topMon` generalizes `BWn.bwT` -/

/-- The all-qubits projector is the corner projector. -/
theorem topProj_eq_bwCorner (n : ℕ) : topProj n n = bwCorner n := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [topProj_succ_succ, bwCorner_succ, ih]

/-- The `T`-type monomial `bwT` is the `I + (ζ₈−1)·corner` factorization. -/
theorem bwT_eq_topMon (n : ℕ) :
    bwT n = bwAdd n (bwId n) (bwSmul n (Z8.zeta - 1) (bwCorner n)) := by
  induction n with
  | zero =>
      show (Z8.zeta : Z8) = (1 : Z8) + (Z8.zeta - 1) * 1
      ring
  | succ m ih =>
      simp only [bwT_succ, bwId_succ, bwCorner_succ, bwSmul_succ, bwSmul_bwZero, bwAdd_succ,
        bwAdd_bwId_bwZero]
      rw [ih]

/-- The all-qubits canonical monomial `topMon n n ζ₈` equals `BWn.bwT n`. -/
theorem topMon_eq_bwT (n : ℕ) : topMon n n Z8.zeta = bwT n := by
  unfold topMon
  rw [topProj_eq_bwCorner, ← bwT_eq_topMon]

/-- The all-`n` `ν = 0` upper bound `g(bwT n) ≤ 2n − 1` recovered from the general
upper bound (cf. `BWn.bwT_graden_le`). -/
theorem graden_bwT_le (n : ℕ) : graden n (bwT n) ≤ 2 * n - 1 := by
  rw [← topMon_eq_bwT]; exact graden_topMon_zeta n n

/-! ## Corollary — the all-`n` product (disjoint-support sum) subadditivity -/

/-- The product (composition) of two diagonal characters preserves the graded bound:
if `λ^j·D` and `λ^k·E` preserve `BW_n`, so does `λ^{j+k}·(D·E)`. -/
theorem gradeLEn_bwMul {n : ℕ} {D E : BWVec n} {j k : ℕ}
    (hD : gradeLEn n D j) (hE : gradeLEn n E k) : gradeLEn n (bwMul n D E) (j + k) := by
  intro v hv
  show inBW n (bwMul n (bwSmul n (Z8.lam ^ (j + k)) (bwMul n D E)) v)
  have hsplit : bwSmul n (Z8.lam ^ (j + k)) (bwMul n D E)
      = bwMul n (bwSmul n (Z8.lam ^ j) D) (bwSmul n (Z8.lam ^ k) E) := by
    rw [bwSmul_bwMul_both, ← pow_add]
  rw [hsplit, bwMul_assoc]
  exact hD _ (hE v hv)

/-- **All-`n` product subadditivity.** `g(D·E) ≤ g(D) + g(E)` for diagonal characters.
Specializing to characters of disjoint monomial support (`D_{e₁+e₂} = D_{e₁}·D_{e₂}`)
gives the disjoint-support additive upper bound at every `n`. -/
theorem graden_bwMul_le (n : ℕ) (D E : BWVec n) :
    graden n (bwMul n D E) ≤ graden n D + graden n E := by
  apply graden_le
  apply gradeLEn_bwMul
  · exact Nat.sInf_mem (gradeLEn_nonempty n D)
  · exact Nat.sInf_mem (gradeLEn_nonempty n E)

end Roots
