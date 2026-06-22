import StabilizerBW.Qutrit.CSSBarnesWall.QutritReedMuller

/-!
# T2 — The genuine qutrit-CSS Barnes–Wall lattice `BWCssQutrit(m, r₁, r₂)`

We package the classical-code data of a qutrit (`𝔽₃`) CSS code and build the
Reed–Muller-pair member, the `q = 3` analogue of the chapter's
`BWCss(m, r₁, r₂)` (`StabilizerBW.BWCss/CSS.lean`).

As in the qubit case no quantum stabiliser formalism is needed: the logical
parameters are derived from the underlying `𝔽₃` linear codes.  The X- and
Z-stabilisers are

  `CX = QRM(r₂, m)`,   `CZ = QRM(2m − 1 − r₁, m)`,

and the **CSS containment** `CX ≤ CZ^⊥` is exactly `QRM_dual_inclusion`
(monomial orthogonality), valid for `r₂ ≤ r₁`.  The block length is `n = 3^m`
and the stabiliser dimensions are the monomial counts from `QRM_dim`.

The canonical instance `BWCssQutrit 3 1 0` is the qutrit analogue of the qubit
Steane code `BWCss(3,1,0) = [[8, 3, 4_X]]`: it is a `[[27, k, d]]₃` qutrit-CSS
Barnes–Wall code with `CX = QRM(0,3)` (the repetition/constants code, dimension
`1`) and `CZ = QRM(4,3)`.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

open scoped BigOperators
open Classical

namespace QutritCSSBarnesWall

/-- The classical-code data of a qutrit (`𝔽₃`) CSS code, in the evaluation-point
model, together with the CSS containment condition `CX ≤ CZ^⊥`. -/
structure QCSSCode where
  /-- Number of qutrits (so block length is `3 ^ m`). -/
  m : ℕ
  /-- The X-stabiliser code. -/
  CX : Submodule (ZMod 3) (QFun m)
  /-- The Z-stabiliser code. -/
  CZ : Submodule (ZMod 3) (QFun m)
  /-- The CSS containment condition `CX ≤ CZ^⊥`. -/
  css_condition : CX ≤ dualQ CZ

/-- Block length of a qutrit-CSS code: `n = 3 ^ m`. -/
def QCSSCode.n (C : QCSSCode) : ℕ := 3 ^ C.m

/-! ### The Reed–Muller-pair qutrit-CSS code -/

/-- The CSS containment for the qutrit Reed–Muller pair: `QRM(r₂) ≤ QRM(2m−1−r₁)^⊥`,
valid whenever `r₂ ≤ r₁` and `r₁ + 1 ≤ 2m`. -/
theorem ofQRMPair_css (m r₁ r₂ : ℕ) (h : r₂ ≤ r₁) (hm : r₁ + 1 ≤ 2 * m) :
    QRM r₂ m ≤ dualQ (QRM (2 * m - 1 - r₁) m) := by
  apply QRM_dual_inclusion
  omega

/-- The qutrit Reed–Muller-pair CSS code `BWCssQutrit(m, r₁, r₂)` with
`CX = QRM(r₂, m)` and `CZ = QRM(2m−1−r₁, m)`. -/
def ofQRMPair (m r₁ r₂ : ℕ) (h : r₂ ≤ r₁) (hm : r₁ + 1 ≤ 2 * m) : QCSSCode where
  m := m
  CX := QRM r₂ m
  CZ := QRM (2 * m - 1 - r₁) m
  css_condition := ofQRMPair_css m r₁ r₂ h hm

@[simp] theorem ofQRMPair_m (m r₁ r₂ : ℕ) (h : r₂ ≤ r₁) (hm : r₁ + 1 ≤ 2 * m) :
    (ofQRMPair m r₁ r₂ h hm).m = m := rfl

@[simp] theorem ofQRMPair_CX (m r₁ r₂ : ℕ) (h : r₂ ≤ r₁) (hm : r₁ + 1 ≤ 2 * m) :
    (ofQRMPair m r₁ r₂ h hm).CX = QRM r₂ m := rfl

@[simp] theorem ofQRMPair_CZ (m r₁ r₂ : ℕ) (h : r₂ ≤ r₁) (hm : r₁ + 1 ≤ 2 * m) :
    (ofQRMPair m r₁ r₂ h hm).CZ = QRM (2 * m - 1 - r₁) m := rfl

@[simp] theorem ofQRMPair_n (m r₁ r₂ : ℕ) (h : r₂ ≤ r₁) (hm : r₁ + 1 ≤ 2 * m) :
    (ofQRMPair m r₁ r₂ h hm).n = 3 ^ m := rfl

/-- The Barnes–Wall qutrit-CSS family, total in `(m, r₁, r₂)`.  On valid
parameters (`r₂ ≤ r₁`, `r₁ + 1 ≤ 2m`) it is `ofQRMPair`; otherwise it falls back
to a fixed valid member. -/
noncomputable def BWCssQutrit (m r₁ r₂ : ℕ) : QCSSCode :=
  if hp : r₂ ≤ r₁ ∧ r₁ + 1 ≤ 2 * m then ofQRMPair m r₁ r₂ hp.1 hp.2
  else ofQRMPair 3 1 0 (by decide) (by decide)

/-! ### Parameters -/

/-- **Headline parameters of the qutrit-CSS Barnes–Wall family.**
For valid parameters the block length is `3 ^ m`, the CSS containment holds, and
the stabiliser dimensions are the monomial counts of `QRM`. -/
theorem BWCssQutrit_params (m r₁ r₂ : ℕ) (h : r₂ ≤ r₁) (hm : r₁ + 1 ≤ 2 * m) :
    (BWCssQutrit m r₁ r₂).n = 3 ^ m ∧
    (BWCssQutrit m r₁ r₂).CX ≤ dualQ (BWCssQutrit m r₁ r₂).CZ ∧
    Module.finrank (ZMod 3) (BWCssQutrit m r₁ r₂).CX
      = (Finset.univ.filter (fun e : Exp m => qdeg e ≤ r₂)).card ∧
    Module.finrank (ZMod 3) (BWCssQutrit m r₁ r₂).CZ
      = (Finset.univ.filter (fun e : Exp m => qdeg e ≤ 2 * m - 1 - r₁)).card := by
  have hp : r₂ ≤ r₁ ∧ r₁ + 1 ≤ 2 * m := ⟨h, hm⟩
  have heq : BWCssQutrit m r₁ r₂ = ofQRMPair m r₁ r₂ h hm := by
    rw [BWCssQutrit, dif_pos hp]
  rw [heq]
  refine ⟨rfl, ofQRMPair_css m r₁ r₂ h hm, ?_, ?_⟩
  · rw [ofQRMPair_CX]; exact QRM_dim r₂ m
  · rw [ofQRMPair_CZ]; exact QRM_dim (2 * m - 1 - r₁) m

/-! ### The canonical instance `BWCssQutrit 3 1 0` (qutrit Steane analogue) -/

/-- **The canonical qutrit-CSS Barnes–Wall code `BWCssQutrit 3 1 0`** — the
`q = 3` analogue of the qubit Steane code `BWCss(3,1,0) = [[8,3,4_X]]`:
a `[[27, …]]₃` code with `CX = QRM(0,3)` of dimension `1` and `CZ = QRM(4,3)`. -/
theorem BWCssQutrit_3_1_0 :
    (BWCssQutrit 3 1 0).n = 27 ∧
    (BWCssQutrit 3 1 0).CX ≤ dualQ (BWCssQutrit 3 1 0).CZ ∧
    Module.finrank (ZMod 3) (BWCssQutrit 3 1 0).CX = 1 := by
  obtain ⟨hn, hcss, hCX, _⟩ := BWCssQutrit_params 3 1 0 (by decide) (by decide)
  refine ⟨by simpa using hn, hcss, ?_⟩
  rw [hCX]
  decide

end QutritCSSBarnesWall
