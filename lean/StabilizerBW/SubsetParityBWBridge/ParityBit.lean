import StabilizerBW.T1A.GradeLinear

/-!
# SubsetParityBWBridge — T1: the Z/8 → Z/2 parity-tag bit

`parityBit : ZMod 8 → Bool` is the odd/even quotient `Z/8 ↠ Z/2`.  It is the
elementary bridge between the operator-side per-coordinate `Z/8` coefficient
of a linear Barnes–Wall phase polynomial and LaRacuente's measurement-side
qubit parity tag (`b̄ ∈ {0,1}^n`).

The headline `parityBit_count_eq` records the 4-and-4 split: exactly four of the
eight residues are odd.  This is the quantitative input that makes the
parity-tag pushforward (T2) uniform.
-/

namespace SubsetParityBWBridge.ParityBit

open Finset

/-- The Z/8 → Z/2 odd/even quotient: `parityBit c = true` iff `c` is odd. -/
def parityBit (c : ZMod 8) : Bool := decide (c.val % 2 = 1)

@[simp] theorem parityBit_iff (c : ZMod 8) : parityBit c = true ↔ c.val % 2 = 1 := by
  unfold parityBit; simp

/-- **T1 headline.** Exactly four of the eight `Z/8` residues are odd. -/
theorem parityBit_count_eq :
    (Finset.univ.filter (fun c : ZMod 8 => parityBit c = true)).card = 4 := by decide

/-- The per-coordinate odd-indicator of `T1A.oddIndic` is the `ℕ`-valued
parity bit. -/
theorem oddIndic_eq_toNat (c : ZMod 8) : T1A.oddIndic c = (parityBit c).toNat := by
  unfold T1A.oddIndic parityBit
  by_cases h : c.val % 2 = 1 <;> simp [h]

end SubsetParityBWBridge.ParityBit
