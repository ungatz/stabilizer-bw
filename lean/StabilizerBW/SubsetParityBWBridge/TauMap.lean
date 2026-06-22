import StabilizerBW.SubsetParityBWBridge.ParityBit

/-!
# SubsetParityBWBridge — T2: the parity-tag map `τ` and its uniform pushforward

`tau P : Fin m → Bool` reads the per-coordinate parities of a linear phase
polynomial `P : LinPhase m`, discarding the constant term `P.1`.

`fiber_card` counts, for a fixed tag `b̄`, the number of coefficient vectors
realising it: `4^m` (each coordinate has four `Z/8` residues of the prescribed
parity).  `tau_fiber_card` adds the eight free choices of the constant term,
giving the constant fiber size `8·4^m`.  Equivalently, the pushforward of
uniform counting measure on `LinPhase m` (cardinality `8^{m+1}`) under `τ` is
uniform on `Fin m → Bool` (cardinality `2^m`).
-/

namespace SubsetParityBWBridge.TauMap

open Finset SubsetParityBWBridge.ParityBit

/-- The parity-tag map: `τ P i` is the parity bit of the `i`-th linear
coefficient `P.2 i`. -/
def tau {m : ℕ} (P : T1A.LinPhase m) : Fin m → Bool := fun i => parityBit (P.2 i)

/-- **Per-coordinate fiber.** For each tag `b̄ : Fin m → Bool`, exactly `4^m`
coefficient vectors `f : Fin m → ZMod 8` have parity profile `b̄`. -/
theorem fiber_card {m : ℕ} (b : Fin m → Bool) :
    (Finset.univ.filter (fun f : Fin m → ZMod 8 => (fun i => parityBit (f i)) = b)).card = 4 ^ m := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight
      (p := fun f : Fin m → ZMod 8 => (fun i => parityBit (f i)) = b)
      (q := fun f => ∀ i, parityBit (f i) = b i) (fun f => by simp [funext_iff]))]
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi
      (p := fun (i : Fin m) (x : ZMod 8) => parityBit x = b i))]
  rw [Fintype.card_pi]
  have hc : ∀ i, Fintype.card {x : ZMod 8 // parityBit x = b i} = 4 := by
    intro i; rcases h : (b i) with _ | _ <;> decide
  rw [Finset.prod_congr rfl (fun i _ => hc i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **T2 headline.** The `τ`-fiber over every tag `b̄` has constant size
`8·4^m`; the pushforward of uniform measure on `LinPhase m` is uniform on
`Fin m → Bool`. -/
theorem tau_fiber_card {m : ℕ} (b : Fin m → Bool) :
    (Finset.univ.filter (fun P : T1A.LinPhase m => tau P = b)).card = 8 * 4 ^ m := by
  classical
  have hset : (Finset.univ.filter (fun P : T1A.LinPhase m => tau P = b))
      = (Finset.univ : Finset (ZMod 8)) ×ˢ
          (Finset.univ.filter (fun f : Fin m → ZMod 8 => (fun i => parityBit (f i)) = b)) := by
    ext ⟨c, f⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    exact Iff.rfl
  rw [hset, Finset.card_product, fiber_card]
  simp [Finset.card_univ]

end SubsetParityBWBridge.TauMap
