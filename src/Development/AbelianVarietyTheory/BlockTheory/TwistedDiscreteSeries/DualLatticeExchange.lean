import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift

open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DualLatticeExchange
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair

section Defs
variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n]

def dualLat (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n → k) where
  carrier := {u | ∀ x ∈ L, u ⬝ᵥ x ∈ 𝒪[k]}
  add_mem' hu hv x hx := by
    rw [add_dotProduct]
    exact add_mem (hu x hx) (hv x hx)
  zero_mem' x _ := by
    rw [zero_dotProduct]
    exact zero_mem _
  smul_mem' s u hu x hx := by
    have : (s • u) ⬝ᵥ x = (s : k) * (u ⬝ᵥ x) := smul_dotProduct (s : k) u x
    rw [this]
    exact mul_mem s.2 (hu x hx)

def intPart (L : Submodule 𝒪[k] (n → k)) (u : n → k) : Submodule 𝒪[k] (n → k) where
  carrier := {x | x ∈ L ∧ u ⬝ᵥ x ∈ 𝒪[k]}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, by
    rw [dotProduct_add]
    exact add_mem hx.2 hy.2⟩
  zero_mem' := ⟨zero_mem _, by
    rw [dotProduct_zero]
    exact zero_mem _⟩
  smul_mem' s x hx := ⟨L.smul_mem s hx.1, by
    have : u ⬝ᵥ (s • x) = (s : k) * (u ⬝ᵥ x) := dotProduct_smul (s : k) u x
    rw [this]
    exact mul_mem s.2 hx.2⟩

end Defs

section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GluedPrimitive : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : n → k),
    IsGlue L f → 1 ≤ p → p ≤ c → ∀ i j : Fin c, j.val = i.val + 1 →
      (fun g : GL (n ⊕ Fin c) k => g.val (Sum.inr i) (Sum.inr j)) ''
        ((N k n c p ⊓ latStab (gluedLat q c p L f) : Subgroup (GL (n ⊕ Fin c) k)) : Set (GL (n ⊕ Fin c) k)) =
        (𝒪[k] : Set k)

end Statements

section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

example (c p : ℕ) (u x : n → k) :
    (rowE c p u).val *ᵥ inX k n c x = inX k n c x + (u ⬝ᵥ x) • avec k n c p := by
  ext (i | i)
  · simp [rowE, lowU, inX, avec, fromBlocks_mulVec]
  · by_cases h : i.val + 1 = p <;> simp [rowE, lowU, inX, avec, fromBlocks_mulVec, mulVec, dotProduct, h]

example : dualLat (stdLat k n) = stdLat k n := by
  ext u
  refine ⟨fun h => mem_stdLat.2 fun i => ?_, fun h x hx => ?_⟩
  · have := h (Pi.single i 1) (mem_stdLat.2 fun j => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
    simpa using this
  · exact sum_mem fun i _ => mul_mem (mem_stdLat.1 h i) (mem_stdLat.1 hx i)

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.DualLatticeExchange
