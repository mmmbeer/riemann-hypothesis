import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

noncomputable section

namespace GlobalTheory.PeriodTests

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

def conjVec (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun := star
  map_add' := star_add
  map_smul' := fun r z => by simp [star_smul]

theorem isHolTo_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    (hB : IsOpen B) (x : Sp ℂ ⟶ X) : IsHolTo B (fun _ => x) := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simpa [h] using hB
  · simp only [h, and_false, Set.setOf_false, isOpen_empty]

end GlobalTheory.PeriodTests
