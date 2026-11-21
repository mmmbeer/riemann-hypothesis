import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open Module Matrix
open scoped ComplexOrder

def ReducedBasisStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Submodule ℤ E) [DiscreteTopology X] [IsZLattice ℝ X] (M : ℝ)
    (v : Fin (finrank ℝ E) → E), LinearIndependent ℝ v → (∀ i, v i ∈ X) →
    (∀ i, ‖v i‖ ^ 2 / 2 ≤ M) →
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ X,
      (∀ j, ‖(b j : E)‖ ^ 2 / 2 ≤ (finrank ℝ E : ℝ) * M) ∧
      ∀ j, ∀ z ∈ X, |inner ℝ (b j : E) z| ≤ 2 * Real.sqrt (finrank ℝ E) * (‖z‖ ^ 2 / 2)

def NakayamaCharStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (ι : Type) [Fintype ι] (Γ : Type)
    (T : Γ → M →ₗ[R] M) (χ : ι → Γ → R) (s : ι → M),
    Fintype.card ι = finrank R M →
    (∀ i, s i ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) →
    (∀ i γ, T γ (s i) - χ i γ • s i ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) →
    (∀ i j, i ≠ j → ∃ γ, χ i γ - χ j γ ∉ IsLocalRing.maximalIdeal R) →
    Submodule.span R (Set.range s) = ⊤

end ReciprocityTheory.ChartRestriction.G.H1
