import Mathlib

open MeasureTheory

noncomputable section
namespace GlobalTheory.ThK.Dbl

def IsAut {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (f : G → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) ∧ ∃ U : Subgroup G, IsOpen (U : Set G) ∧
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => fun x => f (x * u)))

def InSpan {G : Type} [Mul G] (f f' u u' : G → ℂ) : Prop :=
  ∃ (n : ℕ) (y : Fin n → G) (c : Fin n → ℂ),
    u = (fun h => ∑ j, c j * f (h * y j)) ∧ u' = (fun h => ∑ j, c j * f' (h * y j))

end GlobalTheory.ThK.Dbl
