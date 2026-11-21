import Formalism.PeriodIntegrals.HeisDefs

namespace PI

section Th

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def alG (s A : ℝ) (x : T → I → J → ℂ) : ℂ := (-1 : ℂ) ^ (round (s * (HfG A x x).re))

def ThSpG (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Set ((T → I → J → ℂ) → ℂ) :=
  {G | Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, alG s A x * UG A x G z = G z}

noncomputable def normSqG (A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) (G : (T → I → J → ℂ) → ℂ) : ℝ :=
  let Fd : Set (T → I → J → ℂ) :=
    Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain La' Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re)

def GoodLat (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Prop :=
  (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (T → I → J → ℂ)), La' = AddSubgroup.closure (Set.range b)) ∧
  (∀ x ∈ La', ∀ y ∈ La', ∃ n : ℤ, (HfG A x y).im = n) ∧
  (∀ v : T → I → J → ℂ, (∀ x ∈ La', ∃ n : ℤ, (HfG A v x).im = n) → v ∈ La') ∧
  ∀ x ∈ La', ∀ y ∈ La', ∀ n : ℤ, (HfG A x y).im = n → alG s A (x + y) = alG s A x * alG s A y * (-1 : ℂ) ^ n

end Th

end PI
