import Mathlib

noncomputable section

namespace Formalism.WachCohomologyFacts.TopB

def Ord {k : Type} [Field k] (j : ℤ) (x : LaurentSeries k) : Prop := ∀ i < j, x.coeff i = 0

def vv (k : Type) [Field k] : LaurentSeries k := HahnSeries.single 1 1

def IsUnitR {k : Type} [Field k] (x : LaurentSeries k) : Prop := Ord 0 x ∧ x.coeff 0 ≠ 0

structure PsiData (k : Type) [Field k] (ℓ : ℕ) where
  φ : LaurentSeries k →ₐ[k] LaurentSeries k
  γ : LaurentSeries k →ₐ[k] LaurentSeries k
  ψ : LaurentSeries k →+ LaurentSeries k
  u : LaurentSeries k
  c : LaurentSeries k
  c₀ : k
  hu : IsUnitR u
  φ_v : φ (vv k) = u * vv k ^ ℓ
  φ_ord : ∀ (j : ℤ) (x : LaurentSeries k), Ord j x → Ord (ℓ * j) (φ x)
  hc : IsUnitR c
  γ_v : γ (vv k) = vv k + c * vv k ^ 2
  γ_bij : Function.Bijective γ
  γ_φ : ∀ x, γ (φ x) = φ (γ x)
  hc₀ : c₀ ≠ 0
  γ_lead : ∀ (j : ℤ) (x : LaurentSeries k), Ord j x →
    Ord (j + 1) (γ x - x) ∧ Ord (j + 2) (γ x - x - ((j : k) * c₀) • (vv k * x))
  ψ_φ : ∀ a x, ψ (φ a * x) = a * ψ x
  ψ_one : ψ 1 = 1
  ψ_γ : ∀ x, ψ (γ x) = γ (ψ x)
  ψ_low : ∀ a : ℤ, 2 - (ℓ : ℤ) ≤ a → a ≤ 1 → ψ '' {x | Ord a x} = {x | Ord 0 x}
  ψ_high : ∀ a : ℤ, 2 ≤ a → a ≤ (ℓ : ℤ) + 1 → ψ '' {x | Ord a x} = {x | Ord 1 x}

end Formalism.WachCohomologyFacts.TopB
