import Mathlib

open Finset

noncomputable section

namespace Formalism.HadamardInequality

def energy {m : ℕ} (u : Fin m → ℕ) : ℤ :=
  ∑ j, (u j : ℤ) ^ 2 - ∑ j : Fin m, ∑ i : Fin m, if (i : ℕ) + 1 = j then (u i : ℤ) * u j else 0

def EnergyIdentity : Prop :=
  ∀ (m : ℕ) (u : Fin (m + 1) → ℕ),
    2 * energy u = (u 0 : ℤ) ^ 2 +
      (∑ j : Fin (m + 1), ∑ i : Fin (m + 1),
        if (i : ℕ) + 1 = j then ((u j : ℤ) - u i) ^ 2 else 0) + (u (Fin.last m) : ℤ) ^ 2

def succMin {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : Submodule ℤ E)
    (i : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ v : Fin i → E, (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ r}

def zdual {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : Submodule ℤ E) :
    Submodule ℤ E where
  carrier := {y | ∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z1, h1⟩ := ha x hx
    obtain ⟨z2, h2⟩ := hb x hx
    exact ⟨z1 + z2, by rw [inner_add_right, h1, h2]; push_cast; ring⟩
  zero_mem' := by intro x _; exact ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha x hx
    obtain ⟨z, h⟩ := ha x hx
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, inner_smul_right, h]; push_cast; ring⟩

def Transference : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℤ E), DiscreteTopology M → Submodule.span ℝ (M : Set E) = ⊤ →
    ∀ i : ℕ, 1 ≤ i → i ≤ Module.finrank ℝ E →
      succMin (zdual M) i * succMin M (Module.finrank ℝ E + 1 - i) ≤
        (Module.finrank ℝ E : ℝ) ^ 2

end Formalism.HadamardInequality
