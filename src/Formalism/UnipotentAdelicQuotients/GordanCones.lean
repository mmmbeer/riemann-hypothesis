import Mathlib

set_option autoImplicit false

namespace GordanCones

def toQ {n : ℕ} (v : Fin n → ℤ) : Fin n → ℚ := fun i => (v i : ℚ)

def cone {n : ℕ} (s : Finset (Fin n → ℤ)) : Set (Fin n → ℚ) :=
  {x | ∃ c : (Fin n → ℤ) → ℚ, (∀ v ∈ s, 0 ≤ c v) ∧ x = ∑ v ∈ s, c v • toQ v}

def Lattice : Prop :=
  ∀ (n : ℕ) (s : Finset (Fin n → ℤ)), ∃ t : Finset (Fin n → ℤ),
    {x : Fin n → ℤ | toQ x ∈ cone s} = {x | ∃ d : (Fin n → ℤ) → ℕ, x = ∑ v ∈ t, d v • v}

end GordanCones
