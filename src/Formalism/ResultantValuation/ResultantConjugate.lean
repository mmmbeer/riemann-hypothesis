import Mathlib

open Finset

noncomputable section

namespace Formalism.ResultantValuation

def ResultantConjugate : Prop :=
  ∀ (K : Type) [Field K] (c : K →+* K) (a b : ℕ) (α : Fin a → K) (β : Fin b → K)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)),
    (∀ i, α i ≠ 0) → (∀ j, β j ≠ 0) →
    (∀ i, c (α i) = (α (σ i))⁻¹) → (∀ j, c (β j) = (β (τ j))⁻¹) →
    (∏ i, ∏ j, (α i - β j)) =
      (-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a * c (∏ i, ∏ j, (α i - β j))

def LaplaceRows : Prop :=
  ∀ (R : Type) [CommRing R] (a b : ℕ) (M : Matrix (Fin (a + b)) (Fin (a + b)) R),
    M.det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a},
      (-1 : R) ^ (a * (a - 1) / 2 + ∑ j ∈ J.1, (j : ℕ)) *
        (M.submatrix (Fin.castAdd b) (J.1.orderEmbOfFin J.2)).det *
        (M.submatrix (Fin.natAdd a)
          ((J.1ᶜ).orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, J.2]; omega))).det

end Formalism.ResultantValuation
