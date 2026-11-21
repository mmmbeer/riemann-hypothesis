import Mathlib
import Formalism.LogFactorialIndices.StatementSize
import Formalism.LogFactorialIndices.StatementIdx

noncomputable section

namespace Formalism.LatticeIndexTer

open Finset Module
open scoped ComplexConjugate Pointwise

def SubspaceIndexSigned : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (F : ℤ) (M Θ : Submodule O X), IsLat O K X M → IsLat O K X Θ →
      Θ ≤ M.map ((((algebraMap O K ϖ) ^ F) • LinearMap.id : X →ₗ[K] X).restrictScalars O) →
      ∀ W : Submodule K X,
        idx O X (M ⊓ W.restrictScalars O) (Θ ⊓ W.restrictScalars O) ≤
          idx O X M Θ - F * ((finrank K X : ℤ) - finrank K W)

def DetBound : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (D g : ℕ) (a : K) (M : Matrix (Fin D) (Fin D) K),
    (∀ i j, ∃ o : O, a ^ g * M i j = algebraMap O K o) →
      ∃ o : O, a ^ (g * D) * M.det = algebraMap O K o

end Formalism.LatticeIndexTer
