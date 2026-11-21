import Mathlib
import Formalism.HermitianLattices.StatementTheta
import Formalism.HermitianLattices.GenusCovolBound

section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

end Formalism.HermitianLatticesTheory
end
end

section
open Module Formalism.K

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V]

abbrev discr (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : Type _ :=
  (tdualSub h L) ⧸ (L.comap (tdualSub h L).subtype)

def drep (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (δ : discr h L) : V :=
  ((Submodule.mkQ_surjective (L.comap (tdualSub h L).subtype) δ).choose : tdualSub h L)

variable [IsScalarTower (NumberField.RingOfIntegers K) K V]

def thetaVec (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (τ : ℂ)
    (δ : discr h L) : ℂ :=
  thetaL h L (drep h L δ) τ

end Defs

def DiscrFinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    L ≤ tdualSub h L → Finite (discr h L)

end Formalism.HermitianLatticesTheory
end
end
