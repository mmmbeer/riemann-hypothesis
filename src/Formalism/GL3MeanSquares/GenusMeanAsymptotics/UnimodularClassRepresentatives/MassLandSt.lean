import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassSt

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

def TotPos {K : Type*} [Field K] (a : K) : Prop :=
  ∀ φ : K →+* ℂ, 0 < (φ a).re

def gram {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {n : ℕ}
    (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin n → V) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => h (e i) (e j)

def HermRepUnram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ a b n : K, star a = a → star b = b → star n = n → TotPos a → TotPos b → TotPos n →
      ∃ s t : K, a * (s * star s) + b * (t * star t) = n

def OrthBasisPos : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
      h.IsSymm → IsTotPosDef h →
      ∃ e : Basis (Fin (finrank K V)) K V, (∀ i j, i ≠ j → h (e i) (e j) = 0) ∧
        ∀ i, star (h (e i) (e i)) = h (e i) (e i) ∧ TotPos (h (e i) (e i))

end Formalism.HermitianLattices.Ext.L3
