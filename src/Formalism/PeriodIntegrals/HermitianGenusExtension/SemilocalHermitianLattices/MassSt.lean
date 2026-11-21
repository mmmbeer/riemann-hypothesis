import Mathlib
import Formalism.HermitianLattices.StatementMass

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

section Defs

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def IsTotPosDef (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ x : V, x ≠ 0 → ∀ φ : K →+* ℂ, 0 < (φ (h x x)).re

def repCount (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (t : K) : ℕ :=
  Nat.card {x : V // x ∈ L ∧ h x x = t}

def repMass (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (t : K) : ℝ := by
  classical
  exact if hs : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s then
    ∑ M ∈ hs.choose, (repCount h M t : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) else 0

end Defs

def conjO (K : Type*) [Field K] [StarRing K] : 𝓞 K →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (starRingEnd K)

def etaF (K F : Type*) [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) : ℝ := by
  classical
  exact if (𝔭.map (algebraMap (𝓞 F) (𝓞 K))).IsPrime then -1 else 1

def lValEtaF (K F : Type*) [Field K] [Field F] [NumberField F] [Algebra F K] (M : ℕ) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
    (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹

def OrbitCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (M : ℕ), 2 ≤ M →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) V'),
      h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L M →
      Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' (M - 1) →
      repMass h L 1 = Formalism.HermitianLatticesTheory.mass h' L'

end ReciprocityTheory.ChartRestriction.L3
