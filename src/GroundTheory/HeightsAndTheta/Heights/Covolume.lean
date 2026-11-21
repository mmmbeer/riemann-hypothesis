import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module

open scoped Kronecker

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section Real

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E)

namespace RealSpace

instance instMeasurableSpace : MeasurableSpace (RealSpace h) := borel _

instance instBorelSpace : BorelSpace (RealSpace h) := ⟨rfl⟩

end RealSpace

end Real

open Classical in

theorem det_basisMatrix_sq : (basisMatrix K).det ^ 2 = ((discr K : ℤ) : ℂ) := by
  rw [basisMatrix_eq_embeddingsMatrixReindex,
    ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (integralBasis K ∘ (equivReindex K)) (RingHom.equivRatAlgHom K ℂ),
    ← (equivReindex K).symm_symm, Algebra.discr_reindex ℚ (integralBasis K) (equivReindex K).symm,
    ← coe_discr]
  simp

theorem basisMatrix_apply' (τ σ : K →+* ℂ) :
    basisMatrix K τ σ = σ ((RingOfIntegers.basis K (equivReindex K τ) : 𝓞 K) : K) := by
  simp [basisMatrix, canonicalEmbedding.latticeBasis_apply, integralBasis_apply,
    canonicalEmbedding.apply_at]

section Gram

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]

def towerVec (s : ι → E) (p : ι × (K →+* ℂ)) : RealSpace h :=
  RealSpace.ofModule h (RingOfIntegers.basis K (equivReindex K p.2) • s p.1)

end Gram

section RiemannRoch

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {s : ι → E}

def spanToReal (s : ι → E) : Submodule.span (𝓞 K) (Set.range s) →ₗ[ℤ] RealSpace h :=
  (RealSpace.ofModule h).toIntLinearMap ∘ₗ
    ((Submodule.span (𝓞 K) (Set.range s)).subtype.restrictScalars ℤ)

omit [Fintype ι] [DecidableEq ι] in
theorem spanToReal_injective (s : ι → E) : Function.Injective (spanToReal h s) :=
  (RealSpace.ofModule_injective h).comp Subtype.val_injective

def spanLattice (s : ι → E) : Submodule ℤ (RealSpace h) := LinearMap.range (spanToReal h s)

omit [Fintype ι] [DecidableEq ι] in
theorem spanLattice_le (s : ι → E) : spanLattice h s ≤ RealSpace.lattice h := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x, rfl⟩

instance (s : ι → E) : DiscreteTopology (spanLattice h s) := by
  have : DiscreteTopology (RealSpace.lattice h : Set (RealSpace h)) :=
    (inferInstance : DiscreteTopology (RealSpace.lattice h))
  exact DiscreteTopology.of_subset this (spanLattice_le h s)

end RiemannRoch

namespace HermitianExtension

variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')

end HermitianExtension

end

end GroundTheory.Heights₂.Heights
