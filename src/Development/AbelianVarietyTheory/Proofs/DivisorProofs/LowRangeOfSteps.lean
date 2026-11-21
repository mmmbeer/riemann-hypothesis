import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicPeriodicContinuousEqZeroOfFourierCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRangeOfSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ContFromConst

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWLow

open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]
variable (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) (K : Subgroup (UA σ J₂))

def kfin : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | Φ ∈ schA F κ ∧ FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ})}
  zero_mem' := ⟨zero_mem _, by
    have h : Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) 0} ≤ ⊥ :=
      Submodule.span_le.2 (by rintro _ ⟨k, -, rfl⟩; simp)
    exact Submodule.finiteDimensional_of_le h⟩
  add_mem' := by
    rintro Φ Ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨add_mem h1 h3, ?_⟩
    have h : Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) (Φ + Ψ)} ≤
        Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) Φ} ⊔ Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) Ψ} :=
      Submodule.span_le.2 (by
        rintro _ ⟨k, hk, rfl⟩
        rw [map_add]
        exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, hk, rfl⟩) (Submodule.subset_span ⟨k, hk, rfl⟩))
    exact Submodule.finiteDimensional_of_le h
  smul_mem' := by
    rintro c Φ ⟨h1, h2⟩
    refine ⟨Submodule.smul_mem _ c h1, ?_⟩
    have h : Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) (c • Φ)} ≤ Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) Φ} :=
      Submodule.span_le.2 (by
        rintro _ ⟨k, hk, rfl⟩
        rw [map_smul]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, hk, rfl⟩))
    exact Submodule.finiteDimensional_of_le h

def sec (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : ℂ := om (1, g) Φ 0

end Defs

end GlobalTheory.SWLow

end
