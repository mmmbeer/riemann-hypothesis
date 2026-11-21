import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConvolutionEqDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacianStatement

section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCAlphaGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def kavg [MeasurableSpace (Kinf E a)] (ν : Measure (Kinf E a)) (F : GL (Fin a) (Cinf E) → ℂ)
    (y : GL (Fin a) (Cinf E)) : ℂ :=
  ∫ k, F (Unitary.toUnits k * y * (Unitary.toUnits k)⁻¹) ∂ν

variable [IsTotallyComplex E]

def liftInf (F : GL (Fin a) (Cinf E) → ℂ) : GA E a → ℂ := fun x => F (Matrix.GeneralLinearGroup.map (pInf E) x)

variable (E a) in

def sphSpace (W₁ W₂ : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) :
    Set (GL (Fin a) (Cinf E) → ℂ) :=
  {F | ∃ h : liftInf F ∈ Sm E a, (∀ y, (fun k : Kinf E a => F (Unitary.toUnits k * y)) ∈ W₁) ∧
    (∀ y, (fun k : Kinf E a => F (y * Unitary.toUnits k)) ∈ W₂) ∧ ∃ χ ∈ X, GlobalTheory.HCF.CentralNilGL χ N ⟨liftInf F, h⟩}

end GlobalTheory.HCAlphaGL

end
end

section
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic

namespace GlobalTheory.HCAlphaGLC

section

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def topE : glG E a ≃ₜ* GL (Fin a) (Cinf E) where
  toMulEquiv := Subgroup.topEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧ HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
  intro E _ _ _ a L _ W hW X hX N _ _ μ hμ
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite E a L W hW X hX N
  obtain ⟨d, b, P, hPm, -, hP⟩ := GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian E a p hp0
  let e := topE E a
  letI : MeasurableSpace (glG E a) := borel _
  haveI : BorelSpace (glG E a) := ⟨rfl⟩
  let μ' : Measure (glG E a) := μ.map e.symm
  have hH : μ'.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  obtain ⟨α', -, hc, hs, hα⟩ := @GlobalTheory.T.exists_smooth_convolution_eq_derivative (Matrix (Fin a) (Fin a) (Cinf E)) _ _ _ _ (glG E a) (glL E a) (glH E a) d b P hPm _ (by exact ⟨rfl⟩) μ' (by exact hH) []
  refine ⟨α' ∘ e.symm, ?_, ?_, fun φ hφ g => ?_⟩
  · exact hc.comp e.symm.continuous
  · exact hs.comp_homeomorph e.symm.toHomeomorph
  obtain ⟨hf, h0⟩ := (mem_solG _ _).1 (hP φ (hp φ hφ) g)
  have h1 := hα ⟨_, hf⟩ h0 1
  have hm : μ' = μ.map e.symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [hm, integral_map_equiv] at h1
  simp only [one_mul, List.foldr_nil] at h1
  exact h1.trans (by simp [glRes])

end

end GlobalTheory.HCAlphaGLC

end
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harishChandra_reproducing_function_GLinfinity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧ HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
  atlas_forward_decl GlobalTheory.HCAlphaGLC.exists_alpha
end

section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCAlphaGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_toUnits_Kinf : Continuous (Unitary.toUnits : Kinf E a → GL (Fin a) (Cinf E)) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite →
    ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧
      HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g :=
  GlobalTheory.T.exists_harishChandra_reproducing_function_GLinfinity

end GlobalTheory.HCAlphaGL

end
end
