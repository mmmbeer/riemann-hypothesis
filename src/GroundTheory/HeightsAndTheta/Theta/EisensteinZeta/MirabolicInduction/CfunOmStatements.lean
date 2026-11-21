import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup ModularForm Complex NumberField
open scoped Real Modular MatrixGroups nonZeroDivisors

section Objects

def etaPeriod (τ : ℍ) : ℝ := 4 * π * τ.im * ‖η (τ : ℂ)‖ ^ 4

def etaLogPeriod (τ : ℍ) : ℝ := Real.log (etaPeriod τ)

def negConj (τ : ℍ) : ℍ := ⟨-(starRingEnd ℂ) (τ : ℂ), by simpa using τ.im_pos⟩

def latticeOf (τ : ℂ) : Set ℂ := (Submodule.span ℤ ({1, τ} : Set ℂ) : Set ℂ)

def IsLatticeParam (Λ : Set ℂ) (τ : ℍ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ (fun z => c * z) '' Λ = latticeOf (τ : ℂ)

def latticeReducedParams (Λ : Set ℂ) : Set ℍ := {τ | τ ∈ 𝒟 ∧ IsLatticeParam Λ τ}

variable {K : Type*} [Field K] [NumberField K]

def classReducedParams (σ : K →+* ℂ) (A : ClassGroup (𝓞 K)) : Set ℍ :=
  {τ | ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = A ∧
    τ ∈ latticeReducedParams (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K))}

def classTau (σ : K →+* ℂ) (A : ClassGroup (𝓞 K)) : ℍ :=
  Classical.epsilon (fun τ => τ ∈ classReducedParams σ A)

def classPeriod (σ : K →+* ℂ) (A : ClassGroup (𝓞 K)) : ℝ := etaPeriod (classTau σ A)

def classLogPeriod (σ : K →+* ℂ) (A : ClassGroup (𝓞 K)) : ℝ := Real.log (classPeriod σ A)

def legendreCharacter (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

def logPeriodConstant (d : ℕ) [Fact d.Prime] : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * π / Real.sqrt d) -
    (deriv (DirichletCharacter.LFunction (legendreCharacter d)) 1 /
      DirichletCharacter.LFunction (legendreCharacter d) 1).re

end Objects

section Statements

def EtaPeriodModularInvariant.Statement : Prop :=
  ∀ (γ : SL(2, ℤ)) (τ : ℍ), etaPeriod (γ • τ) = etaPeriod τ

def EtaPeriodLatticeClass.Statement : Prop :=
  ∀ (Λ : Set ℂ) (τ τ' : ℍ), IsLatticeParam Λ τ → IsLatticeParam Λ τ' → etaPeriod τ = etaPeriod τ'

def EtaLogPeriodNegConj.Statement : Prop :=
  ∀ τ : ℍ, etaLogPeriod (negConj τ) = etaLogPeriod τ

def EtaLogPeriodConj.Statement : Prop :=
  ∀ (Λ : Set ℂ) (τ τ' : ℍ), IsLatticeParam Λ τ → IsLatticeParam ((starRingEnd ℂ) '' Λ) τ' →
    etaLogPeriod τ' = etaLogPeriod τ

def ClassReducedParamsNonempty.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ σ : K →+* ℂ, (∃ x : K, (σ x).im ≠ 0) →
      ∀ A : ClassGroup (𝓞 K), (classReducedParams σ A).Nonempty

def ClassFunctionsWellDefined.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ σ : K →+* ℂ, (∃ x : K, (σ x).im ≠ 0) →
      ∀ (A : ClassGroup (𝓞 K)) (τ τ' : ℍ), τ ∈ classReducedParams σ A →
        τ' ∈ classReducedParams σ A → τ.im = τ'.im ∧ etaPeriod τ = etaPeriod τ'

def ClassPeriodInv.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ σ : K →+* ℂ, (∃ x : K, (σ x).im ≠ 0) →
      ∀ A : ClassGroup (𝓞 K), classPeriod σ A⁻¹ = classPeriod σ A

def LogDerivLReal.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], legendreCharacter d ≠ 1 →
    (deriv (DirichletCharacter.LFunction (legendreCharacter d)) 1 /
      DirichletCharacter.LFunction (legendreCharacter d) 1).im = 0

end Statements

section Ties

theorem etaPeriod_pos (τ : ℍ) : 0 < etaPeriod τ := by
  have h : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.im_pos
  unfold etaPeriod
  have : 0 < ‖η (τ : ℂ)‖ := norm_pos_iff.mpr h
  have := τ.im_pos
  positivity



instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩





end Ties

end GroundTheory.Heights₂.Theta
