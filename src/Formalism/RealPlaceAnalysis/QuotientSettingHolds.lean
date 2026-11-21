import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.LieOperatorConjHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero

section
open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.REAL

def eqvSub {n : ℕ} {ε : Fin n → Bool} (S : Subgroup (UJ ε)) (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (σ : S → E →ₗᵢ[ℂ] E) :
    Submodule ℂ (UJ ε → E) where
  carrier := {F | ∀ (s : S) (g : UJ ε), F ((s : UJ ε) * g) = σ s (F g)}
  add_mem' := by
    intro F F' hF hF' s g
    simp [hF s g, hF' s g]
  zero_mem' := by
    intro s g
    simp
  smul_mem' := by
    intro c F hF s g
    simp [hF s g]

structure HidaSetting (n : ℕ) (ε : Fin n → Bool) where
  E : Type
  [ng : NormedAddCommGroup E]
  [ips : InnerProductSpace ℂ E]
  [cs : CompleteSpace E]
  S : Subgroup (UJ ε)
  σ : S → E →ₗᵢ[ℂ] E
  ν : Measure (UJ ε)

attribute [instance] HidaSetting.ng HidaSetting.ips HidaSetting.cs

def HidaSetting.adm {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) : Submodule ℂ (UJ ε → P.E) :=
  eqvSub P.S P.E P.σ

def Rs {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h : UJ ε) (F : UJ ε → E) : UJ ε → E :=
  fun g => F (g * h)

def IsRightTranslationIsometric {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) : Prop :=
  ∀ F ∈ P.adm, StronglyMeasurable F → ∀ h : UJ ε,
    ∫⁻ g, ‖Rs h F g‖ₑ ^ 2 ∂P.ν = ∫⁻ g, ‖F g‖ₑ ^ 2 ∂P.ν

def settingG {n : ℕ} (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : HidaSetting n ε :=
  { E := E, S := ⊥, σ := fun _ => LinearIsometry.id, ν := muG ε }

def settingQ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (σ : S → E →ₗᵢ[ℂ] E) (ph : UJ ε → ℝ≥0∞) : HidaSetting n ε :=
  { E := E, S := S, σ := σ, ν := (muG ε).withDensity ph }



lemma rs_mul {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h₁ h₂ : UJ ε) (F : UJ ε → E) :
    Rs (h₁ * h₂) F = Rs h₁ (Rs h₂ F) := by
  funext g
  simp only [Rs, mul_assoc]

def LogLogRegularisationSetting : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
    IsRightTranslationIsometric (settingG ε E)

def QuotientSetting : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (muS : Measure S) (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (σ : S → E →ₗᵢ[ℂ] E) (ph : UJ ε → ℝ≥0∞),
    SFinite muS → muS.IsMulLeftInvariant → Measure.map (fun s : S => s⁻¹) muS = muS → Measurable ph →
    (∀ᵐ g ∂(muG ε), ∫⁻ s, ph ((s : UJ ε) * g) ∂muS = 1) →
    IsRightTranslationIsometric (settingQ ε S E σ ph)

end Formalism.REAL
end
end

section
namespace Formalism.REAL
theorem kHaar : KHaar := compact_haar_holds
theorem kExp : KExp := compact_exponential_surjective
theorem genExp : GenExp := genExp_of kExp
theorem rdExtV : RdExtV := vector_right_derivative_extends
theorem rdLeftV : RdLeftV := vector_right_derivative_left_invariant
theorem rdSmoothV : RdSmoothV := rdSmoothV_of rdExtV
theorem rdLinV : RdLinV := rdLinV_of rdExtV
theorem rdBracketV : RdBracketV := rdBracketV_of rdExtV rdSmoothV
theorem eabGlV : EabGlV := eabGlV_of rdLinV rdBracketV rdSmoothV
theorem rdVPair : RdVPair := rdVPair_of rdExtV
theorem ecSumV : EcSumV := ecSumV_of rdLinV
theorem kWtOrth : KWtOrth := compact_weight_orthogonal
theorem kLow : KLow := compact_lowering_holds
theorem kCasSpan : KCasSpan := compact_casimir_span_holds
theorem kOrth : KOrth := kOrth_of kLow kWtOrth
theorem kHiUniq : KHiUniq := kHiUniq_of kLow kWtOrth kOrth
theorem kHiExist : KHiExist := highestWeightExists_holds
theorem kIrr : KIrr := kIrr_of kHiExist kHiUniq
theorem kDecomp : KDecomp := kDecomp_of kHiExist kOrth
theorem kIsoSplit : KIsoSplit := kIsoSplit_of kDecomp kOrth
theorem kWtBound : KWtBound := kWtBound_of kCasSpan
theorem kCasBound : KCasBound := kCasBound_of kDecomp kCasSpan kOrth
theorem casOnCyc : CasOnCyc := casimir_on_cyclic_holds
theorem pfilFacts : PfilFacts := pfil_facts_hold
theorem arrModule : ArrModule := arr_module_facts
theorem thetaFil : ThetaFil := theta_filtration_holds
theorem hVCoeff : HVCoeff := hVCoeff_of kLow kWtOrth arrModule
theorem typesSplit : TypesSplit := typesSplit_of hVCoeff kIsoSplit arrModule
theorem casArr : CasArr := casArr_of kCasSpan
theorem omSymSlice : OmSymSlice := symmetricSliceMixedCasimir_holds
theorem nStable : NStable := positiveArraysInvariant_holds
theorem omPlus : OmPlus := omPlus_of kDecomp kOrth kCasSpan casArr arrModule
theorem nPos : NPos := nPos_of casArr omSymSlice omPlus
end Formalism.REAL
end
