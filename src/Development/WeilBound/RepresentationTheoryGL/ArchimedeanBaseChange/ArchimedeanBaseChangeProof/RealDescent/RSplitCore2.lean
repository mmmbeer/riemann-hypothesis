import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescentOfLocalGlobalInputs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.RgJS

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def prg (D : Dom E n 0) (ψ : Sm E n) (u : ℝ → ℂ) (φ : Sm E n) : ℂ :=
  ∫ x, starRingEnd ℂ (ψ.1 x.1 * u (ldet x)) * φ.1 x.1 ∂D.ν

def Orth (D : Dom E n 0) (π : CuspSub E n) (φ : Sm E n) : Prop :=
  ∀ ψ ∈ π.V, ∀ u : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → prg D ψ u φ = 0

def OrthAct : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ φ : Sm E n, IsAutForm φ → Orth D π φ → ∀ o, Orth D π (act o φ)

def TwTrEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ φ : H E n 0 → ℂ, IsTestH φ → FinOn D.μ π φ → ∃! t, IsTwTr D.μ π φ t

def AbsSplit : Prop := ForSys fun {W} q X _ A => ∀ (I : Set W), (Summable fun w : I => (q w : ℝ)⁻¹) → ∀ x₀ : X,
  (∀ w ∈ I, ∀ a, ‖A x₀ w a‖ ≤ 1) → ∀ (ι : Type) [Fintype ι] (y : ι → X),
    (∀ w, w ∉ I → ∀ k : ℕ, ∑ a, A x₀ w a ^ (k + 1) = ∑ j, ∑ b, A (y j) w b ^ (k + 1)) → ∃ j, y j = x₀

def InertThin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  Summable fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹

def RSplitCore2 : Prop := AbsSplit → InertThin → DetOne → PrimeOff → RSplitCore

end PositivityTheory.Rg.BcB.Desc

end
