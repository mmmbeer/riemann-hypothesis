import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.CutTrDZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E

namespace PositivityTheory.Rg.BcB.E1

attribute [local instance] borelH

theorem sBound_of (h : SB) : F.SBound := h

theorem bridge_of (h : ProdDom) : F.Bridge := by
  intro E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ h₁ h₂
  obtain ⟨D, hD, hI⟩ := h E a b μ₁ μ₂ F₁ F₂ h₁ h₂
  exact ⟨D, hD, fun τ φ => hI _⟩

theorem opEx_of (h : RatProper) (h1 : OpExA) (h2 : OpAdj) (h3 : OpMul) : F.OpEx := by
  intro E _ _ _ a b D ι _
  refine ⟨fun Φ hΦ => h1 (ctx h D) ι Φ hΦ, fun Φ₁ Φ₂ T₁ T₂ a1 a2 b1 b2 => ?_⟩
  obtain ⟨c1, c2⟩ := h3 (ctx h D) ι Φ₁ Φ₂ T₁ T₂ a1 a2 b1 b2
  exact ⟨c1, c2, h2 (ctx h D) ι Φ₁ T₁ a1 b1⟩

theorem kernel_operator_exists_of (h : F.OpEx) : SmoothSeminormGrowth := by
  intro E _ _ _ a b D ι _ Φ hΦ
  obtain ⟨h1, h2⟩ := h E a b D ι
  obtain ⟨T, hT, -⟩ := h1 Φ hΦ
  exact ⟨T, hT, (h2 Φ Φ T T hΦ hΦ hT hT).2.2, fun Φ' T' a1 a2 => (h2 Φ Φ' T T' hΦ a1 hT a2).2.1⟩


def GrowthJ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (a b : ℕ)
  [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)]
  (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure],
  ∃ D : Dom E a b, ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ))
    (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (r₀ r₁ : ℝ), IsTestM Φ₁ → IsTestM Φ₂ →
    IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ)
      (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ → IsROp D Φ (T₁ * U * T₂) →
      D4.IsTest2J (F.trM Φ M) (r₀ + k * r₁) → ‖ellSum2 μ₁ μ₂ (F.trM Φ M)‖ ≤ C * (1 + k) ^ N * ‖U‖

theorem growthJ_of (hE : D4.EllFormula2J) (hS : F.SBound) (hB : F.Bridge) (hD : DomEx) : GrowthJ := by
  intro E _ _ _ _ a b _ _ _ _ μ₁ _ μ₂ _
  obtain ⟨F₁, h₁⟩ := hD E a μ₁
  obtain ⟨F₂, h₂⟩ := hD E b μ₂
  obtain ⟨D, -, hI⟩ := hB E a b μ₁ μ₂ F₁ F₂ h₁ h₂
  obtain ⟨C₀, hC₀, hell⟩ := hE E a b
  refine ⟨D, fun ι _ Φ₁ Φ₂ T₁ T₂ M r₀ r₁ a1 a2 b1 b2 hr₀ hr₁ => ?_⟩
  obtain ⟨C, N, hb⟩ := hS E a b D ι Φ₁ Φ₂ T₁ T₂ M a1 a2 b1 b2
  refine ⟨|C| * (1 + C₀ * (1 + r₀ + r₁)) ^ N, N, fun k U Φ c1 c2 c3 => ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : 0 ≤ r₀ + k * r₁ := by positivity
  have hτ : 0 ≤ C₀ * (1 + (r₀ + k * r₁)) := by positivity
  rw [← hell μ₁ μ₂ F₁ F₂ _ _ _ h₁ h₂ c3 hr le_rfl, ← hI]
  refine (hb _ U Φ hτ c1 c2).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity) (abs_nonneg C)
  have e1 : 0 ≤ C₀ * (1 + r₀) * k := by positivity
  have e2 : 0 ≤ C₀ * r₁ := by positivity
  nlinarith

end PositivityTheory.Rg.BcB.E1

end
