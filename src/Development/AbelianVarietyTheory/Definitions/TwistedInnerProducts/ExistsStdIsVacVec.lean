import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}




theorem exp_of_even {k : Fin D.R.m} (hk : Even (k : ℕ)) (τ : D.what₂.Tau) :
    expS D k τ = -(D.hc τ).e k - 1 / 2 ∧ expT D k τ = -(D.hc τ).e k := by
  simp [expS, expT, hk]

theorem exp_of_odd {k : Fin D.R.m} (hk : ¬ Even (k : ℕ)) (τ : D.what₂.Tau) :
    expS D k τ = -(D.hc τ).e k ∧ expT D k τ = -(D.hc τ).e k - 1 / 2 := by
  simp [expS, expT, hk]

theorem hasInfExp_div {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ b) : HasInfExp D (χ * η⁻¹) τ (a - b) := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  refine ⟨n - m, by push_cast; rw [hn, hm]; ring, h1, fun θ hθ x hx hτ => ?_⟩
  have e1 := h2 θ hθ x hx hτ
  have e2 := h3 θ hθ x hx hτ
  set z : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hz
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, e1, e2]
  by_cases h0 : z = 0
  · have a1 : n = 0 := by
      by_contra h; exact (χ x).coe_ne_zero (by rw [e1, h0, zero_zpow _ h])
    have a2 : m = 0 := by
      by_contra h; exact (η x).coe_ne_zero (by rw [e2, h0, zero_zpow _ h])
    simp [a1, a2]
  · rw [zpow_sub₀ h0, div_eq_mul_inv]

theorem isHeckeChar_div {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2]; simp⟩


example : signed [1] [2] (1 / 2) = {(3 / 2, true), (5 / 2, false)} := by
  simp [signed]; norm_num

end GlobalTheory.Chain

end
