import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality

open Module

noncomputable section

namespace Formalism.SLP.GlobalBoundRefinements.P

open Formalism.SLP.GlobalBoundRefinements

theorem card_linearEquiv_le : Formalism.SLP.GlobalBoundRefinements.AutCount := by
  intro R M _ _ _ _ e v hv
  have hinj : Function.Injective (fun f : M ≃ₗ[R] M => fun i => f (v i)) := by
    intro f g hfg
    apply LinearEquiv.toLinearMap_injective
    exact LinearMap.ext_on_range hv (fun i => congrFun hfg i)
  calc Nat.card (M ≃ₗ[R] M) ≤ Nat.card (Fin e → M) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card M ^ e := by rw [Nat.card_fun, Nat.card_fin]

set_option maxHeartbeats 800000 in
theorem coefficients_of_form_preserving : Formalism.SLP.GlobalBoundRefinements.FormCoeff := by
  intro a b c d T T' hT hT' hform
  have h10 := hform 1 0
  have h01 := hform 0 1
  simp only [mul_one, mul_zero, add_zero, zero_add, norm_one, norm_zero, one_pow] at h10 h01
  norm_num at h10 h01
  have e1 : ‖a‖ ^ 2 - 1 = T' * ‖c‖ ^ 2 / T := by
    field_simp
    linarith
  have e2 : ‖d‖ ^ 2 - 1 = T * ‖b‖ ^ 2 / T' := by
    field_simp
    linarith
  refine ⟨e1, e2, fun ha => ?_⟩
  have hc2 : ‖c‖ ^ 2 = 0 := by
    rw [ha] at h10
    nlinarith [sq_nonneg ‖c‖]
  have hc : c = 0 := by simpa using hc2
  have haa : a * (starRingEnd ℂ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hx := hform (starRingEnd ℂ a * b) 1
  have h2b : a * (starRingEnd ℂ a * b) + b * 1 = 2 * b := by
    rw [← mul_assoc, haa]
    ring
  rw [h2b, hc] at hx
  simp only [zero_mul, zero_add, mul_one, norm_mul, Complex.norm_conj, ha, one_mul, norm_one,
    one_pow] at hx
  norm_num at hx
  have hb2 : ‖b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖b‖]
  have hb : b = 0 := by simpa using hb2
  refine ⟨hc, hb, ?_⟩
  rw [hb, norm_zero] at e2
  have hd2 : ‖d‖ ^ 2 = 1 := by linarith [e2, show T * (0:ℝ) ^ 2 / T' = 0 by simp]
  nlinarith [norm_nonneg d]



end Formalism.SLP.GlobalBoundRefinements.P
