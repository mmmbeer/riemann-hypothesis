import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFormConstL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartzStatement

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.SchOp

theorem iteratedDeriv_cexp_real (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_ech : Function.HasTemperateGrowth ech := by
  set a : ℂ := -(2 * Real.pi * Complex.I) with ha
  have e : ech = fun y : ℝ => Complex.exp (a * y) := rfl
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (a * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨by rw [e]; exact hc, fun n => ⟨0, ‖a‖ ^ n, fun x => ?_⟩⟩
  rw [e, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (a * x)‖ = 1 := by
    have : a * (x : ℂ) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by rw [ha]; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_ech_affine {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Y →L[ℝ] ℝ) (c : ℝ) : Function.HasTemperateGrowth (fun x : Y => ech (L x + c)) :=
  hasTemperateGrowth_ech.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))

theorem sch_schwartz {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : SchwartzMap Y ℂ) : ∃ g : SchwartzMap Y ℂ, ⇑g = sch β a b ⇑f := by
  let L : Y →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (β.flip b)
  have hL : ∀ x, L x = β x b := fun x => rfl
  have hm : Function.HasTemperateGrowth (fun x : Y => ech (β x b + β a b / 2)) := by
    simpa only [hL] using hasTemperateGrowth_ech_affine L (β a b / 2)
  have ht : Function.HasTemperateGrowth (fun x : Y => x + a) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)
  have hu : ∃ (k : ℕ) (C : ℝ), ∀ x : Y, ‖x‖ ≤ C * (1 + ‖x + a‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, fun x => ?_⟩
    have h1 : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
      calc ‖x‖ = ‖(x + a) - a‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
    have h2 := norm_nonneg (x + a)
    have h3 := norm_nonneg a
    rw [pow_one]
    nlinarith
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x b + β a b / 2)) (SchwartzMap.compCLM ℂ ht hu f), ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, SchwartzMap.compCLM_apply]
  simp [sch, smul_eq_mul]

end GlobalTheory.SchOp
end

section
open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

noncomputable section

namespace GlobalTheory.ArchUniqStd

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def bil {P : V → V → ℝ} (h : IsPairing P) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ P h.addL (fun c x y => by simpa [smul_eq_mul] using h.smulL c x y) h.addR
    (fun c x y => by simpa [smul_eq_mul] using h.smulR c x y)

theorem bil_apply {P : V → V → ℝ} (h : IsPairing P) (x y : V) : bil h x y = P x y := rfl

theorem schrF_schwartz [FiniteDimensional ℝ V] {P : V → V → ℝ} (h : IsPairing P) (w : V × V) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), ⇑g = schrF P w ⇑f := by
  obtain ⟨g, hg⟩ := GlobalTheory.SchOp.sch_schwartz (bil h) w.1 w.2 f
  exact ⟨g, hg⟩

theorem exists_right [FiniteDimensional ℝ V] {P : V → V → ℝ} (h : IsPairing P) (L : V →L[ℝ] ℝ) :
    ∃ b, ∀ y, P y b = L y := by
  have hinj : Function.Injective (bil h).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact h.nondegR b fun x => by simpa [bil_apply] using LinearMap.congr_fun hb x
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  obtain ⟨b, hb⟩ := hsurj (L : V →ₗ[ℝ] ℝ)
  exact ⟨b, fun y => by simpa [bil_apply] using LinearMap.congr_fun hb y⟩

def evAt (x : V) : 𝓢(V, ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)

theorem evAt_apply (x : V) (f : 𝓢(V, ℂ)) : evAt x f = f x := rfl

theorem exists_one [FiniteDimensional ℝ V] : ∃ Φ : 𝓢(V, ℂ), Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

end GlobalTheory.ArchUniqStd

namespace GlobalTheory.ArchUniqStd

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]

end GlobalTheory.ArchUniqStd

namespace GlobalTheory.ArchUniqStd

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]

end GlobalTheory.ArchUniqStd
end
end

section
open MeasureTheory

namespace GlobalTheory
namespace SchwartzIntegralExchange

theorem exists_factor {S X : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup X]
    [NormedSpace ℂ X] (J : S →ₗ[ℂ] X) (Λ : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖Λ w‖ ≤ C * ‖J w‖) :
    ∃ g : X →L[ℂ] ℂ, ∀ w, g (J w) = Λ w := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective J.rangeRestrict
    J.range_rangeRestrict
  have hr' : ∀ y : LinearMap.range J, J (r y) = y := fun y => by
    have := congrArg (fun φ : LinearMap.range J →ₗ[ℂ] LinearMap.range J => (φ y : X)) hr
    simpa using this
  let f : LinearMap.range J →L[ℂ] ℂ := (Λ ∘ₗ r).mkContinuous C (fun y => by
    have := h (r y)
    rw [hr'] at this
    simpa using this)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨g, fun w => ?_⟩
  have h1 := hg ⟨J w, w, rfl⟩
  have h2 := h (r ⟨J w, w, rfl⟩ - w)
  rw [map_sub J, hr'] at h2
  simp only [sub_self, norm_zero, mul_zero, norm_le_zero_iff, map_sub, sub_eq_zero] at h2
  rw [← h2]
  simpa [f] using h1

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def wtFun (k n : ℕ) (w : SchwartzMap E ℂ) :
    BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x)
    ((continuous_norm.pow k).smul ((w.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k n w)
    (fun x => by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact SchwartzMap.le_seminorm ℂ k n w x)

theorem wtFun_apply (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wtFun k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := rfl

theorem norm_wtFun_le (k n : ℕ) (w : SchwartzMap E ℂ) :
    ‖wtFun k n w‖ ≤ SchwartzMap.seminorm ℂ k n w :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _

theorem le_norm_wtFun (k n : ℕ) (w : SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℂ k n w ≤ ‖wtFun k n w‖ := by
  refine SchwartzMap.seminorm_le_bound ℂ k n w (norm_nonneg _) (fun x => ?_)
  have := (wtFun k n w).norm_coe_le_norm x
  rwa [wtFun_apply, norm_smul, Real.norm_of_nonneg (by positivity)] at this

noncomputable def wt (k n : ℕ) : SchwartzMap E ℂ →L[ℂ]
    BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (wtFun k n)
    (fun f g => by
      ext1 x
      have hf : ContDiffAt ℝ n f x := ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      have hg : ContDiffAt ℝ n g x := ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      rw [BoundedContinuousFunction.add_apply, wtFun_apply, wtFun_apply, wtFun_apply, ← smul_add,
        ← iteratedFDeriv_add_apply hf hg]
      rfl)
    (fun a f => by
      ext1 x
      have hf : ContDiffAt ℝ n f x := ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      rw [BoundedContinuousFunction.smul_apply, wtFun_apply, wtFun_apply, RingHom.id_apply,
        smul_comm a, ← iteratedFDeriv_const_smul_apply hf]
      rfl)
    ⟨{(k, n)}, 1, zero_le_one, fun f => by
      simpa using norm_wtFun_le k n f⟩

theorem wt_apply (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wt k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := rfl

theorem wt_eq (k n : ℕ) (w : SchwartzMap E ℂ) : wt k n w = wtFun k n w := rfl

theorem continuous_iteratedFDeriv_at (n : ℕ) (x : E) :
    Continuous (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) := by
  have : (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) = fun w => wt 0 n w x := by
    funext w; simp [wt_apply]
  rw [this]
  exact (continuous_eval_const x).comp (wt 0 n).continuous

variable {P : Type} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {ν : Measure P} {Φ : P → SchwartzMap E ℂ} {c : P → ℂ}

theorem integrable_iteratedFDeriv (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (n : ℕ) (x : E) : Integrable (fun ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x) ν := by
  refine (hi 0 n).mono' (hc.smul
    ((continuous_iteratedFDeriv_at n x).comp hΦ).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ n x)
    (norm_nonneg _)

theorem iteratedFDeriv_integral (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (u : E → ℂ) (hu : ∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) (n : ℕ) :
    ∀ x, iteratedFDeriv ℝ n u x = ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν := by
  induction n with
  | zero =>
    intro x
    ext m
    rw [ContinuousMultilinearMap.integral_apply (integrable_iteratedFDeriv hΦ hc hi 0 x)]
    simp [hu]
  | succ n ih =>
    intro x
    set L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ with hL
    have hfun : iteratedFDeriv ℝ n u = fun x => ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν :=
      funext ih
    have hd : HasFDerivAt (fun x => ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν)
        (∫ ξ, L (c ξ • iteratedFDeriv ℝ (n + 1) (Φ ξ) x) ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
        (F := fun x ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x)
        (F' := fun x ξ => L (c ξ • iteratedFDeriv ℝ (n + 1) (Φ ξ) x))
        (bound := fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ 0 (n + 1) (Φ ξ))
        Filter.univ_mem
        (Filter.Eventually.of_forall fun y =>
          (integrable_iteratedFDeriv hΦ hc hi n y).aestronglyMeasurable)
        (integrable_iteratedFDeriv hΦ hc hi n x)
        (L.continuous.comp_aestronglyMeasurable
          (integrable_iteratedFDeriv hΦ hc hi (n + 1) x).aestronglyMeasurable)
        (ae_of_all _ fun ξ y _ => ?_) (hi 0 (n + 1)) (ae_of_all _ fun ξ y _ => ?_)
      · rw [LinearIsometryEquiv.norm_map, norm_smul]
        exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ _ y)
          (norm_nonneg _)
      · have h1 : DifferentiableAt ℝ (iteratedFDeriv ℝ n (Φ ξ)) y :=
          ((Φ ξ).smooth ⊤).differentiable_iteratedFDeriv
            (by exact_mod_cast ENat.coe_lt_top n) y
        have h2 := h1.hasFDerivAt.const_smul (c ξ)
        rw [fderiv_iteratedFDeriv] at h2
        exact h2
    have h3 := hd.fderiv
    rw [← hfun, fderiv_iteratedFDeriv] at h3
    apply L.injective
    exact h3.trans (L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (integrable_iteratedFDeriv hΦ hc hi (n + 1) x))

theorem integrable_wt (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (k n : ℕ) : Integrable (fun ξ => c ξ • wt k n (Φ ξ)) ν := by
  refine (hi k n).mono' (hc.smul
    ((wt k n).continuous.comp hΦ).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_wtFun_le k n _) (norm_nonneg _)

theorem wt_integral (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (u : SchwartzMap E ℂ) (hu : ∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) (k n : ℕ) :
    wt k n u = ∫ ξ, c ξ • wt k n (Φ ξ) ∂ν := by
  ext1 x
  have := (BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm
    (integrable_wt hΦ hc hi k n)
  simp only [BoundedContinuousFunction.evalCLM_apply] at this
  rw [← this, wt_apply, iteratedFDeriv_integral hΦ hc hi u hu n x, ← integral_smul]
  congr 1
  funext ξ
  rw [BoundedContinuousFunction.smul_apply, wt_apply, smul_comm]

end SchwartzIntegralExchange

open SchwartzIntegralExchange in

theorem schwartz_clm_integral_comm :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Type) [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] (ν : Measure P)
    (Φ : P → SchwartzMap E ℂ), Continuous Φ → ∀ (c : P → ℂ), AEStronglyMeasurable c ν →
    (∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν) →
    ∀ (u : SchwartzMap E ℂ), (∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) →
    ∀ (Λ : SchwartzMap E ℂ →L[ℂ] ℂ), Λ u = ∫ ξ, c ξ * Λ (Φ ξ) ∂ν := by
  intro E _ _ P _ _ _ _ ν Φ hΦ c hc hi u hu Λ
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp Λ.toLinearMap) (continuous_norm.comp Λ.continuous)
  let J : SchwartzMap E ℂ →L[ℂ] (∀ i : s, BoundedContinuousFunction E
      (ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)) :=
    ContinuousLinearMap.pi fun i => wt i.1.1 i.1.2
  obtain ⟨g, hg⟩ := exists_factor J.toLinearMap Λ.toLinearMap C (fun w => by
    have h1 : ‖Λ w‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) w := hC w
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
    exact (le_norm_wtFun i.1 i.2 w).trans (norm_le_pi_norm (J w) ⟨i, hi⟩))
  have hg' : ∀ w, g (J w) = Λ w := hg
  have hint : Integrable (fun ξ => c ξ • J (Φ ξ)) ν :=
    integrable_pi_iff.2 fun i => integrable_wt hΦ hc hi i.1.1 i.1.2
  have hJ : J u = ∫ ξ, c ξ • J (Φ ξ) ∂ν := by
    funext i
    rw [eval_integral (integrable_pi_iff.1 hint)]
    exact wt_integral hΦ hc hi u hu i.1.1 i.1.2
  rw [← hg', hJ, ← g.integral_comp_comm hint]
  simp [hg']

end GlobalTheory
end

section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_integral_superposition : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Type) [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] (ν : Measure P)
    (Φ : P → SchwartzMap E ℂ), Continuous Φ → ∀ (c : P → ℂ), AEStronglyMeasurable c ν →
    (∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν) →
    ∀ (u : SchwartzMap E ℂ), (∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) →
    ∀ (Λ : SchwartzMap E ℂ →L[ℂ] ℂ), Λ u = ∫ ξ, c ξ * Λ (Φ ξ) ∂ν := by
  first | exact @GlobalTheory.schwartz_clm_integral_comm | exact GlobalTheory.schwartz_clm_integral_comm | (intros; apply GlobalTheory.schwartz_clm_integral_comm <;> assumption)
end

section
section
open Complex MeasureTheory

namespace GlobalTheory.CharFamily

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem seminorm_mul_le (c : E → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (h g : SchwartzMap E ℂ)
    (hg : ∀ x, g x = c x * h x) (k n m : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcb : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i c x‖ ≤ M * (1 + ‖x‖) ^ m) :
    SchwartzMap.seminorm ℂ k n g ≤ 2 ^ n * M *
      (2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h) := by
  set S := 2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h
    with hS
  have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine SchwartzMap.seminorm_le_bound ℂ k n g (by positivity) fun x => ?_
  have hg' : (⇑g) = fun x => c x * h x := funext hg
  rw [hg']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) hc (h.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖)
        ≤ (n.choose i : ℝ) * (M * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := hcb i hi' x
    have h2 : (1 + ‖x‖) ^ (k + m) * ‖iteratedFDeriv ℝ (n - i) h x‖ ≤ S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + m, n)) le_rfl (Nat.sub_le n i) h x
    have h5 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
    have hc0 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖)
        = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i c x‖ *
            ‖iteratedFDeriv ℝ (n - i) h x‖) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + ‖x‖) ^ k * (M * (1 + ‖x‖) ^ m) *
            ‖iteratedFDeriv ℝ (n - i) h x‖) := by gcongr
      _ = (n.choose i : ℝ) * (M * ((1 + ‖x‖) ^ (k + m) * ‖iteratedFDeriv ℝ (n - i) h x‖)) := by
            ring
      _ ≤ (n.choose i : ℝ) * (M * S) := by gcongr
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => c y * h y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * S) := Finset.sum_le_sum hterm
    _ = 2 ^ n * M * S := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring

theorem contDiff_char (L : E →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => Complex.exp (I * (L x : ℂ))) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (I * (y : ℂ))) := by fun_prop
  exact hc.comp L.contDiff

theorem norm_iteratedFDeriv_char_le (L : E →L[ℝ] ℝ) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => Complex.exp (I * (L x : ℂ))) x‖ ≤ ‖L‖ ^ i := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) := by
    fun_prop
  have e : (fun x : E => Complex.exp (I * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  rw [e, L.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ i (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) (L x)‖
          * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
        have hexp : I * ((L x : ℝ) : ℂ) = ((L x : ℝ) : ℂ) * I := by ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, Complex.norm_I]
        simp

theorem norm_iteratedFDeriv_char_sub_one_le (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => Complex.exp (I * (L x : ℂ)) - 1) x‖
      ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ℝ => (1 : ℂ) * Complex.exp (I * y) + 0 * y + (-1)) := by fun_prop
  have e : (fun x : E => Complex.exp (I * (L x : ℂ)) - 1)
      = (fun y : ℝ => (1 : ℂ) * Complex.exp (I * y) + 0 * y + (-1)) ∘ ⇑L := by
    funext x; simp; ring
  rw [e, L.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  cases i with
  | zero =>
    rw [iteratedDeriv_zero, pow_zero, mul_one]
    have h0 : (1 : ℂ) * Complex.exp (I * ((L x : ℝ) : ℂ)) + 0 * ((L x : ℝ) : ℂ) + (-1)
        = Complex.exp (((L x : ℝ) : ℂ) * I) - 1 := by ring_nf
    simp only [h0]
    calc _ ≤ 2 * |L x| := GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_le (L x)
      _ ≤ 2 * (‖L‖ * ‖x‖) := by gcongr; rw [← Real.norm_eq_abs]; exact L.le_opNorm x
      _ ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by nlinarith
  | succ j =>
    rw [iteratedDeriv_succ', GlobalTheory.CharFormDeriv.deriv_affine_cexp]
    have hd : (fun y : ℝ => (1 : ℂ) * I * Complex.exp (I * y) + 0)
        = fun y : ℝ => I * Complex.exp (I * y) := by funext y; ring
    rw [hd, GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
    have hexp : I * ((L x : ℝ) : ℂ) = ((L x : ℝ) : ℂ) * I := by ring
    rw [norm_mul, norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_pow, Complex.norm_I]
    simp only [one_pow, mul_one, one_mul]
    calc ‖L‖ ^ (j + 1) ≤ ‖L‖ ^ 1 := pow_le_pow_of_le_one hL0 hL (by omega)
      _ ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by nlinarith

theorem one_add_pow_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  have han : 0 ≤ a ^ n := pow_nonneg ha n
  rcases le_total a 1 with h | h
  · have : (1 + a) ^ n ≤ 2 ^ n := by gcongr; linarith
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
  · have : (1 + a) ^ n ≤ (2 * a) ^ n := by gcongr; linarith
    rw [mul_pow] at this
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]

theorem charMul_family : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by
  intro E P _ _ _ _ A f
  have htg : ∀ L : E →L[ℝ] ℝ,
      Function.HasTemperateGrowth (fun x : E => Complex.exp (I * (L x : ℂ))) := fun L => by
    simpa using GlobalTheory.CharFormDeriv.hasTemperateGrowth_char L 1
  let Φ : P → SchwartzMap E ℂ := fun ξ =>
    SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.exp (I * (A ξ x : ℂ))) f
  have hΦ : ∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x := fun ξ x => by
    simp only [Φ, SchwartzMap.smulLeftCLM_apply_apply (htg (A ξ)), smul_eq_mul]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun ζ => ?_
    unfold ContinuousAt
    rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds Φ (Φ ζ)]
    rintro ⟨k, n⟩ ε hε
    set K := 2 * 2 ^ n * (2 ^ (k + 1) *
      ((Finset.Iic (k + 1, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) (Φ ζ)) with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) (mul_nonneg (by positivity) (apply_nonneg _ _))
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    set m := min 1 (ε / (K + 1)) with hm
    have hm0 : 0 < m := lt_min one_pos (div_pos hε (by linarith))
    have hδ : 0 < m / (‖A‖ + 1) := div_pos hm0 (by linarith)
    filter_upwards [Metric.ball_mem_nhds ζ hδ] with η hη
    rw [Metric.mem_ball, dist_eq_norm] at hη
    show SchwartzMap.seminorm ℂ k n (Φ η - Φ ζ) < ε
    set L := A (η - ζ) with hLdef
    have hLle : ‖L‖ ≤ ‖A‖ * ‖η - ζ‖ := A.le_opNorm _
    have hLm : ‖L‖ < m := by
      calc ‖L‖ ≤ ‖A‖ * ‖η - ζ‖ := hLle
        _ ≤ (‖A‖ + 1) * ‖η - ζ‖ := by gcongr; linarith
        _ < (‖A‖ + 1) * (m / (‖A‖ + 1)) := by gcongr
        _ = m := by field_simp
    have hL1 : ‖L‖ ≤ 1 := (lt_of_lt_of_le hLm (min_le_left _ _)).le
    have hLε : ‖L‖ < ε / (K + 1) := lt_of_lt_of_le hLm (min_le_right _ _)
    have hpt : ∀ x, (Φ η - Φ ζ) x = (Complex.exp (I * (L x : ℂ)) - 1) * Φ ζ x := fun x => by
      have hs : A η x = L x + A ζ x := by simp [hLdef, map_sub]
      rw [SchwartzMap.sub_apply, hΦ, hΦ, hs]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
    have hb := seminorm_mul_le (fun x : E => Complex.exp (I * (L x : ℂ)) - 1)
      ((contDiff_char L).sub contDiff_const) (Φ ζ) (Φ η - Φ ζ) hpt k n 1 (2 * ‖L‖)
      (by positivity) (fun i _ x => norm_iteratedFDeriv_char_sub_one_le L hL1 i x)
    calc SchwartzMap.seminorm ℂ k n (Φ η - Φ ζ) ≤ ‖L‖ * K := by rw [hK]; linarith [hb]
      _ ≤ ‖L‖ * (K + 1) := by gcongr; linarith
      _ < ε / (K + 1) * (K + 1) := by gcongr
      _ = ε := by field_simp
  · intro k n
    set S := 2 ^ (k + 0) * ((Finset.Iic (k + 0, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) f
      with hS
    have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
    refine ⟨2 ^ n * ((1 + ‖A‖) ^ n * 2 ^ n) * S, fun ξ => ?_⟩
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
    set L := A ξ with hLdef
    have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
    have hb := seminorm_mul_le (fun x : E => Complex.exp (I * (L x : ℂ))) (contDiff_char L) f (Φ ξ)
      (hΦ ξ) k n 0 ((1 + ‖L‖) ^ n) (by positivity) (fun i hi x => by
        rw [pow_zero, mul_one]
        calc _ ≤ ‖L‖ ^ i := norm_iteratedFDeriv_char_le L i x
          _ ≤ (1 + ‖L‖) ^ i := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi)
    have h1 : (1 + ‖L‖) ^ n ≤ (1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n)) := by
      calc (1 + ‖L‖) ^ n ≤ ((1 + ‖A‖) * (1 + ‖ξ‖)) ^ n := by
            gcongr
            have := A.le_opNorm ξ
            nlinarith
        _ = (1 + ‖A‖) ^ n * (1 + ‖ξ‖) ^ n := mul_pow _ _ _
        _ ≤ (1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n)) := by
            gcongr; exact one_add_pow_le _ hξ0 n
    calc SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ 2 ^ n * (1 + ‖L‖) ^ n * S := hb
      _ ≤ 2 ^ n * ((1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n))) * S := by gcongr
      _ = 2 ^ n * ((1 + ‖A‖) ^ n * 2 ^ n) * S * (1 + ‖ξ‖ ^ n) := by ring

end GlobalTheory.CharFamily
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_family_phase_bound : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by
  atlas_forward_decl GlobalTheory.CharFamily.charMul_family
end

section
section
open MeasureTheory

namespace GlobalTheory

open Real in

theorem schwartz_eq_fourier_synthesis :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (m : SchwartzMap V ℂ),
    ∃ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] V →L[ℝ] ℝ) (h : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ),
    ∀ x, m x = ∫ ξ, h ξ * Complex.exp (Complex.I * (A ξ x : ℂ)) := by
  intro V _ _ _ m
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let m' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm m
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V →L[ℝ] ℝ :=
    (2 * π) • (((ContinuousLinearMap.compL ℝ V _ ℝ).flip (e : V →L[ℝ] _)).comp (innerSL ℝ))
  have hA : ∀ ξ x, A ξ x = 2 * π * inner ℝ ξ (e x) := by
    intro ξ x
    simp [A]
  refine ⟨Module.finrank ℝ V, A, (FourierTransform.fourier m' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ), fun x => ?_⟩
  have h1 : m x = m' (e x) := by
    simp [m']
  have h2 := congrArg (fun f : SchwartzMap _ ℂ => f (e x)) (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ) m')
  rw [h1, ← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  ext ξ
  rw [hA, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_fourier_representation : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (m : SchwartzMap V ℂ),
    ∃ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] V →L[ℝ] ℝ) (h : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ),
    ∀ x, m x = ∫ ξ, h ξ * Complex.exp (Complex.I * (A ξ x : ℂ)) := by
  atlas_forward_decl GlobalTheory.schwartz_eq_fourier_synthesis
end

section
open MeasureTheory

namespace GlobalTheory

theorem schwartz_pairing_conj_clm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  intro V _ _ _ μ hμ w
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hg : Function.HasTemperateGrowth (fun x => starRingEnd ℂ (w x)) :=
    (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp w.hasTemperateGrowth
  refine ⟨(SchwartzMap.integralCLM ℂ μ).comp (SchwartzMap.smulLeftCLM ℂ (fun x => starRingEnd ℂ (w x))), ?_⟩
  intro u
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  congr 1
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, mul_comm]

end GlobalTheory

alias _root_.GlobalTheory.T.schwartz_inner_product_continuous := _root_.GlobalTheory.schwartz_pairing_conj_clm
end

section
section
open MeasureTheory

namespace GlobalTheory.CharMult

theorem multiplier_symm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by
  intro V _ _ _ μ hμ T hT m f f' g g' hf' hg'
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  obtain ⟨d, A, h, hm⟩ := GlobalTheory.T.schwartz_fourier_representation V m
  obtain ⟨Φf, hΦf, cΦf, bΦf⟩ := GlobalTheory.T.schwartz_family_phase_bound V _ A f
  obtain ⟨Φg, hΦg, cΦg, bΦg⟩ := GlobalTheory.T.schwartz_family_phase_bound V _ (-A) g
  obtain ⟨Λ1, hΛ1⟩ := GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T g)
  obtain ⟨Λ2, hΛ2⟩ := GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T f)
  have hint : ∀ (Φ : EuclideanSpace ℝ (Fin d) → SchwartzMap V ℂ), Continuous Φ →
      (∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n)) →
      ∀ (c : EuclideanSpace ℝ (Fin d) → ℂ), (∀ ξ, ‖c ξ‖ = ‖h ξ‖) →
      ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) := by
    intro Φ hΦ hb c hc k n
    obtain ⟨C, hC⟩ := hb k n
    have hcont : Continuous (fun ξ => SchwartzMap.seminorm ℂ k n (Φ ξ)) :=
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)).comp hΦ
    have i1 : Integrable (fun ξ => ‖h ξ‖) := h.integrable.norm
    have i2 : Integrable (fun ξ => ‖ξ‖ ^ n * ‖h ξ‖) := h.integrable_pow_mul volume n
    refine Integrable.mono' ((i1.add i2).const_mul C) ?_ ?_
    · simp_rw [hc]
      exact (h.continuous.norm.mul hcont).aestronglyMeasurable
    · filter_upwards with ξ
      rw [hc, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))]
      calc ‖h ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ ‖h ξ‖ * (C * (1 + ‖ξ‖ ^ n)) :=
            mul_le_mul_of_nonneg_left (hC ξ) (norm_nonneg _)
        _ = C * (‖h ξ‖ + ‖ξ‖ ^ n * ‖h ξ‖) := by ring

  have hkey : ∀ ξ, Λ1 (T (Φf ξ)) = ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    intro ξ
    rw [hΛ1]
    refine hT (A ξ) f (Φf ξ) (Φg ξ) g (hΦf ξ) (fun x => ?_)
    rw [hΦg, ← mul_assoc, ← Complex.exp_add]
    simp [ContinuousLinearMap.neg_apply]
  have lhs : ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    rw [← hΛ1]
    have := GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φf cΦf h h.continuous.aestronglyMeasurable
      (hint Φf cΦf bΦf h (fun _ => rfl)) f' (fun x => by
        rw [hf', hm, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦf]; ring) (Λ1.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]; simp_rw [hkey]
  have rhs : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    have e1 : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = starRingEnd ℂ (Λ2 (T g')) := by
      rw [hΛ2, ← integral_conj]; congr 1; funext x; simp [mul_comm]
    have := GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φg cΦg (fun ξ => starRingEnd ℂ (h ξ))
      (Complex.continuous_conj.comp h.continuous).aestronglyMeasurable
      (hint Φg cΦg bΦg _ (fun _ => Complex.norm_conj _)) g' (fun x => by
        rw [hg', hm, ← integral_conj, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦg]
        simp only [map_mul, ContinuousLinearMap.neg_apply, ← Complex.exp_conj]
        simp [Complex.ofReal_neg]; ring) (Λ2.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [e1, this, ← integral_conj]
    congr 1; funext ξ
    rw [map_mul, Complex.conj_conj, hΛ2, ← integral_conj]
    congr 2; funext x; simp [mul_comm]
  rw [lhs, rhs]

end GlobalTheory.CharMult
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_character_invariant_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by
  atlas_forward_decl GlobalTheory.CharMult.multiplier_symm
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical
namespace GlobalTheory.ArchInvForm

theorem trace_half {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    (z : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (⅟(2 : mixedEmbedding.mixedSpace F) * z) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z / 2 := by
  have h : (2 : ℝ) • (⅟(2 : mixedEmbedding.mixedSpace F) * z) = z := by
    rw [Algebra.smul_def, map_ofNat, ← mul_assoc, mul_invOf_self, one_mul]
  have h2 := congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h
  rw [map_smul, smul_eq_mul] at h2
  linarith

theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w φ = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ) w φ := by
  funext x
  simp only [schr, GlobalTheory.ArchUniq.schrF, hψ]
  congr 3
  rw [map_add, trace_half]
  rfl

theorem int_phase_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @Measure V (borel V)) (hμ : @Measure.IsAddHaarMeasure V _ _ (borel V) μ)
    (u v p : V → ℂ) (hp : ∀ x, ‖p x‖ = 1) (a : V) :
    @integral V ℂ _ _ (borel V) μ (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) =
      @integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (v x)) := by
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  have e : (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) = fun x => u (x + a) * starRingEnd ℂ (v (x + a)) := by
    funext x
    have h1 : p x * starRingEnd ℂ (p x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp x]; simp
    rw [map_mul]
    linear_combination (u (x + a) * starRingEnd ℂ (v (x + a))) * h1
  rw [e]
  exact integral_add_right_eq_self (μ := μ) (fun x => u x * starRingEnd ℂ (v x)) a

theorem const_of_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro _ F _ _ _ κ _ ψ hψ T A hT
  have hP := GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) κ
  have hnorm : ∀ t, ‖ψ t‖ = 1 := by
    intro t
    rw [hψ, show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) t : ℝ) : ℂ) =
      ((-(2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hK : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ w (f f₁ g g₁ : SInf F κ), (f₁ : _ → ℂ) = schr ψ w f → (g₁ : _ → ℂ) = schr ψ w g →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f₁ x * starRingEnd ℂ (T g₁ x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ w f f₁ g g₁ hf hg
    have e1 := hT w f f₁ hf
    have e2 := hT w g g₁ hg
    have e : (fun x => T f₁ x * starRingEnd ℂ (T g₁ x)) = fun x =>
        (ψ (x ⬝ᵥ (A w).2 + ⅟(2 : mixedEmbedding.mixedSpace F) * ((A w).1 ⬝ᵥ (A w).2)) * T f (x + (A w).1)) *
          starRingEnd ℂ (ψ (x ⬝ᵥ (A w).2 + ⅟(2 : mixedEmbedding.mixedSpace F) * ((A w).1 ⬝ᵥ (A w).2)) *
            T g (x + (A w).1)) := by
      funext x
      rw [show T f₁ x = schr ψ (A w) (T f) x from congrFun e1 x, show T g₁ x = schr ψ (A w) (T g) x from congrFun e2 x]
      rfl
    rw [e]
    exact int_phase_shift μ hμ _ _ _ (fun x => hnorm _) _
  have hmod : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f f' g g' : SInf F κ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ L f f' g g' hf hg
    obtain ⟨b, hb⟩ := GlobalTheory.ArchUniqStd.exists_right hP ((-(1 / (2 * Real.pi))) • L)
    have hw : ∀ (u u' : SInf F κ), (∀ x, u' x = Complex.exp (Complex.I * (L x : ℂ)) * u x) →
        (u' : _ → ℂ) = schr ψ (0, b) u := by
      intro u u' hu
      rw [schr_eq_schrF ψ hψ]
      funext x
      rw [hu x]
      simp only [GlobalTheory.ArchUniq.schrF]
      rw [add_zero, hP.zero_left, zero_div, add_zero, hb, ContinuousLinearMap.smul_apply, smul_eq_mul]
      congr 2
      push_cast
      field_simp
    exact hK μ hμ (0, b) f f' g g' (hw f f' hf) (hw g g' hg)
  have htr : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ (a : κ → mixedEmbedding.mixedSpace F) (f f' g g' : SInf F κ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ a f f' g g' hf hg
    have hw : ∀ (u u' : SInf F κ), (∀ x, u' x = u (x + a)) → (u' : _ → ℂ) = schr ψ (a, 0) u := by
      intro u u' hu
      rw [schr_eq_schrF ψ hψ]
      funext x
      simp [GlobalTheory.ArchUniq.schrF, hu, hP.zero_right]
    exact hK μ hμ (a, 0) f f' g g' (hw f f' hf) (hw g g' hg)
  letI mV : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  set μ₀ : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar with hμ₀
  have hμ₀H : μ₀.IsAddHaarMeasure := by rw [hμ₀]; infer_instance
  obtain ⟨c, hc⟩ := GlobalTheory.T.translation_invariant_form_const_l2 _ μ₀ hμ₀H T (htr μ₀ hμ₀H) (GlobalTheory.T.translation_character_invariant_form _ μ₀ hμ₀H T (hmod μ₀ hμ₀H))
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.ArchUniqStd.exists_one (V := κ → mixedEmbedding.mixedSpace F)
  have hself : ∀ h : SInf F κ, ∫ x, h x * starRingEnd ℂ (h x) ∂μ₀ = ((∫ x, ‖h x‖ ^ 2 ∂μ₀ : ℝ) : ℂ) :=
    fun h => GlobalTheory.WrongSignGauss.ip_self μ₀ h
  have hint : Integrable (fun x => ‖Φ x‖ ^ 2) μ₀ := by
    refine (GlobalTheory.WrongSignGauss.integrable_ip μ₀ Φ Φ).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  have hn : 0 < ∫ x, ‖Φ x‖ ^ 2 ∂μ₀ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
    have ho : IsOpen (Function.support fun x => ‖Φ x‖ ^ 2) := (Φ.continuous.norm.pow 2).isOpen_support
    exact ho.measure_pos μ₀ ⟨0, by simp [hΦ]⟩
  have hm : 0 ≤ ∫ x, ‖T Φ x‖ ^ 2 ∂μ₀ := integral_nonneg fun x => sq_nonneg _
  have hcΦ := hc Φ Φ
  change ∫ x, T Φ x * starRingEnd ℂ (T Φ x) ∂μ₀ = c * ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ₀ at hcΦ
  rw [hself, hself] at hcΦ
  have hcc : c = (((∫ x, ‖T Φ x‖ ^ 2 ∂μ₀) / (∫ x, ‖Φ x‖ ^ 2 ∂μ₀) : ℝ) : ℂ) := by
    have hn' : ((∫ x, ‖Φ x‖ ^ 2 ∂μ₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    rw [eq_div_iff hn', hcΦ]
  refine ⟨(∫ x, ‖T Φ x‖ ^ 2 ∂μ₀) / (∫ x, ‖Φ x‖ ^ 2 ∂μ₀), div_nonneg hm hn.le, fun μ hμ f f' => ?_⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hs : μ = Measure.addHaarScalarFactor μ μ₀ • μ₀ := Measure.isAddLeftInvariant_eq_smul μ μ₀
  have hcf := hc f f'
  change ∫ x, T f x * starRingEnd ℂ (T f' x) ∂μ₀ = c * ∫ x, f x * starRingEnd ℂ (f' x) ∂μ₀ at hcf
  change ∫ x, T f x * starRingEnd ℂ (T f' x) ∂μ = _ * ∫ x, f x * starRingEnd ℂ (f' x) ∂μ
  rw [hs, integral_smul_nnreal_measure, integral_smul_nnreal_measure, hcf, ← hcc]
  simp only [NNReal.smul_def, smul_eq_mul, Complex.real_smul]
  ring

end GlobalTheory.ArchInvForm
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_intertwiner_unique : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  atlas_forward_decl GlobalTheory.ArchInvForm.const_of_intertwines
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.ModelTrUnit

theorem exists_const : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE _hbij μ hμ
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  have hSB : ∀ v : Pl F, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB (Fin n × Fin d → Fv F v) := by
    intro v φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  have hfin : ∀ v : Pl F, ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => ev v φ x * starRingEnd ℂ (ev v φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
    intro v
    have h2 : (2 : Fv F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := F)
      apply (algebraMap F (Fv F v)).injective
      rw [map_ofNat, h, map_zero]
    letI : Invertible (2 : Fv F v) := invertibleOfNonzero h2
    obtain ⟨ψv, hc, hne, A, hA⟩ := GlobalTheory.T.exists_addChar_normalizing_schrodinger_action F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure v
    exact GlobalTheory.T.local_intertwiner_unique_scalar F v (Fin n × Fin d) ψv hc hne (ev v) A (hSB v) hA
  have hinf : ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F (Fin n × Fin d),
        @integral _ ℂ _ _ (borel _) μ (fun x => ei f x * starRingEnd ℂ (ei f' x)) =
          (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
    letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : mixedEmbedding.mixedSpace F) :=
      (Invertible.map (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2).copy 2 (map_ofNat _ 2).symm
    obtain ⟨ψ, hψ, A, hA⟩ := GlobalTheory.T.weil_eigen_continuous_inverse F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure
    exact GlobalTheory.T.archimedean_intertwiner_unique hP F (Fin n × Fin d) ψ hψ ei A hA
  exact GlobalTheory.T.restricted_tensor_schwartz F (Fin n × Fin d) e M.vac M₁.vac ei ev (fun v => (hPair.good.vac v).1) hPair.good.std hM₁.std
    (fun v => (hev v).1) hSB hpure hinf hfin μ hμ

end GlobalTheory.ModelTrUnit
end
