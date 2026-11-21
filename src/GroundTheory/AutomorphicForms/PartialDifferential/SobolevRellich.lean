import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.Sobolev
import GroundTheory.AutomorphicForms.HilbertSchmidtKernel
import GroundTheory.AutomorphicForms.HilbertSchmidtCompact

section
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Duality

variable {s : ℝ}

theorem star_add_lpTwo (f g : Lp ℂ 2 (volume : Measure E)) :
    (star (f + g) : Lp ℂ 2 (volume : Measure E)) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_star f, Lp.coeFn_star g,
    Lp.coeFn_add (star f) (star g), Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3]
  simp only [Pi.star_apply]
  rw [h5, Pi.add_apply, star_add]

theorem star_smul_lpTwo (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)) :
    (star (c • f) : Lp ℂ 2 (volume : Measure E)) = (starRingEnd ℂ c) • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_star f, Lp.coeFn_smul (starRingEnd ℂ c) (star f),
    Lp.coeFn_smul c f] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2]
  simp [h4]

theorem norm_star_lpTwo (f : Lp ℂ 2 (volume : Measure E)) :
    ‖(star f : Lp ℂ 2 (volume : Measure E))‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f)]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact ae_of_all _ fun x ↦ by simp

def dualPairing (v : SobolevSpace E ℂ (-s)) : StrongDual ℂ (SobolevSpace E ℂ s) :=
  (innerSL ℂ (star (SobolevSpace.bessel (-s) v) : Lp ℂ 2 (volume : Measure E))).comp
    ((SobolevSpace.besselₗᵢ (E := E) (F := ℂ) s) : SobolevSpace E ℂ s →L[ℂ] Lp ℂ 2 (volume : Measure E))

theorem dualPairing_apply' (v : SobolevSpace E ℂ (-s)) (u : SobolevSpace E ℂ s) :
    dualPairing v u = inner ℂ (star (SobolevSpace.bessel (-s) v) : Lp ℂ 2 (volume : Measure E))
      (SobolevSpace.bessel s u) := rfl

theorem norm_dualPairing (v : SobolevSpace E ℂ (-s)) : ‖dualPairing (s := s) v‖ = ‖v‖ := by
  rw [dualPairing, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, innerSL_apply_norm,
    norm_star_lpTwo]
  rfl

def dualPairingₗᵢ : SobolevSpace E ℂ (-s) →ₗᵢ[ℂ] StrongDual ℂ (SobolevSpace E ℂ s) where
  toFun := dualPairing
  map_add' v w := by
    ext u
    rw [ContinuousLinearMap.add_apply, dualPairing_apply', dualPairing_apply',
      dualPairing_apply', map_add, star_add_lpTwo, inner_add_left]
  map_smul' c v := by
    ext u
    rw [ContinuousLinearMap.smul_apply, dualPairing_apply', dualPairing_apply', map_smul,
      star_smul_lpTwo, inner_smul_left, Complex.conj_conj, RingHom.id_apply, smul_eq_mul]
  norm_map' v := norm_dualPairing v

theorem dualPairing_surjective :
    Function.Surjective (dualPairing : SobolevSpace E ℂ (-s) → StrongDual ℂ (SobolevSpace E ℂ s)) := by
  intro ℓ
  set L : StrongDual ℂ (Lp ℂ 2 (volume : Measure E)) :=
    ℓ.comp (SobolevSpace.besselₗᵢ s).symm.toLinearIsometry.toContinuousLinearMap
  set y := (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure E))).symm L
  refine ⟨(SobolevSpace.besselₗᵢ (-s)).symm (star y), ?_⟩
  ext u
  have hy : ∀ g, inner ℂ y g = L g := fun g ↦ by
    rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [dualPairing_apply', ← SobolevSpace.besselₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply,
    star_star, hy]
  simp only [L, ContinuousLinearMap.comp_apply]
  rw [← SobolevSpace.besselₗᵢ_apply]
  simp

def dualEquiv : SobolevSpace E ℂ (-s) ≃ₗᵢ[ℂ] StrongDual ℂ (SobolevSpace E ℂ s) :=
  LinearIsometryEquiv.ofSurjective dualPairingₗᵢ dualPairing_surjective

@[simp] theorem dualEquiv_apply (v : SobolevSpace E ℂ (-s)) :
    dualEquiv v = dualPairing v := rfl

theorem bessel_ofSchwartz (φ : 𝓢(E, ℂ)) :
    SobolevSpace.bessel s (SobolevSpace.ofSchwartz s φ) =
      (SchwartzMap.fourierMultiplierCLM ℂ (weight s) φ).toLp 2 := by
  apply toTemperedDistribution_injective
  simp only
  rw [SobolevSpace.toDistribution_bessel, SobolevSpace.toDistribution_ofSchwartz,
    Lp.toTemperedDistribution_toLp_eq, besselPotential_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth _)]

end Duality

end

end GroundTheory.Automorphic.Sobolev
end

section
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section MultiplierFourier

variable {m : E → ℂ} {C s t : ℝ}

theorem fourier_fourierMultiplierCLM_apply (m : E → ℂ) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    𝓕 (fourierMultiplierCLM F m u) φ = 𝓕 u (SchwartzMap.smulLeftCLM ℂ m φ) := by
  rw [fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq, smulLeftCLM_apply_apply]

theorem fourierFun_multiplier (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    fourierFun (SobolevSpace.multiplier hm hC u) =ᵐ[volume] (fun ξ ↦ m ξ • fourierFun u ξ) ∧
      ‖SobolevSpace.multiplier hm hC u‖ ^ 2 =
        ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ t * ‖m ξ • fourierFun u ξ‖ ^ 2 := by
  have hmem : MemLp (fun ξ ↦ weight t ξ • (m ξ • fourierFun u ξ)) 2 (volume : Measure E) := by
    refine (memLp_smul_of_bounded (hasTemperateGrowth_mul_weight hm (t - s)) (bounded_mul_weight hC)
      (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))).congr_norm ?_ ?_
    · exact (weight_hasTemperateGrowth t).1.continuous.aestronglyMeasurable.smul
        (hm.1.continuous.aestronglyMeasurable.smul (fourierFun_aestronglyMeasurable u))
    · refine ae_of_all _ fun ξ ↦ ?_
      have e : m ξ * weight (t - s) ξ * weight s ξ = weight t ξ * m ξ := by
        rw [mul_assoc, weight_mul_weight, sub_add_cancel, mul_comm]
      rw [← weight_smul_fourierFun]
      simp only [smul_smul]
      rw [e]
  have hrep : ∀ φ : 𝓢(E, ℂ), 𝓕 (SobolevSpace.toDistribution (SobolevSpace.multiplier hm hC u)) φ =
      ∫ ξ, φ ξ • (m ξ • fourierFun u ξ) := by
    intro φ
    rw [SobolevSpace.toDistribution_multiplier, fourier_fourierMultiplierCLM_apply,
      fourier_apply_eq_integral]
    congr 1; ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hm, smul_smul, smul_eq_mul, mul_comm]
  have h := norm_sq_eq_integral_of_fourier _ _ hmem hrep
  exact ⟨h.1.symm, h.2⟩

theorem integrable_weight_mul_norm_sq_fourierFun (u : SobolevSpace E F s) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun u ξ‖ ^ 2) (volume : Measure E) := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1
    (Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)))
  refine h.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only
  rw [← weight_smul_fourierFun, norm_smul, norm_weight, mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

theorem bound_of_le {m : E → ℂ} {M : ℝ} (hM : ∀ ξ, ‖m ξ‖ ≤ M) (ξ : E) :
    ‖m ξ‖ ≤ M * (1 + ‖ξ‖ ^ 2) ^ ((s - s) / 2) := by
  rw [sub_self, zero_div, Real.rpow_zero, mul_one]; exact hM ξ

end MultiplierFourier

section Convolution

variable (E) in

def reflect : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := E)).toContinuousLinearEquiv

variable (F) in

def convolution (ψ : 𝓢(E, ℂ)) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ))

theorem convolution_apply_apply (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    convolution F ψ u φ =
      u (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ) φ) := rfl

theorem fourier_reflect (ψ : 𝓢(E, ℂ)) (x : E) : 𝓕 (reflect E ψ) x = 𝓕 ψ (-x) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) ψ x

theorem convolution_reflect_eq (ψ φ : 𝓢(E, ℂ)) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ) φ =
      𝓕 (SchwartzMap.smulLeftCLM ℂ ⇑(𝓕 ψ : 𝓢(E, ℂ)) (𝓕⁻ φ)) := by
  apply SchwartzMap.ext; intro x
  have hψ := (𝓕 ψ : 𝓢(E, ℂ)).hasTemperateGrowth
  simp only [SchwartzMap.convolution, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, fourierInvCLM_apply, fourierCLM_apply]
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_comp_neg]
  have h : (fun y ↦ (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 (reflect E ψ)) (𝓕 φ))
      (-y)) = (⇑(SchwartzMap.smulLeftCLM ℂ ⇑(𝓕 ψ : 𝓢(E, ℂ)) (𝓕⁻ φ)) : E → ℂ) := by
    funext y
    rw [SchwartzMap.pairing_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hψ, fourier_reflect,
      neg_neg, ContinuousLinearMap.mul_apply', smul_eq_mul, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe]
    rfl
  exact congrArg (fun g : E → ℂ ↦ 𝓕 g x) h

theorem convolution_eq_fourierMultiplierCLM (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) :
    convolution F ψ u = fourierMultiplierCLM F ⇑(𝓕 ψ : 𝓢(E, ℂ)) u := by
  ext φ
  rw [convolution_apply_apply, convolution_reflect_eq, fourierMultiplierCLM_apply_apply]

end Convolution

section Mollifier

theorem norm_fourier_le_integral (ψ : 𝓢(E, ℂ)) (ξ : E) :
    ‖(𝓕 ψ : 𝓢(E, ℂ)) ξ‖ ≤ ∫ x, ‖ψ x‖ := by
  rw [SchwartzMap.fourier_coe]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem exists_norm_le_weight (χ : 𝓢(E, ℂ)) (r : ℝ) :
    ∃ C, ∀ ξ : E, ‖χ ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  set n : ℕ := ⌈-r / 2⌉₊
  refine ⟨2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ), fun ξ ↦ ?_⟩
  have h0 : ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ 0 0 χ := by
    have := SchwartzMap.le_seminorm ℂ 0 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have h1 : ‖ξ‖ ^ (2 * n) * ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ (2 * n) 0 χ := by
    have := SchwartzMap.le_seminorm ℂ (2 * n) 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have hb : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have hpow : (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
    rcases le_total (‖ξ‖ ^ 2) 1 with h | h
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
            have : 0 ≤ (‖ξ‖ ^ 2) ^ n := by positivity
            nlinarith [pow_pos (two_pos (α := ℝ)) n]
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ (2 * ‖ξ‖ ^ 2) ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ = 2 ^ n * (‖ξ‖ ^ 2) ^ n := by rw [mul_pow]
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by gcongr; linarith
  have key : (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤
      2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) := by
    calc (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) * ‖χ ξ‖ := by gcongr
      _ = 2 ^ n * (‖χ ξ‖ + ‖ξ‖ ^ (2 * n) * ‖χ ξ‖) := by rw [pow_mul]; ring
      _ ≤ _ := by gcongr
  have hpos : 0 < (1 + ‖ξ‖ ^ 2) ^ n := by positivity
  have hexp : (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hb
    have := Nat.le_ceil (-r / 2)
    linarith
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast] at hexp
  calc ‖χ ξ‖ = ((1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖) * ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by
        field_simp
    _ ≤ 2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) *
        ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by gcongr
    _ ≤ _ := by
        gcongr

namespace SobolevSpace

variable {s : ℝ}

@[simp] theorem toDistribution_sub (u v : SobolevSpace E F s) :
    toDistribution (u - v) = toDistribution u - toDistribution v := rfl

def convolutionCLM (ψ : 𝓢(E, ℂ)) : SobolevSpace E F s →L[ℂ] SobolevSpace E F s :=
  multiplier (𝓕 ψ : 𝓢(E, ℂ)).hasTemperateGrowth (bound_of_le (norm_fourier_le_integral ψ))

@[simp] theorem toDistribution_convolutionCLM (ψ : 𝓢(E, ℂ)) (u : SobolevSpace E F s) :
    toDistribution (convolutionCLM ψ u) = convolution F ψ (toDistribution u) := by
  rw [convolution_eq_fourierMultiplierCLM]; rfl

end SobolevSpace

end Mollifier

end

end GroundTheory.Automorphic.Sobolev
end

section
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Translation

open Complex in
theorem iteratedDeriv_cexp_I_mul (n : ℕ) :
    iteratedDeriv n (fun t : ℝ ↦ exp (I * t)) = fun t : ℝ ↦ I ^ n * exp (I * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h := (((hasDerivAt_id t).ofReal_comp.const_mul I).cexp).const_mul (I ^ n)
    simp only [id] at h
    rw [h.deriv]
    simp only [Complex.ofReal_one, mul_one]
    ring

open Complex in
theorem hasTemperateGrowth_cexp_I_mul : (fun t : ℝ ↦ exp (I * t)).HasTemperateGrowth := by
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n ↦ ⟨0, 1, fun t ↦ ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_I_mul, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

def expChar (a : E) (ξ : E) : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ ξ a : ℝ) : ℂ))

theorem expChar_hasTemperateGrowth (a : E) : (expChar a : E → ℂ).HasTemperateGrowth := by
  have hL : (fun ξ : E ↦ 2 * Real.pi * inner ℝ ξ a).HasTemperateGrowth := by
    have : (fun ξ : E ↦ 2 * Real.pi * inner ℝ ξ a) = ⇑((2 * Real.pi) • innerSL ℝ a) := by
      funext ξ; simp [real_inner_comm]
    rw [this]; exact ContinuousLinearMap.hasTemperateGrowth _
  exact hasTemperateGrowth_cexp_I_mul.comp hL

theorem norm_expChar (a ξ : E) : ‖expChar a ξ‖ = 1 := Complex.norm_exp_I_mul_ofReal _


variable (F) in

def translate (h : E) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compSubConstCLM ℂ (-h))





end Translation

theorem aestronglyMeasurable_weight_mul_sq {s : ℝ} (u : SobolevSpace E F s) (g : E → ℝ)
    (hg : Continuous g) :
    AEStronglyMeasurable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * g ξ * ‖fourierFun u ξ‖ ^ 2)
      (volume : Measure E) := by
  have hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ s) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  exact ((hc.mul hg).aestronglyMeasurable).mul ((fourierFun_aestronglyMeasurable u).norm.pow 2)

theorem memSobolev_add_one_of_lintegral {s : ℝ} (u : SobolevSpace E F s)
    (h : ∀ v : E, ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 *
      ‖fourierFun u ξ‖ ^ 2) < ⊤) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) := by
  rw [memSobolev_iff_fourier]
  refine ⟨fourierFun u, ?_, fourier_apply_eq_integral u⟩
  set b := stdOrthonormalBasis ℝ E
  have hmeas : AEStronglyMeasurable (fun ξ ↦ weight (s + 1) ξ • fourierFun u ξ)
      (volume : Measure E) :=
    (weight_hasTemperateGrowth (s + 1)).1.continuous.aestronglyMeasurable.smul
      (fourierFun_aestronglyMeasurable u)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine ⟨hmeas.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ by positivity)]
  have hpt : ∀ ξ, ENNReal.ofReal (‖weight (s + 1) ξ • fourierFun u ξ‖ ^ 2) =
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * 1 * ‖fourierFun u ξ‖ ^ 2) +
        ∑ i, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2) := by
    intro ξ
    have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity),
      ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ ↦ by positivity)]
    congr 1
    have hsum : ∑ i, (1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2 =
        (1 + ‖ξ‖ ^ 2) ^ s * ‖ξ‖ ^ 2 * ‖fourierFun u ξ‖ ^ 2 := by
      calc ∑ i, (1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2
          = (1 + ‖ξ‖ ^ 2) ^ s * (∑ i, inner ℝ ξ (b i) ^ 2) * ‖fourierFun u ξ‖ ^ 2 := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ = _ := by rw [b.sum_sq_inner_left ξ]
    have hw : ((1 + ‖ξ‖ ^ 2) ^ ((s + 1) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s * (1 + ‖ξ‖ ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_add_one h0.ne']
      congr 1; push_cast; ring
    rw [hsum, norm_smul, norm_weight, mul_pow, hw]
    ring
  simp_rw [hpt]
  have hm : ∀ g : E → ℝ, Continuous g → AEMeasurable (fun ξ ↦ ENNReal.ofReal
      ((1 + ‖ξ‖ ^ 2) ^ s * g ξ * ‖fourierFun u ξ‖ ^ 2)) (volume : Measure E) :=
    fun g hg ↦ (aestronglyMeasurable_weight_mul_sq u g hg).aemeasurable.ennreal_ofReal
  rw [lintegral_add_left' (hm _ continuous_const),
    lintegral_finsetSum' _ fun i _ ↦ hm (fun ξ ↦ inner ℝ ξ (b i) ^ 2) (by fun_prop)]
  refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.sum_lt_top.2 fun i _ ↦ h (b i)⟩
  have := (integrable_weight_mul_norm_sq_fourierFun u).lintegral_lt_top
  simpa using this

theorem locallyIntegrable_fourierFun {s : ℝ} (u : SobolevSpace E F s) :
    LocallyIntegrable (fourierFun u) (volume : Measure E) := by
  have hG := (Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))).locallyIntegrable
    (by norm_num)
  have := hG.continuous_smul (weight_hasTemperateGrowth (-s)).1.continuous
  exact this

open LineDeriv in

theorem memSobolev_add_one_iff_lineDeriv {s : ℝ} (u : SobolevSpace E F s) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) ↔
      ∀ v : E, MemSobolev s 2 (∂_{v} (SobolevSpace.toDistribution u)) := by
  constructor
  · intro hu v
    have := SobolevSpace.memSobolev_toDistribution
      (SobolevSpace.lineDerivCLM v (SobolevSpace.mk (s := s + 1) _ hu))
    rwa [SobolevSpace.toDistribution_lineDerivCLM, SobolevSpace.toDistribution_mk,
      add_sub_cancel_right] at this
  · intro hv
    apply memSobolev_add_one_of_lintegral
    intro v
    set w : SobolevSpace E F s := SobolevSpace.mk _ (hv v)
    set d := SobolevSpace.lineDerivCLM (s := s) v u
    have hd := (fourierFun_multiplier (m := fun ξ ↦ (2 * Real.pi * Complex.I) *
      ((inner ℝ ξ v : ℝ) : ℂ)) (by fun_prop) (SobolevSpace.lineDeriv_bound v) u).1
    have hwd : fourierFun w =ᵐ[volume] fourierFun d := by
      apply ae_eq_of_integral_schwartz_smul_eq (locallyIntegrable_fourierFun w)
        (locallyIntegrable_fourierFun d)
      intro φ _
      rw [← fourier_apply_eq_integral, ← fourier_apply_eq_integral]
      simp [w, d]
    have hint := (integrable_weight_mul_norm_sq_fourierFun w).lintegral_lt_top
    have hc : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
    have hpt : ∀ᵐ ξ ∂(volume : Measure E),
        ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 * ‖fourierFun u ξ‖ ^ 2) =
          ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) *
            ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun w ξ‖ ^ 2) := by
      filter_upwards [hwd, hd] with ξ h1 h2
      rw [← ENNReal.ofReal_mul (by positivity), h1]
      congr 1
      change _ = _ * ((1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun (SobolevSpace.multiplier _ _ u) ξ‖ ^ 2)
      have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
        rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [h2, norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, h2pi,
        Real.norm_eq_abs, mul_one, mul_pow, mul_pow, mul_pow, sq_abs]
      field_simp
    rw [lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

def dqSymbol (v : E) (t : ℝ) (ξ : E) : ℂ := ((t⁻¹ : ℝ) : ℂ) * (expChar (t • v) ξ - 1)

theorem dqSymbol_hasTemperateGrowth (v : E) (t : ℝ) : (dqSymbol v t : E → ℂ).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const _).mul
    ((expChar_hasTemperateGrowth _).sub (Function.HasTemperateGrowth.const 1))

theorem norm_expChar_sub_one_le (a ξ : E) :
    ‖expChar a ξ - 1‖ ≤ 2 * Real.pi * |inner ℝ ξ a| := by
  rw [expChar]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem norm_dqSymbol_le (v : E) (t : ℝ) (ξ : E) : ‖dqSymbol v t ξ‖ ≤ 2 * Real.pi * |inner ℝ ξ v| := by
  rw [dqSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne t 0 with rfl | ht
  · simp; positivity
  calc |t⁻¹| * ‖expChar (t • v) ξ - 1‖ ≤ |t⁻¹| * (2 * Real.pi * |inner ℝ ξ (t • v)|) := by
        gcongr; exact norm_expChar_sub_one_le _ _
    _ = 2 * Real.pi * |inner ℝ ξ v| := by
        rw [inner_smul_right, abs_mul, abs_inv]
        field_simp

theorem norm_dqSymbol_le' (v : E) (t : ℝ) (ξ : E) : ‖dqSymbol v t ξ‖ ≤ 2 * |t|⁻¹ := by
  rw [dqSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, mul_comm]
  gcongr
  calc ‖expChar (t • v) ξ - 1‖ ≤ ‖expChar (t • v) ξ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_expChar, norm_one]; norm_num

theorem dqSymbol_bound {s : ℝ} (v : E) (t : ℝ) (ξ : E) :
    ‖dqSymbol v t ξ‖ ≤ (2 * Real.pi * ‖v‖) * (1 + ‖ξ‖ ^ 2) ^ ((s + 1 - s) / 2) := by
  refine (norm_dqSymbol_le v t ξ).trans ?_
  rw [show (s + 1 - s) / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow]
  have h : |inner ℝ ξ v| ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2) :=
    calc |inner ℝ ξ v| ≤ ‖ξ‖ * ‖v‖ := abs_real_inner_le_norm ξ v
      _ = ‖v‖ * ‖ξ‖ := mul_comm _ _
      _ ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2) := by
          gcongr
          exact Real.le_sqrt_of_sq_le (by linarith)
  calc 2 * Real.pi * |inner ℝ ξ v| ≤ 2 * Real.pi * (‖v‖ * √(1 + ‖ξ‖ ^ 2)) := by gcongr
    _ = _ := by ring

open Filter Topology in
theorem tendsto_dqSymbol (v ξ : E) :
    Tendsto (fun t ↦ dqSymbol v t ξ) (𝓝[≠] 0)
      (𝓝 ((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ))) := by
  set a : ℝ := 2 * Real.pi * inner ℝ ξ v
  have hf : HasDerivAt (fun t : ℝ ↦ Complex.exp (Complex.I * ((t * a : ℝ) : ℂ)))
      (Complex.I * a) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp.const_mul Complex.I).cexp
    simpa using this
  have h := hasDerivAt_iff_tendsto_slope_zero.1 hf
  have e : ∀ t : ℝ, t⁻¹ • (Complex.exp (Complex.I * (((0 + t) * a : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (((0 : ℝ) * a : ℝ) : ℂ))) = dqSymbol v t ξ := by
    intro t
    rw [dqSymbol, expChar, inner_smul_right, Complex.real_smul, zero_add, zero_mul,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    simp only [a]
    congr 3
    push_cast
    ring
  simp_rw [e] at h
  convert h using 2
  simp only [a]; push_cast; ring

namespace SobolevSpace

variable {s : ℝ}

def diffQuot (v : E) (t : ℝ) : SobolevSpace E F s →L[ℂ] SobolevSpace E F s :=
  multiplier (dqSymbol_hasTemperateGrowth v t) (bound_of_le (norm_dqSymbol_le' v t))


theorem norm_diffQuot_le (v : E) (t : ℝ) (u : SobolevSpace E F (s + 1)) :
    ‖diffQuot v t (inclusion (le_add_of_nonneg_right zero_le_one) u)‖ ≤ 2 * Real.pi * ‖v‖ * ‖u‖ := by
  have h : diffQuot v t (inclusion (le_add_of_nonneg_right zero_le_one) u) =
      multiplier (dqSymbol_hasTemperateGrowth v t) (dqSymbol_bound (s := s) v t) u := by
    apply toDistribution_injective
    simp [diffQuot]
  rw [h]
  exact norm_multiplier_apply_le _ _ u

end SobolevSpace

open Filter Topology in

theorem memSobolev_add_one_of_diffQuot {s : ℝ} (u : SobolevSpace E F s)
    (h : ∀ v : E, ∃ C, ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖SobolevSpace.diffQuot v t u‖ ≤ C) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) := by
  apply memSobolev_add_one_of_lintegral
  intro v
  obtain ⟨C, hC⟩ := h v
  set f : ℝ → E → ℝ≥0∞ := fun t ξ ↦
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖dqSymbol v t ξ • fourierFun u ξ‖ ^ 2)
  have hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ s) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  have hfm : ∀ t, AEMeasurable (f t) (volume : Measure E) := fun t ↦
    (hc.aestronglyMeasurable.mul (((dqSymbol_hasTemperateGrowth v t).1.continuous.aestronglyMeasurable.smul
      (fourierFun_aestronglyMeasurable u)).norm.pow 2)).aemeasurable.ennreal_ofReal
  have hnorm : ∀ t, ∫⁻ ξ, f t ξ = ENNReal.ofReal (‖SobolevSpace.diffQuot v t u‖ ^ 2) := by
    intro t
    have hm := fourierFun_multiplier (dqSymbol_hasTemperateGrowth v t)
      (bound_of_le (s := s) (norm_dqSymbol_le' v t)) u
    change _ = ENNReal.ofReal (‖SobolevSpace.multiplier _ _ u‖ ^ 2)
    rw [hm.2, ofReal_integral_eq_lintegral_ofReal]
    · have hi := integrable_weight_mul_norm_sq_fourierFun
        (SobolevSpace.multiplier (dqSymbol_hasTemperateGrowth v t)
          (bound_of_le (s := s) (norm_dqSymbol_le' v t)) u)
      refine hi.congr ?_
      filter_upwards [hm.1] with ξ hξ
      rw [hξ]
    · exact ae_of_all _ fun ξ ↦ by positivity
  have hlim : ∀ ξ, Tendsto (fun t ↦ f t ξ) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
      ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2))) := by
    intro ξ
    apply ENNReal.tendsto_ofReal
    apply Tendsto.const_mul
    apply Tendsto.pow
    apply Tendsto.norm
    exact (tendsto_dqSymbol v ξ).smul_const _
  have hfatou := lintegral_liminf_le' (μ := (volume : Measure E)) (u := 𝓝[≠] (0 : ℝ)) hfm
  have hleft : ∫⁻ ξ, liminf (fun t ↦ f t ξ) (𝓝[≠] 0) = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
      ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2) := by
    congr 1; ext ξ; exact (hlim ξ).liminf_eq
  have hright : liminf (fun t ↦ ∫⁻ ξ, f t ξ) (𝓝[≠] 0) ≤ ENNReal.ofReal (C ^ 2) := by
    simp_rw [hnorm]
    apply liminf_le_of_frequently_le'
    apply Eventually.frequently
    filter_upwards [hC] with t ht
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hbound := (hleft ▸ hfatou).trans hright
  have hc2 : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hpt : ∀ ξ : E,
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 * ‖fourierFun u ξ‖ ^ 2) =
        ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
          ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, h2pi,
      Real.norm_eq_abs, mul_one, mul_pow, mul_pow, mul_pow, sq_abs]
    field_simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hbound.trans_lt ENNReal.ofReal_lt_top)

theorem inclusion_mk_eq {s : ℝ} (u : SobolevSpace E F s)
    (hu : MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u)) :
    SobolevSpace.inclusion (le_add_of_nonneg_right zero_le_one) (SobolevSpace.mk (s := s + 1) _ hu) = u := by
  apply SobolevSpace.toDistribution_injective
  rw [SobolevSpace.toDistribution_inclusion, SobolevSpace.toDistribution_mk]

open Filter Topology in

theorem memSobolev_add_one_iff_diffQuot {s : ℝ} (u : SobolevSpace E F s) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) ↔
      ∀ v : E, ∃ C, ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖SobolevSpace.diffQuot v t u‖ ≤ C := by
  refine ⟨fun hu v ↦ ⟨2 * Real.pi * ‖v‖ * ‖SobolevSpace.mk (s := s + 1) _ hu‖,
    Eventually.of_forall fun t ↦ ?_⟩, memSobolev_add_one_of_diffQuot u⟩
  have h := SobolevSpace.norm_diffQuot_le v t (SobolevSpace.mk (s := s + 1) _ hu)
  rwa [inclusion_mk_eq u hu] at h

end

end GroundTheory.Automorphic.Sobolev
end

section
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem one_add_norm_sq_le (ξ η : E) :
    1 + ‖ξ‖ ^ 2 ≤ 2 * (1 + ‖ξ - η‖ ^ 2) * (1 + ‖η‖ ^ 2) := by
  have h : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    simpa using norm_add_le (ξ - η) η
  have h2 : ‖ξ‖ ^ 2 ≤ 2 * ‖ξ - η‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
    nlinarith [norm_nonneg ξ, norm_nonneg (ξ - η), norm_nonneg η, sq_nonneg (‖ξ - η‖ - ‖η‖)]
  nlinarith [sq_nonneg ‖ξ - η‖, sq_nonneg ‖η‖, mul_nonneg (sq_nonneg ‖ξ - η‖) (sq_nonneg ‖η‖)]

theorem peetre (r : ℝ) (ξ η : E) :
    (1 + ‖ξ‖ ^ 2) ^ r ≤ 2 ^ |r| * (1 + ‖ξ - η‖ ^ 2) ^ |r| * (1 + ‖η‖ ^ 2) ^ r := by
  have pξ : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have pη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have pζ : (0 : ℝ) < 1 + ‖ξ - η‖ ^ 2 := by positivity
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, ← Real.mul_rpow (by norm_num) pζ.le, ← Real.mul_rpow (by positivity) pη.le]
    exact Real.rpow_le_rpow pξ.le (one_add_norm_sq_le ξ η) hr
  · rw [abs_of_nonpos hr]
    have key : (1 + ‖η‖ ^ 2) ^ (-r) ≤ 2 ^ (-r) * (1 + ‖ξ - η‖ ^ 2) ^ (-r) * (1 + ‖ξ‖ ^ 2) ^ (-r) := by
      rw [← Real.mul_rpow (by norm_num) pζ.le, ← Real.mul_rpow (by positivity) pξ.le]
      apply Real.rpow_le_rpow pη.le _ (by linarith)
      have := one_add_norm_sq_le η ξ
      rwa [norm_sub_rev] at this
    rw [Real.rpow_neg pη.le, Real.rpow_neg pξ.le] at key
    have a := Real.rpow_pos_of_pos pξ r
    have b := Real.rpow_pos_of_pos pη r
    have c : 0 < 2 ^ (-r) * (1 + ‖ξ - η‖ ^ 2) ^ (-r) := by positivity
    rw [le_mul_inv_iff₀ a, inv_mul_le_iff₀ b] at key
    calc (1 + ‖ξ‖ ^ 2) ^ r = (1 + ‖ξ‖ ^ 2) ^ r * 1 := (mul_one _).symm
      _ ≤ _ := by nlinarith

theorem fourierFun_inclusion {s t : ℝ} (h : t ≤ s) (v : SobolevSpace E F s) :
    fourierFun (SobolevSpace.inclusion h v) =ᵐ[volume] fourierFun v := by
  have := (fourierFun_multiplier (m := fun _ ↦ (1 : ℂ)) (Function.HasTemperateGrowth.const 1)
    (SobolevSpace.one_bound h) v).1
  filter_upwards [this] with ξ hξ
  rw [one_smul] at hξ
  exact hξ

theorem norm_inclusion_sq {s t : ℝ} (h : t ≤ s) (v : SobolevSpace E F s) :
    ‖SobolevSpace.inclusion h v‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ t * ‖fourierFun v ξ‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [fourierFun_inclusion h v] with ξ hξ
  rw [hξ]

theorem memLp_rpow_of_integrable {A : E → ℝ} (hA : Integrable A (volume : Measure E))
    (h0 : ∀ ξ, 0 ≤ A ξ) {a : ℝ} (ha : 0 < a) :
    MemLp (fun ξ ↦ A ξ ^ a) (ENNReal.ofReal (1 / a)) (volume : Measure E) := by
  have hm : AEStronglyMeasurable (fun ξ ↦ A ξ ^ a) (volume : Measure E) :=
    (hA.1.aemeasurable.pow_const a).aestronglyMeasurable
  have hq0 : ENNReal.ofReal (1 / a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [← memLp_norm_rpow_iff hm hq0 ENNReal.ofReal_ne_top,
    ENNReal.div_self hq0 ENNReal.ofReal_ne_top, memLp_one_iff_integrable]
  refine hA.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only
  rw [ENNReal.toReal_ofReal (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (h0 ξ) a), ← Real.rpow_mul (h0 ξ), mul_one_div_cancel ha.ne',
    Real.rpow_one]

theorem norm_inclusion_le_interpolation {r t s : ℝ} (hrt : r < t) (hts : t < s)
    (v : SobolevSpace E F s) :
    ‖SobolevSpace.inclusion hts.le v‖ ≤
      ‖v‖ ^ ((t - r) / (s - r)) * ‖SobolevSpace.inclusion (hrt.trans hts).le v‖ ^ ((s - t) / (s - r)) := by
  have hsr : 0 < s - r := by linarith
  set a := (t - r) / (s - r) with ha_def
  set θ := (s - t) / (s - r) with hθ_def
  have ha : 0 < a := div_pos (by linarith) hsr
  have hθ : 0 < θ := div_pos (by linarith) hsr
  have haθ : a + θ = 1 := by rw [ha_def, hθ_def, ← add_div]; field_simp; ring
  have hexp : s * a + r * θ = t := by rw [ha_def, hθ_def]; field_simp; ring
  set A : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun v ξ‖ ^ 2
  set B : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ r * ‖fourierFun v ξ‖ ^ 2
  have hA : Integrable A (volume : Measure E) := integrable_weight_mul_norm_sq_fourierFun v
  have hB : Integrable B (volume : Measure E) := by
    have := integrable_weight_mul_norm_sq_fourierFun
      (SobolevSpace.inclusion (hrt.trans hts).le v)
    refine this.congr ?_
    filter_upwards [fourierFun_inclusion (hrt.trans hts).le v] with ξ hξ
    simp only [B, hξ]
  have hA0 : ∀ ξ, 0 ≤ A ξ := fun ξ ↦ by positivity
  have hB0 : ∀ ξ, 0 ≤ B ξ := fun ξ ↦ by positivity
  have hpq : (1 / a).HolderConjugate (1 / θ) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, by simp [haθ]⟩
    rw [lt_div_iff₀ ha, one_mul]; linarith
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ fun ξ ↦ Real.rpow_nonneg (hA0 ξ) a) (ae_of_all _ fun ξ ↦ Real.rpow_nonneg (hB0 ξ) θ)
    (memLp_rpow_of_integrable hA hA0 ha) (memLp_rpow_of_integrable hB hB0 hθ)
  have e1 : ∀ ξ, A ξ ^ a * B ξ ^ θ = (1 + ‖ξ‖ ^ 2) ^ t * ‖fourierFun v ξ‖ ^ 2 := by
    intro ξ
    have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    simp only [A, B]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul h0.le, ← Real.rpow_mul h0.le]
    calc (1 + ‖ξ‖ ^ 2) ^ (s * a) * (‖fourierFun v ξ‖ ^ 2) ^ a *
          ((1 + ‖ξ‖ ^ 2) ^ (r * θ) * (‖fourierFun v ξ‖ ^ 2) ^ θ)
        = ((1 + ‖ξ‖ ^ 2) ^ (s * a) * (1 + ‖ξ‖ ^ 2) ^ (r * θ)) *
          ((‖fourierFun v ξ‖ ^ 2) ^ a * (‖fourierFun v ξ‖ ^ 2) ^ θ) := by ring
      _ = _ := by
        rw [← Real.rpow_add h0, hexp, ← Real.rpow_add_of_nonneg (by positivity) ha.le hθ.le, haθ,
          Real.rpow_one]
  have e2 : ∀ ξ, (A ξ ^ a) ^ (1 / a) = A ξ := fun ξ ↦ by
    rw [← Real.rpow_mul (hA0 ξ), mul_one_div_cancel ha.ne', Real.rpow_one]
  have e3 : ∀ ξ, (B ξ ^ θ) ^ (1 / θ) = B ξ := fun ξ ↦ by
    rw [← Real.rpow_mul (hB0 ξ), mul_one_div_cancel hθ.ne', Real.rpow_one]
  simp only [e1, e2, e3, one_div_one_div] at hH
  rw [← norm_inclusion_sq hts.le, ← norm_sq_eq_integral,
    ← norm_inclusion_sq (hrt.trans hts).le] at hH
  have hsq : ∀ (x : ℝ) (c : ℝ), 0 ≤ x → (x ^ 2) ^ c = (x ^ c) ^ 2 := fun x c hx ↦ by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]
  rw [hsq _ _ (norm_nonneg _), hsq _ _ (norm_nonneg _), ← mul_pow] at hH
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hH

end

end GroundTheory.Automorphic.Sobolev
end

section
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def cutoff (R : ℝ) : 𝓢(E, ℂ) :=
  let b : ContDiffBump (0 : E) := ⟨R.toNNReal + 1, R.toNNReal + 2, by positivity, by linarith⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : E → ℝ)) := b.hasCompactSupport.comp_left rfl
  have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ (b : E → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  h₁.toSchwartzMap h₂

theorem cutoff_eq_one {R : ℝ} {x : E} (hx : x ∈ Metric.ball (0 : E) (R + 1)) : cutoff R x = 1 := by
  simp only [cutoff]
  change ((ContDiffBump.toFun _ x : ℝ) : ℂ) = 1
  rw [Complex.ofReal_eq_one]
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall]
  rw [Metric.mem_ball] at hx
  simp only
  have : R ≤ R.toNNReal := Real.le_coe_toNNReal R
  linarith

theorem smulLeftCLM_cutoff_eq_self {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
    {R : ℝ} (u : 𝓢'(E, F')) (hu : Distribution.IsVanishingOn u (Metric.closedBall (0 : E) R)ᶜ) :
    smulLeftCLM F' (cutoff R : E → ℂ) u = u := by
  ext φ
  rw [smulLeftCLM_apply_apply]
  have h0 : u (SchwartzMap.smulLeftCLM ℂ (cutoff R : E → ℂ) φ - φ) = 0 := by
    apply hu
    have hsub : Function.support ⇑(SchwartzMap.smulLeftCLM ℂ (cutoff R : E → ℂ) φ - φ) ⊆
        (Metric.ball (0 : E) (R + 1))ᶜ := by
      intro x hx
      by_contra hb
      apply hx
      simp only [Set.mem_compl_iff, not_not] at hb
      rw [sub_apply, SchwartzMap.smulLeftCLM_apply_apply
        (cutoff R).hasTemperateGrowth, cutoff_eq_one hb, one_smul, sub_self]
    refine (closure_minimal hsub Metric.isOpen_ball.isClosed_compl).trans ?_
    intro x hx
    simp only [Set.mem_compl_iff, Metric.mem_ball, Metric.mem_closedBall, not_lt, not_le] at hx ⊢
    linarith
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem fourier_char_smul (χ : 𝓢(E, ℂ)) (η ξ : E) :
    𝓕 (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) ξ = (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by
  rw [Real.fourier_eq, SchwartzMap.fourier_coe, Real.fourier_eq]
  congr 1; ext x
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, inner_sub_right]
  congr 3; ring

theorem fourierInv_smulLeft_fourier_apply (χ φ : 𝓢(E, ℂ)) (η : E) :
    (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ)) : 𝓢(E, ℂ)) η =
      ∫ ξ, φ ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by
  have hg : Integrable (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) (volume : Measure E) := by
    refine (χ.integrable (μ := (volume : Measure E))).bdd_mul (c := 1) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact ae_of_all _ fun x ↦ (Circle.norm_coe _).le
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  have h := integral_fourier_smul_eq_of_integrable (F := ℂ) φ hg
  simp only [smul_eq_mul] at h
  simp_rw [fourier_char_smul] at h
  rw [← h]
  congr 1; ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, Circle.smul_def, smul_eq_mul,
    smul_eq_mul, SchwartzMap.fourier_coe]
  ring

section Kernel

variable (s N : ℝ) (χ : 𝓢(E, ℂ))

def rellichKernel (p : E × E) : ℂ :=
  weight (s - N) p.1 * (𝓕 χ : 𝓢(E, ℂ)) (p.1 - p.2) * weight (-s) p.2

variable {s N}

theorem continuous_rellichKernel : Continuous (rellichKernel (E := E) s N χ) := by
  unfold rellichKernel
  have h1 := (weight_hasTemperateGrowth (E := E) (s - N)).1.continuous
  have h2 := (weight_hasTemperateGrowth (E := E) (-s)).1.continuous
  fun_prop

theorem norm_rellichKernel_sq_le (ξ η : E) :
    ‖rellichKernel s N χ (ξ, η)‖ ^ 2 ≤
      2 ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (-N) *
        ((1 + ‖ξ - η‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2) := by
  have pξ : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have pη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have hp := peetre (-s) η ξ
  rw [abs_neg, norm_sub_rev η ξ] at hp
  simp only [rellichKernel, norm_mul, norm_weight, mul_pow]
  have e1 : ((1 + ‖ξ‖ ^ 2) ^ ((s - N) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (s - N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul pξ.le]; congr 1; push_cast; ring
  have e2 : ((1 + ‖η‖ ^ 2) ^ (-s / 2)) ^ 2 = (1 + ‖η‖ ^ 2) ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul pη.le]; congr 1; push_cast; ring
  rw [e1, e2]
  have e3 : (1 + ‖ξ‖ ^ 2) ^ (s - N) * (1 + ‖ξ‖ ^ 2) ^ (-s) = (1 + ‖ξ‖ ^ 2) ^ (-N) := by
    rw [← Real.rpow_add pξ]; congr 1; ring
  calc (1 + ‖ξ‖ ^ 2) ^ (s - N) * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2 * (1 + ‖η‖ ^ 2) ^ (-s)
      ≤ (1 + ‖ξ‖ ^ 2) ^ (s - N) * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2 *
          (2 ^ |s| * (1 + ‖ξ - η‖ ^ 2) ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (-s)) := by gcongr
    _ = 2 ^ |s| * ((1 + ‖ξ‖ ^ 2) ^ (s - N) * (1 + ‖ξ‖ ^ 2) ^ (-s)) *
          ((1 + ‖ξ - η‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2) := by ring
    _ = _ := by rw [e3]

theorem integrable_weight_mul_norm_fourier_sq (s : ℝ) :
    Integrable (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2) (volume : Measure E) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  obtain ⟨C, hC⟩ := exists_norm_le_weight (𝓕 χ : 𝓢(E, ℂ)) (-(n + 1) / 2 - |s|)
  have hint := (integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := n + 1) (by linarith)).const_mul (C ^ 2)
  refine hint.mono' ?_ (ae_of_all _ fun ζ ↦ ?_)
  · have hc : Continuous (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ |s|) :=
      (continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ζ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ζ‖ ^ 2).ne'
    exact (hc.mul ((𝓕 χ : 𝓢(E, ℂ)).continuous.norm.pow 2)).aestronglyMeasurable
  · have pζ : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hC ζ
    have h2 : ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2 ≤ (C * (1 + ‖ζ‖ ^ 2) ^ ((-(n + 1) / 2 - |s|) / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2
        ≤ (1 + ‖ζ‖ ^ 2) ^ |s| * (C * (1 + ‖ζ‖ ^ 2) ^ ((-(n + 1) / 2 - |s|) / 2)) ^ 2 := by
          gcongr
      _ = C ^ 2 * (1 + ‖ζ‖ ^ 2) ^ (-(n + 1) / 2) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + ‖ζ‖ ^ 2) ^ _), ← Real.rpow_mul pζ.le]
          rw [mul_left_comm, ← Real.rpow_add pζ]
          congr 2; push_cast; ring

theorem memLp_rellichKernel (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    MemLp (rellichKernel s N χ) 2 ((volume : Measure E).prod volume) := by
  have hmeas := (continuous_rellichKernel (s := s) (N := N) χ).aestronglyMeasurable
    (μ := (volume : Measure E).prod volume)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hH := integrable_weight_mul_norm_fourier_sq χ s
  have hW := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := 2 * N) hN
  have hW' : Integrable (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-N)) (volume : Measure E) := by
    refine hW.congr (ae_of_all _ fun ξ ↦ ?_)
    simp only; congr 1; ring
  set H : E → ℝ := fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2
  have hdom : Integrable (fun p : E × E ↦ 2 ^ |s| * (1 + ‖p.1‖ ^ 2) ^ (-N) * H (p.1 - p.2))
      ((volume : Measure E).prod volume) := by
    have hg := (hW'.const_mul (2 ^ |s|)).mul_prod (hH.comp_neg (μ := (volume : Measure E)))
    have hc := ((measurePreserving_prod_sub (volume : Measure E) (volume : Measure E)).integrable_comp
      hg.aestronglyMeasurable).2 hg
    refine hc.congr (ae_of_all _ fun p ↦ ?_)
    simp only [Function.comp_apply, neg_sub]
  refine hdom.mono' (hmeas.norm.pow 2) (ae_of_all _ fun p ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_rellichKernel_sq_le χ p.1 p.2

end Kernel

section Identity

variable {s N : ℝ} (χ : 𝓢(E, ℂ))

def rellichOp (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  L2Kernel.kernelOp ((memLp_rellichKernel (s := s) χ hN).toLp _)

theorem isCompactOperator_rellichOp (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    IsCompactOperator (rellichOp (s := s) χ hN) :=
  (L2Kernel.kernelOp_isHilbertSchmidt _).isCompactOperator

theorem rellichOp_apply_ae (hN : (Module.finrank ℝ E : ℝ) < 2 * N)
    (G : Lp ℂ 2 (volume : Measure E)) :
    rellichOp (s := s) χ hN G =ᵐ[volume] fun ξ ↦ ∫ η, rellichKernel s N χ (ξ, η) * G η :=
  L2Kernel.kernelOp_toLp_apply_ae (memLp_rellichKernel χ hN) G

theorem memLp_two_prod_mul (φ : 𝓢(E, ℂ)) (G : Lp ℂ 2 (volume : Measure E)) :
    MemLp (fun p : E × E ↦ φ p.1 * G p.2) 2 ((volume : Measure E).prod volume) := by
  have hφ := (φ.memLp 2 (volume : Measure E))
  have hG := Lp.memLp G
  have hm : AEStronglyMeasurable (fun p : E × E ↦ φ p.1 * G p.2)
      ((volume : Measure E).prod volume) :=
    (φ.continuous.aestronglyMeasurable.comp_fst).mul (hG.1.comp_snd)
  rw [memLp_two_iff_integrable_sq_norm hm]
  have h1 := (memLp_two_iff_integrable_sq_norm hφ.1).1 hφ
  have h2 := (memLp_two_iff_integrable_sq_norm hG.1).1 hG
  refine (h1.mul_prod h2).congr (ae_of_all _ fun p ↦ ?_)
  simp [mul_pow]

theorem fourier_bessel_inclusion_eq (hN : (Module.finrank ℝ E : ℝ) < 2 * N)
    (u : SobolevSpace E ℂ s)
    (hu : smulLeftCLM ℂ (χ : E → ℂ) (SobolevSpace.toDistribution u) = SobolevSpace.toDistribution u) :
    (𝓕 (SobolevSpace.bessel (s - N) (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) :
      Lp ℂ 2 (volume : Measure E)) = rellichOp (s := s) χ hN (𝓕 (SobolevSpace.bessel s u)) := by
  set G : Lp ℂ 2 (volume : Measure E) := 𝓕 (SobolevSpace.bessel s u)
  apply Lp.ext
  apply ae_eq_of_integral_schwartz_smul_eq (F := ℂ)
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  intro φ _
  set φ' : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ (weight (s - N)) φ
  set ψ : 𝓢(E, ℂ) := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ'))

  have hL : ∫ ξ, φ ξ • (𝓕 (SobolevSpace.bessel (s - N)
      (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) : Lp ℂ 2 (volume : Measure E)) ξ =
      ∫ η, (∫ ξ, φ' ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η)) * (weight (-s) η * G η) := by
    have e1 : ∫ ξ, φ ξ • (𝓕 (SobolevSpace.bessel (s - N)
        (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) : Lp ℂ 2 (volume : Measure E)) ξ =
        ∫ ξ, φ' ξ • fourierFun u ξ := by
      apply integral_congr_ae
      filter_upwards [fourierFun_inclusion (by linarith : s - N ≤ s) u] with ξ hξ
      rw [← weight_smul_fourierFun, hξ, SchwartzMap.smulLeftCLM_apply_apply
        (weight_hasTemperateGrowth _)]
      simp only [smul_eq_mul]; ring
    have e2 : SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ') = 𝓕 ψ := by
      simp only [ψ, FourierTransform.fourier_fourierInv_eq]
    rw [e1, ← fourier_apply_eq_integral, ← hu, TemperedDistribution.fourier_apply,
      smulLeftCLM_apply_apply, e2, ← TemperedDistribution.fourier_apply, fourier_apply_eq_integral]
    congr 1; ext η
    rw [fourierInv_smulLeft_fourier_apply, fourierFun, smul_eq_mul, smul_eq_mul]

  have hint : Integrable (fun p : E × E ↦ φ p.1 * rellichKernel s N χ p * G p.2)
      ((volume : Measure E).prod volume) := by
    have := (memLp_rellichKernel (s := s) χ hN).integrable_mul (memLp_two_prod_mul φ G)
    refine this.congr (ae_of_all _ fun p ↦ ?_)
    simp only [Pi.mul_apply]; ring
  have hR : ∫ ξ, φ ξ • (rellichOp (s := s) χ hN G : Lp ℂ 2 (volume : Measure E)) ξ =
      ∫ η, (∫ ξ, φ' ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η)) * (weight (-s) η * G η) := by
    have e1 : ∫ ξ, φ ξ • (rellichOp (s := s) χ hN G : Lp ℂ 2 (volume : Measure E)) ξ =
        ∫ ξ, ∫ η, φ ξ * rellichKernel s N χ (ξ, η) * G η := by
      apply integral_congr_ae
      filter_upwards [rellichOp_apply_ae (s := s) χ hN G] with ξ hξ
      rw [hξ, smul_eq_mul, ← integral_const_mul]
      congr 1; ext η; ring
    rw [e1, integral_integral_swap hint]
    congr 1; ext η
    rw [← integral_mul_const]
    congr 1; ext ξ
    simp only [rellichKernel, φ', SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth _),
      smul_eq_mul]
    ring
  rw [hL, hR]

end Identity

theorem norm_inclusion_sub_eq {s r : ℝ} (h : r ≤ s) (v w : SobolevSpace E ℂ s) :
    ‖SobolevSpace.inclusion h v - SobolevSpace.inclusion h w‖ =
      ‖(𝓕 (SobolevSpace.bessel r (SobolevSpace.inclusion h v)) : Lp ℂ 2 (volume : Measure E)) -
        𝓕 (SobolevSpace.bessel r (SobolevSpace.inclusion h w))‖ := by
  rw [SobolevSpace.norm_def, map_sub, ← Lp.norm_fourier_eq]
  congr 1
  exact (Lp.fourierTransformₗᵢ E ℂ).map_sub _ _

open Filter Topology in

theorem rellich {s t : ℝ} (hts : t < s) {K : Set E} (hK : IsCompact K)
    (u : ℕ → SobolevSpace E ℂ s) {M : ℝ} (hM : ∀ j, ‖u j‖ ≤ M)
    (hsupp : ∀ j, Distribution.IsVanishingOn (SobolevSpace.toDistribution (u j)) Kᶜ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : SobolevSpace E ℂ t,
      Tendsto (fun j ↦ SobolevSpace.inclusion hts.le (u (φ j))) atTop (𝓝 v) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  set χ := cutoff (E := E) R
  have hu : ∀ j, smulLeftCLM ℂ (χ : E → ℂ) (SobolevSpace.toDistribution (u j)) =
      SobolevSpace.toDistribution (u j) := fun j ↦
    smulLeftCLM_cutoff_eq_self _ ((hsupp j).mono (Set.compl_subset_compl.2 hR))
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  set N : ℝ := max n (s - t) + 1
  have hN : n < 2 * N := by
    have : n ≤ max n (s - t) := le_max_left _ _
    have hn : 0 ≤ n := Nat.cast_nonneg _
    linarith
  have hN0 : 0 ≤ N := by
    have : s - t ≤ max n (s - t) := le_max_right _ _
    linarith
  have hrt : s - N < t := by
    have : s - t ≤ max n (s - t) := le_max_right _ _
    linarith
  have hrs : s - N ≤ s := by linarith
  set T := rellichOp (s := s) χ hN
  set G : ℕ → Lp ℂ 2 (volume : Measure E) := fun j ↦ 𝓕 (SobolevSpace.bessel s (u j))
  set M' := max M 0
  have hG : ∀ j, G j ∈ Metric.closedBall (0 : Lp ℂ 2 (volume : Measure E)) M' := fun j ↦ by
    rw [Metric.mem_closedBall, dist_zero_right, Lp.norm_fourier_eq, ← SobolevSpace.norm_def]
    exact (hM j).trans (le_max_left _ _)
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompactOperator_rellichOp (s := s) χ hN).isCompact_closure_image_closedBall
    M' |>.tendsto_subseq (x := fun j ↦ T (G j)) fun j ↦ subset_closure ⟨G j, hG j, rfl⟩
  refine ⟨φ, hφ, ?_⟩

  have hC : CauchySeq (fun j ↦ T (G (φ j))) := hlim.cauchySeq
  have hdist : ∀ i j, dist (SobolevSpace.inclusion hrs (u (φ i)))
      (SobolevSpace.inclusion hrs (u (φ j))) = dist (T (G (φ i))) (T (G (φ j))) := by
    intro i j
    rw [dist_eq_norm, dist_eq_norm, norm_inclusion_sub_eq,
      fourier_bessel_inclusion_eq χ hN _ (hu _), fourier_bessel_inclusion_eq χ hN _ (hu _)]

  set θ := (s - t) / (s - (s - N))
  set α := (t - (s - N)) / (s - (s - N))
  have hθ : 0 < θ := div_pos (by linarith) (by linarith)
  have hα : 0 ≤ α := (div_pos (by linarith) (by linarith)).le
  have hinterp : ∀ i j, dist (SobolevSpace.inclusion hts.le (u (φ i)))
      (SobolevSpace.inclusion hts.le (u (φ j))) ≤
        (2 * M') ^ α * dist (T (G (φ i))) (T (G (φ j))) ^ θ := by
    intro i j
    have h := norm_inclusion_le_interpolation hrt hts (u (φ i) - u (φ j))
    rw [map_sub, map_sub] at h
    rw [dist_eq_norm, ← hdist, dist_eq_norm]
    refine h.trans ?_
    gcongr
    calc ‖u (φ i) - u (φ j)‖ ≤ ‖u (φ i)‖ + ‖u (φ j)‖ := norm_sub_le _ _
      _ ≤ M' + M' := add_le_add ((hM _).trans (le_max_left _ _)) ((hM _).trans (le_max_left _ _))
      _ = 2 * M' := by ring
  have hcauchy : CauchySeq (fun j ↦ SobolevSpace.inclusion hts.le (u (φ j))) := by
    rw [Metric.cauchySeq_iff] at hC ⊢
    intro ε hε
    set c := (2 * M') ^ α + 1
    have hc : 0 < c := by positivity
    obtain ⟨K₀, hK₀⟩ := hC ((ε / c) ^ (1 / θ)) (by positivity)
    refine ⟨K₀, fun i hi j hj ↦ ?_⟩
    have h1 := hK₀ i hi j hj
    have h2 : dist (T (G (φ i))) (T (G (φ j))) ^ θ < ε / c := by
      calc dist (T (G (φ i))) (T (G (φ j))) ^ θ < ((ε / c) ^ (1 / θ)) ^ θ :=
            Real.rpow_lt_rpow dist_nonneg h1 hθ
        _ = ε / c := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ.ne', Real.rpow_one]
    calc dist _ _ ≤ (2 * M') ^ α * dist (T (G (φ i))) (T (G (φ j))) ^ θ := hinterp i j
      _ ≤ c * dist (T (G (φ i))) (T (G (φ j))) ^ θ := by
          gcongr; linarith
      _ < c * (ε / c) := by gcongr
      _ = ε := by field_simp
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨v, hv⟩

end

end GroundTheory.Automorphic.Sobolev
end
