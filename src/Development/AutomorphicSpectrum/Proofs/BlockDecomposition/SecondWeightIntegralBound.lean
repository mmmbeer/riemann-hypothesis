import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.TrDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.HasFDerivAtPm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateTermsVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
import BuildAid.ForwardExisting

section
noncomputable section

open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.PerUAssembled

def rtEquiv (g : GL (Fin 3) ℝ) : M23 ≃L[ℝ] M23 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ))
      map_add' := fun X Y => by
        have : Matrix.of (X + Y) = Matrix.of X + Matrix.of Y := rfl
        rw [this, Matrix.add_mul]
        rfl
      map_smul' := fun c X => by
        have : Matrix.of (c • X) = c • Matrix.of X := rfl
        rw [this, Matrix.smul_mul]
        rfl
      invFun := fun X => Matrix.of.symm (Matrix.of X * ((g⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ))
      left_inv := fun X => by
        simp [Matrix.mul_assoc]
      right_inv := fun X => by
        simp [Matrix.mul_assoc] }

theorem rtEquiv_apply (g : GL (Fin 3) ℝ) (X : M23) :
    rtEquiv g X = Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ)) := rfl

def rtS (g : GL (Fin 3) ℝ) (Φ : Sw) : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rtEquiv g) Φ

theorem rtS_coe (g : GL (Fin 3) ℝ) (Φ : Sw) : (rtS g Φ : M23 → ℂ) = B.rt g Φ := by
  funext X
  simp [rtS, B.rt, rtEquiv_apply]

theorem schwartz_bounds (f : Sw) (n : ℕ) :
    ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m f X‖ ≤ C :=
  ⟨2 ^ n * (Finset.Iic (n, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f, fun m hm X =>
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (n, n)) le_rfl hm f X⟩

theorem ae_det_ne_zero : ∀ᵐ h : M22, (Matrix.of h).det ≠ 0 := by
  rw [ae_iff]
  have h : volume {h : M22 | (Matrix.of h).det = 0} = 0 := GlobalTheory.CompanionTheory.GodementNull.dNull
  simpa using h

end GlobalTheory.CompanionTheory.PerUAssembled
end
end

section
section
noncomputable section

open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

namespace GlobalTheory.CompanionTheory.DInt2.DerivW

def cf (i j : Fin 2) : M22 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i)

theorem cf_apply (i j : Fin 2) (X : M22) : cf i j X = X i j := rfl

def colL (j : Fin 2) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cf 0 j) + Complex.I • Complex.ofRealCLM.comp (cf 1 j)

theorem colL_zero (X : M22) : colL 0 X = al X := by
  simp [colL, al, cf_apply, mul_comm]

theorem colL_one (X : M22) : colL 1 X = be X := by
  simp [colL, be, cf_apply, mul_comm]

theorem hasFDerivAt_al (h : M22) : HasFDerivAt al (colL 0) h := by
  have : al = colL 0 := funext fun X => (colL_zero X).symm
  rw [this]
  exact (colL 0).hasFDerivAt

theorem hasFDerivAt_be (h : M22) : HasFDerivAt be (colL 1) h := by
  have : be = colL 1 := funext fun X => (colL_one X).symm
  rw [this]
  exact (colL 1).hasFDerivAt

def dc (h : M22) : ℂ := (((Matrix.of h).det : ℝ) : ℂ)

def dL (h : M22) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    (h 0 0 • cf 1 1 + h 1 1 • cf 0 0 - (h 0 1 • cf 1 0 + h 1 0 • cf 0 1))

theorem dL_apply (h X : M22) : dL h X = (dd h X : ℂ) := by
  simp only [dL, dd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, cf_apply, smul_eq_mul,
    Complex.ofRealCLM_apply]
  congr 1
  ring

theorem hasFDerivAt_dc (h : M22) : HasFDerivAt dc (dL h) h := by
  have e : dc = fun y : M22 => Complex.ofRealCLM
      (cf 0 0 y * cf 1 1 y - cf 0 1 y * cf 1 0 y) := by
    funext y
    simp [dc, Matrix.det_fin_two, cf_apply]
  rw [e]
  have h1 := ((cf 0 0).hasFDerivAt (x := h)).mul ((cf 1 1).hasFDerivAt (x := h))
  have h2 := ((cf 0 1).hasFDerivAt (x := h)).mul ((cf 1 0).hasFDerivAt (x := h))
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp h (h1.sub h2)
  exact h3

theorem hasFDerivAt_zpow_log {f : M22 → ℂ} {f' : M22 →L[ℝ] ℂ} {x : M22}
    (hf : HasFDerivAt f f' x) (n : ℤ) (h0 : f x ≠ 0) :
    HasFDerivAt (fun y => f y ^ n) ((f x ^ n * ((n : ℂ) / f x)) • f') x := by
  have h1 := (hasDerivAt_zpow n (f x) (Or.inl h0)).comp_hasFDerivAt x hf
  have e : (n : ℂ) * f x ^ (n - 1) = f x ^ n * ((n : ℂ) / f x) := by
    rw [zpow_sub_one₀ h0]
    field_simp
  rw [e] at h1
  exact h1

def cl (k : ℕ) (h : M22) : ℂ :=
  dc h ^ (((k - 1 : ℕ)) : ℤ) * al h ^ (-(2 * (k : ℤ) - 1)) *
    Complex.exp (2 * Real.pi * Complex.I * (be h * al h ^ (-1 : ℤ)))

theorem weight_eq_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    w0 k h = cl k h := by
  rw [GlobalTheory.CompanionTheory.WeightClosed.main k hk h hΔ]
  simp only [cl, dc, al, be, zpow_natCast, zpow_neg_one, div_eq_mul_inv]

theorem weight_eventually_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    w0 k =ᶠ[nhds h] cl k := by
  have hc : Continuous fun y : M22 => (Matrix.of y : Matrix (Fin 2) (Fin 2) ℝ).det :=
    (show Continuous (fun y : M22 => (Matrix.of y : Matrix (Fin 2) (Fin 2) ℝ)) from
      continuous_id).matrix_det
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hΔ] with y hy
  exact weight_eq_closed_form k hk y hy

theorem main_deriv (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    DifferentiableAt ℝ (w0 k) h ∧ ∀ X : M22, fderiv ℝ (w0 k) h X = w0 k h * ell k h X := by
  have hA0 : al h ≠ 0 := GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ
  have hD0 : dc h ≠ 0 := by
    simp only [dc]
    exact_mod_cast hΔ.ne'
  have p1 := hasFDerivAt_zpow_log (hasFDerivAt_dc h) (((k - 1 : ℕ)) : ℤ) hD0
  have p2 := hasFDerivAt_zpow_log (hasFDerivAt_al h) (-(2 * (k : ℤ) - 1)) hA0
  have p3 := hasFDerivAt_zpow_log (hasFDerivAt_al h) (-1 : ℤ) hA0
  have q := ((hasFDerivAt_be h).mul p3).const_mul (2 * Real.pi * Complex.I : ℂ)
  have e := q.cexp
  have t := (p1.mul p2).mul e
  have hw := HasFDerivAt.congr_of_eventuallyEq t (weight_eventually_closed_form k hk h hΔ)
  refine ⟨hw.differentiableAt, fun X => ?_⟩
  rw [hw.fderiv, weight_eq_closed_form k hk h hΔ]
  have c1 : ((((k - 1 : ℕ)) : ℤ) : ℂ) = (k : ℂ) - 1 := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  have c2 : ((-(2 * (k : ℤ) - 1) : ℤ) : ℂ) = 1 - 2 * (k : ℂ) := by
    push_cast
    ring
  have c3 : (((Matrix.of h).det : ℝ) : ℂ) = dc h := rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    dL_apply, colL_zero, colL_one, Pi.mul_apply, cl, ell, c1, c2, c3, zpow_neg_one,
    Int.cast_neg, Int.cast_one]
  clear hw t e q p1 p2 p3
  generalize Complex.exp _ = E
  generalize dc h ^ (((k - 1 : ℕ)) : ℤ) = P
  generalize al h ^ (-(2 * (k : ℤ) - 1)) = Q
  generalize al h = A at hA0 ⊢
  generalize dc h = D at hD0 ⊢
  field_simp
  ring

end GlobalTheory.CompanionTheory.DInt2.DerivW

theorem GlobalTheory.CompanionTheory.DInt2.dw0 : ∀ k : ℕ, 3 ≤ k → ∀ h : M22, 0 < (Matrix.of h).det →
    DifferentiableAt ℝ (w0 k) h ∧ ∀ X : M22, fderiv ℝ (w0 k) h X = w0 k h * ell k h X :=
  fun k hk h hΔ => GlobalTheory.CompanionTheory.DInt2.DerivW.main_deriv k hk h hΔ
end
end

open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_differentiable_logarithmic : ∀ k : ℕ, 3 ≤ k → ∀ h : M22, 0 < (Matrix.of h).det → DifferentiableAt ℝ (w0 k) h ∧ ∀ X : M22, fderiv ℝ (w0 k) h X = w0 k h * ell k h X := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DInt2.dw0
end

section
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

noncomputable section

namespace GlobalTheory.CompanionTheory.DInt2.Drho

def pr (i j : Fin 2) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

theorem pr_apply (i j : Fin 2) (h : M22) : pr i j h = (h i j : ℂ) := rfl

def eps (d : Fin 2) : ℂ := if d = 0 then 1 else Complex.I

theorem norm_eps (d : Fin 2) : ‖eps d‖ = 1 := by
  unfold eps
  split_ifs <;> simp

def alC : M22 →L[ℝ] ℂ := pr 0 0 + Complex.I • pr 1 0

theorem alC_apply (h : M22) : alC h = al h := by
  simp [alC, al, pr_apply, mul_comm]

def rC (c d : Fin 2) : M22 →L[ℝ] ℂ := eps d • pr c 0

theorem al_rpol (c d : Fin 2) (h : M22) : al (rpol c d h) = eps d * (h c 0 : ℂ) := by
  fin_cases d <;> simp [al, rpol, eps, mul_comm]

theorem rC_apply (c d : Fin 2) (h : M22) : rC c d h = al (rpol c d h) := by
  simp [rC, al_rpol, pr_apply]

theorem norm_entry_le (a : Fin 2) (h : M22) : ‖((h a 0 : ℝ) : ℂ)‖ ≤ ‖al h‖ := by
  have h1 : (al h).re = h 0 0 := by simp [al]
  have h2 : (al h).im = h 1 0 := by simp [al]
  fin_cases a
  · simpa [h1] using Complex.abs_re_le_norm (al h)
  · simpa [h2] using Complex.abs_im_le_norm (al h)

theorem norm_al_rpol_le (c d : Fin 2) (h : M22) : ‖al (rpol c d h)‖ ≤ ‖al h‖ := by
  rw [al_rpol, norm_mul, norm_eps, one_mul]
  exact norm_entry_le c h

theorem norm_al_rpol_rpol_le (a b c d : Fin 2) (h : M22) :
    ‖al (rpol c d (rpol a b h))‖ ≤ ‖al h‖ := by
  rw [al_rpol, norm_mul, norm_eps, one_mul]
  by_cases hcb : c = b
  · have : rpol a b h c 0 = h a 0 := by simp [rpol, hcb]
    rw [this]
    exact norm_entry_le a h
  · have : rpol a b h c 0 = 0 := by simp [rpol, hcb]
    rw [this]
    simp

theorem al_ne (h : M22) (hΔ : 0 < (Matrix.of h).det) : al h ≠ 0 :=
  GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ

theorem hasFDerivAt_quot {f g : M22 → ℂ} {f' g' : M22 →L[ℝ] ℂ} {h : M22}
    (hf : HasFDerivAt f f' h) (hg : HasFDerivAt g g' h) (h0 : g h ≠ 0) :
    HasFDerivAt (fun x => f x / g x) ((g h)⁻¹ • f' + (f h * (-(g h ^ 2)⁻¹)) • g') h := by
  have hi : HasFDerivAt (fun x => (g x)⁻¹) ((-(g h ^ 2)⁻¹) • g') h :=
    (hasDerivAt_inv h0).comp_hasFDerivAt h hg
  simp only [div_eq_mul_inv]
  refine (hf.fun_mul hi).congr_fderiv ?_
  ext X
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_rho (c d : Fin 2) (h : M22) (h0 : al h ≠ 0) :
    HasFDerivAt (rho c d)
      ((al h)⁻¹ • rC c d + (al (rpol c d h) * (-(al h ^ 2)⁻¹)) • alC) h := by
  have e : rho c d = fun x => rC c d x / alC x := by
    funext x
    rw [rC_apply, alC_apply, rho]
  rw [e]
  have := hasFDerivAt_quot (rC c d).hasFDerivAt alC.hasFDerivAt
    (h := h) (by rwa [alC_apply])
  simpa only [rC_apply, alC_apply] using this

def detC (h : M22) : M22 →L[ℝ] ℂ :=
  ((h 0 0 : ℂ) • pr 1 1 + (h 1 1 : ℂ) • pr 0 0) - ((h 0 1 : ℂ) • pr 1 0 + (h 1 0 : ℂ) • pr 0 1)

theorem detC_apply (h X : M22) : detC h X = (dd h X : ℂ) := by
  simp only [detC, dd, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pr_apply]
  push_cast
  ring

theorem hasFDerivAt_det (h : M22) :
    HasFDerivAt (fun x : M22 => (((Matrix.of x).det : ℝ) : ℂ)) (detC h) h := by
  have e : (fun x : M22 => (((Matrix.of x).det : ℝ) : ℂ)) =
      fun x => pr 0 0 x * pr 1 1 x - pr 0 1 x * pr 1 0 x := by
    funext x
    rw [Matrix.det_fin_two]
    simp [pr_apply]
  rw [e]
  exact ((pr 0 0).hasFDerivAt.fun_mul (pr 1 1).hasFDerivAt).fun_sub
    ((pr 0 1).hasFDerivAt.fun_mul (pr 1 0).hasFDerivAt)

theorem hasFDerivAt_tt (h : M22) (h0 : al h ≠ 0) :
    HasFDerivAt tt
      ((al h ^ 2)⁻¹ • detC h +
        ((((Matrix.of h).det : ℝ) : ℂ) * (-((al h ^ 2) ^ 2)⁻¹)) • (al h • alC + al h • alC)) h := by
  have e : tt = fun x => (((Matrix.of x).det : ℝ) : ℂ) / (alC x * alC x) := by
    funext x
    rw [alC_apply, tt, sq]
  have hsq : HasFDerivAt (fun x => alC x * alC x) (al h • alC + al h • alC) h := by
    have := alC.hasFDerivAt.fun_mul (alC.hasFDerivAt (x := h))
    simpa only [alC_apply] using this
  have hne : alC h * alC h ≠ 0 := by
    rw [alC_apply]
    exact mul_ne_zero h0 h0
  have := hasFDerivAt_quot (hasFDerivAt_det h) hsq hne
  rw [e]
  simpa only [alC_apply, ← sq] using this

theorem dd_rpol (a b : Fin 2) (h : M22) :
    dd h (rpol a b h) = if a = b then (Matrix.of h).det else 0 := by
  fin_cases a <;> fin_cases b <;> simp [dd, rpol, Matrix.det_fin_two] <;> ring

theorem norm_tt (h : M22) (hΔ : 0 < (Matrix.of h).det) : ‖tt h‖ = uu h := by
  rw [tt, uu, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ]

theorem norm_fderiv_rho (a b c d : Fin 2) (h : M22) (h0 : al h ≠ 0) :
    ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 := by
  rw [(hasFDerivAt_rho c d h h0).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    rC_apply, alC_apply]
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr h0
  have b1 : ‖(al h)⁻¹ * al (rpol c d (rpol a b h))‖ ≤ 1 := by
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hA, mul_one]
    exact norm_al_rpol_rpol_le a b c d h
  have b2 : ‖al (rpol c d h) * (-(al h ^ 2)⁻¹) * al (rpol a b h)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_neg, norm_inv, norm_pow]
    have p1 := norm_al_rpol_le c d h
    have p2 := norm_al_rpol_le a b h
    have : ‖al (rpol c d h)‖ * ‖al (rpol a b h)‖ ≤ ‖al h‖ ^ 2 := by
      rw [sq]
      exact mul_le_mul p1 p2 (norm_nonneg _) (norm_nonneg _)
    calc ‖al (rpol c d h)‖ * (‖al h‖ ^ 2)⁻¹ * ‖al (rpol a b h)‖
        = (‖al (rpol c d h)‖ * ‖al (rpol a b h)‖) / ‖al h‖ ^ 2 := by
          rw [div_eq_mul_inv]; ring
      _ ≤ 1 := div_le_one_of_le₀ this (by positivity)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add b1 b2
    _ = 2 := by norm_num

theorem norm_fderiv_tt (a b : Fin 2) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  have h0 := al_ne h hΔ
  rw [(hasFDerivAt_tt h h0).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    alC_apply, detC_apply, dd_rpol]
  set δ : ℂ := if a = b then 1 else 0 with hδ
  have hdd : (((if a = b then (Matrix.of h).det else 0 : ℝ)) : ℂ) =
      δ * (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [hδ]
    split_ifs <;> simp
  rw [hdd]
  have key : (al h ^ 2)⁻¹ * (δ * (((Matrix.of h).det : ℝ) : ℂ)) +
      (((Matrix.of h).det : ℝ) : ℂ) * (-((al h ^ 2) ^ 2)⁻¹) *
        (al h * al (rpol a b h) + al h * al (rpol a b h)) =
      tt h * (δ - 2 * (al (rpol a b h) / al h)) := by
    rw [tt]
    field_simp
    ring
  rw [key, norm_mul, norm_tt h hΔ, mul_comm]
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr h0
  have huu : 0 ≤ uu h := by
    rw [← norm_tt h hΔ]
    exact norm_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ huu
  have n1 : ‖δ‖ ≤ 1 := by
    rw [hδ]
    split_ifs <;> simp
  have n2 : ‖2 * (al (rpol a b h) / al h)‖ ≤ 2 := by
    rw [norm_mul, norm_div]
    have : ‖al (rpol a b h)‖ / ‖al h‖ ≤ 1 := div_le_one_of_le₀ (norm_al_rpol_le a b h) hA.le
    simpa using this
  calc _ ≤ ‖δ‖ + ‖2 * (al (rpol a b h) / al h)‖ := norm_sub_le _ _
    _ ≤ 1 + 2 := add_le_add n1 n2
    _ = 3 := by norm_num

theorem main : ∀ (a b c d : Fin 2) (h : M22), 0 < (Matrix.of h).det →
    DifferentiableAt ℝ (rho c d) h ∧ DifferentiableAt ℝ tt h ∧
      ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 ∧ ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  intro a b c d h hΔ
  have h0 := al_ne h hΔ
  exact ⟨(hasFDerivAt_rho c d h h0).differentiableAt, (hasFDerivAt_tt h h0).differentiableAt,
    norm_fderiv_rho a b c d h h0, norm_fderiv_tt a b h hΔ⟩

end GlobalTheory.CompanionTheory.DInt2.Drho
end
end

section
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_coordinate_derivative_bounds : ∀ (a b c d : Fin 2) (h : M22), 0 < (Matrix.of h).det → DifferentiableAt ℝ (rho c d) h ∧ DifferentiableAt ℝ tt h ∧ ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 ∧ ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  first | exact @GlobalTheory.CompanionTheory.DInt2.Drho.main | exact GlobalTheory.CompanionTheory.DInt2.Drho.main | (intros; apply GlobalTheory.CompanionTheory.DInt2.Drho.main <;> assumption)
end

section
noncomputable section

open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

namespace GlobalTheory.CompanionTheory.DInt2.WMaj

theorem al_re (h : M22) : (al h).re = h 0 0 := by simp [al]
theorem al_im (h : M22) : (al h).im = h 1 0 := by simp [al]
theorem be_re (h : M22) : (be h).re = h 0 1 := by simp [be]
theorem be_im (h : M22) : (be h).im = h 1 1 := by simp [be]

theorem al_ne (h : M22) (hΔ : 0 < (Matrix.of h).det) : al h ≠ 0 :=
  GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ

theorem im_ratio (h : M22) (hΔ : 0 < (Matrix.of h).det) : (be h / al h).im = uu h := by
  have hn : Complex.normSq (al h) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using al_ne h hΔ
  rw [Complex.div_im, uu, Complex.sq_norm, Matrix.det_fin_two, al_re, al_im, be_re, be_im]
  simp only [Matrix.of_apply]
  field_simp

theorem uu_pos (h : M22) (hΔ : 0 < (Matrix.of h).det) : 0 < uu h := by
  have : 0 < ‖al h‖ := norm_pos_iff.mpr (al_ne h hΔ)
  unfold uu
  positivity

theorem norm_weight_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖w0 k h‖ = (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
      Real.exp (-(2 * Real.pi * uu h)) := by
  have e := GlobalTheory.CompanionTheory.WeightClosed.main k hk h hΔ
  change w0 k h = (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) * (al h) ^ (-(2 * (k : ℤ) - 1)) *
    Complex.exp (2 * Real.pi * Complex.I * (be h / al h)) at e
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (be h / al h)).re = -(2 * Real.pi * uu h) := by
    rw [← im_ratio h hΔ]
    simp [Complex.mul_re, Complex.mul_im]
  rw [e, norm_mul, norm_mul, norm_pow, norm_zpow, Complex.norm_exp, hre, Complex.norm_real,
    Real.norm_of_nonneg hΔ.le]

theorem norm_Wm (k : ℕ) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖Wm k (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹)‖ =
      (1 / 2 * ((Matrix.of h).det)⁻¹) ^ ((2 * (k : ℝ) - 1) / 2) *
        (‖al h‖ / (Matrix.of h).det) ^ (-(2 * (k : ℤ) - 1)) * Real.exp (-(Real.pi * uu h)) := by
  obtain ⟨i00, i01, i10, i11⟩ := GlobalTheory.CompanionTheory.WeightClosed.inv_entries h
  have hα := al_ne h hΔ
  have hD : (((Matrix.of h).det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hdet : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹).det =
      1 / 2 * ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_mul, Matrix.det_diagonal, hdi, Fin.prod_univ_two]
    simp
  have hpos : 0 < (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹).det := by
    rw [hdet]
    have := inv_pos.mpr hΔ
    positivity
  have m00 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 0 =
      1 / 2 * (((Matrix.of h).det)⁻¹ * h 1 1) := by
    rw [Matrix.diagonal_mul, i00]; simp
  have m01 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 1 =
      1 / 2 * (-(((Matrix.of h).det)⁻¹ * h 0 1)) := by
    rw [Matrix.diagonal_mul, i01]; simp
  have m10 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 0 =
      -(((Matrix.of h).det)⁻¹ * h 1 0) := by
    rw [Matrix.diagonal_mul, i10]; simp
  have m11 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 1 =
      ((Matrix.of h).det)⁻¹ * h 0 0 := by
    rw [Matrix.diagonal_mul, i11]; simp
  have e1 : (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 1 : ℝ) : ℂ) -
      (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 0 : ℝ) : ℂ) * Complex.I =
      al h / (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [m11, m10, al]
    push_cast
    field_simp
    ring
  have e2 : (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 1 : ℝ) : ℂ) -
      (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 0 : ℝ) : ℂ) * Complex.I =
      -(be h) / (2 * (((Matrix.of h).det : ℝ) : ℂ)) := by
    rw [m01, m00, be]
    push_cast
    field_simp
    ring
  have hq : -2 * (Real.pi : ℂ) * Complex.I *
      ((-(be h) / (2 * (((Matrix.of h).det : ℝ) : ℂ))) / (al h / (((Matrix.of h).det : ℝ) : ℂ))) =
      (Real.pi : ℂ) * Complex.I * (be h / al h) := by
    field_simp
  have hre : ((Real.pi : ℂ) * Complex.I * (be h / al h)).re = -(Real.pi * uu h) := by
    rw [← im_ratio h hΔ]
    simp [Complex.mul_re, Complex.mul_im]
  have hb : 0 ≤ 1 / 2 * ((Matrix.of h).det)⁻¹ := by
    have := inv_pos.mpr hΔ
    positivity
  unfold Wm
  rw [if_pos hpos, e1, e2, hq, hdet, norm_mul, norm_mul, Complex.norm_real, norm_zpow,
    Complex.norm_exp, hre, norm_div, Complex.norm_real, Real.norm_of_nonneg hΔ.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hb _)]

theorem sq_le_exp (u : ℝ) (hu : 0 ≤ u) : (1 + u) ^ 2 ≤ Real.exp (Real.pi * u) := by
  have hp := Real.pi_gt_three
  have hx : 0 ≤ Real.pi * u := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 3 * u ≤ Real.pi * u := by nlinarith
  have h3 : 9 * u ^ 2 ≤ (Real.pi * u) ^ 2 := by nlinarith [mul_nonneg hu hu]
  nlinarith [mul_nonneg hu hu]

theorem scaled (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    (2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) *
        (‖Wm k (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹)‖ *
          |(Matrix.of h).det| ^ (-(3 : ℝ) / 2)) =
      (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
        Real.exp (-(Real.pi * uu h)) * ((Matrix.of h).det)⁻¹ := by
  have hreal := GlobalTheory.CompanionTheory.WeightClosed.real_factor k (by omega) _ hΔ
  rw [norm_Wm k h hΔ, abs_of_pos hΔ]
  set D := (Matrix.of h).det with hDdef
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hinv : 0 ≤ D⁻¹ := (inv_pos.mpr hΔ).le
  have h32 : D ^ (-(3 : ℝ) / 2) = D ^ (-(1 : ℝ) / 2) * D⁻¹ := by
    rw [← Real.rpow_neg_one D, ← Real.rpow_add hΔ]
    norm_num
  have h2 : (2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) * (1 / 2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) = 1 := by
    rw [← Real.mul_rpow (by norm_num) hhalf]
    norm_num
  rw [Real.mul_rpow hhalf hinv, h32, div_zpow, zpow_neg D, div_inv_eq_mul]
  calc _ = ((2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) * (1 / 2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2)) *
        (D⁻¹ ^ ((2 * (k : ℝ) - 1) / 2) * D ^ (-(1 : ℝ) / 2) * D ^ (2 * (k : ℤ) - 1)) *
        (‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * Real.exp (-(Real.pi * uu h)) * D⁻¹) := by ring
    _ = _ := by rw [h2, hreal]; ring

end GlobalTheory.CompanionTheory.DInt2.WMaj

open GlobalTheory.CompanionTheory.DInt2.WMaj in

theorem GlobalTheory.CompanionTheory.DInt2.WMaj.main : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, ∀ (N : ℕ) (h : M22),
    0 < (Matrix.of h).det →
    (1 + uu h) ^ 2 * ‖w0 k h‖ * |(Matrix.of h).det|⁻¹ /
        ((1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N) ≤ C * Ad3.LR.B.maj k N (1 / 2) 1 h := by
  intro k hk
  refine ⟨(2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2), fun N h hΔ => ?_⟩
  have hsc := scaled k hk h hΔ
  have hu := uu_pos h hΔ
  have hden : 0 < (1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N := by positivity
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr (al_ne h hΔ)
  have hexp : (1 + uu h) ^ 2 * Real.exp (-(2 * Real.pi * uu h)) ≤ Real.exp (-(Real.pi * uu h)) := by
    have e : Real.exp (-(2 * Real.pi * uu h)) =
        Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e' : Real.exp (Real.pi * uu h) * Real.exp (-(Real.pi * uu h)) = 1 := by
      rw [← Real.exp_add]; simp
    have := sq_le_exp _ hu.le
    have hp := Real.exp_pos (-(Real.pi * uu h))
    rw [e]
    calc (1 + uu h) ^ 2 * (Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h)))
        ≤ Real.exp (Real.pi * uu h) * (Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h))) := by
          gcongr
      _ = Real.exp (-(Real.pi * uu h)) := by rw [← mul_assoc, e', one_mul]
  unfold Ad3.LR.B.maj
  rw [abs_one, one_mul, ← mul_div_assoc, hsc, norm_weight_closed_form k hk h hΔ, abs_of_pos hΔ]
  apply div_le_div_of_nonneg_right _ hden.le
  have hc : 0 ≤ (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
      ((Matrix.of h).det)⁻¹ := by
    have := inv_pos.mpr hΔ
    positivity
  calc _ = ((Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * ((Matrix.of h).det)⁻¹) *
        ((1 + uu h) ^ 2 * Real.exp (-(2 * Real.pi * uu h))) := by ring
    _ ≤ ((Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * ((Matrix.of h).det)⁻¹) *
        Real.exp (-(Real.pi * uu h)) := mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by ring
end
end

section
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_majorant_bound : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, ∀ (N : ℕ) (h : M22), 0 < (Matrix.of h).det → (1 + uu h) ^ 2 * ‖w0 k h‖ * |(Matrix.of h).det|⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N) ≤ C * Ad3.LR.B.maj k N (1 / 2) 1 h := by
  first | exact @GlobalTheory.CompanionTheory.DInt2.WMaj.main | exact GlobalTheory.CompanionTheory.DInt2.WMaj.main | (intros; apply GlobalTheory.CompanionTheory.DInt2.WMaj.main <;> assumption)
end

section
noncomputable section

open MeasureTheory Matrix Ad3.LR Ad3.LR.DTr Topology

namespace GlobalTheory.CompanionTheory.DInt2

theorem continuous_det : Continuous (fun h : M22 => (Matrix.of h).det) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  fun_prop

theorem isOpen_pos : IsOpen {h : M22 | 0 < (Matrix.of h).det} :=
  isOpen_lt continuous_const continuous_det

theorem isOpen_neg : IsOpen {h : M22 | (Matrix.of h).det < 0} :=
  isOpen_lt continuous_det continuous_const

theorem inn_eq (Φ : Sw) (g : GL (Fin 3) ℝ) (h : M22) :
    inn Φ g (Matrix.of h) = Ad3.LR.B.innB (Ad3.LR.B.rt g Φ) h 1 := by
  simp [inn, Ad3.LR.B.innB, Ad3.LR.B.rt]

theorem inn_bound (N : ℕ) (Φ : Sw) (g : GL (Fin 3) ℝ) : ∃ C : ℝ, ∀ h : M22, (Matrix.of h).det ≠ 0 →
    ‖inn Φ g (Matrix.of h)‖ ≤ C * |(Matrix.of h).det|⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N) := by
  obtain ⟨C, hC⟩ := Ad3.LR.B.ibpBound N
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.PerUAssembled.schwartz_bounds (GlobalTheory.CompanionTheory.PerUAssembled.rtS g Φ) (N + 8)
  rw [GlobalTheory.CompanionTheory.PerUAssembled.rtS_coe] at hB
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Ad3.LR.B.rt g Φ) := by
    have := (GlobalTheory.CompanionTheory.PerUAssembled.rtS g Φ).smooth ⊤
    rwa [GlobalTheory.CompanionTheory.PerUAssembled.rtS_coe] at this
  refine ⟨C * B, fun h hdet => ?_⟩
  rw [inn_eq]
  have := hC (Ad3.LR.B.rt g Φ) B hsm (fun n hn X => hB n (by omega) X) h 1 hdet
  simpa using this

theorem inn_meas (Φ : Sw) (g : GL (Fin 3) ℝ) :
    AEStronglyMeasurable (fun h : M22 => inn Φ g (Matrix.of h)) volume := by
  have hb : Continuous (fun x : Fin 2 → ℝ => blk x) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [blk] <;> fun_prop
  have ho : Continuous (fun h : M22 => Matrix.of h) := continuous_id
  have hM : Continuous (fun p : M22 × (Fin 2 → ℝ) =>
      Matrix.of p.1 * blk p.2 * (g : Matrix (Fin 3) (Fin 3) ℝ)) :=
    ((ho.comp continuous_fst).matrix_mul (hb.comp continuous_snd)).matrix_mul continuous_const
  have hs : Continuous (fun p : M22 × (Fin 2 → ℝ) =>
      (Matrix.of.symm (Matrix.of p.1 * blk p.2 * (g : Matrix (Fin 3) (Fin 3) ℝ)) : M23)) := hM
  have hp : Continuous (fun p : M22 × (Fin 2 → ℝ) => Ad3.psiR (-(p.2 1))) := by
    unfold Ad3.psiR
    fun_prop
  have hc : Continuous (fun p : M22 × (Fin 2 → ℝ) =>
      Φ (Matrix.of.symm (Matrix.of p.1 * blk p.2 * (g : Matrix (Fin 3) (Fin 3) ℝ))) * Ad3.psiR (-(p.2 1))) :=
    (Φ.continuous.comp hs).mul hp
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

theorem al_rpol (a b : Fin 2) (h : M22) :
    al (rpol a b h) = (if b = 0 then 1 else Complex.I) * (h a 0 : ℂ) := by
  fin_cases b <;> simp [al, rpol, mul_comm]

theorem be_rpol (a b : Fin 2) (h : M22) :
    be (rpol a b h) = (if b = 0 then 1 else Complex.I) * (h a 1 : ℂ) := by
  fin_cases b <;> simp [be, rpol, mul_comm]

theorem dd_rpol (a b : Fin 2) (h : M22) :
    dd h (rpol a b h) = if a = b then (Matrix.of h).det else 0 := by
  rw [Matrix.det_fin_two]
  fin_cases a <;> fin_cases b <;> simp [dd, rpol] <;> ring

theorem cross_rpol (a b : Fin 2) (h : M22) :
    be (rpol a b h) * al h - be h * al (rpol a b h) = kap a b * (((Matrix.of h).det : ℝ) : ℂ) := by
  rw [al_rpol, be_rpol, Matrix.det_fin_two]
  fin_cases a <;> fin_cases b <;> simp [al, be, kap] <;> ring_nf <;> simp <;> ring

theorem al_ne (h : M22) (hd : 0 < (Matrix.of h).det) : al h ≠ 0 :=
  GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hd

theorem ell_rpol (k : ℕ) (a b : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    ell k h (rpol a b h) = (if a = b then (k : ℂ) - 1 else 0) + (1 - 2 * (k : ℂ)) * rho a b h +
      2 * Real.pi * Complex.I * kap a b * tt h := by
  have hA := al_ne h hd
  have hD : (((Matrix.of h).det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold ell rho tt
  rw [cross_rpol, dd_rpol]
  split_ifs
  · field_simp
  · simp only [Complex.ofReal_zero]
    field_simp
    ring

theorem norm_al_rpol_le (a b : Fin 2) (h : M22) : ‖al (rpol a b h)‖ ≤ ‖al h‖ := by
  rw [al_rpol, norm_mul]
  have h1 : ‖(if b = 0 then (1 : ℂ) else Complex.I)‖ = 1 := by split_ifs <;> simp
  rw [h1, one_mul, Complex.norm_real, Real.norm_eq_abs]
  fin_cases a
  · simpa [al] using Complex.abs_re_le_norm (al h)
  · simpa [al] using Complex.abs_im_le_norm (al h)

theorem norm_rho_le (c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) : ‖rho c d h‖ ≤ 1 := by
  have hA := al_ne h hd
  unfold rho
  rw [norm_div]
  exact div_le_one_of_le₀ (norm_al_rpol_le c d h) (norm_nonneg _)

theorem norm_tt (h : M22) (hd : 0 < (Matrix.of h).det) : ‖tt h‖ = uu h := by
  unfold tt uu
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]

theorem uu_pos (h : M22) (hd : 0 < (Matrix.of h).det) : 0 < uu h := by
  have hA := al_ne h hd
  unfold uu
  have : 0 < ‖al h‖ := norm_pos_iff.2 hA
  positivity

theorem norm_kap (a b : Fin 2) : ‖kap a b‖ = 1 := by
  unfold kap
  fin_cases a <;> fin_cases b <;> simp

theorem weight_zero_not_pos_det (k : ℕ) (h : M22) (hd : ¬ 0 < (Matrix.of h).det) : w0 k h = 0 := by
  have : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simpa using hd
  unfold w0 Wm
  rw [if_neg this]
  simp

theorem weight_eventually_zero_neg_det (k : ℕ) (h : M22) (hd : (Matrix.of h).det < 0) : w0 k =ᶠ[𝓝 h] 0 := by
  filter_upwards [isOpen_neg.mem_nhds hd] with x hx
  exact weight_zero_not_pos_det k x (not_lt.2 (le_of_lt hx))

theorem measurable_al : Measurable al := by
  unfold al
  fun_prop

theorem measurable_be : Measurable be := by
  unfold be
  fun_prop

theorem measurable_w0_of_three_le (k : ℕ) (hk : 3 ≤ k) : Measurable (w0 k) := by
  have hdet : Measurable (fun h : M22 => (Matrix.of h).det) := continuous_det.measurable
  have hF : Measurable (fun h : M22 => (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
      (al h) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * (be h / al h))) := by
    have h1 := Complex.measurable_ofReal.comp hdet
    have h2 := measurable_al
    have h3 := measurable_be
    exact ((h1.pow_const _).mul (h2.pow_const _)).mul
      (Complex.measurable_exp.comp (measurable_const.mul (h3.div h2)))
  have hs : MeasurableSet {h : M22 | 0 < (Matrix.of h).det} := isOpen_pos.measurableSet
  have : w0 k = fun h : M22 => if 0 < (Matrix.of h).det then ((((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
      (al h) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * (be h / al h))) else 0 := by
    funext h
    split_ifs with hd
    · exact GlobalTheory.CompanionTheory.WeightClosed.main k hk h hd
    · exact weight_zero_not_pos_det k h hd
  rw [this]
  exact Measurable.ite hs hF measurable_const

theorem measurable_Lt (v : ℂ) (a b : Fin 2) {w : M22 → ℂ} (hw : Measurable w) :
    Measurable (Lt v a b w) := by
  have hr : ∀ h : M22, rpol a b h = h a 0 • (rpol 0 b (fun i j => if i = 0 ∧ j = 0 then 1 else 0)) +
      h a 1 • (rpol 0 b (fun i j => if i = 0 ∧ j = 1 then 1 else 0)) := by
    intro h
    funext r c
    fin_cases c <;> by_cases hb : r = b <;> simp [rpol, hb]
  have hd : Measurable (fun h : M22 => fderiv ℝ w h (rpol a b h)) := by
    have : (fun h : M22 => fderiv ℝ w h (rpol a b h)) = fun h =>
        h a 0 • fderiv ℝ w h (rpol 0 b (fun i j => if i = 0 ∧ j = 0 then 1 else 0)) +
        h a 1 • fderiv ℝ w h (rpol 0 b (fun i j => if i = 0 ∧ j = 1 then 1 else 0)) := by
      funext h
      rw [hr h, map_add, map_smul, map_smul]
    rw [this]
    have m0 := measurable_fderiv_apply_const ℝ w (rpol 0 b (fun i j => if i = 0 ∧ j = 0 then (1 : ℝ) else 0))
    have m1 := measurable_fderiv_apply_const ℝ w (rpol 0 b (fun i j => if i = 0 ∧ j = 1 then (1 : ℝ) else 0))
    have c0 : Measurable (fun h : M22 => h a 0) := by fun_prop
    have c1 : Measurable (fun h : M22 => h a 1) := by fun_prop
    exact (c0.smul m0).add (c1.smul m1)
  unfold Lt Lop
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    fun_prop
  · simp only [hab, if_false]
    fun_prop

theorem Qf_deriv (k : ℕ) (v : ℂ) (a b c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    DifferentiableAt ℝ (Qf k v c d) h ∧ fderiv ℝ (Qf k v c d) h (rpol a b h) =
      (2 * (k : ℂ) - 1) * fderiv ℝ (rho c d) h (rpol a b h) -
        2 * Real.pi * Complex.I * kap c d * fderiv ℝ tt h (rpol a b h) := by
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.polarization_coordinate_derivative_bounds a b c d h hd
  have hq := ((h1.hasFDerivAt.const_mul (2 * (k : ℂ) - 1)).const_add
    (if c = d then v - 2 - ((k : ℂ) - 1) else 0)).sub
    (h2.hasFDerivAt.const_mul (2 * Real.pi * Complex.I * kap c d))
  have e : (fun y => (if c = d then v - 2 - ((k : ℂ) - 1) else 0) + (2 * (k : ℂ) - 1) * rho c d y -
      2 * Real.pi * Complex.I * kap c d * tt y) = Qf k v c d := rfl
  have hq' : HasFDerivAt (Qf k v c d) ((2 * (k : ℂ) - 1) • fderiv ℝ (rho c d) h -
      (2 * Real.pi * Complex.I * kap c d) • fderiv ℝ tt h) h := hq
  refine ⟨hq'.differentiableAt, ?_⟩
  rw [hq'.fderiv]
  simp

theorem first_derivative_weight_formula (k : ℕ) (hk : 3 ≤ k) (v : ℂ) (c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    Lt v c d (w0 k) h = w0 k h * Qf k v c d h := by
  unfold Lt Lop
  rw [(GlobalTheory.T.weight_differentiable_logarithmic k hk h hd).2, ell_rpol k c d h hd]
  unfold Qf
  split_ifs
  · ring
  · ring

theorem second_derivative_weight_formula (k : ℕ) (hk : 3 ≤ k) (v v' : ℂ) (a b c d : Fin 2) (h : M22)
    (hd : 0 < (Matrix.of h).det) :
    Lt v a b (Lt v' c d (w0 k)) h = w0 k h * ((if a = b then (v - 2) * Qf k v' c d h else 0) -
      fderiv ℝ (Qf k v' c d) h (rpol a b h) - Qf k v' c d h * ell k h (rpol a b h)) := by
  obtain ⟨hw, hw'⟩ := GlobalTheory.T.weight_differentiable_logarithmic k hk h hd
  obtain ⟨hq, -⟩ := Qf_deriv k v' a b c d h hd
  have he : Lt v' c d (w0 k) =ᶠ[𝓝 h] fun x => w0 k x * Qf k v' c d x := by
    filter_upwards [isOpen_pos.mem_nhds hd] with x hx
    exact first_derivative_weight_formula k hk v' c d x hx
  have hf : fderiv ℝ (fun x => w0 k x * Qf k v' c d x) h = w0 k h • fderiv ℝ (Qf k v' c d) h + Qf k v' c d h • fderiv ℝ (w0 k) h := (hw.hasFDerivAt.mul hq.hasFDerivAt).fderiv
  have e : fderiv ℝ (Lt v' c d (w0 k)) h (rpol a b h) =
      w0 k h * fderiv ℝ (Qf k v' c d) h (rpol a b h) +
        Qf k v' c d h * (w0 k h * ell k h (rpol a b h)) := by
    rw [he.fderiv_eq, hf]
    simp [hw']
  have e0 := first_derivative_weight_formula k hk v' c d h hd
  show (if a = b then v * Lt v' c d (w0 k) h else 0) + (-(fderiv ℝ (Lt v' c d (w0 k)) h (rpol a b h)) -
    2 * (if a = b then Lt v' c d (w0 k) h else 0)) = _
  rw [e, e0]
  split_ifs
  · ring
  · ring

theorem norm_ite_le (p : Prop) [Decidable p] (x : ℂ) : ‖(if p then x else 0)‖ ≤ ‖x‖ := by
  split_ifs <;> simp

theorem two_pi_le : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]

def Pc (k : ℕ) (v : ℂ) : ℝ := ‖v‖ + 3 * k + 10

theorem norm_const (c d : Fin 2) (y : ℂ) : ‖2 * Real.pi * Complex.I * kap c d * y‖ ≤ 8 * ‖y‖ := by
  have e : ‖2 * Real.pi * Complex.I * kap c d * y‖ = 2 * Real.pi * ‖y‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_kap, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  rw [e]
  exact mul_le_mul_of_nonneg_right two_pi_le (norm_nonneg _)

theorem norm_two_k (k : ℕ) (hk : 3 ≤ k) : ‖(2 * (k : ℂ) - 1)‖ ≤ 2 * k := by
  have : (2 * (k : ℂ) - 1) = ((2 * (k : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

theorem norm_weight_exponent_le (k : ℕ) (hk : 3 ≤ k) : ‖((k : ℂ) - 1)‖ ≤ k := by
  have : ((k : ℂ) - 1) = (((k : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

theorem norm_Qf_le (k : ℕ) (hk : 3 ≤ k) (v : ℂ) (c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    ‖Qf k v c d h‖ ≤ Pc k v * (1 + uu h) := by
  have hu := (uu_pos h hd).le
  have h1 : ‖(if c = d then v - 2 - ((k : ℂ) - 1) else 0)‖ ≤ ‖v‖ + 2 + k := by
    refine (norm_ite_le _ _).trans ?_
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le v 2
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith [norm_weight_exponent_le k hk]
  have h2 : ‖(2 * (k : ℂ) - 1) * rho c d h‖ ≤ 2 * k := by
    rw [norm_mul]
    calc _ ≤ (2 * (k : ℝ)) * 1 := mul_le_mul (norm_two_k k hk) (norm_rho_le c d h hd) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 := norm_const c d (tt h)
  rw [norm_tt h hd] at h3
  unfold Qf
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le (if c = d then v - 2 - ((k : ℂ) - 1) else 0) ((2 * (k : ℂ) - 1) * rho c d h)
  unfold Pc
  have hv := norm_nonneg v
  have hkk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_nonneg hv hu, mul_nonneg hkk hu]

theorem norm_ell_le (k : ℕ) (hk : 3 ≤ k) (v : ℂ) (a b : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    ‖ell k h (rpol a b h)‖ ≤ Pc k v * (1 + uu h) := by
  have hu := (uu_pos h hd).le
  rw [ell_rpol k a b h hd]
  have h1 : ‖(if a = b then (k : ℂ) - 1 else 0)‖ ≤ k := (norm_ite_le _ _).trans (norm_weight_exponent_le k hk)
  have h2 : ‖(1 - 2 * (k : ℂ)) * rho a b h‖ ≤ 2 * k := by
    rw [norm_mul, show (1 - 2 * (k : ℂ)) = -(2 * (k : ℂ) - 1) by ring, norm_neg]
    calc _ ≤ (2 * (k : ℝ)) * 1 := mul_le_mul (norm_two_k k hk) (norm_rho_le a b h hd) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 := norm_const a b (tt h)
  rw [norm_tt h hd] at h3
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (if a = b then (k : ℂ) - 1 else 0) ((1 - 2 * (k : ℂ)) * rho a b h)
  unfold Pc
  have hv := norm_nonneg v
  have hkk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_nonneg hv hu, mul_nonneg hkk hu]

theorem norm_dQf_le (k : ℕ) (hk : 3 ≤ k) (v : ℂ) (a b c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    ‖fderiv ℝ (Qf k v c d) h (rpol a b h)‖ ≤ 3 * Pc k v * (1 + uu h) := by
  have hu := (uu_pos h hd).le
  obtain ⟨-, -, h1, h2⟩ := GlobalTheory.T.polarization_coordinate_derivative_bounds a b c d h hd
  rw [(Qf_deriv k v a b c d h hd).2]
  have h3 := norm_const c d (fderiv ℝ tt h (rpol a b h))
  have h4 : ‖(2 * (k : ℂ) - 1) * fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 * k * 2 := by
    rw [norm_mul]
    exact mul_le_mul (norm_two_k k hk) h1 (norm_nonneg _) (by positivity)
  refine (norm_sub_le _ _).trans ?_
  unfold Pc
  have hv := norm_nonneg v
  have hkk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_nonneg hv hu, mul_nonneg hkk hu]

theorem bound2 (k : ℕ) (hk : 3 ≤ k) (v v' : ℂ) (a b c d : Fin 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : M22,
    0 < (Matrix.of h).det → ‖Lt v a b (Lt v' c d (w0 k)) h‖ ≤ C * ((1 + uu h) ^ 2 * ‖w0 k h‖) := by
  have hP : 0 ≤ Pc k v' := by unfold Pc; positivity
  refine ⟨(‖v‖ + 2) * Pc k v' + 3 * Pc k v' + Pc k v' ^ 2, by positivity, fun h hd => ?_⟩
  have hu := (uu_pos h hd).le
  rw [second_derivative_weight_formula k hk v v' a b c d h hd, norm_mul, mul_comm ‖w0 k h‖, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hQ := norm_Qf_le k hk v' c d h hd
  have hE := norm_ell_le k hk v' a b h hd
  have hD := norm_dQf_le k hk v' a b c d h hd
  have h1 : ‖(if a = b then (v - 2) * Qf k v' c d h else 0)‖ ≤ (‖v‖ + 2) * (Pc k v' * (1 + uu h)) := by
    refine (norm_ite_le _ _).trans ?_
    rw [norm_mul]
    have : ‖v - 2‖ ≤ ‖v‖ + 2 := by simpa using norm_sub_le v 2
    exact mul_le_mul this hQ (norm_nonneg _) (by positivity)
  have h2 : ‖Qf k v' c d h * ell k h (rpol a b h)‖ ≤ (Pc k v' * (1 + uu h)) * (Pc k v' * (1 + uu h)) := by
    rw [norm_mul]
    exact mul_le_mul hQ hE (norm_nonneg _) (by positivity)
  refine (norm_sub_le _ _).trans ?_
  have h3 := norm_sub_le (if a = b then (v - 2) * Qf k v' c d h else 0) (fderiv ℝ (Qf k v' c d) h (rpol a b h))
  have hv := norm_nonneg v
  have hone : 1 + uu h ≤ (1 + uu h) ^ 2 := by nlinarith
  have t1 : (‖v‖ + 2) * (Pc k v' * (1 + uu h)) ≤ (‖v‖ + 2) * Pc k v' * (1 + uu h) ^ 2 := by
    rw [mul_assoc]
    gcongr
  have t2 : 3 * Pc k v' * (1 + uu h) ≤ 3 * Pc k v' * (1 + uu h) ^ 2 := by gcongr
  nlinarith

theorem vanish2 (k : ℕ) (v v' : ℂ) (a b c d : Fin 2) (h : M22) (hd : (Matrix.of h).det < 0) :
    Lt v a b (Lt v' c d (w0 k)) h = 0 := by
  have hz : ∀ x : M22, (Matrix.of x).det < 0 → Lt v' c d (w0 k) x = 0 := by
    intro x hx
    have e : fderiv ℝ (w0 k) x = fderiv ℝ 0 x := (weight_eventually_zero_neg_det k x hx).fderiv_eq
    have e0 := weight_zero_not_pos_det k x (not_lt.2 hx.le)
    unfold Lt Lop
    rw [e, e0]
    simp
  have he : Lt v' c d (w0 k) =ᶠ[𝓝 h] 0 := by
    filter_upwards [isOpen_neg.mem_nhds hd] with x hx
    exact hz x hx
  have e : fderiv ℝ (Lt v' c d (w0 k)) h = fderiv ℝ 0 h := he.fderiv_eq
  show (if a = b then v * Lt v' c d (w0 k) h else 0) + (-(fderiv ℝ (Lt v' c d (w0 k)) h (rpol a b h)) -
    2 * (if a = b then Lt v' c d (w0 k) h else 0)) = 0
  rw [e, hz h hd]
  simp

theorem maj_nonneg (k N : ℕ) (a b : ℝ) (h : M22) : 0 ≤ Ad3.LR.B.maj k N a b h := by
  unfold Ad3.LR.B.maj
  positivity

theorem main : Ad3.LR.B.MajScaled → Ad3.LR.DInt2 := by
  intro hMS k hk v v' a b c d Φ g
  obtain ⟨N, hN⟩ := hMS k hk 1 one_pos
  obtain ⟨C3, hC3⟩ := hN N le_rfl
  have hint := (hC3 (1 / 2) 1 (by norm_num) one_ne_zero).1
  obtain ⟨C1, hC1, hb⟩ := bound2 k hk v v' a b c d
  obtain ⟨C2, hm⟩ := GlobalTheory.T.weight_majorant_bound k hk
  obtain ⟨C4, hi⟩ := inn_bound N Φ g
  have hmeas : AEStronglyMeasurable (fun h : M22 => Lt v a b (Lt v' c d (w0 k)) h * inn Φ g (Matrix.of h)) volume :=
    ((measurable_Lt v a b (measurable_Lt v' c d (measurable_w0_of_three_le k hk))).aestronglyMeasurable).mul (inn_meas Φ g)
  refine Integrable.mono' (hint.const_mul (C1 * |C4| * |C2|)) hmeas ?_
  filter_upwards [GlobalTheory.CompanionTheory.PerUAssembled.ae_det_ne_zero] with h hdet
  have hmn := maj_nonneg k N (1 / 2) 1 h
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · rw [vanish2 k v v' a b c d h hneg, zero_mul, norm_zero]
    positivity
  · rw [norm_mul]
    have hden : 0 < (1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N := by positivity
    have hI := hi h hdet
    have hB := hb h hpos
    have hM := hm N h hpos
    set Den := (1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N with hDen
    set J := |(Matrix.of h).det|⁻¹ with hJ
    set P := (1 + uu h) ^ 2 * ‖w0 k h‖ with hPdef
    have hP : 0 ≤ P := by positivity
    have hJ0 : 0 ≤ J := by positivity
    calc ‖Lt v a b (Lt v' c d (w0 k)) h‖ * ‖inn Φ g (Matrix.of h)‖
        ≤ (C1 * P) * (|C4| * J / Den) := by
          refine mul_le_mul hB (hI.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
          exact le_abs_self _
      _ = C1 * |C4| * (P * J / Den) := by ring
      _ ≤ C1 * |C4| * (|C2| * Ad3.LR.B.maj k N (1 / 2) 1 h) := by
          refine mul_le_mul_of_nonneg_left (hM.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hmn
      _ = C1 * |C4| * |C2| * Ad3.LR.B.maj k N (1 / 2) 1 h := by ring

end GlobalTheory.CompanionTheory.DInt2
end
end
