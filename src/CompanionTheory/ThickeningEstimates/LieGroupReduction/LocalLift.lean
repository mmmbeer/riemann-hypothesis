import CompanionTheory.ThickeningEstimates.InnerProductFactorization.EqOfInner

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E
open scoped Real

namespace CompanionTheory.ThKR

def LocalLift : Prop :=
  ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), X ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∃ (ε : ℝ) (V : ℝ → Sch l →L[ℂ] Sch l) (W : ℝ → Sch l →L[ℂ] Sch l) (c : ℂ), 0 < ε ∧ (∀ f, V 0 f = f) ∧
      (∀ t, |t| < ε → (∀ f, V t (W t f) = f) ∧ (∀ f, W t (V t f) = f) ∧
        Impl (fun w => NormedSpace.exp (t • X) *ᵥ w) (V t).toLinearMap) ∧
      (∀ t, |t| < ε → ∀ f (lam : Sch l →L[ℂ] ℂ), DifferentiableAt ℝ (fun u => lam (V u f)) t) ∧
      ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun u => lam (V u f)) (lam (quad X f + c • f)) 0

end CompanionTheory.ThKR
end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real

namespace CompanionTheory.ThKR.LL

variable {l : Type} [Fintype l]

theorem exists_decay {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : SchwartzMap (EuclideanSpace ℝ l) F) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖g x‖ ≤ C := by
  have h := fun x => one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl g x
  simp only [norm_iteratedFDeriv_zero] at h
  exact ⟨_, le_trans (by positivity) (h 0), h⟩

theorem csmul (r : ℝ) (x : L2 l) : (r : ℂ) • x = r • x := by
  rw [coe_smul]
  rfl

theorem hasDerivAt_schwartz_to_L2 {F : ℝ → Sch l} {G : Sch l} {t₀ : ℝ} (hp : ∀ x, HasDerivAt (fun t => F t x) (G x) t₀) {C : ℝ}
    (hb : ∀ᶠ t in 𝓝 t₀, ∀ x, (1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1) * ‖F t x - F t₀ x‖ ≤ C * |t - t₀|) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l G) t₀ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C', hC', hG⟩ := exists_decay G N
  let u : ℝ → Sch l := fun t => (((t - t₀)⁻¹ : ℝ) : ℂ) • (F t - F t₀) - G
  have hu : ∀ t x, u t x = (t - t₀)⁻¹ • (F t x - F t₀ x) - G x := fun t x => by
    simp [u]
  have h1 : Tendsto (fun t => ∫ x, ‖u t x‖ ^ (2 : ℝ)) (𝓝[≠] t₀) (𝓝 (∫ _x : EuclideanSpace ℝ l, (0 : ℝ))) := by
    have hi := (integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := N)
      (by rw [hN]; push_cast; linarith)).const_mul ((C + C') ^ 2)
    refine tendsto_integral_filter_of_dominated_convergence _
      (.of_forall fun t => ((u t).continuous.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable) ?_ hi
      (.of_forall fun x => ?_)
    · filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with t ht ht0
      refine .of_forall fun x => ?_
      have ht1 : 0 < |t - t₀| := abs_pos.2 (sub_ne_zero.2 ht0)
      have hw : 1 ≤ (1 + ‖x‖) ^ N := one_le_pow₀ (by simp)
      have h2 : (1 + ‖x‖) ^ N * ‖u t x‖ ≤ C + C' := by
        rw [hu]
        refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
        rw [mul_add, norm_smul, norm_inv, Real.norm_eq_abs]
        refine add_le_add ?_ (hG x)
        rw [mul_left_comm, inv_mul_le_iff₀ ht1, mul_comm |t - t₀|]
        exact ht x
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, Real.norm_of_nonneg (by positivity),
        ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h3 : ((1 + ‖x‖) ^ N * ‖u t x‖) ^ 2 ≤ (C + C') ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      refine le_trans ?_ h3
      rw [mul_pow, mul_comm]
      gcongr
      nlinarith
    · have h2 := (hasDerivAt_iff_tendsto_slope.1 (hp x))
      have h3 := tendsto_iff_norm_sub_tendsto_zero.1 h2
      have h4 := h3.rpow_const (p := 2) (Or.inr (by norm_num))
      simpa [hu, slope_def_module] using h4
  rw [integral_zero] at h1
  have h2 := h1.rpow_const (p := 2⁻¹) (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h2
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  refine h2.congr fun t => ?_
  have : slope (fun t => schwartzToL2 l (F t)) t₀ t - schwartzToL2 l G = (u t).toLp 2 volume := by
    rw [← schwartzToL2_apply, slope_def_module]
    simp only [u, map_sub, map_smul]
    simp only [csmul]
  rw [this, norm_toLp' (by simp) (by simp)]
  simp

def LD (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l → Sch l) (t₀ : ℝ) : Prop :=
  ∀ f, HasDerivAt (fun t => schwartzToL2 l (U t f)) (schwartzToL2 l (Q f)) t₀

theorem LD.const (U : Sch l →L[ℂ] Sch l) (t₀ : ℝ) : LD (fun _ => U) (fun _ => 0) t₀ := fun f => by
  simpa using hasDerivAt_const t₀ (schwartzToL2 l (U f))

theorem LD.smul {U : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l → Sch l} {t₀ : ℝ} (h : LD U Q t₀) {c : ℝ → ℂ} {c' : ℂ}
    (hc : HasDerivAt c c' t₀) : LD (fun t => c t • U t) (fun f => c t₀ • Q f + c' • U t₀ f) t₀ := fun f => by
  simpa using hc.fun_smul (h f)

theorem LD.mul {U W : ℝ → Sch l →L[ℂ] Sch l} {P Q : Sch l → Sch l} {t₀ : ℝ} (hU : LD U P t₀) (hW : LD W Q t₀)
    (hn : ∀ᶠ t in 𝓝 t₀, ∀ f, ‖schwartzToL2 l (U t f)‖ = ‖schwartzToL2 l f‖) :
    LD (fun t => U t * W t) (fun f => P (W t₀ f) + U t₀ (Q f)) t₀ := fun f => by
  have h1 : HasDerivAt (fun t => schwartzToL2 l (U t (W t f - W t₀ f - ((t - t₀ : ℝ) : ℂ) • Q f))) 0 t₀ := by
    have h := (hW f).isLittleO
    rw [hasDerivAt_iff_isLittleO]
    refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1 ?_) h
    filter_upwards [hn] with t ht
    simp only [sub_self, ofReal_zero, zero_smul, map_zero, smul_zero, sub_zero, ht, one_mul]
    simp only [map_sub, map_smul]
    simp only [csmul, le_refl]
  have h2 : HasDerivAt (fun t : ℝ => (t - t₀) • schwartzToL2 l (U t (Q f))) (schwartzToL2 l (U t₀ (Q f))) t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).fun_smul (hU (Q f))
  have h3 := (h1.fun_add h2).fun_add (hU (W t₀ f))
  rw [zero_add, ← map_add, add_comm (U t₀ (Q f))] at h3
  refine h3.congr_of_eventuallyEq (.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply, map_sub, map_smul]
  simp only [csmul]
  abel

variable [DecidableEq l]

theorem weyl_step {V : Sch l →L[ℂ] Sch l} {w v : l ⊕ l → ℝ} (h : ∀ f, dRho w (V f) = V (dRho v f))
    (A : Sch l →L[ℂ] Sch l) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (V f)) = ∑ a, v a • schwartzToL2 l (A (V (dRho (Pi.single a 1) f))) := by
  rw [ContinuousLinearMap.mul_apply, h, dRho_eq_sum v]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
  simp only [csmul]

theorem LD.differentiableAt {V : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l → Sch l} {t₀ : ℝ} (hV : LD V Q t₀)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv : ∀ w a, DifferentiableAt ℝ (fun t => v t w a) t₀)
    (h : ∀ᶠ t in 𝓝 t₀, ∀ w f, dRho w (V t f) = V t (dRho (v t w) f)) (f : Sch l) (lam : Sch l →L[ℂ] ℂ) :
    DifferentiableAt ℝ (fun t => lam (V t f)) t₀ := by
  have key : ∀ A ∈ weylAlg l, ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀ := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀)
      (fun f => (hV f).differentiableAt) ?_ (fun f => by simp) ?_ ?_ hA
    · intro A w ih f
      refine (DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_of_eventuallyEq ?_
      filter_upwards [h] with t ht
      exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).differentiableAt.comp t₀ (differentiableAt_pi.2 fun i => key _ (hA i) f)

theorem LD.hasDerivAt {V : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l →L[ℂ] Sch l} (hV : LD V Q 0) (h0 : ∀ f, V 0 f = f)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (v' : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv0 : ∀ w, v 0 w = w)
    (hv : ∀ w a, HasDerivAt (fun t => v t w a) (-v' w a) 0) (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (v' w))
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ w f, dRho w (V t f) = V t (dRho (v t w) f)) (f : Sch l) (lam : Sch l →L[ℂ] ℂ) :
    HasDerivAt (fun t => lam (V t f)) (lam (Q f)) 0 := by
  have key : ∀ A ∈ weylAlg l, ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0 := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0)
      hV ?_ (fun f => by simpa using hasDerivAt_const _ _) ?_ ?_ hA
    · intro A w ih f
      refine ((HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_deriv ?_).congr_of_eventuallyEq ?_
      · have e : dRho w * Q = Q * dRho w - dRho (v' w) := by rw [← hQ, sub_sub_cancel]
        rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (dRho w), e, dRho_eq_sum w,
          dRho_eq_sum (v' w)]
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul, hv0, h0,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub, neg_smul, ← sub_eq_add_neg,
          Finset.sum_sub_distrib]
        simp only [csmul]
      · filter_upwards [h] with t ht
        exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pi.2 fun i => key _ (hA i) f)

end CompanionTheory.ThKR.LL
end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform

namespace CompanionTheory.ThKR.LL

variable {l : Type} [Fintype l]

abbrev Eu (l : Type) : Type := EuclideanSpace ℝ l

def rf (p q : Eu l) (f : Eu l → ℂ) : Eu l → ℂ :=
  fun x => exp (((2 * π * ⟪q, x⟫ + π * ⟪p, q⟫ : ℝ) : ℂ) * I) * f (x + p)

theorem rhoFun_eq (w : l ⊕ l → ℝ) (f : Eu l → ℂ) : rhoFun w f = rf (pPart w) (qPart w) f := rfl

def Intw (S : Sch l →L[ℂ] Sch l) (p q p' q' : Eu l) : Prop :=
  ∀ f g : Sch l, ⇑g = rf p q f → ⇑(S g) = rf p' q' (S f)

def Iso (S : Sch l →L[ℂ] Sch l) : Prop := ∀ f, ‖schwartzToL2 l (S f)‖ = ‖schwartzToL2 l f‖

theorem Intw.mul {S T : Sch l →L[ℂ] Sch l} {p q p' q' p'' q'' : Eu l} (hS : Intw S p' q' p'' q'') (hT : Intw T p q p' q') :
    Intw (S * T) p q p'' q'' := fun f g h => hS _ _ (hT f g h)

theorem Intw.smul {S : Sch l →L[ℂ] Sch l} {p q p' q' : Eu l} (hS : Intw S p q p' q') (c : ℂ) :
    Intw (c • S) p q p' q' := fun f g h => by
  funext x
  have := congrFun (hS f g h) x
  simp only [rf, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul] at this ⊢
  rw [this]
  ring

theorem Iso.mul {S T : Sch l →L[ℂ] Sch l} (hS : Iso S) (hT : Iso T) : Iso (S * T) := fun f => (hS _).trans (hT f)

theorem iso_of_integral {S : Sch l →L[ℂ] Sch l} (h : ∀ f : Sch l, ∫ x, ‖S f x‖ ^ (2 : ℝ) = ∫ x, ‖f x‖ ^ (2 : ℝ)) : Iso S :=
  fun f => by
    rw [schwartzToL2_apply, schwartzToL2_apply, norm_toLp' (by simp) (by simp), norm_toLp' (by simp) (by simp)]
    simp only [ENNReal.toReal_ofNat, h]

theorem temperate_quad (S : Eu l →L[ℝ] Eu l) : Function.HasTemperateGrowth fun x : Eu l => ⟪x, S x⟫ :=
  (innerSL ℝ).bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' S.hasTemperateGrowth

def ph (S : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  smulLeftCLM ℂ fun x : Eu l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I)

theorem ph_apply (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) :
    ph S f x = exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) * f x := by
  have h2 : Function.HasTemperateGrowth fun x : Eu l => (-2⁻¹ : ℝ) * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : Eu l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) := by
    convert GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp h2 using 1
    funext x
    simp only [Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [ph, smulLeftCLM_apply_apply h3, smul_eq_mul]

theorem ph_mul (S T : Eu l →L[ℝ] Eu l) : ph S * ph T = ph (S + T) := by
  ext f x
  simp only [ContinuousLinearMap.mul_apply, ph_apply, ← mul_assoc, ← Complex.exp_add, ContinuousLinearMap.add_apply,
    inner_add_right]
  congr 2
  push_cast
  ring

theorem ph_zero : ph (0 : Eu l →L[ℝ] Eu l) = 1 := by
  ext f x
  simp [ph_apply]

theorem isUnit_ph (S : Eu l →L[ℝ] Eu l) : IsUnit (ph S) :=
  ⟨⟨ph S, ph (-S), by rw [ph_mul, add_neg_cancel, ph_zero], by rw [ph_mul, neg_add_cancel, ph_zero]⟩, rfl⟩

theorem iso_ph (S : Eu l →L[ℝ] Eu l) : Iso (ph S) := iso_of_integral fun f => by
  simp only [ph_apply, norm_mul, norm_exp_ofReal_mul_I, one_mul]

theorem intw_ph {S : Eu l →L[ℝ] Eu l} (hS : ∀ x y, ⟪x, S y⟫ = ⟪y, S x⟫) (p q : Eu l) : Intw (ph S) p q p (q + S p) :=
  fun f g h => by
    funext x
    simp only [rf, ph_apply, h, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
    congr 2
    simp only [inner_add_left, inner_add_right, map_add, hS p x, real_inner_comm x (S p)]
    ring

open Classical in

def dil (B : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  if h : IsUnit B then compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.ofUnit h.unit) else 0

theorem dil_apply {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) (f : Sch l) (x : Eu l) : dil B f x = f (B x) := by
  rw [dil, dif_pos h]
  rfl

theorem dil_one : dil (1 : Eu l →L[ℝ] Eu l) = 1 := by
  ext f x
  simp [dil_apply isUnit_one]

theorem dil_mul {A B : Eu l →L[ℝ] Eu l} (hA : IsUnit A) (hB : IsUnit B) : dil A * dil B = dil (B * A) := by
  ext f x
  simp [dil_apply, hA, hB, hB.mul hA]

theorem isUnit_dil {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) : IsUnit (dil B) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨⟨dil u, dil (u⁻¹ : (Eu l →L[ℝ] Eu l)ˣ), by rw [dil_mul u.isUnit u⁻¹.isUnit, Units.inv_mul, dil_one],
    by rw [dil_mul u⁻¹.isUnit u.isUnit, Units.mul_inv, dil_one]⟩, rfl⟩

theorem intw_dil {B : Eu l →L[ℝ] Eu l} (hB : IsUnit B) {p q p' q' : Eu l} (hp : B p' = p) (hq : ∀ x, ⟪q', x⟫ = ⟪q, B x⟫) :
    Intw (dil B) p q p' q' := fun f g h => by
  funext x
  simp only [rf, dil_apply hB, h, map_add, hp, real_inner_comm q' p', hq, real_inner_comm q p]

theorem iso_dil {B : Eu l →L[ℝ] Eu l} (hB : IsUnit B) {c : ℝ} (hc : c ^ 2 = |B.det|) : Iso ((c : ℂ) • dil B) :=
  iso_of_integral fun f => by
    have hd : LinearMap.det (B : Eu l →ₗ[ℝ] Eu l) ≠ 0 :=
      ((hB.map ContinuousLinearMap.toLinearMapRingHom).map LinearMap.det).ne_zero
    have h1 := integral_map (μ := volume) (φ := (B : Eu l →ₗ[ℝ] Eu l)) (f := fun x => ‖f x‖ ^ (2 : ℝ))
      B.continuous.aemeasurable (f.continuous.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hd, integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _)] at h1
    simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, dil_apply hB, norm_smul, norm_real, Real.rpow_two,
      mul_pow, Real.norm_eq_abs, sq_abs, hc, integral_const_mul] at h1 ⊢
    erw [← h1]
    rw [smul_eq_mul, ← mul_assoc, ← abs_mul, ContinuousLinearMap.det, mul_inv_cancel₀ hd, abs_one, one_mul]

def fou (l : Type) [Fintype l] : Sch l →L[ℂ] Sch l := FourierTransform.fourierCLM ℂ (Sch l)

def fouInv (l : Type) [Fintype l] : Sch l →L[ℂ] Sch l := FourierTransform.fourierInvCLM ℂ (Sch l)

theorem fou_apply (f : Sch l) : fou l f = 𝓕 f := rfl

theorem fouInv_apply (f : Sch l) : fouInv l f = 𝓕⁻ f := rfl

theorem fou_mul_fouInv : fou l * fouInv l = 1 := by
  ext1 f
  rw [ContinuousLinearMap.mul_apply, fou_apply, fouInv_apply, FourierTransform.fourier_fourierInv_eq]
  rfl

theorem fouInv_mul_fou : fouInv l * fou l = 1 := by
  ext1 f
  rw [ContinuousLinearMap.mul_apply, fou_apply, fouInv_apply, FourierTransform.fourierInv_fourier_eq]
  rfl

theorem isUnit_fou : IsUnit (fou l) := ⟨⟨_, _, fou_mul_fouInv, fouInv_mul_fou⟩, rfl⟩

theorem isUnit_fouInv : IsUnit (fouInv l) := ⟨⟨_, _, fouInv_mul_fou, fou_mul_fouInv⟩, rfl⟩

theorem iso_fou : Iso (fou l) := fun f => norm_fourier_toL2_eq f

theorem iso_fouInv : Iso (fouInv l) := fun f => by
  rw [← iso_fou (fouInv l f), ← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]

theorem intw_fou (p q : Eu l) : Intw (fou l) p q (-q) p := fun f g h => by
  funext x
  simp only [fou_apply, fourier_coe, rf, h, Real.fourier_eq', smul_eq_mul]
  rw [← integral_const_mul, ← integral_add_right_eq_self (μ := volume) (fun v => exp (((2 * π * ⟪p, x⟫ + π * ⟪-q, p⟫ : ℝ) : ℂ) * I) *
    (exp (((-2 * π * ⟪v, x + -q⟫ : ℝ) : ℂ) * I) * f v)) p]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
  congr 2
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, real_inner_comm q p, real_inner_comm q v]
  ring

theorem intw_fouInv (p q : Eu l) : Intw (fouInv l) p q q (-p) := fun f g h => by
  funext x
  have h1 := congrFun (intw_fou p q f g h) (-x)
  have e : ∀ (u : Sch l) y, fouInv l u y = fou l u (-y) := fun u y => rfl
  rw [e, h1]
  simp only [rf, e, inner_neg_left, inner_neg_right, neg_add]

def big (Ai B C : Eu l →L[ℝ] Eu l) (c : ℝ) : Sch l →L[ℂ] Sch l :=
  ph (C * Ai) * (((c : ℂ) • dil Ai) * (fou l * (ph (-(Ai * B)) * fouInv l)))

theorem isUnit_big {Ai : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (B C : Eu l →L[ℝ] Eu l) {c : ℝ} (hc : c ≠ 0) :
    IsUnit (big Ai B C c) := by
  refine (isUnit_ph _).mul (IsUnit.mul ?_ (isUnit_fou.mul ((isUnit_ph _).mul isUnit_fouInv)))
  rw [Algebra.smul_def]
  exact ((IsUnit.mk0 (c : ℂ) (by simpa using hc)).map _).mul (isUnit_dil h)

theorem iso_big {Ai : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (B C : Eu l →L[ℝ] Eu l) {c : ℝ} (hc : c ^ 2 = |Ai.det|) :
    Iso (big Ai B C c) :=
  (iso_ph _).mul ((iso_dil h hc).mul (iso_fou.mul ((iso_ph _).mul iso_fouInv)))

theorem big_one : big (1 : Eu l →L[ℝ] Eu l) 0 0 1 = 1 := by
  simp [big, ph_zero, dil_one, fou_mul_fouInv]

theorem intw_big {A Ai B C D : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (h1 : ∀ x, A (Ai x) = x) (h2 : ∀ x, Ai (A x) = x)
    (hAC : ∀ y z, ⟪A y, C z⟫ = ⟪C y, A z⟫) (hBD : ∀ y z, ⟪B y, D z⟫ = ⟪D y, B z⟫)
    (hAD : ∀ y z, ⟪A y, D z⟫ - ⟪C y, B z⟫ = ⟪y, z⟫) (c : ℝ) (p q : Eu l) :
    Intw (big Ai B C c) p q (A p + B q) (C p + D q) := by
  have hS : ∀ x y, ⟪x, (C * Ai) y⟫ = ⟪y, (C * Ai) x⟫ := fun x y => by
    have := hAC (Ai x) (Ai y)
    rw [h1, h1] at this
    exact this.trans (real_inner_comm _ _)
  have hr : ∀ q x, ⟪D q - (C * Ai) (B q), x⟫ = ⟪q, Ai x⟫ := fun q x => by
    have := hAD (Ai x) q
    rw [h1] at this
    rw [inner_sub_left, real_inner_comm x, real_inner_comm x, hS, real_inner_comm (Ai x) q, ← this,
      real_inner_comm _ (B q)]
    rfl
  have hT : ∀ x y, ⟪x, (-(Ai * B)) y⟫ = ⟪y, (-(Ai * B)) x⟫ := fun x y => by
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, ContinuousLinearMap.mul_apply (f := Ai), ← hr,
      inner_sub_left]
    rw [← hBD, real_inner_comm (B x) (D y), real_inner_comm (B y), real_inner_comm (B x), hS]
  have e : C p + D q = D q - (C * Ai) (B q) + (C * Ai) (A p + B q) := by
    simp [h2, add_comm]
  rw [e]
  refine (intw_ph hS _ _).mul (((intw_dil h ?_ (hr q)).smul c).mul
    ((intw_fou _ _).mul ((intw_ph hT _ _).mul (intw_fouInv p q))))
  simp [h2, add_comm]

end CompanionTheory.ThKR.LL
end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform

namespace CompanionTheory.ThKR.LL

variable {l : Type} [Fintype l]

def mq (S : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  smulLeftCLM ℂ fun x : Eu l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I

theorem mq_apply (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) : mq S f x = ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I * f x := by
  have h2 : Function.HasTemperateGrowth fun x : Eu l => -π * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : Eu l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I :=
    (ofRealCLM.hasTemperateGrowth.comp h2).mul (Function.HasTemperateGrowth.const _)
  rw [mq, smulLeftCLM_apply_apply h3, smul_eq_mul]

theorem norm_exp_sub_le (a b : ℝ) : ‖exp ((a : ℂ) * I) - exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have : exp ((a : ℂ) * I) - exp ((b : ℂ) * I) = exp ((b : ℂ) * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem exists_lip {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {S : ℝ → F} {S' : F} {t₀ : ℝ}
    (h : HasDerivAt S S' t₀) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in 𝓝 t₀, ‖S t - S t₀‖ ≤ K * |t - t₀| := by
  obtain ⟨K, hK, h⟩ := h.isBigO_sub.exists_nonneg
  exact ⟨K, hK, h.bound⟩

theorem ld_ph {S : ℝ → Eu l →L[ℝ] Eu l} {S' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt S S' t₀) :
    LD (fun t => ph (S t)) (fun f => mq S' (ph (S t₀) f)) t₀ := fun f => by
  obtain ⟨K, hK, hb⟩ := exists_lip h
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C, hC, hf⟩ := exists_decay f (N + 2)
  refine hasDerivAt_schwartz_to_L2 (C := π * K * C) (fun x => ?_) ?_
  · simp only [ph_apply, mq_apply]
    have h1 : HasDerivAt (fun t => S t x) (S' x) t₀ := by simpa using h.clm_apply (hasDerivAt_const t₀ x)
    have h2 : HasDerivAt (fun t => ⟪x, S t x⟫) ⟪x, S' x⟫ t₀ := (innerSL ℝ x).hasFDerivAt.comp_hasDerivAt t₀ h1
    exact (((h2.const_mul (-π)).ofReal_comp.mul_const I).cexp.mul_const (f x)).congr_deriv (by ring)
  · filter_upwards [hb] with t ht x
    rw [← hN]
    simp only [ph_apply]
    rw [← sub_mul, norm_mul]
    have h1 : |-π * ⟪x, S t x⟫ - -π * ⟪x, S t₀ x⟫| ≤ π * ((1 + ‖x‖) ^ 2 * (K * |t - t₀|)) := by
      rw [← mul_sub, ← inner_sub_right, abs_mul, abs_neg, abs_of_pos Real.pi_pos, ← ContinuousLinearMap.sub_apply]
      refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans ?_) Real.pi_pos.le
      have h2 := (S t - S t₀).le_opNorm x
      calc ‖x‖ * ‖(S t - S t₀) x‖ ≤ ‖x‖ * ((K * |t - t₀|) * ‖x‖) := by
            refine mul_le_mul_of_nonneg_left (h2.trans ?_) (norm_nonneg _)
            gcongr
        _ = ‖x‖ ^ 2 * (K * |t - t₀|) := by ring
        _ ≤ _ := by gcongr; simp
    calc _ ≤ (1 + ‖x‖) ^ N * (π * ((1 + ‖x‖) ^ 2 * (K * |t - t₀|)) * ‖f x‖) := by
          gcongr
          exact (norm_exp_sub_le _ _).trans h1
      _ = π * K * ((1 + ‖x‖) ^ (N + 2) * ‖f x‖) * |t - t₀| := by ring
      _ ≤ _ := by gcongr; exact hf x

def vf (H : Eu l →L[ℝ] Eu l) (f : Sch l) : Sch l :=
  bilinLeftCLM (ContinuousLinearMap.id ℝ (Eu l →L[ℝ] ℂ)) H.hasTemperateGrowth (fderivCLM ℝ (Eu l) ℂ f)

theorem vf_apply (H : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) : vf H f x = fderiv ℝ f x (H x) := rfl

theorem ld_dil_one {H : ℝ → Eu l →L[ℝ] Eu l} {H' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt H H' t₀) (h0 : H t₀ = 1)
    (f : Sch l) {F : ℝ → Sch l} (hF : ∀ᶠ t in 𝓝 t₀, ∀ x, F t x = f (H t x)) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l (vf H' f)) t₀ := by
  obtain ⟨K, hK, hb⟩ := exists_lip h
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C, hC, hf⟩ := exists_decay (fderivCLM ℝ (Eu l) ℂ f) (N + 1)
  refine hasDerivAt_schwartz_to_L2 (C := 2 ^ (N + 1) * C * K) (fun x => ?_) ?_
  · have h1 : HasDerivAt (fun t => H t x) (H' x) t₀ := by simpa using h.clm_apply (hasDerivAt_const t₀ x)
    have h2 := (f.hasFDerivAt (H t₀ x)).comp_hasDerivAt t₀ h1
    rw [h0] at h2
    exact h2.congr_of_eventuallyEq (hF.mono fun t ht => ht x)
  · have hs : ∀ᶠ t in 𝓝 t₀, ‖H t - H t₀‖ ≤ 1 / 2 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 h.continuousAt).eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
      exact this
    filter_upwards [hb, hF, hs] with t ht hFt hst x
    rw [← hN, hFt, hF.self_of_nhds, h0]
    have e : ‖H t x - x‖ ≤ ‖H t - H t₀‖ * ‖x‖ := by
      have := (H t - H t₀).le_opNorm x
      rw [ContinuousLinearMap.sub_apply] at this
      simpa only [h0, ContinuousLinearMap.one_apply] using this
    have hw : 0 < 1 + ‖x‖ := by positivity
    have hm := (convex_closedBall x (‖x‖ / 2)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f)
      (C := 2 ^ (N + 1) * C / (1 + ‖x‖) ^ (N + 1)) (x := x) (y := H t x) (fun y _ => f.differentiableAt) (fun y hy => by
        rw [le_div_iff₀ (by positivity)]
        have h1 : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
          have h2 := norm_sub_norm_le x y
          rw [mem_closedBall_iff_norm'] at hy
          linarith
        calc _ ≤ ‖fderiv ℝ f y‖ * (2 * (1 + ‖y‖)) ^ (N + 1) := by gcongr
          _ = 2 ^ (N + 1) * ((1 + ‖y‖) ^ (N + 1) * ‖fderiv ℝ f y‖) := by rw [mul_pow]; ring
          _ ≤ _ := by gcongr; exact hf y)
      (Metric.mem_closedBall_self (by positivity)) (by
        rw [mem_closedBall_iff_norm]
        nlinarith [norm_nonneg x])
    have e2 : ‖H t x - x‖ ≤ K * |t - t₀| * (1 + ‖x‖) := e.trans (by gcongr; simp)
    calc _ ≤ (1 + ‖x‖) ^ N * (2 ^ (N + 1) * C / (1 + ‖x‖) ^ (N + 1) * (K * |t - t₀| * (1 + ‖x‖))) := by
          refine mul_le_mul_of_nonneg_left (hm.trans ?_) (by positivity)
          gcongr
      _ = _ := by rw [pow_succ (1 + ‖x‖) N]; field_simp

theorem ld_dil {B : ℝ → Eu l →L[ℝ] Eu l} {B' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt B B' t₀) (h0 : IsUnit (B t₀)) :
    LD (fun t => dil (B t)) (fun f => vf (Ring.inverse (B t₀) * B') (dil (B t₀) f)) t₀ := fun f => by
  refine ld_dil_one (h.const_mul (Ring.inverse (B t₀))) (Ring.inverse_mul_cancel _ h0) _ ?_
  filter_upwards [h.continuousAt.eventually (Units.isOpen.mem_nhds h0)] with t ht x
  rw [dil_apply ht, dil_apply h0, ← ContinuousLinearMap.mul_apply, ← mul_assoc, Ring.mul_inverse_cancel _ h0, one_mul]

theorem ld_big {Ai B C : ℝ → Eu l →L[ℝ] Eu l} {Ai' B' C' : Eu l →L[ℝ] Eu l} {c : ℝ → ℝ} {c' t₀ : ℝ}
    (hA : HasDerivAt Ai Ai' t₀) (hB : HasDerivAt B B' t₀) (hC : HasDerivAt C C' t₀) (hc : HasDerivAt c c' t₀)
    (h : ∀ᶠ t in 𝓝 t₀, IsUnit (Ai t) ∧ c t ^ 2 = |(Ai t).det|) :
    ∃ Q, LD (fun t => big (Ai t) (B t) (C t) (c t)) Q t₀ ∧ (Ai t₀ = 1 → B t₀ = 0 → C t₀ = 0 → c t₀ = 1 → ∀ f,
      Q f = mq C' f + vf Ai' f + fou l (mq (-B') (fouInv l f)) + (c' : ℂ) • f) := by
  have h1 := (ld_ph (hA.mul hB).neg).mul (LD.const (fouInv l) t₀) (.of_forall fun t => iso_ph _)
  have h2 := (LD.const (fou l) t₀).mul h1 (.of_forall fun t => iso_fou)
  have h3 := ((ld_dil hA h.self_of_nhds.1).smul hc.ofReal_comp).mul h2 (h.mono fun t ht => iso_dil ht.1 ht.2)
  have h4 := (ld_ph (hC.mul hA)).mul h3 (.of_forall fun t => iso_ph _)
  refine ⟨_, h4, fun e1 e2 e3 e4 f => ?_⟩
  have e5 : fou l (fouInv l f) = f := by
    rw [← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]
  simp [e1, e2, e3, e4, ph_zero, dil_one, e5]
  abel

end CompanionTheory.ThKR.LL
end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform

namespace CompanionTheory.ThKR.LL

variable {l : Type} [Fintype l] [DecidableEq l]

def bl (i j : l → l ⊕ l) : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] (Eu l →L[ℝ] Eu l) where
  toFun g := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (g.submatrix i j)
  map_add' g h := by rw [← map_add]; rfl
  map_smul' c g := by rw [RingHom.id_apply, ← map_smul]; rfl

theorem bl_apply (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (x : Eu l) (a : l) :
    bl i j g x a = ∑ b, g (i a) (j b) * x b := rfl

theorem pPart_mulVec (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    pPart (g *ᵥ w) = bl Sum.inl Sum.inl g (pPart w) + bl Sum.inl Sum.inr g (qPart w) := by
  ext a
  simp [bl_apply, pPart, qPart, mulVec, dotProduct]

theorem qPart_mulVec (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    qPart (g *ᵥ w) = bl Sum.inr Sum.inl g (pPart w) + bl Sum.inr Sum.inr g (qPart w) := by
  ext a
  simp [bl_apply, pPart, qPart, mulVec, dotProduct]

theorem det_bl (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) : (bl i j g).det = (g.submatrix i j).det :=
  LinearMap.det_toLin (EuclideanSpace.basisFun l ℝ).toBasis _

theorem block_inl_inl_one : bl Sum.inl Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := by
  ext x a
  simp [bl_apply, Matrix.one_apply]

theorem block_inl_inr_one : bl Sum.inl Sum.inr (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by
  ext x a
  simp [bl_apply, Matrix.one_apply]

theorem block_inr_inl_one : bl Sum.inr Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by
  ext x a
  simp [bl_apply, Matrix.one_apply]

theorem hasDerivAt_lin_exp {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] F)
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • X))) (L (NormedSpace.exp (t • X) * X)) t := by
  letI := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t)

theorem exp_mul_exp_neg (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right, add_neg_cancel, NormedSpace.exp_zero]

theorem sympl_exp {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (w w' : l ⊕ l → ℝ) :
    sympl (NormedSpace.exp X *ᵥ w) (NormedSpace.exp X *ᵥ w') = sympl w w' := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have hu : IsUnit (Matrix.J l ℝ) :=
    ⟨⟨Matrix.J l ℝ, -Matrix.J l ℝ, by rw [mul_neg, J_squared, neg_neg], by rw [neg_mul, J_squared, neg_neg]⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : Xᵀ = Matrix.J l ℝ * -X * (Matrix.J l ℝ)⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᵀ * (Matrix.J l ℝ * NormedSpace.exp X) = Matrix.J l ℝ := by
    have := exp_mul_exp_neg (-X)
    rw [neg_neg] at this
    rw [← Matrix.exp_transpose, h1, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.J l ℝ),
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc, this, Matrix.mul_one]
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]

theorem intw_of_sympl {g : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hg : ∀ w w', sympl (g *ᵥ w) (g *ᵥ w') = sympl w w')
    (h : IsUnit (bl Sum.inl Sum.inl g)) (c : ℝ) (w : l ⊕ l → ℝ) :
    Intw (big (Ring.inverse (bl Sum.inl Sum.inl g)) (bl Sum.inl Sum.inr g) (bl Sum.inr Sum.inl g) c) (pPart w) (qPart w)
      (pPart (g *ᵥ w)) (qPart (g *ᵥ w)) := by
  have key : ∀ p q p' q' : Eu l, ⟪bl Sum.inl Sum.inl g p + bl Sum.inl Sum.inr g q,
      bl Sum.inr Sum.inl g p' + bl Sum.inr Sum.inr g q'⟫ - ⟪bl Sum.inr Sum.inl g p + bl Sum.inr Sum.inr g q,
      bl Sum.inl Sum.inl g p' + bl Sum.inl Sum.inr g q'⟫ = ⟪p, q'⟫ - ⟪q, p'⟫ := fun p q p' q' => by
    have := hg (Sum.elim (fun i => p i) fun i => q i) (Sum.elim (fun i => p' i) fun i => q' i)
    simp only [sympl, pPart_mulVec, qPart_mulVec] at this
    exact this
  rw [pPart_mulVec, qPart_mulVec]
  refine intw_big h.ringInverse (fun x => ?_) (fun x => ?_) (fun y z => ?_) (fun y z => ?_) (fun y z => ?_) c _ _
  · rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ h, ContinuousLinearMap.one_apply]
  · rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ h, ContinuousLinearMap.one_apply]
  · simpa [sub_eq_zero] using key y 0 z 0
  · simpa [sub_eq_zero] using key 0 y 0 z
  · simpa using key y 0 0 z

theorem fou_mq_fouInv (B : Matrix l l ℝ) (f : Sch l) :
    fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) B)) (fouInv l f)) =
      (4 * π * I : ℂ)⁻¹ • ∑ j, ∑ k, (B j k : ℂ) • (∂_{(EuclideanSpace.single j 1 : Eu l)}
        (∂_{(EuclideanSpace.single k 1 : Eu l)} f)) := by
  have e : ∀ u : Sch l, fou l (fouInv l u) = u := fun u => by
    rw [← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]
  rw [← e (_ • _)]
  congr 1
  have h : ∀ j (u : Sch l), fouInv l (dRho (Pi.single (Sum.inl j) 1) u) = -dRho (Pi.single (Sum.inr j) 1) (fouInv l u) :=
    fourierInv_dRho_inl
  simp only [← dRho_single_inl, map_smul, map_sum, h, map_neg, neg_neg]
  ext x
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [mq_apply, SchwartzMap.smul_apply, SchwartzMap.sum_apply, dRho_single_inr, smul_eq_mul,
    ContinuousLinearMap.neg_apply, inner_neg_right, inner_toEuclideanCLM, dotProduct, mulVec, Finset.mul_sum]
  push_cast
  simp only [mul_neg, neg_mul, neg_neg, Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp
  ring

theorem quad_eq {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (f : Sch l) :
    quad X f = mq (bl Sum.inr Sum.inl X) f + vf (-bl Sum.inl Sum.inl X) f +
      fou l (mq (-bl Sum.inl Sum.inr X) (fouInv l f)) - ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f := by
  ext x
  have h := quad_fromBlocks (A := X.toBlocks₁₁) (B := X.toBlocks₁₂) (C := X.toBlocks₂₁) (D := X.toBlocks₂₂)
    (by rwa [fromBlocks_toBlocks]) f x
  rw [fromBlocks_toBlocks] at h
  have h2 := fou_mq_fouInv X.toBlocks₁₂ f
  have h3 : vf (-bl Sum.inl Sum.inl X) f x =
      -∑ j, ∑ k, (X.toBlocks₁₁ j k : ℂ) * x k * (∂_{(EuclideanSpace.single j 1 : Eu l)} f) x := by
    have : bl Sum.inl Sum.inl X x = ∑ j, ∑ k, (X.toBlocks₁₁ j k * x k) • (EuclideanSpace.single j 1 : Eu l) := by
      ext a
      simp [bl_apply, Pi.single_apply, toBlocks₁₁, Finset.sum_apply]
    rw [vf_apply, ContinuousLinearMap.neg_apply, this]
    simp [lineDerivOp_apply_eq_fderiv]
  have h4 : mq (bl Sum.inr Sum.inl X) f x = -(π * I * ∑ j, ∑ k, (X.toBlocks₂₁ j k : ℂ) * x j * x k * f x) := by
    have : ⟪x, bl Sum.inr Sum.inl X x⟫ = x ⬝ᵥ X.toBlocks₂₁ *ᵥ x := inner_toEuclideanCLM _ _ _
    rw [mq_apply, this]
    simp only [dotProduct, mulVec]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [SchwartzMap.sub_apply, SchwartzMap.add_apply]
  rw [h, h3, h4]
  erw [h2]
  simp only [SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul]
  push_cast
  ring

end CompanionTheory.ThKR.LL

namespace CompanionTheory.ThKR

open LL

end CompanionTheory.ThKR
end
end
