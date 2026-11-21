import Mathlib
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.HilbertSchmidtKernel
import GroundTheory.AutomorphicForms.HilbertSchmidtCompact
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract

section
open MeasureTheory Topology Filter Set
open scoped ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

theorem compMeasurePreserving_congr {α : Type*} [MeasurableSpace α] {ν : Measure α} {p : ℝ≥0∞}
    {f f' : α → α} (h : f = f') (hf : MeasurePreserving f ν ν) (hf' : MeasurePreserving f' ν ν)
    (φ : Lp ℂ p ν) :
    Lp.compMeasurePreserving f hf φ = Lp.compMeasurePreserving f' hf' φ := by
  subst h
  rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.IsMulRightInvariant]

def rightTranslate (g : G) :
    Lp ℂ 2 (quotientMeasure Γ μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure Γ μ) where
  toLinearEquiv :=
    { Lp.compMeasurePreservingₗ ℂ (rightMul Γ g) (measurePreserving_rightMul μ g) with
      invFun := Lp.compMeasurePreservingₗ ℂ (rightMul Γ g⁻¹) (measurePreserving_rightMul μ g⁻¹)
      left_inv := fun φ ↦ by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ) = φ
        rw [← Lp.compMeasurePreserving_comp_apply, compMeasurePreserving_congr _ _
          (MeasurePreserving.id _), Lp.compMeasurePreserving_id_apply]
        rw [← rightMul_mul, inv_mul_cancel, rightMul_one]
      right_inv := fun φ ↦ by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ) = φ
        rw [← Lp.compMeasurePreserving_comp_apply, compMeasurePreserving_congr _ _
          (MeasurePreserving.id _), Lp.compMeasurePreserving_id_apply]
        rw [← rightMul_mul, mul_inv_cancel, rightMul_one] }
  norm_map' φ := Lp.norm_compMeasurePreserving φ _

theorem coeFn_rightTranslate (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightTranslate Γ μ g φ =ᵐ[quotientMeasure Γ μ] fun x ↦ φ (rightMul Γ g x) :=
  Lp.coeFn_compMeasurePreserving φ _

def rightRegular : G →* (Lp ℂ 2 (quotientMeasure Γ μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure Γ μ)) where
  toFun := rightTranslate Γ μ
  map_one' := by
    ext1 φ
    change Lp.compMeasurePreserving _ _ φ = φ
    rw [compMeasurePreserving_congr (rightMul_one Γ) _ (MeasurePreserving.id _),
      Lp.compMeasurePreserving_id_apply]
  map_mul' g h := by
    ext1 φ
    rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
    change Lp.compMeasurePreserving _ _ φ =
      Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact compMeasurePreserving_congr (rightMul_mul Γ g h) _ _ φ

@[simp]
theorem rightRegular_apply (g : G) : rightRegular Γ μ g = rightTranslate Γ μ g :=
  rfl

def rightRegularUnitary :
    G →* unitary (Lp ℂ 2 (quotientMeasure Γ μ) →L[ℂ] Lp ℂ 2 (quotientMeasure Γ μ)) :=
  (Unitary.linearIsometryEquiv (𝕜 := ℂ)).symm.toMonoidHom.comp (rightRegular Γ μ)



section Continuity

variable [IsFiniteMeasureOnCompacts μ]

omit [μ.IsMulRightInvariant] in

theorem tendsto_lintegral_rightMul_sub {ψ : RightCosetSpace Γ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (g₀ : G) :
    Tendsto (fun g ↦ ∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
      ∂quotientMeasure Γ μ) (𝓝 g₀) (𝓝 0) := by
  obtain ⟨N, hN, hNn⟩ := exists_compact_mem_nhds g₀
  set K : Set (RightCosetSpace Γ) :=
    (fun p : RightCosetSpace Γ × G ↦ rightMul Γ p.2⁻¹ p.1) '' (tsupport ψ ×ˢ N) with hKdef
  have hK : IsCompact K := (hs.prod hN).image
    ((continuous_rightMul_prod Γ).comp (continuous_fst.prodMk continuous_snd.inv))
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  have hzero : ∀ g ∈ N, ∀ x ∉ K, ψ (rightMul Γ g x) = 0 := by
    intro g hg x hx
    by_contra h
    refine hx ⟨(rightMul Γ g x, g), ⟨subset_tsupport ψ h, hg⟩, ?_⟩
    change rightMul Γ g⁻¹ (rightMul Γ g x) = x
    rw [rightMul_rightMul, mul_inv_cancel, rightMul_one, id]
  have hg₀N : g₀ ∈ N := mem_of_mem_nhds hNn
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * M) ^ (2 : ℝ) with hc_def
  have hmeas : ∀ g, Measurable fun x ↦ ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ) :=
    fun g ↦ (((hc.comp (continuous_rightMul Γ g)).sub
      (hc.comp (continuous_rightMul Γ g₀))).measurable.enorm).pow_const _
  suffices key : Tendsto (fun g ↦ ∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
      ∂quotientMeasure Γ μ) (𝓝 g₀) (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂quotientMeasure Γ μ)) by
    rwa [lintegral_zero] at key
  refine tendsto_lintegral_filter_of_dominated_convergence (K.indicator fun _ ↦ c)
    (Eventually.of_forall hmeas) ?_ ?_ ?_
  · filter_upwards [hNn] with g hg
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖
          ≤ ‖ψ (rightMul Γ g x)‖ + ‖ψ (rightMul Γ g₀ x)‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hM (rightMul Γ g x), hM (rightMul Γ g₀ x)]
    · rw [hzero g hg x hx, hzero g₀ hg₀N x hx, sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
  · rw [lintegral_indicator_const hK.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hK.measure_lt_top.ne
  · refine Eventually.of_forall fun x ↦ ?_
    have hcont : Continuous fun g ↦ ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const).comp (continuous_enorm.comp
        ((hc.comp ((continuous_rightMul_prod Γ).comp
          (continuous_const.prodMk continuous_id))).sub continuous_const))
    have := hcont.tendsto g₀
    rwa [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem tendsto_rightRegular_of_continuous {ψ : RightCosetSpace Γ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (g₀ : G) :
    Tendsto (fun g ↦ rightRegular Γ μ g ((hc.memLp_of_hasCompactSupport hs).toLp ψ)) (𝓝 g₀)
      (𝓝 (rightRegular Γ μ g₀ ((hc.memLp_of_hasCompactSupport hs).toLp ψ))) := by
  have hψ : MemLp ψ 2 (quotientMeasure Γ μ) := hc.memLp_of_hasCompactSupport hs
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hae : ∀ g, ⇑(rightRegular Γ μ g (hψ.toLp ψ)) =ᵐ[quotientMeasure Γ μ]
      fun x ↦ ψ (rightMul Γ g x) := fun g ↦
    (coeFn_rightTranslate Γ μ g _).trans
      ((measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq_comp hψ.coeFn_toLp)
  have heq : ∀ g, eLpNorm (⇑(rightRegular Γ μ g (hψ.toLp ψ)) - ⇑(rightRegular Γ μ g₀ (hψ.toLp ψ)))
      2 (quotientMeasure Γ μ) = (∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
        ∂quotientMeasure Γ μ) ^ (1 / (2 : ℝ)) := fun g ↦ by
    rw [eLpNorm_congr_ae ((hae g).sub (hae g₀)),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
  simp_rw [heq]
  have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp
    (tendsto_lintegral_rightMul_sub Γ μ hc hs g₀)
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem continuous_rightRegular_apply (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    Continuous fun g ↦ rightRegular Γ μ g φ := by
  refine continuous_iff_continuousAt.2 fun g₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨ψ, hs, hψφ, hc, hmem⟩ := (Lp.memLp φ).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 4)) (by simpa using hε4)
  set φ₀ : Lp ℂ 2 (quotientMeasure Γ μ) := (hc.memLp_of_hasCompactSupport hs).toLp ψ
  have hd : dist φ φ₀ ≤ ε / 4 := by
    rw [Lp.dist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp _))]
    exact ENNReal.toReal_le_of_le_ofReal hε4.le hψφ
  filter_upwards [Metric.tendsto_nhds.1 (tendsto_rightRegular_of_continuous Γ μ hc hs g₀) (ε / 4)
    hε4] with g hg
  calc dist (rightRegular Γ μ g φ) (rightRegular Γ μ g₀ φ)
      ≤ dist (rightRegular Γ μ g φ) (rightRegular Γ μ g φ₀) +
          (dist (rightRegular Γ μ g φ₀) (rightRegular Γ μ g₀ φ₀) +
            dist (rightRegular Γ μ g₀ φ₀) (rightRegular Γ μ g₀ φ)) :=
        (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
    _ = dist φ φ₀ + (dist (rightRegular Γ μ g φ₀) (rightRegular Γ μ g₀ φ₀) + dist φ₀ φ) := by
        rw [LinearIsometryEquiv.dist_map, LinearIsometryEquiv.dist_map]
    _ < ε := by
        rw [dist_comm φ₀ φ]
        linarith


end Continuity

end RightCosetSpace

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Topology Filter Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G)

def automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) (p : G × G) : ℂ :=
  ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2)

theorem automorphicKernel_smul_left (f : CompactlySupportedContinuousMap G ℂ) (δ : Γ) (a b : G) :
    automorphicKernel Γ f (δ • a, b) = automorphicKernel Γ f (a, b) := by
  unfold automorphicKernel
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]
  congr 1
  group

theorem automorphicKernel_smul_right (f : CompactlySupportedContinuousMap G ℂ) (δ : Γ) (a b : G) :
    automorphicKernel Γ f (a, δ • b) = automorphicKernel Γ f (a, b) := by
  unfold automorphicKernel
  rw [← finsum_comp_equiv (Equiv.mulRight δ⁻¹)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulRight, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  congr 1
  group

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ]

theorem locallyFinite_support_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) :
    LocallyFinite fun γ : Γ => support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  intro p
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds p.1
  obtain ⟨B, hBc, hB⟩ := exists_compact_mem_nhds p.2
  refine ⟨A ×ˢ B, prod_mem_nhds hA hB, ?_⟩
  have hAS : IsCompact (A * tsupport f) := hAc.mul f.hasCompactSupport
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image hBc hAS).subset ?_
  rintro γ ⟨⟨a, b⟩, hq, hab⟩
  simp only [mem_prod] at hab
  refine ⟨γ • b, mem_image_of_mem _ hab.2, ?_⟩
  refine ⟨a, hab.1, a⁻¹ * γ * b, subset_tsupport _ hq, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul]
  group

theorem continuous_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (automorphicKernel Γ f) :=
  continuous_finsum (fun γ => f.continuous.comp (by fun_prop))
    (locallyFinite_support_automorphicKernel Γ f)

theorem finite_support_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) (p : G × G) :
    (support fun γ : Γ => f (p.1⁻¹ * γ * p.2)).Finite := by
  exact (locallyFinite_support_automorphicKernel Γ f).point_finite p

def quotientKernel (f : CompactlySupportedContinuousMap G ℂ)
    (p : RightCosetSpace Γ × RightCosetSpace Γ) : ℂ :=
  Quotient.lift₂ (fun a b => automorphicKernel Γ f (a, b)) (fun a₁ b₁ a₂ b₂ ha hb => by
    obtain ⟨δ, rfl⟩ := ha
    obtain ⟨ε, rfl⟩ := hb
    rw [automorphicKernel_smul_left, automorphicKernel_smul_right]) p.1 p.2

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
@[simp] theorem quotientKernel_mk (f : CompactlySupportedContinuousMap G ℂ) (a b : G) :
    quotientKernel Γ f (mk Γ a, mk Γ b) = ∑ᶠ γ : Γ, f (a⁻¹ * γ * b) :=
  rfl

theorem continuous_quotientKernel (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (quotientKernel Γ f) := by
  have hq : IsQuotientMap (Prod.map (mk Γ) (mk Γ)) :=
    ((isOpenQuotientMap_mk Γ).prodMap (isOpenQuotientMap_mk Γ)).isQuotientMap
  refine hq.continuous_iff.2 ?_
  exact continuous_automorphicKernel Γ f

section Operator

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]

def rightRegularRep : UnitaryRep G (Lp ℂ 2 (quotientMeasure Γ μ)) :=
  UnitaryRep.ofLinearIsometryEquiv (rightRegular Γ μ) (continuous_rightRegular_apply Γ μ)

theorem rightRegularRep_apply (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightRegularRep Γ μ g φ = rightTranslate Γ μ g φ :=
  rfl

theorem coeFn_rightRegularRep (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightRegularRep Γ μ g φ =ᵐ[quotientMeasure Γ μ] fun x => φ (rightMul Γ g x) :=
  coeFn_rightTranslate Γ μ g φ

omit [μ.IsMulRightInvariant] in

theorem integral_mul_rightMul_eq (f : CompactlySupportedContinuousMap G ℂ)
    (φ : C(RightCosetSpace Γ, ℂ)) (x : RightCosetSpace Γ) :
    ∫ g, f g * φ (rightMul Γ g x) ∂μ =
      ∫ y, quotientKernel Γ f (x, y) * φ y ∂quotientMeasure Γ μ := by
  obtain ⟨a, rfl⟩ := mk_surjective Γ x
  have h1 : ∫ g, f g * φ (rightMul Γ g (mk Γ a)) ∂μ = ∫ g, φ (mk Γ g) * f (a⁻¹ * g) ∂μ := by
    rw [← integral_mul_left_eq_self (fun g => φ (mk Γ g) * f (a⁻¹ * g)) a]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [rightMul_mk, inv_mul_cancel_left, mul_comm]
  have hcs : HasCompactSupport fun g => f (a⁻¹ * g) :=
    f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft a⁻¹)
  have hint : Integrable (fun g => φ (mk Γ g) * f (a⁻¹ * g)) μ :=
    ((φ.continuous.comp (continuous_mk Γ)).mul
      (f.continuous.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_left
  rw [h1, integral_mul_eq_integral_mul_automorphize μ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  obtain ⟨b, rfl⟩ := mk_surjective Γ y
  dsimp only
  rw [quotientKernel_mk, mul_comm]
  congr 1
  change ∑' γ : Γ, f (a⁻¹ * (γ • b)) = _
  simp_rw [Subgroup.smul_def, smul_eq_mul, ← mul_assoc]
  exact tsum_eq_finsum (finite_support_automorphicKernel Γ f (a, b))

variable [CompactSpace (RightCosetSpace Γ)]

omit [μ.IsMulRightInvariant] in

theorem memLp_quotientKernel (f : CompactlySupportedContinuousMap G ℂ) :
    MemLp (quotientKernel Γ f) 2 ((quotientMeasure Γ μ).prod (quotientMeasure Γ μ)) :=
  (continuous_quotientKernel Γ f).memLp_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
theorem coeFn_compactSupportToL1 (f : CompactlySupportedContinuousMap G ℂ) :
    (UnitaryRep.ccToL1 μ f : G → ℂ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

def kernelOperator (f : CompactlySupportedContinuousMap G ℂ) :
    Lp ℂ 2 (quotientMeasure Γ μ) →L[ℂ] Lp ℂ 2 (quotientMeasure Γ μ) :=
  L2Kernel.kernelOp ((memLp_quotientKernel Γ μ f).toLp _)

omit [μ.IsMulRightInvariant] in

theorem isHilbertSchmidt_kernelOperator (f : CompactlySupportedContinuousMap G ℂ) :
    IsHilbertSchmidt (kernelOperator Γ μ f) :=
  L2Kernel.kernelOp_isHilbertSchmidt _

theorem inner_integrated_toLp (f : CompactlySupportedContinuousMap G ℂ)
    (φ ψ : C(RightCosetSpace Γ, ℂ)) :
    ⟪ContinuousMap.toLp 2 (quotientMeasure Γ μ) ℂ ψ,
      (rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)
        (ContinuousMap.toLp 2 (quotientMeasure Γ μ) ℂ φ)⟫_ℂ =
      ∫ x, conj (ψ x) * ∫ y, quotientKernel Γ f (x, y) * φ y ∂quotientMeasure Γ μ
        ∂quotientMeasure Γ μ := by
  set ν := quotientMeasure Γ μ with hν
  set Ψ := ContinuousMap.toLp 2 ν ℂ ψ
  set Φ := ContinuousMap.toLp 2 ν ℂ φ
  have hΨ : Ψ =ᵐ[ν] ψ := ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) ψ
  have hΦ : Φ =ᵐ[ν] φ := ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) φ
  have hcoef : ∀ g, ⟪Ψ, rightRegularRep Γ μ g Φ⟫_ℂ = ∫ x, conj (ψ x) * φ (rightMul Γ g x) ∂ν := by
    intro g
    rw [L2.inner_def]
    have h2 : (fun x => Φ (rightMul Γ g x)) =ᵐ[ν] fun x => φ (rightMul Γ g x) :=
      (measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq_comp hΦ
    refine integral_congr_ae ?_
    filter_upwards [hΨ, coeFn_rightRegularRep Γ μ g Φ, h2] with x h1 h3 h4
    rw [h1, h3, h4, RCLike.inner_apply']
  have hF : Integrable (uncurry fun g x => f g * (conj (ψ x) * φ (rightMul Γ g x))) (μ.prod ν) := by
    have hc : Continuous (uncurry fun g x => f g * (conj (ψ x) * φ (rightMul Γ g x))) := by
      refine (f.continuous.comp continuous_fst).mul
        ((Complex.continuous_conj.comp (ψ.continuous.comp continuous_snd)).mul
          (φ.continuous.comp ?_))
      exact (continuous_rightMul_prod Γ).comp (continuous_snd.prodMk continuous_fst)
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (f.hasCompactSupport.prod isCompact_univ) fun p hp => ?_
    have : p.1 ∉ tsupport f := fun h => hp ⟨h, mem_univ _⟩
    simp [uncurry, image_eq_zero_of_notMem_tsupport this]
  rw [UnitaryRep.inner_integrated]
  calc ∫ g, (UnitaryRep.ccToL1 μ f) g * ⟪Ψ, rightRegularRep Γ μ g Φ⟫_ℂ ∂μ
      = ∫ g, f g * ∫ x, conj (ψ x) * φ (rightMul Γ g x) ∂ν ∂μ :=
        integral_congr_ae ((coeFn_compactSupportToL1 μ f).mono fun g hg => by simp only [hg, hcoef g])
    _ = ∫ g, ∫ x, f g * (conj (ψ x) * φ (rightMul Γ g x)) ∂ν ∂μ := by
        simp_rw [← integral_const_mul]
    _ = ∫ x, ∫ g, f g * (conj (ψ x) * φ (rightMul Γ g x)) ∂μ ∂ν := integral_integral_swap hF
    _ = ∫ x, conj (ψ x) * ∫ g, f g * φ (rightMul Γ g x) ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← integral_const_mul]
        congr 1
        ext g
        ring
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [integral_mul_rightMul_eq Γ μ f φ x]

omit [μ.IsMulRightInvariant] in

theorem inner_kernelOperator_toLp (f : CompactlySupportedContinuousMap G ℂ)
    (φ ψ : C(RightCosetSpace Γ, ℂ)) :
    ⟪ContinuousMap.toLp 2 (quotientMeasure Γ μ) ℂ ψ,
      kernelOperator Γ μ f (ContinuousMap.toLp 2 (quotientMeasure Γ μ) ℂ φ)⟫_ℂ =
      ∫ x, conj (ψ x) * ∫ y, quotientKernel Γ f (x, y) * φ y ∂quotientMeasure Γ μ
        ∂quotientMeasure Γ μ := by
  set ν := quotientMeasure Γ μ with hν
  set Ψ := ContinuousMap.toLp 2 ν ℂ ψ
  set Φ := ContinuousMap.toLp 2 ν ℂ φ
  have hΨ : Ψ =ᵐ[ν] ψ := ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) ψ
  have hΦ : Φ =ᵐ[ν] φ := ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) φ
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hΨ, L2Kernel.kernelOp_toLp_apply_ae (memLp_quotientKernel Γ μ f) Φ] with x h1 h2
  rw [kernelOperator, h1, h2, RCLike.inner_apply']
  congr 1
  exact integral_congr_ae (hΦ.mono fun y hy => by dsimp only; rw [hy])

theorem integrated_rightRegularRep_eq_kernelOperator (f : CompactlySupportedContinuousMap G ℂ) :
    (rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f) = kernelOperator Γ μ f := by
  set ν := quotientMeasure Γ μ
  have hD : DenseRange (ContinuousMap.toLp 2 ν ℂ : C(RightCosetSpace Γ, ℂ) →L[ℂ] Lp ℂ 2 ν) :=
    ContinuousMap.toLp_denseRange ℂ ν ℂ ENNReal.ofNat_ne_top
  have h2 : ∀ φ : C(RightCosetSpace Γ, ℂ),
      (rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f) (ContinuousMap.toLp 2 ν ℂ φ) =
        kernelOperator Γ μ f (ContinuousMap.toLp 2 ν ℂ φ) := fun φ =>
    ext_inner_left ℂ fun w => hD.induction_on w
      (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const))
      fun ψ => by rw [inner_integrated_toLp, inner_kernelOperator_toLp]
  refine ContinuousLinearMap.ext fun v => ?_
  exact congrFun (hD.equalizer (ContinuousLinearMap.continuous _)
    (ContinuousLinearMap.continuous _) (funext h2)) v

theorem isHilbertSchmidt_integrated_rightRegularRep (f : CompactlySupportedContinuousMap G ℂ) :
    IsHilbertSchmidt ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) := by
  rw [integrated_rightRegularRep_eq_kernelOperator]
  exact isHilbertSchmidt_kernelOperator Γ μ f

theorem isCompactOperator_integrated_rightRegularRep (f : CompactlySupportedContinuousMap G ℂ) :
    IsCompactOperator ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) :=
  (isHilbertSchmidt_integrated_rightRegularRep Γ μ f).isCompactOperator

end Operator

end RightCosetSpace

end

end GroundTheory.Automorphic
end
