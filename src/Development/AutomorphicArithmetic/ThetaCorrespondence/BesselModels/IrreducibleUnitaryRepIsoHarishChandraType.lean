import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsWtOnIffOfTorus
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SetIntegralDifferentiability
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.NsqEqRnSq
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightsCompactStabilizer

section
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ContDiff Topology

noncomputable section

namespace UpperTheory.Lit.Bur.HWSpanType.Derived

theorem contDiff_setIntegral_nat {X P E : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {a : X → E} (ha : Continuous a)
    (m : ℕ) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ψ : P × E → F),
      ContDiff ℝ ∞ Ψ → ContDiff ℝ m fun p => ∫ x in K, Ψ (p, a x) ∂μ :=
  _root_.UpperTheory.Reformulated.B.SetIntegralDifferentiability.contDiff_setIntegral_nat μ hK ha m

open Formalism.REAL

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem differentiableAt_exp_line {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    DifferentiableAt ℝ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).differentiableAt
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact (LinearMap.toContinuousLinearMap L).differentiableAt.comp 0 h

end

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_matMul {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f g : P → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun p => f p * g p := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ => (contDiff_pi.1 (contDiff_pi.1 hf i) l).mul (contDiff_pi.1 (contDiff_pi.1 hg l) j)

theorem contDiff_adj {n : ℕ} : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => xᴴ
      map_add' := fun x y => conjTranspose_add x y
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem smooth_of_continuous {n : ℕ} {ε : Fin n → Bool} {B : Type} [NormedRing B] [NormedAlgebra ℂ B]
    [CompleteSpace B] {σ : Matrix (Fin n) (Fin n) ℂ → B} (h1 : σ 1 = 1)
    (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b)
    (hcont : ContinuousOn σ {g | inUJ ε g}) : SmoothOnGV ε σ := by
  obtain ⟨hemb, hrange⟩ := isClosedEmbeddingMatrix n ε
  set μ := muG ε
  have hmem : ∀ g : UJ ε, inUJ ε (toM g) := fun g => g.2
  have hu : Continuous fun g : UJ ε => toM g := hemb.continuous
  have hb : Continuous fun g : UJ ε => σ (toM g) := hcont.comp_continuous hu hmem
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := hmem 1
  have hnb : {g | ‖σ g - 1‖ < 1 / 2} ∈ 𝓝[{g | inUJ ε g}] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hcont 1 hone) (Metric.ball_mem_nhds _ (half_pos one_pos))
    simpa [h1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφU, hφc, hφ, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hψ : Continuous fun g : UJ ε => φ (toM g) := hφ.continuous.comp hu
  have hψc : HasCompactSupport fun g : UJ ε => φ (toM g) := hφc.comp_isClosedEmbedding hemb
  have hint : Integrable (fun g : UJ ε => φ (toM g) • σ (toM g)) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
  have hψi : Integrable (fun g : UJ ε => φ (toM g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : UJ ε, φ (toM g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  set c := ∫ g : UJ ε, φ (toM g) ∂μ with hc
  set A := ∫ g : UJ ε, φ (toM g) • σ (toM g) ∂μ with hA
  have hAu : ∃ A' : B, A * A' = 1 := by
    have e1 : ∫ g : UJ ε, (φ (toM g) • σ (toM g) - φ (toM g) • (1 : B)) ∂μ = A - c • (1 : B) := by
      rw [integral_sub hint (hψi.smul_const _), integral_smul_const]
    have e2 : ‖∫ g : UJ ε, (φ (toM g) • σ (toM g) - φ (toM g) • (1 : B)) ∂μ‖
        ≤ ∫ g : UJ ε, φ (toM g) * (1 / 2) ∂μ := by
      refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : φ (toM g) = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs ⟨hφU (subset_tsupport _ hg), hmem g⟩)) (hφ0 _)
    rw [e1, integral_mul_const, ← hc] at e2
    have e3 : ‖(1 : B) - c⁻¹ • A‖ < 1 := by
      have : (1 : B) - c⁻¹ • A = -(c⁻¹ • (A - c • (1 : B))) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, neg_sub]
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (inv_pos.2 hpos).le, inv_mul_lt_iff₀ hpos]
      linarith
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one e3
    rw [sub_sub_cancel] at hu
    refine ⟨c⁻¹ • (↑u⁻¹ : B), ?_⟩
    rw [mul_smul_comm, ← smul_mul_assoc, ← hu, Units.mul_inv]
  obtain ⟨A', hA'⟩ := hAu
  let y : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun x => Jm ε * xᴴ * Jm ε
  have hy : ContDiff ℝ ∞ y := contDiff_matMul (contDiff_matMul contDiff_const contDiff_adj) contDiff_const
  have hyx : ∀ x, inUJ ε x → y x * x = 1 := fun x hx => by
    have h : xᴴ * Jm ε * x = Jm ε := hx
    calc y x * x = Jm ε * (xᴴ * Jm ε * x) := by simp only [y, Matrix.mul_assoc]
      _ = 1 := by rw [h, Jm_mul_self]
  have hform : ∀ x, inUJ ε x → σ x * A = ∫ g : UJ ε, φ (y x * toM g) • σ (toM g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [show Set.range (fun g : UJ ε => toM g) = _ from hrange]; exact hx
    have hz' : toM z = x := hz
    have := (ContinuousLinearMap.mul ℂ B (σ x)).integral_comp_comm hint
    rw [ContinuousLinearMap.mul_apply'] at this
    rw [hA, ← this, ← integral_mul_left_eq_self (fun g : UJ ε => φ (y x * toM g) • σ (toM g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : toM (z * g) = x * toM g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hyx x hx, Matrix.one_mul, hmul _ hx _ (hmem g), ContinuousLinearMap.mul_apply',
      mul_smul_comm]
  intro x₀ _
  have hC : IsCompact (Set.image2 (· * ·) (Metric.closedBall x₀ 1) (tsupport φ)) := by
    rw [← Set.image_prod]
    exact ((isCompact_closedBall x₀ 1).prod hφc).image (contDiff_matMul contDiff_fst contDiff_snd).continuous
  have hK := hemb.isCompact_preimage hC
  have hs : ContDiff ℝ ∞ fun x => ∫ g in (fun g : UJ ε => toM g) ⁻¹'
      (Set.image2 (· * ·) (Metric.closedBall x₀ 1) (tsupport φ)), φ (y x * toM g) • σ (toM g) ∂μ :=
    contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
      (fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × B) => φ (y z.1 * z.2.1) • z.2.2)
      ((hφ.comp (contDiff_matMul (hy.comp contDiff_fst) (contDiff_fst.comp contDiff_snd))).smul
        (contDiff_snd.comp contDiff_snd))
  refine ⟨Metric.ball x₀ 1, _, Metric.isOpen_ball, Metric.mem_ball_self one_pos,
    (hs.mul (contDiff_const (c := A'))).contDiffOn, fun x hx hxG => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, ← hform x hxG, mul_assoc, hA', mul_one]
  intro g hg
  by_contra hne
  refine hg ⟨x, Metric.ball_subset_closedBall hx, y x * toM g,
    subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
  show x * (y x * toM g) = toM g
  rw [← Matrix.mul_assoc, mul_eq_one_comm.1 (hyx x hxG), Matrix.one_mul]

section Deriv

variable {n : ℕ} {ε : Fin n → Bool} {B : Type} [NormedRing B] [NormedAlgebra ℂ B]
  {σ : Matrix (Fin n) (Fin n) ℂ → B}

theorem hasDerivAt_rdV {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnGV ε f) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) (RdV X f 1) 0 := by
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simpa using exp_indefinite_unitary_holds n ε X hX 0
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hf 1 hone
  have hd : DifferentiableAt ℝ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0 :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => differentiableAt_exp_line X i j
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
  have hFd : DifferentiableAt ℝ F (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact (hF.contDiffAt (hU.mem_nhds h1)).differentiableAt (by simp)
  have hev : (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      F ∘ fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := by
    filter_upwards [hd.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds h1)] with t ht
    exact hfF _ ht (exp_indefinite_unitary_holds n ε X hX t)
  have := ((hFd.comp 0 hd).congr_of_eventuallyEq hev).hasDerivAt
  simpa only [RdV, Matrix.one_mul] using this

theorem rdV_mul (hs : SmoothOnGV ε σ) (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    RdV X σ g = σ g * RdV X σ 1 := by
  rw [← ((hasDerivAt_rdV hs hX).const_mul (σ g)).deriv, RdV]
  congr 1
  funext t
  exact hmul _ hg _ (exp_indefinite_unitary_holds n ε X hX t)

theorem rdV_one_of_eq (hs : SmoothOnGV ε σ) {f : Matrix (Fin n) (Fin n) ℂ → B} {b : B}
    (hf : ∀ g, inUJ ε g → f g = σ g * b) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    RdV X f 1 = RdV X σ 1 * b := by
  rw [← ((hasDerivAt_rdV hs hX).mul_const b).deriv, RdV]
  congr 1
  funext t
  rw [Matrix.one_mul]
  exact hf _ (exp_indefinite_unitary_holds n ε X hX t)

theorem eabV_mul (hs : SmoothOnGV ε σ) (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b σ g = σ g * EabV ε a b σ 1 := by
  obtain ⟨h1, h2, -⟩ := cpartMem n ε (Matrix.single a b 1)
  simp only [EabV, EcV]
  rw [rdV_mul hs hmul h1 hg, rdV_mul hs hmul h2 hg, mul_add, mul_smul_comm]

theorem eabV_eabV (hs : SmoothOnGV ε σ) (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b)
    (a b c d : Fin n) :
    EabV ε a b (EabV ε c d σ) 1 = EabV ε a b σ 1 * EabV ε c d σ 1 := by
  obtain ⟨h1, h2, -⟩ := cpartMem n ε (Matrix.single a b 1)
  have h := fun g hg => eabV_mul hs hmul c d (g := g) hg
  show RdV _ _ 1 + Complex.I • RdV _ _ 1 = (RdV _ σ 1 + Complex.I • RdV _ σ 1) * _
  rw [rdV_one_of_eq hs h h1, rdV_one_of_eq hs h h2, add_mul, smul_mul_assoc]

theorem glRel_eabV (hs : SmoothOnGV ε σ) (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b) :
    GlRel fun a b => EabV ε a b σ 1 := by
  intro a b c d
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have := eabGlV n ε B σ a b c d 1 hs hone
  rwa [eabV_eabV hs hmul, eabV_eabV hs hmul] at this

theorem rdV_eq_sum (hs : SmoothOnGV ε σ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    RdV Z σ 1 = ∑ a, ∑ b, Z a b • EabV ε a b σ 1 := by
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  obtain ⟨h1, h2⟩ := (cpartMem n ε Z).2.2.2 hZ
  rw [← ecSumV n ε B σ Z 1 hs hone, EcV, h1, h2]
  simp [RdV]

end Deriv

section Unit

variable {n : ℕ} {ε : Fin n → Bool} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}

theorem hasDerivAt_apply (hs : SmoothOnGV ε π) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : W) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (RdV X π 1 v) 0 :=
  ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_rdV hs hX)

theorem rdV_skew (hs : SmoothOnGV ε π) (h1 : π 1 = 1) (hiso : ∀ g, inUJ ε g → ∀ v, ‖π g v‖ = ‖v‖)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (x y : W) :
    ⟪RdV X π 1 x, y⟫_ℂ = -⟪x, RdV X π 1 y⟫_ℂ := by
  have h := (hasDerivAt_apply hs hX x).inner ℂ (hasDerivAt_apply hs hX y)
  have hc : (fun t : ℝ => ⟪π (NormedSpace.exp ((t : ℂ) • X)) x, π (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ)
      = fun _ => ⟪x, y⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(π (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hiso _ (exp_indefinite_unitary_holds n ε X hX t)⟩ x y
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, h1, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

end Unit

theorem Jm_allPos (k : ℕ) : Jm (PI.UpqRep.allPos k) = 1 := by
  simp [Jm, PI.UpqRep.allPos]

theorem exists_derived_action : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)),
    PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π →
    ∃ E : Fin k → Fin k → Module.End ℂ W, Formalism.REAL.GlRel E ∧ Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E ∧
      ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
        HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
  intro k W _ _ _ π ⟨⟨h1, hmul⟩, hiso, hcont⟩
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hmul' : ∀ a, inUJ (PI.UpqRep.allPos k) a → ∀ b, inUJ (PI.UpqRep.allPos k) b → π (a * b) = π a * π b := hmul
  have hs : SmoothOnGV (PI.UpqRep.allPos k) π :=
    smooth_of_continuous h1 hmul' (continuousOn_clm_apply.2 hcont)
  have hone : inUJ (PI.UpqRep.allPos k) (1 : Matrix (Fin k) (Fin k) ℂ) := by simp [inUJ]
  refine ⟨fun a b => (EabV (PI.UpqRep.allPos k) a b π 1).toLinearMap, ?_, ?_, ?_⟩
  · intro a b c d
    have := congrArg ContinuousLinearMap.toLinearMap (glRel_eabV hs hmul' a b c d)
    split_ifs at this ⊢ <;> exact this
  · intro a b x y
    obtain ⟨h1', h2', -⟩ := cpartMem k (PI.UpqRep.allPos k) (Matrix.single a b 1)
    have e1 : cpart1 (PI.UpqRep.allPos k) (Matrix.single b a 1) =
        ((-1 : ℝ) : ℂ) • cpart1 (PI.UpqRep.allPos k) (Matrix.single a b (1 : ℂ)) := by
      simp only [cpart1, Jm_allPos, Matrix.one_mul, Matrix.mul_one, conjTranspose_single, star_one]
      rw [← neg_sub, smul_neg]
      push_cast
      rw [neg_one_smul]
    have e2 : cpart2 (PI.UpqRep.allPos k) (Matrix.single b a 1) =
        cpart2 (PI.UpqRep.allPos k) (Matrix.single a b (1 : ℂ)) := by
      simp only [cpart2, Jm_allPos, Matrix.one_mul, Matrix.mul_one, conjTranspose_single, star_one, add_comm]
    have e3 := (rdLinV k _ _ π π _ _ (-1) 0 1 hs hs h1' h1' hone).2.1
    simp only [EabV, EcV, e1, e2, e3, sgn, PI.UpqRep.allPos, if_true, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    have s1 := rdV_skew hs h1 hiso h1' x y
    have s2 := rdV_skew hs h1 hiso h2' x y
    rw [s1, s2]
    simp
  · intro Z hZ v
    have hG : inG (PI.UpqRep.allPos k) Z := by simp [inG, Jm_allPos, hZ]
    have := hasDerivAt_apply hs hG v
    rw [rdV_eq_sum hs hG] at this
    simpa using this

end UpperTheory.Lit.Bur.HWSpanType.Derived

namespace UpperTheory.Lit.Bur.HWSpanType.Wt

theorem cdom_add_lowering_word {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ)
    (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    PI.UpqRep.CDom ε (Λ + Formalism.REAL.wordWeightShift w) Λ := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, by simp, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, he⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have hp := hw p List.mem_cons_self
    refine ⟨fun a b => c a b + (if a = p.2 then if b = p.1 then 1 else 0 else 0), ?_, ?_⟩
    · intro a b hab
      by_cases h0 : c a b = 0
      · by_cases h1 : a = p.2
        · by_cases h2 : b = p.1
          · subst h1; subst h2; exact ⟨hp.2, hp.1.symm⟩
          · simp [h0, h2] at hab
        · simp [h0, h1] at hab
      · exact hc a b h0
    · have h1 : ∑ a, ∑ b, (((if a = p.2 then if b = p.1 then 1 else 0 else 0 : ℕ) : ℝ)) •
          PI.UpqRep.root a b = PI.UpqRep.root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2]
        · rw [Finset.sum_eq_single p.1]
          · simp
          · intro b _ hb; simp [hb]
          · simp
        · intro a _ ha; simp [ha]
        · simp
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib]
      rw [h1, ← he]
      simp only [Formalism.REAL.wordWeightShift, PI.UpqRep.root]
      abel

theorem weight_cdom_of_mem_kSpan :
    ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (Λ μ : Fin k → ℝ) (x v : W), Formalism.REAL.GlRel E → Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E → Formalism.REAL.KHighest (PI.UpqRep.allPos k) E Λ x → v ∈ Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x → v ≠ 0 → Formalism.REAL.IsWeight E μ v → PI.UpqRep.CDom (PI.UpqRep.allPos k) μ Λ := by
  intro k W _ _ E Λ μ x v hg hu hΛ hv hv0 hμ
  by_contra hne
  have hk := Formalism.REAL.isUnitary_kUnit _ E hu
  have hr := Formalism.REAL.glRel_kRel (PI.UpqRep.allPos k) E hg
  rw [Formalism.REAL.compact_span_eq_lowering hr hΛ] at hv
  have key : ∀ z ∈ Formalism.REAL.lowSpan (PI.UpqRep.allPos k) E x, ⟪z, v⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      refine Formalism.REAL.compact_weight_orthogonal W k _ E _ μ _ v hk
        (Formalism.REAL.word_action_weight hr hΛ.1 w (fun q hq => (hw q hq).1)) hμ ?_
      intro heq
      exact hne (heq ▸ cdom_add_lowering_word _ Λ w hw)
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]
  exact hv0 (inner_self_eq_zero.mp (key v hv))

section OneParam

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem deriv_right (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (t : ℝ) :
    HasDerivAt (fun s => U s v) (U t (A v)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) v) (A v) t := by
    have h := hd v
    rw [← sub_self t] at h
    exact HasDerivAt.comp_sub_const t t h
  have h2 := ((U t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  have h3 : HasDerivAt (fun s => U t (U (s - t) v)) (U t (A v)) t := h2
  convert h3 using 1
  funext s
  simp [← hadd]

theorem deriv_left (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (t : ℝ) :
    HasDerivAt (fun s => U s v) (A (U t v)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) (U t v)) (A (U t v)) t := by
    have h := hd (U t v)
    rw [← sub_self t] at h
    exact HasDerivAt.comp_sub_const t t h
  convert h1 using 1
  funext s
  simp [← hadd]

theorem eigen (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (c : ℂ) (hv : A v = c • v) :
    U 1 v = Complex.exp c • v := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • U t v) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    have h2 := h1.fun_smul (deriv_right U A hadd hd v t)
    convert h2 using 1
    rw [hv, map_smul, smul_smul, ← add_smul]
    simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    one_smul, h0] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem stable [FiniteDimensional ℂ W] (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (S : Submodule ℂ W) (hS : ∀ v ∈ S, A v ∈ S)
    (v : W) (hv : v ∈ S) (t : ℝ) : U t v ∈ S := by
  set Q : W →L[ℂ] W := ContinuousLinearMap.id ℂ W - S.starProjection with hQ
  have hQ0 : ∀ y ∈ S, Q y = 0 := fun y hy => by
    simp [hQ, (Submodule.starProjection_eq_self_iff (K := S)).2 hy]
  set B : W →L[ℂ] W := Q.comp (LinearMap.toContinuousLinearMap A) with hB
  have hq : ∀ t, HasDerivAt (fun s => Q (U s v)) (B (Q (U t v))) t := by
    intro t
    have h2 : HasDerivAt (fun s => Q (U s v)) (Q (A (U t v))) t :=
      (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (deriv_left U A hadd hd v t)
    convert h2 using 1
    have h3 : Q (A (S.starProjection (U t v))) = 0 :=
      hQ0 _ (hS _ (Submodule.starProjection_apply_mem S _))
    have h4 : Q (U t v) = U t v - S.starProjection (U t v) := by simp [hQ]
    simp only [hB, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    rw [h4, map_sub, map_sub, h3, sub_zero]
  have hz : (fun s => Q (U s v)) = fun _ => (0 : W) := by
    refine ODE_solution_unique_univ (v := fun _ y => B y) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0)
      (fun _ => B.lipschitz.lipschitzOnWith) (fun t => ⟨hq t, trivial⟩)
      (fun t => ⟨by simpa using hasDerivAt_const t (0 : W), trivial⟩) ?_
    simp only [h0]
    exact hQ0 v hv
  have h5 : U t v - S.starProjection (U t v) = 0 := by simpa [hQ] using congrFun hz t
  rw [sub_eq_zero.1 h5]
  exact Submodule.starProjection_apply_mem S _

end OneParam

open PI.UpqRep

theorem Jm_allPos (k : ℕ) : Jm (allPos k) = 1 := by
  simp [Jm, allPos]

theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Jm (allPos k) = Jm (allPos k) * g) ↔
    gᴴ * Jm (allPos k) * g = Jm (allPos k)
  rw [Jm_allPos, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

theorem exp_mem {k : ℕ} {Z : Matrix (Fin k) (Fin k) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Z) ∈ UJset (allPos k) := by
  refine Formalism.REAL.exp_indefinite_unitary_holds k (allPos k) Z ?_ t
  show Zᴴ * Jm (allPos k) + Jm (allPos k) * Z = 0
  rw [Jm_allPos, hZ]
  simp

variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)}

theorem group_zero (hπ : IsURepOn (UJset (allPos k)) π) (Z : Matrix (Fin k) (Fin k) ℂ) (v : W) :
    π (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) v = v := by
  simp [hπ.1.1]

theorem group_add (hπ : IsURepOn (UJset (allPos k)) π) {Z : Matrix (Fin k) (Fin k) ℂ} (hZ : Zᴴ = -Z)
    (s t : ℝ) (v : W) :
    π (NormedSpace.exp (((s + t : ℝ) : ℂ) • Z)) v =
      π (NormedSpace.exp ((s : ℂ) • Z)) (π (NormedSpace.exp ((t : ℂ) • Z)) v) := by
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl Z).smul_left _).smul_right _), hπ.1.2 _ (exp_mem hZ s) _ (exp_mem hZ t)]
  rfl

theorem diag_skew (θ : Fin k → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)ᴴ = -Matrix.diagonal fun a => (θ a : ℂ) * Complex.I := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  congr 1
  funext a
  simp

theorem exp_diag (θ : Fin k → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      Matrix.diagonal fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext a
  rw [← Complex.exp_eq_exp_ℂ]
  simp [mul_assoc]

theorem sum_diag (E : Fin k → Fin k → Module.End ℂ W) (d : Fin k → ℂ) (v : W) :
    ∑ a, ∑ b, Matrix.diagonal d a b • E a b v = ∑ a, d a • E a a v := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diagonal_apply, ite_smul]

theorem isWtOn_of_isWeight (hπ : IsURepOn (UJset (allPos k)) π) (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin k → ℝ) (v : W) (hv : Formalism.REAL.IsWeight E μ v) : IsWtOn (Kset (allPos k)) π μ v := by
  intro θ _
  have h := eigen (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)))
    (∑ a, ((θ a : ℂ) * Complex.I) • E a a) (group_zero hπ _) (group_add hπ (diag_skew θ))
    (fun w => by
      have := hE _ (diag_skew θ) w
      rw [sum_diag] at this
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using this)
    v (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) (by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hv _, smul_smul, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring)
  simp only [exp_diag, one_mul] at h
  exact h

theorem isWeight_of_isWtOn (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin k → ℝ) (v : W) (hv : IsWtOn (Kset (allPos k)) π μ v) : Formalism.REAL.IsWeight E μ v := by
  intro a
  set θ : Fin k → ℝ := Pi.single a 1 with hθ
  have h1 := hE _ (diag_skew θ) v
  rw [sum_diag] at h1
  have h2 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) v) =
      fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v := by
    funext t
    have hm := exp_mem (diag_skew θ) t
    rw [exp_diag] at hm ⊢
    rw [hv (fun b => t * θ b) ((mem_K_iff _).2 hm)]
    congr 2
    simp [hθ, Pi.single_apply]
    ring
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v) ((μ a * Complex.I) • v) 0 := by
    have h4 : HasDerivAt (fun t : ℝ => (μ a * Complex.I) * (t : ℂ)) (μ a * Complex.I) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (μ a * Complex.I)
    simpa using h4.cexp.smul_const v
  rw [h2] at h1
  have h5 := h1.unique h3
  have h6 : ∑ b, ((θ b : ℂ) * Complex.I) • E b b v = Complex.I • E a a v := by
    rw [Finset.sum_eq_single a]
    · simp [hθ]
    · intro b _ hb
      simp [hθ, Pi.single_eq_of_ne hb]
    · simp
  rw [h6, mul_comm, ← smul_smul] at h5
  exact smul_right_injective W Complex.I_ne_zero h5

theorem stable_of_derived [FiniteDimensional ℂ W] (hπ : IsURepOn (UJset (allPos k)) π)
    (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (S : Submodule ℂ W) (hS : Formalism.REAL.KStable (allPos k) E S) :
    ∀ g ∈ UJset (allPos k), ∀ v ∈ S, π g v ∈ S := by
  intro g hg v hv
  obtain ⟨Y, hY, hg', -⟩ := Formalism.REAL.compact_exponential_surjective k (allPos k) g ((mem_K_iff g).2 hg)
  have hZ : Yᴴ = -Y := by
    have h : Yᴴ * Jm (allPos k) + Jm (allPos k) * Y = 0 := hY.1
    rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := stable (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E a b)
    (group_zero hπ _) (group_add hπ hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hE _ hZ w) S
    (fun w hw => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b rfl w hw)) v hv 1
  simpa [hg'] using h

end UpperTheory.Lit.Bur.HWSpanType.Wt

end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace UpperTheory.Lit.Bur.HWSpanType

open PI.UpqRep UpperTheory.Lit.Bur.HWSpanType.Wt

theorem mem_of_skew {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (L : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W) (S : Submodule ℂ W)
    (h : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → L Z ∈ S) (Z : Matrix (Fin k) (Fin k) ℂ) : L Z ∈ S := by
  have h1 : L (Z - Zᴴ) ∈ S := h _ (by simp)
  have h2 : L (Complex.I • (Z + Zᴴ)) ∈ S := h _ (by simp [conjTranspose_smul, add_comm])
  have e : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + (-Complex.I / 2) • (Complex.I • (Z + Zᴴ)) := by
    rw [smul_smul, show -Complex.I / 2 * Complex.I = 1 / 2 by
      rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I, neg_neg]]
    module
  rw [e, map_add, map_smul, map_smul]
  exact S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h2)

def actL {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (v : W) :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W where
  toFun Z := ∑ a, ∑ b, Z a b • E a b v
  map_add' Y Z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c Z := by simp [Finset.smul_sum, smul_smul]

theorem actL_single {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (E : Fin k → Fin k → Module.End ℂ W)
    (v : W) (a b : Fin k) : actL E v (Matrix.single a b 1) = E a b v := by
  show ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • E c d v = _
  simp [Matrix.single, ite_and, ite_smul]

variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)}

theorem kStable_of_group [FiniteDimensional ℂ W] (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (S : Submodule ℂ W) (hS : ∀ g ∈ UJset (allPos k), ∀ v ∈ S, π g v ∈ S) :
    Formalism.REAL.KStable (allPos k) E S := by
  intro a b _ v hv
  rw [← actL_single]
  refine mem_of_skew _ S (fun Z hZ => ?_) _
  have h1 : HasDerivAt (fun t : ℝ => Sᗮ.starProjection (π (NormedSpace.exp ((t : ℂ) • Z)) v))
      (Sᗮ.starProjection (actL E v Z)) 0 :=
    (Sᗮ.starProjection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hE Z hZ v)
  have h2 : (fun t : ℝ => Sᗮ.starProjection (π (NormedSpace.exp ((t : ℂ) • Z)) v)) = fun _ => 0 := by
    funext t
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact hS _ (exp_mem hZ t) v hv
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : W))
  rwa [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h3

def compress [FiniteDimensional ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)) (S : Submodule ℂ W)
    (g : Matrix (Fin k) (Fin k) ℂ) : S →L[ℂ] S :=
  S.orthogonalProjection.comp ((π g).comp S.subtypeL)

theorem coe_compress [FiniteDimensional ℂ W] {S : Submodule ℂ W} {g : Matrix (Fin k) (Fin k) ℂ} {v : S}
    (h : π g v ∈ S) : (compress π S g v : W) = π g v :=
  (Submodule.starProjection_eq_self_iff (K := S)).2 h

theorem exists_type_of_highest [FiniteDimensional ℂ W] (hπ : IsURepOn (UJset (allPos k)) π)
    (E : Fin k → Fin k → Module.End ℂ W) (hgl : Formalism.REAL.GlRel E) (hun : Formalism.REAL.IsUnitary (allPos k) E)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (u : Fin k → ℝ) (x : W) (hx : x ≠ 0) (hΛ : Formalism.REAL.KHighest (allPos k) E (lowK (allPos k) u) x) :
    IsHCTypeU k u (compress π (Formalism.REAL.kSpan (allPos k) E x)) := by
  set S := Formalism.REAL.kSpan (allPos k) E x with hSdef
  have hxm : x ∈ S := Formalism.REAL.mem_compactSpan x
  have hst := stable_of_derived hπ E hE S (Formalism.REAL.isCompactInvariant_compactSpan x)
  have hc : ∀ g ∈ UJset (allPos k), ∀ v : S, (compress π S g v : W) = π g v :=
    fun g hg v => coe_compress (hst g hg v v.2)
  have hone : (1 : Matrix (Fin k) (Fin k) ℂ) ∈ UJset (allPos k) := by
    simpa using exp_mem (Z := (0 : Matrix (Fin k) (Fin k) ℂ)) (by simp) 0
  have hmul : ∀ a ∈ UJset (allPos k), ∀ b ∈ UJset (allPos k), a * b ∈ UJset (allPos k) := fun a ha b hb =>
    (mem_K_iff _).1 (Kset_mul _ ((mem_K_iff _).2 ha) ((mem_K_iff _).2 hb))
  have hwt : ∀ (μ : Fin k → ℝ) (v : S), IsWtOn (Kset (allPos k)) (compress π S) μ v ↔
      IsWtOn (Kset (allPos k)) π μ (v : W) := by
    intro μ v
    refine forall_congr' fun θ => forall_congr' fun hθ => ?_
    rw [← hc _ ((mem_K_iff _).1 hθ), ← Submodule.coe_smul, Subtype.coe_inj]
  refine ⟨⟨⟨x, hxm⟩, 0, fun h => hx (congrArg Subtype.val h)⟩, inferInstance, ⟨⟨?_, ?_⟩, ?_, ?_⟩,
    inferInstance, fun _ _ _ _ => trivial, ?_, ?_, ?_⟩
  · ext v
    rw [hc _ hone, hπ.1.1]
    rfl
  · intro a ha b hb
    ext v
    rw [hc _ (hmul a ha b hb), hπ.1.2 a ha b hb, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hc _ ha, hc _ hb]
  · intro g hg v
    show ‖(compress π S g v : W)‖ = ‖(v : W)‖
    rw [hc g hg, hπ.2.1 g hg]
  · intro v
    exact S.orthogonalProjection.continuous.comp_continuousOn (hπ.2.2 v)
  · intro T _ hT
    have hT' : Formalism.REAL.KStable (allPos k) E (T.map S.subtype) := by
      refine kStable_of_group E hE _ ?_
      rintro g hg _ ⟨v, hv, rfl⟩
      exact ⟨_, hT g ((mem_K_iff g).2 hg) v hv, hc g hg v⟩
    rcases Formalism.REAL.kIrr W k (allPos k) E _ x inferInstance (Formalism.REAL.glRel_kRel _ E hgl)
      (Formalism.REAL.isUnitary_kUnit _ E hun) hΛ _ (Submodule.map_subtype_le S T) hT' with h | h
    · left
      exact (Submodule.eq_bot_iff _).2 fun y hy => Subtype.ext ((Submodule.mem_bot ℂ).1
        (h ▸ Submodule.mem_map_of_mem hy))
    · right
      apply Submodule.map_injective_of_injective S.injective_subtype
      rw [h, Submodule.map_subtype_top]
  · exact ⟨⟨x, hxm⟩, trivial, fun h => hx (congrArg Subtype.val h),
      (hwt _ _).2 (isWtOn_of_isWeight hπ E hE _ x hΛ.1)⟩
  · intro μ v _ hv hw
    exact weight_cdom_of_mem_kSpan k W E _ μ x v hgl hun hΛ v.2 (fun h => hv (Subtype.ext h))
      (isWeight_of_isWtOn E hE μ v ((hwt _ _).1 hw))

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry (X : Matrix (Fin k) (Fin k) ℂ) (i j : Fin k) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

end



end UpperTheory.Lit.Bur.HWSpanType
end
end

section
open scoped InnerProductSpace
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
open GlobalTheory.CompanionTheory.KLowSpan (kLowSpan KLower)
open PI.UpqRep (root)

noncomputable section

namespace UpperTheory.Lit.Bur.KShift

variable {n : ℕ} {ε : Fin n → Bool}

section Alg

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}

theorem kUnit_of (hU : IsUnitary ε E) : KUnit ε E := by
  intro a b hab y z
  have := hU a b y z
  simpa [Formalism.REAL.sgn, hab] using this

theorem comm_apply (hE : GlRel E) (i j a b : Fin n) (u : V) :
    E i j (E a b u) = E a b (E i j u) +
      ((if j = a then E i b u else 0) - (if b = i then E a j u else 0)) := by
  have h := congrArg (fun T : Module.End ℂ V => T u) (hE i j a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> simp_all [sub_eq_iff_eq_add, add_comm]

def annSub (E : Fin n → Fin n → Module.End ℂ V) (x : V) : Submodule ℂ V where
  carrier := {s | ⟪x, s⟫_ℂ = 0 ∧ ∀ a b, ⟪x, E a b s⟫_ℂ = 0}
  add_mem' := by
    rintro s t ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [inner_add_right, h1, h3, add_zero], fun a b => by
      rw [map_add, inner_add_right, h2, h4, add_zero]⟩
  zero_mem' := ⟨by simp, fun a b => by simp⟩
  smul_mem' := by
    rintro c s ⟨h1, h2⟩
    exact ⟨by rw [inner_smul_right, h1, mul_zero], fun a b => by
      rw [map_smul, inner_smul_right, h2, mul_zero]⟩

theorem inner_lower_eq_zero (hU : KUnit ε E) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε E μ x)
    {c d : Fin n} (hdc : d < c) (he : ε c = ε d) (y : V) : ⟪x, E c d y⟫_ℂ = 0 := by
  rw [← hU d c he.symm, hx.2 d c hdc he.symm, inner_zero_left]

theorem ann_lower (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε E μ x)
    {c d : Fin n} (hdc : d < c) (he : ε c = ε d) {s : V} (hs : s ∈ annSub E x) :
    E c d s ∈ annSub E x := by
  refine ⟨hs.2 c d, fun a b => ?_⟩
  rw [comm_apply hE a b c d s, inner_add_right, inner_lower_eq_zero hU hx hdc he, inner_sub_right]
  split_ifs <;> simp [hs.2]

theorem lowSpan_le_ann (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {x v : V}
    (hx : KHighest ε E μ x) (hv : v ∈ annSub E x) : kLowSpan ε E v ≤ annSub E x := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => simpa using hv
  | cons p l ih =>
    rw [word_cons, Module.End.mul_apply]
    exact ann_lower hE hU hx (hl p (by simp)).1 (hl p (by simp)).2
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

def nbr (E : Fin n → Fin n → Module.End ℂ V) (A : Submodule ℂ V) : Submodule ℂ V :=
  A ⊔ ⨆ p : Fin n × Fin n, A.map (E p.1 p.2)

theorem mem_nbr_of_mem {A : Submodule ℂ V} {s : V} (hs : s ∈ A) : s ∈ nbr E A :=
  Submodule.mem_sup_left hs

theorem apply_mem_nbr {A : Submodule ℂ V} {s : V} (hs : s ∈ A) (a b : Fin n) : E a b s ∈ nbr E A :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (a, b) ⟨s, hs, rfl⟩)

theorem nbr_finite (A : Submodule ℂ V) [FiniteDimensional ℂ A] : FiniteDimensional ℂ (nbr E A) := by
  unfold nbr
  infer_instance

theorem nbr_stab (hE : GlRel E) {A : Submodule ℂ V} (hA : KStab ε E A) : KStab ε E (nbr E A) := by
  intro c d he v hv
  have hle : nbr E A ≤ (nbr E A).comap (E c d) := by
    refine sup_le (fun s hs => mem_nbr_of_mem (hA c d he s hs)) (iSup_le fun p => ?_)
    rintro _ ⟨s, hs, rfl⟩
    show E c d (E p.1 p.2 s) ∈ nbr E A
    rw [comm_apply hE c d p.1 p.2 s]
    refine Submodule.add_mem _ (apply_mem_nbr (hA c d he s hs) _ _) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact apply_mem_nbr hs _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact apply_mem_nbr hs _ _
      · exact Submodule.zero_mem _
  exact hle hv

theorem weight_shift (hE : GlRel E) (hU : KUnit ε E) {μ μ' : Fin n → ℝ} {v x : V}
    (hv : IsWeight E μ v) (hx : KHighest ε E μ' x) (hx0 : x ≠ 0)
    (hxT : x ∈ nbr E (kLowSpan ε E v)) : μ' = μ ∨ ∃ a b, μ' = μ + root a b := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hv' : v ∈ annSub E x :=
    ⟨GlobalTheory.CompanionTheory.KLowSpan.inner_eq_zero_of_weight hU hx.1 hv h1, fun a b =>
      GlobalTheory.CompanionTheory.KLowSpan.inner_eq_zero_of_weight hU hx.1
        (GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply hE hv a b) (h2 a b)⟩
  have hann := lowSpan_le_ann hE hU hx hv'
  have hle : nbr E (kLowSpan ε E v) ≤ (ℂ ∙ x)ᗮ := by
    refine sup_le (fun s hs => ?_) (iSup_le fun p => ?_)
    · exact (Submodule.mem_orthogonal_singleton_iff_inner_right).2 (hann hs).1
    · rintro _ ⟨s, hs, rfl⟩
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right).2 ((hann hs).2 p.1 p.2)
  exact hx0 (inner_self_eq_zero.1 ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hxT)))

theorem nsq_root_le (a b : Fin n) : Formalism.REAL.nsq (root a b) ≤ 2 := by
  by_cases hab : a = b
  · subst hab
    simp [Formalism.REAL.nsq, Formalism.REAL.dot, root]
  · have h : ∀ c, root a b c * root a b c = (if c = a then (1 : ℝ) else 0) + (if c = b then 1 else 0) := by
      intro c
      simp only [root, Pi.sub_apply, Pi.single_apply]
      by_cases h1 : c = a <;> by_cases h2 : c = b
      · exact absurd (h1.symm.trans h2) hab
      · simp [h1, h2]; simp [← h1, h2]
      · subst h2; simp [h1]
      · simp [h1, h2]
    have : Formalism.REAL.nsq (root a b) = 2 := by
      unfold Formalism.REAL.nsq Formalism.REAL.dot
      simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      norm_num
    exact this.le

theorem exists_weight (hE : GlRel E) (hU : KUnit ε E) {Q : Submodule ℂ V} [FiniteDimensional ℂ Q]
    (hQ : KStab ε E Q) (hQ0 : Q ≠ ⊥) : ∃ ν : Fin n → ℝ, ∃ x ∈ Q, x ≠ 0 ∧ IsWeight E ν x :=
  _root_.UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight hE hU hQ hQ0

theorem exists_highest (hE : GlRel E) (hU : KUnit ε E) {Q : Submodule ℂ V} [FiniteDimensional ℂ Q]
    (hQ : KStab ε E Q) (hQ0 : Q ≠ ⊥) : ∃ μ : Fin n → ℝ, ∃ x ∈ Q, x ≠ 0 ∧ KHighest ε E μ x := by
  classical
  let ht : (Fin n → ℝ) → ℝ := fun ν => ∑ c : Fin n, ((c : ℕ) : ℝ) * ν c
  let h : Module.End ℂ V := ∑ c : Fin n, (((c : ℕ) : ℝ) : ℂ) • E c c
  have hhQ : ∀ w ∈ Q, h w ∈ Q := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Q.sum_mem fun c _ => Q.smul_mem _ (hQ c c rfl w hw)
  have hh : ∀ (ν : Fin n → ℝ) (x : V), IsWeight E ν x → h x = ((ht ν : ℝ) : ℂ) • x := by
    intro ν x hx
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hx _, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℝ := {t | ∃ ν : Fin n → ℝ, ht ν = t ∧ ∃ x ∈ Q, x ≠ 0 ∧ IsWeight E ν x}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhQ)
    refine (hfin.preimage (f := fun t : ℝ => (t : ℂ)) Complex.ofReal_injective.injOn).subset ?_
    rintro t ⟨ν, rfl, x, hxQ, hx0, hx⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨x, hxQ⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh ν x hx)
    · exact fun h0 => hx0 (congrArg Subtype.val h0)
  obtain ⟨ν₀, x₀, hx₀Q, hx₀, hx₀w⟩ := exists_weight hE hU hQ hQ0
  have hSne : S.Nonempty := ⟨_, ν₀, rfl, x₀, hx₀Q, hx₀, hx₀w⟩
  obtain ⟨t, ⟨ν, rfl, x, hxQ, hx0, hx⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨ν, x, hxQ, hx0, hx, fun a b hab he => ?_⟩
  by_contra hne
  have hmem : ht (ν + root a b) ∈ S :=
    ⟨_, rfl, E a b x, hQ a b he x hxQ, hne, GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply hE hx a b⟩
  have h1 : ht (ν + root a b) = ht ν + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [GlobalTheory.CompanionTheory.DSHighestOfKType.height_root]
  have h2 := hmin _ hmem
  have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [id] at h2
  linarith

theorem le_of_highest (hE : GlRel E) (hU : KUnit ε E) {T M : Submodule ℂ V} [FiniteDimensional ℂ T]
    (hT : KStab ε E T) (hM : KStab ε E M)
    (h : ∀ Q : Submodule ℂ V, Q ≤ T → FiniteDimensional ℂ Q → KStab ε E Q →
      ∀ (μ : Fin n → ℝ), ∀ x ∈ Q, x ≠ 0 → KHighest ε E μ x → x ∈ M) : T ≤ M := by
  have hPfin : FiniteDimensional ℂ (T ⊓ M : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hP : KStab ε E (T ⊓ M) := fun a b he x hx => ⟨hT a b he x hx.1, hM a b he x hx.2⟩
  have hPo := GlobalTheory.CompanionTheory.KLowSpan.kstab_orthogonal hU hP
  have hQfin : FiniteDimensional ℂ (T ⊓ (T ⊓ M)ᗮ : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hQ : KStab ε E (T ⊓ (T ⊓ M)ᗮ) := fun a b he x hx => ⟨hT a b he x hx.1, hPo a b he x hx.2⟩
  have hbot : (T ⊓ (T ⊓ M)ᗮ : Submodule ℂ V) = ⊥ := by
    by_contra hne
    obtain ⟨μ, x, hxQ, hx0, hx⟩ := exists_highest hE hU hQ hne
    have hxM := h _ inf_le_left hQfin hQ μ x hxQ hx0 hx
    exact hx0 (inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hxQ.2 x ⟨hxQ.1, hxM⟩))
  intro t ht
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal (K := T ⊓ M) t
  have hzT : z ∈ T := by
    have : z = t - y := by rw [hyz]; abel
    rw [this]
    exact T.sub_mem ht hy.1
  have hz0 : z = 0 := by
    have : z ∈ (T ⊓ (T ⊓ M)ᗮ : Submodule ℂ V) := ⟨hzT, hz⟩
    rw [hbot] at this
    simpa using this
  rw [hyz, hz0, add_zero]
  exact hy.2

end Alg

section Rep

open CompanionTheory.D.DSIC (IsSmMod hStabLink hWtLink hLowSpan hHWofType hSmMod)
open PI.UpqRep (IsKTypeOf IsKStableOn IsURepOn UJset)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Sm : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ Sm}

theorem kType_of_highest (hσ : IsURepOn (UJset ε) σ) (hM : IsSmMod ε σ Sm E) {μ : Fin n → ℝ}
    {x : Sm} (hx0 : x ≠ 0) (hhw : KHighest ε E μ x) {Q : Submodule ℂ Sm}
    (hQf : FiniteDimensional ℂ Q) (hQ : KStab ε E Q) (hxQ : x ∈ Q) :
    ∃ L : Submodule ℂ Sm, x ∈ L ∧ IsKTypeOf ε σ μ (L.map Sm.subtype) := by
  have hinj : Function.Injective Sm.subtype := Sm.injective_subtype
  have hrel : KRel ε E := fun a b c d _ _ => hM.gl a b c d
  have hun : KUnit ε E := kUnit_of hM.unit
  obtain ⟨L, hLU, hxL, hLst, hirr, hdom, -⟩ := hLowSpan n ε Sm E μ x Q hrel hun hx0 hhw hQf hQ hxQ
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLU
  refine ⟨L, hxL, inferInstance, (hStabLink n ε H σ Sm E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩
  · intro S' hle hS'
    have hle' : S'.comap Sm.subtype ≤ L := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [← hinj hzy]
    have hmap : (S'.comap Sm.subtype).map Sm.subtype = S' := by
      apply Submodule.map_comap_eq_of_le
      exact hle.trans LinearMap.map_le_range
    have hst' : KStab ε E (S'.comap Sm.subtype) := by
      refine (hStabLink n ε H σ Sm E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_
      rwa [hmap]
    rcases hirr _ hle' hst' with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h]
  · exact ⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h),
      (hWtLink n ε H σ Sm E hσ hM μ x).1 hhw.1⟩
  · rintro ν _ ⟨v, hv, rfl⟩ hv0 hwt
    exact hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hWtLink n ε H σ Sm E hσ hM ν v).2 hwt)

theorem comap_kStab (hσ : IsURepOn (UJset ε) σ) (hM : IsSmMod ε σ Sm E) {S' : Submodule ℂ H}
    (hf : FiniteDimensional ℂ S') (hst : IsKStableOn ε σ S') (hle : S' ≤ Sm) :
    KStab ε E (S'.comap Sm.subtype) := by
  have hfinU : FiniteDimensional ℂ (S'.comap Sm.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hle).symm.finiteDimensional
  refine (hStabLink n ε H σ Sm E hσ hM _ hfinU).2 ?_
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hle]
  exact hst

end Rep

open CompanionTheory.D.DSIC (hHWofType hStabLink hSmMod) in
open PI.UpqRep (IsKTypeOf) in

theorem kTypeShift : Formalism.L2.S.S7.CasimirNormBounds.KTypeShift := by
  intro n ε lam H _ _ σ _ hds μ S hS a ha X hX
  obtain ⟨hc, -, hσ, hirr, -⟩ := hds
  haveI := hc
  obtain ⟨Sm, E, hM⟩ := hSmMod n ε H σ hσ
  have hgl := hM.gl
  have hun := kUnit_of hM.unit
  have hsm : ∀ (ν : Fin n → ℝ) (S' : Submodule ℂ H), IsKTypeOf ε σ ν S' → S' ≤ Sm :=
    fun ν S' h v hv =>
      (hM.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n ε H σ hσ hirr v ⟨S', h.1, hv, h.2.1⟩)
  have hSle := hsm μ S hS
  obtain ⟨v, hv0, hvS, hvh⟩ := hHWofType n ε H σ Sm E hσ hM μ S hS hSle
  have hAst : KStab ε E (kLowSpan ε E v) :=
    GlobalTheory.CompanionTheory.KLowSpan.kstab_kLowSpan (fun a b c d _ _ => hgl a b c d) hvh
  have hUst := comap_kStab hσ hM hS.1 hS.2.1 hSle
  have hAU : kLowSpan ε E v ≤ S.comap Sm.subtype := GlobalTheory.CompanionTheory.KLowSpan.kLowSpan_le hUst hvS
  have hUfin : FiniteDimensional ℂ (S.comap Sm.subtype) :=
    haveI := hS.1
    (Submodule.comapSubtypeEquivOfLe hSle).symm.finiteDimensional
  haveI hAfin : FiniteDimensional ℂ (kLowSpan ε E v) := Submodule.finiteDimensional_of_le hAU
  have hAmap : (kLowSpan ε E v).map Sm.subtype = S := by
    have hle : (kLowSpan ε E v).map Sm.subtype ≤ S := Submodule.map_le_iff_le_comap.2 hAU
    rcases hS.2.2.1 _ hle ((hStabLink n ε H σ Sm E hσ hM _ hAfin).1 hAst) with h | h
    · exfalso
      have hmem : (v : H) ∈ (kLowSpan ε E v).map Sm.subtype :=
        ⟨v, GlobalTheory.CompanionTheory.KLowSpan.kself_mem, rfl⟩
      rw [h] at hmem
      exact hv0 (Subtype.ext (by simpa using hmem))
    · exact h
  let M : Submodule ℂ Sm := sSup {L | ∃ (S' : Submodule ℂ H) (μ' : Fin n → ℝ),
    IsKTypeOf ε σ μ' S' ∧ Formalism.REAL.nsq (μ' - μ) ≤ 2 ∧ L = S'.comap Sm.subtype}
  have hMst : KStab ε E M := by
    intro c d he y hy
    have hle : M ≤ M.comap (E c d) := by
      refine sSup_le ?_
      rintro _ ⟨S', μ', h1, h2, rfl⟩ z hz
      exact (le_sSup ⟨S', μ', h1, h2, rfl⟩ : S'.comap Sm.subtype ≤ M)
        (comap_kStab hσ hM h1.1 h1.2.1 (hsm _ _ h1) c d he z hz)
    exact hle hy
  haveI : FiniteDimensional ℂ (nbr E (kLowSpan ε E v)) := nbr_finite _
  have hTM : nbr E (kLowSpan ε E v) ≤ M := by
    refine le_of_highest hgl hun (nbr_stab hgl hAst) hMst ?_
    intro Q hQT hQf hQ ν x hxQ hx0 hx
    obtain ⟨L, hxL, hL⟩ := kType_of_highest hσ hM hx0 hx hQf hQ hxQ
    have hnsq : Formalism.REAL.nsq (ν - μ) ≤ 2 := by
      rcases weight_shift hgl hun hvh.1 hx hx0 (hQT hxQ) with rfl | ⟨a, b, rfl⟩
      · simp [Formalism.REAL.nsq, Formalism.REAL.dot]
      · simpa using nsq_root_le a b
    exact (le_sSup ⟨_, ν, hL, hnsq, rfl⟩ : (L.map Sm.subtype).comap Sm.subtype ≤ M) ⟨x, hxL, rfl⟩
  have haA : (⟨a, hSle ha⟩ : Sm) ∈ kLowSpan ε E v := by
    have hmem : a ∈ (kLowSpan ε E v).map Sm.subtype := by rw [hAmap]; exact ha
    obtain ⟨y, hy, rfl⟩ := hmem
    exact hy
  refine ⟨_, hM.real X hX ⟨a, hSle ha⟩, ?_⟩
  have hMH : M.map Sm.subtype ≤ sSup {S' : Submodule ℂ H | ∃ μ', Formalism.MainNotions.S.IsKTypeOf ε σ μ' S' ∧
      Formalism.REAL.nsq (μ' - μ) ≤ 2} := by
    refine Submodule.map_le_iff_le_comap.2 (sSup_le ?_)
    rintro _ ⟨S', μ', h1, h2, rfl⟩ z hz
    have hmemS : S' ∈ {S' : Submodule ℂ H | ∃ μ', Formalism.MainNotions.S.IsKTypeOf ε σ μ' S' ∧
        Formalism.REAL.nsq (μ' - μ) ≤ 2} := ⟨μ', h1, h2⟩
    exact le_sSup hmemS hz
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (hMH ⟨_, hTM (apply_mem_nbr haA i j), rfl⟩)

end UpperTheory.Lit.Bur.KShift
end
end

section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.HWSpanType

theorem exists_hcType_of_irred : ∀ {k : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp] {ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)} (hρ : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ) (hirr : ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤), ∃ (u : Fin k → ℝ) (Wq : Type) (_ : NormedAddCommGroup Wq) (_ : InnerProductSpace ℂ Wq) (ρ' : Matrix (Fin k) (Fin k) ℂ → (Wq →L[ℂ] Wq)) (T : Wp ≃ₗ[ℂ] Wq), PI.UpqRep.IsHCTypeU k u ρ' ∧ ∀ h ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ w, T (ρ h w) = ρ' h (T w) := by
  intro k Wp _ _ _ _ ρ hρ hirr
  obtain ⟨E, hgl, hun, hE⟩ := Derived.exists_derived_action k Wp ρ hρ
  have hQ : CompanionTheory.D.DSIC.KStab (PI.UpqRep.allPos k) E (⊤ : Submodule ℂ Wp) := fun _ _ _ _ _ => trivial
  obtain ⟨μ, x, -, hx0, hx⟩ := UpperTheory.Lit.Bur.KShift.exists_highest hgl (UpperTheory.Lit.Bur.KShift.kUnit_of hun) hQ top_ne_bot
  have hlow : PI.UpqRep.lowK (PI.UpqRep.allPos k) (μ + GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.rhoU k) = μ := by
    rw [GlobalTheory.KTypeCompare.lowK_allPos]
    simp
  have hΛ : Formalism.REAL.KHighest (PI.UpqRep.allPos k) E
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) (μ + GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.rhoU k)) x := by
    rw [hlow]; exact hx
  have htype := exists_type_of_highest hρ E hgl hun hE _ x hx0 hΛ
  set S := Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x with hS
  have hst := Wt.stable_of_derived hρ E hE S (Formalism.REAL.isCompactInvariant_compactSpan x)
  have hxS : x ∈ S := Formalism.REAL.mem_compactSpan x
  have htop : S = ⊤ := (hirr S hst).resolve_left fun h => hx0 (by
    rw [h] at hxS; exact (Submodule.mem_bot ℂ).1 hxS)
  refine ⟨_, S, inferInstance, inferInstance, compress ρ S, (LinearEquiv.ofTop S htop).symm, htype, ?_⟩
  intro h hh w
  apply Subtype.ext
  rw [coe_compress (hst h hh _ (Subtype.property _))]
  simp [LinearEquiv.ofTop_symm_apply]

end UpperTheory.Lit.Bur.HWSpanType

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.irreducible_unitary_rep_iso_harishChandraType : ∀ {k : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp] {ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)} (hρ : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ) (hirr : ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤), ∃ (u : Fin k → ℝ) (Wq : Type) (_ : NormedAddCommGroup Wq) (_ : InnerProductSpace ℂ Wq) (ρ' : Matrix (Fin k) (Fin k) ℂ → (Wq →L[ℂ] Wq)) (T : Wp ≃ₗ[ℂ] Wq), PI.UpqRep.IsHCTypeU k u ρ' ∧ ∀ h ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ w, T (ρ h w) = ρ' h (T w) := by
  first | exact @UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred | exact UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred | (intros; apply UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred <;> assumption)
end
end
