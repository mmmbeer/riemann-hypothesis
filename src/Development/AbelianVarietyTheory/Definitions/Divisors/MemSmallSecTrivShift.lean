import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.InhHasFDerivAtNormSq
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.AnReadModel

open GlobalTheory.CxPts GlobalTheory.AnRead

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem volume_ball_one : volume (Metric.ball (0 : V 1) 1) = ENNReal.ofReal Real.pi := by
  have h : Module.finrank ℝ (V 1) = 2 * 1 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (V 1)]; simp
  rw [InnerProductSpace.volume_ball_of_dim_even h]
  simp

theorem topInt_pos [SmoothOfRelativeDimension D p] [SecondCountableTopology (CxPts p σ)] {B : LB Y}
    (K : CanonLB p D) {φ : Weight p σ B} {f : (tens K.bundle B).ι → CxPts p σ → ℂ}
    {R : AnRead p σ D} (hφ : φ.IsSmooth R) (hf : f ∈ R.holSec (tens K.bundle B))
    {j : (tens K.bundle B).ι} {y : CxPts p σ} (h0 : f j y ≠ 0) : 0 < R.topInt K φ f := by
  have hj : y ∈ ptsIn p σ ((tens K.bundle B).U j) := by
    by_contra h; exact h0 (hf.1.2 j y h)
  obtain ⟨a, b⟩ := j
  obtain ⟨ha, hb⟩ := mem_ptsIn_inf.1 hj
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  let S := ptsIn p σ (c.U ⊓ K.bundle.U a) ∩ ptsIn p σ (B.U b)
  have hS : IsOpen S := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have hc : ContinuousOn (fun v => c.topDens K φ f (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' S) := by
    have h₁ := (holoOn_ev_of_subset (R := R) (c.isFrame.ratio (K.isFrame a)).val
      (inter_subset_left (t := ptsIn p σ (B.U b)))).mul
      ((hf.2 (a, b)).mono
        fun _ hz => mem_ptsIn_inf.2 ⟨(mem_ptsIn_inf.1 hz.1).2, hz.2⟩) i
    have h₂ := (hφ b).mono (inter_subset_right : S ⊆ _) i
    exact (continuousOn_const.mul ((h₁.continuousOn.norm.pow 2).mul h₂.continuousOn.neg.rexp)).congr
      fun v hv => c.topDens_eq K φ hf.1 (c.e.map_target hv.1) (mem_ptsIn_inf.1 hv.2.1).2 hv.2.2
  have hyS : y ∈ S := ⟨mem_ptsIn_inf.2 ⟨c.source_subset hi, ha⟩, hb⟩
  have hpos : 0 < c.topDens K φ f (c.e.symm (c.e y)) := by
    rw [c.e.left_inv hi, c.topDens_eq K φ hf.1 hi ha hb]
    have : c.topCoeff K f a b y ≠ 0 :=
      mul_ne_zero (rv_ne_zero _ _ (c.source_subset hi) ha) h0
    positivity
  have ho := isOpen_over c.e hS
  have hO := hc.isOpen_inter_preimage ho (isOpen_Ioi (a := c.topDens K φ f (c.e.symm (c.e y)) / 2))
  have hA : IsOpen (c.e.source ∩ S) := c.e.open_source.inter hS
  refine lt_of_lt_of_le ?_ (measure_mono (subset_univ (c.e.source ∩ S)))
  rw [R.topMeasure_apply K φ f c hA.measurableSet inter_subset_left, c.e.image_source_inter_eq']
  refine lt_of_lt_of_le ?_ (lintegral_mono_set inter_subset_left (s := (c.e.target ∩ c.e.symm ⁻¹' S) ∩
    (fun v => c.topDens K φ f (c.e.symm v)) ⁻¹' Ioi (c.topDens K φ f (c.e.symm (c.e y)) / 2)))
  refine lt_of_lt_of_le ?_ (setLIntegral_mono' hO.measurableSet
    (f := fun _ => ENNReal.ofReal (c.topDens K φ f (c.e.symm (c.e y)) / 2))
    fun v hv => ENNReal.ofReal_le_ofReal (le_of_lt hv.2))
  rw [setLIntegral_const]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hpos)).ne'
    (hO.measure_pos _ ⟨c.e y, mem_over c.e hi hyS, half_lt_self hpos⟩).ne'

open ProjSpace in

theorem topInt_jac (N : ℕ) (K : CanonLB (PSpace.str k N) N) (R : AnRead (PSpace.str k N) σ N) :
    0 < R.topInt K ((ProjAn.fsO1 k σ N).pow (N + 1)) (secVal _ σ (K.jacSec (coord k N))) ∧
      R.topInt K ((ProjAn.fsO1 k σ N).pow (N + 1)) (secVal _ σ (K.jacSec (coord k N))) < ⊤ := by
  have hs := (Weight.isSmooth_fsBasis (R := R) (O1_isLB k N) (coord k N)
    (iSup_nonzeroLocus_coord k N) 1 (by simp)).zpow ((N + 1 : ℕ) : ℤ)
  refine ⟨?_, topInt_lt_top K hs (R.secVal_mem_holSec _)⟩
  let y : CxPts (PSpace.str k N) σ := projPt σ ⟨fun _ => 1, (Ideal.eq_top_iff_one _).2
    (Ideal.subset_span ⟨0, rfl⟩)⟩
  obtain ⟨_, h⟩ := ProjAn.noCommonZero_jac k σ N K _ y (mem_pick (K.isLB_adj (O1_isLB k N) _) y)
  exact topInt_pos K hs (R.secVal_mem_holSec _) h

def X (a : Fin D) : CxPts (CanonLB.affStr k D) σ → ℂ :=
  ev _ σ ⊤ (CanonLB.polyFn (MvPolynomial.X a))

def origin : CxPts (CanonLB.affStr k D) σ :=
  ofHom (isAffineOpen_top _) ((MvPolynomial.eval₂Hom σ fun _ => 0).comp
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).hom.hom) fun a => by
    have := RingHom.congr_fun (CanonLB.polyFn_comp k D) a
    rw [← this]
    simp [CanonLB.polyFn]

theorem exists_std (y : CxPts (CanonLB.affStr k D) σ) :
    ∃ c : AlgChart (CanonLB.affStr k D) σ D, y ∈ c.e.source ∧
      ∀ z ∈ c.e.source, ∀ a, c.e z a = X a z := by
  have he : MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
      (fun a => CanonLB.polyFn (MvPolynomial.X a)) = CanonLB.polyFn :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans
      (RingHom.congr_fun (CanonLB.polyFn_comp k D) a).symm) fun a => MvPolynomial.eval₂Hom_X' _ _ a
  have het : (MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
      (fun a => CanonLB.polyFn (MvPolynomial.X a))).Etale := by
    rw [he]
    exact RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv)
  obtain ⟨⟨e, U, hU, x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale
    (isAffineOpen_top _) _ het (mem_ptsIn_top (y := y))
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, h₂⟩

def sq (t : ℝ) (z : CxPts (CanonLB.affStr k D) σ) : ℝ := t * ∑ a, Complex.normSq (X a z)

end GlobalTheory.AnReadModel
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V cHess leviV wd wdb bas)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open scoped ContDiff ENNReal

namespace GlobalTheory.ArithHeightModel

variable {k : Type} [CommRing k] {σ : k →+* ℂ} {D : ℕ}

def pt (σ : k →+* ℂ) (v : V D) : CxPts (CanonLB.affStr k D) σ :=
  ofHom (isAffineOpen_top _) ((MvPolynomial.eval₂Hom σ fun a => v a).comp
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).hom.hom) fun a => by
    have := RingHom.congr_fun (CanonLB.polyFn_comp k D) a
    rw [← this]
    simp [CanonLB.polyFn]

theorem ev_pt (v : V D) (P : MvPolynomial (Fin D) k) :
    ev _ σ ⊤ (CanonLB.polyFn P) (pt σ v) = MvPolynomial.eval₂Hom σ (fun a => v a) P := by
  rw [pt, ev_ofHom]
  simp [CanonLB.polyFn]

theorem polyFn_surj : Function.Surjective (CanonLB.polyFn : MvPolynomial (Fin D) k → _) :=
  (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv).2

theorem diff_pt (a : Γ(Sp (MvPolynomial (Fin D) k), ⊤)) :
    DifferentiableOn ℂ (ev (CanonLB.affStr k D) σ ⊤ a ∘ pt σ) univ := by
  obtain ⟨P, rfl⟩ := polyFn_surj a
  refine Differentiable.differentiableOn ?_
  have : ev (CanonLB.affStr k D) σ ⊤ (CanonLB.polyFn P) ∘ pt σ =
    fun v : V D => MvPolynomial.eval₂Hom σ (fun a => v a) P := funext fun v => ev_pt v P
  rw [this]
  clear this
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    simp only [map_mul, MvPolynomial.eval₂Hom_X']
    exact hp.mul (EuclideanSpace.proj (𝕜 := ℂ) n : V D →L[ℂ] ℂ).differentiable

def std (σ : k →+* ℂ) (D : ℕ) : AlgChart (CanonLB.affStr k D) σ D where
  e :=
    { toFun := fun z => WithLp.toLp 2 fun a => AnReadModel.X a z
      invFun := pt σ
      source := univ
      target := univ
      map_source' := fun _ _ => trivial
      map_target' := fun _ _ => trivial
      left_inv' := fun z _ => Subtype.ext (ext_of_valR (isAffineOpen_top _) le_top le_top fun a => by
        obtain ⟨P, rfl⟩ := polyFn_surj a
        refine (ev_pt _ P).trans (Eq.trans ?_ (ev_eq (mem_ptsIn_top (y := z)) _).symm)
        refine RingHom.congr_fun (g := (evHom (mem_ptsIn_top (y := z))).comp CanonLB.polyFn)
          (MvPolynomial.ringHom_ext (fun c => ?_) fun c => ?_) P
        · rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, ← ev_eq]
          exact ((congrArg (ev _ σ ⊤ · z) (RingHom.congr_fun (CanonLB.polyFn_comp k D) c)).trans
            (ev_algX mem_ptsIn_top c)).symm
        · rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, ← ev_eq]
          rfl)
      right_inv' := fun v _ => by
        ext a
        exact (ev_pt v _).trans (MvPolynomial.eval₂Hom_X' _ _ a)
      open_source := isOpen_univ
      open_target := isOpen_univ
      continuousOn_toFun := (PiLp.continuous_toLp 2 _).comp_continuousOn
        ((continuousOn_pi.2 fun a => continuousOn_ev _).mono fun _ _ => mem_ptsIn_top)
      continuousOn_invFun := (holo_of_affine (isAffineOpen_top _) isOpen_univ
        (fun _ _ => mem_ptsIn_top) diff_pt).1 }
  U := ⊤
  affine := isAffineOpen_top _
  x a := CanonLB.polyFn (MvPolynomial.X a)
  etale := by
    have he : MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
        (fun a => CanonLB.polyFn (MvPolynomial.X a)) = CanonLB.polyFn :=
      MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans
        (RingHom.congr_fun (CanonLB.polyFn_comp k D) a).symm) fun a => MvPolynomial.eval₂Hom_X' _ _ a
    rw [he]
    exact RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv)
  source_subset _ _ := mem_ptsIn_top
  apply_eq _ _ _ := rfl
  holo := (holo_of_affine (isAffineOpen_top _) isOpen_univ (fun _ _ => mem_ptsIn_top) diff_pt).2

def u (v : V 1) : ℝ := 1 + ((v 0).re ^ 2 + (v 0).im ^ 2)

theorem u_pos (v : V 1) : 0 < u v := by unfold u; positivity

def crd : V 1 →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : V 1 →L[ℂ] ℂ).restrictScalars ℝ

theorem hasFDerivAt_u (v : V 1) : HasFDerivAt u
    ((2 * (v 0).re) • Complex.reCLM.comp crd + (2 * (v 0).im) • Complex.imCLM.comp crd) v := by
  have h₁ := (Complex.reCLM.comp crd).hasFDerivAt (x := v)
  have h₂ := (Complex.imCLM.comp crd).hasFDerivAt (x := v)
  refine HasFDerivAt.congr_fderiv (((h₁.pow 2).add (h₂.pow 2)).const_add 1) ?_
  ext w
  simp [crd]

theorem wdb_log : wdb 1 0 (fun v => (Real.log (u v) : ℂ)) = fun v => v 0 * ((u v)⁻¹ : ℝ) := by
  funext v
  have h := Complex.ofRealCLM.hasFDerivAt.comp v ((hasFDerivAt_u v).log (u_pos v).ne')
  have h' : HasFDerivAt (fun v => (Real.log (u v) : ℂ)) _ v := h
  rw [wdb, h'.fderiv]
  have h2 := Complex.re_add_im (v 0)
  simp [crd, bas]
  linear_combination (u v : ℂ)⁻¹ * h2

theorem cHess_log (v : V 1) : cHess 1 (fun v => (Real.log (u v) : ℂ)) v 0 0 = ((u v ^ 2)⁻¹ : ℝ) := by
  have h := crd.hasFDerivAt.mul (Complex.ofRealCLM.hasFDerivAt.comp v
    ((hasDerivAt_inv (u_pos v).ne').comp_hasFDerivAt v (hasFDerivAt_u v)))
  have h' : HasFDerivAt (fun v : V 1 => v 0 * (((u v)⁻¹ : ℝ) : ℂ)) _ v := h
  rw [cHess, Matrix.of_apply, wdb_log, wd, h'.fderiv]
  have h0 : (u v : ℂ) ≠ 0 := by exact_mod_cast (u_pos v).ne'
  have h1 : (u v : ℂ) = 1 + ((v 0).re ^ 2 + (v 0).im ^ 2) := by simp [u]
  have h2 := Complex.re_add_im (v 0)
  simp [crd, bas]
  field_simp
  linear_combination (exp := 1) 2 * h1 + (2 * (v 0).re - 2 * Complex.I * (v 0).im) * h2 + (2 * (v 0).im ^ 2 - u v) * Complex.I_mul_I

theorem integral_dens : ∫ v : V 1, 1 / Real.pi * (u v ^ 2)⁻¹ = 1 := by
  have hd : Module.finrank ℝ (V 1) = 2 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (V 1)]; simp
  have hu (v : V 1) : u v = 1 + ‖v‖ ^ 2 := by
    rw [u, EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Complex.sq_norm, Complex.normSq_apply]
    ring
  have : Nontrivial (V 1) := inferInstance
  have h := integral_fun_norm_addHaar (volume : Measure (V 1))
    (fun r => 1 / Real.pi * ((1 + r ^ 2) ^ 2)⁻¹)
  have hr : ∫ r in Ioi (0 : ℝ), r * ((1 + r ^ 2) ^ 2)⁻¹ = 0 - -(2 * (1 + (0 : ℝ) ^ 2))⁻¹ := by
    refine integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun r => -(2 * (1 + r ^ 2))⁻¹)
      (fun r _ => ?_) (fun r hr => mul_nonneg (le_of_lt hr) (by positivity)) ?_
    · have : (2 * (1 + r ^ 2)) ≠ 0 := by positivity
      refine HasDerivAt.congr_deriv
        ((((hasDerivAt_pow 2 r).const_add 1).const_mul 2).inv this).neg ?_
      field_simp
      simp
    · rw [← neg_zero]
      exact (tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop two_pos
        (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)))).neg
  simp only [hu]
  rw [h, hd, Measure.real, AnReadModel.volume_ball_one, ENNReal.toReal_ofReal Real.pi_pos.le]
  simp only [smul_eq_mul, Nat.reduceSub, pow_one, mul_left_comm _ (1 / Real.pi), integral_const_mul, hr]
  have := Real.pi_pos
  field_simp
  norm_num

def fsLine (σ : k →+* ℂ) : Weight (CanonLB.affStr k 1) σ (LB.triv _) :=
  Weight.ofFun fun z => Real.log (u ((std σ 1).e z))






def trivShift (k : Type) [CommRing k] (t : ℝ) : HermLB (𝟙 (Sp k)) :=
  (HermLB.triv _).shift (fun _ => t) fun _ => rfl




end GlobalTheory.ArithHeightModel
end
end
