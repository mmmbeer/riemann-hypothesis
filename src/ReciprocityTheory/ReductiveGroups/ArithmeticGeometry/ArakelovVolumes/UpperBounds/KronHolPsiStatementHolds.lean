import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigCellPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI

noncomputable section

attribute [local instance] Classical.propDecidable

theorem cont_inv {α : Type*} [TopologicalSpace α] {n : ℕ} {f : α → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hd : ∀ a, (f a).det ≠ 0) : Continuous fun a => (f a)⁻¹ := by
  have h : (fun a => (f a)⁻¹) = fun a => (f a).det⁻¹ • (f a).adjugate := by
    funext a
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hf.matrix_det.inv₀ hd).smul hf.matrix_adjugate

theorem cont_uMat {α : Type*} [TopologicalSpace α] {n : ℕ} {g : α → Matrix (Fin n) (Fin n) ℂ}
    (hg : Continuous g) (hd : ∀ a c, (blk (g a) c).det ≠ 0) : Continuous fun a => uMat (g a) := by
  refine continuous_pi fun j => continuous_pi fun c => ?_
  simp only [uMat, Matrix.of_apply]
  split_ifs with h1 h2
  · exact continuous_const
  · have hb : Continuous fun a => blk (g a) c := by
      unfold blk
      exact hg.matrix_submatrix _ _
    have hi := cont_inv hb (fun a => hd a c)
    have hr : Continuous fun a => rowc (g a) c := by
      unfold rowc
      exact continuous_pi fun m => (continuous_apply _).comp ((continuous_apply c).comp hg)
    exact ((continuous_apply (⟨j, h2⟩ : Fin c)).comp (hr.matrix_vecMul hi)).neg
  · exact continuous_const

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cont_mat (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => mat y τ := by
  exact continuous_pi fun a => continuous_pi fun b => continuous_coord X τ a b

private theorem continuous_gram_comp {α : Type*} [TopologicalSpace α] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {f : α → Matrix (Fin r) (Fin r) ℂ} (hf : Continuous f) :
    Continuous fun a => ReciprocityTheory.ChartRestriction.G.FD.gram τ G (f a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact (((continuous_apply i).comp ((continuous_apply a).comp hf)).mul continuous_const).mul
    (Complex.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply b).comp hf)))

theorem cont_gram (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => gram τ.1 X.Gm (mat y τ) := by
  exact continuous_gram_comp τ.1 X.Gm (cont_mat X τ)

theorem cont_uOf (τ : X.Ψ) : Continuous fun y : X.dom => uOf X y.1 τ := by
  have hg : Continuous fun y : X.dom => gram τ.1 X.Gm (mat y.1 τ) := (cont_gram X τ).comp continuous_subtype_val
  exact cont_uMat hg fun y c => blk_det X y.2 τ c

theorem cont_dOf (τ : X.Ψ) (k : Fin r) : Continuous fun y : X.dom => dOf X y.1 τ k := by
  have hm : Continuous fun y : X.dom => mat y.1 τ * uOf X y.1 τ :=
    ((cont_mat X τ).comp continuous_subtype_val).matrix_mul (cont_uOf X τ)
  exact (continuous_apply k).comp ((continuous_apply k).comp (continuous_gram_comp τ.1 X.Gm hm))

theorem cont_sOf (τ : X.Ψ) (k : Fin r) : Continuous fun y : X.dom => sOf X y.1 τ k := by
  have hd := cont_dOf X τ k
  have hr : Continuous fun y : X.dom => Real.sqrt |(dOf X y.1 τ k).re| :=
    (Complex.continuous_re.comp hd).abs.sqrt
  have hne : ∀ y : X.dom, Real.sqrt |(dOf X y.1 τ k).re| ≠ 0 := fun y =>
    (Real.sqrt_pos.mpr (abs_re_pos X y.2 τ k)).ne'
  exact Complex.continuous_ofReal.comp (hr.inv₀ hne)

theorem cont_bOf (τ : X.Ψ) : Continuous fun y : X.dom => mat (bOf X y.1) τ := by
  exact (cont_uOf X τ).matrix_mul (Continuous.matrix_diagonal (continuous_pi fun k => cont_sOf X τ k))

theorem cont_β0 (τ : X.Ψ) : Continuous fun y : X.dom => β0 X y.1 τ := by
  exact cont_inv (cont_bOf X τ) (fun y => bOf_det X y.2 τ)

theorem β0_bound {C : Set (Frame X.Ψ r)} (hC : IsCompact C) (hCd : C ⊆ X.dom) :
    ∃ R0 : ℝ, ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0 := by
  have hcont : ∀ (τ : X.Ψ) (a b : Fin r), ContinuousOn (fun x => ‖β0 X x τ a b‖) C := by
    intro τ a b
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun y : X.dom => ‖β0 X y.1 τ a b‖ :=
      ((continuous_apply b).comp ((continuous_apply a).comp (cont_β0 X τ))).norm
    show Continuous fun x : C => ‖β0 X x.1 τ a b‖
    refine (h1.comp (continuous_inclusion hCd)).congr fun x => ?_
    simp only [Function.comp_apply, Set.coe_inclusion]
  choose R hR using fun (τ : X.Ψ) (a b : Fin r) => hC.bddAbove_image (hcont τ a b)
  refine ⟨∑ τ, ∑ a, ∑ b, max (R τ a b) 0, fun x hx τ a b => ?_⟩
  have h1 : ‖β0 X x τ a b‖ ≤ R τ a b := hR τ a b ⟨x, hx, rfl⟩
  calc ‖β0 X x τ a b‖ ≤ max (R τ a b) 0 := h1.trans (le_max_left _ _)
    _ ≤ ∑ b', max (R τ a b') 0 :=
        Finset.single_le_sum (f := fun b' => max (R τ a b') 0) (fun _ _ => le_max_right _ _)
          (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', max (R τ a' b') 0 :=
        Finset.single_le_sum (f := fun a' => ∑ b', max (R τ a' b') 0)
          (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ a)
    _ ≤ ∑ τ', ∑ a', ∑ b', max (R τ' a' b') 0 :=
        Finset.single_le_sum (f := fun τ' => ∑ a', ∑ b', max (R τ' a' b') 0)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _)
          (Finset.mem_univ τ)

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem Umat_upper (y : UpI X.Ψ r → ℂ) (τ : X.Ψ) : (Umat y τ).BlockTriangular id := by
  intro a b hab
  have h : b < a := hab
  simp [Umat, h]

theorem Lβ_bound {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {R0 : ℝ}
    (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0) {p : Frame X.Ψ r} (hp : p ∈ X.dom)
    {y : UpI X.Ψ r → ℂ} (hy : ∀ τ b, y (dI τ b) ≠ 0) (hx : rmul p (UF X y) ∈ C) (i : UpI X.Ψ r) :
    ‖Lβ (β0 X p) y i‖ ≤ R0 := by
  set x := rmul p (UF X y) with hxdef
  set τ := i.1.1
  have hxd : x ∈ X.dom := hCd hx
  have h1 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X p τ * mat (UF X y) τ) := gram_rmul_eq X hp τ
  let one : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hone' : rmul x one = x := by
    funext τ'
    show (mat x τ' * (1 : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = x τ'
    rw [Matrix.mul_one]; rfl
  have h2 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X x τ * mat one τ) := by
    have := gram_rmul_eq X hxd τ (b := one)
    rwa [hone'] at this
  have hone : mat one τ = 1 := rfl
  rw [hone, Matrix.mul_one] at h2
  have hU : mat (UF X y) τ = Umat y τ := rfl
  rw [hU] at h1
  have hUd : (Umat y τ).det ≠ 0 := ((UF_mem X hy) τ).1
  obtain ⟨D, hD, heq⟩ := gram_upper_unique (ε := fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (fun a => sgn_mul_self X.p0 a) (β0_upper X hxd τ) ((β0_upper X hp τ).mul (Umat_upper X y τ))
    (β0_det X hxd τ) (by rw [Matrix.det_mul]; exact mul_ne_zero (β0_det X hp τ) hUd)
    (by have := h1.symm.trans h2; simpa only [gramT, Jd] using this)
  have hval : Lβ (β0 X p) y i = (β0 X p τ * Umat y τ) i.1.2.1 i.1.2.2 := rfl
  rw [hval, heq, Matrix.diagonal_mul, norm_mul, hD, one_mul]
  exact hR0 x hx τ _ _

def SR (R0 : ℝ) : Set (UpI X.Ψ r → ℂ) := {c | ∀ i, ‖c i‖ ≤ R0}

def KR (R0 : ℝ) : ℝ≥0∞ := ∫⁻ y in SR X R0, ENNReal.ofReal (Complex.normSq (jacU y))

theorem measurableSet_SR (R0 : ℝ) : MeasurableSet (SR X R0) := by
  have h : SR X R0 = ⋂ i, {c : UpI X.Ψ r → ℂ | ‖c i‖ ≤ R0} := by
    ext c
    simp [SR]
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).norm measurable_const

theorem KR_lt_top {R0 : ℝ} (hR0 : 0 ≤ R0) : KR X R0 < ⊤ := by
  have hc : IsCompact (SR X R0) := by
    have h : SR X R0 = Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) R0) := by
      ext c
      simp [SR, Set.mem_pi]
    rw [h]
    exact isCompact_univ_pi fun _ => isCompact_closedBall 0 R0
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    ((Complex.continuous_normSq.comp continuous_jacU).continuousOn)
  calc KR X R0 ≤ ∫⁻ _ in SR X R0, ENNReal.ofReal C := by
        unfold KR
        refine setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal ?_
        have := hC y hy
        rw [Real.norm_eq_abs] at this
        exact le_trans (le_abs_self _) this
    _ = ENNReal.ofReal C * volume (SR X R0) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc.measure_lt_top

theorem upper_gen (β : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) (R0 : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) =
      ENNReal.ofReal ((Complex.normSq (LinearMap.det (Lβ β)) * Complex.normSq (jacβ β))⁻¹) * KR X R0 := by
  have hdet : LinearMap.det (Lβ β) ≠ 0 := det_Lβ_ne β hβ hd
  have hjac : jacβ β ≠ 0 := by
    unfold jacβ
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact hd _ _
    · exact one_ne_zero
  have hnj : 0 < Complex.normSq (jacβ β) := Complex.normSq_pos.2 hjac
  have hnd : 0 < Complex.normSq (LinearMap.det (Lβ β)) := Complex.normSq_pos.2 hdet
  let Lr : (UpI X.Ψ r → ℂ) →ₗ[ℝ] (UpI X.Ψ r → ℂ) := (Lβ β).restrictScalars ℝ
  have hdetr : LinearMap.det Lr = Complex.normSq (LinearMap.det (Lβ β)) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hdetr0 : LinearMap.det Lr ≠ 0 := by rw [hdetr]; exact hnd.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (UpI X.Ψ r → ℂ)) hdetr0
  have hSm : MeasurableSet (SR X R0) := measurableSet_SR X R0
  let c : ℝ≥0∞ := ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹)
  let G : (UpI X.Ψ r → ℂ) → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Complex.normSq (jacU u)) * c * (SR X R0).indicator 1 u
  have hG : Measurable G :=
    (measurable_normSq_jacU.mul_const c).mul (measurable_one.indicator hSm)
  have hLm : Measurable Lr := Lr.continuous_of_finiteDimensional.measurable
  have hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) =
      G (Lr y) := by
    intro y
    have e : ENNReal.ofReal (Complex.normSq (jacβ β * jacU y)) * c =
        ENNReal.ofReal (Complex.normSq (jacU y)) := by
      rw [Complex.normSq_mul, ← ENNReal.ofReal_mul (mul_nonneg hnj.le (Complex.normSq_nonneg _))]
      congr 1
      rw [mul_right_comm, mul_inv_cancel₀ hnj.ne', one_mul]
    show _ = ENNReal.ofReal (Complex.normSq (jacU (Lβ β y))) * c * (SR X R0).indicator 1 (Lβ β y)
    rw [jacU_Lβ β hβ y, e]
  have hGi : ∫⁻ u, G u = KR X R0 * c := by
    have h : G = (SR X R0).indicator (fun u => ENNReal.ofReal (Complex.normSq (jacU u)) * c) := by
      funext u
      simp only [G, Set.indicator]
      split_ifs <;> simp
    rw [h, lintegral_indicator hSm, lintegral_mul_const _ measurable_normSq_jacU]
    rfl
  calc ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y)
      = ∫⁻ y, G (Lr y) := lintegral_congr fun y => hpt y
    _ = ∫⁻ u, G u ∂(Measure.map Lr volume) := (lintegral_map hG hLm).symm
    _ = ENNReal.ofReal |(LinearMap.det Lr)⁻¹| * ∫⁻ u, G u := by
        rw [hmap, lintegral_smul_measure, smul_eq_mul]
    _ = _ := by
        rw [hGi, hdetr, abs_of_pos (inv_pos.2 hnd), mul_inv, ENNReal.ofReal_mul (inv_pos.2 hnd).le]
        ring

def Jp (C : Set (Frame X.Ψ r)) (p : Frame X.Ψ r) : ℝ≥0∞ :=
  ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
    ENNReal.ofReal (Complex.normSq (jacU y)) * C.indicator 1 (rmul p (UF X y)) else 0)

theorem Jp_le {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {R0 : ℝ}
    (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0) {p : Frame X.Ψ r} (hp : p ∈ X.dom)
    (hlast : ∀ τ, ‖dmin X.Gm p τ (Fin.last r)‖ = 1) :
    Jp X C p ≤ ENNReal.ofReal (densY X p) * KR X R0 := by
  have hdg : ∀ τ b, β0 X p τ b b ≠ 0 := by
    intro τ b
    have h := β0_det X hp τ
    rw [Matrix.det_of_upperTriangular (β0_upper X hp τ)] at h
    exact Finset.prod_ne_zero_iff.1 h b (Finset.mem_univ b)
  have hle : Jp X C p ≤ ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) *
      (SR X R0).indicator 1 (Lβ (β0 X p) y) := by
    unfold Jp
    refine lintegral_mono fun y => ?_
    split_ifs with hy
    · by_cases hx : rmul p (UF X y) ∈ C
      · have hS : Lβ (β0 X p) y ∈ SR X R0 := fun i => Lβ_bound X hCd hR0 hp hy hx i
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hS]
      · simp [Set.indicator, hx]
    · simp
  rw [upper_gen X (β0 X p) (β0_upper X hp) hdg R0, exponent_identity X hp hlast, ← densY_eq X] at hle
  exact hle

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def ufL : (Ix X.Ψ r → ℂ) ≃ₗ[ℂ] Frame X.Ψ r where
  toFun := uf X
  invFun x i := x i.1 i.2.1 i.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def ufC : (Ix X.Ψ r → ℂ) ≃L[ℂ] Frame X.Ψ r := (ufL X).toContinuousLinearEquiv

theorem haarF : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure := by
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  rw [volume_pi]
  exact Measure.pi.isAddHaarMeasure _

theorem haarIx : (volume : Measure (Ix X.Ψ r → ℂ)).IsAddHaarMeasure := by
  infer_instance

attribute [local instance] haarF haarIx

theorem lintegral_ufC (F : Frame X.Ψ r → ℝ≥0∞) :
    ∫⁻ v, F (ufC X v) = Measure.addHaarScalarFactor (volume.map (ufC X)) volume * ∫⁻ x, F x := by
  haveI : (volume.map (ufC X)).IsAddHaarMeasure := (ufC X).isAddHaarMeasure_map volume
  have e1 : ∫⁻ v, F (ufC X v) = ∫⁻ x, F x ∂(volume.map (ufC X)) :=
    (lintegral_map_equiv F (ufC X).toHomeomorph.toMeasurableEquiv).symm
  rw [e1]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (volume.map (ufC X)) volume]
  rw [lintegral_smul_measure]
  rfl

theorem continuous_UF : Continuous (UF X) := by
  apply continuous_pi
  intro τ
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [UF, Umat, Matrix.of_apply]
  by_cases hh : b < a
  · simp only [hh, not_true_eq_false, dite_false]
    exact continuous_const
  · simp only [hh, not_false_eq_true, dite_true]
    fun_prop

theorem continuous_rmul : Continuous fun q : Frame X.Ψ r × Frame X.Ψ r => rmul q.1 q.2 := by
  apply continuous_pi
  intro τ
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  apply continuous_finset_sum
  intro k _
  fun_prop

def fI (C : Set (Frame X.Ψ r)) (q : Frame X.Ψ r × (UpI X.Ψ r → ℂ)) : ℝ≥0∞ :=
  if ∀ τ b, q.2 (dI τ b) ≠ 0 then
    ENNReal.ofReal (Complex.normSq (jacU q.2)) * C.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul q.1 (UF X q.2)) else 0

theorem measurable_fI {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C) : Measurable (fI X C) := by
  have hJ : Continuous (fun y : UpI X.Ψ r → ℂ => jacU y) := by
    unfold jacU
    apply continuous_finset_prod
    intro i _
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  have hS : MeasurableSet {q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) | ∀ τ b, q.2 (dI τ b) ≠ 0} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b => ?_
    have hc : Continuous fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) => q.2 (dI τ b) :=
      (continuous_apply (dI τ b) : Continuous fun y : UpI X.Ψ r → ℂ => y (dI τ b)).comp continuous_snd
    exact (isOpen_ne_fun hc continuous_const).measurableSet
  have hf : Measurable (fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) =>
      ENNReal.ofReal (Complex.normSq (jacU q.2))) :=
    ENNReal.measurable_ofReal.comp ((Complex.continuous_normSq.comp (hJ.comp continuous_snd)).measurable)
  have hg : Measurable (fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) =>
      C.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul q.1 (UF X q.2))) :=
    (measurable_one.indicator hCm).comp
      ((continuous_rmul X).comp (continuous_fst.prodMk ((continuous_UF X).comp continuous_snd))).measurable
  unfold fI
  exact Measurable.ite hS (hf.mul hg) measurable_const

theorem measurable_Jp {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C) : Measurable (Jp X C) := by
  exact (measurable_fI X hCm).lintegral_prod_right'

theorem Jp_eq_zero {C : Set (Frame X.Ψ r)} {q : Frame X.Ψ r}
    (h : ∀ y : UpI X.Ψ r → ℂ, (∀ τ b, y (dI τ b) ≠ 0) → rmul q (UF X y) ∉ C) : Jp X C q = 0 := by
  unfold Jp
  have hz : ∀ y : UpI X.Ψ r → ℂ, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * C.indicator 1 (rmul q (UF X y)) else 0) = 0 := by
    intro y
    split_ifs with hy
    · simp [Set.indicator, h y hy]
    · rfl
  simp_rw [hz]
  exact lintegral_zero

theorem mem_sat {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {x0 : Frame X.Ψ r} {z : V (nd X)}
    {y : UpI X.Ψ r → ℂ} (hd : ∀ τ b, y (dI τ b) ≠ 0) (hxC : rmul (cpt X x0 z) (UF X y) ∈ C) :
    z ∈ sat X x0 C := by
  have hb := UF_mem X hd
  refine ⟨?_, rmul (cpt X x0 z) (UF X y), hxC, invF X (UF X y), invF_mem' X hb, (rmul_invF X hb).symm⟩
  show cpt X x0 z ∈ X.dom
  have := OrthogonalFrameDomain.rmul_mem_dom X (hCd hxC) (invF_mem' X hb)
  rwa [rmul_invF X hb] at this

theorem not_dom_rmul {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {p : Frame X.Ψ r} (hp : p ∉ X.dom)
    {y : UpI X.Ψ r → ℂ} (hd : ∀ τ b, y (dI τ b) ≠ 0) : rmul p (UF X y) ∉ C := fun h => by
  have hb := UF_mem X hd
  have := OrthogonalFrameDomain.rmul_mem_dom X (hCd h) (invF_mem' X hb)
  rw [rmul_invF X hb] at this
  exact hp this

theorem inner_le {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C)
    (hCd : C ⊆ X.dom) {R0 : ℝ} (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0)
    {G : Frame X.Ψ r → ℝ≥0∞} (hGinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x)
    (x : LoI X.Ψ r → ℂ) :
    ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then ENNReal.ofReal (Complex.normSq (jacU y)) *
      C.indicator G (ufC X (LA (fun τ => mat x0 τ) (lu ((eS X.Ψ r).symm (x, y))))) else 0) ≤
      KR X R0 * GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
  set p := rmul x0 (NF X x) with hpdef
  have hg : ∀ y, C.indicator G (ufC X (LA (fun τ => mat x0 τ) (lu ((eS X.Ψ r).symm (x, y))))) =
      C.indicator G (rmul p (UF X y)) := by
    intro y
    change C.indicator G (rmul x0 (uf X (lu ((eS X.Ψ r).symm (x, y))))) = _
    rw [uf_lu_eS, rmul_assoc']
  by_cases hp : p ∈ X.dom
  · have hmeas : Measurable fun y => fI X C (p, y) :=
      (measurable_fI X hCm).comp (measurable_const.prodMk measurable_id)
    calc _ = ∫⁻ y, G p * fI X C (p, y) := lintegral_congr fun y => by
            simp only [fI]
            split_ifs with hd
            · rw [hg y]
              by_cases hxC : rmul p (UF X y) ∈ C
              · rw [Set.indicator_of_mem hxC, Set.indicator_of_mem hxC, hGinv p hp _ (UF_mem X hd),
                  Pi.one_apply, mul_one, mul_comm]
              · simp [Set.indicator_of_notMem hxC]
            · rw [mul_zero]
      _ = G p * Jp X C p := lintegral_const_mul _ hmeas
      _ ≤ KR X R0 * GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
          unfold GLo
          rw [if_pos hp]
          by_cases hJ : Jp X C p = 0
          · rw [hJ, mul_zero]; exact bot_le
          · rw [Set.indicator_of_mem (show p ∈ {p | Jp X C p ≠ 0} from hJ)]
            calc G p * Jp X C p ≤ G p * (ENNReal.ofReal (densY X p) * KR X R0) := by
                  gcongr; exact Jp_le X hCd hR0 hp (fun τ => norm_dmin_last X hx0 x τ)
              _ = KR X R0 * (G p * ENNReal.ofReal (densY X p)) := by ring
  · calc _ = ∫⁻ y, (0 : ℝ≥0∞) := lintegral_congr fun y => by
            split_ifs with hd
            · rw [hg y, Set.indicator_of_notMem (not_dom_rmul X hCd hp hd), mul_zero]
            · rfl
      _ = 0 := lintegral_zero
      _ ≤ _ := bot_le

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up.MI ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable FM.haarF FM.haarIx

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem FrameMeasStatement_holds : FrameMeasStatement (E := E) := by
  intro r X x0 hx0 C hC hCd
  have hx0' : X.IsOrtho x0 := hx0
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  obtain ⟨R1, hR1⟩ := β0_bound (X := X) hC hCd
  have hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ max R1 0 :=
    fun x hx τ a b => (hR1 x hx τ a b).trans (le_max_left _ _)
  have hKR : KR X (max R1 0) ≠ ⊤ := (KR_lt_top (X := X) (le_max_right R1 0)).ne
  have hdet : ∀ τ, (mat x0 τ).det ≠ 0 := by
    intro τ h
    have h1 := normSq_det_orthogonalFrame (X := X) hx0' τ
    rw [h, map_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hU0 : ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have hΦ0 : ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have hP : (∏ τ, (mat x0 τ).det ^ r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hdet τ)
  have hA0 : ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (Complex.normSq_pos.mpr hP))).ne'
  refine ⟨((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
      (ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹)⁻¹ * KR X (max R1 0) *
      ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹, ?_, ?_⟩
  · exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr hU0) (ENNReal.inv_ne_top.mpr hA0)) hKR)
      (ENNReal.inv_ne_top.mpr hΦ0)).lt_top
  intro G hGm hGinv
  have hFm : Measurable (C.indicator G) := hGm.indicator hCm
  have hφm : Measurable ({p | Jp X C p ≠ 0}.indicator G) :=
    hGm.indicator ((measurable_Jp (X := X) hCm) (measurableSet_singleton 0).compl)

  have hUf : ∫⁻ v, C.indicator G (ufC X v) =
      ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ x, C.indicator G x := lintegral_ufC (X := X) (C.indicator G)
  have hLA : ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) =
      ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ *
        ∫⁻ v, C.indicator G (ufC X v) :=
    lintegral_comp_LA (fun τ => mat x0 τ) hdet (hFm.comp (ufC X).continuous.measurable)
  have hgm : Measurable (fun v => C.indicator G (ufC X (LA (fun τ => mat x0 τ) v))) :=
    hFm.comp ((ufC X).continuous.measurable.comp
      (LinearMap.continuous_of_finiteDimensional _).measurable)
  have hin : ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) ≤
      KR X (max R1 0) * ∫⁻ x, GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
    refine le_trans (le_of_eq (lintegral_flat hgm)) ?_
    rw [← lintegral_const_mul' _ _ hKR]
    exact lintegral_mono fun x => inner_le (X := X) hx0' hCm hCd hR0 hGinv x
  have hmuX := lintegral_muX (X := X) (x0 := x0) hφm
  have hlast : ∫⁻ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ∂muX X x0 ≤
      ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0 := by
    have hpt : ∀ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ≤
        (sat X x0 C).indicator (fun z => G (cpt X x0 z)) z := by
      intro z
      by_cases hJ : Jp X C (cpt X x0 z) = 0
      · have h0 : ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) = 0 :=
          Set.indicator_apply_eq_zero.mpr fun h => (h hJ).elim
        rw [h0]
        exact zero_le
      · have hz : z ∈ sat X x0 C := by
          by_contra hz
          apply hJ
          apply Jp_eq_zero (X := X)
          intro y hy hyC
          exact hz (mem_sat (X := X) hCd hy hyC)
        rw [Set.indicator_of_mem (show cpt X x0 z ∈ {p | Jp X C p ≠ 0} from hJ),
          Set.indicator_of_mem hz]
    exact (lintegral_mono hpt).trans (lintegral_indicator_le _ _)
  have e1 : ∫⁻ x, C.indicator G x =
      ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ∫⁻ v, C.indicator G (ufC X v) := by
    rw [hUf, ← mul_assoc, ENNReal.inv_mul_cancel hU0 ENNReal.coe_ne_top, one_mul]
  have e2 : ∫⁻ v, C.indicator G (ufC X v) =
      (ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹)⁻¹ *
        ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) := by
    rw [hLA, ← mul_assoc, ENNReal.inv_mul_cancel hA0 ENNReal.ofReal_ne_top, one_mul]
  have e4 : ∫⁻ x, GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x =
      ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ∫⁻ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ∂muX X x0 := by
    rw [hmuX, ← mul_assoc, ENNReal.inv_mul_cancel hΦ0 ENNReal.coe_ne_top, one_mul]
  rw [← lintegral_indicator (f := G) hCm, e1, e2, mul_assoc, mul_assoc, mul_assoc]
  gcongr
  refine hin.trans ?_
  rw [e4]
  gcongr
  all_goals exact hlast

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nsq_eq_normSq (s : Fin (nd X) → Frame X.Ψ r → ℂ) (x0 : Frame X.Ψ r) (z : V (nd X)) :
    (∑ k, ‖s k (cpt X x0 z)‖ ^ 2) = HE.nsq (fun k z => s k (cpt X x0 z)) z := by
  unfold HE.nsq
  exact Finset.sum_congr rfl fun k _ => (Complex.normSq_eq_norm_sq _).symm

theorem lhs_finite (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (Xa : ArchInM X) (Fl : FlatM X Xa)
    (ψ : Frame X.Ψ r → ℝ) (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0) (bb : ℝ) (hbb : 0 ≤ bb)
    (ε : ℝ) (hε : 0 < ε)
    (hnull : volume {y | y ∈ OmF X x0 ∧ HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y = 0} = 0)
    (F : V (nd X) → ℂ)
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) (N : Set (Frame X.Ψ r))
    (hN2 : ∀ z ∈ OmF X x0, cpt X x0 z ∈ N → z ∉ closedBall (0 : V (nd X)) (2 * ε)) :
    ∫⁻ z, N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z) ∂muF X x0 < ⊤ := by
  rw [muF_lintegral]
  have hO := ExF.isOpen_OmF X x0
  have hpt : ∀ᵐ z ∂(volume.restrict (OmF X x0)),
      ENNReal.ofReal (densF X x0 z) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z) ≤
        ENNReal.ofReal (Real.exp C0) * ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := by
    rw [ae_restrict_iff' hO.measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz0 hz
    by_cases hzN : cpt X x0 z ∈ N
    swap
    · rw [Set.indicator_of_notMem hzN, mul_zero]; exact zero_le
    rw [Set.indicator_of_mem hzN]
    have hx : cpt X x0 z ∈ X.dom := hz
    have hN : 0 < HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z := by
      rcases (HE.nsq_nonneg _ z).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨hz, h.symm⟩ hz0
    have hcut : HE.cut ε hε z = 0 := HE.cut_zero ε hε (by
      have := hN2 z hz hzN
      rw [mem_closedBall, dist_zero_right, not_le] at this; exact this.le)
    set S := ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 with hSdef
    have hS : S = HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z * Real.exp (-phla X Xa.L (cpt X x0 z)) :=
      pnorm_sum_eq X Xa.L Fl.s hx
    have hSpos : 0 < S := by rw [hS]; positivity
    have hrho := rhoF_eq X x0 Xa.Fp Xa.L ψ bb Fl.s hz hN
    rw [← hSdef] at hrho
    rw [gφ_dom X P Xa.Fp Xa.L Fl.s hx, ← hSdef, ← ENNReal.ofReal_inv_of_pos hSpos,
      ← ENNReal.ofReal_pow (inv_nonneg.2 hSpos.le), ← mul_assoc,
      ← ENNReal.ofReal_mul (densF_pos X x0 hz).le,
      ← ENNReal.ofReal_mul (mul_nonneg (densF_pos X x0 hz).le (by positivity)),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [hPF z hz, hcut, zero_sub, norm_neg]
    have hd := densF_pos X x0 hz
    have hrho2 : rhoF X x0 Xa.Fp ψ bb z = Real.exp (-phla X Xa.Fp (cpt X x0 z)) *
        Real.exp (-ψ (cpt X x0 z)) * Real.exp (bb * rhF X x0 z) * densF X x0 z := by
      rw [rhoF, Real.exp_add, Real.exp_add, Real.exp_log hd, neg_add, Real.exp_add]
    have hSn : S⁻¹ ^ (nd X) = (S ^ (nd X : ℝ))⁻¹ := by
      rw [Real.rpow_natCast, inv_pow]
    have hSn0 : 0 < S ^ (nd X : ℝ) := Real.rpow_pos_of_pos hSpos _
    set A := Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
      HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ)) with hAdef
    have hA0 : 0 ≤ A := by positivity

    have key : densF X x0 z * Real.exp (-phla X Xa.Fp (cpt X x0 z)) * S⁻¹ ^ (nd X) =
        A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z)) := by
      have e1 : A = rhoF X x0 Xa.Fp ψ bb z / S ^ (nd X : ℝ) := by
        rw [hrho]; field_simp
      rw [e1, hrho2, hSn]
      have h1 : Real.exp (-ψ (cpt X x0 z)) * Real.exp (ψ (cpt X x0 z)) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h2 : Real.exp (bb * rhF X x0 z) * Real.exp (-(bb * rhF X x0 z)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      field_simp
      nlinarith [h1, h2]
    have hle : A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z)) ≤ Real.exp C0 * A := by
      have e2 : Real.exp (ψ (cpt X x0 z)) ≤ Real.exp C0 := Real.exp_le_exp.2 (hψb _ hx)
      have e3 : Real.exp (-(bb * rhF X x0 z)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)
      have e4 := (Real.exp_pos (-(bb * rhF X x0 z))).le
      calc A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z))
          ≤ A * Real.exp C0 * 1 := by gcongr
        _ = Real.exp C0 * A := by ring
    have hF2 : 0 ≤ ‖F z‖ ^ 2 := sq_nonneg _
    calc densF X x0 z * (‖F z‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x0 z))) * S⁻¹ ^ (nd X)
        = ‖F z‖ ^ 2 * (densF X x0 z * Real.exp (-phla X Xa.Fp (cpt X x0 z)) * S⁻¹ ^ (nd X)) := by ring
      _ ≤ ‖F z‖ ^ 2 * (Real.exp C0 * A) := by rw [key]; exact mul_le_mul_of_nonneg_left hle hF2
      _ = Real.exp C0 * (‖F z‖ ^ 2 * Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
            HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := by rw [hAdef]; ring
  calc ∫⁻ z in OmF X x0, ENNReal.ofReal (densF X x0 z) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z)
      ≤ ∫⁻ z in OmF X x0, ENNReal.ofReal (Real.exp C0) * ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp C0) * ∫⁻ z in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

theorem rhs_bound (x1 : Frame X.Ψ r) (Xa : ArchInM X) (Fl : FlatM X Xa) (P : Frame X.Ψ r → ℂ)
    (N : Set (Frame X.Ψ r)) (ρ1 : ℝ) (hρ1 : 0 < ρ1) (hcb : closedBall (0 : V (nd X)) ρ1 ⊆ OmF X x1)
    (hN1 : ∀ w ∈ ball (0 : V (nd X)) ρ1, cpt X x1 w ∈ N) :
    ∃ c1 : ℝ, 0 < c1 ∧ ENNReal.ofReal c1 * ∫⁻ w in ball (0 : V (nd X)) ρ1,
      ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
      ∫⁻ w, N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) ∂muF X x1 := by
  set h1 : V (nd X) → ℝ := fun w => Real.exp (Real.log (densF X x1 w) - phla X Xa.Fp (cpt X x1 w) +
    (nd X : ℝ) * phla X Xa.L (cpt X x1 w)) with hh1
  have hc : ContinuousOn h1 (closedBall (0 : V (nd X)) ρ1) := fun w hw =>
    (Real.continuous_exp.continuousAt.comp ((((logDens_cdAt X x1 (hcb hw)).sub
      (phla_cpt_cdAt X x1 (hcb hw) Xa.Fp)).add (contDiffAt_const.mul
        (phla_cpt_cdAt X x1 (hcb hw) Xa.L))).continuousAt)).continuousWithinAt
  obtain ⟨w0, hw0, hmin⟩ := (isCompact_closedBall (0 : V (nd X)) ρ1).exists_isMinOn
    ⟨0, mem_closedBall_self hρ1.le⟩ hc
  refine ⟨h1 w0, Real.exp_pos _, ?_⟩
  have hpt : ∀ w ∈ ball (0 : V (nd X)) ρ1, ENNReal.ofReal (h1 w0) *
      ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
      ENNReal.ofReal (densF X x1 w) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) := by
    intro w hw
    have hwO := hcb (ball_subset_closedBall hw)
    have hx : cpt X x1 w ∈ X.dom := hwO
    rw [Set.indicator_of_mem (hN1 w hw), gφ_dom X P Xa.Fp Xa.L Fl.s hx, nsq_eq_normSq]
    set n2 := HE.nsq (fun k z => Fl.s k (cpt X x1 z)) w with hn2
    rcases (HE.nsq_nonneg (fun k z => Fl.s k (cpt X x1 z)) w).lt_or_eq with hN | hN
    · have hN' : 0 < n2 := hN
      set S := ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x1 w) ^ 2 with hSdef
      have hS : S = n2 * Real.exp (-phla X Xa.L (cpt X x1 w)) := pnorm_sum_eq X Xa.L Fl.s hx
      have hSpos : 0 < S := by rw [hS]; positivity
      have hd := densF_pos X x1 hwO
      rw [← ENNReal.ofReal_inv_of_pos hSpos, ← ENNReal.ofReal_pow (inv_nonneg.2 hSpos.le), ← mul_assoc,
        ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (mul_nonneg hd.le (by positivity)),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hid : densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) * S⁻¹ ^ (nd X) =
          h1 w * n2 ^ (-(nd X : ℝ)) := by
        have e1 : h1 w = densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) *
            Real.exp (phla X Xa.L (cpt X x1 w)) ^ (nd X) := by
          simp only [hh1]
          rw [Real.exp_add, Real.exp_sub, Real.exp_log hd, Real.exp_neg, Real.exp_nat_mul]
          ring
        rw [e1, hS, Real.rpow_neg hN'.le, Real.rpow_natCast, mul_inv, mul_pow,
          show (Real.exp (-phla X Xa.L (cpt X x1 w)))⁻¹ = Real.exp (phla X Xa.L (cpt X x1 w)) by
            rw [Real.exp_neg, inv_inv], inv_pow]
        ring
      have hm : h1 w0 ≤ h1 w := hmin (ball_subset_closedBall hw)
      have hq : 0 ≤ ‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ)) := by positivity
      calc h1 w0 * (‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ)))
          ≤ h1 w * (‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ))) := mul_le_mul_of_nonneg_right hm hq
        _ = densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x1 w))) *
              S⁻¹ ^ (nd X) := by
            rw [show densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x1 w))) *
              S⁻¹ ^ (nd X) = ‖P (cpt X x1 w)‖ ^ 2 * (densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) *
              S⁻¹ ^ (nd X)) by ring, hid]
            ring
    · have hN' : n2 = 0 := hN.symm
      rw [hN', Real.zero_rpow (by have := Xa.n_ge; simp; omega), mul_zero, ENNReal.ofReal_zero,
        mul_zero]
      exact zero_le
  calc ENNReal.ofReal (h1 w0) * ∫⁻ w in ball (0 : V (nd X)) ρ1,
        ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ)))
      = ∫⁻ w in ball (0 : V (nd X)) ρ1, ENNReal.ofReal (h1 w0) *
        ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ w in ball (0 : V (nd X)) ρ1, ENNReal.ofReal (densF X x1 w) *
          N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) := setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ w in OmF X x1, ENNReal.ofReal (densF X x1 w) *
          N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) :=
        lintegral_mono_set (ball_subset_closedBall.trans hcb)
    _ = _ := (muF_lintegral X x1 _).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem vanish_other (hV : VanishAtSStatement (E := E)) (hM : MeasInvStatement (E := E))
    (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E)) (hR : NfacRmulStatement (E := E))
    (Xa : ArchInM X) (Fl : FlatM X Xa) (ψ : Frame X.Ψ r → ℝ) (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0)
    (bb : ℝ) (hbb : 0 ≤ bb) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (b0 : Frame X.Ψ r)
    (hb0 : b0 ∈ Bor X.Ψ r) (j : Fin Fl.δ) (hx : Fl.xs j = rmul x0 b0) (ε : ℝ) (hε : 0 < ε)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0)
    (hiso : ∀ y ∈ closedBall (0 : V (nd X)) (2 * ε), (∀ k, Fl.s k (cpt X x0 y) = 0) → y = 0)
    (hnull : volume {y | y ∈ OmF X x0 ∧ HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y = 0} = 0)
    (F : V (nd X) → ℂ)
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hBE : IsBEq X Xa.Fp P) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (j' : Fin Fl.δ) (hne : γ ≠ 1 ∨ j' ≠ j) :
    P (lact γ (Fl.xs j')) = 0 := by
  have hw0sec : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hssec : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hy : lact γ (Fl.xs j') ∈ X.dom := OntoS.dom_lact X hγ (Fl.xs_mem j')
  obtain ⟨x1, ho1, b1, hb1, hyeq⟩ := hO r X _ hy
  have hx1dom : x1 ∈ X.dom := orth_mem_dom X x1 ho1

  have hs1 : ∀ k, Fl.s k x1 = 0 := by
    intro k
    have h0 : Fl.s k (lact γ (Fl.xs j')) = 0 :=
      (Fl.S_eq _ hy).2 ⟨j', γ, hγ, idF X, idF_mem X, by rw [rmul_idF]⟩ k
    rw [hyeq, (hssec k).2.1 x1 hx1dom b1 hb1] at h0
    exact (mul_eq_zero.1 h0).resolve_left (bchar_ne_zero X hb1 _)
  have hw1 : Fl.w0 x1 ≠ 0 := by
    intro h
    have h1 : Fl.w0 (lact γ (Fl.xs j')) = X.χ Xa.L γ * Fl.w0 (Fl.xs j') :=
      hw0sec.2.2 γ hγ _ (Fl.xs_mem j')
    rw [hyeq, hw0sec.2.1 x1 hx1dom b1 hb1, h, mul_zero] at h1
    exact mul_ne_zero (chi_ne X hγ) (Fl.w0_ne j') h1.symm
  have hx0dom : x0 ∈ X.dom := orth_mem_dom X x0 ho
  have hx0d : ∀ τ, (mat x0 τ).det ≠ 0 := fun τ => (hx0dom τ).1
  have hx1d : ∀ τ, (mat x1 τ).det ≠ 0 := fun τ => (hx1dom τ).1
  have hx1av := avoid_base X Xa Fl j j' hγ hne x0 b0 hb0 hx x1 b1 hb1 hyeq ε hball hiso hs1
  obtain ⟨Nb, hNb, hNbav⟩ :=
    nbhd_avoid X x0 hx0d (isCompact_closedBall (0 : V (nd X)) (2 * ε)) hx1av hx1d
  have hOm : IsOpen (OmF X x1) := (isOpen_dom X).preimage (cpt_diff X x1).continuous
  have hS : OmF X x1 ∩ cpt X x1 ⁻¹' Nb ∈ 𝓝 (0 : V (nd X)) := by
    refine Filter.inter_mem (hOm.mem_nhds (zero_mem_OmF X x1 ho1)) ?_
    apply (cpt_diff X x1).continuous.continuousAt.preimage_mem_nhds
    rw [cpt_zero X x1]
    exact hNb
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hS
  have hρ : 0 < δ / 2 := half_pos hδ
  have hcbδ : closedBall (0 : V (nd X)) (δ / 2) ⊆ ball 0 δ :=
    Metric.closedBall_subset_ball (half_lt_self hδ)
  have hcb : closedBall (0 : V (nd X)) (δ / 2) ⊆ OmF X x1 := fun w hw => (hδsub (hcbδ hw)).1
  have hbO : ball (0 : V (nd X)) (δ / 2) ⊆ OmF X x1 :=
    fun w hw => hcb (Metric.ball_subset_closedBall hw)
  have hbN : ∀ w ∈ ball (0 : V (nd X)) (δ / 2), cpt X x1 w ∈ Nb :=
    fun w hw => (hδsub (hcbδ (Metric.ball_subset_closedBall hw))).2

  obtain ⟨Δ, zOf, bOf, hΔ, -, hzOf, -, hdec, hlast⟩ := hLU r X x1 ho1
  have hN1 : ∀ w ∈ ball (0 : V (nd X)) (δ / 2), cpt X x1 w ∈ Nset X Δ zOf (δ / 2) := by
    intro w hw
    obtain ⟨hΔw, hzw, -⟩ := hlast w (hbO hw) (idF X) (idF_mem X)
    rw [rmul_idF] at hΔw hzw
    show (cpt X x1 w ∈ X.dom ∧ Δ (cpt X x1 w) ≠ 0) ∧ zOf (cpt X x1 w) ∈ ball (0 : V (nd X)) (δ / 2)
    exact ⟨⟨hbO hw, hΔw⟩, by rw [hzw]; exact hw⟩
  have hN2 : ∀ z ∈ OmF X x0, cpt X x0 z ∈ Nset X Δ zOf (δ / 2) →
      z ∉ closedBall (0 : V (nd X)) (2 * ε) := by
    intro z _ hzN hzB
    generalize hxz : cpt X x0 z = x at hzN
    have hzN' : (x ∈ X.dom ∧ Δ x ≠ 0) ∧ zOf x ∈ ball (0 : V (nd X)) (δ / 2) := hzN
    obtain ⟨⟨hxd, hxΔ⟩, hxb⟩ := hzN'
    obtain ⟨-, hbB, hxeq⟩ := hdec x hxd hxΔ
    apply hNbav _ (hbN _ hxb) z hzB (binv X (bOf x)) (binv_mem X hbB)
    calc cpt X x1 (zOf x) = rmul (rmul (cpt X x1 (zOf x)) (bOf x)) (binv X (bOf x)) :=
          (rmul_binv X _ hbB).symm
      _ = rmul x (binv X (bOf x)) := by rw [← hxeq]
      _ = rmul (cpt X x0 z) (binv X (bOf x)) := by rw [hxz]
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hNopen : IsOpen (Nset X Δ zOf (δ / 2)) :=
    hzOf.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hmeas : Measurable ((Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s)) :=
    (gφ_meas X P hBE.1.continuousOn Xa.Fp Xa.L Fl.s fun k => (hssec k).1.continuousOn).indicator
      hNopen.measurableSet
  have hinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      (Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s) (rmul x b) =
        (Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s) x := by
    classical
    intro x hx b hb
    have hiff := Nset_sat X x1 hdec hlast (δ / 2) hx hb
    by_cases hxN : x ∈ Nset X Δ zOf (δ / 2)
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hiff.2 hxN), if_pos hxN,
        gφ_rmul X hR hBE hssec hx hb]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hxN (hiff.1 h)), if_neg hxN]

  obtain ⟨c1, hc1, hc1le⟩ := rhs_bound X x1 Xa Fl P (Nset X Δ zOf (δ / 2)) (δ / 2) hρ hcb hN1
  have hfin := lhs_finite X x0 ho Xa Fl ψ C0 hψb bb hbb ε hε hnull F hI P hPF
    (Nset X Δ zOf (δ / 2)) hN2
  have heq := hM r X x1 x0 ho1 ho _ hmeas hinv
  have hlt := hc1le.trans_lt (heq.trans_lt hfin)
  have hfinI := ENNReal.lt_top_of_mul_ne_top_right hlt.ne (ENNReal.ofReal_pos.2 hc1).ne'
  have hdet := etale_transfer X hLU hw0sec hssec (Fl.xs_mem j') (Fl.coord j') hγ (idF_mem X) ho1
    hb1 (by rw [rmul_idF]; exact hyeq) hw1
  have hnd : 0 < nd X := by have := Xa.n_ge; omega
  have hP1 : P x1 = 0 :=
    hV r X x1 hnd ho1 hx1dom P Fl.w0 Fl.s (δ / 2) hρ ((comp_cpt_diffOn X hBE.1 x1).mono hbO)
      (fun k => (comp_cpt_diffOn X (hssec k).1 x1).mono hbO)
      ((comp_cpt_diffOn X hw0sec.1 x1).mono hbO) hw1 hs1 hdet hfinI
  rw [hyeq, hBE.2 x1 hx1dom b1 hb1, hP1, mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronHolPsi_of (hE : ExtFStatement (E := E)) (hM : MeasInvStatement (E := E))
    (hV : VanishAtSStatement (E := E)) (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E))
    (hC : OmFConnStatement (E := E)) (hR : NfacRmulStatement (E := E))
    (hLa : NfacLactStatement (E := E)) : KronHolPsiStatement (E := E) := by
  intro r X Xa Fl _hPD ψ hψ hψs hψb hbm0 hstr0 hLnn j
  obtain ⟨bb, m, hbb4, hbm, hmar⟩ := hbm0
  obtain ⟨η, hη, hstr⟩ := hstr0
  obtain ⟨C0, hC0⟩ := hψb

  obtain ⟨x0, ho, b0, hb0, hx⟩ := hO r X (Fl.xs j) (Fl.xs_mem j)
  have hbbpos : 0 < bb := lt_of_le_of_lt (by positivity) hbb4

  obtain ⟨ε, hε, hball, hiso, hnull, F, hFd, hI⟩ :=
    coord_step (X := X) hLU hC Xa Fl ψ x0 ho (hψs x0 ho) bb m hbbpos hbm (hmar x0 ho) η hη (hstr x0 ho)
      (hLnn x0 ho) j b0 hb0 hx
  have hint := integ_step (X := X) x0 ho Xa Fl ψ (hψs x0 ho) bb ε hε hball hnull F hI

  obtain ⟨P, hBE, hPF⟩ :=
    hE r X x0 ho Xa.Fp F hFd (extF_hyp (X := X) x0 ho Xa.Fp ψ C0 hC0 bb hbbpos.le F hint)
  obtain ⟨hw, hs0, hdet⟩ := coord_data (X := X) hLU Xa Fl j x0 ho b0 hb0 hx
  have hP1 : P x0 = 1 :=
    value_base (X := X) hV x0 ho Xa Fl ψ (hψs x0 ho) bb ε hε hball F hFd hI P hPF hw hs0 hdet
  have hMW := metricW_of hR hLa hO hLU X Xa.Fp ψ hψ hψs ⟨C0, hC0⟩
  refine ⟨x0, Wpsi X Xa.Fp ψ, bb, F, P, 1, ho, hMW.1, hMW.2, ?_, hbb4, hFd,
    inAt_of (X := X) x0 Xa.Fp ψ bb F hint, hBE, hPF, X.Γ.one_mem, ?_, ?_⟩
  · intro x hx'
    simp [Wpsi, hx']
  · rw [lact_one (X := X), hx, hBE.2 x0 (orth_mem_dom (X := X) x0 ho) b0 hb0, hP1, mul_one]
    exact bchar_ne_zero (X := X) hb0 Xa.Fp
  · intro γ hγ j' hne
    exact vanish_other (X := X) hV hM hO hLU hR Xa Fl ψ C0 hC0 bb hbbpos.le x0 ho b0 hb0 j hx ε hε hball
      hiso hnull F hI P hBE hPF hγ j' hne

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronHolPsi_of_frameMeas (hF : FrameMeasStatement (E := E)) : KronHolPsiStatement (E := E) :=
  IW.kronHolPsi_of (extF_of lu_holds hF) measInv_holds vanishAtS_holds ortho_holds lu_holds
    OmFConnStatement_holds normFactor_rightBorel_holds normFactor_leftAction_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff

private lemma fderiv_const_mul_apply {n : ℕ} (t : ℝ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (t : ℂ) * g w) y v = (t : ℂ) * fderiv ℝ g y v := by
  by_cases hd : DifferentiableAt ℝ g y
  · rw [fderiv_const_mul hd]
    simp
  · by_cases ht : t = 0
    · subst ht
      simp
    · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      have hd' : ¬ DifferentiableAt ℝ (fun w => (t : ℂ) * g w) y := by
        intro h'
        apply hd
        have h'' := h'.const_mul ((t : ℂ)⁻¹)
        simpa [← mul_assoc, inv_mul_cancel₀ ht'] using h''
      rw [fderiv_zero_of_not_differentiableAt hd', fderiv_zero_of_not_differentiableAt hd]
      simp

private lemma wd_const_mul (n : ℕ) (j : Fin n) (t : ℝ) (g : V n → ℂ) (y : V n) :
    wd n j (fun w => (t : ℂ) * g w) y = (t : ℂ) * wd n j g y := by
  unfold wd
  rw [fderiv_const_mul_apply, fderiv_const_mul_apply]
  ring

private lemma wdb_const_mul (n : ℕ) (j : Fin n) (t : ℝ) (g : V n → ℂ) :
    wdb n j (fun w => (t : ℂ) * g w) = fun y => (t : ℂ) * wdb n j g y := by
  funext y
  unfold wdb
  rw [fderiv_const_mul_apply, fderiv_const_mul_apply]
  ring

private lemma leviM_const_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (g : Frame X.Ψ r → ℝ) (t : ℝ) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviM X (fun x => t * g x) x0 z ξ = t * leviM X g x0 z ξ := by
  unfold leviM leviV
  have h1 : (fun w => (((t * g (cpt X x0 w) : ℝ)) : ℂ)) =
      fun w => (t : ℂ) * ((g (cpt X x0 w) : ℝ) : ℂ) := by
    funext w
    push_cast
    ring
  simp only [h1, wdb_const_mul, wd_const_mul, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]

theorem eta_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : EtaStatement (E := E) := by
  intro r X Xa
  obtain ⟨η, hη, h⟩ := Xa.posF
  refine ⟨η, hη, fun x0 ho z hz ξ => ?_⟩
  have hx0 : x0 ∈ X.dom := IW.orth_mem_dom (X := X) (x0 := x0) (ho := ho)
  have hzd : cpt X x0 z ∈ X.dom := hz
  have hc1 := Xa.frame_theta_const_pos
  have ha1 := Xa.frame_theta_weight_pos
  have ht0 : (0 : ℝ) ≤ 1 + Xa.c1 / Xa.a1 := by positivity
  have htr : (1 + Xa.c1 / Xa.a1) * Xa.rr ≤ 2 * (Xa.T : ℝ) := by
    rw [mul_comm]
    exact Xa.rr_le
  have h1 := h (1 + Xa.c1 / Xa.a1) ht0 htr x0 hx0 z hzd ξ
  have h2 := Xa.base_psi_levi_lower_bound x0 hx0 z hzd ξ
  have h3 := IW.leviM_comb (X := X) (x0 := x0) (ho := ho) (hz := hz) (la1 := Xa.Fp) (la2 := Xa.L)
    (k := nd X) (ξ := ξ)
  have h4 := leviM_const_mul X Xa.ps0 (1 + Xa.c1 / Xa.a1) x0 z ξ
  have h5 := mul_le_mul_of_nonneg_left h2 ht0
  rw [h3] at h1
  unfold leviO at h1 ⊢
  rw [h4]
  nlinarith [h1, h5]

end ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem EtaStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : EtaStatement (E := E) :=
  EtaPf.eta_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bigCellStatement_holds : BigCellStatement (E := E) := bigCell_of (lu_holds (E := E))

theorem kaUnfoldStatement_holds : KaUnfoldStatement (E := E) :=
  kaUnfold_of (measInv_holds (E := E)) SumBoundStatement_holds

theorem pairUnfoldStatement_holds : PairUnfoldStatement (E := E) :=
  PairUnfoldPf.pairUnfold_of (measInv_holds (E := E)) kaUnfoldStatement_holds (lu_holds (E := E))

theorem extFStatement_holds : ExtFStatement (E := E) :=
  extF_of (lu_holds (E := E)) (FrameMeasStatement_holds (E := E))

theorem onto_of_poin_extF (hPoin : PoinStatement (E := E)) (hExtF : ExtFStatement (E := E)) :
    OntoStatement (E := E) :=
  onto_of hPoin hExtF (RGF.rhGradF_holds (E := E)) (exhaustG_holds (E := E)) kaUnfoldStatement_holds
    pairUnfoldStatement_holds bigCellStatement_holds (OFC.omFConn_of_cm (E := E))

theorem kronHolPsiStatement_holds : KronHolPsiStatement (E := E) :=
  kronHolPsi_of_frameMeas (FrameMeasStatement_holds (E := E))

theorem interp_of_poin (hP : PoinStatement (E := E)) : InterpStatement (E := E) :=
  interp_of hP kronHolPsiStatement_holds

theorem interpC_of_poin (hP : PoinStatement (E := E))
    (hη : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 →
      ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ +
          leviO X x0 (fun x => (1 + Xa.c1 / Xa.a1) * Xa.ps0 x) z ξ) :
    InterpCStatement (E := E) := interpC_of hP kronHolPsiStatement_holds hη

theorem ontoStatement_holds : OntoStatement (E := E) :=
  onto_of_poin_extF (poin_holds (E := E)) extFStatement_holds

theorem interpStatement_holds : InterpStatement (E := E) := interp_of_poin (poin_holds (E := E))

theorem interpC_of_eta (hη : EtaStatement (E := E)) : InterpCStatement (E := E) :=
  interpC_of_poin (poin_holds (E := E)) hη

theorem interpCStatement_holds : InterpCStatement (E := E) := interpC_of_eta (EtaPf.eta_holds (E := E))

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
