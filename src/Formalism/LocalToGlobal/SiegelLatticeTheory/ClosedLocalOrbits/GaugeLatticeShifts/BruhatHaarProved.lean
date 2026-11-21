import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExistsGaugeNormalizedStabilizer
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGEB
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwSandwichOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwGaussUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiForm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwBigCellG
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiDeriv

section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.Jac

variable {k r : ℕ}

def gA (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r) : Mt k r :=
  fun i j => ((Matrix.of a)⁻¹ * E * Matrix.of b) i j

def gB (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r) : Mt k r :=
  fun i j => (Matrix.of a * E * (Matrix.of b)⁻¹) i j

theorem meas_gA (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun p : Mt k r × Mt k r => f (gA E p.1 p.2) := by
  have e : (fun p : Mt k r × Mt k r => gA E p.1 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => ((Matrix.of p.1)⁻¹) i j : Mt k r) *
        Matrix.of (E : Mt k r)) i j : Mt k r) * Matrix.of p.2) i j : Mt k r) := by
    funext p; rfl
  have : Measurable fun p : Mt k r × Mt k r => gA E p.1 p.2 := by
    rw [e]
    exact mulMt_meas (mulMt_meas (invMt_meas measurable_fst) measurable_const) measurable_snd
  exact hf.comp this


theorem measurable_comp_group_action (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun b : Mt k r => f (gA E a0 b) := by
  let P : Mt k r → Mt k r := fun b =>
    ((Matrix.of a0)⁻¹ * E * Matrix.of b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  have hP : Continuous P := by
    show Continuous fun b : Mt k r =>
      ((Matrix.of a0)⁻¹ * E * Matrix.of b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    fun_prop
  exact hf.comp hP.measurable

theorem gA_inv (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r)
    (ha : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det) :
    gA E (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) = gB E a b := by
  have h1 : ((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ = Matrix.of a :=
    Matrix.nonsing_inv_nonsing_inv _ ha
  show (fun i j => (((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ * E *
      (Matrix.of b)⁻¹) i j : Mt k r) = fun i j => (Matrix.of a * E * (Matrix.of b)⁻¹) i j
  rw [h1]

theorem prod_to_iter {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') {μW μW' : Measure (Mt k r)} (hW : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW)
    (hW' : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z') μW') (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * E * Matrix.of p.2) ∂(μW.prod μW') =
      ∫⁻ h, ∫⁻ h', f (fun i j => (Matrix.of h * E * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW := by
  have sW := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW
  have sW' := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW'
  have hinv : μW.map Formalism.FourierDecayAlt.B2.invM = μW :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW
  have hinv' : μW'.map Formalism.FourierDecayAlt.B2.invM = μW' :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z') μW' (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z') hW'
  have hA := meas_gA (k := k) (r := r) E hf
  have e0 : (fun p : Mt k r × Mt k r => f ((Matrix.of p.1)⁻¹ * E * Matrix.of p.2)) = fun p => f (gA E p.1 p.2) := by
    funext p; rfl
  rw [e0, lintegral_prod (fun p : Mt k r × Mt k r => f (gA E p.1 p.2)) hA.aemeasurable]
  have key : ∀ (ν : Measure (Mt k r)), ν.map Formalism.FourierDecayAlt.B2.invM = ν → ∀ F : Mt k r → ℝ≥0∞, Measurable F →
      ∫⁻ a, F a ∂ν = ∫⁻ a, F (Formalism.FourierDecayAlt.B2.invM a) ∂ν := by
    intro ν hν F hF
    conv_lhs => rw [← hν]
    exact lintegral_map hF Formalism.FourierDecayAlt.P.B2x1.invM_meas
  refine (key μW hinv _ hA.lintegral_prod_right').trans ?_
  have hae : ∀ᵐ a ∂μW, (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z :=
    ae_iff.2 hW.conc
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with a ha
  have hau : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det := unit_of_UH ha.1
  refine (key μW' hinv' _ (measurable_comp_group_action E (Formalism.FourierDecayAlt.B2.invM a) hf)).trans ?_
  refine lintegral_congr fun b => ?_
  rw [gA_inv E a b hau]
  rfl

theorem rhsWHaar : RhsWHaar := by
  intro k r z z' μW μW' a a' μsec D
  obtain ⟨μb0, hb0⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  have hW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 k r z μW D.z_mem D.T_pos D.haarW
  have hW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 k r z' μW' D.z'_mem D.T'_pos D.haarW'
  obtain ⟨C, hC, hI⟩ := Formalism.FourierDecayAlt.P.rank_one_integration_formula k r z z' μsec μb0 μW μW' D.k_pos D.z_mem D.z'_mem
    D.T_pos D.T'_pos D.sec hb0 hW hW'
  refine ⟨C⁻¹ • μb0, isHaarOn_smul (skHaar_of_cs hb0) (inv_pos.2 hC), fun φ hφ => ?_⟩
  rw [lintegral_smul_measure, hI φ hφ]
  unfold rhsW
  simp_rw [prod_to_iter D.z_mem D.T_pos D.z'_mem D.T'_pos hW hW' _ hφ]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hC.ne', ENNReal.coe_one, one_mul]

theorem mBase_mem {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hsec : IsSection k r z z' μsec) :
    mBase k r z z' μsec ∈ Formalism.FourierDecayAlt.B2.UWb k r := by
  have hlt : Tz k r z * Tz k r z' < Complex.normSq (zeta0 k r z z') := by
    have hp : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
    unfold zeta0
    rw [Complex.normSq_ofReal]
    have hs := Real.mul_self_sqrt hp.le
    have e : (2 * Real.sqrt (Tz k r z * Tz k r z')) * (2 * Real.sqrt (Tz k r z * Tz k r z')) =
        4 * (Real.sqrt (Tz k r z * Tz k r z') * Real.sqrt (Tz k r z * Tz k r z')) := by ring
    rw [e, hs]
    linarith
  exact (Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r).1 ▸ ⟨_, (hsec.2 _ hlt).1, rfl⟩

theorem gaugeShiftW : GaugeShiftW := by
  intro k r z z' μb μW μW' a a' μsec D hμb ρ hρ
  have hg : MeasurableSet (bBall k r ρ) := measurableSet_expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) ρ hρ
  have hmem : (mBase k r z z' μsec)⁻¹ ∈ Formalism.FourierDecayAlt.B2.UWb k r :=
    (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r).inv_mem _ (mBase_mem D.T_pos D.T'_pos D.sec)
  have hl : Measurable (lmulM (k := k) (r := r) (mBase k r z z' μsec)⁻¹) := by
    have : Continuous (lmulM (k := k) (r := r) (mBase k r z z' μsec)⁻¹) := by
      show Continuous fun x : Mt k r =>
        ((mBase k r z z' μsec)⁻¹ * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have e : mBall k r z z' μsec ρ = lmulM (mBase k r z z' μsec)⁻¹ ⁻¹' bBall k r ρ := rfl
  refine ⟨e ▸ hl hg, ?_⟩
  rw [e, ← Measure.map_apply hl hg, hμb.2.2.2 _ hmem]

theorem wbDataEx : WbDataEx := by
  intro k r hk
  set z : Fin (2 * r + k + 1) → ℂ := Formalism.L2.SG.Pf.WFL.zBv k r 1 with hz
  have hzW : inWb k r z := Formalism.L2.SG.Pf.WFL.inWb_zB 1
  have hzT : Tz k r z = 1 := Formalism.L2.SG.Pf.WFL.Tz_zB zero_le_one
  have hT : 0 < Tz k r z := by rw [hzT]; exact one_pos
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hzW hT
  have hcpt := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hzW hT
  have hfin : μ Set.univ < ⊤ := by
    have h1 : μ Set.univ ≤ μ (UWset k r z : Set (Mt k r)) + μ (UWset k r z : Set (Mt k r))ᶜ := by
      have := measure_union_le (μ := μ) (UWset k r z : Set (Mt k r)) (UWset k r z : Set (Mt k r))ᶜ
      rwa [Set.union_compl_self] at this
    have h2 : μ (UWset k r z : Set (Mt k r))ᶜ = 0 := hμ.conc
    have h3 : μ (UWset k r z : Set (Mt k r)) < ⊤ := hμ.finite_compact _ hcpt
    rw [h2, add_zero] at h1
    exact lt_of_le_of_lt h1 h3
  have h0 : μ Set.univ ≠ 0 := fun h => hμ.ne_zero (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨μsec, hsec⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r z z hk hzW hzW hT hT
  have ha : 0 < (μ Set.univ).toReal := ENNReal.toReal_pos h0 hfin.ne
  have hm : μ Set.univ = ENNReal.ofReal (μ Set.univ).toReal := (ENNReal.ofReal_toReal hfin.ne).symm
  exact ⟨z, z, μ, μ, _, _, μsec, ⟨hk, hzW, hzW, hT, hT, skHaar_of_cs hμ, skHaar_of_cs hμ, ha, ha, hm, hm, hsec⟩⟩

end Formalism.L2.SG.Pf.GE
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.GE

theorem bruhatHaar_of_sandwich_volLim (hS : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of_rhsHaar rhsHaar gaugeShift hS hV

theorem wbHaar_of_rhsWLim (hL : RhsWLim) : WbHaar :=
  wbHaar_of_rhsWHaar rhsWHaar gaugeShiftW hL

theorem gaugeExists_of_sandwich_rhsWLim (hS : Sandwich) (hV : VolLim) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : GaugeExists :=
  gaugeExists_of rhsHaar rhsWHaar wbDataEx hU gaugeShift gaugeShiftW (rhsLim_of hS hV) hL

theorem jacGauge_of_sandwich_gaugeMeasure (hS : Sandwich) (hV : VolLim) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : JacGauge :=
  jacGauge_of (bruhatHaar_of_sandwich_volLim hS hV) (wbHaar_of_rhsWLim hL) (gaugeExists_of_sandwich_rhsWLim hS hV hU hL)

end Formalism.L2.SG.Pf
end
end

section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.VL

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

theorem sq_cond {R1 R2 s : ℝ} (hs : 0 < s) (h1 : 0 ≤ R1) (h2 : 0 ≤ R2) (x : ℝ≥0∞) :
    ENNReal.ofReal R1 + x ^ 2 + ENNReal.ofReal R2 < ENNReal.ofReal (s ^ 2) ↔
      x < ENNReal.ofReal (Real.sqrt (s ^ 2 - R1 - R2)) := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  · lift x to NNReal using hx
    have hx2 : ((x : ℝ≥0∞)) ^ 2 = ENNReal.ofReal ((x : ℝ) ^ 2) := by
      rw [ENNReal.ofReal_pow (NNReal.coe_nonneg x), ENNReal.ofReal_coe_nnreal]
    rw [hx2, ← ENNReal.ofReal_add h1 (by positivity), ← ENNReal.ofReal_add (by positivity) h2,
      ENNReal.ofReal_lt_ofReal_iff (by positivity), ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff']
    constructor
    · intro h
      have hpos : 0 < s ^ 2 - R1 - R2 := by nlinarith [sq_nonneg (x : ℝ)]
      exact ⟨Real.lt_sqrt (NNReal.coe_nonneg x) |>.2 (by linarith), Real.sqrt_pos.2 hpos⟩
    · rintro ⟨h, -⟩
      have := (Real.lt_sqrt (NNReal.coe_nonneg x)).1 h
      linarith

variable {k r : ℕ}

theorem rho_lt (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (t : ℝ) :
    {m : Mt k r | rhoS k r S m < ENNReal.ofReal t} = expBall (k := k) (r := r) S t := by
  ext m
  simp only [Set.mem_setOf_eq, rhoS, iInf_lt_iff, expBall, Set.mem_image, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨Y, hY, hlt⟩
    refine ⟨Y, ?_, hY⟩
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_lt_ofReal_iff'] at hlt
    exact hlt.1
  · rintro ⟨Y, hlt, hY⟩
    refine ⟨Y, hY, ?_⟩
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_lt_ofReal_iff']
    exact ⟨hlt, lt_of_le_of_lt (norm_nonneg _) hlt⟩

theorem norm_lt {E : Type*} [NormedAddCommGroup E] (t : ℝ) :
    {Z : E | (‖Z‖₊ : ℝ≥0∞) < ENNReal.ofReal t} = Metric.ball 0 t := by
  ext Z
  simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_lt_ofReal_iff']
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, lt_of_le_of_lt (norm_nonneg _) h⟩

theorem measurableSet_expBall' (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (t : ℝ) :
    MeasurableSet (expBall (k := k) (r := r) S t) := by
  rcases lt_or_ge 0 t with ht | ht
  · exact measurableSet_expBall S t ht
  · have : Metric.ball (0 : Formalism.MainNotions.S.lieE S) t = ∅ := Metric.ball_eq_empty.2 ht
    unfold expBall; rw [this, Set.image_empty]; exact MeasurableSet.empty

theorem m_int (μb : Measure (Mt k r)) {R1 R2 s : ℝ} (hs : 0 < s) (h1 : 0 ≤ R1) (h2 : 0 ≤ R2) :
    ∫⁻ m, (if ENNReal.ofReal R1 + rhoS k r (Formalism.FourierDecayAlt.B2.UWb k r) m ^ 2 + ENNReal.ofReal R2 < ENNReal.ofReal (s ^ 2)
      then (1 : ℝ≥0∞) else 0) ∂μb =
      μb (expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) (Real.sqrt (s ^ 2 - R1 - R2))) := by
  rw [← rho_lt, ← lintegral_indicator_one (by rw [rho_lt]; exact measurableSet_expBall' _ _)]
  refine lintegral_congr fun m => ?_
  simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, sq_cond hs h1 h2]

theorem z_int {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] (ν : Measure E)
    {R1 R2 s : ℝ} (hs : 0 < s) (h1 : 0 ≤ R1) (h2 : 0 ≤ R2) :
    ∫⁻ Z, (if ENNReal.ofReal R1 + (‖Z‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal R2 < ENNReal.ofReal (s ^ 2)
      then (1 : ℝ≥0∞) else 0) ∂ν = ν (Metric.ball 0 (Real.sqrt (s ^ 2 - R1 - R2))) := by
  rw [← norm_lt, ← lintegral_indicator_one (by rw [norm_lt]; exact measurableSet_ball)]
  refine lintegral_congr fun Z => ?_
  simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, sq_cond hs h1 h2]

end Formalism.L2.SG.Pf.BH.VL

namespace Formalism.L2.SG.Pf.BH.VL

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

variable {k r : ℕ}

theorem gauge_bound {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (hμ : IsGaugeOn S μ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ →
      μ (expBall (k := k) (r := r) S t) ≤ ENNReal.ofReal (1 + ε) * volume (Metric.ball (0 : Formalism.MainNotions.S.lieE S) t) ∧
      ENNReal.ofReal (1 - ε) * volume (Metric.ball (0 : Formalism.MainNotions.S.lieE S) t) ≤ μ (expBall (k := k) (r := r) S t) := by
  have hT := hμ.2
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (μ (expBall (k := k) (r := r) S ρ)).toReal /
      (volume (Metric.ball (0 : Formalism.MainNotions.S.lieE S) ρ)).toReal ∈ Set.Ioo (1 - ε) (1 + ε) :=
    hT (Ioo_mem_nhds (by linarith) (by linarith))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hb⟩ := hev
  refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · have h1 : Metric.ball (0 : Formalism.MainNotions.S.lieE S) 0 = ∅ := Metric.ball_zero
    have h2 : expBall (k := k) (r := r) S 0 = ∅ := by unfold expBall; rw [h1, Set.image_empty]
    simp [h1, h2]
  have hmem := hb (by rw [Real.dist_eq, sub_zero, abs_of_pos htpos]; exact htδ) htpos
  set V := volume (Metric.ball (0 : Formalism.MainNotions.S.lieE S) t) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos _ _ htpos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
  set M := μ (expBall (k := k) (r := r) S t) with hM
  have hMt : M ≠ ⊤ := by
    intro h
    rw [h, ENNReal.toReal_top, zero_div] at hmem
    linarith [hmem.1]
  have hlo : (1 - ε) * V.toReal < M.toReal := by
    have := hmem.1; rwa [lt_div_iff₀ hVr] at this
  have hhi : M.toReal < (1 + ε) * V.toReal := by
    have := hmem.2; rwa [div_lt_iff₀ hVr] at this
  constructor
  · rw [← ENNReal.ofReal_toReal hMt, ← ENNReal.ofReal_toReal hVt, ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hhi.le
  · rw [← ENNReal.ofReal_toReal hMt, ← ENNReal.ofReal_toReal hVt, ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hlo.le

theorem cWeight_cont : Continuous (Formalism.FourierDecayAlt.B2.cWeight k r) := by
  unfold Formalism.FourierDecayAlt.B2.cWeight; fun_prop

theorem cWeight_one : Formalism.FourierDecayAlt.B2.cWeight k r 1 = 1 := by
  unfold Formalism.FourierDecayAlt.B2.cWeight; simp

theorem cw_bound {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ c : Fin r → ℂ, 2 * ∑ a, ‖c a - 1‖ ^ 2 < δ ^ 2 →
    |Formalism.FourierDecayAlt.B2.cWeight k r c - 1| < ε := by
  obtain ⟨η, hη, h⟩ := Metric.continuousAt_iff.1 (cWeight_cont (k := k) (r := r)).continuousAt ε hε
  refine ⟨η, hη, fun c hc => ?_⟩
  have hd : dist c 1 < η := by
    rw [dist_pi_lt_iff hη]
    intro a
    rw [dist_eq_norm, Pi.one_apply]
    have h1 : ‖c a - 1‖ ^ 2 ≤ ∑ b, ‖c b - 1‖ ^ 2 :=
      Finset.single_le_sum (f := fun b => ‖c b - 1‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
    nlinarith [norm_nonneg (c a - 1)]
  have := h hd
  rwa [cWeight_one, Real.dist_eq] at this

end Formalism.L2.SG.Pf.BH.VL

namespace Formalism.L2.SG.Pf.BH.VL

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

variable {k r : ℕ}

theorem lie_haar_nilradical_eq_map_exp : Formalism.MainNotions.S.haarLie (Nset k r) 1 = Measure.map (expL k r (Nset k r)) volume := by
  unfold Formalism.MainNotions.S.haarLie; rw [one_smul]; rfl

theorem meas_expL' : Measurable (expL k r (Nset k r)) :=
  (Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) (Nset k r)).measurable

theorem lintegral_lie_haar_nilradical (G : Mt k r → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ n, G n ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) = ∫⁻ Y : Formalism.MainNotions.S.lieE (Nset k r), G (expL k r (Nset k r) Y) := by
  rw [lie_haar_nilradical_eq_map_exp]; exact lintegral_map hG meas_expL'


def ind (c : Fin r → ℂ) (s : ℝ) (n m n' : Mt k r) : ℝ≥0∞ :=
  if Qf k r n c m n' < ENNReal.ofReal (s ^ 2) then 1 else 0

theorem meas_ind_gen {α : Type*} [MeasurableSpace α] (c : Fin r → ℂ) (s : ℝ) {f g h : α → Mt k r}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable fun a => ind (k := k) (r := r) c s (f a) (g a) (h a) := by
  have hN := rhoMeas k r (Nset k r)
  have hW := rhoMeas k r (Formalism.FourierDecayAlt.B2.UWb k r)
  have hQ : Measurable fun a => Qf k r (f a) c (g a) (h a) := by
    unfold Qf
    exact ((((hN.comp hf).pow_const 2).add measurable_const).add ((hW.comp hg).pow_const 2)).add
      ((hN.comp hh).pow_const 2)
  unfold ind
  exact Measurable.ite (measurableSet_lt hQ measurable_const) measurable_const measurable_const

theorem enn_sq' {E : Type*} [NormedAddCommGroup E] (y : E) : ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) :=
  Formalism.L2.SG.Pf.BH.Model.enn_sq y

theorem inner_eq (μb : Measure (Mt k r)) [SFinite μb] (c : Fin r → ℂ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ n, ∫⁻ m, ∫⁻ n', ind c s n m n' ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) =
      ∫⁻ Y : Formalism.MainNotions.S.lieE (Nset k r), ∫⁻ Y' : Formalism.MainNotions.S.lieE (Nset k r),
        μb (expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r)
          (Real.sqrt (s ^ 2 - (‖Y‖ ^ 2 + 2 * ∑ a, ‖c a - 1‖ ^ 2) - ‖Y'‖ ^ 2))) := by
  have : SFinite (Formalism.MainNotions.S.haarLie (Nset k r) 1) := by rw [lie_haar_nilradical_eq_map_exp]; infer_instance

  have hswap : ∀ n : Mt k r, ∫⁻ m, ∫⁻ n', ind c s n m n' ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb =
      ∫⁻ n', ∫⁻ m, ind c s n m n' ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) := by
    intro n
    refine lintegral_lintegral_swap ?_
    exact (meas_ind_gen c s (f := fun _ : Mt k r × Mt k r => n) (g := fun p => p.1) (h := fun p => p.2)
      measurable_const measurable_fst measurable_snd).aemeasurable
  simp_rw [hswap]
  have hG : Measurable fun n : Mt k r => ∫⁻ n', ∫⁻ m, ind c s n m n' ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) := by
    have h3 : Measurable fun p : (Mt k r × Mt k r) × Mt k r => ind (k := k) (r := r) c s p.1.1 p.2 p.1.2 :=
      meas_ind_gen c s (f := fun p : (Mt k r × Mt k r) × Mt k r => p.1.1) (g := fun p => p.2) (h := fun p => p.1.2)
        measurable_fst.fst measurable_snd measurable_fst.snd
    exact h3.lintegral_prod_right'.lintegral_prod_right'
  rw [lintegral_lie_haar_nilradical _ hG]
  refine lintegral_congr fun Y => ?_
  have hG' : Measurable fun n' : Mt k r => ∫⁻ m, ind c s (expL k r (Nset k r) Y) m n' ∂μb := by
    have h2 : Measurable fun p : Mt k r × Mt k r => ind (k := k) (r := r) c s (expL k r (Nset k r) Y) p.2 p.1 :=
      meas_ind_gen c s (f := fun _ : Mt k r × Mt k r => expL k r (Nset k r) Y) (g := fun p => p.2) (h := fun p => p.1)
        measurable_const measurable_snd measurable_fst
    exact h2.lintegral_prod_right'
  rw [lintegral_lie_haar_nilradical _ hG']
  refine lintegral_congr fun Y' => ?_
  have hB : 0 ≤ 2 * ∑ a, ‖c a - 1‖ ^ 2 := by positivity
  have e : ∀ m : Mt k r, ind c s (expL k r (Nset k r) Y) m (expL k r (Nset k r) Y') =
      if ENNReal.ofReal (‖Y‖ ^ 2 + 2 * ∑ a, ‖c a - 1‖ ^ 2) + rhoS k r (Formalism.FourierDecayAlt.B2.UWb k r) m ^ 2 +
        ENNReal.ofReal (‖Y'‖ ^ 2) < ENNReal.ofReal (s ^ 2) then 1 else 0 := by
    intro m
    unfold ind Qf
    rw [rhoN k r Y, rhoN k r Y', enn_sq', enn_sq', ← ENNReal.ofReal_add (by positivity) hB]
  simp_rw [e]
  exact m_int μb hs (by positivity) (by positivity)

end Formalism.L2.SG.Pf.BH.VL

namespace Formalism.L2.SG.Pf.BH.VL

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

variable {k r : ℕ}

theorem model_inner (E1 E2 : Type) [NormedAddCommGroup E1] [InnerProductSpace ℝ E1] [FiniteDimensional ℝ E1]
    [MeasurableSpace E1] [BorelSpace E1] [NormedAddCommGroup E2] [InnerProductSpace ℝ E2] [FiniteDimensional ℝ E2]
    [MeasurableSpace E2] [BorelSpace E2] (B : ℝ) (hB : 0 ≤ B) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y1 : E1, ∫⁻ y2 : E2, ∫⁻ y3 : E1,
      (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal B + (‖y2‖₊ : ℝ≥0∞) ^ 2 + (‖y3‖₊ : ℝ≥0∞) ^ 2 <
          ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) =
      ∫⁻ y1 : E1, ∫⁻ y3 : E1, volume (Metric.ball (0 : E2) (Real.sqrt (s ^ 2 - (‖y1‖ ^ 2 + B) - ‖y3‖ ^ 2))) := by
  refine lintegral_congr fun y1 => ?_
  have hmeas : Measurable fun p : E2 × E1 =>
      (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal B + (‖p.1‖₊ : ℝ≥0∞) ^ 2 + (‖p.2‖₊ : ℝ≥0∞) ^ 2 <
          ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) := by
    refine Measurable.ite (measurableSet_lt ?_ measurable_const) measurable_const measurable_const
    fun_prop
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun y3 => ?_
  have e : ∀ y2 : E2, (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal B + (‖y2‖₊ : ℝ≥0∞) ^ 2 + (‖y3‖₊ : ℝ≥0∞) ^ 2 <
      ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) =
      (if ENNReal.ofReal (‖y1‖ ^ 2 + B) + (‖y2‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal (‖y3‖ ^ 2) <
      ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) := by
    intro y2
    rw [enn_sq' y1, enn_sq' y3, ← ENNReal.ofReal_add (by positivity) hB]
  simp_rw [e]
  exact z_int volume hs (by positivity) (by positivity)

theorem ball_cast (a b : ℕ) (h : a = b) (s : ℝ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin a)) s) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin b)) s) := by
  subst h; rfl

theorem sqrt_sq_sub_le_self {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) : Real.sqrt (s ^ 2 - R) ≤ s := by
  calc Real.sqrt (s ^ 2 - R) ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = s := Real.sqrt_sq hs.le

end Formalism.L2.SG.Pf.BH.VL

namespace Formalism.L2.SG.Pf.BH.VL

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

variable {k r : ℕ}

theorem pt_bound {μb : Measure (Mt k r)} {ε δg δc s : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hg : ∀ t : ℝ, 0 ≤ t → t < δg →
      μb (expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) t) ≤
        ENNReal.ofReal (1 + ε) * volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) t) ∧
      ENNReal.ofReal (1 - ε) * volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) t) ≤
        μb (expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) t))
    (hc : ∀ c : Fin r → ℂ, 2 * ∑ a, ‖c a - 1‖ ^ 2 < δc ^ 2 → |Formalism.FourierDecayAlt.B2.cWeight k r c - 1| < ε)
    (hs : 0 < s) (hsg : s < δg) (hsc : s < δc) (c : Fin r → ℂ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
        μb (expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) (Real.sqrt (s ^ 2 - (u + 2 * ∑ a, ‖c a - 1‖ ^ 2) - v)))
      ≤ ENNReal.ofReal ((1 + ε) ^ 2) *
        volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r))
          (Real.sqrt (s ^ 2 - (u + 2 * ∑ a, ‖c a - 1‖ ^ 2) - v))) ∧
    ENNReal.ofReal ((1 - ε) ^ 2) *
        volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r))
          (Real.sqrt (s ^ 2 - (u + 2 * ∑ a, ‖c a - 1‖ ^ 2) - v)))
      ≤ ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
        μb (expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) (Real.sqrt (s ^ 2 - (u + 2 * ∑ a, ‖c a - 1‖ ^ 2) - v))) := by
  set B := 2 * ∑ a, ‖c a - 1‖ ^ 2 with hBdef
  have hB : 0 ≤ B := by positivity
  set t := Real.sqrt (s ^ 2 - (u + B) - v) with htdef
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le ht0 with ht | ht
  · rw [← ht]
    have h1 : Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) 0 = ∅ := Metric.ball_zero
    have h2 : expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) 0 = ∅ := by unfold expBall; rw [h1, Set.image_empty]
    simp [h1, h2]
  have hpos : 0 < s ^ 2 - (u + B) - v := Real.sqrt_pos.1 ht
  have hBs : B < δc ^ 2 := by nlinarith
  have hcw := hc c hBs
  have hts : t ≤ s := by
    have := sqrt_sq_sub_le_self (s := s) (R := u + B + v) hs (by positivity)
    rw [htdef]; convert this using 2; ring
  obtain ⟨hup, hlo⟩ := hg t ht0 (lt_of_le_of_lt hts hsg)
  rw [abs_lt] at hcw
  constructor
  · calc ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) * μb (expBall (Formalism.FourierDecayAlt.B2.UWb k r) t)
        ≤ ENNReal.ofReal (1 + ε) * (ENNReal.ofReal (1 + ε) *
            volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) t)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) hup
      _ = ENNReal.ofReal ((1 + ε) ^ 2) * volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) t) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith), sq]
  · calc ENNReal.ofReal ((1 - ε) ^ 2) * volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) t)
        = ENNReal.ofReal (1 - ε) * (ENNReal.ofReal (1 - ε) *
            volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) t)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith), sq]
      _ ≤ ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) * μb (expBall (Formalism.FourierDecayAlt.B2.UWb k r) t) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) hlo

end Formalism.L2.SG.Pf.BH.VL

namespace Formalism.L2.SG.Pf.BH.VL

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

variable {k r : ℕ}

theorem const_mul_double_lintegral {X : Type*} [MeasurableSpace X] (μ : Measure X) (a : ℝ≥0∞) (ha : a ≠ ⊤) (f : X → X → ℝ≥0∞) :
    a * ∫⁻ Y, ∫⁻ Y', f Y Y' ∂μ ∂μ = ∫⁻ Y, ∫⁻ Y', a * f Y Y' ∂μ ∂μ := by
  rw [← lintegral_const_mul' _ _ ha]
  refine lintegral_congr fun Y => ?_
  rw [← lintegral_const_mul' _ _ ha]

theorem volLim : VolLim := by
  intro k r μb hμb
  have sμ : SigmaFinite μb := hμb.1.1
  set D := 2 * Module.finrank ℝ (Formalism.MainNotions.S.lieE (Nset k r)) + 2 * r +
    Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) with hD
  set L : ℝ := ((2 : ℝ) ^ r)⁻¹ with hLdef
  have hL : 0 < L := by positivity
  set W : ℝ → ℝ≥0∞ := fun s => volume (Metric.ball (0 : EuclideanSpace ℝ (Fin D)) s) with hWdef
  have hVol : ∀ s, 0 < s → Vol k r μb s = ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
      ∫⁻ Y : Formalism.MainNotions.S.lieE (Nset k r), ∫⁻ Y' : Formalism.MainNotions.S.lieE (Nset k r),
        μb (expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r)
          (Real.sqrt (s ^ 2 - (‖Y‖ ^ 2 + 2 * ∑ a, ‖c a - 1‖ ^ 2) - ‖Y'‖ ^ 2))) := by
    intro s hs
    unfold Vol
    refine lintegral_congr fun c => ?_
    congr 1
    exact inner_eq μb c hs
  have hMod : ∀ s, 0 < s → ∫⁻ c : Fin r → ℂ, ∫⁻ Y : Formalism.MainNotions.S.lieE (Nset k r), ∫⁻ Y' : Formalism.MainNotions.S.lieE (Nset k r),
      volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r))
        (Real.sqrt (s ^ 2 - (‖Y‖ ^ 2 + 2 * ∑ a, ‖c a - 1‖ ^ 2) - ‖Y'‖ ^ 2))) = ENNReal.ofReal L * W s := by
    intro s hs
    rw [hWdef, hLdef, ← Model.modelVol _ _ r s hs]
    refine lintegral_congr fun c => ?_
    exact (model_inner _ _ _ (by positivity) hs).symm
  have hgV : ∀ s, gVol k r s = (W s).toReal := by
    intro s
    unfold gVol
    rw [ballDim, ball_cast _ D (Sw.dimG k r) s]
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal ((1 - ε) ^ 2) * (ENNReal.ofReal L * W s) ≤ Vol k r μb s ∧
      Vol k r μb s ≤ ENNReal.ofReal ((1 + ε) ^ 2) * (ENNReal.ofReal L * W s) := by
    intro ε hε hε1
    obtain ⟨δg, hδg, hg⟩ := gauge_bound hμb hε hε1
    obtain ⟨δc, hδc, hc⟩ := cw_bound (k := k) (r := r) hε
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδg hδc)] with s ⟨hs0, hsδ⟩
    have hsg : s < δg := lt_of_lt_of_le hsδ (min_le_left _ _)
    have hsc : s < δc := lt_of_lt_of_le hsδ (min_le_right _ _)
    rw [hVol s hs0, ← hMod s hs0]
    constructor
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun c => ?_
      rw [const_mul_double_lintegral _ _ ENNReal.ofReal_ne_top, const_mul_double_lintegral _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun Y => lintegral_mono fun Y' => ?_
      exact (pt_bound hε hε1 hg hc hs0 hsg hsc c _ _ (by positivity) (by positivity)).2
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun c => ?_
      rw [const_mul_double_lintegral _ _ ENNReal.ofReal_ne_top, const_mul_double_lintegral _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun Y => lintegral_mono fun Y' => ?_
      exact (pt_bound hε hε1 hg hc hs0 hsg hsc c _ _ (by positivity) (by positivity)).1
  have hWpos : ∀ s, 0 < s → 0 < (W s).toReal := fun s hs =>
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hs).ne' measure_ball_lt_top.ne
  have hWt : ∀ s, W s ≠ ⊤ := fun s => measure_ball_lt_top.ne
  have toR : ∀ (a : ℝ) (ha : 0 ≤ a) (s : ℝ), (ENNReal.ofReal a * (ENNReal.ofReal L * W s)).toReal = a * L * (W s).toReal := by
    intro a ha s
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hL.le, mul_assoc]
  rw [tendsto_order]
  constructor
  · intro a ha
    set ε := min (1 / 2) ((L - a) / (4 * L)) with hε
    have hε0 : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεa : ε ≤ (L - a) / (4 * L) := min_le_right _ _
    have hgt : a < (1 - ε) ^ 2 * L := by
      have h1 : 1 - 2 * ε ≤ (1 - ε) ^ 2 := by nlinarith
      have h2 : 2 * ε * L ≤ (L - a) / 2 := by
        have := mul_le_mul_of_nonneg_right hεa (by positivity : (0 : ℝ) ≤ 2 * L)
        rw [div_mul_eq_mul_div] at this
        have e : (L - a) * (2 * L) / (4 * L) = (L - a) / 2 := by field_simp; ring
        nlinarith
      nlinarith
    filter_upwards [key ε hε0 hε1, self_mem_nhdsWithin] with s ⟨hlo, hup⟩ hs
    have hVt : Vol k r μb s ≠ ⊤ := ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top, hWt]) hup
    rw [hgV s, lt_div_iff₀ (hWpos s hs)]
    have := ENNReal.toReal_mono hVt hlo
    rw [toR _ (sq_nonneg _) s] at this
    nlinarith [hWpos s hs]
  · intro b hb
    set ε := min (1 / 2) ((b - L) / (4 * L)) with hε
    have hε0 : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεb : ε ≤ (b - L) / (4 * L) := min_le_right _ _
    have hεh : ε ≤ 1 / 2 := min_le_left _ _
    have hlt : (1 + ε) ^ 2 * L < b := by
      have h1 : (1 + ε) ^ 2 ≤ 1 + 3 * ε := by nlinarith
      have h2 : 3 * ε * L ≤ 3 * (b - L) / 4 := by
        have := mul_le_mul_of_nonneg_right hεb (by positivity : (0 : ℝ) ≤ 3 * L)
        have e : (b - L) / (4 * L) * (3 * L) = 3 * (b - L) / 4 := by field_simp
        nlinarith
      nlinarith
    filter_upwards [key ε hε0 hε1, self_mem_nhdsWithin] with s ⟨hlo, hup⟩ hs
    rw [hgV s, div_lt_iff₀ (hWpos s hs)]
    have := ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top, hWt]) hup
    rw [toR _ (sq_nonneg _) s] at this
    nlinarith [hWpos s hs]

end Formalism.L2.SG.Pf.BH.VL
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.GE

theorem jacGauge_of_hearts3 (hS : Sandwich) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : JacGauge :=
  jacGauge_of_sandwich_gaugeMeasure hS VL.volLim hU hL

end Formalism.L2.SG.Pf
end
end

section
namespace Formalism.L2.SG.Pf.GE

theorem existsGaugeNormalizedStabilizer : ExistsGaugeMeasureForEachRank := (show PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank ↔ ExistsGaugeMeasureForEachRank from Iff.rfl).mp _root_.exists_gaugeNormalizedStabilizer

end Formalism.L2.SG.Pf.GE
end

section
noncomputable section

namespace Formalism.L2.SG.Pf

theorem jacGauge_of_sandwich_rhsWLim (hS : BH.Sandwich) (hL : WB.RhsWLim) : JacGauge :=
  jacGauge_of_hearts3 hS GE.existsGaugeNormalizedStabilizer hL

end Formalism.L2.SG.Pf
end
end

section
namespace Formalism.L2.SG.Pf.BH

theorem sandwich' : Sandwich := by
  refine sandwich_of_chart Sw.lieG' Sw.lieWb' gauss_sum_unique phi_form' big_cell_g
    (phiDeriv_of Sw.w0Sq) Sw.lIso Sw.w0Sq ?_ ?_
  · unfold PI.SwSand.LieEN
    intros
    exact Formalism.MainNotions.BridgeCSB.lieE_N
  · intros
    apply Formalism.MainNotions.BridgeCSB.exp_mem_N

end Formalism.L2.SG.Pf.BH
end

section
noncomputable section

namespace Formalism.L2.SG.Pf

theorem jacGauge_of_rhsW (hL : WB.RhsWLim) : JacGauge := jacGauge_of_sandwich_rhsWLim BH.sandwich' hL

end Formalism.L2.SG.Pf
end
end
