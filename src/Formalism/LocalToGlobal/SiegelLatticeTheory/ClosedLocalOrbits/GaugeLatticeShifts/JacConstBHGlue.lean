import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGEB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR

section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

variable {k r : ℕ}

def ItgSwap : Prop :=
  ∀ (k r : ℕ) (νN νb : Measure (Mt k r)), Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) νN →
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) νb →
    ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (f : Mt k r → ℝ≥0∞), Measurable f →
    (∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1.2) ∂((νN.prod νN).prod νb)) =
      ∫⁻ n, ∫⁻ m, ∫⁻ n', f (fun i j => (Matrix.of n * g * Matrix.of m * (Matrix.of n')⁻¹) i j) ∂νN ∂νb ∂νN

end Formalism.L2.SG.Pf.BH
end
end

section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.WB

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem wbConst_pos {k : ℕ} {T T' a a' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : 0 < a) (ha' : 0 < a') :
    0 < wbConst k T T' a a' := by
  unfold wbConst
  have h1 : ∀ j, 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU j := fun j => by
    unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
    exact Finset.prod_pos fun i _ => by positivity
  have := h1 k
  have := h1 (k - 1)
  positivity

theorem wbHaar_of (hI : RankGauge) (hS : GaugeShiftW) (hR : RhsWLim) : WbHaar := by
  intro k r z z' hk hz hz' hT hT' μb μW μW' hμb hW hW' a a' ha ha' hma hma' μsec hsec φ hφ
  have D : WbData k r z z' μW μW' a a' μsec := ⟨hk, hz, hz', hT, hT', hW, hW', ha, ha', hma, hma', hsec⟩
  obtain ⟨C, hC, hF⟩ := hI k r z z' μb μW μW' a a' μsec D hμb
  have hlim1 : Tendsto (fun ρ : ℝ => (μb (bBall k r ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1) := hμb.2
  have hlim2 := (hR k r z z' μW μW' a a' μsec D).const_mul (C : ℝ)
  have heq : ∀ᶠ ρ in 𝓝[>] (0:ℝ), (μb (bBall k r ρ)).toReal / bVol k r ρ =
      (C : ℝ) * ((rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    obtain ⟨hm, he⟩ := hS k r z z' μb μW μW' a a' μsec D hμb.1 ρ hρ
    have h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂μb = μb (mBall k r z z' μsec ρ) :=
      lintegral_indicator_one hm
    have h2 := hF _ (measurable_one.indicator hm)
    rw [h1, he] at h2
    rw [h2, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc]
  have hu := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have hw := wbConst_pos (k := k) hT hT' ha ha'
  have hCr : (C : ℝ) = wbConst k (Tz k r z) (Tz k r z') a a' := by
    field_simp at hu
    linarith
  have hCe : (C : ℝ≥0∞) = ENNReal.ofReal (wbConst k (Tz k r z) (Tz k r z') a a') := by
    rw [← hCr, ENNReal.ofReal_coe_nnreal]
  rw [hF φ hφ, hCe]
  rfl

end Formalism.L2.SG.Pf.WB
end
end

section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Classical
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

abbrev dG (k r : ℕ) : ℕ := Module.finrank ℝ (Formalism.MainNotions.S.lieE (UH (Hpk k r)))

theorem gVol_mul (k r : ℕ) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    gVol k r (a * s) = a ^ dG k r * gVol k r s := by
  unfold gVol
  rw [Measure.addHaar_ball_mul_of_pos volume _ ha, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem gVol_pos (k r : ℕ) {s : ℝ} (hs : 0 < s) : 0 < gVol k r s := by
  unfold gVol
  exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hs).ne' measure_ball_lt_top.ne

theorem rhs_bounds (hW : Sandwich) (k r : ℕ) (μb : Measure (Mt k r))
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      Vol k r μb ((1 - ε) * ρ) ≤ rhs k r μb ((wBall k r ρ).indicator 1) ∧
      rhs k r μb ((wBall k r ρ).indicator 1) ≤ Vol k r μb ((1 + ε) * ρ) := by
  obtain ⟨δ, hδ, hW'⟩ := hW k r ε hε0 hε1
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hN : ∀ᵐ x ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1), Matrix.of x ∈ Nset k r :=
    ae_iff.2 (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top).2.2.1
  have hB : ∀ᵐ x ∂μb, Matrix.of x ∈ Formalism.FourierDecayAlt.B2.UWb k r := ae_iff.2 hμb.1.2.2.1
  constructor
  · unfold Vol rhs
    refine lintegral_mono fun c => mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine lintegral_mono_ae (hN.mono fun n hn => ?_)
    refine lintegral_mono_ae (hB.mono fun m hm => ?_)
    refine lintegral_mono_ae (hN.mono fun n' hn' => ?_)
    split_ifs with hQ
    · have hx : (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j : Mt k r) ∈
          wBall k r ρ := (hW' ρ hρ hρδ n c m n' hn hm hn').2 hQ
      rw [Set.indicator_apply, if_pos hx, Pi.one_apply]
    · exact zero_le
  · unfold Vol rhs
    refine lintegral_mono fun c => mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine lintegral_mono_ae (hN.mono fun n hn => ?_)
    refine lintegral_mono_ae (hB.mono fun m hm => ?_)
    refine lintegral_mono_ae (hN.mono fun n' hn' => ?_)
    by_cases hx : (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j : Mt k r) ∈
        wBall k r ρ
    · have hQ := (hW' ρ hρ hρδ n c m n' hn hm hn').1 hx
      rw [Set.indicator_apply, if_pos hx, Pi.one_apply, if_pos hQ]
    · rw [Set.indicator_apply, if_neg hx]
      exact zero_le

theorem scale_lim (hV : VolLim) (k r : ℕ) (μb : Measure (Mt k r))
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ρ : ℝ => (Vol k r μb (a * ρ)).toReal / gVol k r ρ) (𝓝[>] 0)
      (𝓝 (((2 : ℝ) ^ r)⁻¹ * a ^ dG k r)) := by
  have hsc : Tendsto (fun ρ : ℝ => a * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := ((continuous_const_mul a).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact mul_pos ha hρ
  have h1 := ((hV k r μb hμb).comp hsc).mul_const (a ^ dG k r)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hg := gVol_pos k r (s := ρ) hρ
  have ha' : a ^ dG k r ≠ 0 := pow_ne_zero _ ha.ne'
  simp only [Function.comp]
  rw [gVol_mul k r ha ρ]
  field_simp

theorem rhsLim_of (hW : Sandwich) (hV : VolLim) : RhsLim := by
  intro k r μb hμb
  set L : ℝ := ((2 : ℝ) ^ r)⁻¹ with hLdef
  have hL : 0 < L := by positivity

  have hfin : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), rhs k r μb ((wBall k r ρ).indicator 1) ≠ ∞ := by
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := 1 / 2) (by norm_num) (by norm_num)
    have h := scale_lim hV k r μb hμb (a := 1 + 1 / 2) (by norm_num)
    have hpos := (tendsto_order.1 h).1 0 (by positivity)
    filter_upwards [hpos, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h1 h2 h3
    have hg := gVol_pos k r (s := ρ) h2
    have h4 : 0 < (Vol k r μb ((1 + 1 / 2) * ρ)).toReal := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : (Vol k r μb ((1 + 1 / 2) * ρ)).toReal / gVol k r ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hg.le
      linarith
    exact ne_top_of_le_ne_top (ENNReal.toReal_pos_iff.1 h4).2.ne (hb ρ h2 h3).2
  rw [tendsto_order]
  constructor
  · intro a haL
    have hc : Tendsto (fun ε : ℝ => L * (1 - ε) ^ dG k r) (𝓝[>] 0) (𝓝 L) := by
      have : Continuous (fun ε : ℝ => L * (1 - ε) ^ dG k r) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨h1, h2⟩, h0⟩ :=
      (((tendsto_order.1 hc).1 a haL).and ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds)
        |>.and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := ε) h0 h2
    have h := scale_lim hV k r μb hμb (a := 1 - ε) (by linarith)
    have hlo := (tendsto_order.1 h).1 a (by simpa [mul_comm] using h1)
    filter_upwards [hlo, hfin, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h3 h4 h5 h6
    have hg := gVol_pos k r (s := ρ) h5
    refine lt_of_lt_of_le h3 (div_le_div_of_nonneg_right ?_ hg.le)
    exact ENNReal.toReal_mono h4 (hb ρ h5 h6).1
  · intro b hbL
    have hc : Tendsto (fun ε : ℝ => L * (1 + ε) ^ dG k r) (𝓝[>] 0) (𝓝 L) := by
      have : Continuous (fun ε : ℝ => L * (1 + ε) ^ dG k r) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨h1, h2⟩, h0⟩ :=
      (((tendsto_order.1 hc).2 b hbL).and ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds)
        |>.and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := ε) h0 h2
    have h := scale_lim hV k r μb hμb (a := 1 + ε) (by linarith)
    have hup := (tendsto_order.1 h).2 b (by simpa [mul_comm] using h1)
    have hpos := (tendsto_order.1 h).1 0 (by positivity)
    filter_upwards [hup, hpos, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h3 h3' h5 h6
    have hg := gVol_pos k r (s := ρ) h5
    have h4 : 0 < (Vol k r μb ((1 + ε) * ρ)).toReal := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : (Vol k r μb ((1 + ε) * ρ)).toReal / gVol k r ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hg.le
      linarith
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ hg.le) h3
    exact ENNReal.toReal_mono (ENNReal.toReal_pos_iff.1 h4).2.ne (hb ρ h5 h6).2

end Formalism.L2.SG.Pf.BH
end
end

section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem bruhatHaar_of (hI : IterGauge) (hS : GaugeShift) (hR : RhsLim) : BruhatHaar := by
  intro k r μ μb hμ hμb φ hφ
  obtain ⟨C, hC, hF⟩ := hI k r μ μb hμ hμb
  have hlim1 : Tendsto (fun ρ : ℝ => (μ (gBall k r ρ)).toReal / gVol k r ρ) (𝓝[>] 0) (𝓝 1) := hμ.2
  have hlim2 := (hR k r μb hμb).const_mul (C : ℝ)
  have heq : ∀ᶠ ρ in 𝓝[>] (0:ℝ), (μ (gBall k r ρ)).toReal / gVol k r ρ =
      (C : ℝ) * ((rhs k r μb ((wBall k r ρ).indicator 1)).toReal / gVol k r ρ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    obtain ⟨hm, he⟩ := hS k r μ hμ.1 ρ hρ
    have h1 : ∫⁻ x, (wBall k r ρ).indicator 1 x ∂μ = μ (wBall k r ρ) := lintegral_indicator_one hm
    have h2 := hF _ (measurable_one.indicator hm)
    rw [h1, he] at h2
    rw [h2, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc]
  have hu := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have h2r : (0:ℝ) < 2 ^ r := by positivity
  have hCr : (C : ℝ) = 2 ^ r := by
    field_simp at hu
    linarith
  have hCe : (C : ℝ≥0∞) = ENNReal.ofReal (2 ^ r) := by
    rw [← hCr, ENNReal.ofReal_coe_nnreal]
  rw [hF φ hφ, hCe]
  rfl

theorem bruhatHaar_of_iterGauge (hI : IterGauge) (hS : GaugeShift) (hW : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of hI hS (rhsLim_of hW hV)

end Formalism.L2.SG.Pf.BH
end
end

section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB

theorem isHaarOn_smul {k r : ℕ} {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {ν : Measure (Mt k r)} (h : Formalism.MainNotions.S.IsHaarOn S ν) {c : NNReal} (hc : 0 < c) :
    Formalism.MainNotions.S.IsHaarOn S (c • ν) := by
  obtain ⟨hσ, h0, hconc, hl⟩ := h
  have := hσ
  refine ⟨inferInstance, ?_, ?_, fun s hs => ?_⟩
  · intro h
    apply h0
    exact (smul_eq_zero.1 h).resolve_left hc.ne'
  · rw [Measure.smul_apply, hconc, smul_zero]
  · rw [Measure.map_smul, hl s hs]

theorem toReal_smul_apply {α : Type*} [MeasurableSpace α] (c : NNReal) (ν : Measure α) (A : Set α) :
    ((c • ν) A).toReal = (c : ℝ) * (ν A).toReal := by
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

theorem gaugeWb_of (hRW : RhsWHaar) (hD : WbDataEx) (hU : ExistsGaugeMeasureForEachRank) (hSW : GaugeShiftW) (hLW : RhsWLim) :
    ∀ k r : ℕ, ∃ μ : Measure (Mt k r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μ := by
  intro k r
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hU r
  obtain ⟨z, z', μW, μW', a, a', μsec, D⟩ := hD k r hk
  obtain ⟨ν, hν, hνφ⟩ := hRW k r z z' μW μW' a a' μsec D
  have hw := wbConst_pos (k := k) D.T_pos D.T'_pos D.a_pos D.a'_pos
  set w := wbConst k (Tz k r z) (Tz k r z') a a' with hwdef
  refine ⟨(Real.toNNReal w) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 hw), ?_⟩
  have hlim := (hLW k r z z' μW μW' a a' μsec D).const_mul w
  rw [mul_inv_cancel₀ hw.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  obtain ⟨hm, he⟩ := hSW k r z z' ν μW μW' a a' μsec D hν ρ hρ
  have h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂ν = ν (mBall k r z z' μsec ρ) :=
    lintegral_indicator_one hm
  have h2 := hνφ _ (measurable_one.indicator hm)
  rw [h1, he] at h2
  show _ = ((Real.toNNReal w • ν) (bBall k r ρ)).toReal / bVol k r ρ
  rw [toReal_smul_apply, h2, Real.coe_toNNReal _ hw.le, mul_div_assoc]

theorem gaugeExists_of (hR : RhsHaar) (hRW : RhsWHaar) (hD : WbDataEx) (hU : ExistsGaugeMeasureForEachRank) (hS : GaugeShift)
    (hSW : GaugeShiftW) (hL : RhsLim) (hLW : RhsWLim) : GaugeExists := by
  intro k r
  have hb := gaugeWb_of hRW hD hU hSW hLW k r
  refine ⟨?_, hb⟩
  obtain ⟨μb, hμb⟩ := hb
  obtain ⟨ν, hν, hνφ⟩ := hR k r μb hμb
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  refine ⟨(Real.toNNReal (2 ^ r)) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 h2r), ?_⟩
  have hlim := (hL k r μb hμb).const_mul ((2 : ℝ) ^ r)
  rw [mul_inv_cancel₀ h2r.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  obtain ⟨hm, he⟩ := hS k r ν hν ρ hρ
  have h1 : ∫⁻ x, (wBall k r ρ).indicator 1 x ∂ν = ν (wBall k r ρ) := lintegral_indicator_one hm
  have h2 := hνφ _ (measurable_one.indicator hm)
  rw [h1, he] at h2
  show _ = ((Real.toNNReal (2 ^ r) • ν) (gBall k r ρ)).toReal / gVol k r ρ
  rw [toReal_smul_apply, h2, Real.coe_toNNReal _ h2r.le, mul_div_assoc]

theorem iterGauge_of (hR : RhsHaar) : IterGauge := by
  intro k r μ μb hμ hμb
  obtain ⟨ν, hν, hνφ⟩ := hR k r μb hμb
  obtain ⟨ν0, h0⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨c1, hc1, hc1', e1⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hμ.1
  obtain ⟨c2, hc2, hc2', e2⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hν
  have hne : c1 / c2 ≠ ∞ := (ENNReal.div_lt_top hc1' hc2).ne
  refine ⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne,
    fun φ hφ => ?_⟩
  rw [ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_mul_cancel hc2 hc2']

theorem rankGauge_of (hRW : RhsWHaar) : RankGauge := by
  intro k r z z' μb μW μW' a a' μsec D hμb
  obtain ⟨ν, hν, hνφ⟩ := hRW k r z z' μW μW' a a' μsec D
  obtain ⟨ν0, h0⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  obtain ⟨c1, hc1, hc1', e1⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hμb.1
  obtain ⟨c2, hc2, hc2', e2⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hν
  have hne : c1 / c2 ≠ ∞ := (ENNReal.div_lt_top hc1' hc2).ne
  refine ⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne,
    fun φ hφ => ?_⟩
  rw [ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_mul_cancel hc2 hc2']

theorem bruhatHaar_of_rhsHaar (hR : RhsHaar) (hS : GaugeShift) (hW : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of_iterGauge (iterGauge_of hR) hS hW hV

theorem wbHaar_of_rhsWHaar (hRW : RhsWHaar) (hSW : GaugeShiftW) (hLW : RhsWLim) : WbHaar :=
  wbHaar_of (rankGauge_of hRW) hSW hLW

end Formalism.L2.SG.Pf.GE
end
end

section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Jac

variable {k r : ℕ}

theorem skHaar_of_cs {U : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : Formalism.MainNotions.S.IsHaarOn U μ :=
  ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩

def fA (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r) : Mt k r :=
  fun i j => ((Matrix.of a)⁻¹ * g * Matrix.of m * Matrix.of b) i j

def fB (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r) : Mt k r :=
  fun i j => (Matrix.of a * g * Matrix.of m * (Matrix.of b)⁻¹) i j

theorem meas_fA (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable fun p : (Mt k r × Mt k r) × Mt k r => fA g p.1.1 p.1.2 p.2 := by
  have e : (fun p : (Mt k r × Mt k r) × Mt k r => fA g p.1.1 p.1.2 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of
        (fun i j => ((Matrix.of p.1.1)⁻¹) i j : Mt k r) * Matrix.of (g : Mt k r)) i j : Mt k r) *
        Matrix.of p.2) i j : Mt k r) * Matrix.of p.1.2) i j : Mt k r) := by
    funext p; rfl
  rw [e]
  exact mulMt_meas (mulMt_meas (mulMt_meas (invMt_meas (measurable_fst.comp measurable_fst)) measurable_const)
    measurable_snd) (measurable_snd.comp measurable_fst)

theorem meas_fB (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable fun p : (Mt k r × Mt k r) × Mt k r => fB g p.1.1 p.1.2 p.2 := by
  have e : (fun p : (Mt k r × Mt k r) × Mt k r => fB g p.1.1 p.1.2 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of p.1.1 * Matrix.of (g : Mt k r)) i j : Mt k r) *
        Matrix.of p.2) i j : Mt k r) * Matrix.of (fun i j => ((Matrix.of p.1.2)⁻¹) i j : Mt k r)) i j : Mt k r) := by
    funext p; rfl
  rw [e]
  exact mulMt_meas (mulMt_meas (mulMt_meas (measurable_fst.comp measurable_fst) measurable_const) measurable_snd)
    (invMt_meas (measurable_snd.comp measurable_fst))

theorem meas_fA_slice (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun p : Mt k r × Mt k r => f (fA g a0 p.1 p.2) := by
  let P : Mt k r × Mt k r → Mt k r := fun p =>
    ((Matrix.of a0)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  have hP : Continuous P := by
    show Continuous fun p : Mt k r × Mt k r =>
      ((Matrix.of a0)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    fun_prop
  exact hf.comp hP.measurable

theorem meas_fB_slice (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun p : Mt k r × Mt k r => f (fB g a0 p.1 p.2) :=
  hf.comp (meas_PQinv (fun p : Mt k r × Mt k r => Matrix.of a0 * g * Matrix.of p.2) (fun p => Matrix.of p.1)
    (by fun_prop) (by fun_prop))

theorem fA_inv (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r)
    (ha : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det) :
    fA g (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) m = fB g a b m := by
  have h1 : ((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ = Matrix.of a :=
    Matrix.nonsing_inv_nonsing_inv _ ha
  show (fun i j => (((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ * g * Matrix.of m *
      (Matrix.of b)⁻¹) i j : Mt k r) = fun i j => (Matrix.of a * g * Matrix.of m * (Matrix.of b)⁻¹) i j
  rw [h1]

theorem itgSwap : ItgSwap := by
  intro k r νN νb hN hb g f hf
  have sN := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN
  have sb := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hb
  have hinv : νN.map Formalism.FourierDecayAlt.B2.invM = νN :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) νN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
  have hA := hf.comp (meas_fA (k := k) (r := r) g)
  have hB := hf.comp (meas_fB (k := k) (r := r) g)
  have e0 : (fun p : (Mt k r × Mt k r) × Mt k r => f ((Matrix.of p.1.1)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1.2)) =
      fun p => f (fA g p.1.1 p.1.2 p.2) := by funext p; rfl
  rw [e0, lintegral_prod (fun p : (Mt k r × Mt k r) × Mt k r => f (fA g p.1.1 p.1.2 p.2)) hA.aemeasurable]
  rw [lintegral_prod (fun q : Mt k r × Mt k r => ∫⁻ m, f (fA g q.1 q.2 m) ∂νb)
    (hA.lintegral_prod_right' (ν := νb)).aemeasurable]

  have key : ∀ F : Mt k r → ℝ≥0∞, Measurable F → ∫⁻ a, F a ∂νN = ∫⁻ a, F (Formalism.FourierDecayAlt.B2.invM a) ∂νN := by
    intro F hF
    conv_lhs => rw [← hinv]
    exact lintegral_map hF Formalism.FourierDecayAlt.P.B2x1.invM_meas
  have hF : Measurable fun a : Mt k r => ∫⁻ b, ∫⁻ m, f (fA g a b m) ∂νb ∂νN :=
    (hA.lintegral_prod_right' (ν := νb)).lintegral_prod_right' (ν := νN)
  refine (key _ hF).trans ?_
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ a ∂νN, (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r :=
    ae_iff.2 hN.conc
  filter_upwards [hae] with a ha
  have hau : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det := unit_of_UH ha.1
  have hG : Measurable fun b : Mt k r => ∫⁻ m, f (fA g (Formalism.FourierDecayAlt.B2.invM a) b m) ∂νb := by
    exact (meas_fA_slice g (Formalism.FourierDecayAlt.B2.invM a) hf).lintegral_prod_right'
  refine (key _ hG).trans ?_
  have e1 : ∀ b m : Mt k r, f (fA g (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) m) = f (fB g a b m) :=
    fun b m => by rw [fA_inv g a b m hau]
  simp_rw [e1]
  refine lintegral_lintegral_swap ?_
  exact (meas_fB_slice g a hf).aemeasurable

end Formalism.L2.SG.Pf.BH

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

theorem rhsHaar : RhsHaar := by
  intro k r μb hμb
  obtain ⟨νG, hG⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨νN, hN⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  obtain ⟨νb, hb⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  obtain ⟨C, hC, hI⟩ := Formalism.FourierDecayAlt.P.iterated_integration_formula k r νG νN νb hG hN hb
  obtain ⟨cb, cb0, cbt, hμB⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) hb hμb.1
  obtain ⟨cN, cN0, cNt, hμN⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
    (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top)
  set D : ℝ≥0∞ := cN * cb * cN with hD
  have hD0 : D ≠ 0 := by simp [hD, cN0, cb0]
  have hDt : D ≠ ∞ := by simp [hD, ENNReal.mul_eq_top, cNt, cbt]
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  set E : ℝ≥0∞ := D / (C : ℝ≥0∞) with hE
  have hEt : E ≠ ∞ := ENNReal.div_ne_top hDt hC0
  have hE0 : E ≠ 0 := ENNReal.div_ne_zero.2 ⟨hD0, ENNReal.coe_ne_top⟩
  refine ⟨E.toNNReal • νG, isHaarOn_smul (skHaar_of_cs hG) (ENNReal.toNNReal_pos hE0 hEt), fun φ hφ => ?_⟩
  have hR : rhs k r μb φ = D * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
      ∫⁻ n, ∫⁻ m, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j)
        ∂νN ∂νb ∂νN := by
    unfold rhs
    rw [← lintegral_const_mul' _ _ hDt]
    refine lintegral_congr fun c => ?_
    rw [hμN, hμB]
    simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ cNt, lintegral_const_mul' _ _ cbt]
    simp_rw [lintegral_const_mul' _ _ cNt]
    rw [hD]
    ring
  rw [hR, lintegral_smul_measure, hI φ hφ]
  simp_rw [← itgSwap k r νN νb hN hb _ φ hφ]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal hEt, hE, ← mul_assoc, ENNReal.div_mul_cancel hC0 ENNReal.coe_ne_top]

end Formalism.L2.SG.Pf.GE

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

variable {k r : ℕ}

theorem ball_eq_iUnion {E : Type*} [NormedAddCommGroup E] (ρ : ℝ) (hρ : 0 < ρ) :
    Metric.ball (0 : E) ρ = ⋃ n : ℕ, Metric.closedBall (0 : E) (ρ - ρ / (n + 2)) := by
  ext x
  simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (ρ / (ρ - ‖x‖))
    refine ⟨n, ?_⟩
    have h1 : 0 < ρ - ‖x‖ := by linarith
    have h2 : ρ / (ρ - ‖x‖) < (n : ℝ) + 2 := by linarith
    have h3 : ρ / ((n : ℝ) + 2) < ρ - ‖x‖ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at h2
      linarith
    linarith
  · rintro ⟨n, hn⟩
    have : 0 < ρ / ((n : ℝ) + 2) := by positivity
    linarith

theorem measurableSet_expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) (hρ : 0 < ρ) :
    MeasurableSet (expBall (k := k) (r := r) S ρ) := by
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S
  unfold expBall
  rw [ball_eq_iUnion ρ hρ, Set.image_iUnion]
  refine MeasurableSet.iUnion fun n => ?_
  exact ((isCompact_closedBall _ _).image hE).isClosed.measurableSet

theorem long_weyl_element_mem : w0B k r ∈ UH (Hpk k r) :=
  Formalism.QuantumDeterminants.bigCellMem k r 1 1 (fun a => one_ne_zero) (by simp)

theorem gaugeShift : GaugeShift := by
  intro k r μ hμ ρ hρ
  have hg : MeasurableSet (gBall k r ρ) := measurableSet_expBall (k := k) (r := r) (UH (Hpk k r)) ρ hρ
  have hl : Measurable (lmulM (k := k) (r := r) (w0B k r)) := by
    have : Continuous (lmulM (k := k) (r := r) (w0B k r)) := by
      show Continuous fun x : Mt k r =>
        (w0B k r * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have e : wBall k r ρ = lmulM (w0B k r) ⁻¹' gBall k r ρ := rfl
  refine ⟨e ▸ hl hg, ?_⟩
  rw [e, ← Measure.map_apply hl hg, hμ.2.2.2 _ long_weyl_element_mem]

end Formalism.L2.SG.Pf.BH
end
end
