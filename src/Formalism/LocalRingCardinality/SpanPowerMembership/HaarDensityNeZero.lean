import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsOmegaLeb
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeSum

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def QInv (nu : Measure V) (ε δ : ℝ) : Prop :=
  ∀ X : V, ‖X‖ < δ → ∀ r, 0 < r → r < δ →
    nu (closedBall X ((1 - ε) * r)) ≤ nu (closedBall 0 r) ∧
      nu (closedBall 0 r) ≤ nu (closedBall X ((1 + ε) * r))

theorem tendsto_mul_pos {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact mul_pos ht hr

variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]

private theorem frequently_filterAt_of_eventually_closedBall (μ : Measure V) [SFinite μ] (x : V) {P : Set V → Prop}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (closedBall x r)) :
    ∃ᶠ a in (Besicovitch.vitaliFamily μ).filterAt x, P a := by
  intro hne
  have h2 := (Besicovitch.tendsto_filterAt μ x).eventually hne
  obtain ⟨r, hr1, hr2⟩ := (h.and h2).exists
  exact hr2 hr1

theorem le_of_eventually_up {ε δ : ℝ} (hε1 : ε < 1) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M : ℝ≥0∞) ≤ M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V))
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), nu (closedBall 0 r) ≤ M * lam (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : nu s ≤ M' * lam s := by
  have ha : 0 < 1 - ε := by linarith
  have key : nu s ≤ (M' • lam) s := by
    refine VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily nu) (M' • lam)
      MeasureTheory.Measure.AbsolutelyContinuous.rfl s fun x hx => frequently_filterAt_of_eventually_closedBall nu x ?_
    have hx' : ‖x‖ < δ := mem_ball_zero_iff.mp (hs hx)
    have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg x) hx'
    have ht := tendsto_mul_pos (inv_pos.mpr ha)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (1 - ε)⁻¹ * ρ < δ :=
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
    filter_upwards [ht.eventually hev, hsmall, self_mem_nhdsWithin] with ρ h1 h2 h3
    have hr : 0 < (1 - ε)⁻¹ * ρ := mul_pos (inv_pos.mpr ha) h3
    have hq' := (hq x hx' _ hr h2).1
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hq'
    have e := Measure.addHaar_closedBall_mul lam x ha.le hr.le
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    calc nu (closedBall x ρ) ≤ nu (closedBall 0 ((1 - ε)⁻¹ * ρ)) := hq'
      _ ≤ M * lam (closedBall 0 ((1 - ε)⁻¹ * ρ)) := h1
      _ ≤ (M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V)) * lam (closedBall 0 ((1 - ε)⁻¹ * ρ)) :=
          by gcongr
      _ = M' * lam (closedBall x ρ) := by rw [e, mul_assoc]
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using key

theorem le_of_eventually_down {ε δ : ℝ} (hε0 : 0 < ε) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M' : ℝ≥0∞) * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≤ M)
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), M * lam (closedBall 0 r) ≤ nu (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : M' * lam s ≤ nu s := by
  have hb : 0 < 1 + ε := by linarith
  have key : ((M' : ℝ≥0∞) • lam) s ≤ nu s := by
    refine VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily lam) nu
      (Measure.smul_absolutelyContinuous) s fun x hx => frequently_filterAt_of_eventually_closedBall lam x ?_
    have hx' : ‖x‖ < δ := mem_ball_zero_iff.mp (hs hx)
    have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg x) hx'
    have ht := tendsto_mul_pos (inv_pos.mpr hb)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (1 + ε)⁻¹ * ρ < δ :=
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
    filter_upwards [ht.eventually hev, hsmall, self_mem_nhdsWithin] with ρ h1 h2 h3
    have hr : 0 < (1 + ε)⁻¹ * ρ := mul_pos (inv_pos.mpr hb) h3
    have hq' := (hq x hx' _ hr h2).2
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at hq'
    have e := Measure.addHaar_closedBall_mul lam x hb.le hr.le
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at e
    simp only [Measure.smul_apply, smul_eq_mul]
    calc (M' : ℝ≥0∞) * lam (closedBall x ρ)
        = (M' * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V)) * lam (closedBall 0 ((1 + ε)⁻¹ * ρ)) := by
          rw [e, mul_assoc]
      _ ≤ M * lam (closedBall 0 ((1 + ε)⁻¹ * ρ)) := by gcongr
      _ ≤ nu (closedBall 0 ((1 + ε)⁻¹ * ρ)) := h1
      _ ≤ nu (closedBall x ρ) := hq'
  simpa only [Measure.smul_apply, smul_eq_mul] using key

theorem tendsto_ofReal_pow (n : ℕ) (σ : ℝ) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun ε : ℝ => (1 + σ * ε) ^ n) (𝓝 0) (𝓝 ((1 + σ * 0) ^ n)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)).pow n)
  rw [mul_zero, add_zero, one_pow] at h
  have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h
  rw [ENNReal.ofReal_one] at h2
  exact h2.mono_left nhdsWithin_le_nhds

theorem limsup_liminf_bounds {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hq : QInv nu ε δ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      limsup (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L ∧
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L ≤
        liminf (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
  have hae := Besicovitch.ae_tendsto_rnDeriv nu lam
  have hfin := Measure.rnDeriv_lt_top nu lam
  have hpos : lam (ball (0 : V) δ) ≠ 0 := (measure_ball_pos lam 0 hδ).ne'
  obtain ⟨X, hX, hXt, hXf⟩ : ∃ X ∈ ball (0 : V) δ,
      Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r)) (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧
        nu.rnDeriv lam X < ⊤ := by
    by_contra hcon
    apply hpos
    have h3 := ae_iff.mp (hae.and hfin)
    refine measure_mono_null (fun y hy => ?_) h3
    show ¬ _
    exact fun h => hcon ⟨y, hy, h.1, h.2⟩
  have hXn : ‖X‖ < δ := mem_ball_zero_iff.mp hX
  have key : ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r →
      nu (closedBall X (t * r)) / lam (closedBall 0 r) =
        ENNReal.ofReal (t ^ finrank ℝ V) * (nu (closedBall X (t * r)) / lam (closedBall X (t * r))) := by
    intro t ht r hr
    rw [Measure.addHaar_closedBall_mul lam X ht.le hr.le, ← mul_div_assoc, ENNReal.mul_div_mul_left]
    · exact (ENNReal.ofReal_pos.mpr (pow_pos ht _)).ne'
    · exact ENNReal.ofReal_ne_top
  have hup : Tendsto (fun r => ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) *
      (nu (closedBall X ((1 + ε) * r)) / lam (closedBall X ((1 + ε) * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
    ENNReal.Tendsto.const_mul (hXt.comp (tendsto_mul_pos (by linarith))) (Or.inr ENNReal.ofReal_ne_top)
  have hlo : Tendsto (fun r => ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) *
      (nu (closedBall X ((1 - ε) * r)) / lam (closedBall X ((1 - ε) * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
    ENNReal.Tendsto.const_mul (hXt.comp (tendsto_mul_pos (by linarith))) (Or.inr ENNReal.ofReal_ne_top)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hδ)] with r h0 h1
    exact ⟨h0, h1⟩
  refine ⟨nu.rnDeriv lam X, hXf.ne, ?_, ?_⟩
  · refine (Filter.limsup_le_limsup ?_).trans hup.limsup_eq.le
    filter_upwards [hev] with r hr
    rw [← key _ (by linarith) r hr.1]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).2 _
  · refine hlo.liminf_eq.ge.trans (Filter.liminf_le_liminf ?_)
    filter_upwards [hev] with r hr
    rw [← key _ (by linarith) r hr.1]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).1 _

theorem exists_density
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by
  have hlam0 : ∀ r : ℝ, 0 < r → lam (closedBall (0 : V) r) ≠ 0 :=
    fun r hr => (Metric.measure_closedBall_pos lam 0 hr).ne'
  have hlamT : ∀ r : ℝ, lam (closedBall (0 : V) r) ≠ ⊤ :=
    fun r => (isCompact_closedBall (0 : V) r).measure_lt_top.ne
  have hcmp : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤ ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
    intro ε h0 h1
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    obtain ⟨L, -, hls, hli⟩ := limsup_liminf_bounds lam nu h0 h1 hδ hqδ
    calc ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ))
        ≤ ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L) := by gcongr
      _ = ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L) := by ring
      _ ≤ ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by gcongr
  have hls_le : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤ liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
    have A := ENNReal.Tendsto.mul_const (tendsto_ofReal_pow (finrank ℝ V) (-1)) (Or.inl one_ne_zero) (b := limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)))
    have B := ENNReal.Tendsto.mul_const (tendsto_ofReal_pow (finrank ℝ V) 1) (Or.inl one_ne_zero) (b := liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)))
    rw [one_mul] at A B
    refine le_of_tendsto_of_tendsto A B ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε h0 h1
    rw [show (1 : ℝ) + -1 * ε = 1 - ε by ring, show (1 : ℝ) + 1 * ε = 1 + ε by ring]
    exact hcmp ε h0 h1
  have heq : liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) = limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := le_antisymm Filter.liminf_le_limsup hls_le
  have hlsT : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ⊤ := by
    obtain ⟨δ, hδ, hqδ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    obtain ⟨L, hL, hls, -⟩ := limsup_liminf_bounds lam nu (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hδ hqδ
    exact lt_of_le_of_lt hls (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL).lt_top
  have hup : ∀ C : ℝ≥0, limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s := by
    intro C hC
    have t1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_pow (finrank ℝ V) (-1)) (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_one] at t1
    have hev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < C * ENNReal.ofReal ((1 + -1 * ε) ^ finrank ℝ V)) ∧ 0 < ε ∧ ε < 1 := by
      filter_upwards [t1.eventually (lt_mem_nhds hC), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε a b c
      exact ⟨a, b, c⟩
    obtain ⟨ε, hcε, h0, h1⟩ := hev.exists
    rw [show (1 : ℝ) + -1 * ε = 1 - ε by ring] at hcε
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    have hMe : ((C * ((1 - ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) = C * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ((C * ((1 - ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) := by rw [hMe]; exact hcε
    have hevr := Filter.eventually_lt_of_limsup_lt hcM
    refine ⟨δ, hδ, fun s hs => le_of_eventually_up lam nu h1 hqδ _ C hMe.le ?_ s hs⟩
    filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.div_le_iff_le_mul (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le
  have hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s := by
    intro C hC
    have t1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_pow (finrank ℝ V) 1) (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_one] at t1
    have hev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (C * ENNReal.ofReal ((1 + 1 * ε) ^ finrank ℝ V) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ))) ∧ 0 < ε ∧ ε < 1 := by
      filter_upwards [t1.eventually (gt_mem_nhds hC), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε a b c
      exact ⟨a, b, c⟩
    obtain ⟨ε, hcε, h0, h1⟩ := hev.exists
    rw [one_mul] at hcε
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    have hMe : ((C * ((1 + ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) = C * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : ((C * ((1 + ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by rw [hMe]; exact hcε
    have hevr := Filter.eventually_lt_of_lt_liminf hcM
    refine ⟨δ, hδ, fun s hs => le_of_eventually_down lam nu h0 hqδ _ C hMe.ge ?_ s hs⟩
    filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le
  have hc0 : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≠ 0 := by
    intro hzero
    obtain ⟨δ, hδ, hqδ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    have hB : closedBall (0 : V) (δ / 2) ⊆ ball 0 δ := closedBall_subset_ball (by linarith)
    obtain ⟨C, hC0, hClt⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (hlamT (δ / 2)) (hpos (δ / 2) (by linarith)).ne'
    have hMe : ((C * ((1 - 1 / 2 : ℝ) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) =
        C * ENNReal.ofReal ((1 - 1 / 2 : ℝ) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ((C * ((1 - 1 / 2 : ℝ) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [hzero, hMe]
      exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hC0.ne')
        (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) _)).ne'
    have hevr := Filter.eventually_lt_of_limsup_lt hcM
    have hle := le_of_eventually_up lam nu (by norm_num : (1 / 2 : ℝ) < 1) hqδ _ C hMe.le (by
      filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
      exact (ENNReal.div_le_iff_le_mul (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le) _ hB
    exact absurd hle (not_le.mpr hClt)
  refine ⟨limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)), hc0, hlsT.ne, hup, fun C hC => hdown C ?_⟩
  rw [heq]
  exact hC

end Formalism.BasicNotions.Examples₂.CD
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

structure Chart (V : Submodule ℝ 𝔸) (G : Type*) [Group G] [TopologicalSpace G] where
  mat : G →* 𝔸
  emb : IsEmbedding mat
  H1 : ∀ X : V, ∃ g, mat g = exp (X : 𝔸)
  H2 : ∀ᶠ Z in 𝓝 (0 : 𝔸), (∃ g, mat g = exp Z) → Z ∈ V

namespace Chart

variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)

def expG (X : V) : G := (C.H1 X).choose

theorem mat_expG (X : V) : C.mat (C.expG X) = exp (X : 𝔸) := (C.H1 X).choose_spec

def img (s : Set V) : Set G := {g | ∃ X ∈ s, C.mat g = exp ((X : V) : 𝔸)}

theorem img_eq (s : Set V) : C.img s = C.expG '' s := by
  ext g
  constructor
  · rintro ⟨X, hX, hg⟩
    refine ⟨X, hX, C.emb.injective ?_⟩
    rw [C.mat_expG, hg]
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, C.mat_expG X⟩

theorem expG_cont : Continuous C.expG := by
  rw [C.emb.continuous_iff]
  have h : C.mat ∘ C.expG = fun X : V => exp (X : 𝔸) := funext C.mat_expG
  rw [h]
  have hc : Continuous (fun Z : 𝔸 => exp Z) := by
    first
      | exact NormedSpace.exp_continuous (𝕂 := ℝ)
      | exact (NormedSpace.exp_continuous (𝕂 := ℝ) (𝔸 := 𝔸))
      | exact continuous_iff_continuousAt.2 fun Z => (NormedSpace.exp_analytic (𝕂 := ℝ) Z).continuousAt
      | exact NormedSpace.exp_continuous
  exact hc.comp continuous_subtype_val

theorem exists_rho : ∃ ρ > 0, ∀ Z : 𝔸, ‖Z‖ < ρ →
    logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V) := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 ((logA_exp (𝔸 := 𝔸)).and C.H2)
  exact ⟨ε, hε, fun Z hZ => h (by simpa [dist_zero_right] using hZ)⟩

variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))

include hR in
theorem injOn : InjOn C.expG (ball (0 : V) ρ) := by
  intro X hX Y hY hXY
  have h1 : exp (X : 𝔸) = exp (Y : 𝔸) := by
    rw [← C.mat_expG, ← C.mat_expG, hXY]
  have hXn : ‖(X : 𝔸)‖ < ρ := by simpa using hX
  have hYn : ‖(Y : 𝔸)‖ < ρ := by simpa using hY
  apply Subtype.ext
  rw [← (hR _ hXn).1, ← (hR _ hYn).1, h1]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]

include hR in
theorem meas_image {s : Set V} (hs : MeasurableSet s) (hsub : s ⊆ ball 0 ρ) :
    MeasurableSet (C.expG '' s) := by
  haveI : T2Space G := C.emb.t2Space
  haveI : CompleteSpace V := FiniteDimensional.complete ℝ V
  exact hs.image_of_continuousOn_injOn C.expG_cont.continuousOn ((C.injOn hR).mono hsub)

def nu (ρ : ℝ) (μ : Measure G) : Measure V :=
  (μ.comap (fun x : ball (0 : V) ρ => C.expG x.1)).map Subtype.val

variable (μ : Measure G)

include hR in
theorem nu_apply {s : Set V} (hs : MeasurableSet s) :
    C.nu ρ μ s = μ (C.expG '' (s ∩ ball 0 ρ)) := by
  unfold nu
  rw [Measure.map_apply measurable_subtype_coe hs]
  have hf : Function.Injective (fun x : ball (0 : V) ρ => C.expG x.1) :=
    fun a b h => Subtype.ext (C.injOn hR a.2 b.2 h)
  have hfm : ∀ t : Set (ball (0 : V) ρ), MeasurableSet t →
      MeasurableSet ((fun x : ball (0 : V) ρ => C.expG x.1) '' t) := by
    intro t ht
    have h1 : (fun x : ball (0 : V) ρ => C.expG x.1) '' t = C.expG '' (Subtype.val '' t) := by
      rw [Set.image_image]
    rw [h1]
    exact C.meas_image hR (MeasurableSet.subtype_image measurableSet_ball ht)
      (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  rw [Measure.comap_apply _ hf hfm μ (measurable_subtype_coe hs)]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
  · rintro ⟨X, ⟨hXs, hXb⟩, rfl⟩
    exact ⟨⟨X, hXb⟩, hXs, rfl⟩

variable [IsTopologicalGroup G] [μ.IsHaarMeasure]

include hR in
theorem nu_finite : IsFiniteMeasure (C.nu ρ μ) := by
  constructor
  rw [C.nu_apply hR μ MeasurableSet.univ, Set.univ_inter]
  have hK : IsCompact (C.expG '' closedBall (0 : V) ρ) := (isCompact_closedBall 0 ρ).image C.expG_cont
  exact lt_of_le_of_lt (measure_mono (Set.image_mono ball_subset_closedBall)) hK.measure_lt_top

include hR in
theorem nu_pos (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) : 0 < C.nu ρ μ (closedBall (0 : V) r) := by
  have ht : 0 < min r ρ := lt_min hr hρ
  have hcont : ContinuousAt (logA 𝔸) 1 := (hasStrict_logA (𝔸 := 𝔸)).hasFDerivAt.continuousAt
  have hlim : Tendsto (logA 𝔸) (𝓝 1) (𝓝 0) := by
    have h := hcont.tendsto
    rwa [logA_one] at h
  have hev : ∀ᶠ h in 𝓝 (1 : 𝔸), exp (logA 𝔸 h) = h ∧ ‖logA 𝔸 h‖ < min r ρ := by
    refine (exp_logA (𝔸 := 𝔸)).and ?_
    filter_upwards [(Metric.tendsto_nhds.1 hlim) _ ht] with h hh
    simpa [dist_zero_right] using hh
  obtain ⟨W, hWsub, hWo, hW1⟩ := _root_.mem_nhds_iff.1 hev
  have hUo : IsOpen (C.mat ⁻¹' W) := hWo.preimage C.emb.continuous
  have hU1 : (1 : G) ∈ C.mat ⁻¹' W := by
    show C.mat 1 ∈ W
    rw [map_one]
    exact hW1
  have hsub : C.mat ⁻¹' W ⊆ C.expG '' (closedBall 0 r ∩ ball 0 ρ) := by
    intro g hg
    obtain ⟨he, hn⟩ := hWsub hg
    have hZρ : ‖logA 𝔸 (C.mat g)‖ < ρ := lt_of_lt_of_le hn (min_le_right _ _)
    have hZV : logA 𝔸 (C.mat g) ∈ V := (hR _ hZρ).2 ⟨g, he.symm⟩
    refine ⟨⟨logA 𝔸 (C.mat g), hZV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact le_of_lt (lt_of_lt_of_le hn (min_le_left _ _))
    · rw [mem_ball_zero_iff]
      exact hZρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact he
  rw [C.nu_apply hR μ measurableSet_closedBall]
  exact lt_of_lt_of_le (hUo.measure_pos μ ⟨1, hU1⟩) (measure_mono hsub)

include hR in
theorem nu_qinv (hρ : 0 < ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : ∃ δ > 0, QInv (C.nu ρ μ) ε δ := by
  obtain ⟨κ, hκ, hd⟩ := distortion (𝔸 := 𝔸) (half_pos hε0)
  refine ⟨min κ ρ / 3, by positivity, ?_⟩
  intro X hX r hr0 hrδ
  have hm1 : min κ ρ ≤ κ := min_le_left _ _
  have hm2 : min κ ρ ≤ ρ := min_le_right _ _
  have hXn : ‖(X : 𝔸)‖ < min κ ρ / 3 := hX
  have hX0 : 0 ≤ ‖(X : 𝔸)‖ := norm_nonneg _
  have hmul : ∀ a b : G, C.mat (a * b) = C.mat a * C.mat b := fun a b => map_mul _ _ _
  constructor
  · rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
      ← measure_smul μ (C.expG (-X))]
    apply measure_mono
    rintro _ ⟨_, ⟨Y, ⟨hY1, hY2⟩, rfl⟩, rfl⟩
    have hW : ‖(Y : 𝔸) - X‖ ≤ (1 - ε) * r := by
      rw [mem_closedBall_iff_norm] at hY1
      exact hY1
    have hW0 : 0 ≤ ‖(Y : 𝔸) - X‖ := norm_nonneg _
    have hWk : ‖(Y : 𝔸) - X‖ < κ := by nlinarith
    obtain ⟨⟨he, hn⟩, -⟩ := hd X ((Y : 𝔸) - X) (by linarith) hWk
    have hXY : (X : 𝔸) + ((Y : 𝔸) - X) = Y := by abel
    rw [hXY] at he
    have h1 := norm_sub_norm_le (F1 ((X : 𝔸), (Y : 𝔸) - X)) ((Y : 𝔸) - X)
    have hp : (1 + ε / 2) * ‖(Y : 𝔸) - X‖ ≤ (1 + ε / 2) * ((1 - ε) * r) :=
      mul_le_mul_of_nonneg_left hW (by linarith)
    have hq : (1 + ε / 2) * ((1 - ε) * r) ≤ r := by
      nlinarith [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]
    have hZn : ‖F1 ((X : 𝔸), (Y : 𝔸) - X)‖ ≤ r := by linarith
    have hZρ : ‖F1 ((X : 𝔸), (Y : 𝔸) - X)‖ < ρ := by linarith
    have hex : exp (F1 ((X : 𝔸), (Y : 𝔸) - X)) = C.mat (C.expG (-X) * C.expG Y) := by
      rw [hmul, C.mat_expG, C.mat_expG, he, Submodule.coe_neg]
    have hZV := (hR _ hZρ).2 ⟨_, hex.symm⟩
    refine ⟨⟨_, hZV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact hZn
    · rw [mem_ball_zero_iff]
      exact hZρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact hex
  · rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
      ← measure_smul μ (C.expG X)]
    apply measure_mono
    rintro _ ⟨_, ⟨Z, ⟨hZ1, hZ2⟩, rfl⟩, rfl⟩
    have hZ : ‖(Z : 𝔸)‖ ≤ r := by
      rw [mem_closedBall_zero_iff] at hZ1
      exact hZ1
    have hZ0 : 0 ≤ ‖(Z : 𝔸)‖ := norm_nonneg _
    obtain ⟨-, ⟨he, hn⟩⟩ := hd X Z (by linarith) (by linarith)
    have h1 := norm_sub_norm_le (F2 ((X : 𝔸), (Z : 𝔸)) - X) (Z : 𝔸)
    have hp : ε / 2 * ‖(Z : 𝔸)‖ ≤ ε / 2 * r := mul_le_mul_of_nonneg_left hZ (by linarith)
    have hq : ε * r ≤ r := by nlinarith [mul_pos hε0 hr0]
    have hYX : ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ (1 + ε) * r := by
      calc ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ ‖F2 ((X : 𝔸), (Z : 𝔸)) - X - Z‖ + ‖(Z : 𝔸)‖ := by linarith [h1]
        _ ≤ ε / 2 * ‖(Z : 𝔸)‖ + r := add_le_add hn hZ
        _ ≤ ε / 2 * r + r := by linarith [hp]
        _ ≤ (1 + ε) * r := by nlinarith [mul_pos hε0 hr0]
    have h2 := norm_le_insert' (F2 ((X : 𝔸), (Z : 𝔸))) (X : 𝔸)
    have hYρ : ‖F2 ((X : 𝔸), (Z : 𝔸))‖ < ρ := by linarith
    have hex : exp (F2 ((X : 𝔸), (Z : 𝔸))) = C.mat (C.expG X * C.expG Z) := by
      rw [hmul, C.mat_expG, C.mat_expG, he]
    have hYV := (hR _ hYρ).2 ⟨_, hex.symm⟩
    refine ⟨⟨_, hYV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_iff_norm]
      exact hYX
    · rw [mem_ball_zero_iff]
      exact hYρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact hex

theorem exists_density (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ (C.img (S r)) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  haveI := C.nu_finite hR μ
  obtain ⟨c, hc0, hctop, hup, hdown⟩ := Formalism.BasicNotions.Examples₂.CD.exists_density (nu := C.nu ρ μ) (lam := lam)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  refine ⟨c, hc0, hctop, fun S hS hsmall hlam => ?_⟩
  have key : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      S r ⊆ ball 0 δ ∧ S r ⊆ ball 0 ρ ∧ lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤ := fun δ hδ =>
    (((hsmall δ hδ).and (hsmall ρ hρ)).and hlam).mono fun r h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have heq : ∀ r, S r ⊆ ball 0 ρ → μ (C.img (S r)) = C.nu ρ μ (S r) := by
    intro r hr
    rw [C.img_eq, C.nu_apply hR μ (hS r), Set.inter_eq_left.2 hr]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨C', haC', hC'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    obtain ⟨δ, hδ, hδs⟩ := hdown C' hC'c
    filter_upwards [key δ hδ] with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [heq r h2]
    exact lt_of_lt_of_le haC' ((ENNReal.le_div_iff_mul_le (Or.inl h3) (Or.inl h4)).2 (hδs _ h1))
  · obtain ⟨C', hcC', hC'b⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
    obtain ⟨δ, hδ, hδs⟩ := hup C' hcC'
    filter_upwards [key δ hδ] with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [heq r h2]
    exact lt_of_le_of_lt (ENNReal.div_le_of_le_mul (hδs _ h1)) hC'b

end Chart

theorem Chart.exists_density' {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ X ∈ S r, ‖(X : 𝔸)‖ < δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ {g | ∃ X ∈ S r, C.mat g = exp ((X : V) : 𝔸)} / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  letI := mV
  letI := mG
  haveI := _hfd
  haveI := _hbV
  haveI := _hbG
  haveI := _hG
  haveI := _hμ
  haveI := _hlam
  obtain ⟨c, h0, h1, h⟩ := C.exists_density μ lam
  refine ⟨c, h0, h1, fun S hS hsm hl => h S hS (fun δ hδ => (hsm δ hδ).mono fun r hr X hX => ?_) hl⟩
  simpa using hr X hX

end Formalism.BasicNotions.Examples₂.CD
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Filter Topology Metric NormedSpace Set Matrix Formalism.UG.P
open scoped ENNReal NNReal Matrix.Norms.Operator

variable (P Q : ℕ)

local notation "J" => Formalism.UG.Jpq P Q

instance : CompleteSpace (MM P Q) := FiniteDimensional.complete ℝ _

def matHom : UpqT P Q →* MM P Q where
  toFun := UpqT.mat
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mat_mem (g : UpqT P Q) : (UpqT.mat g)ᴴ * J * UpqT.mat g = J := g.2

theorem mat_left_inv (g : UpqT P Q) : (J * (UpqT.mat g)ᴴ * J) * UpqT.mat g = 1 := by
  have h := mat_mem P Q g
  calc J * (UpqT.mat g)ᴴ * J * UpqT.mat g = J * ((UpqT.mat g)ᴴ * J * UpqT.mat g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, J_sq]

theorem mat_inv_eq (g : Formalism.UG.Upq P Q) :
    (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) =
      J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J := by
  have h1 := mat_left_inv P Q g
  have h2 : UpqT.mat (P := P) (Q := Q) g *
      (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) = 1 :=
    Units.mul_inv (g : GL (Fin P ⊕ Fin Q) ℂ)
  calc (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q)
      = (J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J * UpqT.mat (P := P) (Q := Q) g) *
          (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) := by
        rw [h1, Matrix.one_mul]
    _ = J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J := by
        rw [Matrix.mul_assoc (J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J), h2, Matrix.mul_one]

theorem mat_cont : Continuous (UpqT.mat : UpqT P Q → MM P Q) := Units.continuous_val.comp continuous_subtype_val

theorem mat_inducing : IsInducing (UpqT.mat : UpqT P Q → MM P Q) := by
  exact Units.isOpenEmbedding_val.toIsEmbedding.toIsInducing.comp Topology.IsInducing.subtypeVal

theorem mat_injective : Function.Injective (UpqT.mat : UpqT P Q → MM P Q) := fun a b h => Subtype.ext (Units.ext h)

theorem mat_embedding : IsEmbedding (UpqT.mat : UpqT P Q → MM P Q) := ⟨mat_inducing P Q, mat_injective P Q⟩

theorem exists_of_mem (h : MM P Q) (hh : hᴴ * J * h = J) : ∃ g : UpqT P Q, UpqT.mat g = h := by
  have hl : J * hᴴ * J * h = 1 := by
    calc J * hᴴ * J * h = J * (hᴴ * J * h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, J_sq]
  have hr : h * (J * hᴴ * J) = 1 := mul_eq_one_comm.mp hl
  exact ⟨⟨⟨h, J * hᴴ * J, hr, hl⟩, hh⟩, rfl⟩

theorem mat_range : Set.range (UpqT.mat : UpqT P Q → MM P Q) = {h | hᴴ * J * h = J} := by
  ext h
  constructor
  · rintro ⟨g, rfl⟩
    exact mat_mem P Q g
  · intro hh
    exact exists_of_mem P Q h hh

theorem mat_closedEmbedding : IsClosedEmbedding (UpqT.mat : UpqT P Q → MM P Q) := by
  refine ⟨mat_embedding P Q, ?_⟩
  rw [mat_range]
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

instance : LocallyCompactSpace (UpqT P Q) :=
  haveI : LocallyCompactSpace (MM P Q) :=
    inferInstanceAs (LocallyCompactSpace (Fin P ⊕ Fin Q → Fin P ⊕ Fin Q → ℂ))
  (mat_closedEmbedding P Q).locallyCompactSpace

instance (N : ℕ) : CompactSpace (UpqT N 0) :=
  isCompact_iff_compactSpace.mp (indefinite_unitary_compact N)

theorem exp_neg_mul' (X : MM P Q) : exp (-X) * exp X = 1 := by
  have h := NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X))
  rw [neg_add_cancel, NormedSpace.exp_zero] at h
  exact h.symm


theorem exp_conjJ (A : MM P Q) : exp (J * A * J) = J * exp A * J := by
  let u : (MM P Q)ˣ := ⟨J, J, J_sq P Q, J_sq P Q⟩
  exact NormedSpace.exp_units_conj u A

theorem exp_mem (X : MM P Q) (hX : X ∈ lieU P Q) : (exp X)ᴴ * J * exp X = J := by
  have h1 : J * (-Xᴴ) * J = X := (mem_lieU_iff P Q X).1 hX
  have e : J * (J * (-Xᴴ) * J) * J = -Xᴴ := by
    rw [mul_assoc, mul_assoc (J * (-Xᴴ)), J_sq, mul_one, ← mul_assoc, J_sq, one_mul]
  have h2 : Xᴴ = J * (-X) * J := by
    rw [h1] at e
    rw [mul_neg, neg_mul, e, neg_neg]
  rw [← Matrix.exp_conjTranspose, h2, exp_conjJ]
  calc J * exp (-X) * J * J * exp X = J * (exp (-X) * (J * J) * exp X) := by
        simp only [mul_assoc]
    _ = J := by rw [J_sq, mul_one, exp_neg_mul', mul_one]

theorem exp_theta (Z : MM P Q) (hZ : (exp Z)ᴴ * J * exp Z = J) : exp (J * (-Zᴴ) * J) = exp Z := by
  have hc : (exp Z)ᴴ = exp Zᴴ := (Matrix.exp_conjTranspose Z).symm
  rw [hc] at hZ
  have h1 : J * exp Z = exp (-Zᴴ) * J := by
    calc J * exp Z = exp (-Zᴴ) * exp Zᴴ * J * exp Z := by rw [exp_neg_mul', one_mul]
      _ = exp (-Zᴴ) * (exp Zᴴ * J * exp Z) := by simp only [mul_assoc]
      _ = exp (-Zᴴ) * J := by rw [hZ]
  rw [exp_conjJ]
  calc J * exp (-Zᴴ) * J = J * (exp (-Zᴴ) * J) := by rw [mul_assoc]
    _ = J * (J * exp Z) := by rw [h1]
    _ = exp Z := by rw [← mul_assoc, J_sq, one_mul]

def chart : Chart (lieU P Q) (UpqT P Q) where
  mat := matHom P Q
  emb := mat_embedding P Q
  H1 := fun X => exists_of_mem P Q _ (exp_mem P Q X X.2)
  H2 := by
    have hθ : Continuous (fun Z : MM P Q => J * (-Zᴴ) * J) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose.neg).matrix_mul continuous_const
    have h0 : Tendsto (fun Z : MM P Q => J * (-Zᴴ) * J) (𝓝 0) (𝓝 0) := by
      have := hθ.tendsto 0
      simpa using this
    filter_upwards [logA_exp (𝔸 := MM P Q), h0.eventually (logA_exp (𝔸 := MM P Q))] with Z h1 h2
    rintro ⟨g, hg⟩
    have hm : (exp Z)ᴴ * J * exp Z = J := by
      have := mat_mem P Q g
      rw [show UpqT.mat g = exp Z from hg] at this
      exact this
    rw [mem_lieU_iff]
    calc J * (-Zᴴ) * J = logA (MM P Q) (exp (J * (-Zᴴ) * J)) := h2.symm
      _ = logA (MM P Q) (exp Z) := congrArg (logA (MM P Q)) (exp_theta P Q Z hm)
      _ = Z := h1

theorem norm_le_sum (X : MM P Q) : ‖X‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by
  have hs : (Finset.univ.sup fun i => ∑ j, ‖X i j‖₊) ≤ ∑ i, ∑ j, ‖X i j‖₊ :=
    Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊) (fun _ _ => zero_le) (Finset.mem_univ i)
  rw [Matrix.linfty_opNorm_def]
  refine (NNReal.coe_le_coe.mpr hs).trans (le_of_eq ?_)
  simp [NNReal.coe_sum]

theorem omegaDensity_haar (μ : Measure (UpqT P Q)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity μ c := by
  obtain ⟨lam, hlam⟩ := exists_omegaLeb P Q
  have := hlam.1
  obtain ⟨c, hc0, hct, h⟩ := (chart P Q).exists_density' (finDimLie P Q) _ (instBorelLie P Q) _
    (instBorelU P Q) (instTopGroupU P Q) μ inferInstance lam hlam.1
  refine ⟨c, hc0, hct, lam, hlam, ?_⟩
  exact h (ballU P Q) (fun r => (isOpen_ballU P Q r).measurableSet)
    (fun δ hδ => by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr X hX
      exact lt_of_le_of_lt (norm_le_sum P Q X) (lt_trans hX hr.2))
    (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact ⟨(ballU_pos P Q lam hr).ne', (ballU_lt_top P Q lam r).ne⟩)

theorem omegaDensity_smul {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (h : OmegaDensity μ c) (t : ℝ≥0∞)
    (ht : t ≠ ⊤) : OmegaDensity (t • μ) (t * c) := by
  obtain ⟨lam, hl, hc⟩ := h
  refine ⟨lam, hl, ?_⟩
  refine (ENNReal.Tendsto.const_mul hc (Or.inr ht)).congr (fun r => ?_)
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

def mu0 : Measure (UpqT P Q) := Measure.haar

instance : (mu0 P Q).IsHaarMeasure := inferInstanceAs (Measure.haar.IsHaarMeasure)

def c0 : ℝ≥0∞ := (omegaDensity_haar P Q (mu0 P Q)).choose

theorem haar_density_ne_zero : c0 P Q ≠ 0 := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.1
theorem haar_density_ne_top : c0 P Q ≠ ⊤ := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.2.1
theorem haar_density_spec : OmegaDensity (mu0 P Q) (c0 P Q) := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.2.2

def mass (N : ℕ) : ℝ≥0∞ := mu0 N 0 Set.univ

theorem mass_ne_zero (N : ℕ) : mass N ≠ 0 := isOpen_univ.measure_ne_zero (mu0 N 0) ⟨1, trivial⟩

theorem mass_ne_top (N : ℕ) : mass N ≠ ⊤ := (isCompact_univ.measure_lt_top (μ := mu0 N 0)).ne

def scale : ℝ≥0∞ := c0 (P + Q) 0 / (mass (P + Q) * c0 P Q)

theorem scale_ne_zero : scale P Q ≠ 0 := ENNReal.div_ne_zero.mpr ⟨haar_density_ne_zero _ _, ENNReal.mul_ne_top (mass_ne_top _) (haar_density_ne_top _ _)⟩

theorem scale_ne_top : scale P Q ≠ ⊤ := ENNReal.div_ne_top (haar_density_ne_top _ _) (mul_ne_zero (mass_ne_zero _) (haar_density_ne_zero _ _))

theorem scale_mul : scale P Q * c0 P Q = c0 (P + Q) 0 / mass (P + Q) := by
  unfold scale
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (haar_density_ne_top _ _)) (Or.inr (haar_density_ne_zero _ _)), mul_assoc, mul_assoc,
    ENNReal.inv_mul_cancel (haar_density_ne_zero _ _) (haar_density_ne_top _ _), mul_one]

theorem scale_mass (N : ℕ) : scale N 0 * mass N = 1 := by
  unfold scale
  rw [Nat.add_zero, div_eq_mul_inv, ENNReal.mul_inv (Or.inl (mass_ne_zero _)) (Or.inl (mass_ne_top _)),
    mul_comm (mass N)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel (haar_density_ne_zero _ _) (haar_density_ne_top _ _), one_mul,
    ENNReal.inv_mul_cancel (mass_ne_zero _) (mass_ne_top _)]

def cdHaar : CDHaar where
  cd := fun P Q => scale P Q • mu0 P Q
  haar := fun P Q => Measure.IsHaarMeasure.smul (mu0 P Q) (scale_ne_zero P Q) (scale_ne_top P Q)
  prob := fun N => ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact scale_mass N⟩
  trick := fun P Q => ⟨c0 (P + Q) 0 / mass (P + Q),
    ENNReal.div_ne_zero.mpr ⟨haar_density_ne_zero _ _, mass_ne_top _⟩,
    ENNReal.div_ne_top (haar_density_ne_top _ _) (mass_ne_zero _),
    by
      rw [← scale_mul P Q]
      exact omegaDensity_smul P Q (haar_density_spec P Q) _ (scale_ne_top P Q),
    by
      have h := omegaDensity_smul (P + Q) 0 (haar_density_spec (P + Q) 0) _ (scale_ne_top (P + Q) 0)
      rw [scale_mul (P + Q) 0] at h
      exact h⟩


end Formalism.BasicNotions.Examples₂.CD
end
end
