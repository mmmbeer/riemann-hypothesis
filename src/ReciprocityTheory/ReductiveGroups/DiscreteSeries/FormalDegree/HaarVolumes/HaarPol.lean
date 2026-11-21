import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HExp

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
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) := (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos ht hr

variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]

theorem le_of_eventually_up {ε δ : ℝ} (hε1 : ε < 1) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M : ℝ≥0∞) ≤ M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V))
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), nu (closedBall 0 r) ≤ M * lam (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : nu s ≤ M' * lam s := by
  have key := (Besicovitch.vitaliFamily nu).measure_le_of_frequently_le (M' • lam)
    (Measure.AbsolutelyContinuous.refl nu) s ?_
  · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at key
    exact key
  intro X hX
  have hXn : ‖X‖ < δ := by simpa using hs hX
  have ht : Tendsto (fun r : ℝ => closedBall X ((1 - ε) * r)) (𝓝[>] 0)
      ((Besicovitch.vitaliFamily nu).filterAt X) :=
    (Besicovitch.tendsto_filterAt nu X).comp (tendsto_mul_pos (by linarith))
  refine ht.frequently (Eventually.frequently ?_)
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hXn
  filter_upwards [hev, Ioo_mem_nhdsGT hδ] with r hr hrδ
  calc nu (closedBall X ((1 - ε) * r)) ≤ nu (closedBall 0 r) := (hq X hXn r hrδ.1 hrδ.2).1
    _ ≤ M * lam (closedBall 0 r) := hr
    _ ≤ (M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V)) * lam (closedBall 0 r) := by gcongr
    _ = (M' • lam) (closedBall X ((1 - ε) * r)) := by
        rw [Measure.smul_apply, Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r,
          ENNReal.smul_def, smul_eq_mul, mul_assoc]

theorem le_of_eventually_down {ε δ : ℝ} (hε0 : 0 < ε) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M' : ℝ≥0∞) * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≤ M)
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), M * lam (closedBall 0 r) ≤ nu (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : M' * lam s ≤ nu s := by
  have key := (Besicovitch.vitaliFamily lam).measure_le_of_frequently_le (ρ := M' • lam) nu
    (Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl lam) M') s ?_
  · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at key
    exact key
  intro X hX
  have hXn : ‖X‖ < δ := by simpa using hs hX
  have ht : Tendsto (fun r : ℝ => closedBall X ((1 + ε) * r)) (𝓝[>] 0)
      ((Besicovitch.vitaliFamily lam).filterAt X) :=
    (Besicovitch.tendsto_filterAt lam X).comp (tendsto_mul_pos (by linarith))
  refine ht.frequently (Eventually.frequently ?_)
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hXn
  filter_upwards [hev, Ioo_mem_nhdsGT hδ] with r hr hrδ
  calc (M' • lam) (closedBall X ((1 + ε) * r))
      = (M' * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V)) * lam (closedBall 0 r) := by
        rw [Measure.smul_apply, Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r,
          ENNReal.smul_def, smul_eq_mul, mul_assoc]
    _ ≤ M * lam (closedBall 0 r) := by gcongr
    _ ≤ nu (closedBall 0 r) := hr
    _ ≤ nu (closedBall X ((1 + ε) * r)) := (hq X hXn r hrδ.1 hrδ.2).2

theorem tendsto_ofReal_pow (n : ℕ) (σ : ℝ) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) (𝓝[>] 0) (𝓝 1) := by
  have h : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have := h.tendsto 0
  simp only [mul_zero, add_zero, one_pow, ENNReal.ofReal_one] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem limsup_liminf_bounds {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hq : QInv nu ε δ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      limsup (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L ∧
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L ≤
        liminf (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
  have hae := (Besicovitch.ae_tendsto_rnDeriv nu lam).and (Measure.rnDeriv_lt_top nu lam)
  obtain ⟨X, hXm, hX, hXfin⟩ : ∃ X ∈ ball (0 : V) δ,
      Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r)) (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧
        nu.rnDeriv lam X < ⊤ := by
    by_contra hcon
    push Not at hcon
    have hsub : ball (0 : V) δ ⊆ {X | ¬ (Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r))
        (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧ nu.rnDeriv lam X < ⊤)} := by
      intro X hX h
      exact absurd h.2 (not_lt.mpr (hcon X hX h.1))
    have h0 := measure_mono_null hsub (ae_iff.mp hae)
    exact (measure_ball_pos lam (0 : V) hδ).ne' h0
  have hXn : ‖X‖ < δ := by simpa using hXm
  refine ⟨nu.rnDeriv lam X, hXfin.ne, ?_, ?_⟩
  · have hA0 : ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hg : Tendsto (fun r : ℝ => ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) *
        (nu (closedBall X ((1 + ε) * r)) / lam (closedBall X ((1 + ε) * r)))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
      ENNReal.Tendsto.const_mul (hX.comp (tendsto_mul_pos (by linarith)))
        (Or.inr ENNReal.ofReal_ne_top)
    rw [← hg.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ hA0 ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).2 _
  · have hB0 : ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      have : 0 < 1 - ε := by linarith
      positivity
    have hg : Tendsto (fun r : ℝ => ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) *
        (nu (closedBall X ((1 - ε) * r)) / lam (closedBall X ((1 - ε) * r)))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
      ENNReal.Tendsto.const_mul (hX.comp (tendsto_mul_pos (by linarith)))
        (Or.inr ENNReal.ofReal_ne_top)
    rw [← hg.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ hB0 ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).1 _

theorem exists_density
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by
  set f : ℝ → ℝ≥0∞ := fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r) with hf
  set n := finrank ℝ V with hn
  have hl0 : ∀ r : ℝ, 0 < r → lam (closedBall (0 : V) r) ≠ 0 := fun r hr =>
    (measure_closedBall_pos lam 0 hr).ne'
  have hlt : ∀ r : ℝ, lam (closedBall (0 : V) r) ≠ ⊤ := fun r => measure_closedBall_lt_top.ne
  set b := limsup f (𝓝[>] (0 : ℝ)) with hb
  set a := liminf f (𝓝[>] (0 : ℝ)) with ha
  have hI : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := Ioo_mem_nhdsGT one_pos
  have hbtop : b ≠ ⊤ := by
    obtain ⟨δ, hδ, hQ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    obtain ⟨L, hL, h1, -⟩ := limsup_liminf_bounds lam nu (by norm_num) (by norm_num) hδ hQ
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL) h1
  have hba : b ≤ a := by
    have h1 : Tendsto (fun ε : ℝ => b * ENNReal.ofReal ((1 + (-1) * ε) ^ n)) (𝓝[>] 0) (𝓝 (b * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n (-1)) (Or.inl one_ne_zero)
    have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + 1 * ε) ^ n) * a) (𝓝[>] 0) (𝓝 (1 * a)) :=
      ENNReal.Tendsto.mul_const (tendsto_ofReal_pow n 1) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    rw [one_mul] at h2
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [hI] with ε hε
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε.1 hε.2
    obtain ⟨L, hL, h3, h4⟩ := limsup_liminf_bounds lam nu hε.1 hε.2 hδ hQ
    have e1 : (1 + (-1) * ε) = 1 - ε := by ring
    have e2 : (1 + 1 * ε) = 1 + ε := by ring
    rw [e1, e2]
    calc b * ENNReal.ofReal ((1 - ε) ^ n)
        ≤ (ENNReal.ofReal ((1 + ε) ^ n) * L) * ENNReal.ofReal ((1 - ε) ^ n) := by gcongr
      _ = ENNReal.ofReal ((1 + ε) ^ n) * (ENNReal.ofReal ((1 - ε) ^ n) * L) := by ring
      _ ≤ ENNReal.ofReal ((1 + ε) ^ n) * a := by gcongr
  have hft : Tendsto f (𝓝[>] 0) (𝓝 b) := tendsto_of_le_liminf_of_limsup_le hba le_rfl
  have hup : ∀ M : ℝ≥0, b < M → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      nu (closedBall (0 : V) r) ≤ M * lam (closedBall (0 : V) r) := by
    intro M hM
    filter_upwards [hft.eventually (gt_mem_nhds hM), self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.div_le_iff (hl0 r hr0) (hlt r)).mp hr.le
  have hdown : ∀ M : ℝ≥0, (M : ℝ≥0∞) < b → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      M * lam (closedBall (0 : V) r) ≤ nu (closedBall (0 : V) r) := by
    intro M hM
    filter_upwards [hft.eventually (lt_mem_nhds hM), self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hl0 r hr0)) (Or.inl (hlt r))).mp hr.le
  refine ⟨b, ?_, hbtop, ?_, ?_⟩
  · intro hb0
    obtain ⟨δ, hδ, hQ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    have hz : nu (ball (0 : V) δ) = 0 := by
      by_contra hne
      have hlb : lam (ball (0 : V) δ) ≠ ⊤ := measure_ball_lt_top.ne
      have hpos' : 0 < nu (ball (0 : V) δ) / lam (ball (0 : V) δ) :=
        ENNReal.div_pos hne hlb
      obtain ⟨M', hM'0, hM'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos'
      have hM'pos : 0 < M' := by exact_mod_cast hM'0
      have hlt' := ENNReal.mul_lt_of_lt_div hM'
      have hkpos : 0 < Real.toNNReal ((1 - 1 / 2 : ℝ) ^ n) := by
        rw [Real.toNNReal_pos]; positivity
      have := le_of_eventually_up lam nu (ε := 1 / 2) (by norm_num) hQ
        (M' * Real.toNNReal ((1 - 1 / 2 : ℝ) ^ n)) M'
        (by rw [ENNReal.coe_mul]; rfl)
        (hup _ (by rw [hb0]; exact_mod_cast mul_pos hM'pos hkpos)) (ball 0 δ) subset_rfl
      exact absurd hlt' (not_lt.mpr this)
    have h1 := hpos (δ / 2) (by linarith)
    have h2 : nu (closedBall (0 : V) (δ / 2)) ≤ nu (ball (0 : V) δ) :=
      measure_mono (closedBall_subset_ball (by linarith))
    rw [hz] at h2
    exact absurd h1 (not_lt.mpr h2)
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    have h1 : Tendsto (fun ε : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal ((1 + (-1) * ε) ^ n)) (𝓝[>] 0)
        (𝓝 ((C : ℝ≥0∞) * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n (-1)) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    obtain ⟨ε, hε, hε01⟩ := ((h1.eventually (lt_mem_nhds hC'2)).and hI).exists
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε01.1 hε01.2
    have e1 : (1 + (-1) * ε) = 1 - ε := by ring
    rw [e1] at hε
    exact ⟨δ, hδ, fun s hs => le_of_eventually_up lam nu hε01.2 hQ C' C hε.le (hup C' hC'1) s hs⟩
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    have h1 : Tendsto (fun ε : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal ((1 + 1 * ε) ^ n)) (𝓝[>] 0)
        (𝓝 ((C : ℝ≥0∞) * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n 1) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    obtain ⟨ε, hε, hε01⟩ := ((h1.eventually (gt_mem_nhds hC'1)).and hI).exists
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε01.1 hε01.2
    have e1 : (1 + 1 * ε) = 1 + ε := by ring
    rw [e1] at hε
    exact ⟨δ, hδ, fun s hs => le_of_eventually_down lam nu hε01.1 hQ C' C hε.le (hdown C' hC'2) s hs⟩

theorem tendsto_ratio {c : ℝ≥0∞}
    (hup : ∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s)
    (hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s)
    (S : ℝ → Set V) (hS : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ)
    (hS0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) :
    Tendsto (fun r => nu (S r) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    obtain ⟨δ, hδ, h⟩ := hdown C' hC'2
    filter_upwards [hS δ hδ, hS0] with r hr hr0
    exact lt_of_lt_of_le hC'1 ((ENNReal.le_div_iff_mul_le (Or.inl hr0.1) (Or.inl hr0.2)).mpr (h _ hr))
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    obtain ⟨δ, hδ, h⟩ := hup C' hC'1
    filter_upwards [hS δ hδ, hS0] with r hr hr0
    exact lt_of_le_of_lt ((ENNReal.div_le_iff hr0.1 hr0.2).mpr (h _ hr)) hC'2

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open Filter Topology Metric NormedSpace Asymptotics

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasStrictFDerivAt_exp_zero_alt : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
    ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero (𝕂 := ℝ)

variable (𝔸) in

def logA : 𝔸 → 𝔸 := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse _ _ _

theorem logA_exp : ∀ᶠ X in 𝓝 (0 : 𝔸), logA 𝔸 (exp X) = X :=
  (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).eventually_left_inverse

theorem exp_logA : ∀ᶠ h in 𝓝 (1 : 𝔸), exp (logA 𝔸 h) = h := by
  have := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).eventually_right_inverse
  rwa [exp_zero] at this

theorem logA_one : logA 𝔸 (1 : 𝔸) = 0 := by
  have := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse_apply_image
  rwa [exp_zero] at this

theorem hasStrict_logA : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (1 : 𝔸) := by
  have := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).to_localInverse
  rw [exp_zero] at this
  exact this

theorem exp_cont : Continuous (exp : 𝔸 → 𝔸) :=
  let _ := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exp_continuous

theorem exp_neg_mul (X : 𝔸) : exp (-X) * exp X = 1 := by
  letI := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]

theorem exp_mul_neg (X : 𝔸) : exp X * exp (-X) = 1 := by
  have := exp_neg_mul (-X)
  rwa [neg_neg] at this

def F1 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))

def F2 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp p.1 * exp p.2)

theorem hasStrict_exp_comp (L : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => exp (L p)) L (0 : 𝔸 × 𝔸) := by
  have h1 : HasStrictFDerivAt (exp : 𝔸 → 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (L 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero_alt
  exact h1.comp (0 : 𝔸 × 𝔸) L.hasStrictFDerivAt

theorem hasStrict_mul (L M : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => logA 𝔸 (exp (L p) * exp (M p))) (L + M) (0 : 𝔸 × 𝔸) := by
  have h := (hasStrict_exp_comp L).mul' (hasStrict_exp_comp M)
  have hv : ((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0 = 1 := by
    simp [exp_zero]
  have h1 : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸)
      (((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0) := by
    rw [hv]; exact hasStrict_logA
  refine (h1.comp (0 : 𝔸 × 𝔸) h).congr_fderiv ?_
  ext p <;> simp [exp_zero, add_comm]

theorem hasStrictFDerivAt_translateLog : HasStrictFDerivAt (F1 (𝔸 := 𝔸)) (ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := by
  have := hasStrict_mul (-(ContinuousLinearMap.fst ℝ 𝔸 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸)
  refine this.congr_fderiv ?_
  ext p <;> simp

theorem hasStrictFDerivAt_productLog : HasStrictFDerivAt (F2 (𝔸 := 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 :=
  hasStrict_mul (ContinuousLinearMap.fst ℝ 𝔸 𝔸) (ContinuousLinearMap.snd ℝ 𝔸 𝔸)

theorem eventually_pair {P : 𝔸 × 𝔸 → Prop} (h : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), P p) :
    ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ → P (X, Y) := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨δ, hδ, fun X Y hX hY => h _ ?_⟩
  rw [mem_ball_zero_iff, Prod.norm_def]
  exact max_lt hX hY

theorem strict_est {F : 𝔸 × 𝔸 → 𝔸} {F' : 𝔸 × 𝔸 →L[ℝ] 𝔸} (hF : HasStrictFDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
      ‖F (X, Y) - F (X, 0) - F' (0, Y)‖ ≤ ε * ‖Y‖ := by
  have h := hF.isLittleO.def hε
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨δ, hδ, fun X Y hX hY => ?_⟩
  have hm : (((X, Y), (X, 0)) : (𝔸 × 𝔸) × (𝔸 × 𝔸)) ∈ ball ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) δ := by
    rw [show ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) = 0 from rfl, mem_ball_zero_iff]
    simp only [Prod.norm_def, norm_zero]
    simp [hX, hY]
  have := h _ hm
  simpa [Prod.norm_def] using this

theorem distortion {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
    (exp (F1 (X, Y)) = exp (-X) * exp (X + Y) ∧ ‖F1 (X, Y) - Y‖ ≤ ε * ‖Y‖) ∧
    (exp (F2 (X, Y)) = exp X * exp Y ∧ ‖F2 (X, Y) - X - Y‖ ≤ ε * ‖Y‖) := by
  obtain ⟨δ1, h1, H1⟩ := strict_est (hasStrictFDerivAt_translateLog (𝔸 := 𝔸)) hε
  obtain ⟨δ2, h2, H2⟩ := strict_est (hasStrictFDerivAt_productLog (𝔸 := 𝔸)) hε
  have c1 : Tendsto (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) :=
      (exp_cont.comp continuous_fst.neg).mul (exp_cont.comp (continuous_fst.add continuous_snd))
    have h := this.tendsto 0
    simpa [exp_zero] using h
  have c2 : Tendsto (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) :=
      (exp_cont.comp continuous_fst).mul (exp_cont.comp continuous_snd)
    have h := this.tendsto 0
    simpa [exp_zero] using h
  obtain ⟨δ3, h3, H3⟩ := eventually_pair (c1.eventually exp_logA)
  obtain ⟨δ4, h4, H4⟩ := eventually_pair (c2.eventually exp_logA)
  obtain ⟨δ5, h5, H5⟩ := Metric.eventually_nhds_iff_ball.mp (logA_exp (𝔸 := 𝔸))
  refine ⟨min (min δ1 δ2) (min (min δ3 δ4) δ5), by positivity, fun X Y hX hY => ?_⟩
  simp only [lt_min_iff] at hX hY
  refine ⟨⟨H3 X Y hX.2.1.1 hY.2.1.1, ?_⟩, ⟨H4 X Y hX.2.1.2 hY.2.1.2, ?_⟩⟩
  · have := H1 X Y hX.1.1 hY.1.1
    have e : F1 (X, (0 : 𝔸)) = 0 := by simp [F1, exp_neg_mul, logA_one]
    simpa [e] using this
  · have := H2 X Y hX.1.2 hY.1.2
    have e : F2 (X, (0 : 𝔸)) = X := by
      simp only [F2, exp_zero, mul_one]
      exact H5 X (by simpa using hX.2.2)
    simpa [e] using this

end ReciprocityTheory.ChartRestriction.DS.HExp

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HExp

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
  · rintro ⟨X, hX, h⟩
    exact ⟨X, hX, C.emb.injective (by rw [mat_expG, h])⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, C.mat_expG X⟩

theorem expG_cont : Continuous C.expG := by
  rw [C.emb.isInducing.continuous_iff]
  have : C.mat ∘ C.expG = fun X : V => exp (X : 𝔸) := funext C.mat_expG
  rw [this]
  exact exp_cont.comp continuous_subtype_val

theorem exists_rho : ∃ ρ > 0, ∀ Z : 𝔸, ‖Z‖ < ρ →
    logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V) := by
  obtain ⟨ρ, hρ, h⟩ := Metric.eventually_nhds_iff_ball.mp ((logA_exp (𝔸 := 𝔸)).and C.H2)
  exact ⟨ρ, hρ, fun Z hZ => h Z (by simpa using hZ)⟩

variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))

include hR in
theorem injOn : InjOn C.expG (ball (0 : V) ρ) := by
  intro X hX Y hY h
  have hX' : ‖(X : 𝔸)‖ < ρ := by simpa using hX
  have hY' : ‖(Y : 𝔸)‖ < ρ := by simpa using hY
  have e : exp (X : 𝔸) = exp (Y : 𝔸) := by rw [← C.mat_expG, ← C.mat_expG, h]
  exact Subtype.ext (by rw [← (hR _ hX').1, e, (hR _ hY').1])

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]

include hR in
theorem meas_image {s : Set V} (hs : MeasurableSet s) (hsub : s ⊆ ball 0 ρ) :
    MeasurableSet (C.expG '' s) := by
  have : T2Space G := C.emb.t2Space
  exact hs.image_of_continuousOn_injOn C.expG_cont.continuousOn ((C.injOn hR).mono hsub)

def nu (ρ : ℝ) (μ : Measure G) : Measure V :=
  (μ.comap (fun x : ball (0 : V) ρ => C.expG x.1)).map Subtype.val

variable (μ : Measure G)

include hR in
theorem nu_apply {s : Set V} (hs : MeasurableSet s) :
    C.nu ρ μ s = μ (C.expG '' (s ∩ ball 0 ρ)) := by
  have hinj : Function.Injective (fun x : ball (0 : V) ρ => C.expG x.1) := fun x y h =>
    Subtype.ext (C.injOn hR x.2 y.2 h)
  have hm : ∀ t : Set (ball (0 : V) ρ), MeasurableSet t →
      MeasurableSet ((fun x : ball (0 : V) ρ => C.expG x.1) '' t) := by
    intro t ht
    have : (fun x : ball (0 : V) ρ => C.expG x.1) '' t = C.expG '' (Subtype.val '' t) := by
      rw [Set.image_image]
    rw [this]
    refine C.meas_image hR (MeasurableSet.subtype_image measurableSet_ball ht) ?_
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  rw [nu, Measure.map_apply measurable_subtype_coe hs,
    Measure.comap_apply _ hinj hm _ (measurable_subtype_coe hs)]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
  · rintro ⟨X, ⟨hX, hXρ⟩, rfl⟩
    exact ⟨⟨X, hXρ⟩, hX, rfl⟩

variable [IsTopologicalGroup G] [μ.IsHaarMeasure]

include hR in
theorem nu_finite : IsFiniteMeasure (C.nu ρ μ) := by
  refine ⟨?_⟩
  rw [C.nu_apply hR μ MeasurableSet.univ]
  refine lt_of_le_of_lt (measure_mono (Set.image_mono ?_))
    (((isCompact_closedBall (0 : V) ρ).image C.expG_cont).measure_lt_top (μ := μ))
  exact fun x hx => ball_subset_closedBall hx.2

include hR in
theorem nu_pos (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) : 0 < C.nu ρ μ (closedBall (0 : V) r) := by
  rw [C.nu_apply hR μ measurableSet_closedBall]
  have hc : ContinuousAt (logA 𝔸) (1 : 𝔸) := hasStrict_logA.hasFDerivAt.continuousAt
  have h1 : ∀ᶠ h in 𝓝 (1 : 𝔸), ‖logA 𝔸 h‖ < min r ρ := by
    have := hc.eventually (Metric.ball_mem_nhds (logA 𝔸 (1 : 𝔸)) (lt_min hr hρ))
    simpa [logA_one] using this
  have h2 : Tendsto C.mat (𝓝 (1 : G)) (𝓝 (1 : 𝔸)) := by
    have := C.emb.continuous.tendsto 1
    rwa [map_one] at this
  have h3 := h2.eventually (h1.and exp_logA)
  refine lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds μ h3) (measure_mono ?_)
  intro g hg
  have hg1 : ‖logA 𝔸 (C.mat g)‖ < min r ρ := hg.1
  have hg2 : exp (logA 𝔸 (C.mat g)) = C.mat g := hg.2
  have hV : logA 𝔸 (C.mat g) ∈ V := (hR _ (lt_of_lt_of_le hg1 (min_le_right _ _))).2 ⟨g, hg2.symm⟩
  refine ⟨⟨_, hV⟩, ⟨?_, ?_⟩, C.emb.injective (by rw [mat_expG]; exact hg2)⟩
  · rw [mem_closedBall_zero_iff]; exact (lt_of_lt_of_le hg1 (min_le_left _ _)).le
  · rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hg1 (min_le_right _ _)

include hR in
theorem nu_qinv (hρ : 0 < ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : ∃ δ > 0, QInv (C.nu ρ μ) ε δ := by
  obtain ⟨δ0, hδ0, hD⟩ := distortion (𝔸 := 𝔸) hε0
  refine ⟨min δ0 (ρ / 4), by positivity, fun X hX r hr0 hr => ?_⟩
  have hXδ : ‖(X : 𝔸)‖ < δ0 := lt_of_lt_of_le hX (min_le_left _ _)
  have hXρ : ‖(X : 𝔸)‖ < ρ / 4 := lt_of_lt_of_le hX (min_le_right _ _)
  have hrδ : r < δ0 := lt_of_lt_of_le hr (min_le_left _ _)
  have hrρ : r < ρ / 4 := lt_of_lt_of_le hr (min_le_right _ _)
  rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
    C.nu_apply hR μ measurableSet_closedBall]
  constructor
  · rw [← measure_preimage_mul μ (C.expG X)⁻¹ (C.expG '' (closedBall 0 r ∩ ball 0 ρ))]
    refine measure_mono ?_
    rintro _ ⟨W, ⟨hW, -⟩, rfl⟩
    set Y : V := W - X with hY
    have hYn : ‖(Y : 𝔸)‖ ≤ (1 - ε) * r := by
      have := mem_closedBall_iff_norm.mp hW
      exact this
    have hYr : ‖(Y : 𝔸)‖ < δ0 := by nlinarith
    obtain ⟨⟨e1, e2⟩, -⟩ := hD X Y hXδ hYr
    have hZn : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ ≤ r := by
      have h1 : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ ≤ ‖F1 ((X : 𝔸), (Y : 𝔸)) - Y‖ + ‖(Y : 𝔸)‖ := by
        have := norm_add_le (F1 ((X : 𝔸), (Y : 𝔸)) - Y) (Y : 𝔸)
        simpa using this
      have h2 : (1 + ε) * ((1 - ε) * r) ≤ r := by nlinarith [mul_pos hε0 hε0]
      nlinarith [norm_nonneg (Y : 𝔸)]
    have hXY : (X : 𝔸) + (Y : 𝔸) = (W : 𝔸) := by simp [hY]
    have hZV : F1 ((X : 𝔸), (Y : 𝔸)) ∈ V := by
      refine (hR _ (by linarith)).2 ⟨C.expG (-X) * C.expG W, ?_⟩
      rw [map_mul, mat_expG, mat_expG, e1, hXY]
      simp
    refine ⟨⟨_, hZV⟩, ⟨?_, ?_⟩, C.emb.injective ?_⟩
    · rw [mem_closedBall_zero_iff]; exact hZn
    · rw [mem_ball_zero_iff]
      have : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ < ρ := by linarith
      exact this
    · have hinv : C.mat (C.expG X)⁻¹ = exp (-(X : 𝔸)) := by
        have h1 : C.mat (C.expG X)⁻¹ * C.mat (C.expG X) = 1 := by rw [← map_mul]; simp
        rw [mat_expG] at h1
        calc C.mat (C.expG X)⁻¹ = C.mat (C.expG X)⁻¹ * (exp (X : 𝔸) * exp (-(X : 𝔸))) := by
              rw [exp_mul_neg, mul_one]
          _ = exp (-(X : 𝔸)) := by rw [← mul_assoc, h1, one_mul]
      rw [mat_expG, map_mul, hinv, mat_expG]
      show exp (F1 ((X : 𝔸), (Y : 𝔸))) = _
      rw [e1, hXY]
  · rw [← measure_preimage_mul μ (C.expG X) (C.expG '' (closedBall X ((1 + ε) * r) ∩ ball 0 ρ))]
    refine measure_mono ?_
    rintro _ ⟨Z, ⟨hZ, -⟩, rfl⟩
    have hZn : ‖(Z : 𝔸)‖ ≤ r := by
      have := mem_closedBall_zero_iff.mp hZ
      exact this
    obtain ⟨-, ⟨e1, e2⟩⟩ := hD X Z hXδ (lt_of_le_of_lt hZn hrδ)
    have h1 : ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ (1 + ε) * r := by
      have := norm_add_le (F2 ((X : 𝔸), (Z : 𝔸)) - X - Z) (Z : 𝔸)
      have e : F2 ((X : 𝔸), (Z : 𝔸)) - X - Z + Z = F2 ((X : 𝔸), (Z : 𝔸)) - X := by abel
      rw [e] at this
      nlinarith [norm_nonneg (Z : 𝔸)]
    have h2 : ‖F2 ((X : 𝔸), (Z : 𝔸))‖ < ρ := by
      have := norm_add_le (F2 ((X : 𝔸), (Z : 𝔸)) - X) (X : 𝔸)
      have e : F2 ((X : 𝔸), (Z : 𝔸)) - X + X = F2 ((X : 𝔸), (Z : 𝔸)) := by abel
      rw [e] at this
      nlinarith
    have hV : F2 ((X : 𝔸), (Z : 𝔸)) ∈ V := by
      refine (hR _ h2).2 ⟨C.expG X * C.expG Z, ?_⟩
      rw [map_mul, mat_expG, mat_expG, e1]
    refine ⟨⟨_, hV⟩, ⟨?_, ?_⟩, C.emb.injective ?_⟩
    · rw [mem_closedBall_iff_norm]; exact h1
    · rw [mem_ball_zero_iff]; exact h2
    · rw [mat_expG, map_mul, mat_expG, mat_expG]
      exact e1

theorem exists_density (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ (C.img (S r)) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  have := C.nu_finite hR μ
  obtain ⟨c, hc0, hct, hup, hdown⟩ := HExp.exists_density lam (C.nu ρ μ)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  refine ⟨c, hc0, hct, fun S hSm hS hS0 => ?_⟩
  refine (tendsto_ratio lam (C.nu ρ μ) hup hdown S hS hS0).congr' ?_
  filter_upwards [hS ρ hρ] with r hr
  rw [C.nu_apply hR μ (hSm r), Set.inter_eq_self_of_subset_left hr, img_eq]

theorem exists_density_unif (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ D : ℝ≥0, c < D → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        μ (C.img s) ≤ D * lam s) ∧
      (∀ D : ℝ≥0, (D : ℝ≥0∞) < c → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        D * lam s ≤ μ (C.img s)) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  have := C.nu_finite hR μ
  obtain ⟨c, hc0, hct, hup, hdown⟩ := HExp.exists_density lam (C.nu ρ μ)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  have key : ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) ρ → C.nu ρ μ s = μ (C.img s) := by
    intro s hs hsρ
    rw [C.nu_apply hR μ hs, Set.inter_eq_self_of_subset_left hsρ, img_eq]
  refine ⟨c, hc0, hct, fun D hD => ?_, fun D hD => ?_⟩
  · obtain ⟨δ, hδ, h⟩ := hup D hD
    refine ⟨min δ ρ, lt_min hδ hρ, fun s hsm hs => ?_⟩
    rw [← key s hsm (hs.trans (ball_subset_ball (min_le_right _ _)))]
    exact h s (hs.trans (ball_subset_ball (min_le_left _ _)))
  · obtain ⟨δ, hδ, h⟩ := hdown D hD
    refine ⟨min δ ρ, lt_min hδ hρ, fun s hsm hs => ?_⟩
    rw [← key s hsm (hs.trans (ball_subset_ball (min_le_right _ _)))]
    exact h s (hs.trans (ball_subset_ball (min_le_left _ _)))

end Chart

theorem Chart.exists_density_unif' {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ D : ℝ≥0, c < D → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        μ (C.img s) ≤ D * lam s) ∧
      (∀ D : ℝ≥0, (D : ℝ≥0∞) < c → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        D * lam s ≤ μ (C.img s)) :=
  C.exists_density_unif μ lam

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem inG_iff_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} :
    inG ε X ↔ ∀ i j, star (X j i) * sg ε j + sg ε i * X i j = 0 := by
  unfold inG Jm sg
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply] at this
  · intro h
    ext i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    exact h i j

theorem gMat_inG {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  rw [inG_iff_entry]
  intro i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, sg]
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢
  · apply Complex.ext <;> simp <;> split_ifs <;> simp
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
      split_ifs <;> ring
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢

def gCo (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Z a a).im, fun p => Z p.1.1 p.1.2), fun p => Z p.1.1 p.1.2)

theorem gCo_gMat {ε : Fin n → Bool} (s : GCo ε) : gCo ε (gMat s) = s := by
  obtain ⟨⟨w, x⟩, z⟩ := s
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gCo, gMat, kMat, pmat]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]

theorem gMat_gCo {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    gMat (gCo ε Z) = Z := by
  rw [inG_iff_entry] at hZ
  ext i j
  have hij := hZ i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, gCo, sg] at hij ⊢
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    cases hi : ε i <;> cases hj : ε j <;> simp [h, h1, h2, hi, hj] at hij ⊢ <;>
      first | linear_combination hij | linear_combination -hij
  · apply Complex.ext <;> simp
    · have := congrArg Complex.re hij
      cases hi : ε i <;> simp [hi] at this <;> linarith
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    simp [h, h1, h2.symm]
    split_ifs <;> simp

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem gMat_add {ε : Fin n → Bool} (s t : GCo ε) : gMat (s + t) = gMat s + gMat t := by
  ext a b
  simp only [gMat, Matrix.add_apply]
  simp only [kMat, pmat, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> (try simp only [Complex.ofReal_add, star_add, mul_add, neg_add, add_zero]) <;>
    (try ring)

theorem gMat_smul {ε : Fin n → Bool} (c : ℝ) (s : GCo ε) : gMat (c • s) = (RingHom.id ℝ c) • gMat s := by
  ext a b
  simp only [gMat, RingHom.id_apply, Matrix.add_apply, Matrix.smul_apply]
  simp only [kMat, pmat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
  split_ifs <;> (try simp only [Complex.real_smul, Complex.ofReal_mul, star_mul', Complex.star_def,
    Complex.conj_ofReal, smul_add, smul_zero, smul_neg, add_zero, mul_neg]) <;>
    (try simp only [smul_eq_mul, Complex.ofReal_mul]) <;> (try ring_nf)

def gL (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' := gMat_add
  map_smul' := gMat_smul

theorem gL_injective (ε : Fin n → Bool) : Function.Injective (gL ε) := by
  intro s t h
  have h' : gMat s = gMat t := h
  rw [← gCo_gMat s, ← gCo_gMat t, h']

abbrev gV (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := LinearMap.range (gL ε)

def gE (ε : Fin n → Bool) : GCo ε ≃ₗ[ℝ] gV ε := LinearEquiv.ofInjective (gL ε) (gL_injective ε)

def ujMat (ε : Fin n → Bool) : UJ ε →* Matrix (Fin n) (Fin n) ℂ :=
  (Units.coeHom _).comp (UJ ε).subtype

theorem ujMat_apply (ε : Fin n → Bool) (g : UJ ε) : ujMat ε g = toM g := rfl

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_inUJ_small (ε : Fin n → Bool) : ∀ᶠ Z in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ),
    inUJ ε (NormedSpace.exp Z) → inG ε Z := by
  unfold inG
  have hd : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) 0 := hasStrictFDerivAt_exp_zero
  obtain ⟨s, hs, hap⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))

  have hinj : ∀ x ∈ s, ∀ y ∈ s, NormedSpace.exp x = NormedSpace.exp y → x = y := by
    intro x hx y hy hxy
    have h := hap x hx y hy
    rw [hxy, sub_self] at h
    change ‖0 - (x - y)‖ ≤ ((1 / 2 : NNReal) : ℝ) * ‖x - y‖ at h
    rw [zero_sub, norm_neg, NNReal.coe_div, NNReal.coe_one, NNReal.coe_two] at h
    have h0 : ‖x - y‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - y)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hc1 : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => Jm ε * Zᴴ * Jm ε) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun Z : Matrix (Fin n) (Fin n) ℂ => Jm ε * Zᴴ * Jm ε) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    simpa using hcont.tendsto 0
  have hc2 : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => -Z) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : Matrix (Fin n) (Fin n) ℂ))
  filter_upwards [hc1.eventually hs, hc2.eventually hs] with Z h1 h2 hU
  unfold inUJ at hU
  have hE : NormedSpace.exp (Jm ε * Zᴴ * Jm ε) = NormedSpace.exp (-Z) := by
    have hL : Jm ε * (NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z = 1 := by
      calc Jm ε * (NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z
          = Jm ε * ((NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, hJJ]
    rw [show Jm ε * Zᴴ * Jm ε = Jm ε * Zᴴ * (Jm ε)⁻¹ by rw [hJi], Matrix.exp_conj _ _ hJu, hJi,
      Matrix.exp_conjTranspose, Matrix.exp_neg]
    exact (Matrix.inv_eq_left_inv hL).symm
  have hZ := hinj _ h1 _ h2 hE
  calc Zᴴ * Jm ε + Jm ε * Z = Jm ε * (Jm ε * Zᴴ * Jm ε) + Jm ε * Z := by
        simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    _ = 0 := by rw [hZ, Matrix.mul_neg, neg_add_cancel]

def ujChart (ε : Fin n → Bool) : Chart (gV ε) (UJ ε) where
  mat := ujMat ε
  emb := (isClosedEmbedding_toM ε).isEmbedding
  H1 := fun X => by
    obtain ⟨s, hs⟩ := X.2
    have h : NormedSpace.exp (gMat s) ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [range_toM]
      have := exp_smul_mem_UJset (gMat_inG s) 1
      simp only [Complex.ofReal_one, one_smul] at this
      exact this
    obtain ⟨g, hg⟩ := h
    refine ⟨g, ?_⟩
    rw [ujMat_apply, ← hs]
    exact hg
  H2 := by
    filter_upwards [exp_inUJ_small ε] with Z hZ hg
    obtain ⟨g, hg⟩ := hg
    have h1 : inUJ ε (ujMat ε g) := g.2
    rw [hg] at h1
    exact ⟨gCo ε Z, gMat_gCo (hZ h1)⟩

end Normed

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HExp

variable {n : ℕ}

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem haar_exp_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] :
    ∃ d : ℝ, 0 < d ∧ DensOn (fun S => μ (expSet S)) d := by
  letI mV : MeasurableSpace (gV ε) := borel _
  haveI : BorelSpace (gV ε) := ⟨rfl⟩
  let eC : GCo ε ≃L[ℝ] gV ε := (gE ε).toContinuousLinearEquiv
  let lam : Measure (gV ε) := Measure.map eC volume
  haveI : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hlamH : lam.IsAddHaarMeasure := eC.isAddHaarMeasure_map volume
  obtain ⟨c, hc0, hct, hup, hdown⟩ := (ujChart ε).exists_density_unif' inferInstance mV ⟨rfl⟩ _
    inferInstance inferInstance μ inferInstance lam (by exact hlamH)
  have himg : ∀ S : Set (GCo ε), (ujChart ε).img (eC '' S) = expSet S := by
    intro S
    ext g
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
      exact ⟨s, hs, h⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨eC s, ⟨s, hs, rfl⟩, h⟩
  have hmeas : ∀ S : Set (GCo ε), MeasurableSet S → MeasurableSet (eC '' S) := fun S hS =>
    eC.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS
  have hlam : ∀ S : Set (GCo ε), MeasurableSet S → lam (eC '' S) = volume S := by
    intro S hS
    rw [Measure.map_apply eC.continuous.measurable (hmeas S hS), Set.preimage_image_eq S eC.injective]
  have hsmall : ∀ δ > 0, ∃ δ' > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ') →
      eC '' S ⊆ ball (0 : gV ε) δ := by
    intro δ hδ
    obtain ⟨δ', hδ', h⟩ := Metric.continuousAt_iff.mp (eC.continuous.continuousAt (x := 0)) δ hδ
    refine ⟨δ', hδ', fun S hS => ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := h (x := s) (by simpa using hS s hs)
    simpa using this
  set d := c.toReal with hd
  have hdpos : 0 < d := ENNReal.toReal_pos hc0 hct
  have hc : c = ENNReal.ofReal d := (ENNReal.ofReal_toReal hct).symm
  refine ⟨d, hdpos, fun η hη => ?_⟩
  have hU : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      μ (expSet S) ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
    obtain ⟨δ, hδ, h⟩ := hup (Real.toNNReal ((1 + η) * d)) (by
      rw [hc]
      show ENNReal.ofReal d < ENNReal.ofReal ((1 + η) * d)
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      nlinarith)
    obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
    refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
    have := h (eC '' S) (hmeas S hS) (h' S hSδ)
    rw [himg, hlam S hS] at this
    exact this
  have hL : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      ENNReal.ofReal ((1 - η) * d) * volume S ≤ μ (expSet S) := by
    by_cases hη1 : (1 - η) * d ≤ 0
    · refine ⟨1, one_pos, fun S _ _ => ?_⟩
      rw [ENNReal.ofReal_of_nonpos hη1, zero_mul]
      exact bot_le
    · have hη1' : 0 < (1 - η) * d := not_le.mp hη1
      obtain ⟨δ, hδ, h⟩ := hdown (Real.toNNReal ((1 - η) * d)) (by
        rw [hc]
        show ENNReal.ofReal ((1 - η) * d) < ENNReal.ofReal d
        rw [ENNReal.ofReal_lt_ofReal_iff hdpos]
        nlinarith)
      obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
      refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
      have := h (eC '' S) (hmeas S hS) (h' S hSδ)
      rw [himg, hlam S hS] at this
      exact this
  obtain ⟨δ1, hδ1, h1⟩ := hU
  obtain ⟨δ2, hδ2, h2⟩ := hL
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun S hS hSδ => ⟨?_, ?_⟩⟩
  · exact h1 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_left _ _)
  · exact h2 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_right _ _)

end Normed

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.HPol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Log

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero.congr_fderiv (by ext; simp)

variable (n) in

def logM : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
  (exp_strict (n := n)).localInverse _ _ _

theorem logM_exp : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), logM n (NormedSpace.exp X) = X := by
  exact (exp_strict (n := n)).eventually_left_inverse

theorem exp_logM : ∀ᶠ h in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (logM n h) = h := by
  have h := (exp_strict (n := n)).eventually_right_inverse
  rw [NormedSpace.exp_zero] at h
  exact h

theorem logM_one : logM n 1 = 0 := by
  have h := (exp_strict (n := n)).localInverse_apply_image
  rw [NormedSpace.exp_zero] at h
  exact h

theorem logM_strict : HasStrictFDerivAt (logM n) (ContinuousLinearMap.id ℝ _) 1 := by
  have h := (exp_strict (n := n)).to_localInverse
  rw [NormedSpace.exp_zero] at h
  exact h

end Log

private theorem Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem Jm_inv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε := by
  exact Matrix.inv_eq_left_inv (Jm_mul_self_eq_one' ε)

theorem Jm_isUnit (ε : Fin n → Bool) : IsUnit (Jm ε) := by
  exact ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_one' ε, Jm_mul_self_eq_one' ε⟩, rfl⟩

theorem conjT_of_inG {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    Yᴴ = Jm ε * (-Y) * (Jm ε)⁻¹ := by
  have hJ := Jm_mul_self_eq_one' ε
  have h' : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left h'
  rw [Jm_inv]
  calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε * (-Y) * Jm ε := by rw [h1, Matrix.mul_neg]

theorem exp_inUJ {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  have hJ := Jm_mul_self_eq_one' ε
  show (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε
  rw [← Matrix.exp_conjTranspose, conjT_of_inG h, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv,
    Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem inG_of_exp {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hU : inUJ ε (NormedSpace.exp Y)) (h1 : ℓ (NormedSpace.exp Y) = Y)
    (h2 : ℓ (NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε)) = Jm ε * (-Yᴴ) * Jm ε) : inG ε Y := by
  have hJ := Jm_mul_self_eq_one' ε
  have hU' : (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε := hU
  have hEE : NormedSpace.exp Y * NormedSpace.exp (-Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl Y)), add_neg_cancel,
      NormedSpace.exp_zero]
  have key : NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε) = NormedSpace.exp Y := by
    have e1 : Jm ε * (-Yᴴ) * Jm ε = Jm ε * (-Y)ᴴ * (Jm ε)⁻¹ := by
      rw [Jm_inv, Matrix.conjTranspose_neg]
    rw [e1, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv, Matrix.exp_conjTranspose]
    calc Jm ε * (NormedSpace.exp (-Y))ᴴ * Jm ε
        = Jm ε * (NormedSpace.exp (-Y))ᴴ * ((NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y) := by
          rw [hU']
      _ = Jm ε * (NormedSpace.exp Y * NormedSpace.exp (-Y))ᴴ * Jm ε * NormedSpace.exp Y := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp Y := by
          rw [hEE, Matrix.conjTranspose_one, Matrix.mul_one, hJ, Matrix.one_mul]
  have hY : Y = Jm ε * (-Yᴴ) * Jm ε := by rw [← h2, key, h1]
  have h3 : Jm ε * Y = -(Yᴴ * Jm ε) := by
    calc Jm ε * Y = Jm ε * (Jm ε * (-Yᴴ) * Jm ε) := congrArg (Jm ε * ·) hY
      _ = -(Yᴴ * Jm ε) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.neg_mul]
  show Yᴴ * Jm ε + Jm ε * Y = 0
  rw [h3, add_neg_cancel]

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem entry_of_inG {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (i j : Fin n) :
    star (Y j i) * sg ε j + sg ε i * Y i j = 0 := by
  have h' := congrFun (congrFun (show Yᴴ * Jm ε + Jm ε * Y = 0 from h) i) j
  simpa [Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h'

theorem inG_of_entry' {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, star (Y j i) * sg ε j + sg ε i * Y i j = 0) : inG ε Y := by
  show Yᴴ * Jm ε + Jm ε * Y = 0
  ext i j
  simpa [Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

def cLin (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] GCo ε where
  toFun Y := ((fun a => (Y a a).im, fun ab => Y ab.1.1 ab.1.2), fun ab => Y ab.1.1 ab.1.2)
  map_add' _ _ := by
    ext <;> simp
  map_smul' _ _ := by
    ext <;> simp

theorem cLin_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cLin ε Y = ((fun a => (Y a a).im, fun ab => Y ab.1.1 ab.1.2), fun ab => Y ab.1.1 ab.1.2) := rfl

theorem cLin_gMat {ε : Fin n → Bool} (s : GCo ε) : cLin ε (gMat s) = s := by
  obtain ⟨⟨d, k⟩, p⟩ := s
  rw [cLin_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gMat, kMat, pmat]
  · funext ab
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    have h1 : a ≠ b := ne_of_gt hab.1
    have h2 : ¬ a < b := not_lt_of_gt hab.1
    simp [gMat, kMat, pmat, h1, h2, hab.1, hab.2]
  · funext ab
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    have h1 : a ≠ b := ne_of_gt hab.1
    have h2 : ¬ a < b := not_lt_of_gt hab.1
    simp [gMat, kMat, pmat, h1, h2, hab.1, hab.2]

theorem gMat_cLin {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    gMat (cLin ε Y) = Y := by
  ext a b
  have hE := entry_of_inG h a b
  rw [cLin_apply]
  simp only [gMat, kMat, pmat, Matrix.add_apply]
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 : a ≠ b := ne_of_lt hab
    have h2 : ¬ b < a := not_lt_of_gt hab
    cases ha : ε a <;> cases hb : ε b <;>
      simp only [sg, ha, hb, ↓reduceIte, Bool.false_eq_true] at hE <;>
      simp [ha, hb, h1, h2, hab] <;>
      (try simp only [Complex.star_def] at hE) <;>
      first | linear_combination hE | linear_combination -hE
  · have h0 : star (Y a a) + Y a a = 0 := by
      cases ha : ε a <;> simp only [sg, ha, ↓reduceIte, Bool.false_eq_true] at hE <;>
        first | linear_combination hE | linear_combination -hE
    have hre : (Y a a).re = 0 := by
      have h4 := congrArg Complex.re h0
      simp at h4
      linarith
    apply Complex.ext <;> simp [hre]
  · have h1 : a ≠ b := ne_of_gt hab
    have h2 : ¬ a < b := not_lt_of_gt hab
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, h1, h2, hab]

theorem sg_eq {ε : Fin n → Bool} {i j : Fin n} (h : ε i = ε j) : sg ε i = sg ε j := by
  simp [sg, h]

theorem sg_ne {ε : Fin n → Bool} {i j : Fin n} (h : ¬ ε i = ε j) : sg ε i = -sg ε j := by
  unfold sg
  cases hi : ε i <;> cases hj : ε j <;> simp_all

theorem inG_gMat {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  apply inG_of_entry'
  intro i j
  obtain ⟨⟨d, k⟩, p⟩ := s
  simp only [gMat, kMat, pmat, Matrix.add_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have h1 : i ≠ j := ne_of_lt hij
    have h2 : ¬ j < i := not_lt_of_gt hij
    by_cases hε : ε i = ε j
    · simp [hε, h1, h1.symm, h2, hij, sg_eq hε]
      ring
    · simp [hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]
      ring
  · simp <;> ring
  · have h1 : i ≠ j := ne_of_gt hij
    have h2 : ¬ i < j := not_lt_of_gt hij
    by_cases hε : ε i = ε j
    · simp [hε, h1, h1.symm, h2, hij, sg_eq hε]
      ring
    · simp [hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]
      ring

end ReciprocityTheory.ChartRestriction.DS.HPol
end
end

section
noncomputable section

open Matrix Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.HPol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pmat_zero' (ε : Fin n → Bool) : pmat (0 : PCoord ε → ℂ) = 0 := by
  ext a b; simp [pmat]

theorem kMat_zero' (ε : Fin n → Bool) : kMat (0 : KCo ε) = 0 := by
  ext a b; simp [kMat]

theorem gMat_fst {ε : Fin n → Bool} (w : KCo ε) : gMat ((w, 0) : GCo ε) = kMat w := by
  simp [gMat, pmat_zero']

theorem gMat_snd {ε : Fin n → Bool} (z : PCoord ε → ℂ) : gMat ((0, z) : GCo ε) = pmat z := by
  simp [gMat, kMat_zero']

def gLin (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' s t := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp <;> ring
  map_smul' c s := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul] <;> ring

theorem inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

theorem inUJ_pol {ε : Fin n → Bool} (s : GCo ε) :
    inUJ ε (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) := by
  rw [← gMat_fst, ← gMat_snd]
  exact inUJ_mul (exp_inUJ (inG_gMat _)) (exp_inUJ (inG_gMat _))

def Lm {ε : Fin n → Bool} (s : GCo ε) : GCo ε :=
  cLin ε (logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))

section An

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_comp_strict {ε : Fin n → Bool} (A : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (fun s => NormedSpace.exp (A s)) A 0 := by
  have h1 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (ContinuousLinearMap.id ℝ _) (A 0) := by
    rw [map_zero]; exact exp_strict
  exact h1.comp (0 : GCo ε) A.hasStrictFDerivAt

theorem prod_strict (ε : Fin n → Bool) :
    HasStrictFDerivAt (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2))
      (LinearMap.toContinuousLinearMap (gLin ε)) 0 := by
  let kL : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap ((gLin ε).comp ((LinearMap.inl ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  let pL : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap ((gLin ε).comp ((LinearMap.inr ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have ek : ∀ s : GCo ε, kL s = kMat s.1 := fun s => gMat_fst s.1
  have ep : ∀ s : GCo ε, pL s = pmat s.2 := fun s => gMat_snd s.2
  have h := (exp_comp_strict kL).mul' (exp_comp_strict pL)
  have hf : ((fun s : GCo ε => NormedSpace.exp (kL s)) * fun s => NormedSpace.exp (pL s)) =
      fun s => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2) := by
    funext s; rw [Pi.mul_apply, ek, ep]
  rw [hf] at h
  refine h.congr_fderiv (ContinuousLinearMap.ext fun s => ?_)
  have e0 : kMat (0 : GCo ε).1 = 0 := kMat_zero' ε
  have e1 : pmat (0 : GCo ε).2 = 0 := pmat_zero' ε
  change NormedSpace.exp (kL 0) * pL s + kL s * NormedSpace.exp (pL 0) = gMat s
  rw [ek, ep, ek, ep, e0, e1, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one, add_comm]
  rfl

theorem Lm_strict (ε : Fin n → Bool) :
    HasStrictFDerivAt (Lm (ε := ε)) (ContinuousLinearMap.id ℝ (GCo ε)) 0 := by
  have h0 : (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) 0 = 1 := by
    simp [kMat_zero', pmat_zero']
  have hl : HasStrictFDerivAt (logM n) (ContinuousLinearMap.id ℝ _)
      ((fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) 0) := by
    rw [h0]; exact logM_strict
  have h := (LinearMap.toContinuousLinearMap (cLin ε)).hasStrictFDerivAt.comp (0 : GCo ε)
    (hl.comp (0 : GCo ε) (prod_strict ε))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun s => ?_)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.id_apply,
    LinearMap.coe_toContinuousLinearMap']
  exact cLin_gMat s

end An

section An

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem Lm_exp (ε : Fin n → Bool) : ∀ᶠ s in 𝓝 (0 : GCo ε),
    NormedSpace.exp (gMat (Lm s)) = NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2) := by
  have hP0 : NormedSpace.exp (kMat (0 : GCo ε).1) * NormedSpace.exp (pmat (0 : GCo ε).2) = 1 := by
    simp [kMat_zero', pmat_zero']
  have hP : Tendsto (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2))
      (𝓝 0) (𝓝 1) := by
    have := (prod_strict ε).continuousAt.tendsto
    rwa [hP0] at this
  have hl : Tendsto (logM n) (𝓝 1) (𝓝 0) := by
    have := (logM_strict (n := n)).continuousAt.tendsto
    rwa [logM_one] at this
  have hΦ := hl.comp hP
  have hc : Continuous fun Y : Matrix (Fin n) (Fin n) ℂ => Jm ε * (-Yᴴ) * Jm ε :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose.neg).matrix_mul continuous_const
  have hJ : Tendsto (fun s : GCo ε =>
      Jm ε * (-(logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))ᴴ) * Jm ε)
      (𝓝 0) (𝓝 0) := by
    have := (hc.tendsto 0).comp hΦ
    simp only [Matrix.conjTranspose_zero, neg_zero, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this
  filter_upwards [hP.eventually exp_logM, hΦ.eventually logM_exp, hJ.eventually logM_exp]
    with s h1 h2 h3
  have hU : inUJ ε (NormedSpace.exp (logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))) := by
    rw [h1]; exact inUJ_pol s
  have hG := inG_of_exp (logM n) hU h2 h3
  show NormedSpace.exp (gMat (cLin ε _)) = _
  rw [gMat_cLin hG, h1]

end An

theorem polSet_eq_expSet (ε : Fin n → Bool) : ∃ δ > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ) →
    polSet S = expSet (Lm '' S) := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp (Lm_exp ε)
  refine ⟨δ, hδ, fun S hS => ?_⟩
  ext g
  constructor
  · rintro ⟨s, hs, hg⟩
    refine ⟨Lm s, ⟨s, hs, rfl⟩, ?_⟩
    rw [hg, h s (by simpa using hS s hs)]
  · rintro ⟨t, ⟨s, hs, rfl⟩, hg⟩
    refine ⟨s, hs, ?_⟩
    rw [hg, h s (by simpa using hS s hs)]

theorem Lm_zero (ε : Fin n → Bool) : Lm (0 : GCo ε) = 0 := by
  simp [Lm, kMat_zero', pmat_zero', logM_one]

instance borel_gco (ε : Fin n → Bool) : BorelSpace (GCo ε) := Prod.borelSpace

theorem volume_gco_isAddHaar (ε : Fin n → Bool) : (volume : Measure (GCo ε)).IsAddHaarMeasure := by
  have : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem image_est (ε : Fin n → Bool) {η : ℝ} (hη : 0 < η) : ∃ δ > 0, ∀ S : Set (GCo ε),
    MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      MeasurableSet (Lm '' S) ∧ (∀ s ∈ S, ‖Lm s‖ ≤ 2 * ‖s‖) ∧
      volume (Lm '' S) ≤ ENNReal.ofReal (1 + η) * volume S ∧
      ENNReal.ofReal (1 - η) * volume S ≤ volume (Lm '' S) := by
  have := volume_gco_isAddHaar ε
  set A := ContinuousLinearMap.id ℝ (GCo ε)
  have hdet : A.det = 1 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  have hm1 : ENNReal.ofReal |A.det| < ((Real.toNNReal (1 + η) : ℝ≥0) : ℝ≥0∞) := by
    rw [hdet, abs_one, ENNReal.ofReal_one]
    have : (1 : ℝ≥0) < Real.toNNReal (1 + η) := by
      rw [← Real.toNNReal_one]; exact (Real.toNNReal_lt_toNNReal_iff (by linarith)).2 (by linarith)
    exact_mod_cast this
  have hm2 : ((Real.toNNReal (1 - η) : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal |A.det| := by
    rw [hdet, abs_one, ENNReal.ofReal_one]
    have : Real.toNNReal (1 - η) < 1 := by
      rw [Real.toNNReal_lt_one]; linarith
    exact_mod_cast this
  have h1 := addHaar_image_le_mul_of_det_lt (volume : Measure (GCo ε)) A hm1
  have h2 := mul_le_addHaar_image_of_lt_det (volume : Measure (GCo ε)) A hm2
  have h3 : ∀ᶠ c in 𝓝[>] (0 : ℝ≥0), c < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)
  have h4 : ∀ᶠ c in 𝓝[>] (0 : ℝ≥0), 0 < c := self_mem_nhdsWithin
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := (h1.and (h2.and (h3.and h4))).exists
  obtain ⟨U, hU, hA⟩ := (Lm_strict ε).approximates_deriv_on_nhds (c := c) (Or.inr hc4)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hB := hA.mono_set hball
  refine ⟨δ, hδ, fun S hS hSδ => ?_⟩
  have hSb : S ⊆ ball 0 δ := fun s hs => mem_ball_zero_iff.mpr (hSδ s hs)
  have hAS := hB.mono_set hSb
  have hc1' : (c : ℝ) < 1 := by exact_mod_cast hc3
  have hinj : Set.InjOn Lm S := by
    intro x hx y hy hxy
    have h := hAS x hx y hy
    simp only [A, ContinuousLinearMap.id_apply, hxy, sub_self, zero_sub, norm_neg] at h
    have h0 : ‖x - y‖ = 0 := by
      have := norm_nonneg (x - y)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have : PolishSpace (KPair ε → ℂ) := inferInstance
  have : PolishSpace (PCoord ε → ℂ) := inferInstance
  have : PolishSpace (KCo ε) := inferInstance
  have : PolishSpace (GCo ε) := inferInstance
  refine ⟨hS.image_of_continuousOn_injOn hAS.continuousOn hinj, fun s hs => ?_, hc1 S Lm hAS,
    hc2 S Lm hAS⟩
  have h := hB s (hSb hs) 0 (mem_ball_self hδ)
  simp only [A, ContinuousLinearMap.id_apply, Lm_zero, sub_zero] at h
  have := norm_sub_norm_le (Lm s) s
  have := norm_nonneg s
  nlinarith

end ReciprocityTheory.ChartRestriction.DS.HPol
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Metric

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HPol

variable {n : ℕ}

theorem haar_pol_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (d : ℝ)
    (h : DensOn (fun S => μ (expSet S)) d) : DensOn (fun S => μ (polSet S)) d := by
  intro η hη
  set η' : ℝ := min (η / 3) (1 / 2) with hη'def
  have hη'0 : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη'1 : η' ≤ 1 / 2 := min_le_right _ _
  have hη'3 : η' ≤ η / 3 := min_le_left _ _
  obtain ⟨δ1, hδ1, hE⟩ := h η' hη'0
  obtain ⟨δ4, hδ4, hE2⟩ := h 2 (by norm_num)
  obtain ⟨δ2, hδ2, hI⟩ := HPol.image_est ε hη'0
  obtain ⟨δ3, hδ3, hP⟩ := HPol.polSet_eq_expSet ε
  refine ⟨min (min δ2 δ3) (min (δ1 / 2) (δ4 / 2)),
    lt_min (lt_min hδ2 hδ3) (lt_min (by positivity) (by positivity)), fun S hS hsmall => ?_⟩
  have hs2 : ∀ s ∈ S, ‖s‖ < δ2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_left _ _))
  have hs3 : ∀ s ∈ S, ‖s‖ < δ3 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : ∀ s ∈ S, ‖s‖ < δ1 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : ∀ s ∈ S, ‖s‖ < δ4 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hmeas, hnorm, hup, hlo⟩ := hI S hS hs2
  have hsm1 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ1 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs1 s hs
    linarith [hnorm s hs]
  have hsm4 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ4 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs4 s hs
    linarith [hnorm s hs]
  obtain ⟨hEu, hEl⟩ := hE _ hmeas hsm1
  beta_reduce at hEu hEl ⊢
  rw [hP S hs3]
  have hsq1 : (1 + η') * (1 + η') ≤ 1 + η := by nlinarith
  have hsq2 : 1 - η ≤ (1 - η') * (1 - η') := by nlinarith
  constructor
  · calc μ (expSet (HPol.Lm '' S)) ≤ ENNReal.ofReal ((1 + η') * d) * volume (HPol.Lm '' S) := hEu
      _ ≤ ENNReal.ofReal ((1 + η') * d) * (ENNReal.ofReal (1 + η') * volume S) := by gcongr
      _ = (ENNReal.ofReal ((1 + η') * d) * ENNReal.ofReal (1 + η')) * volume S := by
        rw [mul_assoc]
      _ ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
        gcongr
        rcases le_or_gt 0 d with hd | hd
        · rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc (1 + η') * d * (1 + η') = ((1 + η') * (1 + η')) * d := by ring
            _ ≤ (1 + η) * d := mul_le_mul_of_nonneg_right hsq1 hd
        · rw [ENNReal.ofReal_of_nonpos (by nlinarith), zero_mul]
          exact zero_le
  · rcases le_or_gt 0 d with hd | hd
    · calc ENNReal.ofReal ((1 - η) * d) * volume S
          ≤ (ENNReal.ofReal ((1 - η') * d) * ENNReal.ofReal (1 - η')) * volume S := by
            gcongr
            rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) hd)]
            apply ENNReal.ofReal_le_ofReal
            calc (1 - η) * d ≤ ((1 - η') * (1 - η')) * d := mul_le_mul_of_nonneg_right hsq2 hd
              _ = (1 - η') * d * (1 - η') := by ring
        _ = ENNReal.ofReal ((1 - η') * d) * (ENNReal.ofReal (1 - η') * volume S) := by
            rw [mul_assoc]
        _ ≤ ENNReal.ofReal ((1 - η') * d) * volume (HPol.Lm '' S) := by gcongr
        _ ≤ μ (expSet (HPol.Lm '' S)) := hEl
    ·
      obtain ⟨hE2u, hE2l⟩ := hE2 _ hmeas hsm4
      beta_reduce at hE2u hE2l
      have h3 : ENNReal.ofReal ((1 + 2) * d) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
      rw [h3, zero_mul] at hE2u
      have h0 : ENNReal.ofReal ((1 - 2) * d) * volume (HPol.Lm '' S) = 0 :=
        le_antisymm (hE2l.trans hE2u) (zero_le)
      have hpos : ENNReal.ofReal ((1 - 2) * d) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvL : volume (HPol.Lm '' S) = 0 := (mul_eq_zero.mp h0).resolve_left hpos
      rw [hvL] at hlo
      have hpos' : ENNReal.ofReal (1 - η') ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvS : volume S = 0 :=
        (mul_eq_zero.mp (le_antisymm hlo (zero_le))).resolve_left hpos'
      rw [hvS, mul_zero]
      exact zero_le

end ReciprocityTheory.ChartRestriction.DS
end
end
