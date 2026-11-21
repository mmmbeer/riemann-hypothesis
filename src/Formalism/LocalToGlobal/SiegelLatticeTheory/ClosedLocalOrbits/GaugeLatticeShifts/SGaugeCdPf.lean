import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfB
import Formalism.LocalRingCardinality.DataCD
import Mathlib

section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

theorem exists_split {n : ℕ} (ε : Fin n → Bool) : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false) := by
  refine ⟨Fintype.card {i // ε i = true}, Fintype.card {i // ¬ ε i = true},
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl (fun i : Fin n => ε i = true)), fun i => ?_, fun j => ?_⟩
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ((Fintype.equivFin {i // ε i = true}).symm i).2
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact Bool.eq_false_iff.2 ((Fintype.equivFin {i // ¬ ε i = true}).symm j).2

theorem cd_density (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D) {n P Q : ℕ} (ε : Fin n → Bool)
    (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (hD : L1BallDensity ε) (hM : L1BallMeasurable ε) (hL : LamVol ε e) (hS : SetEq ε e)
    {c : ℝ≥0∞} (hc : Formalism.BasicNotions.OmegaDensity (D.cd.cd P Q) c) :
    c = (D.s.cdScale n ε : ℝ≥0∞) * ENNReal.ofReal (gaugeU ε) := by
  obtain ⟨lam, hlam, ht⟩ := hc
  obtain ⟨s, hs, hMs⟩ := hM
  have hcongr : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (D.s.cdScale n ε : ℝ≥0∞) * (Formalism.REAL.muG ε (expC ε '' l1B ε r) / volume (l1B ε r)) =
      D.cd.cd P Q {g | ∃ X ∈ Formalism.BasicNotions.ballU P Q r,
        Formalism.BasicNotions.UpqT.mat g = NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
        lam (Formalism.BasicNotions.ballU P Q r) := by
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    rw [hL h1 h2 lam hlam r, ← hS h1 h2 r, ← hcd n ε P Q e h1 h2 _ (hMs r hr.2.le), Measure.smul_apply,
      smul_eq_mul, mul_div_assoc]
  exact tendsto_nhds_unique ht ((ENNReal.Tendsto.const_mul hD (Or.inr ENNReal.coe_ne_top)).congr' hcongr)

theorem cdScale_mass (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D) (m : ℕ)
    (hU : UpqIn (fun _ : Fin m => true) (Equiv.sumEmpty (Fin m) (Fin 0))) :
    (D.s.cdScale m (fun _ => true) : ℝ≥0∞) * Formalism.REAL.muG (fun _ : Fin m => true) univ = 1 := by
  have h1 : ∀ i : Fin m, (fun _ : Fin m => true) (Equiv.sumEmpty (Fin m) (Fin 0) (Sum.inl i)) = true :=
    fun _ => rfl
  have h2 : ∀ j : Fin 0, (fun _ : Fin m => true) (Equiv.sumEmpty (Fin m) (Fin 0) (Sum.inr j)) = false :=
    fun j => j.elim0
  have h := hcd m (fun _ => true) m 0 (Equiv.sumEmpty _ _) h1 h2 univ MeasurableSet.univ
  rw [Measure.smul_apply, smul_eq_mul] at h
  rw [h]
  have hu : {g : Formalism.BasicNotions.UpqT m 0 | ∃ a ∈ (univ : Set (Formalism.REAL.UJ (fun _ : Fin m => true))),
      umat a = Matrix.reindex (Equiv.sumEmpty (Fin m) (Fin 0)) (Equiv.sumEmpty (Fin m) (Fin 0))
        (Formalism.BasicNotions.UpqT.mat g)} = univ := by
    ext g
    simp only [mem_ofPred_eq, mem_univ, true_and, iff_true]
    exact hU h1 h2 g
  rw [hu]
  have := D.cd.prob m
  exact measure_univ

theorem cdGauge_of_parts (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D)
    (hD : ∀ {m : ℕ} (ε : Fin m → Bool), L1BallDensity ε) (hM : ∀ {m : ℕ} (ε : Fin m → Bool), L1BallMeasurable ε)
    (hL : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), LamVol ε e)
    (hS : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), SetEq ε e)
    (hU : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), UpqIn ε e)
    (n : ℕ) (ε : Fin n → Bool) : CdGauge D n ε := by
  obtain ⟨P, Q, e, h1, h2⟩ := exists_split ε
  obtain ⟨c, -, -, hcPQ, hcN⟩ := D.cd.trick P Q
  have hA := cd_density D hcd ε e h1 h2 (hD ε) (hM ε) (hL ε e) (hS ε e) hcPQ
  have hn : P + Q = n := by simpa using Fintype.card_congr e
  subst hn
  have h1t : ∀ i : Fin (P + Q),
      (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty (Fin (P + Q)) (Fin 0) (Sum.inl i)) = true := fun _ => rfl
  have h2t : ∀ j : Fin 0,
      (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty (Fin (P + Q)) (Fin 0) (Sum.inr j)) = false := fun j => j.elim0
  have hB := cd_density D hcd (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty _ _) h1t h2t (hD _) (hM _) (hL _ _)
    (hS _ _) hcN
  have hmass := cdScale_mass D hcd (P + Q) (hU _ _)
  have hu := (gauge_density_exists _ ε).2
  have hv := (gauge_density_exists _ (fun _ : Fin (P + Q) => true)).2
  have hab : (D.s.cdScale (P + Q) ε : ℝ) * gaugeU ε =
      (D.s.cdScale (P + Q) (fun _ => true) : ℝ) * gaugeU (fun _ : Fin (P + Q) => true) := by
    have h := congrArg ENNReal.toReal (hA.symm.trans hB)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hu.le, ENNReal.toReal_ofReal hv.le,
      ENNReal.coe_toReal, ENNReal.coe_toReal] at h
  have hb0 : (D.s.cdScale (P + Q) (fun _ => true) : ℝ≥0∞) ≠ 0 := by
    intro h; rw [h, zero_mul] at hmass; exact zero_ne_one hmass
  have hb : (D.s.cdScale (P + Q) (fun _ => true) : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.2 (ENNReal.coe_ne_zero.1 hb0)
  have hMe : Formalism.REAL.muG (fun _ : Fin (P + Q) => true) univ = (D.s.cdScale (P + Q) (fun _ => true) : ℝ≥0∞)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])
  have hMr : (Formalism.REAL.muG (fun _ : Fin (P + Q) => true) univ).toReal =
      ((D.s.cdScale (P + Q) (fun _ => true) : ℝ))⁻¹ := by
    rw [hMe, ENNReal.toReal_inv, ENNReal.coe_toReal]
  unfold CdGauge muGauge
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hv.le), hMr, hab]
  field_simp

end Formalism.MainNotions.S.Gauge
end
end

section
open MeasureTheory Filter Topology Set Function
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

theorem setForm0 (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ, 0 < s ∧ Set.InjOn (expC ε) (Metric.ball 0 s) ∧
    ∀ T : Set (EL ε), T ⊆ Metric.ball 0 s → MeasurableSet T →
      Formalism.REAL.muG ε (expC ε '' T) = ENNReal.ofReal c * ∫⁻ t in T, jd ε t := by
  have hN := chartNhd ε
  obtain ⟨s₀, hs₀, hL⟩ := locInvOf ε (transC ε) (jacInv ε)
  obtain ⟨ρ₀, hρ₀, hinj⟩ := injOn_thetaExp ε
  have hs : 0 < min s₀ ρ₀ := lt_min hs₀ hρ₀
  set s := min s₀ ρ₀ with hsdef
  have hLs : LocInv ε s := hL s hs (min_le_left _ _)
  have hinjs : Set.InjOn (expC ε) (Metric.ball 0 s) := by
    intro a ha b hb e
    apply hinj (Metric.ball_subset_ball (min_le_right _ _) ha) (Metric.ball_subset_ball (min_le_right _ _) hb)
    have := congrArg uMat e
    rw [uMat_expC, uMat_expC] at this
    exact Matrix.of.injective this
  have hVo : IsOpen (interior (expC ε '' Metric.ball (0 : EL ε) s)) := isOpen_interior
  have hVW : interior (expC ε '' Metric.ball (0 : EL ε) s) ⊆ expC ε '' Metric.ball (0 : EL ε) s := interior_subset
  have hV1 : (1 : Formalism.REAL.UJ ε) ∈ interior (expC ε '' Metric.ball (0 : EL ε) s) :=
    mem_interior_iff_mem_nhds.2 (hN s hs)
  set V := interior (expC ε '' Metric.ball (0 : EL ε) s) with hVdef
  have hcovN : ∀ x : Formalism.REAL.UJ ε, (fun h => x * h) '' V ∈ 𝓝 x := fun x =>
    ((isOpenMap_mul_left x) V hVo).mem_nhds ⟨1, hV1, mul_one x⟩
  have hOm' : ∀ y : Formalism.REAL.UJ ε, MeasurableSet ((fun h => y * h) '' V) := fun y =>
    ((isOpenMap_mul_left y) V hVo).measurableSet
  obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.countable_cover_nhds hcovN
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : (1 : Formalism.REAL.UJ ε) ∈ ⋃ x ∈ S, (fun h => x * h) '' V := by rw [hSU]; trivial
    rw [h] at this; simp at this
  obtain ⟨xs, hxs⟩ := hSc.exists_eq_range hSne
  let O : ℕ → Set (Formalism.REAL.UJ ε) := fun i => (fun h => xs i * h) '' V
  have hOU : ⋃ i, O i = univ := by rw [← hSU, hxs, Set.biUnion_range]
  have hD : ∀ i, MeasurableSet (disjointed O i) := MeasurableSet.disjointed fun i => hOm' (xs i)
  have hdisj : Pairwise (Disjoint on disjointed O) := disjoint_disjointed O
  have hcov : ⋃ i, disjointed O i = univ := by rw [iUnion_disjointed, hOU]
  have hDV : ∀ i, disjointed O i ⊆ (fun h => xs i * h) '' V := fun i => disjointed_subset O i
  haveI : Measure.IsMulLeftInvariant (nuG ε s xs (disjointed O)) := ⟨fun g => nuG_leftInv hLs hVW hD hdisj hcov hDV g⟩
  haveI : IsLocallyFiniteMeasure (nuG ε s xs (disjointed O)) := ⟨fun y => ⟨(fun h => y * h) '' V, hcovN y, by
      rw [nuG_eq hLs hVW hD hdisj hcov hDV y (hOm' y) (image_mono hVW)]
      calc (lamM ε s).map (fun h => y * h) ((fun h => y * h) '' V) ≤ (lamM ε s).map (fun h => y * h) univ :=
            measure_mono (subset_univ _)
        _ = lamM ε s univ := by rw [Measure.map_apply (measurable_const_mul y) MeasurableSet.univ, preimage_univ]
        _ < ∞ := lamM_univ_lt_top ε s⟩⟩
  haveI : Measure.IsHaarMeasure (Formalism.REAL.muG ε) := by unfold Formalism.REAL.muG; infer_instance
  have hνμ := Measure.isMulLeftInvariant_eq_smul (nuG ε s xs (disjointed O)) (Formalism.REAL.muG ε)
  set κ := Measure.haarScalarFactor (nuG ε s xs (disjointed O)) (Formalism.REAL.muG ε) with hκdef
  have hformT : ∀ T : Set (EL ε), T ⊆ Metric.ball 0 s → MeasurableSet T →
      nuG ε s xs (disjointed O) (expC ε '' T) = ∫⁻ t in T, jd ε t := by
    intro T hsub hT
    have hm : MeasurableSet (expC ε '' T) :=
      hT.image_of_continuousOn_injOn (continuous_expCG ε).continuousOn (hinjs.mono hsub)
    have hsubW : expC ε '' T ⊆ (fun h => (1 : Formalism.REAL.UJ ε) * h) '' (expC ε '' Metric.ball 0 s) := by
      simp only [one_mul, image_id']; exact image_mono hsub
    rw [nuG_eq hLs hVW hD hdisj hcov hDV 1 hm hsubW]
    have hmap : (lamM ε s).map (fun h => (1 : Formalism.REAL.UJ ε) * h) = lamM ε s := by
      simp only [one_mul]; exact Measure.map_id
    rw [hmap, lamM_applyG ε s hm]
    rw [show expC ε ⁻¹' (expC ε '' T) ∩ Metric.ball 0 s = T from ?_]
    ext t
    constructor
    · rintro ⟨⟨t', ht', e⟩, ht⟩
      rw [← hinjs (hsub ht') ht e]; exact ht'
    · intro ht; exact ⟨⟨t, ht, rfl⟩, hsub ht⟩
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1 ((continuous_chartJac_thetaExp ε).continuousAt (x := 0)) (1 / 2)
    (by norm_num)
  have hρ1 : 0 < min s η := lt_min hs hη
  have hpos : ∫⁻ t in Metric.ball (0 : EL ε) (min s η), jd ε t ≠ 0 := by
    have hle : ENNReal.ofReal (1 / 2) * volume (Metric.ball (0 : EL ε) (min s η)) ≤
        ∫⁻ t in Metric.ball (0 : EL ε) (min s η), jd ε t := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with t ht
      have := hcont (lt_of_lt_of_le ht (min_le_right _ _))
      rw [chartJac_thetaExp_zero, Real.dist_eq] at this
      exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 this).1])
    refine (lt_of_lt_of_le ?_ hle).ne'
    exact ENNReal.mul_pos (by simp) (Metric.measure_ball_pos _ _ hρ1).ne'
  have hκ : κ ≠ 0 := by
    intro h0
    apply hpos
    rw [← hformT _ (Metric.ball_subset_ball (min_le_left _ _)) measurableSet_ball, hνμ, h0, zero_smul]
    rfl
  have hκpos : (0 : ℝ) < (κ : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hκ)
  refine ⟨((κ : ℝ))⁻¹, inv_pos.2 hκpos, s, hs, hinjs, fun T hsub hT => ?_⟩
  have h1 := hformT T hsub hT
  rw [hνμ] at h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  rw [← h1, ← mul_assoc, ENNReal.ofReal_inv_of_pos hκpos, ENNReal.ofReal_coe_nnreal,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hκ) ENNReal.coe_ne_top, one_mul]

theorem setForm (ε : Fin n → Bool) : ∃ s : ℝ, 0 < s ∧ Set.InjOn (expC ε) (Metric.ball 0 s) ∧
    ∀ T : Set (EL ε), T ⊆ Metric.ball 0 s → MeasurableSet T →
      Formalism.REAL.muG ε (expC ε '' T) = ENNReal.ofReal (gaugeU ε) * ∫⁻ t in T, jd ε t := by
  obtain ⟨c, hc, s, hs, hinj, hT⟩ := setForm0 ε
  have hb : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      Formalism.REAL.muG ε (expSet ε (Metric.ball (0 : gLie ε) ρ)) = ENNReal.ofReal c * ∫⁻ t in Metric.ball (0 : EL ε) ρ, jd ε t := by
    intro ρ _ hρs
    rw [expSet_ball_eq_image]
    exact hT _ (Metric.ball_subset_ball hρs) measurableSet_ball
  have he := gaugeU_eq (tendsto_ratioAt_of_ball hc hs hb)
  rw [he]
  exact ⟨s, hs, hinj, hT⟩

theorem norm_le_two_l1_norm (ε : Fin n → Bool) (t : EL ε) : ‖t‖ ≤ 2 * ∑ i, ∑ j, ‖linT ε t i j‖ := by
  set x : EuclideanSpace ℝ (Fin n × Fin n × Bool) := ((obG ε).repr.symm t).1 with hx
  have h1 : ‖t‖ = ‖x‖ := by rw [hx]; exact ((obG ε).repr.symm.norm_map t).symm
  have h2 : ‖x‖ ≤ ∑ p, ‖x p‖ := by
    rw [EuclideanSpace.norm_eq]
    calc √(∑ p, ‖x p‖ ^ 2) ≤ √((∑ p, ‖x p‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _))
      _ = ∑ p, ‖x p‖ := Real.sqrt_sq (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have h3 : ∑ p, ‖x p‖ ≤ 2 * ∑ i, ∑ j, ‖linT ε t i j‖ := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Fintype.sum_bool, linT_apply]
    have hre : ‖x (i, j, false)‖ ≤ ‖unrealify x i j‖ := by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm (unrealify x i j)
    have him : ‖x (i, j, true)‖ ≤ ‖unrealify x i j‖ := by
      rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm (unrealify x i j)
    linarith
  linarith

theorem l1B_subset_ball_two_mul (ε : Fin n → Bool) (r : ℝ) : l1B ε r ⊆ Metric.ball 0 (2 * r) := fun t ht => by
  rw [mem_ball_zero_iff]
  have h := norm_le_two_l1_norm ε t
  have ht' : ∑ i, ∑ j, ‖linT ε t i j‖ < r := ht
  linarith

theorem continuous_matrixEntryAbsSum (ε : Fin n → Bool) : Continuous (fun t : EL ε => ∑ i, ∑ j, ‖linT ε t i j‖) := by
  refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
  exact ((continuous_apply j).comp ((continuous_apply i).comp (linT ε).continuous)).norm

theorem isOpen_l1B (ε : Fin n → Bool) (r : ℝ) : IsOpen (l1B ε r) := isOpen_lt (continuous_matrixEntryAbsSum ε) continuous_const

theorem zero_mem_l1B (ε : Fin n → Bool) {r : ℝ} (hr : 0 < r) : (0 : EL ε) ∈ l1B ε r := by
  show ∑ i, ∑ j, ‖linT ε 0 i j‖ < r
  simp [map_zero, hr]

theorem l1BallDensity_signs (ε : Fin n → Bool) : L1BallDensity ε := by
  obtain ⟨s, hs, _, hT⟩ := setForm ε
  have hJ : Tendsto (fun r : ℝ => (∫⁻ t in l1B ε r, jd ε t) / volume (l1B ε r)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
    intro e he
    obtain ⟨δ0, _, h0δ, hδe⟩ := ENNReal.lt_iff_exists_real_btwn.1 he
    have hδ0p : 0 < δ0 := ENNReal.ofReal_pos.1 h0δ
    have hδp : 0 < min δ0 (1 / 2) := lt_min hδ0p (by norm_num)
    have hδ1 : min δ0 (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hδe' : ENNReal.ofReal (min δ0 (1 / 2)) ≤ e := (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans hδe.le
    obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1 ((continuous_chartJac_thetaExp ε).continuousAt (x := 0))
      (min δ0 (1 / 2)) hδp
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < η / 2 by linarith)] with r hr
    have hsub : l1B ε r ⊆ Metric.ball 0 η :=
      (l1B_subset_ball_two_mul ε r).trans (Metric.ball_subset_ball (by linarith [hr.2]))
    have hbd : ∀ t ∈ l1B ε r, |chartJac (thetaExp ε) t - 1| < min δ0 (1 / 2) := by
      intro t ht
      have h := hcont (show dist t 0 < η from hsub ht)
      rwa [chartJac_thetaExp_zero, Real.dist_eq] at h
    have hm : MeasurableSet (l1B ε r) := (isOpen_l1B ε r).measurableSet
    have hV0 : volume (l1B ε r) ≠ 0 := ((isOpen_l1B ε r).measure_pos volume ⟨0, zero_mem_l1B ε hr.1⟩).ne'
    have hVt : volume (l1B ε r) ≠ ∞ := ((measure_mono (l1B_subset_ball_two_mul ε r)).trans_lt measure_ball_lt_top).ne
    have hup : ∫⁻ t in l1B ε r, jd ε t ≤ ENNReal.ofReal (1 + min δ0 (1 / 2)) * volume (l1B ε r) := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem hm] with t ht
      exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 (hbd t ht)).2])
    have hlo : ENNReal.ofReal (1 - min δ0 (1 / 2)) * volume (l1B ε r) ≤ ∫⁻ t in l1B ε r, jd ε t := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem hm] with t ht
      exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 (hbd t ht)).1])
    constructor
    · rw [ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVt)]
      refine le_trans ?_ hlo
      gcongr
      rw [ENNReal.ofReal_sub 1 hδp.le, ENNReal.ofReal_one]
      exact tsub_le_tsub_left hδe' 1
    · rw [ENNReal.div_le_iff hV0 hVt]
      refine hup.trans ?_
      gcongr
      rw [ENNReal.ofReal_add zero_le_one hδp.le, ENNReal.ofReal_one]
      gcongr
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (gaugeU ε) * ((∫⁻ t in l1B ε r, jd ε t) / volume (l1B ε r)))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (gaugeU ε) * 1)) :=
    ENNReal.Tendsto.const_mul hJ (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < s / 2 by linarith)] with r hr
  rw [hT _ ((l1B_subset_ball_two_mul ε r).trans (Metric.ball_subset_ball (by linarith [hr.2]))) (isOpen_l1B ε r).measurableSet,
    mul_div_assoc]

theorem l1BallMeasurable_signs (ε : Fin n → Bool) : L1BallMeasurable ε := by
  obtain ⟨s, hs, hinj, -⟩ := setForm ε
  refine ⟨s / 2, by linarith, fun r hr => ?_⟩
  have hsub : l1B ε r ⊆ Metric.ball 0 s := (l1B_subset_ball_two_mul ε r).trans (Metric.ball_subset_ball (by linarith))
  exact (isOpen_l1B ε r).measurableSet.image_of_continuousOn_injOn (continuous_expCG ε).continuousOn (hinj.mono hsub)

end Formalism.MainNotions.S.Gauge
end
end

section
open MeasureTheory Filter Topology Set Matrix

noncomputable section

namespace Formalism.MainNotions.S.Gauge

section Reindex

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem reindex_mul' (e : α ≃ β) (A B : Matrix α α ℂ) : reindex e e (A * B) = reindex e e A * reindex e e B := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem reindex_add' (e : α ≃ β) (A B : Matrix α α ℂ) : reindex e e (A + B) = reindex e e A + reindex e e B := by
  ext i j
  simp [Matrix.reindex_apply]

theorem reindex_zero' (e : α ≃ β) : reindex e e (0 : Matrix α α ℂ) = 0 := by
  ext i j
  simp [Matrix.reindex_apply]

theorem exp_reindex (e : α ≃ β) (X : Matrix α α ℂ) :
    NormedSpace.exp (reindex e e X) = reindex e e (NormedSpace.exp X) := by
  letI : NormedRing (Matrix α α ℂ) := Matrix.linftyOpNormedRing
  letI : NormedRing (Matrix β β ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix α α ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix β β ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix α α ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix β β ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : Continuous (Matrix.reindexAlgEquiv ℂ ℂ e) := by
    show Continuous fun M : Matrix α α ℂ => M.submatrix e.symm e.symm
    exact continuous_id.matrix_submatrix _ _
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) hc X).symm

theorem l1_entry_sum_reindex (e : α ≃ β) (X : Matrix α α ℂ) :
    ∑ i, ∑ j, ‖reindex e e X i j‖ = ∑ i, ∑ j, ‖X i j‖ := by
  calc ∑ i, ∑ j, ‖reindex e e X i j‖ = ∑ i, ∑ j, ‖X (e.symm i) (e.symm j)‖ := rfl
    _ = ∑ i, ∑ j, ‖X i (e.symm j)‖ := e.symm.sum_comp (fun i => ∑ j, ‖X i (e.symm j)‖)
    _ = ∑ i, ∑ j, ‖X i j‖ := Finset.sum_congr rfl fun i _ => e.symm.sum_comp (fun j => ‖X i j‖)

end Reindex

variable {n P Q : ℕ}

theorem reindex_Jpq (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true)
    (h2 : ∀ j, ε (e (Sum.inr j)) = false) : reindex e e (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨s, rfl⟩ := e.surjective i
  obtain ⟨t, rfl⟩ := e.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.UG.Jpq,
    Formalism.REAL.Jm, Matrix.diagonal_apply, e.injective.eq_iff]
  rcases s with s | s <;> rcases t with t | t <;>
    simp [h1, h2, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem lieU_iff (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true)
    (h2 : ∀ j, ε (e (Sum.inr j)) = false) (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ Formalism.BasicNotions.lieU P Q ↔ Formalism.REAL.inG ε (reindex e e X) := by
  have hJ := reindex_Jpq ε e h1 h2
  show Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔
    (reindex e e X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * reindex e e X = 0
  have hc : (reindex e e X)ᴴ = reindex e e Xᴴ := by
    simp [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [← hJ, hc, ← reindex_mul', ← reindex_mul', ← reindex_add', ← reindex_zero' e]
  exact (Matrix.reindex e e).injective.eq_iff.symm

theorem upqIn (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : UpqIn ε e := by
  unfold UpqIn
  intro h1 h2 g
  have hJ := reindex_Jpq ε e h1 h2
  let g' : Formalism.UG.Upq P Q := g
  have hct : ∀ M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  have hg : g.matᴴ * Formalism.UG.Jpq P Q * g.mat = Formalism.UG.Jpq P Q := by
    have h : Formalism.UG.cT (starRingEnd ℂ) g.mat * Formalism.UG.Jpq P Q * g.mat = Formalism.UG.Jpq P Q := g'.2
    rwa [hct] at h
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    Units.map (Matrix.reindexAlgEquiv ℂ ℂ e : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →* Matrix (Fin n) (Fin n) ℂ) g'.1
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) = reindex e e g.mat := rfl
  have hmem : u ∈ Formalism.REAL.UJ ε := by
    show (u : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * (u : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm ε
    have hc : (reindex e e g.mat)ᴴ = reindex e e g.matᴴ := by
      simp [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
    rw [hu, ← hJ, hc, ← reindex_mul', ← reindex_mul', hg]
  exact ⟨⟨u, hmem⟩, hu⟩

theorem setEq (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : SetEq ε e := by
  intro h1 h2 r
  ext g
  constructor
  · rintro ⟨a, ⟨t, ht, rfl⟩, hat⟩
    have hexp : umat (expC ε t) = NormedSpace.exp (linT ε t) := uMat_expC' ε t
    have hY : Formalism.REAL.inG ε (linT ε t) := by rw [linT_apply]; exact inG_of_gLie ε _
    have hXY : reindex e e ((reindex e e).symm (linT ε t)) = linT ε t := (reindex e e).apply_symm_apply _
    have hX : (reindex e e).symm (linT ε t) ∈ Formalism.BasicNotions.lieU P Q := (lieU_iff ε e h1 h2 _).2 (by rw [hXY]; exact hY)
    refine ⟨⟨_, hX⟩, ?_, ?_⟩
    · show ∑ i, ∑ j, ‖(reindex e e).symm (linT ε t) i j‖ < r
      rw [← l1_entry_sum_reindex e, hXY]; exact ht
    · apply (reindex e e).injective
      show reindex e e (Formalism.BasicNotions.UpqT.mat g) = reindex e e (NormedSpace.exp ((reindex e e).symm (linT ε t)))
      rw [← hat, hexp, ← exp_reindex, hXY]
  · rintro ⟨X, hXb, hgX⟩
    have hY : Formalism.REAL.inG ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) :=
      (lieU_iff ε e h1 h2 _).1 X.2
    refine ⟨expC ε (cM ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))), ⟨_, ?_, rfl⟩, ?_⟩
    · show ∑ i, ∑ j, ‖linT ε (cM ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) i j‖ < r
      rw [linT_cM hY, l1_entry_sum_reindex]; exact hXb
    · have hexp : umat (expC ε (cM ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))) =
          NormedSpace.exp (linT ε (cM ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))) :=
        uMat_expC' ε _
      rw [hexp, linT_cM hY, hgX, exp_reindex]

end Formalism.MainNotions.S.Gauge
end
end

section
namespace Formalism.MainNotions.S.Gauge

theorem cdGauge_of_lamVol (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D)
    (hL : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), LamVol ε e)
    (n : ℕ) (ε : Fin n → Bool) : CdGauge D n ε :=
  cdGauge_of_parts D hcd (fun ε => l1BallDensity_signs ε) (fun ε => l1BallMeasurable_signs ε) hL (fun ε e => setEq ε e) (fun ε e => upqIn ε e) n ε

end Formalism.MainNotions.S.Gauge
end

section
open Matrix

noncomputable section

namespace Formalism.MainNotions.S.Gauge.Cd

variable {P Q : ℕ}

local notation "ι" => Fin P ⊕ Fin Q

theorem jpq_sq : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  unfold Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp

def hs2 (Z : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (Z i j)



end Formalism.MainNotions.S.Gauge.Cd
end
end

section
open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge.CdV

variable {n P Q : ℕ}

local notation "ι" => Fin P ⊕ Fin Q

instance borelSpace_lieU (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩

section Alg

variable (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)

theorem jpq_eq (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.UG.Jpq P Q = (Formalism.REAL.Jm ε).submatrix e e := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j <;>
      simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, h, h1, h2, e.injective.eq_iff]
  · simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, e.injective.eq_iff]
  · simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, e.injective.eq_iff]
  · by_cases h : i = j <;>
      simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, h, h1, h2, e.injective.eq_iff]

theorem mem_lieU_iff (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Matrix (Fin n) (Fin n) ℂ) : X.submatrix e e ∈ Formalism.BasicNotions.lieU P Q ↔ Formalism.REAL.inG ε X := by
  show (X.submatrix e e)ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X.submatrix e e = 0 ↔ _
  rw [jpq_eq ε e h1 h2, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.inG
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (e.symm i)) (e.symm j)
    simpa using this
  · intro h
    ext i j
    have := congrFun (congrFun h (e i)) (e j)
    simpa using this

theorem inG_linT (t : EL ε) : Formalism.REAL.inG ε (linT ε t) := by
  rw [linT_apply]
  exact inG_of_gLie ε _

variable (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

def phiL : EL ε →ₗ[ℝ] Formalism.BasicNotions.lieU P Q where
  toFun t := ⟨(linT ε t).submatrix e e, (mem_lieU_iff ε e h1 h2 _).2 (inG_linT ε t)⟩
  map_add' s t := by
    apply Subtype.ext
    simp [Matrix.submatrix_add]
  map_smul' c t := by
    apply Subtype.ext
    simp [Matrix.submatrix_smul]


include h1 h2 in
theorem inG_back (Y : Formalism.BasicNotions.lieU P Q) :
    Formalism.REAL.inG ε ((Y : Matrix ι ι ℂ).submatrix e.symm e.symm) := by
  refine (mem_lieU_iff ε e h1 h2 _).1 ?_
  simpa [Matrix.submatrix_submatrix] using Y.2

def phiE : EL ε ≃ₗ[ℝ] Formalism.BasicNotions.lieU P Q :=
  { phiL ε e h1 h2 with
    invFun := fun Y => cM ε ((Y : Matrix ι ι ℂ).submatrix e.symm e.symm)
    left_inv := fun t => by
      show cM ε (((linT ε t).submatrix e e).submatrix e.symm e.symm) = t
      simpa [Matrix.submatrix_submatrix] using cM_linT ε t
    right_inv := fun Y => by
      apply Subtype.ext
      show (linT ε (cM ε ((Y : Matrix ι ι ℂ).submatrix e.symm e.symm))).submatrix e e = Y
      rw [linT_cM (inG_back ε e h1 h2 Y)]
      simp [Matrix.submatrix_submatrix] }

def phiC : EL ε ≃L[ℝ] Formalism.BasicNotions.lieU P Q := (phiE ε e h1 h2).toContinuousLinearEquiv

theorem phiC_coe (t : EL ε) : ((phiC ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) = (linT ε t).submatrix e e := rfl

theorem l1_entries_coordinate_chart (t : EL ε) :
    ∑ i, ∑ j, ‖((phiC ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) i j‖ = ∑ a, ∑ b, ‖linT ε t a b‖ := by
  rw [phiC_coe]
  exact Fintype.sum_equiv e _ _ (fun i => Fintype.sum_equiv e _ _ (fun j => rfl))

theorem preimage_ballU (r : ℝ) : (phiC ε e h1 h2) ⁻¹' Formalism.BasicNotions.ballU P Q r = l1B ε r := by
  ext t
  show (∑ i, ∑ j, ‖((phiC ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) i j‖ < r) ↔ _
  rw [l1_entries_coordinate_chart]
  rfl

theorem hilbert_schmidt_coordinate_chart (t : EL ε) :
    Cd.hs2 ((phiC ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) = ‖t‖ ^ 2 := by
  unfold Cd.hs2
  rw [phiC_coe]
  have e1 : ∑ i, ∑ j, Complex.normSq ((linT ε t).submatrix e e i j) = ∑ a, ∑ b, Complex.normSq (linT ε t a b) :=
    Fintype.sum_equiv e _ _ (fun i => Fintype.sum_equiv e _ _ (fun j => rfl))
  rw [e1, linT_apply]
  have hnorm : ‖t‖ = ‖(((obG ε).repr.symm t : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ := by
    rw [← LinearIsometryEquiv.norm_map (obG ε).repr.symm t]
    rfl
  rw [hnorm, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Real.norm_eq_abs, sq_abs, Formalism.MainNotions.S.unrealify, Complex.normSq_mk]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Alg

section Iso

variable (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

def mL : EL ε × EL ε →ₗ[ℝ] Matrix ι ι ℂ where
  toFun p := ((phiC ε e h1 h2 p.1 : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) +
    Complex.I • ((phiC ε e h1 h2 p.2 : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add, smul_add]; abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul, RingHom.id_apply, smul_add]
    rw [smul_comm c Complex.I]

theorem mL_apply (p : EL ε × EL ε) : mL ε e h1 h2 p = ((phiC ε e h1 h2 p.1 : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) +
    Complex.I • ((phiC ε e h1 h2 p.2 : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) := rfl

end Iso

def rL : Matrix ι ι ℂ →ₗ[ℝ] EuclideanSpace ℝ ((ι × ι) × Fin 2) where
  toFun Z := WithLp.toLp 2 (fun p => if p.2 = 0 then (Z p.1.1 p.1.2).re else (Z p.1.1 p.1.2).im)
  map_add' Z W := by
    ext p
    by_cases h : p.2 = 0 <;> simp [h]
  map_smul' c Z := by
    ext p
    by_cases h : p.2 = 0 <;> simp [h]

theorem rL_apply (Z : Matrix ι ι ℂ) (p : (ι × ι) × Fin 2) :
    rL Z p = if p.2 = 0 then (Z p.1.1 p.1.2).re else (Z p.1.1 p.1.2).im := rfl

theorem norm_rL_sq (Z : Matrix ι ι ℂ) : ‖rL Z‖ ^ 2 = Cd.hs2 Z := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [rL_apply, Real.norm_eq_abs, sq_abs]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  unfold Cd.hs2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Fin.sum_univ_two, Complex.normSq_apply, sq]

section Iso2

variable (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

def gL : WithLp 2 (EL ε × EL ε) →ₗ[ℝ] EuclideanSpace ℝ ((ι × ι) × Fin 2) :=
  rL.comp ((mL ε e h1 h2).comp (WithLp.linearEquiv 2 ℝ (EL ε × EL ε)).toLinearMap)

theorem gL_apply (w : WithLp 2 (EL ε × EL ε)) : gL ε e h1 h2 w = rL (mL ε e h1 h2 (WithLp.ofLp w)) := rfl

private theorem cross_lemma {A B : Matrix ι ι ℂ} (hA : A ∈ Formalism.BasicNotions.lieU P Q) (hB : B ∈ Formalism.BasicNotions.lieU P Q) :
    Cd.hs2 (A + Complex.I • B) = Cd.hs2 A + Cd.hs2 B := by
  let s : ι → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hJ : Formalism.UG.Jpq P Q = Matrix.diagonal s := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h, s]
    · simp [Formalism.UG.Jpq, Matrix.diagonal_apply, s]
    · simp [Formalism.UG.Jpq, Matrix.diagonal_apply, s]
    · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h, s]
  have hss : ∀ j, s j * s j = 1 := by
    intro j
    rcases j with j | j <;> simp [s]
  have key : ∀ {M : Matrix ι ι ℂ}, M ∈ Formalism.BasicNotions.lieU P Q → ∀ j k, star (M j k) = -(s k * s j * M k j) := by
    intro M hM j k
    have h := congrFun (congrFun (show Mᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * M = 0 from hM) k) j
    rw [hJ] at h
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply] at h
    linear_combination (s j) * h - star (M j k) * hss j
  have hT : (∑ j, ∑ k, A j k * star (B j k)).im = 0 := by
    have h1 : star (∑ j, ∑ k, A j k * star (B j k)) = ∑ j, ∑ k, A j k * star (B j k) := by
      simp only [star_sum, star_mul', star_star]
      simp only [key hA, key hB]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    exact Complex.conj_eq_iff_im.1 h1
  have hpt : ∀ j k, Complex.normSq ((A + Complex.I • B) j k) =
      Complex.normSq (A j k) + Complex.normSq (B j k) + 2 * (A j k * star (B j k)).im := by
    intro j k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  have hsum : ∑ j, ∑ k, (A j k * star (B j k)).im = 0 := by
    rw [← hT, Complex.im_sum]
    simp only [Complex.im_sum]
  unfold Cd.hs2
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero]

theorem norm_gL (w : WithLp 2 (EL ε × EL ε)) : ‖gL ε e h1 h2 w‖ = ‖w‖ := by
  have hsq : ‖gL ε e h1 h2 w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [gL_apply, norm_rL_sq, mL_apply, cross_lemma (phiC ε e h1 h2 _).2 (phiC ε e h1 h2 _).2, hilbert_schmidt_coordinate_chart, hilbert_schmidt_coordinate_chart,
      WithLp.prod_norm_sq_eq_of_L2]
    rfl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

private theorem jpq_sq_lemma : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

private theorem jpq_herm_lemma_2 : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem a_mem (Z : Matrix ι ι ℂ) :
    ((1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q)) ∈ Formalism.BasicNotions.lieU P Q := by
  have jj' : ∀ X : Matrix ι ι ℂ, Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, jpq_sq_lemma, Matrix.one_mul]
  show _ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * _ = 0
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, jpq_herm_lemma_2,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, jj', jpq_sq_lemma, Matrix.mul_one]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hs, ← smul_add]
  have : Zᴴ * Formalism.UG.Jpq P Q - Formalism.UG.Jpq P Q * Z + (Formalism.UG.Jpq P Q * Z - Zᴴ * Formalism.UG.Jpq P Q) = 0 := by abel
  rw [this, smul_zero]

theorem b_mem (Z : Matrix ι ι ℂ) :
    ((-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q)) ∈ Formalism.BasicNotions.lieU P Q := by
  have jj' : ∀ X : Matrix ι ι ℂ, Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, jpq_sq_lemma, Matrix.one_mul]
  show _ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * _ = 0
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, jpq_herm_lemma_2,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, jj', jpq_sq_lemma, Matrix.mul_one]
  have hs : star (-(Complex.I / 2)) = Complex.I / 2 := by
    first | (simp [Complex.conj_I]; done) | (simp [Complex.conj_I]; ring)
  rw [hs, neg_smul, add_comm (Formalism.UG.Jpq P Q * Z) (Zᴴ * Formalism.UG.Jpq P Q), add_neg_cancel]

theorem ab_sum (Z : Matrix ι ι ℂ) :
    (1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) +
      Complex.I • ((-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q)) = Z := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (-(Z i j + (Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) i j) / 2) * Complex.I_sq

theorem gL_surj : Function.Surjective (gL ε e h1 h2) := by
  intro y
  let Z : Matrix ι ι ℂ := fun i j => (y ((i, j), 0) : ℂ) + (y ((i, j), 1) : ℂ) * Complex.I
  let A : Formalism.BasicNotions.lieU P Q := ⟨_, a_mem Z⟩
  let B : Formalism.BasicNotions.lieU P Q := ⟨_, b_mem Z⟩
  refine ⟨WithLp.toLp 2 ((phiC ε e h1 h2).symm A, (phiC ε e h1 h2).symm B), ?_⟩
  rw [gL_apply, WithLp.ofLp_toLp, mL_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [show ((A : Matrix ι ι ℂ) + Complex.I • (B : Matrix ι ι ℂ)) = Z from ab_sum Z]
  ext p
  rw [rL_apply]
  rcases p with ⟨⟨i, j⟩, k⟩
  fin_cases k <;> simp [Z]

def gI : WithLp 2 (EL ε × EL ε) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ((ι × ι) × Fin 2) :=
  LinearIsometryEquiv.ofSurjective { toLinearMap := gL ε e h1 h2, norm_map' := norm_gL ε e h1 h2 } (gL_surj ε e h1 h2)

theorem gI_apply (w : WithLp 2 (EL ε × EL ε)) : gI ε e h1 h2 w = gL ε e h1 h2 w := rfl

end Iso2

section Meas

def MpCF (κ : Type) [Fintype κ] : Prop :=
  MeasurePreserving (fun y : EuclideanSpace ℝ (κ × Fin 2) => fun k => (y (k, 0) : ℂ) + (y (k, 1) : ℂ) * Complex.I)
    volume volume

variable (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

def aF (p : EL ε × EL ε) : (ι × ι) → ℂ := Formalism.BasicNotions.entries (mL ε e h1 h2 p)

private theorem mpT_lemma (m : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).prod volume) volume := by
  have hA := (PiLp.volume_preserving_ofLp (Fin m)).prod (PiLp.volume_preserving_ofLp (Fin m))
  have hB := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin m => (volume : Measure ℝ))
  have hC := PiLp.volume_preserving_toLp (Fin m ⊕ Fin m)
  have hJ := (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin m ⊕ Fin m => ℝ)).measurePreserving
  have := hJ.comp (hC.comp (hB.comp hA))
  convert this using 1
  all_goals first | rfl | (funext p; rfl)

theorem mp_aF (hC : MpCF (ι × ι)) :
    MeasurePreserving (aF ε e h1 h2) ((volume : Measure (EL ε)).prod volume) volume := by
  have hT := mpT_lemma (dimL ε)
  have hG := (gI ε e h1 h2).measurePreserving
  have := MeasurePreserving.comp hC (hG.comp hT)
  convert this using 1
  funext p
  funext k
  simp only [Function.comp_apply, gI_apply, gL_apply, WithLp.ofLp_toLp, aF, Formalism.BasicNotions.entries, rL_apply]
  simp [Complex.re_add_im]

theorem lamVol_of (hC : MpCF (ι × ι)) : LamVol ε e := by
  intro h1 h2 lam hlam r
  have hcl : IsClosed ((Formalism.BasicNotions.lieU P Q : Submodule ℝ (Matrix ι ι ℂ)) : Set (Matrix ι ι ℂ)) := by
    have : ((Formalism.BasicNotions.lieU P Q : Submodule ℝ (Matrix ι ι ℂ)) : Set (Matrix ι ι ℂ)) =
        {X | Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0} := rfl
    rw [this]
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)) continuous_const
  haveI : LocallyCompactSpace (Matrix ι ι ℂ) := inferInstanceAs (LocallyCompactSpace (ι → ι → ℂ))
  haveI : SecondCountableTopology (Matrix ι ι ℂ) := inferInstanceAs (SecondCountableTopology (ι → ι → ℂ))
  haveI : SecondCountableTopology (Formalism.BasicNotions.lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology ((Formalism.BasicNotions.lieU P Q : Submodule ℝ (Matrix ι ι ℂ)) : Set (Matrix ι ι ℂ))
  haveI : LocallyCompactSpace (Formalism.BasicNotions.lieU P Q) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := hlam.1
  have hφm : Measurable (phiC ε e h1 h2) := (phiC ε e h1 h2).continuous.measurable
  haveI hH : ((volume : Measure (EL ε)).map (phiC ε e h1 h2)).IsAddHaarMeasure := by
    first
    | infer_instance
    | exact (phiC ε e h1 h2).isAddHaarMeasure_map volume
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, lam = c • (volume : Measure (EL ε)).map (phiC ε e h1 h2) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul lam _⟩
  have hνν : ((volume : Measure (EL ε)).map (phiC ε e h1 h2)).prod ((volume : Measure (EL ε)).map (phiC ε e h1 h2)) =
      ((volume : Measure (EL ε)).prod volume).map (Prod.map (phiC ε e h1 h2) (phiC ε e h1 h2)) :=
    Measure.map_prod_map _ _ hφm hφm
  have hA : Continuous fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q => (ab.1 : Matrix ι ι ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hB : Continuous fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q => (ab.2 : Matrix ι ι ℂ) :=
    continuous_subtype_val.comp continuous_snd
  have hF' : Continuous (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
      (ab.1 : Matrix ι ι ℂ) + Complex.I • (ab.2 : Matrix ι ι ℂ)) := hA.add (hB.const_smul Complex.I)
  have hF : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix ι ι ℂ) + Complex.I • (ab.2 : Matrix ι ι ℂ))) :=
    (continuous_pi fun k : ι × ι => hF'.matrix_elem k.1 k.2).measurable
  have h := hlam.2
  rw [hc, Measure.prod_smul_left, Measure.prod_smul_right, hνν, Measure.map_smul, Measure.map_smul,
    Measure.map_map hF (hφm.prodMap hφm)] at h
  change c • c • Measure.map (aF ε e h1 h2) ((volume : Measure (EL ε)).prod volume) = volume at h
  rw [(mp_aF ε e h1 h2 hC).map_eq] at h
  have hK : 0 < volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1) := Metric.measure_closedBall_pos _ _ one_pos
  have hK' : volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1) ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  have hx : 0 < (volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1)).toReal := ENNReal.toReal_pos hK.ne' hK'
  have hv := congrArg (fun μ : Measure ((ι × ι) → ℂ) => (μ (Metric.closedBall 0 1)).toReal) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at hv
  have hcc : ((c : ℝ) * c) = 1 := by
    have h3 : ((c : ℝ) * c) * (volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1)).toReal =
        1 * (volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1)).toReal := by
      rw [one_mul]
      linear_combination hv
    exact mul_right_cancel₀ hx.ne' h3
  have hc1 : c = 1 := by
    have h0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  have hballm : MeasurableSet (Formalism.BasicNotions.ballU P Q r) := by
    apply IsOpen.measurableSet
    apply isOpen_lt _ continuous_const
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_subtype_val.matrix_elem i j).norm
  rw [hc, hc1, one_smul, Measure.map_apply hφm hballm, preimage_ballU]

end Meas

end Formalism.MainNotions.S.Gauge.CdV
end
end

section
open MeasureTheory Set

noncomputable section

namespace Formalism.MainNotions.S.Gauge

theorem mp_uncurry (κ : Type*) [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry κ (Fin 2) ℝ).symm volume volume := by
  refine ⟨(MeasurableEquiv.curry κ (Fin 2) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq (fun s _ => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : ((MeasurableEquiv.curry κ (Fin 2) ℝ).symm) ⁻¹' (univ.pi s) =
      univ.pi (fun k => univ.pi (fun i => s (k, i))) := by
    ext x; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
  rw [hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [Fintype.prod_prod_type]

theorem mp_cF (κ : Type*) [Fintype κ] :
    MeasurePreserving (fun y : EuclideanSpace ℝ (κ × Fin 2) => fun k => (y (k, 0) : ℂ) + (y (k, 1) : ℂ) * Complex.I)
      volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (ι := κ × Fin 2)
  have h2 := MeasurePreserving.symm _ (mp_uncurry κ)
  have h3 := volume_preserving_pi (fun _ : κ => Complex.volume_preserving_equiv_pi.symm)
  exact (h3.comp h2).comp h1

end Formalism.MainNotions.S.Gauge
end
end

section
noncomputable section

namespace Formalism.MainNotions.S.Gauge

theorem lamVol_of_sum_equiv {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : LamVol ε e :=
  CdV.lamVol_of ε e (mp_cF ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q)))

end Formalism.MainNotions.S.Gauge
end
end

section
namespace Formalism.MainNotions.S.Gauge

theorem complex_gauge_normalization (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D) (n : ℕ) (ε : Fin n → Bool) : CdGauge D n ε :=
  cdGauge_of_lamVol D hcd (fun ε e => lamVol_of_sum_equiv ε e) n ε

end Formalism.MainNotions.S.Gauge
end
