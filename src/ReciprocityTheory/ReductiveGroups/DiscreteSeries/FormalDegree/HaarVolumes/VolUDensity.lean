import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LeftMulMapEqTransposeConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriUniq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QrMapMeasurableSetImage
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DetNull
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import Lemmata.CurryModusPonens.CurryMp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalA

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.QRH

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def qrDom (N : ℕ) : Set (UNgrp N × TriCo N) := Set.univ ×ˢ triPos N

def glSet (N : ℕ) : Set (Fin N → Fin N → ℂ) := {Z | (Matrix.of Z).det ≠ 0}

theorem measurableSet_triPos : MeasurableSet (triPos N) := by
  unfold triPos
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)

theorem measurableSet_qrDom : MeasurableSet (qrDom N) :=
  MeasurableSet.univ.prod measurableSet_triPos

theorem continuous_det_of : Continuous fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det :=
  show Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => Z.det from continuous_id.matrix_det

theorem measurableSet_glSet : MeasurableSet (glSet N) :=
  (isOpen_ne_fun continuous_det_of continuous_const).measurableSet

theorem measurable_qrMap : Measurable (qrMap (N := N)) := qrMap_continuous.measurable

def qrW (p : qrDom N) : Fin N → Fin N → ℂ := qrMap p.1

theorem range_qrW : Set.range (qrW (N := N)) = glSet N := by
  rw [show Set.range (qrW (N := N)) = qrMap '' qrDom N by
    ext Z; constructor
    · rintro ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩]
  exact qrMap_image

theorem measurableEmbedding_qrW : MeasurableEmbedding (qrW (N := N)) where
  injective := by
    intro p q h
    exact Subtype.ext (qrMap_injOn p.2 q.2 h)
  measurable := measurable_qrMap.comp measurable_subtype_coe
  measurableSet_image' := by
    intro s hs
    have h1 : MeasurableSet (Subtype.val '' s : Set (UNgrp N × TriCo N)) :=
      (MeasurableEmbedding.subtype_coe measurableSet_qrDom).measurableSet_image' hs
    have h2 : qrW '' s = qrMap '' (Subtype.val '' s) := by
      rw [Set.image_image]; rfl
    rw [h2]
    refine qrMap_measurableSet_image _ h1 ?_
    rintro _ ⟨p, _, rfl⟩
    exact p.2

def nuW (N : ℕ) : Measure (qrDom N) := (gmMeas N).comap qrW

def nuQR (N : ℕ) : Measure (UNgrp N × TriCo N) := (nuW N).map Subtype.val

theorem map_qrW_nuW : (nuW N).map qrW = (gmMeas N).restrict (glSet N) := by
  rw [nuW, measurableEmbedding_qrW.map_comap, range_qrW]

theorem map_qrMap_nuQR : (nuQR N).map qrMap = (gmMeas N).restrict (glSet N) := by
  rw [nuQR, Measure.map_map measurable_qrMap measurable_subtype_coe]
  exact map_qrW_nuW

theorem nuQR_apply (s : Set (UNgrp N × TriCo N)) (hs : MeasurableSet s) :
    nuQR N s = gmMeas N (qrW '' (Subtype.val ⁻¹' s)) := by
  rw [nuQR, Measure.map_apply measurable_subtype_coe hs, nuW, measurableEmbedding_qrW.comap_apply]

theorem nuQR_map_eq (φ : UNgrp N × TriCo N → UNgrp N × TriCo N) (hφ : Measurable φ)
    (hφW : ∀ p ∈ qrDom N, φ p ∈ qrDom N) (ψ : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ))
    (hψ : Measurable ψ) (hψm : (gmMeas N).map ψ = gmMeas N) (hψG : ψ ⁻¹' glSet N = glSet N)
    (hcomm : ∀ p ∈ qrDom N, qrMap (φ p) = ψ (qrMap p)) :
    (nuQR N).map φ = nuQR N := by
  let φW : qrDom N → qrDom N := fun p => ⟨φ p.1, hφW p.1 p.2⟩
  have hφWm : Measurable φW := (hφ.comp measurable_subtype_coe).subtype_mk
  have key : (nuW N).map φW = nuW N := by
    have h1 : ((nuW N).map φW).map qrW = (nuW N).map qrW := by
      rw [Measure.map_map measurableEmbedding_qrW.measurable hφWm]
      have hc : qrW ∘ φW = ψ ∘ qrW := by
        funext p; exact hcomm p.1 p.2
      rw [hc, ← Measure.map_map hψ measurableEmbedding_qrW.measurable, map_qrW_nuW]
      conv_lhs => rw [← hψG]
      rw [← Measure.restrict_map hψ measurableSet_glSet, hψm]
    have h2 := congrArg (fun m => m.comap qrW) h1
    simp only [measurableEmbedding_qrW.comap_map] at h2
    exact h2
  rw [nuQR, Measure.map_map hφ measurable_subtype_coe]
  have : φ ∘ Subtype.val = Subtype.val ∘ φW := rfl
  rw [this, ← Measure.map_map measurable_subtype_coe hφWm, key]

theorem det_toM_ne_zero (k : UNgrp N) : (toM k).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (k : (Matrix (Fin N) (Fin N) ℂ)ˣ).isUnit).ne_zero

theorem det_upMat (t : TriCo N) : (upMat t).det = ∏ j, ((t.1 j : ℝ) : ℂ) := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upMat]
  · intro a b hba
    have h1 : a ≠ b := ne_of_gt hba
    have h2 : ¬ a < b := not_lt.mpr (le_of_lt hba)
    simp [upMat, h1, h2]

theorem det_upMat_ne_zero (t : TriCo N) (ht : t ∈ triPos N) : (upMat t).det ≠ 0 := by
  rw [det_upMat]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => by
    exact_mod_cast (ne_of_gt (ht j))

theorem continuous_upMat : Continuous (upMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [upMat]
  split_ifs with h1 h2
  · exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const

theorem continuous_triCoOf : Continuous (triCoOf (N := N)) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun ab => ?_)
  · exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply j))
  · exact (continuous_apply _).comp (continuous_apply _)

def triR (t0 : TriCo N) (t : TriCo N) : TriCo N := triCoOf (upMat t * upMat t0)

theorem continuous_triR (t0 : TriCo N) : Continuous (triR t0) :=
  continuous_triCoOf.comp (continuous_upMat.matrix_mul continuous_const)

theorem measurable_mulLeft_mat (g : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z) := by
  have hc : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z) := by
    exact (continuous_const.matrix_mul continuous_id : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => g * Z)
  exact hc.measurable

theorem measurable_mulRight_mat (g : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g) := by
  have hc : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g) := by
    exact (continuous_id.matrix_mul continuous_const : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => Z * g)
  exact hc.measurable

theorem nuQR_map_left (k0 : UNgrp N) :
    (nuQR N).map (fun p : UNgrp N × TriCo N => (k0 * p.1, p.2)) = nuQR N := by
  refine nuQR_map_eq _ ((measurable_const_mul k0).comp measurable_fst |>.prodMk measurable_snd)
    (fun p hp => ⟨trivial, hp.2⟩) (fun Z => Matrix.of.symm (toM k0 * Matrix.of Z))
    (measurable_mulLeft_mat _) (gmMeas_map_mul_left _ (det_toM_ne_zero k0)) ?_ ?_
  · ext Z
    simp only [glSet, Set.mem_preimage, Set.mem_ofPred_eq]
    change (toM k0 * Matrix.of Z).det ≠ 0 ↔ _
    rw [Matrix.det_mul]
    exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (det_toM_ne_zero k0) h⟩
  · intro p _
    simp only [qrMap]
    change Matrix.of.symm (toM (k0 * p.1) * upMat p.2) = Matrix.of.symm (toM k0 * (toM p.1 * upMat p.2))
    rw [← Matrix.mul_assoc]; rfl

theorem nuQR_map_right (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    (nuQR N).map (fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2)) = nuQR N := by
  refine nuQR_map_eq _ (measurable_fst.prodMk ((continuous_triR t0).measurable.comp measurable_snd))
    ?_ (fun Z => Matrix.of.symm (Matrix.of Z * upMat t0))
    (measurable_mulRight_mat _) (gmMeas_map_mul_right _ (det_upMat_ne_zero t0 h0)) ?_ ?_
  · intro p hp
    refine ⟨trivial, fun j => ?_⟩
    change 0 < (triR t0 p.2).1 j
    rw [triR, (upMat_triCoOf_mul p.2 t0).2 j]
    exact mul_pos (hp.2 j) (h0 j)
  · ext Z
    simp only [glSet, Set.mem_preimage, Set.mem_ofPred_eq]
    change (Matrix.of Z * upMat t0).det ≠ 0 ↔ _
    rw [Matrix.det_mul]
    exact ⟨fun h => left_ne_zero_of_mul h, fun h => mul_ne_zero h (det_upMat_ne_zero t0 h0)⟩
  · intro p _
    simp only [qrMap, triR]
    rw [(upMat_triCoOf_mul p.2 t0).1]
    change Matrix.of.symm (toM p.1 * (upMat p.2 * upMat t0)) = Matrix.of.symm ((toM p.1 * upMat p.2) * upMat t0)
    rw [Matrix.mul_assoc]

def kap (N : ℕ) : Measure (TriCo N) := (nuQR N).map Prod.snd

theorem kap_compl : kap N (triPos N)ᶜ = 0 := by
  rw [kap, Measure.map_apply measurable_snd measurableSet_triPos.compl,
    nuQR_apply _ (measurable_snd measurableSet_triPos.compl)]
  have : (Subtype.val ⁻¹' (Prod.snd ⁻¹' (triPos N)ᶜ) : Set (qrDom N)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp p.2.2
  rw [this, Set.image_empty, measure_empty]

theorem kap_compact [CompactSpace (UNgrp N)] (K : Set (TriCo N)) (hK : IsCompact K)
    (hKs : K ⊆ triPos N) : kap N K < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [kap, Measure.map_apply measurable_snd hKm, nuQR_apply _ (measurable_snd hKm)]
  refine lt_of_le_of_lt (measure_mono ?_) (gmMeas_compact_lt_top (qrMap '' (Set.univ ×ˢ K))
    ((isCompact_univ.prod hK).image qrMap_continuous) ?_)
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.1, ⟨trivial, hp⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    have : qrMap p ∈ qrMap '' (Set.univ ×ˢ triPos N) := ⟨p, ⟨trivial, hKs hp.2⟩, rfl⟩
    rw [qrMap_image] at this
    exact this

theorem kap_inv (t0 : TriCo N) (h0 : t0 ∈ triPos N) : (kap N).map (triR t0) = kap N := by
  have hm : Measurable fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2) :=
    measurable_fst.prodMk ((continuous_triR t0).measurable.comp measurable_snd)
  rw [kap, Measure.map_map (continuous_triR t0).measurable measurable_snd]
  have : triR t0 ∘ Prod.snd = Prod.snd ∘ (fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2)) := rfl
  rw [this, ← Measure.map_map measurable_snd hm, nuQR_map_right t0 h0]

theorem kap_eq [CompactSpace (UNgrp N)] : ∃ c : ENNReal, c ≠ ⊤ ∧ kap N = c • triMeas N :=
  triMeas_unique (kap N) kap_compl kap_compact (fun t0 h0 => kap_inv t0 h0)

theorem nuQR_rect (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    [CompactSpace (UNgrp N)] (s : Set (UNgrp N)) (hs : MeasurableSet s) (t : Set (TriCo N))
    (ht : MeasurableSet t) (hfin : kap N t < ⊤) : nuQR N (s ×ˢ t) = μ s * kap N t := by
  set ρ : Measure (UNgrp N) := ((nuQR N).restrict (Prod.snd ⁻¹' t)).map Prod.fst with hρ
  have hρA : ∀ A, MeasurableSet A → ρ A = nuQR N (A ×ˢ t) := by
    intro A hA
    rw [hρ, Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
    rfl
  have hρu : ρ Set.univ = kap N t := by
    rw [hρA _ MeasurableSet.univ, kap, Measure.map_apply measurable_snd ht, Set.univ_prod]
  have : IsFiniteMeasure ρ := ⟨by rw [hρu]; exact hfin⟩
  have : ρ.IsMulLeftInvariant := ⟨fun g => by
    have hL : Measurable fun p : UNgrp N × TriCo N => (g * p.1, p.2) :=
      ((measurable_const_mul g).comp measurable_fst).prodMk measurable_snd
    rw [hρ, Measure.map_map (measurable_const_mul g) measurable_fst]
    have : (fun x => g * x) ∘ Prod.fst =
        Prod.fst ∘ (fun p : UNgrp N × TriCo N => (g * p.1, p.2)) := rfl
    rw [this, ← Measure.map_map measurable_fst hL]
    congr 1
    have := Measure.restrict_map (μ := nuQR N) hL (measurable_snd ht)
    rw [nuQR_map_left] at this
    exact this.symm⟩
  have hsm := Measure.isMulInvariant_eq_smul_of_compactSpace ρ μ
  have hc : ρ.haarScalarFactor μ = kap N t := by
    have := congrArg (fun m : Measure (UNgrp N) => m Set.univ) hsm
    simp only [Measure.smul_apply, measure_univ] at this
    rw [← hρu, this]
    simp
  rw [← hρA s hs, hsm, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, mul_comm]

theorem nuQR_eq_prod (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    [CompactSpace (UNgrp N)] [SigmaFinite (kap N)] : μ.prod (kap N) = nuQR N := by
  refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
    (D := {t | MeasurableSet t ∧ kap N t < ⊤}) MeasurableSpace.generateFrom_measurableSet ?_
    MeasurableSpace.isPiSystem_measurableSet ?_ μ.toFiniteSpanningSetsIn
    ((kap N).toFiniteSpanningSetsIn.mono' fun t ht => ⟨ht.1, ht.2⟩) ?_
  · refine le_antisymm (MeasurableSpace.generateFrom_le fun t ht => ht.1) fun t ht => ?_
    rw [← Set.inter_univ t, ← iUnion_spanningSets (kap N), Set.inter_iUnion]
    exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
      ⟨ht.inter (measurableSet_spanningSets (kap N) n),
        lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_spanningSets_lt_top (kap N) n)⟩
  · intro s hs t ht _
    exact ⟨hs.1.inter ht.1, lt_of_le_of_lt (measure_mono Set.inter_subset_left) hs.2⟩
  · intro s hs t ht
    exact nuQR_rect μ s hs t ht.1 ht.2



theorem norm_det_toM (k : UNgrp N) : ‖(toM k).det‖ = 1 := by
  have hk : inUJ (fun _ : Fin N => true) (toM k) := k.2
  have hJ : Jm (fun _ : Fin N => true) = 1 := by
    unfold Jm; simp
  unfold inUJ at hk
  rw [hJ, Matrix.mul_one] at hk
  have h1 := congrArg Matrix.det hk
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h1
  have h2 : Complex.normSq (toM k).det = 1 := by
    have h3 := Complex.normSq_eq_conj_mul_self (z := (toM k).det)
    have h4 : ((Complex.normSq (toM k).det : ℝ) : ℂ) = 1 := by rw [h3]; exact h1
    exact_mod_cast h4
  have h5 : ‖(toM k).det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h2]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5

theorem gmDens_mul (Z : Fin N → Fin N → ℂ) (hZ : Z ∈ glSet N) :
    gmDens N Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) = 1 := by
  have hn : ‖(Matrix.of Z).det‖ ≠ 0 := norm_ne_zero_iff.mpr hZ
  rw [gmDens, ← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← zpow_natCast,
    ← zpow_add₀ hn]
  push_cast
  simp

theorem triDens_mul (t : TriCo N) (ht : t ∈ triPos N) :
    triDens t * ENNReal.ofReal ((∏ j, t.1 j) ^ (2 * N)) = ENNReal.ofReal (qrWt t) := by
  have hpos : ∀ j, 0 ≤ t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1)) := fun j => zpow_nonneg (ht j).le _
  rw [triDens, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hpos j), ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, qrWt]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := j.2
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ne_of_gt (ht j))]
  congr 1
  omega

theorem d_qrMap (k : UNgrp N) (t : TriCo N) (ht : t ∈ triPos N) :
    ENNReal.ofReal (‖(Matrix.of (qrMap (k, t))).det‖ ^ (2 * N)) =
      ENNReal.ofReal ((∏ j, t.1 j) ^ (2 * N)) := by
  congr 2
  have : Matrix.of (qrMap (k, t)) = toM k * upMat t := by
    simp [qrMap]
  rw [this, Matrix.det_mul, norm_mul, norm_det_toM, one_mul, det_upMat, norm_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (ht j).le]

end ReciprocityTheory.ChartRestriction.DS.QRH
end
end

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.QRH

variable {N : ℕ}

theorem qr_lintegral (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ := by
  haveI hcpt : CompactSpace (UNgrp N) := by
    by_contra hnc
    rw [not_compactSpace_iff] at hnc
    have h1 := MeasureTheory.measure_univ_of_isMulLeftInvariant μ
    rw [measure_univ] at h1
    exact ENNReal.one_ne_top h1
  obtain ⟨c, hct, hkap⟩ := kap_eq (N := N)
  haveI : SigmaFinite (triMeas N) := by
    unfold triMeas triDens
    infer_instance
  haveI : SigmaFinite (kap N) := by
    rw [hkap]
    lift c to NNReal using hct
    show SigmaFinite (c • triMeas N)
    infer_instance
  have hprod := nuQR_eq_prod (N := N) μ
  have hcd : Continuous fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det :=
    Continuous.matrix_det (continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z)
  have hdet : Measurable fun Z : Fin N → Fin N → ℂ => ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) :=
    ((hcd.norm.pow _).measurable).ennreal_ofReal
  have hgm : Measurable (gmDens N) := by
    have he : gmDens N = fun Z => ENNReal.ofReal ((‖(Matrix.of Z).det‖ ^ (2 * N))⁻¹) := by
      funext Z
      unfold gmDens
      rw [_root_.zpow_neg, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [he]
    exact ((hcd.norm.pow _).measurable.inv).ennreal_ofReal
  have htd : Measurable (triDens (N := N)) := by
    unfold triDens
    first
    | fun_prop
    | measurability
  have key : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = c * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ := by
    intro f hf
    have hg : Measurable fun Z => f Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) := hf.mul hdet
    have hgq : Measurable fun p : UNgrp N × TriCo N =>
        f (qrMap p) * ENNReal.ofReal (‖(Matrix.of (qrMap p)).det‖ ^ (2 * N)) := hg.comp measurable_qrMap
    have s1 : ∫⁻ Z, f Z = ∫⁻ Z in glSet N, f Z := by
      rw [← lintegral_add_compl f (measurableSet_glSet (N := N))]
      have hc : (glSet N)ᶜ = {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det = 0} := by
        ext Z
        simp [glSet]
      rw [hc, setLIntegral_measure_zero _ _ volume_det_eq_zero, add_zero]
    have s2 : ∫⁻ Z in glSet N, f Z =
        ∫⁻ Z, f Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) ∂((gmMeas N).restrict (glSet N)) := by
      unfold gmMeas
      rw [restrict_withDensity measurableSet_glSet, lintegral_withDensity_eq_lintegral_mul _ hgm hg]
      apply setLIntegral_congr_fun measurableSet_glSet
      intro Z hZ
      simp only [Pi.mul_apply]
      rw [mul_comm (f Z), ← mul_assoc, gmDens_mul Z hZ, one_mul]
    rw [s1, s2, ← map_qrMap_nuQR, lintegral_map hg measurable_qrMap, ← hprod,
      lintegral_prod _ hgq.aemeasurable, ← lintegral_const_mul' _ _ hct]
    apply lintegral_congr
    intro k
    rw [hkap, lintegral_smul_measure]
    congr 1
    unfold triMeas
    rw [lintegral_withDensity_eq_lintegral_mul _ htd (by
      first
      | exact hgq.comp measurable_prodMk_left
      | exact hgq.comp measurable_prod_mk_left)]
    apply setLIntegral_congr_fun measurableSet_triPos
    intro t ht
    simp only [Pi.mul_apply]
    rw [d_qrMap k t ht, mul_comm, mul_assoc, mul_comm _ (triDens t), triDens_mul t ht]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := key (fun _ => 1) measurable_const
    rw [h0, zero_mul, lintegral_const, one_mul] at h1
    have hv : (volume : Measure (Fin N → Fin N → ℂ)) Set.univ ≠ 0 := by
      rw [MeasureTheory.volume_pi, Measure.pi_univ, Finset.prod_ne_zero_iff]
      intro i _
      rw [MeasureTheory.volume_pi, Measure.pi_univ, Finset.prod_ne_zero_iff]
      intro j _
      exact isOpen_univ.measure_ne_zero volume Set.univ_nonempty
    exact hv h1
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, ?_⟩
  intro f hf
  rw [ENNReal.ofReal_toReal hct]
  exact key f hf

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

section
open Finset MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

theorem gaussA_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => h0 i _), integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))]

theorem gaussA_real_int : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem gaussA_cfun_eq : (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) =
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) ∘ Complex.measurableEquivRealProd := by
  funext z
  simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, ← Real.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem gaussA_cint : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
  rw [gaussA_cfun_eq, Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding]
  exact Integrable.mul_prod gaussA_real_int gaussA_real_int

theorem gaussA_cintegral : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))
  have h2 : ∫ p : ℝ × ℝ, Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2) = Real.pi := by
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2)) (fun x : ℝ => Real.exp (-x ^ 2))]
    have hg : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
      simpa using integral_gaussian 1
    rw [hg, Real.mul_self_sqrt Real.pi_pos.le]
  rw [gaussA_cfun_eq]
  simpa [Function.comp_def] using h.trans h2

theorem gaussA_rad (a : ℕ) :
    ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) = (a.factorial : ℝ) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2 * a + 1 : ℕ) : ℝ)) two_pos (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  have hc : ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) =
      ∫ x in Ioi (0:ℝ), x ^ (((2 * a + 1 : ℕ) : ℝ)) * Real.exp (-x ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
    rw [show x ^ (2:ℝ) = x ^ (2:ℕ) by exact_mod_cast Real.rpow_natCast x 2, mul_comm]
  rw [hc, h]
  have : ((((2 * a + 1 : ℕ) : ℝ)) + 1) / 2 = (a : ℝ) + 1 := by push_cast; ring
  rw [this, Real.Gamma_nat_eq_factorial]
  ring

theorem gaussA_rad_int (a : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-r ^ 2) * |r| ^ (2 * a + 1)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := ((2 * a + 1 : ℕ) : ℝ)) (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
  ring_nf

end ReciprocityTheory.ChartRestriction.DS

end

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussB_hs_eq_re_trace (M : Matrix (Fin N) (Fin N) ℂ) : hs M = (trace (Mᴴ * M)).re := by
  simp only [hs, trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem gaussB_hs_unitary_mul (k : UNgrp N) (M : Matrix (Fin N) (Fin N) ℂ) : hs (toM k * M) = hs M := by
  have hk : inUJ (fun _ : Fin N => true) (toM k) := k.2
  have hJ : Jm (fun _ : Fin N => true) = 1 := by
    unfold Jm; simp
  unfold inUJ at hk
  rw [hJ, Matrix.mul_one] at hk
  rw [gaussB_hs_eq_re_trace, gaussB_hs_eq_re_trace, conjTranspose_mul,
    show Mᴴ * (toM k)ᴴ * (toM k * M) = Mᴴ * ((toM k)ᴴ * toM k) * M by simp only [Matrix.mul_assoc],
    hk, Matrix.mul_one]

theorem gaussB_card_lt : Fintype.card {ab : Fin N × Fin N // ab.1 < ab.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have h1 : ∀ i : Fin N, (∑ j : Fin N, if i < j then 1 else 0) = N - 1 - i := by
    intro i
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  simp_rw [h1]
  have h2 : (∑ i : Fin N, (N - 1 - (i : ℕ))) = ∑ i : Fin N, (i : ℕ) := by
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [h2, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem gaussB_prod_fact :
    (∏ j : Fin N, (((N - 1 - (j : ℕ)).factorial : ℝ) / 2)) = (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) N]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  exact congrArg (fun m : ℕ => ((m.factorial : ℕ) : ℝ)) (by omega)

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussC_mat :
    ∫⁻ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (Real.pi ^ (N ^ 2)) := by
  have hpt : ∀ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (∏ i, (fun (_ : Fin N) (row : Fin N → ℂ) => ∏ j, Real.exp (-‖row j‖ ^ 2)) i (Z i)) := by
    intro Z
    congr 1
    simp only [hs, Matrix.of_apply, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  have hrow : Integrable (fun row : Fin N → ℂ => ∏ j, Real.exp (-‖row j‖ ^ 2)) :=
    Integrable.fintype_prod (fun _ => gaussA_cint)
  have hrowi : ∫ row : Fin N → ℂ, ∏ j, Real.exp (-‖row j‖ ^ 2) = Real.pi ^ N := by
    rw [integral_fintype_prod_volume_eq_prod (fun (_ : Fin N) (z : ℂ) => Real.exp (-‖z‖ ^ 2))]
    simp only [gaussA_cintegral, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hpt]
  rw [show (volume : Measure (Fin N → Fin N → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal _ (fun _ => hrow)
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  simp only [hrowi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (pow_nonneg Real.pi_pos.le _), ← pow_mul, sq]

theorem gaussC_hs_upMat (t : TriCo N) :
    hs (upMat t) = ∑ j, t.1 j ^ 2 + ∑ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, ‖t.2 ab‖ ^ 2 := by
  have hp : ∀ a b : Fin N, ‖upMat t a b‖ ^ 2 = (if a = b then t.1 a ^ 2 else 0) +
      (if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0) := by
    intro a b
    unfold upMat
    by_cases hab : a = b
    · subst hab; simp [Complex.norm_real, sq_abs]
    · by_cases h : a < b
      · simp [hab, h]
      · simp [hab, h]
  unfold hs
  simp_rw [hp, Finset.sum_add_distrib]
  congr 1
  · simp [Finset.sum_ite_eq]
  · rw [← Finset.sum_product' (f := fun a b => if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0),
      Finset.univ_product_univ,
      ← (Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)).sum_comp, Fintype.sum_sum_type]
    have h1 : ∀ a : {p : Fin N × Fin N // p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inl a)) = ‖t.2 a‖ ^ 2 := by
      intro a; obtain ⟨⟨x, y⟩, h⟩ := a; simp [h]
    have h2 : ∀ b : {p : Fin N × Fin N // ¬ p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inr b)) = 0 := by
      intro b; obtain ⟨⟨x, y⟩, h⟩ := b; simp [h]
    simp only [h1, h2, Finset.sum_const_zero, add_zero]

def gaussRadW (N : ℕ) (j : Fin N) (r : ℝ) : ℝ := Real.exp (-r ^ 2) * |r| ^ (2 * (N - 1 - (j : ℕ)) + 1)

theorem gaussD_integrand (t : TriCo N) (ht : t ∈ triPos N) :
    ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (∏ j, gaussRadW N j (t.1 j)) *
        ENNReal.ofReal (∏ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, Real.exp (-‖t.2 ab‖ ^ 2)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul' (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  congr 1
  rw [gaussC_hs_upMat, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    Real.exp_sum, Real.exp_sum]
  have hw : ∀ j : Fin N, t.1 j ^ (2 * (N - (j : ℕ)) - 1) = |t.1 j| ^ (2 * (N - 1 - (j : ℕ)) + 1) := by
    intro j
    rw [abs_of_pos (ht j)]
    congr 1
    have := j.2
    omega
  unfold qrWt gaussRadW
  simp_rw [hw, Finset.prod_mul_distrib]
  ring

theorem gaussD_triPos_eq : triPos N = (Set.univ.pi fun _ : Fin N => Set.Ioi (0:ℝ)) ×ˢ Set.univ := by
  ext t
  simp [triPos]

theorem gaussD_tri :
    ∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
  have hms : MeasurableSet (triPos N) := by
    rw [gaussD_triPos_eq]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioi).prod MeasurableSet.univ
  rw [setLIntegral_congr_fun hms (fun t ht => gaussD_integrand t ht), gaussD_triPos_eq,
    show (volume : Measure (TriCo N)) = (volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) from rfl,
    ← Measure.prod_restrict, Measure.restrict_univ,
    show (volume : Measure (Fin N → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  rw [lintegral_prod_mul (f := fun x : Fin N → ℝ => ENNReal.ofReal (∏ j, gaussRadW N j (x j)))
    (g := fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ENNReal.ofReal (∏ ab, Real.exp (-‖y ab‖ ^ 2)))
    (by unfold gaussRadW; fun_prop)
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ∏ ab, Real.exp (-‖y ab‖ ^ 2)).measurable).aemeasurable]
  rw [gaussA_lint_pi_ofReal (fun j => gaussRadW N j) (fun j => gaussA_rad_int _)
      (fun j r => mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _)),
    show (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal (fun (_ : {ab : Fin N × Fin N // ab.1 < ab.2}) (z : ℂ) => Real.exp (-‖z‖ ^ 2))
      (fun _ => gaussA_cint) (fun _ _ => (Real.exp_pos _).le)]
  simp only [gaussRadW, gaussA_rad, gaussA_cintegral, Finset.prod_const, Finset.card_univ, gaussB_card_lt]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity),
    ← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity),
    gaussB_prod_fact]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussE_pow_odd (n : ℕ) : (∏ i ∈ range n, Real.pi ^ (2 * i + 1)) = Real.pi ^ (n ^ 2) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem gaussE_volU_mul :
    volU N * (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) =
      Real.pi ^ (N ^ 2) := by
  have hX : Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N =
      ∏ i ∈ range N, (Real.pi ^ i * (i.factorial : ℝ) / 2) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.sum_range_id, Finset.prod_const, Finset.card_range]
  rw [hX, volU, ← Finset.prod_mul_distrib, ← gaussE_pow_odd N]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hf : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
  field_simp
  ring

theorem gaussE_qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N := by
  have hcont : Continuous fun Z : Fin N → Fin N → ℂ => hs (Matrix.of Z) := by
    unfold hs
    simp only [Matrix.of_apply]
    fun_prop
  have h := hC (fun Z => ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))))
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hcont.neg).measurable)
  have hin : ∀ k : UNgrp N, (∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (Matrix.of (qrMap (k, t))))) *
      ENNReal.ofReal (qrWt t)) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
    intro k
    simp only [qrMap, Equiv.apply_symm_apply, gaussB_hs_unitary_mul]
    exact gaussD_tri
  simp only [hin, lintegral_const, measure_univ, mul_one, gaussC_mat] at h
  set X := Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    have : 0 < ∏ i ∈ range N, (i.factorial : ℝ) :=
      Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos i)
    positivity
  have hPpos : 0 < Real.pi ^ (N ^ 2) := pow_pos Real.pi_pos _
  have hCpos : 0 < C := by
    by_contra hc
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hc), zero_mul, ENNReal.ofReal_eq_zero] at h
    linarith
  rw [← ENNReal.ofReal_mul hCpos.le, ENNReal.ofReal_eq_ofReal_iff hPpos.le (by positivity)] at h
  have h2 := gaussE_volU_mul (N := N)
  rw [← hXdef] at h2
  exact mul_right_cancel₀ hXpos.ne' (h.symm.trans h2.symm)



theorem qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N :=
  gaussE_qr_const μ C hC

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

theorem mp_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.curry : (ι × κ → ℂ) → ι → κ → ℂ) volume volume := by
  first | exact Bl.CurryModusPonens.goal1 .. | (apply Bl.CurryModusPonens.goal1 <;> assumption) | (intros; apply Bl.CurryModusPonens.goal1 <;> assumption)

theorem mp_perm4 {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SigmaFinite μa] [SigmaFinite μb] [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.2.1, p.1.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μc.prod μa).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    ((measurePreserving_prodAssoc μb μc μd).symm _)
  have h3 := (MeasurePreserving.id μa).prod
    (((Measure.measurePreserving_swap (μ := μb) (ν := μc))).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm _
  have h6 := (Measure.measurePreserving_swap (μ := μa) (ν := μc)).prod (MeasurePreserving.id (μb.prod μd))
  have h := h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))
  convert h using 1
  funext p
  rfl

abbrev Lo (N : ℕ) : Type := {ab : Fin N × Fin N // ab.2 < ab.1}

abbrev Up (N : ℕ) : Type := {ab : Fin N × Fin N // ab.1 < ab.2}

variable {N : ℕ}

local instance volTri : (volume : Measure (TriCo N)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
local instance volUCo : (volume : Measure (UCo N)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

def idx (N : ℕ) : Fin N ⊕ (Lo N ⊕ Up N) ≃ Fin N × Fin N where
  toFun i := match i with
    | Sum.inl a => (a, a)
    | Sum.inr (Sum.inl ab) => ab.1
    | Sum.inr (Sum.inr ab) => ab.1
  invFun ab := if h : ab.1 = ab.2 then Sum.inl ab.1 else if h' : ab.2 < ab.1 then Sum.inr (Sum.inl ⟨ab, h'⟩)
    else Sum.inr (Sum.inr ⟨ab, lt_of_le_of_ne (not_lt.1 h') h⟩)
  left_inv := by
    rintro (a | ⟨ab, h⟩ | ⟨ab, h⟩)
    · simp
    · simp [h.ne', h]
    · simp [h.ne, not_lt.2 h.le]
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only
    split_ifs with h h'
    · simp [h]
    · rfl
    · rfl

def rho (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := fun a b =>
  if a = b then ((p.2.1 a : ℝ) : ℂ) + ((p.1.1 a : ℝ) : ℂ) * Complex.I
  else if h : b < a then p.1.2 ⟨(a, b), h⟩ else if h' : a < b then p.2.2 ⟨(a, b), h'⟩ else 0

def e2 (q : (Fin N → ℝ) × (Fin N → ℝ)) : Fin N → ℂ := fun a => ⟨q.1 a, q.2 a⟩

theorem measurePreserving_second_reorder : MeasurePreserving (e2 (N := N)) volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm _
  have h2 := volume_preserving_pi (fun _ : Fin N => (Complex.volume_preserving_equiv_real_prod).symm _)
  exact h2.comp h1

def rho0 (p : UCo N × TriCo N) : Fin N → Fin N → ℂ :=
  Function.curry (MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
      (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2))))

theorem measurePreserving_rho_reorder : MeasurePreserving (rho0 (N := N)) volume volume := by
  have h1 := mp_perm4 (volume : Measure (Fin N → ℝ)) (volume : Measure (Lo N → ℂ))
    (volume : Measure (Fin N → ℝ)) (volume : Measure (Up N → ℂ))
  have h2 := (measurePreserving_second_reorder (N := N)).prod (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Lo N ⊕ Up N => ℂ))
  have h3 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)
  have h4 := volume_measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
  have h5 := mp_curry (Fin N) (Fin N)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem rho_reorder_eq_rho : rho0 (N := N) = rho := by
  funext p a b
  have key : ∀ i, rho0 p (idx N i).1 (idx N i).2 =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
        (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2)) i :=
    fun i => MeasurableEquiv.piCongrLeft_apply_apply (idx N) (β := fun _ => ℂ) _ i
  rcases lt_trichotomy a b with h | rfl | h
  · have k := key (Sum.inr (Sum.inr ⟨(a, b), h⟩))
    simp only [rho, h.ne, not_lt.2 h.le, h, if_false, dif_neg, dif_pos, not_false_eq_true]
    exact k
  · have k := key (Sum.inl a)
    simp only [rho, if_true]
    refine k.trans ?_
    apply Complex.ext <;> simp <;> rfl
  · have k := key (Sum.inr (Sum.inl ⟨(a, b), h⟩))
    simp only [rho, h.ne', h, if_false, dif_pos]
    exact k

theorem mp_rho : MeasurePreserving (rho (N := N)) volume volume := by
  rw [← rho_reorder_eq_rho]; exact measurePreserving_rho_reorder

def sh (p : UCo N × TriCo N) : UCo N × TriCo N :=
  (p.1, (p.2.1, fun ab => p.2.2 ab - star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)))

theorem mp_sh : MeasurePreserving (sh (N := N)) volume volume := by
  have hc : Continuous (fun q : UCo N × TriCo N =>
      ((0 : Fin N → ℝ), fun ab : Up N => -star (q.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + q.2) := by
    refine (continuous_const.prodMk (continuous_pi fun ab => ?_)).add continuous_snd
    exact ((continuous_apply _).comp (continuous_snd.comp continuous_fst)).star.neg
  have h := (MeasurePreserving.id (volume : Measure (UCo N))).skew_product
    (g := fun x (t : TriCo N) => ((0 : Fin N → ℝ), fun ab : Up N => -star (x.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + t)
    (μc := (volume : Measure (TriCo N))) (μd := (volume : Measure (TriCo N)))
    hc.measurable (Filter.Eventually.of_forall fun x => map_add_left_eq_self (volume : Measure (TriCo N)) _)
  have e : sh (N := N) = fun p => (id p.1,
      ((0 : Fin N → ℝ), fun ab : Up N => -star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + p.2) := by
    funext p
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp [sh]
    · funext ab
      simp [sh, sub_eq_add_neg, add_comm]
  rw [e]; exact h

def lam (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := Matrix.of.symm (skMat p.1 + upMat p.2)

theorem lam_eq : lam (N := N) = rho ∘ sh := by
  funext p a b
  simp only [lam, Function.comp_apply, rho, sh, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]; ring
  · simp; ring
  · simp [h.ne', h, not_lt.2 h.le]

theorem mp_lam : MeasurePreserving (lam (N := N)) volume volume := by
  rw [lam_eq]; exact mp_rho.comp mp_sh

def lamInv (Z : Fin N → Fin N → ℂ) : UCo N × TriCo N :=
  ((fun a => (Z a a).im, fun ab => Z ab.1.1 ab.1.2),
   (fun a => (Z a a).re, fun ab => Z ab.1.1 ab.1.2 + star (Z ab.1.2 ab.1.1)))

theorem lamInv_lam (p : UCo N × TriCo N) : lamInv (lam p) = p := by
  obtain ⟨⟨x1, x2⟩, ⟨t1, t2⟩⟩ := p
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne', h, not_lt.2 h.le]
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne, h.ne', h, not_lt.2 h.le]

theorem lam_lamInv (Z : Fin N → Fin N → ℂ) : lam (lamInv Z) = Z := by
  funext a b
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]
  · apply Complex.ext <;> simp
  · simp [h.ne', h, not_lt.2 h.le]

def lamL : (UCo N × TriCo N) →ₗ[ℝ] (Fin N → Fin N → ℂ) where
  toFun := lam
  map_add' p q := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.fst_add, Prod.snd_add,
      Pi.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { lamL with invFun := lamInv, left_inv := lamInv_lam, right_inv := lam_lamInv }

theorem lamE_apply (p : UCo N × TriCo N) : lamE p = lam p := rfl

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

variable {N : ℕ}

def skML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := skMat p.1
  map_add' p q := by
    ext a b
    simp only [skMat, Prod.fst_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [skMat, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def upML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := upMat p.2
  map_add' p q := by
    ext a b
    simp only [upMat, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [upMat, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem chartWR_strict :
    HasStrictFDerivAt (chartWR (N := N))
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) 0 := by
  let skL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap skML
  let upL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap upML
  let ofL : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hsk0 : skL 0 = 0 := map_zero _
  have hup0 : upL 0 = 0 := map_zero _
  have h1 : HasStrictFDerivAt (fun p : UCo N × TriCo N => NormedSpace.exp (skL p))
      ((1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) 0 := by
    have he := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) ℂ)
    rw [← hsk0] at he
    exact he.comp 0 skL.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : UCo N × TriCo N => 1 + upL p) upL 0 :=
    upL.hasStrictFDerivAt.const_add 1
  have h3 := h1.mul' h2
  have h4 := ofL.hasStrictFDerivAt.comp 0 h3
  have hF : (fun x => ofL (((fun p => NormedSpace.exp (skL p)) * fun p => 1 + upL p) x)) = chartWR := by
    funext p; rfl
  have hD : ofL.comp (NormedSpace.exp (skL 0) • upL + MulOpposite.op (1 + upL 0) •
      (1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) =
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) := by
    refine ContinuousLinearMap.ext fun p => ?_
    rw [hsk0, hup0, NormedSpace.exp_zero]
    simp
    exact (add_comm _ _).trans rfl
  rw [hF] at h4
  exact h4.congr_fderiv hD

end Deriv

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Set Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

open ChartWRAux in
theorem chartWR_vol (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ (B : Set (UCo N)) (E : Set (TriCo N)), MeasurableSet B → MeasurableSet E →
      (∀ x ∈ B, ‖x‖ < δ) → (∀ t ∈ E, ‖t‖ < δ) →
      volume (chartWR '' (B ×ˢ E)) ≤ ENNReal.ofReal (1 + η) * (volume B * volume E) ∧
        ENNReal.ofReal (1 - η) * (volume B * volume E) ≤ volume (chartWR '' (B ×ˢ E)) := by
  have : (volume : Measure (Fin N → Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let L : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ) := (lamE : (UCo N × TriCo N) ≃L[ℝ] _)
  let g : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ) := fun z => chartWR (lamE.symm z)
  have hg : HasStrictFDerivAt g (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) 0 := by
    have hc : HasStrictFDerivAt (chartWR (N := N)) L (lamE.symm 0) := by
      rw [map_zero]; exact chartWR_strict
    have h := hc.comp (0 : Fin N → Fin N → ℂ)
      ((lamE.symm : (Fin N → Fin N → ℂ) ≃L[ℝ] (UCo N × TriCo N)) :
        (Fin N → Fin N → ℂ) →L[ℝ] (UCo N × TriCo N)).hasStrictFDerivAt
    rwa [ContinuousLinearEquiv.coe_comp_coe_symm] at h
  have hdet : ENNReal.ofReal |(ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)).det| = 1 := by
    simp [ContinuousLinearMap.det, ContinuousLinearMap.coe_id]
  have ev1 := addHaar_image_le_mul_of_det_lt (μ := (volume : Measure (Fin N → Fin N → ℂ)))
    (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) (m := (1 + η).toNNReal) (by
      rw [hdet]; exact_mod_cast (show (1 : ℝ) < (1 + η).toNNReal by
        rw [Real.coe_toNNReal _ (by linarith)]; linarith))
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : NNReal), ∀ (s : Set (Fin N → Fin N → ℂ)) (f : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ)),
      ApproximatesLinearOn f (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) s δ →
        ENNReal.ofReal (1 - η) * volume s ≤ volume (f '' s) := by
    rcases lt_or_ge η 1 with h1 | h1
    · have := mul_le_addHaar_image_of_lt_det (μ := (volume : Measure (Fin N → Fin N → ℂ)))
        (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) (m := (1 - η).toNNReal) (by
          rw [hdet]; exact_mod_cast (show ((1 - η).toNNReal : ℝ) < 1 by
            rw [Real.coe_toNNReal _ (by linarith)]; linarith))
      exact this
    · refine Filter.Eventually.of_forall fun δ s f _ => ?_
      rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]; exact bot_le
  obtain ⟨c, ⟨hc1, hc2⟩, hcpos⟩ := ((ev1.and ev2).and self_mem_nhdsWithin).exists
  obtain ⟨s, hs, hap⟩ := hg.approximates_deriv_on_nhds (Or.inr hcpos)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  refine ⟨r / (‖L‖ + 1), by positivity, fun B E hB hE hBδ hEδ => ?_⟩
  have hLr : ‖L‖ * (r / (‖L‖ + 1)) < r := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hball : (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) '' (B ×ˢ E) ⊆ s := by
    rintro _ ⟨p, hp, rfl⟩
    apply hrs
    rw [Metric.mem_ball, dist_zero_right]
    have hp' : ‖p‖ < r / (‖L‖ + 1) := by
      rw [Prod.norm_def]; exact max_lt (hBδ _ hp.1) (hEδ _ hp.2)
    calc ‖lamE p‖ = ‖L p‖ := rfl
      _ ≤ ‖L‖ * ‖p‖ := L.le_opNorm p
      _ ≤ ‖L‖ * (r / (‖L‖ + 1)) := mul_le_mul_of_nonneg_left hp'.le hL0
      _ < r := hLr
  have hap' := hap.mono_set hball
  have himg : chartWR '' (B ×ˢ E) = g '' ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) := by
    rw [Set.image_image]
    refine Set.image_congr fun p _ => ?_
    simp [g]
  have hmp : MeasurePreserving (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) volume volume := by
    have e : (⇑(lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ))) = lam := funext lamE_apply
    rw [e]; exact mp_lam
  have hme : MeasurableEmbedding (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) :=
    lamE.toHomeomorph.measurableEmbedding
  have hvol : volume ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) = volume B * volume E := by
    calc volume ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E))
        = (Measure.map lamE volume) ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) := by
          rw [hmp.map_eq]
      _ = volume (lamE ⁻¹' ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E))) := hme.map_apply _ _
      _ = volume (B ×ˢ E) := by rw [Set.preimage_image_eq _ lamE.injective]
      _ = volume B * volume E := Measure.prod_prod _ _
  rw [himg]
  refine ⟨?_, ?_⟩
  · have := hc1 _ g hap'
    rw [hvol] at this
    exact this
  · have := hc2 _ g hap'
    rw [hvol] at this
    exact this

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_pos' (M : ℕ) : 0 < volU M := by
  unfold volU
  exact Finset.prod_pos fun i _ => by positivity

theorem volU_skMat_conjTranspose (x : UCo N) : (skMat x)ᴴ = -skMat x := by
  ext a b
  simp only [conjTranspose_apply, Matrix.neg_apply, skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, h.ne', h, not_lt.2 h.le]
  · simp
  · simp [h.ne, h.ne', h, not_lt.2 h.le]

theorem volU_exp_inUJ (x : UCo N) :
    inUJ (fun _ : Fin N => true) (NormedSpace.exp (skMat x)) := by
  have hJ : Jm (fun _ : Fin N => true) = 1 := by simp [Jm]
  unfold inUJ
  rw [hJ, Matrix.mul_one, ← Matrix.exp_conjTranspose, volU_skMat_conjTranspose,
    ← Matrix.exp_add_of_commute (-skMat x) (skMat x) (Commute.refl (skMat x)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

theorem volU_continuous_skMat : Continuous (skMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h.ne, h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop
  · simp only [if_true]
    fun_prop
  · simp only [h.ne', h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop

theorem volU_skMat_injective : Function.Injective (skMat (N := N)) := by
  intro x y h
  have h1 : ∀ a b, skMat x a b = skMat y a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · simpa [skMat, Complex.I_ne_zero] using h1 a a
  · obtain ⟨⟨a, b⟩, hab⟩ := ab
    simpa [skMat, hab.ne', hab] using h1 a b

theorem volU_skMat_zero : skMat (0 : UCo N) = 0 := by
  ext a b
  simp [skMat]

theorem volU_exp_injOn : ∃ δ > 0, Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x))
    (Metric.ball 0 δ) := by
  obtain ⟨ℓ, -, -, hℓ⟩ := lcA_exists_log (n := N)
  have hc : Tendsto (skMat (N := N)) (𝓝 0) (𝓝 0) := by
    have := (volU_continuous_skMat (N := N)).tendsto 0
    rwa [volU_skMat_zero] at this
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hc.eventually hℓ)
  refine ⟨δ, hδ, fun x hx y hy hxy => volU_skMat_injective ?_⟩
  have ex := hδ' (Metric.mem_ball.1 hx)
  have ey := hδ' (Metric.mem_ball.1 hy)
  simp only at hxy ex ey
  rw [← ex, ← ey, hxy]

def volUOne (N : ℕ) : TriCo N := (fun _ => 1, 0)

theorem volU_upMat_add (t : TriCo N) : upMat (t + volUOne N) = 1 + upMat t := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [upMat, volUOne, add_comm]
  · simp [upMat, volUOne, h]

theorem volU_qrWt_one : qrWt (volUOne N) = 1 := by
  simp [qrWt, volUOne]

theorem volU_continuous_qrWt : Continuous (qrWt (N := N)) :=
  continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_fst).pow _

theorem volU_ball_sub_triPos {ρ : ℝ} (hρ : ρ ≤ 1) : Metric.ball (volUOne N) ρ ⊆ triPos N := by
  intro t ht j
  rw [Metric.mem_ball, dist_eq_norm] at ht
  have h1 : ‖(t - volUOne N).1 j‖ ≤ ‖t - volUOne N‖ :=
    (norm_le_pi_norm _ j).trans (norm_fst_le _)
  have h2 : (t - volUOne N).1 j = t.1 j - 1 := by simp [volUOne]
  rw [h2, Real.norm_eq_abs] at h1
  linarith [neg_le_abs (t.1 j - 1)]

theorem volU_measurableSet_triPos : MeasurableSet (triPos N) := by
  simp only [triPos, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_real {V η ε a b e i : ℝ} (hV : 0 < V) (he : 0 < e) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) (hkey : (1 - ε) * (1 + η) = 1 + ε)
    (h1 : V * (i * a) ≤ (1 + ε) * (b * e)) (h2 : (1 - ε) * (b * e) ≤ V * (i * a))
    (h3 : (1 - ε) * e ≤ i) (h4 : i ≤ (1 + ε) * e) :
    a ≤ (1 + η) / V * b ∧ (1 - η) / V * b ≤ a := by
  have hε' : 0 < 1 - ε := by linarith
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hV]
    have k1 : V * a * ((1 - ε) * e) ≤ V * a * i :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hV.le ha)
    have k2 : (1 + ε) * (b * e) = (1 - ε) * (1 + η) * (b * e) := by rw [hkey]
    have k3 : (1 - ε) * e * (a * V) ≤ (1 - ε) * e * ((1 + η) * b) := by
      linarith [k1, h1, k2]
    exact le_of_mul_le_mul_left k3 (mul_pos hε' he)
  · rw [div_mul_eq_mul_div, div_le_iff₀ hV]
    have k1 : V * a * i ≤ V * a * ((1 + ε) * e) :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hV.le ha)
    have k2 : (1 + ε) * (1 - η) * (b * e) = (1 - ε) * (1 + η) * (1 - η) * (b * e) := by
      rw [hkey]
    have k3 : 0 ≤ (1 - ε) * η ^ 2 * (b * e) :=
      mul_nonneg (mul_nonneg hε'.le (sq_nonneg η)) (mul_nonneg hb he.le)
    have k4 : (1 + ε) * e * ((1 - η) * b) ≤ (1 + ε) * e * (a * V) := by
      linarith [k1, h2, k2, k3]
    exact le_of_mul_le_mul_left k4 (mul_pos (by linarith) he)

def volUSet (B : Set (UCo N)) : Set (UNgrp N) := {k | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)}

theorem volUSet_measurable {δ : ℝ}
    (hinj : Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x)) (Metric.ball 0 δ))
    {B : Set (UCo N)} (hB : MeasurableSet B) (hBs : B ⊆ Metric.ball 0 δ) :
    MeasurableSet (volUSet B) := by
  set F : UCo N → (Fin N → Fin N → ℂ) := fun x => Matrix.of.symm (NormedSpace.exp (skMat x)) with hF
  set G : UNgrp N → (Fin N → Fin N → ℂ) := fun k => Matrix.of.symm (toM k) with hG
  have hS : volUSet B = G ⁻¹' (F '' B) := by
    ext k
    simp only [volUSet, Set.mem_preimage, Set.mem_image, hF, hG]
    constructor
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, hx, by rw [hk]⟩
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, hx, (Matrix.of.symm.injective hk).symm⟩
  have hGc : Continuous G := continuous_toM _
  have hexp : Continuous (fun X : Matrix (Fin N) (Fin N) ℂ => NormedSpace.exp X) := by
    let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
    exact @NormedSpace.exp_continuous (Matrix (Fin N) (Fin N) ℂ) _ _
      (inferInstanceAs (CompleteSpace (Fin N → Fin N → ℂ)))
  have hFc : Continuous F := hexp.comp volU_continuous_skMat
  rw [hS]
  refine hGc.measurable ?_
  refine MeasurableSet.image_of_continuousOn_injOn hB hFc.continuousOn ?_
  intro x hx y hy hxy
  exact hinj (hBs hx) (hBs hy) (Matrix.of.symm.injective hxy)

theorem volU_image_eq (B : Set (UCo N)) (ρ : ℝ) :
    chartWR '' (B ×ˢ Metric.ball 0 ρ) = qrMap '' (volUSet B ×ˢ Metric.ball (volUOne N) ρ) := by
  ext Z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have hmem : NormedSpace.exp (skMat x) ∈ Set.range (fun g : UNgrp N => toM g) := by
      rw [range_toM]
      exact volU_exp_inUJ x
    obtain ⟨k, hk⟩ := hmem
    have hk' : toM k = NormedSpace.exp (skMat x) := hk
    refine ⟨(k, t + volUOne N), ⟨⟨x, hx, hk'⟩, ?_⟩, ?_⟩
    · show dist (t + volUOne N) (volUOne N) < ρ
      rw [dist_eq_norm, add_sub_cancel_right, ← dist_zero_right]
      exact ht
    · simp only [qrMap, chartWR, volU_upMat_add, hk']
  · rintro ⟨⟨k, t⟩, ⟨⟨x, hx, hk⟩, ht⟩, rfl⟩
    refine ⟨(x, t - volUOne N), ⟨hx, ?_⟩, ?_⟩
    · show dist (t - volUOne N) 0 < ρ
      rw [dist_zero_right, ← dist_eq_norm]
      exact ht
    · have ht' : upMat t = 1 + upMat (t - volUOne N) := by
        rw [← volU_upMat_add, sub_add_cancel]
      have hk' : toM k = NormedSpace.exp (skMat x) := hk
      simp only [qrMap, chartWR, ht']
      rw [hk']

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_density (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ B : Set (UCo N), MeasurableSet B → (∀ x ∈ B, ‖x‖ < δ) →
      μ {k : UNgrp N | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)} ≤ ENNReal.ofReal ((1 + η) / volU N) * volume B ∧
        ENNReal.ofReal ((1 - η) / volU N) * volume B ≤ μ {k : UNgrp N | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)} := by
  obtain ⟨C, -, hC⟩ := qr_lintegral μ
  have hCV : C = volU N := qr_const μ C hC
  subst hCV
  have hV := volU_pos' N
  obtain ⟨ε, hε0, hε1, hkey⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 - ε) * (1 + η) = 1 + ε :=
    ⟨η / (2 + η), by positivity, by rw [div_lt_one (by linarith)]; linarith,
      by field_simp; ring⟩
  obtain ⟨δ1, hδ1, hchart⟩ := chartWR_vol (N := N) ε hε0
  obtain ⟨δ2, hδ2, hinj⟩ := volU_exp_injOn (N := N)
  obtain ⟨ρw, hρw, hw⟩ := Metric.continuousAt_iff.1
    (volU_continuous_qrWt (N := N)).continuousAt ε hε0
  obtain ⟨ρ, hρ0, hρ1, hρ2, hρ3⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ1 ∧ ρ ≤ ρw ∧ ρ ≤ 1 :=
    ⟨min δ1 (min ρw 1), lt_min hδ1 (lt_min hρw one_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun B hB hBs => ?_⟩
  show μ (volUSet B) ≤ _ ∧ _ ≤ μ (volUSet B)
  have hBsub : B ⊆ Metric.ball 0 δ2 := fun x hx =>
    mem_ball_zero_iff.2 ((hBs x hx).trans_le (min_le_right _ _))
  have hA : MeasurableSet (volUSet B) := volUSet_measurable hinj hB hBsub
  have hE'pos : Metric.ball (volUOne N) ρ ⊆ triPos N := volU_ball_sub_triPos hρ3
  set S := qrMap '' (volUSet B ×ˢ Metric.ball (volUOne N) ρ) with hSdef
  have hS : MeasurableSet S := qrMap_measurableSet_image _ (hA.prod Metric.isOpen_ball.measurableSet)
    (fun p hp => ⟨Set.mem_univ _, hE'pos hp.2⟩)
  set I := ∫⁻ t in Metric.ball (volUOne N) ρ, ENNReal.ofReal (qrWt t) with hIdef
  have hmem : ∀ k (t : TriCo N), t ∈ triPos N →
      (qrMap (k, t) ∈ S ↔ k ∈ volUSet B ∧ t ∈ Metric.ball (volUOne N) ρ) := by
    intro k t ht
    constructor
    · rintro ⟨⟨k', t'⟩, ⟨hk', ht'⟩, heq⟩
      have := qrMap_injOn ⟨Set.mem_univ _, hE'pos ht'⟩ ⟨Set.mem_univ _, ht⟩ heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
      exact ⟨hk', ht'⟩
    · rintro ⟨hk, ht'⟩
      exact ⟨(k, t), ⟨hk, ht'⟩, rfl⟩
  have hin : ∀ k, (∫⁻ t in triPos N, S.indicator 1 (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) =
      (volUSet B).indicator (fun _ => I) k := by
    intro k
    by_cases hk : k ∈ volUSet B
    · rw [Set.indicator_of_mem hk, hIdef,
        ← Set.inter_eq_left.2 hE'pos, ← setLIntegral_indicator Metric.isOpen_ball.measurableSet]
      refine setLIntegral_congr_fun volU_measurableSet_triPos (fun t ht => ?_)
      by_cases ht' : t ∈ Metric.ball (volUOne N) ρ
      · rw [Set.indicator_of_mem ((hmem k t ht).2 ⟨hk, ht'⟩), Set.indicator_of_mem ht', Pi.one_apply,
          one_mul]
      · rw [Set.indicator_of_notMem (fun h => ht' ((hmem k t ht).1 h).2), Set.indicator_of_notMem ht',
          zero_mul]
    · rw [Set.indicator_of_notMem hk]
      rw [setLIntegral_congr_fun volU_measurableSet_triPos (g := fun _ => 0) (fun t ht => by
        simp only
        rw [Set.indicator_of_notMem (fun h => hk ((hmem k t ht).1 h).1), zero_mul])]
      simp
  have hSeq : volume S = ENNReal.ofReal (volU N) * (I * μ (volUSet B)) := by
    have h := hC (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS] at h
    rw [h, lintegral_congr hin, lintegral_indicator_const hA]
  have : Measure.IsAddHaarMeasure (volume : Measure (TriCo N)) := by
    show Measure.IsAddHaarMeasure ((volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have : Measure.IsAddHaarMeasure (volume : Measure (UCo N)) := by
    show Measure.IsAddHaarMeasure ((volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.2 < ab.1} → ℂ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hE : volume (Metric.ball (volUOne N) ρ) = volume (Metric.ball (0 : TriCo N) ρ) :=
    Measure.addHaar_ball_center _ _ _
  have hIlo : ENNReal.ofReal (1 - ε) * volume (Metric.ball (0 : TriCo N) ρ) ≤ I := by
    rw [← hE, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun t ht => ENNReal.ofReal_le_ofReal ?_)
    have := hw (lt_of_lt_of_le (Metric.mem_ball.1 ht) hρ2)
    rw [volU_qrWt_one, Real.dist_eq] at this
    linarith [neg_abs_le (qrWt t - 1)]
  have hIhi : I ≤ ENNReal.ofReal (1 + ε) * volume (Metric.ball (0 : TriCo N) ρ) := by
    rw [← hE, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun t ht => ENNReal.ofReal_le_ofReal ?_)
    have := hw (lt_of_lt_of_le (Metric.mem_ball.1 ht) hρ2)
    rw [volU_qrWt_one, Real.dist_eq] at this
    linarith [le_abs_self (qrWt t - 1)]
  obtain ⟨hup, hlo⟩ := hchart B (Metric.ball 0 ρ) hB Metric.isOpen_ball.measurableSet
    (fun x hx => (hBs x hx).trans_le (min_le_left _ _))
    (fun t ht => (mem_ball_zero_iff.1 ht).trans_le hρ1)
  rw [volU_image_eq, ← hSdef, hSeq] at hup hlo

  have hEpos : 0 < volume (Metric.ball (0 : TriCo N) ρ) := Metric.measure_ball_pos _ _ hρ0
  have hEfin : volume (Metric.ball (0 : TriCo N) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hBfin : volume B ≠ ⊤ := ((measure_mono hBsub).trans_lt measure_ball_lt_top).ne
  have hAfin : μ (volUSet B) ≠ ⊤ := measure_ne_top μ _
  have hIfin : I ≠ ⊤ := (hIhi.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEfin.lt_top)).ne
  set a := (μ (volUSet B)).toReal
  set b := (volume B).toReal
  set e := (volume (Metric.ball (0 : TriCo N) ρ)).toReal
  set i := I.toReal
  have ha' : μ (volUSet B) = ENNReal.ofReal a := (ENNReal.ofReal_toReal hAfin).symm
  have hb' : volume B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hBfin).symm
  have he' : volume (Metric.ball (0 : TriCo N) ρ) = ENNReal.ofReal e := (ENNReal.ofReal_toReal hEfin).symm
  have hi' : I = ENNReal.ofReal i := (ENNReal.ofReal_toReal hIfin).symm
  have he0 : 0 < e := ENNReal.toReal_pos hEpos.ne' hEfin
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hi0 : 0 ≤ i := ENNReal.toReal_nonneg
  rw [ha', hb', he', hi'] at hup hlo
  rw [he', hi'] at hIlo hIhi
  rw [← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul hV.le] at hup hlo
  rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul (by linarith)] at hup
  rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul' (by positivity)] at hlo
  rw [← ENNReal.ofReal_mul (by linarith)] at hIhi
  rw [← ENNReal.ofReal_mul' he0.le] at hIlo
  have h1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlo
  have h3 := (ENNReal.ofReal_le_ofReal_iff hi0).1 hIlo
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hIhi
  obtain ⟨r1, r2⟩ := volU_real hV he0 ha0 hb0 hε0 hε1 hη hkey h1 h2 h3 h4
  rw [ha', hb']
  constructor
  · rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal r1
  · rw [← ENNReal.ofReal_mul' hb0]
    exact ENNReal.ofReal_le_ofReal r2

end ReciprocityTheory.ChartRestriction.DS
end
end
