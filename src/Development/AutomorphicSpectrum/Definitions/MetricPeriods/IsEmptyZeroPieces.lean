import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import ReciprocityTheory.AnalyticForms.LeviForms.ProjectiveLineLogLogRegularized
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.LineModel

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory Matrix
open scoped ComplexOrder

def sysLog : AnSys 1 Unit where
  X := OnePoint ℂ
  A := p1
  Θ := fsPot
  L := fsPot
  s := projectiveLinePairSection
  nb := 1
  m := ![1]
  W := ![{OnePoint.infty}]
  potΘ := projLine_isSmoothPotential
  posΘ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.projLine_fubiniStudy_isPosPot
  potL := projLine_isSmoothPotential
  sec := projLine_isHolomorphicSection
  snc := projLine_isSimpleNormalCrossing
  norm_le := logNormSec_nonpos
  th _ := fsPot
  ph _ := llw
  phT _ := llT
  C₅ := 1
  C := 2
  t₀ := T0
  sing _ := singWeight
  reg _ := projectiveLine_isRegFamily
  c2 _ := projectiveLine_isRegFamilyC2



def flagTh (p : Unit × Fin 2) : LocPot (OnePoint ℂ) := if p.2 = 0 then fsPot else LocPot.ofFun fun _ => 0

theorem psh_fs_zero : IsPsh p1 (fsPot + LocPot.ofFun fun _ => 0) := by
  intro x j y hy w
  have := projLine_isPlurisubharmonic x j y ⟨hy.1, hy.2.1⟩ w
  show 0 ≤ levi (fun z => fsPot.φ x ((p1.chart j).symm z) + 0) y w
  simp only [add_zero]
  exact this

theorem sing_flag (p : Unit × Fin 2) : IsSingWeight p1 fsPot projectiveLinePairSection (flagTh p) (fun _ => 0) 0 := by
  unfold flagTh
  split_ifs
  · exact ⟨projLine_isSmoothPotential, fun _ => contDiffOn_const, fun x j y hy w => psh_fs_zero x j y ⟨hy.1, hy.2.1⟩ w,
      fun _ _ => by simp⟩
  · refine ⟨isPotential_ofFun _ _ fun _ => contDiffOn_const, fun _ => contDiffOn_const, fun x j y _ w => ?_,
      fun _ _ => by simp⟩
    show 0 ≤ levi (fun _ => (0 : ℝ) + 0) y w
    simp [levi]

theorem reg_flag (p : Unit × Fin 2) :
    IsRegFamily p1 fsPot fsPot projectiveLinePairSection (flagTh p) (fun _ => 0) (fun _ _ => 0) 1 (Real.exp (-Real.exp 1)) := by
  have h := (isRegFamilyInhabit p1 fsPot fsPot projectiveLinePairSection projLine_isSmoothPotential
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.projLine_fubiniStudy_isPosPot logNormSec_nonpos).1
  unfold flagTh
  split_ifs
  · exact h
  · refine ⟨h.1, h.2.1, fun t ht ht0 => ?_⟩
    obtain ⟨a, b, c, d, -, f⟩ := h.2.2 t ht ht0
    refine ⟨a, b, c, d, ?_, f⟩
    have hε : 0 ≤ epsT 1 t := by
      have h1 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge ht ht0
      have h2 : 0 ≤ Real.log (Real.log (1 / t)) := Real.log_nonneg (by linarith [one_le_exp_one])
      unfold epsT
      rw [one_mul]
      exact div_nonneg h2 (by linarith [Real.exp_pos 1])
    intro x j y hy w
    have hyD : y ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x := ⟨hy.1, hy.2.2⟩
    have hc : ContDiffAt ℝ 2 (fsPot.φ x ∘ (p1.chart j).symm) y :=
      ((projLine_isSmoothPotential.1 x j).contDiffAt (((p1.chart j).isOpen_inter_preimage_symm
        (fsPot.isOpen_U x)).mem_nhds hyD)).of_le two_le_inf
    show 0 ≤ levi (fun z => (0 : ℝ) + 0 + epsT 1 t * fsPot.φ x ((p1.chart j).symm z)) y w
    rw [levi_add_smul (f := fun _ => (0 : ℝ) + 0) (g := fun z => fsPot.φ x ((p1.chart j).symm z)) (epsT 1 t)
      contDiffAt_const hc w]
    have h0 : levi (fun _ : Fin 1 → ℂ => (0 : ℝ) + 0) y w = 0 := by simp [levi]
    rw [h0, zero_add]
    exact mul_nonneg hε (projLine_isPlurisubharmonic x j y hyD w)

def sysFlag : AnSys 1 (Unit × Fin 2) :=
  { sysLog with
    th := flagTh, ph := fun _ _ => 0, phT := fun _ _ _ => 0, C₅ := 0, C := 1, t₀ := Real.exp (-Real.exp 1)
    sing := sing_flag, reg := reg_flag
    c2 := fun _ => (isRegFamilyInhabit p1 fsPot fsPot projectiveLinePairSection projLine_isSmoothPotential
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.projLine_fubiniStudy_isPosPot logNormSec_nonpos).2 }

def frame (_ : Unit) (y : OnePoint ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; crd0 y, 1]

theorem det_head_zero (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (gramHead hd 0 g).det = 1 := by
  haveI : IsEmpty {a : Fin 2 // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
  exact Matrix.det_isEmpty

instance uniqueHead : Unique {a : Fin 2 // (a : ℕ) < 1} where
  default := ⟨0, by decide⟩
  uniq a := Subtype.ext (Fin.ext (by have := a.2; simp; omega))

theorem det_head_one (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (gramHead hd 1 g).det = gramOf hd g 0 0 := by
  rw [Matrix.det_unique]; rfl

theorem det_head_two (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (gramHead hd 2 g).det = (gramOf hd g).det :=
  Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin 2 => (a : ℕ) < 2) fun a => a.2) _

theorem gram_frame_zero (hd : Fin 2 → ℝ) (y : OnePoint ℂ) :
    gramOf hd (frame () y) 0 0 = ((hd 0 + hd 1 * ‖crd0 y‖ ^ 2 : ℝ) : ℂ) := by
  simp [gramOf, frame, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ← Complex.conj_mul']
  ring

theorem det_frame (y : OnePoint ℂ) : (frame () y).det = 1 := by simp [frame, Matrix.det_fin_two]

theorem det_gram_frame (hd : Fin 2 → ℝ) (y : OnePoint ℂ) : (gramOf hd (frame () y)).det = hd 0 * hd 1 := by
  simp [gramOf, det_frame]

theorem holo_frame {V : Set (OnePoint ℂ)} (hV : V ⊆ Set.range ((↑) : ℂ → OnePoint ℂ)) (τ : Unit) (a b : Fin 2) :
    p1.HoloOn V fun y => frame τ y a b := by
  fin_cases a <;> fin_cases b
  · exact holoOn_const _ 1
  · exact holoOn_const _ 0
  · exact holoOn_mono holomorphicOn_finiteCoord hV
  · exact holoOn_const _ 1


theorem flagTh_zero : flagTh ((), 0) = fsPot := if_pos rfl
theorem flagTh_one : flagTh ((), 1) = LocPot.ofFun fun _ => 0 := if_neg (by decide)

theorem chart_flag (z : ℂ) :
    IsPeriodChart p1 2 sysFlag.potH (z : OnePoint ℂ) (Set.range ((↑) : ℂ → OnePoint ℂ)) frame := by
  refine ⟨OnePoint.isOpen_range_coe, ⟨z, rfl⟩, holo_frame subset_rfl, fun τ y _ => ⟨?_, ?_⟩, ?_⟩
  · rw [det_frame]; exact isUnit_one
  · have := (inFlagDomain_one 2).2
    convert this using 1
    haveI : IsEmpty {a : Fin 2 // (a : ℕ) < 2 - 2} := ⟨fun a => by have := a.2; omega⟩
    ext i; exact isEmptyElim i
  · rintro ⟨⟨⟩, i⟩
    refine ⟨fun _ => 0, holoOn_const _ 0, fun y _ => ?_⟩
    fin_cases i
    · show (flagTh ((), 0)).φ z y + 0 = gramLog (sigForm 2 2) 1 (frame () y) - gramLog (sigForm 2 2) 0 (frame () y) + 0
      rw [flagTh_zero, fsPot_φ_coe, gramLog, gramLog, det_head_zero, det_head_one, gram_frame_zero, Complex.norm_real]
      have : (0 : ℝ) ≤ 1 + ‖crd0 y‖ ^ 2 := by positivity
      simp [sigForm]
    · show (flagTh ((), 1)).φ z y + 0 = gramLog (sigForm 2 2) 2 (frame () y) - gramLog (sigForm 2 2) 0 (frame () y) + 0
      rw [flagTh_one, gramLog, gramLog, det_head_zero, det_head_two, det_gram_frame]
      simp [sigForm, LocPot.ofFun]



def disc : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' Metric.ball 0 1

def discPot (p : Unit × Fin 2) : LocPot (OnePoint ℂ) :=
  LocPot.ofFun fun y => if p.2 = 0 then -(1 / 2) * Real.log (1 - ‖crd0 y‖ ^ 2) else 0




theorem affine_chart_param_cover_projective_line : IsParamCover p1 (fun _ => Set.univ) (fun n => if n = 0 then Set.univ else ∅)
    (fun _ => projectiveLineChartAtZero.symm) := by
  refine ⟨fun _ => ⟨isOpen_univ, projectiveLineChartAtZero.continuousOn_symm, projectiveLineChartAtZero.symm.injOn, fun j => p1.holo (0 : Fin 2) j⟩,
    fun n => ⟨by by_cases hn : n = 0 <;> simp [hn], Set.subset_univ _⟩, fun n n' h => ?_, fun j => ?_⟩
  · by_cases hn : n = 0
    · have hn' : n' ≠ 0 := fun e => h (hn.trans e.symm)
      simp [hn']
    · simp [hn]
  · have hsub : (⋃ n : ℕ, projectiveLineChartAtZero.symm '' (if n = 0 then Set.univ else ∅ : Set (Fin 1 → ℂ)))ᶜ ⊆
        (Set.range ((↑) : ℂ → OnePoint ℂ))ᶜ := by
      refine Set.compl_subset_compl.2 ?_
      rintro _ ⟨z, rfl⟩
      exact Set.mem_iUnion.2 ⟨0, fun _ => z, by simp, rfl⟩
    refine measure_mono_null (t := {0}) ?_ (measure_singleton _)
    rintro w ⟨-, hw⟩
    have hw' := hsub hw
    fin_cases j
    · exact absurd ⟨w 0, rfl⟩ hw'
    · have : w 0 = 0 := by
        by_contra hc
        exact hw' (projLineChart1_symm_mem_range.2 hc)
      funext i
      fin_cases i
      exact this


end GlobalTheory.CompanionTheory.Ar.PB.LineModel
end
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Model

open Matrix
open scoped ComplexOrder



instance uniq1 : Unique {a : Fin 2 // (a : ℕ) < 1} where
  default := ⟨0, by simp⟩
  uniq := by rintro ⟨a, ha⟩; apply Subtype.ext; apply Fin.ext; simp only [Fin.val_zero]; omega

def eqv2 : {a : Fin 2 // (a : ℕ) < 2} ≃ Fin 2 := Equiv.subtypeUnivEquiv (fun a => a.2)

theorem det_head_one (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (gramHead hd 1 g).det = gramOf hd g 0 0 := by
  rw [det_unique]; rfl

theorem det_head_two (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (gramHead hd 2 g).det = (gramOf hd g).det := by
  rw [← det_submatrix_equiv_self eqv2 (gramOf hd g)]; rfl

theorem det_head_zero {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramHead hd 0 g).det = 1 := by
  haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
  exact det_isEmpty

theorem gram_signature_two_one_entry_zero_zero (z : ℂ) : gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0 = -((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
  simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
  ring


theorem inFlagDomain_disc (z : ℂ) : InFlagDomain 2 1 !![1, 0; z, 1] ↔ ‖z‖ < 1 := by
  have h : -gramHead (sigForm 2 1) (2 - 1) !![1, 0; z, 1]
      = diagonal (fun _ : {a : Fin 2 // (a : ℕ) < 1} => ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)) := by
    ext a b
    have ha : a = default := Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _
    have hb : b = default := Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _
    subst ha; rw [hb]
    rw [diagonal_apply_eq, Matrix.neg_apply]
    change -(gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0) = _
    rw [gram_signature_two_one_entry_zero_zero, neg_neg]
  unfold InFlagDomain
  rw [h, posDef_diagonal_iff]
  have hu : IsUnit (!![1, 0; z, 1] : Matrix (Fin 2) (Fin 2) ℂ).det := by simp [det_fin_two_of]
  simp only [hu, true_and, Complex.zero_lt_real, forall_const]
  constructor
  · intro h; nlinarith [norm_nonneg z]
  · intro h; nlinarith [norm_nonneg z]



theorem stepPot_pos_zero (z : ℂ) :
    stepPot 2 2 0 !![1, 0; z, 1] = (1 / 2) * Real.log (1 + ‖z‖ ^ 2) := by
  have : stepPot 2 2 0 !![1, 0; z, 1]
      = gramLog (sigForm 2 2) 1 !![1, 0; z, 1] - gramLog (sigForm 2 2) 0 !![1, 0; z, 1] := by
    simp [stepPot]
  have h : gramOf (sigForm 2 2) !![1, 0; z, 1] 0 0 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
  rw [this, gramLog, gramLog, det_head_one, det_head_zero, h, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  simp







end GlobalTheory.CompanionTheory.Ar.PB.Model
end
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PieceModel

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory.CompanionTheory.Ar.PB.LineModel

instance uniqueLow : Unique (LowEnt Unit 2) where
  default := ((), ⟨(1, 0), by decide⟩)
  uniq := by decide

def q1 : LowEnt Unit 2 ≃ Fin 1 := Equiv.ofUnique _ _

theorem lowMat_two (q : LowEnt Unit 2 ≃ Fin 1) (z : Fin 1 → ℂ) (τ : Unit) : lowMat q z τ = !![1, 0; z 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lowMat]
  congr 1; exact Subsingleton.elim _ _

theorem cellDom_two_two (q : LowEnt Unit 2 ≃ Fin 1) : cellDom 2 q = Set.univ := by
  refine Set.eq_univ_of_forall fun z τ => ?_
  rw [lowMat_two]
  exact (chart_flag (z 0)).2.2.2.1 () (z 0 : ℂ) ⟨_, rfl⟩





def lineUnif : PieceUnif sysFlag 2 1 where
  q _ := q1
  π _ := projectiveLineChartAtZero.symm
  FF _ := Set.univ
  mem_open _ z _ h := OnePoint.coe_ne_infty (z 0) ((mem_boundary_projectiveLine _).1 h)
  param _ z _ := ⟨Set.univ, trivial, by rw [cellDom_two_two], affine_chart_param_cover_projective_line.1 0⟩
  pot _ z _ p := by
    refine ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => ?_⟩
    rw [lowMat_two]
    obtain ⟨⟨⟩, i⟩ := p
    fin_cases i
    · show (flagTh ((), 0)).φ (z 0 : ℂ) (z' 0 : ℂ) + 0 = stepPot 2 2 0 !![1, 0; z' 0, 1] + 0
      rw [flagTh_zero, fsPot_φ_coe, Model.stepPot_pos_zero]
      simp
    · show (flagTh ((), 1)).φ (z 0 : ℂ) (z' 0 : ℂ) + 0 =
        gramLog (sigForm 2 2) 2 (frame () (z' 0 : ℂ)) - gramLog (sigForm 2 2) 0 (frame () (z' 0 : ℂ)) + 0
      rw [flagTh_one, gramLog, gramLog, det_head_zero, det_head_two, det_gram_frame]
      simp [sigForm, LocPot.ofFun]
  meas _ := MeasurableSet.univ
  sub _ := by rw [cellDom_two_two]
  inj _ := projectiveLineChartAtZero.symm.injOn
  disj k k' h := absurd (Subsingleton.elim k k') h
  cover := by
    intro j
    refine measure_mono_null ?_ (affine_chart_param_cover_projective_line.2.2.2 j)
    refine Set.inter_subset_inter_right _ (Set.preimage_mono (Set.compl_subset_compl.2 ?_))
    refine Set.iUnion_subset fun n => ?_
    exact (Set.image_mono (Set.subset_univ _)).trans (Set.subset_iUnion (fun _ : Fin 1 => projectiveLineChartAtZero.symm '' Set.univ) 0)






end GlobalTheory.CompanionTheory.Ar.Cmp.PieceModel
end
end
