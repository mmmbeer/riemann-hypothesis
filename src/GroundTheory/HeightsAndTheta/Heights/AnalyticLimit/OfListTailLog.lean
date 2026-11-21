import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Convergence
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPolyMaxLowerBound
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PKaehlerBound
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StBoundingKaehler
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PDivisorNull
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGluedLocal
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.LinearWeights
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StatementsPullback
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailDimZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UniformIntegrability
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.JointExample
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListProductMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMono
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSection
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLogSmooth
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StProductBounds
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListProductMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStep
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplace
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassError
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PWeightCocycle
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPolynomialInWeights
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Imports
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPropertyF

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier polyMax molli mollify_thm polyMax_le' polyMax_mono' le_polyMax
  limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.Regular

noncomputable section

def regularisedAt {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    (R : RegChartData A) (ρ : Mollifier D) (η : Fin R.N → X → ℝ) (κ E t : ℝ) : X → ℝ :=
  R.regularised ρ (κ * Real.log (Real.log t⁻¹)) t
    (E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹ + t)) η

def RegularisedMonotone.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (η : Fin R.N → X → ℝ) (Cη κ E : ℝ),
    R.IsCutoffFamily η Cη → 0 ≤ κ → 0 ≤ E →
    ∃ C ℓ₀ : ℝ, ∀ t t₀ : ℝ, 0 < t → t ≤ t₀ → ℓ₀ ≤ Real.log t₀⁻¹ → ∀ x : X,
      regularisedAt R ρ η κ E t x ≤
        regularisedAt R ρ η κ E t₀ x + C * (Real.log (Real.log t₀⁻¹) / Real.log t₀⁻¹)


theorem le_logLog_div {t ℓ : ℝ} (ht : 0 < t) (hℓdef : ℓ = Real.log t⁻¹) (hℓe : Real.exp 1 ≤ ℓ) :
    t ≤ Real.log ℓ / ℓ := by
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓe
  have hlog1 : 1 ≤ Real.log ℓ := by rw [Real.le_log_iff_exp_le hℓ0]; exact hℓe
  have hlogt : Real.log t = -ℓ := by rw [hℓdef, Real.log_inv, neg_neg]
  have htexp : t = Real.exp (-ℓ) := by rw [← hlogt, Real.exp_log ht]
  rw [htexp, Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos ℓ)]
  have h5 : ℓ + 1 ≤ Real.exp ℓ := Real.add_one_le_exp ℓ
  have h6 : 1 ≤ Real.exp ℓ * (Real.log ℓ / ℓ) := by
    rw [mul_div_assoc', le_div_iff₀ hℓ0, one_mul]
    have := le_mul_of_one_le_right (Real.exp_pos ℓ).le hlog1
    linarith
  rw [mul_comm]; exact h6

theorem RegularisedMonotone.proof : RegularisedMonotone.Statement := by
  intro X _ _ _ D A R ρ η Cη κ E hη hκ hE
  obtain ⟨δ, B₀, hδ, hV⟩ := TruncPsh.proof X D A R
  choose V hVo hVt hVball hVpsh using hV
  obtain ⟨C₂, t₂, ht₂, hlow⟩ := PolyMaxLowerBound.proof X D A R
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨B', hB'⟩ : ∃ c : ℝ, c = max B₀ 0 := ⟨_, rfl⟩
  obtain ⟨C₂', hC₂'⟩ : ∃ c : ℝ, c = max C₂ 0 := ⟨_, rfl⟩
  have hB'0 : 0 ≤ B' := hB' ▸ le_max_right _ _
  have hB₀B' : B₀ ≤ B' := hB' ▸ le_max_left _ _
  have hC₂'0 : 0 ≤ C₂' := hC₂' ▸ le_max_right _ _
  have hC₂C₂' : C₂ ≤ C₂' := hC₂' ▸ le_max_left _ _
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / 2)| := ⟨_, rfl⟩
  have hL16 : 0 ≤ Real.log (4 * 2 ^ 2 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨E₁, hE₁⟩ : ∃ c : ℝ, c = 2 * Real.log (4 * 2 ^ 2 : ℝ) * (B' + C₂') := ⟨_, rfl⟩
  have hE₁0 : 0 ≤ E₁ := by rw [hE₁]; positivity
  refine ⟨10 * E + c₀ * E₁,
    max (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2))) + 1,
    fun t t₀ ht htt₀ hℓ x => ?_⟩
  have ht₀ : 0 < t₀ := ht.trans_le htt₀
  obtain ⟨ℓ, hℓdef⟩ : ∃ s : ℝ, s = Real.log t₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨ℓt, hℓtdef⟩ : ∃ s : ℝ, s = Real.log t⁻¹ := ⟨_, rfl⟩
  rw [← hℓdef] at hℓ
  have h1 := le_max_left (Real.exp 1) (2 * a)
  have h2 := le_max_right (Real.exp 1) (2 * a)
  have h3 := le_max_left (-Real.log t₂) (-Real.log (δ / 2))
  have h4 := le_max_right (-Real.log t₂) (-Real.log (δ / 2))
  have h5 := le_max_left (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2)))
  have h6 := le_max_right (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2)))
  have hℓe : Real.exp 1 ≤ ℓ := by linarith
  have hℓa : 2 * a ≤ ℓ := by linarith
  have hlogt₀ : Real.log t₀ = -ℓ := by rw [hℓdef, Real.log_inv, neg_neg]
  have htt₂ : t₀ < t₂ := (Real.log_lt_log_iff ht₀ ht₂).1 (by linarith)
  have htδ : t₀ < δ / 2 := (Real.log_lt_log_iff ht₀ (by linarith)).1 (by linarith)
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓe
  have hlog1 : 1 ≤ Real.log ℓ := by rw [Real.le_log_iff_exp_le hℓ0]; exact hℓe
  obtain ⟨q, hqdef⟩ : ∃ s : ℝ, s = Real.log ℓ / ℓ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqdef]; exact div_nonneg (by linarith) hℓ0.le
  have htq : t₀ ≤ q := hqdef ▸ le_logLog_div ht₀ hℓdef hℓe
  have hqℓ : q * ℓ = Real.log ℓ := by rw [hqdef]; field_simp

  have hℓℓt : ℓ ≤ ℓt := by
    rw [hℓdef, hℓtdef]; exact Real.log_le_log (inv_pos.2 ht₀) (inv_anti₀ ht htt₀)
  have hqt : Real.log ℓt / ℓt ≤ q := by
    have h := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe) (Set.mem_Ici.2 (hℓe.trans hℓℓt))
      hℓℓt
    simp only at h
    rw [hqdef]; exact h
  have hlogℓt : Real.log ℓ ≤ Real.log ℓt := Real.log_le_log hℓ0 hℓℓt
  have hKK : κ * Real.log ℓ ≤ κ * Real.log ℓt := mul_le_mul_of_nonneg_left hlogℓt hκ
  have hK0 : 0 ≤ κ * Real.log ℓ := mul_nonneg hκ (by linarith)
  have hqt0 : 0 ≤ Real.log ℓt / ℓt := div_nonneg (by linarith) (by linarith)
  have hεt0 : 0 ≤ E * (Real.log ℓt / ℓt + t) := mul_nonneg hE (by linarith)
  have hε0 : 0 ≤ E * (q + t₀) := mul_nonneg hE (by linarith)
  have hεle : E * (Real.log ℓt / ℓt + t) ≤ E * (q + t₀) :=
    mul_le_mul_of_nonneg_left (by linarith) hE
  have hε2 : E * (q + t₀) ≤ 2 * E * q := by
    have := mul_le_mul_of_nonneg_left htq hE
    linarith

  have key : ∀ j, x ∈ R.mid j → R.phReg ρ (κ * Real.log ℓt) t j x ≤
      R.phReg ρ (κ * Real.log ℓ) t₀ j x + c₀ * E₁ * q := by
    intro j hx
    obtain ⟨hp₀, hbd₀⟩ := hVpsh j (κ * Real.log ℓ)
    have hball : ∀ s, s ≤ δ → closedBall (R.chart j x) s ⊆ V j := fun s hs =>
      (closedBall_subset_closedBall hs).trans (hVball j x hx)
    have h2t : 2 * t₀ ≤ δ := by linarith

    have hpt := (hVpsh j (κ * Real.log ℓt)).1
    have hi : molli ρ t (R.trunc (κ * Real.log ℓt) j) (R.chart j x) ≤
        polyMax (R.trunc (κ * Real.log ℓt) j) (R.chart j x) t :=
      (((mollify_thm D ρ (V j) _ (hVo j) hpt).1 t ht).2.2.2 (R.chart j x)
        (hball t (by linarith))).2
    have hii : polyMax (R.trunc (κ * Real.log ℓt) j) (R.chart j x) t ≤
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) := by
      refine polyMax_le' ht.le fun y hy => ?_
      have hyV : y ∈ V j := hball t (by linarith) hy
      exact TruncTransfer.limsupExt_max_le (R.chart j).open_target (R.S j) (R.u j) _ _ t₀
        (hVt j hyV) ht₀ fun y' hy' _ hy'S => by
          have hy'b : y' ∈ closedBall (R.chart j x) (2 * t₀) := by
            rw [mem_closedBall]; rw [mem_ball] at hy'; rw [mem_closedBall] at hy
            linarith [dist_triangle y' y (R.chart j x)]
          have e : R.trunc (κ * Real.log ℓ) j y' = max (R.u j y') (-(κ * Real.log ℓ)) := by
            simp only [RegChartData.trunc, limsupExt, if_neg hy'S]
          calc max (R.u j y') (-(κ * Real.log ℓt)) ≤ max (R.u j y') (-(κ * Real.log ℓ)) :=
                max_le_max le_rfl (neg_le_neg hKK)
            _ = R.trunc (κ * Real.log ℓ) j y' := e.symm
            _ ≤ _ := le_polyMax hp₀.1 (hball _ h2t) hy'b

    have hiv := MollifiedLowerBound.full D ρ b (V j) (R.trunc (κ * Real.log ℓ) j) (R.chart j x) t₀
      (hVo j) hp₀ ht₀ (hball _ h2t) hb
    rw [← hc₀] at hiv
    have hv := PolyMaxOscillation.full D (V j) (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ t₀ 2
      (hVo j) hp₀ (hball δ le_rfl) ht₀ (by norm_num) (by linarith)
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) s ≤
          polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hp₀.1 hs hss' (hball _ hs')
    have e1 := mono (t₀ / (4 * 2)) (t₀ / 4) (by linarith) (by linarith) (by linarith)
    have e2 := mono t₀ (2 * t₀) ht₀.le (by linarith) h2t
    have hlowj := hlow t₀ ht₀ htt₂ (κ * Real.log ℓ) j x hx
    rw [← hℓdef] at hlowj
    have hMδ : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ ≤ B' :=
      polyMax_le' hδ.le fun y hy => (hbd₀ y (hVball j x hx hy)).trans
        (max_le hB₀B' (by linarith))
    have hN : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) ≤ (B' + C₂') * Real.log ℓ := by
      have h1' : C₂ * Real.log ℓ ≤ C₂' * Real.log ℓ :=
        mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
      have h2' : B' ≤ B' * Real.log ℓ := le_mul_of_one_le_right hB'0 hlog1
      linarith
    have hden : ℓ / 2 ≤ Real.log (δ / (2 * t₀)) := by
      rw [show δ / (2 * t₀) = (δ / 2) * t₀⁻¹ by field_simp,
        Real.log_mul (by linarith : (0 : ℝ) < δ / 2).ne' (inv_pos.2 ht₀).ne']
      have := neg_abs_le (Real.log (δ / 2))
      rw [← ha] at this
      linarith
    have hden0 : 0 < Real.log (δ / (2 * t₀)) := by linarith
    have hO : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (t₀ / (4 * 2)) ≤ E₁ * q := by
      refine hv.trans ?_
      rw [div_le_iff₀ hden0]
      calc Real.log (4 * 2 ^ 2) * (polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ -
              polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀))
          ≤ Real.log (4 * 2 ^ 2) * ((B' + C₂') * Real.log ℓ) :=
            mul_le_mul_of_nonneg_left hN hL16
        _ = E₁ * q * (ℓ / 2) := by rw [hE₁, ← hqℓ]; ring
        _ ≤ E₁ * q * Real.log (δ / (2 * t₀)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg hE₁0 hq0)
    have hc : c₀ * (polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (t₀ / 4)) ≤ c₀ * (E₁ * q) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    simp only [RegChartData.phReg, RegChartData.smoothed]
    linarith

  have hg := LogLogRegularisation.glue_le R.toPotentialCharts
    (fun j x => R.phReg ρ (κ * Real.log ℓt) t j x + 4 * (E * (Real.log ℓt / ℓt + t)) * η j x)
    hεt0 (c := regularisedAt R ρ η κ E t₀ x + 4 * (E * (q + t₀)) + c₀ * E₁ * q) (x := x)
    fun j hx => by
      have hb' := hη.bounds j x hx
      have hlo := LogLogRegularisation.le_glue R.toPotentialCharts
        (fun j x => R.phReg ρ (κ * Real.log ℓ) t₀ j x + 4 * (E * (q + t₀)) * η j x) hε0 hx
      have e : R.toPotentialCharts.glue
          (fun j x => R.phReg ρ (κ * Real.log ℓ) t₀ j x + 4 * (E * (q + t₀)) * η j x)
          (E * (q + t₀)) x = regularisedAt R ρ η κ E t₀ x := by
        simp only [regularisedAt, ← hℓdef, ← hqdef]; rfl
      rw [e] at hlo
      have hk := key j hx
      have m1 : 4 * (E * (Real.log ℓt / ℓt + t)) * η j x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hb'.2
      have m2 : 0 ≤ 4 * (E * (q + t₀)) * (η j x + 1) := mul_nonneg (by linarith) (by linarith)
      linarith
  have e : R.toPotentialCharts.glue
      (fun j x => R.phReg ρ (κ * Real.log ℓt) t j x + 4 * (E * (Real.log ℓt / ℓt + t)) * η j x)
      (E * (Real.log ℓt / ℓt + t)) x = regularisedAt R ρ η κ E t x := by
    simp only [regularisedAt, ← hℓtdef]; rfl
  rw [e] at hg
  rw [← hℓdef, ← hqdef]
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi levi_zero levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_rsmul_chart (A : FinHolAtlas D X) (P : LocPot X) (hP : IsPotential A P) (a : ℝ)
    (x : X) (k : Fin A.n) (y : Fin D → ℂ)
    (hy : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) (w : Fin D → ℂ) :
    levi ((P.rsmul a).φ x ∘ (A.chart k).symm) y w = a * levi (P.φ x ∘ (A.chart k).symm) y w := by
  have hs : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y :=
    ((hP.1 x k).of_le two_le_smooth_kb).contDiffAt
      (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
        (P.isOpen_U x)).mem_nhds hy)
  have h := levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hs w
  have he : (P.rsmul a).φ x ∘ (A.chart k).symm =
      fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z := by
    funext z
    simp [LocPot.rsmul]
  rw [he, h, levi_const, zero_add]

theorem BoundingKaehler.proof : BoundingKaehler.Statement := by
  intro X _ _ _ D A om m th hth
  have hX : IsCompact (Set.univ : Set X) := isCompact_univ
  choose M hM0 hM using fun i => levi_abs_le_global A hX (th i) om.pot (hth i) om.isPot om.pos
  set K : ℝ := 1 + ∑ i, M i with hKdef
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
  have hK : 0 < K := by linarith
  have hMK : ∀ i, M i ≤ K := fun i => by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hM0 j) (Finset.mem_univ i)
    linarith
  have hnn : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x, ∀ w : Fin D → ℂ,
      0 ≤ levi (om.pot.φ x ∘ (A.chart k).symm) y w := by
    intro x k y hy w
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (om.pos x k y hy w h0).le
  refine ⟨⟨om.pot.rsmul K, ReciprocityTheory.AnForm.M.isPotentialRsmul A K om.pot om.isPot,
    fun x k y hy w hw => ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [levi_rsmul_chart A om.pot om.isPot K x k y hy w]
    exact mul_pos hK (om.pos x k y hy w hw)
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.1.2, hy.2.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.1.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.2, hy.2.1.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential HoloMap IsDegreeOff mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ThGe ell errE)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe (compat_chart contDiffAt_comp_symm)

noncomputable section

section Maps

variable {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
  {B : FinHolAtlas D Y} {A : FinHolAtlas E Z} {f : Y → Z}

theorem comp_chart_eventuallyEq (hf : HoloMap B A f) (g : Z → ℝ) (j : Fin B.n) (k : Fin A.n)
    {y : Fin D → ℂ} (hy : y ∈ (B.chart j).target)
    (hk : f ((B.chart j).symm y) ∈ (A.chart k).source) :
    (g ∘ f) ∘ (B.chart j).symm =ᶠ[𝓝 y]
      (g ∘ (A.chart k).symm) ∘ (A.chart k ∘ f ∘ (B.chart j).symm) := by
  filter_upwards [ReciprocityTheory.AnForm.M.holoMap_preimage_mem_nhds hf j k hy hk] with z hz
  simp only [Function.comp_apply, (A.chart k).left_inv hz.2]

theorem contDiffAt_comp_map (hf : HoloMap B A f) (g : Z → ℝ) (j : Fin B.n) (k : Fin A.n)
    {y : Fin D → ℂ} (hy : y ∈ (B.chart j).target)
    (hk : f ((B.chart j).symm y) ∈ (A.chart k).source)
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart k).symm) (A.chart k (f ((B.chart j).symm y)))) :
    ContDiffAt ℝ 2 ((g ∘ f) ∘ (B.chart j).symm) y := by
  have hτ : ContDiffAt ℝ 2 (A.chart k ∘ f ∘ (B.chart j).symm) y :=
    (show AnalyticAt ℝ (A.chart k ∘ f ∘ (B.chart j).symm) y from
      (hf.2 j k y ⟨hy, hk⟩).restrictScalars).contDiffAt
  exact (hg.comp y hτ).congr_of_eventuallyEq (comp_chart_eventuallyEq hf g j k hy hk)

theorem smooth_comp (hf : HoloMap B A f) {g : Z → ℝ} (hg : A.Smooth g) : B.Smooth (g ∘ f) := by
  intro j y hy
  obtain ⟨k, hk⟩ := A.cover (f ((B.chart j).symm y))
  have hτ : ContDiffAt ℝ ∞ (A.chart k ∘ f ∘ (B.chart j).symm) y :=
    (show AnalyticAt ℝ (A.chart k ∘ f ∘ (B.chart j).symm) y from
      (hf.2 j k y ⟨hy.1, hk⟩).restrictScalars).contDiffAt
  have hmem : (A.chart k).target ∩ (A.chart k).symm ⁻¹' Set.univ ∈
      𝓝 ((A.chart k ∘ f ∘ (B.chart j).symm) y) := by
    rw [Set.preimage_univ, Set.inter_univ]
    exact (A.chart k).open_target.mem_nhds ((A.chart k).map_source hk)
  exact (((hg k).contDiffAt hmem).comp y hτ).congr_of_eventuallyEq
    (comp_chart_eventuallyEq hf g j k hy.1 hk) |>.contDiffWithinAt

theorem levi_comp_map (hf : HoloMap B A f) (g : Z → ℝ) (j : Fin B.n) (k : Fin A.n)
    {y : Fin D → ℂ} (hy : y ∈ (B.chart j).target)
    (hk : f ((B.chart j).symm y) ∈ (A.chart k).source)
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart k).symm) (A.chart k (f ((B.chart j).symm y))))
    (w : Fin D → ℂ) :
    levi ((g ∘ f) ∘ (B.chart j).symm) y w =
      levi (g ∘ (A.chart k).symm) (A.chart k (f ((B.chart j).symm y)))
        (fderiv ℂ (A.chart k ∘ f ∘ (B.chart j).symm) y w) := by
  rw [levi_congr (comp_chart_eventuallyEq hf g j k hy hk) w]
  exact levi_comp w (hf.2 j k y ⟨hy, hk⟩) hg

theorem thGe_pullback {R' : RegChartData B} {R : RegChartData A} (hP : IsPullbackData R' R f)
    {K : ℝ} (hK : ∀ (x x' : Y) (k : Fin B.n),
      ∀ y ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (R'.om.U x ∩ f ⁻¹' R.om.U (f x')),
      ∀ w : Fin D → ℂ, levi ((fun z => R.om.φ (f x') (f z)) ∘ (B.chart k).symm) y w ≤
        K * levi (R'.om.φ x ∘ (B.chart k).symm) y w)
    {g : Z → ℝ} (hg : A.Smooth g) {e e' : ℝ} (hS : ThGe A R.θ g R.om (-e))
    (he : |e| * |K| ≤ e') : ThGe B R'.θ (g ∘ f) R'.om (-e') := by
  intro x k y hy w
  have hyt : y ∈ (B.chart k).target := hy.1
  have hqs : (B.chart k).symm y ∈ (B.chart k).source := (B.chart k).map_target hyt
  have hqy : B.chart k ((B.chart k).symm y) = y := (B.chart k).right_inv hyt
  obtain ⟨k', hk'⟩ := A.cover (f ((B.chart k).symm y))
  have hp' : A.chart k' (f ((B.chart k).symm y)) ∈ (A.chart k').target :=
    (A.chart k').map_source hk'
  have hpp : (A.chart k').symm (A.chart k' (f ((B.chart k).symm y))) = f ((B.chart k).symm y) :=
    (A.chart k').left_inv hk'
  have hθ' : ContDiffAt ℝ 2 (R'.θ.φ x ∘ (B.chart k).symm) y := by
    have h := contDiffAt_comp_symm (R'.θ.isOpen_U x) (R'.θ_pot.1 x) (compat_chart B k) hy.2.1 hqs
    rwa [hqy] at h
  have hgC := contDiffAt_comp_symm isOpen_univ hg (compat_chart A k') trivial hk'
  have hθC := contDiffAt_comp_symm (R.θ.isOpen_U (f ((B.chart k).symm y)))
    (R.θ_pot.1 (f ((B.chart k).symm y))) (compat_chart A k') (R.θ.mem_U _) hk'
  have hωC := contDiffAt_comp_symm (R.om.isOpen_U (f ((B.chart k).symm y)))
    (R.om_pot.1 (f ((B.chart k).symm y))) (compat_chart A k') (R.om.mem_U _) hk'
  have hsumC : ContDiffAt ℝ 2
      ((fun z => R.θ.φ (f ((B.chart k).symm y)) z + g z) ∘ (A.chart k').symm)
      (A.chart k' (f ((B.chart k).symm y))) := hθC.add hgC

  have e1 : levi ((fun z => R'.θ.φ x z + (g ∘ f) z) ∘ (B.chart k).symm) y w =
      levi (R'.θ.φ x ∘ (B.chart k).symm) y w + 1 * levi ((g ∘ f) ∘ (B.chart k).symm) y w := by
    rw [← levi_add_smul 1 hθ' (contDiffAt_comp_map hP.holo g k k' hyt hk' hgC) w]
    exact levi_congr (Eventually.of_forall fun z => by simp [Function.comp]) w
  have e2 : levi (((fun z => R.θ.φ (f ((B.chart k).symm y)) z + g z) ∘ f) ∘ (B.chart k).symm) y w =
      levi ((R.θ.φ (f ((B.chart k).symm y)) ∘ f) ∘ (B.chart k).symm) y w +
        1 * levi ((g ∘ f) ∘ (B.chart k).symm) y w := by
    rw [← levi_add_smul 1 (contDiffAt_comp_map hP.holo _ k k' hyt hk' hθC)
      (contDiffAt_comp_map hP.holo g k k' hyt hk' hgC) w]
    exact levi_congr (Eventually.of_forall fun z => by simp [Function.comp]) w
  have e3 := levi_comp_map hP.holo _ k k' hyt hk' hsumC w
  have e4 : levi (R'.θ.φ x ∘ (B.chart k).symm) y w =
      levi ((R.θ.φ (f ((B.chart k).symm y)) ∘ f) ∘ (B.chart k).symm) y w :=
    hP.θ_eq x ((B.chart k).symm y) k y ⟨hyt, hy.2.1, R.θ.mem_U _⟩ w
  have hbase := hS (f ((B.chart k).symm y)) k' (A.chart k' (f ((B.chart k).symm y)))
    ⟨hp', by rw [Set.mem_preimage, hpp]; exact ⟨R.θ.mem_U _, R.om.mem_U _⟩⟩
    (fderiv ℂ (A.chart k' ∘ f ∘ (B.chart k).symm) y w)
  have e5 := levi_comp_map hP.holo _ k k' hyt hk' hωC w
  have hKy := hK x ((B.chart k).symm y) k y ⟨hyt, hy.2.2, R.om.mem_U _⟩ w
  have hLz : 0 ≤ levi (R.om.φ (f ((B.chart k).symm y)) ∘ (A.chart k').symm)
      (A.chart k' (f ((B.chart k).symm y))) (fderiv ℂ (A.chart k' ∘ f ∘ (B.chart k).symm) y w) := by
    by_cases hv : fderiv ℂ (A.chart k' ∘ f ∘ (B.chart k).symm) y w = 0
    · rw [hv, levi_zero]
    · exact (R.om_pos _ k' _ ⟨hp', by rw [Set.mem_preimage, hpp]; exact R.om.mem_U _⟩ _ hv).le
  have hL' : 0 ≤ levi (R'.om.φ x ∘ (B.chart k).symm) y w := by
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (R'.om_pos x k y ⟨hyt, hy.2.2⟩ w hw).le
  have hz : levi ((fun z => R.om.φ (f ((B.chart k).symm y)) (f z)) ∘ (B.chart k).symm) y w =
      levi (R.om.φ (f ((B.chart k).symm y)) ∘ (A.chart k').symm)
        (A.chart k' (f ((B.chart k).symm y))) (fderiv ℂ (A.chart k' ∘ f ∘ (B.chart k).symm) y w) :=
    e5
  rw [hz] at hKy
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self e) hLz
  have h2 := mul_le_mul_of_nonneg_left (hKy.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hL'))
    (abs_nonneg e)
  have h3 := mul_le_mul_of_nonneg_right he hL'
  rw [e1, e4, ← e2, e3]
  nlinarith

end Maps

theorem SystemPullback.proof (hc2 : C2ConvergencePullback.Statement) : SystemPullback.Statement := by
  intro D E Y Z _ _ B A R' R f hP S
  obtain ⟨K, hK⟩ := hP.om_le
  have hYo : ∀ y ∈ R'.Yo, f y ∈ R.Yo := fun y hy => by rw [hP.Yo_eq] at hy; exact hy
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = (|K| + 1) * |S.C| := ⟨_, rfl⟩
  have hCC' : |S.C| ≤ C' := by
    rw [hC']; exact le_mul_of_one_le_left (abs_nonneg _) (by linarith [abs_nonneg K])
  have herr : ∀ c t, errE c t = c * (Real.log (ell t) / ell t) := fun c t => by
    unfold errE; ring
  have ha : ∀ t, 1 ≤ ell t → 0 ≤ Real.log (ell t) / ell t := fun t h =>
    div_nonneg (Real.log_nonneg h) (by linarith)
  have hle : ∀ t, 1 ≤ ell t → errE S.C t ≤ errE C' t := fun t h => by
    rw [herr, herr]; exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCC') (ha t h)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (S.ph t) := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (Real.exp_pos (-S.ell₀))] with t ht ht'
    refine S.smooth t ht ?_
    have h1 : Real.log t < -S.ell₀ := by
      have := Real.log_lt_log ht ht'.2
      rwa [Real.log_exp] at this
    show S.ell₀ ≤ Real.log t⁻¹
    rw [Real.log_inv]; linarith
  have hc := hc2 B A f hP.holo R.Yo R.isOpen_Yo S.ph R.φ R'.φ R.φ_smooth
    (fun y hy => hP.φ_eq y (by rw [hP.Yo_eq]; exact hy)) hev S.c2
  refine ⟨{ ph := fun t y => S.ph t (f y)
            C := C'
            ell₀ := max S.ell₀ 1
            smooth := ?_
            le_ph := ?_
            ph_le := ?_
            le_log := ?_
            thGe := ?_
            near := ?_
            far := ?_
            mono := ?_
            c2 := ?_ }, fun _ _ => rfl⟩
  · intro t ht hℓ
    exact smooth_comp hP.holo (S.smooth t ht (le_of_max_le_left hℓ))
  · intro t ht hℓ y hy
    rw [hP.φ_eq y hy]
    exact S.le_ph t ht (le_of_max_le_left hℓ) (f y) (hYo y hy)
  · intro t ht hℓ y
    exact (S.ph_le t ht (le_of_max_le_left hℓ) (f y)).trans ((le_abs_self _).trans hCC')
  · intro t ht hℓ y
    have hl : 0 ≤ Real.log (ell t) := Real.log_nonneg (le_of_max_le_right hℓ)
    have h1 := S.le_log t ht (le_of_max_le_left hℓ) (f y)
    have h2 := mul_le_mul_of_nonneg_right ((le_abs_self S.C).trans hCC') hl
    linarith
  · intro t ht hℓ
    refine thGe_pullback hP hK (S.smooth t ht (le_of_max_le_left hℓ))
      (S.thGe t ht (le_of_max_le_left hℓ)) ?_
    have h0 := ha t (le_of_max_le_right hℓ)
    rw [herr, herr, abs_mul, abs_of_nonneg h0, hC']
    nlinarith [mul_nonneg (abs_nonneg S.C) h0, abs_nonneg K]
  · intro t ht hℓ y hy hr
    rw [hP.r_eq y hy] at hr
    rw [hP.φ_eq y hy]
    have h1 := S.near t ht (le_of_max_le_left hℓ) (f y) (hYo y hy) hr
    have h2 := hle t (le_of_max_le_right hℓ)
    linarith
  · intro t ht hℓ y hy
    rw [hP.φ_eq y hy, hP.r_eq y hy]
    have h1 := S.far t ht (le_of_max_le_left hℓ) (f y) (hYo y hy)
    have hr : 0 ≤ R.r (f y) := by linarith [R.one_le_r (f y) (hYo y hy)]
    have h2 := mul_le_mul_of_nonneg_right (hle t (le_of_max_le_right hℓ)) hr
    linarith
  · intro t t₀ ht htt hℓ y
    have h1 : 1 ≤ ell t₀ := le_of_max_le_right hℓ
    have h0 := ha t₀ h1
    have hm := S.mono t t₀ ht htt (le_of_max_le_left hℓ) (f y)
    have hsq : S.C * S.C ≤ C' * C' := by
      have := mul_self_le_mul_self (abs_nonneg S.C) hCC'
      rwa [abs_mul_abs_self] at this
    have h2 := mul_le_mul_of_nonneg_right hsq h0
    rw [herr] at hm
    rw [herr]
    nlinarith
  · intro k K' hK' hKs
    rw [hP.Yo_eq] at hKs
    exact hc k K' hK' hKs

section Cover

variable {D : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [CompactSpace Y]
  [T2Space Y] [CompactSpace Z] [T2Space Z] {B : FinHolAtlas D Y} {A : FinHolAtlas D Z} {h : Y → Z}

end Cover

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

def TailBound.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A), (∀ x ∈ F.Yo, Real.exp 1 ≤ F.r x) →
    ∃ CE : ℝ, ∀ (i : Fin D → Fin F.m) (τ : Fin D → ℝ),
      (∀ j, 0 < τ j ∧ (F.sys (i j)).ell₀ ≤ ell (τ j) ∧ errE (F.sys (i j)).C (τ j) ≤ 1) →
      TailLogBound A F.Yo F.r (fun j => (F.sys (i j)).curr (τ j)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem tailLogBound_congr {A : FinHolAtlas D X} {Yo : Set X} {r r' : X → ℝ}
    (h : ∀ x ∈ Yo, r x = r' x) {T : Fin D → LocPot X} {CE : ℝ}
    (hT : TailLogBound A Yo r T CE) : TailLogBound A Yo r' T CE := by
  intro R₀ hR₀
  have ht : tail Yo r R₀ = tail Yo r' R₀ := Set.ext fun x =>
    ⟨fun hx => ⟨hx.1, by rw [← h x hx.1]; exact hx.2⟩,
      fun hx => ⟨hx.1, by rw [h x hx.1]; exact hx.2⟩⟩
  have hi : (tail Yo r' R₀).indicator (fun x => Real.log (r' x)) =
      (tail Yo r R₀).indicator (fun x => Real.log (r x)) := by
    rw [ht]
    exact Set.indicator_congr fun x hx => by rw [h x hx.1]
  rw [hi]
  exact hT R₀ hR₀

theorem isBoundedPotForm_congr {A : FinHolAtlas D X} {Yo : Set X} {r r' : X → ℝ}
    (h : ∀ x ∈ Yo, r x = r' x) {Om : KaehlerForm A} {C₁ : ℝ} {th : LocPot X} {u : X → ℝ}
    (hT : IsBoundedPotForm A Yo r Om C₁ th u) : IsBoundedPotForm A Yo r' Om C₁ th u :=
  { hT with le_u := fun x hx => by rw [← h x hx]; exact hT.le_u x hx }

theorem isBoundedPotForm_mono {A : FinHolAtlas D X} {Yo : Set X} {r : X → ℝ}
    (hr : ∀ x ∈ Yo, Real.exp 1 ≤ r x) {Om : KaehlerForm A} {C₁ C₁' : ℝ} (hC : C₁ ≤ C₁')
    {th : LocPot X} {u : X → ℝ} (hT : IsBoundedPotForm A Yo r Om C₁ th u) :
    IsBoundedPotForm A Yo r Om C₁' th u :=
  { hT with
    le_u := fun x hx => by
      have h0 : 0 ≤ Real.log (r x) := Real.log_nonneg (le_trans (by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith) (hr x hx))
      have := mul_le_mul_of_nonneg_right hC h0
      have := hT.le_u x hx
      linarith }

theorem TailBound.proof (h₁ : ListTailLog.Statement) (h₂ : BoundingKaehler.Statement) :
    TailBound.Statement := by
  intro X _ _ _ D A F hr
  rcases Nat.eq_zero_or_pos F.m with hm | hm
  · rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      obtain ⟨CE, hCE⟩ := tailLogBound_dim_zero A F.Yo F.r Fin.elim0
      refine ⟨CE, fun i τ _ => ?_⟩
      have e : (fun j => (F.sys (i j)).curr (τ j)) = (Fin.elim0 : Fin 0 → LocPot X) :=
        funext fun j => j.elim0
      rw [e]
      exact hCE
    · exact ⟨0, fun i => absurd (i ⟨0, hD⟩).2 (by omega)⟩
  · set k : Fin F.m := ⟨0, hm⟩
    obtain ⟨Om, hOm⟩ := h₂ D A ⟨(F.R k).om, (F.R k).om_pot, (F.R k).om_pos⟩ F.m
      (fun i => thetaOmega (F.R i))
      (fun i => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot (F.R i).om_pot)
    have hrk : ∀ x ∈ (F.R k).Yo, Real.exp 1 ≤ (F.R k).r x := fun x hx => by
      rw [F.Yo_eq k] at hx
      rw [F.r_eq k x hx]
      exact hr x hx
    obtain ⟨CE, hCE⟩ := h₁ D A (F.R k) hrk Om (∑ i, (|(F.R i).C| + |(F.sys i).C|))
    refine ⟨CE, fun i τ hτ => ?_⟩
    have h := hCE (fun j => thetaOmega (F.R (i j))) (fun j => (F.sys (i j)).uT (τ j)) fun j => by
      have hRi : ∀ x ∈ (F.R (i j)).Yo, Real.exp 1 ≤ (F.R (i j)).r x := fun x hx => by
        rw [F.Yo_eq] at hx
        rw [F.r_eq _ x hx]
        exact hr x hx
      have hT := ((F.sys (i j)).curr_isSmoothPotForm hRi Om (hOm (i j)).1 (hOm (i j)).2 (τ j)
        (hτ j).1 (hτ j).2.1 (hτ j).2.2).1
      have hCi : |(F.R (i j)).C| + |(F.sys (i j)).C| ≤ ∑ l, (|(F.R l).C| + |(F.sys l).C|) :=
        Finset.single_le_sum (f := fun l => |(F.R l).C| + |(F.sys l).C|)
          (fun _ _ => by positivity) (Finset.mem_univ _)
      have hT' := isBoundedPotForm_mono hRi hCi hT
      rw [F.Yo_eq] at hT' ⊢
      exact isBoundedPotForm_congr (fun x hx => by rw [F.r_eq _ x hx, F.r_eq k x hx]) hT'
    rw [F.Yo_eq k] at h
    exact tailLogBound_congr (fun x hx => F.r_eq k x hx) h

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ContDiff

section Objects

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type}
  [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E}

def regularizedFlagPullbackLine (Pl : PlueckerData D) (H : HodgeData D) {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ)
    (t : ℝ) : HermLine Pl.ιY :=
  IndefiniteRowSideFullHecke.Inter.pullHerm Pl.isBlockMap_xV (muReg H S B t)

def flagFun (Pl : PlueckerData D) (H : HodgeData D) (Ba : AdaptedBasis H) {M : XModel D}
    (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) {r : ℕ} (c : Fin r → ℝ)
    (N : Fin r → Fin D.flagDim0 → HermLine Pl.ιY) (t : ℝ) : ℝ :=
  ∑ m, c m * II _ Pl.ιY (Pl.flagPrime Ba) (D.n + 1 + D.flagDim0)
    (Fin.append (fun _ : Fin (D.n + 1) => regularizedFlagPullbackLine Pl H S B t) (N m))

def PPmuFib (Pl : PlueckerData D) (H : HodgeData D) (Ba : AdaptedBasis H) {M : XModel D}
    (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) {r : ℕ} (c : Fin r → ℝ)
    (N : Fin r → Fin D.flagDim0 → HermLine Pl.ιY) : ℝ :=
  limUnder (𝓝[>] 0) (flagFun Pl H Ba S B c N)

def fibNum {Pl : PlueckerData D} {H : HodgeData D} {Ba : AdaptedBasis H} (G : GenFibre Pl.xV (Pl.flagPrime Ba))
    (J : IFamily G.Φ (fibreIdx Pl.ιY (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))))) {r : ℕ} (c : Fin r → ℝ)
    (N : Fin r → Fin D.flagDim0 → HermLine Pl.ιY) : ℝ :=
  ∑ m, c m * (J (fibreIdeal Sum.inl G) D.flagDim0 (fun j => fibreDeg Sum.inl (N m j).a) : ℝ)

end Objects

def AgreementOnBase.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D) (Ba : AdaptedBasis H)
    (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) (G : GenFibre Pl.xV (Pl.flagPrime Ba))
    (J : IFamily G.Φ (fibreIdx Pl.ιY (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))))) (r : ℕ) (c : Fin r → ℝ)
    (N : Fin r → Fin D.flagDim0 → HermLine Pl.ιY),
    IsFieldIntersection J → (∀ m j, IsSmoothHerm (N m j)) →
    (∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg H S B t)) → ArLimExists H S B →
    Tendsto (flagFun Pl H Ba S B c N) (𝓝[>] 0) (𝓝 (fibNum G J c N * arLim H S B)) ∧
      PPmuFib Pl H Ba S B c N = fibNum G J c N * arLim H S B

theorem AgreementOnBase.proof (hPD : PushDown.Statement) : AgreementOnBase.Statement := by
  intro II hII Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H Ba M S B G J r c N hJ hN hsm hlim
  obtain ⟨L, hL⟩ := hlim
  have hPush := (hPD II hII Ψ K ι Ω E D Pl H Ba).1
  have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      fibNum G J c N * arLimFun H S B t = flagFun Pl H Ba S B c N t := by
    filter_upwards [hsm] with t ht
    unfold flagFun fibNum
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hPush G J (fun _ => muReg H S B t) (fun _ => regularizedFlagPullbackLine Pl H S B t) (N m) hJ (fun _ => ht)
      (fun _ => IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm _ _) (hN m)]
    unfold arLimFun
    ring
  have hT : Tendsto (flagFun Pl H Ba S B c N) (𝓝[>] 0) (𝓝 (fibNum G J c N * L)) :=
    (hL.const_mul _).congr' heq
  have hA : arLim H S B = L := hL.limUnder_eq
  rw [hA]
  exact ⟨hT, hT.limUnder_eq⟩

section Inhabitants

open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine
open Line

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit

end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem RegularizedMaxConvergenceC2.full : RegularizedMaxConvergenceC2.Statement := RegularizedMaxConvergenceC2.proof

theorem GluedLocal.full : GluedLocal.Statement := GluedLocal.proof

theorem ConvergenceRate.full : ConvergenceRate.Statement := ConvergenceRate.proof

theorem ConvergenceSigned.full : ConvergenceSigned.Statement := ConvergenceSigned.proof

theorem EnergyStep.full : EnergyStep.Statement := EnergyStep.proof

theorem EnergySum.full : EnergySum.Statement := EnergySum.proof

theorem RegularisedMonotone.full : RegularisedMonotone.Statement := RegularisedMonotone.proof

theorem KaehlerBound.full : KaehlerBound.Statement := KaehlerBound.proof

theorem BoundingKaehler.full : BoundingKaehler.Statement := BoundingKaehler.proof

theorem LinearWeights.full : LinearWeights.Statement := LinearWeights.proof KaehlerBound.full

theorem C2ConvergencePullback.full : C2ConvergencePullback.Statement := C2ConvergencePullback.proof

theorem SystemPullback.full : SystemPullback.Statement := SystemPullback.proof C2ConvergencePullback.full

theorem DivisorNull.full : DivisorNull.Statement := DivisorNull.proof

theorem GreenMassZero.full : GreenMassZero.Statement := GreenMassZero.proof

theorem Telescoping.full : Telescoping.Statement := Telescoping.proof

theorem TelescopingFamily.full : TelescopingFamily.Statement := TelescopingFamily.proof

theorem TailBound.of_listTailLog (h : ListTailLog.Statement) : TailBound.Statement :=
  TailBound.proof h BoundingKaehler.full

theorem SystemIndependence.of_productBounds (h : ProductBounds.Statement) :
    SystemIndependence.Statement :=
  SystemIndependence.proof DivisorNull.full h

theorem UniformIntegrability.of_greenMass (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement :=
  UniformIntegrability.proof GreenMassZero.full h₁ h₂ h₃

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)

theorem log_le_one_add_mul_log {a b B : ℝ} (ha : Real.exp 1 ≤ a) (hb : 0 < b) (hB : 0 ≤ B)
    (hab : b ≤ a + B) : Real.log b ≤ (1 + B) * Real.log a := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha0 : 0 < a := by linarith
  have hla : 1 ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at this
  have h1 : b ≤ a * (1 + B) := by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ a by linarith) hB]
  have h2 : Real.log b ≤ Real.log a + Real.log (1 + B) := by
    rw [← Real.log_mul ha0.ne' (by linarith)]
    exact Real.log_le_log hb h1
  have h3 : Real.log (1 + B) ≤ B := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + B by linarith)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hla hB]

theorem ListTailLog.proof (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement := by
  intro X _ _ _ D A R hr Om C₁
  obtain ⟨L, s, hL, hs, hs1, hYo, hden, hrc, hrEc, B, hB⟩ := hC D A R
  have hrE : ∀ x ∈ R.Yo, Real.exp 1 ≤ rSec L s x := fun x hx => by
    rw [← hYo] at hx
    have hpos : 0 < ‖s x x‖ * Real.exp (-L.φ x x) :=
      mul_pos (norm_pos_iff.2 hx) (Real.exp_pos _)
    have : logNormSec L s x ≤ 0 := Real.log_nonpos hpos.le (hs1 x)
    simp only [rSec]
    linarith
  have hC₁ : 0 ≤ max C₁ 0 * (1 + max B 0) :=
    mul_nonneg (le_max_right _ _) (by linarith [le_max_right B 0])
  obtain ⟨CE, hCE⟩ := hE D A Om L s hL hs (hYo ▸ hden) hs1 _ hC₁
  obtain ⟨CE', hCE'⟩ := hS D (max B 0) CE
  refine ⟨CE', fun th u hT => ?_⟩
  obtain ⟨hA, hpos, hmono⟩ := hM D A R.Yo R.r Om C₁ th u R.isOpen_Yo hT
  have hu : ∀ i, IsLemmaEPot A Om L s (max C₁ 0 * (1 + max B 0)) (u i) := fun i => by
    have hTi := hT i
    refine ⟨by rw [hYo]; exact hTi.u_smooth, by rw [hYo]; exact hA i,
      by rw [hYo]; exact hTi.u_nonpos, fun x hx => ?_, ?_⟩
    · rw [hYo] at hx
      have hl := log_le_one_add_mul_log (b := R.r x) (hrE x hx) (by linarith [hr x hx, Real.exp_pos 1])
        (le_max_right B 0) (by linarith [(abs_le.1 (hB x hx)).2, le_max_left B 0])
      have h0 : 0 ≤ Real.log (R.r x) :=
        Real.log_nonneg (by linarith [hr x hx, Real.add_one_le_exp (1 : ℝ)])
      have := mul_le_mul_of_nonneg_left hl (le_max_right C₁ 0)
      have := mul_le_mul_of_nonneg_right (le_max_left C₁ 0) h0
      have := hTi.le_u x hx
      nlinarith
    · rcases hTi.smooth_or_pole with h | h
      · exact Or.inl h
      · right
        rw [hYo]
        exact h
  have h2 : TailLogBound A R.Yo (rSec L s) (fun j => potForm (th j) (u j)) CE := by
    have h1 := hCE u hu
    rw [hYo] at h1
    intro R₀ hR₀
    obtain ⟨hi, hle⟩ := h1 R₀ hR₀
    obtain ⟨hi', hle'⟩ := hmono _
      (fun x => Set.indicator_nonneg (fun y hy => Real.log_nonneg
        (by linarith [hrE y hy.1, Real.add_one_le_exp (1 : ℝ)])) x)
      (fun x hx => Set.indicator_of_notMem (fun h => hx h.1) _) hi
    exact ⟨hi', hle'.trans hle⟩
  exact hCE' A R.Yo R.r (rSec L s) _ R.isOpen_Yo hrc hrEc hr hrE
    (fun x hx => (hB x hx).trans (le_max_left B 0)) hpos h2

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem regChartData_continuousOn_r (R : RegChartData A) : ContinuousOn R.r R.Yo := by
  intro x hx
  obtain ⟨j, hxs, hxW⟩ := R.cover x
  have hW : R.ψ j x ∈ R.W j :=
    R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hxW)))
  have hnd : R.ψ j x ∉ coordDiv (R.S j) :=
    (R.mem_Yo_iff j _ hW).1 (by rw [(R.ψ j).left_inv hxs]; exact hx)
  have hne : ∀ i ∈ R.S j, R.ψ j x i ≠ 0 := fun i hi h0 => hnd ⟨i, hi, h0⟩
  let g : (Fin D → ℂ) → ℝ := fun z => Real.exp 1 + R.f j z - ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)
  have hg : ContinuousAt g (R.ψ j x) := by
    refine (continuousAt_const.add ((R.f_cont j).continuousAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW))).sub
      (tendsto_finsetSum (R.S j) fun i hi => ?_)
    exact ((continuous_apply i).continuousAt.norm.pow 2).log (pow_pos (norm_pos_iff.2 (hne i hi)) 2).ne'
  have hz : ∀ᶠ z in 𝓝 (R.ψ j x), z ∈ R.W j ∧ z ∉ coordDiv (R.S j) := by
    refine (show ∀ᶠ z in 𝓝 (R.ψ j x), z ∈ R.W j from (R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW).and ?_
    have : ∀ᶠ z in 𝓝 (R.ψ j x), ∀ i ∈ R.S j, z i ≠ 0 := (eventually_all_finset _).2 fun i hi =>
      (continuous_apply i).continuousAt.eventually_ne (hne i hi)
    exact this.mono fun z hz ⟨i, hi, h0⟩ => hz i hi h0
  have hev : R.r =ᶠ[𝓝 x] g ∘ R.ψ j := by
    filter_upwards [((R.ψ j).continuousAt hxs).eventually hz, (R.ψ j).open_source.mem_nhds hxs]
      with y hy hys
    have := R.r_chart j (R.ψ j y) ⟨hy.1, hy.2⟩
    rw [(R.ψ j).left_inv hys] at this
    exact this
  exact ((hg.comp ((R.ψ j).continuousAt hxs)).congr hev.symm).continuousWithinAt

theorem regChartData_C_nonneg (R : RegChartData A) {x : X} (hx : x ∈ R.Yo) : 0 ≤ R.C := by
  by_contra h
  have h1 := R.le_φ x hx
  have h2 := R.φ_le x hx
  have h3 : 0 ≤ Real.log (R.r x) := Real.log_nonneg (R.one_le_r x hx)
  nlinarith

def regChartShift (R : RegChartData A) : RegChartData A :=
  { R with
    r := fun x => R.r x + (Real.exp 1 - 1)
    f := fun j z => R.f j z + (Real.exp 1 - 1)
    f_cont := fun j => (R.f_cont j).add continuousOn_const
    f_bdd := fun j => by
      obtain ⟨B, hB⟩ := R.f_bdd j
      exact ⟨B + |Real.exp 1 - 1|, fun z hz => (abs_add_le _ _).trans (by linarith [hB z hz])⟩
    r_chart := fun j z hz => by rw [R.r_chart j z hz]; ring
    one_le_r := fun x hx => by
      have := R.one_le_r x hx
      have := Real.add_one_le_exp (0 : ℝ)
      rw [Real.exp_zero] at this
      linarith [Real.add_one_le_exp (1 : ℝ)]
    le_φ := fun x hx => by
      have hC := regChartData_C_nonneg R hx
      have h1 := R.one_le_r x hx
      have : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith [Real.add_one_le_exp (1 : ℝ)])
      nlinarith [R.le_φ x hx]
    grad := fun j z hz => by
      have hx : (R.ψ j).symm z ∈ R.Yo := (R.mem_Yo_iff j z hz.1).2 hz.2
      have hC := regChartData_C_nonneg R hx
      have h1 := R.one_le_r _ hx
      have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      refine (R.grad j z hz).trans (mul_le_mul (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) (by linarith) hC) hC)
        (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)) }

theorem tailLogBound_of_le [CompactSpace X] [T2Space X] {Yo : Set X} (hYo : IsOpen Yo)
    {r r' : X → ℝ} (hr : ContinuousOn r Yo) (hle : ∀ x ∈ Yo, r x ≤ r' x) {T : Fin D → LocPot X}
    (hpot : ∀ i, IsPotential A (T i)) (hnn : ∀ i, FormNonneg A Yo (T i)) {CE : ℝ}
    (h : TailLogBound A Yo r' T CE) : TailLogBound A Yo r T CE := by
  intro R₀ hR₀
  obtain ⟨hI, hB⟩ := h R₀ hR₀
  have he : (1 : ℝ) ≤ R₀ := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hR₀
  set gs := (tail Yo r R₀).indicator fun x => Real.log (r x) with hgs
  set gb := (tail Yo r' R₀).indicator fun x => Real.log (r' x) with hgb
  have hg : ∀ x, 0 ≤ gs x ∧ gs x ≤ gb x := by
    intro x
    by_cases hx : x ∈ tail Yo r R₀
    · have hx' : x ∈ tail Yo r' R₀ := ⟨hx.1, hx.2.trans (hle x hx.1)⟩
      rw [hgs, hgb, indicator_of_mem hx, indicator_of_mem hx']
      exact ⟨Real.log_nonneg (he.trans hx.2),
        Real.log_le_log (by linarith [hx.2]) (hle x hx.1)⟩
    · rw [hgs, indicator_of_notMem hx]
      refine ⟨le_rfl, ?_⟩
      by_cases hx' : x ∈ tail Yo r' R₀
      · rw [hgb, indicator_of_mem hx']
        exact Real.log_nonneg (he.trans hx'.2)
      · rw [hgb, indicator_of_notMem hx']
  have hI' : MIntegrable A T gs := by
    intro k K hK hKc
    set U := (A.chart k).target ∩ (A.chart k).symm ⁻¹' Yo with hUdef
    have hU : IsOpen U := (A.chart k).isOpen_inter_preimage_symm hYo
    have hF : ContinuousOn (fun y => r ((A.chart k).symm y)) U :=
      hr.comp ((A.chart k).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2
    set Ms := U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Ici R₀ with hMs
    have hM : MeasurableSet Ms := by
      have ho := hF.isOpen_inter_preimage hU (isOpen_Iio (a := R₀))
      have e : Ms = U \ (U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Iio R₀) := by
        ext y
        constructor
        · rintro ⟨hu, hge⟩
          exact ⟨hu, fun hm => (not_le.2 (show r ((A.chart k).symm y) < R₀ from hm.2)) (show R₀ ≤ r ((A.chart k).symm y) from hge)⟩
        · rintro ⟨hu, hn⟩
          exact ⟨hu, show R₀ ≤ r ((A.chart k).symm y) from not_lt.1 fun hlt => hn ⟨hu, hlt⟩⟩
      rw [e]
      exact hU.measurableSet.diff ho.measurableSet
    have hlog : ContinuousOn (fun y => Real.log (r ((A.chart k).symm y))) Ms :=
      (hF.mono inter_subset_left).log fun y hy => by
        have : R₀ ≤ r ((A.chart k).symm y) := hy.2
        exact (by linarith : (0 : ℝ) < _).ne'
    have hcongr : (fun y => gs ((A.chart k).symm y)) =ᵐ[volume.restrict K]
        Ms.indicator fun y => Real.log (r ((A.chart k).symm y)) := by
      refine ae_restrict_of_forall_mem hKc.measurableSet fun y hy => ?_
      have hyt := hK hy
      by_cases hc : (A.chart k).symm y ∈ tail Yo r R₀
      · show (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart k).symm y) = _
        rw [indicator_of_mem hc, indicator_of_mem (show y ∈ Ms from ⟨⟨hyt, hc.1⟩, hc.2⟩)]
      · show (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart k).symm y) = _
        rw [indicator_of_notMem hc,
          indicator_of_notMem (show y ∉ Ms from fun hm => hc ⟨hm.1.2, hm.2⟩)]
    have hmeas : AEStronglyMeasurable
        (fun y => gs ((A.chart k).symm y) * ReciprocityTheory.AnForm.M.locDens A T k y) (volume.restrict K) :=
      (((aestronglyMeasurable_indicator_iff hM).2 (hlog.aestronglyMeasurable hM)).congr
        hcongr.symm).mul
        (((ReciprocityTheory.AnForm.M.locDensCont A T hpot k).mono hK).aestronglyMeasurable hKc.measurableSet)
    refine (hI k K hK hKc).norm.mono' hmeas (ae_of_all _ fun y => ?_)
    simp only [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_of_nonneg (hg _).1, Real.norm_of_nonneg ((hg _).1.trans (hg _).2)]
    exact (hg _).2
  refine ⟨hI', ?_⟩
  have hlin := ReciprocityTheory.AnForm.M.mIntLinear A T hpot (-1) gs gb hI' hI
  have h0 := SystemIndependence.mInt_nonneg_on A Yo T hpot hnn (fun x => -1 * gs x + gb x)
    (fun x => by linarith [hg x]) (fun x hx => by
      rw [hgs, hgb, indicator_of_notMem (fun h => hx h.1), indicator_of_notMem (fun h => hx h.1)]
      ring)
  linarith

theorem ListTailLogSmooth.proof (h : ListTailLog.Statement) : ListTailLogSmooth.Statement := by
  intro D X _ _ _ A R Om C₁
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨CE, hCE⟩ := h D A (regChartShift R) (fun x hx => by
    show Real.exp 1 ≤ R.r x + (Real.exp 1 - 1)
    linarith [R.one_le_r x hx]) Om (max C₁ 0)
  refine ⟨CE, fun th u hT => ?_⟩
  have hpot : ∀ i, IsPotential A (potForm (th i) (u i)) := fun i =>
    ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (hT i).1.th_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hT i).2)
  refine tailLogBound_of_le R.isOpen_Yo (regChartData_continuousOn_r R)
    (r' := (regChartShift R).r) (fun x _ => by show R.r x ≤ R.r x + (Real.exp 1 - 1); linarith)
    hpot (fun i => (hT i).1.nonneg) (hCE th u fun j => ?_)
  exact { (hT j).1 with
    le_u := fun x hx => by
      have h1 := R.one_le_r x hx
      have hl : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith)
      have h0 := Real.log_nonneg h1
      have hu := (hT j).1.le_u x hx
      show -(max C₁ 0 * Real.log (R.r x + (Real.exp 1 - 1))) ≤ u j x
      nlinarith [le_max_left C₁ 0, le_max_right C₁ 0] }

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable isPotentialAdd
  isPotential_ofFun mIntCongrNull massIndep mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem ProductBounds.proof (hM : ListProductMass.Statement) (hT : ListTailLogSmooth.Statement) :
    ProductBounds.Statement := by
  intro D X _ _ _ A R Om C₁
  obtain ⟨CE, hCE⟩ := hT A R Om C₁
  refine ⟨Om.vol, CE, fun th u hf => ⟨?_, hCE th u hf⟩⟩
  have hpot : ∀ i, IsPotential A (potForm (th i) (u i)) := fun i =>
    isPotentialAdd A _ _ (hf i).1.th_pot (isPotential_ofFun A _ (hf i).2)
  have hnull := DivisorNull.proof A R
  have hind : mInt A (fun i => potForm (th i) (u i)) (R.Yo.indicator 1) =
      mInt A (fun i => potForm (th i) (u i)) (fun _ => 1) :=
    mIntCongrNull A _ R.Yoᶜ hnull.1 hnull.2 _ _ fun x hx => by
      have hx' : x ∈ R.Yo := by simpa using hx
      simp [Set.indicator_of_mem hx']
  have hstokes : mInt A (fun i => potForm (th i) (u i)) (fun _ => 1) = mInt A th (fun _ => 1) :=
    massIndep A th u (fun i => (hf i).1.th_pot) (fun i => (hf i).2)
  refine ⟨?_, hind.trans hstokes, ?_⟩
  · intro j K hK hKc
    have h1 := mIntegrableCont A _ hpot (fun _ => (1 : ℝ)) continuous_const j K hK hKc
    have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo) :=
      (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target R.isOpen_Yo
    refine (h1.indicator hO.measurableSet).congr_fun (fun y hy => ?_) hKc.measurableSet
    by_cases hy' : (A.chart j).symm y ∈ R.Yo
    · have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := ⟨hK hy, hy'⟩
      simp [Set.indicator_of_mem hyO, Set.indicator_of_mem hy']
    · have hyO : y ∉ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := fun h => hy' h.2
      simp [Set.indicator_of_notMem hyO, Set.indicator_of_notMem hy']
  · rw [← hstokes]
    exact hM A R Om C₁ th u hf

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem GreenMassStep.full : GreenMassStep.Statement := GreenMassStep.proof

theorem GreenMassReplace.full : GreenMassReplace.Statement := GreenMassReplace.proof

theorem GreenMassError.full : GreenMassError.Statement := GreenMassError.proof

theorem UniformIntegrability.full : UniformIntegrability.Statement :=
  UniformIntegrability.of_greenMass GreenMassStep.full GreenMassReplace.full GreenMassError.full

theorem WeightCocycle.full : WeightCocycle.Statement := WeightCocycle.proof

theorem PolynomialInWeights.full : PolynomialInWeights.Statement := PolynomialInWeights.proof

theorem Convergence.full : Convergence.Statement := Convergence.proof WeightCocycle.full

theorem CoefficientLimit.full : CoefficientLimit.Statement :=
  CoefficientLimit.proof WeightCocycle.full PolynomialInWeights.full

theorem ArgumentConvergenceC2.full : ArgumentConvergenceC2.Statement := ArgumentConvergenceC2.proof

theorem PropertyF.full : PropertyF.Statement := PropertyF.proof GluedLocal.full ArgumentConvergenceC2.full

theorem ListProductMass.full : ListProductMass.Statement := ListProductMass.proof

theorem ListTailLog.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement :=
  ListTailLog.proof hE hM hC hS

theorem TailBound.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : TailBound.Statement :=
  TailBound.of_listTailLog (ListTailLog.of_lemmaE hE hM hC hS)

theorem ListTailLogSmooth.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLogSmooth.Statement :=
  ListTailLogSmooth.proof (ListTailLog.of_lemmaE hE hM hC hS)

theorem ProductBounds.of_listTailLog (h : ListTailLog.Statement) : ProductBounds.Statement :=
  ProductBounds.proof ListProductMass.full (ListTailLogSmooth.proof h)

theorem ProductBounds.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ProductBounds.Statement :=
  ProductBounds.of_listTailLog (ListTailLog.of_lemmaE hE hM hC hS)

theorem SystemIndependence.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : SystemIndependence.Statement :=
  SystemIndependence.of_productBounds (ProductBounds.of_lemmaE hE hM hC hS)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
