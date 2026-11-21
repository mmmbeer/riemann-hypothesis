import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountMonoLattice
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StNmSmallIntoFS
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StFSSmallFinite
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StFSSmallCountBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StSmallFormsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeComplexRadical
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexMinimalPrimesContract
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIndependentModBaseChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSTopPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter

noncomputable section

theorem G6ppB.proof (hBig : MoriwakiBigStatement) (hInj : NmSmallIntoFS.Statement)
    (hFin : FSSmallFinite.Statement) (hCnt : FSSmallCountBound.Statement) : BirationalPullbackPushforwardFormula := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc
  refine (ArithmeticVolumeBig.of_moriwakiBig_only hBig K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc).trans ?_
  obtain ⟨M, k, C₀, hM, hC₀, hf⟩ := hInj K ι Ω y D A har hb hs.1
  obtain ⟨R, hR⟩ := hCnt K ι Ω y D II hII har hb C₀ hC₀
  have hg : Tendsto (fun τ : ℕ => M * (τ + k)) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun τ hτ => le_trans hτ (by nlinarith)⟩

  have hev : ∀ᶠ τ : ℕ in atTop,
      {s : chartLatNm y A.a τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite ∧
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
        R * ((M * (τ + k) : ℕ) : ℝ) ^ (D + 1) := by
    filter_upwards [hg.eventually hR] with τ hτ
    obtain ⟨f, hfi⟩ := hf C₀ le_rfl τ
    have : Finite {σ : chartLat y (fsScaled ι C₀).a (M * (τ + k)) //
        IsSmallH (mCoordIdeal y) y (fsScaled ι C₀) (M * (τ + k)) (σ : Ω)} :=
      (hFin K ι Ω y D har hb C₀ (M * (τ + k))).to_subtype
    have : Finite {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} :=
      Finite.of_injective f hfi
    refine ⟨Set.finite_coe_iff.mp this, le_trans ?_ hτ⟩
    unfold smallSectionCount
    have hcard := Nat.card_le_card_of_injective f hfi
    rcases Nat.eq_zero_or_pos
        (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)}) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)
  unfold arVolP
  simp only [one_mul]
  have hden : ∀ τ : ℕ, 0 ≤ ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := fun τ => by positivity
  refine limsup_le_limsup ?_ ?_ ?_
  · filter_upwards [hev] with τ hτ
    exact div_le_div_of_nonneg_right
      (smallSectionCount_mono_lattice _ τ (chartLat_le_chartLatNm y A.a τ) hτ.1) (hden τ)
  · exact isCoboundedUnder_le_of_le atTop fun τ => div_nonneg (Real.log_natCast_nonneg _) (hden τ)
  · refine isBoundedUnder_of_eventually_le
      (a := |R| * ((M : ℝ) * (1 + k)) ^ (D + 1) * ((D + 1).factorial : ℝ)) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with τ hτ hτ1
    have hτ1' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
    have hF : (0 : ℝ) < (D + 1).factorial := by positivity
    have hkp : (0 : ℝ) < (τ : ℝ) ^ (D + 1) := by positivity
    rw [div_le_iff₀ (by positivity)]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hMk : ((M * (τ + k) : ℕ) : ℝ) ≤ (M : ℝ) * (1 + k) * τ := by
      push_cast
      nlinarith [mul_nonneg hM0 hk0, mul_le_mul_of_nonneg_left hτ1' (mul_nonneg hM0 hk0)]
    calc smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ
        ≤ R * ((M * (τ + k) : ℕ) : ℝ) ^ (D + 1) := hτ.2
      _ ≤ |R| * ((M * (τ + k) : ℕ) : ℝ) ^ (D + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)
      _ ≤ |R| * ((M : ℝ) * (1 + k) * τ) ^ (D + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hMk _) (abs_nonneg R)
      _ = |R| * ((M : ℝ) * (1 + k)) ^ (D + 1) * ((D + 1).factorial : ℝ) *
            ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
          rw [mul_pow]
          field_simp

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded

noncomputable section

set_option linter.unusedSectionVars false

namespace NmSmallIntoFSProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem one_mem_chartLat (y : (Σ k, ι k) → Ω) : (1 : Ω) ∈ chartLat y (fun _ => 1) 0 := by
  intro c _
  simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, Finset.prod_const_one, one_mul]
  exact one_mem _

theorem form_mul_mem_chartLat (y : (Σ k, ι k) → Ω) {n d : ℕ} {s : Ω} (hs : s ∈ chartLat y (fun _ => 1) n)
    {g : MRing ι} (hg : IsMultiHomog g (fun _ => d)) : aeval y g * s ∈ chartLat y (fun _ => 1) (n + d) := by
  intro c hc
  have h1 : s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * 1)) ∈ chartRingZ y c := hs c hc
  have h2 := Conductor.form_mul_invMon_mem y c hg
  rw [← Conductor.prod_zpow_eq_invMon] at h2
  have hk : ∀ k, y ⟨k, c k⟩ ^ (-(((n + d : ℕ) : ℤ) * 1)) =
      y ⟨k, c k⟩ ^ (-((n : ℤ) * 1)) * y ⟨k, c k⟩ ^ (-((d : ℕ) : ℤ)) := fun k => by
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  show aeval y g * s * ∏ k, y ⟨k, c k⟩ ^ (-(((n + d : ℕ) : ℤ) * 1)) ∈ chartRingZ y c
  rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib]
  have e : aeval y g * s * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * 1))) * ∏ k, y ⟨k, c k⟩ ^ (-((d : ℕ) : ℤ))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * 1))) * (aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((d : ℕ) : ℤ))) := by ring
  rw [e]
  exact mul_mem h1 h2

theorem secM_le_chartLat (y : (Σ k, ι k) → Ω) (n : ℕ) : secM y (fun _ => n) ≤ chartLat y (fun _ => 1) n := by
  intro x hx
  replace hx : x ∈ Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g (fun _ => n) ∧ aeval y g = s} := hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    simpa using form_mul_mem_chartLat y (one_mem_chartLat y) hg
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul r a _ ha => exact zsmul_mem ha r

theorem monomial_mul_mem_chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (M : ℕ) (e : K → ℕ)
    (he : ∀ k, (e k : ℤ) = M - a k) (i₀ : ∀ k, ι k) (τ : ℕ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    aeval y (chartMon i₀ e) ^ τ * s ∈ chartLatNm y (fun _ => (M : ℤ)) τ := by
  intro c hc
  have h1 := hs c hc
  have h2 : aeval y (chartMon i₀ e) * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ chartRingZ y c := by
    rw [Conductor.prod_zpow_eq_invMon]
    exact Conductor.form_mul_invMon_mem y c (homog_chartMon i₀ e)
  have h3 : aeval y (chartMon i₀ e) * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ integralClosure (chartRingZ y c) Ω :=
    (integralClosure (chartRingZ y c) Ω).algebraMap_mem ⟨_, h2⟩
  have hk : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * M)) =
      y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) * (y ⟨k, c k⟩ ^ (-(e k : ℤ))) ^ τ := fun k => by
    rw [← zpow_natCast (y ⟨k, c k⟩ ^ (-(e k : ℤ))), ← zpow_mul, ← zpow_add₀ (hc k)]
    congr 1
    linear_combination (τ : ℤ) * he k
  show aeval y (chartMon i₀ e) ^ τ * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * M)) ∈ _
  rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow]
  have e' : aeval y (chartMon i₀ e) ^ τ * s *
      ((∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) * (∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ))) ^ τ) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) *
        (aeval y (chartMon i₀ e) * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ))) ^ τ := by ring
  rw [e']
  exact mul_mem h1 (pow_mem h3 τ)

theorem exists_max_coord (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ c : ∀ k, ι k, ∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖ := by
  have : ∀ k, ∃ j, ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, j⟩‖ := fun k => by
    obtain ⟨i, -⟩ := hz k
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i, Finset.mem_univ _⟩
    exact ⟨j, fun i => hj i (Finset.mem_univ _)⟩
  choose c hc using this
  exact ⟨c, hc⟩

theorem fsH_h_eq (z : (Σ k, ι k) → ℂ) : (fsH ι).h z = ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ := by
  simp [fsH, HermLine.ofMetrics, fsMetric]

theorem coord_le_fs (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    ‖z ⟨k, i⟩‖ ≤ ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ :=
  PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) i

theorem prod_le_fsH_pow (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : ℕ) :
    ∏ k, ‖z ⟨k, c k⟩‖ ^ d ≤ (fsH ι).h z ^ d := by
  rw [fsH_h_eq, ← Finset.prod_pow]
  exact Finset.prod_le_prod (fun k _ => pow_nonneg (norm_nonneg _) _) fun k _ =>
    pow_le_pow_left₀ (norm_nonneg _) (coord_le_fs z k (c k)) d

theorem norm_eval_le_fs {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {G : MRing ι} {d : ℕ}
    (hG : IsMultiHomog G (fun _ => d)) :
    ‖eval z (map (Int.castRingHom ℂ) G)‖ ≤ coeffNorm G * (fsH ι).h z ^ d := by
  obtain ⟨c, hc⟩ := exists_max_coord z hz
  exact (norm_eval_le hc hG).trans (mul_le_mul_of_nonneg_left (prod_le_fsH_pow z c d) (coeffNorm_nonneg G))

theorem mon_mul_h_le (A : HermLine ι) {CA : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      A.h z ≤ CA * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z)
    (M : ℕ) (e : K → ℕ) (he : ∀ k, (e k : ℤ) = M - A.a k) (i₀ : ∀ k, ι k) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z ≤ CA * (fsH ι).h z ^ M := by
  obtain ⟨c, hc⟩ := exists_max_coord z hz
  have hν : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (norm_pos_iff.2 hi) (hc k i)
  have hsup : ∀ k, (maxMetric ℂ (ι k)).ρ (fun i => z ⟨k, i⟩) = ‖z ⟨k, c k⟩‖ := fun k =>
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hc k i)
      (norm_le_pi_norm (fun i => z ⟨k, i⟩) (c k))
  have hA : A.h z ≤ CA * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := by
    have := hCA z hz
    simp only [HermLine.ofMetrics, hsup] at this
    exact this
  have hm : ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ ≤ ∏ k, ‖z ⟨k, c k⟩‖ ^ e k := by
    rw [eval_chartMon, norm_prod]
    exact Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hc k _) _
  have hprod : (∏ k, ‖z ⟨k, c k⟩‖ ^ e k) * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = ∏ k, ‖z ⟨k, c k⟩‖ ^ M := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hν k).ne']
    congr 1
    rw [he k]
    ring
  calc ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z
      ≤ (∏ k, ‖z ⟨k, c k⟩‖ ^ e k) * (CA * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) :=
        mul_le_mul hm hA (A.pos z hz).le (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)
    _ = CA * ∏ k, ‖z ⟨k, c k⟩‖ ^ M := by rw [← hprod]; ring
    _ ≤ CA * (fsH ι).h z ^ M := mul_le_mul_of_nonneg_left (prod_le_fsH_pow z c M) hCA0

end NmSmallIntoFSProof

open NmSmallIntoFSProof in

theorem NmSmallIntoFS.proof : NmSmallIntoFS.Statement := by
  classical
  intro K _ ι _ Ω _ y D A hV hbir hA
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  choose i₀ hi₀ using hy
  obtain ⟨M, hM1, haM⟩ : ∃ M : ℕ, 1 ≤ M ∧ ∀ k, A.a k ≤ M := by
    refine ⟨1 + ∑ k, (A.a k).toNat, by omega, fun k => ?_⟩
    have h1 : (A.a k).toNat ≤ ∑ k, (A.a k).toNat :=
      Finset.single_le_sum (f := fun k => (A.a k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (A.a k)
    omega
  let e : K → ℕ := fun k => (M - A.a k).toNat
  have he : ∀ k, (e k : ℤ) = M - A.a k := fun k => Int.toNat_of_nonneg (by linarith [haM k])
  obtain ⟨k₀, c, hc, hc0, hcond⟩ := Conductor.proof SecEq.proof K ι Ω y (fun _ => M) (fun _ => hM1)
    (fun k => ⟨i₀ k, hi₀ k⟩) hbir
  obtain ⟨CA, hCA1, hCA⟩ := MetricMaxComparison.proof K ι A hA
  let c' := c * chartMon i₀ (fun _ => M)
  have hc' : IsMultiHomog c' (fun _ => (k₀ + 1) * M) :=
    homog_congr (homog_mul hc (homog_chartMon i₀ _)) fun κ => by simp only [Pi.add_apply]; ring
  have hmon0 : ∀ d : K → ℕ, aeval y (chartMon i₀ d) ≠ 0 := fun d => by
    rw [aeval_chartMon]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hi₀ k)
  refine ⟨M, k₀ + 1, max 1 (max CA (coeffNorm c')), hM1, le_max_left _ _, fun C hC τ => ?_⟩
  have hC1 : 1 ≤ C := (le_max_left _ _).trans hC
  have hCA' : CA ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hcn : coeffNorm c' ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  let u := aeval y c' * aeval y (chartMon i₀ e) ^ τ
  have hu : u ≠ 0 := mul_ne_zero (by simp only [c', map_mul]; exact mul_ne_zero hc0 (hmon0 _))
    (pow_ne_zero _ (hmon0 e))
  have hmem : ∀ s ∈ chartLatNm y A.a τ, u * s ∈ chartLat y (fsScaled ι C).a (M * (τ + (k₀ + 1))) := by
    intro s hs
    rw [fsScaled_a]
    have h1 := hcond τ _ (monomial_mul_mem_chartLatNm y A.a M e he i₀ τ hs)
    have h3 := form_mul_mem_chartLat y (secM_le_chartLat y ((τ + k₀) * M) h1) (homog_chartMon i₀ (fun _ => M))
    have e1 : u * s = aeval y (chartMon i₀ fun _ => M) * (aeval y c * (aeval y (chartMon i₀ e) ^ τ * s)) := by
      simp only [u, c', map_mul]
      ring
    have e2 : M * (τ + (k₀ + 1)) = (τ + k₀) * M + M := by ring
    rw [e1, e2]
    exact h3
  have hsmall : ∀ s, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y (fsScaled ι C) (M * (τ + (k₀ + 1))) (u * s) := by
    intro s hs dg dh g h z hg hh hdeg hrep hz
    have key := hs dg (fun κ => (k₀ + 1) * M + τ * e κ + dh κ) g (c' * chartMon i₀ e ^ τ * h) z hg
      (homog_congr (homog_mul (homog_mul hc' (homog_pow (homog_chartMon i₀ e) τ)) hh)
        fun κ => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul])
      (fun κ => by
        have h1 := hdeg κ
        simp only [fsScaled_a] at h1
        push_cast at h1 ⊢
        linear_combination h1 - (τ : ℤ) * he κ)
      (by rw [hrep]; simp only [u, map_mul, map_pow]; ring) hz
    simp only [map_mul, map_pow, norm_mul, norm_pow] at key
    rw [fsScaled_h ι (by linarith) z]
    have hF : 0 ≤ (fsH ι).h z := ((fsH ι).pos z hz.1).le
    have hCF : 0 ≤ C * (fsH ι).h z := mul_nonneg (by linarith) hF
    have b1 : ‖eval z (map (Int.castRingHom ℂ) c')‖ ≤ (C * (fsH ι).h z) ^ ((k₀ + 1) * M) := by
      refine (norm_eval_le_fs hz.1 hc').trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (hcn.trans (le_self_pow₀ hC1 (by positivity))) (pow_nonneg hF _)
    have b2 : ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z ≤ (C * (fsH ι).h z) ^ M := by
      refine (mon_mul_h_le A (by linarith) hCA M e he i₀ hz.1).trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (hCA'.trans (le_self_pow₀ hC1 (by omega))) (pow_nonneg hF _)
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) c')‖ * ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ ^ τ *
            ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := key
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (‖eval z (map (Int.castRingHom ℂ) c')‖ *
            (‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z) ^ τ) := by ring
      _ ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * ((C * (fsH ι).h z) ^ ((k₀ + 1) * M) *
            ((C * (fsH ι).h z) ^ M) ^ τ) := by
        have h0 : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z :=
          mul_nonneg (norm_nonneg _) (A.pos z hz.1).le
        exact mul_le_mul_of_nonneg_left (mul_le_mul b1 (pow_le_pow_left₀ h0 b2 τ) (pow_nonneg h0 _)
          (pow_nonneg hCF _)) (norm_nonneg _)
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (C * (fsH ι).h z) ^ (M * (τ + (k₀ + 1))) := by ring
  refine ⟨fun s => ⟨⟨u * s, hmem s s.1.2⟩, hsmall s s.2⟩, fun s t hst => ?_⟩
  have h1 : u * (s : Ω) = u * (t : Ω) := congrArg (fun x => ((x.1 : chartLat _ _ _) : Ω)) hst
  exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hu h1))

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial

noncomputable section

namespace FSSmallFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem norm_eval_le (c : MRing ι) (k : ℕ) (hc : IsMultiHomog c (fun _ => k)) (z : (Σ κ, ι κ) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) c)‖ ≤
      (∑ μ ∈ c.support, |((c.coeff μ : ℤ) : ℝ)|) * (fsH ι).h z ^ k := by
  classical
  have hH : (fsH ι).h z = ∏ κ, ‖WithLp.toLp 2 (fun i => z ⟨κ, i⟩)‖ := by
    simp [fsH, HermLine.ofMetrics, fsMetric]
  have hmon : ∀ μ ∈ c.support, ‖∏ p, z p ^ μ p‖ ≤ (fsH ι).h z ^ k := by
    intro μ hμ
    rw [hH, norm_prod, Fintype.prod_sigma, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun κ _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun κ _ => ?_
    have hk : ∑ i, μ ⟨κ, i⟩ = k := hc μ hμ κ
    rw [← hk, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have := PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨κ, i⟩)) i
    rwa [PiLp.toLp_apply] at this
  rw [eval_map, eval₂_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ hμ => ?_)
  rw [norm_mul]
  have hcoef : ‖(Int.castRingHom ℂ) (c.coeff μ)‖ = |((c.coeff μ : ℤ) : ℝ)| := by
    simp [Complex.norm_intCast]
  rw [hcoef]
  exact mul_le_mul_of_nonneg_left (hmon μ hμ) (abs_nonneg _)

theorem fsScaled_h_eq (C : ℝ) (z : (Σ κ, ι κ) → ℂ) :
    (fsScaled ι C).h z = Real.exp (Real.log C) * (fsH ι).h z := by
  simp [fsScaled, HermLine.constShift, HermLine.tensor, HermLine.ofWeight, mul_comm]

end FSSmallFinite

open FSSmallFinite in

theorem FSSmallFinite.proof (hS : SmallFormsFinite.Statement) : FSSmallFinite.Statement := by
  classical
  intro K _ ι _ Ω _ y D hV hB C n

  have hy : ∀ κ, ∃ i, y ⟨κ, i⟩ ≠ 0 := by
    intro κ
    obtain ⟨i, hi⟩ := hV.2.1.2.2 κ
    refine ⟨i, fun h0 => hi ?_⟩
    show (X ⟨κ, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  obtain ⟨k, c, hc, hcy, hcond⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.Conductor.proof GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.proof
      K ι Ω y (fun _ => 1) (fun _ => le_rfl) hy hB
  have hc' : IsMultiHomog c (fun _ => k) := fun μ hμ κ => by simpa using hc μ hμ κ
  set e : ℝ := Real.exp (Real.log C) with he
  have he0 : 0 < e := Real.exp_pos _
  set R : ℝ := (∑ μ ∈ c.support, |((c.coeff μ : ℤ) : ℝ)|) * e ^ n with hR
  have hfin := hS K ι Ω y D hV (n + k) R
  refine (hfin.preimage (f := fun σ : chartLat y (fsScaled ι C).a n => aeval y c * (σ : Ω))
    fun σ _ τ _ hστ => Subtype.ext (mul_left_cancel₀ hcy hστ)).subset ?_
  intro σ hσ
  refine ⟨?_, fun g hg hgy z hz => ?_⟩
  ·
    have hσNm : (σ : Ω) ∈ chartLatNm y (fun _ => ((1 : ℕ) : ℤ)) n := by
      have key : ∀ s : Ω, s ∈ chartLat y (fsScaled ι C).a n → s ∈ chartLat y (fun _ => ((1 : ℕ) : ℤ)) n := by
        rw [fsScaled_a]
        intro s hs
        simpa using hs
      have h1 := key σ σ.2
      exact fun c' hc' => isIntegral_algebraMap (R := chartRingZ y c') (A := Ω) (x := ⟨_, h1 c' hc'⟩)
    simpa using hcond n σ hσNm
  ·
    have hdeg : ∀ κ, (((fun _ => n + k) : K → ℕ) κ : ℤ) = ((fun _ => k) : K → ℕ) κ + n * (fsScaled ι C).a κ := by
      intro κ
      rw [fsScaled_a]
      push_cast
      ring
    have h1 := hσ (fun _ => n + k) (fun _ => k) g c z hg hc' hdeg (by rw [hgy, mul_comm]) hz
    have h2 := norm_eval_le c k hc' z
    have hH0 : 0 ≤ (fsH ι).h z := ((fsH ι).pos z hz.1).le
    rw [fsScaled_h_eq, mul_pow] at h1
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) c)‖ * (e ^ n * (fsH ι).h z ^ n) := h1
      _ ≤ ((∑ μ ∈ c.support, |((c.coeff μ : ℤ) : ℝ)|) * (fsH ι).h z ^ k) * (e ^ n * (fsH ι).h z ^ n) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = R * (fsH ι).h z ^ (n + k) := by rw [hR, pow_add]; ring

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial

noncomputable section

theorem SmallFormsFinite.proof : SmallFormsFinite.Statement := by
  intro K _ ι _ Ω _ y D hV m R
  classical
  have hRF : RealFormsOnPoints.Statement := RealFormsOnPoints.proof
    (ComplexFormsOnPoints.proof PrimeComplexRadical.proof ComplexMinimalPrimesContract.proof)
    IndependentModBaseChange.proof

  have : CharZero Ω := charZero_of_inj_zero fun n hn => by
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      show C (n : ℤ) ∈ RingHom.ker (mConeMap y)
      rw [RingHom.mem_ker, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, eq_intCast, Int.cast_natCast,
        ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hV.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  set d : K → ℕ := fun _ => m with hd
  set N : Submodule ℤ Ω := Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s} with hN
  have : Module.Finite ℤ N :=
    Module.Finite.iff_fg.mpr ((Submodule.fg_iff_addSubgroup_fg N).mpr (SectionLatticeFinite.secM_fg y d))

  have hrep : ∀ σ ∈ N, ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = σ := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, SectionLatticeFinite.homog_zero d, map_zero _⟩
    | add x x' _ _ h h' =>
      obtain ⟨g, hg, rfl⟩ := h
      obtain ⟨g', hg', rfl⟩ := h'
      exact ⟨g + g', SectionLatticeFinite.homog_add hg hg', map_add _ _ _⟩
    | smul n x _ h =>
      obtain ⟨g, hg, rfl⟩ := h
      refine ⟨n • g, fun s hs k => hg s (MvPolynomial.support_smul hs) k, map_zsmul _ _ _⟩
  let b := Module.finBasis ℤ N
  set r := Module.finrank ℤ N
  choose g hg hgy using fun i => hrep (b i) (b i).2
  have hsum : ∀ n : Fin r → ℤ, IsMultiHomog (∑ i, n i • g i) d := by
    intro n s hs k
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
    exact hg i s (MvPolynomial.support_smul hi) k
  have hli : LinearIndependent ℤ (fun i => aeval y (g i)) := by
    rw [Fintype.linearIndependent_iff]
    intro n hn
    refine (Fintype.linearIndependent_iff.mp b.linearIndependent) n (Subtype.ext ?_)
    simpa [hgy] using hn

  let G : Fin r → ((Σ k, ι k) → ℂ) → ℂ := fun i z => eval z (map (Int.castRingHom ℂ) (g i))
  let ψ : ((Σ k, ι k) → ℂ) → (Fin r → ℝ) →ₗ[ℝ] ℂ := fun z =>
    ∑ i, (LinearMap.proj i : (Fin r → ℝ) →ₗ[ℝ] ℝ).smulRight (G i z)
  have hψ : ∀ z c, ψ z c = ∑ i, (c i : ℂ) * G i z := by
    intro z c
    simp [ψ, Complex.real_smul]

  obtain ⟨N0, ⟨F0, hF0, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal
    {L : Submodule ℝ (Fin r → ℝ) | ∃ F : Finset ((Σ k, ι k) → ℂ), (↑F ⊆ mcPts (mCoordIdeal y)) ∧
      L = ⨅ z ∈ F, LinearMap.ker (ψ z)} ⟨_, ∅, by simp, rfl⟩
  let Φ : (Fin r → ℝ) →ₗ[ℝ] (F0 → ℂ) := LinearMap.pi fun z => ψ z
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    refine hRF K ι Ω y (D + 1) d r g hV hg hli c fun z hz => ?_
    have hle : (⨅ w ∈ insert z F0, LinearMap.ker (ψ w)) ≤ ⨅ w ∈ F0, LinearMap.ker (ψ w) :=
      le_iInf₂ fun w hw => iInf₂_le w (Finset.mem_insert_of_mem hw)
    have heq := (eq_of_le_of_not_lt hle (hmin _ ⟨insert z F0, by
      simpa [Set.insert_subset_iff] using ⟨hz, hF0⟩, rfl⟩))
    have hc' : c ∈ ⨅ w ∈ F0, LinearMap.ker (ψ w) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro w hw
      exact congrFun (LinearMap.mem_ker.mp hc) ⟨w, hw⟩
    rw [← heq] at hc'
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hc'
    rw [← hψ]
    exact hc' z (Finset.mem_insert_self _ _)
  obtain ⟨Kc, -, hK⟩ := Φ.exists_antilipschitzWith hker
  set B : ℝ := ∑ z ∈ F0, |R * (fsH ι).h z ^ m| with hB
  set T : ℝ := Kc * B

  have hbox : ∀ n : Fin r → ℤ, (∀ z ∈ mcPts (mCoordIdeal y),
      ‖∑ i, (n i : ℂ) * G i z‖ ≤ R * (fsH ι).h z ^ m) → ∀ i, |(n i : ℝ)| ≤ T := by
    intro n hn i
    set c : Fin r → ℝ := fun i => (n i : ℝ)
    have hΦ : ‖Φ c‖ ≤ B := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr fun z => ?_
      have h1 : ‖Φ c z‖ ≤ R * (fsH ι).h z ^ m := by
        have := hn z (hF0 z.2)
        simpa [Φ, hψ, c] using this
      exact h1.trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun z => |R * (fsH ι).h z ^ m|) (fun _ _ => abs_nonneg _) z.2))
    have hc : ‖c‖ ≤ Kc * ‖Φ c‖ := by
      simpa using hK.le_mul_dist c 0
    calc |(n i : ℝ)| = ‖c i‖ := by simp [c]
      _ ≤ ‖c‖ := norm_le_pi_norm c i
      _ ≤ Kc * ‖Φ c‖ := hc
      _ ≤ T := mul_le_mul_of_nonneg_left hΦ Kc.2
  have hfin : (Set.pi Set.univ fun _ : Fin r => Set.Icc (-⌈T⌉) ⌈T⌉).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine (hfin.image fun n => ∑ i, n i • aeval y (g i)).subset ?_
  rintro σ ⟨hσ, hsmall⟩
  set n : Fin r → ℤ := fun i => b.repr ⟨σ, hσ⟩ i
  have hσn : aeval y (∑ i, n i • g i) = σ := by
    rw [map_sum]
    simp_rw [map_zsmul, hgy]
    have := congrArg Subtype.val (b.sum_repr ⟨σ, hσ⟩)
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this
  have hb := hbox n fun z hz => by
    have := hsmall _ (hsum n) hσn z hz
    simpa [G, map_sum, zsmul_eq_mul] using this
  refine ⟨n, fun i _ => ?_, by simpa [map_sum] using hσn⟩
  have := abs_le.mp (hb i)
  constructor
  · have h := Int.le_ceil T
    exact_mod_cast (show (-(⌈T⌉ : ℝ)) ≤ n i by linarith [this.1])
  · have h := Int.le_ceil T
    exact_mod_cast (show (n i : ℝ) ≤ ⌈T⌉ by linarith [this.2])

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial
  Filter Topology

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsH_semipos (P : Ideal (MRing ι)) : IsSemipositiveRel ⊥ P (fsH ι) := by
  have hM : IsSemipositiveRel ⊥ P (constLine (ι := ι) 0) := by
    refine ⟨G5.isSmoothHerm_constLine 0, fun z _ w _ => ?_⟩
    simp [leviForm, constLine, HermLine.ofWeight]
  exact ScaledFSTopPos.semipos_of_h_eq (funext fun z => by simp [HermLine.zcomb])
    (PerturbSemipos.proof K ι ⊥ P _ 0 1 hM le_rfl zero_le_one)

theorem fsScaled_semipos (P : Ideal (MRing ι)) (C : ℝ) : IsSemipositiveRel ⊥ P (fsScaled ι C) :=
  Mono.semipos_constShift (fsH_semipos P) (-Real.log C)

theorem fsScaled_heightsNonneg (P : Ideal (MRing ι)) {C : ℝ} (hC : 1 ≤ C) (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) : HeightsNonneg II P (fsScaled ι C) := by
  classical
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hBa := fsScaled_a ι C
  let e := Fintype.equivFin (∀ k, ι k)
  let w : Fin (Fintype.card (∀ k, ι k)) → MRing ι :=
    fun j => ∏ k, (X ⟨k, e.symm j k⟩ : MRing ι) ^ (fun _ : K => (1 : ℕ)) k
  refine SmallGenHeightsNonneg.proof K ι P (fsScaled ι C) II _ w hII (fsScaled_semipos P C).1
    (fun k => by rw [hBa]; norm_num) (fun j => ?_) (fun Q hQ _ => ?_) (fun j z hz => ?_)
  · have h := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_coordMonomial (e.symm j) (fun _ : K => (1 : ℕ))
    convert h using 1
    funext k
    rw [hBa]
    rfl
  · let c : ∀ k, ι k := fun k => (hQ.2.2 k).choose
    exact ⟨e c, by
      simp only [w, Equiv.symm_apply_apply]
      exact GroundTheory.Heights₂.Heights.Inter.ThmIUnique.coordMonomial_not_mem hQ.1 c
        (fun k => (hQ.2.2 k).choose_spec) _⟩
  · have hpos := (fsH ι).pos z hz.1
    have hlog := ScaledFSTopPos.logNorm_fsH_nonpos (e.symm j) hz.1
    unfold logNorm at hlog
    rw [Real.log_nonpos_iff (div_nonneg (norm_nonneg _) hpos.le), div_le_one hpos] at hlog
    rw [fsScaled_h ι hC0]
    exact hlog.trans (le_mul_of_one_le_left hpos.le hC)

theorem FSSmallCountBound.proof (hHS : MoriwakiHSStatement) : FSSmallCountBound.Statement := by
  intro K _ ι _ Ω _ y D II hII har hb C hC
  set B := fsScaled ι C with hBdef
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  have hsemi : IsSemipositiveRel ⊥ (mCoordIdeal y) B := fsScaled_semipos _ C
  have hT := hHS K ι Ω y D B ⊥ II hII har hb bot_le hsemi
    (Mono.conj_constShift (fsH_isConjInvariantH ι) (-Real.log C))
    (ProjLine.nefOnFibres_of_nonneg _ B.a fun k => by rw [hBdef, fsScaled_a]; norm_num)
    (NefOnGenericOfSemipos.proof K ι _ ⊥ B bot_le hsemi)
    (fsScaled_heightsNonneg _ hC II hII)
  set L := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hL
  refine ⟨(|L| + 1) / F, ?_⟩
  filter_upwards [hT.eventually (gt_mem_nhds (show L < L + 1 by linarith)), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm : (0 : ℝ) < (n : ℝ) ^ (D + 1) / F := by positivity
  rw [div_lt_iff₀ hm] at hn
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) n
      ≤ (L + 1) * ((n : ℝ) ^ (D + 1) / F) := hn.le
    _ ≤ (|L| + 1) * ((n : ℝ) ^ (D + 1) / F) := by gcongr; exact le_abs_self L
    _ = (|L| + 1) / F * (n : ℝ) ^ (D + 1) := by ring

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

end GroundTheory.Heights₂.Heights.ForSecondHalf
end
