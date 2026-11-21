import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
import GroundTheory.AutomorphicForms.DixmierMalliavinProducts
import GroundTheory.AutomorphicForms.DixmierMalliavinLineBounds
import GroundTheory.AutomorphicForms.DixmierMalliavinHaarDensity
import GroundTheory.AutomorphicForms.HeckeAlgebra

section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem contDiff_iteratedDeriv_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) :
    ∀ {Ψ : E × ℝ → F}, ContDiff ℝ ∞ Ψ → ∀ s : ℝ,
      ContDiff ℝ ∞ (fun Y : E => iteratedDeriv p (fun t : ℝ => Ψ (Y, t)) s) := by
  induction p with
  | zero =>
    intro Ψ hΨ s
    simp only [iteratedDeriv_zero]
    exact hΨ.comp (contDiff_id.prodMk contDiff_const)
  | succ p ih =>
    intro Ψ hΨ s
    have hd : ∀ Y : E, deriv (fun t : ℝ => Ψ (Y, t)) = fun t => fderiv ℝ Ψ (Y, t) (0, 1) := by
      intro Y; funext t
      have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (Y, t)) (Y, t) :=
        (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => ((Y, t) : E × ℝ)) (0, 1) t :=
        (hasDerivAt_const t Y).prodMk (hasDerivAt_id t)
      exact (h1.comp_hasDerivAt t h2).deriv
    have hΨ' : ContDiff ℝ ∞ (fun q : E × ℝ => fderiv ℝ Ψ q (0, 1)) :=
      (hΨ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have e : (fun Y : E => iteratedDeriv (p + 1) (fun t : ℝ => Ψ (Y, t)) s) =
        fun Y => iteratedDeriv p (fun t : ℝ => fderiv ℝ Ψ (Y, t) (0, 1)) s := by
      funext Y; rw [iteratedDeriv_succ', hd Y]
    rw [e]; exact ih hΨ' s

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

noncomputable def dirDeriv (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) : ℂ :=
  iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) 0

theorem iteratedDeriv_comp_expG_mul (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) (s : ℝ) :
    iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) s =
      h.dirDeriv X p f (h.expG (s • X) * x) := by
  have e := congrFun (iteratedDeriv_comp_add_const p (fun t : ℝ => f (h.expG (t • X) * x)) s) 0
  simp only [zero_add] at e
  rw [← e, dirDeriv]
  congr 1
  funext u
  rw [h.expG_add_smul, mul_assoc]

theorem contMDiff_expG_smul_mul (X : 𝔤) (x : G) :
    letI := h.chartedSpace; ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔤) ∞ (fun t : ℝ => h.expG (t • X) * x) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  exact (h.contMDiff_expG_comp (contDiff_id.smul contDiff_const)).mul contMDiff_const

theorem contDiff_comp_expG_smul_mul {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (x : G) :
    ContDiff ℝ ∞ (fun t : ℝ => f (h.expG (t • X) * x)) := by
  let := h.chartedSpace
  exact (hf.comp (h.contMDiff_expG_smul_mul X x)).contDiff

theorem contDiff_comp_expG_smul_mul_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (g : G) :
    ContDiff ℝ ∞ (fun q : 𝔤 × ℝ => f (h.expG (q.2 • X) * (g * h.expG q.1))) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × ℝ) 𝓘(ℝ, 𝔤) ∞
      (fun q : 𝔤 × ℝ => h.expG (q.2 • X) * (g * h.expG q.1)) :=
    (h.contMDiff_expG_comp (contDiff_snd.smul contDiff_const)).mul
      (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_fst))
  exact (hf.comp hm).contDiff

theorem dirDeriv_eq_zero_of_notMem {f : G → ℂ} (X : 𝔤) (p : ℕ) {x : G}
    (hx : x ∉ tsupport f) : h.dirDeriv X p f x = 0 := by
  have hc : Continuous (fun t : ℝ => h.expG (t • X) * x) :=
    (h.continuous_expG.comp (continuous_id.smul continuous_const)).mul continuous_const
  have h0 : h.expG ((0 : ℝ) • X) * x = x := by
    simp only [zero_smul]; rw [h.expG_zero, one_mul]
  have hev : (fun t : ℝ => f (h.expG (t • X) * x)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have := hc.continuousAt (x := 0)
    rw [ContinuousAt] at this
    simp only [h0] at this
    exact this.eventually (notMem_tsupport_iff_eventuallyEq.1 hx)
  rw [dirDeriv, hev.iteratedDeriv_eq]
  simp

theorem contDiff_dirDeriv_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (p : ℕ) (g : G) :
    ContDiff ℝ ∞ (fun Y : 𝔤 => h.dirDeriv X p f (g * h.expG Y)) :=
  contDiff_iteratedDeriv_snd p (h.contDiff_comp_expG_smul_mul_mul_expG hf X g) 0

theorem mem_chart_source_self (g : G) : g ∈ (h.chart g).source := by
  let := h.chartedSpace
  exact mem_chart_source 𝔤 g

theorem chart_symm_chart {g x : G} (hx : x ∈ (h.chart g).source) :
    g * h.expG (h.chart g x) = x :=
  (h.chart g).left_inv hx

theorem exists_bound_dirDeriv {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) :
    ∃ M : ℕ → ℝ, (∀ p x, ‖h.dirDeriv X p f x‖ ≤ M p) ∧
      ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) →
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞
          (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x)) ∧
        HasCompactSupport (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfc
  let U : G → Set G := fun g => (h.chart g).source ∩ (h.chart g) ⁻¹' Metric.ball 0 1
  have hU : ∀ g, IsOpen (U g) := fun g =>
    (h.chart g).isOpen_inter_preimage Metric.isOpen_ball
  have hgU : ∀ g, g ∈ U g := fun g =>
    ⟨h.mem_chart_source_self g, by
      show h.chart g g ∈ Metric.ball 0 1
      rw [h.chart_self]; exact Metric.mem_ball_self one_pos⟩
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover U (fun g _ => (hU g).mem_nhds (hgU g))
  let β : ContDiffBump (0 : 𝔤) := ⟨1, 2, one_pos, one_lt_two⟩
  let Φ : G → ℕ → 𝔤 → ℂ := fun g p Y => (β Y : ℂ) * h.dirDeriv X p f (g * h.expG Y)
  have hΦ : ∀ g p, ContDiff ℝ ∞ (Φ g p) := fun g p =>
    (Complex.ofRealCLM.contDiff.comp β.contDiff).mul (h.contDiff_dirDeriv_mul_expG hf X p g)
  have hΦc : ∀ g p, HasCompactSupport (Φ g p) := fun g p =>
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hS : ∀ g k p, ∃ C, ∀ Y, ‖iteratedFDeriv ℝ k (Φ g p) Y‖ ≤ C := fun g k p =>
    ((hΦ g p).continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((hΦc g p).iteratedFDeriv k)
  choose S hS using hS
  have hS0 : ∀ g k p, 0 ≤ S g k p := fun g k p => (norm_nonneg _).trans (hS g k p 0)
  let M : ℕ → ℝ := fun p => ∑ g ∈ t, ∑ k ∈ Finset.range (p + 1), S g k p
  have hM0 : ∀ p, 0 ≤ M p := fun p =>
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun k _ => hS0 g k p
  have hSM : ∀ p, ∀ g ∈ t, ∀ k ≤ p, S g k p ≤ M p := by
    intro p g hg k hk
    calc S g k p ≤ ∑ k ∈ Finset.range (p + 1), S g k p :=
          Finset.single_le_sum (fun k _ => hS0 g k p) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
      _ ≤ M p := Finset.single_le_sum (f := fun g => ∑ k ∈ Finset.range (p + 1), S g k p)
          (fun g _ => Finset.sum_nonneg fun k _ => hS0 g k p) hg

  have hloc : ∀ g p x, x ∈ U g → h.dirDeriv X p f x = Φ g p (h.chart g x) := by
    intro g p x hx
    have hb : β (h.chart g x) = 1 :=
      β.one_of_mem_closedBall (Metric.ball_subset_closedBall hx.2)
    simp only [Φ, hb, Complex.ofReal_one, one_mul, h.chart_symm_chart hx.1]
  have hzero : ∀ p x, x ∉ K → h.dirDeriv X p f x = 0 := fun p x hx =>
    h.dirDeriv_eq_zero_of_notMem X p hx
  refine ⟨M, ?_, ?_⟩
  · intro p x
    by_cases hx : x ∈ K
    · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (htK hx)
      rw [hloc g p x hxg]
      calc ‖Φ g p (h.chart g x)‖ = ‖iteratedFDeriv ℝ 0 (Φ g p) (h.chart g x)‖ := by
            rw [norm_iteratedFDeriv_zero]
        _ ≤ S g 0 p := hS g 0 p _
        _ ≤ M p := hSM p g hg 0 (Nat.zero_le p)
    · rw [hzero p x hx, norm_zero]; exact hM0 p
  intro c hc

  let F : G → 𝔤 → ℂ := fun g Y => ∑' p, (c p) • Φ g p Y
  have hF : ∀ g ∈ t, ContDiff ℝ ∞ (F g) := by
    intro g hg
    refine contDiff_tsum (N := ⊤) (v := fun k p => |c p| * S g k p)
      (fun p => (hΦ g p).const_smul (c p)) ?_ ?_
    · intro k _
      rw [← summable_nat_add_iff k]
      refine Summable.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (hS0 g k _))
        (fun p => mul_le_mul_of_nonneg_left (hSM (p + k) g hg k (Nat.le_add_left k p))
          (abs_nonneg _)) ?_
      exact (summable_nat_add_iff k).2 hc
    · intro k p Y _
      rw [iteratedFDeriv_const_smul_apply' ((hΦ g p).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hS g k p Y) (abs_nonneg _)
  have hsupp : ∀ x, x ∉ K → ∑' p, (c p : ℂ) * h.dirDeriv X p f x = 0 := by
    intro x hx; simp [hzero _ x hx]
  refine ⟨?_, HasCompactSupport.intro hK hsupp⟩
  intro x
  by_cases hx : x ∈ K
  · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (htK hx)
    have hev : (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) =ᶠ[𝓝 x]
        fun x => F g (chartAt 𝔤 g x) := by
      filter_upwards [(hU g).mem_nhds hxg] with x' hx'
      show _ = F g (h.chart g x')
      simp only [F, hloc g _ x' hx', Complex.real_smul]
    have hch : ContMDiffAt 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔤) ∞ (chartAt 𝔤 g) x := by
      have := contMDiffAt_extChartAt' (I := 𝓘(ℝ, 𝔤)) (n := ∞) (x := g) hxg.1
      simpa [extChartAt] using this
    exact (((hF g hg).contMDiff.contMDiffAt).comp x hch).congr_of_eventuallyEq hev
  · have hev : (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with x' hx'
      exact hsupp x' hx'
    exact contMDiffAt_const.congr_of_eventuallyEq hev

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

section
namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff

namespace WeakLimit

theorem integral_fourier_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hf hg)

theorem integral_fourierInv_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq_fourier_comp_neg, integral_fourier_mul_eq hf.comp_neg hg,
    ← integral_neg_eq_self (fun x => f x * 𝓕⁻ g x)]
  congr 1; funext x
  simp [Real.fourierInv_eq_fourier_neg]

theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

theorem exists_smooth_near (a b : ℝ) {ψ : ℝ → ℂ} (hψ : Continuous ψ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ' : ℝ → ℂ, ContDiff ℝ ∞ ψ' ∧ HasCompactSupport ψ' ∧ ∀ t ∈ Icc a b, ‖ψ t - ψ' t‖ ≤ η := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).re)
    (Complex.continuous_re.comp hψ).continuousOn (η / 2) (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).im)
    (Complex.continuous_im.comp hψ).continuousOn (η / 2) (by positivity)
  have hpd : ∀ r : Polynomial ℝ, ContDiff ℝ ∞ (fun t : ℝ => r.eval t) := fun r => by
    simpa [Polynomial.coe_aeval_eq_eval] using r.contDiff_aeval (𝕜 := ℝ) ∞
  let χ : ContDiffBump ((a + b) / 2) := ⟨|b - a| + 1, |b - a| + 2, by positivity, by linarith⟩
  refine ⟨fun t => (χ t : ℂ) * (((p.eval t : ℝ) : ℂ) + ((q.eval t : ℝ) : ℂ) * Complex.I), ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul
      ((Complex.ofRealCLM.contDiff.comp (hpd p)).add
        ((Complex.ofRealCLM.contDiff.comp (hpd q)).mul contDiff_const))
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro t ht
    have hχ : χ t = 1 := by
      apply χ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq]
      have := ht.1; have := ht.2
      rw [abs_le]; constructor <;> cases abs_cases (b - a) <;> linarith
    show ‖ψ t - (χ t : ℂ) * _‖ ≤ η
    rw [hχ, Complex.ofReal_one, one_mul]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h1 := hp t ht
    have h2 := hq t ht
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add]
    rw [abs_sub_comm] at h1 h2
    linarith

end WeakLimit

theorem exists_smooth_weak_limit {K : ℕ → ℝ → ℝ} {a b : ℝ} (hKi : ∀ N, Integrable (K N))
    (hK0 : ∀ N t, 0 ≤ K N t) (hK1 : ∀ N, ∫ t, K N t ≤ 1)
    (hKs : ∀ N, Function.support (K N) ⊆ Icc a b)
    (hconv : ∀ ξ : ℝ, ∃ l : ℂ, Tendsto (fun N => 𝓕 (fun t => (K N t : ℂ)) ξ) atTop (𝓝 l))
    (hdecay : ∀ m : ℕ, ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
      ‖𝓕 (fun t => (K N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ))) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ tsupport g ⊆ Icc a b ∧
      ∀ ψ : ℝ → ℂ, Continuous ψ →
        Tendsto (fun N => ∫ t, ψ t * K N t) atTop (𝓝 (∫ t, ψ t * g t)) := by
  set Kc : ℕ → ℝ → ℂ := fun N t => (K N t : ℂ) with hKc
  have hKci : ∀ N, Integrable (Kc N) := fun N => (hKi N).ofReal
  have hKn : ∀ N ξ, ‖𝓕 (Kc N) ξ‖ ≤ 1 := by
    intro N ξ
    refine (WeakLimit.norm_fourier_le _ ξ).trans ?_
    simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N _)]
    exact hK1 N
  choose Φ hΦ using hconv
  have hΦd : ∀ m : ℕ, ∃ C, ∀ ξ, ‖Φ ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ)) := by
    intro m
    obtain ⟨C, N₀, hC⟩ := hdecay m
    exact ⟨C, fun ξ => le_of_tendsto ((hΦ ξ).norm) (eventually_atTop.2 ⟨N₀, fun N hN => hC N hN ξ⟩)⟩
  have hΦm : AEStronglyMeasurable Φ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable)
      (ae_of_all _ hΦ)
  have hΦint : ∀ n : ℕ, Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖Φ ξ‖) := by
    intro n
    obtain ⟨C, hC⟩ := hΦd (n + 2)
    have hI : Integrable (fun ξ : ℝ => C * (1 + ‖ξ‖) ^ (-(2 : ℝ))) :=
      (integrable_one_add_norm (by norm_num)).const_mul C
    refine hI.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul hΦm.norm)
      (ae_of_all _ fun ξ => ?_)
    have h1 : 0 < 1 + |ξ| := by positivity
    rw [norm_mul, norm_pow, norm_norm, norm_norm, Real.norm_eq_abs]
    calc |ξ| ^ n * ‖Φ ξ‖ ≤ (1 + |ξ|) ^ n * (C * (1 + |ξ|) ^ (-((n + 2 : ℕ) : ℝ))) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (by linarith) n) (hC ξ) (norm_nonneg _)
            (by positivity)
      _ = C * (1 + |ξ|) ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add h1]
          congr 2; push_cast; ring
  have hΦi : Integrable Φ := (integrable_norm_iff hΦm).1 (by simpa using hΦint 0)
  set g : ℝ → ℂ := 𝓕⁻ Φ with hgdef
  have hg : ContDiff ℝ ∞ g := by
    rw [hgdef, Real.fourierInv_eq_fourier_comp_neg]
    exact Real.contDiff_fourier fun n _ => by simpa using (hΦint n).comp_neg

  have hsmooth : ∀ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Tendsto (fun N => ∫ t, ψ t * Kc N t) atTop (𝓝 (∫ t, ψ t * g t)) := by
    intro ψ hψ hψc
    let ψS := hψc.toSchwartzMap hψ
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hθi : Integrable (𝓕⁻ ψ) := by
      have := (𝓕⁻ ψS).integrable (μ := volume)
      rwa [SchwartzMap.fourierInv_coe] at this
    have hFψ : Integrable (𝓕 ψ) := by
      have := (𝓕 ψS).integrable (μ := volume)
      rwa [SchwartzMap.fourier_coe] at this
    have hinv : 𝓕 (𝓕⁻ ψ) = ψ := hψ.continuous.fourier_fourierInv_eq hψi hFψ
    have e1 : ∀ N, ∫ t, ψ t * Kc N t = ∫ ξ, 𝓕⁻ ψ ξ * 𝓕 (Kc N) ξ := by
      intro N
      conv_lhs => rw [← hinv]
      exact WeakLimit.integral_fourier_mul_eq hθi (hKci N)
    have e2 : ∫ t, ψ t * g t = ∫ ξ, 𝓕⁻ ψ ξ * Φ ξ :=
      (WeakLimit.integral_fourierInv_mul_eq hψi hΦi).symm
    simp_rw [e1, e2]
    refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕⁻ ψ ξ‖) (fun N => ?_)
      hθi.norm (fun N => ae_of_all _ fun ξ => ?_) (ae_of_all _ fun ξ => (hΦ ξ).const_mul _)
    · exact hθi.aestronglyMeasurable.mul
        (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hKn N ξ)

  have hgi : LocallyIntegrable g := hg.continuous.locallyIntegrable
  have hsupp : Function.support g ⊆ Icc a b := by
    have hae : ∀ᵐ x, x ∈ (Icc a b)ᶜ → g x = 0 := by
      refine isClosed_Icc.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hgi.locallyIntegrableOn _) fun φ hφ hφc hφs => ?_
      have hlim := hsmooth (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ)
        (hφc.comp_left Complex.ofReal_zero)
      have h0 : ∀ N, ∫ t, (φ t : ℂ) * Kc N t = 0 := by
        intro N
        refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
        by_cases ht : t ∈ Icc a b
        · have : φ t = 0 := image_eq_zero_of_notMem_tsupport fun h' => hφs h' ht
          simp [this]
        · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
          simp [Kc, this]
      simp_rw [h0] at hlim
      simp_rw [Complex.real_smul]
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    intro x hx
    by_contra hxI
    have hopen : IsOpen ((Icc a b)ᶜ ∩ Function.support g) :=
      isClosed_Icc.isOpen_compl.inter hg.continuous.isOpen_support
    have hnull : volume ((Icc a b)ᶜ ∩ Function.support g) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      exact hae.mono fun y hy hy' => hy'.2 (hy hy'.1)
    exact (hopen.measure_ne_zero volume ⟨x, hxI, hx⟩) hnull
  refine ⟨g, hg, closure_minimal hsupp isClosed_Icc, fun ψ hψ => ?_⟩
  have hgc : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) (closure_minimal hsupp isClosed_Icc)
  have hIK : ∀ φ : ℝ → ℂ, Continuous φ → ∀ N, Integrable (fun t => φ t * Kc N t) := by
    intro φ hφ N
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ.continuousOn
    refine ((hKi N).const_mul B).mono' (hφ.aestronglyMeasurable.mul (hKci N).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ Icc a b
    · rw [norm_mul]
      simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]
      exact mul_le_mul_of_nonneg_right (hB t ht) (hK0 N t)
    · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
      simp [Kc, this]
  have hIg : ∀ φ : ℝ → ℂ, Continuous φ → Integrable (fun t => φ t * g t) := fun φ hφ =>
    (hφ.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  set L := ∫ t, ‖g t‖ with hLdef
  have hL : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set η := δ / (4 * (L + 2)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ψ', hψ', hψ'c, hψψ'⟩ := WeakLimit.exists_smooth_near a b hψ hηpos
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hsmooth ψ' hψ' hψ'c) (δ / 2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hdiffK : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ ≤ η := by
    rw [← integral_sub (hIK ψ hψ N) (hIK ψ' hψ'.continuous N)]
    refine (norm_integral_le_of_norm_le ((hKi N).const_mul η) (ae_of_all _ fun t => ?_)).trans ?_
    · rw [← sub_mul, norm_mul]
      by_cases ht : t ∈ Icc a b
      · simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]
        exact mul_le_mul_of_nonneg_right (hψψ' t ht) (hK0 N t)
      · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
        simp [Kc, this]
    · rw [integral_const_mul]
      exact mul_le_of_le_one_right hηpos.le (hK1 N)
  have hdiffg : ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ ≤ η * L := by
    rw [← integral_sub (hIg ψ' hψ'.continuous) (hIg ψ hψ), hLdef, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hg.continuous.norm.integrable_of_hasCompactSupport hgc.norm).const_mul η) (ae_of_all _ fun t => ?_)
    rw [← sub_mul, norm_mul]
    by_cases ht : t ∈ Icc a b
    · rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_right (hψψ' t ht) (norm_nonneg _)
    · have : g t = 0 := Function.notMem_support.1 fun h' => ht (hsupp h')
      simp [this]
  have hmid : dist (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t) < δ / 2 := hN₀ N hN
  rw [dist_eq_norm] at hmid ⊢
  have h3 : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ ≤
      ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ +
        ‖(∫ t, ψ' t * Kc N t) - ∫ t, ψ' t * g t‖ + ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by
      linarith [norm_sub_le_norm_sub_add_norm_sub (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t)
        (∫ t, ψ t * g t)])
  have h4 : η + η * L < δ / 2 := by
    have hpos : 0 < 4 * (L + 2) := by positivity
    have h5 : η * (4 * (L + 2)) = δ := by rw [hη]; field_simp
    nlinarith [mul_nonneg hηpos.le hL]
  show ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ < δ
  linarith

end GroundTheory.Automorphic
end

section
namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform

set_option linter.unusedSectionVars false

noncomputable section

namespace LineKernel

def radii (ε : ℝ) (j : ℕ) : ℝ := ε / 2 ^ (j + 3)

theorem radii_pos {ε : ℝ} (hε : 0 < ε) (j : ℕ) : 0 < radii ε j := by unfold radii; positivity

theorem Rs_radii_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) : Rs (radii ε) n ≤ ε / 2 := by
  have e : ∀ j, 2 * radii ε j = ε / 4 * (1 / 2) ^ j := by
    intro j; unfold radii; rw [pow_add, one_div_pow]; field_simp; norm_num
  unfold Rs
  simp_rw [e, ← Finset.mul_sum]
  have := sum_geometric_two_le (n + 1)
  nlinarith

def weight (M : ℕ → ℝ) (p : ℕ) : ℝ := if p = 0 then 1 else (1 / 2) ^ p / max 1 |M p|

theorem weight_pos (M : ℕ → ℝ) (p : ℕ) : 0 < weight M p := by
  unfold weight; split_ifs
  · exact one_pos
  · exact div_pos (by positivity) (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem weight_le_one (M : ℕ → ℝ) (p : ℕ) : weight M p ≤ 1 := by
  unfold weight; split_ifs
  · exact le_rfl
  · rw [div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]
    exact (pow_le_one₀ (by norm_num) (by norm_num)).trans (le_max_left _ _)

theorem weight_mul_abs_le (M : ℕ → ℝ) (p : ℕ) :
    weight M p * |M p| ≤ (1 / 2) ^ p * max 1 |M 0| := by
  unfold weight; split_ifs with h
  · subst h; simp
  · have hm : 0 < max 1 |M p| := lt_of_lt_of_le one_pos (le_max_left _ _)
    calc (1 / 2) ^ p / max 1 |M p| * |M p| ≤ (1 / 2) ^ p := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hm]
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ ≤ (1 / 2) ^ p * max 1 |M 0| := le_mul_of_one_le_right (by positivity) (le_max_left _ _)

def Good (M : ℕ → ℝ) (ε : ℝ) (j : ℕ) (x : ℝ) : Prop :=
  0 < x ∧ (∀ p ∈ Finset.range (j + 2), 1 ≤ p →
      x⁻¹ * weight M (p - 1) ≤ (1 / 2) ^ (j + 1) * weight M p) ∧
    (∀ q ∈ Finset.range (2 * j + 3), ∀ t,
      ‖iteratedDeriv q (rem x (radii ε j)) t‖ ≤ (1 / 2) ^ j / (j + 2)) ∧
    exp (-x * radii ε j) ≤ (1 / 2) ^ j

theorem eventually_good (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ x in atTop, Good M ε j x := by
  have hr := radii_pos hε j
  refine (eventually_gt_atTop 0).and (((eventually_all_finset _).2 fun p _ => ?_).and
    (((eventually_all_finset _).2 fun q _ => ?_).and ?_))
  · have hc : 0 < (1 / 2 : ℝ) ^ (j + 1) * weight M p := by
      have := weight_pos M p; positivity
    filter_upwards [eventually_ge_atTop (weight M (p - 1) / ((1 / 2) ^ (j + 1) * weight M p)),
      eventually_gt_atTop 0] with x hx hx0 _
    rw [inv_mul_le_iff₀ hx0]
    rw [div_le_iff₀ hc] at hx; linarith
  · exact eventually_norm_iteratedDeriv_rem_le hr q (by positivity)
  · have ht : Tendsto (fun x : ℝ => exp (-x * radii ε j)) atTop (𝓝 0) := by
      have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hr)
      refine this.congr fun x => ?_
      simp [neg_mul]
    exact ht.eventually (ge_mem_nhds (by positivity))

theorem integral_norm_le_of_support {f : ℝ → ℂ} (hf : Continuous f) {c D : ℝ} (hc : 0 ≤ c)
    (hs : support f ⊆ Icc 0 c) (hD : ∀ t ∈ Icc 0 c, ‖f t‖ ≤ D) : ∫ t, ‖f t‖ ≤ D * c := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc 0 c) fun t ht => by
    have : f t = 0 := by by_contra h; exact ht (hs h)
    simp [this]]
  calc ∫ t in Icc 0 c, ‖f t‖ ≤ ∫ t in Icc 0 c, D :=
        setIntegral_mono_on hf.norm.integrableOn_Icc (integrableOn_const (by simp) (by simp))
          measurableSet_Icc hD
    _ = D * c := by simp [hc, mul_comm]

theorem integrable_mul_of_support {φ K : ℝ → ℂ} (hφ : Continuous φ) (hK : Integrable K) {c : ℝ}
    (hs : support K ⊆ Icc 0 c) : Integrable fun u => φ u * K u := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 c) hφ.continuousOn
  refine Integrable.mono' (hK.norm.const_mul B) (hφ.aestronglyMeasurable.mul hK.aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  by_cases hu : K u = 0
  · simp [hu]
  · exact mul_le_mul_of_nonneg_right (hB u (hs hu)) (norm_nonneg _)

section Sequence

variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg

theorem coef_le_weight (n p : ℕ) : coef a n p ≤ weight M p := by
  refine coef_le_of (fun j => (hg j).1) (by simp [weight]) (fun p => (weight_pos M p).le)
    (fun n p hp hpn => (hg n).2.1 p (Finset.mem_range.2 (by omega)) hp) n p

theorem norm_iteratedDeriv_ρ_succ_le_half_pow (n k : ℕ) (hk : k ≤ n + 1) (t : ℝ) :
    ‖iteratedDeriv k (ρ a (radii ε) (n + 1)) t‖ ≤ (1 / 2) ^ (n + 1) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hS := fun q => norm_iteratedDeriv_rem_le (hr (n + 1)) q
  choose S hS0 hS using hS
  set δ : ℝ := (1 / 2) ^ (n + 1) / ((n + 1 : ℕ) + 2 : ℝ) with hδ
  set B : ℕ → ℝ := fun q => if q < 2 * (n + 1) + 3 then δ else
    2 ^ q * (1 + a (n + 1)) ^ q * exp (-a (n + 1) * radii ε (n + 1)) * S q with hB
  have hBq : ∀ q t, ‖iteratedDeriv q (rem (a (n + 1)) (radii ε (n + 1))) t‖ ≤ B q := by
    intro q t
    simp only [hB]
    split_ifs with hq
    · exact (hg (n + 1)).2.2.1 q (Finset.mem_range.2 hq) t
    · exact hS q (a (n + 1)) (ha _).le t
  refine (norm_iteratedDeriv_ρ_succ_le ha hr n k hBq t).trans ?_
  have h1 : ∀ p ∈ Finset.range (n + 2), coef a (n + 1) p * B (p + k) ≤ δ := by
    intro p hp
    have hp' := Finset.mem_range.1 hp
    have hB' : B (p + k) = δ := by simp only [hB]; rw [if_pos (by omega)]
    rw [hB']
    have hδ0 : 0 ≤ δ := by positivity
    calc coef a (n + 1) p * δ ≤ 1 * δ :=
          mul_le_mul_of_nonneg_right ((coef_le_weight hε hg _ _).trans (weight_le_one M p)) hδ0
      _ = δ := one_mul δ
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hδ]
  have : ((n + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) + 2 : ℝ) := by push_cast; linarith
  rw [mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ (n + 1) := by positivity
  nlinarith

theorem exists_bound_iteratedDeriv_ρ (k j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv k (ρ a (radii ε) j) t‖ ≤ C := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hc : HasCompactSupport (ρ a (radii ε) j) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_ρ_subset ha hr j)
  obtain ⟨C, hC⟩ := (hasCompactSupport_iteratedDeriv hc k).exists_bound_of_continuous
    ((contDiff_ρ ha hr j).continuous_iteratedDeriv k (by exact_mod_cast le_top))
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

def majorant (k j : ℕ) : ℝ :=
  (1 / 2) ^ j + if j ≤ k then (exists_bound_iteratedDeriv_ρ hε hg k j).choose else 0

theorem summable_majorant (k : ℕ) : Summable (majorant hε hg k) := by
  refine (summable_geometric_two).add (summable_of_ne_finset_zero (s := Finset.range (k + 1))
    fun j hj => ?_)
  rw [if_neg]; rw [Finset.mem_range] at hj; omega

theorem norm_iteratedDeriv_ρ_le_majorant (k j : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (ρ a (radii ε) j) t‖ ≤ majorant hε hg k j := by
  have hC := (exists_bound_iteratedDeriv_ρ hε hg k j).choose_spec
  unfold majorant
  split_ifs with hjk
  · linarith [hC.2 t, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j]
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have := norm_iteratedDeriv_ρ_succ_le_half_pow hε hg n k (by omega) t
    linarith

def remSum (t : ℝ) : ℂ := ∑' j, ρ a (radii ε) j t

theorem contDiff_remSum : ContDiff ℝ ∞ (remSum (ε := ε) (a := a)) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  refine contDiff_tsum (fun j => contDiff_ρ ha hr j) (fun k _ => summable_majorant hε hg k)
    fun k j t _ => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedDeriv_ρ_le_majorant hε hg k j t

theorem summable_ρ (t : ℝ) : Summable fun j => ρ a (radii ε) j t :=
  Summable.of_norm_bounded (summable_majorant hε hg 0) fun j => by
    simpa using norm_iteratedDeriv_ρ_le_majorant hε hg 0 j t

theorem support_remSum_subset : support (remSum (ε := ε) (a := a)) ⊆ Icc 0 (ε / 2) := by
  intro t ht
  by_contra h
  apply ht
  unfold remSum
  refine (tsum_congr fun j => ?_).trans tsum_zero
  by_contra hj
  have h1 := support_ρ_subset (fun j => (hg j).1) (radii_pos hε) j hj
  exact h ⟨h1.1, h1.2.trans (Rs_radii_le hε j)⟩

theorem hasSum_integral_remSum {F : ℝ → ℂ} (hF : Continuous F) {B : ℝ}
    (hB : ∀ t ∈ Icc (-ε) ε, ‖F t‖ ≤ B) :
    HasSum (fun j => ∫ t, F t * ρ a (radii ε) j t) (∫ t, F t * remSum (ε := ε) (a := a) t) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hint : ∀ j, Integrable fun t => F t * ρ a (radii ε) j t := fun j =>
    (hF.mul (contDiff_ρ ha hr j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_ρ_subset ha hr j)).mul_left
  have hbound : ∀ j, ∫ t, ‖F t * ρ a (radii ε) j t‖ ≤ (B * majorant hε hg 0 j) * (ε / 2) := by
    intro j
    refine integral_norm_le_of_support (hF.mul (contDiff_ρ ha hr j).continuous) (by positivity)
      ?_ ?_
    · intro t ht
      have h1 : t ∈ support (ρ a (radii ε) j) := fun h => ht (by simp [h])
      have h2 := support_ρ_subset ha hr j h1
      exact ⟨h2.1, h2.2.trans (Rs_radii_le hε j)⟩
    · intro t ht
      rw [Pi.mul_apply, norm_mul]
      have h1 := hB t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 : ‖ρ a (radii ε) j t‖ ≤ majorant hε hg 0 j := by
        simpa using norm_iteratedDeriv_ρ_le_majorant hε hg 0 j t
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hsum : Summable fun j => ∫ t, ‖F t * ρ a (radii ε) j t‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _) hbound
      (((summable_majorant hε hg 0).mul_left B).mul_right (ε / 2))
  have := hasSum_integral_of_summable_integral_norm hint hsum
  have e : ∫ t, F t * remSum (ε := ε) (a := a) t = ∫ t, ∑' j, F t * ρ a (radii ε) j t := by
    congr 1; funext t; rw [remSum, tsum_mul_left]
  rw [e]; exact this

end Sequence

theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
  have h1 : 1 + x ≤ 2 * max 1 x := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 x) ^ m ≤ 1 + x ^ m := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg hx m]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx m]
  calc (1 + x) ^ m ≤ (2 * max 1 x) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    _ = 2 ^ m * (max 1 x) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (1 + x ^ m) := mul_le_mul_of_nonneg_left h2 (by positivity)

section Limit

variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg

theorem tendsto_fourier_Kc (ξ : ℝ) : ∃ l : ℂ,
    Tendsto (fun N => 𝓕 (fun t => (Kc a (radii ε) N t : ℂ)) ξ) atTop (𝓝 l) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hd : ∀ N, dist (𝓕 (KC a (radii ε) N) ξ) (𝓕 (KC a (radii ε) N.succ) ξ) ≤
      4 * π * |ξ| * (ε / 16) * (1 / 2) ^ N + (1 / 2) ^ (N + 1) := by
    intro N
    rw [dist_comm, dist_eq_norm]
    refine (norm_fourier_KC_succ_sub_le ha hr N ξ).trans (add_le_add (le_of_eq ?_) ?_)
    · unfold radii; rw [pow_add, pow_add, one_div_pow]; field_simp; ring
    · exact (hg (N + 1)).2.2.2
  have hs : Summable fun N : ℕ => 4 * π * |ξ| * (ε / 16) * (1 / 2 : ℝ) ^ N + (1 / 2) ^ (N + 1) :=
    (summable_geometric_two.mul_left _).add (summable_geometric_two.comp_injective
      (add_left_injective 1))
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable _ hd hs)

theorem decay_fourier_Kc (m : ℕ) : ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
    ‖𝓕 (fun t => (Kc a (radii ε) N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ)) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  set P := ∏ j ∈ Finset.range m, (a j / π) with hP
  refine ⟨2 ^ m * (1 + P), m, fun N hN ξ => ?_⟩
  have h1 := abs_pow_mul_norm_fourier_KC_le ha hr N m (by omega) ξ
  have h2 := norm_fourier_KC_le_one ha hr N ξ
  have h3 := one_add_pow_le |ξ| (abs_nonneg ξ) m
  have hpos : 0 < (1 + |ξ|) ^ m := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  change ‖𝓕 (KC a (radii ε) N) ξ‖ * (1 + |ξ|) ^ m ≤ _
  calc ‖𝓕 (KC a (radii ε) N) ξ‖ * (1 + |ξ|) ^ m
      ≤ ‖𝓕 (KC a (radii ε) N) ξ‖ * (2 ^ m * (1 + |ξ| ^ m)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = 2 ^ m * (‖𝓕 (KC a (radii ε) N) ξ‖ + |ξ| ^ m * ‖𝓕 (KC a (radii ε) N) ξ‖) := by ring
    _ ≤ 2 ^ m * (1 + P) := by gcongr

def climit (p : ℕ) : ℝ := ⨆ n, coef a n p

theorem bddAbove_coef (p : ℕ) : BddAbove (Set.range fun n => coef a n p) :=
  ⟨weight M p, by rintro _ ⟨n, rfl⟩; exact coef_le_weight hε hg n p⟩

theorem tendsto_coef (p : ℕ) : Tendsto (fun n => coef a n p) atTop (𝓝 (climit (a := a) p)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => coef_mono (fun j => (hg j).1) n p)
    (bddAbove_coef hε hg p)

theorem climit_le_weight (p : ℕ) : climit (a := a) p ≤ weight M p :=
  ciSup_le fun n => coef_le_weight hε hg n p

theorem climit_nonneg (p : ℕ) : 0 ≤ climit (a := a) p :=
  (coef_nonneg (fun j => (hg j).1) 0 p).trans (le_ciSup (bddAbove_coef hε hg p) 0)

end Limit

end LineKernel

open LineKernel in

theorem exists_dixmierMalliavin_line (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → ℝ) (g h : ℝ → ℂ), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      tsupport g ⊆ Set.Icc (-ε) ε ∧ tsupport h ⊆ Set.Icc (-ε) ε ∧
      Summable (fun p => |c p| * M p) ∧
      ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → (∀ p, ∀ t ∈ Set.Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p) →
        F 0 = (∑' p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t) + ∫ t, F t * h t := by
  choose a hg using fun j => (eventually_good M hε j).exists
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hKs : ∀ N, support (Kc a (radii ε) N) ⊆ Icc 0 (ε / 2) := fun N t ht =>
    ⟨(support_Kc_subset ha hr N ht).1, (support_Kc_subset ha hr N ht).2.trans (Rs_radii_le hε N)⟩
  obtain ⟨g, hgs, hgt, hgl⟩ := exists_smooth_weak_limit (K := Kc a (radii ε)) (a := 0)
    (b := ε / 2) (integrable_Kc ha hr) (Kc_nonneg ha hr) (integral_Kc_le_one ha hr) hKs
    (tendsto_fourier_Kc hε hg) (decay_fourier_Kc hε hg)
  have hsub : Icc 0 (ε / 2) ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) (by linarith)
  refine ⟨fun p => (-1) ^ p * climit (a := a) p, g, remSum (ε := ε) (a := a), hgs,
    contDiff_remSum hε hg, hgt.trans hsub,
    (closure_minimal (support_remSum_subset hε hg) isClosed_Icc).trans hsub, ?_, ?_⟩
  · refine Summable.of_norm_bounded
      (summable_geometric_two.mul_right (max 1 |M 0|)) fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (climit_nonneg hε hg p)]
    exact (mul_le_mul_of_nonneg_right (climit_le_weight hε hg p) (abs_nonneg _)).trans
      (weight_mul_abs_le M p)
  · intro F hF hFM

    have hA : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), ∫ t, F t * ρ a (radii ε) j t) atTop
        (𝓝 (∫ t, F t * remSum (ε := ε) (a := a) t)) :=
      ((hasSum_integral_remSum hε hg hF.continuous (fun t ht => by
        simpa using hFM 0 t ht)).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

    have hB : Tendsto (fun n => ∫ u, opT a (n + 1) F u * KC a (radii ε) n u) atTop
        (𝓝 (∑' p, (((-1) ^ p * climit (a := a) p : ℝ) : ℂ) *
          ∫ t, iteratedDeriv p F t * g t)) := by
      have hcont : ∀ p, Continuous (iteratedDeriv p F) := fun p =>
        hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
      have hKsC : ∀ n, support (KC a (radii ε) n) ⊆ Icc 0 (ε / 2) := fun n u hu =>
        hKs n (by simpa [KC] using hu)
      have hsplit : ∀ n, ∫ u, opT a (n + 1) F u * KC a (radii ε) n u =
          ∑' p, sc a (n + 1) p * ∫ u, iteratedDeriv p F u * KC a (radii ε) n u := by
        intro n
        rw [tsum_eq_sum (s := Finset.range (n + 2)) fun p hp => by
          rw [Finset.mem_range, not_lt] at hp
          simp [sc, coef_eq_zero a (by omega : n + 1 < p)]]
        simp only [opT, Finset.sum_mul]
        rw [integral_finsetSum (Finset.range (n + 1 + 1))
          (f := fun p u => sc a (n + 1) p * iteratedDeriv p F u * KC a (radii ε) n u)
          fun p _ => integrable_mul_of_support (φ := fun u => sc a (n + 1) p * iteratedDeriv p F u)
          (continuous_const.mul (hcont p)) (integrable_KC ha hr n) (hKsC n)]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← integral_const_mul]; congr 1; funext u; ring
      rw [show (fun n => ∫ u, opT a (n + 1) F u * KC a (radii ε) n u) =
          fun n => ∑' p, sc a (n + 1) p * ∫ u, iteratedDeriv p F u * KC a (radii ε) n u from
        funext hsplit]
      refine tendsto_tsum_of_dominated_convergence (bound := fun p => weight M p * |M p|) ?_ ?_ ?_
      · exact Summable.of_nonneg_of_le (fun p => mul_nonneg (weight_pos M p).le (abs_nonneg _))
          (weight_mul_abs_le M) (summable_geometric_two.mul_right _)
      · intro p
        have h1 : Tendsto (fun n => sc a (n + 1) p) atTop
            (𝓝 ((((-1) ^ p * climit (a := a) p : ℝ) : ℂ))) := by
          have := ((Complex.continuous_ofReal.tendsto _).comp
            ((tendsto_coef hε hg p).comp (tendsto_add_atTop_nat 1))).const_mul ((-1 : ℂ) ^ p)
          simpa [sc, Function.comp_def] using this
        exact h1.mul (hgl _ (hcont p))
      · refine Eventually.of_forall fun n p => ?_
        rw [norm_mul]
        have hsc : ‖sc a (n + 1) p‖ ≤ weight M p := by
          simp only [sc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (coef_nonneg ha _ _)]
          exact coef_le_weight hε hg _ _
        have hint : ‖∫ u, iteratedDeriv p F u * KC a (radii ε) n u‖ ≤ |M p| := by
          refine (norm_integral_le_integral_norm _).trans ?_
          calc ∫ u, ‖iteratedDeriv p F u * KC a (radii ε) n u‖
              ≤ ∫ u, |M p| * Kc a (radii ε) n u := by
                refine integral_mono (integrable_mul_of_support (hcont p) (integrable_KC ha hr n)
                  (hKsC n)).norm ((integrable_Kc ha hr n).const_mul _) fun u => ?_
                rw [norm_mul]
                simp only [KC, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (Kc_nonneg ha hr n u)]
                by_cases hu : Kc a (radii ε) n u = 0
                · simp [hu]
                · exact mul_le_mul_of_nonneg_right ((hFM p u (hsub (hKs n hu))).trans
                    (le_abs_self _)) (Kc_nonneg ha hr n u)
            _ = |M p| * ∫ u, Kc a (radii ε) n u := integral_const_mul _ _
            _ ≤ |M p| := by
                have := integral_Kc_le_one ha hr n
                have h0 : 0 ≤ |M p| := abs_nonneg _
                nlinarith
        exact mul_le_mul hsc hint (norm_nonneg _) (weight_pos M p).le
    have hlim := hB.add hA
    have hconst : (fun n => F 0) = fun n => (∫ u, opT a (n + 1) F u * KC a (radii ε) n u) +
        ∑ j ∈ Finset.range (n + 1), ∫ t, F t * ρ a (radii ε) j t :=
      funext fun n => stage_identity ha hr hF n
    rw [← hconst] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim

end

end GroundTheory.Automorphic
end

section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_decomp_direction {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f₁ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f₁) ∧
      HasCompactSupport f₁ ∧
      ∃ g k : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧ tsupport g ⊆ Icc (-ε) ε ∧
        tsupport k ⊆ Icc (-ε) ε ∧
        ∀ x, f x = (∫ t, g t * f₁ (h.expG (t • X) * x)) + ∫ t, k t * f (h.expG (t • X) * x) := by
  obtain ⟨M, hM, hser⟩ := h.exists_bound_dirDeriv hf hfc X
  obtain ⟨c, g, k, hg, hk, hgs, hks, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  obtain ⟨hf₁, hf₁c⟩ := hser c hc
  refine ⟨_, hf₁, hf₁c, g, k, hg, hk, hgs, hks, fun x => ?_⟩
  set F : ℝ → ℂ := fun t => f (h.expG (t • X) * x) with hFdef
  have hF : ContDiff ℝ ∞ F := h.contDiff_comp_expG_smul_mul hf X x
  have hD : ∀ p t, iteratedDeriv p F t = h.dirDeriv X p f (h.expG (t • X) * x) :=
    fun p t => h.iteratedDeriv_comp_expG_mul X p f x t
  have key := hid F hF (fun p t _ => by rw [hD]; exact hM p _)
  have hF0 : F 0 = f x := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero, one_mul]
  rw [hF0] at key
  rw [key]
  congr 1
  · have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    have hcont : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * g t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcont p).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * ‖g t‖ := by
      intro p t
      simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_assoc (|c p|)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (c p))
      have : ‖iteratedDeriv p F t‖ ≤ M p := by rw [hD]; exact hM p _
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hgi : Integrable (fun t => ‖g t‖) :=
      (hg.continuous.integrable_of_hasCompactSupport hgc).norm
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, ‖g t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e1 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e1]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    simp only [T, hD]
    rw [← tsum_mul_left]
    congr 1
    funext p
    ring
  · congr 1; funext t; rw [mul_comm]

theorem exists_decomp_iter {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤) (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        HasCompactSupport (F i)) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x)
  | 0, X, f, hf, hfc => by
    refine ⟨1, fun _ => f, fun _ _ => 1, fun _ => ⟨hf, hfc⟩, fun _ => ⟨contDiff_const, ?_⟩,
      fun x => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [h.revProdExp_zero, hv]
  | d + 1, X, f, hf, hfc => by
    let := h.chartedSpace
    obtain ⟨f₁, hf₁, hf₁c, g, k, hg, hk, hgs, hks, hdec⟩ :=
      h.exists_decomp_direction hf hfc (X 0) hε
    obtain ⟨m₁, F₁, K₁, hF₁, hK₁, hd₁⟩ := exists_decomp_iter hε (Fin.tail X) f₁ hf₁ hf₁c
    obtain ⟨m₂, F₂, K₂, hF₂, hK₂, hd₂⟩ := exists_decomp_iter hε (Fin.tail X) f hf hfc
    refine ⟨m₁ + m₂, Fin.append F₁ F₂,
      Fin.append (fun i t => g (t 0) * K₁ i (Fin.tail t)) (fun i t => k (t 0) * K₂ i (Fin.tail t)),
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hF₁ i
      · simpa only [Fin.append_right] using hF₂ i
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨contDiff_cons_kernel hg (hK₁ i).1, tsupport_cons_kernel hε.le hgs (hK₁ i).2⟩
      · simp only [Fin.append_right]
        exact ⟨contDiff_cons_kernel hk (hK₂ i).1, tsupport_cons_kernel hε.le hks (hK₂ i).2⟩
    · intro x
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le hg.continuous hgs (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => (hF₁ i).1.continuous) hd₁ x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hk.continuous hks (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => (hF₂ i).1.continuous) hd₂ x).symm

end IsExpLieAlgebra

theorem dixmierMalliavin (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ)
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ (n : ℕ) (φ ψ : Fin n → G → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (φ i)) ∧
        HasCompactSupport (φ i) ∧
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧ HasCompactSupport (ψ i)) ∧
      f = ∑ i, groupConv μ (φ i) (ψ i) := by
  let := h.chartedSpace
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp μ b
  obtain ⟨m, F, K, hF, hK, hd⟩ := h.exists_decomp_iter hε (⇑b) f hf hfc
  have hK' : ∀ i, ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ Metric.closedBall 0 ε := by
    intro i
    refine ⟨(hK i).1.comp contDiff_neg, ?_⟩
    intro t ht
    have : -t ∈ tsupport (K i) := by
      have := tsupport_comp_subset_preimage (K i) (f := fun t : Fin _ → ℝ => -t) continuous_neg ht
      simpa using this
    have := (hK i).2 this
    simpa [mem_closedBall_zero_iff, norm_neg] using this
  choose κ hκs hκc hκ using fun i => hdens (fun t => K i (-t)) (hK' i).1 (hK' i).2
  refine ⟨m, κ, F, fun i => ⟨hκs i, hκc i, (hF i).1, (hF i).2⟩, ?_⟩
  funext x
  rw [hd x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [groupConv, hκ i (fun y => F i (y⁻¹ * x))
    ((hF i).1.continuous.comp (continuous_inv.mul continuous_const))]
  have e : ∀ t : Fin (Module.finrank ℝ 𝔤) → ℝ, K i (-t) * F i ((h.prodExp (⇑b) t)⁻¹ * x) =
      (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) (-t) := by
    intro t
    have := h.revProdExp_inv (⇑b) (-t)
    rw [neg_neg] at this
    simp only [← this, inv_inv]
  simp_rw [e]
  exact (integral_neg_eq_self (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) volume).symm

end GroundTheory.Automorphic
end
