import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TranslationZeroModeLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAC

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

def ucL (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : X.L →ₗ[ℤ] Vsp X.dim :=
  (AddMonoidHom.mk' (fun γ : X.L => uc (IR I) (γ : Vsp X.dim))
    (fun a b => by simp only [Submodule.coe_add]; exact uc_add _ _)).toIntLinearMap

theorem NIp_le_ker (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : NIp X I ≤ LinearMap.ker (ucL X I) := by
  intro x hx
  rw [LinearMap.mem_ker]
  exact uc_Ip hx

def uQ (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Qc X I →ₗ[ℤ] Vsp X.dim :=
  (NIp X I).liftQ (ucL X I) (NIp_le_ker X I)

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)}

theorem uQ_mk (γ : X.L) : uQ X I (Submodule.Quotient.mk γ) = uc (IR I) (γ : Vsp X.dim) := rfl

theorem uQ_out (c : Qc X I) : uQ X I c = uc (IR I) ((Quotient.out c : X.L) : Vsp X.dim) := by
  have e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c := Quotient.out_eq c
  calc uQ X I c = uQ X I (Submodule.Quotient.mk (Quotient.out c)) := by rw [e]
    _ = _ := uQ_mk _

theorem uQ_mem (c : Qc X I) : uQ X I c ∈ IR I := by
  rw [uQ_out]
  exact uc_mem _ _

theorem uQ_eq_zero {c : Qc X I} (h : uQ X I c = 0) : c = 0 := by
  have hγ : ((Quotient.out c : X.L) : Vsp X.dim) ∈ Ip X I := by
    rw [mem_Ip]
    refine ⟨(Quotient.out c).2, fun a ha => ?_⟩
    rw [← inner_uc (IR I) _ a (Submodule.subset_span ha), ← uQ_out, h, inner_zero_left]
  have e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c := Quotient.out_eq c
  rw [← e]
  exact (Submodule.Quotient.mk_eq_zero _).2 hγ

variable {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem uQ_sep {c : Qc X I} (h : c ≠ 0) : b0 (E := E) P.q P.R0 ≤ ‖uQ X I c‖ ^ 2 := by
  have hne : uQ X I c ≠ 0 := fun h0 => h (uQ_eq_zero h0)
  rw [uQ_out] at hne ⊢
  exact hI.sep _ (Quotient.out c).2 _ (isU_uc _) hne

theorem uQ_dist {c c' : Qc X I} (h : c ≠ c') :
    Real.sqrt (b0 (E := E) P.q P.R0) ≤ dist (uQ X I c) (uQ X I c') := by
  have h1 := uQ_sep hI (sub_ne_zero.2 h)
  rw [dist_eq_norm, ← map_sub, ← Real.sqrt_sq (norm_nonneg (uQ X I (c - c')))]
  exact Real.sqrt_le_sqrt h1

theorem tailQ (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (a : ℝ) (ha : 0 < a)
    (hcond : (dK (IR I) : ℝ) + 1 ≤ a * P.q * b0 (E := E) P.q P.R0) :
    Summable (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} =>
        Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2)) ∧
      ∑' c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2) ≤
        2 * 3 ^ (dK (IR I)) * Real.exp (-(a * P.q * b0 (E := E) P.q P.R0)) := by
  classical
  obtain ⟨ρ, -, hρ⟩ := hI.rank
  have hdK : dK (IR I) = 2 * (PT.f E * ρ) := by
    show Module.finrank ℝ (IR I) = 2 * (PT.f E * ρ)
    rw [hρ]; ring
  have hb0 : 0 < b0 (E := E) P.q P.R0 := cutoff_pos P
  have haqb : 0 < a * P.q * b0 (E := E) P.q P.R0 := by
    have : (0 : ℝ) ≤ dK (IR I) := Nat.cast_nonneg _
    linarith
  have haq : 0 < a * (P.q : ℝ) := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [haqb, hb0, hneg]
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a * P.q) := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.2 haq
  have hs2 : s ^ 2 = a * P.q := by rw [hs_def]; exact Real.sq_sqrt haq.le
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = Real.sqrt (b0 (E := E) P.q P.R0) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδ_def ▸ Real.sqrt_pos.2 hb0
  have hδ2 : δ ^ 2 = b0 (E := E) P.q P.R0 := by rw [hδ_def]; exact Real.sq_sqrt hb0.le
  have h4s : 0 < 4 * s := by positivity
  have hr0pos : 0 < 4 * s * δ := by positivity
  have hnorm : ∀ c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, δ ≤ ‖uQ X I c.1‖ := by
    intro c
    have hc : c.1 ≠ 0 := by simpa using c.2
    rw [hδ_def, ← Real.sqrt_sq (norm_nonneg (uQ X I c.1))]
    exact Real.sqrt_le_sqrt (uQ_sep hI hc)
  have hinj : Function.Injective
      (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} => uQ X I c.1) := by
    intro c c' hcc
    apply Subtype.ext
    have h0 : uQ X I (c.1 - c'.1) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hcc
    exact sub_eq_zero.1 (uQ_eq_zero h0)
  have key := hA {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} (fun c => 4 * s * ‖uQ X I c.1‖)
    (PT.f E * ρ) (4 * s * δ) hr0pos
    (by
      have e1 : (4 * s * δ) ^ 2 = 16 * (a * P.q * b0 (E := E) P.q P.R0) := by
        rw [mul_pow, mul_pow, hs2, hδ2]; ring
      have e2 : (dK (IR I) : ℝ) = 2 * ((PT.f E * ρ : ℕ) : ℝ) := by rw [hdK]; push_cast; ring
      rw [e1]; rw [e2] at hcond; linarith)
    (fun c => mul_le_mul_of_nonneg_left (hnorm c) h4s.le)
    (by
      intro R hR S hS
      have hcard : (S.image fun c => uQ X I c.1).card = S.card := Finset.card_image_of_injective _ hinj
      have hpk := pack_K hP (IR I) (S.image fun c => uQ X I c.1)
        (by
          intro u hu
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
          exact uQ_mem c.1) δ (R / (4 * s)) hδ
        (by
          rw [le_div_iff₀ h4s]
          calc δ * (4 * s) = 4 * s * δ := by ring
            _ ≤ R := hR)
        (by
          intro u hu
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hu
          rw [le_div_iff₀ h4s]
          calc ‖uQ X I c.1‖ * (4 * s) = 4 * s * ‖uQ X I c.1‖ := by ring
            _ ≤ R := hS c hc)
        (by
          intro u hu v hv huv
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hv
          have hcc : c.1 ≠ c'.1 := fun e => huv (by simp only [e])
          rw [hδ_def]
          exact uQ_dist hI hcc)
      have e3 : 3 * (R / (4 * s)) / δ = 3 * R / (4 * s * δ) := by
        field_simp
      rw [e3, hdK, hcard] at hpk
      exact hpk)
  have hfun : (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} =>
      Real.exp (-(4 * s * ‖uQ X I c.1‖) ^ 2 / 16)) =
      fun c => Real.exp (-(a * P.q) * ‖uQ X I c.1‖ ^ 2) := by
    funext c
    congr 1
    rw [mul_pow, mul_pow, hs2]; ring
  have e9 : (9 : ℝ) ^ (PT.f E * ρ) = 3 ^ (dK (IR I)) := by rw [hdK, pow_mul (3 : ℝ) 2 (PT.f E * ρ)]; norm_num
  have er : -(4 * s * δ) ^ 2 / 16 = -(a * P.q * b0 (E := E) P.q P.R0) := by
    rw [mul_pow, mul_pow, hs2, hδ2]; ring
  rw [hfun, e9, er] at key
  exact key

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

theorem norm_uc_sq {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι) :
    ‖uc K v‖ ^ 2 = ∑ k, (z K k v).im ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_uc _ v _ (uc_mem _ v), uc, Hf_sum_r, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_rsmul_r, Complex.im_ofReal_mul, z]; ring

theorem re_S {ι : Type} [Fintype ι] {K : Submodule ℝ (EuclideanSpace ℂ ι)}
    (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0) (w : EuclideanSpace ℂ ι) :
    (S K w).re = ‖w‖ ^ 2 - ‖p2 K w‖ ^ 2 - 2 * ‖uc K w‖ ^ 2 := by
  rw [norm_sq_decomp hK, norm_uc_sq, S, Complex.re_sum]
  have hz : ∀ k, ‖z K k w‖ ^ 2 = (z K k w).re ^ 2 + (z K k w).im ^ 2 := fun k => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [hz, sq, Complex.mul_re]
  rw [Finset.mul_sum]
  have h3 : ∑ k, ((z K k w).re * (z K k w).re - (z K k w).im * (z K k w).im) =
      ∑ k, ((z K k w).re * (z K k w).re + (z K k w).im * (z K k w).im) -
        ∑ k, 2 * ((z K k w).im * (z K k w).im) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h3]; ring

section Nsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
include hI

theorem norm_Tm (γ : X.L) (v : Vsp X.dim) :
    ‖Tm X I q β γ v‖ = Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(q * Real.pi) * ‖uc (IR I) (v - γ)‖ ^ 2) *
        (‖β (wmap (IR I) (v - γ))‖ * Real.exp (-(q * Real.pi) * ‖wmap (IR I) (v - γ)‖ ^ 2 / 2)) := by
  have hK := hK_of hI
  have he : ‖(X.eps (γ : Vsp X.dim) : ℂ)‖ = 1 := by
    rcases X.eps_pm _ γ.2 with h | h <;> simp [h]
  simp only [Tm, Uh, Uq, F0, norm_mul, norm_pow, he, one_pow, one_mul, Complex.norm_exp]
  set w := v - (γ : Vsp X.dim) with hw
  have h1 : (Hf v (γ : Vsp X.dim)).re = (‖v‖ ^ 2 + ‖(γ : Vsp X.dim)‖ ^ 2 - ‖w‖ ^ 2) / 2 := by
    have := Hf_self_re w
    rw [hw, Hf_sub_l, Hf_sub_r, Hf_sub_r, Complex.sub_re, Complex.sub_re, Complex.sub_re,
      Hf_self_re, Hf_self_re, Hf_swap v (γ : Vsp X.dim), Complex.conj_re] at this
    rw [← hw] at this
    linarith
  have h2 := re_S hK w
  rw [norm_wmap hK]
  have hre1 : (q * Real.pi * Hf v (γ : Vsp X.dim) - q * Real.pi * Hf (γ : Vsp X.dim) γ / 2 : ℂ).re =
      q * Real.pi * (Hf v (γ : Vsp X.dim)).re - q * Real.pi * ‖(γ : Vsp X.dim)‖ ^ 2 / 2 := by
    simp [Complex.mul_re, Hf_self_re]
  have hre2 : ((q * Real.pi / 2 : ℂ) * S (IR I) w).re = q * Real.pi / 2 * (S (IR I) w).re := by
    simp [Complex.mul_re]
  rw [hre1, hre2, h1, h2]
  rw [← mul_assoc, ← Real.exp_add, mul_comm (‖β _‖), ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem exp_shift_le (a : ℝ) (ha : 0 ≤ a) (u w : Vsp X.dim) :
    Real.exp (-a * ‖u - w‖ ^ 2) ≤ Real.exp (a * ‖u‖ ^ 2) * Real.exp (-(a / 2) * ‖w‖ ^ 2) := by
  have h1 : ‖w‖ ≤ ‖u‖ + ‖u - w‖ := by
    calc ‖w‖ = ‖u - (u - w)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - w‖ := norm_sub_le _ _
  have h2 : ‖w‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖u - w‖ ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg u, norm_nonneg (u - w), sq_nonneg (‖u‖ - ‖u - w‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

theorem cond_tail (a : ℝ) (ha : 1 / 2 ≤ a) : (dK (IR I) : ℝ) + 1 ≤ a * P.q * b0 (E := E) P.q P.R0 := by
  obtain ⟨ρ, hρm, hρ⟩ := hI.rank
  have hdK : (dK (IR I) : ℝ) ≤ dstar (E := E) P.m := by
    rw [dK, hρ, dstar]; push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hρm) (by positivity)
  have h6 := P.C6
  have hr : 0 ≤ (X.r : ℝ) * Real.log X.r := by
    rcases Nat.eq_zero_or_pos X.r with h | h
    · simp [h]
    · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast h))
  have hDF : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) := by positivity
  have hg : 0 ≤ (X.gA : ℝ) * Real.log 2 := by positivity
  have ht0 : t0 (E := E) P.q P.R0 = P.q * b0 (E := E) P.q P.R0 := rfl
  have hb := cutoff_pos P
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hqb : 0 < (P.q : ℝ) * b0 (E := E) P.q P.R0 := mul_pos hq hb
  rw [ht0] at h6
  nlinarith

theorem summable_gauss (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (a : ℝ) (ha : 1 / 2 ≤ a) :
    Summable (fun c : Qc X I => Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2)) :=
  (Finset.summable_compl_iff {0}).1 (tailQ hI hP hA a (by linarith) (cond_tail hI a ha)).1

variable {q β}

theorem norm_Tc_le {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2) (c : Qc X I) (v : Vsp X.dim) :
    ‖Tc X I q β c v‖ ≤ B * Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(q * Real.pi) * ‖uc (IR I) v - uQ X I c‖ ^ 2) := by
  rw [Tc, norm_Tm hI, uc_sub, ← uQ_out]
  have hN : ‖β (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)))‖ *
      Real.exp (-(q * Real.pi) * ‖wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim))‖ ^ 2 / 2) ≤ B := by
    set t := wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim))
    have h := hB t
    have hsq : (‖β t‖ * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2 / 2)) ^ 2 =
        ‖β t‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [← hsq] at h
    exact (pow_le_pow_iff_left₀ (by positivity) hB0 two_ne_zero).1 h
  calc _ ≤ Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) * Real.exp (-(q * Real.pi) * ‖uc (IR I) v - uQ X I c‖ ^ 2) * B :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by ring

omit hI in
theorem diff_Hf (a : Vsp X.dim) : Differentiable ℂ (fun v : Vsp X.dim => Hf v a) := by
  unfold Hf
  first
    | fun_prop
    | exact Differentiable.fun_sum fun i _ =>
        (EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable.mul_const _
    | exact Differentiable.sum fun i _ =>
        (EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable.mul_const _

omit hI in
theorem differentiable_zeroModeLift_of (hβd : Differentiable ℂ β) : Differentiable ℂ (F0 I q β) := by
  unfold F0
  apply Differentiable.mul
  · apply Differentiable.cexp
    apply Differentiable.const_mul
    unfold S z
    exact Differentiable.fun_sum (fun k _ => (diff_Hf _).pow 2)
  · exact hβd.comp (wmap (IR I)).differentiable

omit hI in
theorem diff_Tm (hβd : Differentiable ℂ β) (γ : Vsp X.dim) : Differentiable ℂ (Uh X q γ (F0 I q β)) := by
  unfold Uh Uq
  apply Differentiable.const_mul
  apply Differentiable.mul
  · apply Differentiable.cexp
    exact ((diff_Hf γ).const_mul _).sub_const _
  · exact (differentiable_zeroModeLift_of hβd).comp (differentiable_id.sub_const γ)

end Nsec

section Ssec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ} (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound)
  {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2)
include hI hP hA hB0 hB

theorem Tc_bound (R : ℝ) (c : Qc X I) (v : Vsp X.dim) (hv : ‖v‖ ≤ R) :
    ‖Tc X I P.q β c v‖ ≤ B * Real.exp (P.q * Real.pi * R ^ 2 / 2) *
      (Real.exp (P.q * Real.pi * R ^ 2) * Real.exp (-(Real.pi / 2 * P.q) * ‖uQ X I c‖ ^ 2)) := by
  have hq : (0 : ℝ) ≤ P.q * Real.pi := by positivity
  have hv2 : ‖v‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have hu2 : ‖uc (IR I) v‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((norm_uc_le hI.iso v).trans hv) 2
  refine (norm_Tc_le hI hB0 hB c v).trans ?_
  rw [mul_assoc, mul_assoc B]
  apply mul_le_mul_of_nonneg_left _ hB0
  apply mul_le_mul (Real.exp_le_exp.2 (by nlinarith)) _ (by positivity) (by positivity)
  refine (exp_shift_le hI (P.q * Real.pi) hq _ _).trans ?_
  apply mul_le_mul (Real.exp_le_exp.2 (by nlinarith)) (le_of_eq ?_) (by positivity) (by positivity)
  congr 1; ring

theorem summable_Tc (v : Vsp X.dim) : Summable (fun c : Qc X I => Tc X I P.q β c v) := by
  refine Summable.of_norm_bounded ?_ (fun c => Tc_bound hI hP hA hB0 hB ‖v‖ c v le_rfl)
  exact ((summable_gauss hI hP hA (Real.pi / 2) (by linarith [Real.pi_gt_three])).mul_left _).mul_left _

theorem diff_sP (hβd : Differentiable ℂ β) : Differentiable ℂ (sP X I P.q β) := by
  intro x
  have hb : ∀ R : ℝ, ∃ u : Qc X I → ℝ, Summable u ∧
      ∀ c v, ‖v‖ ≤ R → ‖Tc X I P.q β c v‖ ≤ u c := by
    intro R
    exact ⟨_, ((summable_gauss hI hP hA (Real.pi / 2) (by linarith [Real.pi_gt_three])).mul_left
      (Real.exp (P.q * Real.pi * R ^ 2))).mul_left (B * Real.exp (P.q * Real.pi * R ^ 2 / 2)),
      fun c v hv => Tc_bound hI hP hA hB0 hB R c v hv⟩
  exact (pa_tsum_hasFDeriv (fun c => Tc X I P.q β c)
    (fun c => diff_Tm (q := P.q) hβd _) hb x).2.differentiableAt

def colS (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ) :
    (Fin 1 → Vsp X.dim) → ℂ :=
  fun w => sP X I q β (w 0)

theorem colS_mem (hβ : β ∈ (YB hI hP P.q).Sec P.q) : colS X I P.q β ∈ X.Sec P.q 1 := by
  refine ⟨(diff_sP hI hP hA hB0 hB hβ.1).comp (differentiable_apply 0), fun γ hγ v => ?_⟩
  have h := sP_shift hI hP P.q hβ ⟨γ 0, hγ 0⟩ (v 0)
  simp only [colS, Pi.add_apply, Fin.prod_univ_one, HC, Fin.sum_univ_one]
  exact h

end Ssec

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end
