import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DecayAtCusp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariables
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerDbar

def P (s : ℂ) (G : ℂ → ℂ) (d : ℂ) : Prop :=
  ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = d

lemma wirtinger_eq_zero_of_hasDerivAt {s : ℂ} {g : ℂ → ℂ} {g' : ℂ} (hg : HasDerivAt g g' s) : P s g 0 := by
  refine ⟨_, hg.hasFDerivAt.restrictScalars ℝ, ?_⟩
  simp

lemma wirtinger_sub {s : ℂ} {G H : ℂ → ℂ} {d e : ℂ} (hG : P s G d) (hH : P s H e) :
    P s (fun z => G z - H z) (d - e) := by
  obtain ⟨L, hL, hd⟩ := hG
  obtain ⟨M, hM, he⟩ := hH
  refine ⟨L - M, hL.sub hM, ?_⟩
  simp only [ContinuousLinearMap.sub_apply]
  rw [← hd, ← he]; ring

lemma wirtinger_sum {s : ℂ} {ι : Type} (S : Finset ι) (G : ι → ℂ → ℂ) (d : ι → ℂ)
    (h : ∀ i ∈ S, P s (G i) (d i)) : P s (fun z => ∑ i ∈ S, G i z) (∑ i ∈ S, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simpa using hasFDerivAt_const (0 : ℂ) s, by simp⟩
  | insert a S ha ih =>
    obtain ⟨L, hL, hd⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨M, hM, he⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨L + M, ?_, ?_⟩
    · refine (hL.add hM).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      simp [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha, ← hd, ← he]; simp only [ContinuousLinearMap.add_apply]; ring

lemma wirtinger_conj_mul_pow {s : ℂ} {b : ℂ → ℂ} {b' : ℂ} (hb : HasDerivAt b b' s) (j : ℕ) :
    P s (fun z => starRingEnd ℂ (b z) * z ^ j) (-2 * Complex.I * s ^ j * starRingEnd ℂ b') := by
  have h1 : HasFDerivAt (fun z => starRingEnd ℂ (b z))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) b').restrictScalars ℝ)) s :=
    Complex.conjCLE.hasFDerivAt.comp s (hb.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun z : ℂ => z ^ j)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((j : ℂ) * s ^ (j - 1))).restrictScalars ℝ) s :=
    ((hasDerivAt_pow j s).hasFDerivAt.restrictScalars ℝ)
  refine ⟨_, h1.mul h2, ?_⟩
  simp
  ring

theorem wirtinger_eichler : ∀ (w : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → ∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun z : ℂ => (eichler w f (ofComplex z) - (eichler w h (ofComplex z)).map (starRingEnd ℂ) - p).eval z) L s ∧
      L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s)) := by
  intro w f h p hf hh s hs
  have he : ∀ (g : ℍ → ℂ) (z : ℂ), 0 < z.im → eichler w g (ofComplex z) =
      ∑ j ∈ Finset.range (w + 1), C ((w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w g j z) * X ^ j := by
    intro g z hz
    rw [ofComplex_apply_of_im_pos hz]
    rfl
  have hF : P s (fun z => ∑ j ∈ Finset.range (w + 1), (w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w f j z * z ^ j)
      (∑ j ∈ Finset.range (w + 1), (0 : ℂ)) :=
    wirtinger_sum _ _ _ fun j _ => wirtinger_eq_zero_of_hasDerivAt
      (((GlobalTheory.EichlerChange.hasDerivAt_ecoef w f hf j s hs).const_mul _).mul (hasDerivAt_pow j s))
  have hH : P s (fun z => ∑ j ∈ Finset.range (w + 1), starRingEnd ℂ ((w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w h j z) * z ^ j)
      (∑ j ∈ Finset.range (w + 1), -2 * Complex.I * s ^ j *
        starRingEnd ℂ ((w.choose j : ℂ) * ((h ∘ ofComplex) s * (-s) ^ (w - j)))) :=
    wirtinger_sum _ _ _ fun j _ => wirtinger_conj_mul_pow ((GlobalTheory.EichlerChange.hasDerivAt_ecoef w h hh j s hs).const_mul _) j
  obtain ⟨L, hL, hd⟩ := wirtinger_sub (wirtinger_sub hF hH) (wirtinger_eq_zero_of_hasDerivAt (Polynomial.hasDerivAt p s))
  refine ⟨L, hL.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hs] with z hz
    rw [he f z hz, he h z hz]
    simp [Polynomial.map_sum, eval_finset_sum]
  · rw [hd]
    have hb : (s - (starRingEnd ℂ) s) ^ w = ∑ j ∈ Finset.range (w + 1),
        s ^ j * (-(starRingEnd ℂ) s) ^ (w - j) * (w.choose j : ℂ) := by
      rw [sub_eq_add_neg, add_pow]
    rw [hb, Finset.mul_sum, Finset.sum_mul, Finset.sum_const_zero]
    simp only [zero_sub, sub_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, map_mul, map_natCast, map_pow, map_neg]
    ring

end GlobalTheory.EichlerDbar
end
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_eichler_sub_conj_wirtinger : ∀ (w : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → ∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun z : ℂ => (eichler w f (ofComplex z) - (eichler w h (ofComplex z)).map (starRingEnd ℂ) - p).eval z) L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s)) := by
  atlas_forward_decl GlobalTheory.EichlerDbar.wirtinger_eichler
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory

open scoped Interval

theorem green_periodic_rectangle : ∀ (G D : ℂ → ℂ) (T a b : ℝ), 0 < T → 0 < a → a ≤ b →
    (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = D s) →
    ContinuousOn D {s : ℂ | 0 < s.im} → (∀ s : ℂ, 0 < s.im → G (s + T) = G s) →
    (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (b : ℂ) * Complex.I)) -
      (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (a : ℂ) * Complex.I)) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
  intro G D T a b hT ha hab hG hD hper
  let φL : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Complex.I
  have hφ : ∀ p : ℝ × ℝ, φL p = (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
    intro p; simp [φL, Complex.real_smul]
  have him : ∀ p : ℝ × ℝ, (φL p).im = p.1 := by
    intro p; simp [hφ]
  have hder : ∀ s : ℂ, 0 < s.im → HasFDerivAt G (fderiv ℝ G s) s ∧
      fderiv ℝ G s Complex.I - Complex.I * fderiv ℝ G s 1 = D s := by
    intro s hs
    obtain ⟨L, hL, hLD⟩ := hG s hs
    rw [hL.fderiv]; exact ⟨hL, hLD⟩
  have hRpos : ∀ p ∈ [[a, b]] ×ˢ [[(0:ℝ), T]], 0 < (φL p).im := by
    intro p hp
    rw [him]
    have h1 := hp.1
    rw [Set.uIcc_of_le hab] at h1
    exact lt_of_lt_of_le ha h1.1
  have hGc : ContinuousOn G {s : ℂ | 0 < s.im} := fun s hs =>
    ((hder s hs).1.continuousAt).continuousWithinAt
  have hfc : ContinuousOn (fun p => G (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) :=
    hGc.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)
  have hsub : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T),
      x ∈ [[a, b]] ×ˢ [[(0:ℝ), T]] := fun x hx =>
    ⟨Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩
  have hdf : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T),
      HasFDerivAt (fun p => G (φL p)) ((fderiv ℝ G (φL x)).comp φL) x := fun x hx =>
    (hder _ (hRpos x (hsub x hx))).1.comp x φL.hasFDerivAt
  have hpt : ∀ p : ℝ × ℝ, 0 < p.1 →
      (fderiv ℝ G (φL p)).comp φL (1, 0) + ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)
        = D (φL p) := by
    intro p hp
    have h := (hder (φL p) (by rw [him]; exact hp)).2
    rw [← h]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, hφ, smul_eq_mul]
    simp
    ring
  have hi : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (fderiv ℝ G (φL p)).comp φL (1, 0) +
        ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) := by
    have hc : ContinuousOn (fun p => D (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) :=
      hD.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)
    refine (hc.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun ?_
      (measurableSet_uIcc.prod measurableSet_uIcc)
    intro p hp
    have := hRpos p hp
    rw [him] at this
    exact (hpt p this).symm
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (fun p => G (φL p)) (fun p => (-Complex.I) • G (φL p))
    (fun p => (fderiv ℝ G (φL p)).comp φL) (fun p => (-Complex.I) • (fderiv ℝ G (φL p)).comp φL)
    a 0 b T hfc (by exact hfc.const_smul (-Complex.I)) hdf (fun x hx => by exact (hdf x hx).const_smul (-Complex.I)) hi
  have hL : (∫ y in a..b, ∫ x in (0:ℝ)..T,
      (fderiv ℝ G (φL (y, x))).comp φL (1, 0) +
        ((-Complex.I) • (fderiv ℝ G (φL (y, x))).comp φL) (0, 1)) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1
    try simp only
    rw [hpt (y, x) hy', hφ]
  have hg : (∫ y in a..b, (-Complex.I) • G (φL (y, T))) =
      ∫ y in a..b, (-Complex.I) • G (φL (y, 0)) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1
    try simp only
    have : φL (y, T) = φL (y, 0) + (T : ℂ) := by rw [hφ, hφ]; push_cast; ring
    rw [this, hper _ (by rw [him]; exact hy')]
  rw [hL, hg, sub_self, zero_add] at key
  rw [key]
  simp only [hφ]

end GlobalTheory
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.green_formula_periodic_rectangle_upperHalfPlane : ∀ (G D : ℂ → ℂ) (T a b : ℝ), 0 < T → 0 < a → a ≤ b → (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = D s) → ContinuousOn D {s : ℂ | 0 < s.im} → (∀ s : ℂ, 0 < s.im → G (s + T) = G s) → (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (b : ℂ) * Complex.I)) - (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (a : ℂ) * Complex.I)) = ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
  atlas_forward_decl GlobalTheory.green_periodic_rectangle
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Qc

lemma exp_eq_conj_qParam (T : ℝ) (n : ℕ) (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) =
      (starRingEnd ℂ) (1 / Function.Periodic.qParam T ((x : ℂ) + (y : ℂ) * Complex.I) ^ n) *
        (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, one_div, ← Complex.exp_neg, ← Complex.exp_conj,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, map_div₀, map_add, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  push_cast
  linear_combination (4 * (Real.pi : ℂ) * n * y / T) * Complex.I_sq

theorem conj_integral (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ) (hT : 0 < T) (hy : 0 < y)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (hper : Function.Periodic (h ∘ ofComplex) T)
    (hbdd : IsBoundedAtImInfty h) :
    (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) *
        Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) =
      T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  have hc : ∀ f : ℝ → ℂ, (starRingEnd ℂ) (∫ u in (0 : ℝ)..T, f u) = ∫ u in (0 : ℝ)..T, (starRingEnd ℂ) (f u) := by
    intro f
    rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le, integral_conj]
  rw [qExpansion_coeff_eq_intervalIntegral hT hper hhol hbdd n hy, map_mul, hc]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [show (starRingEnd ℂ) (1 / (T : ℂ)) = 1 / (T : ℂ) by simp [Complex.conj_ofReal],
    ← mul_assoc, mul_one_div_cancel hT', one_mul, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  simp only [ofComplex_apply_of_im_pos him]
  rw [exp_eq_conj_qParam, map_mul, ← mul_assoc, mul_comm ((starRingEnd ℂ) (h _))]
  rfl

end GlobalTheory.HeckeFamilyMatrices.Qc
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff : ∀ (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ), 0 < T → 0 < y → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) = T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
open Filter Topology Set MeasureTheory

namespace GlobalTheory

theorem ode_coeff_zero_of_decay_ends : ∀ (v : ℝ → ℂ) (K c : ℂ) (C α β : ℝ) (w : ℕ), 1 ≤ w → 0 < α → 0 < β → K ≠ 0 → (∀ y : ℝ, 0 < y → ‖v y‖ ≤ C * y ^ ((w : ℝ) / 2) * Real.exp (-α * y)) → (∀ a b : ℝ, 0 < a → a ≤ b → v b - v a = K * c * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) → c = 0 := by
  intro v K c C α β w hw hα hβ hK hbound hdiff
  set g : ℝ → ℝ := fun y => y ^ w * Real.exp (-β * y) with hg
  have gcont : Continuous g := by fun_prop
  have hint : ∀ a b : ℝ, (∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) = ((∫ y in a..b, g y : ℝ) : ℂ) := by
    intro a b
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    ext y
    simp [g]
  set I := ∫ y in (1:ℝ)..2, g y with hIdef
  have hI : 0 < I := intervalIntegral.intervalIntegral_pos_of_pos_on (gcont.intervalIntegrable _ _)
    (fun x hx => by
      have : 0 < x := by linarith [hx.1]
      simp only [g]; positivity) (by norm_num)
  have key : ∀ a b : ℝ, 0 < a → a ≤ 1 → 2 ≤ b → ‖K * c‖ * I ≤ ‖v b‖ + ‖v a‖ := by
    intro a b ha ha1 hb2
    have h1 := hdiff a b ha (by linarith)
    have hmono : I ≤ ∫ y in a..b, g y := by
      apply intervalIntegral.integral_mono_interval ha1 (by norm_num) hb2
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        have : 0 < y := lt_trans ha hy.1
        simp only [g, Pi.zero_apply]; positivity
      · exact gcont.intervalIntegrable _ _
    calc ‖K * c‖ * I ≤ ‖K * c‖ * ∫ y in a..b, g y := mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
      _ ≤ ‖K * c‖ * |∫ y in a..b, g y| := mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
      _ = ‖v b - v a‖ := by rw [h1, hint, norm_mul (K * c) _, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖v b‖ + ‖v a‖ := norm_sub_le _ _
  have hw2 : (0:ℝ) < (w:ℝ) / 2 := by
    have : (1:ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have h0 : Tendsto (fun a => ‖v a‖) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun a : ℝ => C * a ^ ((w:ℝ)/2) * Real.exp (-α * a)) (𝓝[>] 0) (𝓝 0) := by
      have hca : ContinuousAt (fun a : ℝ => C * a ^ ((w:ℝ)/2) * Real.exp (-α * a)) 0 := by
        apply ContinuousAt.mul
        · exact ContinuousAt.mul continuousAt_const (Real.continuousAt_rpow_const _ _ (Or.inr hw2.le))
        · fun_prop
      have h := hca.tendsto
      simp only [Real.zero_rpow hw2.ne', mul_zero, zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hc
    filter_upwards [self_mem_nhdsWithin] with a ha using hbound a ha
  have hinf : Tendsto (fun b => ‖v b‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun b : ℝ => C * (b ^ ((w:ℝ)/2) * Real.exp (-α * b))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((w:ℝ)/2) α hα).const_mul C
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hc
    filter_upwards [eventually_gt_atTop 0] with b hb
    rw [← mul_assoc]; exact hbound b hb
  have step : ∀ b : ℝ, 2 ≤ b → ‖K * c‖ * I ≤ ‖v b‖ := by
    intro b hb
    have ht : Tendsto (fun a => ‖v b‖ + ‖v a‖) (𝓝[>] 0) (𝓝 (‖v b‖ + 0)) := tendsto_const_nhds.add h0
    rw [add_zero] at ht
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))] with a ha ha1
    exact key a b ha (le_of_lt ha1) hb
  have hle : ‖K * c‖ * I ≤ 0 :=
    ge_of_tendsto hinf (by filter_upwards [eventually_ge_atTop 2] with b hb using step b hb)
  have hKc : ‖K * c‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (K * c)]) (norm_nonneg _)
  rw [norm_eq_zero, mul_eq_zero] at hKc
  exact hKc.resolve_left hK

end GlobalTheory
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_exp_decay_of_integral_identity : ∀ (v : ℝ → ℂ) (K c : ℂ) (C α β : ℝ) (w : ℕ), 1 ≤ w → 0 < α → 0 < β → K ≠ 0 → (∀ y : ℝ, 0 < y → ‖v y‖ ≤ C * y ^ ((w : ℝ) / 2) * Real.exp (-α * y)) → (∀ a b : ℝ, 0 < a → a ≤ b → v b - v a = K * c * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) → c = 0 := by
  atlas_forward_decl GlobalTheory.ode_coeff_zero_of_decay_ends
end

section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerPositivity

theorem periodic_of_dbar : ∀ (U : ℂ → ℂ) (h : ℍ → ℂ) (w : ℕ) (T : ℝ), (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt U L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))) → (∀ s : ℂ, 0 < s.im → U (s + T) = U s) → ∀ s : ℂ, 0 < s.im → h (ofComplex (s + T)) = h (ofComplex s) := by
  intro U h w T hd hp s hs
  have hsT : 0 < (s + T).im := by simpa using hs
  obtain ⟨L0, hL0, e0⟩ := hd s hs
  obtain ⟨L1, hL1, e1⟩ := hd (s + T) hsT
  have hshift : HasFDerivAt (fun z : ℂ => U (z + T)) L1 s := by
    have := hL1.comp s ((hasFDerivAt_id (𝕜 := ℝ) s).add_const (T : ℂ))
    simpa [Function.comp_def] using this
  have hev : U =ᶠ[nhds s] fun z : ℂ => U (z + T) :=
    ((Complex.continuous_im.tendsto s).eventually (lt_mem_nhds hs)).mono fun z hz => (hp z hz).symm
  have hL : L0 = L1 := hL0.unique (hshift.congr_of_eventuallyEq hev)
  have hconj : (s + T) - (starRingEnd ℂ) (s + T) = s - (starRingEnd ℂ) s := by
    simp only [map_add, Complex.conj_ofReal]; ring
  have hne : 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w ≠ 0 := by
    have : s - (starRingEnd ℂ) s ≠ 0 := by
      rw [Complex.sub_conj]
      exact mul_ne_zero (by exact_mod_cast (by positivity : (2 * s.im) ≠ 0)) Complex.I_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (pow_ne_zero _ this)
  have key := e1
  rw [hconj, ← hL, e0] at key
  exact ((starRingEnd ℂ).injective (mul_left_cancel₀ hne key)).symm

theorem fourier_sub_eq : ∀ (U : ℂ → ℂ) (h : ℍ → ℂ) (w : ℕ) (T : ℝ) (n : ℕ) (a b : ℝ), 0 < T → 0 < a → a ≤ b → (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt U L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))) → (∀ s : ℂ, 0 < s.im → U (s + T) = U s) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, U ((x : ℂ) + (b : ℂ) * Complex.I) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (b : ℂ) * Complex.I) / T)) - (∫ x in (0 : ℝ)..T, U ((x : ℂ) + (a : ℂ) * Complex.I) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (a : ℂ) * Complex.I) / T)) = 2 * Complex.I * (2 * Complex.I) ^ w * T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  intro U h w T n a b hT ha hab hd hp hh hper hbdd
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  refine (GlobalTheory.T.green_formula_periodic_rectangle_upperHalfPlane (fun z => U z * Complex.exp (2 * Real.pi * Complex.I * n * z / T))
    (fun s => Complex.exp (2 * Real.pi * Complex.I * n * s / T) *
      (2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))))
    T a b hT ha hab ?_ ?_ ?_).trans ?_
  · intro s hs
    obtain ⟨L, hL, e⟩ := hd s hs
    have h1 : HasDerivAt (fun z : ℂ => 2 * Real.pi * Complex.I * n * z / T)
        (2 * Real.pi * Complex.I * n / T) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * Real.pi * Complex.I * n : ℂ)).div_const (T : ℂ)
    refine ⟨_, hL.mul (h1.cexp.hasFDerivAt.restrictScalars ℝ), ?_⟩
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    linear_combination (Complex.exp (2 * Real.pi * Complex.I * n * s / T)) * e
  · have hc : ContinuousOn (h ∘ ofComplex) {s : ℂ | 0 < s.im} :=
      (UpperHalfPlane.mdifferentiable_iff.1 hh).continuousOn
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) (ContinuousOn.mul
      (Continuous.continuousOn ?_) (Complex.continuous_conj.comp_continuousOn hc))
    exact continuous_const.mul ((continuous_id.sub Complex.continuous_conj).pow w)
  · intro s hs
    show U (s + T) * Complex.exp _ = U s * Complex.exp _
    rw [hp s hs]
    congr 1
    rw [show 2 * (Real.pi : ℂ) * Complex.I * n * (s + T) / T =
        2 * Real.pi * Complex.I * n * s / T + n * (2 * Real.pi * Complex.I) by field_simp,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · have inner : ∀ y ∈ Set.uIcc a b,
        (∫ x in (0 : ℝ)..T, Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) *
          (2 * Complex.I * (((x : ℂ) + (y : ℂ) * Complex.I) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I)) ^ w *
            (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))) =
        2 * Complex.I * (2 * Complex.I) ^ w * T * (starRingEnd ℂ) ((qExpansion T h).coeff n) *
          ((y : ℂ) ^ w * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ)) := by
      intro y hy
      have hy0 : 0 < y := by
        rw [Set.uIcc_of_le hab] at hy
        exact lt_of_lt_of_le ha hy.1
      have hpt : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I) =
          2 * Complex.I * y := by
        intro x
        rw [Complex.sub_conj]
        simp
        ring
      simp_rw [hpt]
      have hfun : (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) *
          (2 * Complex.I * (2 * Complex.I * (y : ℂ)) ^ w *
            (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))) =
          fun x : ℝ => (2 * Complex.I * (2 * Complex.I) ^ w * (y : ℂ) ^ w) *
            ((starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) *
              Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) := by
        funext x
        rw [mul_pow]
        ring
      rw [hfun, intervalIntegral.integral_const_mul, GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff h T n y hT hy0 hh hper hbdd]
      ring
    rw [intervalIntegral.integral_congr inner, intervalIntegral.integral_const_mul]

theorem cuspForm_eq_zero_of_periodic_of_bound : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)) (p : ℂ[X]) (h₀ : ℕ) (C : ℝ), 0 < h₀ → (∀ τ : ℍ, (eichler (k - 2) ⇑f ((h₀ : ℝ) +ᵥ τ) - (eichler (k - 2) ⇑h ((h₀ : ℝ) +ᵥ τ)).map (starRingEnd ℂ) - p).eval (((h₀ : ℝ) +ᵥ τ : ℍ) : ℂ) = (eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p).eval (τ : ℂ)) → (∀ τ : ℍ, ‖(eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p).eval (τ : ℂ)‖ ≤ C * τ.im ^ (((k : ℝ) - 2) / 2)) → h = 0 := by
  intro Γ k hfi hk f h p h₀ C hh₀ hper hbd
  have := hfi
  have hT : (0 : ℝ) < (h₀ : ℝ) := by exact_mod_cast hh₀
  have hcoe : ∀ z : ℂ, 0 < z.im → ((ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [ofComplex_apply_of_im_pos hz]
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑h) := ModularFormClass.holo h
  have hd := GlobalTheory.T.hasFDerivAt_eichler_sub_conj_wirtinger (k - 2) ⇑f ⇑h p (ModularFormClass.holo f) hholo
  have hUper : ∀ s : ℂ, 0 < s.im →
      (eichler (k - 2) ⇑f (ofComplex (s + ((h₀ : ℝ) : ℂ))) -
          (eichler (k - 2) ⇑h (ofComplex (s + ((h₀ : ℝ) : ℂ)))).map (starRingEnd ℂ) - p).eval
          (s + ((h₀ : ℝ) : ℂ)) =
        (eichler (k - 2) ⇑f (ofComplex s) - (eichler (k - 2) ⇑h (ofComplex s)).map (starRingEnd ℂ) - p).eval s := by
    intro s hs
    have hs' : 0 < (s + ((h₀ : ℝ) : ℂ)).im := by simpa using hs
    have e : ofComplex (s + ((h₀ : ℝ) : ℂ)) = ((h₀ : ℝ) +ᵥ ofComplex s) := by
      ext
      rw [UpperHalfPlane.coe_vadd, hcoe _ hs', hcoe _ hs]
      ring
    have key := hper (ofComplex s)
    rw [← e, hcoe _ hs', hcoe _ hs] at key
    exact key
  have hhper := periodic_of_dbar _ ⇑h (k - 2) (h₀ : ℝ) hd hUper
  have hperh : Function.Periodic (⇑h ∘ ofComplex) ((h₀ : ℝ) : ℂ) := by
    intro s
    by_cases hs : 0 < s.im
    · exact hhper s hs
    · rw [not_lt] at hs
      simp only [Function.comp_apply]
      rw [ofComplex_apply_eq_of_im_nonpos (by simpa using hs) hs]
  have hbdd : IsBoundedAtImInfty (⇑h) := ModularFormClass.bdd_at_infty h
  have hzero : IsZeroAtImInfty (⇑h) := CuspFormClass.zero_at_infty h
  have hq : qExpansion (h₀ : ℝ) ⇑h = 0 := by
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    rcases n with _ | n
    · rw [qExpansion_coeff_zero hT (analyticAt_cuspFunction_zero hT hperh hholo hbdd) hperh,
        hzero.valueAtInfty_eq_zero]
    · have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hα : 0 < 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ) := by positivity
      have hβ : 0 < 4 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ) := by positivity
      have hK : 2 * Complex.I * (2 * Complex.I) ^ (k - 2) * ((h₀ : ℝ) : ℂ) ≠ 0 := by
        have : ((h₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
          (pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero))) this
      have hw1 : 1 ≤ k - 2 := by omega
      have hwR : (((k - 2 : ℕ) : ℝ)) = (k : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hbound : ∀ y : ℝ, 0 < y →
          ‖∫ x in (0 : ℝ)..(h₀ : ℝ),
              (eichler (k - 2) ⇑f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
                (eichler (k - 2) ⇑h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).map (starRingEnd ℂ) - p).eval
                ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) / ((h₀ : ℝ) : ℂ))‖ ≤
            (C * (h₀ : ℝ)) * y ^ ((((k - 2 : ℕ) : ℝ)) / 2) *
              Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y) := by
        intro y hy
        have hpt : ∀ x : ℝ,
            ‖(eichler (k - 2) ⇑f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
                (eichler (k - 2) ⇑h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).map (starRingEnd ℂ) - p).eval
                ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) / ((h₀ : ℝ) : ℂ))‖ ≤
            C * y ^ ((((k - 2 : ℕ) : ℝ)) / 2) * Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y) := by
          intro x
          have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
          have hb := hbd (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))
          rw [hcoe _ hz] at hb
          have him : (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
            rw [← UpperHalfPlane.coe_im, hcoe _ hz]
            simp
          rw [him, ← hwR] at hb
          rw [norm_mul, Complex.norm_exp]
          have hre : (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) /
              ((h₀ : ℝ) : ℂ)).re = -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y := by
            rw [Complex.div_ofReal_re]
            simp
            ring
          rw [hre]
          exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (h₀ : ℝ))
          (fun x _ => hpt x)
        rw [sub_zero, abs_of_pos hT] at this
        calc _ ≤ _ := this
          _ = _ := by ring
      have hc := GlobalTheory.T.coeff_eq_zero_of_exp_decay_of_integral_identity _ (2 * Complex.I * (2 * Complex.I) ^ (k - 2) * ((h₀ : ℝ) : ℂ))
        ((starRingEnd ℂ) ((qExpansion (h₀ : ℝ) ⇑h).coeff (n + 1)))
        (C * (h₀ : ℝ)) _ (4 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) (k - 2) hw1 hα hβ hK hbound
        (fun a b ha hab => fourier_sub_eq _ ⇑h (k - 2) (h₀ : ℝ) (n + 1) a b hT ha hab hd hUper
          hholo hperh hbdd)
      simpa using hc
  have hfun : (⇑h : ℍ → ℂ) = 0 := (qExpansion_eq_zero_iff hT hperh hholo hbdd).1 hq
  ext τ
  simpa using congrFun hfun τ

end GlobalTheory.EichlerPositivity
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Positivity

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eichler_mem_degreeLT_succ (w : ℕ) (g : ℍ → ℂ) (τ : ℍ) :
    _root_.GlobalTheory.HeckeFamilyMatrices.eichler w g τ ∈ ℂ[X]_(w + 1) := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [_root_.GlobalTheory.EichlerChange.coeff_eichler, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma map_conj_mem_degreeLT {n : ℕ} {p : ℂ[X]} (hp : p ∈ ℂ[X]_n) :
    p.map (starRingEnd ℂ) ∈ ℂ[X]_n := by
  rw [Polynomial.mem_degreeLT] at hp ⊢
  rwa [Polynomial.degree_map]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma sl_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  simpa [UpperHalfPlane.denom] using h

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eval_eq_denom_pow_mul_eval_of_slP_invariant (w : ℕ) (V : ℍ → ℂ[X]) (γ : SL(2, ℤ)) (τ : ℍ)
    (hmem : V (γ • τ) ∈ ℂ[X]_(w + 1))
    (hrel : _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ) :
    eval (τ : ℂ) (V τ) =
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * eval ((γ • τ : ℍ) : ℂ) (V (γ • τ)) := by
  rw [← hrel, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ _ hmem (sl_denom_ne_zero γ τ)]
  congr 2
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [_root_.GlobalTheory.HeckeFamilyMatrices.mat]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma im_sl_smul_eq_im_div_normSq_denom (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ • τ).im = τ.im / Complex.normSq (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [ModularGroup.sl_moeb, UpperHalfPlane.im_smul_eq_div_normSq]
  simp [UpperHalfPlane.denom]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma continuous_eval_of_continuous_coeff_of_degree_le (w : ℕ) (V : ℍ → ℂ[X])
    (hmem : ∀ τ, V τ ∈ ℂ[X]_(w + 1)) (hc : ∀ n, Continuous fun τ => (V τ).coeff n) :
    Continuous fun τ : ℍ => eval (τ : ℂ) (V τ) := by
  have h : (fun τ : ℍ => eval (τ : ℂ) (V τ)) =
      fun τ => ∑ i ∈ Finset.range (w + 1), (V τ).coeff i * (τ : ℂ) ^ i := by
    funext τ
    apply eval_eq_sum_range'
    by_cases h0 : V τ = 0
    · simp [h0]
    · have := hmem τ
      rw [mem_degreeLT] at this
      exact (natDegree_lt_iff_degree_lt h0).2 this
  rw [h]
  exact continuous_finset_sum _ fun i _ => (hc i).mul (continuous_coe.pow i)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma exists_norm_eval_le_mul_im_rpow_of_slP_invariant (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (w : ℕ)
    (V : ℍ → ℂ[X]) (hmem : ∀ τ, V τ ∈ ℂ[X]_(w + 1))
    (hc : ∀ n, Continuous fun τ => (V τ).coeff n)
    (hrel : ∀ γ ∈ Γ, ∀ τ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ)
    (hdecay : ∀ g : SL(2, ℤ), Filter.Tendsto
      (fun τ => ‖eval ((g • τ : ℍ) : ℂ) (V (g • τ))‖ * (g • τ).im ^ (-(w : ℝ) / 2))
      atImInfty (nhds 0)) :
    ∃ C, ∀ τ : ℍ, ‖eval (τ : ℂ) (V τ)‖ ≤ C * τ.im ^ ((w : ℝ) / 2) := by
  have hinv : ∀ γ ∈ Γ, ∀ τ : ℍ,
      ‖eval ((γ • τ : ℍ) : ℂ) (V (γ • τ))‖ * (γ • τ).im ^ (-(w : ℝ) / 2) =
        ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
    intro γ hγ τ
    have he := eval_eq_denom_pow_mul_eval_of_slP_invariant w V γ τ (hmem _) (hrel γ hγ τ)
    have hD := sl_denom_ne_zero γ τ
    set D := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hDdef
    have hDpos : 0 < ‖D‖ := norm_pos_iff.2 hD
    have hx : (‖D‖ ^ (2 : ℕ)) ^ (-(w : ℝ) / 2) = (‖D‖ ^ w)⁻¹ := by
      rw [← Real.rpow_natCast ‖D‖ 2, ← Real.rpow_mul (norm_nonneg _),
        show ((2 : ℕ) : ℝ) * (-(w : ℝ) / 2) = -(w : ℝ) by push_cast; ring,
        Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    rw [he, im_sl_smul_eq_im_div_normSq_denom, ← hDdef, Real.div_rpow τ.im_pos.le (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq, hx, norm_mul, norm_pow]
    have hw : 0 < ‖D‖ ^ w := pow_pos hDpos w
    field_simp
  obtain ⟨C, hC⟩ := ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO
    (f := fun τ : ℍ => ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2))
    (((continuous_eval_of_continuous_coeff_of_degree_le w V hmem hc).norm).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ => Or.inl τ.im_pos.ne'))
    le_rfl (fun g => by simpa using (hdecay g).isBigO_one ℝ) (Γ := Γ) hinv
  refine ⟨C, fun τ => ?_⟩
  have h1 := hC τ
  rw [Real.rpow_zero, mul_one, Real.norm_of_nonneg (by positivity)] at h1
  have hpos : 0 < τ.im ^ ((w : ℝ) / 2) := Real.rpow_pos_of_pos τ.im_pos _
  calc ‖eval (τ : ℂ) (V τ)‖
      = ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2) * τ.im ^ ((w : ℝ) / 2) := by
        rw [mul_assoc, ← Real.rpow_add τ.im_pos]
        simp [neg_div]
    _ ≤ C * τ.im ^ ((w : ℝ) / 2) := mul_le_mul_of_nonneg_right h1 hpos.le

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eq_zero_of_eichler_conj_slash_relation (Γ : Subgroup SL(2, ℤ)) (k : ℕ)
    (hΓ : Γ.FiniteIndex) (hk : 3 ≤ k)
    (f h : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k) (p : ℂ[X])
    (hp : p ∈ ℂ[X]_(k - 1))
    (hrel : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ)) - p) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - p) :
    h = 0 := by
  set V : ℍ → ℂ[X] := fun τ => _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
    map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - p with hV
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have hp' : p ∈ ℂ[X]_(k - 2 + 1) := by rw [← hk1]; exact hp
  have hmem : ∀ τ, V τ ∈ ℂ[X]_(k - 2 + 1) := fun τ =>
    sub_mem (sub_mem (eichler_mem_degreeLT_succ _ _ _)
      (map_conj_mem_degreeLT (eichler_mem_degreeLT_succ _ _ _))) hp'
  have hcf : ∀ g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k, ∀ n : ℕ,
      Continuous fun τ => (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ).coeff n := by
    intro g n
    simp_rw [_root_.GlobalTheory.EichlerChange.coeff_eichler]
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun τ => ?_)
    exact ((_root_.GlobalTheory.EichlerChange.hasDerivAt_ecoef (k - 2) g (CuspFormClass.holo g) n τ
      τ.im_pos).continuousAt).comp continuous_coe.continuousAt
  have hc : ∀ n, Continuous fun τ => (V τ).coeff n := by
    intro n
    simp only [hV, coeff_sub, coeff_map]
    exact ((hcf f n).sub (Complex.continuous_conj.comp (hcf h n))).sub continuous_const
  have hrel' : ∀ γ ∈ Γ, ∀ τ,
      _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ :=
    fun γ hγ τ => hrel ⟨γ, hγ⟩ τ
  have hdecay := _root_.GlobalTheory.HeckeFamilyMatrices.Decay.decay_at_cusp Γ k hΓ hk f h p hp hrel
  have hw : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  obtain ⟨C, hC⟩ := exists_norm_eval_le_mul_im_rpow_of_slP_invariant Γ (k - 2) V hmem hc hrel'
    (by rw [hw]; exact hdecay)
  obtain ⟨n, hn, -, hTn⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero ModularGroup.T
  refine _root_.GlobalTheory.EichlerPositivity.cuspForm_eq_zero_of_periodic_of_bound Γ k hΓ hk f h p n C hn (fun τ => ?_)
    (fun τ => by rw [← hw]; exact hC τ)
  have hT : ModularGroup.T ^ n • τ = (n : ℝ) +ᵥ τ := by
    rw [← zpow_natCast, modular_T_zpow_smul]; simp
  have he := eval_eq_denom_pow_mul_eval_of_slP_invariant (k - 2) V (ModularGroup.T ^ n) τ (hmem _) (hrel' _ hTn τ)
  have h10 : ((ModularGroup.T ^ n) 1 0 : ℤ) = 0 ∧ ((ModularGroup.T ^ n) 1 1 : ℤ) = 1 := by
    rw [← zpow_natCast, ModularGroup.coe_T_zpow]; simp
  rw [h10.1, h10.2] at he
  simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_one, one_pow, one_mul, hT] at he
  exact he.symm

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in

theorem _root_.GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N →
    Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)),
    _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑f - _root_.GlobalTheory.HeckeFamilyMatrices.cj (_root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑h) ∈
      _root_.GlobalTheory.HeckeFamilyMatrices.B1 Γ (k - 2) → f = 0 ∧ h = 0 := by
  intro N Γ k _ _ hΓ hk f h hB
  unfold _root_.GlobalTheory.HeckeFamilyMatrices.B1 at hB
  obtain ⟨⟨q, hq⟩, hqe⟩ := hB
  have hcoc : ∀ γ : Γ, _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) q - q =
      _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑f γ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑h γ) := fun γ => by
    have := congrFun hqe γ
    simpa [_root_.GlobalTheory.HeckeFamilyMatrices.cj] using this
  have hper : ∀ g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k,
      ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑g γ =
        _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
            (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g (γ • τ)) -
          _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ := fun g =>
    (_root_.GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub Γ k (by omega) (CuspForm.toModularFormₗ g)).2
  have hmemE : ∀ (g : ℍ → ℂ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ ∈ ℂ[X]_(k - 2 + 1) :=
    fun g τ => eichler_mem_degreeLT_succ _ _ _
  have hconj : ∀ p ∈ ℂ[X]_(k - 2 + 1), ∀ γ : SL(2, ℤ),
      map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) p) =
        _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (map (starRingEnd ℂ) p) :=
    fun p hp γ =>
      (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) 1 p hp).2.2.2
  have hcc : ∀ p : ℂ[X], map (starRingEnd ℂ) (map (starRingEnd ℂ) p) = p := fun p => by
    ext n; simp [coeff_map]
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have rel1 : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ)) - q) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - q := by
    intro γ τ
    have h1 := hcoc γ
    rw [hper f γ τ, hper h γ τ, Polynomial.map_sub, hconj _ (hmemE _ _)] at h1
    rw [map_sub, map_sub]
    linear_combination -h1
  have rel2 : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) - -map (starRingEnd ℂ) q) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ) - -map (starRingEnd ℂ) q := by
    intro γ τ
    have h2 := congrArg (map (starRingEnd ℂ)) (rel1 γ τ)
    rw [hconj _ (sub_mem (sub_mem (hmemE _ _) (map_conj_mem_degreeLT (hmemE _ _))) hq)] at h2
    simp only [Polynomial.map_sub, hcc] at h2
    have hneg : _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) - -map (starRingEnd ℂ) q =
        -(map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) -
          _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) - map (starRingEnd ℂ) q) := by ring
    rw [hneg, map_neg, h2]
    ring
  have hq' : q ∈ ℂ[X]_(k - 1) := by rw [hk1]; exact hq
  exact ⟨eq_zero_of_eichler_conj_slash_relation Γ k hΓ hk h f _
      (neg_mem (map_conj_mem_degreeLT hq')) rel2,
    eq_zero_of_eichler_conj_slash_relation Γ k hΓ hk f h q hq' rel1⟩

end GlobalTheory.HeckeFamilyMatrices.Positivity
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)), per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) → f = 0 ∧ h = 0 := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem
end
