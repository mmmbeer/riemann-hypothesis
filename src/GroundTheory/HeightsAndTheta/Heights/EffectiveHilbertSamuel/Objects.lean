import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

theorem log_add_log_two_pi_le : log 280 + log (2 * π) ≤ 7.6 := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_gt_three
  rw [← Real.log_mul (by norm_num) (by positivity)]
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hsplit : exp 7.6 = exp 1 ^ 7 * exp 0.6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [hsplit]
  have h7 : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 7
  have h06 : (1 + 0.6 + 0.6 ^ 2 / 2 : ℝ) ≤ exp 0.6 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hpos : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 7 := by positivity
  calc 280 * (2 * π) ≤ (2.7182818283 : ℝ) ^ 7 * (1 + 0.6 + 0.6 ^ 2 / 2) := by
        norm_num; nlinarith
    _ ≤ exp 1 ^ 7 * exp 0.6 :=
        mul_le_mul h7 h06 (by norm_num) (by positivity)

theorem log_two_pi_le : log (2 * π) ≤ 7.6 := by
  have h := log_add_log_two_pi_le
  have h280 : 0 ≤ log (280 : ℝ) := Real.log_nonneg (by norm_num)
  linarith

theorem half_log_add_le (D : ℝ) (hD : 1 ≤ D) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D := by
  have h1 := log_add_log_two_pi_le
  have h2 := log_two_pi_le
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ D - 1)]

theorem seven_point_six_le_log (ρ : ℝ) (hρ : 2 ^ 26 ≤ ρ) : 7.6 ≤ log ρ := by
  have h : log ((2 : ℝ) ^ 26) ≤ log ρ := Real.log_le_log (by positivity) hρ
  rw [Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

theorem three_point_eight_le_half_log (D ρ : ℝ) (hD : 0 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    3.8 * D ≤ (D / 2) * log ρ := by
  have h := seven_point_six_le_log ρ hρ
  nlinarith [mul_le_mul_of_nonneg_left h hD]

theorem half_log_add_le_half_log (D ρ : ℝ) (hD : 1 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D ∧ 3.8 * D ≤ (D / 2) * log ρ :=
  ⟨half_log_add_le D hD, three_point_eight_le_half_log D ρ (by linarith) hρ⟩

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace EffectiveHS

open Finset

structure MulTower (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] where

  W : Submodule R A

  V : ℕ → Submodule R A

  mul_mem : ∀ j, ∀ w ∈ W, ∀ f ∈ V j, w * f ∈ V (j + 1)

def mono {A : Type*} [CommRing A] {D : ℕ} (s : Fin D → A) (α : Fin D → ℕ) : A :=
  ∏ i, s i ^ α i

namespace MulTower

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)

def Raises (k : ℕ) (x : A) : Prop := ∀ j, ∀ f ∈ τ.V j, x * f ∈ τ.V (j + k)

theorem raises_one : τ.Raises 0 1 := by
  intro j f hf
  simpa using hf

theorem raises_of_mem {w : A} (hw : w ∈ τ.W) : τ.Raises 1 w :=
  fun j f hf => τ.mul_mem j w hw f hf

theorem Raises.mul {τ : MulTower R A} {k l : ℕ} {x y : A} (hx : τ.Raises k x)
    (hy : τ.Raises l y) : τ.Raises (k + l) (x * y) := by
  intro j f hf
  have e : j + (k + l) = j + l + k := by omega
  rw [e, mul_assoc]
  exact hx _ _ (hy j f hf)

theorem Raises.pow {τ : MulTower R A} {k : ℕ} {x : A} (hx : τ.Raises k x) (n : ℕ) :
    τ.Raises (k * n) (x ^ n) := by
  induction n with
  | zero => simpa using τ.raises_one
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact ih.mul hx

theorem raises_prod {ι : Type*} (t : Finset ι) (k : ι → ℕ) (x : ι → A)
    (h : ∀ i ∈ t, τ.Raises (k i) (x i)) : τ.Raises (∑ i ∈ t, k i) (∏ i ∈ t, x i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using τ.raises_one
  | insert a t ha ih =>
    rw [sum_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a t)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem raises_mono {D : ℕ} {s : Fin D → A} (hs : ∀ i, s i ∈ τ.W) (α : Fin D → ℕ) :
    τ.Raises (∑ i, α i) (mono s α) := by
  have h := τ.raises_prod univ (fun i => 1 * α i) (fun i => s i ^ α i)
    (fun i _ => (τ.raises_of_mem (hs i)).pow (α i))
  simpa [mono] using h

theorem raises_prod_alt {k : ℕ} (w : Fin k → A) (hw : ∀ i, w i ∈ τ.W) :
    τ.Raises k (∏ i, w i) := by
  have h := τ.raises_prod univ (fun _ => 1) w (fun i _ => τ.raises_of_mem (hw i))
  simpa using h

def P (D T : ℕ) (s : Fin D → A) : Submodule R A :=
  Submodule.span R {F | ∃ α : Fin D → ℕ, ∃ h ∈ τ.V D, ∑ i, α i = T - D ∧ F = mono s α * h}

def Vpp (D T a₀ : ℕ) (s : Fin D → A) : Submodule R A :=
  Submodule.span R {F | ∃ (α : Fin D → ℕ) (k : ℕ) (w : Fin k → A) (m : A),
      (∀ i, w i ∈ τ.W) ∧ m ∈ τ.V 0 ∧ ∑ i, α i + k = T ∧ ∑ i, α i ≤ a₀ ∧
        F = mono s α * (∏ i, w i) * m} ⊔ τ.P D T s

variable {D : ℕ} {s : Fin D → A}

theorem gen_mem (hs : ∀ i, s i ∈ τ.W) {T : ℕ} (α : Fin D → ℕ) {k : ℕ} (w : Fin k → A)
    (hw : ∀ i, w i ∈ τ.W) {m : A} (hm : m ∈ τ.V 0) (hT : ∑ i, α i + k = T) :
    mono s α * (∏ i, w i) * m ∈ τ.V T := by
  have h := ((τ.raises_mono hs α).mul (τ.raises_prod_alt w hw)) 0 m hm
  rwa [zero_add, hT] at h


theorem P_le (hs : ∀ i, s i ∈ τ.W) {T : ℕ} (hDT : D ≤ T) : τ.P D T s ≤ τ.V T := by
  rw [P, Submodule.span_le]
  rintro F ⟨α, h, hh, hα, rfl⟩
  have h' := τ.raises_mono hs α D h hh
  rwa [hα, Nat.add_sub_cancel' hDT] at h'


end MulTower

noncomputable def polyTower : MulTower ℚ (MvPolynomial (Fin 2) ℚ) where
  W := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 1
  V j := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ j
  mul_mem j w hw f hf := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hw hf ⊢
    have h := hw.mul hf
    rwa [add_comm] at h


section Lift

open MeasureTheory


noncomputable def cD (D : ℕ) : ℝ := 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial

theorem cD_pos (D : ℕ) : 0 < cD D := by
  unfold cD
  have := Real.pi_pos
  positivity

theorem cD_le (D : ℕ) : cD D ≤ 2 * (2 * Real.pi) ^ D := by
  unfold cD
  have h1 : (1 : ℝ) ≤ (D - 1).factorial := by exact_mod_cast Nat.factorial_pos (D - 1)
  have h0 : (0 : ℝ) ≤ 2 ^ (D + 1) * Real.pi ^ D := by have := Real.pi_pos; positivity
  calc 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial ≤ 2 ^ (D + 1) * Real.pi ^ D :=
        div_le_self h0 h1
    _ = 2 * (2 * Real.pi) ^ D := by rw [mul_pow, pow_succ]; ring


end Lift

open Real in

theorem lift_constants_le (D : ℕ) (hD : 1 ≤ D) (ρ ρ₁ T C : ℝ) (hρ : 2 ^ 26 ≤ ρ)
    (hDρ : (D : ℝ) ≤ ρ) (h1 : 1 ≤ ρ₁) (h1ρ : ρ₁ ≤ ρ) (hT : 1 ≤ T) (hC : 26 ≤ C) :
    2 * D * log ρ₁ + D * log (Real.sqrt D * ρ₁) + (1 / 2) * log (140 * cD D * T ^ D) ≤
        4 * D * log (ρ * T) ∧
      4 * D * log (ρ * T) ≤ C * D ^ 2 * log (ρ * T) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le one_pos h1
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hlogT : 0 ≤ log T := log_nonneg hT
  have hlogρ₁ : log ρ₁ ≤ log ρ := log_le_log hρ₁0 h1ρ
  have hlogD : log D ≤ log ρ := log_le_log (by linarith) hDρ
  have hlogD0 : 0 ≤ log (D : ℝ) := log_nonneg hD'
  have hlogρ₁0 : 0 ≤ log ρ₁ := log_nonneg h1
  obtain ⟨hc1, hc2⟩ := half_log_add_le_half_log (D : ℝ) ρ hD' hρ
  have hcD := cD_pos D
  have hcDle : log (cD D) ≤ log 2 + D * log (2 * π) := by
    have h := log_le_log hcD (cD_le D)
    rwa [log_mul (by norm_num) (by positivity), log_pow] at h
  have hsplit : log (140 * cD D * T ^ D) = log 140 + log (cD D) + D * log T := by
    rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) hcD.ne', log_pow]
  have h280 : log 280 = log 140 + log 2 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have hsq : log (Real.sqrt D * ρ₁) = log D / 2 + log ρ₁ := by
    rw [log_mul (by positivity) hρ₁0.ne', log_sqrt (by positivity)]
  have hρT : log (ρ * T) = log ρ + log T := log_mul hρ0.ne' hT0.ne'
  have hlogρ : 0 ≤ log ρ := log_nonneg (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hsplit, hsq, hρT]
    have e1 : (D : ℝ) * log ρ₁ ≤ D * log ρ := mul_le_mul_of_nonneg_left hlogρ₁ (by linarith)
    have e2 : (D : ℝ) * log D ≤ D * log ρ := mul_le_mul_of_nonneg_left hlogD (by linarith)
    have e3 : (D : ℝ) * log T ≥ 0 := mul_nonneg (by linarith) hlogT
    nlinarith
  · rw [hρT]
    have hL : 0 ≤ log ρ + log T := by linarith
    have hDD : 4 * (D : ℝ) ≤ C * D ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hDD hL

end EffectiveHS

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

variable {D : ℕ} {U : Type} [TopologicalSpace U]

def jac (A : FinHolAtlas D U) (j k : Fin A.n) (x : U) : ℂ :=
  LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) (A.chart j x) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))

def topSections (A : FinHolAtlas D U) (L₂ L : HolLineBundle A) (m : ℕ) :
    Submodule ℂ (Fin A.n → U → ℂ) where
  carrier := {u | (∀ j, A.HoloOn (A.chart j).source (u j)) ∧
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
      u j x = jac A j k x * L₂.g j k x * L.g j k x ^ m * u k x) ∧
    ∀ j, ∀ x ∉ (A.chart j).source, u j x = 0}
  add_mem' := by
    rintro f f' ⟨hf, hc, hz⟩ ⟨hf', hc', hz'⟩
    refine ⟨fun j k => (hf j k).add (hf' j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.add_apply, hc j k x hx, hc' j k x hx]; ring
    · simp [hz j x hx, hz' j x hx]
  zero_mem' := by
    refine ⟨fun j k => ?_, fun j k x _ => by simp, fun j x _ => rfl⟩
    exact analyticOnNhd_const
  smul_mem' := by
    rintro c f ⟨hf, hc, hz⟩
    refine ⟨fun j k => analyticOnNhd_const.mul (hf j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hc j k x hx]; ring
    · simp [hz j x hx]

def piece (A : FinHolAtlas D U) (j : Fin A.n) : Set (Fin D → ℂ) :=
  {y | y ∈ (A.chart j).target ∧ ∀ k < j, (A.chart j).symm y ∉ (A.chart k).source}

def chartIntegral (A : FinHolAtlas D U) (f : Fin A.n → U → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, ∫⁻ y in piece A j, f j ((A.chart j).symm y)

def topNormSq (A : FinHolAtlas D U) (ψ : Fin A.n → U → ℝ) (F : Fin A.n → U → ℂ) : ℝ≥0∞ :=
  chartIntegral A fun j x => ENNReal.ofReal (2 ^ D * ‖F j x‖ ^ 2 * Real.exp (-ψ j x))

def fsWeight {N : ℕ} {A : FinHolAtlas D U} (e : Fin N → Fin A.n → U → ℂ) (j : Fin A.n) (x : U) :
    ℝ :=
  Real.log (∑ i, ‖e i j x‖ ^ 2)

def NoCommonZero {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ) : Prop :=
  ∀ x, ∃ i, e i (chartIdx A x) x ≠ 0

def lin {N : ℕ} {A : FinHolAtlas D U} (e : Fin N → Fin A.n → U → ℂ) (c : Fin N → ℂ) :
    Fin A.n → U → ℂ :=
  ∑ k, c k • e k

def zeroSet (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) : Set U :=
  {x | ∀ i, s i (chartIdx A x) x = 0}

def sJacMap (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (c : Fin A.n) (x : U) :
    (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) :=
  fderiv ℂ (fun z i => s i c ((A.chart c).symm z)) (A.chart c x)

def sJac (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (c : Fin A.n) (x : U) : ℂ :=
  LinearMap.det (sJacMap A s c x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))

def IsNondeg (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) : Prop :=
  ∀ x ∈ zeroSet A s, sJac A s (chartIdx A x) x ≠ 0

def res (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (F : Fin A.n → U → ℂ) (x : U) : ℂ :=
  F (chartIdx A x) x / sJac A s (chartIdx A x) x

def sNormSq (A : FinHolAtlas D U) (S : Set U) (ψ : Fin A.n → U → ℝ) (g : U → ℂ) : ℝ :=
  ∑ᶠ x ∈ S, ‖g x‖ ^ 2 * Real.exp (-ψ (chartIdx A x) x)

def FLBound {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ)
    (s : Fin D → Fin A.n → U → ℂ) : Prop :=
  ∀ V : Set U, IsOpen V → zeroSet A s ⊆ V → ∃ C : ℝ, ∀ x ∉ V,
    ∑ k, ‖e k (chartIdx A x) x‖ ^ 2 ≤ C * ∑ i, ‖s i (chartIdx A x) x‖ ^ 2

def IsAlgCover (A : FinHolAtlas D U) : Prop :=
  ∃ (MS : Set U) (z : U → Fin D → ℂ) (Δ : MvPolynomial (Fin D) ℂ), IsOpen MS ∧ Δ ≠ 0 ∧
    (∀ i, A.HoloOn MS fun x => z x i) ∧
    (∀ x ∈ MS, MvPolynomial.eval (z x) Δ ≠ 0) ∧
    IsCoveringMapOn (fun p : MS => z p) {y | MvPolynomial.eval y Δ ≠ 0} ∧
    (∀ y, MvPolynomial.eval y Δ ≠ 0 → ((fun p : MS => z p) ⁻¹' {y}).Finite) ∧
    ∀ j, ∃ f : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ f (A.chart j).target ∧
      interior {y | y ∈ (A.chart j).target ∧ f y = 0} = ∅ ∧
      ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ MS → f y = 0

structure TwistWeight (A : FinHolAtlas D U) (L₂ L : HolLineBundle A) (m : ℕ) where

  φ : Fin A.n → U → ℝ
  smooth : ∀ j, A.SmoothOn (A.chart j).source (φ j)
  compat : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L₂.g j k x‖ ^ 2) + m * Real.log (‖L.g j k x‖ ^ 2)
  psh : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w : Fin D → ℂ, 0 ≤ levi (φ j ∘ (A.chart j).symm) y w

def Vnat (A : FinHolAtlas D U) (L₂ L : HolLineBundle A) (φA φ : Fin A.n → U → ℝ) (j : ℕ) :
    Set (Fin A.n → U → ℂ) :=
  {F | F ∈ topSections A L₂ L (D + j) ∧ topNormSq A (fun k x => φA k x + j * φ k x) F < ⊤}

def IsFil (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (F : Fin A.n → U → ℂ) (a : ℕ) :
    Prop :=
  ∀ x ∈ zeroSet A s, ∀ k < a, iteratedFDeriv ℂ k (F (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm)
    (A.chart (chartIdx A x) x) = 0

def SymEq (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (F : Fin A.n → U → ℂ) (a : ℕ)
    (g : (Fin D → ℕ) → U → ℂ) : Prop :=
  ∀ x ∈ zeroSet A s, ∀ w : Fin D → ℂ,
    iteratedFDeriv ℂ a (F (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm)
        (A.chart (chartIdx A x) x) (fun _ => w) / (a.factorial : ℂ) =
      sJac A s (chartIdx A x) x * ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        (∏ i, (sJacMap A s (chartIdx A x) x w i) ^ α i) * g α x

def sPow {A : FinHolAtlas D U} (s : Fin D → Fin A.n → U → ℂ) (α : Fin D → ℕ) :
    Fin A.n → U → ℂ :=
  ∏ i, s i ^ α i

def Pspace {A : FinHolAtlas D U} (s : Fin D → Fin A.n → U → ℂ)
    (VD : Submodule ℂ (Fin A.n → U → ℂ)) (T : ℕ) : Submodule ℂ (Fin A.n → U → ℂ) :=
  Submodule.span ℂ {F | ∃ α ∈ Finset.Nat.antidiagonalTuple D (T - D), ∃ h ∈ VD, F = sPow s α * h}

def Vpp {N : ℕ} {A : FinHolAtlas D U} (e : Fin N → Fin A.n → U → ℂ)
    (s : Fin D → Fin A.n → U → ℂ) (V₀ VD : Submodule ℂ (Fin A.n → U → ℂ)) (T : ℕ) :
    Submodule ℂ (Fin A.n → U → ℂ) :=
  Submodule.span ℂ {F | ∃ (α : Fin D → ℕ) (j : ℕ) (ι : Fin j → Fin N), ∃ m ∈ V₀,
      ∑ i, α i + j = T ∧ ∑ i, α i ≤ T - D - 1 ∧ F = sPow s α * (∏ l, e (ι l)) * m} ⊔
    Pspace s VD T

def rSq {N : ℕ} (c : Fin D → Fin N → ℂ) : ℝ := ∑ i, ∑ k, ‖c i k‖ ^ 2

def wtNormSq {N : ℕ} (A : FinHolAtlas D U) (c : Fin D → Fin N → ℂ) (S : Set U)
    (ψ : Fin A.n → U → ℝ) (a : ℕ) (g : (Fin D → ℕ) → U → ℂ) : ℝ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple D a, (∏ i, (∑ k, ‖c i k‖ ^ 2) ^ α i) * sNormSq A S ψ (g α)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end
