import Formalism.StatementU
import Formalism.DefsOC
import Formalism.ZetaRealNonvanish
import Formalism.ZetaNonvanishing.MellinSgen
import Formalism.ZetaNonvanishing.ZetaRealNonvanish

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

section SlopeTestRemainingChoices

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma Pfun_eq_of_ne {s : ℂ} (hs : s ≠ 1) :
    Pfun χ s = (s - 1) * riemannZeta s * DirichletCharacter.LFunction χ s := by
  simp [Pfun, hs]

lemma Pfun_one : Pfun χ 1 = DirichletCharacter.LFunction χ 1 := by simp [Pfun]

lemma Pfun_ne_zero_of_one_le_re (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : Pfun χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1
    rw [Pfun_one]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  · rw [Pfun_eq_of_ne χ h1]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs))
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs)

lemma deriv_Pfun_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv (Pfun χ) s = riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * deriv riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s := by
  have heq : Pfun χ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact Pfun_eq_of_ne χ hz
  rw [heq.deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z)
      ((1 * riemannZeta s + (s - 1) * deriv riemannZeta s) * DirichletCharacter.LFunction χ s +
        (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s) s :=
    (((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt).mul
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).hasDerivAt
  rw [h.deriv]
  ring

lemma LSeries_LamF_eq (hχ : χ ≠ 1) (h4 : LSeriesLamF) (hreal : ∀ n : ℕ, (χ n).im = 0)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (LamF χ n : ℂ)) s = -deriv (Pfun χ) s / Pfun χ s + 1 / (s - 1) := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hre : 1 ≤ s.re := hs.le
  have hz := riemannZeta_ne_zero_of_one_le_re hre
  have hL := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [h4 N χ hreal s hs, deriv_Pfun_of_ne χ hs1, Pfun_eq_of_ne χ hs1]
  field_simp
  ring

end SlopeTestRemainingChoices

section Mellin

lemma cint_of_abs (f : ℝ → ℝ) (hf : Measurable f) (s : ℂ)
    (hI : IntegrableOn (fun x : ℝ => |f x| * x ^ (-s.re - 1)) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  refine Integrable.mono' hI ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hf).mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp

lemma rint_of_abs (f : ℝ → ℝ) (hf : Measurable f) (σ : ℝ)
    (hI : IntegrableOn (fun x : ℝ => |f x| * x ^ (-σ - 1)) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => f x * x ^ (-σ - 1)) (Ioi 1) := by
  refine Integrable.mono' hI ((hf.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]

lemma int_abs_rpow (h5 : MellinElem) {a σ : ℝ} (h : a < σ) :
    IntegrableOn (fun x : ℝ => |x ^ a| * x ^ (-σ - 1)) (Ioi 1) := by
  refine (h5.1 a σ h).congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
  simp only [abs_of_nonneg (Real.rpow_nonneg hx0.le a)]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma mellin_H (h3 : MellinS) (h5 : MellinElem) (σ₀ C : ℝ) {s : ℂ} (hs : 1 < s.re)
    (hσ₀ : σ₀ < 1) :
    ∫ x in Ioi (1:ℝ), ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      LSeries (fun n => (LamF χ n : ℂ)) s / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + gammaF χ) * (1 / (s - 1)) + C * (1 / (s - σ₀)) := by
  have hS := h3 N χ
  have i1 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i2 : IntegrableOn (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (h5.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have i4 : IntegrableOn (fun x : ℝ => ((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) =
      fun x => ((S χ x : ℂ) * (x : ℂ) ^ (-s - 1) - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
        + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)))
        + (C : ℂ) * (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [G, Real.rpow_one]
    push_cast
    ring
  have j12 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)
      - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := Integrable.sub i1 i2
  have j3 : IntegrableOn (fun x : ℝ => ((1 + gammaF χ : ℝ) : ℂ) *
      (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := Integrable.const_mul i3 _
  have j4 : IntegrableOn (fun x : ℝ => (C : ℂ) *
      (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := Integrable.const_mul i4 _
  have j123 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)
      - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) :=
    Integrable.add j12 j3
  rw [hfun, integral_add j123 j4, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    hS.2.2 s hs, h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs), h5.2.2.1 σ₀ s (by linarith)]
  push_cast
  ring

end Mellin

section Main

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

def Hf (σ₀ C : ℝ) (x : ℝ) : ℝ := G χ x + C * x ^ σ₀

def Imel (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((Hf χ σ₀ C x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

def q0 (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  -1 + s * (1 + (gammaF χ : ℂ)) + C * s * (s - 1) / (s - σ₀)

def Afun (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  -deriv (Pfun χ) s - Pfun χ s + s * (1 + (gammaF χ : ℂ)) * Pfun χ s
    + C * s * (s - 1) * Pfun χ s / (s - σ₀)

def Phi (σ₀ C : ℝ) (s : ℂ) : ℂ := dslope (Afun χ σ₀ C) 1 s / (s * Pfun χ s)

lemma ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  simp at hs

lemma sub_ne_zero_of_lt_re {s : ℂ} {a : ℝ} (hs : a < s.re) : s - a ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma ne_zero_of_lt_re {s : ℂ} {a : ℝ} (ha : 0 ≤ a) (hs : a < s.re) : s ≠ 0 := by
  rintro rfl
  simp at hs
  linarith

lemma key_identity (hχ : χ ≠ 1) (h3 : MellinS) (h4 : LSeriesLamF) (h5 : MellinElem)
    (hreal : ∀ n : ℕ, (χ n).im = 0) {σ₀ C : ℝ} (hσ₀1 : σ₀ < 1) {s : ℂ}
    (hs : 1 < s.re) :
    s * (s - 1) * Imel χ σ₀ C s = -deriv (Pfun χ) s / Pfun χ s + q0 χ σ₀ C s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hs)
  have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
  have hsσ : s - σ₀ ≠ 0 := sub_ne_zero_of_lt_re (a := σ₀) (by linarith)
  have hP : Pfun χ s ≠ 0 := Pfun_ne_zero_of_one_le_re χ hχ hs.le
  have hm := mellin_H χ h3 h5 σ₀ C hs hσ₀1
  unfold Imel Hf
  rw [hm, LSeries_LamF_eq χ hχ h4 hreal hs]
  unfold q0
  field_simp
  ring

end Main

end Formalism
end
end

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction

lemma Sz_eq_Sa : Sz = Sa (fun n => Λ n) := rfl

lemma Schi_eq_Sa {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Schi χ = Sa (fun n => Λ n * (χ n).re) := rfl

lemma vM_bound : ∀ n : ℕ, |(Λ n : ℝ)| ≤ 1 * Λ n := fun n => by
  rw [one_mul, abs_of_nonneg vonMangoldt_nonneg]

lemma twist_bound {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∀ n : ℕ, |Λ n * (χ n).re| ≤ 1 * Λ n := fun n => by
  rw [one_mul, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
  have h1 : |(χ n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
  exact mul_le_of_le_one_right vonMangoldt_nonneg h1

lemma measurable_Gz (h3 : MellinSgen) : Measurable Gz := by
  have := (h3 _ 1 vM_bound).1
  unfold Gz
  rw [Sz_eq_Sa]
  fun_prop

lemma measurable_Gchi (h3 : MellinSgen) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Measurable (Gchi χ) := by
  have := (h3 _ 1 (twist_bound χ)).1
  unfold Gchi
  rw [Schi_eq_Sa]
  fun_prop

lemma rint_Gz (h3 : MellinSgen) (h5 : MellinElem) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gz x * x ^ (-σ - 1)) (Ioi 1) := by
  have hS := h3 _ 1 vM_bound
  have a1 := rint_of_abs _ hS.1 σ (hS.2.1 σ hσ)
  have a2 := rint_of_abs (fun x => x * Real.log x) (by fun_prop) σ (h5.2.1 σ hσ)
  have a3 := h5.1 1 σ hσ
  have hfun : (fun x : ℝ => Gz x * x ^ (-σ - 1)) = fun x =>
      (Sa (fun n => Λ n) x * x ^ (-σ - 1) - (x * Real.log x) * x ^ (-σ - 1))
        + (1 + Real.eulerMascheroniConstant) * (x ^ (1:ℝ) * x ^ (-σ - 1)) := by
    funext x
    simp only [Gz, Sz_eq_Sa, Real.rpow_one]
    ring
  rw [hfun]
  exact Integrable.add (Integrable.sub a1 a2) (Integrable.const_mul a3 _)

lemma rint_Gchi (h3 : MellinSgen) (h5 : MellinElem) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) (Ioi 1) := by
  have hS := h3 _ 1 (twist_bound χ)
  have a1 := rint_of_abs _ hS.1 σ (hS.2.1 σ hσ)
  have a3 := h5.1 1 σ hσ
  have hfun : (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) = fun x =>
      Sa (fun n => Λ n * (χ n).re) x * x ^ (-σ - 1)
        + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
          * (x ^ (1:ℝ) * x ^ (-σ - 1)) := by
    funext x
    simp only [Gchi, Schi_eq_Sa, Real.rpow_one]
    ring
  rw [hfun]
  exact Integrable.add a1 (Integrable.const_mul a3 _)

lemma mellin_Gz (h3 : MellinSgen) (h5 : MellinElem) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1:ℝ), (Gz x : ℂ) * (x : ℂ) ^ (-s - 1) =
      (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + (Real.eulerMascheroniConstant : ℂ)) * (1 / (s - 1)) := by
  have hS := h3 _ 1 vM_bound
  have i1 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i2 := cint_of_abs (fun x => x * Real.log x) (by fun_prop) s (h5.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => (Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      ((Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)
        - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        + ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [Gz, Sz_eq_Sa, Real.rpow_one]
    push_cast
    ring
  have j12 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)
        - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := Integrable.sub i1 i2
  have j3 := Integrable.const_mul i3 ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ)
  refine ⟨by rw [hfun]; exact j12.add j3, ?_⟩
  rw [hfun, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, hS.2.2 s hs,
    h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs)]
  have hL : LSeries (fun n => ((Λ n : ℝ) : ℂ)) s = -deriv riemannZeta s / riemannZeta s :=
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [hL]
  push_cast
  ring

end Formalism
end
end

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

lemma riemannZetaOne_eq_mul_of_ne_one {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp

lemma riemannZetaOne_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1; simp
  · rw [riemannZetaOne_eq_mul_of_ne_one h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)

lemma ofReal_ne_one_of_lt {σ : ℝ} (h : σ < 1) : (σ : ℂ) ≠ 1 := by
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith

lemma riemannZetaOne_ne_zero_of_real_mem_Ioo (h8 : ZetaRealNonvanish) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta₁ σ ≠ 0 := by
  rw [riemannZetaOne_eq_mul_of_ne_one (ofReal_ne_one_of_lt h1)]
  exact mul_ne_zero (sub_ne_zero.mpr (ofReal_ne_one_of_lt h1)) (h8 σ h0 h1)

lemma deriv_riemannZetaOne_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta₁ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have heq : riemannZeta₁ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact riemannZetaOne_eq_mul_of_ne_one hz
  rw [heq.deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [h.deriv]
  ring

lemma logderiv_zeta_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      -(deriv riemannZeta₁ s / riemannZeta₁ s) + 1 / (s - 1) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_riemannZetaOne_of_ne_one hs, riemannZetaOne_eq_mul_of_ne_one hs]
  field_simp
  ring

section Fam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)

lemma differentiable_deriv_of {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (deriv f) :=
  fun z => ((analyticOnNhd_univ_iff_differentiable.mpr hf).deriv z trivial).differentiableAt

end Fam

end Formalism
end
end

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

section Fam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)

lemma ofReal_ne_ofReal_of_lt {a b : ℝ} (h : a < b) : (b : ℂ) ≠ (a : ℂ) := by
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith

lemma ne_ofReal_of_lt_re {s : ℂ} {a : ℝ} (h : a < s.re) : s ≠ (a : ℂ) := by
  intro h'
  rw [h'] at h
  simp at h

end Fam

end Formalism
end
end

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

namespace landauIteratedDerivatives

def Good (H : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)

lemma meas_rpow (H : ℝ → ℝ) (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (σ : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => H x * x ^ (-σ - 1)) (volume.restrict (Ioi 1)) :=
  hH.mul (by fun_prop : Measurable fun x : ℝ => x ^ (-σ - 1)).aestronglyMeasurable

lemma good_mono {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    {σ σ' : ℝ} (h : Good H σ) (hle : σ ≤ σ') : Good H σ' := by
  refine Integrable.mono h (meas_rpow H hH σ') ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
    (norm_nonneg _)

lemma logpow_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ n ≤ (((n : ℝ) + 1) / ε) ^ n * x ^ ε := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set η : ℝ := ε / ((n : ℝ) + 1) with hη
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hηpos : 0 < η := div_pos hε hn1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ x ^ η / η := Real.log_le_rpow_div hx0 hηpos
  have h2 : Real.log x ^ n ≤ (x ^ η / η) ^ n := pow_le_pow_left₀ hlog0 h1 n
  have h3 : (x ^ η / η) ^ n = (1 / η) ^ n * x ^ (η * n) := by
    rw [Real.rpow_mul_natCast hx0, div_pow, one_div_pow]; ring
  have h4 : x ^ (η * n) ≤ x ^ ε := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ hn1]
    nlinarith
  have h5 : 1 / η = ((n : ℝ) + 1) / ε := by rw [hη]; field_simp
  calc Real.log x ^ n ≤ (x ^ η / η) ^ n := h2
    _ = (1 / η) ^ n * x ^ (η * n) := h3
    _ ≤ (1 / η) ^ n * x ^ ε := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (((n : ℝ) + 1) / ε) ^ n * x ^ ε := by rw [h5]

lemma good_logpow {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    {τ σ : ℝ} (hτ : Good H τ) (hlt : τ < σ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-σ - 1))) (Ioi 1) := by
  set K : ℝ := (((n : ℝ) + 1) / (σ - τ)) ^ n
  have hK : 0 ≤ K := by
    have : 0 < σ - τ := by linarith
    positivity
  refine Integrable.mono' (hτ.norm.const_mul K) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => Real.log x ^ n).aestronglyMeasurable.mul
      (meas_rpow H hH σ)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hb := logpow_le n (sub_pos.2 hlt) hx1
  rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (pow_nonneg hlog0 n),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hsplit : x ^ (-τ - 1) = x ^ (σ - τ) * x ^ (-σ - 1) := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [hsplit]
  calc Real.log x ^ n * (‖H x‖ * x ^ (-σ - 1))
      ≤ (K * x ^ (σ - τ)) * (‖H x‖ * x ^ (-σ - 1)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = K * (‖H x‖ * (x ^ (σ - τ) * x ^ (-σ - 1))) := by ring

def J (H : ℝ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), (((-Real.log x) ^ n * H x : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1)

lemma hasDerivAt_J (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {σc : ℝ} (hgood : ∀ σ, σc < σ → Good H σ) (n : ℕ) {z : ℂ} (hz : σc < z.re) :
    HasDerivAt (J H n) (J H (n + 1) z) z := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (((-Real.log x) ^ n * H x : ℝ) : ℂ))
      (volume.restrict (Ioi 1)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (((by fun_prop : Measurable fun x : ℝ => (-Real.log x) ^ n).aestronglyMeasurable).mul hH)
  have hint : ∀ σ : ℝ, σc < σ → IntegrableOn
      (fun x : ℝ => ‖(((-Real.log x) ^ n * H x : ℝ) : ℂ)‖ * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    have := good_logpow hH (hgood ((σc + σ) / 2) (by linarith))
      (show (σc + σ) / 2 < σ by linarith) n
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    simp only
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (hpos x hx)]
    ring
  have := hMD _ σc hmeas hint z hz
  unfold J
  convert this using 2
  funext x
  push_cast
  ring

lemma iteratedDeriv_J (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {σc : ℝ} (hgood : ∀ σ, σc < σ → Good H σ) (n : ℕ) :
    ∀ z : ℂ, σc < z.re → iteratedDeriv n (J H 0) z = J H n z := by
  induction n with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (J H 0) =ᶠ[𝓝 z] J H n := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
      exact ih w hw
    rw [hev.deriv_eq]
    exact (hasDerivAt_J hMD hH hpos hgood n hz).deriv

lemma J_real (H : ℝ → ℝ) (cr : ℝ) (n : ℕ) :
    J H n (cr : ℂ) = ((∫ x in Ioi (1:ℝ), (-Real.log x) ^ n * H x * x ^ (-cr - 1) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  unfold J
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans one_pos hx)
  rw [Complex.ofReal_mul _ (x ^ (-cr - 1)), Complex.ofReal_cpow hx0]
  push_cast
  ring

lemma term_eq (H : ℝ → ℝ) (cr t : ℝ) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ • ((-(t : ℂ)) ^ n • J H n (cr : ℂ)) =
      ((∫ x in Ioi (1:ℝ), t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1))) : ℝ) : ℂ) := by
  have hI : (∫ x in Ioi (1:ℝ), t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1)))) =
      (-t) ^ n / n.factorial * ∫ x in Ioi (1:ℝ), (-Real.log x) ^ n * H x * x ^ (-cr - 1) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    have hp : (-t) ^ n * (-Real.log x) ^ n = t ^ n * Real.log x ^ n := by
      rw [← mul_pow, ← mul_pow, neg_mul_neg]
    have e1 : t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1))) =
        (t ^ n * Real.log x ^ n) * (H x * x ^ (-cr - 1)) / n.factorial := by ring
    rw [e1, ← hp]
    ring
  rw [hI, J_real]
  simp only [smul_eq_mul]
  push_cast
  ring

lemma integrable_of_series {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x) {cr t : ℝ} (ht : 0 ≤ t)
    (hint : ∀ n : ℕ, IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-cr - 1))) (Ioi 1))
    (hsum : Summable (fun n : ℕ =>
      ∫ x in Ioi (1:ℝ), t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1))))) :
    Good H (cr - t) := by
  set f : ℕ → ℝ → ℝ := fun n x => t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1)))
    with hf
  have hfi : ∀ n, Integrable (f n) (volume.restrict (Ioi 1)) := fun n => (hint n).const_mul _
  have hf0 : ∀ n, ∀ x ∈ Ioi (1:ℝ), 0 ≤ f n x := by
    intro n x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have := hpos x hx
    have := Real.log_nonneg hx1
    have := Real.rpow_nonneg hx0 (-cr - 1)
    simp only [hf]
    positivity
  have hsumx : ∀ x ∈ Ioi (1:ℝ), HasSum (fun n => f n x) (H x * x ^ (-(cr - t) - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have he := NormedSpace.expSeries_div_hasSum_exp (t * Real.log x)
    rw [← Real.exp_eq_exp_ℝ] at he
    have := he.mul_left (H x * x ^ (-cr - 1))
    have e1 : (fun n => f n x) =
        fun i => H x * x ^ (-cr - 1) * ((t * Real.log x) ^ i / i.factorial) := by
      funext n
      simp only [hf]
      rw [mul_pow]
      ring
    have e2 : H x * x ^ (-(cr - t) - 1) = H x * x ^ (-cr - 1) * Real.exp (t * Real.log x) := by
      rw [show Real.exp (t * Real.log x) = x ^ t by rw [Real.rpow_def_of_pos hx0]; ring_nf,
        mul_assoc, ← Real.rpow_add hx0]
      ring_nf
    rw [e1, e2]
    exact this
  unfold Good IntegrableOn
  rw [← lintegral_ofReal_ne_top_iff_integrable (meas_rpow H hH _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx =>
      (hsumx x hx).nonneg (fun n => hf0 n x hx)))]
  have h1 : ∫⁻ x in Ioi (1:ℝ), ENNReal.ofReal (H x * x ^ (-(cr - t) - 1)) =
      ∫⁻ x in Ioi (1:ℝ), ∑' n, ENNReal.ofReal (f n x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [← (hsumx x hx).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun n => hf0 n x hx) (hsumx x hx).summable]
  rw [h1, lintegral_tsum (fun n => (hfi n).aemeasurable.ennreal_ofReal)]
  have h2 : ∀ n, ∫⁻ x in Ioi (1:ℝ), ENNReal.ofReal (f n x) =
      ENNReal.ofReal (∫ x in Ioi (1:ℝ), f n x) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hfi n)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hf0 n)))).symm
  rw [tsum_congr h2, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => setIntegral_nonneg measurableSet_Ioi (hf0 n)) hsum]
  exact ENNReal.ofReal_ne_top

lemma dist_ofReal' (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma dist_re (z : ℂ) : dist z (z.re : ℂ) = |z.im| := by
  rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im, sub_self, sub_zero,
    show (0 : ℝ) ^ 2 + z.im ^ 2 = z.im ^ 2 by ring, Real.sqrt_sq_eq_abs]

lemma key (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {b σc : ℝ} (hσcb : σc ≤ b) (hgood : ∀ σ, σc < σ → Good H σ) {Φ : ℂ → ℂ}
    (hΦ1 : ∀ s : ℂ, b < s.re → AnalyticAt ℂ Φ s)
    (hΦ2 : ∀ σ : ℝ, σc ≤ σ → σ ≤ b → AnalyticAt ℂ Φ σ)
    (hΦeq : ∀ s : ℂ, b < s.re → Φ s = J H 0 s) : ∃ σ' < σc, Good H σ' := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_Icc.image continuous_ofReal : IsCompact ((fun σ : ℝ => (σ : ℂ)) '' Icc σc b)).exists_thickening_subset_open
      (isOpen_analyticAt ℂ Φ) (by rintro _ ⟨σ, ⟨h1, h2⟩, rfl⟩; exact hΦ2 σ h1 h2)
  have hA : ∀ z : ℂ, (b < z.re ∨ ∃ σ : ℝ, σc ≤ σ ∧ σ ≤ b ∧ dist z σ < δ) → AnalyticAt ℂ Φ z := by
    rintro z (h | ⟨σ, h1, h2, h3⟩)
    · exact hΦ1 z h
    · exact hthick (Metric.mem_thickening_iff.2 ⟨σ, ⟨σ, ⟨h1, h2⟩, rfl⟩, h3⟩)
  set R : Set ℂ := {z : ℂ | σc < z.re} ∩ {z : ℂ | z.im < δ} ∩ {z : ℂ | -δ < z.im} with hR
  have hRopen : IsOpen R :=
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_im continuous_const)).inter
      (isOpen_lt continuous_const continuous_im)
  have hRconv : Convex ℝ R :=
    ((convex_halfSpace_re_gt σc).inter (convex_halfSpace_im_lt δ)).inter (convex_halfSpace_im_gt (-δ))
  have hΦR : AnalyticOnNhd ℂ Φ R := by
    rintro z ⟨⟨h1, h2⟩, h3⟩
    apply hA
    by_cases hb : b < z.re
    · exact Or.inl hb
    · refine Or.inr ⟨z.re, le_of_lt h1, not_lt.1 hb, ?_⟩
      rw [dist_re]
      exact abs_lt.2 ⟨h3, h2⟩
  have hJan : AnalyticOnNhd ℂ (J H 0) {z : ℂ | σc < z.re} :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (hasDerivAt_J hMD hH hpos hgood 0 hz).differentiableAt.differentiableWithinAt)
      (isOpen_lt continuous_const continuous_re)
  have hEq : EqOn Φ (J H 0) R := by
    have hz0 : ((b + 1 : ℝ) : ℂ) ∈ R := by
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> linarith
    refine hΦR.eqOn_of_preconnected_of_eventuallyEq (hJan.mono (fun z hz => hz.1.1))
      hRconv.isPreconnected hz0 ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show b < (((b + 1 : ℝ) : ℂ)).re by simp)] with w hw
    exact hΦeq w hw
  set cr : ℝ := σc + δ / 4 with hcr
  have hcR : (cr : ℂ) ∈ R := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [hcr] <;> linarith
  have hev : Φ =ᶠ[𝓝 (cr : ℂ)] J H 0 := by
    filter_upwards [hRopen.mem_nhds hcR] with w hw
    exact hEq hw
  have hder : ∀ n : ℕ, iteratedDeriv n Φ (cr : ℂ) = J H n (cr : ℂ) := fun n =>
    (hev.iteratedDeriv_eq n).trans
      (iteratedDeriv_J hMD hH hpos hgood n (cr : ℂ) (by simp [hcr]; linarith))
  have hdiff : DifferentiableOn ℂ Φ (Metric.ball (cr : ℂ) (δ / 2)) := by
    intro z hz
    refine (hA z ?_).differentiableAt.differentiableWithinAt
    rw [Metric.mem_ball] at hz
    by_cases hb : b < z.re
    · exact Or.inl hb
    · right
      have him : |z.im| < δ / 2 := by
        have := Complex.abs_im_le_norm (z - cr)
        rw [← dist_eq_norm] at this
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
        linarith
      by_cases hs : σc ≤ z.re
      · refine ⟨z.re, hs, not_lt.1 hb, ?_⟩
        rw [dist_re]; linarith
      · refine ⟨σc, le_rfl, hσcb, ?_⟩
        have h1 : dist (cr : ℂ) (σc : ℂ) = δ / 4 := by
          rw [dist_ofReal', hcr, show σc + δ / 4 - σc = δ / 4 by ring,
            abs_of_pos (by linarith)]
        linarith [dist_triangle z (cr : ℂ) (σc : ℂ)]
  set t : ℝ := 3 * δ / 8 with ht
  have hzmem : ((cr - t : ℝ) : ℂ) ∈ Metric.ball (cr : ℂ) (δ / 2) := by
    rw [Metric.mem_ball, dist_ofReal', show cr - t - cr = -t by ring, abs_neg,
      abs_of_pos (by rw [ht]; linarith)]
    rw [ht]; linarith
  have hs := Complex.hasSum_taylorSeries_on_ball hdiff hzmem
  have hsub : ((cr - t : ℝ) : ℂ) - (cr : ℂ) = -(t : ℂ) := by push_cast; ring
  simp_rw [hsub, hder, term_eq] at hs
  have hsum := Complex.summable_ofReal.1 hs.summable
  have hint : ∀ n : ℕ, IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-cr - 1))) (Ioi 1) :=
    fun n => good_logpow hH (hgood (σc + δ / 8) (by linarith)) (by rw [hcr]; linarith) n
  refine ⟨cr - t, by rw [hcr, ht]; linarith, ?_⟩
  exact integrable_of_series hH hpos (by rw [ht]; positivity) hint hsum

end landauIteratedDerivatives

open landauIteratedDerivatives in
theorem landauLemma_of (hMD : MellinDeriv) : LandauLemma := by
  intro H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq σ hσ
  by_contra hbad
  set T : Set ℝ := {τ | a < τ ∧ ¬ Good H τ} with hT
  have hσT : σ ∈ T := ⟨hσ, hbad⟩
  have hbdd : BddAbove T := ⟨b, fun τ hτ => by
    by_contra h
    exact hτ.2 (hb τ (lt_of_not_ge h))⟩
  set σc := sSup T with hσc
  have hσσc : σ ≤ σc := le_csSup hbdd hσT
  have hσcb : σc ≤ b := csSup_le ⟨σ, hσT⟩ (fun τ hτ => by
    by_contra h
    exact hτ.2 (hb τ (lt_of_not_ge h)))
  have hgood : ∀ τ, σc < τ → Good H τ := by
    intro τ hτ
    by_contra h
    have : τ ≤ σc := le_csSup hbdd ⟨by linarith, h⟩
    linarith
  have hJ0 : ∀ s : ℂ, b < s.re → Φ s = J H 0 s := by
    intro s hs
    rw [hΦeq s hs]
    unfold J
    congr 1
    funext x
    simp
  obtain ⟨σ', hσ'lt, hσ'⟩ := key hMD hH hpos hσcb hgood hΦ1
    (fun τ h1 h2 => hΦ2 τ (by linarith) h2) hJ0
  have : σc ≤ σ' := csSup_le ⟨σ, hσT⟩ (fun τ hτ => by
    by_contra h
    exact hτ.2 (good_mono hH hσ' (le_of_lt (lt_of_not_ge h))))
  linarith

end Formalism
end
end

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

theorem mellinDeriv : MellinDeriv := by
  intro H σs hH hint s hs
  set μ : Measure ℝ := volume.restrict (Ioi (1:ℝ)) with hμ
  set η : ℝ := (s.re - σs) / 3 with hη
  have hηpos : 0 < η := by rw [hη]; linarith

  have hcpow_meas : ∀ c : ℂ, Measurable (fun x : ℝ => (x : ℂ) ^ c) :=
    fun c => (Complex.measurable_ofReal).pow_const c
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => H x * (x : ℂ) ^ (-z - 1)) μ :=
    fun z => hH.mul (hcpow_meas _).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => -(Real.log x : ℂ) * H x * (x : ℂ) ^ (-s - 1)) μ := by
    have hlog : Measurable (fun x : ℝ => -(Real.log x : ℂ)) :=
      (Complex.measurable_ofReal.comp Real.measurable_log).neg
    exact (hlog.aestronglyMeasurable.mul hH).mul (hcpow_meas _).aestronglyMeasurable

  have hF_int : Integrable (fun x : ℝ => H x * (x : ℂ) ^ (-s - 1)) μ := by
    have h1 := hint s.re hs
    refine Integrable.mono' h1 (hF_meas s) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp

  set bound : ℝ → ℝ := fun x => ‖H x‖ * x ^ (-(s.re - 2 * η) - 1) / η with hbound
  have hbound_int : Integrable bound μ := by
    have h1 := hint (s.re - 2 * η) (by rw [hη]; linarith)
    exact h1.div_const η
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s η,
      ‖-(Real.log x : ℂ) * H x * (x : ℂ) ^ (-z - 1)‖ ≤ bound x := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro x hx z hz
    have hx1 : (1:ℝ) < x := hx
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    have hzre : s.re - η < z.re := by
      have : |z.re - s.re| < η := by
        have h := Metric.mem_ball.1 hz
        rw [Complex.dist_eq] at h
        calc |z.re - s.re| = |(z - s).re| := by simp
          _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _
          _ < η := h
      have := (abs_lt.1 this).1
      linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hlogle : Real.log x ≤ x ^ η / η := Real.log_le_rpow_div hx0.le hηpos
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
      Real.norm_of_nonneg hlog0]
    have hre : (-z - 1).re = -z.re - 1 := by simp
    rw [hre]
    have hpow : x ^ (-z.re - 1) ≤ x ^ (-(s.re - η) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have hHn : 0 ≤ ‖H x‖ := norm_nonneg _
    have hp0 : 0 ≤ x ^ (-z.re - 1) := Real.rpow_nonneg hx0.le _
    have hmul : x ^ η * x ^ (-(s.re - η) - 1) = x ^ (-(s.re - 2 * η) - 1) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    calc Real.log x * ‖H x‖ * x ^ (-z.re - 1)
        ≤ (x ^ η / η) * ‖H x‖ * x ^ (-(s.re - η) - 1) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hlogle hHn) hpow hp0
          exact mul_nonneg (div_nonneg (Real.rpow_nonneg hx0.le _) hηpos.le) hHn
      _ = bound x := by
          rw [hbound]; simp only
          rw [← hmul]; field_simp
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s η,
      HasDerivAt (fun w : ℂ => H x * (x : ℂ) ^ (-w - 1))
        (-(Real.log x : ℂ) * H x * (x : ℂ) ^ (-z - 1)) z := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro x hx z _
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    have hf : HasDerivAt (fun w : ℂ => -w - 1) (-1) z := by
      simpa using ((hasDerivAt_id z).neg.sub_const (1:ℂ))
    have hc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have h2 := (hf.const_cpow (c := (x:ℂ)) (Or.inl hc)).const_mul (H x)
    refine h2.congr_deriv ?_
    rw [← Complex.ofReal_log hx0.le]
    ring
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z x => H x * (x : ℂ) ^ (-z - 1))
    (F' := fun z x => -(Real.log x : ℂ) * H x * (x : ℂ) ^ (-z - 1))
    (Metric.ball_mem_nhds s hηpos) (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas
    h_bound hbound_int h_diff
  exact this.2

end Formalism
end
end

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

namespace LandauMellinIdentity

def Imel (H : ℝ → ℝ) (s : ℂ) : ℂ := ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1)

lemma imel_differentiableOn {H : ℝ → ℝ} {a : ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    (hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) :
    DifferentiableOn ℂ (Imel H) {s : ℂ | a < s.re} := by
  intro s hs
  have hHc : AEStronglyMeasurable (fun x : ℝ => (H x : ℂ)) (volume.restrict (Ioi 1)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hH)
  have hnorm : ∀ σ : ℝ, a < σ →
      IntegrableOn (fun x : ℝ => ‖(H x : ℂ)‖ * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    refine (hint σ hσ).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos x hx)]
  exact (mellinDeriv (fun x => (H x : ℂ)) a hHc hnorm s hs).differentiableAt
    |>.differentiableWithinAt

end LandauMellinIdentity

open LandauMellinIdentity in
theorem landauEq : LandauEq := by
  intro H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq
  have hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) :=
    landauLemma_of mellinDeriv H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq
  intro σ hσ
  refine ⟨hint σ hσ, ?_⟩

  have hOpen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hIan : AnalyticOnNhd ℂ (LandauMellinIdentity.Imel H) {s : ℂ | a < s.re} :=
    (imel_differentiableOn hH hpos hint).analyticOnNhd hOpen

  set A : Set ℂ := {s : ℂ | b < s.re} with hA
  set B : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioi a with hB
  have hb1A : ((b + 1 : ℝ) : ℂ) ∈ A := by simp [hA]
  have hb1B : ((b + 1 : ℝ) : ℂ) ∈ B := ⟨b + 1, by simp; linarith, rfl⟩
  have hAconv : Convex ℝ A := convex_halfSpace_re_gt b
  have hApc : IsPreconnected A := hAconv.isPreconnected
  have hBpc : IsPreconnected B :=
    (isPreconnected_Ioi).image _ Complex.continuous_ofReal.continuousOn
  have hTpc : IsPreconnected (A ∪ B) := IsPreconnected.union _ hb1A hb1B hApc hBpc
  have hTsub : A ∪ B ⊆ {s : ℂ | a < s.re} := by
    rintro s (hs | ⟨t, ht, rfl⟩)
    · show a < s.re
      have : b < s.re := hs
      linarith
    · show a < ((t : ℂ)).re
      simpa using ht
  have hΦan : AnalyticOnNhd ℂ Φ (A ∪ B) := by
    rintro s (hs | ⟨t, ht, rfl⟩)
    · exact hΦ1 s hs
    · by_cases htb : t ≤ b
      · exact hΦ2 t ht htb
      · exact hΦ1 _ (by simpa using lt_of_not_ge htb)
  have hev : Φ =ᶠ[𝓝 ((b + 1 : ℝ) : ℂ)] LandauMellinIdentity.Imel H := by
    have hAo : IsOpen A := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hAo.mem_nhds hb1A] with s hs
    exact hΦeq s hs
  have heq := hΦan.eqOn_of_preconnected_of_eventuallyEq (hIan.mono hTsub) hTpc
    (Or.inl hb1A) hev
  exact heq (Or.inr ⟨σ, hσ, rfl⟩)

end Formalism
end
end

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

theorem mellinElem_part1 (a σ : ℝ) (h : a < σ) :
    IntegrableOn (fun x : ℝ => x ^ a * x ^ (-σ - 1)) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (a + (-σ - 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0:ℝ) < x := lt_trans one_pos hx
  simp only
  rw [Real.rpow_add hx0]

theorem mellinElem_part2 (σ : ℝ) (h : 1 < σ) :
    IntegrableOn (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) (Ioi 1) := by
  set ε : ℝ := (σ - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hi : IntegrableOn (fun x : ℝ => x ^ (ε - σ) / ε) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by rw [hε]; linarith) one_pos).div_const ε
  refine hi.mono' ?_ ?_
  · have : Measurable (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) := by fun_prop
    exact this.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
    have hl := Real.log_le_rpow_div hx0.le hε0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have e1 : x * Real.log x * x ^ (-σ - 1) = Real.log x * x ^ (-σ) := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    rw [e1, Real.rpow_sub hx0, Real.rpow_neg hx0.le]
    calc Real.log x * (x ^ σ)⁻¹ ≤ x ^ ε / ε * (x ^ σ)⁻¹ :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ = x ^ ε / x ^ σ / ε := by ring

theorem mellinElem_part3 (a : ℝ) (s : ℂ) (h : a < s.re) :
    ∫ x in Ioi (1:ℝ), ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - a) := by
  have e : EqOn (fun x : ℝ => ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - s - 1)) (Ioi 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    simp only
    rw [ofReal_cpow hx0.le, ← cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne')]
    ring_nf
  have hre : ((a : ℂ) - s - 1).re < -1 := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_cpow_of_lt hre one_pos,
    ofReal_one, one_cpow, show (a : ℂ) - s - 1 + 1 = -(s - a) by ring, neg_div_neg_eq]

theorem mellinElem_part4 (s : ℂ) (h : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - 1) ^ 2 := by
  set w : ℂ := 1 - s with hw
  have hw0 : w ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hw] at this
    linarith
  have hwre : w.re < 0 := by simp [hw]; linarith
  have e : EqOn (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (lt_trans one_pos hx).ne'
    simp only
    rw [cpow_sub _ _ hx0, cpow_one]
    push_cast
    field_simp
  have hderiv : ∀ x ∈ Ici (1:ℝ), HasDerivAt
      (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
      ((Real.log x : ℂ) * (x : ℂ) ^ (-s)) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
    have hx0c : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
    have h1 := hasDerivAt_ofReal_cpow_const hx0.ne' hw0
    have h2 : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
      (Real.hasDerivAt_log hx0.ne').ofReal_comp
    have h3 := h1.mul ((h2.div_const w).sub_const (1 / w ^ 2))
    have h4 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
        (w * (x : ℂ) ^ (w - 1) * ((Real.log x : ℂ) / w - 1 / w ^ 2) + (x : ℂ) ^ w * (((x⁻¹ : ℝ) : ℂ) / w)) x := h3
    refine h4.congr_deriv ?_
    have ea : (x : ℂ) ^ (w - 1) = (x : ℂ) ^ (-s) := by congr 1; rw [hw]; ring
    have eb : (x : ℂ) ^ w = x * (x : ℂ) ^ (-s) := by
      rw [show w = 1 + -s by rw [hw]; ring, cpow_add _ _ hx0c, cpow_one]
    rw [ea, eb]
    push_cast
    field_simp
    ring
  have hint : IntegrableOn (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) := by
    refine (mellinElem_part2 s.re h).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      exact ((continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx0.ne')).mul
        (continuousAt_ofReal_cpow_const x (-s) (Or.inr hx0.ne'))).continuousWithinAt
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
        norm_cpow_eq_rpow_re_of_pos hx0, abs_of_nonneg (by positivity),
        Real.rpow_sub_one hx0.ne']
      simp only [neg_re]
      apply le_of_eq
      field_simp
  have hlim : Tendsto (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, w.re = -r := ⟨-w.re, by ring⟩
    have hr0 : 0 < r := by linarith
    have hA : Tendsto (fun x : ℝ => x ^ (-r)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hr0
    have hB : Tendsto (fun x : ℝ => Real.log x * x ^ (-r)) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop hr0).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.rpow_neg hx.le, div_eq_mul_inv]
    have hg := (hB.div_const ‖w‖).add (hA.div_const (‖w‖ ^ 2))
    simp only [zero_div, add_zero] at hg
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, hr]
    calc x ^ (-r) * ‖(Real.log x : ℂ) / w - 1 / w ^ 2‖
        ≤ x ^ (-r) * (Real.log x / ‖w‖ + 1 / ‖w‖ ^ 2) := by
          gcongr
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
            norm_one, norm_pow]
      _ = Real.log x * x ^ (-r) / ‖w‖ + x ^ (-r) / ‖w‖ ^ 2 := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_div, zero_sub, one_mul]
  rw [hw]
  field_simp
  ring

theorem mellinElem : MellinElem :=
  ⟨mellinElem_part1, mellinElem_part2, mellinElem_part3, mellinElem_part4⟩

end Formalism
end
end

section
open Complex Filter Topology

noncomputable section

namespace Formalism

theorem logDerivZeroFree : LogDerivZeroFree := by
  intro P q U hU hP ⟨z, hz⟩ hq hPq s hs hPs
  have hPa : ∀ w, AnalyticAt ℂ P w := fun w => hP.analyticAt w
  have hqa : AnalyticAt ℂ q s := hq.analyticAt (hU.mem_nhds hs)

  have hne : analyticOrderAt P s ≠ ⊤ := by
    rw [Ne, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s hPa]
    intro h
    exact hz (by simp [h])
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne

  have hn0 : n ≠ 0 := by
    rintro rfl
    have : analyticOrderAt P s = 0 := by rw [← hn]; rfl
    rcases analyticOrderAt_eq_zero.mp this with h | h
    · exact h (hPa s)
    · exact h hPs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hord : analyticOrderAt P s = (m : ℕ∞) + 1 := by rw [← hn]; push_cast; rfl
  have hd : analyticOrderAt (deriv P) s = m := analyticOrderAt_deriv_of_pos (hPa s) hord

  have hev : deriv P =ᶠ[𝓝 s] q * P :=
    Filter.eventually_of_mem (hU.mem_nhds hs) (fun w hw => by simpa using hPq w hw)
  have hmul : analyticOrderAt (deriv P) s = analyticOrderAt q s + ((m : ℕ∞) + 1) := by
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hqa (hPa s), hord]
  rw [hd] at hmul
  have hle : (m : ℕ∞) + 1 ≤ (m : ℕ∞) := by
    calc (m : ℕ∞) + 1 ≤ analyticOrderAt q s + ((m : ℕ∞) + 1) := le_add_self
      _ = m := hmul.symm
  exact absurd hle (by
    rw [not_le]
    exact ENat.lt_add_one_iff (ENat.natCast_ne_top m) |>.mpr le_rfl)

end Formalism
end
end

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction

def linZ (s : ℂ) : ℂ := -1 + (1 + (Real.eulerMascheroniConstant : ℂ)) * s

def nZ (s : ℂ) : ℂ := -(deriv riemannZeta₁ s / riemannZeta₁ s) + linZ s

def AZ (s : ℂ) : ℂ := -deriv riemannZeta₁ s + linZ s * riemannZeta₁ s

def HZ (ε C θ : ℝ) (x : ℝ) : ℝ := ε * Gz x + C * x ^ θ

def IZ (ε C θ : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((HZ ε C θ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

def PhiZ (ε C θ : ℝ) (s : ℂ) : ℂ := ε * dslope AZ 1 s / (s * riemannZeta₁ s) + C / (s - θ)

lemma AZ_eq {s : ℂ} (hZ : riemannZeta₁ s ≠ 0) : AZ s = riemannZeta₁ s * nZ s := by
  unfold AZ nZ
  field_simp

lemma AZ_one : AZ 1 = 0 := by
  unfold AZ linZ
  rw [deriv_riemannZeta₁_one, riemannZeta₁_one]
  ring

lemma differentiable_AZ : Differentiable ℂ AZ := by
  have hZ : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hZ' : Differentiable ℂ (deriv riemannZeta₁) := differentiable_deriv_of hZ
  unfold AZ linZ
  fun_prop

lemma mellin_Gz_n (h3 : MellinSgen) (h5 : MellinElem) {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), (Gz x : ℂ) * (x : ℂ) ^ (-s - 1) = nZ s / (s * (s - 1)) := by
  have hs1 : s ≠ 1 := ne_one_of_one_lt_re hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  have hZ1 := riemannZetaOne_ne_zero_of_one_le_re hs.le
  rw [(mellin_Gz h3 h5 hs).2, logderiv_zeta_eq hs1 hz]
  unfold nZ linZ
  field_simp
  ring

lemma measurable_HZ (h3 : MellinSgen) (ε C θ : ℝ) : Measurable (HZ ε C θ) := by
  have hz := measurable_Gz h3
  unfold HZ
  exact (measurable_const.mul hz).add (measurable_const.mul (measurable_id.pow_const _))

lemma rint_HZ (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1) {σ : ℝ}
    (hσ : 1 < σ) : IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1) := by
  have a1 := rint_Gz h3 h5 hσ
  have a4 := h5.1 θ σ (by linarith)
  have hfun : (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) = fun x =>
      ε * (Gz x * x ^ (-σ - 1)) + C * (x ^ θ * x ^ (-σ - 1)) := by
    funext x
    simp only [HZ]
    ring
  rw [hfun]
  exact Integrable.add (Integrable.const_mul a1 _) (Integrable.const_mul a4 _)

lemma mellin_HZ (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1)
    {s : ℂ} (hs : 1 < s.re) :
    IZ ε C θ s = ε * nZ s / (s * (s - 1)) + C / (s - θ) := by
  have iz := (mellin_Gz h3 h5 hs).1
  have i4 : IntegrableOn (fun x : ℝ => ((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => ((HZ ε C θ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      (ε : ℂ) * ((Gz x : ℂ) * (x : ℂ) ^ (-s - 1))
        + (C : ℂ) * (((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [HZ]
    push_cast
    ring
  unfold IZ
  rw [hfun, integral_add (Integrable.const_mul iz _) (Integrable.const_mul i4 _),
    integral_const_mul, integral_const_mul, mellin_Gz_n h3 h5 hs, h5.2.2.1 θ s (by linarith)]
  ring

lemma PhiZ_eq {ε C θ : ℝ} {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hZ : riemannZeta₁ s ≠ 0) :
    PhiZ ε C θ s = ε * nZ s / (s * (s - 1)) + C / (s - θ) := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold PhiZ
  rw [dslope_of_ne _ hs1, slope_def_field, AZ_one, sub_zero, AZ_eq hZ]
  field_simp

lemma PhiZ_eq_IZ (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1)
    {s : ℂ} (hs : 1 < s.re) : PhiZ ε C θ s = IZ ε C θ s := by
  rw [mellin_HZ h3 h5 hθ hs, PhiZ_eq (ne_one_of_one_lt_re hs) (ne_zero_of_lt_re zero_le_one hs)
    (riemannZetaOne_ne_zero_of_one_le_re hs.le)]

lemma PhiZ_analyticAt (ε C θ : ℝ) {s : ℂ} (hs0 : s ≠ 0)
    (hE : riemannZeta₁ s ≠ 0) (hsθ : s ≠ θ) : AnalyticAt ℂ (PhiZ ε C θ) s := by
  set V : Set ℂ := {z | z ≠ 0 ∧ riemannZeta₁ z ≠ 0 ∧ z ≠ θ} with hV
  have hEd : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hVo : IsOpen V :=
    isOpen_ne.inter ((isOpen_ne_fun hEd.continuous continuous_const).inter isOpen_ne)
  have hdsl : DifferentiableOn ℂ (dslope AZ 1) univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr differentiable_AZ.differentiableOn
  have hd : DifferentiableOn ℂ (PhiZ ε C θ) V := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (dslope AZ 1) z :=
      (hdsl z (mem_univ z)).differentiableAt Filter.univ_mem
    have h2 : DifferentiableAt ℂ riemannZeta₁ z := hEd z
    unfold PhiZ
    apply DifferentiableAt.add
    · exact (h1.const_mul _).div (differentiableAt_id.mul h2) (mul_ne_zero hz.1 hz.2.1)
    · exact (differentiableAt_const _).div (differentiableAt_id.sub_const _)
        (sub_ne_zero.mpr hz.2.2)
  exact hd.analyticAt (hVo.mem_nhds ⟨hs0, hE, hsθ⟩)

lemma landau_Z (h2 : LandauEq) (h3 : MellinSgen) (h5 : MellinElem) (h8 : ZetaRealNonvanish)
    {ε C θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ ε C θ x) :
    ∀ σ : ℝ, θ < σ → IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1) := by
  intro σ hσ
  refine (h2 (HZ ε C θ) θ 1 hθ1 (measurable_HZ h3 ε C θ).aestronglyMeasurable
    (fun x hx => hH x (le_of_lt hx)) (fun σ hσ => rint_HZ h3 h5 hθ1 hσ) (PhiZ ε C θ)
    ?_ ?_ (fun s hs => PhiZ_eq_IZ h3 h5 hθ1 hs) σ hσ).1
  · intro s hs
    exact PhiZ_analyticAt ε C θ (ne_zero_of_lt_re zero_le_one hs)
      (riemannZetaOne_ne_zero_of_one_le_re hs.le) (ne_ofReal_of_lt_re (by linarith))
  · intro σ h1' h2'
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
    have hσθ : (σ : ℂ) ≠ θ := ofReal_ne_ofReal_of_lt (by linarith)
    refine PhiZ_analyticAt ε C θ hσ0 ?_ hσθ
    rcases h2'.lt_or_eq with h2' | h2'
    · exact riemannZetaOne_ne_zero_of_real_mem_Ioo h8 (by linarith) h2'
    · subst h2'
      exact riemannZetaOne_ne_zero_of_one_le_re (by simp)

lemma riemannZetaOne_ne_zero_of_integrable_mellin (h1 : MellinDeriv) (h3 : MellinSgen) (h5 : MellinElem)
    (h11 : LogDerivZeroFree) {ε C θ : ℝ} (hε : ε * ε = 1) (hθ1 : θ < 1)
    (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ ε C θ x)
    (hInt : ∀ σ : ℝ, θ < σ → IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1)) :
    ∀ s : ℂ, θ < s.re → riemannZeta₁ s ≠ 0 := by
  set U : Set ℂ := {s | θ < s.re} with hU_def
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hId : DifferentiableOn ℂ (IZ ε C θ) U := by
    intro s hs
    have hD := h1 (fun x => ((HZ ε C θ x : ℝ) : ℂ)) θ
      (Complex.measurable_ofReal.comp (measurable_HZ h3 ε C θ)).aestronglyMeasurable
      (fun σ hσ => (hInt σ hσ).congr_fun (fun x hx => by
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hH x (le_of_lt (mem_Ioi.mp hx)))])
        measurableSet_Ioi) s hs
    exact hD.differentiableAt.differentiableWithinAt
  have hZd : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hAd := differentiable_AZ
  have hf1 : DifferentiableOn ℂ
      (fun s => s * (s - 1) * riemannZeta₁ s * (IZ ε C θ s - C / (s - θ))) U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    have hEs := hZd s
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hsθ)
  have hEq : EqOn (fun s => s * (s - 1) * riemannZeta₁ s * (IZ ε C θ s - C / (s - θ)))
      (fun s => (ε : ℂ) * AZ s) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hf1.analyticOnNhd hUopen)
      ((hAd.const_mul (ε : ℂ)).differentiableOn.analyticOnNhd hUopen)
      (convex_halfSpace_re_gt θ).isPreconnected (z₀ := 2)
      (show θ < (2:ℂ).re by simp; linarith) ?_
    have h2mem : (2:ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2mem] with z hz
    have hz' : 1 < z.re := hz
    have hZ := riemannZetaOne_ne_zero_of_one_le_re hz'.le
    have hs1' : z - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hz')
    have hs0 : z ≠ 0 := ne_zero_of_lt_re zero_le_one hz'
    have hsθ : z - θ ≠ 0 := sub_ne_zero_of_lt_re (a := θ) (by linarith)
    rw [mellin_HZ h3 h5 hθ1 hz', AZ_eq hZ]
    field_simp
    ring
  set q : ℂ → ℂ := fun s => linZ s - (ε : ℂ) * (s * (s - 1) * (IZ ε C θ s - C / (s - θ)))
    with hq_def
  have hqd : DifferentiableOn ℂ q U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    apply DifferentiableAt.differentiableWithinAt
    simp only [hq_def, linZ]
    fun_prop (disch := exact hsθ)
  have hid : ∀ s ∈ U, deriv riemannZeta₁ s = q s * riemannZeta₁ s := by
    intro s hs
    have he := hEq hs
    simp only at he
    unfold AZ at he
    have hεc : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
    simp only [hq_def]
    linear_combination (ε : ℂ) * he - (deriv riemannZeta₁ s - linZ s * riemannZeta₁ s) * hεc
  intro s hs
  exact h11 riemannZeta₁ q U hUopen hZd ⟨1, by simp⟩ hqd hid s hs

lemma Sz_bound {x X : ℝ} (hx1 : 1 ≤ x) (hxX : x ≤ X) :
    0 ≤ Sz x ∧ Sz x ≤ X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n := by
  unfold Sz
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn'.1
    have hnx : (n:ℝ) ≤ x := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith))
    apply mul_nonneg vonMangoldt_nonneg
    rw [sub_nonneg, le_div_iff₀ hnpos]
    linarith
  · rw [Finset.mul_sum]
    calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, X * Λ n := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' := Finset.mem_Icc.mp hn
          have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn'.1
          have hdiv : x / n ≤ x := div_le_self (by linarith) hn1
          have hΛ : (0:ℝ) ≤ Λ n := vonMangoldt_nonneg
          nlinarith [mul_nonneg hΛ (show 0 ≤ x - x / n + 1 by linarith),
            mul_nonneg hΛ (show 0 ≤ X - x by linarith)]
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, X * Λ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hxX)
          · intro n _ _
            exact mul_nonneg (by linarith) vonMangoldt_nonneg

lemma Gz_bdd {X : ℝ} (hX : 1 ≤ X) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → x ≤ X → |Gz x| ≤ B := by
  have hγ : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hS0 : 0 ≤ X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => vonMangoldt_nonneg)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  refine ⟨X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n + X * Real.log X
      + (1 + Real.eulerMascheroniConstant) * X, by positivity, ?_⟩
  intro x hx1 hxX
  obtain ⟨hS1, hS2⟩ := Sz_bound hx1 hxX
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hl1 : Real.log x ≤ Real.log X := Real.log_le_log (by linarith) hxX
  have hxl : x * Real.log x ≤ X * Real.log X := mul_le_mul hxX hl1 hl0 (by linarith)
  have hxl0 : 0 ≤ x * Real.log x := mul_nonneg (by linarith) hl0
  have hg : (1 + Real.eulerMascheroniConstant) * x ≤ (1 + Real.eulerMascheroniConstant) * X :=
    mul_le_mul_of_nonneg_left hxX (by linarith)
  have hg0 : 0 ≤ (1 + Real.eulerMascheroniConstant) * x := mul_nonneg (by linarith) (by linarith)
  unfold Gz
  rw [abs_le]
  constructor <;> nlinarith

theorem zetaLandau : ZetaLandau := by
  intro s₀ hs₀ θ hθ0 hθ1 hCex s hs
  obtain ⟨C, x₀, hC⟩ := hCex
  obtain ⟨B, hB0, hB⟩ := Gz_bdd (le_max_right x₀ 1)
  have hs₀abs : |s₀| = 1 := by rcases hs₀ with h | h <;> simp [h]
  have hε : (-s₀) * (-s₀) = 1 := by rcases hs₀ with h | h <;> simp [h]
  have hCC : C ≤ max C B := le_max_left _ _
  have hBC : B ≤ max C B := le_max_right _ _
  have hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ (-s₀) (max C B) θ x := by
    intro x hx
    have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ0.le
    unfold HZ
    rcases le_or_gt x (max x₀ 1) with hxX | hxX
    · have h1 := hB x hx hxX
      have h2 : s₀ * Gz x ≤ B := by
        calc s₀ * Gz x ≤ |s₀ * Gz x| := le_abs_self _
          _ = |Gz x| := by rw [abs_mul, hs₀abs, one_mul]
          _ ≤ B := h1
      have h3 : B ≤ max C B * x ^ θ := by
        nlinarith [mul_nonneg (show 0 ≤ max C B by linarith) (show 0 ≤ x ^ θ - 1 by linarith)]
      linarith
    · have h1 := hC x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hxX))
      have h2 : C * x ^ θ ≤ max C B * x ^ θ := mul_le_mul_of_nonneg_right hCC (by linarith)
      linarith
  have hInt := landau_Z landauEq mellinSgen mellinElem zetaRealNonvanish
    hθ0 hθ1 hH
  have hZ1 := riemannZetaOne_ne_zero_of_integrable_mellin mellinDeriv mellinSgen mellinElem
    logDerivZeroFree hε hθ1 hH hInt s hs
  by_cases h1 : s = 1
  · subst h1
    exact riemannZeta_ne_zero_of_one_le_re (by simp)
  · rw [riemannZetaOne_eq_mul_of_ne_one h1] at hZ1
    exact right_ne_zero_of_mul hZ1

theorem zetaLandauEps : ZetaLandauEps := by
  intro s₀ hs₀ θ hθ0 hθ1 hB s hs
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ θ + ε < s.re ∧ θ + ε < 1 := by
    refine ⟨min ((s.re - θ) / 2) ((1 - θ) / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · have := min_le_left ((s.re - θ) / 2) ((1 - θ) / 2); linarith
    · have := min_le_right ((s.re - θ) / 2) ((1 - θ) / 2); linarith
  exact zetaLandau s₀ hs₀ (θ + ε) (by linarith) hε2 (hB ε hε0) s hε1

end Formalism
end
end
