import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.Residue

section
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rectIntegral (f : ℂ → E) (z w : ℂ) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

def rectBoundary (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    {w.re} ×ℂ [[z.im, w.im]]

section Edges

variable {z w : ℂ}

lemma bottom_mem_rectBoundary {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + z.im * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hx]

lemma top_mem_rectBoundary {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + w.im * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hx]

lemma right_mem_rectBoundary {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (w.re : ℂ) + y * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hy]

lemma left_mem_rectBoundary {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (z.re : ℂ) + y * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hy]

lemma rectBoundary_subset : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
  intro u hu
  simp only [rectBoundary, mem_union, mem_reProdIm, mem_singleton_iff] at hu ⊢
  rcases hu with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact ⟨h1, h2 ▸ left_mem_uIcc⟩
  · exact ⟨h1, h2 ▸ right_mem_uIcc⟩
  · exact ⟨h1 ▸ left_mem_uIcc, h2⟩
  · exact ⟨h1 ▸ right_mem_uIcc, h2⟩

lemma notMem_rectBoundary_of_mem_Ioo {p : ℂ}
    (hre : p.re ∈ Ioo (min z.re w.re) (max z.re w.re))
    (him : p.im ∈ Ioo (min z.im w.im) (max z.im w.im)) : p ∉ rectBoundary z w := by
  simp only [rectBoundary, mem_union, mem_reProdIm, mem_singleton_iff, not_or, not_and]
  have key : ∀ {a b t : ℝ}, t ∈ Ioo (min a b) (max a b) → t ≠ a ∧ t ≠ b := by
    intro a b t ht
    obtain ⟨h1, h2⟩ := ht
    rw [min_lt_iff] at h1
    rw [lt_max_iff] at h2
    constructor <;> rintro rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith
  refine ⟨⟨⟨fun _ h ↦ (key him).1 h, fun _ h ↦ (key him).2 h⟩, fun h _ ↦ (key hre).1 h⟩,
    fun h _ ↦ (key hre).2 h⟩

variable {f g : ℂ → E}

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_bottom (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + z.im * I).continuousOn
    fun _ hx ↦ bottom_mem_rectBoundary hx).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_top (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + w.im * I).continuousOn
    fun _ hx ↦ top_mem_rectBoundary hx).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_right (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (w.re : ℂ) + y * I).continuousOn
    fun _ hy ↦ right_mem_rectBoundary hy).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_left (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (z.re : ℂ) + y * I).continuousOn
    fun _ hy ↦ left_mem_rectBoundary hy).intervalIntegrable

end Edges

section Linearity

variable {z w : ℂ} {f g : ℂ → E}

theorem rectIntegral_add (hf : ContinuousOn f (rectBoundary z w))
    (hg : ContinuousOn g (rectBoundary z w)) :
    rectIntegral (fun u ↦ f u + g u) z w = rectIntegral f z w + rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_add (intervalIntegrable_bottom hf) (intervalIntegrable_bottom hg),
    integral_add (intervalIntegrable_top hf) (intervalIntegrable_top hg),
    integral_add (intervalIntegrable_right hf) (intervalIntegrable_right hg),
    integral_add (intervalIntegrable_left hf) (intervalIntegrable_left hg)]
  simp only [smul_add]
  abel



theorem rectIntegral_smul (c : ℂ) : rectIntegral (fun u ↦ c • f u) z w = c • rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_smul, smul_sub, smul_add]
  rw [smul_comm I c, smul_comm I c]

theorem rectIntegral_const_mul {f : ℂ → ℂ} (c : ℂ) :
    rectIntegral (fun u ↦ c * f u) z w = c * rectIntegral f z w :=
  rectIntegral_smul (f := f) c

theorem rectIntegral_zero : rectIntegral (fun _ ↦ (0 : E)) z w = 0 := by
  simp [rectIntegral]

theorem rectIntegral_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (hf : ∀ i ∈ s, ContinuousOn (f i) (rectBoundary z w)) :
    rectIntegral (fun u ↦ ∑ i ∈ s, f i u) z w = ∑ i ∈ s, rectIntegral (f i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rectIntegral_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [rectIntegral_add (hf a (Finset.mem_insert_self a s))
      (continuousOn_finsetSum _ fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

theorem rectIntegral_congr (h : EqOn f g (rectBoundary z w)) :
    rectIntegral f z w = rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_congr (g := fun x : ℝ ↦ g (x + z.im * I))
      fun x hx ↦ h (bottom_mem_rectBoundary hx),
    integral_congr (g := fun x : ℝ ↦ g (x + w.im * I)) fun x hx ↦ h (top_mem_rectBoundary hx),
    integral_congr (g := fun y : ℝ ↦ g (w.re + y * I)) fun y hy ↦ h (right_mem_rectBoundary hy),
    integral_congr (g := fun y : ℝ ↦ g (z.re + y * I)) fun y hy ↦ h (left_mem_rectBoundary hy)]

end Linearity

section Derivative

variable {z w : ℂ}

theorem rectIntegral_eq_zero_of_hasDerivAt [CompleteSpace E] {F f : ℂ → E}
    (hF : ∀ u ∈ rectBoundary z w, HasDerivAt F (f u) u) (hf : ContinuousOn f (rectBoundary z w)) :
    rectIntegral f z w = 0 := by
  have hh : ∀ c : ℝ, ∀ x : ℝ, (x : ℂ) + c * I ∈ rectBoundary z w →
      HasDerivAt (fun x : ℝ ↦ F (x + c * I)) (f (x + c * I)) x := by
    intro c x hx
    have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ) + c * I) 1 x := by
      simpa using (hasDerivAt_id' x).ofReal_comp.add_const ((c : ℂ) * I)
    have h2 := (hF _ hx).scomp x h1
    rw [one_smul] at h2
    exact h2
  have hv : ∀ c : ℝ, ∀ y : ℝ, (c : ℂ) + y * I ∈ rectBoundary z w →
      HasDerivAt (fun y : ℝ ↦ F (c + y * I)) (I • f (c + y * I)) y := by
    intro c y hy
    have h1 : HasDerivAt (fun y : ℝ ↦ (c : ℂ) + y * I) I y := by
      simpa using ((hasDerivAt_id' y).ofReal_comp.mul_const I).const_add (c : ℂ)
    exact (hF _ hy).scomp y h1
  have hb : ∫ x : ℝ in z.re..w.re, f (x + z.im * I) =
      F (w.re + z.im * I) - F (z.re + z.im * I) :=
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hh _ x (bottom_mem_rectBoundary hx))
      (intervalIntegrable_bottom hf)
  have ht : ∫ x : ℝ in z.re..w.re, f (x + w.im * I) =
      F (w.re + w.im * I) - F (z.re + w.im * I) :=
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hh _ x (top_mem_rectBoundary hx))
      (intervalIntegrable_top hf)
  have hr : I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I) =
      F (w.re + w.im * I) - F (w.re + z.im * I) := by
    rw [← intervalIntegral.integral_smul]
    exact integral_eq_sub_of_hasDerivAt (fun y hy ↦ hv _ y (right_mem_rectBoundary hy))
      ((intervalIntegrable_right hf).smul I)
  have hl : I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I) =
      F (z.re + w.im * I) - F (z.re + z.im * I) := by
    rw [← intervalIntegral.integral_smul]
    exact integral_eq_sub_of_hasDerivAt (fun y hy ↦ hv _ y (left_mem_rectBoundary hy))
      ((intervalIntegrable_left hf).smul I)
  rw [rectIntegral, hb, ht, hr, hl]
  abel

theorem rectIntegral_zpow_sub {p : ℂ} {n : ℤ} (hn : n ≠ -1) (hp : p ∉ rectBoundary z w) :
    rectIntegral (fun u ↦ (u - p) ^ n) z w = 0 := by
  have hn' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hup : ∀ u ∈ rectBoundary z w, u - p ≠ 0 := fun u hu h ↦ hp (sub_eq_zero.1 h ▸ hu)
  refine rectIntegral_eq_zero_of_hasDerivAt (F := fun u ↦ (u - p) ^ (n + 1) / ((n : ℂ) + 1))
    (fun u hu ↦ ?_) ?_
  · have h1 : HasDerivAt (fun u : ℂ ↦ u - p) 1 u := (hasDerivAt_id u).sub_const p
    have h2 := ((hasDerivAt_zpow (n + 1) (u - p) (Or.inl (hup u hu))).comp u h1).div_const
      ((n : ℂ) + 1)
    refine h2.congr_deriv ?_
    rw [add_sub_cancel_right]
    push_cast
    field_simp
  · exact continuousOn_of_forall_continuousAt fun u hu ↦
      ((continuousAt_id.sub continuousAt_const).zpow₀ n (Or.inl (hup u hu)))

end Derivative

section Inverse

def invPrimitive (c x : ℝ) : ℂ :=
  ((Real.log (x ^ 2 + c ^ 2) / 2 : ℝ) : ℂ) - I * ((Real.arctan (x / c) : ℝ) : ℂ)

lemma ofReal_add_mul_I_ne_zero {c : ℝ} (hc : c ≠ 0) (x : ℝ) : (x : ℂ) + c * I ≠ 0 := by
  intro h
  apply hc
  simpa using congrArg Complex.im h

lemma hasDerivAt_invPrimitive {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (invPrimitive c) ((x : ℂ) + c * I)⁻¹ x := by
  have hpos : 0 < x ^ 2 + c ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x ^ 2 + c ^ 2) / 2) (x / (x ^ 2 + c ^ 2)) x := by
    have := (((hasDerivAt_pow 2 x).add_const (c ^ 2)).log hpos.ne').div_const 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h2 : HasDerivAt (fun x : ℝ ↦ Real.arctan (x / c)) (c / (x ^ 2 + c ^ 2)) x := by
    have := ((hasDerivAt_id' x).div_const c).arctan
    refine this.congr_deriv ?_
    field_simp
    ring
  have h3 : HasDerivAt (invPrimitive c)
      (((x / (x ^ 2 + c ^ 2) : ℝ) : ℂ) - I * ((c / (x ^ 2 + c ^ 2) : ℝ) : ℂ)) x :=
    h1.ofReal_comp.sub (h2.ofReal_comp.const_mul I)
  refine h3.congr_deriv ?_
  apply Complex.ext
  · rw [Complex.inv_re, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, sub_re]
    ring
  · rw [Complex.inv_im, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, sub_im]
    ring

theorem integral_inv_ofReal_add_mul_I {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    ∫ x : ℝ in a..b, ((x : ℂ) + c * I)⁻¹ = invPrimitive c b - invPrimitive c a := by
  refine integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_invPrimitive hc x) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact (continuous_ofReal.add continuous_const).inv₀ (ofReal_add_mul_I_ne_zero hc)

lemma invPrimitive_rect_sum {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂) (hb₁ : b₁ < 0)
    (hb₂ : 0 < b₂) :
    (invPrimitive b₁ a₂ - invPrimitive b₁ a₁) - (invPrimitive b₂ a₂ - invPrimitive b₂ a₁) +
      (invPrimitive (-a₂) b₂ - invPrimitive (-a₂) b₁) -
      (invPrimitive (-a₁) b₂ - invPrimitive (-a₁) b₁) = 2 * π * I := by
  have hlog : ∀ s t : ℝ, Real.log (s ^ 2 + (-t) ^ 2) = Real.log (t ^ 2 + s ^ 2) := by
    intro s t; congr 1; ring
  have hat : ∀ s t : ℝ, Real.arctan (s / -t) = -Real.arctan (s / t) := by
    intro s t; rw [div_neg, Real.arctan_neg]
  have e1 : Real.arctan (b₂ / a₂) = π / 2 - Real.arctan (a₂ / b₂) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos ha₂ hb₂)]
  have e2 : Real.arctan (b₁ / a₂) = -(π / 2) - Real.arctan (a₂ / b₁) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_pos_of_neg ha₂ hb₁)]
  have e3 : Real.arctan (b₂ / a₁) = -(π / 2) - Real.arctan (a₁ / b₂) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha₁ hb₂)]
  have e4 : Real.arctan (b₁ / a₁) = π / 2 - Real.arctan (a₁ / b₁) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos_of_neg_of_neg ha₁ hb₁)]
  simp only [invPrimitive, hlog, hat, e1, e2, e3, e4]
  push_cast
  ring

theorem rectIntegral_sub_inv {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im)
    (h4 : p.im < w.im) : rectIntegral (fun u ↦ (u - p)⁻¹) z w = 2 * π * I := by
  have horiz : ∀ c : ℝ, c - p.im ≠ 0 → ∫ x : ℝ in z.re..w.re, ((x : ℂ) + c * I - p)⁻¹ =
      invPrimitive (c - p.im) (w.re - p.re) - invPrimitive (c - p.im) (z.re - p.re) := by
    intro c hc
    have e : ∀ x : ℝ, ((x : ℂ) + c * I - p) = ((x - p.re : ℝ) : ℂ) + ((c - p.im : ℝ) : ℂ) * I := by
      intro x; apply Complex.ext <;> simp
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ ↦ ((t : ℂ) + ((c - p.im : ℝ) : ℂ) * I)⁻¹) p.re (a := z.re) (b := w.re)
    rw [this]
    exact integral_inv_ofReal_add_mul_I hc _ _
  have vert : ∀ c : ℝ, -(c - p.re) ≠ 0 → I • ∫ y : ℝ in z.im..w.im, ((c : ℂ) + y * I - p)⁻¹ =
      invPrimitive (-(c - p.re)) (w.im - p.im) - invPrimitive (-(c - p.re)) (z.im - p.im) := by
    intro c hc
    rw [← intervalIntegral.integral_smul]
    have e : ∀ y : ℝ, I • ((c : ℂ) + y * I - p)⁻¹ =
        (((y - p.im : ℝ) : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I)⁻¹ := by
      intro y
      have hX : (c : ℂ) + y * I - p = I * (((y - p.im : ℝ) : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [smul_eq_mul, hX, mul_inv, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ ↦ ((t : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I)⁻¹) p.im (a := z.im) (b := w.im)
    rw [this]
    exact integral_inv_ofReal_add_mul_I hc _ _
  unfold rectIntegral
  beta_reduce
  rw [horiz _ (by linarith), horiz _ (by linarith), vert _ (by linarith), vert _ (by linarith)]
  exact invPrimitive_rect_sum (by linarith) (by linarith) (by linarith) (by linarith)

end Inverse

section Cauchy

theorem rectIntegral_eq_zero_of_differentiable_on_off_countable [CompleteSpace E] (f : ℂ → E)
    (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    rectIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs Hc Hd

end Cauchy

section Periodic

theorem rectIntegral_eq_zero_of_periodic {g : ℂ → E} {τ : ℂ} (h1 : ∀ u, g (u + 1) = g u)
    (hτ : ∀ u, g (u + τ) = g u) (a : ℂ) : rectIntegral g a (a + 1 + τ.im * I) = 0 := by
  have hre : (a + 1 + τ.im * I).re = a.re + 1 := by simp
  have him : (a + 1 + τ.im * I).im = a.im + τ.im := by simp
  have hv : ∫ y : ℝ in a.im..a.im + τ.im, g (((a.re + 1 : ℝ) : ℂ) + y * I) =
      ∫ y : ℝ in a.im..a.im + τ.im, g ((a.re : ℂ) + y * I) := by
    congr 1
    ext y
    rw [← h1 ((a.re : ℂ) + y * I)]
    congr 1
    push_cast
    ring
  have hh : ∫ x : ℝ in a.re..a.re + 1, g ((x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I) =
      ∫ x : ℝ in a.re..a.re + 1, g ((x : ℂ) + a.im * I) := by
    have e : ∀ x : ℝ, g ((x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I) =
        g (((x - τ.re : ℝ) : ℂ) + a.im * I) := by
      intro x
      rw [← hτ (((x - τ.re : ℝ) : ℂ) + a.im * I)]
      congr 1
      apply Complex.ext <;> simp
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ g ((t : ℂ) + a.im * I)) τ.re
      (a := a.re) (b := a.re + 1)
    rw [this]
    have hper : Function.Periodic (fun t : ℝ ↦ g ((t : ℂ) + a.im * I)) 1 := by
      intro t
      beta_reduce
      rw [← h1 ((t : ℂ) + a.im * I)]
      congr 1
      push_cast
      ring
    rw [show a.re + 1 - τ.re = a.re - τ.re + 1 by ring]
    exact hper.intervalIntegral_add_eq (a.re - τ.re) a.re
  unfold rectIntegral
  rw [hre, him, hv, hh]
  abel

end Periodic

end Elliptic
end GroundTheory.Global
end
end

section
open Complex Filter Topology Set
open scoped Interval Real

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

lemma swap_dslope_comp_add (G : ℂ → ℂ) (a w₀ : ℂ) :
    Function.swap dslope w₀ (fun w ↦ G (w + a)) =
      fun w ↦ Function.swap dslope (w₀ + a) G (w + a) := by
  funext w
  show dslope (fun w ↦ G (w + a)) w₀ w = dslope G (w₀ + a) (w + a)
  rcases eq_or_ne w w₀ with rfl | hw
  · rw [dslope_same, dslope_same]
    exact deriv_comp_add_const _ _ _
  · have hw' : w + a ≠ w₀ + a := fun h ↦ hw (add_right_cancel h)
    rw [dslope_of_ne _ hw, dslope_of_ne _ hw', slope_def_field, slope_def_field]
    congr 1
    ring

lemma dslopeIter_comp_add (G : ℂ → ℂ) (a w₀ : ℂ) (k : ℕ) :
    dslopeIter w₀ k (fun w ↦ G (w + a)) = fun w ↦ dslopeIter (w₀ + a) k G (w + a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dslopeIter_succ', ih, swap_dslope_comp_add]
    funext w
    rw [dslopeIter_succ']

theorem residue_comp_add {f : ℂ → ℂ} {a w₀ : ℂ} (hf : MeromorphicAt f (w₀ + a)) :
    residue (fun w ↦ f (w + a)) w₀ = residue f (w₀ + a) := by
  set n := meromorphicShift f (w₀ + a)
  set G : ℂ → ℂ := fun z ↦ (z - (w₀ + a)) ^ (n + 1) * f z with hGdef
  have hG : AnalyticAt ℂ G (w₀ + a) :=
    analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)
  have e : (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) = fun w ↦ G (w + a) := by
    funext w
    simp only [hGdef]
    congr 2
    ring
  have hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) w₀ := by
    rw [e]
    have : AnalyticAt ℂ (fun w ↦ w + a) w₀ := by fun_prop
    exact hG.comp_of_eq this rfl
  rw [residue_eq_dslopeIter hana, e, dslopeIter_comp_add]
  rfl

theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (h : 0 ≤ meromorphicOrderAt f p) : residue f p = 0 := by
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [meromorphicOrderAt_eq_top_iff] at htop
    rw [residue_congr hf htop]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    have hn0 : 0 ≤ n := by rw [← hn] at h; exact_mod_cast h
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
    simp only [smul_eq_mul] at hfg
    lift n to ℕ using hn0
    rw [residue_congr hf hfg]
    apply residue_eq_zero_of_analyticAt
    simp only [zpow_natCast]
    fun_prop

lemma analyticAt_principalPart (f : ℂ → ℂ) {p u : ℂ} (hu : u ≠ p) :
    AnalyticAt ℂ (principalPart f p) u := by
  have h : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ((z - p) ^ k)⁻¹) u := fun k ↦
    ((analyticAt_id.sub analyticAt_const).pow k).inv (pow_ne_zero _ (sub_ne_zero.2 hu))
  have : principalPart f p = fun z ↦ ∑ j ∈ Finset.range (meromorphicShift f p + 1),
      laurentCoeff f p j * ((z - p) ^ (meromorphicShift f p + 1 - j))⁻¹ := rfl
  rw [this]
  exact Finset.analyticAt_fun_sum _ fun j _ ↦ analyticAt_const.mul (h _)

theorem rectIntegral_principalPart (f : ℂ → ℂ) {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectIntegral (principalPart f p) z w = 2 * π * I * residue f p := by
  have hp : p ∉ rectBoundary z w := notMem_rectBoundary_of_mem_Ioo
    ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
    ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hne : ∀ u ∈ rectBoundary z w, u ≠ p := fun u hu h ↦ hp (h ▸ hu)
  have hc : ∀ k : ℕ, ContinuousOn (fun u ↦ ((u - p) ^ k)⁻¹) (rectBoundary z w) := fun k u hu ↦
    ((((continuous_id.sub continuous_const).pow k).continuousAt).inv₀
      (pow_ne_zero _ (sub_ne_zero.2 (hne u hu)))).continuousWithinAt
  set n := meromorphicShift f p
  have e : principalPart f p = fun u ↦ ∑ j ∈ Finset.range (n + 1),
      laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹ := rfl
  rw [e, rectIntegral_finset_sum (Finset.range (n + 1))
    (f := fun j u ↦ laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹)
    (fun j _ ↦ continuousOn_const.mul (hc _))]
  simp_rw [rectIntegral_const_mul]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · rw [Nat.add_sub_cancel_left]
    simp_rw [pow_one]
    rw [rectIntegral_sub_inv h1 h2 h3 h4]
    exact mul_comm _ _
  · intro j hj
    have hj' : j < n := Finset.mem_range.1 hj
    have e2 : (fun u ↦ ((u - p) ^ (n + 1 - j))⁻¹) = fun u ↦ (u - p) ^ (-((n + 1 - j : ℕ) : ℤ)) := by
      funext u
      rw [zpow_neg, zpow_natCast]
    rw [e2, rectIntegral_zpow_sub _ hp, mul_zero]
    omega

theorem rectIntegral_eq_sum_residue {f : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ)
    (hS : ∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im)
    (hmero : ∀ p ∈ S, MeromorphicAt f p)
    (hana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], u ∉ S → AnalyticAt ℂ f u) :
    rectIntegral f z w = 2 * π * I * ∑ p ∈ S, residue f p := by
  classical
  set F : ℂ → ℂ := fun u ↦ f u - ∑ q ∈ S, principalPart f q u with hF
  set E : ℂ → ℂ → ℂ := fun p u ↦ regularPart f p u - ∑ q ∈ S.erase p, principalPart f q u
    with hE
  set G : ℂ → ℂ := fun u ↦ if u ∈ S then E u u else F u with hG
  have hFE : ∀ p ∈ S, ∀ u, u ≠ p → F u = E p u := by
    intro p hp u hu
    simp only [hF, hE]
    rw [eq_principalPart_add_regularPart f p hu, ← Finset.add_sum_erase S _ hp]
    ring
  have hEana : ∀ p ∈ S, AnalyticAt ℂ (E p) p := by
    intro p hp
    exact (analyticAt_regularPart (hmero p hp)).sub
      (Finset.analyticAt_fun_sum _ fun q hq ↦
        analyticAt_principalPart f (Finset.ne_of_mem_erase hq).symm)
  have hGana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], AnalyticAt ℂ G u := by
    intro u hu
    by_cases huS : u ∈ S
    · have hnhds : ((S.erase u : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 u :=
        (S.erase u).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine (hEana u huS).congr ?_
      filter_upwards [hnhds] with v hv
      simp only [hG]
      rcases eq_or_ne v u with rfl | hvu
      · simp [huS]
      · have hvS : v ∉ S := fun h ↦ hv (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvu, h⟩))
        rw [if_neg hvS, hFE u huS v hvu]
    · have hnhds : ((S : Set ℂ))ᶜ ∈ 𝓝 u :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using huS)
      have hFana : AnalyticAt ℂ F u :=
        (hana u hu huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
          analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))
      refine hFana.congr ?_
      filter_upwards [hnhds] with v hv
      have hvS : v ∉ S := by simpa using hv
      simp only [hG, if_neg hvS]
  have hSb : ∀ p ∈ S, p ∉ rectBoundary z w := fun p hp ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := hS p hp
    exact notMem_rectBoundary_of_mem_Ioo
      ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
      ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hbK : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := rectBoundary_subset
  have hG0 : rectIntegral G z w = 0 := by
    apply rectIntegral_eq_zero_of_differentiable_on_off_countable G z w ∅ countable_empty
    · exact fun u hu ↦ (hGana u hu).continuousAt.continuousWithinAt
    · intro u hu
      apply (hGana u _).differentiableAt
      have h' := hu.1
      rw [mem_reProdIm] at h' ⊢
      exact ⟨Ioo_subset_Icc_self h'.1, Ioo_subset_Icc_self h'.2⟩
  have hGF : rectIntegral G z w = rectIntegral F z w := by
    apply rectIntegral_congr
    intro u hu
    have huS : u ∉ S := fun h ↦ hSb u h hu
    simp only [hG, if_neg huS]
  have hPc : ∀ q ∈ S, ContinuousOn (principalPart f q) (rectBoundary z w) := fun q hq u hu ↦
    (analyticAt_principalPart f (fun (h : u = q) ↦ hSb q hq (h ▸ hu))).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (rectBoundary z w) := fun u hu ↦ by
    have huS : u ∉ S := fun h ↦ hSb u h hu
    exact ((hana u (hbK hu) huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
      analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))).continuousAt.continuousWithinAt
  have hsplit : rectIntegral f z w =
      rectIntegral F z w + ∑ q ∈ S, rectIntegral (principalPart f q) z w := by
    rw [← rectIntegral_finset_sum S hPc, ← rectIntegral_add hFc (continuousOn_finsetSum S hPc)]
    congr 1
    funext u
    simp only [hF]
    ring
  rw [hsplit, ← hGF, hG0, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hS q hq
  exact rectIntegral_principalPart f h1 h2 h3 h4

end Elliptic
end GroundTheory.Global
end
end

section
open Complex Filter Topology Set
open scoped Interval Real

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L : PeriodPair}

lemma IsPeriodic.residue_add {f : ℂ → ℂ} (hp : IsPeriodic L f) (hf : Meromorphic f) {l : ℂ}
    (hl : l ∈ L.lattice) (z : ℂ) : residue f (z + l) = residue f z := by
  rw [← residue_comp_add (hf (z + l)), hp.comp_add hl]

lemma IsPeriodic.residue_eq_of_mk_eq {f : ℂ → ℂ} (hp : IsPeriodic L f) (hf : Meromorphic f)
    {z w : ℂ} (h : Torus.mk L z = Torus.mk L w) : residue f z = residue f w := by
  have hzw := (Torus.mk_eq_mk_iff L).1 h
  have := hp.residue_add hf hzw w
  rwa [add_sub_cancel] at this

variable (L) in

def torusResidue (f : ℂ → ℂ) (x : Torus L) : ℂ :=
  residue f x.out

lemma torusResidue_mk {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (z : ℂ) :
    torusResidue L f (Torus.mk L z) = residue f z :=
  hf.2.residue_eq_of_mk_eq hf.1 (QuotientAddGroup.out_eq' (Torus.mk L z))

variable (L) in
lemma ω₁_ne_zero : L.ω₁ ≠ 0 := by
  intro h
  have := LinearIndependent.pair_iff.mp L.indep 1 0 (by simp [h])
  simp at this

variable (L) in
lemma im_ω₂_div_ω₁_ne_zero : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro him
  have hc := ω₁_ne_zero L
  set τ := L.ω₂ / L.ω₁ with hτdef
  have hτ : ((τ.re : ℝ) : ℂ) = τ := Complex.ext (by simp) (by simp [him])
  have key := LinearIndependent.pair_iff.mp L.indep τ.re (-1) (by
    rw [Complex.real_smul, Complex.real_smul, hτ, hτdef]
    push_cast
    field_simp
    ring)
  norm_num at key

theorem finsum_torusResidue_eq_zero {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, torusResidue L f x = 0 := by
  classical
  obtain ⟨hmer, hper⟩ := hf
  have hω₁ : L.ω₁ ≠ 0 := ω₁_ne_zero L
  set c := L.ω₁ with hc_def
  have hc : c ≠ 0 := ω₁_ne_zero L
  have hcL : c ∈ L.lattice := L.ω₁_mem_lattice
  obtain ⟨τ, s, hs, hω₂, hτ⟩ : ∃ τ : ℂ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      L.ω₂ = (s : ℂ) * (c * τ) ∧ 0 < τ.im := by
    rcases lt_or_gt_of_ne (im_ω₂_div_ω₁_ne_zero L) with h | h
    · refine ⟨-(L.ω₂ / L.ω₁), -1, Or.inr rfl, ?_, by simpa using h⟩
      rw [hc_def]
      have h0 := ω₁_ne_zero L
      field_simp
      push_cast
      ring
    · refine ⟨L.ω₂ / L.ω₁, 1, Or.inl rfl, ?_, h⟩
      rw [hc_def]
      have h0 := ω₁_ne_zero L
      field_simp
      push_cast
      ring
  have hτL : c * τ ∈ L.lattice := by
    have h2 := L.ω₂_mem_lattice
    rcases hs with rfl | rfl
    · simpa [hω₂] using h2
    · simpa [hω₂] using L.lattice.neg_mem h2
  set h := τ.im with hh
  set g : ℂ → ℂ := fun w ↦ f (c * w) with hg_def
  have hg1 : ∀ u, g (u + 1) = g u := fun u ↦ by
    simp only [hg_def, mul_add, mul_one]
    exact hper _ _ hcL
  have hgτ : ∀ u, g (u + τ) = g u := fun u ↦ by
    simp only [hg_def, mul_add]
    exact hper _ _ hτL
  have hgmer : Meromorphic g := fun w ↦
    (hmer (c * w)).comp_analyticAt (g := fun w ↦ c * w) (by fun_prop)

  have hScount : (singularSet g).Countable := by
    have e : singularSet g = ⋃ n : ℕ, Metric.closedBall (0 : ℂ) n ∩ singularSet g := by
      ext z
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
        exact ⟨n, hn, hz⟩
      · rintro ⟨n, -, hz⟩
        exact hz
    rw [e]
    exact countable_iUnion fun n ↦
      (finite_inter_singularSet hgmer (isCompact_closedBall 0 (n : ℝ))).countable

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ ((fun s : ℂ ↦ s.re) '' singularSet g ∪
      (fun s : ℂ ↦ s.re - 1) '' singularSet g)ᶜ :=
    (((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ ∈ ((fun s : ℂ ↦ s.im) '' singularSet g ∪
      (fun s : ℂ ↦ s.im - h) '' singularSet g)ᶜ :=
    (((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty
  set a : ℂ := x₀ + y₀ * I with ha
  set b : ℂ := a + 1 + h * I with hb
  have ha_re : a.re = x₀ := by simp [ha]
  have ha_im : a.im = y₀ := by simp [ha]
  have hb_re : b.re = x₀ + 1 := by simp [hb, ha]
  have hb_im : b.im = y₀ + h := by simp [hb, ha]
  set K : Set ℂ := [[a.re, b.re]] ×ℂ [[a.im, b.im]] with hK_def
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hKmem : ∀ u : ℂ, u ∈ K ↔ u.re ∈ Icc x₀ (x₀ + 1) ∧ u.im ∈ Icc y₀ (y₀ + h) := by
    intro u
    rw [hK_def, mem_reProdIm, ha_re, hb_re, ha_im, hb_im, uIcc_of_le (by linarith),
      uIcc_of_le (by linarith)]
  set T : Finset ℂ := (finite_inter_singularSet hgmer hK).toFinset with hT
  have hTmem : ∀ p, p ∈ T ↔ p ∈ K ∧ p ∈ singularSet g := by
    intro p
    simp [hT]

  have hTin : ∀ p ∈ T, x₀ < p.re ∧ p.re < x₀ + 1 ∧ y₀ < p.im ∧ p.im < y₀ + h := by
    intro p hp
    obtain ⟨hpK, hpS⟩ := (hTmem p).1 hp
    obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := (hKmem p).1 hpK
    have nr1 : p.re ≠ x₀ := fun e ↦ hx₀ (Or.inl ⟨p, hpS, e⟩)
    have nr2 : p.re ≠ x₀ + 1 := fun e ↦ hx₀ (Or.inr ⟨p, hpS, by simp [e]⟩)
    have ni1 : p.im ≠ y₀ := fun e ↦ hy₀ (Or.inl ⟨p, hpS, e⟩)
    have ni2 : p.im ≠ y₀ + h := fun e ↦ hy₀ (Or.inr ⟨p, hpS, by simp [e]⟩)
    exact ⟨lt_of_le_of_ne r1 (Ne.symm nr1), lt_of_le_of_ne r2 nr2,
      lt_of_le_of_ne i1 (Ne.symm ni1), lt_of_le_of_ne i2 ni2⟩

  have hsum0 : ∑ p ∈ T, residue g p = 0 := by
    have hres := rectIntegral_eq_sum_residue (f := g) (z := a) (w := b) T
      (fun p hp ↦ by
        obtain ⟨r1, r2, i1, i2⟩ := hTin p hp
        exact ⟨by rwa [ha_re], by rwa [hb_re], by rwa [ha_im], by rwa [hb_im]⟩)
      (fun p _ ↦ hgmer p)
      (fun u hu huT ↦ by
        by_contra hna
        exact huT ((hTmem u).2 ⟨hu, hna⟩))
    have hper0 : rectIntegral g a b = 0 := rectIntegral_eq_zero_of_periodic hg1 hgτ a
    rw [hper0] at hres
    have h2pi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
    exact (mul_eq_zero.1 hres.symm).resolve_left h2pi

  set φ : ℂ → Torus L := fun p ↦ Torus.mk L (c * p) with hφ
  have hlat : ∀ m n : ℤ, (m : ℂ) * c + (n : ℂ) * (c * τ) ∈ L.lattice := fun m n ↦
    L.lattice.add_mem (by simpa [zsmul_eq_mul] using L.lattice.smul_mem m hcL)
      (by simpa [zsmul_eq_mul] using L.lattice.smul_mem n hτL)

  have hsupp : Function.support (torusResidue L f) ⊆ ↑(T.image φ) := by
    intro x hx
    set z := x.out with hz
    have hxz : Torus.mk L z = x := QuotientAddGroup.out_eq' x
    have hnz : residue f z ≠ 0 := hx
    have hfz : ¬ AnalyticAt ℂ f z := fun ha ↦ hnz (residue_eq_zero_of_analyticAt ha)
    set w := z / c with hw
    set n : ℤ := ⌊(w.im - y₀) / h⌋ with hn
    set p₁ : ℂ := w - n * τ with hp₁
    set m : ℤ := ⌊p₁.re - x₀⌋ with hm
    set p : ℂ := p₁ - m with hp
    have hp_re : p.re = p₁.re - m := by simp [hp]
    have hp_im : p.im = w.im - n * h := by simp [hp, hp₁, hh]
    have hn1 := Int.floor_le ((w.im - y₀) / h)
    have hn2 := Int.lt_floor_add_one ((w.im - y₀) / h)
    have hm1 := Int.floor_le (p₁.re - x₀)
    have hm2 := Int.lt_floor_add_one (p₁.re - x₀)
    rw [← hn] at hn1 hn2
    rw [← hm] at hm1 hm2
    rw [le_div_iff₀ hτ] at hn1
    rw [div_lt_iff₀ hτ] at hn2
    have hpK : p ∈ K := by
      rw [hKmem, hp_re, hp_im]
      refine ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
    have hcp : z = c * p + ((m : ℂ) * c + (n : ℂ) * (c * τ)) := by
      simp only [hp, hp₁, hw]
      field_simp
      ring
    have hpS : p ∈ singularSet g := by
      intro hga
      apply hfz
      have h1 : AnalyticAt ℂ (fun z' ↦ g (c⁻¹ * z')) (c * p) := by
        have : AnalyticAt ℂ (fun z' ↦ c⁻¹ * z') (c * p) := by fun_prop
        exact hga.comp_of_eq this (by field_simp)
      have h2 : (fun z' ↦ g (c⁻¹ * z')) = f := by
        funext z'
        simp only [hg_def]
        congr 1
        field_simp
      rw [h2] at h1
      rw [hcp]
      exact (hper.analyticAt_add_iff (hlat m n) (c * p)).2 h1
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hTmem p).2 ⟨hpK, hpS⟩, ?_⟩)
    rw [← hxz, hφ]
    exact ((Torus.mk_eq_mk_iff L).2 (by rw [hcp]; simpa using hlat m n)).symm

  have hinj : Set.InjOn φ ↑T := by
    intro p hp q hq hpq
    obtain ⟨pr1, pr2, pi1, pi2⟩ := hTin p hp
    obtain ⟨qr1, qr2, qi1, qi2⟩ := hTin q hq
    have hdiff := (Torus.mk_eq_mk_iff L).1 hpq
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 hdiff
    have hk : p - q = (m : ℂ) + ((n * s : ℤ) : ℂ) * τ := by
      have e : c * (p - q) = c * ((m : ℂ) + ((n * s : ℤ) : ℂ) * τ) := by
        rw [mul_sub, ← hmn, hω₂]
        push_cast
        ring
      exact mul_left_cancel₀ hc e
    set k : ℤ := n * s with hkdef
    have him := congrArg Complex.im hk
    have hre := congrArg Complex.re hk
    simp only [sub_im, add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add,
      sub_re, add_re, intCast_re, mul_re, intCast_im, zero_mul, sub_zero] at him hre
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) * h < h := by rw [hh]; linarith
      have h2 : -h < (k : ℝ) * h := by rw [hh]; linarith
      have h3 : (k : ℝ) < 1 := by
        by_contra hc'
        rw [not_lt] at hc'
        nlinarith
      have h4 : (-1 : ℝ) < k := by
        by_contra hc'
        rw [not_lt] at hc'
        nlinarith
      have h5 : k < 1 := by exact_mod_cast h3
      have h6 : -1 < k := by exact_mod_cast h4
      omega
    rw [hk0] at hre him
    simp only [Int.cast_zero, zero_mul, add_zero, sub_eq_zero] at hre him
    have hm0 : m = 0 := by
      have h3 : (m : ℝ) < 1 := by linarith
      have h4 : (-1 : ℝ) < m := by linarith
      have h5 : m < 1 := by exact_mod_cast h3
      have h6 : -1 < m := by exact_mod_cast h4
      omega
    rw [hm0] at hre
    simp only [Int.cast_zero, sub_eq_zero] at hre
    exact Complex.ext hre him
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]
  have hterm : ∀ p ∈ T, torusResidue L f (φ p) = c * residue g p := by
    intro p _
    rw [hφ, torusResidue_mk ⟨hmer, hper⟩,
      show residue g p = c⁻¹ * residue f (c * p) from residue_comp_mul hc (hmer _)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum0, mul_zero]

end Elliptic
end GroundTheory.Global
end
end

section
open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L : PeriodPair}

variable (L) in

def torusOrder (f : ℂ → ℂ) (x : Torus L) : ℤ :=
  (meromorphicOrderAt f x.out).untopD 0

lemma torusOrder_mk {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (z : ℂ) :
    torusOrder L f (Torus.mk L z) = (meromorphicOrderAt f z).untopD 0 := by
  have h := (Torus.mk_eq_mk_iff L).1 (QuotientAddGroup.out_eq' (Torus.mk L z))
  have := hf.2.meromorphicOrderAt_add h z
  rw [add_sub_cancel] at this
  rw [torusOrder, this]

lemma isEllipticFunction_logDeriv {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    IsEllipticFunction L (logDeriv f) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ ?_⟩
  · have : logDeriv f = fun w ↦ deriv f w / f w := rfl
    rw [this]
    exact (hf.1 z).deriv.div (hf.1 z)
  · simp only [logDeriv_apply]
    rw [hf.2 z l hl]
    congr 1
    rw [← deriv_comp_add_const, hf.2.comp_add hl]

lemma residue_logDeriv_eq_untopD {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    residue (logDeriv f) z = (((meromorphicOrderAt f z).untopD 0 : ℤ) : ℂ) := by
  by_cases htop : meromorphicOrderAt f z = ⊤
  · rw [htop, WithTop.untopD_top, Int.cast_zero]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hmer : MeromorphicAt (logDeriv f) z := by
      have : logDeriv f = fun w ↦ deriv f w / f w := rfl
      rw [this]
      exact hf.deriv.div hf
    have h0 : logDeriv f =ᶠ[𝓝[≠] z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [htop] with w hw
      simp [logDeriv_apply, hw]
    rw [residue_congr hmer h0]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hn, WithTop.untopD_coe]
    exact residue_logDeriv hf hn.symm

lemma torusResidue_logDeriv {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (x : Torus L) :
    torusResidue L (logDeriv f) x = (torusOrder L f x : ℂ) :=
  residue_logDeriv_eq_untopD (hf.1 _)

lemma finite_support_torusResidue {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusResidue L f)).Finite := by
  refine (finite_image_singularSet L hf.1 hf.2).subset ?_
  intro x hx
  refine ⟨x.out, fun ha ↦ hx (residue_eq_zero_of_analyticAt ha), QuotientAddGroup.out_eq' x⟩

lemma finite_support_torusOrder {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusOrder L f)).Finite := by
  refine (finite_support_torusResidue (isEllipticFunction_logDeriv hf)).subset ?_
  intro x hx
  simp only [Function.mem_support, torusResidue_logDeriv hf] at hx ⊢
  exact_mod_cast hx

theorem finsum_torusOrder_eq_zero {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, torusOrder L f x = 0 := by
  have h := finsum_torusResidue_eq_zero (isEllipticFunction_logDeriv hf)
  simp_rw [torusResidue_logDeriv hf] at h
  have hc := (Int.castAddHom ℂ).map_finsum (finite_support_torusOrder hf)
  simp only [Int.coe_castAddHom] at hc
  rw [← hc] at h
  exact_mod_cast h

variable (L) in

def degree (f : ℂ → ℂ) : ℕ :=
  ∑ᶠ x : Torus L, (-torusOrder L f x).toNat

lemma toNat_neg_untopD_sub_const {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) (c : ℂ) :
    (-(meromorphicOrderAt (fun w ↦ f w - c) z).untopD 0).toNat =
      (-(meromorphicOrderAt f z).untopD 0).toNat := by
  have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
  have e : (fun w ↦ f w - c) = f + fun _ ↦ -c := by
    funext w; simp [sub_eq_add_neg]
  have hc0 : 0 ≤ meromorphicOrderAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicOrderAt_nonneg
  rw [e]
  by_cases hneg : meromorphicOrderAt f z < 0
  · rw [meromorphicOrderAt_add_eq_left_of_lt hc (hneg.trans_le hc0)]
  · push Not at hneg
    have h1 : 0 ≤ meromorphicOrderAt (f + fun _ ↦ -c) z :=
      le_trans (le_min hneg hc0) (meromorphicOrderAt_add hf hc)
    have key : ∀ o : WithTop ℤ, 0 ≤ o → (-(o.untopD 0)).toNat = 0 := by
      intro o ho
      induction o with
      | top => simp
      | coe n =>
        simp only [WithTop.untopD_coe]
        have : (0 : ℤ) ≤ n := by exact_mod_cast ho
        omega
    rw [key _ h1, key _ hneg]

lemma nonneg_of_toNat_neg_untopD_eq_zero {o : WithTop ℤ} (h : (-(o.untopD 0)).toNat = 0) :
    0 ≤ o := by
  induction o with
  | top => exact le_top
  | coe n =>
    simp only [WithTop.untopD_coe] at h
    exact_mod_cast (by omega : (0 : ℤ) ≤ n)

lemma toNat_neg_untopD_eq_zero_of_nonneg {o : WithTop ℤ} (h : 0 ≤ o) :
    (-(o.untopD 0)).toNat = 0 := by
  induction o with
  | top => simp
  | coe n =>
    simp only [WithTop.untopD_coe]
    have : (0 : ℤ) ≤ n := by exact_mod_cast h
    omega

lemma eq_neg_one_of_toNat_neg_untopD_eq_one {o : WithTop ℤ} (h : (-(o.untopD 0)).toNat = 1) :
    o = ((-1 : ℤ) : WithTop ℤ) := by
  induction o with
  | top => simp at h
  | coe n =>
    simp only [WithTop.untopD_coe] at h
    have : n = -1 := by omega
    rw [this]

lemma eventually_nhdsNE_of_eventually_codiscrete {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z)
    (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, p z := by
  rw [Filter.Eventually, codiscrete, mem_codiscreteWithin] at h
  have := disjoint_principal_right.1 (h x (mem_univ x))
  filter_upwards [this] with z hz
  by_contra hpz
  exact hz ⟨mem_univ z, hpz⟩

lemma finite_support_toNat_neg_torusOrder {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support fun x ↦ (-torusOrder L f x).toNat).Finite :=
  (finite_support_torusOrder hf).subset fun x hx ↦ by
    simp only [Function.mem_support] at hx ⊢
    omega

theorem finsum_toNat_torusOrder_sub_const {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder L (fun z ↦ f z - c) x).toNat = degree L f := by
  classical
  have hg : IsEllipticFunction L (fun z ↦ f z - c) := by
    refine ⟨fun z ↦ ?_, fun z l hl ↦ by simp only [hf.2 z l hl]⟩
    have := hf.1 z
    fun_prop
  set g : ℂ → ℂ := fun z ↦ f z - c with hgdef
  have hfin := finite_support_torusOrder hg
  set s := hfin.toFinset with hs
  have hsupp : Function.support (torusOrder L g) ⊆ ↑s := by simp [hs]
  have hsum := finsum_torusOrder_eq_zero hg
  rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum
  have h1 : ∑ᶠ x, (torusOrder L g x).toNat = ∑ x ∈ s, (torusOrder L g x).toNat :=
    finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by
      simp only [Function.mem_support] at hx ⊢
      omega)
  have hpt : ∀ x, (-torusOrder L f x).toNat = (-torusOrder L g x).toNat := fun x ↦
    (toNat_neg_untopD_sub_const (hf.1 _) c).symm
  have h2 : degree L f = ∑ x ∈ s, (-torusOrder L g x).toNat := by
    rw [degree]
    simp_rw [hpt]
    exact finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by
      simp only [Function.mem_support] at hx ⊢
      omega)
  rw [h1, h2]
  have key : ∀ x, ((torusOrder L g x).toNat : ℤ) - ((-torusOrder L g x).toNat : ℤ) =
      torusOrder L g x := fun x ↦ Int.toNat_sub_toNat_neg _
  have : ((∑ x ∈ s, (torusOrder L g x).toNat : ℕ) : ℤ) =
      ((∑ x ∈ s, (-torusOrder L g x).toNat : ℕ) : ℤ) := by
    push_cast
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simp only [key]
    exact hsum
  exact_mod_cast this


lemma eq_zero_of_finsum_eq_zero_nat {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (h : ∑ᶠ x, u x = 0) (x : α) : u x = 0 := by
  classical
  by_contra hx
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset) (by simp)] at h
  exact hx ((Finset.sum_eq_zero_iff.1 h) x (by simpa using hx))

theorem degree_ne_one {f : ℂ → ℂ} (hf : IsEllipticFunction L f) : degree L f ≠ 1 := by
  classical
  intro h1
  set u : Torus L → ℕ := fun x ↦ (-torusOrder L f x).toNat with hu
  have hfin : (Function.support u).Finite := finite_support_toNat_neg_torusOrder hf
  set s := hfin.toFinset with hs
  have hsum : ∑ x ∈ s, u x = 1 := by
    rw [← finsum_eq_sum_of_support_subset u (by simp [hs])]
    exact h1
  obtain ⟨x₀, hx₀s, hx₀⟩ : ∃ x₀ ∈ s, u x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at hsum
    exact zero_ne_one hsum
  have hsplit := Finset.add_sum_erase s u hx₀s
  rw [hsum] at hsplit
  have hux₀ : u x₀ = 1 := by omega
  have hrest : ∀ x, x ≠ x₀ → u x = 0 := by
    intro x hx
    by_cases hxs : x ∈ s
    · have h0 : ∑ y ∈ s.erase x₀, u y = 0 := by omega
      exact Finset.sum_eq_zero_iff.1 h0 x (Finset.mem_erase.2 ⟨hx, hxs⟩)
    · simpa [hs] using hxs
  have hres := finsum_torusResidue_eq_zero hf
  rw [finsum_eq_single _ x₀ (fun x hx ↦ ?_)] at hres
  · have hord := eq_neg_one_of_toNat_neg_untopD_eq_one hux₀
    exact residue_ne_zero_of_meromorphicOrderAt_eq_neg_one (hf.1 _) hord hres
  · exact residue_eq_zero_of_meromorphicOrderAt_nonneg (hf.1 _)
      (nonneg_of_toNat_neg_untopD_eq_zero (hrest x hx))

theorem degree_weierstrassP : degree L ℘[L] = 2 := by
  have hP : IsEllipticFunction L ℘[L] := isEllipticFunction_weierstrassP
  have h0 : (0 : Torus L) = Torus.mk L 0 := (QuotientAddGroup.mk_zero _).symm
  rw [degree, finsum_eq_single _ (0 : Torus L) ?_]
  · rw [h0, torusOrder_mk hP]
    have h2 : meromorphicOrderAt ℘[L] 0 = ((-2 : ℤ) : WithTop ℤ) := by
      rw [L.order_weierstrassP 0 (zero_mem _)]
      norm_num
    rw [h2, WithTop.untopD_coe]
    rfl
  · intro x hx
    obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
    have hz : z ∉ L.lattice := fun h ↦ hx (by
      rw [h0]
      exact (Torus.mk_eq_mk_iff L).2 (by simpa using h))
    rw [torusOrder_mk hP]
    exact toNat_neg_untopD_eq_zero_of_nonneg
      (L.analyticOnNhd_weierstrassP z hz).meromorphicOrderAt_nonneg

end Elliptic
end GroundTheory.Global
end
end

section
open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable (L : PeriodPair)

def weierstrassCurve : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(L.g₂ / 4)
  a₆ := -(L.g₃ / 4)

instance : (weierstrassCurve L).IsShortNF := ⟨rfl, rfl, rfl⟩

@[simp] lemma weierstrassCurve_a₁ : (weierstrassCurve L).a₁ = 0 := rfl
@[simp] lemma weierstrassCurve_a₂ : (weierstrassCurve L).a₂ = 0 := rfl
@[simp] lemma weierstrassCurve_a₃ : (weierstrassCurve L).a₃ = 0 := rfl
@[simp] lemma weierstrassCurve_a₄ : (weierstrassCurve L).a₄ = -(L.g₂ / 4) := rfl
@[simp] lemma weierstrassCurve_a₆ : (weierstrassCurve L).a₆ = -(L.g₃ / 4) := rfl

def discr : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

theorem weierstrassCurve_Δ : (weierstrassCurve L).Δ = discr L := by
  rw [WeierstrassCurve.Δ_of_isShortNF, discr]
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆]
  ring

theorem weierstrassCurve_equation_iff (x Y : ℂ) :
    (weierstrassCurve L).toAffine.Equation x Y ↔
      (2 * Y) ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆]
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    linear_combination h / 4

theorem equation_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    (weierstrassCurve L).toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [weierstrassCurve_equation_iff, mul_div_cancel₀ _ two_ne_zero]
  exact L.derivWeierstrassP_sq z hz

variable {L}

lemma sum_le_finsum_of_finite {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (s : Finset α) : ∑ x ∈ s, u x ≤ ∑ᶠ x, u x := by
  classical
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset ∪ s) (fun x hx ↦ by simp [hx])]
  exact Finset.sum_le_sum_of_subset Finset.subset_union_right

lemma isEllipticFunction_weierstrassP_sub (c : ℂ) :
    IsEllipticFunction L (fun z ↦ ℘[L] z - c) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ by simp only [isPeriodic_weierstrassP z l hl]⟩
  have := L.meromorphic_weierstrassP z
  fun_prop

lemma meromorphicOrderAt_weierstrassP_sub_ne_top (c z : ℂ) :
    meromorphicOrderAt (fun w ↦ ℘[L] w - c) z ≠ ⊤ := by
  intro htop
  have h1 := meromorphicOrderAt_eq_top_iff.1 htop
  have h2 := eventually_nhdsNE_of_eventually_codiscrete
    (eventually_codiscrete_eval_weierstrassP_ne_zero (L := L) (Polynomial.X_sub_C_ne_zero c)) z
  obtain ⟨w, hw1, hw2⟩ := (h1.and h2).exists
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hw2
  exact hw2 hw1

lemma le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) {n : ℕ}
    (h : ∀ i < n, iteratedDeriv i (fun w ↦ ℘[L] w - c) z = 0) :
    n ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat := by
  have ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z :=
    (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have hne := meromorphicOrderAt_weierstrassP_sub_ne_top (L := L) c z
  have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).2 h
  rw [torusOrder_mk (isEllipticFunction_weierstrassP_sub c), ha.meromorphicOrderAt_eq]
  rw [ha.meromorphicOrderAt_eq] at hne
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt (fun w ↦ ℘[L] w - c) z :=
    ENat.ne_top_iff_exists.1 (fun h ↦ hne (by simp [h]))
  rw [← hm] at hle ⊢
  simp only [ENat.map_natCast, WithTop.untopD_coe, Int.toNat_natCast]
  exact_mod_cast hle

lemma one_le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) (hc : ℘[L] z = c) :
    1 ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat :=
  le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by
    obtain rfl : i = 0 := by omega
    simp [hc]

lemma two_le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) (hc : ℘[L] z = c)
    (h' : ℘'[L] z = 0) :
    2 ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat :=
  le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by
    interval_cases i
    · simp [hc]
    · rw [iteratedDeriv_one, deriv_sub_const, L.deriv_weierstrassP]
      exact h'

lemma finsum_toNat_torusOrder_weierstrassP_sub (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat = 2 := by
  rw [finsum_toNat_torusOrder_sub_const isEllipticFunction_weierstrassP c, degree_weierstrassP]

lemma finite_support_toNat_torusOrder_weierstrassP_sub (c : ℂ) :
    (Function.support fun x ↦ (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat).Finite :=
  (finite_support_torusOrder (isEllipticFunction_weierstrassP_sub c)).subset fun x hx ↦ by
    simp only [Function.mem_support] at hx ⊢
    omega

lemma torus_mk_ne {z w : ℂ} (h : z - w ∉ L.lattice) : Torus.mk L z ≠ Torus.mk L w :=
  fun e ↦ h ((Torus.mk_eq_mk_iff L).1 e)

theorem derivWeierstrassP_eq_zero_of_two_mul_mem {w : ℂ} (h : 2 * w ∈ L.lattice) :
    ℘'[L] w = 0 := by
  have h1 : ℘'[L] (w - 2 * w) = ℘'[L] w := L.derivWeierstrassP_sub_coe w ⟨_, h⟩
  rw [show w - 2 * w = -w by ring, L.derivWeierstrassP_neg] at h1
  linear_combination -h1 / 2

theorem two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero {w : ℂ} (hw : w ∉ L.lattice) :
    2 * w ∈ L.lattice ↔ ℘'[L] w = 0 := by
  classical
  refine ⟨derivWeierstrassP_eq_zero_of_two_mul_mem, fun h' ↦ ?_⟩
  by_contra h2
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hne : Torus.mk L w ≠ Torus.mk L (-w) :=
    torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])
  have hsum := sum_le_finsum_of_finite (finite_support_toNat_torusOrder_weierstrassP_sub (℘[L] w))
    {Torus.mk L w, Torus.mk L (-w)}
  rw [finsum_toNat_torusOrder_weierstrassP_sub, Finset.sum_pair hne] at hsum
  have o1 := two_le_toNat_torusOrder_weierstrassP_sub hw rfl h'
  have o2 := one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)
  omega

theorem sub_mem_or_add_mem_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h : ℘[L] z = ℘[L] w) :
    z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hfin := finite_support_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)
  have htot := finsum_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)
  have oz := one_le_toNat_torusOrder_weierstrassP_sub hz h
  have hzw : Torus.mk L z ≠ Torus.mk L w := torus_mk_ne h1
  by_cases h2w : 2 * w ∈ L.lattice
  · have hsum := sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w}
    rw [htot, Finset.sum_pair hzw] at hsum
    have ow := two_le_toNat_torusOrder_weierstrassP_sub hw rfl
      (derivWeierstrassP_eq_zero_of_two_mul_mem h2w)
    omega
  · have hzw' : Torus.mk L z ≠ Torus.mk L (-w) := torus_mk_ne (by rwa [sub_neg_eq_add])
    have hww' : Torus.mk L w ≠ Torus.mk L (-w) :=
      torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])
    have hsum := sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w, Torus.mk L (-w)}
    rw [htot, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hzw, hzw'⟩), Finset.sum_pair hww'] at hsum
    have ow := one_le_toNat_torusOrder_weierstrassP_sub hw rfl
    have ow' := one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)
    omega

lemma notMem_lattice_of_eq {x : ℂ} (α β : ℚ) (hx : x = α * L.ω₁ + β * L.ω₂)
    (h : ¬(α.den = 1 ∧ β.den = 1)) : x ∉ L.lattice := by
  rw [hx]
  exact fun hm ↦ h (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice.1 hm)

lemma halfPeriod_facts :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₁ / 2) + ℘[L] (L.ω₂ / 2) + ℘[L] ((L.ω₁ + L.ω₂) / 2) = 0 ∧
      4 * (℘[L] (L.ω₁ / 2) ^ 2 + ℘[L] (L.ω₁ / 2) * ℘[L] (L.ω₂ / 2) + ℘[L] (L.ω₂ / 2) ^ 2) =
        L.g₂ ∧
      L.g₃ = 4 * ℘[L] (L.ω₁ / 2) ^ 3 - L.g₂ * ℘[L] (L.ω₁ / 2) := by
  set e1 := ℘[L] (L.ω₁ / 2)
  set e2 := ℘[L] (L.ω₂ / 2)
  set e3 := ℘[L] ((L.ω₁ + L.ω₂) / 2)
  have n1 : L.ω₁ / 2 ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have n2 : L.ω₂ / 2 ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have n3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice :=
    notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num)
  have root : ∀ u, u ∉ L.lattice → 2 * u ∈ L.lattice →
      4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := fun u hu h2 ↦ by
    rw [← L.derivWeierstrassP_sq u hu, derivWeierstrassP_eq_zero_of_two_mul_mem h2]
    ring
  have f1 := root _ n1 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice)
  have f2 := root _ n2 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice)
  have f3 := root _ n3 (by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)
  have d12 : e1 ≠ e2 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n1 n2 h with h' | h'
    · exact notMem_lattice_of_eq (1 / 2) (-1 / 2) (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num) h'
  have d13 : e1 ≠ e3 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n1 n3 h with h' | h'
    · exact notMem_lattice_of_eq 0 (-1 / 2) (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq 1 (1 / 2) (by push_cast; ring) (by norm_num) h'
  have d23 : e2 ≠ e3 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n2 n3 h with h' | h'
    · exact notMem_lattice_of_eq (-1 / 2) 0 (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq (1 / 2) 1 (by push_cast; ring) (by norm_num) h'
  have s12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = L.g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 d12) (by linear_combination f1 - f2)
  have s13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = L.g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 d13) (by linear_combination f1 - f3)
  have hs : e1 + e2 + e3 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 d23) (by linear_combination (s12 - s13) / 4)
  exact ⟨d12, d13, d23, hs, s12, by linear_combination -f1⟩

variable (L)

theorem weierstrassP_halfPeriods_ne :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) :=
  let h := halfPeriod_facts (L := L)
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem discr_eq :
    discr L = 16 * ((℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2)) *
      (℘[L] (L.ω₁ / 2) - ℘[L] ((L.ω₁ + L.ω₂) / 2)) *
      (℘[L] (L.ω₂ / 2) - ℘[L] ((L.ω₁ + L.ω₂) / 2))) ^ 2 := by
  obtain ⟨-, -, -, hs, s12, hg3⟩ := halfPeriod_facts (L := L)
  rw [discr, hg3, ← s12, show ℘[L] ((L.ω₁ + L.ω₂) / 2) = -℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2) by
    linear_combination hs]
  ring

theorem discr_ne_zero : discr L ≠ 0 := by
  obtain ⟨d12, d13, d23⟩ := weierstrassP_halfPeriods_ne L
  rw [discr_eq]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 d12)
    (sub_ne_zero.2 d13)) (sub_ne_zero.2 d23)))

theorem weierstrassCurve_Δ_ne_zero : (weierstrassCurve L).Δ ≠ 0 := by
  rw [weierstrassCurve_Δ]
  exact discr_ne_zero L

instance : (weierstrassCurve L).IsElliptic :=
  ⟨isUnit_iff_ne_zero.2 (weierstrassCurve_Δ_ne_zero L)⟩

theorem weierstrassCurve_j : (weierstrassCurve L).j = 1728 * L.g₂ ^ 3 / discr L := by
  rw [WeierstrassCurve.j_of_isShortNF, discr]
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆]
  have h := discr_ne_zero L
  rw [discr] at h
  have h1 : 4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0 := by
    intro h0
    apply h
    linear_combination -16 * h0
  rw [div_eq_div_iff h1 h]
  ring

end Elliptic
end GroundTheory.Global
end
end
