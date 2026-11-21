import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible

open Finset Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

namespace CommonScale

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

open Classical in
lemma primePower_kernel_re (D : ArithData H) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i)
    (g : E0 × H) : (Kc D (p ^ i) g).re =
      if g - i • D.frob p ∈ D.inertia p then 2 / (Nat.card (D.inertia p) : ℝ) else 0 := by
  rw [Kc, orthogonality_ramified D p i hp hi g]
  split_ifs
  · have hcast : ((2 / (Nat.card (D.inertia p) : ℝ) : ℝ) : ℂ) =
        2 / (Nat.card (D.inertia p) : ℂ) := by push_cast; rfl
    rw [← hcast, Complex.ofReal_re]
  · rfl

lemma primePower_nonneg (D : ArithData H) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i)
    (g : E0 × H) : 0 ≤ (Kc D (p ^ i) g).re := by
  classical
  rw [primePower_kernel_re D hp hi]
  split_ifs <;> positivity

open Classical in
/-- A set of labels receives twice the fraction of the Frobenius coset it contains. -/
theorem primePower_mass (D : ArithData H) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i)
    (S : Finset (E0 × H)) :
    ∑ g ∈ S, (Kc D (p ^ i) g).re =
      ((S.filter fun g => g - i • D.frob p ∈ D.inertia p).card : ℝ) *
        (2 / (Nat.card (D.inertia p) : ℝ)) := by
  simp_rw [primePower_kernel_re D hp hi]
  rw [← Finset.sum_filter]
  simp

theorem primePower_total (D : ArithData H) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    ∑ g : E0 × H, (Kc D (p ^ i) g).re = 2 := by
  classical
  rw [primePower_mass D hp hi]
  have hc : (univ.filter fun g => g - i • D.frob p ∈ D.inertia p).card = Nat.card (D.inertia p) := by
    rw [natCard_eq_filter]
    apply Finset.card_bij (fun (g : E0 × H) _ => g - i • D.frob p)
    · intro g hg; simpa using hg
    · intro a _ b _ hab; exact sub_left_inj.mp hab
    · intro h hh; exact ⟨h + i • D.frob p, by simpa using hh, by simp⟩
  rw [hc]
  have hpos : 0 < Nat.card (D.inertia p) := Nat.card_pos
  field_simp

/-- Raising a thick weight by at most δ costs at most δ times its prime mass.
If the prime power is above the common cutoff, the signed loss is nonpositive. -/
theorem primePower_thick_loss (D : ArithData H) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i)
    (S : Finset (E0 × H)) (a v δ : ℝ) (t : H) (w : E0 × H → ℝ)
    (hw : ∀ g ∈ S, w (partner t g) ≤ v + δ) :
    ∑ g ∈ S, (Kc D (p ^ i) g).re *
        ((Fc a t (fun _ => v) (p ^ i) g).re - (Fc a t w (p ^ i) g).re) ≤
      (if v < a / ((p ^ i : ℕ) : ℝ) then δ else 0) * ∑ g ∈ S, (Kc D (p ^ i) g).re := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  conv_rhs => rw [mul_comm]
  apply mul_le_mul_of_nonneg_left
  · have h := hw g hg
    simp only [Fc, Complex.ofReal_re]
    split_ifs <;> simp only [max_def] <;> split_ifs <;> linarith
  · exact primePower_nonneg D hp hi g

/-- The thick interval [b,b+h] controls both the ramp loss and the principal
logarithm when the comparison weight is a/x. -/
theorem thick_weight_allowance {a b x w h : ℝ} (hb : 0 < b) (hx : 1 < x)
    (ha : |a / b - x| ≤ 1) (hw : b ≤ w) (hwb : w ≤ b + h) :
    w ≤ a / x + (h + b / x) ∧ Real.log (a / x / w) ≤ Real.log (1 + 1 / x) := by
  obtain ⟨hl, hu⟩ := abs_le.mp ha
  have h₁ : (x - 1) * b ≤ a := (le_div_iff₀ hb).mp (by linarith)
  have h₂ : a ≤ (x + 1) * b := (div_le_iff₀ hb).mp (by linarith)
  have hx₀ : 0 < x := by linarith
  have ha₀ : 0 < a := lt_of_lt_of_le (mul_pos (sub_pos.mpr hx) hb) h₁
  have hw₀ : 0 < w := hb.trans_le hw
  constructor
  · have hlow : b ≤ (a + b) / x := (le_div_iff₀ hx₀).mpr (by nlinarith)
    rw [add_div] at hlow
    linarith
  · apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hw₀, div_le_iff₀ hx₀]
    calc a ≤ (x + 1) * w := h₂.trans (mul_le_mul_of_nonneg_left hw (by positivity))
         _ = (1 + 1 / x) * w * x := by field_simp

/-- Centering two weights at the same order cancels every nonprincipal affine
term. The principal character contributes the logarithm in equation (3.6). -/
theorem centered_weight_change (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (g : E0 × H) (a w v : ℝ) (ha : 0 < a) (hw : 0 < w) (hv : 0 < v)
    (N : ℕ) (hwN : a / w ≤ N) (hvN : a / v ≤ N) :
    (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) *
      ((w : ℂ) * GPsi D ell ψ (a / w) - (v : ℂ) * GPsi D ell ψ (a / v)) =
      (∑ n ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * Kc D n g *
        ((max (a / n - w) 0 - max (a / n - v) 0 : ℝ) : ℂ)) +
      ((a * Real.log (w / v) : ℝ) : ℂ) / (PhiSet (H := H)).card := by
  classical
  let prime := fun (ψ : AddChar (E0 × H) ℂ) (z : ℝ) => ∑ n ∈ Icc 1 N,
    (ArithmeticFunction.vonMangoldt n : ℂ) * primVal D ψ n * ((max (a / n - z) 0 : ℝ) : ℂ)
  have hdiff (ψ : AddChar (E0 × H) ℂ) :
      (w : ℂ) * GPsi D ell ψ (a / w) - (v : ℂ) * GPsi D ell ψ (a / v) =
      (prime ψ w - prime ψ v) + if ψ = 0 then ((a * Real.log (w / v) : ℝ) : ℂ) else 0 := by
    dsimp [prime]
    rw [sum_cut D ψ N a w ha hw hwN, inner_eq D ell ψ a w ha hw,
      sum_cut D ψ N a v ha hv hvN, inner_eq D ell ψ a v ha hv, Real.log_div hw.ne' hv.ne']
    split_ifs <;> push_cast <;> ring
  simp_rw [hdiff, mul_add, Finset.sum_add_distrib]
  rw [mul_add]
  congr 1
  · dsimp [prime]
    simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Kc, Finset.mul_sum, Finset.sum_mul]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro ψ _
    push_cast
    ring
  · simp [div_eq_mul_inv, mul_comm]

open Classical in
/-- Prime mass at thick labels, summed over subgroup translates and tops.
C bounds the number of tops in any one coset. -/
theorem thick_translate_mass (D : ArithData H) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i)
    (A₀ : AddSubgroup H) [Fintype A₀] (T S : Finset H) (hS : ∀ s ∈ S, s ∈ A₀)
    (C : ℕ) (hC : ∀ h : H, (T.filter fun t => h + t ∈ A₀).card ≤ C) :
    ∑ t ∈ T, ∑ u : A₀, ∑ s ∈ S,
      (Kc D (p ^ i) (((1, 0), s + (u : H) - t) : E0 × H)).re ≤ S.card * (C : ℝ) * 2 := by
  let K := fun g : E0 × H => (Kc D (p ^ i) g).re
  let label := fun h : H => (((1, 0), h) : E0 × H)
  have hK (g) : 0 ≤ K g := primePower_nonneg D hp hi g
  have hslice (s t : H) (hs : s ∈ A₀) :
      ∑ u : A₀, K (label (s + (u : H) - t)) =
        ∑ h ∈ univ.filter (fun h : H => h + t ∈ A₀), K (label h) := by
    apply Finset.sum_bij (fun (u : A₀) _ => s + (u : H) - t)
    · intro u _
      simpa using A₀.add_mem hs u.property
    · intro u _ v _ huv
      exact Subtype.ext (add_left_cancel (sub_left_inj.mp huv))
    · intro h hh
      have hm : h + t ∈ A₀ := (mem_filter.mp hh).2
      exact ⟨⟨h + t - s, A₀.sub_mem hm hs⟩, mem_univ _, by dsimp; abel⟩
    · intros; rfl
  have htotal : ∑ h : H, K (label h) ≤ 2 := by
    rw [← primePower_total D hp hi]
    calc _ = ∑ g ∈ univ.image label, K g := by
                rw [sum_image]; intro a _ b _ hab; exact congrArg Prod.snd hab
         _ ≤ ∑ g, K g := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun g _ _ => hK g)
  have hsum : ∑ t ∈ T, ∑ h ∈ univ.filter (fun h : H => h + t ∈ A₀), K (label h) ≤ C * 2 := by
    simp_rw [Finset.sum_filter]
    rw [sum_comm]
    calc _ = ∑ h : H, ((T.filter fun t => h + t ∈ A₀).card : ℝ) * K (label h) := by
                apply sum_congr rfl
                intro h _
                rw [← Finset.sum_filter]
                simp
         _ ≤ ∑ h : H, C * K (label h) := sum_le_sum fun h _ =>
                mul_le_mul_of_nonneg_right (by exact_mod_cast hC h) (hK _)
         _ ≤ C * 2 := by rw [← mul_sum]; gcongr
  change ∑ t ∈ T, ∑ u : A₀, ∑ s ∈ S, K (label (s + (u : H) - t)) ≤ _
  simp_rw [show ∀ t : H, ∑ u : A₀, ∑ s ∈ S, K (label (s + (u : H) - t)) =
      ∑ s ∈ S, ∑ u : A₀, K (label (s + (u : H) - t)) from fun _ => sum_comm]
  rw [sum_comm]
  calc _ = ∑ s ∈ S, ∑ t ∈ T, ∑ h ∈ univ.filter (fun h : H => h + t ∈ A₀), K (label h) :=
            sum_congr rfl fun s hs => sum_congr rfl fun t _ => hslice s t (hS s hs)
       _ ≤ ∑ _s ∈ S, (C : ℝ) * 2 := sum_le_sum fun _ _ => hsum
       _ = _ := by simp [mul_assoc]

open Classical in
/-- The common weight at top t is a(t)/x. Below x the loss is bounded by the
coset occupancy; at and above x it is nonpositive. -/
theorem thick_translate_prime_loss (D : ArithData H) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i)
    (A₀ : AddSubgroup H) [Fintype A₀] (T S : Finset H) (hS : ∀ s ∈ S, s ∈ A₀)
    (C : ℕ) (hC : ∀ h : H, (T.filter fun t => h + t ∈ A₀).card ≤ C)
    (x δ : ℝ) (hx : 0 < x) (hδ : 0 ≤ δ) (a : H → ℝ) (ha : ∀ t ∈ T, 0 < a t)
    (w : H → A₀ → E0 × H → ℝ)
    (hw : ∀ t ∈ T, ∀ u : A₀, ∀ s ∈ S,
      w t u (partner t ((1, 0), s + (u : H) - t)) ≤ a t / x + δ) :
    ∑ t ∈ T, ∑ u : A₀, ∑ s ∈ S,
      (let g : E0 × H := ((1, 0), s + (u : H) - t)
      (Kc D (p ^ i) g).re * ((Fc (a t) t (fun _ => a t / x) (p ^ i) g).re -
        (Fc (a t) t (w t u) (p ^ i) g).re)) ≤
      (if ((p ^ i : ℕ) : ℝ) < x then δ else 0) * (S.card * (C : ℝ) * 2) := by
  let n := p ^ i
  let d : ℝ := if (n : ℝ) < x then δ else 0
  have hd : 0 ≤ d := by dsimp [d]; split_ifs <;> positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (thick_translate_mass D hp hi A₀ T S hS C hC) hd)
  simp only [Finset.mul_sum]
  refine sum_le_sum fun t ht => sum_le_sum fun u _ => sum_le_sum fun s hs => ?_
  let g : E0 × H := ((1, 0), s + (u : H) - t)
  have h := primePower_thick_loss D hp hi {g} (a t) (a t / x) δ t (w t u)
    (by simpa using hw t ht u s hs)
  have hn : (0 : ℝ) < n := by exact_mod_cast pow_pos hp.pos i
  have hcut : a t / x < a t / (n : ℝ) ↔ (n : ℝ) < x := by
    rw [div_lt_div_iff₀ hx hn, mul_lt_mul_iff_right₀ (ha t ht)]
  simpa only [Finset.sum_singleton, hcut, n, d] using h

end CommonScale
