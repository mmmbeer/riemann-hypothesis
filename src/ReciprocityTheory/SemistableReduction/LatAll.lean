import ReciprocityTheory.SemistableReduction.LemmaH
import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import ReciprocityTheory.SemistableReduction.ApproxBasis
import ReciprocityTheory.SemistableReduction.Unipotent
import ReciprocityTheory.SemistableReduction.DegAddHolds
import Lemmata.IterateZero.IterZero
import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.SemistableReduction.BWPolyA
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup

section
namespace ReciprocityTheory.MultiplicativeHeights

open Metric Set




end ReciprocityTheory.MultiplicativeHeights
end

section
namespace ReciprocityTheory.MultiplicativeHeights

open Metric
open scoped InnerProductSpace


end ReciprocityTheory.MultiplicativeHeights
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

def posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then u k else 0

def negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then 0 else u k

def euc {r : ℕ} (u : Fin r → ℂ) : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 u

lemma euc_add {r : ℕ} (u v : Fin r → ℂ) : euc (u + v) = euc u + euc v := rfl

lemma euc_smul {r : ℕ} (c : ℂ) (u : Fin r → ℂ) : euc (c • u) = c • euc u := rfl

lemma normSq_eq_euc {r : ℕ} (u : Fin r → ℂ) : normSq u = ‖euc u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [normSq, euc]

lemma posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = ‖euc (posPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold posSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, posPart, PiLp.toLp_apply]
  split_ifs <;> simp

lemma negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = ‖euc (negPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold negSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, negPart, PiLp.toLp_apply]
  split_ifs <;> simp

lemma normSq_split (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : normSq u = posSq p u + negSq p u := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma posPart_add_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p u + negPart p u = u := by
  funext k
  simp only [posPart, negPart, Pi.add_apply]
  split_ifs <;> simp

lemma posPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    posPart p (u + v) = posPart p u + posPart p v := by
  funext k
  simp only [posPart, Pi.add_apply]
  split_ifs <;> simp

lemma negPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    negPart p (u + v) = negPart p u + negPart p v := by
  funext k
  simp only [negPart, Pi.add_apply]
  split_ifs <;> simp

lemma posPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    posPart p (c • u) = c • posPart p u := by
  funext k
  simp only [posPart, Pi.smul_apply]
  split_ifs <;> simp

lemma negPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    negPart p (c • u) = c • negPart p u := by
  funext k
  simp only [negPart, Pi.smul_apply]
  split_ifs <;> simp

lemma inner_euc {r : ℕ} (x y : Fin r → ℂ) : inner ℂ (euc x) (euc y) = ∑ k, conj (x k) * y k := by
  simp [euc, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma jForm_eq (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) :
    jForm p x y = inner ℂ (euc (posPart p x)) (euc (posPart p y)) -
      inner ℂ (euc (negPart p x)) (euc (negPart p y)) := by
  rw [inner_euc, inner_euc, ← Finset.sum_sub_distrib]
  unfold jForm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn, posPart, negPart]
  split_ifs <;> simp

lemma jForm_self (p : ℕ) {r : ℕ} (y : Fin r → ℂ) :
    jForm p y y = ((posSq p y - negSq p y : ℝ) : ℂ) := by
  unfold jForm posSq negSq
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  unfold sgn
  split_ifs <;> simp

lemma norm_posPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (posPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := posSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (posPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

lemma norm_negPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (negPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := negSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (negPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

lemma euc_zero {r : ℕ} : euc (0 : Fin r → ℂ) = 0 := by
  rfl

lemma euc_sum {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) :
    euc (∑ j ∈ s, f j) = ∑ j ∈ s, euc (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact euc_zero
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, euc_add, ih]

lemma euc_eq_zero {r : ℕ} {w : Fin r → ℂ} (h : euc w = 0) : w = 0 := by
  have h' := congrArg WithLp.ofLp h
  simpa [euc] using h'

lemma sum_norm_le_sqrt {r : ℕ} (w : Fin r → ℂ) : ∑ j, ‖w j‖ ≤ √(r : ℝ) * ‖euc w‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin r => (1 : ℝ)) (fun j => ‖w j‖)
  rw [EuclideanSpace.norm_eq]
  simpa [euc] using h

lemma norm_err_le {r p : ℕ} {μ R : ℝ} (X : Fin r → Fin r → ℂ)
    (hX : ∀ j : Fin r, (j : ℕ) < p → normSq (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (hμ : 0 ≤ μ) (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := by
  have he : ∀ j : Fin r, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ ≤ ‖w j‖ * μ := by
    intro j
    by_cases hj : (j : ℕ) < p
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := hX j hj
      rw [normSq_eq_euc] at h1
      have ha := norm_nonneg (euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))
      by_contra h
      push_neg at h
      nlinarith
    · rw [hw j (not_lt.mp hj)]
      simp
  calc ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖
      = ‖∑ j, w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        rw [euc_sum]
        simp only [euc_smul]
    _ ≤ ∑ j, ‖w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := norm_sum_le _ _
    _ = ∑ j, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        simp only [norm_smul]
    _ ≤ ∑ j, ‖w j‖ * μ := Finset.sum_le_sum fun j _ => he j
    _ = μ * ∑ j, ‖w j‖ := by
        rw [Finset.mul_sum]
        simp only [mul_comm]
    _ ≤ μ * (√(r : ℝ) * ‖euc w‖) := mul_le_mul_of_nonneg_left (sum_norm_le_sqrt w) hμ
    _ = √(r : ℝ) * μ * ‖euc w‖ := by ring

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

lemma posPart_posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (posPart p u) = posPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma posPart_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (negPart p u) = 0 := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma negPart_posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negPart p (posPart p u) = 0 := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma negPart_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negPart p (negPart p u) = negPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma posPart_zero (p : ℕ) {r : ℕ} : posPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [posPart]

lemma negPart_zero (p : ℕ) {r : ℕ} : negPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [negPart]

lemma posPart_supp (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ∀ j : Fin r, p ≤ (j : ℕ) → posPart p u j = 0 := fun j hj => by
  simp [posPart, not_lt.mpr hj]

lemma approxR_nonneg (r : ℕ) {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) : 0 ≤ approxR r μ ρ := by
  unfold approxR
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hμ.le) hρ.le

lemma graph_bound {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (negPart p (∑ j, w j • X j))‖ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ ∧
      3 * (√(r : ℝ) * μ * ‖euc w‖) ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
  set R := approxR r μ ρ with hRdef
  have hR0 : 0 ≤ R := approxR_nonneg r hμ hρ
  set E : Fin r → ℂ := ∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) with hE
  have hEn : ‖euc E‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := norm_err_le X hX hμ.le w hw

  have hsum : ∑ j, w j • X j = (R : ℂ) • w + E := by
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hpw : posPart p w = w := by
    ext k
    simp only [posPart]
    split_ifs with h
    · rfl
    · exact (hw k (not_lt.mp h)).symm
  have hnw : negPart p w = 0 := by
    ext k
    simp only [negPart, Pi.zero_apply]
    split_ifs with h
    · rfl
    · exact hw k (not_lt.mp h)
  have hpos : posPart p (∑ j, w j • X j) = (R : ℂ) • w + posPart p E := by
    rw [hsum, posPart_add, posPart_smul, hpw]
  have hneg : negPart p (∑ j, w j • X j) = negPart p E := by
    rw [hsum, negPart_add, negPart_smul, hnw, smul_zero, zero_add]
  set s := √(r : ℝ) * μ * ‖euc w‖ with hs
  have hs0 : 0 ≤ s := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hμ.le) (norm_nonneg _)
  have hnegle : ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := by
    rw [hneg]; exact (norm_negPart_le p E).trans hEn
  have hRw : ‖euc ((R : ℂ) • w)‖ = 4 * s / ρ := by
    rw [euc_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hR0, hRdef, approxR, hs]
    ring
  have hposge : 4 * s / ρ - s ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
    rw [hpos, euc_add]
    have h1 := norm_sub_le (euc ((R : ℂ) • w) + euc (posPart p E)) (euc (posPart p E))
    rw [add_sub_cancel_right] at h1
    have h2 := (norm_posPart_le p E).trans hEn
    linarith
  have hq : 4 * s ≤ 4 * s / ρ := by
    rw [le_div_iff₀ hρ]; nlinarith
  have hqρ : 4 * s / ρ * ρ = 4 * s := div_mul_cancel₀ _ hρ.ne'
  refine ⟨?_, by linarith⟩
  calc ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := hnegle
    _ ≤ ρ / 3 * (4 * s / ρ - s) := by nlinarith [mul_le_mul_of_nonneg_right hρ1 hs0]
    _ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ :=
      mul_le_mul_of_nonneg_left hposge (by positivity)

lemma approxGraph_one {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)) := by
  obtain ⟨h1, h2⟩ := graph_bound X hμ hρ hρ1 hX w hw
  refine ⟨?_, fun hw0 => ?_⟩
  · rw [negSq_eq, posSq_eq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  · rw [posSq_eq]
    have hwpos : 0 < ‖euc w‖ := by
      rw [norm_pos_iff]; intro h; exact hw0 (euc_eq_zero h)
    have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; exact absurd (Subsingleton.elim w 0) hw0
      · exact h
    have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
    have h3 : 0 < 3 * (√(r : ℝ) * μ * ‖euc w‖) :=
      mul_pos (by norm_num) (mul_pos (mul_pos hsq hμ) hwpos)
    exact pow_pos (lt_of_lt_of_le h3 h2) 2

def graphMap (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun w := posPart p (∑ j, posPart p w j • X j) + negPart p w
  map_add' u v := by
    simp only [posPart_add, negPart_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c u := by
    have h : ∀ j, posPart p (c • u) j • X j = c • (posPart p u j • X j) := fun j => by
      rw [posPart_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [Finset.sum_congr rfl (fun j _ => h j)]
    simp only [← Finset.smul_sum, posPart_smul, negPart_smul, RingHom.id_apply, smul_add]

lemma graphMap_apply (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) :
    graphMap p X w = posPart p (∑ j, posPart p w j • X j) + negPart p w := rfl

lemma exists_graph_pos {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (b : Fin r → ℂ) : ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧
      posPart p (∑ j, w j • X j) = posPart p b := by

  have hinj : Function.Injective (graphMap p X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [graphMap_apply] at hu
    have hn : negPart p u = 0 := by
      have := congrArg (negPart p) hu
      rwa [negPart_add, negPart_posPart, zero_add, negPart_negPart, negPart_zero] at this
    have hp : posPart p (∑ j, posPart p u j • X j) = 0 := by
      have := congrArg (posPart p) hu
      rwa [posPart_add, posPart_posPart, posPart_negPart, add_zero, posPart_zero] at this
    have h2 := (graph_bound X hμ hρ hρ1 hX (posPart p u) (posPart_supp p u)).2
    rw [hp, euc_zero, norm_zero] at h2
    have hu0 : posPart p u = 0 := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; exact Subsingleton.elim _ _
      · have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
        have hle : ‖euc (posPart p u)‖ ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (mul_pos hsq hμ) hc)
          linarith
        exact euc_eq_zero (norm_le_zero_iff.mp hle)
    rw [← posPart_add_negPart p u, hu0, hn, add_zero]
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) (posPart p b)
  refine ⟨posPart p u, posPart_supp p u, ?_⟩
  have := congrArg (posPart p) hu
  rwa [graphMap_apply, posPart_add, posPart_posPart, posPart_negPart, add_zero,
    posPart_posPart] at this

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

lemma jForm_zero_left (p : ℕ) {r : ℕ} (y : Fin r → ℂ) : jForm p 0 y = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.jForm]

lemma jForm_add_left (p : ℕ) {r : ℕ} (x x' y : Fin r → ℂ) :
    jForm p (x + x') y = jForm p x y + jForm p x' y := by
  simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]

lemma jForm_smul_left (p : ℕ) {r : ℕ} (c : ℂ) (x y : Fin r → ℂ) :
    jForm p (c • x) y = conj c * jForm p x y := by
  simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma jForm_sum_left (p : ℕ) {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ)
    (y : Fin r → ℂ) : jForm p (∑ j ∈ s, f j) y = ∑ j ∈ s, jForm p (f j) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jForm_add_left, ih]

lemma jForm_span_zero (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (y : Fin r → ℂ)
    (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) (w : Fin r → ℂ)
    (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) : jForm p (∑ j, w j • X j) y = 0 := by
  rw [jForm_sum_left]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [jForm_smul_left]
  by_cases hj : (j : ℕ) < p
  · rw [hy j hj, mul_zero]
  · rw [hw j (not_lt.mp hj), map_zero, zero_mul]

lemma pos_small_of_orth {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) :
    ‖euc (posPart p y)‖ ≤ ρ / 3 * ‖euc (negPart p y)‖ := by
  obtain ⟨w, hw, hwb⟩ := exists_graph_pos X hμ hρ hρ1 hX y
  have h0 : ReciprocityTheory.MultiplicativeHeights.jForm p (∑ j, w j • X j) y = 0 := jForm_span_zero p X y hy w hw
  have hb := (graph_bound X hμ hρ hρ1 hX w hw).1
  rw [hwb] at hb
  rw [jForm_eq, hwb, sub_eq_zero] at h0
  have h1 := congrArg (fun z : ℂ => (RCLike.re z : ℝ)) h0
  rw [inner_self_eq_norm_sq] at h1
  have h2 : ‖euc (posPart p y)‖ ^ 2 ≤
      ‖euc (negPart p (∑ j, w j • X j))‖ * ‖euc (negPart p y)‖ :=
    h1 ▸ (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hA := norm_nonneg (euc (posPart p y))
  have hB := norm_nonneg (euc (negPart p y))
  have h3 : ‖euc (posPart p y)‖ ^ 2 ≤
      ρ / 3 * ‖euc (posPart p y)‖ * ‖euc (negPart p y)‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hb hB)
  rcases hA.eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (div_nonneg hρ.le (by norm_num)) hB
  · nlinarith

lemma approxGraph_two {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) (hy0 : y ≠ 0) :
    (jForm p y y).re < 0 := by
  have hs := pos_small_of_orth X hμ hρ hρ1 hX y hy
  rw [jForm_self, Complex.ofReal_re, posSq_eq, negSq_eq]
  have hA := norm_nonneg (euc (posPart p y))
  have hB := norm_nonneg (euc (negPart p y))
  have hB0 : 0 < ‖euc (negPart p y)‖ := by
    refine lt_of_le_of_ne hB fun h => hy0 ?_
    have hA0 : ‖euc (posPart p y)‖ = 0 :=
      le_antisymm (by rw [← h, mul_zero] at hs; exact hs) hA
    rw [← posPart_add_negPart p y, euc_eq_zero (norm_eq_zero.mp hA0),
      euc_eq_zero (norm_eq_zero.mp h.symm), add_zero]
  have hk : ρ / 3 ≤ 1 / 3 := by linarith
  have hs' : ‖euc (posPart p y)‖ ≤ ‖euc (negPart p y)‖ / 3 :=
    hs.trans (by nlinarith)
  nlinarith [mul_le_mul hs' hs' hA (by linarith : (0 : ℝ) ≤ ‖euc (negPart p y)‖ / 3)]

private theorem exists_coeffs_of_mem_span_lemma {r p : ℕ} (X : Fin r → Fin r → ℂ) {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧ u = ∑ j, w j • X j := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨(Pi.single j 1 : Fin r → ℂ), fun k hk => ?_, ?_⟩
    · have hkj : k ≠ j := fun h => by subst h; exact (not_lt.mpr hk) hj
      simp [hkj]
    · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    refine ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨c • a, fun j hj => by simp [ha j hj], ?_⟩
    simp [Finset.smul_sum, smul_smul]

lemma approxGraph_three {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (v y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0)
    (hvy : v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ‖jForm p y y‖ ≤ 2 * normSq v := by
  obtain ⟨w, hw, hu⟩ := exists_coeffs_of_mem_span_lemma X hvy
  have hv : v = y + ∑ j, w j • X j := by rw [← hu]; abel
  have h0 : ReciprocityTheory.MultiplicativeHeights.jForm p (∑ j, w j • X j) y = 0 := jForm_span_zero p X y hy w hw
  have hb := (graph_bound X hμ hρ hρ1 hX w hw).1
  have hs := pos_small_of_orth X hμ hρ hρ1 hX y hy
  rw [jForm_eq, sub_eq_zero] at h0
  have hre : RCLike.re (inner ℂ (euc (posPart p y))
        (euc (posPart p (∑ j, w j • X j)))) =
      RCLike.re (inner ℂ (euc (negPart p y)) (euc (negPart p (∑ j, w j • X j)))) := by
    rw [inner_re_symm, h0, inner_re_symm]
  have hI := (RCLike.abs_re_le_norm (inner ℂ (euc (negPart p y))
    (euc (negPart p (∑ j, w j • X j))))).trans (norm_inner_le_norm _ _)
  rw [jForm_self, Complex.norm_real, Real.norm_eq_abs, normSq_split p v, posSq_eq,
    posSq_eq, negSq_eq, negSq_eq, hv, posPart_add, negPart_add, euc_add,
    euc_add, norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hre]
  have hPy := norm_nonneg (euc (posPart p y))
  have hNy := norm_nonneg (euc (negPart p y))
  have hPu := norm_nonneg (euc (posPart p (∑ j, w j • X j)))
  have hNu := norm_nonneg (euc (negPart p (∑ j, w j • X j)))
  have hk : ρ / 3 ≤ 1 / 3 := by linarith
  have hs' : ‖euc (posPart p y)‖ ≤ ‖euc (negPart p y)‖ / 3 :=
    hs.trans (by nlinarith)
  have hb' : ‖euc (negPart p (∑ j, w j • X j))‖ ≤
      ‖euc (posPart p (∑ j, w j • X j))‖ / 3 :=
    hb.trans (by nlinarith)
  have hI' := (abs_le.mp hI).1
  have ha : ‖euc (posPart p y)‖ ^ 2 ≤ ‖euc (negPart p y)‖ ^ 2 := by nlinarith
  have hc : ‖euc (negPart p y)‖ * ‖euc (negPart p (∑ j, w j • X j))‖ ≤
      ‖euc (negPart p y)‖ * (‖euc (posPart p (∑ j, w j • X j))‖ / 3) :=
    mul_le_mul_of_nonneg_left hb' hNy
  rw [abs_le]
  constructor <;>
    nlinarith [sq_nonneg (‖euc (posPart p (∑ j, w j • X j))‖ -
      2 / 3 * ‖euc (negPart p y)‖), sq_nonneg ‖euc (posPart p y)‖,
      sq_nonneg ‖euc (negPart p (∑ j, w j • X j))‖, sq_nonneg ‖euc (negPart p y)‖]

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

section
namespace ReciprocityTheory.MultiplicativeHeights

open ApproximationGraph in
theorem approxGraph_holds : ApproxGraphStatement := by
  intro r p μ ρ X _ hμ hρ hρ1 hX
  exact ⟨fun w hw => approxGraph_one X hμ hρ hρ1 hX w hw,
    fun y hy hy0 => approxGraph_two X hμ hρ hρ1 hX y hy hy0,
    fun v y hy hvy => approxGraph_three X hμ hρ hρ1 hX v y hy hvy⟩

end ReciprocityTheory.MultiplicativeHeights
end

section
namespace ReciprocityTheory.MultiplicativeHeights

open Filter Topology Function Metric Polynomial

theorem entire_poly_of_growth (k : ℕ) : ∀ (g : ℂ → ℂ) (A : ℝ), Differentiable ℂ g →
    (∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t, g t = P.eval t := by
  first | exact Bl.IterateZero.goal1 .. | (apply Bl.IterateZero.goal1 <;> assumption) | (intros; apply Bl.IterateZero.goal1 <;> assumption)

theorem exists_entire_of_finite_growth (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ) (hB : B.Finite)
    (hf : DifferentiableOn ℂ f Bᶜ) (hb : ∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ t ∉ B, g t = f t := by
  classical
  let g : ℂ → ℂ := fun t => if t ∈ B then limUnder (𝓝[≠] t) f else f t
  refine ⟨g, fun c => ?_, fun t ht => if_neg ht⟩
  by_cases hc : c ∈ B
  · have hU : IsOpen (B \ {c})ᶜ := (hB.sdiff).isClosed.isOpen_compl
    set s : Set ℂ := (B \ {c})ᶜ ∩ ball c 1 with hs
    have hsn : s ∈ 𝓝 c := inter_mem (hU.mem_nhds (fun h => h.2 rfl)) (ball_mem_nhds c one_pos)
    have hsub : s \ {c} ⊆ Bᶜ := by
      rintro t ⟨⟨h1, -⟩, h2⟩ htB
      exact h1 ⟨htB, h2⟩
    have hbdd : BddAbove (norm ∘ f '' (s \ {c})) := by
      refine ⟨|A| * (2 + ‖c‖) ^ k, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have htc : ‖t‖ ≤ ‖c‖ + 1 := by
        have h := ht.1.2
        rw [mem_ball, dist_eq_norm] at h
        have := norm_le_norm_add_norm_sub' t c
        linarith [norm_sub_rev t c]
      calc ‖f t‖ ≤ A * (1 + ‖t‖) ^ k := hb t (hsub ht)
        _ ≤ |A| * (1 + ‖t‖) ^ k := mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * (2 + ‖c‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k)
              (abs_nonneg A)
    have hdiff := Complex.differentiableOn_update_limUnder_of_bddAbove hsn
      (hf.mono hsub) hbdd
    refine (hdiff.differentiableAt hsn).congr_of_eventuallyEq ?_
    filter_upwards [hsn] with t ht
    by_cases htc : t = c
    · subst htc
      simp [g, hc]
    · have htB : t ∉ B := fun h => ht.1 ⟨h, htc⟩
      simp [g, htB, update_of_ne htc]
  · have hO : IsOpen Bᶜ := hB.isClosed.isOpen_compl
    refine (hf.differentiableAt (hO.mem_nhds hc)).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hc] with t ht
    exact if_neg ht

theorem onePolyGrowth_holds : OnePolyGrowthStatement := by
  intro f B A k hB hf hb
  obtain ⟨g, hg, hgf⟩ := exists_entire_of_finite_growth f B A k hB hf hb
  have hclosed : IsClosed {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} :=
    isClosed_le (continuous_norm.comp hg.continuous)
      (continuous_const.mul ((continuous_const.add continuous_norm).pow k))
  have hsub : Bᶜ ⊆ {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} := fun t ht => by
    simpa [hgf t ht] using hb t ht
  have hall : ∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k := by
    have hd : Dense Bᶜ := hB.countable.dense_compl ℂ
    intro t
    have : t ∈ closure Bᶜ := by rw [hd.closure_eq]; trivial
    exact closure_minimal hsub hclosed this
  obtain ⟨P, hPd, hP⟩ := entire_poly_of_growth k g A hg hall
  exact ⟨P, hPd, fun t ht => by rw [← hgf t ht, hP t]⟩

end ReciprocityTheory.MultiplicativeHeights
end

section
namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_ext_poly {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ) (g D : (σ → ℂ) → ℂ)
    (w : σ → ℂ) (hw : ∀ z, {s : ℂ | D (z + s • w) = 0}.Finite)
    (hD : ∀ z v, D z ≠ 0 → {t : ℂ | D (z + t • v) = 0}.Finite)
    (hL : ∀ z v, {t : ℂ | D (z + t • v) = 0}.Finite → ∃ Q : ℂ[X], Q.natDegree ≤ k ∧
      ∀ t, D (z + t • v) ≠ 0 → g (z + t • v) = Q.eval t) :
    ∃ F : MvPolynomial σ ℂ, ∀ z, D z ≠ 0 → g z = MvPolynomial.eval z F := by

  have hw' := fun y => hL y w (hw y)
  choose Qw hQd hQ using hw'

  have hv' := fun (y v : σ → ℂ) (h : D y ≠ 0) => hL y v (hD y v h)
  choose P hPd hP using hv'
  let G : (σ → ℂ) → ℂ := fun y => (Qw y).eval 0
  have hsep : ∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t := by
    intro y m
    set z : σ → ℂ := Function.update y m 0
    set e : σ → ℂ := Pi.single m 1
    have hupd : ∀ t, Function.update y m t = z + t • e := by
      intro t; ext i
      by_cases hi : i = m
      · subst hi; simp [z, e]
      · simp [z, e, Function.update_apply, hi, Pi.single_apply]
    let Pc : ℂ → ℂ[X] := fun c => if h : D (z + c • w) = 0 then 0 else P (z + c • w) e h
    let R : Finset ℂ → ℂ[X] := fun S =>
      ∑ c ∈ S, Polynomial.C ((Lagrange.basis S id c).eval 0) * Pc c
    have hRdeg : ∀ S, (R S).natDegree ≤ k := by
      intro S
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun c _ => ?_)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      simp only [Pc]
      split_ifs with h
      · simp
      · exact hPd _ _ h

    have key : ∀ S : Finset ℂ, S.card = k + 1 → (∀ c ∈ S, D (z + c • w) ≠ 0) →
        ∀ t, (∀ c ∈ S, D ((z + t • e) + c • w) ≠ 0) → G (z + t • e) = (R S).eval t := by
      intro S hS hSz t ht
      simp only [G, R]
      rw [bwp_eval_eq_lagrange S (Qw (z + t • e)) k hS (hQd _) 0, Polynomial.eval_finset_sum]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_C, ← hQ _ c (ht c hc)]
      congr 1
      simp only [Pc, dif_neg (hSz c hc)]
      rw [← hP _ _ (hSz c hc) t (by rw [add_right_comm]; exact ht c hc), add_right_comm]
    have hbad : ∀ S : Finset ℂ, (∀ c ∈ S, D (z + c • w) ≠ 0) →
        {t : ℂ | ∃ c ∈ S, D ((z + t • e) + c • w) = 0}.Finite := by
      intro S hSz
      have : {t : ℂ | ∃ c ∈ S, D ((z + t • e) + c • w) = 0} =
          ⋃ c ∈ S, {t : ℂ | D ((z + c • w) + t • e) = 0} := by
        ext t; simp [add_right_comm]
      rw [this]
      exact Set.Finite.biUnion S.finite_toSet (fun c hc => hD _ e (hSz c hc))
    obtain ⟨S0, hS0, hS0z⟩ := bwp_exists_nodes {s | D (z + s • w) = 0} (hw z) k
    refine ⟨R S0, hRdeg S0, fun t0 => ?_⟩
    rw [hupd]
    obtain ⟨S1, hS1, hS1z⟩ := bwp_exists_nodes
      ({s | D (z + s • w) = 0} ∪ {s | D ((z + t0 • e) + s • w) = 0})
      ((hw z).union (hw (z + t0 • e))) k
    have hS1a : ∀ c ∈ S1, D (z + c • w) ≠ 0 := fun c hc h => hS1z c hc (Or.inl h)
    have hS1b : ∀ c ∈ S1, D ((z + t0 • e) + c • w) ≠ 0 := fun c hc h => hS1z c hc (Or.inr h)
    have hS0a : ∀ c ∈ S0, D (z + c • w) ≠ 0 := fun c hc h => hS0z c hc h
    have hRR : R S0 = R S1 := by
      refine bwp_poly_eq_of_eval_eq_off _ _ _ ((hbad S0 hS0a).union (hbad S1 hS1a)) (fun t ht => ?_)
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at ht
      rw [← key S0 hS0 hS0a t ht.1, ← key S1 hS1 hS1a t ht.2]
    rw [hRR, key S1 hS1 hS1a t0 hS1b]
  obtain ⟨F, hF⟩ := bwp_sepPoly k G hsep
  refine ⟨F, fun z hz => ?_⟩
  rw [← hF]
  have := hQ z 0 (by simpa using hz)
  simpa [G] using this

end ReciprocityTheory.MultiplicativeHeights
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_eval_smul_of_isHomogeneous {σ : Type*} {φ : MvPolynomial σ ℂ} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (t : ℂ) (z : σ → ℂ) :
    MvPolynomial.eval (t • z) φ = t ^ d * MvPolynomial.eval z φ := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hdeg]
  ring

def bwpMat {p : ℕ} (z : Fin p × Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun i j => z (i, j)

def bwpId (p : ℕ) : Fin p × Fin p → ℂ := fun ij => if ij.1 = ij.2 then 1 else 0

theorem bwp_det_line_poly {p : ℕ} (z v : Fin p × Fin p → ℂ) :
    ∃ Λ : ℂ[X], ∀ t : ℂ, Λ.eval t = (bwpMat (z + t • v)).det := by
  refine ⟨(Matrix.of fun i j => Polynomial.C (z (i, j)) + Polynomial.C (v (i, j)) * Polynomial.X).det,
    fun t => ?_⟩
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, bwpMat, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem bwp_finite_det_line {p : ℕ} (z v : Fin p × Fin p → ℂ) (hz : (bwpMat z).det ≠ 0) :
    {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite := by
  obtain ⟨Λ, hΛ⟩ := bwp_det_line_poly z v
  have hΛ0 : Λ ≠ 0 := by
    intro h
    apply hz
    have h0 := hΛ 0
    rw [h, Polynomial.eval_zero] at h0
    simpa using h0.symm
  refine (bwp_finite_eval_eq_zero hΛ0).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [hΛ]
  exact ht

theorem bwp_finite_det_id_line {p : ℕ} (z : Fin p × Fin p → ℂ) :
    {s : ℂ | (bwpMat (z + s • bwpId p)).det = 0}.Finite := by
  have hne : (-bwpMat z).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  refine (bwp_finite_eval_eq_zero hne).subset fun s hs => ?_
  simp only [Set.mem_setOf_eq] at hs ⊢
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  convert hs using 2
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply]
    ring
  · simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply, h]

theorem bwp_continuous_of_matrix {p : ℕ} :
    Continuous (fun y : Fin p → Fin p → ℂ => Matrix.of y) := by
  first
    | exact continuous_id
    | exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)

theorem bwp_exists_bound_unitary {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) :
    ∃ C : ℝ, ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ‖P U‖ ≤ C := by
  set S : Set (Fin p → Fin p → ℂ) := {y | Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1} with hS
  have hcl : IsClosed S :=
    isClosed_eq (bwp_continuous_of_matrix.matrix_conjTranspose.matrix_mul bwp_continuous_of_matrix)
      continuous_const
  have hbd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun y hy => ?_⟩
    have hU : Matrix.of y ∈ Matrix.unitaryGroup (Fin p) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    first
      | exact entry_norm_bound_of_unitary hU i j
      | exact Matrix.UnitaryGroup.entry_norm_bound hU i j
      | exact Matrix.norm_entry_le_one_of_unitary hU i j
  have hK : IsCompact S := Metric.isCompact_of_isClosed_isBounded hcl hbd
  have hsub : S ⊆ {y | (Matrix.of y).det ≠ 0} := fun y hy => by
    have h := congrArg Matrix.det (show Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1 from hy)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (DifferentiableOn.continuousOn hP |>.mono hsub)
  refine ⟨C, fun U hU => ?_⟩
  have hU' : U ∈ S := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  exact hC U hU'

theorem bwp_line_poly (hH : LemmaHStatement) (hO : OnePolyGrowthStatement) {p : ℕ} (a : Fin p → ℕ)
    (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) (hT : IsTriEquivariant a P)
    (z v : Fin p × Fin p → ℂ) (hB : {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite) :
    ∃ Q : ℂ[X], Q.natDegree ≤ ∑ i, a i ∧
      ∀ t, (bwpMat (z + t • v)).det ≠ 0 → P (bwpMat (z + t • v)) = Q.eval t := by
  classical
  obtain ⟨C, hC⟩ := bwp_exists_bound_unitary P hP
  set M : ℝ := ∑ i, ∑ j, (‖z (i, j)‖ + ‖v (i, j)‖) with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hMj : ∀ j, ∑ i, (‖z (i, j)‖ + ‖v (i, j)‖) ≤ M := fun j =>
    Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j' => ‖z (i, j')‖ + ‖v (i, j')‖)
      (fun j' _ => by positivity) (Finset.mem_univ j)
  have hbound : ∀ t ∉ {t : ℂ | (bwpMat (z + t • v)).det = 0},
      ‖P (bwpMat (z + t • v))‖ ≤ (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i) := by
    intro t ht
    have hdet : (bwpMat (z + t • v)).det ≠ 0 := ht
    have hcol : ∀ j, colNormSq (bwpMat (z + t • v)) j ≤ (M * (1 + ‖t‖)) ^ 2 := by
      intro j
      have hz : ∑ i, ‖z (i, j)‖ ≤ M :=
        le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (norm_nonneg _)) (hMj j)
      have hv : ∑ i, ‖v (i, j)‖ ≤ M :=
        le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_left (norm_nonneg _)) (hMj j)
      set e : Fin p → ℝ := fun i => ‖bwpMat (z + t • v) i j‖ with he_def
      have he0 : ∀ i, 0 ≤ e i := fun i => norm_nonneg _
      have he : ∑ i, e i ≤ M * (1 + ‖t‖) := by
        calc ∑ i, e i ≤ ∑ i, (‖z (i, j)‖ + ‖t‖ * ‖v (i, j)‖) := by
              refine Finset.sum_le_sum fun i _ => ?_
              simp only [he_def, bwpMat, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              exact (norm_add_le _ _).trans (by rw [norm_mul])
          _ = ∑ i, ‖z (i, j)‖ + ‖t‖ * ∑ i, ‖v (i, j)‖ := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ M * (1 + ‖t‖) := by nlinarith [norm_nonneg t]
      have hsq : ∑ i, e i ^ 2 ≤ (∑ i, e i) ^ 2 := by
        calc ∑ i, e i ^ 2 = ∑ i, e i * e i := Finset.sum_congr rfl fun i _ => sq (e i)
          _ ≤ ∑ i, e i * ∑ j', e j' := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (fun j' _ => he0 j') (Finset.mem_univ i)) (he0 i)
          _ = (∑ i, e i) ^ 2 := by rw [← Finset.sum_mul, sq]
      calc colNormSq (bwpMat (z + t • v)) j = ∑ i, e i ^ 2 := rfl
        _ ≤ (∑ i, e i) ^ 2 := hsq
        _ ≤ (M * (1 + ‖t‖)) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => he0 i) he 2
    have hR : 0 ≤ M * (1 + ‖t‖) := mul_nonneg hM0 (by positivity)
    have h := hH Unit (fun _ => p) (fun _ => a) (fun x => P (x ())) C (M * (1 + ‖t‖))
      (by
        intro x s b hx hb htri
        cases s
        first
          | simp only [Function.update_self]
          | simp only [Function.update_same]
        exact hT (x ()) b (hx ()) hb htri)
      (fun k hk => hC (k ()) (hk ())) hR (fun _ => bwpMat (z + t • v)) (fun _ => hdet)
      (fun _ j => hcol j)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    calc ‖P (bwpMat (z + t • v))‖ ≤ C * (M * (1 + ‖t‖)) ^ ∑ i, a i := h
      _ = (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i) := by rw [mul_pow]; ring
  have hdiff : DifferentiableOn ℂ (fun t => P (bwpMat (z + t • v)))
      {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ := by
    have hL : Differentiable ℂ (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ)) := by
      rw [differentiable_pi]
      intro i
      rw [differentiable_pi]
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have hc : DifferentiableOn ℂ ((fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) ∘
        (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ)))
        {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ :=
      DifferentiableOn.comp hP hL.differentiableOn (fun t ht => ht)
    exact hc
  obtain ⟨Q, hQdeg, hQ⟩ := hO (fun t => P (bwpMat (z + t • v))) _ (C * M ^ (∑ i, a i)) (∑ i, a i) hB
    hdiff hbound
  exact ⟨Q, hQdeg, fun t ht => hQ t ht⟩

end ReciprocityTheory.MultiplicativeHeights
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwPoly_holds (hH : LemmaHStatement) (hE : ∀ n, ReciprocityTheory.L2DbarEstimates.EXTStatement n)
    (hO : OnePolyGrowthStatement) : BWPolyStatement := by
  intro p a P hP hT
  obtain ⟨F, hF⟩ := bwp_ext_poly (σ := Fin p × Fin p) (∑ i, a i) (fun z => P (bwpMat z))
    (fun z => (bwpMat z).det) (bwpId p) (fun z => bwp_finite_det_id_line z)
    (fun z v hz => bwp_finite_det_line z v hz) (fun z v hB => bwp_line_poly hH hO a P hP hT z v hB)
  have hF' : ∀ z, (bwpMat z).det ≠ 0 → P (bwpMat z) = MvPolynomial.eval z F := fun z hz => hF z hz
  refine ⟨MvPolynomial.homogeneousComponent (∑ i, a i) F,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, fun x hx => ?_⟩
  set z : Fin p × Fin p → ℂ := fun ij => x ij.1 ij.2 with hz
  have hxz : bwpMat z = x := by
    ext i j
    rfl
  have hPz : P x = MvPolynomial.eval z F := by
    rw [← hxz]
    exact hF' z (by rw [hxz]; exact hx)
  rw [hPz]
  have hscale : ∀ t : ℂ, t ≠ 0 → MvPolynomial.eval (t • z) F = t ^ (∑ i, a i) * MvPolynomial.eval z F := by
    intro t ht
    have hb : bwpMat (t • z) = x * (t • (1 : Matrix (Fin p) (Fin p) ℂ)) := by
      ext i j
      simp [bwpMat, hz, Matrix.mul_smul]
    have hbdet : (t • (1 : Matrix (Fin p) (Fin p) ℂ)).det ≠ 0 := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ ht
    have hbtri : (t • (1 : Matrix (Fin p) (Fin p) ℂ)).BlockTriangular id := by
      intro i j h
      have hij : i ≠ j := fun hij => by subst hij; exact lt_irrefl _ h
      rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]
    have hdet : (bwpMat (t • z)).det ≠ 0 := by
      rw [hb, Matrix.det_mul]
      exact mul_ne_zero hx hbdet
    rw [← hF' _ hdet, hb, hT x _ hx hbdet hbtri, hPz]
    congr 1
    simp [triChar, Finset.prod_pow_eq_pow_sum]
  have hsum : ∀ t : ℂ, MvPolynomial.eval (t • z) F = ∑ j ∈ Finset.range (F.totalDegree + 1),
      t ^ j * MvPolynomial.eval z (MvPolynomial.homogeneousComponent j F) := by
    intro t
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent F]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => bwp_eval_smul_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous j F) t z)
  have hΦ : (∑ j ∈ Finset.range (F.totalDegree + 1),
      Polynomial.C (MvPolynomial.eval z (MvPolynomial.homogeneousComponent j F)) * Polynomial.X ^ j) =
      Polynomial.C (MvPolynomial.eval z F) * Polynomial.X ^ (∑ i, a i) := by
    refine bwp_poly_eq_of_eval_eq_off _ _ {0} (Set.finite_singleton 0) (fun t ht => ?_)
    have ht0 : t ≠ 0 := ht
    rw [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, mul_comm, ← hscale t ht0, hsum t]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hc := congrArg (fun q => Polynomial.coeff q (∑ i, a i)) hΦ
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  rw [Finset.sum_ite_eq] at hc
  split_ifs at hc with hk
  · exact hc.symm
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using hk), map_zero]
    exact hc.symm

end ReciprocityTheory.MultiplicativeHeights
end
end

section
namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights





theorem approx : ApproxStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.approxBasis_holds ReciprocityTheory.MultiplicativeHeights.approxGraph_holds

theorem unipotent : UnipotentStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.unipotent_holds

theorem degAdd : DegAddStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.degAdd_holds


theorem bwPoly : BWPolyStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.bwPoly_holds ReciprocityTheory.MultiplicativeHeights.lemmaH_holds ReciprocityTheory.L2DbarEstimates.ext
    ReciprocityTheory.MultiplicativeHeights.onePolyGrowth_holds

end ReciprocityTheory.MultiplicativeHeights.Closed
end
