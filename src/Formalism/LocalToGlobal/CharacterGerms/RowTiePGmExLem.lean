import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.GmExArith

open Formalism.L2.FormalSeriesBounds NumberField

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_neg {a : C} (h : V.MM a) : V.MM (-a) := by
  unfold VF.MM at *; rwa [V.v.map_neg]

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]; exact mm_add ha (mm_neg hb)

theorem mm_ge {a : C} (h : V.MM a) : V.Ge 0 a := by
  unfold VF.Ge; rw [WithTop.coe_zero]; exact le_of_lt h

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact add_pos_of_pos_of_nonneg ha hb'

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem not_mm_one : ¬ V.MM (1 : C) := by
  unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl 0

theorem mm_pow {a : C} (h : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]; exact mm_int_mul ((mm_ge h).pow k) h

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem v_eq_zero_of {a : C} (h0 : V.Ge 0 a) (h : ¬ V.MM a) : V.v a = 0 :=
  le_antisymm (not_lt.1 h) (by simpa [VF.Ge] using h0)


theorem ge_natCast' (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

theorem ge_intCast' (m : ℤ) : V.Ge 0 (m : C) := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, Int.cast_natCast]; exact ge_natCast' n
  | negSucc n => rw [Int.cast_negSucc]; exact (ge_natCast' (n + 1)).neg

theorem eq_zero_of_ge_all {x : C} (h : ∀ n : ℕ, V.Ge n x) : x = 0 := by
  by_contra hx
  have ht : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have h1 := h n
  unfold VF.Ge at h1
  rw [← hr] at h1
  exact absurd (WithTop.coe_le_coe.1 h1) (not_le.2 hn)

theorem ge_of_isIntegral {z : C} (hz : IsIntegral ℤ z) : V.Ge 0 z := by
  by_contra hneg
  obtain ⟨p, hpm, hp⟩ := hz
  have hz0 : z ≠ 0 := by rintro rfl; exact hneg (VF.Ge.zero 0)
  have hw : V.MM z⁻¹ := by
    unfold VF.Ge at hneg; unfold VF.MM
    have e : V.v z + V.v z⁻¹ = 0 := by rw [← V.v.map_mul, mul_inv_cancel₀ hz0, V.v.map_one]
    induction ha : V.v z using WithTop.recTopCoe with
    | top => rw [ha] at hneg; exact absurd le_top hneg
    | coe r =>
      rw [ha] at hneg e
      have hr : r < 0 := by
        by_contra hr; exact hneg (by exact_mod_cast not_lt.1 hr)
      induction hb : V.v z⁻¹ using WithTop.recTopCoe with
      | top => exact WithTop.top_pos
      | coe s =>
        rw [hb] at e
        have e2 : r + s = 0 := by exact_mod_cast e
        exact_mod_cast (show (0 : ℝ) < s by linarith)
  have h0 : Polynomial.aeval z p = 0 := by rw [Polynomial.aeval_def]; exact hp
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul] at h0
  have hn : ∀ i ∈ Finset.range p.natDegree, V.MM ((p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have e : (p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree = (p.coeff i : C) * z⁻¹ ^ (p.natDegree - i) := by
      rw [pow_sub₀ _ (inv_ne_zero hz0) hi'.le, ← inv_pow, inv_inv, zsmul_eq_mul]; ring
    rw [e]
    exact mm_int_mul (ge_intCast' _) (mm_pow hw (by omega))
  have e : (∑ i ∈ Finset.range p.natDegree, p.coeff i • z ^ i + z ^ p.natDegree) * z⁻¹ ^ p.natDegree
      = 0 * z⁻¹ ^ p.natDegree := by rw [h0]
  rw [add_mul, zero_mul, Finset.sum_mul, ← mul_pow, mul_inv_cancel₀ hz0, one_pow] at e
  have h1 : (1 : C) = -∑ i ∈ Finset.range p.natDegree, (p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree := by
    linear_combination e
  have := mm_neg (mm_sum hn)
  rw [← h1] at this
  exact not_mm_one this


theorem geom_int {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (n : ℕ) :
    V.Ge 0 (∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i)) :=
  VF.Ge.sum fun i _ => (hA.pow i).mul_int (hB.pow _)

theorem ge_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) {w : ℝ} (h : V.Ge w (A - B)) (n : ℕ) :
    V.Ge w (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact (geom_int hA hB n).mul_int h

theorem mm_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (h : V.MM (A - B)) (n : ℕ) :
    V.MM (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact mm_int_mul (geom_int hA hB n) h



theorem tele (z : ℕ → C) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ k : ℕ, V.Ge ((k + 1 : ℝ) * ε) (z (k + 1) - z k))
    (k j : ℕ) (hkj : k ≤ j) : V.Ge ((k + 1 : ℝ) * ε) (z j - z k) := by
  induction j, hkj using Nat.le_induction with
  | base => rw [sub_self]; exact VF.Ge.zero _
  | succ j hkj ih =>
    have e : z (j + 1) - z k = (z (j + 1) - z j) + (z j - z k) := by ring
    rw [e]
    refine VF.Ge.add ((h j).mono ?_) ih
    have : (k : ℝ) ≤ j := by exact_mod_cast hkj
    exact mul_le_mul_of_nonneg_right (by linarith) hε

def Kf (ε : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) / ε⌉₊



def Cpl (V : VF C) : Prop :=
  ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)



end Formalism.L2.FormalSeriesBounds.GmExArith
