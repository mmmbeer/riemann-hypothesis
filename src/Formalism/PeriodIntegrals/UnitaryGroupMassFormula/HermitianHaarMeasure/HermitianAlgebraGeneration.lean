import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development

section
open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem valSuccAbove {n : ℕ} (p : Fin (n + 1)) (x : Fin n) :
    (p.succAbove x).val = if x.val < p.val then x.val else x.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

theorem skip1Eq {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : skip1 i j = i.succAbove j := by
  apply Fin.ext
  rw [valSuccAbove]
  unfold skip1
  split_ifs <;> simp

theorem skip1Fun {t : ℕ} (i : Fin (t + 1)) : (skip1 i : Fin t → Fin (t + 1)) = i.succAbove :=
  funext (skip1Eq i)

theorem valSkip2 {t : ℕ} (i i' : Fin t) (j : Fin (t - 2)) :
    (skip2 i i' j).val =
      if j.val < i.val then j.val else if j.val + 1 < i'.val then j.val + 1 else j.val + 2 := by
  unfold skip2
  split_ifs <;> rfl

theorem skip2Lt {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : (k : ℕ) < (i' : ℕ)) :
    (skip2 (i'.succAbove k) i' : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  simp only [Function.comp, valSuccAbove, valSkip2]
  split_ifs <;> omega

theorem skip2Gt {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : ¬ (k : ℕ) < (i' : ℕ)) :
    (skip2 i' (i'.succAbove k) : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  simp only [Function.comp, valSuccAbove, valSkip2]
  split_ifs <;> omega

theorem pairSum {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (c d : Fin (t + 2) → A)
    (G : (Fin t → Fin (t + 2)) → A) :
    ∑ i : Fin (t + 2), ∑ i' : Fin (t + 2),
        (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • ((c i * d i' - c i' * d i) * G (skip2 i i')) else 0) =
      ∑ i' : Fin (t + 2), ∑ k : Fin (t + 1),
        ((-1 : ℂ) ^ ((i' : ℕ) + (k : ℕ))) • (c (i'.succAbove k) * d i' * G (i'.succAbove ∘ k.succAbove)) := by
  have hR : ∀ i' : Fin (t + 2), ∑ k : Fin (t + 1),
      ((-1 : ℂ) ^ ((i' : ℕ) + (k : ℕ))) • (c (i'.succAbove k) * d i' * G (i'.succAbove ∘ k.succAbove)) =
        ∑ j : Fin (t + 2),
          ((if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ))) • (c j * d i' * G (skip2 j i')) else 0) -
            (if i' < j then ((-1 : ℂ) ^ ((i' : ℕ) + (j : ℕ))) • (c j * d i' * G (skip2 i' j)) else 0)) := by
    intro i'
    conv_rhs => rw [Fin.sum_univ_succAbove _ i']
    simp only [lt_irrefl, if_false, sub_zero, zero_add]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : (k : ℕ) < (i' : ℕ)
    · have hv : ((i'.succAbove k : Fin (t + 2)) : ℕ) = k := by rw [valSuccAbove, if_pos hk]
      have h1 : i'.succAbove k < i' := by rw [Fin.lt_def, hv]; exact hk
      have h2 : ¬ i' < i'.succAbove k := by rw [Fin.lt_def, hv]; omega
      rw [if_pos h1, if_neg h2, sub_zero, skip2Lt i' k hk, hv, add_comm (k : ℕ)]
    · have hv : ((i'.succAbove k : Fin (t + 2)) : ℕ) = k + 1 := by rw [valSuccAbove, if_neg hk]
      have h1 : ¬ i'.succAbove k < i' := by rw [Fin.lt_def, hv]; omega
      have h2 : i' < i'.succAbove k := by rw [Fin.lt_def, hv]; omega
      rw [if_pos h2, if_neg h1, zero_sub, skip2Gt i' k hk, hv, ← neg_smul]
      congr 1
      rw [← add_assoc, pow_succ]
      ring
  have hL : ∀ i i' : Fin (t + 2),
      (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • ((c i * d i' - c i' * d i) * G (skip2 i i')) else 0) =
        (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • (c i * d i' * G (skip2 i i')) else 0) -
          (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • (c i' * d i * G (skip2 i i')) else 0) := by
    intro i i'
    split_ifs <;> simp [sub_mul, smul_sub]
  simp only [hL, Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i' _ => hR i')]
  simp only [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem intCastMul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (X : A) : (z : A) * X = (z : ℂ) • X := by
  rw [Algebra.smul_def, map_intCast]

theorem eSq (e : ℤˣ) : ((e : ℤ) : ℂ) * ((e : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem starE (e : ℤˣ) : star (((e : ℤ) : ℂ)) = ((e : ℤ) : ℂ) := star_intCast _

theorem prodSA {t : ℕ} (ε : Fin (t + 1) → ℤˣ) (i : Fin (t + 1)) :
    ∏ k, ε (i.succAbove k) = ε i * ∏ k, ε k := by
  rw [Fin.prod_univ_succAbove ε i, ← mul_assoc, Int.units_mul_self, one_mul]

theorem prodSA2 {t : ℕ} (ε : Fin (t + 2) → ℤˣ) (i : Fin (t + 2)) (k : Fin (t + 1)) :
    ∏ x, ε (i.succAbove (k.succAbove x)) = ε i * ε (i.succAbove k) * ∏ k, ε k := by
  have h := prodSA (fun y => ε (i.succAbove y)) k
  rw [h, prodSA ε i, ← mul_assoc, mul_comm (ε (i.succAbove k)) (ε i)]

theorem star1 (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {t : ℕ}
    (E : Fin (t + 1) → Fin (t + 1) → A) (ε : Fin (t + 1) → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (i j : Fin (t + 1)) (w : ℂ) :
    star (qminor E i.succAbove j.succAbove w) =
      (((ε i : ℤ) : ℂ) * ((ε j : ℤ) : ℂ)) • qminor E j.succAbove i.succAbove (star w) := by
  rw [hSM A (t + 1) t E ε hGl hE i.succAbove j.succAbove w, intCastMul, prodSA, prodSA,
    mul_mul_mul_comm, Int.units_mul_self, mul_one]
  push_cast
  rfl

theorem star2 (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {t : ℕ}
    (E : Fin (t + 2) → Fin (t + 2) → A) (ε : Fin (t + 2) → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (i : Fin (t + 2)) (k : Fin (t + 1))
    (j : Fin (t + 2)) (l : Fin (t + 1)) (w : ℂ) :
    star (qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) w) =
      (((ε i : ℤ) : ℂ) * ((ε (i.succAbove k) : ℤ) : ℂ) * (((ε j : ℤ) : ℂ) * ((ε (j.succAbove l) : ℤ) : ℂ))) •
        qminor E (j.succAbove ∘ l.succAbove) (i.succAbove ∘ k.succAbove) (star w) := by
  rw [hSM A (t + 2) t E ε hGl hE _ _ w, intCastMul]
  simp only [Function.comp_apply]
  rw [prodSA2, prodSA2, mul_mul_mul_comm, Int.units_mul_self, mul_one]
  push_cast
  rfl

theorem mvC (hMV : MoveVec) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
    (hGl : GlRel E) (hL : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (hC : ∀ a b, y a * y b = y b * y a) (a : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (w : ℂ) :
    ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (y (b j) * qminor E a (b ∘ j.succAbove) w) =
      ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j)) := by
  have h := hMV A n t E y hGl hL hC a b w
  simp only [intCastMul] at h
  push_cast at h
  exact h

theorem nested_minor_expansion_zero_one {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 1) → Fin (t + 1) → A)
    (Y Yb : Fin (t + 1) → A) (x xb : Fin (t + 1) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 0 1 = -∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E i.succAbove j.succAbove (u - 1)) := by
  simp only [tA, skip1Fun]

theorem nested_minor_expansion_one_zero {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 1) → Fin (t + 1) → A)
    (Y Yb : Fin (t + 1) → A) (x xb : Fin (t + 1) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 0 = -∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * xb i) • (Y j * qminor E i.succAbove j.succAbove u) := by
  simp only [tA, skip1Fun]

theorem star_transfer_diagonal_zero (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (u : ℂ) :
    star (tA E Y Yb x xb u 0 0) = tA E Y Yb x xb (star u) 0 0 := by
  show star (qminor E id id u) = qminor E id id (star u)
  rw [hSM A m m E ε hGl hE id id u, Int.units_mul_self]
  simp

theorem star_transfer_zero_one (hSM : StarMinor) (hMV : MoveVec) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (hxb : ∀ c, xb c = ((ε c : ℤ) : ℂ) * star (x c))
    (u : ℂ) :
    star (tA E Y Yb x xb u 0 1) = tA E Y Yb x xb (star u) 1 0 := by
  cases m with
  | zero => simp [tA]
  | succ t =>
    rw [nested_minor_expansion_zero_one, nested_minor_expansion_one_zero]
    have hterm : ∀ i j : Fin (t + 1),
        star (((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E i.succAbove j.succAbove (u - 1))) =
          ((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ)) * xb j) •
            (qminor E j.succAbove i.succAbove (star u - 1) * Y i) := by
      intro i j
      rw [star_smul, star_mul (Yb i), star1 hSM E ε hGl hE, hYb i, star_smul, star_star, starE, hxb j, star_mul,
        star_pow, star_neg, star_one, star_sub, star_one]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      have h1 := eSq (ε i)
      linear_combination ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * star (x j) * ((ε j : ℤ) : ℂ)) * h1
    simp only [star_neg, star_sum, hterm]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hmv := mvC hMV E Y hGl hLY hYY a.succAbove id (star u)
    simp only [Function.id_comp, id] at hmv
    have e1 : ∀ i : Fin (t + 1), ((-1 : ℂ) ^ ((a : ℕ) + (i : ℕ)) * xb a) • (qminor E a.succAbove i.succAbove (star u - 1) * Y i)
        = ((-1 : ℂ) ^ (a : ℕ) * xb a) • (((-1 : ℂ) ^ (i : ℕ)) • (qminor E a.succAbove i.succAbove (star u - 1) * Y i)) := by
      intro i; rw [smul_smul, pow_add]; ring_nf
    have e2 : ∀ j : Fin (t + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ)) * xb a) • (Y j * qminor E a.succAbove j.succAbove (star u))
        = ((-1 : ℂ) ^ (a : ℕ) * xb a) • (((-1 : ℂ) ^ (j : ℕ)) • (Y j * qminor E a.succAbove j.succAbove (star u))) := by
      intro j; rw [smul_smul, pow_add]; ring_nf
    simp only [e1, e2, ← Finset.smul_sum, hmv]

end PI.QnHermHaar
end
end

section
open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem mulAM {A : Type*} [Ring A] [Algebra ℂ A] (X : A) (c : ℂ) : X * algebraMap ℂ A c = c • X := by
  rw [Algebra.smul_def, Algebra.commutes]

theorem swap4a {A : Type*} [AddCommMonoid A] {p q : ℕ} (F : Fin p → Fin q → Fin p → Fin q → A) :
    ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ j, ∑ i, ∑ l, ∑ k, F i k j l := by
  calc ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, ∑ k, F i k j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ l, ∑ k, F i k j l := Finset.sum_comm

theorem swap4b {A : Type*} [AddCommMonoid A] {p q : ℕ} (F : Fin p → Fin q → Fin p → Fin q → A) :
    ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l :=
  Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem nested_minor_expansion_one_one {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 2) → Fin (t + 2) → A)
    (Y Yb : Fin (t + 2) → A) (x xb : Fin (t + 2) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 1 = -∑ i : Fin (t + 2), ∑ k : Fin (t + 1), ∑ j : Fin (t + 2), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb i * x j) •
        (Yb (i.succAbove k) * Y (j.succAbove l) *
          qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) (u - 1)) := by
  simp only [tA]
  congr 1

  set G : (Fin t → Fin (t + 2)) → A := fun s => ∑ j : Fin (t + 2), ∑ j' : Fin (t + 2),
    (if j < j' then ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ))) •
      ((Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) * qminor E s (skip2 j j') (u - 1)) else 0)
    with hG
  have h1 : ∀ i i' : Fin (t + 2), (∑ j : Fin (t + 2), ∑ j' : Fin (t + 2),
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0) =
      if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) •
        ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) * G (skip2 i i')) else 0 := by
    intro i i'
    by_cases hi : i < i'
    · simp only [hi, true_and, if_true, hG, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
      split_ifs
      · rw [mul_smul_comm, smul_smul, ← pow_add, mul_assoc]
        congr 2
        ring
      · simp
    · simp [hi]
  simp only [h1]
  have hp := pairSum Yb (fun i => algebraMap ℂ A (xb i)) G
  try simp only at hp
  rw [hp]
  have hq : ∀ s : Fin t → Fin (t + 2), G s = ∑ j : Fin (t + 2), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((j : ℕ) + (l : ℕ))) • (Y (j.succAbove l) * algebraMap ℂ A (x j) *
        qminor E s (j.succAbove ∘ l.succAbove) (u - 1)) := by
    intro s
    have h := pairSum Y (fun j => algebraMap ℂ A (x j)) (fun s' => qminor E s s' (u - 1))
    rw [hG]
    exact h
  simp only [hq, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ =>
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))))
  simp only [mulAM, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  congr 1
  ring

theorem transfer_commutator_one_one (hMV : MoveVec) (hMC : MoveCov) {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ}
    (E : Fin (t + 2) → Fin (t + 2) → A) (Y Yb : Fin (t + 2) → A) (hGl : GlRel E)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (hYbYb : ∀ a b, Yb a * Yb b = Yb b * Yb a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hLYb : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0)
    (a b : Fin (t + 2)) (w : ℂ) :
    ∑ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w * Yb (a.succAbove k) *
          Y (b.succAbove l)) =
      ∑ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
        (Yb (a.succAbove k) * Y (b.succAbove l) *
          qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w) := by
  have hz : ∀ (p : ℕ) (X : A), (((-1 : ℤ) ^ p : ℤ) : A) * X = ((-1 : ℂ) ^ p) • X := by
    intro p X
    rw [← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    try rfl
  have MC := fun l : Fin (t + 1) =>
    hMC A (t + 2) t E Yb hGl hLYb hYbYb a.succAbove (b.succAbove ∘ l.succAbove) w
  have MV := fun k : Fin (t + 1) =>
    hMV A (t + 2) t E Y hGl hLY hYY (a.succAbove ∘ k.succAbove) b.succAbove w
  simp only [hz] at MC MV
  have h1 : ∀ l : Fin (t + 1), ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w *
        (Yb (a.succAbove k) * Y (b.succAbove l))) =
      ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) *
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (w - 1) * Y (b.succAbove l))) := by
    intro l
    have e := congrArg (fun S => ((-1 : ℂ) ^ (l : ℕ)) • (S * Y (b.succAbove l))) (MC l)
    simp only [Finset.sum_mul, Finset.smul_sum, smul_mul_assoc, smul_smul, mul_assoc,
      mul_comm ((-1 : ℂ) ^ (l : ℕ))] at e
    exact e.symm
  have h2 : ∀ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) *
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (w - 1) * Y (b.succAbove l))) =
      ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) * (Y (b.succAbove l) *
        qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w)) := by
    intro k
    have e := congrArg (fun S => ((-1 : ℂ) ^ (k : ℕ)) • (Yb (a.succAbove k) * S)) (MV k)
    simp only [Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_smul] at e
    exact e.symm
  simp only [mul_assoc]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => h2 k

theorem starY {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ} (Y Yb : Fin m → A)
    (ε : Fin m → ℤˣ) (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (c : Fin m) :
    star (Y c) = ((ε c : ℤ) : ℂ) • Yb c := by
  have he : ((ε c : ℤ) : ℂ) * ((ε c : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [hYb c, smul_smul, he, one_smul]

theorem starYb {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ} (Y Yb : Fin m → A)
    (ε : Fin m → ℤˣ) (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (c : Fin m) :
    star (Yb c) = ((ε c : ℤ) : ℂ) • Y c := by
  rw [hYb c, star_smul, star_star, star_intCast]

theorem lower_right_ne_zero_of_upper_right_zero (hSM : StarMinor) (hMV : MoveVec) (hMC : MoveCov) {A : Type} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (hYbYb : ∀ a b, Yb a * Yb b = Yb b * Yb a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hLYb : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0)
    (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (hxb : ∀ c, xb c = ((ε c : ℤ) : ℂ) * star (x c))
    (u : ℂ) :
    star (tA E Y Yb x xb u 1 1) = tA E Y Yb x xb (star u) 1 1 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp [tA]
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
  have hterm : ∀ (i : Fin (t + 2)) (k : Fin (t + 1)) (j : Fin (t + 2)) (l : Fin (t + 1)),
      star (((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb i * x j) •
        (Yb (i.succAbove k) * Y (j.succAbove l) *
          qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) (u - 1))) =
      ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb j * x i) •
        (qminor E (j.succAbove ∘ l.succAbove) (i.succAbove ∘ k.succAbove) (star u - 1) *
          Yb (j.succAbove l) * Y (i.succAbove k)) := by
    intro i k j l
    rw [star_smul, star_mul (Yb _ * Y _), star_mul (Yb _), star2 hSM E ε hGl hE, starY Y Yb ε hYb, starYb Y Yb ε hYb,
      star_sub, star_one]
    simp only [star_mul', star_pow, star_neg, star_one, hxb, starE, star_star]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    have h1 := eSq (ε i)
    have h2 := eSq (ε (i.succAbove k))
    have h4 := eSq (ε (j.succAbove l))
    set p2 := ((ε (i.succAbove k) : ℤ) : ℂ)
    set p4 := ((ε (j.succAbove l) : ℤ) : ℂ)
    linear_combination ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * x i * star (x j) *
      ((ε j : ℤ) : ℂ)) * (p2 * p2 * p4 * p4 * h1 + p4 * p4 * h2 + h4)
  rw [nested_minor_expansion_one_one, nested_minor_expansion_one_one]
  simp only [star_neg, star_sum, hterm]
  congr 1
  conv_lhs => rw [swap4a]
  conv_rhs => rw [swap4b]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  have eL : ∑ l : Fin (t + 1), ∑ k : Fin (t + 1),
      ((-1 : ℂ) ^ ((b : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((a : ℕ) + (l : ℕ)) * xb a * x b) •
        (qminor E (a.succAbove ∘ l.succAbove) (b.succAbove ∘ k.succAbove) (star u - 1) *
          Yb (a.succAbove l) * Y (b.succAbove k)) =
      ((-1 : ℂ) ^ (a : ℕ) * (-1 : ℂ) ^ (b : ℕ) * xb a * x b) • ∑ l : Fin (t + 1), ∑ k : Fin (t + 1),
        ((-1 : ℂ) ^ (l : ℕ) * (-1 : ℂ) ^ (k : ℕ)) •
          (qminor E (a.succAbove ∘ l.succAbove) (b.succAbove ∘ k.succAbove) (star u - 1) *
            Yb (a.succAbove l) * Y (b.succAbove k)) := by
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    congr 1
    ring
  have eR : ∑ k : Fin (t + 1), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((b : ℕ) + (l : ℕ)) * xb a * x b) •
        (Yb (a.succAbove k) * Y (b.succAbove l) *
          qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (star u - 1)) =
      ((-1 : ℂ) ^ (a : ℕ) * (-1 : ℂ) ^ (b : ℕ) * xb a * x b) • ∑ k : Fin (t + 1), ∑ l : Fin (t + 1),
        ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
          (Yb (a.succAbove k) * Y (b.succAbove l) *
            qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (star u - 1)) := by
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    congr 1
    ring
  rw [eL, eR, transfer_commutator_one_one hMV hMC E Y Yb hGl hYY hYbYb hLY hLYb a b (star u - 1)]

end PI.QnHermHaar
end
end

section
open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem commSumA {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    (∑ i, h i) * g - g * (∑ i, h i) = ∑ i, (h i * g - g * h i) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem commSumB {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    g * (∑ i, h i) - (∑ i, h i) * g = ∑ i, (g * h i - h i * g) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem smulComm {A : Type*} [Ring A] [Algebra ℂ A] (α β : ℂ) (X Y : A) :
    (α • X) * (β • Y) - (β • Y) * (α • X) = (α * β) • (X * Y - Y * X) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm β α, smul_sub]

def vecC {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (Y : Fin m → A) : Fin m → A :=
  fun c => ∑ k, Q c k • Y k

def covC {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (Yb : Fin m → A) : Fin m → A :=
  fun c => ∑ l, P l c • Yb l

theorem qpApply {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1) (b c : Fin m) :
    ∑ j, Q b j * P j c = if b = c then 1 else 0 := by
  have h := congrFun (congrFun hQP b) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

theorem glConj {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hGl : GlRel E) (hQP : Q * P = 1) : GlRel (Econj E P Q) := by
  intro a b c d
  have hG : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0) := hGl
  simp only [Econj]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hG, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero]
  congr 1
  ·
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
    simp only [← Finset.sum_smul]
    have hc : ∀ i l : Fin m, ∑ j, P i a * Q b j * (P j c * Q d l) = (if b = c then 1 else 0) * (P i a * Q d l) := by
      intro i l
      rw [← qpApply P Q hQP b c, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    simp only [hc]
    split_ifs <;> simp
  ·
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∀ i j k : Fin m, P i a * Q b j * (P k c * Q d i) = (P k c * Q b j) * (Q d i * P i a) := by
      intros; ring
    simp only [e2]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
    simp only [← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP d a]
    split_ifs with h
    · simp only [mul_one]
      exact Finset.sum_comm
    · simp

theorem leibVec {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y : Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1)
    (hL : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0) (a b c : Fin m) :
    Econj E P Q a b * vecC Q Y c - vecC Q Y c * Econj E P Q a b = if a = c then -vecC Q Y b else 0 := by
  simp only [Econj, vecC]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hL, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  have e : ∀ i j : Fin m, P i a * Q b j * Q c i = Q b j * (Q c i * P i a) := by intros; ring
  simp only [e, ← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP c a]
  split_ifs with h1 h2 h2
  · simp [Finset.sum_neg_distrib]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

theorem leibCov {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Yb : Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1)
    (hL : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0) (a b c : Fin m) :
    Econj E P Q a b * covC P Yb c - covC P Yb c * Econj E P Q a b = if b = c then covC P Yb a else 0 := by
  simp only [Econj, covC]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hL, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e : ∀ i j : Fin m, P i a * Q b j * P j c = P i a * (Q b j * P j c) := by intros; ring
  simp only [e, ← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP b c]
  split_ifs <;> simp

theorem commVec {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Y : Fin m → A) (Q : Matrix (Fin m) (Fin m) ℂ)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (a b : Fin m) :
    vecC Q Y a * vecC Q Y b = vecC Q Y b * vecC Q Y a := by
  simp only [vecC, Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hYY k l, mul_comm (Q a k)]

theorem commCov {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Yb : Fin m → A) (P : Matrix (Fin m) (Fin m) ℂ)
    (hYY : ∀ a b, Yb a * Yb b = Yb b * Yb a) (a b : Fin m) :
    covC P Yb a * covC P Yb b = covC P Yb b * covC P Yb a := by
  simp only [covC, Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hYY k l, mul_comm (P k a)]

theorem sum_four_comm_version {A : Type*} [AddCommMonoid A] {m : ℕ} (f : Fin m → Fin m → Fin m → Fin m → A) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun k _ => Finset.sum_comm)

theorem starConj {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Hm P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ)
    (hstar : ∀ a b, star (E a b) = ∑ c, ∑ d, (Hm c b * Hm a d) • E c d)
    (hP : ∀ i j, star (P i j) = Q j i) (hQ : ∀ i j, star (Q i j) = P j i)
    (hHP : ∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ))
    (hQH : ∀ a l, ∑ i, Q a i * Hm i l = ((ε a : ℤ) : ℂ) * Q a l) (a b : Fin m) :
    star (Econj E P Q a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * Econj E P Q b a := by
  simp only [Econj, star_sum, star_smul, hstar, Finset.smul_sum, smul_smul, star_mul', hP, hQ]
  rw [sum_four_comm_version]
  simp only [← Finset.sum_smul, intCastMul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  congr 1
  have h1 : ∑ i, ∑ j, Q a i * P j b * (Hm k j * Hm i l) = (∑ i, Q a i * Hm i l) * (∑ j, Hm k j * P j b) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [h1, hQH, hHP]
  push_cast
  ring


end PI.QnHermHaar
end
end

section
open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem chatAβ {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ) (a : Fin m → ℂ)
    (l : Fin m) : chatA E w a (Pi.single l 1) =
      ∑ j : Fin m, ((-1 : ℂ) ^ ((l : ℕ) + (j : ℕ)) * a j) • qminor E (skip1 l) (skip1 j) w := by
  simp only [chatA]
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

theorem chatAa {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ) (β : Fin m → ℂ)
    (p : Fin m) : chatA E w (Pi.single p 1) β =
      ∑ i : Fin m, ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * β i) • qminor E (skip1 i) (skip1 p) w := by
  simp only [chatA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

theorem transfer_entry_zero_one {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 0 1 = -∑ l, Yb l * chatA E (u - 1) x (Pi.single l 1) := by
  show -∑ i : Fin m, ∑ j : Fin m,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E (skip1 i) (skip1 j) (u - 1)) = _
  simp only [chatAβ, Finset.mul_sum, mul_smul_comm]

theorem transfer_entry_one_zero {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 0 = -∑ p, Y p * chatA E u (Pi.single p 1) xb := by
  show -∑ i : Fin m, ∑ j : Fin m,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * xb i) • (Y j * qminor E (skip1 i) (skip1 j) u) = _
  simp only [chatAa, Finset.mul_sum, mul_smul_comm]
  exact congrArg Neg.neg Finset.sum_comm

theorem chatAlinβ {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a β : Fin m → ℂ) : chatA E w a β = ∑ l, β l • chatA E w a (Pi.single l 1) := by
  simp only [chatAβ]
  simp only [chatA, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

theorem chatAlina {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a β : Fin m → ℂ) : chatA E w a β = ∑ p, a p • chatA E w (Pi.single p 1) β := by
  simp only [chatAa]
  simp only [chatA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

theorem vecMulSingle {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (l l' : Fin m) :
    (Pi.single l (1 : ℂ) ᵥ* P) l' = P l l' := by
  first
    | (show ∑ j, (Pi.single l (1 : ℂ) : Fin m → ℂ) j * P j l' = P l l'
       simp [Pi.single_apply])
    | simp [Matrix.vecMul, Pi.single_apply]

theorem mulVecSingle {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (p p' : Fin m) :
    (Q *ᵥ Pi.single p (1 : ℂ)) p' = Q p' p := by
  first
    | (show ∑ j, Q p' j * (Pi.single p (1 : ℂ) : Fin m → ℂ) j = Q p' p
       simp [Pi.single_apply])
    | simp [Matrix.mulVec, Pi.single_apply]

theorem pull1 {A : Type*} [AddCommMonoid A] {m : ℕ} (g : Fin m → Fin m → Fin m → A) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ c, ∑ a, ∑ b, g a b c := by
  calc ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ c, ∑ b, g a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, g a b c := Finset.sum_comm

theorem pull6 {A : Type*} [AddCommMonoid A] {m : ℕ} (f : Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → A) :
    ∑ l, ∑ p, ∑ i, ∑ i', ∑ j, ∑ j', f l p i i' j j' = ∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ p, f l p i i' j j' := by
  calc ∑ l, ∑ p, ∑ i, ∑ i', ∑ j, ∑ j', f l p i i' j j'
        = ∑ i, ∑ l, ∑ p, ∑ i', ∑ j, ∑ j', f l p i i' j j' := pull1 _
    _ = ∑ i, ∑ i', ∑ l, ∑ p, ∑ j, ∑ j', f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => pull1 _
    _ = ∑ i, ∑ i', ∑ j, ∑ l, ∑ p, ∑ j', f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => pull1 _
    _ = ∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ p, f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
          Finset.sum_congr rfl fun j _ => pull1 _

theorem sumSingle {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (W : Fin m → A) (c : Fin m → ℂ) (i i' : Fin m) :
    W i * algebraMap ℂ A (c i') - W i' * algebraMap ℂ A (c i) =
      ∑ l, ((Pi.single l (1 : ℂ) : Fin m → ℂ) i * c i' - (Pi.single l (1 : ℂ) : Fin m → ℂ) i' * c i) • W l := by
  simp [Pi.single_apply, sub_smul, Finset.sum_sub_distrib, ite_smul]
  simp only [Algebra.smul_def, Algebra.commutes]

private theorem sum_mul_sum_mul_eq_sum_sum {A : Type*} [Ring A] {m : ℕ} (f g : Fin m → A) (q : A) :
    (∑ l, f l) * (∑ p, g p) * q = ∑ l, ∑ p, f l * g p * q := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  try (first | rfl | exact Finset.sum_comm)

theorem general_second_minor_expansion {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (W V : Fin m → A) (w : ℂ)
    (a' β' : Fin m → ℂ) :
    ∑ l, ∑ p, W l * V p * chat2A E w (Pi.single p 1) a' (Pi.single l 1) β' =
      ∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
            ((W i * algebraMap ℂ A (β' i') - W i' * algebraMap ℂ A (β' i)) *
              (V j * algebraMap ℂ A (a' j') - V j' * algebraMap ℂ A (a' j)) *
              qminor E (skip2 i i') (skip2 j j') w)
        else 0 := by
  simp only [chat2A, Finset.mul_sum, mul_ite, mul_zero]
  refine (pull6 _).trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  by_cases h : i < i' ∧ j < j'
  · simp only [if_pos h]
    rw [sumSingle W β' i i', sumSingle V a' j j', sum_mul_sum_mul_eq_sum_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
  · simp only [if_neg h, Finset.sum_const_zero]

theorem transfer_entry_one_one {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 1 = -∑ l, ∑ p, Yb l * Y p * chat2A E (u - 1) (Pi.single p 1) x (Pi.single l 1) xb := by
  rw [general_second_minor_expansion E Yb Y (u - 1) x xb]
  try rfl

private theorem mul_sum_mul_sum_eq_sum_sum {m : ℕ} (a : ℂ) (f g : Fin m → ℂ) :
    a * (∑ l, f l) * (∑ p, g p) = ∑ l, ∑ p, a * f l * g p := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  try (first | rfl | exact Finset.sum_comm)

private theorem sub_mul_eq_sum_single_sub_mul {m : ℕ} (β c : Fin m → ℂ) (i i' : Fin m) :
    β i * c i' - β i' * c i =
      ∑ l, β l * ((Pi.single l (1 : ℂ) : Fin m → ℂ) i * c i' - (Pi.single l (1 : ℂ) : Fin m → ℂ) i' * c i) := by
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite]

theorem chat2Alin {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a a' β β' : Fin m → ℂ) :
    chat2A E w a a' β β' = ∑ l, ∑ p, (β l * a p) • chat2A E w (Pi.single p 1) a' (Pi.single l 1) β' := by
  simp only [chat2A, Finset.smul_sum, smul_ite, smul_zero, smul_smul]
  refine Eq.trans ?_ (pull6 _).symm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  by_cases h : i < i' ∧ j < j'
  · simp only [if_pos h]
    simp only [← Finset.sum_smul]
    congr 1
    rw [sub_mul_eq_sum_single_sub_mul β β' i i', sub_mul_eq_sum_single_sub_mul a a' j j', mul_sum_mul_sum_eq_sum_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ => by ring
  · simp only [if_neg h, Finset.sum_const_zero]

private theorem measurePreserving_swap4 {A : Type*} [AddCommMonoid A] {m : ℕ} (g : Fin m → Fin m → Fin m → Fin m → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, g a b c d = ∑ c, ∑ d, ∑ a, ∑ b, g a b c d :=
  (pull1 _).trans (Finset.sum_congr rfl fun _ _ => pull1 _)

theorem tATrans (hCC : ContractionsCovariant) {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (P Q : Matrix (Fin m) (Fin m) ℂ)
    (hGl : GlRel E) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (p q : Fin 2) :
    tA E Y Yb x xb u p q = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u p q := by
  have h00 : tA E Y Yb x xb u 0 0 = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u 0 0 :=
    (hCC A m E P Q hGl hQP hPQ u 0 0 0 0).1.symm
  have h01 : tA E Y Yb x xb u 0 1 = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u 0 1 := by
    have key : ∀ l', chatA E (u - 1) x (Pi.single l' 1) =
        ∑ l, P l' l • chatA (Econj E P Q) (u - 1) (Q *ᵥ x) (Pi.single l 1) := by
      intro l'
      rw [← (hCC A m E P Q hGl hQP hPQ (u - 1) x x (Pi.single l' 1) (Pi.single l' 1)).2.1, chatAlinβ]
      try simp only [vecMulSingle]
    rw [transfer_entry_zero_one, transfer_entry_zero_one]
    congr 1
    simp only [key, covC, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    exact Finset.sum_comm
  have h10 : tA E Y Yb x xb u 1 0 = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u 1 0 := by
    have key : ∀ p', chatA E u (Pi.single p' 1) xb =
        ∑ p, Q p p' • chatA (Econj E P Q) u (Pi.single p 1) (xb ᵥ* P) := by
      intro p'
      rw [← (hCC A m E P Q hGl hQP hPQ u (Pi.single p' 1) (Pi.single p' 1) xb xb).2.1, chatAlina]
      try simp only [mulVecSingle]
    rw [transfer_entry_one_zero, transfer_entry_one_zero]
    congr 1
    simp only [key, vecC, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    exact Finset.sum_comm
  have h11 : tA E Y Yb x xb u 1 1 = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u 1 1 := by
    have key : ∀ l' p', chat2A E (u - 1) (Pi.single p' 1) x (Pi.single l' 1) xb =
        ∑ l, ∑ p, (P l' l * Q p p') •
          chat2A (Econj E P Q) (u - 1) (Pi.single p 1) (Q *ᵥ x) (Pi.single l 1) (xb ᵥ* P) := by
      intro l' p'
      rw [← (hCC A m E P Q hGl hQP hPQ (u - 1) (Pi.single p' 1) x (Pi.single l' 1) xb).2.2, chat2Alin]
      try simp only [vecMulSingle, mulVecSingle]
    rw [transfer_entry_one_one, transfer_entry_one_one]
    congr 1
    simp only [key, covC, vecC, Finset.mul_sum, Finset.sum_mul]
    simp only [smul_mul_assoc]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    refine (measurePreserving_swap4 _).trans ?_
    first
      | rfl
      | exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
  fin_cases p <;> fin_cases q
  exacts [h00, h01, h10, h11]

end PI.QnHermHaar
end
end

section
open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem hermitian_algebra_generation : HermAlgFrom := by
  unfold HermAlgFrom HermAlg
  intro hSM hCC hMV hMC A _ _ _ _ m E Y Yb Hm x xb hGl hHm hHm2 hstarE hYY hYbYb hYYb hLY hLYb hYbH hxbH u p q

  obtain ⟨P, Q, ε, hQP, hPQ, hPs, hQs, hHmP, hQHm⟩ : ∃ (P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ),
      Q * P = 1 ∧ P * Q = 1 ∧ (∀ i j, star (P i j) = Q j i) ∧ (∀ i j, star (Q i j) = P j i) ∧
      (∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ)) ∧
      (∀ a l, ∑ i, Q a i * Hm i l = ((ε a : ℤ) : ℂ) * Q a l) := by
    have hH : Hm.IsHermitian := hHm
    set P : Matrix (Fin m) (Fin m) ℂ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hPdef
    have hQP : star P * P = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
        | exact unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
        | exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have hPQ : P * star P = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
        | exact unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
        | exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
    set d : Fin m → ℂ := fun b => ((hH.eigenvalues b : ℝ) : ℂ) with hd
    have hspec : Hm = P * Matrix.diagonal d * star P := by
      first
        | exact hH.spectral_theorem
        | exact Matrix.IsHermitian.spectral_theorem hH
    have hHP : Hm * P = P * Matrix.diagonal d := by
      rw [hspec]
      simp only [Matrix.mul_assoc, hQP, Matrix.mul_one]
    have hQH : star P * Hm = Matrix.diagonal d * star P := by
      rw [hspec]
      simp only [← Matrix.mul_assoc, hQP, Matrix.one_mul]
    have hPHP : star P * Hm * P = Matrix.diagonal d := by
      rw [hQH, Matrix.mul_assoc, hQP, Matrix.mul_one]
    have hD2 : Matrix.diagonal d * Matrix.diagonal d = 1 := by
      rw [← hPHP]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P (star P), hPQ, Matrix.one_mul, ← Matrix.mul_assoc Hm Hm, hHm2, Matrix.one_mul, hQP]
    have hdd : ∀ b, hH.eigenvalues b * hH.eigenvalues b = 1 := fun b => by
      have h1 := congrFun (congrFun hD2 b) b
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
      have h2 : ((hH.eigenvalues b : ℝ) : ℂ) * ((hH.eigenvalues b : ℝ) : ℂ) = 1 := h1
      exact_mod_cast h2
    have hεd : ∀ b, (((if hH.eigenvalues b = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℂ) = d b := fun b => by
      rcases mul_self_eq_one_iff.mp (hdd b) with h | h
      · simp [hd, h]
      · have hne : hH.eigenvalues b ≠ 1 := by rw [h]; norm_num
        rw [if_neg hne]
        simp [hd, h]
    refine ⟨P, star P, fun b => if hH.eigenvalues b = 1 then 1 else -1, hQP, hPQ,
      fun i j => by rw [Matrix.star_apply], fun i j => by rw [Matrix.star_apply, star_star], fun k b => ?_,
      fun a l => ?_⟩
    · have h1 := congrFun (congrFun hHP k) b
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at h1
      rw [h1]
      congr 1
      exact (hεd b).symm
    · have h1 := congrFun (congrFun hQH a) l
      rw [Matrix.mul_apply, Matrix.diagonal_mul] at h1
      rw [h1]
      congr 1
      exact (hεd a).symm

  have hGl' := glConj E P Q hGl hQP
  have hE' := starConj E Hm P Q ε hstarE hPs hQs hHmP hQHm
  have hYY' := commVec Y Q hYY
  have hYbYb' := commCov Yb P hYbYb
  have hLY' := leibVec E Y P Q hQP hLY
  have hLYb' := leibCov E Yb P Q hQP hLYb
  have hYb' : ∀ c, covC P Yb c = ((ε c : ℤ) : ℂ) • star (vecC Q Y c) := by
    intro c
    simp only [covC, vecC, hYbH, star_sum, star_smul, hQs, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    calc ∑ l, P l c * Hm l' l = ∑ l, Hm l' l * P l c := Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = P l' c * ((ε c : ℤ) : ℂ) := hHmP l' c
      _ = ((ε c : ℤ) : ℂ) * P l' c := mul_comm _ _
  have hxb' : ∀ c, (xb ᵥ* P) c = ((ε c : ℤ) : ℂ) * star ((Q *ᵥ x) c) := by
    intro c
    show ∑ l, xb l * P l c = ((ε c : ℤ) : ℂ) * star (∑ k, Q c k * x k)
    simp only [hxbH, star_sum, star_mul', hQs, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    have e1 : ∑ l, Hm l' l * star (x l') * P l c = star (x l') * ∑ l, Hm l' l * P l c := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, hHmP l' c]
    ring
  rw [tATrans hCC E Y Yb x xb P Q hGl hQP hPQ u p q, tATrans hCC E Y Yb x xb P Q hGl hQP hPQ (star u) q p]
  fin_cases p <;> fin_cases q
  · exact star_transfer_diagonal_zero hSM _ _ _ _ _ ε hGl' hE' u
  · exact star_transfer_zero_one hSM hMV _ _ _ _ _ ε hGl' hE' hYY' hLY' hYb' hxb' u
  · have h := congrArg star (star_transfer_zero_one hSM hMV _ _ _ _ _ ε hGl' hE' hYY' hLY' hYb' hxb' (star u))
    rw [star_star, star_star] at h
    exact h.symm
  · exact lower_right_ne_zero_of_upper_right_zero hSM hMV hMC _ _ _ _ _ ε hGl' hE' hYY' hYbYb' hLY' hLYb' hYb' hxb' u

end PI.QnHermHaar
end
end
