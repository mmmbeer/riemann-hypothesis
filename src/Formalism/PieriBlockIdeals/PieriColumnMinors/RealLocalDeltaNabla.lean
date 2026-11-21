import Formalism.PieriBlockIdeals.LocalFaithfullyFlat
import Formalism.PieriBlockIdeals.ExponentBoundCounterexample
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
import Mathlib
import Formalism.PieriBlockIdeals.StatementW
import Formalism.RankGapBounds.RankGapProofs.FormsTensorLocalization
import Formalism.PieriBlockIdeals.JointTheoremALoc

section
noncomputable section

open Classical

namespace Formalism.CohomologicalDescent

open CoxeterSystem List

namespace ReflectionWords

variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

def reflStep (g : W) (p : W × ZMod 2) : W × ZMod 2 :=
  (g * p.1 * g, p.2 + if p.1 = g then 1 else 0)

lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

lemma reflStep_involutive {g : W} (hg : g * g = 1) : Function.Involutive (reflStep g) := by
  rintro ⟨w, e⟩
  have h1 : g * (g * w * g) * g = w := by
    calc g * (g * w * g) * g = (g * g) * w * (g * g) := by group
    _ = w := by simp [hg]
  have h2 : (g * w * g = g) ↔ (w = g) := by
    constructor
    · intro h
      calc w = g * (g * w * g) * g := h1.symm
      _ = g := by rw [h, hg, one_mul]
    · rintro rfl; rw [hg, one_mul]
  simp only [reflStep, h1, h2, Prod.mk.injEq, true_and]
  rw [add_assoc, zmod_two_add_self, add_zero]

def reflPerm (i : B) : Equiv.Perm (W × ZMod 2) :=
  Function.Involutive.toPerm _ (reflStep_involutive (cs.simple_mul_simple_self i))

lemma prod_map_reflPerm (ω : List B) (w : W) (e : ZMod 2) :
    (ω.map (reflPerm cs)).prod (w, e) =
      (cs.wordProd ω * w * (cs.wordProd ω)⁻¹, e + ((cs.rightInvSeq ω).count w : ZMod 2)) := by
  induction ω with
  | nil => simp [rightInvSeq]
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih]
    simp only [reflPerm, Function.Involutive.coe_toPerm, reflStep, rightInvSeq, List.count_cons,
      wordProd_cons, mul_inv_rev, inv_simple]
    have key : (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω = w ↔
        cs.wordProd ω * w * (cs.wordProd ω)⁻¹ = cs.simple i := by
      constructor
      · rintro rfl; group
      · intro h; rw [← h]; group
    refine Prod.ext ?_ ?_
    · simp only; group
    · by_cases h : cs.wordProd ω * w * (cs.wordProd ω)⁻¹ = cs.simple i
      · have h' := key.mpr h
        simp [h, h', add_assoc]
      · have h' : ¬ (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω = w := fun hh => h (key.mp hh)
        simp [h, h']

lemma prod_map_alternatingWord {G : Type*} [Monoid G] (f : B → G) (i i' : B) (p : ℕ) :
    ((alternatingWord i i' (2 * p)).map f).prod = (f i * f i') ^ p := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    have h : alternatingWord i i' (2 * (p + 1)) = i :: i' :: alternatingWord i i' (2 * p) := by
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ', alternatingWord_succ']
      simp
    rw [h]
    simp [ih, pow_succ', mul_assoc]

lemma reverse_alternatingWord (i i' : B) (p : ℕ) :
    (alternatingWord i i' (2 * p)).reverse = alternatingWord i' i (2 * p) := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    have h : alternatingWord i i' (2 * (p + 1)) = i :: i' :: alternatingWord i i' (2 * p) := by
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ', alternatingWord_succ']
      simp
    rw [h, show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ, alternatingWord_succ]
    simp [ih]

lemma count_leftInvSeq_alternatingWord_even (i i' : B) (w : W) :
    Even ((cs.leftInvSeq (alternatingWord i' i (2 * M i i'))).count w) := by
  set m := M i i' with hm
  set L := cs.leftInvSeq (alternatingWord i' i (2 * m)) with hL
  have hlen : L.length = 2 * m := by simp [L]
  have hper : ∀ k (hk : k < m), L[m + k]'(by omega) = L[k]'(by omega) := by
    intro k hk
    simp only [L]
    rw [cs.getElem_leftInvSeq_alternatingWord i' i m (m + k) (by omega),
      cs.getElem_leftInvSeq_alternatingWord i' i m k (by omega),
      cs.prod_alternatingWord_eq_mul_pow, cs.prod_alternatingWord_eq_mul_pow]
    have e1 : ¬ Even (2 * (m + k) + 1) := by simp
    have e2 : ¬ Even (2 * k + 1) := by simp
    simp only [e1, e2, if_false]
    rw [show (2 * (m + k) + 1) / 2 = m + k by omega, show (2 * k + 1) / 2 = k by omega, pow_add,
      hm, cs.simple_mul_simple_pow, one_mul]
  have hsplit : L = L.take m ++ L.take m := by
    conv_lhs => rw [← List.take_append_drop m L]
    congr 1
    apply List.ext_getElem
    · simp [hlen]; omega
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_take]
      exact hper k (by simp [hlen] at h2; omega)
  rw [hsplit, List.count_append]
  exact ⟨_, rfl⟩

lemma isLiftable_reflPerm : M.IsLiftable (reflPerm cs) := by
  intro i i'
  rw [← prod_map_alternatingWord]
  refine Equiv.ext fun p => ?_
  obtain ⟨w, e⟩ := p
  rw [prod_map_reflPerm]
  have h1 : cs.wordProd (alternatingWord i i' (2 * M i i')) = 1 := by
    rw [wordProd, prod_map_alternatingWord, cs.simple_mul_simple_pow]
  have h2 : ((cs.rightInvSeq (alternatingWord i i' (2 * M i i'))).count w : ZMod 2) = 0 := by
    rw [← List.count_reverse, ← leftInvSeq_reverse, reverse_alternatingWord]
    obtain ⟨r, hr⟩ := count_leftInvSeq_alternatingWord_even cs i i' w
    rw [hr]; push_cast; exact zmod_two_add_self _
  simp [h1, h2]

def act : W →* Equiv.Perm (W × ZMod 2) := cs.lift ⟨reflPerm cs, isLiftable_reflPerm cs⟩

end ReflectionWords

universe u v

namespace ReflectionWords

lemma h11 : (1 : ZMod 2) + 1 = 0 := by decide

end ReflectionWords

end Formalism.CohomologicalDescent
end
end

section
open MvPolynomial CategoryTheory TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.SL2BinomialLattices

open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA

universe u v u' v'

theorem maxVal_le_log_alt (l n : ℕ) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l n ≤ Nat.log l n :=
  Finset.sup_le fun _ _ => Nat.factorization_choose_le_log


theorem log_le_log_bound : LgLog := by
  intro l y
  by_cases h0 : Nat.log l y = 0
  · rw [h0]
    simpa using Real.log_natCast_nonneg y
  · obtain ⟨hl, hy⟩ : 1 < l ∧ l ≤ y := by
      by_contra hcon
      apply h0
      rw [Nat.log_eq_zero_iff]
      omega
    have h1 : l ^ Nat.log l y ≤ y := Nat.pow_log_le_self l (by omega)
    have h2 : ((l : ℝ)) ^ Nat.log l y ≤ (y : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) < (l : ℝ) ^ Nat.log l y := by positivity
    have h4 := Real.log_le_log h3 h2
    rwa [Real.log_pow] at h4

theorem sum_maxVal_le_card_mul_log {N : ℕ} (U : Fin N → ℤ) (l M : ℕ) (hl : 0 < l) (s : Finset (Fin N × Fin N))
    (h : ∀ p ∈ s, U p.1 - U p.2 ≤ (M : ℤ)) :
    ∑ p ∈ s, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat ≤ s.card * Nat.log l M ∧
      (M ≤ l → ∑ p ∈ s, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat = 0) := by
  constructor
  · rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    have := h p hp
    exact (maxVal_le_log_alt l _).trans (Nat.log_mono_right (by omega))
  · intro hM
    apply Finset.sum_eq_zero
    intro p hp
    apply Formalism.CohomologicalDescent.max_val_eq_zero_of_lt
    have := h p hp
    omega

theorem card_posPairs (N : ℕ) : (posPairs N).card = N.choose 2 := by
  have h1 : (posPairs N).card = ∑ b : Fin N, (Finset.Iio b).card := by
    unfold posPairs
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.card_filter]
    congr 1
    ext a
    simp
  rw [h1]
  simp only [Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id, Nat.choose_two_right]


theorem nat_le_mul_log_real (ex c l y : ℕ) (h : ex ≤ c * Nat.log l y) :
    (ex : ℝ) * Real.log l ≤ (c : ℝ) * Real.log y := by
  have h1 : (ex : ℝ) ≤ (c : ℝ) * (Nat.log l y : ℝ) := by exact_mod_cast h
  have h2 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
  calc (ex : ℝ) * Real.log l ≤ (c : ℝ) * (Nat.log l y : ℝ) * Real.log l :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = (c : ℝ) * ((Nat.log l y : ℝ) * Real.log l) := by ring
    _ ≤ (c : ℝ) * Real.log y := mul_le_mul_of_nonneg_left (log_le_log_bound l y) (Nat.cast_nonneg c)

theorem sum_posPairs_split {N : ℕ} (k : ℕ) (g : Fin N × Fin N → ℕ) :
    ∑ p ∈ posPairs N, g p = ∑ p ∈ (posPairs N).filter (fun p => p.2.val < k), g p +
      ∑ p ∈ (posPairs N).filter (fun p => k ≤ p.1.val), g p +
      ∑ p ∈ (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val), g p := by
  have hlt : ∀ p ∈ posPairs N, p.1.val < p.2.val := fun p hp => (Finset.mem_filter.1 hp).2
  have hR : (posPairs N).filter (fun p => ¬ p.2.val < k ∧ k ≤ p.1.val) =
      (posPairs N).filter (fun p => k ≤ p.1.val) :=
    Finset.filter_congr fun p hp => by have := hlt p hp; omega
  have hC : (posPairs N).filter (fun p => ¬ p.2.val < k ∧ ¬ k ≤ p.1.val) =
      (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val) :=
    Finset.filter_congr fun p hp => by have := hlt p hp; omega
  rw [← Finset.sum_filter_add_sum_filter_not (posPairs N) (fun p => p.2.val < k),
    ← Finset.sum_filter_add_sum_filter_not ((posPairs N).filter (fun p => ¬ p.2.val < k))
      (fun p => k ≤ p.1.val), Finset.filter_filter, Finset.filter_filter, hR, hC, add_assoc]

theorem raising_split_three : ESplit3 := by
  intro N k l U
  exact sum_posPairs_split k _

def embedFinFirst {N k : ℕ} (hk : k ≤ N) : Fin k ↪ Fin N := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩

def embedFinLast (N k : ℕ) : Fin (N - k) ↪ Fin N :=
  ⟨fun a => ⟨k + a.val, by have := a.isLt; omega⟩, fun a b h => by
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)⟩

theorem posPairs_filter_lt {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => p.2.val < k) =
      (posPairs k).map ((embedFinFirst hk).prodMap (embedFinFirst hk)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨hab, hb⟩
    have hab' : a.val < b.val := hab
    exact ⟨(⟨a.val, by omega⟩, ⟨b.val, hb⟩), hab, rfl⟩
  · rintro ⟨⟨a', b'⟩, hab, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact ⟨hab, b'.isLt⟩

theorem posPairs_filter_ge {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => k ≤ p.1.val) =
      (posPairs (N - k)).map ((embedFinLast N k).prodMap (embedFinLast N k)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨hab, ha⟩
    have hab' : a.val < b.val := hab
    have ha2 := a.isLt
    have hb2 := b.isLt
    refine ⟨(⟨a.val - k, by omega⟩, ⟨b.val - k, by omega⟩), ?_, ?_⟩
    · show a.val - k < b.val - k
      omega
    · apply Prod.ext
      · apply Fin.ext
        show k + (a.val - k) = a.val
        omega
      · apply Fin.ext
        show k + (b.val - k) = b.val
        omega
  · rintro ⟨⟨a', b'⟩, hab, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    have hab' : a'.val < b'.val := hab
    refine ⟨?_, ?_⟩
    · show k + a'.val < k + b'.val
      omega
    · show k ≤ k + a'.val
      omega

theorem posPairs_filter_cross {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val) =
      ((Finset.univ : Finset (Fin k)).map (embedFinFirst hk)) ×ˢ
        ((Finset.univ : Finset (Fin (N - k))).map (embedFinLast N k)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Finset.mem_product]
  constructor
  · rintro ⟨-, ha, hb⟩
    have hb2 := b.isLt
    refine ⟨⟨⟨a.val, ha⟩, rfl⟩, ⟨⟨b.val - k, by omega⟩, ?_⟩⟩
    apply Fin.ext
    show k + (b.val - k) = b.val
    omega
  · rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
    have := a'.isLt
    refine ⟨?_, ?_, ?_⟩
    · show a'.val < k + b'.val
      omega
    · exact a'.isLt
    · show k ≤ k + b'.val
      omega

theorem choose_split_alt : ChooseSplit := by
  intro N k hk
  have h1 : ((posPairs N).filter (fun p => p.2.val < k)).card = k.choose 2 := by
    rw [posPairs_filter_lt hk, Finset.card_map, card_posPairs]
  have h2 : ((posPairs N).filter (fun p => k ≤ p.1.val)).card = (N - k).choose 2 := by
    rw [posPairs_filter_ge hk, Finset.card_map, card_posPairs]
  have h3 : ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)).card = k * (N - k) := by
    rw [posPairs_filter_cross hk, Finset.card_product, Finset.card_map, Finset.card_map,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  refine ⟨?_, h1, h2, h3⟩
  have h4 := sum_posPairs_split (N := N) k (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h4
  rw [card_posPairs, h1, h2, h3] at h4
  exact h4.symm

theorem three_bounds : ThreeBounds := by
  intro l N k h S eta xm lo U hl sh
  obtain ⟨-, c1, c2, c3⟩ := choose_split_alt N k sh.k_le
  have hlt : ∀ p ∈ posPairs N, p.1.val < p.2.val := fun p hp => (Finset.mem_filter.1 hp).2
  have b1 := sum_maxVal_le_card_mul_log U l S hl.pos ((posPairs N).filter (fun p => p.2.val < k)) (by
    intro p hp
    rw [Finset.mem_filter] at hp
    have h0 := hlt p hp.1
    have h1 := sh.cloudIn p.1 (by omega)
    have h2 := sh.cloudIn p.2 hp.2
    omega)
  have b2 := sum_maxVal_le_card_mul_log U l eta hl.pos ((posPairs N).filter (fun p => k ≤ p.1.val)) (by
    intro p hp
    rw [Finset.mem_filter] at hp
    have h0 := hlt p hp.1
    have h1 := sh.restIn p.1 hp.2
    have h2 := sh.restIn p.2 (by omega)
    omega)
  have b3 := sum_maxVal_le_card_mul_log U l h hl.pos
    ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)) (by
    intro p _
    have h1 := sh.inRange p.1
    have h2 := sh.inRange p.2
    omega)
  rw [c1] at b1
  rw [c2] at b2
  rw [c3] at b3
  exact ⟨b1.1, b1.2, b2.1, b2.2, b3.1, Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))⟩

theorem real_log_mono_of_le (a : ℕ) (b : ℝ) (hab : (a : ℝ) ≤ b) (hb : 0 ≤ Real.log b) :
    Real.log a ≤ Real.log b := by
  by_cases h0 : a = 0
  · rw [h0]
    simpa using hb
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0) hab

theorem choose_two_le_sq (N : ℕ) : (N.choose 2 : ℝ) ≤ (N : ℝ) ^ 2 := by
  rw [Nat.cast_choose_two]
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem size_large : SizeLarge := by
  intro l N k h S eta ex m t xm lo U hl sh hex heta hmt
  obtain ⟨b1, -, -, b2, b3, -⟩ := three_bounds l N k h S eta xm lo U hl sh
  have h0 := raising_split_three N k l U
  rw [b2 heta] at h0
  constructor
  · have e1 := nat_le_mul_log_real _ _ _ _ b1
    have e3 := nat_le_mul_log_real _ _ _ _ b3
    have hex' : (ex : ℝ) ≤ (eCl U k l : ℝ) + (eCross U k l : ℝ) := by
      have : ex ≤ eCl U k l + eCross U k l := by omega
      exact_mod_cast this
    have hl0 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
    push_cast at e3
    nlinarith [mul_le_mul_of_nonneg_right hex' hl0]
  · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
    have l1 : 0 ≤ Real.log (3 * (h : ℝ)) := by
      have := Real.log_natCast_nonneg (3 * h)
      push_cast at this
      exact this
    have l2 : 0 ≤ Real.log ((S : ℝ) + k) := by
      have := Real.log_natCast_nonneg (S + k)
      push_cast at this
      exact this
    have a1 : Real.log h ≤ Real.log (3 * (h : ℝ)) := real_log_mono_of_le h _ (by linarith) l1
    have a2 : Real.log S ≤ Real.log ((S : ℝ) + k) := real_log_mono_of_le S _ (by linarith) l2
    have a3 : ((N - k : ℕ) : ℝ) ≤ (m : ℝ) + t := by exact_mod_cast hmt
    have a4 : (k : ℝ) * ((N - k : ℕ) : ℝ) ≤ (k : ℝ) * ((m : ℝ) + t) :=
      mul_le_mul_of_nonneg_left a3 hk0
    have a5 := mul_le_mul a4 a1 (Real.log_natCast_nonneg h) (by positivity)
    have a6 := mul_le_mul (choose_two_le_sq k) a2 (Real.log_natCast_nonneg S) (by positivity)
    linarith









end Formalism.CohomologicalDescent.SL2BinomialLattices
end
end

section
namespace Formalism.CohomologicalDescent

open TensorProduct Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization




end Formalism.CohomologicalDescent
end

section
open MvPolynomial TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla

open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices


theorem units_of_local_holds : UnitsOfLocal := by
  intro O _ _ l hl hlO m hm
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  have hb : ((l : ℤ) * Nat.gcdA l m + (m : ℤ) * Nat.gcdB l m) = 1 := by
    have h := Nat.gcd_eq_gcd_ab l m
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have hO : ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) = 1 := by
    have h := congrArg (Int.cast : ℤ → O) hb
    push_cast at h
    exact h
  have hu : IsUnit ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) := by
    rw [hO]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
  · exact absurd (isUnit_of_mul_isUnit_left h) hlO
  · exact isUnit_of_mul_isUnit_left h













section core

variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ) (hl : l.Prime)
  (hlO : ¬ IsUnit (l : O)) (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
  (ν : ∀ i, Fin (n i) → ℕ) (e : ι → ℕ) (he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (e i))

include hl hlO he





end core


















theorem nabla_rep_tensor_product : NablaRepTprod := by
  intro O _ ι r n ν g a
  exact ⟨PiTensorProduct.map_tprod (fun i => dualWeylRep O (r i) (n i) (ν i) (g i)) a, fun i => rfl⟩

theorem delta_lattice_stable_holds : DeltaInStable := by
  intro O _ r n hn ν g x hx
  exact Formalism.UG.P.weyl_module_GL_stable O r n hn ν g _ hx

theorem nablaRep_mem_delta (O : Type) [CommRing O] (ι : Type) (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
    (ν : ∀ i, Fin (n i) → ℕ) (g : ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O)
    (x : Nabla O r n ν) (hx : x ∈ Delta O r n hn ν) : nablaRep O r n ν g x ∈ Delta O r n hn ν := by
  unfold Delta tensSub at hx ⊢
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
  clear hx
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, (nabla_rep_tensor_product O ι r n ν g _).1]
    refine Submodule.smul_mem _ c (LinearMap.mem_range.mpr ⟨PiTensorProduct.tprod O (fun i =>
      (⟨dualWeylRep O (r i) (n i) (ν i) (g i) (a i),
        delta_lattice_stable_holds O (r i) (n i) (hn i) (ν i) (g i) _ (a i).2⟩ :
          deltaIn O (r i) (n i) (hn i) (ν i))), ?_⟩)
    rw [PiTensorProduct.map_tprod]
    all_goals rfl
  | add x y ihx ihy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ihx ihy










end Formalism.CohomologicalDescent.RealLocalDeltaNabla
end
end
