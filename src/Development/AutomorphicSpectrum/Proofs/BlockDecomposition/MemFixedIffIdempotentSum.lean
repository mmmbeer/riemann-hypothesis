import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.FrobFixed

open Polynomial in

theorem sum_one_sub_pow {l : ℕ} [Fact l.Prime] [NeZero l] :
    ∑ c : ZMod l, (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) = 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by
    have := hl.two_le
    omega
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun a _ => ?_) ?_
  · have key : ∀ c : ZMod l, (1 - (a - c) ^ (l - 1) : ZMod l) = if a = c then 1 else 0 := fun c => by
      split_ifs with h
      · rw [h, sub_self, zero_pow hl1, sub_zero]
      · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.2 h), sub_self]
    simp only [eval_sub, eval_finset_sum, eval_one, eval_pow, eval_X, eval_C, key]
    simp
  · have hdeg : ∀ c : ZMod l, natDegree (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) ≤ l - 1 := fun c => by
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      refine natDegree_pow_le.trans ?_
      rw [natDegree_X_sub_C, mul_one]
    have h1 : natDegree (∑ c : ZMod l, (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) - 1) ≤ l - 1 := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      exact natDegree_sum_le_of_forall_le _ _ fun c _ => hdeg c
    rw [Finset.card_univ, ZMod.card]
    have := hl.two_le
    omega

theorem exists_idempotents {R : Type*} [CommRing R] {l : ℕ} [Fact l.Prime] [NeZero l]
    (hR : (l : R) = 0) (x : R) (hx : x ^ l = x) :
    ∃ e : ZMod l → R, CompleteOrthogonalIdempotents e ∧ ∀ c, e c * (x - (c.val : R)) = 0 := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, ⟨⟨fun _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by
    have := hl.two_le
    omega
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hl).2 hR
  letI : Algebra (ZMod l) R := ZMod.algebra R l
  have hφ : ∀ c : ZMod l, (c.val : R) = algebraMap (ZMod l) R c := fun c => by
    rw [← map_natCast (algebraMap (ZMod l) R), ZMod.natCast_zmod_val]
  have hpow : ∀ c : ZMod l, (x - algebraMap (ZMod l) R c) ^ l = x - algebraMap (ZMod l) R c := fun c => by
    rw [sub_pow_char, hx, ← map_pow, ZMod.pow_card]
  obtain ⟨e, he⟩ : ∃ e : ZMod l → R, ∀ c, e c = 1 - (x - algebraMap (ZMod l) R c) ^ (l - 1) := ⟨_, fun _ => rfl⟩
  have hann : ∀ c, e c * (x - algebraMap (ZMod l) R c) = 0 := fun c => by
    have h1 : (x - algebraMap (ZMod l) R c) ^ (l - 1) * (x - algebraMap (ZMod l) R c)
        = x - algebraMap (ZMod l) R c := by
      rw [← pow_succ, Nat.sub_add_cancel hl.one_le, hpow]
    rw [he, sub_mul, one_mul, h1, sub_self]
  have hlin : ∀ c d, e c * (x - algebraMap (ZMod l) R d) = e c * algebraMap (ZMod l) R (c - d) := fun c d => by
    have h1 : x - algebraMap (ZMod l) R d
        = (x - algebraMap (ZMod l) R c) + algebraMap (ZMod l) R (c - d) := by
      rw [map_sub]; ring
    rw [h1, mul_add, hann, zero_add]
  have hmul : ∀ c d k, e c * (x - algebraMap (ZMod l) R d) ^ k
      = e c * algebraMap (ZMod l) R ((c - d) ^ k) := fun c d k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_right_comm, hlin, mul_assoc, ← map_mul, pow_succ']
  refine ⟨e, ⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩, fun c => by rw [hφ, hann]⟩
  · change e c * e c = e c
    have h1 : e c * e c = e c * (1 - (x - algebraMap (ZMod l) R c) ^ (l - 1)) := congrArg (e c * ·) (he c)
    rw [h1, mul_sub, mul_one, hmul, sub_self, zero_pow hl1, map_zero, mul_zero, sub_zero]
  · change e c * e d = 0
    rw [he d, mul_sub, mul_one, hmul, ZMod.pow_card_sub_one_eq_one (sub_ne_zero.2 hcd), map_one, mul_one,
      sub_self]
  · have h1 := congrArg (Polynomial.aeval x) (sum_one_sub_pow (l := l))
    simp only [map_sum, map_sub, map_one, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun c _ => he c

theorem fix_one : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (x : A.A), x ^ l = x → ∃ e : ZMod l → A.A, (haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e ∧ ∀ c, e c * (x - (c.val : A.A)) = 0) := by
  intro l _ A x hx
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact exists_idempotents A.natCast_l x hx

end GlobalTheory.CompanionTheory.FrobFixed
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.FixW

section Idem

variable {R I J : Type} [CommRing R] [Fintype I] [Fintype J]

theorem coi_prod {f : I → R} {g : J → R} (hf : CompleteOrthogonalIdempotents f)
    (hg : CompleteOrthogonalIdempotents g) :
    CompleteOrthogonalIdempotents fun p : I × J => f p.1 * g p.2 := by
  refine ⟨⟨fun p => (hf.idem p.1).mul (hg.idem p.2), ?_⟩, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    by_cases hi : i = i'
    · subst hi
      have hj : j ≠ j' := fun hj => h (by rw [hj])
      change f i * g j * (f i * g j') = 0
      rw [mul_mul_mul_comm, hg.ortho hj, mul_zero]
    · change f i * g j * (f i' * g j') = 0
      rw [mul_mul_mul_comm, hf.ortho hi, zero_mul]
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hg.complete, mul_one]
    exact hf.complete

theorem coi_push [DecidableEq J] {e : I → R} (he : CompleteOrthogonalIdempotents e) (v : I → J) :
    CompleteOrthogonalIdempotents fun c => ∑ i with v i = c, e i := by
  refine ⟨⟨fun c => he.1.isIdempotentElem_sum, fun c c' h => ?_⟩, ?_⟩
  · change (∑ i with v i = c, e i) * (∑ i with v i = c', e i) = 0
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => he.ortho ?_
    rintro rfl
    exact h ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
  · rw [Finset.sum_fiberwise]
    exact he.complete

end Idem

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

local notation "τ" => WittVector.teichmuller l

theorem phiW_teichmuller {a : A.A} (h : IsIdempotentElem a) : A.phiW (τ a) = τ a := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : l.Prime).ne_zero
  have h2 : a ^ (k + 1) = a := h.pow_succ_eq k
  rw [show k + 1 = l from hk.symm] at h2
  have : A.frob a = a := h2
  rw [phiW, WittVector.map_teichmuller, this]

theorem sum_teichmuller {I : Type} [Fintype I] {e : I → A.A}
    (he : CompleteOrthogonalIdempotents e) : ∑ i, τ (e i) = 1 := by
  have ho : OrthogonalIdempotents fun i => τ (e i) :=
    ⟨fun i => by
      change τ (e i) * τ (e i) = τ (e i)
      rw [← map_mul, (he.idem i).eq], fun i j hij => by
      change τ (e i) * τ (e j) = 0
      rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero]⟩
  have hu : IsIdempotentElem (1 - ∑ i, τ (e i)) := ho.isIdempotentElem_sum.one_sub
  have h0 : (1 - ∑ i, τ (e i)) ∈ Ideal.span {(l : A.W)} := by
    rw [A.mem_span_l_iff, ← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  have hz : (1 - ∑ i, τ (e i)) = 0 :=
    IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : A.W)}) A.W) _ fun k => by
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      rcases k with _ | k
      · simp
      · rw [← hu.pow_succ_eq k]
        exact Ideal.pow_mem_pow h0 _
  exact (sub_eq_zero.1 hz).symm

theorem teichmuller_push {I J : Type} [Fintype I] [DecidableEq J] {e : I → A.A}
    (he : CompleteOrthogonalIdempotents e) (v : I → J) (c : J) :
    τ (∑ i with v i = c, e i) = ∑ i with v i = c, τ (e i) := by
  calc τ (∑ i with v i = c, e i) = τ (∑ i with v i = c, e i) * ∑ i, τ (e i) := by
        rw [sum_teichmuller A he, mul_one]
    _ = ∑ i, τ ((∑ j with v j = c, e j) * e i) := by
        rw [Finset.mul_sum]
        simp only [map_mul]
    _ = ∑ i, if v i = c then τ (e i) else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm]
        split_ifs with h
        · rw [he.1.mul_sum_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)]
        · rw [he.1.mul_sum_of_notMem (fun hi => h (Finset.mem_filter.1 hi).2),
            WittVector.teichmuller_zero]
    _ = ∑ i with v i = c, τ (e i) := (Finset.sum_filter _ _).symm

theorem natCast_val_eq (n m : ℕ) [NeZero (l ^ n)] :
    ((((m : ZMod (l ^ n)).val : ℕ)) : A.Wn n) = (m : A.Wn n) := by
  have h0 : ((l ^ n : ℕ) : A.Wn n) = 0 := by
    have : ((l ^ n : ℕ) : A.Wn n) = Ideal.Quotient.mk _ ((l : A.W) ^ n) := by
      rw [Nat.cast_pow, map_pow, map_natCast]
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div m (l ^ n)]
  rw [Nat.cast_add, Nat.cast_mul, h0, zero_mul, add_zero]

theorem exists_idemSum (n : ℕ) {I : Type} [Fintype I] (v : I → ℕ) (e : I → A.A)
    (he : CompleteOrthogonalIdempotents e) :
    ∃ e' : ZMod (l ^ n) → A.A,
      (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
       CompleteOrthogonalIdempotents e') ∧
      Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n}) (∑ i, (v i : A.W) * τ (e i)) =
        A.idemSum n e' := by
  classical
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨fun c => ∑ i with ((v i : ℕ) : ZMod (l ^ n)) = c, e i, coi_push he _, ?_⟩
  rw [idemSum]
  simp only [teichmuller_push A he, map_sum, map_mul, map_natCast]
  have key : ∀ c : ZMod (l ^ n), ((c.val : ℕ) : A.Wn n) *
      ∑ i with ((v i : ℕ) : ZMod (l ^ n)) = c, Ideal.Quotient.mk _ (τ (e i)) =
      ∑ i with ((v i : ℕ) : ZMod (l ^ n)) = c, (v i : A.Wn n) * Ideal.Quotient.mk _ (τ (e i)) := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← (Finset.mem_filter.1 hi).2, natCast_val_eq]
  simp only [key]
  rw [Finset.sum_fiberwise]

theorem exists_rep (n : ℕ) : ∀ y : A.W, A.phiW y - y ∈ Ideal.span {(l : A.W) ^ n} →
    ∃ (I : Type) (_ : Fintype I) (v : I → ℕ) (e : I → A.A), CompleteOrthogonalIdempotents e ∧
      y - ∑ i, (v i : A.W) * τ (e i) ∈ Ideal.span {(l : A.W) ^ n} := by
  induction n with
  | zero =>
    intro y _
    refine ⟨Unit, inferInstance, fun _ => 0, fun _ => 1,
      CompleteOrthogonalIdempotents.unique_iff.2 rfl, ?_⟩
    simp
  | succ n ih =>
    intro y hy
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    have hl : Ideal.span {(l : A.W) ^ (n + 1)} ≤ Ideal.span {(l : A.W)} :=
      Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ n.succ_ne_zero)
    have h0 : y.coeff 0 ^ l = y.coeff 0 := by
      have := (A.mem_span_l_iff _).1 (hl hy)
      rw [← WittVector.constantCoeff_apply, map_sub, sub_eq_zero, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, phiW, WittVector.map_coeff] at this
      exact this
    obtain ⟨f, hf, hfc⟩ := GlobalTheory.CompanionTheory.FrobFixed.fix_one A _ h0
    have hTφ : A.phiW (∑ c : ZMod l, (c.val : A.W) * τ (f c)) =
        ∑ c : ZMod l, (c.val : A.W) * τ (f c) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, map_natCast, phiW_teichmuller A (hf.idem c)]
    have hT0 : (y - ∑ c : ZMod l, (c.val : A.W) * τ (f c)).coeff 0 = 0 := by
      rw [← WittVector.constantCoeff_apply, map_sub, map_sum]
      simp only [map_mul, map_natCast, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero]
      rw [sub_eq_zero]
      have hs : y.coeff 0 = ∑ c, f c * y.coeff 0 := by
        rw [← Finset.sum_mul, hf.complete, one_mul]
      rw [hs]
      refine Finset.sum_congr rfl fun c _ => ?_
      have := hfc c
      linear_combination this
    generalize hT : ∑ c : ZMod l, (c.val : A.W) * τ (f c) = T at hTφ hT0
    obtain ⟨y1, hy1⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hT0)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hy
    have e1 : y = T + y1 * l := by rw [hy1]; ring
    have e3 : A.phiW y = T + A.phiW y1 * l := by
      rw [e1, map_add, map_mul, map_natCast, hTφ]
    have e2 : (l : A.W) * (A.phiW y1 - y1 - d * (l : A.W) ^ n) = 0 := by
      linear_combination -hd - e3 + e1
    have hφ : A.phiW y1 - y1 ∈ Ideal.span {(l : A.W) ^ n} :=
      Ideal.mem_span_singleton'.2 ⟨d, (sub_eq_zero.1 (A.l_mul_eq_zero e2)).symm⟩
    obtain ⟨I, _, v, e, he, hm⟩ := ih y1 hφ
    obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton'.1 hm
    have hS : ∑ p : ZMod l × I, (((p.1.val + l * v p.2 : ℕ)) : A.W) * τ (f p.1 * e p.2) =
        T + (l : A.W) * ∑ i, (v i : A.W) * τ (e i) := by
      rw [Fintype.sum_prod_type]
      calc ∑ c : ZMod l, ∑ i, (((c.val + l * v i : ℕ)) : A.W) * τ (f c * e i)
          = ∑ c : ZMod l, ∑ i, (((c.val : A.W) * τ (f c)) * τ (e i) +
              τ (f c) * ((l : A.W) * ((v i : A.W) * τ (e i)))) := by
            refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul]
            push_cast
            ring
        _ = (∑ c : ZMod l, (c.val : A.W) * τ (f c)) * (∑ i, τ (e i)) +
              (∑ c, τ (f c)) * ((l : A.W) * ∑ i, (v i : A.W) * τ (e i)) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        _ = T + (l : A.W) * ∑ i, (v i : A.W) * τ (e i) := by
            rw [sum_teichmuller A he, sum_teichmuller A hf, hT, mul_one, one_mul]
    refine ⟨ZMod l × I, inferInstance, fun p => p.1.val + l * v p.2, fun p => f p.1 * e p.2,
      coi_prod hf he, ?_⟩
    beta_reduce
    rw [hS]
    refine Ideal.mem_span_singleton'.2 ⟨d', ?_⟩
    linear_combination (l : A.W) * hd' + hy1

end GlobalTheory.CompanionTheory.FixW
end
end
