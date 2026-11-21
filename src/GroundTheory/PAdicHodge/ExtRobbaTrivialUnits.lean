import Mathlib
import GroundTheory.PAdicHodge.SlopeFiltration
import GroundTheory.PAdicHodge.ExtRobbaEigen
import GroundTheory.PAdicHodge.ExtRobbaOrd
import GroundTheory.PAdicHodge.DMTeichPow
import GroundTheory.PAdicHodge.DMTeichBasic
import GroundTheory.PAdicHodge.ExtRobbaRoot
import GroundTheory.PAdicHodge.ToUntiltFieldEqZeroIff
import GroundTheory.PAdicHodge.ExtRobbaGamma
import GroundTheory.PAdicHodge.ExtRobbaFrob
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.ExtRobbaNewton

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob) [CompleteSpace L]

def πEdag (T : TeichLift p L Γ) : T.Edag :=
  ⟨algebraMap Γ T.B T.π, T.Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩
    (T.algebraMap_π_mem_Econ _)⟩

theorem edagToTilde_πEdag : T.edagToTilde (πEdag T) = T.πTilde := rfl

theorem ordB_algebraMap_π_pow_mul (m : ℕ) {c : T.B} (hc : c ≠ 0) :
    T.ordB (algebraMap Γ T.B T.π ^ m * c) = m + T.ordB c := by
  have h1 : algebraMap Γ T.B T.π ^ m = ((T.piB ^ (m : ℤ) : T.Bˣ) : T.B) * algebraMap Γ T.B 1 := by
    rw [map_one, mul_one, zpow_natCast, Units.val_pow_eq_pow_val, piB_val]
  have h1' : T.ordB (algebraMap Γ T.B T.π ^ m) = m := by
    rw [h1]; exact T.ordB_piB_zpow_mul _ (by rw [map_one]; exact one_ne_zero)
  have hne : algebraMap Γ T.B T.π ^ m ≠ 0 := by
    have := T.nontrivial_B
    exact ((IsLocalization.Away.algebraMap_isUnit T.π).pow m).ne_zero
  rw [T.ordB_mul hne hc, h1']

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem ptRad_ptElt {c : L} (hc : ‖c‖ ≤ 1) : T.ptRad (T.ptElt hc) = ‖c‖ := by
  show ‖T.coeff (T.ptElt hc : Γ) 0‖ = ‖c‖
  rw [coeff_zero, coe_ptElt, map_sub, red_π, red_teich, zero_sub, norm_neg]

theorem ptPi_ptElt {c : L} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    T.ptPi (T.isPrimOne_ptElt hc0 hc1) = T.ptSharp (T.isPrimOne_ptElt hc0 hc1) c := by
  set hξ := T.isPrimOne_ptElt hc0 hc1
  have h0 := T.ptE_ξ hξ
  rw [coe_ptElt, sub_eq_add_neg, T.ptE_add hξ (T.convergesAt_π _)
    (T.convergesAt_zcoeff_neg (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ) (T.convergesAt_teich c _)),
    T.ptE_neg hξ (T.convergesAt_teich c _), ptE_π, ptE_teich] at h0
  exact add_neg_eq_zero.1 h0

theorem convergesAt_of_norm_le_seq {a a' : ℤ → L} {ρ : ℝ} (ha : ConvergesAt a ρ)
    (h : ∀ n, ‖a' n‖ ≤ ‖a n‖) (hρ : 0 < ρ) : ConvergesAt a' ρ := by
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) ha
  exact mul_le_mul_of_nonneg_right (h n) (zpow_pos hρ n).le

variable [IsAlgClosed L] {ρ0 : Set.Ioo (0 : ℝ) 1}

theorem exists_start_point {x : T.RobbaExt ρ0} (hx : x ≠ 0) {r : ℝ} (h : 0 < r ∧ r < ρ0)
    (hm : 1 ≤ T.mult x r) :
    ∃ (c : L) (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) (hrad : T.ptRad (T.ptElt hc1.le) = r),
      ‖T.ptEval (T.isPrimOne_ptElt hc0 hc1) (hrad.trans_le h.2.le) x‖ <
        T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x := by
  classical
  set rr : Set.Ioc (0 : ℝ) ρ0 := ⟨r, h.1, h.2.le⟩
  set b := T.approx hx h
  have hb : T.extNorm ρ0 rr (x - b) < T.extNorm ρ0 rr x :=
    T.approx_spec hx h rr le_rfl (mid_rad h).2.2.le
  set N := T.extNorm ρ0 rr x with hNdef
  have hNpos : 0 < N := T.extNorm_pos hx rr
  set a : ℤ → L := T.coeffB b with hadef
  have ha : ConvergesAt a r := T.convergesAt_rad ρ0 b rr
  have hgn : Laurent.gaussNorm a r = N := by
    have e1 := T.extNorm_eq_of_lt hb
    rw [extNorm_coe] at e1
    exact e1
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0] at hgn; simp [Laurent.gaussNorm] at hgn; linarith
  set lo := lowIndex a r
  set hi := highIndex a r
  have hlo := T.lowIdx_eq_approx hx h
  have hhi := T.highIdx_eq_approx hx h
  have hmult : T.mult x r = hi - lo := by rw [mult, hlo, hhi]
  have hwlo : ‖a lo‖ * r ^ lo = N := by
    have := lowIndex_mem h.1 ha ha0; simp only [domSet, Set.mem_setOf_eq] at this; rw [this, hgn]
  have hwhi : ‖a hi‖ * r ^ hi = N := by
    have := highIndex_mem h.1 ha ha0; simp only [domSet, Set.mem_setOf_eq] at this; rw [this, hgn]
  have hwle : ∀ n, ‖a n‖ * r ^ n ≤ N := fun n => hgn ▸ ha.le_gaussNorm n
  set m : ℕ := (hi - lo).toNat
  have hm' : (m : ℤ) = hi - lo := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m := by omega
  have hhi' : hi = lo + m := by omega

  set P : Polynomial L := ∑ i ∈ Finset.range (m + 1), Polynomial.C (a (lo + i)) * Polynomial.X ^ i
    with hPdef
  have hcoeff : ∀ k, P.coeff k = if k < m + 1 then a (lo + k) else 0 := fun k => by
    rw [hPdef, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range (m + 1)) k (fun i => a (lo + i))]
    simp [Finset.mem_range]
  have hlo0 : a lo ≠ 0 := by
    intro h0; rw [h0, norm_zero, zero_mul] at hwlo; exact hNpos.ne hwlo
  have hhi0 : a hi ≠ 0 := by
    intro h0; rw [h0, norm_zero, zero_mul] at hwhi; exact hNpos.ne hwhi
  have hdeg : P.natDegree = m := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_
      (by rw [hcoeff, if_pos (by omega), ← hhi']; exact hhi0)
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi' => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := Finset.mem_range.1 hi'; omega
  have hP0 : P.coeff 0 ≠ 0 := by rw [hcoeff, if_pos (by omega)]; simpa using hlo0
  obtain ⟨c, hroot, hcj⟩ := exists_isRoot_forall_norm_pow_mul_le (by omega : 0 < P.natDegree) hP0
  have hcoeff0 : P.coeff 0 = a lo := by rw [hcoeff, if_pos (by omega)]; simp
  have hrel : ‖a lo‖ = ‖a hi‖ * r ^ m := by
    have e1 : r ^ hi = r ^ lo * r ^ m := by
      rw [hhi', zpow_add₀ h.1.ne', zpow_natCast]
    have := hwlo.trans hwhi.symm
    rw [e1] at this
    have hlp := zpow_pos h.1 lo
    field_simp at this
    nlinarith [this]

  have hcle : ‖c‖ ≤ r := by
    have := hcj m
    rw [hcoeff, if_pos (by omega), ← hhi', hcoeff0, hrel] at this
    have hn : 0 < ‖a hi‖ := norm_pos_iff.2 hhi0
    have : ‖c‖ ^ m ≤ r ^ m := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h.1.le (by omega)).1 this
  have hcge : r ≤ ‖c‖ := by
    by_contra hlt
    push_neg at hlt
    have hbound : ∀ i ∈ Finset.range m, ‖a (lo + (i + 1)) * c ^ (i + 1)‖ < ‖a lo‖ := by
      intro i _
      rw [norm_mul, norm_pow]
      have hw := hwle (lo + (i + 1))
      rw [← hwlo, zpow_add₀ h.1.ne'] at hw
      have hz : r ^ ((i : ℤ) + 1) = r ^ (i + 1) := by rw [← zpow_natCast]; push_cast; rfl
      rw [hz] at hw
      have hlp := zpow_pos h.1 lo
      have h1 : ‖a (lo + (i + 1))‖ * r ^ (i + 1) ≤ ‖a lo‖ := by
        have : (‖a (lo + (i + 1))‖ * r ^ (i + 1)) * r ^ lo ≤ ‖a lo‖ * r ^ lo := by nlinarith
        exact le_of_mul_le_mul_right this hlp
      have hcpow : ‖c‖ ^ (i + 1) < r ^ (i + 1) :=
        pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega)
      rcases (norm_nonneg (a (lo + (i + 1)))).lt_or_eq with hpos | heq
      · calc ‖a (lo + (i + 1))‖ * ‖c‖ ^ (i + 1) < ‖a (lo + (i + 1))‖ * r ^ (i + 1) :=
              mul_lt_mul_of_pos_left hcpow hpos
          _ ≤ ‖a lo‖ := h1
      · rw [← heq, zero_mul]; exact norm_pos_iff.2 hlo0
    obtain ⟨i0, hi0mem, hi0max⟩ := (Finset.range m).exists_max_image
      (fun i => ‖a (lo + (i + 1)) * c ^ (i + 1)‖) ⟨0, Finset.mem_range.2 (by omega)⟩
    have hrest : ‖∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1)‖ < ‖a lo‖ :=
      (norm_finset_sum_le_ultra _ _ (norm_nonneg _) fun i hi' => hi0max i hi').trans_lt
        (hbound i0 hi0mem)
    have hPc : P.eval c = a lo + ∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1) := by
      rw [hPdef, Polynomial.eval_finset_sum, Finset.sum_range_succ']
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        pow_zero, mul_one, Nat.cast_zero, add_zero]
      push_cast
      ring
    have : P.eval c ≠ 0 := by
      rw [hPc]
      intro h0
      have := ultra_norm_sub_eq_left (a := a lo)
        (b := -∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1)) (by rw [norm_neg]; exact hrest)
      rw [sub_neg_eq_add, h0, norm_zero] at this
      exact hlo0 (norm_eq_zero.1 this.symm)
    exact this hroot
  have hcr : ‖c‖ = r := le_antisymm hcle hcge
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hcr; exact h.1.ne hcr
  have hc1 : ‖c‖ < 1 := hcr ▸ (h.2.trans ρ0.2.2)
  have hrad : T.ptRad (T.ptElt hc1.le) = r := (T.ptRad_ptElt hc1.le).trans hcr
  refine ⟨c, hc0, hc1, hrad, ?_⟩
  set hξ0 := T.isPrimOne_ptElt hc0 hc1
  set hr0 := hrad.trans_le h.2.le
  have hIoc : T.ptRadIoc hξ0 hr0 = rr := Subtype.ext hrad
  have har : ConvergesAt a (T.ptRad (T.ptElt hc1.le)) := by rw [hrad]; exact ha
  have hvb : T.ptEval hξ0 hr0 ((b : T.Econ ρ0) : T.RobbaExt ρ0) = T.ptEvalSeq hξ0 a := by
    rw [ptEval_coe]; rfl
  have hterm : ∀ n, T.ptTerm hξ0 a n = T.ptSharp hξ0 (c ^ n * a n) := by
    intro n; rw [ptTerm, T.ptPi_ptElt hc0 hc1, map_mul, map_zpow₀]
  set S : Finset ℤ := (Finset.range (m + 1)).image (fun i : ℕ => lo + i)
  have hSmem : ∀ n, n ∈ S ↔ lo ≤ n ∧ n ≤ hi := by
    intro n
    simp only [S, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi', rfl⟩; omega
    · rintro ⟨h1, h2⟩; exact ⟨(n - lo).toNat, by omega, by omega⟩
  set ablock : ℤ → L := fun n => if n ∈ S then a n else 0
  set arest : ℤ → L := fun n => if n ∈ S then 0 else a n
  have hcb : ConvergesAt ablock (T.ptRad (T.ptElt hc1.le)) :=
    convergesAt_of_norm_le_seq har (fun n => by simp only [ablock]; split_ifs <;> simp)
      (T.ptRad_pos' hξ0)
  have hcr' : ConvergesAt arest (T.ptRad (T.ptElt hc1.le)) :=
    convergesAt_of_norm_le_seq har (fun n => by simp only [arest]; split_ifs <;> simp)
      (T.ptRad_pos' hξ0)
  have hsplit : T.ptEvalSeq hξ0 a = T.ptEvalSeq hξ0 ablock + T.ptEvalSeq hξ0 arest := by
    rw [ptEvalSeq, ptEvalSeq, ptEvalSeq, ← (T.summable_ptTerm hξ0 hcb).tsum_add
      (T.summable_ptTerm hξ0 hcr')]
    congr 1
    funext n
    simp only [ptTerm, ablock, arest]
    split_ifs <;> simp
  have hblock : T.ptEvalSeq hξ0 ablock =
      ∑ i ∈ Finset.range (m + 1), T.ptSharp hξ0 (c ^ (lo + i) * a (lo + i)) := by
    rw [ptEvalSeq, tsum_eq_sum (s := S) (fun n hn => by simp [ptTerm, ablock, hn]),
      Finset.sum_image (fun i _ j _ hij => by simpa using hij)]
    refine Finset.sum_congr rfl fun i hi' => ?_
    have hin : lo + (i : ℤ) ∈ S := Finset.mem_image_of_mem _ hi'
    simp only [ptTerm, ablock, if_pos hin, T.ptPi_ptElt hc0 hc1, map_mul, map_zpow₀]
  have hsum0 : ∑ i ∈ Finset.range (m + 1), c ^ (lo + i) * a (lo + i) = 0 := by
    have hev : P.eval c = ∑ i ∈ Finset.range (m + 1), a (lo + i) * c ^ i := by
      rw [hPdef, Polynomial.eval_finset_sum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have : ∑ i ∈ Finset.range (m + 1), c ^ (lo + i) * a (lo + i) = c ^ lo * P.eval c := by
      rw [hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zpow_add₀ hc0, zpow_natCast]; ring
    rw [this, hroot.eq_zero, mul_zero]
  have hA : ‖T.ptEvalSeq hξ0 ablock‖ ≤ r * N := by
    rw [hblock]
    have := T.norm_sum_sharp_sub_le hξ0 (Finset.range (m + 1))
      (fun i => c ^ (lo + i) * a (lo + i)) hNpos.le fun i _ => by
        rw [norm_mul, norm_zpow, hcr, mul_comm]; exact hwle _
    rwa [hsum0, map_zero, sub_zero, hrad] at this
  have hB : ‖T.ptEvalSeq hξ0 arest‖ < N := by
    refine (T.norm_ptEvalSeq_le hξ0 hcr').trans_lt ?_
    rw [hrad]
    by_cases h0 : arest = 0
    · rw [h0]; simp [Laurent.gaussNorm]; exact hNpos
    have hcr'' : ConvergesAt arest r := hrad ▸ hcr'
    have hmem := lowIndex_mem h.1 hcr'' h0
    have hne := ne_zero_of_mem_domSet h.1 hcr'' h0 hmem
    simp only [domSet, Set.mem_setOf_eq] at hmem
    rw [← hmem]
    set n1 := lowIndex arest r
    have hn1S : n1 ∉ S := by
      intro hS; apply hne; simp [arest, hS]
    have hn1 : arest n1 = a n1 := by simp [arest, hn1S]
    rw [hn1, ← hgn]
    rw [hSmem] at hn1S
    rcases (not_and_or.1 hn1S) with h1 | h1
    · exact weight_lt_of_lt_lowIndex h.1 ha ha0 (by omega)
    · exact weight_lt_of_highIndex_lt h.1 ha ha0 (by omega)
  have hbval : ‖T.ptEval hξ0 hr0 ((b : T.Econ ρ0) : T.RobbaExt ρ0)‖ < N := by
    rw [hvb, hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hB)
    exact hA.trans_lt (by nlinarith [h.2.trans ρ0.2.2])
  have hxb : ‖T.ptEval hξ0 hr0 (x - ((b : T.Econ ρ0) : T.RobbaExt ρ0))‖ < N := by
    refine (T.norm_ptEval_le hξ0 hr0 _).trans_lt ?_
    rw [hIoc]; exact hb
  have e : x = ((b : T.Econ ρ0) : T.RobbaExt ρ0) + (x - ((b : T.Econ ρ0) : T.RobbaExt ρ0)) := by ring
  rw [e, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hbval hxb)

section Iterate

variable [IsAlgClosed L] {ρ0 : Set.Ioo (0 : ℝ) 1} {x : T.RobbaExt ρ0} {r : ℝ}

omit [IsAlgClosed L] in
theorem movePt_zero {ξ : T.int} (hξ : T.IsPrimOne ξ) (h0 : ‖(0 : L)‖ < T.ptRad ξ) :
    (T.movePt hξ h0 : Γ) = ξ := by
  rw [coe_movePt, T.teich_zero, sub_zero]

structure GoodPt (x : T.RobbaExt ρ0) (r : ℝ) (h : 0 < r ∧ r < ρ0) where

  η : T.int
  hη : T.IsPrimOne η
  hrad : T.ptRad η = r
  hlt : ‖T.ptEval hη (hrad.trans_le h.2.le) x‖ < T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x

variable (h : 0 < r ∧ r < ρ0)

theorem exists_next (hx : x ≠ 0) (hm : 1 ≤ T.mult x r) (P : T.GoodPt x r h) :
    ∃ (s : L) (P' : T.GoodPt x r h), (P'.η : Γ) = P.η - T.teich s ∧ ‖s‖ < r ∧
      (∃ J : ℕ, 1 ≤ J ∧ (J : ℤ) ≤ T.mult x r ∧
        (‖s‖ / r) ^ J ≤ ‖T.ptEval P.hη (P.hrad.trans_le h.2.le) x‖ /
          T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x) ∧
      ‖T.ptEval P'.hη (P'.hrad.trans_le h.2.le) x‖ ≤
        ‖T.ptEval P.hη (P.hrad.trans_le h.2.le) x‖ * max r (‖s‖ / r) := by
  obtain ⟨η, hη, hrad, hlt⟩ := P
  subst hrad
  have hNpos : 0 < T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x := T.extNorm_pos hx _
  by_cases hε : T.ptEval hη h.2.le x = 0
  ·
    have h0 : ‖(0 : L)‖ < T.ptRad η := by rw [norm_zero]; exact T.ptRad_pos' hη
    have hη' := T.isPrimOne_movePt hη h0
    have hrad' : T.ptRad (T.movePt hη h0) = T.ptRad η := T.ptRad_movePt hη h0
    obtain ⟨y, hy⟩ := (T.ptEval_eq_zero_iff hη h.2.le x).1 hε
    have hval : T.ptEval hη' (hrad'.trans_le h.2.le) x = 0 := by
      rw [hy, map_mul, T.ptEval_ξExt_movePt hη h0, map_zero, zero_mul]
    have hJpart : ∃ J : ℕ, 1 ≤ J ∧ (J : ℤ) ≤ T.mult x (T.ptRad η) ∧
        (‖(0 : L)‖ / T.ptRad η) ^ J ≤ ‖T.ptEval hη h.2.le x‖ /
          T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x := by
      refine ⟨1, le_rfl, hm, ?_⟩
      rw [norm_zero, zero_div, zero_pow one_ne_zero]
      exact div_nonneg (norm_nonneg _) hNpos.le
    have hlt' : ‖T.ptEval hη' (hrad'.trans_le h.2.le) x‖ < T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x := by
      rw [hval, norm_zero]; exact hNpos
    have hle' : ‖T.ptEval hη' (hrad'.trans_le h.2.le) x‖ ≤
        ‖T.ptEval hη h.2.le x‖ * max (T.ptRad η) (‖(0 : L)‖ / T.ptRad η) := by
      rw [hval, norm_zero]
      exact mul_nonneg (norm_nonneg _) (le_max_of_le_left h.1.le)
    refine ⟨0, ⟨T.movePt hη h0, hη', hrad', hlt'⟩, ?_, by rw [norm_zero]; exact h.1, hJpart, hle'⟩
    show (T.movePt hη h0 : Γ) = η - T.teich 0
    rw [coe_movePt]
  · have hεN : ‖T.ptEval hη h.2.le x‖ < T.extNorm ρ0 (T.ptRadIoc hη h.2.le) x := hlt
    obtain ⟨s, hs, J, hJ1, hJm, hratio, hnew⟩ := T.step_estimate hη h.2 hx hε hεN
    have hrad' : T.ptRad (T.movePt hη hs) = T.ptRad η := T.ptRad_movePt hη hs
    have hfac : max (T.ptRad η) (‖s‖ / T.ptRad η) < 1 :=
      max_lt (h.2.trans ρ0.2.2) ((div_lt_one h.1).2 hs)
    have hεpos : 0 < ‖T.ptEval hη h.2.le x‖ := norm_pos_iff.2 hε
    refine ⟨s, ⟨T.movePt hη hs, T.isPrimOne_movePt hη hs, hrad', ?_⟩, rfl, hs,
      ⟨J, hJ1, hJm, hratio⟩, hnew⟩
    calc ‖T.ptEval (T.isPrimOne_movePt hη hs) (hrad'.trans_le h.2.le) x‖
        ≤ ‖T.ptEval hη h.2.le x‖ * max (T.ptRad η) (‖s‖ / T.ptRad η) := hnew
      _ < ‖T.ptEval hη h.2.le x‖ * 1 := mul_lt_mul_of_pos_left hfac hεpos
      _ = _ := mul_one _
      _ < _ := hlt

end Iterate

section Limit

theorem isPrimOne_sub_of_prefix {ξ : T.int} (hξ : T.IsPrimOne ξ) {Y : T.int} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ < T.ptRad ξ) (hY : T.PrefixLe (Y : Γ) 1 δ) :
    T.IsPrimOne (ξ - Y) ∧ T.ptRad (ξ - Y) = T.ptRad ξ := by
  have hr1 := T.ptRad_lt_one' hξ
  have hδ1 : δ < 1 := hδ.trans hr1
  have hrad : T.ptRad (ξ - Y) = T.ptRad ξ := by
    show ‖T.coeff ((ξ - Y : T.int) : Γ) 0‖ = ‖T.coeff (ξ : Γ) 0‖
    rw [show ((ξ - Y : T.int) : Γ) = (ξ : Γ) - Y from rfl, coeff_zero, coeff_zero, map_sub]
    refine ultra_norm_sub_eq_left ?_
    rw [← coeff_zero]
    exact (hY 0 (Nat.zero_le _)).trans_lt hδ
  refine ⟨⟨?_, ?_, ?_⟩, hrad⟩
  · intro h0
    have := hrad
    rw [ptRad, h0, norm_zero] at this
    exact (T.ptRad_pos' hξ).ne this
  · have := hrad; rw [ptRad] at this; rw [this]; exact hr1
  · have hx : T.PrefixLe (ξ : Γ) 1 1 := fun m _ => T.mem_int_iff.1 ξ.2 m
    have hy : T.PrefixLe (-(Y : Γ)) 1 δ := T.prefixLe_neg hY
    have hh := T.norm_coeff_add_sub_le 1 hδ0 hδ1.le hx hy 1 le_rfl
    rw [Real.one_rpow, one_mul, ← sub_eq_add_neg] at hh
    obtain ⟨ht0, -⟩ := coeffHolderExp_pos_le_one (p := p) 1
    have hlt : δ ^ coeffHolderExp p 1 < 1 := Real.rpow_lt_one hδ0 hδ1 ht0
    have e1 : ‖T.coeff (ξ : Γ) 1‖ = 1 := hξ.norm_coeff_one
    rw [show ((ξ - Y : T.int) : Γ) = (ξ : Γ) - Y from rfl]
    have := ultra_norm_sub_eq_left (a := T.coeff (ξ : Γ) 1)
      (b := T.coeff (ξ : Γ) 1 - T.coeff ((ξ : Γ) - Y) 1) (by
        rw [norm_sub_rev, e1]; exact hh.trans_lt hlt)
    rw [sub_sub_cancel, e1] at this
    exact this

variable [IsAlgClosed L] [CompleteSpace L] {ρ0 : Set.Ioo (0 : ℝ) 1} {x : T.RobbaExt ρ0} {r : ℝ}
  (h : 0 < r ∧ r < ρ0)

theorem exists_zero_of_goodPt (hx : x ≠ 0) (hm : 1 ≤ T.mult x r) (P0 : T.GoodPt x r h) :
    ∃ (η : T.int) (hη : T.IsPrimOne η) (hrad : T.ptRad η = r),
      T.ptEval hη (hrad.trans_le h.2.le) x = 0 := by
  classical
  choose sF PF hrel hsr hJ hdec using T.exists_next h hx hm
  set pts : ℕ → T.GoodPt x r h := fun k => PF^[k] P0 with hpts
  have hpts_succ : ∀ k, pts (k + 1) = PF (pts k) := fun k =>
    Function.iterate_succ_apply' PF k P0
  set s : ℕ → L := fun k => sF (pts k)
  set N := T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x with hNdef
  have hNpos : 0 < N := T.extNorm_pos hx _
  set ε : ℕ → ℝ := fun k => ‖T.ptEval (pts k).hη ((pts k).hrad.trans_le h.2.le) x‖
  have hεnn : ∀ k, 0 ≤ ε k := fun k => norm_nonneg _
  have hεN : ∀ k, ε k < N := fun k => (pts k).hlt
  have hsr' : ∀ k, ‖s k‖ < r := fun k => hsr (pts k)
  have hdec' : ∀ k, ε (k + 1) ≤ ε k * max r (‖s k‖ / r) := fun k => by
    show ‖T.ptEval (pts (k + 1)).hη _ x‖ ≤ _
    have := hdec (pts k)
    rw [← hpts_succ] at this
    exact this
  have hmax : ∀ k, max r (‖s k‖ / r) < 1 := fun k =>
    max_lt (h.2.trans ρ0.2.2) ((div_lt_one h.1).2 (hsr' k))
  have hεmono : ∀ k, ε (k + 1) ≤ ε k := fun k =>
    (hdec' k).trans (mul_le_of_le_one_right (hεnn k) (hmax k).le)
  have hεle0 : ∀ k, ε k ≤ ε 0 := by
    intro k; induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hεmono k).trans ih

  set M : ℕ := (T.mult x r).toNat
  have hM : (M : ℤ) = T.mult x r := Int.toNat_of_nonneg (T.mult_nonneg x r)
  have hM1 : 1 ≤ M := by omega
  set q := ε 0 / N
  have hq0 : 0 ≤ q := div_nonneg (hεnn 0) hNpos.le
  have hq1 : q < 1 := (div_lt_one hNpos).2 (hεN 0)
  obtain ⟨lam0, hl0, hl1, hql⟩ : ∃ l : ℝ, 0 < l ∧ l < 1 ∧ q < l ^ M := by
    set t := q ^ ((M : ℝ)⁻¹) with htdef
    have ht0 : 0 ≤ t := Real.rpow_nonneg hq0 _
    have ht1 : t < 1 := Real.rpow_lt_one hq0 hq1 (inv_pos.2 (by exact_mod_cast hM1))
    refine ⟨(t + 1) / 2, by linarith, by linarith, ?_⟩
    have htM : t ^ M = q := Real.rpow_inv_natCast_pow hq0 (by omega)
    rw [← htM]
    exact pow_lt_pow_left₀ (by linarith) ht0 (by omega)
  have ht_le : ∀ k, ‖s k‖ / r ≤ lam0 := by
    intro k
    by_contra hcon
    push_neg at hcon
    obtain ⟨J, hJ1, hJM, hJr⟩ := hJ (pts k)
    have hJM' : J ≤ M := by omega
    have ht1 : ‖s k‖ / r ≤ 1 := ((div_lt_one h.1).2 (hsr' k)).le
    have h1 : (‖s k‖ / r) ^ M ≤ (‖s k‖ / r) ^ J :=
      pow_le_pow_of_le_one (div_nonneg (norm_nonneg _) h.1.le) ht1 hJM'
    have h2 : lam0 ^ M < (‖s k‖ / r) ^ M := pow_lt_pow_left₀ hcon hl0.le (by omega)
    have h3 : ε k / N ≤ q := div_le_div_of_nonneg_right (hεle0 k) hNpos.le
    have := hJr
    change (‖s k‖ / r) ^ J ≤ ε k / N at this
    linarith
  set lam := max r lam0
  have hlam1 : lam < 1 := max_lt (h.2.trans ρ0.2.2) hl1
  have hlam0 : 0 ≤ lam := le_max_of_le_left h.1.le
  have hεgeom : ∀ k, ε k ≤ lam ^ k * ε 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      calc ε (k + 1) ≤ ε k * max r (‖s k‖ / r) := hdec' k
        _ ≤ ε k * lam := mul_le_mul_of_nonneg_left (max_le_max le_rfl (ht_le k)) (hεnn k)
        _ ≤ lam ^ k * ε 0 * lam := mul_le_mul_of_nonneg_right ih hlam0
        _ = lam ^ (k + 1) * ε 0 := by ring
  set mu := lam ^ ((M : ℝ)⁻¹)
  have hmu0 : 0 ≤ mu := Real.rpow_nonneg hlam0 _
  have hmu1 : mu < 1 := Real.rpow_lt_one hlam0 hlam1 (inv_pos.2 (by exact_mod_cast hM1))
  have hmuM : mu ^ M = lam := Real.rpow_inv_natCast_pow hlam0 (by omega)
  have hs_geom : ∀ k, ‖s k‖ ≤ mu ^ k := by
    intro k
    obtain ⟨J, hJ1, hJM, hJr⟩ := hJ (pts k)
    have hJM' : J ≤ M := by omega
    change (‖s k‖ / r) ^ J ≤ ε k / N at hJr
    have ht1 : ‖s k‖ / r ≤ 1 := ((div_lt_one h.1).2 (hsr' k)).le
    have h1 : (‖s k‖ / r) ^ M ≤ lam ^ k := by
      calc (‖s k‖ / r) ^ M ≤ (‖s k‖ / r) ^ J := pow_le_pow_of_le_one (div_nonneg (norm_nonneg _) h.1.le) ht1 hJM'
        _ ≤ ε k / N := hJr
        _ ≤ lam ^ k * ε 0 / N := div_le_div_of_nonneg_right (hεgeom k) hNpos.le
        _ = lam ^ k * q := by rw [mul_div_assoc]
        _ ≤ lam ^ k * 1 := mul_le_mul_of_nonneg_left hq1.le (pow_nonneg hlam0 k)
        _ = lam ^ k := mul_one _
    have h2 : ‖s k‖ / r ≤ mu ^ k := by
      by_contra hcon
      push_neg at hcon
      have := pow_lt_pow_left₀ hcon (pow_nonneg hmu0 k) (by omega : M ≠ 0)
      rw [← pow_mul, mul_comm, pow_mul, hmuM] at this
      linarith
    calc ‖s k‖ ≤ ‖s k‖ / r := le_div_self (norm_nonneg _) h.1 (h.2.trans ρ0.2.2).le
      _ ≤ mu ^ k := h2

  set S : ℕ → Γ := fun k => ∑ i ∈ Finset.range k, T.teich (s i) with hSdef
  have hs1 : ∀ k, ‖s k‖ ≤ 1 := fun k => ((hsr' k).trans (h.2.trans ρ0.2.2)).le
  have hSint : ∀ k, S k ∈ T.int := fun k =>
    Subring.sum_mem _ fun i _ => T.teich_mem_int (hs1 i)
  have hSsucc : ∀ k, S (k + 1) = S k + T.teich (s k) := fun k => by
    simp only [S, Finset.sum_range_succ]
  have hSpts : ∀ k, ((pts k).η : Γ) = P0.η - S k := by
    intro k
    induction k with
    | zero => simp [S, pts]
    | succ k ih =>
      rw [hpts_succ, hrel (pts k), ih, hSsucc]
      simp only [s]
      ring

  have hstep : ∀ n k, ‖T.coeff (S (k + 1)) n - T.coeff (S k) n‖ ≤
      (mu ^ coeffHolderExp p n) ^ k := by
    intro n k
    have hxp : T.PrefixLe (S k) n 1 := fun m _ => T.mem_int_iff.1 (hSint k) m
    have hyp : T.PrefixLe (T.teich (s k)) n ‖s k‖ := T.prefixLe_teich' (s k) n le_rfl
    have := T.norm_coeff_add_sub_le n (norm_nonneg _) (hs1 k) hxp hyp n le_rfl
    rw [Real.one_rpow, one_mul] at this
    rw [hSsucc]
    refine this.trans ?_
    obtain ⟨ht0, -⟩ := coeffHolderExp_pos_le_one (p := p) n
    calc ‖s k‖ ^ coeffHolderExp p n ≤ (mu ^ k) ^ coeffHolderExp p n :=
          Real.rpow_le_rpow (norm_nonneg _) (hs_geom k) ht0.le
      _ = (mu ^ coeffHolderExp p n) ^ k := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hmu0, ← Real.rpow_mul hmu0,
            mul_comm]
  have hcauchy : ∀ n, CauchySeq (fun k => T.coeff (S k) n) := fun n => by
    obtain ⟨ht0, -⟩ := coeffHolderExp_pos_le_one (p := p) n
    refine cauchySeq_of_le_geometric (mu ^ coeffHolderExp p n) 1
      (Real.rpow_lt_one hmu0 hmu1 ht0) fun k => ?_
    rw [dist_eq_norm, norm_sub_rev, one_mul]
    exact hstep n k
  choose a ha using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  have ha1 : ∀ n, ‖a n‖ ≤ 1 := fun n =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (ha n))
      (Filter.Eventually.of_forall fun k => T.mem_int_iff.1 (hSint k) n)
  set X := T.ofCoeff a with hXdef
  have hXc : ∀ n, T.coeff X n = a n := fun n => by rw [hXdef, coeff_ofCoeff]
  have hXint : X ∈ T.int := T.mem_int_iff.2 fun n => by rw [hXc]; exact ha1 n

  set δ := r * lam0
  have hsδ : ∀ i, ‖s i‖ ≤ δ := fun i => by
    have := ht_le i
    rw [div_le_iff₀ h.1] at this
    show ‖s i‖ ≤ r * lam0
    linarith
  have hδ0 : 0 ≤ δ := mul_nonneg h.1.le hl0.le
  have hSpre : ∀ k, T.PrefixLe (S k) 1 δ := fun k =>
    T.prefixLe_sum _ _ hδ0 fun i _ => T.prefixLe_teich' (s i) 1 (hsδ i)
  have hXpre : T.PrefixLe X 1 δ := fun m hm => by
    rw [hXc]
    exact le_of_tendsto ((continuous_norm.tendsto _).comp (ha m))
      (Filter.Eventually.of_forall fun k => hSpre k m hm)
  have hδr : δ < T.ptRad P0.η := by
    rw [P0.hrad]; show r * lam0 < r; nlinarith [h.1]
  obtain ⟨hξi, hradi'⟩ := T.isPrimOne_sub_of_prefix P0.hη (Y := ⟨X, hXint⟩) hδ0 hδr hXpre
  set ξi : T.int := P0.η - ⟨X, hXint⟩ with hξidef
  have hradi : T.ptRad ξi = r := hradi'.trans P0.hrad
  have hri : T.ptRad ξi ≤ ρ0 := hradi.trans_le h.2.le
  have hIoci : T.ptRadIoc hξi hri = ⟨r, h.1, h.2.le⟩ := Subtype.ext hradi

  have hr1 : r < 1 := h.2.trans ρ0.2.2
  have hDint : ∀ k, X - S k ∈ T.int := fun k => sub_mem hXint (hSint k)
  set G : ℕ → ℝ := fun k => gaussNorm (T.zcoeff (X - S k)) r
  have hG : Tendsto G atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro e he
    set e' := min e 1 / 2 with he'
    have he'0 : 0 < e' := by positivity
    have he'1 : e' < 1 := by
      have := min_le_right e 1; rw [he']; linarith
    have he'e : e' < e := by
      have := min_le_left e 1; rw [he']; linarith
    obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one he'0 hr1
    set tol := e' ^ (p ^ n0 : ℕ)
    have htol0 : 0 < tol := by positivity
    have htol1 : tol ≤ 1 := pow_le_one₀ he'0.le he'1.le
    have htole : tol ^ ((p ^ n0 : ℕ) : ℝ)⁻¹ = e' :=
      Real.pow_rpow_inv_natCast he'0.le (pow_ne_zero _ hp.out.ne_zero)
    have hev : ∀ᶠ k in atTop, ∀ i ∈ Finset.range (n0 + 1), ‖a i - T.coeff (S k) i‖ < tol := by
      refine (Finset.eventually_all _).2 fun i _ => ?_
      have := (ha i).eventually (Metric.ball_mem_nhds (a i) htol0)
      filter_upwards [this] with k hk
      rw [dist_eq_norm, norm_sub_rev] at hk
      exact hk
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
    refine ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (gaussNorm_nonneg h.1)]
    have hpre := T.prefixLe_sub_of_coeff_close (u := X) (v := S k) (n := n0) htol0.le htol1
      (fun i _ => by rw [hXc]; exact ha1 i) (fun i _ => T.mem_int_iff.1 (hSint k) i)
      (fun i hi => by rw [hXc]; exact (hK k hk i (Finset.mem_range.2 (by omega))).le)
    rw [Real.one_rpow, one_mul, htole] at hpre
    refine lt_of_le_of_lt (gaussNorm_le fun n => ?_) he'e
    rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact he'0.le
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [T.zcoeff_natCast, zpow_natCast]
    by_cases hmn : m ≤ n0
    · calc ‖T.coeff (X - S k) m‖ * r ^ m ≤ ‖T.coeff (X - S k) m‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ h.1.le hr1.le) (norm_nonneg _)
        _ ≤ e' := by rw [mul_one]; exact hpre m hmn
    · have hc1 : ‖T.coeff (X - S k) m‖ ≤ 1 := T.mem_int_iff.1 (hDint k) m
      calc ‖T.coeff (X - S k) m‖ * r ^ m ≤ 1 * r ^ m :=
            mul_le_mul_of_nonneg_right hc1 (pow_nonneg h.1.le m)
        _ ≤ r ^ n0 := by rw [one_mul]; exact pow_le_pow_of_le_one h.1.le hr1.le (by omega)
        _ ≤ e' := hn0.le

  have hbound : ∀ k, ‖T.ptEval hξi hri x‖ ≤ max (ε k) (G k * (N / r)) := by
    intro k
    have hrk : T.ptRad (pts k).η ≤ ρ0 := (pts k).hrad.trans_le h.2.le
    set D := T.divStep (pts k).hη hrk x
    have h1 : ‖T.ptEval hξi hri (T.liftExt ρ0 D.z D.hV)‖ ≤ ε k := by
      refine (T.norm_ptEval_le hξi hri _).trans ?_
      rw [T.extNorm_liftExt _ _ D.hred, D.hz]
    have h2 : ‖T.ptEval hξi hri (T.ξExt (pts k).η ρ0)‖ ≤ G k := by
      rw [ξExt, T.ptEval_coe_algebraMap hξi hri]
      have hr0' := T.ptRad_pos' hξi
      have hr1' := T.ptRad_lt_one' hξi
      have hdiff : ((pts k).η : Γ) = (ξi : Γ) + (X - S k) := by
        rw [hSpts k, hξidef]; push_cast; ring
      rw [hdiff, T.ptE_add hξi (T.convergesAt_of_mem_int ξi.2 hr0' hr1')
        (T.convergesAt_of_mem_int (hDint k) hr0' hr1'), T.ptE_ξ hξi, zero_add]
      refine (T.norm_ptE_le hξi (T.convergesAt_of_mem_int (hDint k) hr0' hr1')).trans ?_
      rw [hradi]
    have h3 : ‖T.ptEval hξi hri D.next‖ ≤ N / r := by
      refine (T.norm_ptEval_le hξi hri _).trans ?_
      rw [hIoci]
      have := T.extNorm_next_le (hξ := (pts k).hη) (hr := hrk) x
      have hIock : T.ptRadIoc (pts k).hη hrk = ⟨r, h.1, h.2.le⟩ := Subtype.ext (pts k).hrad
      rw [hIock, (pts k).hrad] at this
      rw [le_div_iff₀ h.1, mul_comm]
      exact this
    have e := D.eq
    rw [e, map_add, map_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h1 ?_)
    rw [norm_mul]
    exact mul_le_mul h2 h3 (norm_nonneg _) (gaussNorm_nonneg h.1)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const (ε 0)
    rw [zero_mul] at this
    exact squeeze_zero hεnn hεgeom this
  have hmaxlim : Tendsto (fun k => max (ε k) (G k * (N / r))) atTop (𝓝 0) := by
    have := hεlim.max (hG.mul_const (N / r))
    rwa [zero_mul, max_self] at this
  have hz : ‖T.ptEval hξi hri x‖ = 0 :=
    le_antisymm (ge_of_tendsto' hmaxlim hbound) (norm_nonneg _)
  exact ⟨ξi, hξi, hradi, norm_eq_zero.1 hz⟩

end Limit

variable [IsAlgClosed L] [CompleteSpace L] in

theorem exists_point_dvd {ρ0 : Set.Ioo (0 : ℝ) 1} {x : T.RobbaExt ρ0} (hx : x ≠ 0) {r : ℝ}
    (hr0 : 0 < r) (hrρ : r < ρ0) (hm : 1 ≤ T.mult x r) :
    ∃ (ξ : T.int) (hξ : T.IsPrimOne ξ), T.ptRad ξ = r ∧ ∃ y, x = T.ξExt ξ ρ0 * y := by
  obtain ⟨c, hc0, hc1, hrad, hlt⟩ := T.exists_start_point hx ⟨hr0, hrρ⟩ hm
  obtain ⟨η, hη, hrad', hval⟩ := T.exists_zero_of_goodPt ⟨hr0, hrρ⟩ hx hm
    ⟨T.ptElt hc1.le, T.isPrimOne_ptElt hc0 hc1, hrad, hlt⟩
  obtain ⟨y, hy⟩ := (T.ptEval_eq_zero_iff hη _ x).1 hval
  exact ⟨η, hη, hrad', y, hy⟩

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} [CompleteSpace L]

theorem exists_adjusted {g y a b : T.RobbaExt ρ0} (hab : a * g + b * y = 1) {s : ℝ} (hs : 0 ≤ s)
    (hg1 : ∀ ρ : Set.Ioc (0 : ℝ) ρ0, s ≤ ρ → T.extNorm ρ0 ρ g = 1)
    (hgW : ∀ ρ : Set.Ioc (0 : ℝ) ρ0, s ≤ ρ → T.extNorm ρ0 ρ (g - 1) ≤ s / ρ)
    (σ : Set.Ioc (0 : ℝ) ρ0) (hσ : 2 * s ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a' b' : T.RobbaExt ρ0, a' * g + b' * y = 1 ∧ ∀ ρ : Set.Ioc (0 : ℝ) ρ0, (σ : ℝ) ≤ ρ →
      T.extNorm ρ0 ρ b' ≤ ε ∧ T.extNorm ρ0 ρ (b' * y) ≤ ε ∧
        T.extNorm ρ0 ρ (a' - 1) ≤ max ε (s / ρ) := by
  set β := max (T.extNorm ρ0 σ b) (T.extNorm ρ0 (topRad ρ0) b)
  set γ := max 1 (max (T.extNorm ρ0 σ y) (T.extNorm ρ0 (topRad ρ0) y))
  have hβ0 : 0 ≤ β := le_max_of_le_left (T.extNorm_nonneg _ _)
  have hγ1 : 1 ≤ γ := le_max_left _ _
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (β * γ + 1) by positivity)
    (show (1 : ℝ) / 2 < 1 by norm_num)
  set W := g - 1
  set t := b * ∑ j ∈ Finset.range K, (-W) ^ j
  refine ⟨a + t * y, b * (-W) ^ K, ?_, fun ρ hρ => ?_⟩
  · have hgs : g * ∑ j ∈ Finset.range K, (-W) ^ j = 1 - (-W) ^ K := by
      rw [← mul_neg_geom_sum (-W) K]
      congr 1
      simp [W]
    have : t * g = b - b * (-W) ^ K := by
      rw [show t * g = b * (g * ∑ j ∈ Finset.range K, (-W) ^ j) by simp only [t]; ring, hgs]
      ring
    linear_combination hab + y * this
  have hsρ : s ≤ ρ := by linarith [σ.2.1, hσ, hρ]
  have hρ0 := rad_pos ρ0 ρ
  have hW : T.extNorm ρ0 ρ W ≤ 1 / 2 := by
    refine (hgW ρ hsρ).trans ?_
    rw [div_le_iff₀ hρ0]
    linarith
  have hb : T.extNorm ρ0 ρ b ≤ β := T.extNorm_le_max σ (topRad ρ0) ρ hρ ρ.2.2 b
  have hy : T.extNorm ρ0 ρ y ≤ γ :=
    (T.extNorm_le_max σ (topRad ρ0) ρ hρ ρ.2.2 y).trans (le_max_right _ _)
  have hWK : T.extNorm ρ0 ρ ((-W) ^ K) ≤ (1 / 2) ^ K := by
    rw [extNorm_pow, extNorm_neg]
    exact pow_le_pow_left₀ (T.extNorm_nonneg _ _) hW K
  have hsmall : β * γ * (1 / 2) ^ K ≤ ε := by
    have h1 : (1 / 2 : ℝ) ^ K * (β * γ + 1) < ε := by
      rw [lt_div_iff₀ (by positivity)] at hK; exact hK
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) K, mul_nonneg hβ0 (zero_le_one.trans hγ1)]
  have hb' : T.extNorm ρ0 ρ (b * (-W) ^ K) ≤ β * (1 / 2) ^ K := by
    rw [extNorm_mul]
    exact mul_le_mul hb hWK (T.extNorm_nonneg _ _) hβ0
  have hby : T.extNorm ρ0 ρ (b * (-W) ^ K * y) ≤ ε := by
    rw [extNorm_mul]
    calc T.extNorm ρ0 ρ (b * (-W) ^ K) * T.extNorm ρ0 ρ y ≤ β * (1 / 2) ^ K * γ :=
          mul_le_mul hb' hy (T.extNorm_nonneg _ _) (by positivity)
      _ = β * γ * (1 / 2) ^ K := by ring
      _ ≤ ε := hsmall
  refine ⟨hb'.trans ?_, hby, ?_⟩
  · calc β * (1 / 2) ^ K ≤ β * γ * (1 / 2) ^ K := by
          have := pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) K
          nlinarith [mul_nonneg (mul_nonneg hβ0 this) (sub_nonneg.2 hγ1)]
      _ ≤ ε := hsmall
  ·
    have e : (a + t * y - 1) * g = -(b * (-W) ^ K * y + W) := by
      have hgs : g * ∑ j ∈ Finset.range K, (-W) ^ j = 1 - (-W) ^ K := by
        rw [← mul_neg_geom_sum (-W) K]
        congr 1
        simp [W]
      have : t * g = b - b * (-W) ^ K := by
        rw [show t * g = b * (g * ∑ j ∈ Finset.range K, (-W) ^ j) by simp only [t]; ring, hgs]
        ring
      linear_combination hab + y * this
    have e2 := congrArg (T.extNorm ρ0 ρ) e
    rw [extNorm_mul, hg1 ρ hsρ, mul_one, extNorm_neg] at e2
    rw [e2]
    exact (T.extNorm_add_le ρ _ _).trans (max_le_max hby (hgW ρ hsρ))

variable (hRE : T.RootExists)
include hRE

theorem exists_full_factor {x : T.RobbaExt ρ0} (hx : x ≠ 0) :
    ∃ (ls : ℕ → List T.Pt) (hl : ∀ k, ∀ P ∈ ls k, T.ptRad P.1 ≤ annHi ρ0 k) (w : T.RobbaExt ρ0),
      x = (InfProd.ofLists T ρ0 ls (annHi ρ0) annHi_nonneg tendsto_annHi hl).prod * w ∧ w ≠ 0 ∧
      (∀ k, ∀ P ∈ ls k, ∀ hr : T.ptRad P.1 ≤ ρ0, T.ptEval P.2 hr x = 0) ∧
      ∀ Q : T.Pt, ∀ hQ : T.ptRad Q.1 ≤ (ρ0 : ℝ) / 2,
        T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) w ≠ 0 := by
  set S0 : T.GcdSt ρ0 := ⟨x, x, hx, hx⟩
  have hl : ∀ k, ∀ P ∈ T.gcdRemoved hRE S0 k, T.ptRad P.1 ≤ annHi ρ0 k := fun k P hP =>
    ((T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)).2.2.1 P hP).2
  set D := InfProd.ofLists T ρ0 (T.gcdRemoved hRE S0) (annHi ρ0) annHi_nonneg tendsto_annHi hl
  have hpart : ∀ k, D.part k = T.normProd ρ0 ((List.range k).flatMap (T.gcdRemoved hRE S0)) :=
    fun k => InfProd.ofLists_part T _ _ _ _ _ k
  have hdx : ∀ k, D.part k ∣ x := fun k => by
    rw [hpart, normProd_dvd_iff]; exact ⟨_, (T.gcdStates_spec hRE S0 k).1⟩
  obtain ⟨w, hw⟩ := D.dvd_of_forall hdx
  have hw0 : w ≠ 0 := by rintro rfl; rw [mul_zero] at hw; exact hx hw
  refine ⟨T.gcdRemoved hRE S0, hl, w, hw, hw0, ?_, ?_⟩
  · intro k P hP hr
    rw [T.ptEval_eq_zero_iff P.2 hr]
    have hmem : P ∈ (List.range (k + 1)).flatMap (T.gcdRemoved hRE S0) :=
      List.mem_flatMap.2 ⟨k, List.mem_range.2 (Nat.lt_succ_self k), hP⟩
    have hdvd : T.ξExt P.1 ρ0 ∣ T.ptProd ρ0 ((List.range (k + 1)).flatMap (T.gcdRemoved hRE S0)) :=
      List.dvd_prod (List.mem_map.2 ⟨P, hmem, rfl⟩)
    exact dvd_trans hdvd ⟨_, (T.gcdStates_spec hRE S0 (k + 1)).1⟩
  · intro Q hQ h1
    have hs0 := T.ptRad_pos' Q.2
    obtain ⟨k, hk1, hk2⟩ := exists_ann (ρ0 := ρ0) hs0 hQ
    set F := (List.range (k + 1)).flatMap (T.gcdRemoved hRE S0)
    have hQr : T.ptRad Q.1 ≤ ρ0 := hQ.trans (half_le_self ρ0.2.1.le)
    have e : T.ptProd ρ0 F * (T.gcdStates hRE S0 (k + 1)).x =
        T.ptProd ρ0 F * (T.unitProd ρ0 F * (D.shift (k + 1)).prod * w) := by
      rw [← (T.gcdStates_spec hRE S0 (k + 1)).1]
      change x = _
      rw [hw, D.prod_eq_part_mul_shift (k + 1), hpart, normProd_eq]; ring
    have hW' := mul_left_cancel₀ (T.ptProd_ne_zero F) e
    have hX : T.ptEval Q.2 hQr (T.gcdStates hRE S0 (k + 1)).x = 0 := by
      rw [hW', map_mul, h1, mul_zero]
    have hY : T.ptEval Q.2 hQr (T.gcdStates hRE S0 (k + 1)).y = 0 := by
      have : (T.gcdStates hRE S0 (k + 1)).y = (T.gcdStates hRE S0 (k + 1)).x := by
        have h1' := (T.gcdStates_spec hRE S0 (k + 1)).1
        have h2' := (T.gcdStates_spec hRE S0 (k + 1)).2
        exact (mul_left_cancel₀ (T.ptProd_ne_zero F) (h2'.symm.trans h1'))
      rw [this]; exact hX
    exact (T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)).2.2.2 Q ⟨hk1, hk2⟩ ⟨hX, hY⟩

omit hRE in
theorem annHi_le_half (k : ℕ) : annHi ρ0 k ≤ (ρ0 : ℝ) / 2 := by
  unfold annHi
  exact div_le_div_of_nonneg_left ρ0.2.1.le (by norm_num)
    (by calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega))

theorem isUnit_ofRad_of_no_point {w : T.RobbaExt ρ0} (hw0 : w ≠ 0)
    (hw : ∀ Q : T.Pt, ∀ hQ : T.ptRad Q.1 ≤ (ρ0 : ℝ) / 2,
      T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) w ≠ 0) :
    IsUnit (T.ofRad ρ0 w) := by
  set ρ1 := halfRad ρ0
  have hρ1 : (ρ1 : ℝ) = (ρ0 : ℝ) / 2 := rfl
  have hw1 : T.res (halfRad_le ρ0) w ≠ 0 := fun h0 => hw0 (T.res_injective _ (h0.trans (map_zero _).symm))
  rw [← T.ofRad_res (halfRad_le ρ0)]
  refine T.isUnit_ofRad_of_mult_eq_zero hw1 fun σ hσ0 hσ1 => ?_
  rw [T.mult_res (halfRad_le ρ0) w ⟨hσ0, hσ1⟩]
  by_contra hm
  have hm1 : 1 ≤ T.mult w σ := by have := T.mult_nonneg w σ; omega
  have hσρ0 : σ < ρ0 := hσ1.trans_le (halfRad_le ρ0)
  obtain ⟨ξ, hξ, hr, y, hy⟩ := hRE ρ0 w hw0 σ hσ0 hσρ0 hm1
  have hQ : T.ptRad ξ ≤ (ρ0 : ℝ) / 2 := by rw [hr, ← hρ1]; exact hσ1.le
  exact hw ⟨ξ, hξ⟩ hQ ((T.ptEval_eq_zero_iff hξ _ w).2 ⟨y, hy⟩)

omit hRE in
theorem bound_of_eventually_antitone {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) {k1 : ℕ}
    (h : ∀ k ≥ k1, c (k + 1) ≤ c k) : ∃ M, ∀ k, c k ≤ M := by
  refine ⟨∑ j ∈ Finset.range (k1 + 1), c j, fun k => ?_⟩
  have hsum : ∀ j ≤ k1, c j ≤ ∑ j ∈ Finset.range (k1 + 1), c j := fun j hj =>
    Finset.single_le_sum (fun i _ => hc0 i) (Finset.mem_range.2 (by omega))
  rcases le_total k k1 with hk | hk
  · exact hsum k hk
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction i with
    | zero => exact hsum k1 le_rfl
    | succ i ih => exact (h (k1 + i) (by omega)).trans (ih (by omega))

theorem one_mem_span_of_coprime {x y : T.RobbaExt ρ0} (hx : x ≠ 0)
    (hcop : ∀ Q : T.Pt, ∀ hQ : T.ptRad Q.1 ≤ (ρ0 : ℝ) / 2,
      ¬ (T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) x = 0 ∧
        T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) y = 0)) :
    (1 : T.RobbaTilde) ∈ Ideal.span {T.ofRad ρ0 x, T.ofRad ρ0 y} := by
  obtain ⟨ls, hl, w, hxw, hw0, hlx, hwnz⟩ := T.exists_full_factor hRE hx
  set D := InfProd.ofLists T ρ0 ls (annHi ρ0) annHi_nonneg tendsto_annHi hl
  have hDg : ∀ k, D.g k = T.normProd ρ0 (ls k) := fun k => rfl

  have hAB : ∀ k, ∃ a b : T.RobbaExt ρ0, a * D.g k + b * y = 1 := by
    intro k
    rw [hDg]
    refine T.exists_bezout_list y (ls k) fun P hP => ⟨(hl k P hP).trans
      ((annHi_le_half k).trans (half_le_self ρ0.2.1.le)), fun h0 => ?_⟩
    have hQ : T.ptRad P.1 ≤ (ρ0 : ℝ) / 2 := (hl k P hP).trans (annHi_le_half k)
    exact hcop P hQ ⟨hlx k P hP _, h0⟩
  have hσ : ∀ k : ℕ, 0 < 2 * annHi ρ0 k ∧ 2 * annHi ρ0 k ≤ ρ0 := fun k => by
    refine ⟨by have := annLo_pos (ρ0 := ρ0) k; have := annLo_le (ρ0 := ρ0) k; linarith, ?_⟩
    have := annHi_le_half (ρ0 := ρ0) k; linarith
  have hAdj : ∀ k, ∃ a' b' : T.RobbaExt ρ0, a' * D.g k + b' * y = 1 ∧
      ∀ ρ : Set.Ioc (0 : ℝ) ρ0, 2 * annHi ρ0 k ≤ ρ →
        T.extNorm ρ0 ρ b' ≤ (1 / 2) ^ k ∧ T.extNorm ρ0 ρ (b' * y) ≤ (1 / 2) ^ k ∧
          T.extNorm ρ0 ρ (a' - 1) ≤ max ((1 / 2) ^ k) (annHi ρ0 k / ρ) := by
    intro k
    obtain ⟨a, b, hab⟩ := hAB k
    rw [hDg] at hab ⊢
    exact T.exists_adjusted hab (annHi_nonneg k)
      (fun ρ hρ => (T.norm_normProd_of_le (annHi_nonneg k) (hl k) ρ hρ).1)
      (fun ρ hρ => (T.norm_normProd_of_le (annHi_nonneg k) (hl k) ρ hρ).2)
      ⟨2 * annHi ρ0 k, (hσ k).1, (hσ k).2⟩ le_rfl (by positivity)
  choose a' b' hab' hbnd using hAdj
  set A : ℕ → T.RobbaExt ρ0 := fun k => ∏ j ∈ Finset.range k, a' j
  set B : ℕ → T.RobbaExt ρ0 := fun k => ∑ j ∈ Finset.range k, A j * D.part j * b' j
  have hA : ∀ k, A (k + 1) = A k * a' k := fun k => Finset.prod_range_succ _ _
  have hB : ∀ k, B (k + 1) = B k + A k * D.part k * b' k := fun k => Finset.sum_range_succ _ _
  have hinv : ∀ k, A k * D.part k + B k * y = 1 := by
    intro k
    induction k with
    | zero => simp [A, B, InfProd.part_zero]
    | succ k ih =>
      rw [hA, hB, InfProd.part_succ]
      linear_combination ih + A k * D.part k * hab' k

  have hconv : ∀ ρ : Set.Ioc (0 : ℝ) ρ0,
      Tendsto (fun k => T.extNorm ρ0 ρ (A (k + 1) - A k)) atTop (𝓝 0) ∧
        Tendsto (fun k => T.extNorm ρ0 ρ (B (k + 1) - B k)) atTop (𝓝 0) := by
    intro ρ
    have hρ := rad_pos ρ0 ρ
    have hs : Tendsto (fun k => 2 * annHi ρ0 k) atTop (𝓝 0) := by
      simpa using (tendsto_annHi (ρ0 := ρ0)).const_mul 2
    have he : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hsr : Tendsto (fun k => annHi ρ0 k / ρ) atTop (𝓝 0) := by
      simpa using (tendsto_annHi (ρ0 := ρ0)).div_const (ρ : ℝ)
    have hm : Tendsto (fun k => max ((1 / 2 : ℝ) ^ k) (annHi ρ0 k / ρ)) atTop (𝓝 0) := by
      simpa using he.max hsr
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 (hs.eventually (ge_mem_nhds hρ))
    obtain ⟨k1, hk1⟩ := eventually_atTop.1 (hm.eventually (gt_mem_nhds one_pos))
    have ha1 : ∀ k ≥ max k0 k1, T.extNorm ρ0 ρ (a' k) ≤ 1 := by
      intro k hk
      have h1 := (hbnd k ρ (hk0 k (le_of_max_le_left hk))).2.2
      have h2 := hk1 k (le_of_max_le_right hk)
      have := T.extNorm_add_le ρ (a' k - 1) 1
      rw [sub_add_cancel, extNorm_one] at this
      exact this.trans (max_le (h1.trans h2.le) le_rfl)
    obtain ⟨M, hM⟩ := bound_of_eventually_antitone (c := fun k => T.extNorm ρ0 ρ (A k))
      (fun k => T.extNorm_nonneg _ _) (k1 := max k0 k1) fun k hk => by
        rw [hA, extNorm_mul]
        exact mul_le_of_le_one_right (T.extNorm_nonneg _ _) (ha1 k hk)
    obtain ⟨CP, hCP⟩ := D.exists_bound ρ
    have hM0 : 0 ≤ M := (T.extNorm_nonneg _ _).trans (hM 0)
    have hCP0 : 0 ≤ CP := (T.extNorm_nonneg _ _).trans (hCP 0)
    refine ⟨?_, ?_⟩
    · have hlim := hm.const_mul M
      rw [mul_zero] at hlim
      refine squeeze_zero' (Eventually.of_forall fun k => T.extNorm_nonneg _ _) ?_ hlim
      filter_upwards [eventually_ge_atTop k0] with k hk
      rw [hA, show A k * a' k - A k = A k * (a' k - 1) by ring, extNorm_mul]
      exact mul_le_mul (hM k) (hbnd k ρ (hk0 k hk)).2.2 (T.extNorm_nonneg _ _) hM0
    · have hlim := he.const_mul (M * CP)
      rw [mul_zero] at hlim
      refine squeeze_zero' (Eventually.of_forall fun k => T.extNorm_nonneg _ _) ?_ hlim
      filter_upwards [eventually_ge_atTop k0] with k hk
      rw [hB, add_sub_cancel_left, extNorm_mul, extNorm_mul]
      exact mul_le_mul (mul_le_mul (hM k) (hCP k) (T.extNorm_nonneg _ _) hM0)
        (hbnd k ρ (hk0 k hk)).1 (T.extNorm_nonneg _ _) (mul_nonneg hM0 hCP0)
  obtain ⟨Al, hAl⟩ := cauchySeq_tendsto_of_complete (T.cauchySeq_of_increments fun ρ => (hconv ρ).1)
  obtain ⟨Bl, hBl⟩ := cauchySeq_tendsto_of_complete (T.cauchySeq_of_increments fun ρ => (hconv ρ).2)
  have hlim : Tendsto (fun k => A k * D.part k + B k * y) atTop (𝓝 (Al * D.prod + Bl * y)) :=
    (hAl.mul D.tendsto_part).add (hBl.mul tendsto_const_nhds)
  have hconst : (fun k => A k * D.part k + B k * y) = fun _ => (1 : T.RobbaExt ρ0) := funext hinv
  rw [hconst] at hlim
  have hrel : Al * D.prod + Bl * y = 1 := (tendsto_nhds_unique tendsto_const_nhds hlim).symm

  obtain ⟨u, hu⟩ := (T.isUnit_ofRad_of_no_point hRE hw0 hwnz).exists_right_inv
  rw [Ideal.mem_span_pair]
  refine ⟨T.ofRad ρ0 Al * u, T.ofRad ρ0 Bl, ?_⟩
  have e := congrArg (T.ofRad ρ0) hrel
  rw [map_add, map_mul, map_mul, map_one] at e
  rw [hxw, map_mul, ← e]
  linear_combination T.ofRad ρ0 Al * T.ofRad ρ0 D.prod * hu

theorem isBezout_of_rootExists : IsBezout T.RobbaTilde := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  by_cases hx : x = 0
  · subst hx
    refine ⟨⟨y, ?_⟩⟩
    rw [Ideal.span_insert_zero]
  by_cases hy : y = 0
  · subst hy
    refine ⟨⟨x, ?_⟩⟩
    rw [Set.pair_comm, Ideal.span_insert_zero]
  obtain ⟨ρ0, x0, y0, rfl, rfl⟩ := T.exists_ofRad₂ x y
  have hx0 : x0 ≠ 0 := by rintro rfl; exact hx (map_zero _)
  have hy0 : y0 ≠ 0 := by rintro rfl; exact hy (map_zero _)
  obtain ⟨d, x', y', hd, hx', hy', hcop⟩ := T.exists_gcd hRE hx0 hy0
  have hx'0 : x' ≠ 0 := by rintro rfl; rw [mul_zero] at hx'; exact hx0 hx'
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (T.one_mem_span_of_coprime hRE hx'0 hcop)
  refine ⟨⟨T.ofRad ρ0 d, le_antisymm ?_ ?_⟩⟩
  · rw [Ideal.span_le]
    rintro z hz
    rcases hz with rfl | rfl
    · rw [hx', map_mul]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · rw [hy', map_mul]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have e : T.ofRad ρ0 d = a * T.ofRad ρ0 x0 + b * T.ofRad ρ0 y0 := by
      rw [hx', hy', map_mul, map_mul]
      linear_combination (-(T.ofRad ρ0 d)) * hab
    rw [SetLike.mem_coe, e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open IsLocalRing

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem mem_int_of_map_mem_int (ψ : Γ →+* Γ) (g : L →+* L) (hg : ∀ c, ‖g c‖ ≤ 1 ↔ ‖c‖ ≤ 1)
    {u : Γ} (hπ : ψ T.π = T.π * u) (hu : u ∈ T.int) (hu1 : ‖T.red u‖ = 1)
    (hteich : ∀ c, ψ (T.teich c) = T.teich (g c)) {y : Γ} (hy : ψ y ∈ T.int) : y ∈ T.int := by
  classical
  by_contra hyint
  rw [T.mem_int_iff] at hyint
  push_neg at hyint
  set n0 := Nat.find hyint with hn0def
  have hn0 : 1 < ‖T.coeff y n0‖ := Nat.find_spec hyint
  have hlow : ∀ i < n0, ‖T.coeff y i‖ ≤ 1 := fun i hi => by
    have := Nat.find_min hyint hi; push_neg at this; exact this

  have hA : ψ (T.partialSum y n0) ∈ T.int := by
    simp only [partialSum, finSum, map_sum, map_mul, map_pow, hπ, hteich]
    refine Subring.sum_mem _ fun i hi => mul_mem (pow_mem (mul_mem T.π_mem_int hu) _) ?_
    exact T.teich_mem_int ((hg _).2 (hlow i (Finset.mem_range.1 hi)))

  set t := T.tail^[n0] y with htdef
  have hy' : y = T.partialSum y n0 + T.π ^ n0 * t := by rw [← T.sub_partialSum]; ring
  have ht : t = T.teich (T.coeff y n0) + T.π * T.tail t := by
    have := T.eq_teich_add_π_mul_tail t
    rwa [show T.red t = T.coeff y n0 from rfl] at this
  have hX : ψ y - ψ (T.partialSum y n0) =
      T.π ^ n0 * (u ^ n0 * T.teich (g (T.coeff y n0)) + T.π * (u ^ (n0 + 1) * ψ (T.tail t))) := by
    have e : ψ y = ψ (T.partialSum y n0) + ψ (T.π ^ n0 * t) := by rw [← map_add, ← hy']
    have hψt : ψ t = T.teich (g (T.coeff y n0)) + T.π * u * ψ (T.tail t) := by
      conv_lhs => rw [ht]
      rw [map_add, map_mul, hteich, hπ]
    rw [e, add_sub_cancel_left, map_mul, map_pow, hπ, hψt]
    ring
  have hXint : ψ y - ψ (T.partialSum y n0) ∈ T.int := sub_mem hy hA
  have hc := (T.mem_int_iff.1 hXint) n0
  rw [hX] at hc
  have := T.coeff_π_pow_mul_add n0
    (u ^ n0 * T.teich (g (T.coeff y n0)) + T.π * (u ^ (n0 + 1) * ψ (T.tail t))) 0
  rw [zero_add] at this
  rw [this, coeff_zero, map_add, map_mul, map_mul, map_pow, red_teich, red_π, zero_mul, add_zero,
    norm_mul, norm_pow, hu1, one_pow, one_mul] at hc
  exact absurd ((hg _).1 hc) (not_le.2 hn0)

end TeichLift

namespace ExtRobba

section Lift

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : ResidueField (normInteger K) →+* L)
variable {ϖ : normInteger K} (hϖ : Irreducible ϖ) (hι : ∀ a, ‖ι a‖ ≤ 1)

def gammaTeichLift : TeichLift p L (Gamma p ι) where
  π := gammaPi p ι ϖ
  red := gammaRed p ι
  red_surjective := gammaRed_surjective p ι
  ker_red := ker_gammaRed p ι hϖ
  π_mem_nonZeroDivisors := gammaPi_mem_nonZeroDivisors p ι hϖ
  isAdicComplete := isAdicComplete_gammaPi p ι hϖ
  int := gammaInt p ι
  π_mem_int := tmul_mem_gammaInt p ι (Subring.one_mem _) ϖ
  norm_red_le_one := fun _ hx => norm_gammaRed_le_one p ι hϖ hι hx
  exists_mem_int := fun _ ha => exists_mem_gammaInt_gammaRed_eq p ι ha
  exists_eq_π_mul := fun _ hx h0 => exists_mem_gammaInt_eq_gammaPi_mul p ι hϖ hι hx h0
  mem_int_of_approx := fun _ h => mem_gammaInt_of_forall p ι hϖ hι h

@[simp] theorem gammaTeichLift_π : (gammaTeichLift p ι hϖ hι).π = gammaPi p ι ϖ := rfl

@[simp] theorem gammaTeichLift_red : (gammaTeichLift p ι hϖ hι).red = gammaRed p ι := rfl

@[simp] theorem gammaTeichLift_int : (gammaTeichLift p ι hϖ hι).int = gammaInt p ι := rfl

include hι in

theorem norm_ι_eq_one {c : ResidueField (normInteger K)} (hc : c ≠ 0) : ‖ι c‖ = 1 := by
  have h1 : ‖ι c‖ * ‖ι c⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, norm_one]
  have ha := hι c
  have hb := hι c⁻¹
  nlinarith [norm_nonneg (ι c), norm_nonneg (ι c⁻¹)]

end Lift

section Frob

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]
variable (σ : K →+* K) (hσn : ∀ x, ‖σ x‖ = ‖x‖)

def intFrob : normInteger K →+* normInteger K :=
  (σ.comp (normInteger K).subtype).codRestrict (normInteger K) fun x => mem_normInteger.2 (by
    rw [RingHom.comp_apply, hσn]; exact mem_normInteger.1 x.2)

@[simp] theorem coe_intFrob (x : normInteger K) : ((intFrob σ hσn x : normInteger K) : K) = σ x := rfl

variable (a : ℕ) (hσr : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ p ^ a‖ < 1)

include hσr in

theorem residue_intFrob (x : normInteger K) :
    residue (normInteger K) (intFrob σ hσn x) = residue (normInteger K) x ^ p ^ a := by
  rw [← sub_eq_zero, ← map_pow, ← map_sub, residue_eq_zero_iff_norm_lt_one]
  push_cast
  exact hσr x (mem_normInteger.1 x.2)

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)

include hσn hσr hϖ in

theorem exists_intFrob_approx (n : ℕ) (z : normInteger K) (hz : ‖(z : K)‖ ≤ ‖(ϖ : K)‖ ^ n) :
    ∃ x : normInteger K, ‖σ x - z‖ ≤ ‖(ϖ : K)‖ ^ (n + 1) := by
  have hϖ0 : ‖(ϖ : K)‖ ≠ 0 := (norm_unif_pos hϖ).ne'
  have hσϖ : ‖σ ϖ‖ = ‖(ϖ : K)‖ := hσn _
  have hσϖ0 : σ ϖ ≠ 0 := fun h => hϖ0 (by rw [← hσϖ, h, norm_zero])
  have hz' : ‖(z : K) / σ ϖ ^ n‖ ≤ 1 := by
    rw [norm_div, norm_pow, hσϖ, div_le_one (pow_pos (norm_unif_pos hϖ) n)]; exact hz
  set z' : normInteger K := ⟨(z : K) / σ ϖ ^ n, mem_normInteger.2 hz'⟩ with hz'def
  obtain ⟨x0, hx0⟩ := residue_surjective
    ((iterateFrobeniusEquiv (ResidueField (normInteger K)) p a).symm (residue (normInteger K) z'))
  have hres : residue (normInteger K) (intFrob σ hσn x0 - z') = 0 := by
    rw [map_sub, residue_intFrob p σ hσn a hσr, hx0, ← iterateFrobeniusEquiv_def,
      RingEquiv.apply_symm_apply, sub_self]
  rw [residue_eq_zero_iff_norm_lt_one] at hres
  have h1 := norm_le_norm_unif_of_lt_one hϖ hres
  push_cast at h1
  refine ⟨ϖ ^ n * x0, ?_⟩
  have e : σ ((ϖ ^ n * x0 : normInteger K) : K) - z = σ ϖ ^ n * (σ x0 - (z : K) / σ ϖ ^ n) := by
    push_cast
    rw [map_mul, map_pow, mul_sub, mul_div_cancel₀ _ (pow_ne_zero _ hσϖ0)]
  rw [e, norm_mul, norm_pow, hσϖ, pow_succ]
  exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg _) _)

include hσn hσr hϖ in
theorem exists_intFrob_near (n : ℕ) (z : normInteger K) :
    ∃ x : normInteger K, ‖σ x - z‖ ≤ ‖(ϖ : K)‖ ^ n := by
  induction n generalizing z with
  | zero => exact ⟨0, by simpa using mem_normInteger.1 z.2⟩
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih z
    have hw : ‖((z - intFrob σ hσn x : normInteger K) : K)‖ ≤ ‖(ϖ : K)‖ ^ n := by
      push_cast; rw [norm_sub_rev]; exact hx
    obtain ⟨x', hx'⟩ := exists_intFrob_approx p σ hσn a hσr hϖ n _ hw
    refine ⟨x + x', ?_⟩
    have e : σ ((x + x' : normInteger K) : K) - z = σ x' - ((z - intFrob σ hσn x : normInteger K) : K) := by
      push_cast; rw [map_add, coe_intFrob]; ring
    rw [e]; exact hx'

include hσn hσr hϖ in

theorem intFrob_bijective : Function.Bijective (intFrob σ hσn) := by
  refine ⟨fun x y h => Subtype.ext (σ.injective (by
    have := congrArg (fun z : normInteger K => (z : K)) h; simpa using this)), fun y => ?_⟩
  have hiso : Isometry σ := AddMonoidHomClass.isometry_of_norm σ hσn
  have hclosed : IsClosed (Set.range σ) := hiso.isClosedEmbedding.isClosed_range
  have hmem : (y : K) ∈ closure (Set.range σ) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_unif_lt_one hϖ)
    obtain ⟨x, hx⟩ := exists_intFrob_near p σ hσn a hσr hϖ n y
    exact ⟨σ x, ⟨x, rfl⟩, by rw [dist_eq_norm, norm_sub_rev]; exact hx.trans_lt hn⟩
  rw [hclosed.closure_eq] at hmem
  obtain ⟨x, hx⟩ := hmem
  have hx1 : ‖x‖ ≤ 1 := by rw [← hσn, hx]; exact mem_normInteger.1 y.2
  exact ⟨⟨x, mem_normInteger.2 hx1⟩, Subtype.ext hx⟩

def frobUnifUnit (hϖ : Irreducible ϖ) : normInteger K :=
  ⟨σ ϖ / ϖ, mem_normInteger.2 (by
    rw [norm_div, hσn, div_self (norm_unif_pos hϖ).ne'])⟩

theorem norm_frobUnifUnit : ‖((frobUnifUnit σ hσn hϖ : normInteger K) : K)‖ = 1 := by
  show ‖σ ϖ / ϖ‖ = 1
  rw [norm_div, hσn, div_self (norm_unif_pos hϖ).ne']

theorem intFrob_unif : intFrob σ hσn ϖ = ϖ * frobUnifUnit σ hσn hϖ := by
  apply Subtype.ext
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => (norm_unif_pos hϖ).ne' (by rw [h, norm_zero])
  show σ ϖ = (ϖ : K) * (σ ϖ / ϖ)
  rw [mul_div_cancel₀ _ hϖ0]

theorem residue_frobUnifUnit_ne_zero : residue (normInteger K) (frobUnifUnit σ hσn hϖ) ≠ 0 := by
  rw [Ne, residue_eq_zero_iff_norm_lt_one, norm_frobUnifUnit]
  exact lt_irrefl 1

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : ResidueField (normInteger K) →+* L) (hι : ∀ a, ‖ι a‖ ≤ 1)

def gammaPhiEquiv : Gamma p ι ≃+* Gamma p ι :=
  RingEquiv.ofBijective (gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr))
    (gammaPhi_bijective p ι a _ _ (intFrob_bijective p σ hσn a hσr hϖ) hϖ)

theorem gammaPhiEquiv_apply (x : Gamma p ι) :
    gammaPhiEquiv p σ hσn a hσr hϖ ι x =
      gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr) x := rfl

theorem gammaPhi_gammaPi_eq :
    gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr) (gammaPi p ι ϖ) =
      gammaPi p ι ϖ * gammaOfInt p ι (frobUnifUnit σ hσn hϖ) := by
  rw [gammaPhi_gammaPi, intFrob_unif σ hσn hϖ, gammaPi_eq, gammaPi_eq, gammaOfInt_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

include hι in
theorem norm_gammaRed_frobUnifUnit :
    ‖gammaRed p ι (gammaOfInt p ι (frobUnifUnit σ hσn hϖ))‖ = 1 := by
  rw [gammaOfInt_apply, gammaRed_tmul, map_one, WittVector.one_coeff_zero, one_mul]
  exact norm_ι_eq_one ι hι (residue_frobUnifUnit_ne_zero σ hσn hϖ)

def gammaTeichFrob : TeichLift.TeichFrob (gammaTeichLift p ι hϖ hι) where
  φ := gammaPhiEquiv p σ hσn a hσr hϖ ι
  a := a
  red_φ := fun x => gammaRed_gammaPhi p ι a _ _ x
  u := gammaOfInt p ι (frobUnifUnit σ hσn hϖ)
  φ_π := gammaPhi_gammaPi_eq p σ hσn a hσr hϖ ι
  u_mem_int := tmul_mem_gammaInt p ι (Subring.one_mem _) _
  norm_red_u := norm_gammaRed_frobUnifUnit p σ hσn hϖ ι hι
  map_int := fun _ hx => gammaPhi_mem_gammaInt p ι a _ _ hx
  symm_map_int := fun x hx => by
    set T := gammaTeichLift p ι hϖ hι
    have hψ : ∀ y, T.red (gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr) y) =
        iterateFrobenius L p a (T.red y) := fun y => by
      rw [iterateFrobenius_def]; exact gammaRed_gammaPhi p ι a _ _ y
    refine T.mem_int_of_map_mem_int
      (gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr)) (iterateFrobenius L p a)
      (fun c => by
        rw [iterateFrobenius_def, norm_pow]
        exact pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero))
      (gammaPhi_gammaPi_eq p σ hσn a hσr hϖ ι) (tmul_mem_gammaInt p ι (Subring.one_mem _) _)
      (norm_gammaRed_frobUnifUnit p σ hσn hϖ ι hι) (T.map_teich _ _ hψ) ?_
    rw [← gammaPhiEquiv_apply p σ hσn a hσr hϖ ι, RingEquiv.apply_symm_apply]
    exact hx

@[simp] theorem gammaTeichFrob_a : (gammaTeichFrob p σ hσn a hσr hϖ ι hι).a = a := rfl

theorem gammaTeichFrob_φ (x : Gamma p ι) :
    (gammaTeichFrob p σ hσn a hσr hϖ ι hι).φ x =
      gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr) x := rfl

end Frob

end ExtRobba

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ExtRobba

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (IsLocalRing.ResidueField (normInteger K)) p]
  [PerfectRing (IsLocalRing.ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : IsLocalRing.ResidueField (normInteger K) →+* L) {ϖ : normInteger K}
  (hϖ : Irreducible ϖ) (hι : ∀ a, ‖ι a‖ ≤ 1)

abbrev RobbaR (ρ0 : Set.Ioo (0 : ℝ) 1) := (gammaTeichLift p ι hϖ hι).RobbaExt ρ0

abbrev RobbaTildeL := (gammaTeichLift p ι hϖ hι).RobbaTilde

example : IsDomain (RobbaTildeL p ι hϖ hι) := inferInstance

example (ρ0 : Set.Ioo (0 : ℝ) 1) : IsDomain (RobbaR p ι hϖ hι ρ0) := inferInstance

def frobenius (σ : K →+* K) (hσn : ∀ x, ‖σ x‖ = ‖x‖) (a : ℕ)
    (hσr : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ p ^ a‖ < 1) :
    RobbaTildeL p ι hϖ hι ≃+* RobbaTildeL p ι hϖ hι :=
  (gammaTeichFrob p σ hσn a hσr hϖ ι hι).tildeEquiv

end ExtRobba

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  [IsAlgClosed L] [CompleteSpace L]

theorem rootExists : T.RootExists := fun _ _ hx _ hr0 hrρ hm => T.exists_point_dvd hx hr0 hrρ hm

theorem isBezout_robbaTilde : IsBezout T.RobbaTilde := T.isBezout_of_rootExists T.rootExists

end TeichLift

namespace ExtRobba

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (IsLocalRing.ResidueField (normInteger K)) p]
  [PerfectRing (IsLocalRing.ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p] [IsAlgClosed L]
variable (ι : IsLocalRing.ResidueField (normInteger K) →+* L) {ϖ : normInteger K}
  (hϖ : Irreducible ϖ) (hι : ∀ a, ‖ι a‖ ≤ 1)

end ExtRobba

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Module PhiModule

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}
  [CompleteSpace L] [IsAlgClosed L]

instance instIsBezoutRobbaTilde : IsBezout T.RobbaTilde := T.isBezout_robbaTilde

namespace TeichFrob

variable (F : T.TeichFrob)

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Module PhiModule

namespace PhiModule.UnitOrd

variable {R : Type*} [CommRing R] {φ : R →+* R} (v : UnitOrd R φ)

theorem map_zpow (a : Rˣ) (k : ℤ) : v.ord (a ^ k) = k * v.ord a := by
  rcases k with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, v.map_pow]
  · rw [zpow_negSucc, v.map_inv, v.map_pow, Int.negSucc_eq]; push_cast; ring

end PhiModule.UnitOrd

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}
  [CompleteSpace L]

theorem πTilde_ne_zero : T.πTilde ≠ 0 := by
  intro h
  have := T.ofRad_πExt ⟨1 / 2, by norm_num, by norm_num⟩
  rw [h] at this
  have h1 := T.πExt_mul_πInvExt ⟨1 / 2, by norm_num, by norm_num⟩
  have h2 := congrArg (T.ofRad ⟨1 / 2, by norm_num, by norm_num⟩) h1
  rw [map_mul, this, zero_mul, map_one] at h2
  exact zero_ne_one h2

theorem isUnit_πTilde : IsUnit T.πTilde := by
  rw [T.isUnit_iff]
  exact ⟨πTilde_ne_zero, ⟨TeichFrob.πEdag T, rfl⟩⟩

variable (T) in

def πUnit : T.RobbaTildeˣ := (isUnit_πTilde (T := T)).unit

theorem coe_πUnit : ((πUnit T : T.RobbaTildeˣ) : T.RobbaTilde) = T.πTilde := IsUnit.unit_spec _

theorem tildeOrd_πUnit : T.tildeOrd (πUnit T) = 1 := by
  rw [T.tildeOrd_eq (b := TeichFrob.πEdag T) (by rw [coe_πUnit]; rfl)]
  show T.ordB (algebraMap Γ T.B T.π) = 1
  have h1 : algebraMap Γ T.B T.π = ((T.piB ^ (1 : ℤ) : T.Bˣ) : T.B) * algebraMap Γ T.B 1 := by
    rw [map_one, mul_one, zpow_one, piB_val]
  rw [h1]
  exact T.ordB_piB_zpow_mul _ (by rw [map_one]; exact one_ne_zero)

namespace TeichFrob

variable (F : T.TeichFrob)

variable [IsAlgClosed L]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end
