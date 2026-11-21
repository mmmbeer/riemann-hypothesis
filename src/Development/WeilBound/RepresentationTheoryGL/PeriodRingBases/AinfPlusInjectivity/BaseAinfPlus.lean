import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

namespace BaseC

theorem inv_uniq {R : Type*} [CommRing R] {a b c : R} (ha : a * c = 1) (hb : b * c = 1) : a = b :=
  calc a = a * (b * c) := by rw [hb, mul_one]
    _ = (a * c) * b := by ring
    _ = b := by rw [ha, one_mul]

variable {l : ℕ} [Fact l.Prime]

theorem ι_eq : ι l = PositivityTheory.LocInh.ιCD l :=
  PositivityTheory.LocInh.bcris_hom_ext fun x =>
    (Loc2.lift_mk₀ (iC l) (isUnit_iC_l l) (isUnit_image_period l) x).trans (PositivityTheory.LocInh.ιCD_cB x).symm

theorem aB_ainfMap (a : WittVector l (PreTilt ↥(PadicComplexInt l) l)) :
    aB l (ainfMap l a) = Formalism.Per6.aB l a := rfl

theorem aB_injective : Function.Injective (aB l) := by
  intro a b h
  obtain ⟨a, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) b
  rw [aB_ainfMap, aB_ainfMap] at h
  rw [PositivityTheory.LocInh.aB_injective h]

theorem φ_aB (a : AInf ℂ_[l] l) : φ l (aB l a) = aB l (WittVector.frobenius a) := by
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  rw [← PositivityTheory.LocInh.frob_ainfMap_frobenius, aB_ainfMap, aB_ainfMap]
  exact (PositivityTheory.LocInh.aB_frobenius b).symm

theorem σ_aB (g : GQ l) (a : AInf ℂ_[l] l) : ∃ a' : AInf ℂ_[l] l, σB g (aB l a) = aB l a' := by
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  refine ⟨ainfMap l (WittVector.map (PositivityTheory.LocInh.galT g) b), ?_⟩
  rw [aB_ainfMap, aB_ainfMap]
  exact (PositivityTheory.LocInh.aB_act g b).symm

abbrev u (l : ℕ) [Fact l.Prime] : B l := qB l ((l : ℚ_[l])⁻¹)

theorem u_mul : u l * (l : B l) = 1 := by
  rw [u, ← map_natCast (qB l) l, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), map_one]

theorem map_u (f : B l →+* B l) : f (u l) = u l := by
  refine inv_uniq (c := (l : B l)) ?_ u_mul
  rw [← map_natCast f l, ← map_mul, u_mul, map_one]

theorem aB_mem (a : AInf ℂ_[l] l) : aB l a ∈ Ainf' l :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem u_mem : u l ∈ Ainf' l :=
  Subring.subset_closure (Or.inr rfl)

theorem map_mem {f : B l →+* B l} (h1 : ∀ a, f (aB l a) ∈ Ainf' l) :
    ∀ x ∈ Ainf' l, f x ∈ Ainf' l := fun x hx =>
  (Subring.closure_le (t := (Ainf' l).comap f)).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · exact h1 a
    · rw [Set.mem_singleton_iff.1 hy]
      show f (u l) ∈ Ainf' l
      rw [map_u]
      exact u_mem) hx

theorem pow_u (y : B l) (n : ℕ) : y * (l : B l) ^ n * u l ^ n = y := by
  rw [mul_assoc, ← mul_pow, mul_comm (l : B l), u_mul, one_pow, mul_one]

def rep (l : ℕ) [Fact l.Prime] : Subring (B l) where
  carrier := {x | ∃ (a : AInf ℂ_[l] l) (k : ℕ), x = aB l a * u l ^ k}
  mul_mem' := by
    rintro _ _ ⟨a, k, rfl⟩ ⟨b, j, rfl⟩
    exact ⟨a * b, k + j, by rw [map_mul, pow_add]; ring⟩
  one_mem' := ⟨1, 0, by rw [map_one, pow_zero, mul_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, k, rfl⟩ ⟨b, j, rfl⟩
    refine ⟨a * (l : AInf ℂ_[l] l) ^ j + b * (l : AInf ℂ_[l] l) ^ k, k + j, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
    calc aB l a * u l ^ k + aB l b * u l ^ j =
        aB l a * (l : B l) ^ j * u l ^ j * u l ^ k + aB l b * (l : B l) ^ k * u l ^ k * u l ^ j := by
          rw [pow_u, pow_u]
      _ = _ := by ring
  zero_mem' := ⟨0, 0, by rw [map_zero, zero_mul]⟩
  neg_mem' := by
    rintro _ ⟨a, k, rfl⟩
    exact ⟨-a, k, by rw [map_neg, neg_mul]⟩

theorem mem_rep {x : B l} (hx : x ∈ Ainf' l) : ∃ (a : AInf ℂ_[l] l) (k : ℕ), x = aB l a * u l ^ k :=
  (Subring.closure_le (t := rep l)).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · exact ⟨a, 0, by rw [pow_zero, mul_one]⟩
    · rw [Set.mem_singleton_iff.1 hy]
      exact ⟨1, 1, by rw [map_one, one_mul, pow_one]⟩) hx

end BaseC

end period_ring_base
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

namespace BaseC

variable {l : ℕ} [Fact l.Prime]

theorem ainf_φ : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l :=
  map_mem fun a => by rw [φ_aB]; exact aB_mem _

theorem ainf_σ (g : GQ l) : ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l :=
  map_mem fun a => by
    obtain ⟨a', h⟩ := σ_aB g a
    rw [h]; exact aB_mem _

theorem ι_u : ι l (u l) = qQ l ((l : ℚ_[l])⁻¹) := by
  refine inv_uniq (c := (l : BdR l)) ?_ ?_
  · rw [← map_natCast (ι l) l, ← map_mul, u_mul, map_one]
  · rw [← map_natCast (qQ l) l, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), map_one]

theorem ainf_plus : ∀ x ∈ Ainf' l, ι l x ∈ Plus l := fun x hx =>
  (Subring.closure_le (t := (Plus l).comap (ι l))).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · refine ⟨ACris.iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) a), ?_⟩
      exact (Loc2.lift_mk₀ (iC l) (isUnit_iC_l l) (isUnit_image_period l) _).symm
    · rw [Set.mem_singleton_iff.1 hy]
      show ι l (u l) ∈ Plus l
      rw [ι_u]
      exact ⟨algebraMap ℚ_[l] (BdRp l) _, rfl⟩) hx

theorem φpow_aB (h : ℕ) (a : AInf ℂ_[l] l) :
    (φ l ^ h) (aB l a) = aB l ((WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] a) := by
  induction h with
  | zero => rfl
  | succ n ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, φ_aB,
      Function.iterate_succ_apply']

theorem cancel_l {N : ℕ} {y z : B l} (h : (l : B l) ^ N * y = (l : B l) ^ N * z) : y = z := by
  rw [← pow_u y N, ← pow_u z N, mul_comm y, mul_comm z, h]

theorem coeff_ne (b : AInf ℂ_[l] l) (hb : b.coeff 0 ≠ 0) (h : ℕ) :
    ((WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] b).coeff 0 ≠ 0 := by
  rw [WittVector.iterate_frobenius_coeff]
  intro h0
  apply hb
  have hinj : Function.Injective (⇑(frobenius (PreTilt ↥(normInteger ℂ_[l]) l) l))^[h] :=
    Function.Injective.iterate (PerfectRing.bijective_frobenius (R := PreTilt ↥(normInteger ℂ_[l]) l)
      (p := l)).1 h
  apply hinj
  rw [iterate_frobenius, iterate_frobenius, h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]

theorem coeff_l_mul {n : ℕ} (hn : n ≠ 0) (b : AInf ℂ_[l] l) : ((l : AInf ℂ_[l] l) ^ n * b).coeff 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [show (l : AInf ℂ_[l] l) ^ (k + 1) * b = ((l : AInf ℂ_[l] l) ^ k * b) * (l : AInf ℂ_[l] l) by ring]
  exact WittVector.mul_charP_coeff_zero _

theorem ainf_eig (h : ℕ) (m : ℤ) (hm : m ≠ 0) (x : B l) (hx : x ∈ Ainf' l) (he : Eig h m x) : x = 0 := by
  obtain ⟨a, k, rfl⟩ := mem_rep hx
  have hu : (φ l ^ h) (u l) = u l := map_u _
  set F := (WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] with hF
  have he' : aB l (F a) * u l ^ k = (qB l ((l : ℚ_[l]) ^ m) * aB l a) * u l ^ k := by
    have := he
    rw [Eig, map_mul, map_pow, hu, φpow_aB] at this
    rw [this]; ring
  have e : aB l (F a) = qB l ((l : ℚ_[l]) ^ m) * aB l a := by
    have k1 : ∀ y : B l, y * u l ^ k * (l : B l) ^ k = y := fun y => by
      rw [mul_right_comm]; exact pow_u y k
    rw [← k1 (aB l (F a)), he', k1]
  have hFl : F (l : AInf ℂ_[l] l) = l := Function.iterate_fixed (map_natCast _ l) h
  have hFmul : ∀ (N : ℕ) (b : AInf ℂ_[l] l), F ((l : AInf ℂ_[l] l) ^ N * b) = (l : AInf ℂ_[l] l) ^ N * F b :=
    fun N b => by
      rw [hF, iterate_map_mul, iterate_map_pow, ← hF, hFl]
  have haB : ∀ (N : ℕ) (b : AInf ℂ_[l] l), aB l ((l : AInf ℂ_[l] l) ^ N * b) = (l : B l) ^ N * aB l b :=
    fun N b => by rw [map_mul, map_pow, map_natCast]
  suffices ha : a = 0 by rw [ha, map_zero, zero_mul]
  by_contra ha
  obtain ⟨N, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a ha
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : n ≠ 0 := by rintro rfl; exact hm rfl
    have e1 : (l : B l) ^ N * aB l (F b) = (l : B l) ^ N * aB l ((l : AInf ℂ_[l] l) ^ n * b) :=
      calc (l : B l) ^ N * aB l (F b) = aB l (F ((l : AInf ℂ_[l] l) ^ N * b)) := by rw [hFmul, haB]
        _ = qB l ((l : ℚ_[l]) ^ (n : ℤ)) * aB l ((l : AInf ℂ_[l] l) ^ N * b) := e
        _ = _ := by rw [zpow_natCast, map_pow, map_natCast, haB, haB]; ring
    have e2 := aB_injective (cancel_l e1)
    have c := congrArg (fun w => WittVector.coeff w 0) e2
    rw [coeff_l_mul hn] at c
    exact coeff_ne b hb h c
  · have hn : n ≠ 0 := by rintro rfl; exact hm (by simp)
    have hq : qB l ((l : ℚ_[l]) ^ (-(n : ℤ))) * (l : B l) ^ n = 1 := by
      rw [← map_natCast (qB l) l, ← map_pow, ← map_mul, _root_.zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)), map_one]
    have e1 : (l : B l) ^ N * aB l (F b * (l : AInf ℂ_[l] l) ^ n) = (l : B l) ^ N * aB l b :=
      calc (l : B l) ^ N * aB l (F b * (l : AInf ℂ_[l] l) ^ n)
          = aB l (F ((l : AInf ℂ_[l] l) ^ N * b)) * (l : B l) ^ n := by
            rw [hFmul, map_mul, haB, map_pow, map_natCast]; ring
        _ = qB l ((l : ℚ_[l]) ^ (-(n : ℤ))) * aB l ((l : AInf ℂ_[l] l) ^ N * b) * (l : B l) ^ n := by
            rw [e]
        _ = _ := by rw [mul_right_comm, hq, one_mul, haB]
    have e2 := aB_injective (cancel_l e1)
    have c := congrArg (fun w => WittVector.coeff w 0) e2
    rw [mul_comm, coeff_l_mul hn] at c
    exact hb c.symm

end BaseC

end period_ring_base
end
end

section
noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

theorem base_ainf_φ (l : ℕ) [Fact l.Prime] : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l :=
  BaseC.ainf_φ

theorem base_ainf_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l), ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l :=
  BaseC.ainf_σ

theorem base_ainf_plus (l : ℕ) [Fact l.Prime] : ∀ x ∈ Ainf' l, ι l x ∈ Plus l :=
  BaseC.ainf_plus

theorem base_ainf_eig (l : ℕ) [Fact l.Prime] :
    ∀ (h : ℕ) (m : ℤ), m ≠ 0 → ∀ x ∈ Ainf' l, Eig h m x → x = 0 :=
  fun h m hm x hx he => BaseC.ainf_eig h m hm x hx he

end period_ring_base
end
end
