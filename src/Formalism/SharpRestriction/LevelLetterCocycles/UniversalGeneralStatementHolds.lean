import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IsUnitOfMk
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasicsD
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneratorsOfUnits
import Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
import Formalism.SharpRestriction.LevelLetterCocycles.LocalInputsFromLiterature

section
namespace Formalism.MainNotions.UnusedSlot80.InvCutPfL

open Formalism.MainNotions.N.Ln03 Formalism.MainNotions.UnusedSlot80.InvCut

section Part1

variable (LL : Type) [Field LL] (l : ℕ) [Fact l.Prime] (s : ℕ)

theorem invCutPf_precomp_mul (a b : (ZMod (l ^ (s + 1)))ˣ) (f : Rs LL l s → LL) :
    precomp LL l s a (precomp LL l s b f) = precomp LL l s (a * b) f := by
  funext ζ
  simp only [precomp_apply, powR_powR]

theorem invCutPf_precomp_one (f : Rs LL l s → LL) : precomp LL l s 1 f = f := by
  funext ζ
  simp only [precomp_apply, powR_one]

def invCutPf_stab (f : Rs LL l s → LL) : Subgroup (ZMod (l ^ (s + 1)))ˣ where
  carrier := {a | precomp LL l s a f = f}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [← invCutPf_precomp_mul, hb, ha]
  one_mem' := invCutPf_precomp_one LL l s f
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc precomp LL l s a⁻¹ f = precomp LL l s a⁻¹ (precomp LL l s a f) := by rw [ha]
      _ = f := by rw [invCutPf_precomp_mul, inv_mul_cancel, invCutPf_precomp_one]

theorem invCutPf_mem_stab (f : Rs LL l s → LL) (a : (ZMod (l ^ (s + 1)))ˣ) :
    a ∈ invCutPf_stab LL l s f ↔ precomp LL l s a f = f := Iff.rfl

theorem invCutPf_exists_pow (ζ₀ ζ : Rs LL l s) : ∃ a, powR LL l s a ζ₀ = ζ := by
  have hN : 0 < l ^ (s + 1) := pos_pow l s
  haveI : NeZero (l ^ (s + 1)) := ⟨hN.ne'⟩
  have h0 : IsPrimitiveRoot (ζ₀ : LL) (l ^ (s + 1)) := (mem_primitiveRoots hN).1 ζ₀.2
  have h1 : IsPrimitiveRoot (ζ : LL) (l ^ (s + 1)) := (mem_primitiveRoots hN).1 ζ.2
  obtain ⟨i, hi, hζ⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime (l ^ (s + 1)) := (h0.pow_iff_coprime hN i).1 (by rw [hζ]; exact h1)
  refine ⟨ZMod.unitOfCoprime i hcop, Subtype.ext ?_⟩
  show (ζ₀ : LL) ^ ((ZMod.unitOfCoprime i hcop : ZMod (l ^ (s + 1)))).val = ζ
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hζ]

end Part1

theorem precompConst : PrecompConst := by
  intro LL _ l _ s S hS f hf
  by_cases h : Nonempty (Rs LL l s)
  · obtain ⟨ζ₀⟩ := h
    refine ⟨f ζ₀, fun ζ => ?_⟩
    have hle : Subgroup.closure S ≤ invCutPf_stab LL l s f :=
      (Subgroup.closure_le _).2 fun a ha => (invCutPf_mem_stab LL l s f a).2 (hf a ha)
    obtain ⟨a, rfl⟩ := invCutPf_exists_pow LL l s ζ₀ ζ
    have ha : precomp LL l s a f = f :=
      (invCutPf_mem_stab LL l s f a).1 (hle (by rw [hS]; exact Subgroup.mem_top a))
    exact (precomp_apply LL l s a f ζ₀).symm.trans (congrFun ha ζ₀)
  · exact ⟨0, fun ζ => (h ⟨ζ⟩).elim⟩

section Part2

variable {l : ℕ} [Fact l.Prime]

theorem invCutPf_toZModPow_eq_zero {n : ℕ} {z : ℤ_[l]} :
    PadicInt.toZModPow n z = 0 ↔ z ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]

theorem invCutPf_eq_one_iff {k : ℕ} {z : ℤ_[l]} :
    PadicInt.toZModPow k z = 1 ↔ z - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
  rw [← invCutPf_toZModPow_eq_zero, map_sub, map_one, sub_eq_zero]

theorem invCutPf_lt_one_iff {z : ℤ_[l]} : ‖z‖ < 1 ↔ PadicInt.toZModPow 1 z = 0 := by
  rw [PadicInt.norm_lt_one_iff_dvd, invCutPf_toZModPow_eq_zero, pow_one, Ideal.mem_span_singleton]

theorem invCutPf_norm_eq_one {z : ℤ_[l]} (h : PadicInt.toZModPow 1 z ≠ 0) : ‖z‖ = 1 := by
  rcases (PadicInt.norm_le_one z).lt_or_eq with h1 | h1
  · exact absurd (invCutPf_lt_one_iff.1 h1) h
  · exact h1

theorem invCutPf_congr {z w : ℤ_[l]} (h : ‖z - w‖ < 1) :
    PadicInt.toZModPow 1 z = PadicInt.toZModPow 1 w := by
  rw [← sub_eq_zero, ← map_sub]
  exact invCutPf_lt_one_iff.1 h

theorem invCutPf_lower {k n : ℕ} (h : k ≤ n) {z w : ℤ_[l]}
    (e : PadicInt.toZModPow n z = PadicInt.toZModPow n w) :
    PadicInt.toZModPow k z = PadicInt.toZModPow k w := by
  rw [← PadicInt.zmod_cast_comp_toZModPow k n h, RingHom.comp_apply, RingHom.comp_apply, e]

theorem invCutPf_le (s : ℕ) : 0 + 1 ≤ s + 1 := by omega

def invCutPf_rho (s : ℕ) : (ZMod (l ^ (s + 1)))ˣ →* (ZMod (l ^ (0 + 1)))ˣ :=
  ZMod.unitsMap (pow_dvd_pow l (invCutPf_le s))

theorem invCutPf_rho_red (s : ℕ) (x : ℤ_[l]ˣ) : invCutPf_rho s (redU l s x) = redU l 0 x :=
  Units.ext (RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow (0 + 1) (s + 1) (invCutPf_le s))
    (x : ℤ_[l]))

theorem reduction_zero_of_principal_unit (u : ℤ_[l]ˣ) (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) :
    redU l 0 u = 1 := by
  apply Units.ext
  show PadicInt.toZModPow (0 + 1) (u : ℤ_[l]) = 1
  rw [invCutPf_eq_one_iff, zero_add, pow_one]
  exact h1

theorem invCutPf_teich (x : (ZMod (l ^ 1))ˣ) : ∃ d : DeltaT l, redU l 0 d.1 = x := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], a = (((x : ZMod (l ^ 1)).val : ℕ) : ℤ_[l]) := ⟨_, rfl⟩
  have hxa : PadicInt.toZModPow 1 a = x := by
    rw [ha, map_natCast, ZMod.natCast_zmod_val]
  have hanorm : ‖a‖ = 1 := invCutPf_norm_eq_one (by rw [hxa]; exact x.ne_zero)
  have htot : Nat.totient (l ^ 1) = l - 1 := by rw [pow_one, Nat.totient_prime hl]
  have hferm : (x : ZMod (l ^ 1)) ^ (l - 1) = 1 := by
    have h := pow_card_eq_one (x := x)
    rw [ZMod.card_units_eq_totient, htot] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hl1norm : ‖((l - 1 : ℕ) : ℤ_[l])‖ = 1 := by
    apply invCutPf_norm_eq_one
    rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by have := hl.two_le; omega) hd
    rw [pow_one] at this
    have := hl.two_le
    omega
  have hFa : ‖Polynomial.aeval a ((Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))‖ < 1 := by
    rw [invCutPf_lt_one_iff]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, hxa, hferm, sub_self]
  have hder : ‖Polynomial.aeval a
      (Polynomial.derivative (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))‖ = 1 := by
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
      sub_zero, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply, norm_mul, norm_pow, hanorm, one_pow, mul_one]
    exact hl1norm
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))
    (a := a) (by rw [hder, one_pow]; exact hFa)
  rw [hder] at hza
  have hz1 : z ^ (l - 1) = 1 := by
    simpa [sub_eq_zero] using hz
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  have hzu : IsUnit z := IsUnit.of_pow_eq_one hz1 hl1
  refine ⟨⟨hzu.unit, Units.ext (by simpa using hz1)⟩, Units.ext ?_⟩
  show PadicInt.toZModPow 1 z = (x : ZMod (l ^ 1))
  rw [invCutPf_congr hza, hxa]

theorem invCutPf_pow_eq_one_iff (n : ℕ) (u : ℤ_[l]ˣ) (m : ℕ)
    (hmu : ((m : ℕ) : ZMod (l ^ (n + 1))) = PadicInt.toZModPow (n + 1) (u : ℤ_[l])) (hm : 1 ≤ m)
    (e : ℕ) : redU l n u ^ e = 1 ↔ l ^ (n + 1) ∣ m ^ e - 1 := by
  rw [← Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hm), ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow,
    Nat.cast_one, hmu, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  exact eq_comm

theorem invCutPf_orderOf (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]ˣ)
    (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])})
    (h2 : (u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) :
    orderOf (redU l s u) = l ^ s := by
  have hl := (Fact.out : l.Prime)
  cases s with
  | zero => rw [pow_zero, orderOf_eq_one_iff]; exact reduction_zero_of_principal_unit u h1
  | succ t =>
    haveI : NeZero (l ^ (t + 1 + 1)) := ⟨(pos_pow l (t + 1)).ne'⟩
    obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = (PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l])).val := ⟨_, rfl⟩
    have hmu : ((m : ℕ) : ZMod (l ^ (t + 1 + 1))) = PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l]) := by
      rw [hm_def, ZMod.natCast_zmod_val]
    have hmu' : PadicInt.toZModPow (t + 1 + 1) ((m : ℕ) : ℤ_[l]) =
        PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l]) := by
      rw [map_natCast, hmu]
    have hk : ∀ k ≤ t + 1 + 1,
        (((m : ℕ) : ZMod (l ^ k)) = 1 ↔ (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ k}) := by
      intro k hk
      rw [← map_natCast (PadicInt.toZModPow (p := l) k) m, invCutPf_lower hk hmu', invCutPf_eq_one_iff]
    have hl2' : 1 < l ^ 2 := Nat.one_lt_pow two_ne_zero hl.one_lt
    have hA : m % l = 1 := by
      have := (hk 1 (by omega)).2 (by rw [pow_one]; exact h1)
      rw [← Nat.cast_one (R := ZMod (l ^ 1)), ZMod.natCast_eq_natCast_iff', pow_one,
        Nat.mod_eq_of_lt hl.one_lt] at this
      exact this
    have hB : m % l ^ 2 ≠ 1 := by
      intro hc
      apply h2
      apply (hk 2 (by omega)).1
      rw [← Nat.cast_one (R := ZMod (l ^ 2)), ZMod.natCast_eq_natCast_iff', hc, Nat.mod_eq_of_lt hl2']
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge 1 m with h | h
      · exact h
      · interval_cases m
        · simp at hA
        · exact absurd (Nat.mod_eq_of_lt hl2') hB
    have hdvd1 : l ∣ m - 1 := (Nat.modEq_iff_dvd' hm1.le).1 (by
      show 1 % l = m % l
      rw [hA, Nat.mod_eq_of_lt hl.one_lt])
    have hndvd2 : ¬ l ^ 2 ∣ m - 1 := fun hd => hB (by
      have : 1 % l ^ 2 = m % l ^ 2 := (Nat.modEq_iff_dvd' hm1.le).2 hd
      rw [← this, Nat.mod_eq_of_lt hl2'])
    have hndvd : ¬ l ∣ m := by
      rw [Nat.dvd_iff_mod_eq_zero, hA]; exact one_ne_zero
    have hm0 : m - 1 ≠ 0 := by omega
    have hv1 : padicValNat l (m - 1) = 1 := by
      have a1 : 1 ≤ padicValNat l (m - 1) := (padicValNat_dvd_iff_le hm0).1 (by rw [pow_one]; exact hdvd1)
      have a2 : ¬ 2 ≤ padicValNat l (m - 1) := fun h => hndvd2 ((padicValNat_dvd_iff_le hm0).2 h)
      omega
    have hodd : Odd l := hl.odd_of_ne_two hl2
    have hv : ∀ j : ℕ, padicValNat l (m ^ (l ^ j) - 1) = 1 + j := by
      intro j
      have := padicValNat.pow_sub_pow hodd hm1 hdvd1 hndvd (pow_ne_zero j hl.ne_zero)
      rw [one_pow] at this
      rw [this, hv1, padicValNat.prime_pow]
    have hne : ∀ j : ℕ, m ^ (l ^ j) - 1 ≠ 0 := by
      intro j
      have := Nat.one_lt_pow (pow_ne_zero j hl.ne_zero) hm1
      omega
    apply orderOf_eq_prime_pow
    · rw [invCutPf_pow_eq_one_iff (t + 1) u m hmu hm1.le, padicValNat_dvd_iff_le (hne t), hv]
      omega
    · rw [invCutPf_pow_eq_one_iff (t + 1) u m hmu hm1.le, padicValNat_dvd_iff_le (hne (t + 1)), hv]
      omega

theorem invCutPf_card_ker (s : ℕ) : Nat.card (invCutPf_rho (l := l) s).ker = l ^ s := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ (s + 1)) := ⟨(pos_pow l s).ne'⟩
  haveI : NeZero (l ^ (0 + 1)) := ⟨(pos_pow l 0).ne'⟩
  have hsurj : Function.Surjective (invCutPf_rho (l := l) s) :=
    ZMod.unitsMap_surjective (pow_dvd_pow l (invCutPf_le s))
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (invCutPf_rho (l := l) s).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (s + 1)))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (0 + 1)))ˣ),
    ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl,
    Nat.totient_prime_pow_succ hl, pow_zero, one_mul] at e1
  have hpos : 0 < l - 1 := by have := hl.two_le; omega
  exact Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans (mul_comm _ _))

theorem invCutPf_ker_eq (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]ˣ)
    (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])})
    (h2 : (u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) :
    (invCutPf_rho (l := l) s).ker = Subgroup.zpowers (redU l s u) := by
  haveI : NeZero (l ^ (s + 1)) := ⟨(pos_pow l s).ne'⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, invCutPf_rho_red, reduction_zero_of_principal_unit u h1]
  · rw [Nat.card_zpowers, invCutPf_orderOf hl2 s u h1 h2, invCutPf_card_ker]

end Part2

theorem genUnits : GenUnits := by
  intro l _ hl2 s u h1 h2
  rw [eq_top_iff]
  intro g _
  obtain ⟨d, hd⟩ := invCutPf_teich (l := l) (invCutPf_rho s g)
  have hk : g * (redU l s d.1)⁻¹ ∈ (invCutPf_rho (l := l) s).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, invCutPf_rho_red, hd, mul_inv_cancel]
  rw [invCutPf_ker_eq hl2 s u h1 h2] at hk
  have hu : redU l s u ∈ Subgroup.closure
      (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hdm : redU l s d.1 ∈ Subgroup.closure
      (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨d, rfl⟩)
  have hz := (Subgroup.zpowers_le.2 hu) hk
  simpa using Subgroup.mul_mem _ hz hdm

end Formalism.MainNotions.UnusedSlot80.InvCutPfL

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def levelBasicsOfRingCondition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hGen : GenUnitsC) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
    (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ) :
    LevBasics ((HW l).W K 1 LL h.2.2) a s := by
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI hpF : Fact ((D.loc l).PD K).p.Prime := ⟨by rw [e]; exact Fact.out⟩
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := OLC.complete_max LL
  haveI : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  letI : Algebra ℤ_[((D.loc l).PD K).p] ↥(OL LL) :=
    ((algebraMap ℤ_[l] ↥(OL LL)).comp (castZp e)).toAlgebra
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := h9
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL h.2.2) :=
    Formalism.MainNotions.UnusedSlot80.ring_condition_uniformizer_polynomial D HW F hP9 l K LL h
  have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [e]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
  have hZinj : Function.Injective (algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL)) :=
    (Formalism.MainNotions.LiftingTheory.zl_inj_O LL).comp (castZp_inj e)
  have hχ : ∀ g : ((HW l).W K 1 LL h.2.2).Gam, ∃ z : ℤ_[((D.loc l).PD K).p]ˣ,
      algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL) (z : ℤ_[((D.loc l).PD K).p]) =
        (((HW l).W K 1 LL h.2.2).χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨z, hz⟩ := Formalism.MainNotions.LiftingTheory.chi_zl (P := D.loc l) (H := HW l) h.2.2 g
    refine ⟨Units.map (castZp e.symm).toMonoidHom z, ?_⟩
    show algebraMap ℤ_[l] ↥(OL LL) (castZp e (castZp e.symm (z : ℤ_[l]))) = _
    rw [castZp_symm, hz]
  have hγz : ∃ z0 : ℤ_[((D.loc l).PD K).p]ˣ,
      algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL) (z0 : ℤ_[((D.loc l).PD K).p]) =
        (((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) ∧
      ((z0 : ℤ_[((D.loc l).PD K).p]) - 1).valuation = 1 := by
    obtain ⟨z, hz, hv⟩ := Formalism.MainNotions.LiftingTheory.gam_zl (P := D.loc l) (H := HW l) h.2.2
    refine ⟨Units.map (castZp e.symm).toMonoidHom z, ?_, ?_⟩
    · show algebraMap ℤ_[l] ↥(OL LL) (castZp e (castZp e.symm (z : ℤ_[l]))) = _
      rw [castZp_symm, hz]
    · have : ((Units.map (castZp e.symm).toMonoidHom z : ℤ_[((D.loc l).PD K).p]ˣ) :
          ℤ_[((D.loc l).PD K).p]) - 1 = castZp e.symm ((z : ℤ_[l]) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, castZp_val, hv]
  have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F hP9 l K LL h
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [e]; exact h.2.1
  letI : Algebra ↥(OL LL) (AlgebraicClosure ↥LL.1) :=
    ((algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).comp (algebraMap ↥(OL LL) ↥LL.1)).toAlgebra
  have hinjF : Function.Injective (algebraMap ↥(OL LL) (AlgebraicClosure ↥LL.1)) :=
    (algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).injective.comp Subtype.val_injective
  haveI : CharZero (AlgebraicClosure ↥LL.1) :=
    charZero_of_injective_algebraMap (algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).injective
  exact levBasics_of ((HW l).W K 1 LL h.2.2) hlm (AlgebraicClosure ↥LL.1) hR hinjF hZinj hχ hγz
    (by rw [hcard, e]) hp2 hGen a s

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def levBasics_conv {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {PD : PeriodData G Qp K₀ K B BdR}
    {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (h : Formalism.MainNotions.N.Pv.LocalLengthBound.LB.LevBasics W a s) :
    LevBasics W a s :=
  ⟨h.F, h.fF, h.algOF, h.inj, h.hp, h.root, h.ev, h.ev_O, h.ev_letE, h.ev_π, h.ev_ps, h.ev_pt, h.σ,
    h.ev_γ, h.gen⟩

theorem invLevCore_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hRat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ) (hB : LevBasics ((HW l).W K 1 LL h.2.2) a s),
      LevRat ((HW l).W K 1 LL h.2.2) a s hB.F hB.ev) :
    AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have hR : ToolsR.RingP ((HW l).W K 1 LL hCA.2.2) := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hCA.2.2) := tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hCA.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have hB : ∀ (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ),
      LevBasics ((HW l).W K 1 LL hCA.2.2) a s := fun a s =>
    levBasics_conv (Formalism.MainNotions.N.Pv.LocalLengthBound.LB.levelBasicsOfRingCondition D HW F h9
      Formalism.MainNotions.UnusedSlot80.InvCutPfL.genUnits l K LL hCA a s)
  exact invLevCore_of_parts ((HW l).W K 1 LL hCA.2.2) hR.1 hB
    (fun a s => levDiv_of ((HW l).W K 1 LL hCA.2.2) hR hT hpu a s (hB a s))
    (fun a s => hRat l K LL hCA a s (hB a s)) Formalism.MainNotions.UnusedSlot80.InvCutPfL.precompConst

end Formalism.MainNotions.UnusedSlot80.InvW
end
end
end

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section LevRatPf

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem exists_dvd_pow_of_not_isUnit_dvr [IsDomain O] [IsDiscreteValuationRing O] (p : O) (hp0 : p ≠ 0) (hpu : ¬ IsUnit p)
    {y : O} (hy : y ≠ 0) : ∃ (κ : ℕ) (z : O), p ^ κ = y * z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  obtain ⟨e, u', hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hpe, h, pow_zero, mul_one]; exact u'.isUnit) hpu
    · exact h
  refine ⟨m, ((u⁻¹ : Oˣ) : O) * (u' : O) ^ m * ϖ ^ (e * m - m), ?_⟩
  have hm : m ≤ e * m := Nat.le_mul_of_pos_left m he
  rw [hpe, hyu, mul_pow, ← pow_mul]
  have e1 : ϖ ^ (e * m) = ϖ ^ m * ϖ ^ (e * m - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  rw [e1]
  have e2 : ((u : O) * ((u⁻¹ : Oˣ) : O)) = 1 := Units.mul_inv u
  linear_combination (-((u' : O) ^ m * ϖ ^ m * ϖ ^ (e * m - m))) * e2

variable [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem levRatPf_ev (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) (g : LetA O n) :
    ∃ r : Polynomial O, r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) ∧
      ∀ ζ : Rs hB.F PD.p s, hB.ev ζ g = Polynomial.aeval ((ζ : hB.F) - 1) r := by
  obtain ⟨H, r, hdeg, heq⟩ := wdiv_ps W hR hT hpu a s (g a)
  refine ⟨r, hdeg, fun ζ => ?_⟩
  set wH : LetA O n := Pi.single a H with hwH
  have hRr : (fun _ : ZMod n => (r : PowerSeries O)) = Polynomial.aeval (letπ : LetA O n) r := by
    funext i
    show (r : PowerSeries O) = Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i (Polynomial.aeval letπ r)
    rw [← Polynomial.aeval_algHom_apply]
    exact (aeval_X_coe r).symm
  have key : (letE a : LetA O n) * g = ps W s * wH + letE a * Polynomial.aeval (letπ : LetA O n) r := by
    rw [← hRr]
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_same, one_mul, heq]
    · simp [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_of_ne hi]
  have h1 := congrArg (hB.ev ζ) key
  rw [map_mul, hB.ev_letE, one_mul, map_add, map_mul, hB.ev_ps, zero_mul, zero_add, map_mul,
    hB.ev_letE, one_mul, ev_aeval hB] at h1
  exact h1

theorem levRat_of [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) (hR : ToolsR.RingP W)
    (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ)
    (hB : LevBasics W a s) : LevRat W a s hB.F hB.ev := by
  intro g _ d _ hd c hc
  obtain ⟨rg, hgdeg, hg⟩ := levRatPf_ev W hR hT hpu a s hB g
  obtain ⟨rd, hddeg, hdv⟩ := levRatPf_ev W hR hT hpu a s hB d
  have hN : ∀ r : Polynomial O, r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) →
      (r.map (algebraMap O hB.F)).natDegree < (PD.p - 1) * PD.p ^ s := by
    intro r hr
    have hNpos : 0 < (PD.p - 1) * PD.p ^ s :=
      Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
    refine lt_of_le_of_lt Polynomial.natDegree_map_le ?_
    by_cases h0 : r = 0
    · rw [h0, Polynomial.natDegree_zero]; exact hNpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hr
  set R : Polynomial hB.F := rg.map (algebraMap O hB.F) - Polynomial.C c * rd.map (algebraMap O hB.F) with hRdef
  have hR0 : R = 0 := by
    refine poly_eq_zero hB R ?_ ?_
    · refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt (hN rg hgdeg) ?_)
      exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (hN rd hddeg)
    · intro ζ
      rw [hRdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
        Polynomial.eval_map, ← Polynomial.aeval_def, ← Polynomial.aeval_def, ← hg ζ, ← hdv ζ, hc ζ, sub_self]
  have hne : Nonempty (Rs hB.F PD.p s) := by
    rw [← Fintype.card_pos_iff, card_Rs hB]
    exact Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
  obtain ⟨ζ₀⟩ := hne
  have hrd : rd ≠ 0 := by
    intro h
    apply hd ζ₀
    rw [hdv ζ₀, h, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, rd.coeff k ≠ 0 := by
    by_contra h
    push Not at h
    exact hrd (Polynomial.ext fun k => by simpa using h k)
  have hck : algebraMap O hB.F (rg.coeff k) = c * algebraMap O hB.F (rd.coeff k) := by
    have := congrArg (fun P : Polynomial hB.F => P.coeff k) hR0
    simp only [hRdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_zero] at this
    exact sub_eq_zero.1 this
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hB.hp
    rw [← map_natCast (algebraMap O hB.F), h, map_zero]
  obtain ⟨κ, z, hz⟩ := exists_dvd_pow_of_not_isUnit_dvr ((PD.p : ℕ) : O) hp0 hpu hk
  refine ⟨κ, z * rg.coeff k, ?_⟩
  rw [map_mul, hck, ← map_natCast (algebraMap O hB.F), ← map_pow, hz, map_mul]
  ring

end LevRatPf

end Formalism.MainNotions.UnusedSlot80.InvW
end
end

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.KWP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

abbrev γL : Module.End O W.EE := (W.γE W.gam).toLinearMap

def fac (e : ℕ) (i : ℤ) : Polynomial O :=
  Polynomial.X ^ (PD.p ^ e) - Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ e) : Oˣ) : O)

theorem aeval_mul_apply (P Q : Polynomial O) (f : W.EE) :
    Polynomial.aeval (γL W) (P * Q) f = Polynomial.aeval (γL W) P (Polynomial.aeval (γL W) Q f) := by
  rw [map_mul]; rfl

theorem raise (hKL : KillerLevCore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (hS : PsStable W) {a : ZMod n} {e : ℕ}
    {α : ℕ → ℤ} {f : W.EE} (hf : InId W a e α f) {s : ℕ} (hs : s < e) (N : ℕ) (T : Finset ℤ)
    (hT : Finset.Ico (α s) (α s + N) ⊆ T) :
    ∃ κ : ℕ, InId W a e (Function.update α s (α s + N))
      (lE W κ * Polynomial.aeval (γL W) (∏ i ∈ T, fac W e i) f) := by
  have hprod : (∏ i ∈ T, fac W e i) = (∏ i ∈ Finset.Ico (α s) (α s + N), fac W e i) *
      ∏ i ∈ T \ Finset.Ico (α s) (α s + N), fac W e i := by
    rw [mul_comm, Finset.prod_sdiff hT]
  have hg := Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS (∏ i ∈ T \ Finset.Ico (α s) (α s + N), fac W e i) f hf
  obtain ⟨κ, hκ⟩ := ((hKL hCA e ∅).2 a α s hs _ hg).2.2 N
  exact ⟨κ, by rw [hprod, aeval_mul_apply]; exact hκ⟩

theorem inFr_add {a : ZMod n} {num den : LetA O n} {f g : W.EE} (hf : InFr W a num den f)
    (hg : InFr W a num den g) : InFr W a num den (f + g) := by
  unfold InFr at *
  obtain ⟨u, hu, e1⟩ := hf
  obtain ⟨u', hu', e2⟩ := hg
  exact ⟨u + u', add_mem hu hu', by rw [mul_add, e1, e2, mul_add, map_add]⟩

theorem inFr_zero (a : ZMod n) (num den : LetA O n) : InFr W a num den 0 := by
  unfold InFr
  exact ⟨0, zero_mem _, by simp⟩

theorem inFr_num_drop {a : ZMod n} {num x den : LetA O n} {f : W.EE} (hx : x ∈ W.AΔ)
    (h : InFr W a (num * x) den f) : InFr W a num den f := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  exact ⟨x * u, mul_mem hx hu, by rw [e]; congr 1; ring⟩

theorem inFr_den_mul {a : ZMod n} {num den d : LetA O n} {f : W.EE} (hd : d ∈ W.AΔ)
    (h : InFr W a num den f) : InFr W a num (den * d) f := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  refine ⟨u * d, mul_mem hu hd, ?_⟩
  rw [map_mul, mul_right_comm, e, ← map_mul]
  congr 1; ring

theorem inFr_lE {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) (κ : ℕ) :
    InFr W a num den (lE W κ * f) := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  refine ⟨u * ((PD.p : ℕ) : LetA O n) ^ κ, mul_mem hu (pow_mem (natCast_mem _ _) _), ?_⟩
  have hl : lE W κ = algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ) := by
    unfold lE; rw [map_pow, map_natCast]
  rw [hl, mul_left_comm, e, ← map_mul]
  congr 1; ring

theorem inFr_congr {a : ZMod n} {num num' den den' : LetA O n} {f : W.EE} (hn : num = num')
    (hd : den = den') (h : InFr W a num den f) : InFr W a num' den' f := by
  subst hn hd; exact h


theorem prod_ps_mem (hπ : W.π₀ ∈ W.AΔ) (e : ℕ) (d : ℕ → ℕ) :
    (∏ s ∈ Finset.range e, ps W s ^ d s) ∈ W.AΔ := by
  exact prod_mem fun s _ => pow_mem (Formalism.MainNotions.UnusedSlot80.KL.ps_mem (W := W) hπ s) _

theorem prod_ps_mem' (hπ : W.π₀ ∈ W.AΔ) (S : Finset ℕ) (d : ℕ → ℕ) :
    (∏ s ∈ S, ps W s ^ d s) ∈ W.AΔ := by
  exact prod_mem fun s _ => pow_mem (Formalism.MainNotions.UnusedSlot80.KL.ps_mem (W := W) hπ s) _

theorem level_form (hπ : W.π₀ ∈ W.AΔ) {a : ZMod n} {e s : ℕ} (hs : s ∈ Finset.range e) (α : ℕ → ℤ) (x : ℤ)
    (H : ℕ → ℕ) (hα : ∀ t ∈ (Finset.range e).erase s, -(H t : ℤ) ≤ α t) {g : W.EE}
    (hg : InId W a e (Function.update α s x) g) :
    InFr W a (ps W s ^ x.toNat) (ps W s ^ (-x).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ H t) g := by
  simp only [InId] at hg
  rw [← Finset.mul_prod_erase _ _ hs, ← Finset.mul_prod_erase _ _ hs] at hg
  simp only [Function.update_apply, if_pos rfl] at hg
  have e1 : (∏ t ∈ (Finset.range e).erase s, ps W t ^ (if t = s then x else α t).toNat) =
      ∏ t ∈ (Finset.range e).erase s, ps W t ^ (α t).toNat :=
    Finset.prod_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]
  have e2 : (∏ t ∈ (Finset.range e).erase s, ps W t ^ (-(if t = s then x else α t)).toNat) =
      ∏ t ∈ (Finset.range e).erase s, ps W t ^ (-α t).toNat :=
    Finset.prod_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]
  rw [e1, e2] at hg
  have h1 := inFr_num_drop W (prod_ps_mem' W hπ _ _) hg
  have h2 := inFr_den_mul W (prod_ps_mem' W hπ ((Finset.range e).erase s) (fun t => H t - (-α t).toNat)) h1
  refine inFr_congr W rfl ?_ h2
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [← pow_add]
  congr 1
  have := hα t ht
  show (-α t).toNat + (H t - (-α t).toNat) = H t
  omega

section ThetaShiftProofs

open Formalism.MainNotions.LocalTheoryWindows

def mmF (A : ArcP n) : LT → ℕ
  | .thin => A.G₀
  | .up b => b + A.S
  | .down _ => 0

def dnF : LT → ℕ
  | .thin => 0
  | .up _ => 0
  | .down b => b

def nnNF (A : ArcP n) : LT → ℕ
  | .thin => A.G₀
  | .up _ => 0
  | .down b => b + A.S

def nnDF : LT → ℕ
  | .thin => 0
  | .up b => b
  | .down _ => 0

theorem mmDen_eq (A : ArcP n) (c : ZMod n) :
    mmDen W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ mmF A (A.ty (c - (s : ZMod n))) := by
  unfold mmDen prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem downB_eq (A : ArcP n) (c : ZMod n) :
    downB W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ dnF (A.ty (c - (s : ZMod n))) := by
  unfold downB prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem nnNum_eq (A : ArcP n) (c : ZMod n) :
    nnNum W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ nnNF A (A.ty (c - (s : ZMod n))) := by
  unfold nnNum prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem nnDen_eq (A : ArcP n) (c : ZMod n) :
    nnDen W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ nnDF (A.ty (c - (s : ZMod n))) := by
  unfold nnDen prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem letter_after (c : ZMod n) (e s : ℕ) (hs : s ≤ e) :
    c - (s : ZMod n) = (c - (e : ZMod n)) + ((e - s : ℕ) : ZMod n) := by
  rw [Nat.cast_sub hs]; ring

theorem thick_near_cut (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ}
    (hs : s < A.len c) (hj : A.len c - s ≤ A.j) (hth : (A.ty (c - (s : ZMod n))).thick) :
    (A.ty (c - (s : ZMod n))).size + A.S ≤ A.G₀ := by
  obtain ⟨-, -, hcuts, -, -, -, -, -, hlast⟩ := hOK
  obtain ⟨-, -, hc', -⟩ := hcuts c hc
  have hk1 : 1 ≤ A.len c - s := by omega
  have heq : c - (s : ZMod n) = (c - ((A.len c : ℕ) : ZMod n)) + ((A.len c - s : ℕ) : ZMod n) :=
    letter_after c (A.len c) s hs.le
  rcases hlast with h | ⟨hj', -, h⟩
  · have h0 := h _ hc' (A.len c - s) hk1 hj
    rw [heq, h0] at hth
    exact absurd hth (by decide)
  · have hk : A.len c - s = 1 := by omega
    rw [heq, hk, Nat.cast_one]
    exact h _ hc'

theorem thick_le_H (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ}
    (hs : s < A.len c) (hth : (A.ty (c - (s : ZMod n))).thick) :
    (A.ty (c - (s : ZMod n))).size + A.S ≤ A.Hs c (A.len c) s := by
  unfold ArcP.Hs
  split_ifs with hc'
  · rcases hc' with h | h
    · rw [h] at hth; exact absurd hth (by decide)
    · exact thick_near_cut A hOK hc hs h hth
  · exact hOK.2.2.2.2.2.2.2.1 _ hth

theorem G_le_H (A : ArcP n) (hOK : A.OK) (c : ZMod n) (s : ℕ) : A.G₀ ≤ A.Hs c (A.len c) s := by
  unfold ArcP.Hs
  split_ifs
  · exact le_rfl
  · exact hOK.2.2.2.2.2.1

theorem mmF_le_H (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ} (hs : s < A.len c) :
    mmF A (A.ty (c - (s : ZMod n))) ≤ A.Hs c (A.len c) s := by
  have hG := G_le_H A hOK c s
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin => exact hG
  | up b =>
    have h' := thick_le_H A hOK hc hs (by rw [hty]; rfl)
    rw [hty] at h'
    exact h'
  | down b => exact Nat.zero_le _

theorem nnNF_le_H (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ} (hs : s < A.len c) :
    nnNF A (A.ty (c - (s : ZMod n))) ≤ A.Hs c (A.len c) s := by
  have hG := G_le_H A hOK c s
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin => exact hG
  | up b => exact Nat.zero_le _
  | down b =>
    have h' := thick_le_H A hOK hc hs (by rw [hty]; rfl)
    rw [hty] at h'
    exact h'

theorem nnDF_le_H (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ} (hs : s < A.len c) :
    nnDF (A.ty (c - (s : ZMod n))) ≤ A.Hs c (A.len c) s := by
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin => exact Nat.zero_le _
  | up b =>
    have h' := thick_le_H A hOK hc hs (by rw [hty]; rfl)
    rw [hty] at h'
    exact le_trans (Nat.le_add_right b A.S) h'
  | down b => exact Nat.zero_le _

theorem size_pos (A : ArcP n) (hOK : A.OK) (i : ZMod n) (hth : (A.ty i).thick) : 1 ≤ (A.ty i).size := by
  have hok := hOK.2.2.2.2.1 i
  cases hty : A.ty i with
  | thin => rw [hty] at hth; exact absurd hth (by decide)
  | up b =>
    rw [hty] at hok
    have h' : A.η < b := hok
    show 1 ≤ b
    omega
  | down b =>
    rw [hty] at hok
    have h' : A.η < b := hok
    show 1 ≤ b
    omega

end ThetaShiftProofs

theorem toNat_sub_of (a d : ℕ) (h : a = 0 ∨ d = 0) :
    ((a : ℤ) - d).toNat = a ∧ (-((a : ℤ) - d)).toNat = d := by
  rcases h with h | h <;> subst h <;> constructor <;> omega

theorem inId_of_inFr {a : ZMod n} (e : ℕ) (α δ : ℕ → ℕ) (h : ∀ s ∈ Finset.range e, α s = 0 ∨ δ s = 0)
    {f : W.EE} (hf : InFr W a (∏ s ∈ Finset.range e, ps W s ^ α s) (∏ s ∈ Finset.range e, ps W s ^ δ s) f) :
    InId W a e (fun s => (α s : ℤ) - δ s) f := by
  simp only [InId]
  refine inFr_congr W ?_ ?_ hf
  · exact Finset.prod_congr rfl fun s hs => by rw [(toNat_sub_of (α s) (δ s) (h s hs)).1]
  · exact Finset.prod_congr rfl fun s hs => by rw [(toNat_sub_of (α s) (δ s) (h s hs)).2]

theorem inFr_of_inId {a : ZMod n} (e : ℕ) (α δ : ℕ → ℕ) (h : ∀ s ∈ Finset.range e, α s = 0 ∨ δ s = 0)
    {f : W.EE} (hf : InId W a e (fun s => (α s : ℤ) - δ s) f) :
    InFr W a (∏ s ∈ Finset.range e, ps W s ^ α s) (∏ s ∈ Finset.range e, ps W s ^ δ s) f := by
  simp only [InId] at hf
  refine inFr_congr W ?_ ?_ hf
  · exact Finset.prod_congr rfl fun s hs => by rw [(toNat_sub_of (α s) (δ s) (h s hs)).1]
  · exact Finset.prod_congr rfl fun s hs => by rw [(toNat_sub_of (α s) (δ s) (h s hs)).2]


section Pi0

open Formalism.MainNotions.UnusedSlot80.ToolsR Formalism.MainNotions.WachCoordinates

theorem exists_gamma_pi0_eq_pi0_mul [IsDomain O] [NeZero n] (hR : RingP W) : ∃ z ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * z := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.2.1
  have e : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      qP W := by
    funext i; simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qP, LocWach.π₀]
  rw [e] at hw
  have hp0 := Formalism.MainNotions.WachCoordinates.Br.p_ne_zero_O W
  have hπ : W.π₀ ∈ W.AΔ := hR.1
  have hq : qP W ∈ W.AΔ := qP_AΔ hR
  have hc : W.π₀ * qP W ∈ W.AΔ := Subalgebra.mul_mem _ hπ hq
  have hc0 : ∀ i, (W.π₀ * qP W) i ≠ 0 := fun i => by
    show W.π₀₁ * qP W i ≠ 0
    exact mul_ne_zero (π₀₁_ne hR) (q_component_ne_zero' hR hp0 i)
  have hwΔ : (w : LetA O n) ∈ W.AΔ := by
    refine cancel_AΔ hc hc0 ?_
    have : W.π₀ * qP W * (w : LetA O n) = W.γA W.gam W.π₀ - W.π₀ := by rw [hw]; ring
    rw [this]
    exact Subalgebra.sub_mem _ (γA_mem W _ hπ) hπ
  refine ⟨1 + qP W * (w : LetA O n), Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ hq hwΔ), ?_⟩
  linear_combination hw

def InIdπ (a : ZMod n) (e : ℕ) (α : ℕ → ℤ) (f : W.EE) : Prop :=
  ∃ u ∈ W.AΔ, ιE (denI W e α) * f = ιE (letE a * numI W e α * (W.π₀ * u))

theorem inIdπ_γ [IsDomain O] [NeZero n] (hR : RingP W) (hS : PsStable W) {a : ZMod n} {e : ℕ}
    {α : ℕ → ℤ} {f : W.EE} (hf : InIdπ W a e α f) : InIdπ W a e α (W.γE W.gam f) := by
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨z, hz, hγπ⟩ := exists_gamma_pi0_eq_pi0_mul W hR
  choose r hr r' hr' hrr hσ using hS
  have h := Formalism.MainNotions.UnusedSlot80.KL.transport W (W.γA W.gam) (W.γE W.gam) (fun x => W.γE_ext _ x)
    (Formalism.MainNotions.UnusedSlot80.KL.γA_letE W _) r r' hrr hσ hfu
  refine ⟨(∏ t ∈ Finset.range e, r' t ^ (-(α t)).toNat) * (∏ t ∈ Finset.range e, r t ^ (α t).toNat) *
    (z * W.γA W.gam u), ?_, ?_⟩
  · refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) (Subalgebra.mul_mem _ hz (γA_mem W _ hu))
    · exact Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (hr' t) _
    · exact Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (hr t) _
  · refine h.trans ?_
    rw [show W.γA W.gam (W.π₀ * u) = W.γA W.gam W.π₀ * W.γA W.gam u from map_mul _ _ _, hγπ]
    congr 1; ring

theorem inIdπ_add {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f g : W.EE} (hf : InIdπ W a e α f)
    (hg : InIdπ W a e α g) : InIdπ W a e α (f + g) := by
  unfold InIdπ at *
  obtain ⟨u, hu, e1⟩ := hf
  obtain ⟨u', hu', e2⟩ := hg
  exact ⟨u + u', add_mem hu hu', by rw [mul_add, e1, e2, ← map_add]; congr 1; ring⟩

theorem inIdπ_smul {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f : W.EE} (hf : InIdπ W a e α f) (c : O) :
    InIdπ W a e α (c • f) := by
  unfold InIdπ at *
  obtain ⟨u, hu, e⟩ := hf
  refine ⟨u * algebraMap O (LetA O n) c, mul_mem hu (Subalgebra.algebraMap_mem _ c), ?_⟩
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, e, ← map_mul]
  congr 1; ring

theorem inIdπ_aeval [IsDomain O] [NeZero n] (hR : RingP W) (hS : PsStable W) {a : ZMod n} {e : ℕ}
    {α : ℕ → ℤ} (P : Polynomial O) : ∀ f, InIdπ W a e α f → InIdπ W a e α (Polynomial.aeval (γL W) P f) := by
  intro f hf
  induction P using Polynomial.induction_on' generalizing f with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact inIdπ_add W (hp f hf) (hq f hf)
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine inIdπ_smul W ?_ c
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact inIdπ_γ W hR hS ih

end Pi0

section Down

theorem lE_eq_alg (κ : ℕ) : lE W κ = algebraMap O W.EE (((PD.p : ℕ) : O) ^ κ) := by
  unfold lE; rw [map_pow, map_natCast]

theorem γE_lE (κ : ℕ) : W.γE W.gam (lE W κ) = lE W κ := by
  unfold lE; rw [map_pow, map_natCast]

theorem γE_const (c : ZMod n) (x : O) :
    W.γE W.gam (ιE (letE c) * algebraMap O W.EE x) = ιE (letE c) * algebraMap O W.EE x := by
  have h1 := W.γE_ext W.gam (letE c)
  rw [map_mul, h1]
  erw [Formalism.MainNotions.UnusedSlot80.KL.γA_letE W W.gam c]
  rw [AlgHom.commutes]

theorem inFr_neg {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) :
    InFr W a num den (-f) := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  exact ⟨-u, neg_mem hu, by rw [mul_neg, e, ← map_neg]; congr 1; ring⟩

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f g : W.EE} (hf : InFr W a num den f)
    (hg : InFr W a num den g) : InFr W a num den (f - g) := by
  simpa only [sub_eq_add_neg] using inFr_add W hf (inFr_neg W hg)

theorem inFr_smul {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) (c : O) :
    InFr W a num den (c • f) := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  refine ⟨u * algebraMap O (LetA O n) c, mul_mem hu (Subalgebra.algebraMap_mem _ c), ?_⟩
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, e, ← map_mul]
  congr 1; ring

def αk (e s : ℕ) (d : ℕ → ℕ) (k : ℕ) : ℕ → ℤ := fun t => if t = s then (k : ℤ) else -(d t : ℤ)

theorem inId_αk_iff {a : ZMod n} {e s : ℕ} (hs : s ∈ Finset.range e) (d : ℕ → ℕ) (k : ℕ) (y : W.EE) :
    InId W a e (αk e s d k) y ↔
      InFr W a (ps W s ^ k) (∏ t ∈ (Finset.range e).erase s, ps W t ^ d t) y := by
  have hn : (∏ t ∈ Finset.range e, ps W t ^ (αk e s d k t).toNat) = ps W s ^ k := by
    rw [← Finset.mul_prod_erase _ _ hs, Finset.prod_eq_one, mul_one]
    · simp [αk]
    · intro t ht
      have ht' := Finset.ne_of_mem_erase ht
      have h0 : (αk e s d k t).toNat = 0 := by simp only [αk, if_neg ht']; omega
      rw [h0, pow_zero]
  have hd : (∏ t ∈ Finset.range e, ps W t ^ (-(αk e s d k t)).toNat) =
      ∏ t ∈ (Finset.range e).erase s, ps W t ^ d t := by
    rw [← Finset.mul_prod_erase _ _ hs]
    have h1 : (-(αk e s d k s)).toNat = 0 := by
      have h3 : αk e s d k s = k := by simp [αk]
      rw [h3]; omega
    rw [h1, pow_zero, one_mul]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.ne_of_mem_erase ht
    have h2 : (-(αk e s d k t)).toNat = d t := by simp only [αk, if_neg ht']; omega
    rw [h2]
  simp only [InId]
  rw [hn, hd]

theorem update_αk (e s : ℕ) (d : ℕ → ℕ) (k : ℕ) :
    Function.update (αk e s d k) s ((k : ℤ) + 1) = αk e s d (k + 1) := by
  funext t
  by_cases h : t = s <;> simp [Function.update_apply, αk, h]

theorem inFr_pow_mono {a : ZMod n} {s k k' : ℕ} (hk : k ≤ k') {den : LetA O n} {f : W.EE}
    (hπ : W.π₀ ∈ W.AΔ) (h : InFr W a (ps W s ^ k') den f) : InFr W a (ps W s ^ k) den f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add] at h
  exact inFr_num_drop W (pow_mem (Formalism.MainNotions.UnusedSlot80.KL.ps_mem (W := W) hπ s) _) h

theorem div_of_val (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hvp : v (algebraMap O LL ((PD.p : ℕ) : O)) = 1) (c : O) (M : ℕ)
    (hc : v (algebraMap O LL c) = ((M : ℕ) : WithTop ℚ)) :
    ∃ o : O, ((PD.p : ℕ) : O) ^ M = c * o := by
  have hc0 : algebraMap O LL c ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hc
    simp at hc
  have hx : algebraMap O LL ((PD.p : ℕ) : O) ^ M / algebraMap O LL c * algebraMap O LL c =
      algebraMap O LL ((PD.p : ℕ) : O) ^ M := div_mul_cancel₀ _ hc0
  have hvM : v (algebraMap O LL ((PD.p : ℕ) : O) ^ M) = ((M : ℕ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hvp, nsmul_one]
  have key : v (algebraMap O LL ((PD.p : ℕ) : O) ^ M / algebraMap O LL c) + v (algebraMap O LL c) =
      v (algebraMap O LL c) := by
    rw [← AddValuation.map_mul, hx, hvM, hc]
  rw [hc] at key
  have h0 : 0 ≤ v (algebraMap O LL ((PD.p : ℕ) : O) ^ M / algebraMap O LL c) :=
    (WithTop.add_le_add_iff_right (WithTop.natCast_ne_top M)).1 (by rw [zero_add, key])
  obtain ⟨o, ho⟩ := hO2 _ h0
  refine ⟨o, hinj ?_⟩
  rw [map_pow, map_mul, ho, mul_comm, hx]

end Down

section Main

open Formalism.MainNotions.LocalTheoryWindows

theorem ppγ_eq (e : ℕ) (JS : Finset ℤ) (f : W.EE) :
    PPγ W e JS f = Polynomial.aeval (γL W) (∏ i ∈ JS.erase 0, fac W e i)
      (Polynomial.aeval (γL W) (∑ k ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ k) f) := by
  unfold PPγ
  rw [show PPO W e JS = (∏ i ∈ JS.erase 0, fac W e i) *
      ∑ k ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ k from rfl]
  exact aeval_mul_apply W _ _ f

theorem mem_JS_thin (A : ArcP n) {c : ZMod n} {s : ℕ} (hs : s < A.len c)
    (hth : A.ty (c - (s : ZMod n)) = LT.thin) {i : ℤ} (hi1 : -(2 * A.G₀ : ℤ) ≤ i) (hi2 : i ≤ A.G₀) :
    i ∈ A.JS c := by
  unfold ArcP.JS
  apply Finset.mem_union_left
  rw [if_pos ⟨s, hs, hth⟩]
  exact Finset.mem_Icc.2 ⟨hi1, hi2⟩

theorem mem_JS_up (A : ArcP n) {c : ZMod n} {s : ℕ} (hs : s < A.len c) {b : ℕ}
    (hτ : A.ty (c - (s : ZMod n)) = LT.up b) {i : ℤ} (hi : i ∈ Finset.Ico (-(b : ℤ) - A.S) (-(b : ℤ))) :
    i ∈ A.JS c := by
  unfold ArcP.JS
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_range.2 hs, ?_⟩
  rw [hτ]
  exact hi

theorem mem_JS_down (A : ArcP n) {c : ZMod n} {s : ℕ} (hs : s < A.len c) {b : ℕ}
    (hτ : A.ty (c - (s : ZMod n)) = LT.down b) {i : ℤ} (hi : i ∈ Finset.Ico (b : ℤ) ((b : ℤ) + A.S)) :
    i ∈ A.JS c := by
  unfold ArcP.JS
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_range.2 hs, ?_⟩
  rw [hτ]
  exact hi

theorem inId_Lam {A : ArcP n} {c : ZMod n} {e : ℕ} {f : W.EE} (h : InFr W c 1 (abelian₂ W A c e) f) :
    InId W c e (fun s => ((0 : ℕ) : ℤ) - (A.Hs c e s : ℕ)) f := by
  refine inId_of_inFr W e (fun _ => 0) (fun s => A.Hs c e s) (fun s _ => Or.inl rfl) ?_
  simp only [pow_zero, Finset.prod_const_one]
  exact h

theorem inFr_Lam {A : ArcP n} {c : ZMod n} {e : ℕ} {f : W.EE}
    (h : InId W c e (fun s => ((0 : ℕ) : ℤ) - (A.Hs c e s : ℕ)) f) : InFr W c 1 (abelian₂ W A c e) f := by
  have h' := inFr_of_inId W e (fun _ => 0) (fun s => A.Hs c e s) (fun s _ => Or.inl rfl) h
  simp only [pow_zero, Finset.prod_const_one] at h'
  exact h'

private theorem nnDF_le_mmF (A : ArcP n) (τ : Formalism.MainNotions.LocalTheoryWindows.LT) : nnDF τ ≤ mmF A τ := by
  cases τ with
  | thin => exact Nat.zero_le _
  | up b => exact Nat.le_add_right b A.S
  | down b => exact le_rfl

theorem part_b (hKL : KillerLevCore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) (hRAT : Formalism.MainNotions.UnusedSlot80.CutU.RATCore W) (A : ArcP n) (hOK : A.OK) {c : ZMod n}
    (hc : c ∈ A.cuts) {f : W.EE} (h1 : InFr W c 1 (abelian₂ W A c (A.len c)) f)
    (h2 : InFr W c 1 (mmDen W A c) f) :
    InFr W c 1 (nnDen W A c) (PPγ W (A.len c) (A.JS c) f) := by
  obtain ⟨α, hα_def⟩ : ∃ α : ℕ → ℤ,
      α = fun t : ℕ => ((0 : ℕ) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  obtain ⟨E, hE_def⟩ : ∃ E : ℕ → ℤ,
      E = fun t : ℕ => ((0 : ℕ) : ℤ) - (nnDF (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  have hαt : ∀ t : ℕ, α t = ((0 : ℕ) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := fun t => by rw [hα_def]
  have hEt : ∀ t : ℕ, E t = ((0 : ℕ) : ℤ) - (nnDF (A.ty (c - (t : ZMod n))) : ℕ) := fun t => by rw [hE_def]
  have hf2 : InId W c (A.len c) α f := by
    rw [hα_def]
    refine inId_of_inFr W (A.len c) (fun _ => 0) (fun t => mmF A (A.ty (c - (t : ZMod n))))
      (fun _ _ => Or.inl rfl) ?_
    simp only [pow_zero, Finset.prod_const_one]
    rw [mmDen_eq] at h2
    exact h2
  have hg := Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS
    (∑ k ∈ Finset.range (PD.p ^ A.len c), (Polynomial.X : Polynomial O) ^ k) f hf2
  have hLam : InFr W c 1 (abelian₂ W A c (A.len c)) (PPγ W (A.len c) (A.JS c) f) :=
    inFr_Lam W (Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS (PPO W (A.len c) (A.JS c)) f (inId_Lam W h1))
  have hE : ∀ s < A.len c, -(A.Hs c (A.len c) s : ℤ) ≤ E s ∧ E s ≤ A.Hs c (A.len c) s := by
    intro s hs
    have := nnDF_le_H A hOK hc hs
    rw [hEt]
    constructor <;> omega
  have hdec : ∀ s < A.len c, ∃ κ : ℕ, ∃ f₁ f₂ : W.EE,
      lE W κ * PPγ W (A.len c) (A.JS c) f = f₁ + f₂ ∧
      InFr W c (ps W s ^ (E s).toNat)
        (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range (A.len c)).erase s, ps W t ^ A.Hs c (A.len c) t) f₁ ∧
      InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 f₂ := by
    intro s hs
    have hq : α s + ((mmF A (A.ty (c - (s : ZMod n))) - nnDF (A.ty (c - (s : ZMod n))) : ℕ) : ℤ) = E s := by
      have := nnDF_le_mmF A (A.ty (c - (s : ZMod n)))
      rw [hαt, hEt]
      omega
    have hT : Finset.Ico (α s) (α s + ((mmF A (A.ty (c - (s : ZMod n))) - nnDF (A.ty (c - (s : ZMod n))) : ℕ) : ℤ)) ⊆
        (A.JS c).erase 0 := by
      intro i hi
      rw [Finset.mem_Ico, hαt] at hi
      rw [Finset.mem_erase]
      cases hty : A.ty (c - (s : ZMod n)) with
      | thin =>
        rw [hty] at hi
        simp only [mmF, nnDF] at hi
        exact ⟨by omega, mem_JS_thin A hs hty (by omega) (by omega)⟩
      | up b =>
        rw [hty] at hi
        simp only [mmF, nnDF] at hi
        exact ⟨by omega, mem_JS_up A hs hty (Finset.mem_Ico.2 ⟨by omega, by omega⟩)⟩
      | down b =>
        rw [hty] at hi
        simp only [mmF, nnDF] at hi
        exfalso; omega
    obtain ⟨κ, hκ⟩ := raise W hKL hCA hS hg hs _ _ hT
    rw [hq] at hκ
    have hκ' : InId W c (A.len c) (Function.update α s (E s)) (lE W κ * PPγ W (A.len c) (A.JS c) f) := by
      rw [ppγ_eq]; exact hκ
    have hα' : ∀ t ∈ (Finset.range (A.len c)).erase s, -(A.Hs c (A.len c) t : ℤ) ≤ α t := by
      intro t ht
      have ht' := Finset.mem_range.1 (Finset.mem_of_mem_erase ht)
      have := mmF_le_H A hOK hc ht'
      rw [hαt]
      omega
    exact ⟨κ, _, 0, (add_zero _).symm,
      level_form W hπ (Finset.mem_range.2 hs) α (E s) (A.Hs c (A.len c)) hα' hκ', inFr_zero W c _ _⟩
  obtain ⟨f₁, f₂, hsum, hf₁, hf₂⟩ := hRAT hCA h5 A c (A.len c) 0 E (Nat.zero_le 1) hE _ hLam hdec
    (fun h => absurd h (by decide))
  have hf₁' : InFr W c 1 (nnDen W A c) f₁ := by
    rw [pow_zero, one_mul] at hf₁
    have hi : InId W c (A.len c) E f₁ := hf₁
    rw [hE_def] at hi
    have h' := inFr_of_inId W (A.len c) (fun _ => 0) (fun t => nnDF (A.ty (c - (t : ZMod n))))
      (fun _ _ => Or.inl rfl) hi
    simp only [pow_zero, Finset.prod_const_one] at h'
    rw [nnDen_eq]
    exact h'
  have hnn : nnDen W A c ∈ W.AΔ := by
    rw [nnDen_eq]; exact prod_ps_mem W hπ _ _
  have hLm : abelian₂ W A c (A.len c) ∈ W.AΔ := by
    unfold abelian₂; exact prod_ps_mem W hπ _ _
  have hf₂' : InFr W c 1 (nnDen W A c) f₂ := by
    have h' := inFr_den_mul W hnn hf₂
    rw [one_mul] at h'
    rw [← one_mul (W.π₀ * abelian₂ W A c (A.len c))] at h'
    exact inFr_num_drop W (mul_mem hπ hLm) h'
  rw [hsum]
  exact inFr_add W hf₁' hf₂'

theorem gsub_eq (x : W.EE) :
    W.γE W.gam x - x = Polynomial.aeval (γL W) (Polynomial.X - 1 : Polynomial O) x := by
  simp [γL]

theorem fac_zero (e : ℕ) : fac W e 0 = Polynomial.X ^ (PD.p ^ e) - 1 := by
  simp [fac]

theorem xsub_ppo (e : ℕ) (JS : Finset ℤ) :
    (Polynomial.X - 1 : Polynomial O) * PPO W e JS = ∏ i ∈ insert 0 (JS.erase 0), fac W e i := by
  have hg : (Polynomial.X - 1 : Polynomial O) *
      ∑ k ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ k = Polynomial.X ^ (PD.p ^ e) - 1 :=
    mul_geom_sum _ _
  have hP : PPO W e JS = (∏ i ∈ JS.erase 0, fac W e i) *
      ∑ k ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ k := rfl
  rw [hP, Finset.prod_insert (by simp), fac_zero]
  linear_combination (∏ i ∈ JS.erase 0, fac W e i) * hg

private theorem dnF_eq_zero_or_mmF_eq_zero (A : ArcP n) (τ : Formalism.MainNotions.LocalTheoryWindows.LT) : dnF τ = 0 ∨ mmF A τ = 0 := by
  cases τ with
  | thin => exact Or.inl rfl
  | up b => exact Or.inl rfl
  | down b => exact Or.inr rfl

private theorem nnNF_eq_zero_or_nnDF_eq_zero (A : ArcP n) (τ : Formalism.MainNotions.LocalTheoryWindows.LT) : nnNF A τ = 0 ∨ nnDF τ = 0 := by
  cases τ with
  | thin => exact Or.inr rfl
  | up b => exact Or.inl rfl
  | down b => exact Or.inr rfl

theorem part_a [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) (hRAT : Formalism.MainNotions.UnusedSlot80.CutU.RATCore W) (A : ArcP n) (hOK : A.OK) {c : ZMod n}
    (hc : c ∈ A.cuts) {f : W.EE} (h1 : InFr W c 1 (abelian₂ W A c (A.len c)) f)
    (h2 : InFr W c 1 (mmDen W A c) f)
    (h3 : InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam f - f)) :
    InFr W c (W.π₀ * nnNum W A c) (nnDen W A c)
      (W.γE W.gam (PPγ W (A.len c) (A.JS c) f) - PPγ W (A.len c) (A.JS c) f) := by
  obtain ⟨hl1, hl2, -⟩ := hOK.2.2.1 c hc
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨F, hFdef⟩ : ∃ F : W.EE,
      F = W.γE W.gam (PPγ W (A.len c) (A.JS c) f) - PPγ W (A.len c) (A.JS c) f := ⟨_, rfl⟩
  rw [← hFdef]
  obtain ⟨α₂, hα₂_def⟩ : ∃ α : ℕ → ℤ,
      α = fun t : ℕ => ((0 : ℕ) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  obtain ⟨α₃, hα₃_def⟩ : ∃ α : ℕ → ℤ, α = fun t : ℕ =>
      (dnF (A.ty (c - (t : ZMod n))) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  obtain ⟨E, hE_def⟩ : ∃ E : ℕ → ℤ, E = fun t : ℕ =>
      (nnNF A (A.ty (c - (t : ZMod n))) : ℤ) - (nnDF (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  have hα₂t : ∀ t : ℕ, α₂ t = ((0 : ℕ) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) :=
    fun t => by rw [hα₂_def]
  have hα₃t : ∀ t : ℕ, α₃ t =
      (dnF (A.ty (c - (t : ZMod n))) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := fun t => by rw [hα₃_def]
  have hEt : ∀ t : ℕ, E t =
      (nnNF A (A.ty (c - (t : ZMod n))) : ℤ) - (nnDF (A.ty (c - (t : ZMod n))) : ℕ) := fun t => by rw [hE_def]
  have hF1 : F = Polynomial.aeval (γL W) (∏ i ∈ insert 0 ((A.JS c).erase 0), fac W (A.len c) i) f := by
    rw [hFdef, gsub_eq, show PPγ W (A.len c) (A.JS c) f =
      Polynomial.aeval (γL W) (PPO W (A.len c) (A.JS c)) f from rfl, ← aeval_mul_apply, xsub_ppo]
  have hF2' : F = Polynomial.aeval (γL W) (PPO W (A.len c) (A.JS c)) (W.γE W.gam f - f) := by
    rw [hFdef, gsub_eq, show PPγ W (A.len c) (A.JS c) f =
      Polynomial.aeval (γL W) (PPO W (A.len c) (A.JS c)) f from rfl, ← aeval_mul_apply, mul_comm,
      aeval_mul_apply, ← gsub_eq]
  have hF2 : F = Polynomial.aeval (γL W) (∏ i ∈ (A.JS c).erase 0, fac W (A.len c) i)
      (Polynomial.aeval (γL W) (∑ k ∈ Finset.range (PD.p ^ A.len c), (Polynomial.X : Polynomial O) ^ k)
        (W.γE W.gam f - f)) := by
    rw [hF2']; exact ppγ_eq W (A.len c) (A.JS c) _
  have hLamF : InFr W c 1 (abelian₂ W A c (A.len c)) F := by
    have h' : InId W c (A.len c) (fun s => ((0 : ℕ) : ℤ) - (A.Hs c (A.len c) s : ℕ)) F := by
      rw [hF1]
      exact Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS _ f (inId_Lam W h1)
    exact inFr_Lam W h'
  have hf2 : InId W c (A.len c) α₂ f := by
    rw [hα₂_def]
    refine inId_of_inFr W (A.len c) (fun _ => 0) (fun t => mmF A (A.ty (c - (t : ZMod n))))
      (fun _ _ => Or.inl rfl) ?_
    simp only [pow_zero, Finset.prod_const_one]
    have h2' := h2
    rw [mmDen_eq] at h2'
    exact h2'
  have hdn : downB W A c ∈ W.AΔ := by rw [downB_eq]; exact prod_ps_mem W hπ _ _
  have hnn : nnDen W A c ∈ W.AΔ := by rw [nnDen_eq]; exact prod_ps_mem W hπ _ _
  have hf3 : InId W c (A.len c) α₃ (W.γE W.gam f - f) := by
    have h3' := h3
    rw [mul_comm] at h3'
    have h3'' := inFr_num_drop W hπ h3'
    rw [downB_eq, mmDen_eq] at h3''
    rw [hα₃_def]
    exact inId_of_inFr W (A.len c) (fun t => dnF (A.ty (c - (t : ZMod n))))
      (fun t => mmF A (A.ty (c - (t : ZMod n)))) (fun t _ => dnF_eq_zero_or_mmF_eq_zero A (A.ty (c - (t : ZMod n)))) h3''
  have hg3 : InId W c (A.len c) α₃ (Polynomial.aeval (γL W)
      (∑ k ∈ Finset.range (PD.p ^ A.len c), (Polynomial.X : Polynomial O) ^ k) (W.γE W.gam f - f)) :=
    Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS _ _ hf3
  have hH2 : ∀ t < A.len c, -(A.Hs c (A.len c) t : ℤ) ≤ α₂ t := fun t ht => by
    have := mmF_le_H A hOK hc ht; rw [hα₂t]; omega
  have hH3 : ∀ t < A.len c, -(A.Hs c (A.len c) t : ℤ) ≤ α₃ t := fun t ht => by
    have := mmF_le_H A hOK hc ht; rw [hα₃t]; omega
  have hnum3 : numI W (A.len c) α₃ = downB W A c := by
    unfold numI
    rw [downB_eq]
    exact Finset.prod_congr rfl fun t _ => by
      rw [hα₃t, (toNat_sub_of _ _ (dnF_eq_zero_or_mmF_eq_zero A (A.ty (c - (t : ZMod n))))).1]
  have hden3 : denI W (A.len c) α₃ = mmDen W A c := by
    unfold denI
    rw [mmDen_eq]
    exact Finset.prod_congr rfl fun t _ => by
      rw [hα₃t, (toNat_sub_of _ _ (dnF_eq_zero_or_mmF_eq_zero A (A.ty (c - (t : ZMod n))))).2]
  have hπ3 : InIdπ W c (A.len c) α₃ (W.γE W.gam f - f) := by
    have h3' := h3
    unfold InFr at h3'
    obtain ⟨u, hu, e⟩ := h3'
    unfold InIdπ
    refine ⟨u, hu, ?_⟩
    rw [hnum3, hden3, e]
    congr 1; ring
  have hLamM : abelian₂ W A c (A.len c) = mmDen W A c *
      ∏ s ∈ Finset.range (A.len c), ps W s ^ (A.Hs c (A.len c) s - mmF A (A.ty (c - (s : ZMod n)))) := by
    unfold abelian₂
    rw [mmDen_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [← pow_add]
    congr 1
    have := mmF_le_H A hOK hc (Finset.mem_range.1 ht)
    omega
  have hπF : InFr W c W.π₀ (abelian₂ W A c (A.len c)) F := by
    have hP := inIdπ_aeval W hR hS (PPO W (A.len c) (A.JS c)) (W.γE W.gam f - f) hπ3
    unfold InIdπ at hP
    obtain ⟨u, hu, e⟩ := hP
    rw [hnum3, hden3] at e
    unfold InFr
    refine ⟨(∏ s ∈ Finset.range (A.len c),
        ps W s ^ (A.Hs c (A.len c) s - mmF A (A.ty (c - (s : ZMod n))))) * downB W A c * u,
      mul_mem (mul_mem (prod_ps_mem W hπ _ _) hdn) hu, ?_⟩
    rw [hF2', hLamM, map_mul, mul_right_comm, e, ← map_mul]
    congr 1; ring
  have step : ∀ s < A.len c, ∀ (α : ℕ → ℤ) (g : W.EE) (T : Finset ℤ) (N : ℕ),
      InId W c (A.len c) α g → Finset.Ico (α s) (α s + N) ⊆ T → α s + N = E s →
      (∀ t < A.len c, -(A.Hs c (A.len c) t : ℤ) ≤ α t) →
      F = Polynomial.aeval (γL W) (∏ i ∈ T, fac W (A.len c) i) g →
      ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * F = f₁ + f₂ ∧
        InFr W c (ps W s ^ (E s).toNat)
          (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range (A.len c)).erase s, ps W t ^ A.Hs c (A.len c) t) f₁ ∧
        InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 f₂ := by
    intro s hs α g T N hg hT hN hH hFg
    obtain ⟨κ, hκ⟩ := raise W hKL hCA hS hg hs N T hT
    rw [hN, ← hFg] at hκ
    exact ⟨κ, _, 0, (add_zero _).symm,
      level_form W hπ (Finset.mem_range.2 hs) α (E s) (A.Hs c (A.len c))
        (fun t ht => hH t (Finset.mem_range.1 (Finset.mem_of_mem_erase ht))) hκ, inFr_zero W c _ _⟩
  have hdec : ∀ s < A.len c, ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * F = f₁ + f₂ ∧
      InFr W c (ps W s ^ (E s).toNat)
        (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range (A.len c)).erase s, ps W t ^ A.Hs c (A.len c) t) f₁ ∧
      InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 f₂ := by
    intro s hs
    cases hty : A.ty (c - (s : ZMod n)) with
    | thin =>
      refine step s hs α₂ f _ (2 * A.G₀) hf2 ?_ ?_ hH2 hF1
      · intro i hi
        rw [Finset.mem_Ico, hα₂t, hty] at hi
        simp only [mmF] at hi
        by_cases h0 : i = 0
        · rw [h0]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (Finset.mem_erase.2 ⟨h0, mem_JS_thin A hs hty (by omega) (by omega)⟩)
      · rw [hα₂t, hEt, hty]; simp only [mmF, nnNF, nnDF]; omega
    | up b =>
      refine step s hs α₃ _ _ A.S hg3 ?_ ?_ hH3 hF2
      · intro i hi
        rw [Finset.mem_Ico, hα₃t, hty] at hi
        simp only [dnF, mmF] at hi
        exact Finset.mem_erase.2 ⟨by omega, mem_JS_up A hs hty (Finset.mem_Ico.2 ⟨by omega, by omega⟩)⟩
      · rw [hα₃t, hEt, hty]; simp only [dnF, mmF, nnNF, nnDF]; omega
    | down b =>
      have hb : 1 ≤ b := by
        have h' := size_pos A hOK (c - (s : ZMod n)) (by rw [hty]; rfl)
        rw [hty] at h'
        exact h'
      refine step s hs α₃ _ _ A.S hg3 ?_ ?_ hH3 hF2
      · intro i hi
        rw [Finset.mem_Ico, hα₃t, hty] at hi
        simp only [dnF, mmF] at hi
        exact Finset.mem_erase.2 ⟨by omega, mem_JS_down A hs hty (Finset.mem_Ico.2 ⟨by omega, by omega⟩)⟩
      · rw [hα₃t, hEt, hty]; simp only [dnF, mmF, nnNF, nnDF]; omega
  have hE : ∀ s < A.len c, -(A.Hs c (A.len c) s : ℤ) ≤ E s ∧ E s ≤ A.Hs c (A.len c) s := by
    intro s hs
    have h₁ := nnDF_le_H A hOK hc hs
    have h₂ := nnNF_le_H A hOK hc hs
    rw [hEt]
    constructor <;> omega
  obtain ⟨f₁, f₂, hsum, hf₁, hf₂⟩ := hRAT hCA h5 A c (A.len c) 1 E le_rfl hE F hLamF hdec
    (fun _ => ⟨0, F, 0, by simp [lE], hπF, inFr_zero W c _ _⟩)
  have hf₁' : InFr W c (W.π₀ * nnNum W A c) (nnDen W A c) f₁ := by
    rw [pow_one] at hf₁
    refine inFr_congr W ?_ ?_ hf₁
    · rw [nnNum_eq]
      congr 1
      exact Finset.prod_congr rfl fun t _ => by
        rw [hEt, (toNat_sub_of _ _ (nnNF_eq_zero_or_nnDF_eq_zero A (A.ty (c - (t : ZMod n))))).1]
    · rw [nnDen_eq]
      exact Finset.prod_congr rfl fun t _ => by
        rw [hEt, (toNat_sub_of _ _ (nnNF_eq_zero_or_nnDF_eq_zero A (A.ty (c - (t : ZMod n))))).2]
  have hLamN : abelian₂ W A c (A.len c) = nnNum W A c *
      ∏ s ∈ Finset.range (A.len c), ps W s ^ (A.Hs c (A.len c) s - nnNF A (A.ty (c - (s : ZMod n)))) := by
    unfold abelian₂
    rw [nnNum_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [← pow_add]
    congr 1
    have := nnNF_le_H A hOK hc (Finset.mem_range.1 ht)
    omega
  have hf₂' : InFr W c (W.π₀ * nnNum W A c) (nnDen W A c) f₂ := by
    have h' := inFr_den_mul W hnn hf₂
    rw [one_mul, hLamN, ← mul_assoc] at h'
    exact inFr_num_drop W (prod_ps_mem W hπ _ _) h'
  rw [hsum]
  exact inFr_add W hf₁' hf₂'

theorem lE_add (a b : ℕ) : lE W (a + b) = lE W a * lE W b := by
  unfold lE; rw [pow_add]

theorem ppo_single_eval {e : ℕ} {k : ℤ} (hk : k ≠ 0) :
    (PPO W e {k}).eval 1 = ((((W.χΓ W.gam) ^ (k * (PD.p : ℤ) ^ e) : Oˣ) : O) - 1) *
      (-(((PD.p ^ e : ℕ) : O))) := by
  have hks : ({k} : Finset ℤ).erase 0 = {k} := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨hk, rfl⟩
  unfold PPO
  rw [hks, Finset.prod_singleton]
  simp [Polynomial.eval_finset_sum] <;> ring

theorem part_c [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) (hRAT : Formalism.MainNotions.UnusedSlot80.CutU.RATCore W) (hInv : Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore W)
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hvp : v (algebraMap O LL ((PD.p : ℕ) : O)) = 1)
    (A : ArcP n) (hOK : A.OK) {c : ZMod n}
    (hc : c ∈ A.cuts) {f : W.EE} (h1 : InFr W c 1 (abelian₂ W A c (A.len c)) f)
    (h2 : InFr W c 1 (mmDen W A c) f)
    (h3 : InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam f - f)) :
    ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c)
        (lE W κ * PPγ W (A.len c) (A.JS c) f -
          algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) := by
  intro s hs b hτ
  set e := A.len c with he
  have hsm : s ∈ Finset.range e := Finset.mem_range.2 hs
  set d : ℕ → ℕ := fun t => nnDF (A.ty (c - (t : ZMod n))) with hd
  set D := ∏ t ∈ (Finset.range e).erase s, ps W t ^ d t with hD
  have hb1 : 1 ≤ b := by
    have := size_pos A hOK (c - (s : ZMod n)) (by rw [hτ]; rfl)
    rwa [hτ] at this
  have hnnDen : nnDen W A c = D := by
    rw [nnDen_eq, ← Finset.mul_prod_erase _ _ hsm, hτ]
    simp [nnDF, hD, hd]
  set f' := PPγ W e (A.JS c) f with hf'
  set g := W.γE W.gam f' - f' with hg
  have hf'D : InFr W c 1 D f' := hnnDen ▸ part_b W hKL hCA h5 hS hπ hRAT A hOK hc h1 h2
  have hgD : InFr W c (ps W s ^ (b + A.S)) D g := by
    have ha := part_a W hR hKL hCA h5 hS hπ hRAT A hOK hc h1 h2 h3
    rw [hnnDen, nnNum_eq, ← Finset.mul_prod_erase _ _ hsm, hτ] at ha
    refine inFr_num_drop W (x := W.π₀ * ∏ t ∈ (Finset.range e).erase s,
      ps W t ^ nnNF A (A.ty (c - (t : ZMod n)))) (Subalgebra.mul_mem _ hπ (prod_ps_mem' W hπ _ _)) ?_
    refine inFr_congr W ?_ rfl ha
    simp only [nnNF]; ring

  obtain ⟨κ0, x0, h0⟩ := hInv hCA h5 c s ((Finset.range e).erase s) d (Finset.notMem_erase s _) f' hf'D
    ⟨0, by rw [show lE W 0 = 1 by simp [lE], one_mul]; exact (pow_one (ps W s)) ▸
      inFr_pow_mono W (by omega) hπ hgD⟩
  set h := lE W κ0 * f' - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x0 with hh
  have hγh : W.γE W.gam h - h = lE W κ0 * g := by
    rw [hh, map_sub, map_mul, γE_lE, γE_const, hg]; ring

  have key : ∀ k, 1 ≤ k → k ≤ b + A.S → ∃ m, InFr W c (ps W s ^ k) D (lE W m * h) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base => intro _; exact ⟨0, by rw [show lE W 0 = 1 by simp [lE], one_mul, pow_one]; exact h0⟩
    | succ k hk ih =>
      intro hkb
      obtain ⟨m, hm⟩ := ih (by omega)
      set y := lE W m * h with hy
      have hyI : InId W c e (αk e s d k) y := (inId_αk_iff W hsm d k y).2 hm
      have hwin : Finset.Ico (αk e s d k s) (αk e s d k s + ((1 : ℕ) : ℤ)) ⊆ {(k : ℤ)} := by
        intro i hi
        simp only [αk, ↓reduceIte, Finset.mem_Ico] at hi
        simp only [Finset.mem_singleton]; push_cast at hi; omega
      obtain ⟨κ1, hκ1⟩ := raise W hKL hCA hS hyI hs 1 _ hwin
      rw [Finset.prod_singleton, show αk e s d k s + ((1 : ℕ) : ℤ) = (k : ℤ) + 1 by simp [αk],
        update_αk] at hκ1
      have hf1 := (inId_αk_iff W hsm d (k + 1) _).1 hκ1

      set Sp : Polynomial O := ∑ j ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ j with hSp
      have hγy : W.γE W.gam y - y = lE W m * (lE W κ0 * g) := by
        rw [hy, map_mul, γE_lE, ← hγh]; ring
      have hγyI : InId W c e (αk e s d (k + 1)) (W.γE W.gam y - y) := by
        refine (inId_αk_iff W hsm d (k + 1) _).2 ?_
        rw [hγy]
        exact inFr_lE W (inFr_lE W (inFr_pow_mono W (by omega) hπ hgD) κ0) m
      have hN : Polynomial.aeval (γL W) (Polynomial.X ^ (PD.p ^ e) - 1 : Polynomial O) y =
          Polynomial.aeval (γL W) Sp (W.γE W.gam y - y) := by
        rw [gsub_eq, ← aeval_mul_apply, hSp, mul_comm, mul_geom_sum]
      have hf2 := (inId_αk_iff W hsm d (k + 1) _).1 (inId_lE W (hN ▸ inId_aeval W hS Sp _ hγyI) κ1)

      have hdiff : lE W κ1 * Polynomial.aeval (γL W) (Polynomial.X ^ (PD.p ^ e) - 1 : Polynomial O) y -
          lE W κ1 * Polynomial.aeval (γL W) (fac W e k) y =
          (((((W.χΓ W.gam) ^ ((k : ℤ) * (PD.p : ℤ) ^ e) : Oˣ) : O) - 1) • (lE W κ1 * y)) := by
        rw [← mul_sub, ← LinearMap.sub_apply, ← map_sub]
        rw [show (Polynomial.X ^ (PD.p ^ e) - 1 : Polynomial O) - fac W e k =
          Polynomial.C ((((W.χΓ W.gam) ^ ((k : ℤ) * (PD.p : ℤ) ^ e) : Oˣ) : O) - 1) by
            simp only [fac, map_sub, map_one]; ring]
        rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
          mul_smul_comm]
      have hz := inFr_sub W hf2 hf1
      rw [hdiff] at hz

      have hv := ((hKL hCA e {(k : ℤ)}).1)
      have hk0 : (k : ℤ) ≠ 0 := by omega
      rw [ppo_single_eval W hk0] at hv
      obtain ⟨o, ho⟩ := div_of_val hinj hO2 hvp _ _ hv
      set M := e + ∑ i ∈ ({(k : ℤ)} : Finset ℤ).erase 0, (e + 1 + padicValInt PD.p i) with hM
      have hw : lE W M * (lE W κ1 * y) = o • ((-(((PD.p ^ e : ℕ) : O))) •
          ((((((W.χΓ W.gam) ^ ((k : ℤ) * (PD.p : ℤ) ^ e) : Oˣ) : O) - 1)) • (lE W κ1 * y))) := by
        rw [lE_eq_alg W M, ← Algebra.smul_def, ho, smul_smul, smul_smul]
        congr 1; ring
      refine ⟨M + (κ1 + m), ?_⟩
      rw [show lE W (M + (κ1 + m)) * h = lE W M * (lE W κ1 * y) by
        rw [hy, show M + (κ1 + m) = (M + κ1) + m by ring, lE_add W (M + κ1) m, lE_add W M κ1]; ring, hw]
      exact inFr_smul W (inFr_smul W hz _) _
  obtain ⟨m, hm⟩ := key (b + A.S) (by omega) le_rfl
  refine ⟨m + κ0, ((PD.p : ℕ) : O) ^ m * x0, ?_⟩
  rw [hnnDen]
  convert hm using 1
  simp only [hh, lE_eq_alg, map_mul, map_pow, pow_add]
  ring

theorem killWinFromCut [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hvp : v (algebraMap O LL ((PD.p : ℕ) : O)) = 1) : Formalism.MainNotions.UnusedSlot80.CutU.KillWinFromCut W := by
  intro hR hKL hS hπ hRAT hInv hCA h5 A hOK c hc f h1 h2 h3
  exact ⟨part_a W hR hKL hCA h5 hS hπ hRAT A hOK hc h1 h2 h3,
    part_b W hKL hCA h5 hS hπ hRAT A hOK hc h1 h2,
    part_c W hR hKL hCA h5 hS hπ hRAT hInv hinj hO2 hvp A hOK hc h1 h2 h3⟩

end Main

end Formalism.MainNotions.UnusedSlot80.KWP
end
end

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem killWinL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG)) :
    KillWinL D HW := by
  intro l _ K LL hG hCA h5
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hR : ToolsR.RingP ((HW l).W K 1 LL hG) := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hG) := tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hvp : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (((((D.loc l).PD K).p : ℕ) : ↥(OL LL)))) = 1 := by
    rw [map_natCast, (D.loc l).PD_p K]; exact (D.loc l).v_l LL
  have hKL := hAdm.2.1 l K LL hG hCA h5
  exact Formalism.MainNotions.UnusedSlot80.KWP.killWinFromCut ((HW l).W K 1 LL hG) hV.1 hV.2.1 hvp hR hKL
    (Formalism.MainNotions.UnusedSlot80.KF.psStable_of _ hR) hR.1
    (Formalism.MainNotions.UnusedSlot80.RatW.ratCore_of _ hR hT hR.2.2.1 hR.1) (hInv l K LL hG hCA h5)

end Formalism.MainNotions.UnusedSlot80
end
end

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem universal_general_of_inverse_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG))
    (hUG : UnivGenL D HW) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_window D HW F Cm hAdm h9 hH h15 (killWinL_of D HW F Cm hAdm h9 hInv) hUG

end Formalism.MainNotions.UnusedSlot80
end
end

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem univGenL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG)) :
    UnivGenL D HW := by
  intro l _ K LL hG hCA h5 _
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have hR : ToolsR.RingP ((HW l).W K 1 LL hG) := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hG) := tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hG) hV
  have hKL := hAdm.2.1 l K LL hG hCA h5
  exact Formalism.MainNotions.UnusedSlot80.UGen.universal_generators_of_units ((HW l).W K 1 LL hG) hV.1 hV.2.1 hpu hR hKL
    (Formalism.MainNotions.UnusedSlot80.KF.psStable_of _ hR) hR.1
    (Formalism.MainNotions.UnusedSlot80.RatW.ratCore_of _ hR hT hR.2.2.1 hR.1) (hInv l K LL hG hCA h5)

theorem universal_general_of_level_inverse (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG)) :
    UniversalComponentCaseA D HW F Cm :=
  universal_general_of_inverse_levels D HW F Cm hAdm h9 hH h15 hInv (univGenL_of D HW F Cm hAdm h9 hInv)

end Formalism.MainNotions.UnusedSlot80
end
end

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem toolsAlg_at (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) :
    Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL h.2.2) := by
  have hR : ToolsR.RingP ((HW l).W K 1 LL h.2.2) := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hp0 := Formalism.MainNotions.WachCoordinates.Br.p_ne_zero_O ((HW l).W K 1 LL h.2.2)
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL h.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  exact ⟨ToolsR.tools1 hR, ToolsR.tools2 hR hp0 hpu, ToolsR.tools3 hR, ToolsR.tools4 hR⟩

theorem invLevCore_fin (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG) := by
  refine InvW.invLevCore_L D HW F h9 fun l _ K LL h a s hB => ?_
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  exact InvW.levRat_of ((HW l).W K 1 LL h.2.2) (ring_condition_uniformizer_polynomial D HW F h9 l K LL h) (toolsAlg_at D HW F h9 l K LL h)
    (Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL h.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)) a s hB

theorem universal_general_statement_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_level_inverse D HW F Cm hAdm h9 hH h15 (invLevCore_fin D HW F h9)

end Formalism.MainNotions.UnusedSlot80
end
end
