import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Filter Topology

namespace GlobalTheory.PZ.LTModel

def Kb : FinExt 2 := ⟨⊥, inferInstance⟩

theorem resCard_Kb : resCard Kb = 2 := by
  have : K0 Kb = ⊥ := by simp [K0, Kb]
  rw [resCard, this, IntermediateField.finrank_bot, pow_one]

theorem bij : Function.Bijective (algebraMap ℤ_[2] ↥(OL Kb)) := by
  have hinj : Function.Injective (algebraMap ℤ_[2] ↥Kb.1) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[2] ℚ_[2] ↥Kb.1]
    exact (algebraMap ℚ_[2] ↥Kb.1).injective.comp (IsFractionRing.injective ℤ_[2] ℚ_[2])
  constructor
  · intro a b h
    exact hinj (congrArg Subtype.val h)
  · rintro ⟨⟨x, hx⟩, hi⟩
    obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx
    have hi' : IsIntegral ℤ_[2] (algebraMap ℚ_[2] ↥Kb.1 y) := hi
    have hy : IsIntegral ℤ_[2] y := (isIntegral_algebraMap_iff (algebraMap ℚ_[2] ↥Kb.1).injective).1 hi'
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hy
    exact ⟨a, rfl⟩

theorem irr : Irreducible (2 : ↥(OL Kb)) := by
  have h := (MulEquiv.irreducible_iff (x := ((2 : ℕ) : ℤ_[2]))
    (RingEquiv.ofBijective (algebraMap ℤ_[2] ↥(OL Kb)) bij).toMulEquiv).2 (PadicInt.irreducible_p (p := 2))
  have e : (RingEquiv.ofBijective (algebraMap ℤ_[2] ↥(OL Kb)) bij).toMulEquiv ((2 : ℕ) : ℤ_[2]) = 2 :=
    map_natCast (algebraMap ℤ_[2] ↥(OL Kb)) 2
  rwa [e] at h

theorem coeff_cyc (k : ℕ) (hk : k ≠ 0) (c : ℤ_[2]) :
    PowerSeries.coeff k (GlobalTheory.Cyc.cyc 2 ↥(OL Kb) c) = algebraMap ℤ_[2] ↥(OL Kb) (Ring.choose c k) := by
  rw [GlobalTheory.Cyc.cyc, map_sub, PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, PowerSeries.coeff_one,
    if_neg hk, sub_zero, smul_eq_mul, mul_one]

theorem commGroup_mul_eq_mul_mul_div (O : Type) [CommRing O] [Algebra ℤ_[2] O] (c : ℤ_[2]) :
    PowerSeries.C 2 * GlobalTheory.Cyc.cyc 2 O c + GlobalTheory.Cyc.cyc 2 O c ^ 2 =
      PowerSeries.subst (PowerSeries.C 2 * PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries O) (GlobalTheory.Cyc.cyc 2 O c) := by
  have h := GlobalTheory.Cyc.Series.phi_act 2 O c PowerSeries.X
  rw [GlobalTheory.Cyc.Series.phi_X, GlobalTheory.Cyc.Series.act_X, map_sub, map_pow, map_add, map_one, GlobalTheory.Cyc.Series.act_X] at h
  have e : (PowerSeries.C 2 * PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries O) =
      GlobalTheory.Cyc.cyc 2 O ((2 : ℕ) : ℤ_[2]) := by
    rw [GlobalTheory.Cyc.Series.cyc_natCast, map_ofNat]; ring
  rw [e, map_ofNat, ← PowerSeries.coe_substAlgHom
    (PowerSeries.HasSubst.of_constantCoeff_zero' (GlobalTheory.Cyc.cyc_const 2 O _))]
  change _ = GlobalTheory.Cyc.phi 2 O _
  rw [h]; ring

theorem endo (c : ℤ_[2]) : IsLTEndo Kb 2 (algebraMap ℤ_[2] ↥(OL Kb) c) (GlobalTheory.Cyc.cyc 2 ↥(OL Kb) c) := by
  refine ⟨GlobalTheory.Cyc.cyc_const _ _ _, ?_, ?_⟩
  · rw [coeff_cyc 1 one_ne_zero, Ring.choose_one_right]
  · rw [ltSeries, resCard_Kb]
    exact commGroup_mul_eq_mul_mul_div _ c

section
variable {R : Type} [NormedField R] [NormedAlgebra ℚ_[2] R] [IsUltrametricDist R]

theorem norm_lt {ζ : R} {n : ℕ} (h : ζ ^ 2 ^ n = 1) : ‖ζ - 1‖ < 1 := by
  induction n generalizing ζ with
  | zero => simp at h; simp [h]
  | succ n ih =>
    have h2 := ih (ζ := ζ ^ 2) (by rw [← pow_mul, ← pow_succ']; exact h)
    by_contra hc
    push Not at hc
    have e : (ζ - 1) ^ 2 = (ζ ^ 2 - 1) + (-2) * (ζ - 1) := by ring
    have h22 : ‖(-2 : R)‖ < 1 := by
      rw [norm_neg, show (2 : R) = algebraMap ℚ_[2] R ((2 : ℕ) : ℚ_[2]) from (map_natCast (algebraMap ℚ_[2] R) 2).symm, norm_algebraMap']
      exact Padic.norm_p_lt_one
    have h3 := IsUltrametricDist.norm_add_le_max (ζ ^ 2 - 1) ((-2) * (ζ - 1))
    rw [← e, norm_pow, norm_mul] at h3
    rcases le_max_iff.1 h3 with h4 | h4
    · nlinarith
    · nlinarith [norm_nonneg (-2 : R)]

theorem hasSum_C [CompleteSpace R] {ζ : R} {n : ℕ} (h : ζ ^ 2 ^ n = 1) (c : ℤ_[2]) :
    HasSum (fun k => algebraMap ℚ_[2] R ((Ring.choose c k : ℤ_[2]) : ℚ_[2]) * (ζ - 1) ^ k)
      (ζ ^ (PadicInt.toZModPow n c).val) := by
  letI : Algebra ℤ_[2] R := ((algebraMap ℚ_[2] R).comp PadicInt.Coe.ringHom).toAlgebra
  haveI : IsBoundedSMul ℤ_[2] R := IsBoundedSMul.of_norm_smul_le fun a x => by
    rw [Algebra.smul_def, norm_mul]
    change ‖algebraMap ℚ_[2] R (a : ℚ_[2])‖ * _ ≤ _
    rw [norm_algebraMap']; rfl
  have hr : Tendsto (fun k : ℕ => (ζ - 1) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_lt h)
  let κ := PadicInt.addChar_of_value_at_one (p := 2) (ζ - 1) hr
  have hκ : Continuous κ := PadicInt.continuous_addChar_of_value_at_one hr
  have h1 : κ 1 = ζ := by simp [κ]
  have hn : ∀ m : ℕ, κ m = ζ ^ m := fun m => by
    rw [← nsmul_one, AddChar.map_nsmul_eq_pow, h1]
  have hk : ∀ b : ℤ_[2], κ (2 ^ n * b) = 1 := fun b =>
    congr_fun (PadicInt.denseRange_natCast.equalizer (g := fun b => κ (2 ^ n * b)) (h := fun _ => 1)
      (by fun_prop) continuous_const (funext fun m => by
        have := hn (2 ^ n * m)
        push_cast at this
        simp only [Function.comp]
        rw [this, pow_mul, h, one_pow])) b
  have hm : c - ((PadicInt.toZModPow n c).val : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hm
  have hc : κ c = ζ ^ (PadicInt.toZModPow n c).val := by
    have : c = ((PadicInt.toZModPow n c).val : ℤ_[2]) + 2 ^ n * b := by
      push_cast at hb; linear_combination hb
    conv_lhs => rw [this]
    rw [AddChar.map_add_eq_mul, hk, hn, mul_one]
  rw [← hc]
  have hs := ContinuousMap.hasSum_apply (PadicInt.hasSum_mahlerSeries (p := 2) hr) c
  simp only [PadicInt.mahlerTerm_apply, mahler_apply, Algebra.smul_def] at hs
  exact hs

end


theorem exists_roots : ∃ ζ : ℕ → Om 2, ζ 0 = 1 ∧ ζ 1 = -1 ∧ ∀ n, ζ (n + 1) ^ 2 = ζ n := by
  choose s hs using fun x : Om 2 => IsAlgClosed.exists_pow_nat_eq x (n := 2) two_pos
  refine ⟨fun n => Nat.rec 1 (fun m _ => s^[m] (-1)) n, rfl, rfl, fun n => ?_⟩
  cases n with
  | zero => simp
  | succ n =>
    change s^[n + 1] (-1) ^ 2 = s^[n] (-1)
    rw [Function.iterate_succ_apply', hs]

def cycZ : ↥(GK Kb) →* ℤ_[2]ˣ :=
  ((cyclotomicCharacter (Om 2) 2).comp (MulSemiringAction.toRingAut (GQ 2) (Om 2))).comp (GK Kb).subtype

def cycK : ↥(GK Kb) →* (↥Kb.1)ˣ := (Units.map (algebraMap ℤ_[2] ↥Kb.1).toMonoidHom).comp cycZ


section General
variable {l : ℕ} [Fact l.Prime]

theorem two_le_resCard (K : FinExt l) : 2 ≤ resCard K := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  exact (Fact.out : l.Prime).two_le.trans (Nat.le_self_pow Module.finrank_pos.ne' l)

theorem lubinTateSeries_eq_of_coeff_one_eq {O : Type} [CommRing O] [IsDomain O] {π : O} (hπ : Irreducible π) {q : ℕ} (hq : 2 ≤ q)
    {φ ψ : PowerSeries O} (h0 : PowerSeries.constantCoeff φ = 0) (h0' : PowerSeries.constantCoeff ψ = 0)
    (h1 : PowerSeries.coeff 1 φ = PowerSeries.coeff 1 ψ)
    (h : PowerSeries.C π * φ + φ ^ q =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries O) φ)
    (h' : PowerSeries.C π * ψ + ψ ^ q =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries O) ψ) : φ = ψ := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  set e : PowerSeries O := PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ (p + 2) with he
  have hs : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [he])
  let F : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom hs
  have hF : ∀ f : PowerSeries O, PowerSeries.subst e f = F f := fun f => by
    rw [← PowerSeries.coe_substAlgHom hs]
  have hX : F PowerSeries.X = PowerSeries.X * (PowerSeries.C π + PowerSeries.X ^ (p + 1)) := by
    rw [show F PowerSeries.X = e from PowerSeries.substAlgHom_X hs, he]; ring
  have hC : ∀ a : O, F (PowerSeries.C a) = PowerSeries.C a := fun a => F.commutes a
  rw [hF] at h h'
  have key : ∀ k : ℕ, PowerSeries.X ^ (k + 2) ∣ φ - ψ := by
    intro k
    induction k with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [h0, h0']
      · simp [h1]
    | succ k ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨S, hS, hS0⟩ : ∃ S : PowerSeries O, S * (φ - ψ) = φ ^ (p + 2) - ψ ^ (p + 2) ∧
          PowerSeries.constantCoeff S = 0 := by
        refine ⟨_, (Commute.all φ ψ).geom_sum₂_mul (p + 2), ?_⟩
        rw [map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_mul, map_pow, map_pow, h0, h0', ← pow_add, zero_pow (by omega)]
      have e1 : PowerSeries.C π * (φ - ψ) + S * (φ - ψ) = F (φ - ψ) := by
        rw [hS, map_sub F]; linear_combination h - h'
      rw [hu, map_mul F, map_pow F, hX, mul_pow] at e1
      have e2 : PowerSeries.C π * u + S * u = (PowerSeries.C π + PowerSeries.X ^ (p + 1)) ^ (k + 2) * F u :=
        mul_left_cancel₀ (pow_ne_zero (k + 2) (PowerSeries.X_ne_zero (R := O))) (by linear_combination e1)
      have e3 : PowerSeries.constantCoeff (F u) = PowerSeries.constantCoeff u := by
        conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const u, map_add F, map_mul F, hX, hC]
        simp
      have e4 := congrArg PowerSeries.constantCoeff e2
      simp only [map_add, map_mul, map_pow, hS0, e3, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
        zero_pow (Nat.succ_ne_zero p), add_zero, zero_mul] at e4
      have e5 : π * (1 - π ^ (k + 1)) * PowerSeries.constantCoeff u = 0 := by linear_combination e4
      have hne : (1 - π ^ (k + 1)) ≠ 0 := fun h1 =>
        hπ.not_isUnit (IsUnit.of_pow_eq_one (n := k + 1) (by linear_combination -h1) (Nat.succ_ne_zero k))
      have e6 : PowerSeries.constantCoeff u = 0 :=
        (mul_eq_zero.1 e5).resolve_left (mul_ne_zero hπ.ne_zero hne)
      obtain ⟨v, hv⟩ := PowerSeries.X_dvd_iff.2 e6
      exact ⟨v, by rw [hu, hv]; ring⟩
  rw [← sub_eq_zero]
  ext n
  exact PowerSeries.X_pow_dvd_iff.1 (key n) n (by omega)

theorem IsLTEndo_unique {K : FinExt l} {π a : ↥(OL K)} (hπ : Irreducible π) {φ ψ : PowerSeries ↥(OL K)}
    (h : IsLTEndo K π a φ) (h' : IsLTEndo K π a ψ) : φ = ψ :=
  lubinTateSeries_eq_of_coeff_one_eq hπ (two_le_resCard K) h.1 h'.1 (h.2.1.trans h'.2.1.symm) h.2.2 h'.2.2



end General



end GlobalTheory.PZ.LTModel

end
