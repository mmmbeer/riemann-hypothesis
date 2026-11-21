import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfCharFrame
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

section
noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

theorem unitsMap_unitOfCoprime {M N : ℕ} (h : M ∣ N) (a : ℕ) (ha : Nat.Coprime a N) :
    ZMod.unitsMap h (ZMod.unitOfCoprime a ha) = ZMod.unitOfCoprime a (ha.coprime_dvd_right h) := by
  ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]

theorem HostRaw.art_eq_of_prim_eq {φ : Frame} (H : HostRaw φ) {θ θ' : φ.Char} (h : H.prim θ = H.prim θ')
    (u : (ZMod H.condN)ˣ) : θ (H.art u) = θ' (H.art u) := by
  have h1 := (H.isPrimOf_prim θ).2 _ (ZMod.val_coe_unit_coprime u)
  have h2 := ((H.isPrimOf_iff θ' _).mpr h).2 _ (ZMod.val_coe_unit_coprime u)
  have h3 := h1.symm.trans h2
  rw [HostRaw.dirAt, HostRaw.dirAt, ZMod.natCast_zmod_val, H.dir_unit, H.dir_unit] at h3
  exact Units.ext h3

namespace EvenGrp

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

def ann : Subgroup (ZMod M)ˣ := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).symm (OrderDual.toDual Ξ)

theorem mem_ann (u : (ZMod M)ˣ) : u ∈ ann Ξ ↔ ∀ χ ∈ Ξ, χ u = 1 := by
  simp [ann]

theorem mem_iff (χ : DirichletCharacter ℂ M) : χ ∈ Ξ ↔ ∀ u ∈ ann Ξ, χ u = 1 := by
  have h1 := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).apply_symm_apply (OrderDual.toDual Ξ)
  have h2 : χ ∈ Ξ ↔ χ ∈ OrderDual.ofDual ((MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ) (ann Ξ)) := by
    simp only [ann, h1, OrderDual.ofDual_toDual]
  rw [h2]
  generalize ann Ξ = S
  simp

abbrev B : Type := (ZMod M)ˣ ⧸ ann Ξ

theorem card_B : Nat.card (B Ξ) = Nat.card Ξ := by
  rw [← MulChar.card_subgroupOrderIsoSubgroupMulChar (R := ℂ), ann, OrderIso.apply_symm_apply]
  rfl

instance neZero_lcm : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩

def xiW : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ →* B Ξ := (QuotientGroup.mk' _).comp (ZMod.unitsMap (Nat.dvd_lcm_right _ _))

theorem xiW_surj : Function.Surjective (xiW Ξ e) := by
  intro b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (ann Ξ) b
  obtain ⟨c, rfl⟩ := ZMod.unitsMap_surjective (Nat.dvd_lcm_right (2 ^ (e + 2)) M) a
  exact ⟨c, rfl⟩

def Good (m : ℕ) : Prop := m ∣ Nat.lcm (2 ^ (e + 2)) M ∧ 2 ^ (e + 2) ∣ m ∧
  ∀ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ, (u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val ≡ 1 [MOD m] → xiW Ξ e u = 1

theorem exists_good : ∃ m, Good Ξ e m := by
  refine ⟨Nat.lcm (2 ^ (e + 2)) M, dvd_rfl, Nat.dvd_lcm_left _ _, fun u hu => ?_⟩
  have h1 : ((u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val : ZMod (Nat.lcm (2 ^ (e + 2)) M)) =
      ((1 : ℕ) : ZMod (Nat.lcm (2 ^ (e + 2)) M)) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h1
  have h2 : u = 1 := Units.ext (by rw [h1, Units.val_one])
  rw [h2, map_one]

open Classical in

def QS : ℕ := Nat.find (exists_good Ξ e)

open Classical in
theorem good_QS : Good Ξ e (QS Ξ e) := Nat.find_spec (exists_good Ξ e)

open Classical in
theorem not_good {m : ℕ} (h : m < QS Ξ e) : ¬ Good Ξ e m := Nat.find_min (exists_good Ξ e) h

theorem QS_dvd : QS Ξ e ∣ Nat.lcm (2 ^ (e + 2)) M := (good_QS Ξ e).1

theorem QS_dvd_mul : QS Ξ e ∣ 2 ^ (e + 2) * M :=
  (QS_dvd Ξ e).trans (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))

theorem QS_pos : 0 < QS Ξ e := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have h1 := QS_dvd Ξ e
  rw [h, zero_dvd_iff] at h1
  exact (NeZero.ne _) h1

instance neZero_QS : NeZero (QS Ξ e) := ⟨(QS_pos Ξ e).ne'⟩

def xi : (ZMod (QS Ξ e))ˣ →* B Ξ :=
  (ZMod.unitsMap (QS_dvd Ξ e)).liftOfSurjective (ZMod.unitsMap_surjective _)
    ⟨xiW Ξ e, fun u hu => (good_QS Ξ e).2.2 u ((unitsMap_eq_one_iff _ u).mp hu)⟩

theorem xi_unitsMap (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) : xi Ξ e (ZMod.unitsMap (QS_dvd Ξ e) u) = xiW Ξ e u :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem xi_surj : Function.Surjective (xi Ξ e) := by
  intro b
  obtain ⟨u, rfl⟩ := xiW_surj Ξ e b
  exact ⟨_, xi_unitsMap Ξ e u⟩

variable (hev : ∀ χ ∈ Ξ, χ.Even)

def data : EvenData where
  e := e
  m := QS Ξ e
  m_pos := QS_pos Ξ e
  tower := (good_QS Ξ e).2.1
  B := B Ξ
  ξ := xi Ξ e
  even := by
    rw [← D7.unitsMap_neg_one (QS_dvd Ξ e), xi_unitsMap]
    show ((ZMod.unitsMap _ (-1) : (ZMod M)ˣ) : B Ξ) = 1
    rw [D7.unitsMap_neg_one, QuotientGroup.eq_one_iff, mem_ann]
    exact hev

def frame : Frame := (data Ξ e hev).frame

theorem frame_e : (frame Ξ e hev).e = e := rfl

theorem o_eq : (frame Ξ e hev).o = Nat.card Ξ := by
  rw [← card_B Ξ]
  refine ((data Ξ e hev).o_eq).trans ?_
  show Nat.card (xi Ξ e).range = Nat.card (B Ξ)
  rw [MonoidHom.range_eq_top.mpr (xi_surj Ξ e)]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

theorem twoGroup (h : ∃ j : ℕ, Nat.card Ξ = 2 ^ j) : (frame Ξ e hev).TwoGroup := by
  obtain ⟨j, hj⟩ := h
  have hU : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega),
      show e + 2 - 1 = e + 1 by omega]
    norm_num
  have h2 : Nat.card (HGrp e) ∣ 2 ^ (e + 1) := by
    have h0 := Subgroup.card_quotient_dvd_card (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
    rwa [hU] at h0
  have hB : Nat.card (B Ξ) = 2 ^ j := (card_B Ξ).trans hj
  have h3 : Nat.card (data Ξ e hev).R ∣ 2 ^ (e + 1 + j) := by
    have h1 : Nat.card (data Ξ e hev).R ∣ Nat.card (HGrp e × B Ξ) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_prod, hB] at h1
    rw [pow_add]
    exact h1.trans (mul_dvd_mul_right h2 _)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  exact ⟨k, ((data Ξ e hev).ord_eq).trans hk⟩

theorem QS_le (h : 4 * M ≤ 2 ^ e) : QS Ξ e ≤ (frame Ξ e hev).ord ^ 2 := by
  have h1 := Nat.le_of_dvd (Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero (NeZero.ne M))) (QS_dvd_mul Ξ e)
  have h2 : 2 ^ e ≤ (frame Ξ e hev).ord := (frame Ξ e hev).two_pow_le_ord
  calc QS Ξ e ≤ 2 ^ e * (4 * M) := by rw [pow_add] at h1; linarith
    _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul_left _ h
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul h2 h2

theorem dvd_of_dvd_QS {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (h : l ∣ QS Ξ e) : l ∣ M := by
  rcases (Nat.Prime.dvd_mul hl).mp (h.trans (QS_dvd_mul Ξ e)) with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h1)) h2
  · exact h1

theorem exact_data (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧ (data Ξ e hev).eta v ≠ 1 := by
  have hlt : QS Ξ e / l < QS Ξ e := Nat.div_lt_self (QS_pos Ξ e) hl.one_lt
  have hdv : QS Ξ e / l ∣ QS Ξ e := Nat.div_dvd_of_dvd hd
  by_cases h2 : 2 ^ (e + 2) ∣ QS Ξ e / l
  · by_contra hn
    refine not_good Ξ e hlt ⟨hdv.trans (QS_dvd Ξ e), h2, fun u hu => ?_⟩
    by_contra h3
    refine hn ⟨ZMod.unitsMap (QS_dvd Ξ e) u, ((unitsMap_val_modEq (QS_dvd Ξ e) u).of_dvd hdv).symm.trans hu, fun h4 => h3 ?_⟩
    rw [← xi_unitsMap]
    exact congrArg Prod.snd h4
  · obtain ⟨c, hc⟩ := (good_QS Ξ e).2.1
    have hl2 : l = 2 := by
      by_contra h3
      have h4 : Nat.Coprime (2 ^ (e + 2)) l := Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))
      exact h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact (good_QS Ξ e).2.1))
    subst hl2
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c := by
      rw [hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    have hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c) := by rw [hc]; ring
    have hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1)) := by
      rw [hQ]
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_two_right]
      exact ⟨2 ^ (k + 1) * c, by ring⟩
    have hval : ((ZMod.unitOfCoprime _ hcop : (ZMod (QS Ξ (k + 1)))ˣ) : ZMod (QS Ξ (k + 1))).val ≡ 2 ^ (k + 2) * c + 1
        [MOD QS Ξ (k + 1)] := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact Nat.mod_modEq _ _
    refine ⟨ZMod.unitOfCoprime _ hcop, (hval.of_dvd hdv).trans ?_, fun h4 => ?_⟩
    · rw [hdiv]
      simp [Nat.ModEq]
    · have h5 : hcl (k + 1) (ZMod.unitsMap (good_QS Ξ (k + 1)).2.1 (ZMod.unitOfCoprime _ hcop)) = hcl (k + 1) 1 :=
        congrArg Prod.fst h4
      rw [unitsMap_unitOfCoprime, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
        Units.val_one, Nat.cast_add, Nat.cast_one] at h5
      rcases h5 with h5 | h5
      · refine h2 ?_
        rw [hdiv, ← ZMod.natCast_eq_zero_iff]
        linear_combination h5
      · have h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
          linear_combination h5
        have h7 : 4 ∣ 2 ^ (k + 2) * c + 2 := Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6
        have h8 : 4 ∣ 2 ^ (k + 2) * c := ⟨2 ^ k * c, by ring⟩
        omega

def thetaB (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : B Ξ →* ℂˣ :=
  QuotientGroup.lift (ann Ξ) χ.toUnitHom fun u hu =>
    Units.ext ((MulChar.coe_toUnitHom χ u).trans ((mem_ann Ξ u).mp hu χ hχ))

def theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e hev).Char :=
  (thetaB Ξ χ hχ).comp
    ((data Ξ e hev).xiA.comp (MonoidHom.snd G0 (data Ξ e hev).frame.MA))

theorem theta_mem (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : theta Ξ e hev χ hχ ∈ (frame Ξ e hev).Chat := by
  simp only [Frame.Chat, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · unfold Frame.TrivialOnFirstFactor
    intro s hs
    have h1 := ((data Ξ e hev).mem_cusp_forms_iff_automorphic_compact s).mp hs
    show thetaB Ξ χ hχ ((data Ξ e hev).xiA ((data Ξ e hev).frame.iota s)) = 1
    rw [h1]
    exact map_one (thetaB Ξ χ hχ)
  · show thetaB Ξ χ hχ ((data Ξ e hev).xiA 1) = 1
    rw [map_one]
    exact map_one (thetaB Ξ χ hχ)
  · show thetaB Ξ χ hχ ((data Ξ e hev).xiA 1) = 1
    rw [map_one]
    exact map_one (thetaB Ξ χ hχ)

theorem theta_toA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (s : G0) (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    theta Ξ e hev χ hχ (s, (data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) =
      χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) := by
  show thetaB Ξ χ hχ ((data Ξ e hev).xiA ((data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u))) = _
  have h1 : (data Ξ e hev).xiA ((data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) = xiW Ξ e u :=
    ((data Ξ e hev).xiA_toA (ZMod.unitsMap (QS_dvd Ξ e) u)).trans (xi_unitsMap Ξ e u)
  rw [h1]
  rfl

theorem exists_theta (θ : (frame Ξ e hev).Char) (hθ : θ ∈ (frame Ξ e hev).Chat) : ∃ χ hχ, theta Ξ e hev χ hχ = θ := by
  obtain ⟨h1, h2, h3⟩ := hθ
  set D := data Ξ e hev with hD
  have hsurj : Function.Surjective D.xiA := fun b => by
    obtain ⟨u, rfl⟩ := xi_surj Ξ e b
    exact ⟨D.toA u, D.xiA_toA u⟩
  let θA : D.frame.MA →* ℂˣ := θ.comp (MonoidHom.inr G0 D.frame.MA)
  let θB : B Ξ →* ℂˣ := D.xiA.liftOfSurjective hsurj ⟨θA, fun a ha => h1 a.toAdd ((D.mem_cusp_forms_iff_automorphic_compact a.toAdd).mpr ha)⟩
  have hB : ∀ a, θB (D.xiA a) = θA a := fun a => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hχ : MulChar.ofUnitHom (θB.comp (QuotientGroup.mk' _)) ∈ Ξ := by
    refine (mem_iff Ξ _).mpr fun u hu => ?_
    rw [MulChar.ofUnitHom_coe, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).mpr hu, map_one,
      Units.val_one]
  have h0 : ∀ s : G0, θ (s, 1) = 1 := by
    rintro ⟨s, t⟩
    have h4 : θ (frame Ξ e hev).sg = 1 := by rw [← Frame.cc_mul_iod, map_mul, h2, h3, one_mul]
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
    · exact map_one θ
    · exact h2
    · exact h4
    · exact h3
  refine ⟨_, hχ, MonoidHom.ext fun g => ?_⟩
  obtain ⟨s, a⟩ := g
  obtain ⟨v, rfl⟩ := D.toA_surj a
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective (QS_dvd Ξ e) v
  refine (theta_toA Ξ e hev _ hχ s u).trans (Units.ext ?_)
  have h5 : θ (s, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) = θA (D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) := by
    have h6 : ((s, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) : (frame Ξ e hev).GG) =
        (s, 1) * (1, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) := Prod.ext (mul_one _).symm (one_mul _).symm
    exact (congrArg θ h6).trans ((map_mul θ _ _).trans ((congrArg (· * _) (h0 s)).trans (one_mul _)))
  rw [MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe]
  refine congrArg Units.val (Eq.trans ?_ h5.symm)
  exact (congrArg θB ((D.xiA_toA _).trans (xi_unitsMap Ξ e u))).symm.trans (hB _)

section Host

variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

include hH hc in
theorem coprime_QS : Nat.Coprime (QS Ξ e) (q * d) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  have h2 : Nat.Coprime 2 (q * d) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · exact (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
    · exact (Nat.coprime_primes Nat.prime_two hd).mpr (by omega)
  exact Nat.Coprime.coprime_dvd_left (QS_dvd_mul Ξ e) (Nat.Coprime.mul (Nat.Coprime.pow_left _ h2) hc)

def host : HostRaw (frame Ξ e hev) :=
  (data Ξ e hev).host hH (coprime_QS Ξ e hH hc) he fun l hl h2 h => hs l hl h2 (dvd_of_dvd_QS Ξ e hl h2 h)

theorem host_q : (host Ξ e hev hH hc he hs).q = q := rfl
theorem host_d : (host Ξ e hev hH hc he hs).d = d := rfl
theorem host_QS : (host Ξ e hev hH hc he hs).QS = QS Ξ e := rfl

theorem psQ : (host Ξ e hev hH hc he hs).PsQ := by
  apply (data Ξ e hev).psQ

theorem exact : (host Ξ e hev hH hc he hs).Exact := by
  apply (data Ξ e hev).exact
  intro l hl hd
  exact exact_data Ξ e hev (by omega) l hl hd

theorem muPM (hq : q ≠ 3) : (host Ξ e hev hH hc he hs).MuPM := by
  apply (data Ξ e hev).muPM
  exact hq

theorem coprimeFifteen_of_coprime (h : Nat.Coprime M 15) : (host Ξ e hev hH hc he hs).CoprimeFifteen := by
  show Nat.Coprime (QS Ξ e) 15
  exact Nat.Coprime.coprime_dvd_left (QS_dvd_mul Ξ e) (Nat.Coprime.mul (Nat.Coprime.pow_left _ (by decide)) h)

theorem exists_sqq : ∃ s : (host Ξ e hev hH hc he hs).E, s ^ 2 = -((host Ξ e hev hH hc he hs).q : (host Ξ e hev hH hc he hs).E) ∧
    ∀ σ : (host Ξ e hev hH hc he hs).E ≃ₐ[ℚ] (host Ξ e hev hH hc he hs).E,
      σ s = (((((host Ξ e hev hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (host Ξ e hev hH hc he hs).E) * s := by
  apply (data Ξ e hev).exists_sqq

theorem prim_theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) :
    PChar.of χ = (host Ξ e hev hH hc he hs).prim (theta Ξ e hev χ hχ) := by
  set H := host Ξ e hev hH hc he hs with hHdef
  refine An.Induces.unique (f := fun a => χ (a : ZMod M)) (M := H.condN * M) (mul_ne_zero H.condN_pos.ne' (NeZero.ne M))
    ⟨(PChar.of χ).prim, fun a ha => (An.induces_of χ).2 a ha.coprime_mul_left_right⟩ ⟨(H.prim _).prim, fun a ha => ?_⟩
  have haN : a.Coprime H.condN := ha.coprime_mul_right_right
  have haM : a.Coprime M := ha.coprime_mul_left_right
  have haW : a.Coprime (Nat.lcm (2 ^ (e + 2)) M) :=
    (Nat.Coprime.mul_right (haN.coprime_dvd_right ((H.tower_dvd.mul_right _).mul_right _)) haM).coprime_dvd_right
      (Nat.lcm_dvd_mul _ _)
  refine ((H.isPrimOf_prim _).2 a haN).trans ?_
  show _ = χ (a : ZMod M)
  rw [HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a haN, H.dir_unit, ← ZMod.coe_unitOfCoprime a haM, ← MulChar.coe_toUnitHom]
  refine congrArg Units.val ?_
  have h1 := theta_toA Ξ e hev χ hχ (H.art (ZMod.unitOfCoprime a haN)).1 (ZMod.unitOfCoprime a haW)
  rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at h1
  have h2 : (H.art (ZMod.unitOfCoprime a haN)).2 =
      (data Ξ e hev).toA (ZMod.unitOfCoprime a (haW.coprime_dvd_right (QS_dvd Ξ e))) :=
    congrArg (data Ξ e hev).toA (unitsMap_unitOfCoprime ((data Ξ e hev).m_dvd q d) a haN)
  have h3 : H.art (ZMod.unitOfCoprime a haN) = ((H.art (ZMod.unitOfCoprime a haN)).1,
      (data Ξ e hev).toA (ZMod.unitOfCoprime a (haW.coprime_dvd_right (QS_dvd Ξ e)))) := Prod.ext rfl h2
  exact (congrArg (theta Ξ e hev χ hχ) h3).trans h1

theorem keptEqChat : (host Ξ e hev hH hc he hs).KeptEqChat (Level.ofSub Ξ).KEPT := by
  unfold HostRaw.KeptEqChat HostRaw.Kept
  refine ⟨fun ψ hψ => ?_, fun θ hθ => ?_⟩
  · obtain ⟨χ, hχ, rfl⟩ := (Level.mem_ofSub Ξ ψ).mp hψ
    exact ⟨theta Ξ e hev χ hχ, theta_mem Ξ e hev χ hχ,
      ((host Ξ e hev hH hc he hs).isPrimOf_iff _ _).mpr (prim_theta Ξ e hev hH hc he hs χ hχ)⟩
  · obtain ⟨χ, hχ, rfl⟩ := exists_theta Ξ e hev θ hθ
    exact ⟨PChar.of χ, (Level.mem_ofSub Ξ _).mpr ⟨χ, hχ, rfl⟩,
      ((host Ξ e hev hH hc he hs).isPrimOf_iff _ _).mpr (prim_theta Ξ e hev hH hc he hs χ hχ)⟩

theorem keptInXp : (host Ξ e hev hH hc he hs).KeptInXp (Level.ofSub Ξ).KEPT := by
  have hk := keptEqChat Ξ e hev hH hc he hs
  unfold HostRaw.KeptEqChat at hk
  unfold HostRaw.KeptInXp
  intro ψ hψ
  obtain ⟨θ, hθ, h⟩ := hk.1 ψ hψ
  refine ⟨θ, ?_, h⟩
  simp only [Frame.Chat, Frame.Xp, Set.mem_setOf_eq] at hθ ⊢
  exact ⟨hθ.1, hθ.2.1⟩

theorem exceptional_character_condition : (host Ξ e hev hH hc he hs).ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK := by
  refine ⟨fun ψ h => (by cases h), fun _ h => ?_⟩
  obtain ⟨χ, hχ, h1⟩ := (Level.mem_ofSub Ξ _).mp ((HostRaw.kept_iff _ _ _).mp h)
  rw [prim_theta Ξ e hev hH hc he hs χ hχ] at h1
  have h2 := HostRaw.art_eq_of_prim_eq _ h1 (-1)
  rw [HostRaw.art_neg_one, (theta_mem Ξ e hev χ hχ).2.2] at h2
  have h3 : (1 : ℂ) = ((-1 : ℤ) : ℂ) := congrArg Units.val h2
  norm_num at h3

theorem o_eq_level : (frame Ξ e hev).o = (Level.ofSub Ξ).o := o_eq Ξ e hev

end Host

end EvenGrp

end Formalism.HC

end
end

section
noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

structure ModData where
  e : ℕ
  m : ℕ
  m_pos : 0 < m
  tower : 2 ^ (e + 2) ∣ m
  B : Type
  [grp : CommGroup B]
  ξ : (ZMod m)ˣ →* B

attribute [instance] ModData.grp

namespace ModData

variable (D : ModData)

instance neZero : NeZero D.m := ⟨D.m_pos.ne'⟩

def cl : (ZMod D.m)ˣ →* HGrp D.e := (QuotientGroup.mk' _).comp (ZMod.unitsMap D.tower)

theorem cl_apply (u : (ZMod D.m)ˣ) : D.cl u = hcl D.e (ZMod.unitsMap D.tower u) := rfl

def eta : (ZMod D.m)ˣ →* HGrp D.e × D.B := D.cl.prod D.ξ

theorem cl_neg_one : D.cl (-1) = 1 := by
  rw [cl_apply, D7.unitsMap_neg_one]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

abbrev R : Type := D.eta.range

instance : Finite D.R := Finite.of_surjective _ D.eta.rangeRestrict_surjective

instance : Fintype (Additive D.R) := Fintype.ofFinite _

def p1 : D.R →* HGrp D.e := (MonoidHom.fst _ _).comp D.eta.range.subtype

def p2 : D.R →* D.B := (MonoidHom.snd _ _).comp D.eta.range.subtype

theorem eq_one_of {x : D.R} (h1 : D.p1 x = 1) (h2 : D.p2 x = 1) : x = 1 := Subtype.ext (Prod.ext h1 h2)

theorem projection_surjective : Function.Surjective D.p1 := by
  intro h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective h
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective D.tower u
  refine ⟨⟨D.eta v, v, rfl⟩, ?_⟩
  show D.cl v = _
  rw [cl_apply, hv]
  rfl

theorem exists_gen : ∃ a : D.R, ∀ x : D.R, D.p2 x = 1 ↔ x ∈ Subgroup.zpowers a := by
  haveI : IsCyclic (HGrp D.e) := (hostGroup D.e).2.2.2.2.2.1
  have hinj : Function.Injective (D.p1.comp D.p2.ker.subtype) := by
    intro x y hxy
    have hxy' : D.p1 x.1 = D.p1 y.1 := hxy
    have h1 : D.p1 (x.1 * y.1⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy', mul_inv_cancel]
    have h2 : D.p2 (x.1 * y.1⁻¹) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp x.2, MonoidHom.mem_ker.mp y.2, inv_one, mul_one]
    exact Subtype.ext (mul_inv_eq_one.mp (D.eq_one_of h1 h2))
  haveI : IsCyclic D.p2.ker := isCyclic_of_injective (D.p1.comp D.p2.ker.subtype) hinj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D.p2.ker)
  refine ⟨g.1, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h3 := congrArg Subtype.val hk
    simpa using h3
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [map_zpow, MonoidHom.mem_ker.mp g.2, one_zpow]

def gen : D.R := D.exists_gen.choose

theorem gen_spec (x : D.R) : D.p2 x = 1 ↔ x ∈ Subgroup.zpowers D.gen := D.exists_gen.choose_spec x

def hA : Additive D.R →+ Additive (HGrp D.e) := MonoidHom.toAdditive D.p1

theorem hA_surj : Function.Surjective D.hA := D.projection_surjective

theorem hA_ker (k : ℤ) (hk : D.hA (k • Additive.ofMul D.gen) = 0) : k • Additive.ofMul D.gen = 0 := by
  rw [← ofMul_zpow] at hk ⊢
  have h2 : D.p2 (D.gen ^ k) = 1 := by
    rw [map_zpow, (D.gen_spec D.gen).mpr (Subgroup.mem_zpowers _), one_zpow]
  have h1 : D.p1 (D.gen ^ k) = 1 := by
    rw [← ofMul_eq_zero]
    exact hk
  rw [ofMul_eq_zero]
  exact D.eq_one_of h1 h2

def frame : Frame := Frame.ofGroup D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker

def isoA : D.frame.A ≃+ Additive D.R := Frame.ofGroupIso D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker

def iso : D.frame.MA ≃* D.R where
  toFun a := (D.isoA a.toAdd).toMul
  invFun x := Multiplicative.ofAdd (D.isoA.symm (Additive.ofMul x))
  left_inv a := by simp
  right_inv x := by simp
  map_mul' a b := by simp

theorem frame_e : D.frame.e = D.e := rfl

theorem hH_eq (a : D.frame.MA) : D.frame.hH a = D.p1 (D.iso a) := rfl


theorem ord_eq : D.frame.ord = Nat.card D.R := by
  rw [frame, Frame.ofGroup_ord, ← Nat.card_eq_fintype_card]
  rfl

def toA : (ZMod D.m)ˣ →* D.frame.MA := D.iso.symm.toMonoidHom.comp D.eta.rangeRestrict

theorem iso_toA (u : (ZMod D.m)ˣ) : D.iso (D.toA u) = D.eta.rangeRestrict u := D.iso.apply_symm_apply _

theorem toA_surj : Function.Surjective D.toA := D.iso.symm.surjective.comp (MonoidHom.rangeRestrict_surjective _)

theorem toA_eq_one_iff (u : (ZMod D.m)ˣ) : D.toA u = 1 ↔ D.eta u = 1 := by
  rw [← D.iso.injective.eq_iff, map_one, iso_toA, Subtype.ext_iff]
  rfl

theorem hH_toA (u : (ZMod D.m)ˣ) : D.frame.hH (D.toA u) = D.cl u := by
  rw [hH_eq, iso_toA]
  rfl

def xiA : D.frame.MA →* D.B := D.p2.comp D.iso.toMonoidHom

theorem xiA_toA (u : (ZMod D.m)ˣ) : D.xiA (D.toA u) = D.ξ u := by
  show D.p2 (D.iso (D.toA u)) = _
  rw [iso_toA]
  rfl

theorem mem_cusp_forms_iff_automorphic_compact (t : D.frame.A) : t ∈ D.frame.A0 ↔ D.xiA (D.frame.iota t) = 1 := by
  have ha0 : D.isoA D.frame.a0 = Additive.ofMul D.gen :=
    Frame.ofGroup_generator D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker
  show t ∈ AddSubgroup.zmultiples D.frame.a0 ↔ D.p2 ((D.isoA t).toMul) = 1
  rw [D.gen_spec, AddSubgroup.mem_zmultiples_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [map_zsmul, ha0]; rfl⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, D.isoA.injective ?_⟩
    rw [map_zsmul, ha0, ← ofMul_zpow, hk]
    rfl

theorem o_eq : D.frame.o = Nat.card D.ξ.range := by
  have hker : D.p2.ker = Subgroup.zpowers D.gen := by
    ext x
    exact D.gen_spec x
  have hn0 : D.frame.n0 = Nat.card D.p2.ker := by
    rw [hker, Nat.card_zpowers, frame, Frame.ofGroup_order, addOrderOf_ofMul_eq_orderOf]
  have hs : D.p2.range = D.ξ.range := by
    ext b
    constructor
    · rintro ⟨⟨_, v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨D.eta v, v, rfl⟩, rfl⟩
  have hmul := Subgroup.card_mul_index D.p2.ker
  rw [Subgroup.index_ker, hs] at hmul
  unfold Frame.o
  rw [ord_eq, hn0, ← hmul]
  have hpos : 0 < Nat.card D.p2.ker := Nat.card_pos
  exact Nat.mul_div_cancel_left _ hpos

theorem twoGroup (h : ∃ j : ℕ, ∀ u, D.ξ u ^ 2 ^ j = 1) : D.frame.TwoGroup := by
  obtain ⟨j, hj⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : Nat.card (HGrp D.e) = 2 ^ D.e := (hostGroup D.e).2.2.2.2.2.2.1
  have hp : IsPGroup 2 D.R := by
    intro x
    refine ⟨D.e + j, ?_⟩
    obtain ⟨_, u, rfl⟩ := x
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst]
      show (D.cl u) ^ 2 ^ (D.e + j) = 1
      rw [show 2 ^ (D.e + j) = Nat.card (HGrp D.e) * 2 ^ j by rw [hH, pow_add], pow_mul,
        pow_card_eq_one', one_pow]
    · rw [Prod.pow_snd]
      show (D.ξ u) ^ 2 ^ (D.e + j) = 1
      rw [show 2 ^ (D.e + j) = 2 ^ j * 2 ^ D.e by rw [pow_add, mul_comm], pow_mul, hj, one_pow]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  exact ⟨k, by rw [ord_eq, hk]⟩

def w : ℤˣ →* D.frame.MA := D.toA.comp (Units.map (Int.castRingHom (ZMod D.m)).toMonoidHom)

theorem w_neg_one : D.w (-1) = D.toA (-1) := by
  show D.toA (Units.map (Int.castRingHom (ZMod D.m)).toMonoidHom (-1)) = _
  congr 1
  ext
  simp

theorem w_mul_self (s : ℤˣ) : D.w s * D.w s = 1 := by
  rw [← map_mul, Int.units_mul_self, map_one]

theorem hH_w (s : ℤˣ) : D.frame.hH (D.w s) = 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [map_one, map_one]
  · rw [w_neg_one, hH_toA, cl_neg_one]
    rfl

section Host

variable {q d : ℕ} (hH : HostHyp q d)

theorem m_dvd (q d : ℕ) : D.m ∣ D.m * q * d := ⟨q * d, by ring⟩
theorem q_dvd (q d : ℕ) : q ∣ D.m * q * d := ⟨D.m * d, by ring⟩
theorem d_dvd (q d : ℕ) : d ∣ D.m * q * d := ⟨D.m * q, by ring⟩

include hH in
theorem neZeroN : NeZero (D.m * q * d) := by
  have h1 := hH.1.pos
  have h2 := hH.2.1.pos
  have h3 := D.m_pos
  exact ⟨by positivity⟩

def art : (ZMod (D.m * q * d))ˣ →* D.frame.GG :=
  ((D7.sgnN hH.1 (D.q_dvd q d)).prod (D7.sgnN hH.2.1 (D.d_dvd q d))).prod
    (D.toA.comp (ZMod.unitsMap (D.m_dvd q d)) * D.w.comp (D7.sgnN hH.1 (D.q_dvd q d)))

theorem art_snd (u : (ZMod (D.m * q * d))ˣ) :
    (D.art hH u).2 = D.toA (ZMod.unitsMap (D.m_dvd q d) u) * D.w (D.art hH u).1.1 := rfl

theorem art_ps (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q := by
  haveI := D.neZeroN hH
  exact D7.sgnN_val hH.1 (D.q_dvd q d) u

theorem art_ch (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d := by
  haveI := D.neZeroN hH
  exact D7.sgnN_val hH.2.1 (D.d_dvd q d) u

theorem art_ps_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD q])
    (hy : jacobiSym (y : ℤ) q = 1) : (D.art hH u).1.1 = 1 := by
  have h := D.art_ps hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q = jacobiSym (y : ℤ) q := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ), ← Int.natCast_mod, ← Int.natCast_mod,
      show (u : ZMod (D.m * q * d)).val % q = y % q from hu]
  exact Units.ext (by rw [h, h2, hy]; rfl)

theorem art_ch_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD d])
    (hy : jacobiSym (y : ℤ) d = 1) : (D.art hH u).1.2 = 1 := by
  have h := D.art_ch hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d = jacobiSym (y : ℤ) d := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ), ← Int.natCast_mod, ← Int.natCast_mod,
      show (u : ZMod (D.m * q * d)).val % d = y % d from hu]
  exact Units.ext (by rw [h, h2, hy]; rfl)

theorem art_snd_one (u : (ZMod (D.m * q * d))ˣ) (hu : (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m]) :
    (D.art hH u).2 = D.w (D.art hH u).1.1 := by
  haveI := D.neZeroN hH
  have h1 : ZMod.unitsMap (D.m_dvd q d) u = 1 := by
    apply Units.ext
    rw [D7.unitsMap_val, Units.val_one]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
    simpa using h2
  rw [art_snd, h1, map_one, one_mul]

theorem art_eq_one (u : (ZMod (D.m * q * d))ˣ) (h1 : (D.art hH u).1.1 = 1) (h2 : (D.art hH u).1.2 = 1)
    (h3 : D.eta (ZMod.unitsMap (D.m_dvd q d) u) = 1) : D.art hH u = 1 := by
  refine Prod.ext (Prod.ext h1 h2) ?_
  rw [art_snd, h1, map_one, mul_one]
  exact (D.toA_eq_one_iff _).mpr h3

include hH in
theorem eta_one (u : (ZMod (D.m * q * d))ˣ) (hu : (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m]) :
    D.eta (ZMod.unitsMap (D.m_dvd q d) u) = 1 := by
  haveI := D.neZeroN hH
  have h1 : ZMod.unitsMap (D.m_dvd q d) u = 1 := by
    apply Units.ext
    rw [D7.unitsMap_val, Units.val_one]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
    simpa using h2
  rw [h1, map_one]

variable (hc : Nat.Coprime D.m (q * d))

include hc in
theorem art_surj : Function.Surjective (D.art hH) := by
  have := D.neZeroN hH
  intro g
  obtain ⟨v, hv⟩ := D.toA_surj (g.2 * D.w g.1.1)
  obtain ⟨y, cy, hy⟩ := D7.exists_sign hH.1 (D7.q4 hH) g.1.1
  obtain ⟨z, cz, hz⟩ := D7.exists_sign hH.2.1 (D7.d4 hH) g.1.2
  obtain ⟨u, h1, h2, h3⟩ := exists_unit_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
    (v : ZMod D.m).val y z (ZMod.val_coe_unit_coprime v) cy cz
  have h4 : (D.art hH u).1.1 = g.1.1 := Units.ext (by rw [art_ps, D7.jac_congr h2, hy])
  refine ⟨u, Prod.ext (Prod.ext h4 (Units.ext ?_)) ?_⟩
  · rw [art_ch, D7.jac_congr h3, hz]
  · rw [art_snd, (unitsMap_eq_iff _ u v).mpr h1, hv, h4, mul_assoc, w_mul_self, mul_one]

variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)

def charData : CharData D.frame where
  q := q
  d := d
  QS := D.m
  hyp := hH
  two_le_e := he
  QS_pos := D.m_pos
  tower_dvd := D.tower
  QS_coprime := hc
  QS_split := hs
  art := D.art hH
  art_surj := D.art_surj hH hc
  art_neg_one := by
    have h1 : (D.art hH (-1)).1.1 = -1 := D7.sgnN_neg_one hH.1 (D7.q4 hH) _
    refine Prod.ext (Prod.ext h1 (D7.sgnN_neg_one hH.2.1 (D7.d4 hH) _)) ?_
    rw [art_snd, D7.unitsMap_neg_one, h1, ← w_neg_one]
    exact D.w_mul_self _
  art_h := fun u v hv => by
    have := D.neZeroN hH
    rw [art_snd, map_mul, hH_w, mul_one, hH_toA, cl_apply, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
    exact congrArg (hcl D.e) (Units.ext ((D7.unitsMap_val _ u).trans hv.symm))
  art_d := fun u hu => by
    have h1 := D.art_ps_one hH u (hu.of_dvd (dvd_mul_left _ _)) (by simp)
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    rw [h1, map_one] at h2
    rcases Int.units_eq_one_or (D.art hH u).1.2 with h3 | h3
    · exact Or.inl (Prod.ext (Prod.ext h1 h3) h2)
    · exact Or.inr (Prod.ext (Prod.ext h1 h3) h2)
  art_q := fun u hu => by
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    refine Prod.ext (Prod.ext (Int.units_sq _) (Int.units_sq _)) ?_
    show (D.art hH u).2 ^ 2 = 1
    rw [h2, sq, w_mul_self]
  art_ch := D.art_ch hH

def host : HostRaw D.frame := (D.charData hH hc he hs).toHostRaw

theorem host_q : (D.host hH hc he hs).q = q := rfl
theorem host_d : (D.host hH hc he hs).d = d := rfl
theorem host_QS : (D.host hH hc he hs).QS = D.m := rfl

theorem psQ : (D.host hH hc he hs).PsQ := D.art_ps hH

theorem exists_sqq : ∃ s : (D.host hH hc he hs).E, s ^ 2 = -((D.host hH hc he hs).q : (D.host hH hc he hs).E) ∧
    ∀ σ : (D.host hH hc he hs).E ≃ₐ[ℚ] (D.host hH hc he hs).E,
      σ s = (((((D.host hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (D.host hH hc he hs).E) * s :=
  (D.charData hH hc he hs).exists_sqq (D.psQ hH hc he hs)

theorem muPM (hq : q ≠ 3)
    (hmu : ∀ k : ℕ, k ∣ D.m → (∀ v : (ZMod D.m)ˣ, D.eta v = 1 → (v : ZMod D.m).val ≡ 1 [MOD k]) → k ∣ 2) : (D.host hH hc he hs).MuPM := by
  have := D.neZeroN hH
  refine (D.charData hH hc he hs).muPM fun k (hk : k ∣ D.m * q * d)
    (h : ∀ u : (ZMod (D.m * q * d))ˣ, D.art hH u = 1 → (u : ZMod (D.m * q * d)).val ≡ 1 [MOD k]) => ?_
  have hq2 := D7.q4 hH
  have hd2 := D7.d4 hH
  have c4 : ∀ p : ℕ, p % 4 = 3 → Nat.Coprime 4 p := fun p hp =>
    Nat.Coprime.pow_left 2 ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega)))
  have j4 : ∀ p : ℕ, p % 4 = 3 → jacobiSym ((4 : ℕ) : ℤ) p = 1 := fun p hp => by
    have h2 : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega))
    exact jacobiSym.sq_one' (a := 2) h2
  have n4 : ∀ p : ℕ, p.Prime → p ≠ 3 → ¬ 4 ≡ 1 [MOD p] := fun p hp h3 h4 =>
    h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ((Nat.modEq_iff_dvd' (by norm_num)).mp h4.symm))
  have ex := exists_unit_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
  have kq : Nat.Coprime k q := by
    refine ((Nat.Prime.coprime_iff_not_dvd hH.1).mpr fun hqk => ?_).symm
    obtain ⟨u, h1, h2, h3⟩ := ex 1 4 1 (Nat.coprime_one_left _) (c4 q hq2) (Nat.coprime_one_left _)
    have h4 := h u (D.art_eq_one hH u (D.art_ps_one hH u h2 (j4 q hq2)) (D.art_ch_one hH u h3 (by simp))
      (D.eta_one hH u h1))
    exact n4 q hH.1 hq (h2.symm.trans (h4.of_dvd hqk))
  have kd : Nat.Coprime k d := by
    refine ((Nat.Prime.coprime_iff_not_dvd hH.2.1).mpr fun hqk => ?_).symm
    obtain ⟨u, h1, h2, h3⟩ := ex 1 1 4 (Nat.coprime_one_left _) (Nat.coprime_one_left _) (c4 d hd2)
    have h4 := h u (D.art_eq_one hH u (D.art_ps_one hH u h2 (by simp)) (D.art_ch_one hH u h3 (j4 d hd2))
      (D.eta_one hH u h1))
    exact n4 d hH.2.1 (by have := hH.2.2.2.1; omega) (h3.symm.trans (h4.of_dvd hqk))
  have km : k ∣ D.m := kq.dvd_of_dvd_mul_right (kd.dvd_of_dvd_mul_right hk)
  refine hmu k km fun v hv => ?_
  obtain ⟨u, h1, h2, h3⟩ := ex (v : ZMod D.m).val 1 1 (ZMod.val_coe_unit_coprime _)
    (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  have h4 := h u (D.art_eq_one hH u (D.art_ps_one hH u h2 (by simp)) (D.art_ch_one hH u h3 (by simp)) (by
    rw [(unitsMap_eq_iff _ u _).mpr h1, hv]))
  exact (h1.of_dvd km).symm.trans h4

theorem exact (h : ∀ l : ℕ, l.Prime → l ∣ D.m → ∃ v : (ZMod D.m)ˣ, (v : ZMod D.m).val ≡ 1 [MOD D.m / l] ∧ D.eta v ≠ 1) :
    (D.host hH hc he hs).Exact := by
  have := D.neZeroN hH
  intro l hl (hlm : l ∣ D.m)
  obtain ⟨v, hv, hv1⟩ := h l hl hlm
  obtain ⟨u, h1, h2, h3⟩ := exists_unit_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
    (v : ZMod D.m).val 1 1 (ZMod.val_coe_unit_coprime v) (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  refine ⟨u, ?_, fun h4 => hv1 ?_⟩
  · show (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m * q * d / l]
    have h5 : D.m * q * d / l = D.m / l * (q * d) := by rw [mul_assoc, Nat.div_mul_right_comm hlm]
    have h6 : D.m / l ∣ D.m := Nat.div_dvd_of_dvd hlm
    rw [h5]
    exact (Nat.modEq_and_modEq_iff_modEq_mul (hc.coprime_dvd_left h6)).mp
      ⟨(h1.of_dvd h6).trans hv, (Nat.modEq_and_modEq_iff_modEq_mul (D7.cop_qd hH)).mp ⟨h2, h3⟩⟩
  · have h5 : (D.art hH u).2 = 1 := congrArg Prod.snd h4
    rw [art_snd, (unitsMap_eq_iff _ u v).mpr h1, D.art_ps_one hH u h2 (by simp), map_one, mul_one] at h5
    exact (D.toA_eq_one_iff v).mp h5

end Host

end ModData

end Formalism.HC

end
end

section
noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

namespace AnyGrp

open EvenGrp hiding data frame frame_e o_eq twoGroup QS_le exact_data theta theta_mem host host_q host_d host_QS psQ exact muPM
  coprimeFifteen_of_coprime exists_sqq prim_theta keptInXp exceptional_character_condition o_eq_level

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

def data : ModData where
  e := e
  m := QS Ξ e
  m_pos := QS_pos Ξ e
  tower := (good_QS Ξ e).2.1
  B := B Ξ
  ξ := xi Ξ e

abbrev frame : Frame := (data Ξ e).frame

theorem frame_e : (frame Ξ e).e = e := rfl

theorem o_eq : (frame Ξ e).o = Nat.card Ξ := by
  show (data Ξ e).frame.o = _
  rw [ModData.o_eq]
  show Nat.card (xi Ξ e).range = _
  rw [MonoidHom.range_eq_top.mpr (EvenGrp.xi_surj Ξ e), Subgroup.card_top]
  exact EvenGrp.card_B Ξ

theorem twoGroup (h : ∃ j : ℕ, Nat.card Ξ = 2 ^ j) : (frame Ξ e).TwoGroup := by
  obtain ⟨j, hj⟩ := h
  apply ModData.twoGroup
  refine ⟨j, fun u => ?_⟩
  have h2 : Nat.card (B Ξ) = 2 ^ j := (EvenGrp.card_B Ξ).trans hj
  rw [← h2]
  exact pow_card_eq_one'

theorem QS_le (h : 4 * M ≤ 2 ^ e) : QS Ξ e ≤ (frame Ξ e).ord ^ 2 := by
  have h1 := Nat.le_of_dvd (Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero (NeZero.ne M))) (QS_dvd_mul Ξ e)
  have h2 : 2 ^ e ≤ (frame Ξ e).ord := (frame Ξ e).two_pow_le_ord
  calc QS Ξ e ≤ 2 ^ e * (4 * M) := by rw [pow_add] at h1; linarith
    _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul_left _ h
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul h2 h2

theorem exact_data (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧ (data Ξ e).eta v ≠ 1 := by
  have hlt : QS Ξ e / l < QS Ξ e := Nat.div_lt_self (QS_pos Ξ e) hl.one_lt
  have hdv : QS Ξ e / l ∣ QS Ξ e := Nat.div_dvd_of_dvd hd
  by_cases h2 : 2 ^ (e + 2) ∣ QS Ξ e / l
  · by_contra hn
    refine not_good Ξ e hlt ⟨hdv.trans (QS_dvd Ξ e), h2, fun u hu => ?_⟩
    by_contra h3
    refine hn ⟨ZMod.unitsMap (QS_dvd Ξ e) u, ((unitsMap_val_modEq (QS_dvd Ξ e) u).of_dvd hdv).symm.trans hu, fun h4 => h3 ?_⟩
    rw [← xi_unitsMap]
    exact congrArg Prod.snd h4
  · obtain ⟨c, hc⟩ := (good_QS Ξ e).2.1
    have hl2 : l = 2 := by
      by_contra h3
      have h4 : Nat.Coprime (2 ^ (e + 2)) l := Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))
      exact h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact (good_QS Ξ e).2.1))
    subst hl2
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c := by
      rw [hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    have hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c) := by rw [hc]; ring
    have hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1)) := by
      rw [hQ]
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_two_right]
      exact ⟨2 ^ (k + 1) * c, by ring⟩
    have hval : ((ZMod.unitOfCoprime _ hcop : (ZMod (QS Ξ (k + 1)))ˣ) : ZMod (QS Ξ (k + 1))).val ≡ 2 ^ (k + 2) * c + 1
        [MOD QS Ξ (k + 1)] := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact Nat.mod_modEq _ _
    refine ⟨ZMod.unitOfCoprime _ hcop, (hval.of_dvd hdv).trans ?_, fun h4 => ?_⟩
    · rw [hdiv]
      simp [Nat.ModEq]
    · have h5 : hcl (k + 1) (ZMod.unitsMap (good_QS Ξ (k + 1)).2.1 (ZMod.unitOfCoprime _ hcop)) = hcl (k + 1) 1 :=
        congrArg Prod.fst h4
      rw [unitsMap_unitOfCoprime, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
        Units.val_one, Nat.cast_add, Nat.cast_one] at h5
      rcases h5 with h5 | h5
      · refine h2 ?_
        rw [hdiv, ← ZMod.natCast_eq_zero_iff]
        linear_combination h5
      · have h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
          linear_combination h5
        have h7 : 4 ∣ 2 ^ (k + 2) * c + 2 := Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6
        have h8 : 4 ∣ 2 ^ (k + 2) * c := ⟨2 ^ k * c, by ring⟩
        omega

def thetaA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e).MA →* ℂˣ := (thetaB Ξ χ hχ).comp (data Ξ e).xiA

def theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e).Char :=
  (thetaA Ξ e χ hχ).comp (MonoidHom.snd G0 (frame Ξ e).MA * (data Ξ e).w.comp (frame Ξ e).chQ)

theorem theta_mem (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : theta Ξ e χ hχ ∈ (frame Ξ e).Xp := by
  refine ⟨fun s hs => ?_, ?_⟩
  · have h1 : (frame Ξ e).iota s * (data Ξ e).w 1 = (frame Ξ e).iota s :=
      (congrArg ((frame Ξ e).iota s * ·) (map_one (data Ξ e).w)).trans (mul_one _)
    exact (congrArg (thetaA Ξ e χ hχ) h1).trans
      ((congrArg (thetaB Ξ χ hχ) (((data Ξ e).mem_cusp_forms_iff_automorphic_compact s).mp hs)).trans (map_one _))
  · exact (congrArg (thetaA Ξ e χ hχ) ((one_mul _).trans (map_one (data Ξ e).w))).trans (map_one _)

theorem thetaA_toA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) =
      χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) :=
  congrArg (thetaB Ξ χ hχ) (((data Ξ e).xiA_toA _).trans (xi_unitsMap Ξ e u))

section Host

variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

def host : HostRaw (frame Ξ e) :=
  (data Ξ e).host hH (coprime_QS Ξ e hH hc) he fun l hl h2 h => hs l hl h2 (dvd_of_dvd_QS Ξ e hl h2 h)

theorem host_q : (host Ξ e hH hc he hs).q = q := rfl
theorem host_d : (host Ξ e hH hc he hs).d = d := rfl
theorem host_QS : (host Ξ e hH hc he hs).QS = QS Ξ e := rfl

theorem psQ : (host Ξ e hH hc he hs).PsQ := by
  unfold host
  apply ModData.psQ

theorem exact : (host Ξ e hH hc he hs).Exact := by
  unfold host
  apply ModData.exact
  intro l hl hd
  exact exact_data Ξ e (by omega) l hl hd

theorem muPM (hq : q ≠ 3) (hmu : ∀ k : ℕ, k ∣ QS Ξ e →
    (∀ v : (ZMod (QS Ξ e))ˣ, (data Ξ e).eta v = 1 → (v : ZMod (QS Ξ e)).val ≡ 1 [MOD k]) → k ∣ 2) :
    (host Ξ e hH hc he hs).MuPM := by
  unfold host
  apply ModData.muPM (hq := hq) (hmu := hmu)

theorem coprimeFifteen_of_coprime (h : Nat.Coprime M 15) : (host Ξ e hH hc he hs).CoprimeFifteen :=
  (Nat.Coprime.mul_left (Nat.Coprime.pow_left _ (by norm_num)) h).coprime_dvd_left (QS_dvd_mul Ξ e)

theorem exists_sqq : ∃ s : (host Ξ e hH hc he hs).E, s ^ 2 = -((host Ξ e hH hc he hs).q : (host Ξ e hH hc he hs).E) ∧
    ∀ σ : (host Ξ e hH hc he hs).E ≃ₐ[ℚ] (host Ξ e hH hc he hs).E,
      σ s = (((((host Ξ e hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (host Ξ e hH hc he hs).E) * s := by
  unfold host
  apply ModData.exists_sqq

theorem theta_art (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (u : (ZMod (QS Ξ e * q * d))ˣ) :
    theta Ξ e χ hχ ((host Ξ e hH hc he hs).art u) =
      thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) :=
  congrArg (thetaA Ξ e χ hχ) ((mul_assoc _ _ _).trans
    ((congrArg (_ * ·) ((data Ξ e).w_mul_self ((data Ξ e).art hH u).1.1)).trans (mul_one _)))

theorem prim_theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) :
    PChar.of χ = (host Ξ e hH hc he hs).prim (theta Ξ e χ hχ) := by
  set H := host Ξ e hH hc he hs with hHdef
  refine An.Induces.unique (f := fun a => χ (a : ZMod M)) (M := H.condN * M) (mul_ne_zero H.condN_pos.ne' (NeZero.ne M))
    ⟨(PChar.of χ).prim, fun a ha => (An.induces_of χ).2 a ha.coprime_mul_left_right⟩ ⟨(H.prim _).prim, fun a ha => ?_⟩
  have haN : a.Coprime H.condN := ha.coprime_mul_right_right
  have haM : a.Coprime M := ha.coprime_mul_left_right
  have haW : a.Coprime (Nat.lcm (2 ^ (e + 2)) M) :=
    (Nat.Coprime.mul_right (haN.coprime_dvd_right ((H.tower_dvd.mul_right _).mul_right _)) haM).coprime_dvd_right
      (Nat.lcm_dvd_mul _ _)
  refine ((H.isPrimOf_prim _).2 a haN).trans ?_
  show _ = χ (a : ZMod M)
  rw [HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a haN, H.dir_unit, ← ZMod.coe_unitOfCoprime a haM, ← MulChar.coe_toUnitHom]
  refine congrArg Units.val ?_
  have h1 := thetaA_toA Ξ e χ hχ (ZMod.unitOfCoprime a haW)
  rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at h1
  exact (theta_art Ξ e hH hc he hs χ hχ _).trans ((congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v))
    (unitsMap_unitOfCoprime ((data Ξ e).m_dvd q d) a haN)).trans h1)

theorem keptInXp : (host Ξ e hH hc he hs).KeptInXp (Level.ofSub Ξ).KEPT := fun ψ hψ => by
  obtain ⟨χ, hχ, rfl⟩ := (Level.mem_ofSub Ξ ψ).mp hψ
  exact ⟨_, theta_mem Ξ e χ hχ, (HostRaw.isPrimOf_iff _ _ _).mpr (prim_theta Ξ e hH hc he hs χ hχ)⟩

theorem exceptional_character_condition : (host Ξ e hH hc he hs).ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK := by
  refine ⟨fun ψ h => (by cases h), fun _ h => ?_⟩
  obtain ⟨χ, hχ, h1⟩ := (Level.mem_ofSub Ξ _).mp ((HostRaw.kept_iff _ _ _).mp h)
  rw [prim_theta Ξ e hH hc he hs χ hχ] at h1
  have : NeZero (QS Ξ e * q * d) := (data Ξ e).neZeroN hH
  have : NeZero ((data Ξ e).m * q * d) := this
  have hco := coprime_QS Ξ e hH hc
  obtain ⟨y, cy, hy⟩ := D7.exists_sign hH.1 (D7.q4 hH) (-1)
  obtain ⟨u, u1, u2, -⟩ := exists_unit_three hco.coprime_mul_right_right hco.coprime_mul_left_right (D7.cop_qd hH)
    1 y 1 (Nat.coprime_one_left _) cy (Nat.coprime_one_left _)
  have h2 := (theta_art Ξ e hH hc he hs χ hχ u).symm.trans (HostRaw.art_eq_of_prim_eq _ h1 u)
  have h3 : thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) = 1 :=
    (congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v))
      ((unitsMap_eq_one_iff ((data Ξ e).m_dvd q d) u).mpr u1)).trans
      ((congrArg (thetaA Ξ e χ hχ) (map_one (data Ξ e).toA)).trans (map_one _))
  have h4 : ((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) = -1 := ((data Ξ e).art_ps hH u).trans ((D7.jac_congr u2).trans hy)
  have h5 : (1 : ℂ) = (((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) : ℂ) := congrArg Units.val (h3.symm.trans h2)
  rw [h4] at h5
  norm_num at h5

theorem o_eq_level : (frame Ξ e).o = (Level.ofSub Ξ).o := by
  rw [o_eq]
  rfl

end Host

end AnyGrp

end Formalism.HC

end
end
