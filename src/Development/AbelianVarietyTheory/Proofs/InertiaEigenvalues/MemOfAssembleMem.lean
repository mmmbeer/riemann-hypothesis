import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.KernelCharacterDelta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubIdBijOfContracting

section
noncomputable section
namespace GlobalTheory.PsiLemmaCompare
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.IndefiniteRowSideFullHecke

section Subst
variable {k : Type} [Field k]

theorem vv_eq : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by simp [vv]

theorem vv_ne : vv k ≠ 0 := by simp [vv]

theorem single_eq (m : ℤ) : (HahnSeries.single m 1 : k⸨X⸩) = vv k ^ m := by
  rw [vv, ← RatFunc.single_zpow]

theorem coe_ne {f : k⟦X⟧} (h : f ≠ 0) : (f : k⸨X⸩) ≠ 0 := fun e =>
  h (HahnSeries.ofPowerSeries_injective (e.trans (map_zero _).symm))

def substHom (f : k⟦X⟧) (h0 : PowerSeries.constantCoeff f = 0) (h1 : f ≠ 0) : k⸨X⸩ →+* k⸨X⸩ :=
  IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : k⟦X⟧))
    (g := (HahnSeries.ofPowerSeries ℤ k).comp
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom)
    (by
      rintro ⟨_, n, rfl⟩
      refine IsUnit.mk0 _ ?_
      simp only [map_pow]
      refine pow_ne_zero _ ?_
      simpa [PowerSeries.substAlgHom_X] using coe_ne h1)

theorem substHom_coe (f : k⟦X⟧) (h0 : PowerSeries.constantCoeff f = 0) (h1 : f ≠ 0) (a : k⟦X⟧) :
    substHom f h0 h1 (a : k⸨X⸩) = ((a.subst f : k⟦X⟧) : k⸨X⸩) := by
  have := IsLocalization.lift_eq (S := k⸨X⸩) (M := Submonoid.powers (PowerSeries.X : k⟦X⟧))
    (g := (HahnSeries.ofPowerSeries ℤ k).comp
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom)
    (by
      rintro ⟨_, n, rfl⟩
      refine IsUnit.mk0 _ ?_
      simp only [map_pow]
      refine pow_ne_zero _ ?_
      simpa [PowerSeries.substAlgHom_X] using coe_ne h1) a
  refine this.trans ?_
  simp [PowerSeries.coe_substAlgHom]

theorem substL_eq (f : k⟦X⟧) (h0 : PowerSeries.constantCoeff f = 0) (h1 : f ≠ 0) (x : k⸨X⸩) :
    FrobeniusBinomialReduction.substL f x = substHom f h0 h1 x := by
  conv_rhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart x]
  rw [map_mul, substHom_coe, single_eq, map_zpow₀, vv_eq, substHom_coe,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' h0), FrobeniusBinomialReduction.substL]

theorem hom_ext {F G : k⸨X⸩ →+* k⸨X⸩} (h : ∀ a : k⟦X⟧, F (a : k⸨X⸩) = G (a : k⸨X⸩)) : F = G :=
  IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : k⟦X⟧)) (RingHom.ext h)

theorem exists_mul_pow (x : k⸨X⸩) : ∃ (n : ℕ) (a : k⟦X⟧), x * vv k ^ n = (a : k⸨X⸩) := by
  obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : k⟦X⟧)) x
  refine ⟨n, a, ?_⟩
  simpa [vv_eq] using h

end Subst

section Frob
variable (k : Type) [Field k] (l : ℕ) [hl : Fact l.Prime]

theorem phiPi_coeff_mul (x : k⸨X⸩) (q : ℤ) : (OnePlusPowerCharacters.phiPi k l x).coeff (l * q) = x.coeff q := by
  unfold OnePlusPowerCharacters.phiPi
  erw [HahnSeries.embDomainRingHom_apply]
  exact HahnSeries.embDomain_coeff (a := q)

theorem phiPi_coeff_not (x : k⸨X⸩) (n : ℤ) (h : ¬ (l : ℤ) ∣ n) : (OnePlusPowerCharacters.phiPi k l x).coeff n = 0 := by
  unfold OnePlusPowerCharacters.phiPi
  erw [HahnSeries.embDomainRingHom_apply]
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨q, rfl⟩
  exact h ⟨q, rfl⟩

theorem coeff_neg (a : k⟦X⟧) {n : ℤ} (h : n < 0) : (a : k⸨X⸩).coeff n = 0 := by
  rw [PowerSeries.coeff_coe, if_pos h]

theorem phiPi_eq (x : k⸨X⸩) : OnePlusPowerCharacters.phiPi k l x = FrobeniusBinomialReduction.frobπ k l x := by
  have hp := hl.out.ne_zero
  have h0 : PowerSeries.constantCoeff ((PowerSeries.X : k⟦X⟧) ^ l) = 0 := by simp [hp]
  have h1 : ((PowerSeries.X : k⟦X⟧) ^ l) ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  rw [FrobeniusBinomialReduction.frobπ, substL_eq _ h0 h1]
  congr 1
  refine hom_ext fun a => ?_
  rw [substHom_coe]
  ext n
  have hpos : (0 : ℤ) < l := by exact_mod_cast hl.out.pos
  by_cases hd : (l : ℤ) ∣ n
  · obtain ⟨q, rfl⟩ := hd
    rw [phiPi_coeff_mul]
    rcases lt_or_ge q 0 with hq | hq
    · rw [coeff_neg k a hq, coeff_neg k _ (mul_neg_of_pos_of_neg hpos hq)]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      rw [← Nat.cast_mul, LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries,
        PowerSeries.coeff_subst_X_pow hp, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl.out.pos]
      simp
  · rw [phiPi_coeff_not k l _ _ hd]
    rcases lt_or_ge n 0 with hq | hq
    · rw [coeff_neg k _ hq]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      rw [LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_subst_X_pow hp, if_neg]
      exact fun h => hd (Int.natCast_dvd_natCast.2 h)

def assembleX (y : Fin l → k⸨X⸩) : k⸨X⸩ := ∑ j : Fin l, vv k ^ (j : ℕ) * OnePlusPowerCharacters.phiPi k l (y j)

theorem assembleX_coeff (y : Fin l → k⸨X⸩) (q : ℤ) (j : Fin l) :
    (assembleX k l y).coeff (l * q + (j : ℕ)) = (y j).coeff q := by
  have hv : ∀ (i : ℕ) (z : k⸨X⸩) (n : ℤ), (vv k ^ i * z).coeff n = z.coeff (n - i) := by
    intro i z n
    rw [← zpow_natCast, ← single_eq]
    conv_lhs => rw [← sub_add_cancel n i]
    rw [HahnSeries.coeff_single_mul_add, one_mul]
  rw [assembleX, HahnSeries.coeff_sum, Finset.sum_eq_single j]
  · rw [hv, add_sub_cancel_right, phiPi_coeff_mul]
  · intro i _ hij
    rw [hv, phiPi_coeff_not]
    intro hd
    rw [add_sub_assoc] at hd
    have h2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - (i : ℕ) := (dvd_add_right (dvd_mul_right _ _)).1 hd
    have h3 := Int.eq_zero_of_abs_lt_dvd h2 (by
      have := i.2; have := j.2
      rw [abs_lt]; constructor <;> omega)
    exact hij (Fin.ext (by omega))
  · simp

theorem assembleX_bijective : Function.Bijective (assembleX k l) := by
  have hpos : (0 : ℤ) < l := by exact_mod_cast hl.out.pos
  constructor
  · intro y z h
    funext j
    ext q
    rw [← assembleX_coeff, h, assembleX_coeff]
  · intro x
    have hb : ∀ j : Fin l, BddBelow (Function.support fun q : ℤ => x.coeff (l * q + (j : ℕ))) := by
      intro j
      refine ⟨-|x.order| - 1, fun q hq => ?_⟩
      have h1 : x.order ≤ l * q + (j : ℕ) := HahnSeries.order_le_of_coeff_ne_zero hq
      have h2 : ((j : ℕ) : ℤ) < l := by exact_mod_cast j.2
      by_contra hc
      push Not at hc
      have h3 := neg_abs_le x.order
      have h4 := abs_nonneg x.order
      nlinarith
    refine ⟨fun j => HahnSeries.ofSuppBddBelow _ (hb j), ?_⟩
    ext n
    have hn : n = l * (n / l) + ((⟨(n % l).toNat, by
        have := Int.emod_lt_of_pos n hpos; have := Int.emod_nonneg n hpos.ne'; omega⟩ : Fin l) : ℕ) := by
      have := Int.emod_nonneg n hpos.ne'
      simp only [Int.toNat_of_nonneg this]
      exact (Int.mul_ediv_add_emod n l).symm
    rw [hn, assembleX_coeff]
    simp

theorem assemble_bijective : Function.Bijective (OnePlusPowerCharacters.assemble k l) := by
  let T : Matrix (Fin l) (Fin l) k⸨X⸩ := Matrix.of fun m j => (((j : ℕ).choose m : ℕ) : k⸨X⸩)
  have hdet : T.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · simp [T]
    · intro i j h
      simp only [T, Matrix.of_apply]
      rw [Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from h), Nat.cast_zero]
  have hT : Function.Bijective T.mulVec :=
    ⟨Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det T).2 (hdet ▸ isUnit_one)),
     Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det T).2 (hdet ▸ isUnit_one))⟩
  have e : OnePlusPowerCharacters.assemble k l = assembleX k l ∘ T.mulVec := by
    funext y
    simp only [Function.comp, OnePlusPowerCharacters.assemble, assembleX, Matrix.mulVec, dotProduct, map_sum, map_mul, T,
      Matrix.of_apply, map_natCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, add_comm, add_pow]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun m => vv k ^ m * (((j : ℕ).choose m : ℕ) : k⸨X⸩))]
    simp only [one_pow, mul_one]
    refine Finset.sum_subset (Finset.range_subset_range.2 j.2) fun m _ hm => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hm), Nat.cast_zero, mul_zero]
  rw [e]
  exact (assembleX_bijective k l).comp hT

end Frob

section Ring
variable {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] [CharP k l]

theorem binom_const (t : ℤ_[l]) : PowerSeries.constantCoeff (FrobeniusBinomialReduction.binomPow k l t - 1) = 0 := by
  rw [map_sub, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, FrobeniusBinomialReduction.binomPow, PowerSeries.coeff_map,
    PowerSeries.binomialSeries_coeff]
  simp

theorem binom_ne (t : ℤ_[l]) (h : FrobeniusBinomialReduction.red k l t ≠ 0) : FrobeniusBinomialReduction.binomPow k l t - 1 ≠ 0 := by
  intro e
  have := congrArg (PowerSeries.coeff 1) e
  rw [map_sub, FrobeniusBinomialReduction.binomPow, PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff] at this
  exact h (by simpa [PowerSeries.coeff_one] using this)

theorem binom_unit_ne (t : ℤ_[l]ˣ) : FrobeniusBinomialReduction.binomPow k l t - 1 ≠ 0 :=
  binom_ne _ (t.isUnit.map (FrobeniusBinomialReduction.red k l)).ne_zero

theorem gam_const : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ (1 + l) - 1) = 0 := by simp

theorem gam_ne : (1 + PowerSeries.X : k⟦X⟧) ^ (1 + l) - 1 ≠ 0 := by
  rw [← FrobeniusBinomialReduction.binomPow_natCast k l]
  refine binom_ne _ ?_
  rw [map_natCast]
  simp

theorem gam_coe (b : k⟦X⟧) : FrobeniusBinomialReduction.gamπ k l (b : k⸨X⸩) = ((OnePlusPowerCharacters.gammaPi k l b : k⟦X⟧) : k⸨X⸩) := by
  rw [FrobeniusBinomialReduction.gamπ, substL_eq _ gam_const gam_ne, substHom_coe, OnePlusPowerCharacters.gammaPi]

theorem act_coe (t : ℤ_[l]ˣ) (b : k⟦X⟧) :
    FrobeniusBinomialReduction.actπ k l t (b : k⸨X⸩) = ((OnePlusPowerCharacters.deltaPi k l t b : k⟦X⟧) : k⸨X⸩) := by
  rw [FrobeniusBinomialReduction.actπ, substL_eq _ (binom_const _) (binom_unit_ne t), substHom_coe]
  rfl

theorem deltaInv_coe (b : k⟦X⟧) : FrobeniusBinomialReduction.DeltaInv k l (b : k⸨X⸩) ↔
    ∀ z : ℤ_[l], z ^ (l - 1) = 1 → OnePlusPowerCharacters.deltaPi k l z b = b := by
  have h1 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
  constructor
  · intro h z hz
    obtain ⟨t, rfl⟩ := IsUnit.of_pow_eq_one hz h1
    have := h t (Units.ext (by simpa using hz))
    rw [act_coe] at this
    exact HahnSeries.ofPowerSeries_injective this
  · intro h t ht
    rw [act_coe, h t (by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one])]

theorem deltaInv_mul {x y : k⸨X⸩} (hx : FrobeniusBinomialReduction.DeltaInv k l x) (hy : FrobeniusBinomialReduction.DeltaInv k l y) :
    FrobeniusBinomialReduction.DeltaInv k l (x * y) := by
  intro t ht
  have h1 := hx t ht
  have h2 := hy t ht
  rw [FrobeniusBinomialReduction.actπ, substL_eq _ (binom_const _) (binom_unit_ne t)] at h1 h2 ⊢
  rw [map_mul, h1, h2]

theorem deltaInv_zpow {x : k⸨X⸩} (hx : FrobeniusBinomialReduction.DeltaInv k l x) (m : ℤ) :
    FrobeniusBinomialReduction.DeltaInv k l (x ^ m) := by
  intro t ht
  have h1 := hx t ht
  rw [FrobeniusBinomialReduction.actπ, substL_eq _ (binom_const _) (binom_unit_ne t)] at h1 ⊢
  rw [map_zpow₀, h1]

theorem isCyclotomic_iff (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) :
    OnePlusPowerCharacters.IsCyclotomic R ι ↔ FrobeniusBinomialReduction.IsCyclotomic R ι := by
  constructor
  · rintro ⟨⟨u, hu⟩, hint, hinv, hφ, hγ⟩
    have hA : ∀ a : k⟦X⟧, FrobeniusBinomialReduction.DeltaInv k l (ι (a : k⸨X⸩)) := by
      intro a
      obtain ⟨b, hb⟩ := hint a
      rw [hb, deltaInv_coe, hinv]
      exact ⟨a, hb⟩
    have hv : FrobeniusBinomialReduction.DeltaInv k l (ι (vv k)) := by rw [vv_eq]; exact hA _
    refine ⟨?_, ?_, ⟨u, hu⟩, fun x => by rw [hφ, phiPi_eq], ?_⟩
    · ext y
      constructor
      · rintro ⟨x, rfl⟩
        rw [← LaurentSeries.single_order_mul_powerSeriesPart x, single_eq, map_mul, map_zpow₀]
        exact deltaInv_mul (deltaInv_zpow hv _) (hA _)
      · intro hy
        obtain ⟨n, c, hc⟩ := exists_mul_pow y
        obtain ⟨e, he⟩ : ∃ e, l - 1 = e + 1 := ⟨l - 2, by have := hl.out.two_le; omega⟩
        have hb : y * ι (vv k) ^ n = ((c * ((u : k⟦X⟧) * PowerSeries.X ^ e) ^ n : k⟦X⟧) : k⸨X⸩) := by
          rw [hu, he, map_mul, map_pow, map_mul, map_pow, ← hc, ← vv_eq]
          ring
        have h2 : FrobeniusBinomialReduction.DeltaInv k l (y * ι (vv k) ^ n) :=
          deltaInv_mul hy (by simpa using deltaInv_zpow hv n)
        rw [hb, deltaInv_coe, hinv] at h2
        obtain ⟨a, ha⟩ := h2
        have hne : ι (vv k) ≠ 0 := (map_ne_zero ι).2 vv_ne
        refine ⟨(a : k⸨X⸩) / vv k ^ n, ?_⟩
        rw [map_div₀, map_pow, ha, ← hb, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)]
    · ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨hint a, hA a⟩
      · rintro ⟨⟨b, rfl⟩, hb⟩
        rw [deltaInv_coe, hinv] at hb
        exact hb
    · have : (ι : k⸨X⸩ →+* k⸨X⸩).comp (R.γ : k⸨X⸩ →+* k⸨X⸩) =
          (substHom _ (gam_const (k := k) (l := l)) gam_ne).comp (ι : k⸨X⸩ →+* k⸨X⸩) := by
        refine hom_ext fun a => ?_
        obtain ⟨b, hb⟩ := hint a
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hγ a b hb, hb, substHom_coe, OnePlusPowerCharacters.gammaPi]
      intro x
      rw [FrobeniusBinomialReduction.gamπ, substL_eq _ gam_const gam_ne]
      simpa only [RingHom.comp_apply, RingHom.coe_coe] using RingHom.congr_fun this x
  · rintro ⟨-, hA, hu, hφ, hγ⟩
    refine ⟨hu, fun a => ?_, fun b => ?_, fun x => by rw [hφ, phiPi_eq], fun a b hab => ?_⟩
    · have : ι (a : k⸨X⸩) ∈ Set.range (fun a : k⟦X⟧ => ι (a : k⸨X⸩)) := ⟨a, rfl⟩
      rw [hA] at this
      exact this.1
    · rw [← deltaInv_coe]
      change _ ↔ (b : k⸨X⸩) ∈ Set.range (fun a : k⟦X⟧ => ι (a : k⸨X⸩))
      rw [hA]
      exact ⟨fun h => ⟨⟨b, rfl⟩, h⟩, fun h => h.2⟩
    · rw [hγ, hab, gam_coe]

omit hl [CharP k l] in

theorem psiRing_iff (R : RingPG k l) (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) :
    OnePlusPowerCharacters.PsiRing R ψ ↔ FrobeniusBinomialReduction.PsiRing R ψ := by
  have e : {x : k⸨X⸩ | ∃ b : k⟦X⟧, x = (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)) := by
    ext x
    simp [eq_comm]
  unfold OnePlusPowerCharacters.PsiRing FrobeniusBinomialReduction.PsiRing
  rw [e]
  refine and_congr_right fun h => and_congr_left fun _ => ⟨fun h1 => by simpa using h1 1, fun h1 a => ?_⟩
  have := h a 1
  rwa [mul_one, h1, mul_one] at this

end Ring

section Mod
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem coe_smul (b : k⟦X⟧) (x : V) : (b : k⸨X⸩) • x = b • x := algebraMap_smul k⸨X⸩ b x

theorem image_sh_pull (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) (f Ψ : V →ₗ[k] V) (a : ℤ)
    (h3 : ψ '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)))
    (h1 : ∀ (a : k⸨X⸩) (x : V), Ψ (a • f x) = ψ a • x) (M₀ : Submodule k⟦X⟧ V) :
    Ψ '' (sh a (pull f M₀) : Set V) = (M₀ : Set V) := by
  ext m
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have key : ∀ b : k⟦X⟧, Ψ (vv k ^ a • b • y) ∈ M₀ := by
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, hm, rfl⟩ := hx
        intro b
        have : ψ (vv k ^ a * (b : k⸨X⸩)) ∈ Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)) :=
          h3 ▸ ⟨_, ⟨b, rfl⟩, rfl⟩
        obtain ⟨c, hc⟩ := this
        rw [← coe_smul, ← mul_smul, h1, ← hc, coe_smul]
        exact M₀.smul_mem c hm
      | zero => intro b; simp
      | add x y _ _ hx hy => intro b; rw [smul_add, smul_add, map_add]; exact M₀.add_mem (hx b) (hy b)
      | smul c x _ hx => intro b; rw [← mul_smul b]; exact hx _
    simpa using key 1
  · intro hm
    have : (1 : k⸨X⸩) ∈ Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)) := ⟨1, map_one _⟩
    rw [← h3] at this
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := this
    refine ⟨_, ⟨b • f m, Submodule.smul_mem _ b (Submodule.subset_span ⟨m, hm, rfl⟩), rfl⟩, ?_⟩
    change Ψ (vv k ^ a • b • f m) = m
    rw [← coe_smul, ← mul_smul, h1, hb, one_smul]

theorem psiMod_iff {l : ℕ} (R : RingPG k l) (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) (hψ : FrobeniusBinomialReduction.PsiRing R ψ)
    (f g₀ g Ψ : V →ₗ[k] V) :
    OnePlusPowerCharacters.PsiMod l ψ f g₀ g Ψ ↔
      (∀ a x, Ψ (a • f x) = ψ a • x) ∧ (∀ x, Ψ (g x) = g₀ (Ψ x)) ∧
        ∀ M₀ : Submodule k⟦X⟧ V, IsLat M₀ → CondC g₀ M₀ → FrobeniusBinomialReduction.PsiShift l g Ψ (pull f M₀) :=
  ⟨fun h => ⟨h.1, h.2.1, fun M₀ hM hc => (h.2.2 M₀ hM).2 hc⟩,
   fun h => ⟨h.1, h.2.1, fun M₀ hM =>
    ⟨fun a h1 h2 => image_sh_pull ψ f Ψ a (hψ.2.2.2 a h1 h2) h.1 M₀, h.2.2 M₀ hM⟩⟩⟩

end Mod

end GlobalTheory.PsiLemmaCompare
end
end

section
noncomputable section
namespace GlobalTheory.PhiGam.TwistShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem zpow_one_add (c : k⟦X⟧) (s : ℤ) :
    ∃ d : k⟦X⟧, (1 + (c : k⸨X⸩) * vv k ^ 2) ^ s = 1 + (d : k⸨X⸩) * vv k ^ 2 := by
  have hw : (1 + c * PowerSeries.X ^ 2) * PowerSeries.invOfUnit (1 + c * PowerSeries.X ^ 2) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp)
  set w := PowerSeries.invOfUnit (1 + c * PowerSeries.X ^ 2) 1
  have hw' := congrArg (fun a : k⟦X⟧ => (a : k⸨X⸩)) hw
  simp only [map_mul, map_add, map_one, map_pow, ← vv_eq_coe_X] at hw'
  have hne : 1 + (c : k⸨X⸩) * vv k ^ 2 ≠ 0 := left_ne_zero_of_mul_eq_one hw'
  induction s using Int.induction_on with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + c + d * c * PowerSeries.X ^ 2, ?_⟩
    rw [zpow_add_one₀ hne, hd]
    simp only [map_mul, map_add, map_pow, ← vv_eq_coe_X]
    ring
  | pred n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨(d - c) * w, ?_⟩
    rw [zpow_sub_one₀ hne, hd, ← eq_inv_of_mul_eq_one_right hw']
    simp only [map_mul, map_sub]
    linear_combination hw'

theorem one_add_pow (j : ℕ) :
    ∃ e : k⟦X⟧, (1 + vv k) ^ j = 1 + j * vv k + (e : k⸨X⸩) * vv k ^ 2 := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e + (n : k⟦X⟧) + e * PowerSeries.X, ?_⟩
    rw [pow_succ, he]
    simp only [map_mul, map_add, map_natCast, ← vv_eq_coe_X]
    push_cast
    ring

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem coe_smul_mem {N : Submodule k⟦X⟧ V} (a : k⟦X⟧) {x : V} (hx : x ∈ N) : (a : k⸨X⸩) • x ∈ N := by
  have := N.smul_mem a hx
  rwa [← algebraMap_smul k⸨X⸩ a x] at this

theorem zpow_smul_mem {N : Submodule k⟦X⟧ V} (a : ℤ) {s t : ℤ} (h : a + s = t) {x : V} (hx : x ∈ sh s N) :
    vv k ^ a • x ∈ sh t N := by
  rw [← h, ← sh_sh_eq]
  exact mem_sh_iff_exists.2 ⟨x, hx, rfl⟩

variable [Module k V]

theorem sub_mem_sh {σ : k⸨X⸩ →ₐ[k] k⸨X⸩} {g : V →ₗ[k] V} (hg : Semi σ g)
    (hv : ∃ c : k⟦X⟧, σ (vv k) = vv k * (1 + (c : k⸨X⸩) * vv k ^ 2)) {N : Submodule k⟦X⟧ V}
    (hN : ∀ x ∈ N, g x - x ∈ sh 2 N) {s : ℤ} {y : V} (hy : y ∈ sh s N) : g y - y ∈ sh (s + 2) N := by
  obtain ⟨c, hc⟩ := hv
  obtain ⟨d, hd⟩ := zpow_one_add c s
  obtain ⟨x, hx, rfl⟩ := mem_sh_iff_exists.1 hy
  have h1 : g (vv k ^ s • x) - vv k ^ s • x =
      ((1 + d * PowerSeries.X ^ 2 : k⟦X⟧) : k⸨X⸩) • vv k ^ s • (g x - x) +
        (d : k⸨X⸩) • vv k ^ (2 : ℤ) • vv k ^ s • x := by
    rw [hg, map_zpow₀, hc, mul_zpow, hd, zpow_ofNat]
    simp only [map_mul, map_add, map_one, map_pow, ← vv_eq_coe_X, smul_sub, smul_smul]
    rw [sub_eq_iff_eq_add, mul_comm (vv k ^ s), add_assoc, ← add_smul,
      add_mul _ _ (vv k ^ s), one_mul, mul_assoc, add_comm (_ * _) (vv k ^ s), sub_add_cancel]
  rw [h1]
  exact Submodule.add_mem _ (coe_smul_mem _ (zpow_smul_mem s rfl (hN x hx)))
    (coe_smul_mem _ (zpow_smul_mem 2 (add_comm _ _) hy))

theorem bijOn_twist : ∀ {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (g : V →ₗ[k] V), Semi σ g → (∀ a : k⟦X⟧, ∃ b : k⟦X⟧, σ (a : k⸨X⸩) = b) → (∃ c : k⟦X⟧, σ (vv k) = vv k * (1 + (c : k⸨X⸩) * vv k ^ 2)) → ∀ N : Submodule k⟦X⟧ V, IsLat N → (∀ x ∈ N, g x - x ∈ sh 2 N) → ∀ j : ℕ, (j : k) ≠ 0 → ∀ s : ℤ, Set.BijOn (fun y => (1 + vv k) ^ j • g y - y) (sh s N) (sh (s + 1) N) := by
  intro k _ V _ _ _ _ _ _ _ _ σ g hg _ hv N hL hN j hj s
  have hv0 := vv_ne_zero k
  obtain ⟨e, he⟩ := one_add_pow (k := k) j
  obtain ⟨r, hr⟩ : ∃ r : k⟦X⟧, (r : k⸨X⸩) * j = 1 :=
    ⟨PowerSeries.C (j : k)⁻¹, by
      rw [← map_natCast (HahnSeries.ofPowerSeries ℤ k), ← map_mul, ← map_natCast (PowerSeries.C (R := k)),
        ← map_mul, inv_mul_cancel₀ hj, map_one, map_one]⟩
  have hvv : vv k ^ (-1 : ℤ) * vv k = 1 := by rw [zpow_neg_one, inv_mul_cancel₀ hv0]
  let θ : V →+ V :=
    { toFun := fun y => (1 + vv k) ^ j • g y - y
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add, smul_add]; abel }
  have hθ : ∀ y, θ y = (1 + vv k) ^ j • g y - y := fun _ => rfl
  let E : V →+ V :=
    { toFun := fun y => y - (r : k⸨X⸩) • vv k ^ (-1 : ℤ) • θ y
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add, smul_add]; abel }
  have hE : ∀ y, E y = y - (r : k⸨X⸩) • vv k ^ (-1 : ℤ) • θ y := fun _ => rfl
  have hθE : ∀ y, θ y = ((j : k⟦X⟧) : k⸨X⸩) • vv k ^ (1 : ℤ) • (y - E y) := by
    intro y
    rw [hE, sub_sub_cancel, smul_smul, smul_smul, smul_smul, map_natCast, zpow_one]
    rw [show (j : k⸨X⸩) * vv k * r * vv k ^ (-1 : ℤ) = 1 by linear_combination (r * j) * hvv + hr, one_smul]
  have hEm : ∀ (t : ℤ), ∀ y ∈ sh t N, E y ∈ sh (t + 1) N := by
    intro t y hy
    have h1 : θ y = (((1 + PowerSeries.X) ^ j : k⟦X⟧) : k⸨X⸩) • (g y - y) + (e : k⸨X⸩) • vv k ^ (2 : ℤ) • y
        + (j * vv k) • y := by
      rw [hθ, map_pow, map_add, map_one, ← vv_eq_coe_X, smul_sub, zpow_ofNat]
      generalize (1 + vv k) ^ j • g y = z
      rw [he, add_smul, add_smul, one_smul, mul_smul (e : k⸨X⸩)]
      abel
    have h2 : E y = -((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • ((((1 + PowerSeries.X) ^ j : k⟦X⟧) : k⸨X⸩) • (g y - y) +
        (e : k⸨X⸩) • vv k ^ (2 : ℤ) • y)) := by
      rw [hE, h1, smul_add _ _ ((j * vv k) • y), smul_add _ _ (_ • (j * vv k) • y),
        smul_smul _ (j * vv k), smul_smul _ (_ * (j * vv k)),
        show (r : k⸨X⸩) * (vv k ^ (-1 : ℤ) * (j * vv k)) = 1 by linear_combination (r * j) * hvv + hr, one_smul]
      abel
    rw [h2]
    refine Submodule.neg_mem _ (coe_smul_mem _ (zpow_smul_mem (s := t + 2) _ (by ring) ?_))
    exact Submodule.add_mem _ (coe_smul_mem _ (sub_mem_sh hg hv hN hy))
      (coe_smul_mem _ (zpow_smul_mem 2 (add_comm _ _) hy))
  have hEs : ∀ y ∈ sh s N, E y ∈ sh s N := fun y hy => sh_le_sh_of_le (by omega) N (hEm s y hy)
  let T : sh s N →+ sh s N :=
    { toFun := fun m => ⟨E m, hEs _ m.2⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hT : ∀ m, ((T m : sh s N) : V) = E m := fun _ => rfl
  haveI : Module.Finite k⟦X⟧ (sh s N) := Module.Finite.iff_fg.2 (hL.shift s).1
  haveI : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (sh s N) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _
  haveI : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (sh s N) := by
    rw [← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have hXs : ∀ (i : ℕ) (x : V), (PowerSeries.X ^ i : k⟦X⟧) • x = vv k ^ (i : ℤ) • x := by
    intro i x
    rw [← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ i : k⟦X⟧) x, zpow_natCast, map_pow, vv_eq_coe_X]
    rfl
  have hfil : ∀ (i : ℕ) (m : sh s N),
      m ∈ (Ideal.span {(PowerSeries.X : k⟦X⟧)} ^ i • ⊤ : Submodule k⟦X⟧ (sh s N)) ↔ (m : V) ∈ sh (i + s) N := by
    intro i m
    rw [mem_span_pow_smul_top, ← sh_sh_eq, mem_sh_iff_exists]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, (hXs i y).symm⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext ((hXs i y).trans h)⟩
  have key := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T (by
    intro i m hm
    rw [hfil] at hm ⊢
    have := hEm _ _ hm
    rw [hT]
    convert this using 2
    push_cast
    ring)
  change Set.BijOn θ _ _
  refine ⟨fun y hy => ?_, fun a ha b hb hab => ?_, fun z hz => ?_⟩
  · rw [hθE]
    exact coe_smul_mem _ (zpow_smul_mem 1 (add_comm _ _) (Submodule.sub_mem _ hy (hEs y hy)))
  · have := key.2 ⟨a - b, Submodule.sub_mem _ ha hb⟩ (Subtype.ext (by
      rw [hT, hE, map_sub θ, hab]; simp))
    exact sub_eq_zero.1 (congrArg Subtype.val this)
  · obtain ⟨m, hm⟩ := key.1 ⟨-((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • z),
      Submodule.neg_mem _ (coe_smul_mem _ (zpow_smul_mem _ (by ring) hz))⟩
    refine ⟨m, m.2, ?_⟩
    have h1 : E m - m = -((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • z) := congrArg Subtype.val hm
    rw [hθE, ← neg_sub, h1, neg_neg, smul_smul, smul_smul, smul_smul, map_natCast, zpow_one,
      show (j : k⸨X⸩) * vv k * r * vv k ^ (-1 : ℤ) = 1 by linear_combination (r * j) * hvv + hr, one_smul]

end GlobalTheory.PhiGam.TwistShift
end
end

section
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.PsiBasis

variable {k : Type} [Field k]

noncomputable def comp (l : ℕ) (hl : 0 < l) (i : ℕ) : k⸨X⸩ →ₗ[k] k⸨X⸩ where
  toFun y :=
    { coeff := fun m => y.coeff (l * m + i)
      isPWO_support' := by
        apply Set.IsWF.isPWO
        apply BddBelow.isWF
        refine ⟨min 0 (y.order - i), fun m hm => ?_⟩
        by_contra h
        apply hm
        apply HahnSeries.coeff_eq_zero_of_lt_order
        have h1 : m < 0 := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
        have h2 : m < y.order - i := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
        have h3 : (1 : ℤ) ≤ l := by exact_mod_cast hl
        nlinarith }
  map_add' x y := by ext m; simp
  map_smul' c x := by ext m; simp

theorem comp_coeff (l : ℕ) (hl : 0 < l) (i : ℕ) (y : k⸨X⸩) (m : ℤ) :
    (comp l hl i y).coeff m = y.coeff (l * m + i) := rfl

theorem p_zpow (s : ℤ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single s 1 := by
  cases s with
  | ofNat n => simp [HahnSeries.single_pow]
  | negSucc n =>
    rw [zpow_negSucc, HahnSeries.single_pow, HahnSeries.inv_single]
    simp [Int.negSucc_eq]

theorem p_pow (s : ℕ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single (s : ℤ) 1 := by
  simp [HahnSeries.single_pow]

theorem mem_iff (s : ℤ) (x : k⸨X⸩) :
    (∃ b : k⟦X⟧, x = (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s * (b : k⸨X⸩)) ↔
      ∀ m < s, x.coeff m = 0 := by
  rw [p_zpow]
  constructor
  · rintro ⟨b, rfl⟩ m hm
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, if_pos (by omega), mul_zero]
  · intro h
    refine ⟨PowerSeries.mk fun n => x.coeff (s + n), ?_⟩
    ext m
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, one_mul]
    split_ifs with hm
    · exact h m (by omega)
    · rw [PowerSeries.coeff_mk]; congr 1; omega

section
variable (l : ℕ) (hl : 0 < l) (φ : k⸨X⸩ →+* k⸨X⸩)
  (hφ : ∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0)
include hl hφ

theorem comp_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ j * φ a)
      = if j = i then a else 0 := by
  ext m
  have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [comp_coeff, p_pow, HahnSeries.coeff_single_mul, one_mul, hφ]
  by_cases h : j = i
  · subst h
    simp [Int.mul_ediv_cancel_left _ hl']
  · rw [if_neg h, if_neg]
    · simp
    · intro hd
      have : (l : ℤ) ∣ (i : ℤ) - j := by
        have h2 := dvd_sub hd (dvd_mul_right (l : ℤ) m)
        have e : (l : ℤ) * m + i - j - l * m = i - j := by ring
        rwa [e] at h2
      have := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> omega)
      omega

theorem eq_of_comp_eq {y z : k⸨X⸩} (h : ∀ i < l, comp l hl i y = comp l hl i z) : y = z := by
  ext m
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  have h0 := Int.emod_nonneg m hl'.ne'
  have h1 := Int.emod_lt_of_pos m hl'
  have := congrArg (fun w => w.coeff (m / l)) (h (m % l).toNat (by omega))
  simp only [comp_coeff] at this
  rw [Int.toNat_of_nonneg h0, Int.mul_ediv_add_emod] at this
  exact this

theorem comp_one_add_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j * φ a)
      = (j.choose i) • a := by
  rw [add_comm, add_pow, Finset.sum_mul, map_sum]
  have : ∀ m ∈ Finset.range (j + 1),
      comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ m * 1 ^ (j - m) *
        (j.choose m : k⸨X⸩) * φ a) = if m = i then (j.choose i) • a else 0 := by
    intro m hm
    have hm' : m < l := by have := Finset.mem_range.1 hm; omega
    rw [one_pow, mul_one, mul_assoc, ← map_natCast φ, ← map_mul,
      comp_pow_mul l hl φ hφ hi hm']
    split_ifs with h
    · subst h; rw [nsmul_eq_mul]
    · rfl
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using h), zero_smul]

theorem existsUnique_decomp (y : k⸨X⸩) :
    ∃! x : Fin l → k⸨X⸩, y = ∑ j : Fin l,
      (1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j.val * φ (x j) := by
  let M : Matrix (Fin l) (Fin l) k⸨X⸩ := fun i j => (j.val.choose i.val : k⸨X⸩)
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular]
    · simp [M]
    · intro i j hij
      have : j.val < i.val := hij
      simp [M, Nat.choose_eq_zero_of_lt this]
  have hb : Function.Bijective M.mulVec :=
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hM, Matrix.mulVec_surjective_iff_isUnit.2 hM⟩
  have key : ∀ (x : Fin l → k⸨X⸩) (i : Fin l), comp l hl i (∑ j : Fin l,
      (1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j.val * φ (x j)) = M.mulVec x i := by
    intro x i
    rw [map_sum, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [comp_one_add_pow_mul l hl φ hφ i.2 j.2, nsmul_eq_mul]
  have := hb.existsUnique (fun i : Fin l => comp l hl i y)
  refine (existsUnique_congr fun x => ?_).1 this
  constructor
  · intro h
    refine eq_of_comp_eq l hl φ hφ fun i hi => ?_
    rw [key x ⟨i, hi⟩, h]
  · intro h
    funext i
    rw [← key, ← h]

end

noncomputable def psi (l : ℕ) (hl : 0 < l) : k⸨X⸩ →ₗ[k] k⸨X⸩ :=
  ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i

theorem psi_apply (l : ℕ) (hl : 0 < l) (y : k⸨X⸩) :
    psi l hl y = ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i y := by
  simp only [psi, LinearMap.sum_apply, LinearMap.smul_apply]

theorem finiteRing_sq_sub_mul_sq_eq_of_card : ∀ {k : Type} [Field k] (l : ℕ) (_ : 0 < l) (φ : k⸨X⸩ →+* k⸨X⸩), (∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0) → let p : k⸨X⸩ := HahnSeries.single 1 1; (∀ y : k⸨X⸩, ∃! x : Fin l → k⸨X⸩, y = ∑ j : Fin l, (1 + p) ^ j.val * φ (x j)) ∧ ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, (∀ a, ψ (φ a) = a) ∧ (∀ (a) (j : ℕ), 0 < j → j < l → ψ ((1 + p) ^ j * φ a) = 0) ∧ ∀ s : ℤ, ψ '' {x | ∃ b : k⟦X⟧, x = p ^ s * (b : k⸨X⸩)} = {x | ∃ b : k⟦X⟧, x = p ^ (s / l) * (b : k⸨X⸩)} := by
  intro k _ l hl φ hφ p
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  have hpow : ∀ j < l, ∀ a, psi l hl (p ^ j * φ a) = ((-1 : ℤ) ^ j) • a := by
    intro j hj a
    rw [psi_apply, Finset.sum_eq_single j]
    · congr 1
      exact (comp_pow_mul l hl φ hφ hj hj a).trans (if_pos rfl)
    · intro i hi hij
      have := (comp_pow_mul l hl φ hφ (Finset.mem_range.1 hi) hj a).trans (if_neg hij.symm)
      rw [this, smul_zero]
    · intro h; exact absurd (Finset.mem_range.2 hj) h
  refine ⟨existsUnique_decomp l hl φ hφ, psi l hl, fun a => ?_, fun a j hj0 hj => ?_, fun s => ?_⟩
  · simpa using hpow 0 hl a
  · rw [psi_apply]
    have : ∀ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i ((1 + p) ^ j * φ a)
        = ((-1 : ℤ) ^ i * (j.choose i : ℤ)) • a := by
      intro i hi
      have := comp_one_add_pow_mul l hl φ hφ (Finset.mem_range.1 hi) hj a
      rw [this]
      rw [mul_smul, natCast_zsmul]
    rw [Finset.sum_congr rfl this, ← Finset.sum_smul,
      ← Finset.sum_subset (Finset.range_subset_range.2 (show j + 1 ≤ l from hj)),
      Int.alternating_sum_range_choose_of_ne hj0.ne', zero_smul]
    intro i _ hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]
    simp
  · have h0 := Int.emod_nonneg s hl'.ne'
    have h1 := Int.emod_lt_of_pos s hl'
    have h2 := Int.mul_ediv_add_emod s l
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq, p, mem_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ m hm
      rw [psi_apply, HahnSeries.coeff_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : (i : ℤ) < l := by exact_mod_cast Finset.mem_range.1 hi
      have : (comp l hl i y).coeff m = 0 := by
        rw [comp_coeff]
        apply hy
        nlinarith
      rw [HahnSeries.coeff_smul, this, smul_zero]
    · intro hz
      refine ⟨p ^ (l - 1) * φ (((-1 : ℤ) ^ (l - 1)) • z), fun m hm => ?_, ?_⟩
      · rw [p_pow, HahnSeries.coeff_single_mul, one_mul, hφ]
        split_ifs with hd
        · obtain ⟨c, hc⟩ := hd
          rw [hc, Int.mul_ediv_cancel_left _ hl'.ne', HahnSeries.coeff_smul, hz, smul_zero]
          have : ((l - 1 : ℕ) : ℤ) = l - 1 := by omega
          rw [this] at hc
          nlinarith
        · rfl
      · rw [hpow _ (by omega), smul_smul, ← mul_pow]
        simp

theorem main : ∀ {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (φ : k⸨X⸩ →ₐ[k] k⸨X⸩), (∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0) → let p : k⸨X⸩ := HahnSeries.single 1 1; (∀ y : k⸨X⸩, ∃! x : Fin l → k⸨X⸩, y = ∑ j : Fin l, (1 + p) ^ j.val * φ (x j)) ∧ ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, (∀ a, ψ (φ a) = a) ∧ (∀ (a) (j : ℕ), 0 < j → j < l → ψ ((1 + p) ^ j * φ a) = 0) ∧ ∀ s : ℤ, ψ '' {x | ∃ b : k⟦X⟧, x = p ^ s * (b : k⸨X⸩)} = {x | ∃ b : k⟦X⟧, x = p ^ (s / l) * (b : k⸨X⸩)} :=
  fun l hp _ φ hφ => finiteRing_sq_sub_mul_sq_eq_of_card l hp.out.pos φ.toRingHom hφ

end GlobalTheory.PsiBasis
end

section
noncomputable section
namespace GlobalTheory.PsiShiftProof
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.PhiGam.Inh GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters GlobalTheory.PsiLemmaCompare

section Filt
variable {k : Type} [Field k]

def Dp (k : Type) [Field k] (s : ℤ) : Submodule k⟦X⟧ k⸨X⸩ := sh s (stdLat k)

theorem mem_Dp {s : ℤ} {x : k⸨X⸩} : x ∈ Dp k s ↔ ∃ b : k⟦X⟧, x = vv k ^ s * (b : k⸨X⸩) := by
  rw [Dp, mem_sh_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := mem_stdLat.1 hy
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, mem_stdLat.2 ⟨b, rfl⟩, rfl⟩

theorem mem_Dp_coeff {s : ℤ} {x : k⸨X⸩} : x ∈ Dp k s ↔ ∀ m < s, x.coeff m = 0 :=
  mem_Dp.trans (PsiBasis.mem_iff s x)

theorem mem_Dp_zero {x : k⸨X⸩} : x ∈ Dp k 0 ↔ ∃ b : k⟦X⟧, x = (b : k⸨X⸩) := by
  simp [mem_Dp]

theorem coe_mem (b : k⟦X⟧) : (b : k⸨X⸩) ∈ Dp k 0 := mem_Dp_zero.2 ⟨b, rfl⟩

theorem Dp_mul {s t u : ℤ} {x y : k⸨X⸩} (hx : x ∈ Dp k s) (hy : y ∈ Dp k t) (h : u ≤ s + t) :
    x * y ∈ Dp k u := by
  obtain ⟨a, rfl⟩ := mem_Dp.1 hx
  obtain ⟨b, rfl⟩ := mem_Dp.1 hy
  refine sh_le_sh_of_le h _ (mem_Dp.2 ⟨a * b, ?_⟩)
  rw [zpow_add₀ (vv_ne_zero k), map_mul]; ring

theorem Dp_mono {s t : ℤ} (h : t ≤ s) {x : k⸨X⸩} (hx : x ∈ Dp k s) : x ∈ Dp k t :=
  sh_le_sh_of_le h _ hx

theorem zpow_mem (s : ℤ) : vv k ^ s ∈ Dp k s := mem_Dp.2 ⟨1, by simp⟩

theorem pow_mem (s : ℕ) : vv k ^ s ∈ Dp k s := by simpa using zpow_mem (k := k) s

theorem order_mem (x : k⸨X⸩) : x ∈ Dp k x.order :=
  mem_Dp_coeff.2 fun _ hm => HahnSeries.coeff_eq_zero_of_lt_order hm

theorem one_not_mem : (1 : k⸨X⸩) ∉ Dp k 1 := fun h => by
  simpa using mem_Dp_coeff.1 h 0 one_pos

theorem one_add_pow_mem (j : ℕ) : (1 + vv k) ^ j ∈ Dp k 0 :=
  mem_Dp_zero.2 ⟨(1 + PowerSeries.X) ^ j, by simp [vv_eq_coe_X]⟩

theorem mem_of_one_add_mul {s : ℤ} {x : k⸨X⸩} (h : (1 + vv k) * x ∈ Dp k s) : x ∈ Dp k s := by
  have h0 := congrArg (fun a : k⟦X⟧ => (a : k⸨X⸩)) (powerSeries_oneAddConstMulX_mul_inv (1 : k))
  simp only [map_one, one_mul, map_mul, map_add, ← vv_eq_coe_X] at h0
  have := Dp_mul (coe_mem (inv1 (1 : k))) h (u := s) (by simp)
  rwa [← mul_assoc, mul_comm _ (1 + vv k), h0, one_mul] at this

theorem map_mem {σ : k⸨X⸩ →+* k⸨X⸩} (hint : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, σ (a : k⸨X⸩) = (b : k⸨X⸩)) {e : ℕ}
    (hv : ∃ u : (k⟦X⟧)ˣ, σ (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ e) {a : ℤ} {x : k⸨X⸩} (hx : x ∈ Dp k a) :
    σ x ∈ Dp k (e * a) := by
  obtain ⟨u, hu⟩ := hv
  obtain ⟨b, rfl⟩ := mem_Dp.1 hx
  obtain ⟨c, hc⟩ := hint b
  refine mem_Dp.2 ⟨((u ^ a : (k⟦X⟧)ˣ) : k⟦X⟧) * c, ?_⟩
  have : ((((u ^ a : (k⟦X⟧)ˣ) : k⟦X⟧)) : k⸨X⸩) = (((u : k⟦X⟧)) : k⸨X⸩) ^ a := by
    have h := map_zpow (Units.map (HahnSeries.ofPowerSeries ℤ k).toMonoidHom) u a
    have h2 := congrArg Units.val h
    rw [Units.val_zpow_eq_zpow_val] at h2
    exact h2
  rw [map_mul, map_zpow₀, hu, hc, map_mul, this, mul_zpow, zpow_mul, zpow_natCast]
  ring

theorem mem_of_map_mem {σ : k⸨X⸩ →+* k⸨X⸩} (hint : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, σ (a : k⸨X⸩) = (b : k⸨X⸩)) {e : ℕ}
    (hv : ∃ u : (k⟦X⟧)ˣ, σ (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ e) {a s : ℤ} (hs : e * (a - 1) < s)
    {x : k⸨X⸩} (hx : σ x ∈ Dp k s) : x ∈ Dp k a := by
  by_cases h0 : x = 0
  · rw [h0]; exact Submodule.zero_mem _
  by_contra hc
  have h1 : x.order ≤ a - 1 := by
    by_contra h
    exact hc (Dp_mono (by omega) (order_mem x))
  have h2 : x.order + (x⁻¹).order = 0 := by
    rw [← HahnSeries.order_mul h0 (inv_ne_zero h0), mul_inv_cancel₀ h0, HahnSeries.order_one]
  have h3 := map_mem hint hv (order_mem x⁻¹)
  have h4 := Dp_mul hx h3 (u := 1) (by
    have : (x⁻¹).order = -x.order := by omega
    rw [this]
    have : (0 : ℤ) ≤ e := by positivity
    nlinarith)
  rw [← map_mul, mul_inv_cancel₀ h0, map_one] at h4
  exact one_not_mem h4

end Filt

section Psi
variable (k : Type) [Field k] (l : ℕ) [hl : Fact l.Prime]

def psiPi : k⸨X⸩ →ₗ[k] k⸨X⸩ := PsiBasis.psi l hl.out.pos

theorem phi_coeff (x : k⸨X⸩) (m : ℤ) :
    (phiPi k l x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0 := by
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [phiPi_coeff_mul, Int.mul_ediv_cancel_left _ (by exact_mod_cast hl.out.ne_zero)]
  · exact phiPi_coeff_not k l x m h

theorem phi_mem {s : ℤ} {x : k⸨X⸩} (hx : x ∈ Dp k s) : phiPi k l x ∈ Dp k (l * s) := by
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl.out.pos
  rw [mem_Dp_coeff] at hx ⊢
  intro m hm
  rw [phi_coeff]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Int.mul_ediv_cancel_left _ hl'.ne']
    exact hx q (lt_of_mul_lt_mul_left hm hl'.le)
  · rfl

theorem psi_pow_mul {j : ℕ} (hj : j < l) (a : k⸨X⸩) :
    psiPi k l ((1 + vv k) ^ j * phiPi k l a) = if j = 0 then a else 0 := by
  rw [psiPi, PsiBasis.psi_apply]
  have : ∀ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • PsiBasis.comp l hl.out.pos i ((1 + vv k) ^ j * phiPi k l a)
      = ((-1 : ℤ) ^ i * (j.choose i : ℤ)) • a := by
    intro i hi
    have := PsiBasis.comp_one_add_pow_mul l hl.out.pos (phiPi k l) (phi_coeff k l) (Finset.mem_range.1 hi) hj a
    rw [vv, this, mul_smul, natCast_zsmul]
  rw [Finset.sum_congr rfl this, ← Finset.sum_smul,
    ← Finset.sum_subset (Finset.range_subset_range.2 (show j + 1 ≤ l from hj)),
    Int.alternating_sum_range_choose]
  · split_ifs <;> simp
  · intro i _ hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]
    simp

theorem psi_assemble (y : Fin l → k⸨X⸩) : psiPi k l (assemble k l y) = y 0 := by
  rw [assemble, map_sum, Finset.sum_eq_single 0]
  · rw [psi_pow_mul k l (0 : Fin l).2, if_pos (by simp)]
  · intro j _ hj
    rw [psi_pow_mul k l j.2, if_neg (by simpa using hj)]
  · simp

theorem psi_coeff (y : k⸨X⸩) (m : ℤ) :
    (psiPi k l y).coeff m = ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • y.coeff (l * m + i) := by
  rw [psiPi, PsiBasis.psi_apply, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HahnSeries.coeff_smul, PsiBasis.comp_coeff]

theorem psi_mem {s t : ℤ} (h : l * t ≤ s) {y : k⸨X⸩} (hy : y ∈ Dp k s) : psiPi k l y ∈ Dp k t := by
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl.out.pos
  rw [mem_Dp_coeff] at hy ⊢
  intro m hm
  rw [psi_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : (i : ℤ) < l := by exact_mod_cast Finset.mem_range.1 hi
  rw [hy, smul_zero]
  nlinarith

theorem psi_coeff_zero {y : k⸨X⸩} (hy : y ∈ Dp k (l - 1)) :
    (psiPi k l y).coeff 0 = ((-1 : ℤ) ^ (l - 1)) • y.coeff (l - 1) := by
  have h1 := hl.out.pos
  rw [psi_coeff, Finset.sum_eq_single (l - 1)]
  · congr 2; omega
  · intro i hi hne
    have := Finset.mem_range.1 hi
    rw [mem_Dp_coeff.1 hy, smul_zero]
    omega
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem mem_of_psi_eq_zero {y : k⸨X⸩} (hy : y ∈ Dp k (l - 1)) (h : psiPi k l y = 0) : y ∈ Dp k l := by
  have h1 := psi_coeff_zero k l hy
  rw [h, HahnSeries.coeff_zero, eq_comm, zsmul_eq_mul, mul_eq_zero] at h1
  have h2 := h1.resolve_left (by simp)
  refine mem_Dp_coeff.2 fun m hm => ?_
  rcases eq_or_ne m (l - 1) with rfl | hne
  · exact h2
  · exact mem_Dp_coeff.1 hy m (by omega)

theorem psi_phi_mul (a x : k⸨X⸩) : psiPi k l (phiPi k l a * x) = a * psiPi k l x := by
  obtain ⟨y, rfl⟩ := (assemble_bijective k l).2 x
  have : phiPi k l a * assemble k l y = assemble k l (fun j => a * y j) := by
    simp only [assemble, Finset.mul_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, psi_assemble, psi_assemble]

theorem psi_comm (σ : k⸨X⸩ →+* k⸨X⸩) (hφ : ∀ x, σ (phiPi k l x) = phiPi k l (σ x))
    (hj : ∀ j : ℕ, 0 < j → j < l → ∃ (i : ℕ) (w : k⸨X⸩), 0 < i ∧ i < l ∧
      σ ((1 + vv k) ^ j) = (1 + vv k) ^ i * phiPi k l w) (x : k⸨X⸩) :
    psiPi k l (σ x) = σ (psiPi k l x) := by
  obtain ⟨y, rfl⟩ := (assemble_bijective k l).2 x
  rw [psi_assemble, assemble, map_sum, map_sum, Finset.sum_eq_single 0]
  · have := psi_pow_mul k l hl.out.pos (σ (y 0))
    simpa [hφ] using this
  · intro j _ hj0
    obtain ⟨i, w, h0, h1, h2⟩ := hj j (Nat.pos_of_ne_zero (by simpa using hj0)) j.2
    rw [map_mul, h2, hφ, mul_assoc, ← map_mul, psi_pow_mul k l h1, if_neg h0.ne']
  · simp

theorem assemble_mem {s : ℤ} {y : Fin l → k⸨X⸩} (h : ∀ j, y j ∈ Dp k s) : assemble k l y ∈ Dp k (l * s) :=
  Submodule.sum_mem _ fun j _ => Dp_mul (one_add_pow_mem j) (phi_mem k l (h j)) (by simp)

variable [CharP k l]

theorem phi_one_add : phiPi k l (1 + vv k) = (1 + vv k) ^ l := by
  haveI : CharP k⸨X⸩ l := charP_of_injective_algebraMap (algebraMap k k⸨X⸩).injective l
  rw [map_add, map_one, phiPi_vv, add_pow_char, one_pow]

theorem mem_of_assemble_mem {s : ℤ} {y : Fin l → k⸨X⸩} (h : assemble k l y ∈ Dp k (l * s)) (j : Fin l) :
    y j ∈ Dp k s := by
  have h1 := psi_mem k l le_rfl (Dp_mul (one_add_pow_mem (l - j)) h (u := l * s) (by simp))
  apply mem_of_one_add_mul
  convert h1 using 1
  have hj := j.2
  have key : ∀ i : Fin l, (j : ℕ) ≤ i → (1 + vv k) ^ (l - j) * ((1 + vv k) ^ (i : ℕ) * phiPi k l (y i)) =
      (1 + vv k) ^ ((i : ℕ) - j) * phiPi k l ((1 + vv k) * y i) := by
    intro i hi
    rw [map_mul, phi_one_add, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
    congr 2; omega
  rw [assemble, Finset.mul_sum, map_sum, Finset.sum_eq_single j]
  · rw [key j le_rfl, psi_pow_mul k l (by omega), if_pos (by omega)]
  · intro i _ hi
    have hi' : (i : ℕ) ≠ j := fun e => hi (Fin.ext e)
    have := i.2
    rcases lt_or_ge (i : ℕ) j with h2 | h2
    · rw [← mul_assoc, ← pow_add, psi_pow_mul k l (by omega), if_neg (by omega)]
    · rw [key i h2, psi_pow_mul k l (by omega), if_neg (by omega)]
  · simp

end Psi

section Delta
variable {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] [CharP k l]

theorem opp_add (z w : ℤ_[l]) : onePlusPow k l (z + w) = onePlusPow k l z * onePlusPow k l w := by
  simp only [onePlusPow, PowerSeries.binomialSeries_add, map_mul]

theorem opp_nat (m : ℕ) : onePlusPow k l (m : ℤ_[l]) = (1 + PowerSeries.X) ^ m :=
  FrobeniusBinomialReduction.binomPow_natCast k l m

theorem opp_mul (m : ℕ) (z : ℤ_[l]) : onePlusPow k l (m * z) = onePlusPow k l z ^ m := by
  induction m with
  | zero => simpa using opp_nat (k := k) (l := l) 0
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, opp_add, ih, pow_succ]

theorem opp_dvd (z : ℤ_[l]) : PowerSeries.X ∣ onePlusPow k l z - 1 :=
  PowerSeries.X_dvd_iff.2 (binom_const z)

theorem hom_opp (σ : k⟦X⟧ →+* k⟦X⟧) (m : ℕ) (h : σ (1 + PowerSeries.X) = (1 + PowerSeries.X) ^ m) (z : ℤ_[l]) :
    σ (onePlusPow k l z) = onePlusPow k l z ^ m := by
  haveI : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l
  have hX : PowerSeries.X ∣ σ PowerSeries.X := by
    rw [map_add, map_one, ← eq_sub_iff_add_eq'] at h
    rw [h, PowerSeries.X_dvd_iff]; simp
  have key : ∀ N : ℕ, PowerSeries.X ^ N ∣ σ (onePlusPow k l z) - onePlusPow k l z ^ m := by
    intro N
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec N z)
    have hz : z = (z.appr N : ℕ) + ((l ^ N : ℕ) : ℤ_[l]) * w := by push_cast; linear_combination hw
    have h1 : PowerSeries.X ∣ σ (onePlusPow k l w) - onePlusPow k l w ^ m := by
      obtain ⟨c, hc⟩ := opp_dvd (k := k) w
      have h2 : PowerSeries.X ∣ σ (onePlusPow k l w) - 1 := by
        rw [← map_one σ, ← map_sub, hc, map_mul]; exact hX.mul_right _
      have h3 : PowerSeries.X ∣ onePlusPow k l w ^ m - 1 :=
        (opp_dvd w).trans (by simpa using sub_dvd_pow_sub_pow (onePlusPow k l w) 1 m)
      simpa using dvd_sub h2 h3
    rw [hz, opp_add, opp_nat, opp_mul, map_mul, map_pow, map_pow, h, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
      mul_comm m, ← mul_sub, mul_comm (l ^ N) m, pow_mul (onePlusPow k l w), ← sub_pow_char_pow]
    exact ((pow_dvd_pow _ (Nat.lt_pow_self hl.out.one_lt).le).trans (pow_dvd_pow_of_dvd h1 _)).mul_left _
  rw [← sub_eq_zero]
  ext n
  exact PowerSeries.X_pow_dvd_iff.1 (key (n + 1)) n (by omega)

def delPi (k : Type) [Field k] [CharP k l] (t : ℤ_[l]ˣ) : k⸨X⸩ →+* k⸨X⸩ :=
  substHom (onePlusPow k l t - 1) (binom_const _) (binom_unit_ne t)

theorem delPi_coe (t : ℤ_[l]ˣ) (a : k⟦X⟧) :
    delPi k t (a : k⸨X⸩) = ((a.subst (onePlusPow k l t - 1) : k⟦X⟧) : k⸨X⸩) := substHom_coe _ _ _ a

theorem delPi_eq (t : ℤ_[l]ˣ) (x : k⸨X⸩) : FrobeniusBinomialReduction.actπ k l t x = delPi k t x :=
  substL_eq _ (binom_const _) (binom_unit_ne t) x

theorem delPi_comm (t : ℤ_[l]ˣ) (m : ℕ) (h0 : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) = 0)
    (h1 : ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) ≠ 0) (x : k⸨X⸩) :
    delPi k t (substHom _ h0 h1 x) = substHom _ h0 h1 (delPi k t x) := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hb : PowerSeries.HasSubst (onePlusPow k l t - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (binom_const (k := k) (t : ℤ_[l]))
  have key : PowerSeries.subst (onePlusPow k l t - 1) ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) =
      PowerSeries.subst ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) (onePlusPow k l t - 1) := by
    have := hom_opp (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom m
      (by simp [PowerSeries.substAlgHom_X]) t
    rw [← PowerSeries.coe_substAlgHom ha, ← PowerSeries.coe_substAlgHom hb, map_sub, map_sub, map_pow, map_add,
      PowerSeries.substAlgHom_X, map_one, map_one]
    rw [show (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧) (onePlusPow k l t) = _ from this]
    simp
  have : (delPi k t).comp (substHom _ h0 h1) = (substHom _ h0 h1).comp (delPi k t) := by
    refine hom_ext fun a => ?_
    simp only [RingHom.comp_apply, delPi_coe, substHom_coe]
    rw [PowerSeries.subst_comp_subst_apply ha hb, PowerSeries.subst_comp_subst_apply hb ha, key]
  exact RingHom.congr_fun this x

theorem frob_eq : ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) = PowerSeries.X ^ l := by
  haveI : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l
  rw [add_pow_char]; simp

theorem frob_ne : ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) ≠ 0 := by
  rw [frob_eq]; exact pow_ne_zero _ PowerSeries.X_ne_zero

theorem phi_eq_subst (x : k⸨X⸩) :
    phiPi k l x = substHom ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) (by simp) frob_ne x := by
  rw [phiPi_eq, FrobeniusBinomialReduction.frobπ, ← substL_eq, frob_eq]

theorem del_phi (t : ℤ_[l]ˣ) (x : k⸨X⸩) : delPi k t (phiPi k l x) = phiPi k l (delPi k t x) := by
  rw [phi_eq_subst, phi_eq_subst, delPi_comm]

theorem phi_opp (w : ℤ_[l]) :
    phiPi k l (onePlusPow k l w : k⟦X⟧) = ((onePlusPow k l w ^ l : k⟦X⟧) : k⸨X⸩) := by
  have ha : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have := hom_opp (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom l
      (by simp [PowerSeries.substAlgHom_X]) w
  rw [phi_eq_subst, substHom_coe, ← this, ← PowerSeries.coe_substAlgHom ha]
  rfl

theorem del_one_add (t : ℤ_[l]ˣ) : delPi k t (1 + vv k) = ((onePlusPow k l t : k⟦X⟧) : k⸨X⸩) := by
  rw [map_add, map_one, vv_eq, delPi_coe,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero'
      (show PowerSeries.constantCoeff (onePlusPow k l t - 1) = 0 from binom_const _))]
  simp

theorem psi_del (t : ℤ_[l]ˣ) (x : k⸨X⸩) : psiPi k l (delPi k t x) = delPi k t (psiPi k l x) := by
  refine psi_comm k l _ (del_phi t) (fun j h0 h1 => ?_) x
  obtain ⟨i, hi, hm⟩ := PadicInt.exists_mem_range ((j : ℤ_[l]) * (t : ℤ_[l]))
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  refine ⟨i, (onePlusPow k l w : k⟦X⟧), Nat.pos_of_ne_zero ?_, hi, ?_⟩
  · rintro rfl
    have h2 : (l : ℤ_[l]) ∣ (j : ℤ_[l]) := by
      rw [← Units.dvd_mul_right (u := t)]; exact ⟨w, by simpa using hw⟩
    have h3 : ‖((j : ℤ) : ℤ_[l])‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]; simpa using h2
    rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at h3
    exact absurd (Nat.le_of_dvd h0 h3) (by omega)
  · rw [map_pow, del_one_add, phi_opp, ← map_pow, ← opp_mul, ← opp_mul, eq_add_of_sub_eq' hw, opp_add, opp_nat]
    simp [vv_eq]

def gamPi (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] : k⸨X⸩ →ₐ[k] k⸨X⸩ :=
  extend (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (gam_const (k := k) (l := l))))
    (by rw [PowerSeries.substAlgHom_X]; exact gam_ne)

theorem gamPi_eq (x : k⸨X⸩) : gamPi k l x = substHom _ (gam_const (k := k) (l := l)) gam_ne x := by
  have : (gamPi k l : k⸨X⸩ →+* k⸨X⸩) = substHom _ (gam_const (k := k) (l := l)) gam_ne := by
    refine hom_ext fun a => ?_
    rw [substHom_coe, RingHom.coe_coe, gamPi, extend_coe, PowerSeries.coe_substAlgHom]
  exact RingHom.congr_fun this x

theorem gamPi_eq' (x : k⸨X⸩) : FrobeniusBinomialReduction.gamπ k l x = gamPi k l x := by
  rw [gamPi_eq, FrobeniusBinomialReduction.gamπ, substL_eq]

theorem del_gam (t : ℤ_[l]ˣ) (x : k⸨X⸩) : delPi k t (gamPi k l x) = gamPi k l (delPi k t x) := by
  rw [gamPi_eq, gamPi_eq, delPi_comm]

theorem gam_int (a : k⟦X⟧) : ∃ b : k⟦X⟧, gamPi k l (a : k⸨X⸩) = b := ⟨_, extend_coe _ _ a⟩

theorem gam_one_add : gamPi k l (1 + vv k) = (1 + vv k) ^ (1 + l) := by
  rw [map_add, map_one, vv_eq, gamPi, extend_coe, PowerSeries.substAlgHom_X]
  simp

theorem gam_phi (x : k⸨X⸩) : gamPi k l (phiPi k l x) = phiPi k l (gamPi k l x) := by
  have ha : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hb := PowerSeries.HasSubst.of_constantCoeff_zero' (gam_const (k := k) (l := l))
  have : (gamPi k l : k⸨X⸩ →+* k⸨X⸩).comp (phiPi k l) = (phiPi k l).comp (gamPi k l : k⸨X⸩ →+* k⸨X⸩) := by
    refine hom_ext fun a => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, gamPi_eq, phi_eq_subst, substHom_coe]
    rw [PowerSeries.subst_comp_subst_apply ha hb, PowerSeries.subst_comp_subst_apply hb ha]
    congr 2
    rw [← PowerSeries.coe_substAlgHom ha, ← PowerSeries.coe_substAlgHom hb]
    simp only [map_sub, map_pow, map_add, map_one, PowerSeries.substAlgHom_X, add_sub_cancel, ← pow_mul, mul_comm]
  exact RingHom.congr_fun this x

theorem gam_pow (j : ℕ) : gamPi k l ((1 + vv k) ^ j) = (1 + vv k) ^ j * phiPi k l ((1 + vv k) ^ j) := by
  rw [map_pow, map_pow, gam_one_add, phi_one_add, ← mul_pow, pow_add, pow_one]

theorem psi_gam (x : k⸨X⸩) : psiPi k l (gamPi k l x) = gamPi k l (psiPi k l x) :=
  psi_comm k l (gamPi k l : k⸨X⸩ →+* k⸨X⸩) gam_phi (fun j h0 h1 => ⟨j, _, h0, h1, gam_pow j⟩) x

theorem gam_vv (h5 : 5 ≤ l) : ∃ c : k⟦X⟧, gamPi k l (vv k) = vv k * (1 + (c : k⸨X⸩) * vv k ^ 2) := by
  haveI : CharP k⸨X⸩ l := charP_of_injective_algebraMap (algebraMap k k⸨X⸩).injective l
  have h := gam_one_add (k := k) (l := l)
  rw [map_add, map_one, pow_add, pow_one, add_pow_char, one_pow] at h
  obtain ⟨e, he⟩ : ∃ e, l = e + 3 := ⟨l - 3, by omega⟩
  rw [show vv k ^ l = vv k ^ (e + 3) by rw [← he]] at h
  refine ⟨PowerSeries.X ^ e * (1 + PowerSeries.X), ?_⟩
  simp only [map_mul, map_pow, map_add, map_one, ← vv_eq]
  linear_combination h

theorem gam_sub_mem (h5 : 5 ≤ l) {x : k⸨X⸩} (hx : x ∈ Dp k 0) : gamPi k l x - x ∈ Dp k 2 := by
  obtain ⟨c, hc⟩ := gam_vv (k := k) h5
  have step : ∀ (s : ℤ), s ≤ 1 → (∀ b : k⟦X⟧, gamPi k l b - b ∈ Dp k s) →
      ∀ b : k⟦X⟧, gamPi k l b - b ∈ Dp k (s + 1) := by
    intro s hs h a
    set b : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
    have ha : (a : k⸨X⸩) = vv k * (b : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff a) := by
      conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a, map_add, map_mul, ← vv_eq_coe_X]
      rfl
    obtain ⟨t, ht⟩ := gam_int (l := l) b
    have : gamPi k l a - a = vv k ^ 1 * (gamPi k l b - b) + vv k ^ 3 * ((c * t : k⟦X⟧) : k⸨X⸩) := by
      rw [ha, map_add (gamPi k l), map_mul (gamPi k l), AlgHom.commutes, hc, ht, map_mul]; ring
    rw [this]
    exact Submodule.add_mem _ (Dp_mul (pow_mem 1) (h b) (by omega)) (Dp_mul (pow_mem 3) (coe_mem _) (by omega))
  obtain ⟨a, rfl⟩ := mem_Dp_zero.1 hx
  refine step 1 le_rfl (step 0 zero_le_one fun b => ?_) a
  obtain ⟨t, ht⟩ := gam_int (l := l) b
  rw [ht]
  exact Submodule.sub_mem _ (coe_mem _) (coe_mem _)

end Delta

section Core
variable {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] [CharP k l] {n : ℕ}

def piLat (k : Type) [Field k] (n : ℕ) : Submodule k⟦X⟧ (Fin n → k⸨X⸩) :=
  Submodule.pi Set.univ fun _ => stdLat k

theorem mem_sh_piLat {s : ℤ} {y : Fin n → k⸨X⸩} : y ∈ sh s (piLat k n) ↔ ∀ i, y i ∈ Dp k s := by
  simp only [Dp, mem_sh_iff_smul_mem, piLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Pi.smul_apply]

theorem isLat_piLat : IsLat (piLat k n) := by
  refine ⟨Submodule.fg_pi fun _ => isLat_stdLat.1, ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun k⸨X⸩ (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩ i -
  rw [Pi.basisFun_apply, Pi.single_apply]
  split_ifs
  · exact mem_stdLat.2 ⟨1, map_one _⟩
  · exact Submodule.zero_mem _

theorem exists_mem_sh (y : Fin n → k⸨X⸩) : ∃ s, y ∈ sh s (piLat k n) := by
  obtain ⟨s, hs⟩ := (Set.finite_range fun i => (y i).order).bddBelow
  exact ⟨s, mem_sh_piLat.2 fun i => Dp_mono (hs ⟨i, rfl⟩) (order_mem _)⟩

def semiOp (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : Matrix (Fin n) (Fin n) k⸨X⸩) : (Fin n → k⸨X⸩) →ₗ[k] (Fin n → k⸨X⸩) :=
  ((Matrix.toLin' H).restrictScalars k) ∘ₗ (lin σ).compLeft (Fin n)

theorem semiOp_apply (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : Matrix (Fin n) (Fin n) k⸨X⸩) (y : Fin n → k⸨X⸩) (i : Fin n) :
    semiOp σ H y i = ∑ m, H i m * σ (y m) := rfl

theorem semi_semiOp (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : Matrix (Fin n) (Fin n) k⸨X⸩) : Semi σ (semiOp σ H) := by
  intro a x
  funext i
  simp only [semiOp_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem twist_bij (h5 : 5 ≤ l) (H : Matrix (Fin n) (Fin n) k⸨X⸩) (hH : ∀ i m, (H - 1) i m ∈ Dp k 2)
    {j : ℕ} (h0 : 0 < j) (h1 : j < l) (s : ℤ) :
    Set.BijOn (fun y => (1 + vv k) ^ j • semiOp (gamPi k l) H y - y) (sh s (piLat k n)) (sh (s + 1) (piLat k n)) := by
  refine TwistShift.bijOn_twist (gamPi k l) _ (semi_semiOp _ H) gam_int (gam_vv h5) _ isLat_piLat ?_ j ?_ s
  · intro x hx
    rw [← sh_zero_eq (piLat k n), mem_sh_piLat] at hx
    refine mem_sh_piLat.2 fun i => ?_
    have : (semiOp (gamPi k l) H x - x) i =
        ∑ m, (H - 1) i m * gamPi k l (x m) + (gamPi k l (x i) - x i) := by
      simp [semiOp_apply, sub_mul, Matrix.one_apply]
    rw [this]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun m _ => Dp_mul (t := 0) (hH i m) ?_ (by simp))
      (gam_sub_mem h5 (hx i))
    obtain ⟨a, ha⟩ := mem_Dp_zero.1 (hx m)
    obtain ⟨b, hb⟩ := gam_int (l := l) a
    rw [ha, hb]; exact coe_mem _
  · rw [Ne, CharP.cast_eq_zero_iff k l]
    exact Nat.not_dvd_of_pos_of_lt h0 h1

theorem op_assemble (H : Matrix (Fin n) (Fin n) k⸨X⸩) (y : Fin l → Fin n → k⸨X⸩) (i : Fin n) :
    ∑ m, phiPi k l (H i m) * gamPi k l (assemble k l fun j => y j m) - assemble k l (fun j => y j i) =
      assemble k l fun j => ((1 + vv k) ^ (j : ℕ) • semiOp (gamPi k l) H (y j) - y j) i := by
  simp only [assemble, map_sum, map_mul (gamPi k l), gam_pow, gam_phi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    semiOp_apply, map_sub, map_mul (phiPi k l), mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [CharP k l] in
theorem exists_assemble (x : Fin n → k⸨X⸩) (hx : ∀ i, psiPi k l (x i) = 0) :
    ∃ y : Fin l → Fin n → k⸨X⸩, y 0 = 0 ∧ x = fun i => assemble k l fun j => y j i := by
  choose y hy using fun i => (assemble_bijective k l).2 (x i)
  refine ⟨fun j i => y i j, funext fun i => ?_, funext fun i => (hy i).symm⟩
  change y i 0 = 0
  rw [← psi_assemble k l (y i), hy, hx]

variable (h5 : 5 ≤ l) (H : Matrix (Fin n) (Fin n) k⸨X⸩) (hH : ∀ i m, (H - 1) i m ∈ Dp k 2)
include h5 hH

theorem core_maps {s : ℤ} (x : Fin n → k⸨X⸩) (hx : ∀ i, psiPi k l (x i) = 0) (hs : ∀ i, x i ∈ Dp k (l * s))
    (i : Fin n) : psiPi k l (∑ m, phiPi k l (H i m) * gamPi k l (x m) - x i) = 0 ∧
      ∑ m, phiPi k l (H i m) * gamPi k l (x m) - x i ∈ Dp k (l * (s + 1)) := by
  obtain ⟨y, h0, rfl⟩ := exists_assemble x hx
  rw [op_assemble, psi_assemble]
  refine ⟨by simp [h0], assemble_mem k l fun j => ?_⟩
  by_cases hj : j = 0
  · simp [hj, h0]
  · exact mem_sh_piLat.1 ((twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).1
      (mem_sh_piLat.2 fun i => mem_of_assemble_mem k l (hs i) j)) i

theorem core_inj (x : Fin n → k⸨X⸩) (hx : ∀ i, psiPi k l (x i) = 0)
    (h : ∀ i, ∑ m, phiPi k l (H i m) * gamPi k l (x m) - x i = 0) : x = 0 := by
  obtain ⟨y, h0, rfl⟩ := exists_assemble x hx
  have hz : assemble k l 0 = 0 := by simp [assemble]
  have : ∀ j, y j = 0 := by
    intro j
    by_cases hj : j = 0
    · rw [hj, h0]
    obtain ⟨s, hs⟩ := exists_mem_sh (y j)
    refine (twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).2.1 hs (Submodule.zero_mem _) ?_
    funext i
    have h1 := h i
    rw [op_assemble, ← hz] at h1
    simpa using congrFun ((assemble_bijective k l).1 h1) j
  funext i
  simp [this, assemble]

theorem core_surj {s : ℤ} (z : Fin n → k⸨X⸩) (hz : ∀ i, psiPi k l (z i) = 0) (hs : ∀ i, z i ∈ Dp k (l * (s + 1))) :
    ∃ x : Fin n → k⸨X⸩, (∀ i, psiPi k l (x i) = 0) ∧ (∀ i, x i ∈ Dp k (l * s)) ∧
      ∀ i, ∑ m, phiPi k l (H i m) * gamPi k l (x m) - x i = z i := by
  obtain ⟨w, h0, rfl⟩ := exists_assemble z hz
  have : ∀ j : Fin l, ∃ y ∈ sh s (piLat k n), (j = 0 → y = 0) ∧
      (1 + vv k) ^ (j : ℕ) • semiOp (gamPi k l) H y - y = w j := by
    intro j
    by_cases hj : j = 0
    · exact ⟨0, Submodule.zero_mem _, fun _ => rfl, by simp [hj, h0]⟩
    obtain ⟨y, hy, h⟩ := (twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).2.2
      (mem_sh_piLat.2 fun i => mem_of_assemble_mem k l (hs i) j)
    exact ⟨y, hy, fun e => absurd e hj, h⟩
  choose y h1 h2 h3 using this
  refine ⟨fun i => assemble k l fun j => y j i, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [psi_assemble, h2 0 rfl]; rfl
  · exact assemble_mem k l fun j => mem_sh_piLat.1 (h1 j) i
  · rw [op_assemble]; simp only [h3]

end Core

end GlobalTheory.PsiShiftProof
end
end
