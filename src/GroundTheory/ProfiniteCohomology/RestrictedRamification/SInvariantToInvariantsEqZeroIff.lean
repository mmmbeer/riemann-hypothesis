import Mathlib
import GroundTheory.GlobalFields.SUnits
import GroundTheory.GlobalFields.KummerTheory.Unramified
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SPicDefs

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory

universe u

section SUnits

variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E]

def sUnitsOf : Subgroup Eˣ where
  carrier := {x | IsIntegral (S.integer F) (x : E) ∧ IsIntegral (S.integer F) ((x⁻¹ : Eˣ) : E)}
  mul_mem' hx hy := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact hx.1.mul hy.1
    · rw [mul_inv, Units.val_mul]
      exact hx.2.mul hy.2
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]
      exact isIntegral_one
    · rw [inv_one, Units.val_one]
      exact isIntegral_one
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {S E}

theorem mem_sUnitsOf {x : Eˣ} :
    x ∈ sUnitsOf S E ↔
      IsIntegral (S.integer F) (x : E) ∧ IsIntegral (S.integer F) ((x⁻¹ : Eˣ) : E) :=
  Iff.rfl

theorem isIntegral_algEquiv_apply (σ : E ≃ₐ[F] E) {x : E} (hx : IsIntegral (S.integer F) x) :
    IsIntegral (S.integer F) (σ x) :=
  hx.map ((σ : E →ₐ[F] E).restrictScalars (S.integer F))

theorem mem_sUnitsOf_of_mem_rootsOfUnity {n : ℕ} (hn0 : n ≠ 0) {ζ : Eˣ}
    (hζ : ζ ∈ rootsOfUnity n E) : ζ ∈ sUnitsOf S E := by
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have h1 : ∀ y : Eˣ, y ^ n = 1 → IsIntegral (S.integer F) (y : E) := fun y hy =>
    ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, ← Units.val_pow_eq_pow_val,
        hy, Units.val_one, sub_self]⟩
  have hζ' : ζ ^ n = 1 := (mem_rootsOfUnity n ζ).1 hζ
  exact ⟨h1 ζ hζ', h1 ζ⁻¹ (by rw [inv_pow, hζ', inv_one])⟩

theorem galUnitsHom_mem_sUnitsOf (σ : E ≃ₐ[F] E) {x : Eˣ} (hx : x ∈ sUnitsOf S E) :
    galUnitsHom F E σ x ∈ sUnitsOf S E := by
  refine ⟨isIntegral_algEquiv_apply σ hx.1, ?_⟩
  rw [← map_inv]
  exact isIntegral_algEquiv_apply σ hx.2

variable (S E)

def galSUnitsHom : Gal(E/F) →* Monoid.End (sUnitsOf S E) where
  toFun σ := ((galUnitsHom F E σ).comp (sUnitsOf S E).subtype).codRestrict (sUnitsOf S E)
    fun x => galUnitsHom_mem_sUnitsOf σ x.2
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

@[simp]
theorem coe_galSUnitsHom_apply (σ : Gal(E/F)) (x : sUnitsOf S E) :
    (((galSUnitsHom S E σ x : Eˣ)) : E) = σ (x : Eˣ) :=
  rfl

abbrev galSUnits : Rep.{u} (ULift.{u} ℤ) Gal(E/F) :=
  Rep.of (intRepOfMonoidEnd.{u} (galSUnitsHom S E))

@[simp]
theorem galSUnits_ρ_apply (σ : Gal(E/F)) (x : Additive (sUnitsOf S E)) :
    (galSUnits S E).ρ σ x = Additive.ofMul (galSUnitsHom S E σ x.toMul) :=
  rfl

def sUnitsToUnits : galSUnits S E ⟶ galUnits.{u} F E :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (sUnitsOf S E).subtype), fun σ => by
    ext x
    rfl⟩

@[simp]
theorem sUnitsToUnits_hom_apply (x : Additive (sUnitsOf S E)) :
    ((sUnitsToUnits S E).hom x : Additive Eˣ) =
      Additive.ofMul ((Additive.toMul x : sUnitsOf S E) : Eˣ) :=
  rfl

theorem sUnitsToUnits_injective : Function.Injective (sUnitsToUnits S E).hom := fun _ _ h =>
  Additive.toMul.injective (Subtype.ext (Additive.ofMul.symm.injective h))

instance isDiscreteRep_galSUnits [Algebra.IsIntegral F E] : IsDiscreteRep (galSUnits S E) :=
  IsDiscreteRep.of_injective (sUnitsToUnits S E) (sUnitsToUnits_injective S E)

variable (n : ℕ) [NeZero n]

def rootsOfUnityToSUnitsHom : rootsOfUnity n E →* sUnitsOf S E :=
  (rootsOfUnity n E).subtype.codRestrict (sUnitsOf S E) fun ζ =>
    mem_sUnitsOf_of_mem_rootsOfUnity (NeZero.ne n) ζ.2

def rootsOfUnityToSUnits : galRootsOfUnity.{u} F E n ⟶ galSUnits S E :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (rootsOfUnityToSUnitsHom S E n)), fun σ => by
    ext x
    rfl⟩

@[simp]
theorem rootsOfUnityToSUnits_hom_apply (x : Additive (rootsOfUnity n E)) :
    ((((Additive.toMul ((rootsOfUnityToSUnits S E n).hom x) : sUnitsOf S E)) : Eˣ) : E) =
      (((Additive.toMul x : rootsOfUnity n E) : Eˣ) : E) :=
  rfl

noncomputable def sUnitsKummerSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(E/F)) :=
  ShortComplex.mk (rootsOfUnityToSUnits S E n) (n • 𝟙 (galSUnits S E)) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change ((((Additive.toMul (α := rootsOfUnity n E) x : rootsOfUnity n E) : Eˣ) ^ n : Eˣ) : E) = 1
    rw [(mem_rootsOfUnity n _).1 (Additive.toMul (α := rootsOfUnity n E) x).2, Units.val_one])

theorem sUnitsKummerSequence_g : (sUnitsKummerSequence S E n).g = n • 𝟙 (galSUnits S E) :=
  rfl

end SUnits

section Max

variable (F : Type u) [Field F] [NumberField F] (Ω : Type u) [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

noncomputable abbrev sUnitsMax : Subgroup (maxUnramifiedOutside F Ω S)ˣ :=
  sUnitsOf S (maxUnramifiedOutside F Ω S)

noncomputable abbrev galSUnitsMax : Rep.{u} (ULift.{u} ℤ) (galUnramifiedOutside F Ω S) :=
  galSUnits S (maxUnramifiedOutside F Ω S)

example [Algebra.IsIntegral F Ω] : IsDiscreteRep (galSUnitsMax F Ω S) := inferInstance

end Max

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

universe u

section Valuation

theorem valuation_le_one_of_isIntegral {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (w : Valuation L (WithZero (Multiplicative ℤ))) (hR : ∀ r : R, w (algebraMap R L r) ≤ 1)
    {x : L} (hx : IsIntegral R x) : w x ≤ 1 := by
  let f : R →+* w.integer := (algebraMap R L).codRestrict w.integer hR
  have hx' : IsIntegral w.integer (RingHom.id L x) :=
    IsIntegral.map_of_comp_eq f (RingHom.id L) (by ext r; rfl) hx
  exact (Valuation.integer.integers w).mem_of_integral hx'

theorem exists_mul_pow_le_one {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (ha : a < 1)
    (hb : b ≠ 0) : ∃ N : ℕ, b * a ^ N ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = WithZero.exp k := ⟨_, (WithZero.exp_log ha0).symm⟩
  obtain ⟨m, rfl⟩ : ∃ m, b = WithZero.exp m := ⟨_, (WithZero.exp_log hb).symm⟩
  have hk : k < 0 := by
    rw [← WithZero.exp_zero] at ha
    exact WithZero.exp_lt_exp.1 ha
  refine ⟨m.toNat, ?_⟩
  rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  have : (m.toNat : ℤ) * k ≤ -(m.toNat : ℤ) := by nlinarith [Int.self_le_toNat m]
  rw [nsmul_eq_mul]
  omega

end Valuation

section Compare

variable {F : Type u} [Field F] [NumberField F] {L : Type u} [Field L] [NumberField L] [Algebra F L]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

def underPlace (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 F) :=
  ⟨w.asIdeal.under (𝓞 F), inferInstance, Ideal.under_ne_bot (𝓞 F) w.ne_bot⟩

instance liesOver_underPlace (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (underPlace (F := F) w).asIdeal :=
  ⟨rfl⟩

omit [NumberField F] [NumberField L] in
theorem liesOver_iff_eq_underPlace {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 F)} :
    w.asIdeal.LiesOver v.asIdeal ↔ v = underPlace w :=
  ⟨fun h => HeightOneSpectrum.ext h.over, fun h => h ▸ ⟨rfl⟩⟩

variable {S} in
omit [NumberField F] [NumberField L] in
theorem mem_placesOver_iff {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOver S ↔ underPlace w ∈ S := by
  constructor
  · rintro ⟨v, hv, hwv⟩
    rwa [← liesOver_iff_eq_underPlace.1 hwv]
  · intro h
    exact ⟨_, h, inferInstance⟩

theorem valuation_algebraMap_integer_le_one {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ placesOver S)
    (r : S.integer F) : w.valuation L (algebraMap F L r) ≤ 1 := by
  have hv : underPlace (F := F) w ∉ S := fun h => hw (mem_placesOver_iff.2 h)
  rw [← valuation_liesOver (K := F) L (underPlace (F := F) w) w]
  exact pow_le_one₀ zero_le (r.2 _ hv)

theorem valuation_le_one_of_isIntegral_integer {x : L} (hx : IsIntegral (S.integer F) x)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ placesOver S) : w.valuation L x ≤ 1 :=
  valuation_le_one_of_isIntegral (w.valuation L)
    (fun r => valuation_algebraMap_integer_le_one S hw r) hx

theorem isIntegral_integer_of_valuation_le_one {x : L}
    (h : ∀ w ∉ placesOver (L := L) S, w.valuation L x ≤ 1) : IsIntegral (S.integer F) x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · exact isIntegral_zero
  have hT : (Support (𝓞 L) x).Finite := Support.finite (𝓞 L) x
  have hTS : ∀ w ∈ Support (𝓞 L) x, underPlace (F := F) w ∈ S := fun w hw => by
    by_contra hn
    exact (not_lt.2 (h w fun hm => hn (mem_placesOver_iff.1 hm))) hw
  let V : Finset (HeightOneSpectrum (𝓞 F)) := hT.toFinset.image underPlace
  let π : HeightOneSpectrum (𝓞 F) → 𝓞 F := fun v =>
    (Global.SUnit.exists_pow_classNumber_eq_span v).choose
  let t : Fˣ := ∏ v ∈ V, Global.SUnit.placeUnit v
  have htS : t ∈ S.unit F := Subgroup.prod_mem _ fun v hv => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact Global.SUnit.placeUnit_mem S (hTS w (hT.mem_toFinset.1 hw))
  have ht₀ : (t : F) = algebraMap (𝓞 F) F (∏ v ∈ V, π v) := by
    simp only [t, Units.coe_prod, map_prod]
    rfl
  have hπ : ∀ v, π v ∈ v.asIdeal := fun v => by
    have h1 : π v ∈ Ideal.span {π v} := Ideal.mem_span_singleton_self _
    rw [← (Global.SUnit.exists_pow_classNumber_eq_span v).choose_spec.2] at h1
    exact Ideal.pow_le_self Fintype.card_ne_zero h1
  have hwt : ∀ w ∈ Support (𝓞 L) x, w.valuation L (algebraMap F L t) < 1 := by
    intro w hw
    have hv : underPlace w ∈ V := Finset.mem_image_of_mem _ (hT.mem_toFinset.2 hw)
    have hmem : ∏ v ∈ V, π v ∈ (underPlace (F := F) w).asIdeal := by
      rw [← Finset.mul_prod_erase V π hv]
      exact Ideal.mul_mem_right _ _ (hπ _)
    have hmem' : algebraMap (𝓞 F) (𝓞 L) (∏ v ∈ V, π v) ∈ w.asIdeal := hmem
    rw [ht₀, ← IsScalarTower.algebraMap_apply (𝓞 F) F L,
      IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L, valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem w _).2 hmem'
  have hwt1 : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L (algebraMap F L t) ≤ 1 := by
    intro w
    rw [ht₀, ← IsScalarTower.algebraMap_apply (𝓞 F) F L,
      IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L]
    exact w.valuation_le_one _
  have ht0 : algebraMap F L t ≠ 0 := (map_ne_zero _).2 t.ne_zero
  have hN : ∀ w : HeightOneSpectrum (𝓞 L), ∃ N : ℕ, w ∈ Support (𝓞 L) x →
      w.valuation L x * w.valuation L (algebraMap F L t) ^ N ≤ 1 := by
    intro w
    by_cases hw : w ∈ Support (𝓞 L) x
    · obtain ⟨N, hN⟩ := exists_mul_pow_le_one ((map_ne_zero (w.valuation L)).2 ht0) (hwt w hw)
        ((map_ne_zero (w.valuation L)).2 hx0)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose Nw hNw using hN
  let N := ∑ w ∈ hT.toFinset, Nw w
  let y := algebraMap F L t ^ N * x
  have hy : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L y ≤ 1 := by
    intro w
    simp only [y, map_mul, map_pow]
    by_cases hw : w ∈ Support (𝓞 L) x
    · have hle : Nw w ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hT.mem_toFinset.2 hw)
      rw [mul_comm]
      exact (mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' (hwt1 w) hle)).trans
        (hNw w hw)
    · have hx1 : w.valuation L x ≤ 1 := not_lt.1 hw
      exact mul_le_one' (pow_le_one₀ zero_le (hwt1 w)) hx1
  obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one (R := 𝓞 L) L y hy
  have hyI : IsIntegral (S.integer F) y := by
    rw [← hb]
    exact (RingOfIntegers.isIntegral_coe b).tower_top
  have hc : (((t⁻¹ ^ N : Fˣ)) : F) ∈ S.integer F := fun v hv =>
    (Subgroup.pow_mem _ (inv_mem htS) N v hv).le
  have hxy : x = algebraMap (S.integer F) L ⟨_, hc⟩ * y := by
    change x = algebraMap F L (((t⁻¹ ^ N : Fˣ)) : F) * (algebraMap F L t ^ N * x)
    rw [← mul_assoc, ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      inv_pow, inv_mul_cancel, Units.val_one, map_one, one_mul]
  rw [hxy]
  exact isIntegral_algebraMap.mul hyI

theorem mem_sUnitsOf_iff_mem_unit {x : Lˣ} :
    x ∈ sUnitsOf S L ↔ x ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L := by
  constructor
  · intro hx w hw
    have h1 := valuation_le_one_of_isIntegral_integer S hx.1 hw
    have h2 := valuation_le_one_of_isIntegral_integer S hx.2 hw
    refine eq_one_of_one_le_mul_left h1 h2 (Eq.ge ?_)
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  · intro hx
    exact ⟨isIntegral_integer_of_valuation_le_one S fun w hw =>
        (hx w hw).le,
      isIntegral_integer_of_valuation_le_one S fun w hw =>
        (inv_mem hx w hw).le⟩

end Compare

section Invariants

variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E]

theorem isIntegral_algebraMap_of_mem_integer {c : F} (hc : c ∈ S.integer F) :
    IsIntegral (S.integer F) (algebraMap F E c) :=
  isIntegral_algebraMap (x := (⟨c, hc⟩ : S.integer F))

theorem isIntegral_of_isIntegral_algebraMap {c : F}
    (hc : IsIntegral (S.integer F) (algebraMap F E c)) : IsIntegral (S.integer F) c :=
  (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars (S.integer F))
    (algebraMap F E).injective).1 hc

theorem mem_integer_of_isIntegral {c : F} (hc : IsIntegral (S.integer F) c) : c ∈ S.integer F :=
  fun v _ => valuation_le_one_of_isIntegral (v.valuation F) (fun r => r.2 v ‹_›) hc

variable {E} in

theorem map_mem_sUnitsOf_iff {a : Fˣ} :
    Units.map (algebraMap F E : F →* E) a ∈ sUnitsOf S E ↔ a ∈ S.unit F := by
  constructor
  · intro h v hv
    have h1 : (a : F) ∈ S.integer F :=
      mem_integer_of_isIntegral S (isIntegral_of_isIntegral_algebraMap S E h.1)
    have h2 : ((a⁻¹ : Fˣ) : F) ∈ S.integer F := by
      refine mem_integer_of_isIntegral S (isIntegral_of_isIntegral_algebraMap S E ?_)
      have := h.2
      rwa [← map_inv] at this
    refine eq_one_of_one_le_mul_left (h1 v hv) (h2 v hv) (Eq.ge ?_)
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  · intro h
    refine ⟨isIntegral_algebraMap_of_mem_integer S E fun v hv => (h v hv).le, ?_⟩
    rw [← map_inv]
    exact isIntegral_algebraMap_of_mem_integer S E fun v hv => (inv_mem h v hv).le

def sUnitsToInvariants : Additive (S.unit F) →+ (galSUnits S E).ρ.invariants where
  toFun a := ⟨Additive.ofMul ⟨Units.map (algebraMap F E : F →* E) (Additive.toMul a : S.unit F),
      (map_mem_sUnitsOf_iff S).2 (Additive.toMul a).2⟩, fun σ =>
    Additive.toMul.injective (Subtype.ext (Units.ext (σ.commutes _)))⟩
  map_zero' := Subtype.ext (Additive.toMul.injective (Subtype.ext (Units.ext (map_one _))))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Subtype.ext (Units.ext (map_mul _ _ _))))

@[simp]
theorem coe_sUnitsToInvariants_apply (a : Additive (S.unit F)) :
    (((Additive.toMul (α := sUnitsOf S E) (sUnitsToInvariants S E a).1 : sUnitsOf S E) : Eˣ) : E) =
      algebraMap F E ((Additive.toMul a : S.unit F) : Fˣ) :=
  rfl

theorem sUnitsToInvariants_injective : Function.Injective (sUnitsToInvariants S E) := by
  intro a b h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (algebraMap F E).injective (congrArg (fun v : (galSUnits S E).ρ.invariants =>
    (((Additive.toMul (α := sUnitsOf S E) v.1 : sUnitsOf S E) : Eˣ) : E)) h)

theorem sUnitsToInvariants_surjective [IsGalois F E] :
    Function.Surjective (sUnitsToInvariants S E) := by
  intro v
  let u : Eˣ := ((Additive.toMul (α := sUnitsOf S E) v.1 : sUnitsOf S E) : Eˣ)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (u : E)).2 fun σ =>
    congrArg (fun w : Additive (sUnitsOf S E) =>
      (((Additive.toMul w : sUnitsOf S E) : Eˣ) : E)) (v.2 σ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact u.ne_zero ha.symm
  have hmap : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = u := Units.ext ha
  have hS : Units.mk0 a ha0 ∈ S.unit F := by
    rw [← map_mem_sUnitsOf_iff S (E := E), hmap]
    exact (Additive.toMul (α := sUnitsOf S E) v.1).2
  exact ⟨Additive.ofMul ⟨Units.mk0 a ha0, hS⟩,
    Subtype.ext (Additive.toMul.injective (Subtype.ext hmap))⟩

noncomputable def sUnitsInvariantsEquiv [IsGalois F E] :
    Additive (S.unit F) ≃+ (galSUnits S E).ρ.invariants :=
  AddEquiv.ofBijective (sUnitsToInvariants S E)
    ⟨sUnitsToInvariants_injective S E, sUnitsToInvariants_surjective S E⟩

@[simp]
theorem sUnitsInvariantsEquiv_apply [IsGalois F E] (a : Additive (S.unit F)) :
    sUnitsInvariantsEquiv S E a = sUnitsToInvariants S E a :=
  rfl

end Invariants

section Max

variable (F : Type u) [Field F] [NumberField F] (Ω : Type u) [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem map_inclusion_mem_sUnitsMax_iff {L : IntermediateField F Ω}
    (hL : L ≤ maxUnramifiedOutside F Ω S) {x : Lˣ} :
    Units.map (IntermediateField.inclusion hL : L →* maxUnramifiedOutside F Ω S) x ∈
      sUnitsMax F Ω S ↔ x ∈ sUnitsOf S L := by
  let f := (IntermediateField.inclusion hL).restrictScalars (S.integer F)
  have hf : Function.Injective f := (IntermediateField.inclusion hL).toRingHom.injective
  constructor
  · intro h
    refine ⟨(isIntegral_algHom_iff f hf).1 h.1, (isIntegral_algHom_iff f hf).1 ?_⟩
    have := h.2
    rwa [← map_inv] at this
  · intro h
    refine ⟨(isIntegral_algHom_iff f hf).2 h.1, ?_⟩
    rw [← map_inv]
    exact (isIntegral_algHom_iff f hf).2 h.2

variable [IsGalois F Ω]

theorem exists_of_mem_sUnitsMax {y : (maxUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ sUnitsMax F Ω S) :
    ∃ (L : IntermediateField F Ω) (_ : FiniteDimensional F L)
      (hL : L ≤ maxUnramifiedOutside F Ω S) (x : Lˣ), x ∈ sUnitsOf S L ∧
        Units.map (IntermediateField.inclusion hL : L →* maxUnramifiedOutside F Ω S) x = y := by
  obtain ⟨L, hf, hu, hmem⟩ :=
    (mem_maxUnramifiedOutside_iff S).1 (y : maxUnramifiedOutside F Ω S).2
  have hL := le_maxUnramifiedOutside S hu
  have hx0 : (⟨_, hmem⟩ : L) ≠ 0 := by
    intro h
    apply y.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  have hmap : Units.map (IntermediateField.inclusion hL : L →* maxUnramifiedOutside F Ω S)
      (Units.mk0 _ hx0) = y := Units.ext rfl
  refine ⟨L, hf, hL, Units.mk0 _ hx0, ?_, hmap⟩
  rw [← map_inclusion_mem_sUnitsMax_iff F Ω S hL, hmap]
  exact hy

end Max

section Roots

variable {F : Type u} [Field F] [NumberField F] {Ω : Type u} [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem adjoin_gen_eq_top (L : Type u) [Field L] [Algebra L Ω] (α : Ω) :
    IntermediateField.adjoin L {IntermediateField.AdjoinSimple.gen L α} = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin L {α}).val
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.val_mk,
    IntermediateField.AdjoinSimple.coe_gen, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]

variable [IsGalois F Ω]

theorem mem_maxUnramifiedOutside_of_pow_eq {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {y : (maxUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ sUnitsMax F Ω S) {α : Ω} (hα : α ^ n = ((y : maxUnramifiedOutside F Ω S) : Ω)) :
    α ∈ maxUnramifiedOutside F Ω S := by
  obtain ⟨L, hfin, hLle, x, hxS, rfl⟩ := exists_of_mem_sUnitsMax F Ω S hy
  have : NumberField L := NumberField.of_module_finite F L
  have hxU := (mem_sUnitsOf_iff_mem_unit S).1 hxS
  have hLu : IsUnramifiedOutside S L := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hLle
  have hα' : α ^ n = algebraMap L Ω (x : L) := hα
  have hαint : IsIntegral L α := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hα']
    exact isIntegral_algebraMap
  let M : IntermediateField L Ω := IntermediateField.adjoin L {α}
  have : FiniteDimensional L M := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField M := NumberField.of_module_finite L M
  have hgen : α ^ n = algebraMap L Ω (x : L) := hα'
  have hβ : IntermediateField.AdjoinSimple.gen L α ^ n = algebraMap L M (x : L) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hgen]
    rfl
  have hMu : IsUnramifiedOutside (placesOver S) M := by
    intro w hw
    refine Global.Kummer.isUnramifiedIn_of_pow_eq x hβ (adjoin_gen_eq_top L α) w ?_ ?_
    · intro hmem
      have hv : underPlace (F := F) w ∉ S := fun h => hw (mem_placesOver_iff.2 h)
      apply hnS _ hv
      change ((n : ℕ) : 𝓞 F) ∈ Ideal.comap (algebraMap (𝓞 F) (𝓞 L)) w.asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hmem
    · rw [hxU w hw, WithZero.log_one]
      exact dvd_zero _
  have hMF := (isUnramifiedOutside_restrictScalars_iff S hLu M).2 hMu
  have : FiniteDimensional F (M.restrictScalars F) := FiniteDimensional.trans F L M
  exact le_maxUnramifiedOutside S hMF (IntermediateField.mem_adjoin_simple_self L α)

theorem mem_maxUnramifiedOutside_of_pow_eq_one {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {ζ : Ω} (hζ : ζ ^ n = 1) :
    ζ ∈ maxUnramifiedOutside F Ω S :=
  mem_maxUnramifiedOutside_of_pow_eq S hn hnS (sUnitsMax F Ω S).one_mem hζ

theorem mem_sUnitsOf_of_pow_mem (E : Type u) [Field E] [Algebra F E] {n : ℕ} (hn : n ≠ 0)
    {β : Eˣ} (hβ : β ^ n ∈ sUnitsOf S E) : β ∈ sUnitsOf S E := by
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_, IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_⟩
  · rw [← Units.val_pow_eq_pow_val]
    exact hβ.1
  · rw [← Units.val_pow_eq_pow_val, inv_pow]
    exact hβ.2

variable [IsSepClosed Ω]

theorem exists_pow_eq_of_mem_sUnitsMax {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {y : (maxUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ sUnitsMax F Ω S) : ∃ β ∈ sUnitsMax F Ω S, β ^ n = y := by
  have : NeZero ((n : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap F Ω)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)⟩
  obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq
    (((y : maxUnramifiedOutside F Ω S) : Ω)) n
  have hαS := mem_maxUnramifiedOutside_of_pow_eq S hn hnS hy hα
  have hα0 : (⟨α, hαS⟩ : maxUnramifiedOutside F Ω S) ≠ 0 := by
    intro h
    have h' : α = 0 := congrArg Subtype.val h
    rw [h', zero_pow hn] at hα
    exact y.ne_zero (Subtype.ext hα.symm)
  have hpow : Units.mk0 _ hα0 ^ n = y := Units.ext (Subtype.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow]
    exact hα))
  refine ⟨Units.mk0 _ hα0, mem_sUnitsOf_of_pow_mem S _ hn (hpow ▸ hy), hpow⟩

theorem sUnitsKummerSequence_shortExact (n : ℕ) [NeZero n]
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro x hx
    let x' : Additive (sUnitsMax F Ω S) := x
    have hx2 : n • x' = 0 :=
      (nsmul_id_hom_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n x).symm.trans hx
    have hx' : (Additive.toMul x' : sUnitsMax F Ω S) ^ n = 1 := by
      rw [← toMul_nsmul, hx2]
      rfl
    have hmem : ((Additive.toMul x' : sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ) ∈
        rootsOfUnity n (maxUnramifiedOutside F Ω S) := by
      rw [mem_rootsOfUnity, ← Subgroup.coe_pow, hx']
      rfl
    exact ⟨Additive.ofMul ⟨_, hmem⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun a b h =>
    Additive.toMul.injective (Subtype.ext (congrArg
      (fun z : Additive (sUnitsMax F Ω S) => ((Additive.toMul z : sUnitsMax F Ω S) :
        (maxUnramifiedOutside F Ω S)ˣ)) h))
  epi_g := (Rep.epi_iff_surjective _).2 fun y => by
    obtain ⟨β, hβ, hβn⟩ := exists_pow_eq_of_mem_sUnitsMax S (NeZero.ne n) hnS
      (Additive.toMul y : sUnitsMax F Ω S).2
    refine ⟨Additive.ofMul ⟨β, hβ⟩, ?_⟩
    refine (nsmul_id_hom_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n _).trans ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    change β ^ n = _
    exact hβn

end Roots

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Pointwise

theorem eq_of_forall_le_exp_iff {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, a ≠ 0 → a ≤ 1 →
      (∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) → b ≤ WithZero.exp (-(n : ℤ))) → b ≤ a := by
    intro a b ha0 ha1 h
    have hlog : WithZero.log a ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log ha0, WithZero.exp_zero]
      exact ha1
    have hn : ((-WithZero.log a).toNat : ℤ) = -WithZero.log a := Int.toNat_of_nonneg (by omega)
    have := h (-WithZero.log a).toNat (by rw [hn, neg_neg, WithZero.exp_log ha0])
    rwa [hn, neg_neg, WithZero.exp_log ha0] at this
  exact le_antisymm (key hb0 hb1 fun n => (h n).2) (key ha0 ha1 fun n => (h n).1)

section Conjugate

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]

def smulPlace (σ : G) (w : HeightOneSpectrum B) : HeightOneSpectrum B where
  asIdeal := σ • w.asIdeal
  isPrime := Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv G B σ)
  ne_bot := by
    intro h
    apply w.ne_bot
    rw [← inv_smul_smul σ w.asIdeal, h]
    exact Ideal.map_bot

omit [IsDedekindDomain B] in
theorem smulPlace_asIdeal (σ : G) (w : HeightOneSpectrum B) :
    (smulPlace σ w).asIdeal = σ • w.asIdeal :=
  rfl

theorem intValuation_smulPlace (σ : G) (w : HeightOneSpectrum B) (r : B) :
    (smulPlace σ w).intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [smul_zero, map_zero, map_zero]
  have hσr : σ • r ≠ 0 := fun h => hr (by rw [← inv_smul_smul σ r, h, smul_zero])
  refine eq_of_forall_le_exp_iff (intValuation_ne_zero _ _ hσr) (intValuation_ne_zero _ _ hr)
    (intValuation_le_one _ _) (intValuation_le_one _ _) fun n => ?_
  rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, smulPlace_asIdeal, ← smul_pow']
  exact Ideal.smul_mem_pointwise_smul_iff

end Conjugate

section NumberField

variable {F M : Type*} [Field F] [Field M] [NumberField M] [Algebra F M]

theorem valuation_smulPlace (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M (σ x) = w.valuation M x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  have ha : σ (algebraMap (𝓞 M) M a) = algebraMap (𝓞 M) M (σ • a) := rfl
  have hb' : σ (algebraMap (𝓞 M) M b) = algebraMap (𝓞 M) M (σ • b) := rfl
  rw [map_div₀, ha, hb', map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_smulPlace,
    intValuation_smulPlace]

theorem valuation_smulPlace_apply (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M x = w.valuation M (σ⁻¹ x) := by
  rw [← valuation_smulPlace σ w (σ⁻¹ x)]
  congr 1
  exact (AlgEquiv.apply_symm_apply σ x).symm

end NumberField

section Unramified

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem valuation_algebraMap_of_isUnramifiedAt (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L)) [W.asIdeal.LiesOver w.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal] (x : K) :
    W.valuation L (algebraMap K L x) = w.valuation K x := by
  rw [← valuation_liesOver L w W x,
    Ideal.ramificationIdx'_eq_ramificationIdx' w.asIdeal W.asIdeal
      (Ideal.map_ne_bot_of_ne_bot w.ne_bot),
    Ideal.ramificationIdx_eq_one, pow_one]

end Unramified

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Pointwise

universe u

section Tower

variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra F K]
  [Algebra F L] [Algebra K L] [IsScalarTower F K L]

omit [NumberField F] [NumberField L] in

theorem exists_underPlace_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ w : HeightOneSpectrum (𝓞 L), underPlace (F := F) w = v := by
  obtain ⟨⟨Q, hQ, hQv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
    (liesOver_iff_eq_underPlace.1 hQv).symm⟩

omit [NumberField F] [NumberField K] [NumberField L] in

theorem underPlace_underPlace (W : HeightOneSpectrum (𝓞 L)) :
    underPlace (F := F) (underPlace (F := K) W) = underPlace (F := F) W :=
  HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 F) (B := 𝓞 K) W.asIdeal)

theorem valuation_algebraMap_underPlace (W : HeightOneSpectrum (𝓞 L))
    (hW : Algebra.IsUnramifiedAt (𝓞 F) W.asIdeal) (y : K) :
    W.valuation L (algebraMap K L y) = (underPlace (F := K) W).valuation K y := by
  have hu := ((isUnramifiedAt_tower_iff (F := F) (L := K) W.asIdeal).1 hW).2
  exact valuation_algebraMap_of_isUnramifiedAt (underPlace (F := K) W) W y

end Tower

section Field

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

def IsSInvariant (x : (maxUnramifiedOutside F Ω S)ˣ) : Prop :=
  ∀ σ : galUnramifiedOutside F Ω S, galUnitsHom F _ σ x * x⁻¹ ∈ sUnitsMax F Ω S

def IsOrdAbove (v : HeightOneSpectrum (𝓞 F)) (x : (maxUnramifiedOutside F Ω S)ˣ) (m : ℤ) : Prop :=
  ∃ (E : IntermediateField F Ω) (_ : FiniteDimensional F E) (_ : E ≤ maxUnramifiedOutside F Ω S)
    (hx : ((x : maxUnramifiedOutside F Ω S) : Ω) ∈ E),
    letI := NumberField.of_module_finite F E
    ∃ w : HeightOneSpectrum (𝓞 E), underPlace (F := F) w = v ∧
      w.valuation E ⟨_, hx⟩ = WithZero.exp (-m)

variable [IsGalois F Ω]

theorem exists_isOrdAbove (v : HeightOneSpectrum (𝓞 F)) (x : (maxUnramifiedOutside F Ω S)ˣ) :
    ∃ m, IsOrdAbove S v x m := by
  obtain ⟨E, hf, hu, hx⟩ :=
    (mem_maxUnramifiedOutside_iff S).1 (x : maxUnramifiedOutside F Ω S).2
  have := NumberField.of_module_finite F E
  obtain ⟨w, hw⟩ := exists_underPlace_eq (L := E) v
  have h0 : w.valuation E ⟨_, hx⟩ ≠ 0 := by
    rw [Ne, map_eq_zero]
    intro h
    apply x.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  refine ⟨-WithZero.log (w.valuation E ⟨_, hx⟩), E, hf, le_maxUnramifiedOutside S hu, hx, w, hw, ?_⟩
  rw [neg_neg, WithZero.exp_log h0]

end Field

section Galois

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem exists_galUnramifiedOutside_restrict {M : IntermediateField F Ω} [Normal F M]
    (hMle : M ≤ maxUnramifiedOutside F Ω S) (τ : Gal(M/F)) :
    ∃ ρ : galUnramifiedOutside F Ω S, ∀ y : M,
      ((ρ ⟨y, hMle y.2⟩ : maxUnramifiedOutside F Ω S) : Ω) = ((τ y : M) : Ω) := by
  refine ⟨(τ.liftNormal Ω).restrictNormal (maxUnramifiedOutside F Ω S), fun y => ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes (τ.liftNormal Ω) (maxUnramifiedOutside F Ω S)
    ⟨y, hMle y.2⟩
  have h2 := AlgEquiv.liftNormal_commutes τ Ω y
  exact h1.trans h2

theorem valuation_eq_of_isSInvariant {M : IntermediateField F Ω} [FiniteDimensional F M]
    [IsGalois F M] [NumberField M] (hMle : M ≤ maxUnramifiedOutside F Ω S)
    {x : (maxUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x)
    (hxM : ((x : maxUnramifiedOutside F Ω S) : Ω) ∈ M) (W W' : HeightOneSpectrum (𝓞 M))
    (hWW' : underPlace (F := F) W = underPlace (F := F) W')
    (hWS : underPlace (F := F) W ∉ S) :
    W.valuation M ⟨_, hxM⟩ = W'.valuation M ⟨_, hxM⟩ := by
  have : IsGaloisGroup Gal(M/F) (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ F M
  have : W'.asIdeal.LiesOver (underPlace (F := F) W).asIdeal := by
    rw [hWW']
    infer_instance
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (underPlace (F := F) W).asIdeal
    W.asIdeal W'.asIdeal Gal(M/F)
  have hW' : W' = smulPlace σ W := HeightOneSpectrum.ext hσ.symm
  rw [hW', valuation_smulPlace_apply]
  set y : M := ⟨_, hxM⟩ with hy
  have hy0 : y ≠ 0 := by
    intro h
    apply x.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp [hy] at this
  obtain ⟨ρ, hρ⟩ := exists_galUnramifiedOutside_restrict S hMle σ⁻¹
  have hyu : (σ⁻¹ y / y : M) ≠ 0 := div_ne_zero ((map_ne_zero _).2 hy0) hy0
  let u : Mˣ := Units.mk0 _ hyu
  have hmap : Units.map (IntermediateField.inclusion hMle : M →* maxUnramifiedOutside F Ω S) u =
      galUnitsHom F _ ρ x * x⁻¹ := by
    apply Units.ext
    apply Subtype.ext
    have h1 := hρ y
    simp only [Units.coe_map, Units.val_mk0, MonoidHom.coe_coe, Units.val_mul,
      coe_galUnitsHom_apply, Units.val_inv_eq_inv_val, IntermediateField.coe_mul,
      IntermediateField.coe_inv, u]
    rw [IntermediateField.coe_inclusion, IntermediateField.coe_div, div_eq_mul_inv]
    congr 1
    exact h1.symm
  have hu : u ∈ sUnitsOf S M := by
    rw [← map_inclusion_mem_sUnitsMax_iff F Ω S hMle, hmap]
    exact hx ρ
  have hu1 := (mem_sUnitsOf_iff_mem_unit S).1 hu W (fun h => hWS (mem_placesOver_iff.1 h))
  have hu1' : W.valuation M (σ⁻¹ y / y) = 1 := hu1
  rw [map_div₀, div_eq_one_iff_eq ((map_ne_zero _).2 hy0)] at hu1'
  exact hu1'.symm

end Galois

section Ord

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

omit [IsGalois F Ω] in
theorem finiteDimensional_of_numberField (E : IntermediateField F Ω) [NumberField E] :
    FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem exists_place_valuation_eq_of_le {E M : IntermediateField F Ω} [NumberField E]
    [NumberField M] (hEM : E ≤ M) (hMle : M ≤ maxUnramifiedOutside F Ω S)
    (w : HeightOneSpectrum (𝓞 E)) (hwS : underPlace (F := F) w ∉ S) :
    ∃ W : HeightOneSpectrum (𝓞 M), underPlace (F := F) W = underPlace (F := F) w ∧
      ∀ y : E, W.valuation M ⟨y, hEM y.2⟩ = w.valuation E y := by
  have := finiteDimensional_of_numberField M
  let _ : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hMu : IsUnramifiedOutside S M :=
    (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hMle
  obtain ⟨W, hW⟩ := exists_underPlace_eq (F := E) (L := M) w
  have hWF : underPlace (F := F) W = underPlace (F := F) w := by
    rw [← hW, underPlace_underPlace]
  refine ⟨W, hWF, fun y => ?_⟩
  have hun : Algebra.IsUnramifiedAt (𝓞 F) W.asIdeal :=
    hMu (underPlace (F := F) W) (hWF ▸ hwS) W.asIdeal inferInstance inferInstance
  have := valuation_algebraMap_underPlace (F := F) W hun y
  rw [hW] at this
  exact this

theorem IsOrdAbove.unique {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {x : (maxUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x) {m m' : ℤ}
    (h : IsOrdAbove S v x m) (h' : IsOrdAbove S v x m') : m = m' := by
  obtain ⟨E, hEf, hEle, hxE, hh⟩ := h
  obtain ⟨E', hE'f, hE'le, hxE', hh'⟩ := h'
  have := NumberField.of_module_finite F E
  have := NumberField.of_module_finite F E'
  obtain ⟨w, hw, hwx⟩ := hh
  obtain ⟨w', hw', hw'x⟩ := hh'
  let M : IntermediateField F Ω := IntermediateField.normalClosure F ↥(E ⊔ E') Ω
  have hMle : M ≤ maxUnramifiedOutside F Ω S :=
    (IntermediateField.normalClosure_le_iff_of_normal (K₂ := maxUnramifiedOutside F Ω S)).2 (sup_le hEle hE'le)
  have hEM : E ≤ M := le_sup_left.trans (IntermediateField.le_normalClosure _)
  have hE'M : E' ≤ M := le_sup_right.trans (IntermediateField.le_normalClosure _)
  have : FiniteDimensional F M := inferInstance
  have : IsGalois F M := ⟨⟩
  have := NumberField.of_module_finite F M
  obtain ⟨W, hW, hWx⟩ := exists_place_valuation_eq_of_le S hEM hMle w (hw ▸ hv)
  obtain ⟨W', hW', hW'x⟩ := exists_place_valuation_eq_of_le S hE'M hMle w' (hw' ▸ hv)
  have e1 := hWx ⟨_, hxE⟩
  have e2 := hW'x ⟨_, hxE'⟩
  have e3 := valuation_eq_of_isSInvariant S hMle hx (hEM hxE) W W' (by rw [hW, hW', hw, hw'])
    (by rw [hW, hw]; exact hv)
  have : WithZero.exp (-m) = WithZero.exp (-m') := by
    rw [← hwx, ← hw'x, ← e1, ← e2]
    exact e3
  simpa using this

noncomputable def ordAbove (v : HeightOneSpectrum (𝓞 F)) (x : (maxUnramifiedOutside F Ω S)ˣ) : ℤ :=
  (exists_isOrdAbove S v x).choose

theorem isOrdAbove_ordAbove (v : HeightOneSpectrum (𝓞 F)) (x : (maxUnramifiedOutside F Ω S)ˣ) :
    IsOrdAbove S v x (ordAbove S v x) :=
  (exists_isOrdAbove S v x).choose_spec

theorem ordAbove_eq_of_isOrdAbove {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {x : (maxUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x) {m : ℤ}
    (h : IsOrdAbove S v x m) : ordAbove S v x = m :=
  IsOrdAbove.unique S hv hx (isOrdAbove_ordAbove S v x) h

theorem valuation_eq_exp_ordAbove {x : (maxUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x)
    {E : IntermediateField F Ω} [NumberField E] (hEle : E ≤ maxUnramifiedOutside F Ω S)
    (hxE : ((x : maxUnramifiedOutside F Ω S) : Ω) ∈ E) (w : HeightOneSpectrum (𝓞 E))
    (hwS : underPlace (F := F) w ∉ S) :
    w.valuation E ⟨_, hxE⟩ = WithZero.exp (-ordAbove S (underPlace (F := F) w) x) := by
  have h0 : w.valuation E ⟨_, hxE⟩ ≠ 0 := by
    rw [Ne, map_eq_zero]
    intro h
    apply x.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  have hE := finiteDimensional_of_numberField E
  have hw : IsOrdAbove S (underPlace (F := F) w) x (-WithZero.log (w.valuation E ⟨_, hxE⟩)) :=
    ⟨E, hE, hEle, hxE, w, rfl, by rw [neg_neg, WithZero.exp_log h0]⟩
  rw [ordAbove_eq_of_isOrdAbove S hwS hx hw, neg_neg, WithZero.exp_log h0]

end Ord

section Div

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

omit [NumberField F] [IsGalois F Ω] in
theorem galUnitsHom_mul_inv_eq (σ : galUnramifiedOutside F Ω S) (x y : (maxUnramifiedOutside F Ω S)ˣ) :
    galUnitsHom F _ σ (x * y) * (x * y)⁻¹ = (galUnitsHom F _ σ x * x⁻¹) * (galUnitsHom F _ σ y * y⁻¹) := by
  rw [map_mul, mul_inv]
  ac_rfl

variable (Ω) in

def sInvariantSubgroup : Subgroup (maxUnramifiedOutside F Ω S)ˣ where
  carrier := {x | IsSInvariant S x}
  mul_mem' {x y} hx hy σ := by
    rw [galUnitsHom_mul_inv_eq]
    exact mul_mem (hx σ) (hy σ)
  one_mem' σ := by
    rw [map_one, inv_one, mul_one]
    exact one_mem _
  inv_mem' {x} hx σ := by
    have : galUnitsHom F _ σ x⁻¹ * x⁻¹⁻¹ = (galUnitsHom F _ σ x * x⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
    rw [this]
    exact inv_mem (hx σ)

omit [IsGalois F Ω] in
theorem mem_sInvariantSubgroup {x : (maxUnramifiedOutside F Ω S)ˣ} :
    x ∈ sInvariantSubgroup Ω S ↔ IsSInvariant S x :=
  Iff.rfl

omit [IsGalois F Ω] in

theorem map_algebraMap_mem_sInvariantSubgroup (a : Fˣ) :
    Units.map (algebraMap F (maxUnramifiedOutside F Ω S) : F →* _) a ∈ sInvariantSubgroup Ω S := by
  intro σ
  have : galUnitsHom F _ σ (Units.map (algebraMap F (maxUnramifiedOutside F Ω S) : F →* _) a) =
      Units.map (algebraMap F (maxUnramifiedOutside F Ω S) : F →* _) a :=
    Units.ext (σ.commutes _)
  rw [this, mul_inv_cancel]
  exact one_mem _

theorem exists_numberField_mem (x : (maxUnramifiedOutside F Ω S)ˣ) :
    ∃ E : IntermediateField F Ω, NumberField E ∧ E ≤ maxUnramifiedOutside F Ω S ∧
      ((x : maxUnramifiedOutside F Ω S) : Ω) ∈ E := by
  obtain ⟨E, hf, hu, hx⟩ :=
    (mem_maxUnramifiedOutside_iff S).1 (x : maxUnramifiedOutside F Ω S).2
  exact ⟨E, NumberField.of_module_finite F E, le_maxUnramifiedOutside S hu, hx⟩

theorem finite_ordAbove_ne_zero {x : (maxUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x) :
    {v : HeightOneSpectrum (𝓞 F) | v ∉ S ∧ ordAbove S v x ≠ 0}.Finite := by
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem S x
  have hx0 : (⟨_, hxE⟩ : E) ≠ 0 := by
    intro h
    apply x.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  refine ((finite_ordAt_ne_zero (Units.mk0 _ hx0)).image (underPlace (F := F))).subset ?_
  rintro v ⟨hv, hvo⟩
  obtain ⟨w, hw⟩ := exists_underPlace_eq (L := E) v
  refine ⟨w, ?_, hw⟩
  intro h0
  apply hvo
  have h1 := valuation_eq_exp_ordAbove S hx hEle hxE w (hw ▸ hv)
  have h2 := (ordAt_eq_zero_iff w _).1 h0
  rw [Units.val_mk0] at h2
  rw [h2, hw] at h1
  have := congrArg WithZero.log h1
  simpa using this.symm

theorem ordAbove_one {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ordAbove S v (1 : (maxUnramifiedOutside F Ω S)ˣ) = 0 := by
  refine ordAbove_eq_of_isOrdAbove S hv (one_mem (sInvariantSubgroup Ω S)) ?_
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem S (1 : (maxUnramifiedOutside F Ω S)ˣ)
  obtain ⟨w, hw⟩ := exists_underPlace_eq (L := E) v
  refine ⟨E, finiteDimensional_of_numberField E, hEle, hxE, w, hw, ?_⟩
  have : (⟨_, hxE⟩ : E) = 1 := Subtype.ext (by simp)
  rw [this, map_one, neg_zero, WithZero.exp_zero]

theorem ordAbove_mul {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {x y : (maxUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x) (hy : IsSInvariant S y) :
    ordAbove S v (x * y) = ordAbove S v x + ordAbove S v y := by
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem S x
  obtain ⟨E', hE', hE'le, hyE'⟩ := exists_numberField_mem S y
  have : FiniteDimensional F E := finiteDimensional_of_numberField E
  have : FiniteDimensional F E' := finiteDimensional_of_numberField E'
  have := NumberField.of_module_finite F ↥(E ⊔ E')
  have hle := sup_le hEle hE'le
  have hxE'' : ((x : maxUnramifiedOutside F Ω S) : Ω) ∈ E ⊔ E' :=
    le_sup_left (α := IntermediateField F Ω) hxE
  have hyE'' : ((y : maxUnramifiedOutside F Ω S) : Ω) ∈ E ⊔ E' :=
    le_sup_right (α := IntermediateField F Ω) hyE'
  have hxy : (((x * y : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) : Ω) ∈
      E ⊔ E' := by
    simp only [Units.val_mul, IntermediateField.coe_mul]
    exact mul_mem hxE'' hyE''
  obtain ⟨w, hw⟩ := exists_underPlace_eq (L := ↥(E ⊔ E')) v
  have hxy' : IsSInvariant S (x * y) := (mul_mem hx hy : x * y ∈ sInvariantSubgroup Ω S)
  have h1 := valuation_eq_exp_ordAbove S hxy' hle hxy w (hw ▸ hv)
  have h2 := valuation_eq_exp_ordAbove S hx hle hxE'' w (hw ▸ hv)
  have h3 := valuation_eq_exp_ordAbove S hy hle hyE'' w (hw ▸ hv)
  have hmul : (⟨_, hxy⟩ : ↥(E ⊔ E')) = ⟨_, hxE''⟩ * ⟨_, hyE''⟩ := Subtype.ext (by simp)
  rw [hmul, map_mul, h2, h3, hw, ← WithZero.exp_add] at h1
  have := congrArg WithZero.log h1
  simp only [WithZero.log_exp] at this
  omega

noncomputable def divAbove : Additive (sInvariantSubgroup Ω S) →+ sDivisor S where
  toFun x := Finsupp.ofSupportFinite
    (fun v => ordAbove S v.1 ((Additive.toMul x : sInvariantSubgroup Ω S) : (maxUnramifiedOutside F Ω S)ˣ))
    (((finite_ordAbove_ne_zero S (Additive.toMul x).2).preimage Subtype.val_injective.injOn).subset
      fun v hv => ⟨v.2, Function.mem_support.1 hv⟩)
  map_zero' := by
    ext v
    exact ordAbove_one S v.2
  map_add' x y := by
    ext v
    exact ordAbove_mul S v.2 (Additive.toMul x).2 (Additive.toMul y).2

theorem divAbove_apply (x : Additive (sInvariantSubgroup Ω S)) (v : {v // v ∉ S}) :
    divAbove S x v =
      ordAbove S v.1 ((Additive.toMul x : sInvariantSubgroup Ω S) : (maxUnramifiedOutside F Ω S)ˣ) :=
  rfl

end Div

section Descent

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem mem_sUnitsMax_of_divAbove_eq_zero {x : sInvariantSubgroup Ω S}
    (h : divAbove S (Additive.ofMul x) = 0) :
    (x : (maxUnramifiedOutside F Ω S)ˣ) ∈ sUnitsMax F Ω S := by
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem S (x : (maxUnramifiedOutside F Ω S)ˣ)
  have hx0 : (⟨_, hxE⟩ : E) ≠ 0 := by
    intro h
    apply (x : (maxUnramifiedOutside F Ω S)ˣ).ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  have hmem : Units.mk0 _ hx0 ∈ sUnitsOf S E := by
    rw [mem_sUnitsOf_iff_mem_unit]
    intro w hw
    have hwS : underPlace (F := F) w ∉ S := fun h => hw (mem_placesOver_iff.2 h)
    have h1 := valuation_eq_exp_ordAbove S x.2 hEle hxE w hwS
    have h2 : ordAbove S (underPlace (F := F) w) (x : (maxUnramifiedOutside F Ω S)ˣ) = 0 := by
      have := congrArg (fun D : sDivisor S => D ⟨_, hwS⟩) h
      simpa [divAbove_apply] using this
    rw [Units.val_mk0, h1, h2, neg_zero, WithZero.exp_zero]
  have hmap : Units.map (IntermediateField.inclusion hEle : E →* maxUnramifiedOutside F Ω S)
      (Units.mk0 _ hx0) = x := Units.ext rfl
  rw [← hmap]
  exact (map_inclusion_mem_sUnitsMax_iff F Ω S hEle).2 hmem

theorem divAbove_algebraMap (a : Fˣ) :
    divAbove S (Additive.ofMul ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩) =
      divS S (Additive.ofMul a) := by
  ext v
  rw [divAbove_apply, divS_apply]
  refine ordAbove_eq_of_isOrdAbove S v.2 (map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a) ?_
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem (Ω := Ω) S
    (Units.map (algebraMap F (maxUnramifiedOutside F Ω S) : F →* _) a)
  obtain ⟨w, hw⟩ := exists_underPlace_eq (L := E) v.1
  have hEf := finiteDimensional_of_numberField E
  refine ⟨E, hEf, hEle, hxE, w, hw, ?_⟩
  have hE : IsUnramifiedOutside S E := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hEle
  have : w.asIdeal.LiesOver v.1.asIdeal := liesOver_iff_eq_underPlace.2 hw.symm
  have : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := hE v.1 v.2 w.asIdeal inferInstance this
  have he : (⟨_, hxE⟩ : E) = algebraMap F E (a : F) := rfl
  rw [he, valuation_algebraMap_of_isUnramifiedAt v.1 w, valuation_eq_exp_neg_ordAt]
  rfl

end Descent

section Capitulation

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [IsSepClosed Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem exists_divAbove_eq {N : ℕ} (hN : N ≠ 0) (hNS : ∀ v ∉ S, ((N : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (D : sDivisor S) (a : Fˣ) (ha : divS S (Additive.ofMul a) = N • D) :
    ∃ x : sInvariantSubgroup Ω S, divAbove S (Additive.ofMul x) = D := by
  have : NeZero ((N : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap F Ω)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hN)⟩
  obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap F Ω (a : F)) N
  have hαint : IsIntegral F α := IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (hα ▸ isIntegral_algebraMap)
  let E : IntermediateField F Ω := IntermediateField.adjoin F {α}
  have : FiniteDimensional F E := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField E := NumberField.of_module_finite F E
  have hβ : IntermediateField.AdjoinSimple.gen F α ^ N = algebraMap F E (a : F) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hα]
    rfl
  have hdiv : ∀ v ∉ S, (N : ℤ) ∣ WithZero.log (v.valuation F (a : F)) := by
    intro v hv
    have := congrArg (fun D' : sDivisor S => D' ⟨v, hv⟩) ha
    simp only [divS_apply, toMul_ofMul, Finsupp.smul_apply, nsmul_eq_mul] at this
    rw [valuation_eq_exp_neg_ordAt, WithZero.log_exp, this]
    exact ⟨-D ⟨v, hv⟩, by ring⟩
  have hEu : IsUnramifiedOutside S E := fun v hv =>
    Global.Kummer.isUnramifiedIn_of_pow_eq a hβ (adjoin_gen_eq_top F α) v (hNS v hv) (hdiv v hv)
  have hEle : E ≤ maxUnramifiedOutside F Ω S := le_maxUnramifiedOutside S hEu
  have hαS : α ∈ maxUnramifiedOutside F Ω S := hEle (IntermediateField.mem_adjoin_simple_self F α)
  have hα0 : (⟨α, hαS⟩ : maxUnramifiedOutside F Ω S) ≠ 0 := by
    intro h
    have h' : α = 0 := congrArg Subtype.val h
    rw [h', zero_pow hN] at hα
    exact a.ne_zero ((map_eq_zero _).1 hα.symm)
  let x : (maxUnramifiedOutside F Ω S)ˣ := Units.mk0 _ hα0
  have hxN : x ^ N = Units.map (algebraMap F (maxUnramifiedOutside F Ω S) : F →* _) a :=
    Units.ext (Subtype.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow]
      exact hα))
  have hx : IsSInvariant S x := by
    intro σ
    apply mem_sUnitsOf_of_mem_rootsOfUnity hN
    rw [mem_rootsOfUnity, mul_pow, ← map_pow, hxN, inv_pow, hxN]
    have : galUnitsHom F _ σ (Units.map (algebraMap F (maxUnramifiedOutside F Ω S) : F →* _) a) =
        Units.map (algebraMap F (maxUnramifiedOutside F Ω S) : F →* _) a :=
      Units.ext (σ.commutes _)
    rw [this, mul_inv_cancel]
  refine ⟨⟨x, hx⟩, ?_⟩
  ext v
  rw [divAbove_apply]
  obtain ⟨w, hw⟩ := exists_underPlace_eq (L := E) v.1
  have hαE : ((x : maxUnramifiedOutside F Ω S) : Ω) ∈ E := IntermediateField.mem_adjoin_simple_self F α
  have h1 := valuation_eq_exp_ordAbove S hx hEle hαE w (hw ▸ v.2)
  have : w.asIdeal.LiesOver v.1.asIdeal := liesOver_iff_eq_underPlace.2 hw.symm
  have : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := hEu v.1 v.2 w.asIdeal inferInstance this
  have h2 := valuation_algebraMap_of_isUnramifiedAt v.1 w (a : F)
  rw [← hβ, map_pow, valuation_eq_exp_neg_ordAt] at h2
  have hgen : IntermediateField.AdjoinSimple.gen F α = ⟨_, hαE⟩ := rfl
  rw [hgen, h1, hw, ← WithZero.exp_nsmul] at h2
  have h3 := congrArg WithZero.log h2
  simp only [WithZero.log_exp, smul_neg, nsmul_eq_mul] at h3
  have h4 := congrArg (fun D' : sDivisor S => D' v) ha
  simp only [divS_apply, toMul_ofMul, Finsupp.smul_apply, nsmul_eq_mul] at h4
  rw [h4] at h3
  have hN' : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have := mul_left_cancel₀ hN' (neg_injective h3)
  exact this

end Capitulation

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

universe u

section Quot

variable (F Ω : Type u) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

def sUnitsSubmodule : Submodule (ULift.{u} ℤ) (galUnits.{u} F (maxUnramifiedOutside F Ω S)) where
  carrier := {z | Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) z ∈ sUnitsMax F Ω S}
  add_mem' {a b} ha hb := by
    change Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) a *
      Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) b ∈ sUnitsMax F Ω S
    exact mul_mem ha hb
  zero_mem' := by
    change (1 : (maxUnramifiedOutside F Ω S)ˣ) ∈ sUnitsMax F Ω S
    exact one_mem _
  smul_mem' r z hz := by
    change Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) (r.down • z) ∈ sUnitsMax F Ω S
    rw [toMul_zsmul]
    exact zpow_mem hz _

theorem sUnitsSubmodule_le_comap (σ : galUnramifiedOutside F Ω S) :
    sUnitsSubmodule F Ω S ≤ (sUnitsSubmodule F Ω S).comap
      ((galUnits.{u} F (maxUnramifiedOutside F Ω S)).ρ σ) :=
  fun _ hz => galUnitsHom_mem_sUnitsOf (S := S) σ hz

noncomputable abbrev galUnitsModSUnits : Rep.{u} (ULift.{u} ℤ) (galUnramifiedOutside F Ω S) :=
  (galUnits.{u} F (maxUnramifiedOutside F Ω S)).quotient (sUnitsSubmodule F Ω S)
    (sUnitsSubmodule_le_comap F Ω S)

noncomputable def sUnitsQuotSequence :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) (galUnramifiedOutside F Ω S)) :=
  ShortComplex.mk (sUnitsToUnits S (maxUnramifiedOutside F Ω S))
    (Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero _).2
        (show Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) _ ∈ sUnitsMax F Ω S from
          (Additive.toMul x).2))

theorem sUnitsQuotSequence_shortExact : (sUnitsQuotSequence F Ω S).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro x hx
    exact ⟨Additive.ofMul ⟨Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) x,
      (Submodule.Quotient.mk_eq_zero _).1 hx⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 (sUnitsToUnits_injective S _)
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

variable [IsGalois F Ω]

instance isDiscreteRep_sUnitsQuotSequence_X₁ : IsDiscreteRep (sUnitsQuotSequence F Ω S).X₁ :=
  inferInstanceAs (IsDiscreteRep (galSUnits S (maxUnramifiedOutside F Ω S)))

instance isDiscreteRep_sUnitsQuotSequence_X₂ : IsDiscreteRep (sUnitsQuotSequence F Ω S).X₂ :=
  inferInstanceAs (IsDiscreteRep (galUnits.{u} F (maxUnramifiedOutside F Ω S)))

instance isDiscreteRep_sUnitsQuotSequence_X₃ : IsDiscreteRep (sUnitsQuotSequence F Ω S).X₃ :=
  isDiscreteRep_quotient _ _ _

end Quot

section Phi

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

omit [IsGalois F Ω] in

theorem mk_mem_invariants_iff (x : (maxUnramifiedOutside F Ω S)ˣ) :
    (Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)).hom
        (Additive.ofMul x : Additive (maxUnramifiedOutside F Ω S)ˣ) ∈
      (galUnitsModSUnits F Ω S).ρ.invariants ↔ IsSInvariant S x :=
  forall_congr' fun _ => (Submodule.Quotient.eq _).trans Iff.rfl

noncomputable def sInvariantToInvariants :
    Additive (sInvariantSubgroup Ω S) →+ (galUnitsModSUnits F Ω S).ρ.invariants where
  toFun x := ⟨(Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)).hom
      (Additive.ofMul (Additive.toMul x : sInvariantSubgroup Ω S).1 :
        Additive (maxUnramifiedOutside F Ω S)ˣ),
    (mk_mem_invariants_iff S _).2 (Additive.toMul x).2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsGalois F Ω] in
theorem sInvariantToInvariants_surjective : Function.Surjective (sInvariantToInvariants (Ω := Ω) S) := by
  rintro ⟨q, hq⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Additive.ofMul ⟨Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) z,
    (mk_mem_invariants_iff S _).1 hq⟩, rfl⟩

omit [IsGalois F Ω] in
theorem sInvariantToInvariants_eq_zero_iff (x : Additive (sInvariantSubgroup Ω S)) :
    sInvariantToInvariants S x = 0 ↔
      ((Additive.toMul x : sInvariantSubgroup Ω S) : (maxUnramifiedOutside F Ω S)ˣ) ∈ sUnitsMax F Ω S := by
  rw [Subtype.ext_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem divAbove_eq_zero_of_mem {x : sInvariantSubgroup Ω S}
    (hx : (x : (maxUnramifiedOutside F Ω S)ˣ) ∈ sUnitsMax F Ω S) :
    divAbove S (Additive.ofMul x) = 0 := by
  ext v
  rw [divAbove_apply, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨L, hf, hL, y, hy, hyx⟩ := exists_of_mem_sUnitsMax F Ω S hx
  have := NumberField.of_module_finite F L
  have hyL : (((x : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) : Ω) ∈ L := by
    rw [← hyx]
    exact (y : L).2
  obtain ⟨w, hw⟩ := exists_underPlace_eq (L := L) v.1
  have h1 := valuation_eq_exp_ordAbove S x.2 hL hyL w (hw ▸ v.2)
  have hyy : (⟨_, hyL⟩ : L) = (y : L) :=
    Subtype.ext (congrArg (fun u : (maxUnramifiedOutside F Ω S)ˣ =>
      ((u : maxUnramifiedOutside F Ω S) : Ω)) hyx).symm
  have h2 := (mem_sUnitsOf_iff_mem_unit S).1 hy w (fun h => (hw ▸ v.2) (mem_placesOver_iff.1 h))
  rw [hyy, h2, hw] at h1
  have := congrArg WithZero.log h1
  simp only [WithZero.log_one, WithZero.log_exp] at this
  simp only [toMul_ofMul]
  omega

noncomputable def invariantsToSPic : (galUnitsModSUnits F Ω S).ρ.invariants →+ sPic S :=
  (QuotientAddGroup.lift (sInvariantToInvariants (Ω := Ω) S).ker ((sPicMk S).comp (divAbove S))
    (fun x hx => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      have := divAbove_eq_zero_of_mem S
        ((sInvariantToInvariants_eq_zero_iff S x).1 (AddMonoidHom.mem_ker.1 hx))
      rw [ofMul_toMul] at this
      rw [this, map_zero])).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (sInvariantToInvariants_surjective (Ω := Ω) S)).symm.toAddMonoidHom

theorem invariantsToSPic_apply (x : Additive (sInvariantSubgroup Ω S)) :
    invariantsToSPic S (sInvariantToInvariants S x) = sPicMk S (divAbove S x) := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (sInvariantToInvariants_surjective (Ω := Ω) S)).symm (sInvariantToInvariants S x) =
      (x : Additive (sInvariantSubgroup Ω S) ⧸ (sInvariantToInvariants (Ω := Ω) S).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  simp only [invariantsToSPic, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

noncomputable def invariantsToH1 :
    (galUnitsModSUnits F Ω S).ρ.invariants →+ cohomology (galSUnits S (maxUnramifiedOutside F Ω S)) 1 :=
  (δ (sUnitsQuotSequence_shortExact F Ω S) 0 1 rfl).hom.toAddMonoidHom.comp
    (H0Iso (sUnitsQuotSequence F Ω S).X₃).inv.hom.toAddMonoidHom

theorem invariantsToH1_surjective : Function.Surjective (invariantsToH1 (Ω := Ω) S) := fun x =>
  exists_δ_H0Iso_inv_eq (sUnitsQuotSequence_shortExact F Ω S)
    (subsingleton_cohomology_one_galUnits (K := F) (L := maxUnramifiedOutside F Ω S)) x

theorem invariantsToH1_eq_zero_iff (q : (galUnitsModSUnits F Ω S).ρ.invariants) :
    invariantsToH1 S q = 0 ↔ ∃ a : Fˣ,
      sInvariantToInvariants S (Additive.ofMul ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩) = q := by
  refine (δ_H0Iso_inv_eq_zero_iff (sUnitsQuotSequence_shortExact F Ω S) q).trans ?_
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨a, rfl⟩ := unitsToInvariants_surjective F (maxUnramifiedOutside F Ω S) w
    exact ⟨Additive.toMul a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨unitsToInvariants F (maxUnramifiedOutside F Ω S) (Additive.ofMul a), rfl⟩

end Phi

section H1

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

noncomputable def h1SUnitsToSPic :
    cohomology (galSUnits S (maxUnramifiedOutside F Ω S)) 1 →+ sPic S :=
  (QuotientAddGroup.lift (invariantsToH1 (Ω := Ω) S).ker (invariantsToSPic S) (fun q hq => by
      obtain ⟨a, rfl⟩ := (invariantsToH1_eq_zero_iff S q).1 (AddMonoidHom.mem_ker.1 hq)
      rw [AddMonoidHom.mem_ker, invariantsToSPic_apply, divAbove_algebraMap]
      exact (sPicMk_eq_zero_iff S _).2 ⟨a, rfl⟩)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (invariantsToH1_surjective (Ω := Ω) S)).symm.toAddMonoidHom

theorem h1SUnitsToSPic_invariantsToH1 (q : (galUnitsModSUnits F Ω S).ρ.invariants) :
    h1SUnitsToSPic S (invariantsToH1 S q) = invariantsToSPic S q := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (invariantsToH1_surjective (Ω := Ω) S)).symm (invariantsToH1 S q) =
      (q : (galUnitsModSUnits F Ω S).ρ.invariants ⧸ (invariantsToH1 (Ω := Ω) S).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  simp only [h1SUnitsToSPic, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

theorem h1SUnitsToSPic_apply (x : Additive (sInvariantSubgroup Ω S)) :
    h1SUnitsToSPic S (invariantsToH1 S (sInvariantToInvariants S x)) = sPicMk S (divAbove S x) := by
  rw [h1SUnitsToSPic_invariantsToH1, invariantsToSPic_apply]

theorem h1SUnitsToSPic_injective : Function.Injective (h1SUnitsToSPic (Ω := Ω) S) := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  obtain ⟨q, rfl⟩ := invariantsToH1_surjective (Ω := Ω) S h
  obtain ⟨x, rfl⟩ := sInvariantToInvariants_surjective (Ω := Ω) S q
  rw [h1SUnitsToSPic_apply, sPicMk_eq_zero_iff] at hh
  obtain ⟨a, ha⟩ := hh
  let y : Additive (sInvariantSubgroup Ω S) :=
    Additive.ofMul ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩
  have hxy : divAbove S (x - y) = 0 := by
    rw [map_sub, divAbove_algebraMap, ha, sub_self]
  have hmem := mem_sUnitsMax_of_divAbove_eq_zero S (x := Additive.toMul (x - y)) hxy
  have h0 : sInvariantToInvariants S (x - y) = 0 := (sInvariantToInvariants_eq_zero_iff S _).2 hmem
  rw [map_sub, sub_eq_zero] at h0
  rw [h0]
  exact (invariantsToH1_eq_zero_iff S _).2 ⟨a, rfl⟩

variable [IsSepClosed Ω]



end H1

section KummerPic

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [IsSepClosed Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n]
  (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal)

instance isDiscreteRep_sUnitsKummerSequence_X₁ :
    IsDiscreteRep (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₁ :=
  inferInstanceAs (IsDiscreteRep (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n))

instance isDiscreteRep_sUnitsKummerSequence_X₂ :
    IsDiscreteRep (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₂ :=
  inferInstanceAs (IsDiscreteRep (galSUnits S (maxUnramifiedOutside F Ω S)))

instance isDiscreteRep_sUnitsKummerSequence_X₃ :
    IsDiscreteRep (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃ :=
  inferInstanceAs (IsDiscreteRep (galSUnits S (maxUnramifiedOutside F Ω S)))

omit [IsGalois F Ω] [IsSepClosed Ω] [NeZero n] in
theorem invariantsFunctor_map_nsmul_apply
    (w : (galSUnits S (maxUnramifiedOutside F Ω S)).ρ.invariants) :
    ((Rep.invariantsFunctor (ULift.{u} ℤ) (galUnramifiedOutside F Ω S)).map
      (n • 𝟙 (galSUnits S (maxUnramifiedOutside F Ω S)))).hom w = n • w := by
  apply Subtype.ext
  change (n • 𝟙 (galSUnits S (maxUnramifiedOutside F Ω S))).hom w.1 = _
  rw [nsmul_id_hom_apply]
  rfl

include hnS

noncomputable def kummerSUnitsHom :
    Additive (S.unit F) →+ cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1 :=
  ((δ (sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS) 0 1 rfl).hom.toAddMonoidHom.comp
    (H0Iso (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃).inv.hom.toAddMonoidHom).comp
    (sUnitsToInvariants S (maxUnramifiedOutside F Ω S))

noncomputable def kummerPicHom :
    cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1 →+ sPic S :=
  (h1SUnitsToSPic (Ω := Ω) S).comp
    (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).f 1).hom.toAddMonoidHom

theorem kummerSUnitsHom_eq_zero_iff (a : Additive (S.unit F)) :
    kummerSUnitsHom (Ω := Ω) S n hnS a = 0 ↔ ∃ b, n • b = a := by
  refine (δ_H0Iso_inv_eq_zero_iff (sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS) _).trans ?_
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, rfl⟩ := sUnitsToInvariants_surjective S (maxUnramifiedOutside F Ω S) w
    refine ⟨b, sUnitsToInvariants_injective S (maxUnramifiedOutside F Ω S) ?_⟩
    rw [map_nsmul]
    refine Eq.trans ?_ hw
    exact (invariantsFunctor_map_nsmul_apply (Ω := Ω) S n _).symm
  · rintro ⟨b, rfl⟩
    refine ⟨sUnitsToInvariants S (maxUnramifiedOutside F Ω S) b, ?_⟩
    exact (invariantsFunctor_map_nsmul_apply (Ω := Ω) S n _).trans (map_nsmul _ _ _).symm

theorem kummerPicHom_eq_zero_iff (y : cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1) :
    kummerPicHom (Ω := Ω) S n y = 0 ↔ ∃ a, kummerSUnitsHom (Ω := Ω) S n hnS a = y := by
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  constructor
  · intro hy
    have h0 : (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).f 1).hom y = 0 :=
      h1SUnitsToSPic_injective S (hy.trans (map_zero _).symm)
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hK 0 1 rfl) y h0
    obtain ⟨b, hb⟩ := sUnitsToInvariants_surjective S (maxUnramifiedOutside F Ω S)
      ((H0Iso (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃).hom.hom z)
    refine ⟨b, ?_⟩
    change (δ hK 0 1 rfl).hom ((H0Iso _).inv.hom (sUnitsToInvariants S _ b)) = y
    rw [hb, H0Iso_inv_hom_apply]
    exact hz
  · rintro ⟨a, rfl⟩
    have h0 := congrArg (fun φ => φ.hom ((H0Iso (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃).inv.hom
      (sUnitsToInvariants S (maxUnramifiedOutside F Ω S) a))) (δ_comp hK 0 1 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h0
    exact (congrArg (h1SUnitsToSPic (Ω := Ω) S) h0).trans (map_zero _)


end KummerPic

section BaseChange

variable {F L E : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field E]
  [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem isIntegral_integer_iff_placesOver (x : E) :
    IsIntegral (S.integer F) x ↔
      IsIntegral ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).integer L) x := by
  constructor
  · intro hx
    let f : S.integer F →+* (placesOver S : Set (HeightOneSpectrum (𝓞 L))).integer L :=
      ((algebraMap F L).comp (S.integer F).val.toRingHom).codRestrict _
        fun r w hw => valuation_algebraMap_integer_le_one S hw r
    exact IsIntegral.map_of_comp_eq f (RingHom.id E) (by
      ext r
      exact (IsScalarTower.algebraMap_apply F L E (r : F)).symm) hx
  · intro hx
    let C := integralClosure (S.integer F) E
    let f : (placesOver S : Set (HeightOneSpectrum (𝓞 L))).integer L →+* C :=
      ((algebraMap L E).comp
        ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).integer L).val.toRingHom).codRestrict
        C.toSubring fun c => by
          have hc : IsIntegral (S.integer F) (c : L) :=
            isIntegral_integer_of_valuation_le_one S fun w hw => c.2 w hw
          exact hc.map ((IsScalarTower.toAlgHom F L E).restrictScalars (S.integer F))
    have hxC : IsIntegral C (RingHom.id E x) := IsIntegral.map_of_comp_eq f (RingHom.id E)
      (by ext c; rfl) hx
    have hmem : x ∈ integralClosure C E := hxC
    rw [integralClosure_idem, Algebra.mem_bot] at hmem
    obtain ⟨c, rfl⟩ := hmem
    exact c.2

theorem sUnitsOf_placesOver_eq :
    sUnitsOf (placesOver S : Set (HeightOneSpectrum (𝓞 L))) E = sUnitsOf S E := by
  ext x
  rw [mem_sUnitsOf, mem_sUnitsOf, isIntegral_integer_iff_placesOver (L := L) S,
    isIntegral_integer_iff_placesOver (L := L) S]

end BaseChange

end GroundTheory.ProfCoh
end
