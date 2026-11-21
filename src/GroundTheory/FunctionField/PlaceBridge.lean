import Mathlib
import GroundTheory.FunctionField.PlaceBasic

section
namespace GroundTheory.FunctionField

namespace Place

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']

def LiesOver (w : Place k K') (v : Place k K) : Prop :=
  w.ring.comap (algebraMap K K') = v.ring

omit [IsScalarTower k K K'] in
theorem LiesOver.mem_iff {w : Place k K'} {v : Place k K} (h : w.LiesOver v) {x : K} :
    algebraMap K K' x ∈ w.ring ↔ x ∈ v.ring := by
  rw [← ValuationSubring.mem_comap, h]

omit [IsScalarTower k K K'] in
theorem LiesOver.algebraMap_mem {w : Place k K'} {v : Place k K} (h : w.LiesOver v) {x : K}
    (hx : x ∈ v.ring) : algebraMap K K' x ∈ w.ring :=
  h.mem_iff.2 hx

def comap [Algebra.IsAlgebraic K K'] (w : Place k K') : Place k K where
  ring := w.ring.comap (algebraMap K K')
  ne_top := by
    intro htop
    apply w.ne_top
    have hK : ∀ a : K, algebraMap K K' a ∈ w.ring := fun a =>
      ValuationSubring.mem_comap.1 (htop ▸ ValuationSubring.mem_top a)
    let : Algebra K w.ring := (RingHom.codRestrict (algebraMap K K') w.ring hK).toAlgebra
    have : IsScalarTower K w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine eq_top_iff.2 fun z _ => ?_
    have hz : IsIntegral w.ring z := (Algebra.IsIntegral.isIntegral (R := K) z).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hz
    rw [← hy]
    exact y.2
  algebraMap_mem c := by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact w.algebraMap_mem c

theorem liesOver_comap [Algebra.IsAlgebraic K K'] (w : Place k K') : w.LiesOver (w.comap (K := K)) :=
  rfl

theorem liesOver_iff_comap_eq [Algebra.IsAlgebraic K K'] {w : Place k K'} {v : Place k K} :
    w.LiesOver v ↔ w.comap = v :=
  ⟨fun h => Place.ext h, fun h => congrArg Place.ring h⟩

theorem liesOver_of_le [IsFunctionField k K] [Algebra.IsAlgebraic K K'] {w : Place k K'}
    {v : Place k K} (h : ∀ x ∈ v.ring, algebraMap K K' x ∈ w.ring) : w.LiesOver v := by
  have := Place.eq_of_le (v := v) (w := w.comap) fun x hx => ValuationSubring.mem_comap.2 (h x hx)
  exact liesOver_iff_comap_eq.2 this.symm

theorem exists_liesOver (v : Place k K) : ∃ w : Place k K', w.LiesOver v := by
  let f : v.ring →+* K' := (algebraMap K K').comp v.ring.subtype
  have hf : Function.Injective f := (algebraMap K K').injective.comp Subtype.val_injective
  let g : v.ring →+* f.range := f.rangeRestrict
  have hg : Function.Bijective g :=
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let I : Ideal f.range := (IsLocalRing.maximalIdeal v.ring).map g
  have hI : I ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal v.ring).ne_top ((Ideal.map_eq_top_of_bijective g hg).1 h)
  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hmem : ∀ a : v.ring, a ∈ IsLocalRing.maximalIdeal v.ring → f a ∈ B.nonunits := fun a ha =>
    hIB ⟨g a, Ideal.mem_map_of_mem g ha, rfl⟩
  have hAB' : ∀ a : v.ring, f a ∈ B := fun a => hAB (RingHom.mem_range_self f a)
  obtain ⟨x, hx0, hx⟩ := v.exists_valuation_lt_one_ne_zero
  have hxO : x ∈ v.ring := (v.ring.valuation_le_one_iff x).1 hx.le
  have hfx : algebraMap K K' x ∈ B.nonunits := hmem ⟨x, hxO⟩ ((v.ring.valuation_lt_one_iff _).2 hx)
  refine ⟨⟨B, ?_, ?_⟩, ?_⟩
  · intro htop
    rcases B.mem_nonunits_iff_or.1 hfx with h | h
    · exact hx0 ((algebraMap K K').injective (h.trans (map_zero _).symm))
    · exact h (htop ▸ ValuationSubring.mem_top _)
  · intro c
    rw [IsScalarTower.algebraMap_apply k K K']
    exact hAB' ⟨_, v.algebraMap_mem c⟩
  · apply le_antisymm
    · intro y hy
      rw [ValuationSubring.mem_comap] at hy
      by_contra hyv
      have hy0 : y ≠ 0 := fun h => hyv (h ▸ v.ring.zero_mem)
      have hinv : y⁻¹ ∈ v.ring.nonunits := v.ring.inv_mem_nonunits_iff.2 (Or.inr hyv)
      obtain ⟨hr, hrm⟩ := v.ring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hinv
      have h1 : algebraMap K K' y⁻¹ ∈ B.nonunits := hmem _ hrm
      rw [map_inv₀] at h1
      rcases B.inv_mem_nonunits_iff.1 h1 with h | h
      · exact hy0 ((algebraMap K K').injective (h.trans (map_zero _).symm))
      · exact h hy
    · intro y hy
      exact ValuationSubring.mem_comap.2 (hAB' ⟨y, hy⟩)

abbrev LiesOver.algebra {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    Algebra v.ring w.ring :=
  (RingHom.codRestrict ((algebraMap K K').comp v.ring.subtype) w.ring
    fun a => h.algebraMap_mem a.2).toAlgebra

omit [IsScalarTower k K K'] in
theorem LiesOver.isLocalHom {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsLocalHom (algebraMap v.ring w.ring) := by
  let := h.algebra
  refine ⟨fun a ha => ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff] at ha ⊢
  have hw : w.ring.valuation (algebraMap K K' (a : K)) = 1 := ha
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hw
    exact zero_ne_one hw
  have hinv : (a : K)⁻¹ ∈ v.ring := by
    rw [← h.mem_iff, ← w.ring.valuation_le_one_iff, map_inv₀, map_inv₀, hw, inv_one]
  have h1 := (v.ring.valuation_le_one_iff _).2 hinv
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))] at h1
  exact le_antisymm (v.ring.valuation_le_one a) h1

theorem LiesOver.isScalarTower {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsScalarTower k v.ring w.ring := by
  let := h.algebra
  exact IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (IsScalarTower.algebraMap_apply k K K' c)

theorem _root_.GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional [IsFunctionField k K]
    [FiniteDimensional K K'] : IsFunctionField k K' := by
  obtain ⟨y, hy, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hb := (isTranscendenceBasis_singleton hy hfin).algebraMap_comp (A := K')
  have hr : Set.range (⇑(algebraMap K K') ∘ ((↑) : ({y} : Set K) → K)) = {algebraMap K K' y} := by
    rw [Set.range_comp, Subtype.range_coe, Set.image_singleton]
  have halg := hb.isAlgebraic_field
  rw [hr] at halg
  have := essFiniteType (k := k) (K := K)
  have : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {algebraMap K K' y}) K' :=
    Algebra.EssFiniteType.of_comp k _ K'
  exact ⟨⟨algebraMap K K' y,
    (algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set K))).1 hb.1,
    Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩

section Degree

variable [IsFunctionField k K]

noncomputable def uniformizer (v : Place k K) : K :=
  Classical.choose v.exists_ord_eq_one

theorem ord_uniformizer (v : Place k K) : v.ord v.uniformizer = 1 :=
  Classical.choose_spec v.exists_ord_eq_one

theorem uniformizer_ne_zero (v : Place k K) : v.uniformizer ≠ 0 := fun h => by
  have h1 := v.ord_uniformizer
  rw [h, ord_zero] at h1
  exact zero_ne_one h1

variable [IsFunctionField k K']

noncomputable def ramificationIdx (w : Place k K') (v : Place k K) : ℕ :=
  (w.ord (algebraMap K K' v.uniformizer)).toNat

noncomputable def inertiaDeg (w : Place k K') (v : Place k K) : ℕ :=
  w.deg / v.deg

omit [IsFunctionField k K] [IsFunctionField k K'] [IsScalarTower k K K'] in
theorem LiesOver.isTorsionFree {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    Module.IsTorsionFree v.ring w.ring := by
  let := h.algebra
  exact Module.isTorsionFree_iff_algebraMap_injective.2 fun a b hab =>
    Subtype.ext ((algebraMap K K').injective (congrArg Subtype.val hab))

omit [IsScalarTower k K K'] in

theorem LiesOver.valuation_algebraMap {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    letI := h.algebra
    v.valuation x ^ (IsLocalRing.maximalIdeal v.ring).ramificationIdx'
        (IsLocalRing.maximalIdeal w.ring) =
      w.valuation (algebraMap K K' x) := by
  let := h.algebra
  have := h.isLocalHom
  have := h.isTorsionFree
  let : Algebra v.ring K' := ((algebraMap K K').comp (algebraMap v.ring K)).toAlgebra
  have : IsScalarTower v.ring K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower v.ring w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : w.heightOneSpectrum.asIdeal.LiesOver v.heightOneSpectrum.asIdeal :=
    inferInstanceAs ((IsLocalRing.maximalIdeal w.ring).LiesOver (IsLocalRing.maximalIdeal v.ring))
  exact IsDedekindDomain.HeightOneSpectrum.valuation_liesOver K' v.heightOneSpectrum
    w.heightOneSpectrum x

theorem LiesOver.ramificationIdx'_eq {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    (IsLocalRing.maximalIdeal v.ring).ramificationIdx' (IsLocalRing.maximalIdeal w.ring) =
      w.ramificationIdx v := by
  let := h.algebra
  have h1 := h.valuation_algebraMap v.uniformizer
  have hπ : algebraMap K K' v.uniformizer ≠ 0 := (map_ne_zero _).2 v.uniformizer_ne_zero
  rw [v.valuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer,
    w.valuation_eq_exp_neg_ord hπ, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h1
  rw [ramificationIdx]
  omega

theorem LiesOver.ord_algebraMap {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    w.ord (algebraMap K K' x) = w.ramificationIdx v * v.ord x := by
  by_cases hx : x = 0
  · simp [hx]
  let := h.algebra
  have h1 := h.valuation_algebraMap x
  have hx' : algebraMap K K' x ≠ 0 := (map_ne_zero _).2 hx
  rw [v.valuation_eq_exp_neg_ord hx, w.valuation_eq_exp_neg_ord hx', ← WithZero.exp_nsmul,
    WithZero.exp_inj, nsmul_eq_mul, h.ramificationIdx'_eq] at h1
  linarith

omit [IsFunctionField k K'] in

theorem LiesOver.deg_mul_finrank {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    v.deg * Module.finrank v.ResidueField w.ResidueField = w.deg := by
  let := h.algebra
  have := h.isLocalHom
  have := h.isScalarTower
  exact Module.finrank_mul_finrank k v.ResidueField w.ResidueField

omit [IsFunctionField k K'] in

theorem LiesOver.finrank_residueField {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    Module.finrank v.ResidueField w.ResidueField = w.inertiaDeg v := by
  let := h.algebra
  have := h.isLocalHom
  rw [inertiaDeg, ← h.deg_mul_finrank, Nat.mul_div_cancel_left _ v.deg_pos]

theorem LiesOver.deg_eq {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    w.deg = w.inertiaDeg v * v.deg := by
  let := h.algebra
  have := h.isLocalHom
  rw [← h.finrank_residueField, ← h.deg_mul_finrank, mul_comm]

end Degree

end Place

end GroundTheory.FunctionField
end

section
namespace GroundTheory.FunctionField

open IsDedekindDomain IsLocalRing

open scoped WithZero

theorem valuation_eq_of_isEquiv {F : Type*} [Field F] {v₁ v₂ : Valuation F ℤᵐ⁰}
    (h : v₁.IsEquiv v₂) (h₁ : Function.Surjective v₁) (h₂ : Function.Surjective v₂) : v₁ = v₂ := by
  have disc : ∀ y : ℤᵐ⁰, y < 1 → y ≤ WithZero.exp (-1) := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact zero_le
    · rw [← WithZero.exp_log hy0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
      rw [← WithZero.exp_log hy0, WithZero.exp_le_exp]
      omega
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  obtain ⟨π, hπ⟩ := h₁ (WithZero.exp (-1))
  obtain ⟨π', hπ'⟩ := h₂ (WithZero.exp (-1))
  have hπ2 : v₂ π = WithZero.exp (-1) := by
    have h2lt : v₂ π < 1 := h.lt_one_iff_lt_one.1 (hπ ▸ hlt)
    have h1 : v₁ π' < 1 := h.lt_one_iff_lt_one.2 (hπ' ▸ hlt)
    have h3 : v₂ π' ≤ v₂ π := h.le_iff_le.1 (hπ ▸ disc _ h1)
    exact le_antisymm (disc _ h2lt) (hπ' ▸ h3)
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx1 : v₁ x = WithZero.exp (WithZero.log (v₁ x)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm
  have hy : v₁ (x * π ^ (WithZero.log (v₁ x))) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hx1, WithZero.log_exp, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero]
    congr 1
    simp
  have hy2 := h.eq_one_iff_eq_one.1 hy
  rw [map_mul, map_zpow₀, hπ2, ← WithZero.exp_zsmul] at hy2
  rw [hx1, eq_inv_of_mul_eq_one_left hy2, ← WithZero.exp_neg]
  congr 1
  simp

namespace Place

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']

noncomputable abbrev algebraExt (v : Place k K) : Algebra v.ring K' :=
  ((algebraMap K K').comp (algebraMap v.ring K)).toAlgebra

attribute [local instance low] algebraExt

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isScalarTower_ext (v : Place k K) : IsScalarTower v.ring K K' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] isScalarTower_ext

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isTorsionFree_ext (v : Place k K) : Module.IsTorsionFree v.ring K' :=
  Module.isTorsionFree_iff_algebraMap_injective.2
    ((algebraMap K K').injective.comp (IsFractionRing.injective v.ring K))

attribute [local instance] isTorsionFree_ext

section Closure

variable [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] (v : Place k K)

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isDedekindDomain_closure : IsDedekindDomain (integralClosure v.ring K') :=
  IsIntegralClosure.isDedekindDomain v.ring K K' _

omit [Algebra k K'] [IsScalarTower k K K'] [IsFunctionField k K] [Algebra.IsSeparable K K'] in
theorem isFractionRing_closure : IsFractionRing (integralClosure v.ring K') K' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.ring) K K'

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem finite_closure : Module.Finite v.ring (integralClosure v.ring K') :=
  IsIntegralClosure.finite v.ring K K' _

omit [Algebra k K'] [IsScalarTower k K K'] [IsFunctionField k K] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] in
theorem isTorsionFree_closure : Module.IsTorsionFree v.ring (integralClosure v.ring K') :=
  IsIntegralClosure.isTorsionFree v.ring K'

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem finrank_closure :
    Module.finrank v.ring (integralClosure v.ring K') = Module.finrank K K' :=
  IsIntegralClosure.rank v.ring K K' _

attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure

end Closure

section Correspondence

variable [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] (v : Place k K)

attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure

omit [Algebra k K'] [IsScalarTower k K K'] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] in
theorem ne_bot_of_mem_primesOver {q : Ideal (integralClosure v.ring K')}
    (hq : q ∈ (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) : q ≠ ⊥ := by
  intro h
  have hinj : Function.Injective (algebraMap v.ring (integralClosure v.ring K')) :=
    Module.isTorsionFree_iff_algebraMap_injective.1 (isTorsionFree_closure v)
  apply IsDiscreteValuationRing.not_a_field v.ring
  rw [hq.2.over, h]
  exact Ideal.comap_bot_of_injective _ hinj

noncomputable def primeHS (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    HeightOneSpectrum (integralClosure v.ring K') :=
  ⟨q.1, q.2.1, v.ne_bot_of_mem_primesOver q.2⟩

omit [IsScalarTower k K K'] [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] in

theorem mem_of_isIntegral_of_liesOver {w : Place k K'} (h : w.LiesOver v) {x : K'}
    (hx : IsIntegral v.ring x) : x ∈ w.ring := by
  let := h.algebra
  have : IsScalarTower v.ring w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := w.ring))
  rw [← hy]
  exact y.2

noncomputable abbrev placeOfPrime (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    Place k K' where
  ring := HeightOneSpectrum.valuationSubringAtPrime K' (v.primeHS q)
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := (v.primeHS q).valuation_exists_uniformizer K'
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
    have hmem : π⁻¹ ∈ ((v.primeHS q).valuation K').valuationSubring :=
      hle (htop ▸ ValuationSubring.mem_top _)
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    have hc : IsIntegral v.ring (algebraMap k K' c) := by
      rw [IsScalarTower.algebraMap_apply k K K']
      exact isIntegral_algebraMap (R := v.ring) (x := (⟨_, v.algebraMap_mem c⟩ : v.ring))
    exact Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K' _
      (v.primeHS q).asIdeal.primeCompl_le_nonZeroDivisors)
      (⟨algebraMap k K' c, hc⟩ : integralClosure v.ring K')

theorem closure_mem_placeOfPrime (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K'))
    (b : integralClosure v.ring K') : (b : K') ∈ (v.placeOfPrime q).ring :=
  Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K' _
    (v.primeHS q).asIdeal.primeCompl_le_nonZeroDivisors) b

theorem placeOfPrime_liesOver (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    (v.placeOfPrime q).LiesOver v :=
  liesOver_of_le fun x hx =>
    v.closure_mem_placeOfPrime q (algebraMap v.ring (integralClosure v.ring K') ⟨x, hx⟩)

end Correspondence

section Sum

variable [IsFunctionField k K] [IsFunctionField k K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] (v : Place k K)

attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure

noncomputable def closureHom {w : Place k K'} (h : w.LiesOver v) :
    integralClosure v.ring K' →+* w.ring :=
  RingHom.codRestrict (algebraMap (integralClosure v.ring K') K') w.ring fun b =>
    v.mem_of_isIntegral_of_liesOver h ((mem_integralClosure_iff v.ring K').1 b.2)

noncomputable def primeOfPlace {w : Place k K'} (h : w.LiesOver v) :
    (maximalIdeal v.ring).primesOver (integralClosure v.ring K') :=
  ⟨(maximalIdeal w.ring).comap (v.closureHom h), Ideal.comap_isPrime _ _, ⟨by
    let := h.algebra
    have := h.isLocalHom
    have hc : (v.closureHom h).comp (algebraMap v.ring (integralClosure v.ring K')) =
        algebraMap v.ring w.ring := RingHom.ext fun a => Subtype.ext rfl
    change maximalIdeal v.ring = Ideal.comap (algebraMap v.ring (integralClosure v.ring K'))
      (Ideal.comap (v.closureHom h) (maximalIdeal w.ring))
    rw [Ideal.comap_comap, hc]
    have hlo : (maximalIdeal w.ring).LiesOver (maximalIdeal v.ring) := inferInstance
    exact hlo.over⟩⟩

theorem placeOfPrime_primeOfPlace {w : Place k K'} (h : w.LiesOver v) :
    v.placeOfPrime (v.primeOfPlace h) = w := by
  refine Place.eq_of_le fun x hx => ?_
  obtain ⟨a, s, hs, rfl⟩ := hx
  have ha : ((a : integralClosure v.ring K') : K') ∈ w.ring := (v.closureHom h a).2
  have hsw : ((s : integralClosure v.ring K') : K') ∈ w.ring := (v.closureHom h s).2
  have hs' : v.closureHom h s ∉ maximalIdeal w.ring := hs
  have hs1 : w.ring.valuation (s : K') = 1 :=
    le_antisymm (w.ring.valuation_le_one_iff _ |>.2 hsw) (not_lt.1 fun hlt =>
      hs' ((w.ring.valuation_lt_one_iff _).2 hlt))
  have hsinv : ((s : integralClosure v.ring K') : K')⁻¹ ∈ w.ring := by
    rw [← w.ring.valuation_le_one_iff, map_inv₀, hs1, inv_one]
  exact mul_mem ha hsinv

omit [IsFunctionField k K'] in
theorem primeOfPlace_placeOfPrime
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    v.primeOfPlace (v.placeOfPrime_liesOver q) = q := by
  apply Subtype.ext
  ext b
  change v.closureHom _ b ∈ maximalIdeal (v.placeOfPrime q).ring ↔ b ∈ q.1
  rw [ValuationSubring.valuation_lt_one_iff]
  change (v.placeOfPrime q).ring.valuation (b : K') < 1 ↔ b ∈ q.1
  constructor
  · intro hb
    by_contra hbq
    have hinv : ((b : integralClosure v.ring K') : K')⁻¹ ∈ (v.placeOfPrime q).ring :=
      ⟨1, b, hbq, by simp⟩
    have hbmem := v.closure_mem_placeOfPrime q b
    have hb0 : (b : K') ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at hinv
      exact hbq (by
        have : b = 0 := Subtype.ext h0
        rw [this]; exact q.1.zero_mem)
    have h1 := (v.placeOfPrime q).ring.valuation_le_one_iff _ |>.2 hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd hb (not_lt.2 h1)
  · intro hbq
    by_contra hb
    have hb1 : (v.placeOfPrime q).ring.valuation (b : K') = 1 :=
      le_antisymm ((v.placeOfPrime q).ring.valuation_le_one_iff _ |>.2
        (v.closure_mem_placeOfPrime q b)) (not_lt.1 hb)
    have hb0 : (b : K') ≠ 0 := by
      intro h0; rw [h0, map_zero] at hb1; exact zero_ne_one hb1
    have hinv : ((b : integralClosure v.ring K') : K')⁻¹ ∈ (v.placeOfPrime q).ring := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
    have h1 : (v.primeHS q).valuation K' (b : K')⁻¹ ≤ 1 := hle hinv
    have h2 : (v.primeHS q).valuation K' (algebraMap (integralClosure v.ring K') K' b) < 1 :=
      ((v.primeHS q).valuation_lt_one_iff_mem (K := K') b).2 hbq
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd h2 (not_lt.2 h1)

noncomputable def primesOverEquiv :
    (maximalIdeal v.ring).primesOver (integralClosure v.ring K') ≃
      {w : Place k K' // w.LiesOver v} where
  toFun q := ⟨v.placeOfPrime q, v.placeOfPrime_liesOver q⟩
  invFun w := v.primeOfPlace w.2
  left_inv q := v.primeOfPlace_placeOfPrime q
  right_inv w := Subtype.ext (v.placeOfPrime_primeOfPlace w.2)

theorem valuation_primeHS (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    (v.primeHS q).valuation K' = (v.placeOfPrime q).valuation := by
  symm
  refine valuation_eq_of_isEquiv ?_ (v.placeOfPrime q).valuation_surjective
    (HeightOneSpectrum.valuation_surjective K' _)
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [Place.valuation_le_one_iff]
  have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
  let P : Place k K' :=
    { ring := ((v.primeHS q).valuation K').valuationSubring
      ne_top := by
        intro htop
        obtain ⟨π, hπ⟩ := (v.primeHS q).valuation_exists_uniformizer K'
        have hmem : π⁻¹ ∈ ((v.primeHS q).valuation K').valuationSubring :=
          htop ▸ ValuationSubring.mem_top _
        rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg,
          ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
        omega
      algebraMap_mem := fun c => hle ((v.placeOfPrime q).algebraMap_mem c) }
  have heq : v.placeOfPrime q = P := Place.eq_of_le hle
  constructor
  · intro hx
    exact hle hx
  · intro hx
    have hxP : x ∈ P.ring := hx
    rw [← heq] at hxP
    exact hxP

theorem ramificationIdx_primeOfPlace_eq
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    q.1.ramificationIdx v.ring = (v.placeOfPrime q).ramificationIdx v := by
  have := q.2.1
  have := q.2.2
  have : (v.primeHS q).asIdeal.LiesOver v.heightOneSpectrum.asIdeal := q.2.2
  have hp : maximalIdeal v.ring ≠ ⊥ := IsDiscreteValuationRing.not_a_field v.ring
  have h := v.placeOfPrime_liesOver q
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal v.ring) q.1 hp,
    ← h.ramificationIdx'_eq]
  have e1 : v.valuation v.uniformizer ^ (maximalIdeal v.ring).ramificationIdx' q.1 =
      (v.primeHS q).valuation K' (algebraMap K K' v.uniformizer) :=
    HeightOneSpectrum.valuation_liesOver K' v.heightOneSpectrum (v.primeHS q) v.uniformizer
  have e2 := h.valuation_algebraMap v.uniformizer
  rw [valuation_primeHS, ← e2, v.valuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer,
    ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj] at e1
  simpa using e1

omit [IsFunctionField k K'] in

theorem inertiaDeg_primeOfPlace_eq
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    q.1.inertiaDeg v.ring = (v.placeOfPrime q).inertiaDeg v := by
  have := q.2.1
  have := q.2.2
  have hmax : q.1.IsMaximal := q.2.1.isMaximal (v.ne_bot_of_mem_primesOver q.2)
  have h := v.placeOfPrime_liesOver q
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal v.ring) q.1, ← h.finrank_residueField]
  let := h.algebra
  have := h.isLocalHom
  have : IsLocalization.AtPrime (v.placeOfPrime q).ring q.1 :=
    inferInstanceAs (IsLocalization (v.primeHS q).asIdeal.primeCompl
      (HeightOneSpectrum.valuationSubringAtPrime K' (v.primeHS q)))
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (IsLocalization.AtPrime.equivQuotMaximalIdeal q.1 (v.placeOfPrime q).ring) ?_
  apply Ideal.Quotient.ringHom_ext
  ext a
  rfl

theorem finite_liesOver : {w : Place k K' | w.LiesOver v}.Finite := by
  have hfin : ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')).Finite :=
    Algebra.QuasiFinite.finite_primesOver _
  have := hfin.to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ v.primesOverEquiv)

theorem sum_ramificationIdx_mul_inertiaDeg :
    ∑ w ∈ (v.finite_liesOver (K' := K')).toFinset, w.ramificationIdx v * w.inertiaDeg v =
      Module.finrank K K' := by
  classical
  have hfin : ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')).Finite :=
    Algebra.QuasiFinite.finite_primesOver _
  let : Fintype ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')) := hfin.fintype
  let : Fintype {w : Place k K' // w.LiesOver v} := Fintype.ofEquiv _ v.primesOverEquiv
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal v.ring)
    (integralClosure v.ring K')
  rw [finrank_closure] at hsum
  have hs : ∀ w : Place k K', w ∈ (v.finite_liesOver (K' := K')).toFinset ↔ w.LiesOver v :=
    fun w => Set.Finite.mem_toFinset _
  rw [← hsum, Finset.sum_subtype _ hs]
  refine (Fintype.sum_equiv v.primesOverEquiv _ _ fun q => ?_).symm
  rw [ramificationIdx_primeOfPlace_eq, inertiaDeg_primeOfPlace_eq]
  rfl

noncomputable def heightOneSpectrumEquiv :
    {P : HeightOneSpectrum (integralClosure v.ring K') //
        P.asIdeal.LiesOver (maximalIdeal v.ring)} ≃
      (maximalIdeal v.ring).primesOver (integralClosure v.ring K') where
  toFun P := ⟨P.1.asIdeal, P.1.isPrime, P.2⟩
  invFun q := ⟨v.primeHS q, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Sum

end Place

end GroundTheory.FunctionField
end

section
namespace GroundTheory.FunctionField

open IsDedekindDomain IsLocalRing

open scoped WithZero

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section General

variable (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]
  (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range)

noncomputable abbrev ofHeightOneSpectrum (P : HeightOneSpectrum B) : Place k K where
  ring := HeightOneSpectrum.valuationSubringAtPrime K P
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
    have hmem : π⁻¹ ∈ (P.valuation K).valuationSubring := hle (htop ▸ ValuationSubring.mem_top _)
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    obtain ⟨b, hb⟩ := hk c
    rw [← hb]
    exact Subalgebra.algebraMap_mem
      (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b

theorem algebraMap_mem_ofHeightOneSpectrum (P : HeightOneSpectrum B) (b : B) :
    algebraMap B K b ∈ (ofHeightOneSpectrum B hk P).ring :=
  Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b

noncomputable def centerHom (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) : B →+* v.ring :=
  RingHom.codRestrict (algebraMap B K) v.ring hv

noncomputable def center (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) :
    HeightOneSpectrum B where
  asIdeal := (maximalIdeal v.ring).comap (centerHom B v hv)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h0
    apply v.ne_top
    have hunit : ∀ b : B, b ≠ 0 → v.ring.valuation (algebraMap B K b) = 1 := by
      intro b hb
      refine le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv b)) (not_lt.1 fun hlt => hb ?_)
      have hmem : centerHom B v hv b ∈ maximalIdeal v.ring := (v.ring.valuation_lt_one_iff _).2 hlt
      have : b ∈ (maximalIdeal v.ring).comap (centerHom B v hv) := hmem
      rw [h0] at this
      exact this
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    rw [← v.ring.valuation_le_one_iff, map_div₀, hunit s hs0, div_one]
    exact (v.ring.valuation_le_one_iff _).2 (hv a)

variable [IsFunctionField k K]

theorem ofHeightOneSpectrum_center (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) :
    ofHeightOneSpectrum B hk (center B v hv) = v := by
  refine Place.eq_of_le fun x hx => ?_
  obtain ⟨a, s, hs, rfl⟩ := hx
  have hs' : centerHom B v hv s ∉ maximalIdeal v.ring := hs
  have hs1 : v.ring.valuation (algebraMap B K s) = 1 :=
    le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv s)) (not_lt.1 fun hlt =>
      hs' ((v.ring.valuation_lt_one_iff _).2 hlt))
  have hsinv : (algebraMap B K s)⁻¹ ∈ v.ring := by
    rw [← v.ring.valuation_le_one_iff, map_inv₀, hs1, inv_one]
  exact mul_mem (hv a) hsinv

omit [IsFunctionField k K] in
theorem center_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    center B (ofHeightOneSpectrum B hk P) (algebraMap_mem_ofHeightOneSpectrum B hk P) = P := by
  ext b
  change centerHom B _ _ b ∈ maximalIdeal (ofHeightOneSpectrum B hk P).ring ↔ b ∈ P.asIdeal
  rw [ValuationSubring.valuation_lt_one_iff]
  change (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) < 1 ↔ b ∈ P.asIdeal
  have hbmem := algebraMap_mem_ofHeightOneSpectrum B hk P b
  constructor
  · intro hb
    by_contra hbP
    have hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring :=
      ⟨1, b, hbP, by simp⟩
    have hb0 : algebraMap B K b ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at hinv
      apply hbP
      have : b = 0 := IsFractionRing.injective B K (h0.trans (map_zero _).symm)
      rw [this]
      exact P.asIdeal.zero_mem
    have h1 := (ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd hb (not_lt.2 h1)
  · intro hbP
    by_contra hb
    have hb1 : (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) = 1 :=
      le_antisymm ((ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hbmem)
        (not_lt.1 hb)
    have hb0 : algebraMap B K b ≠ 0 := by
      intro h0; rw [h0, map_zero] at hb1; exact zero_ne_one hb1
    have hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
    have h1 : P.valuation K (algebraMap B K b)⁻¹ ≤ 1 := hle hinv
    have h2 : P.valuation K (algebraMap B K b) < 1 := (P.valuation_lt_one_iff_mem (K := K) b).2 hbP
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd h2 (not_lt.2 h1)

noncomputable def equivHeightOneSpectrum :
    {v : Place k K // ∀ b : B, algebraMap B K b ∈ v.ring} ≃ HeightOneSpectrum B where
  toFun v := center B v.1 v.2
  invFun P := ⟨ofHeightOneSpectrum B hk P, algebraMap_mem_ofHeightOneSpectrum B hk P⟩
  left_inv v := Subtype.ext (ofHeightOneSpectrum_center B hk v.1 v.2)
  right_inv P := center_ofHeightOneSpectrum B hk P

theorem valuation_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum B hk P).valuation = P.valuation K := by
  refine valuation_eq_of_isEquiv ?_ (ofHeightOneSpectrum B hk P).valuation_surjective
    (HeightOneSpectrum.valuation_surjective K P)
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [Place.valuation_le_one_iff]
  have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
  let Q : Place k K :=
    { ring := (P.valuation K).valuationSubring
      ne_top := (ofHeightOneSpectrum B hk P).ne_top ∘ fun htop => by
        apply le_antisymm le_top
        intro y _
        obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
        have hmem : π⁻¹ ∈ (P.valuation K).valuationSubring := htop ▸ ValuationSubring.mem_top _
        rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg,
          ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
        omega
      algebraMap_mem := fun c => hle ((ofHeightOneSpectrum B hk P).algebraMap_mem c) }
  have heq : ofHeightOneSpectrum B hk P = Q := Place.eq_of_le hle
  constructor
  · exact fun hx => hle hx
  · intro hx
    have hxQ : x ∈ Q.ring := hx
    rw [← heq] at hxQ
    exact hxQ

end General

section RatFunc

open scoped Polynomial

omit [Algebra k K] in

theorem _root_.GroundTheory.FunctionField.IsFunctionField.of_trdeg_eq_one [Algebra k K]
    [Algebra.EssFiniteType k K] (h : Algebra.trdeg k K = 1) : IsFunctionField k K := by
  have : Algebra.Transcendental k K :=
    (trdeg_ne_zero_iff (R := k) (A := K)).1 (by rw [h]; exact one_ne_zero)
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := K)
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set K) → K) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set K))).2 hx)
      (by rw [h, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K :=
    Algebra.EssFiniteType.of_comp k _ K
  exact ⟨⟨x, hx, Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩

omit [Algebra k K] in
theorem _root_.GroundTheory.FunctionField.essFiniteType_ratFunc : Algebra.EssFiniteType k (RatFunc k) := by
  have : Algebra.EssFiniteType k[X] (RatFunc k) :=
    .of_isLocalization _ (nonZeroDivisors k[X])
  exact .comp k k[X] (RatFunc k)

omit [Algebra k K] in

instance _root_.GroundTheory.FunctionField.isFunctionField_ratFunc : IsFunctionField k (RatFunc k) := by
  have := essFiniteType_ratFunc (k := k)
  apply IsFunctionField.of_trdeg_eq_one
  have : Algebra.IsAlgebraic k[X] (RatFunc k) := IsLocalization.isAlgebraic _ (nonZeroDivisors k[X])
  have h := trdeg_add_eq k k[X] (A := RatFunc k)
  rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
  exact h.symm

omit [Algebra k K] in

theorem _root_.GroundTheory.FunctionField.IsFunctionField.of_functionField [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] :
    IsFunctionField k K := by
  have := essFiniteType_ratFunc (k := k)
  have : Algebra.EssFiniteType k K := .comp k (RatFunc k) K
  apply IsFunctionField.of_trdeg_eq_one
  have h := lift_trdeg_add_eq k (RatFunc k) K
  rw [trdeg_eq_one (k := k) (K := RatFunc k), trdeg_eq_zero, Cardinal.lift_zero, add_zero,
    Cardinal.lift_one] at h
  exact (Cardinal.lift_eq_one.1 h.symm)

end RatFunc

section RingOfIntegers

open scoped Polynomial

variable [IsFunctionField k K] [Algebra k[X] K] [Algebra (RatFunc k) K]
  [IsScalarTower k[X] (RatFunc k) K] [IsScalarTower k k[X] K] [FunctionField k K]

omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in
theorem algebraMap_polynomial_mem (v : Place k K) (hv : algebraMap k[X] K Polynomial.X ∈ v.ring)
    (p : k[X]) : algebraMap k[X] K p ∈ v.ring := by
  have h : algebraMap k[X] K p = Polynomial.aeval (algebraMap k[X] K Polynomial.X) p := by
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [h, ← v.ring.valuation_le_one_iff]
  exact v.valuation_aeval_le_one hv p

omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in

theorem forall_mem_ringOfIntegers_iff (v : Place k K) :
    (∀ b : FunctionField.ringOfIntegers k K, algebraMap _ K b ∈ v.ring) ↔
      algebraMap k[X] K Polynomial.X ∈ v.ring := by
  constructor
  · intro h
    have hX : IsIntegral k[X] (algebraMap k[X] K Polynomial.X) := isIntegral_algebraMap
    have := h (IsIntegralClosure.mk' (FunctionField.ringOfIntegers k K) _ hX)
    rwa [IsIntegralClosure.algebraMap_mk'] at this
  · intro hv b
    let : Algebra k[X] v.ring :=
      (RingHom.codRestrict (algebraMap k[X] K) v.ring (v.algebraMap_polynomial_mem hv)).toAlgebra
    have : IsScalarTower k[X] v.ring K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hb : IsIntegral k[X] (algebraMap (FunctionField.ringOfIntegers k K) K b) :=
      (IsIntegralClosure.isIntegral k[X] K b).map
        (IsScalarTower.toAlgHom k[X] (FunctionField.ringOfIntegers k K) K)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := v.ring))
    rw [← hy]
    exact y.2

omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in
theorem algebraMap_mem_range_ringOfIntegers (c : k) :
    algebraMap k K c ∈ (algebraMap (FunctionField.ringOfIntegers k K) K).range := by
  have hc : IsIntegral k[X] (algebraMap k[X] K (Polynomial.C c)) := isIntegral_algebraMap
  refine ⟨IsIntegralClosure.mk' (FunctionField.ringOfIntegers k K) _ hc, ?_⟩
  rw [IsIntegralClosure.algebraMap_mk', ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

noncomputable def equivHeightOneSpectrumRingOfIntegers [Algebra.IsSeparable (RatFunc k) K] :
    {v : Place k K // algebraMap k[X] K Polynomial.X ∈ v.ring} ≃
      HeightOneSpectrum (FunctionField.ringOfIntegers k K) :=
  (Equiv.subtypeEquivRight fun v => (forall_mem_ringOfIntegers_iff v).symm).trans
    (equivHeightOneSpectrum _ algebraMap_mem_range_ringOfIntegers)

end RingOfIntegers

section Separating

open scoped IntermediateField.algebraAdjoinAdjoin

omit [Algebra k K] in

theorem isPrincipalIdealRing_adjoin [Algebra k K] (t : K) :
    IsPrincipalIdealRing (Algebra.adjoin k {t}) := by
  refine IsPrincipalIdealRing.of_surjective
    (Polynomial.aeval (R := k) (⟨t, Algebra.self_mem_adjoin_singleton k t⟩ : Algebra.adjoin k {t})) ?_
  rintro ⟨y, hy⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
  exact ⟨p, Subtype.ext (Polynomial.aeval_subalgebra_coe p _ _)⟩

variable [IsFunctionField k K] (t : K) [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]

theorem transcendental_of_isSeparable : Transcendental k t := by
  intro ht
  have : FiniteDimensional k (IntermediateField.adjoin k {t}) :=
    IntermediateField.adjoin.finiteDimensional ht.isIntegral
  have : Algebra.IsAlgebraic k (IntermediateField.adjoin k {t}) := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.trans k (IntermediateField.adjoin k {t}) K
  have h := trdeg_eq_one (k := k) (K := K)
  rw [trdeg_eq_zero] at h
  exact zero_ne_one h

theorem isDedekindDomain_closure_adjoin :
    IsDedekindDomain (integralClosure (Algebra.adjoin k {t}) K) := by
  have := isPrincipalIdealRing_adjoin (k := k) t
  have := finiteDimensional_adjoin (transcendental_of_isSeparable (k := k) t)
  exact IsIntegralClosure.isDedekindDomain (Algebra.adjoin k {t}) (IntermediateField.adjoin k {t}) K _

theorem isFractionRing_closure_adjoin :
    IsFractionRing (integralClosure (Algebra.adjoin k {t}) K) K := by
  have := finiteDimensional_adjoin (transcendental_of_isSeparable (k := k) t)
  exact integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin k {t})
    (IntermediateField.adjoin k {t}) K

attribute [local instance] isDedekindDomain_closure_adjoin isFractionRing_closure_adjoin

omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K] in

theorem forall_mem_closure_adjoin_iff (v : Place k K) :
    (∀ b : integralClosure (Algebra.adjoin k {t}) K, algebraMap _ K b ∈ v.ring) ↔ t ∈ v.ring := by
  constructor
  · intro h
    have hint : IsIntegral (Algebra.adjoin k {t}) t :=
      isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K)
        (x := ⟨t, Algebra.self_mem_adjoin_singleton k t⟩)
    exact h ⟨t, hint⟩
  · intro hv b
    have hA : ∀ a : Algebra.adjoin k {t}, (a : K) ∈ v.ring := by
      rintro ⟨y, hy⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
      rw [← v.ring.valuation_le_one_iff]
      exact v.valuation_aeval_le_one hv p
    let : Algebra (Algebra.adjoin k {t}) v.ring :=
      (RingHom.codRestrict (algebraMap (Algebra.adjoin k {t}) K) v.ring hA).toAlgebra
    have : IsScalarTower (Algebra.adjoin k {t}) v.ring K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hb : IsIntegral (Algebra.adjoin k {t}) (b : K) := b.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := v.ring))
    show (b : K) ∈ v.ring
    rw [← hy]
    exact y.2

omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K] in
theorem algebraMap_mem_range_closure_adjoin (c : k) :
    algebraMap k K c ∈ (algebraMap (integralClosure (Algebra.adjoin k {t}) K) K).range := by
  have hc : IsIntegral (Algebra.adjoin k {t}) (algebraMap k K c) :=
    isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K)
      (x := ⟨algebraMap k K c, Subalgebra.algebraMap_mem _ c⟩)
  exact ⟨⟨algebraMap k K c, hc⟩, rfl⟩

noncomputable def equivOfSeparating :
    {v : Place k K // t ∈ v.ring} ≃ HeightOneSpectrum (integralClosure (Algebra.adjoin k {t}) K) :=
  (Equiv.subtypeEquivRight fun v => (forall_mem_closure_adjoin_iff t v).symm).trans
    (equivHeightOneSpectrum _ (algebraMap_mem_range_closure_adjoin t))

omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K] in
theorem adjoin_inv_eq : IntermediateField.adjoin k {t⁻¹} = IntermediateField.adjoin k {t} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)
    rwa [inv_inv] at this

omit [IsFunctionField k K] in

theorem isSeparable_adjoin_inv : Algebra.IsSeparable (IntermediateField.adjoin k {t⁻¹}) K := by
  rw [adjoin_inv_eq]
  infer_instance

end Separating

end Place

end GroundTheory.FunctionField
end
