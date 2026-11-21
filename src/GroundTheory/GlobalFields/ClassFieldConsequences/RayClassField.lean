import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClass
import GroundTheory.GlobalFields.Adele.WeakApproxUnits
import GroundTheory.GlobalFields.ClassFieldConsequences.OpenSubgroup
import GroundTheory.GlobalFields.GlobalArtinMap.ArtinMap

section
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace Modulus

variable (𝔪 : Modulus K)

def coprimeIdeals : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
    count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' v _ := by rw [Units.val_one, count_one]
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, count_inv, hI v hv, neg_zero]


theorem ord_eq_zero_of_mem_idelesOneMod {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.ideal) : ord v x = 0 := by
  have h := ((𝔪.mem_idelesOneMod.1 hx).1 v hv).1
  rw [coe_finiteProj] at h
  rw [ord, h, log_one, neg_zero]

theorem toFractionalIdeal_mem_coprimeIdeals {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    toFractionalIdeal x ∈ 𝔪.coprimeIdeals := fun v hv ↦ by
  rw [count_toFractionalIdeal, 𝔪.ord_eq_zero_of_mem_idelesOneMod hx hv]


def principalRay : Subgroup 𝔪.coprimeIdeals :=
  (𝔪.rayUnits.map (toPrincipalIdeal (𝓞 K) K)).subgroupOf 𝔪.coprimeIdeals

theorem mem_principalRay {I : 𝔪.coprimeIdeals} :
    I ∈ 𝔪.principalRay ↔
      ∃ a ∈ 𝔪.rayUnits, toPrincipalIdeal (𝓞 K) K a = (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  rw [principalRay, Subgroup.mem_subgroupOf, Subgroup.mem_map]

abbrev IdealRayClassGroup : Type _ :=
  𝔪.coprimeIdeals ⧸ 𝔪.principalRay

theorem exists_diagonal_mul_mem_idelesOneMod (x : IdeleGroup K) :
    ∃ a : Kˣ, diagonal K a * x ∈ 𝔪.idelesOneMod := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 K)) := 𝔪.finite_support_exponent.toFinset
  let T : Finset (InfinitePlace K) := Finset.univ
  let O : Set (((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ)) :=
    (Set.univ.pi fun v : S ↦ {z | z * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)}) ×ˢ
      (Set.univ.pi fun w : T ↦ {z | ∀ hw : w.1.IsReal,
        (⟨w.1, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ 𝔪.real →
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
            ((z * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)})
  have hO : IsOpen O := by
    refine (isOpen_set_pi Set.finite_univ fun v _ ↦ ?_).prod
      (isOpen_set_pi Set.finite_univ fun w _ ↦ ?_)
    · exact (isOpen_unitsLevel v.1 _).preimage (continuous_mul_const _)
    · simp only [Set.ofPred_forall]
      refine isOpen_iInter_of_finite fun hw ↦ isOpen_iInter_of_finite fun _ ↦ ?_
      exact isOpen_lt continuous_const
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp
          (Units.continuous_val.comp (continuous_mul_const _)))
  have hne : O.Nonempty := by
    refine ⟨(fun v ↦ (finiteProj v.1 x)⁻¹, fun w ↦ (infiniteProj w.1 x)⁻¹),
      Set.mem_univ_pi.2 fun v ↦ ?_, Set.mem_univ_pi.2 fun w ↦ ?_⟩
    · show (finiteProj v.1 x)⁻¹ * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)
      rw [inv_mul_cancel]
      exact one_mem _
    · intro hw _
      show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((infiniteProj w.1 x)⁻¹ * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)
      rw [inv_mul_cancel, Units.val_one, map_one]
      exact one_pos
  obtain ⟨a, ha⟩ := (denseRange_units_prod_pi S T).exists_mem_open hO hne
  refine ⟨a, 𝔪.mem_idelesOneMod.2 ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩⟩
  · have hvS : v ∈ S := by
      rw [Set.Finite.mem_toFinset, mem_support, ← Nat.one_le_iff_ne_zero]
      exact (𝔪.one_le_exponent_iff v).2 hv
    have h := Set.mem_univ_pi.1 ha.1 ⟨v, hvS⟩
    have he : finiteProj v (diagonal K a) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
      refine Units.ext ?_
      change ((a : K) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) a
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [map_mul, he]
    exact h
  · have h := Set.mem_univ_pi.1 ha.2 ⟨w.1, Finset.mem_univ _⟩ w.2 hw
    have he : infiniteProj w.1 (diagonal K a) =
        Units.map (algebraMap K w.1.Completion).toMonoidHom a :=
      Units.ext rfl
    rw [map_mul, he]
    exact h

def idelesOneModToCoprimeIdeals : 𝔪.idelesOneMod →* 𝔪.coprimeIdeals :=
  ((toFractionalIdeal (K := K)).comp 𝔪.idelesOneMod.subtype).codRestrict _
    fun x ↦ 𝔪.toFractionalIdeal_mem_coprimeIdeals x.2

@[simp]
theorem coe_idelesOneModToCoprimeIdeals (x : 𝔪.idelesOneMod) :
    ((𝔪.idelesOneModToCoprimeIdeals x : 𝔪.coprimeIdeals) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toFractionalIdeal (x : IdeleGroup K) :=
  rfl

def toIdealRayClassGroup : 𝔪.idelesOneMod →* 𝔪.IdealRayClassGroup :=
  (QuotientGroup.mk' _).comp 𝔪.idelesOneModToCoprimeIdeals

def toRayClassGroup : 𝔪.idelesOneMod →* 𝔪.RayClassGroup :=
  (QuotientGroup.mk' _).comp 𝔪.idelesOneMod.subtype

theorem exists_mem_idelesOneMod_toFractionalIdeal_eq {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    ∃ x ∈ 𝔪.idelesOneMod, toFractionalIdeal x = primeIdealUnit v := by
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  refine ⟨finiteEmbedding v (Units.mk0 _ hne), 𝔪.mem_idelesOneMod.2 ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩,
    toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  · have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    rw [finiteProj_finiteEmbedding_of_ne hwv]
    exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos
  · rw [count_primeIdealUnit]
    split_ifs with h
    · subst h
      rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp,
        neg_neg]
    · exact ord_finiteEmbedding_of_ne h _

theorem idelesOneModToCoprimeIdeals_surjective : Surjective 𝔪.idelesOneModToCoprimeIdeals := by
  rintro ⟨I, hI⟩
  have h : I ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K)) := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    refine finprod_induction (· ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K))) (one_mem _)
      (fun _ _ ↦ mul_mem) fun v ↦ ?_
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · rw [hI v hv, zpow_zero]
      exact one_mem _
    · obtain ⟨x, hx, hxI⟩ := 𝔪.exists_mem_idelesOneMod_toFractionalIdeal_eq hv
      exact zpow_mem (Subgroup.mem_map.2 ⟨x, hx, hxI⟩) _
  obtain ⟨x, hx, hxI⟩ := h
  exact ⟨⟨x, hx⟩, Subtype.ext hxI⟩

theorem toIdealRayClassGroup_surjective : Surjective 𝔪.toIdealRayClassGroup :=
  (QuotientGroup.mk'_surjective _).comp 𝔪.idelesOneModToCoprimeIdeals_surjective

theorem toRayClassGroup_surjective : Surjective 𝔪.toRayClassGroup := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, ha⟩ := 𝔪.exists_diagonal_mul_mem_idelesOneMod x
  refine ⟨⟨_, ha⟩, ?_⟩
  change (QuotientGroup.mk (diagonal K a * x) : 𝔪.RayClassGroup) = QuotientGroup.mk x
  rw [QuotientGroup.eq, show (diagonal K a * x)⁻¹ * x = (diagonal K a)⁻¹ by
    rw [mul_inv_rev, mul_comm x⁻¹, mul_assoc, inv_mul_cancel, mul_one]]
  exact inv_mem (𝔪.diagonal_range_le_rayGroup ⟨a, rfl⟩)

theorem ker_toRayClassGroup :
    𝔪.toRayClassGroup.ker = 𝔪.rayGroup.subgroupOf 𝔪.idelesOneMod := by
  ext x
  rw [MonoidHom.mem_ker, toRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem ker_toIdealRayClassGroup :
    𝔪.toIdealRayClassGroup.ker = 𝔪.rayGroup.subgroupOf 𝔪.idelesOneMod := by
  ext ⟨x, hx⟩
  rw [MonoidHom.mem_ker, toIdealRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_principalRay, Subgroup.mem_subgroupOf, rayGroup, Subgroup.mem_sup]
  constructor
  · rintro ⟨a, ha, hax⟩
    change toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal x at hax
    refine ⟨diagonal K a, ⟨a, rfl⟩, (diagonal K a)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
    rw [congruenceSubgroup_eq_inf, Subgroup.mem_inf, ← ker_toFractionalIdeal, MonoidHom.mem_ker,
      map_mul, map_inv, toFractionalIdeal_diagonal, hax]
    exact ⟨mul_mem (inv_mem ha) hx, inv_mul_cancel _⟩
  · rintro ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
    have hu' := 𝔪.congruenceSubgroup_le_idelesOneMod hu
    have ha : a ∈ 𝔪.rayUnits := by
      change diagonal K a ∈ 𝔪.idelesOneMod
      rw [← mul_inv_cancel_right (diagonal K a) u]
      exact mul_mem hx (inv_mem hu')
    refine ⟨a, ha, ?_⟩
    change toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal (diagonal K a * u)
    have hu0 : toFractionalIdeal u = 1 := by
      rw [← MonoidHom.mem_ker, ker_toFractionalIdeal]
      exact 𝔪.congruenceSubgroup_le_standardOpenSubgroup hu
    rw [map_mul, hu0, mul_one, toFractionalIdeal_diagonal]

def rayClassGroupEquiv : 𝔪.RayClassGroup ≃* 𝔪.IdealRayClassGroup :=
  (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (𝔪.ker_toRayClassGroup.trans 𝔪.ker_toIdealRayClassGroup.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toIdealRayClassGroup_surjective))

theorem rayClassGroupEquiv_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.rayClassGroupEquiv (QuotientGroup.mk x : 𝔪.RayClassGroup) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm
      (QuotientGroup.mk x : 𝔪.RayClassGroup) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [rayClassGroupEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl

def quotientEquivIdealRayClassGroup :
    IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≃* 𝔪.IdealRayClassGroup :=
  𝔪.quotientMapCongruenceEquiv.trans 𝔪.rayClassGroupEquiv


instance : Finite 𝔪.IdealRayClassGroup :=
  Finite.of_equiv _ 𝔪.rayClassGroupEquiv.toEquiv

end Modulus

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup SemiLocal WithZero
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension)
open scoped Pointwise

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

namespace Modulus

variable (𝔪 : Modulus K)

def normSubgroup : OpenFiniteIndexSubgroup K :=
  ⟨𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K), 𝔪.isOpen_map_congruenceSubgroup,
    𝔪.finiteIndex_map_congruenceSubgroup⟩

theorem finiteEmbedding_mem_congruenceSubgroup {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) {u : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    finiteEmbedding v u ∈ 𝔪.congruenceSubgroup := by
  refine 𝔪.mem_congruenceSubgroup.2 ⟨fun w ↦ ?_, fun w _ ↦ ?_⟩
  · by_cases hwv : w = v
    · subst hwv
      rw [finiteProj_finiteEmbedding, (𝔪.exponent_eq_zero_iff w).2 hv]
      refine mem_unitsLevel.2 ⟨hu, ?_⟩
      rw [Nat.cast_zero, neg_zero, exp_zero]
      exact Valuation.map_sub_le _ hu.le (by simp)
    · rw [finiteProj_finiteEmbedding_of_ne hwv]
      exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos

theorem exists_uniformizer_finiteEmbedding_mem_idelesOneMod {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    ∃ π : (v.adicCompletion K)ˣ, LocalField.ord (π : v.adicCompletion K) = 1 ∧
      ∃ _ : finiteEmbedding v π ∈ 𝔪.idelesOneMod,
        toFractionalIdeal (finiteEmbedding v π) = primeIdealUnit v := by
  classical
  obtain ⟨π, hπ, hval⟩ := exists_ord_eq_one_valued v
  refine ⟨π, hπ, 𝔪.mem_idelesOneMod.2 ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩,
    toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  · have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    rw [finiteProj_finiteEmbedding_of_ne hwv]
    exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos
  · rw [count_primeIdealUnit]
    split_ifs with h
    · subst h
      rw [ord_finiteEmbedding_self, hval, log_exp, neg_neg]
    · exact ord_finiteEmbedding_of_ne h _

theorem primeIdealUnit_mem_coprimeIdeals {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    primeIdealUnit v ∈ 𝔪.coprimeIdeals := fun w hw ↦ by
  rw [count_primeIdealUnit, if_neg]
  rintro rfl
  exact hv hw

def primeClass {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) : 𝔪.IdealRayClassGroup :=
  QuotientGroup.mk ⟨primeIdealUnit v, 𝔪.primeIdealUnit_mem_coprimeIdeals hv⟩

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

def rayClassFieldSubfield : FiniteAbelianSubfield K Ω :=
  (normGroupOrderIso K Ω).symm (OrderDual.toDual 𝔪.normSubgroup)

def rayClassField : IntermediateField K Ω :=
  (𝔪.rayClassFieldSubfield Ω).1

instance finiteDimensional_rayClassField : FiniteDimensional K (𝔪.rayClassField Ω) :=
  (𝔪.rayClassFieldSubfield Ω).2.1

instance isAbelianGalois_rayClassField : IsAbelianGalois K (𝔪.rayClassField Ω) :=
  (𝔪.rayClassFieldSubfield Ω).2.2

theorem range_ideleClassNorm_rayClassField :
    (ideleClassNorm K (𝔪.rayClassField Ω)).range = 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  have h : normGroup (𝔪.rayClassFieldSubfield Ω) = 𝔪.normSubgroup := by
    rw [← normGroupOrderIso_apply, rayClassFieldSubfield, OrderIso.apply_symm_apply]
    rfl
  exact congrArg Subtype.val h

def rayClassGroupGalEquiv : 𝔪.RayClassGroup ≃* (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) :=
  𝔪.quotientMapCongruenceEquiv.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (𝔪.range_ideleClassNorm_rayClassField Ω).symm).trans
      (reciprocityMapEquiv K (𝔪.rayClassField Ω)))

theorem rayClassGroupGalEquiv_mk (x : IdeleGroup K) :
    𝔪.rayClassGroupGalEquiv Ω (QuotientGroup.mk x) =
      reciprocityMap K (𝔪.rayClassField Ω) (IdeleClassGroup.mk K x) := by
  rw [rayClassGroupGalEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← quotientMapCongruenceEquiv_mk, MulEquiv.symm_apply_apply]
  rfl

def rayClassArtinEquiv : 𝔪.IdealRayClassGroup ≃* (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) :=
  𝔪.rayClassGroupEquiv.symm.trans (𝔪.rayClassGroupGalEquiv Ω)

theorem rayClassArtinEquiv_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.rayClassArtinEquiv Ω (QuotientGroup.mk ⟨toFractionalIdeal x,
      𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩) =
      reciprocityMap K (𝔪.rayClassField Ω) (IdeleClassGroup.mk K x) := by
  rw [rayClassArtinEquiv, MulEquiv.trans_apply, ← 𝔪.rayClassGroupEquiv_mk hx,
    MulEquiv.symm_apply_apply, rayClassGroupGalEquiv_mk]

theorem unitFiltrationUnits_le_ker_localSymbol {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    LocalField.unitFiltrationUnits (v.adicCompletion K) 0 ≤ (localSymbol (𝔪.rayClassField Ω) v).ker := by
  intro u hu
  have hx : IdeleClassGroup.mk K (finiteEmbedding v u) ∈
      (ideleClassNorm K (𝔪.rayClassField Ω)).range := by
    rw [𝔪.range_ideleClassNorm_rayClassField Ω]
    exact ⟨_, 𝔪.finiteEmbedding_mem_congruenceSubgroup hv
      (mem_unitFiltrationUnits_zero_iff_valued.1 hu), rfl⟩
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk, ideleSymbol_finiteEmbedding] at hx
  exact hx

theorem ramificationIdx_rayClassField_eq_one {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal)
    (w : HeightOneSpectrum (𝓞 (𝔪.rayClassField Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
  ramificationIdx_eq_one_of_units_le_ker_localSymbol v (𝔪.unitFiltrationUnits_le_ker_localSymbol Ω hv) w

theorem rayClassArtinEquiv_primeClass {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal)
    (w : HeightOneSpectrum (𝓞 (𝔪.rayClassField Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    𝔪.rayClassArtinEquiv Ω (𝔪.primeClass hv) =
      arithFrobAt (𝓞 K) (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) w.asIdeal := by
  obtain ⟨π, hπ, hx, hxp⟩ := 𝔪.exists_uniformizer_finiteEmbedding_mem_idelesOneMod hv
  have hc : 𝔪.primeClass hv = QuotientGroup.mk ⟨toFractionalIdeal (finiteEmbedding v π),
      𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ := by
    rw [primeClass]
    congr 2
    exact hxp.symm
  rw [hc, 𝔪.rayClassArtinEquiv_mk Ω hx, reciprocityMap_mk,
    ideleSymbol_finiteEmbedding_eq_arithFrobAt v w (𝔪.ramificationIdx_rayClassField_eq_one Ω hv w) hπ]

theorem splitsCompletely_rayClassField_iff {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    SplitsCompletely (𝔪.rayClassField Ω) v ↔ 𝔪.primeClass hv = 1 := by
  obtain ⟨w, hw⟩ := nonempty_placesOver (𝔪.rayClassField Ω) v
  rw [splitsCompletely_iff_arithFrobAt_eq_one v (𝔪.unitFiltrationUnits_le_ker_localSymbol Ω hv) w,
    ← 𝔪.rayClassArtinEquiv_primeClass Ω hv w, MulEquiv.map_eq_one_iff]

end Modulus

theorem exists_le_rayClassField (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ 𝔪 : Modulus K, L ≤ 𝔪.rayClassField Ω := by
  obtain ⟨𝔪, -, hle⟩ := IdeleClassGroup.exists_map_congruenceSubgroup_le _
    (isOpen_range_ideleClassNorm (K := K) (L := L))
  refine ⟨𝔪, (range_ideleClassNorm_le_range_iff L (𝔪.rayClassField Ω)).1 ?_⟩
  rw [𝔪.range_ideleClassNorm_rayClassField Ω]
  exact hle

end

end GroundTheory.Global
end
