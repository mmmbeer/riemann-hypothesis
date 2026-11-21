import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.Ur

open Polynomial IsLocalRing

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

def ball (M : Subfield C) : Subring C where
  carrier := {x | x ∈ M ∧ ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨one_mem _, norm_one.le⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, by rw [norm_neg]; exact ha.2⟩

variable (M : Subfield C)

theorem dvd_iff (a b : ball M) : a ∣ b ↔ ‖(b : C)‖ ≤ ‖(a : C)‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) c.2.2
  · intro h
    by_cases ha : (a : C) = 0
    · have : b = 0 := Subtype.ext (by rw [ha, norm_zero] at h; exact norm_le_zero_iff.mp h)
      rw [this]; exact dvd_zero _
    · refine ⟨⟨b / a, div_mem b.2.1 a.2.1, ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · show (b : C) = a * (b / a)
        field_simp

theorem isUnit_iff (a : ball M) : IsUnit a ↔ ‖(a : C)‖ = 1 := by
  rw [isUnit_iff_dvd_one, dvd_iff, Subring.coe_one, norm_one]
  exact ⟨fun h => le_antisymm a.2.2 h, fun h => h.ge⟩

instance : IsLocalRing (ball M) := .of_nonunits_add fun a b ha hb => by
  rw [mem_nonunits_iff, isUnit_iff] at *
  exact ((IsUltrametricDist.norm_add_le_max (a : C) b).trans_lt
    (max_lt (lt_of_le_of_ne a.2.2 ha) (lt_of_le_of_ne b.2.2 hb))).ne

theorem mem_max (a : ball M) : a ∈ maximalIdeal (ball M) ↔ ‖(a : C)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  exact ⟨fun h => lt_of_le_of_ne a.2.2 h, fun h => h.ne⟩

def toM : ball M →+* M := (ball M).subtype.codRestrict M.toSubring fun x => x.2.1

instance : Algebra (ball M) M := (toM M).toAlgebra

instance : IsScalarTower (ball M) M C := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : IsFractionRing (ball M) M := by
  have hinj : Function.Injective (algebraMap (ball M) M) := fun a b h =>
    Subtype.ext (congrArg (fun t : M => (t : C)) h)
  have : FaithfulSMul (ball M) M := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖(z : C)‖ ≤ 1
  · exact ⟨⟨z, z.2, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · have h1 : ‖(z : C)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_le.mp h).le
    refine ⟨1, ⟨(z : C)⁻¹, inv_mem z.2, h1⟩, ?_⟩
    rw [map_one, one_div]
    exact Subtype.ext (inv_inv (z : C)).symm

def iC : FractionRing (ball M) →+* C := IsFractionRing.lift (g := (ball M).subtype) Subtype.val_injective

theorem iC_alg (a : ball M) : iC M (algebraMap _ _ a) = a := IsFractionRing.lift_algebraMap _ a

theorem iC_mem (x : FractionRing (ball M)) : iC M x ∈ M := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ball M) x
  rw [map_div₀, iC_alg, iC_alg]; exact div_mem a.2.1 b.2.1

theorem iC_int (x : FractionRing (ball M)) :
    ‖iC M x‖ ≤ 1 ↔ x ∈ (algebraMap (ball M) (FractionRing (ball M))).range :=
  ⟨fun h => ⟨⟨iC M x, iC_mem M x, h⟩, (iC M).injective (iC_alg M _)⟩,
    fun ⟨a, h⟩ => by rw [← h, iC_alg]; exact a.2.2⟩

theorem norm_le_of_integral {x : C} (h : IsIntegral (ball M) x) : ‖x‖ ≤ 1 := by
  let V := (NormedField.valuation (K := C)).integer
  let _ : Algebra (ball M) V := (Subring.inclusion (S := ball M) (T := V) fun y hy => by
    show ‖y‖₊ ≤ 1
    exact_mod_cast hy.2).toAlgebra
  have : IsScalarTower (ball M) V C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).isIntegral_iff_v_le_one.mp
    (h.tower_top (A := V))
  exact_mod_cast (show ‖x‖₊ ≤ 1 from h2)

theorem lifts_of_coeff (g : M[X]) (h : ∀ n, ‖(g.coeff n : C)‖ ≤ 1) : g ∈ lifts (algebraMap (ball M) M) :=
  (lifts_iff_coeff_lifts g).mpr fun n => ⟨⟨g.coeff n, (g.coeff n).2, h n⟩, rfl⟩

theorem norm_aeval_lt (g : (ball M)[X]) (h : g.map (residue (ball M)) = 0) {α : C} (hα : ‖α‖ ≤ 1) :
    ‖aeval α g‖ < 1 := by
  rw [aeval_eq_sum_range]
  have : (Finset.range (g.natDegree + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty this
    (fun i => g.coeff i • α ^ i)
  refine hi.trans_lt ?_
  have h1 : ‖(g.coeff i : C)‖ < 1 := (mem_max M _).mp ((residue_eq_zero_iff _).mp (by
    rw [← coeff_map, h, coeff_zero]))
  rw [Algebra.smul_def, norm_mul, norm_pow]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h1 (pow_le_one₀ (norm_nonneg _) hα)

theorem norm_aeval_le (g : (ball M)[X]) {α : C} (hα : ‖α‖ ≤ 1) : ‖aeval α g‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [Algebra.smul_def, norm_mul, norm_pow]
  exact mul_le_one₀ (g.coeff i).2.2 (by positivity) (pow_le_one₀ (norm_nonneg _) hα)

def Disc (M : Subfield C) (π : C) : Prop := ∀ x ∈ M, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n

variable {M} {π : C} (hπ : π ∈ M) (h0 : π ≠ 0) (h1 : ‖π‖ < 1) (hD : Disc M π)

include h0 hD in
theorem max_eq : maximalIdeal (ball M) = Ideal.span {(⟨π, hπ, h1.le⟩ : ball M)} := by
  ext a
  rw [mem_max, Ideal.mem_span_singleton, dvd_iff]
  refine ⟨fun h => ?_, fun h => h.trans_lt h1⟩
  by_cases ha : (a : C) = 0
  · rw [ha, norm_zero]; exact norm_nonneg _
  obtain ⟨n, hn⟩ := hD a a.2.1 ha
  have hp : 0 < ‖π‖ := norm_pos_iff.mpr h0
  rw [hn] at h ⊢
  have : 0 < n := (zpow_lt_one_iff_right_of_lt_one₀ hp h1).mp h
  exact (zpow_le_zpow_right_of_le_one₀ hp h1.le (show 1 ≤ n by omega)).trans (zpow_one _).le

include hπ h0 h1 hD in
theorem isDVR : IsDiscreteValuationRing (ball M) := by
  have hp : 0 < ‖π‖ := norm_pos_iff.mpr h0
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨⟨π, hπ, h1.le⟩,
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (fun h => h0 (congrArg Subtype.val h))
      (max_eq hπ h0 h1 hD), fun {x} hx => ?_⟩
  obtain ⟨n, hn⟩ := hD x x.2.1 (fun h => hx (Subtype.ext h))
  have : 0 ≤ n := (zpow_le_one_iff_right_of_lt_one₀ hp h1).mp (hn ▸ x.2.2)
  lift n to ℕ using this
  rw [zpow_natCast, ← norm_pow] at hn
  exact ⟨n, associated_of_dvd_dvd ((dvd_iff M _ _).mpr hn.le) ((dvd_iff M _ _).mpr hn.ge)⟩

include hπ h0 h1 hD in
theorem isAdic : IsAdic (maximalIdeal (ball M)) := by
  have hp : 0 < ‖π‖ := norm_pos_iff.mpr h0
  have key : ∀ n : ℕ, ((maximalIdeal (ball M) ^ n : Ideal (ball M)) : Set (ball M)) =
      Metric.closedBall 0 (‖π‖ ^ n) := fun n => by
    ext a
    rw [max_eq hπ h0 h1 hD, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton, dvd_iff,
      Metric.mem_closedBall, Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right, ← norm_pow]
    rfl
  refine isAdic_iff.mpr ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [key]; exact IsUltrametricDist.isOpen_closedBall _ (pow_pos hp n).ne'
  · obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    exact ⟨n, by rw [key]; exact (Metric.closedBall_subset_ball hn).trans h⟩

theorem ball_closed (hc : IsClosed (M : Set C)) : IsClosed (ball M : Set C) :=
  hc.inter (isClosed_le continuous_norm continuous_const)

include hπ h0 h1 hD in
theorem isComplete [CompleteSpace C] (hc : IsClosed (M : Set C)) :
    IsAdicComplete (maximalIdeal (ball M)) (ball M) := by
  have := (ball_closed hc).completeSpace_coe
  exact (isAdic hπ h0 h1 hD).isAdicComplete_iff.mpr ⟨this, inferInstance⟩

theorem exists_max (L : Subfield C) (π : C) (hL : Disc L π) :
    ∃ M, L ≤ M ∧ Maximal (fun M => Disc M π) M := by
  refine zorn_le_nonempty₀ {M | Disc M π} (fun c hc hch y hy => ⟨sSup c, fun x hx hx0 => ?_,
    fun z hz => le_sSup hz⟩) L hL
  obtain ⟨S, hS, hxS⟩ := (Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).mp hx
  exact hc hS x hxS hx0

theorem closed_of_max (hM : Maximal (fun M => Disc M π) M) : IsClosed (M : Set C) := by
  have : Disc M.topologicalClosure π := fun x hx hx0 => by
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (show x ∈ closure (M : Set C) from hx) ‖x‖
      (norm_pos_iff.mpr hx0)
    rw [dist_comm, dist_eq_norm] at hxy
    have e : ‖y‖ = ‖x‖ := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hxy.ne
      rwa [sub_add_cancel, max_eq_right hxy.le] at this
    obtain ⟨n, hn⟩ := hM.1 y hy (by rintro rfl; exact hx0 (by simpa using e.symm))
    exact ⟨n, e ▸ hn⟩
  exact isClosed_of_closure_subset (hM.2 this M.le_topologicalClosure)

theorem res_algClosed [IsAlgClosed C] (hM : Maximal (fun M => Disc M π) M) :
    IsAlgClosed (ResidueField (ball M)) := by
  refine IsAlgClosed.of_exists_root _ fun fb hm hirr => ?_
  obtain ⟨f, hf, hdeg, hfm⟩ := lifts_and_degree_eq_and_monic
    (show fb ∈ lifts (residue (ball M)) from map_surjective _ residue_surjective fb) hm
  have hd0 : f.degree ≠ 0 := by rw [hdeg]; exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective C Subtype.val_injective f hd0
  have hint : IsIntegral (ball M) α := ⟨f, hfm, hα⟩
  have hα1 := norm_le_of_integral M hint
  have unit : ∀ g : (ball M)[X], g.degree < f.degree → g.map (residue _) ≠ 0 → ‖aeval α g‖ = 1 := by
    intro g hg hg0
    have hc : IsCoprime fb (g.map (residue _)) := hirr.coprime_iff_not_dvd.mpr fun hdv =>
      absurd ((degree_le_of_dvd hdv hg0).trans degree_map_le) (not_le.mpr (hdeg ▸ hg))
    obtain ⟨a, b, hab⟩ := hc
    obtain ⟨a, rfl⟩ := map_surjective _ residue_surjective a
    obtain ⟨b, rfl⟩ := map_surjective _ residue_surjective b
    have h2 := norm_aeval_lt M (a * f + b * g - 1)
      (by rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hf, hab]; simp) hα1
    rw [map_sub, map_add, map_mul, map_mul, hα, mul_zero, zero_add, map_one] at h2
    have h3 : ‖aeval α b * aeval α g‖ = 1 := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (x := aeval α b * aeval α g - 1) (y := 1) (by rw [norm_one]; exact h2.ne)
      rwa [sub_add_cancel, norm_one, max_eq_right h2.le] at this
    rw [norm_mul] at h3
    refine le_antisymm (norm_aeval_le M g hα1) ?_
    nlinarith [norm_aeval_le M b hα1, norm_nonneg (aeval α g), norm_nonneg (aeval α b)]
  have hintM : IsIntegral M α := hint.tower_top
  have hDisc : Disc (IntermediateField.adjoin M {α}).toSubfield π := fun x hx hx0 => by
    have hx' : x ∈ Algebra.adjoin M {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintM.isAlgebraic]; exact hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
    obtain ⟨q, rfl⟩ := hx'
    let F := f.map (algebraMap (ball M) M)
    have hF : F.Monic := hfm.map _
    let g := q %ₘ F
    have hgx : aeval α g = aeval α q := aeval_modByMonic_eq_self_of_root (by rw [aeval_map_algebraMap, hα])
    have hg0 : g ≠ 0 := fun h => hx0 (by
      show aeval α q = 0
      rw [← hgx, h, map_zero])
    obtain ⟨i, hi, hmax⟩ := g.support.exists_max_image (fun n => ‖(g.coeff n : C)‖) (support_nonempty.mpr hg0)
    have hc0 : g.coeff i ≠ 0 := mem_support_iff.mp hi
    have hc0' : (g.coeff i : C) ≠ 0 := fun h => hc0 (Subtype.ext h)
    obtain ⟨g0, hg0e, hg0d⟩ := (mem_lifts_and_degree_eq (lifts_of_coeff M (Polynomial.C (g.coeff i)⁻¹ * g) fun n => by
      rw [coeff_C_mul]
      push_cast
      rw [norm_mul, norm_inv, inv_mul_le_one₀ (norm_pos_iff.mpr hc0')]
      by_cases hn : n ∈ g.support
      · exact hmax n hn
      · rw [notMem_support_iff.mp hn]; simp))
    have hco : g0.coeff i = 1 := IsFractionRing.injective (ball M) M (by
      rw [← coeff_map, hg0e, coeff_C_mul, inv_mul_cancel₀ hc0, map_one])
    have hu := unit g0 (by
      rw [hg0d, degree_C_mul (inv_ne_zero hc0), ← hfm.degree_map (algebraMap (ball M) M)]
      exact degree_modByMonic_lt q hF) (fun h => by
      have := congrArg (coeff · i) h
      simp [hco] at this)
    rw [← aeval_map_algebraMap M, hg0e, map_mul, aeval_C, norm_mul, hgx] at hu
    obtain ⟨n, hn⟩ := hM.1 _ (g.coeff i).2 hc0'
    refine ⟨n, ?_⟩
    have e : ‖algebraMap M C (g.coeff i)⁻¹‖ = ‖(g.coeff i : C)‖⁻¹ := by rw [map_inv₀, norm_inv]; rfl
    rw [e, inv_mul_eq_one₀ (norm_ne_zero_iff.mpr hc0')] at hu
    exact hu.symm.trans hn
  have hαM : α ∈ M := hM.2 hDisc (fun y hy => (IntermediateField.adjoin M {α}).algebraMap_mem ⟨y, hy⟩)
    (IntermediateField.mem_adjoin_simple_self M α)
  refine ⟨residue _ ⟨α, hαM, hα1⟩, ?_⟩
  have : f.eval ⟨α, hαM, hα1⟩ = 0 := Subtype.val_injective (by
    exact (aeval_algebraMap_apply C (⟨α, hαM, hα1⟩ : ball M) f).symm.trans hα)
  rw [← hf, eval_map, eval₂_at_apply, this, map_zero]

section Ext

variable (M) (ζ : C)

def ext : Subfield C := (IntermediateField.adjoin M {ζ}).toSubfield

theorem le_ext : M ≤ ext M ζ := fun y hy => (IntermediateField.adjoin M {ζ}).algebraMap_mem ⟨y, hy⟩

instance : Algebra (ball M) (ball (ext M ζ)) :=
  (Subring.inclusion (S := ball M) (T := ball (ext M ζ)) fun _ h => ⟨le_ext M ζ h.1, h.2⟩).toAlgebra

theorem ext_inj : Function.Injective (algebraMap (ball M) (ball (ext M ζ))) :=
  fun _ _ h => Subtype.ext (congrArg (fun t : ball (ext M ζ) => (t : C)) h)

instance : IsScalarTower (ball M) (ball (ext M ζ)) C := IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {M}

include hπ h0 h1 hD in
theorem ext_spec [CompleteSpace C] [CharZero C] (hc : IsClosed (M : Set C)) (hζ : IsIntegral M ζ) :
    Module.Finite (ball M) (ball (ext M ζ)) ∧ IsDiscreteValuationRing (ball (ext M ζ)) := by
  have := isDVR hπ h0 h1 hD
  let K := IntermediateField.adjoin M {ζ}
  have : FiniteDimensional M K := IntermediateField.adjoin.finiteDimensional hζ
  let _ : NontriviallyNormedField M := { (inferInstance : NormedField M) with
    non_trivial := ⟨⟨π, hπ⟩⁻¹, by
      show 1 < ‖π⁻¹‖
      rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1⟩ }
  have : CompleteSpace M := hc.completeSpace_coe
  let _ : Algebra (ball (ext M ζ)) K := (toM (ext M ζ)).toAlgebra
  have : IsScalarTower (ball M) (ball (ext M ζ)) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsIntegralClosure (ball (ext M ζ)) (ball M) K := ⟨fun a b h => Subtype.ext (congrArg (fun t : K => (t : C)) h), fun {x} => by
    constructor
    · intro hx
      exact ⟨⟨x, x.2, norm_le_of_integral M (hx.map (K.val.restrictScalars (ball M)))⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      have hs := spectralNorm_unique_field_norm_ext (K := M) (L := K)
        (f := (NormedField.toAbsoluteValue C).comp (algebraMap K C).injective) (fun _ => rfl) (algebraMap _ K y)
      have hi : IsIntegral M (algebraMap _ K y) := Algebra.IsIntegral.isIntegral _
      have hv : spectralValue (minpoly M (algebraMap _ K y)) ≤ 1 := hs.symm.le.trans y.2.2
      obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic
        (lifts_of_coeff M _ ((spectralValue_le_one_iff (minpoly.monic hi)).mp hv)) (minpoly.monic hi)
      exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap M, hq, minpoly.aeval]⟩⟩
  have hfin := IsIntegralClosure.finite (ball M) M K (ball (ext M ζ))
  have hded := IsIntegralClosure.isDedekindDomain (ball M) M K (ball (ext M ζ))
  have hnf : ¬ IsField (ball (ext M ζ)) := fun hf => by
    have hm : (⟨π, le_ext M ζ hπ, h1.le⟩ : ball (ext M ζ)) ∈ maximalIdeal _ := (mem_max _ _).mpr h1
    rw [isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
    exact h0 (congrArg Subtype.val hm)
  exact ⟨hfin, ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded⟩

theorem ext_gen (hζ : IsIntegral M ζ) (z : ball (ext M ζ)) (hz : (z : C) = ζ)
    (x : FractionRing (ball (ext M ζ))) : ∃ p : (ball M)[X], ∃ d : ball M, d ≠ 0 ∧
    x * algebraMap (ball (ext M ζ)) _ (algebraMap (ball M) (ball (ext M ζ)) d) =
      algebraMap (ball (ext M ζ)) _ (aeval z p) := by
  have hx : iC _ x ∈ Algebra.adjoin M {ζ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic]; exact iC_mem _ x
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨q, hq⟩ := hx
  obtain ⟨d, hd, e⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (ball M)) q
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q, d, nonZeroDivisors.ne_zero hd,
    (iC _).injective ?_⟩
  rw [map_mul, iC_alg, iC_alg, ← hq]
  have h2 : ((aeval z (IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q) : ball (ext M ζ)) : C) =
      aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q) :=
    (aeval_algebraMap_apply C z _).symm.trans (congrArg (fun t => aeval t _) hz)
  rw [h2, ← aeval_map_algebraMap M, e, Algebra.smul_def, map_mul, mul_comm]
  congr 1
  exact (aeval_C ζ (algebraMap (ball M) M d)).symm

end Ext

end Formalism.BasicNotions.Examples₂.Ur
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Ur IsLocalRing

structure UrPkg (l : ℕ) [Fact l.Prime] (O0 : Type) [CommRing O0] : Type 1 where
  O : Type
  [crO : CommRing O]
  [domO : IsDomain O]
  [dvrO : IsDiscreteValuationRing O]
  [algO : Algebra O0 O]
  O_inj : Function.Injective (algebraMap O0 O)
  O_l : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O
  [topO : TopologicalSpace O]
  [trO : IsTopologicalRing O]
  O_adic : IsAdic (IsLocalRing.maximalIdeal O)
  resO_ac : IsAlgClosed (IsLocalRing.ResidueField O)
  O_complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  Ok : ℕ → Type
  [crOk : ∀ k, CommRing (Ok k)]
  [domOk : ∀ k, IsDomain (Ok k)]
  [dvrOk : ∀ k, IsDiscreteValuationRing (Ok k)]
  [algOk : ∀ k, Algebra O (Ok k)]
  Ok_inj : ∀ k, Function.Injective (algebraMap O (Ok k))
  Ok_fin : ∀ k, Module.Finite O (Ok k)
  zk : ∀ k, (Ok k)ˣ
  zk_prim : ∀ k, IsPrimitiveRoot ((zk k : Ok k)) (l ^ k)
  Ok_gen : ∀ k (x : FractionRing (Ok k)), ∃ p : Polynomial O, ∃ d : O, d ≠ 0 ∧
    x * algebraMap (Ok k) (FractionRing (Ok k)) (algebraMap O (Ok k) d) =
      algebraMap (Ok k) (FractionRing (Ok k)) (Polynomial.aeval (zk k : Ok k) p)
  iC : FractionRing O →+* ℂ_[l]
  iC_int : ∀ x : FractionRing O, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range

theorem urPkg_nonempty (l : ℕ) [hl : Fact l.Prime] (O0 : Type) [CommRing O0] [IsDomain O0]
    [IsDiscreteValuationRing O0] (j : O0 →+* ℂ_[l]) (hj : Function.Injective j) (hle : ∀ x, ‖j x‖ ≤ 1)
    (hlt : ∀ x ∈ maximalIdeal O0, ‖j x‖ < 1) : Nonempty (UrPkg l O0) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O0
  have h0 : j ϖ ≠ 0 := (map_ne_zero_iff j hj).mpr hϖ.ne_zero
  have h1 : ‖j ϖ‖ < 1 := hlt ϖ hϖ.not_isUnit
  have hu : ∀ u : O0ˣ, ‖j u‖ = 1 := fun u => le_antisymm (hle _) (by
    have h : ‖j u‖ * ‖j (u⁻¹ : O0ˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
    nlinarith [hle (u⁻¹ : O0ˣ), norm_nonneg (j u), norm_nonneg (j (u⁻¹ : O0ˣ))])
  have hn : ∀ a : O0, a ≠ 0 → ∃ n : ℕ, ‖j a‖ = ‖j ϖ‖ ^ n := fun a ha => by
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    exact ⟨n, by rw [map_mul, norm_mul, hu, one_mul, map_pow, norm_pow]⟩
  let J : FractionRing O0 →+* ℂ_[l] := IsFractionRing.lift hj
  have hJ : ∀ a, J (algebraMap _ _ a) = j a := IsFractionRing.lift_algebraMap hj
  have hL : Disc J.fieldRange (j ϖ) := by
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O0) x
    rw [map_div₀, hJ, hJ] at hx ⊢
    obtain ⟨n, hn1⟩ := hn a (by rintro rfl; simp at hx)
    obtain ⟨m, hm⟩ := hn b (nonZeroDivisors.ne_zero hb)
    exact ⟨n - m, by rw [norm_div, hn1, hm, zpow_sub₀ (norm_ne_zero_iff.mpr h0), zpow_natCast, zpow_natCast]⟩
  obtain ⟨M, hLM, hM⟩ := exists_max _ _ hL
  have hmem : ∀ a, j a ∈ M := fun a => hLM ⟨_, hJ a⟩
  have hc := closed_of_max hM
  have := isDVR (hmem ϖ) h0 h1 hM.1
  let _ : Algebra O0 (ball M) := (j.codRestrict (ball M) fun a => (show j a ∈ ball M from And.intro (hmem a) (hle a))).toAlgebra
  have hζ : ∀ k : ℕ, ∃ ζ : ℂ_[l], IsPrimitiveRoot ζ (l ^ k) := fun k =>
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero k hl.out.ne_zero⟩
    HasEnoughRootsOfUnity.exists_primitiveRoot _ _
  choose ζ hζ using hζ
  have hpos : ∀ k, 0 < l ^ k := fun k => pow_pos hl.out.pos k
  have hint : ∀ k, IsIntegral M (ζ k) := fun k =>
    ⟨Polynomial.X ^ (l ^ k) - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ (hpos k).ne', by
      simp [(hζ k).pow_eq_one]⟩
  have hnorm : ∀ k, ‖ζ k‖ = 1 := fun k =>
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (hpos k).ne').mp (by rw [← norm_pow, (hζ k).pow_eq_one, norm_one])
  let z : ∀ k, ball (ext M (ζ k)) := fun k =>
    ⟨ζ k, IntermediateField.mem_adjoin_simple_self M (ζ k), (hnorm k).le⟩
  have hz : ∀ k, IsUnit (z k) := fun k => (Ur.isUnit_iff _ _).mpr (hnorm k)
  have hext := fun k => ext_spec (hπ := hmem ϖ) (h0 := h0) (h1 := h1) (hD := hM.1) (ζ := ζ k) hc (hint k)
  exact ⟨{ O := ball M
           O_inj := fun a b h => hj (congrArg (fun t : ball M => (t : ℂ_[l])) h)
           O_l := (mem_max M _).mpr (by
             rw [SubringClass.coe_natCast, ← map_natCast (algebraMap ℚ_[l] ℂ_[l])]
             exact (norm_algebraMap' ℂ_[l] (l : ℚ_[l])).trans_lt Padic.norm_p_lt_one)
           O_adic := isAdic (hmem ϖ) h0 h1 hM.1
           resO_ac := res_algClosed hM
           O_complete := isComplete (hmem ϖ) h0 h1 hM.1 hc
           Ok := fun k => ball (ext M (ζ k))
           dvrOk := fun k => (hext k).2
           Ok_inj := fun k => ext_inj M (ζ k)
           Ok_fin := fun k => (hext k).1
           zk := fun k => (hz k).unit
           zk_prim := fun k => IsPrimitiveRoot.of_map_of_injective (f := (ball (ext M (ζ k))).subtype)
             (hζ k) Subtype.val_injective
           Ok_gen := fun k => ext_gen (ζ := ζ k) (hint k) (z k) rfl
           iC := Ur.iC M
           iC_int := Ur.iC_int M }⟩

end Formalism.BasicNotions.Examples₂
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

def DeltaGap {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] (cc : Ω ≃+* Ω) (p : ℕ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (δ : Formalism.ConjugateSelfDual.G H.E Ω →* Multiplicative (ZMod N)),
    IsOpen (δ.ker : Set (Formalism.ConjugateSelfDual.G H.E Ω)) ∧ AntiHom cc δ ∧ RamExactly δ (placesOver H.E p) ∧
    ∀ v ∈ placesOver H.E p, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      Nat.card ((Ine (F := H.E) A).map δ) = 15

structure RcgAt {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] (cc : Ω ≃+* Ω) (l : ℕ) : Type 1 where
  RCG : Finset (HeightOneSpectrum (𝓞 H.E)) → Type
  [grpRCG : ∀ Q, CommGroup (RCG Q)]
  [finRCG : ∀ Q, Fintype (RCG Q)]
  RCG_l : ∀ Q (x : RCG Q), ∃ n : ℕ, x ^ (l ^ n) = 1
  art : ∀ Q, Formalism.ConjugateSelfDual.G H.E Ω →* RCG Q
  art_surj : ∀ Q, Function.Surjective (art Q)
  art_cont : ∀ Q, IsOpen ((art Q).ker : Set (Formalism.ConjugateSelfDual.G H.E Ω))
  art_anti : ∀ Q, AntiHom cc (art Q)
  art_unr : ∀ Q v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, art Q σ = 1
  art_univ : ∀ Q, (∀ v ∈ Q, v ∉ placesOver H.E l) → ∀ (A' : Type) [CommGroup A'] [Finite A'],
    (∀ x : A', ∃ n : ℕ, x ^ (l ^ n) = 1) → ∀ φ : Formalism.ConjugateSelfDual.G H.E Ω →* A',
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G H.E Ω)) → AntiHom cc φ →
    (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, φ σ = 1) →
    ∃ f : RCG Q →* A', f.comp (art Q) = φ
  res : ∀ (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (RCG Q →* RCG Q')
  res_art : ∀ Q Q' (h : Q' ⊆ Q), (res Q Q' h).comp (art Q) = art Q'

attribute [instance] RcgAt.grpRCG RcgAt.finRCG

namespace TwB

variable {R : Ranks} (H : Host R) (F : Type) [Field F] [NumberField F]
  {Ω : Type} [Field Ω] [Algebra H.E Ω] {cc : Ω ≃+* Ω}

def pOf (l : ℕ) : ℕ := if l = H.pde then H.pde' else H.pde

variable (dg : ∀ l : ℕ, DeltaGap H cc (pOf H l))

def NOf (l : ℕ) : ℕ := (dg l).choose

instance (l : ℕ) : NeZero (NOf H dg l) := ⟨(dg l).choose_spec.choose.ne'⟩

def dOf (l : ℕ) : Formalism.ConjugateSelfDual.G H.E Ω →* Multiplicative (ZMod (NOf H dg l)) := (dg l).choose_spec.choose_spec.choose


variable (l : ℕ) [hl : Fact l.Prime]

def zeta : PadicAlgCl l := (exists_prim l (NOf H dg l) (NeZero.pos _)).choose

theorem zeta_prim : IsPrimitiveRoot (zeta H dg l) (NOf H dg l) :=
  (exists_prim l (NOf H dg l) (NeZero.pos _)).choose_spec

def LLf : FinExt l :=
  ⟨KE l H.E ⊔ KE l F ⊔ IntermediateField.adjoin ℚ_[l] {zeta H dg l},
    haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {zeta H dg l}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    inferInstance⟩

theorem E_le : KE l H.E ≤ (LLf H F dg l).1 := le_sup_left.trans le_sup_left
theorem zeta_mem : zeta H dg l ∈ (LLf H F dg l).1 :=
  (le_sup_right : _ ≤ (LLf H F dg l).1) (IntermediateField.mem_adjoin_simple_self _ _)

def delta : Formalism.ConjugateSelfDual.G H.E Ω →* (↥(OL (LLf H F dg l)))ˣ :=
  (muHom (LLf H F dg l) (zeta_prim H dg l) (zeta_mem H F dg l)).comp (dOf H dg l)

set_option synthInstance.maxHeartbeats 400000 in

def br [IsAlgClosure H.E Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    LocBridge l H.E Ω (Dec (F := H.E) A) ↥(OL (LLf H F dg l)) :=
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap H.E Ω).injective
  haveI : IsAlgClosure ℚ Ω := isAlgClosureQ H.E Ω
  bridgeOf (exists_emb (l := l) A hA).choose_spec (LLf H F dg l) fun τ x =>
    E_le H F dg l (conj_mem_KE (jE (E := H.E) (exists_emb (l := l) A hA).choose) τ x)

end TwB

end Formalism.BasicNotions.Examples₂
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB


namespace TwB

section Settings

variable (F : Type) [Field F] [NumberField F]

abbrev TwT : Type :=
  Σ l : Nat.Primes, {w : HeightOneSpectrum (𝓞 F) // (((l : ℕ) : ℕ) : 𝓞 F) ∈ w.asIdeal}

instance (i : TwT F) : Fact ((i.1 : ℕ)).Prime := ⟨i.1.2⟩

def phi (i : TwT F) : F →+* PadicAlgCl (i.1 : ℕ) := (exists_embAt i.2.1 i.2.2).choose

end Settings

section OneLL

variable {l : ℕ} [hl : Fact l.Prime] {F : Type} [Field F] (LL : FinExt l) (φ : F →+* PadicAlgCl l)
  (hφ : ∀ x, φ x ∈ LL.1)

def phiL : F →+* ↥LL.1 := φ.codRestrict LL.1.toSubfield hφ


def embF : F →+* FractionRing ↥(OL LL) := (toFrac LL).comp (phiL LL φ hφ)


def pkg : UrPkg l ↥(OL LL) :=
  (urPkg_nonempty l ↥(OL LL) (toC LL) (toC_injective LL)
    (fun x => (norm_toC LL x).le.trans (nrm_le LL x))
    (fun x hx => by rw [norm_toC]; exact (mem_max LL x).mp hx)).some

end OneLL

end TwB

end Formalism.BasicNotions.Examples₂
end
end
