import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalVal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerOrd
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MemMaxUnramifiedOutsideOfMemLevelOfField
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ExistsUnitsToIdelesEqOfIdelesSumInvEqZero

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace PicInf

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

variable (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]

omit [FiniteDimensional K.1 L] in

theorem exists_mem_pow_eq_of_dvd_log_valuation (Lq : IntermediateField K.1 ℚ̄) [FiniteDimensional K.1 Lq]
    [NumberField Lq]
    (hLqle : Lq ≤ maxUnramifiedOutside K.1 ℚ̄ S) (M : ℕ) (hM : M ≠ 0)
    (hMS : ∀ v ∉ S, ((M : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (π : Lqˣ)
    (hπ : ∀ W : HeightOneSpectrum (𝓞 Lq), (M : ℤ) ∣ WithZero.log (W.valuation Lq (π : Lq))) :
    ∃ α : ℚ̄, α ∈ maxUnramifiedOutside K.1 ℚ̄ S ∧ α ^ M = ((π : Lq) : ℚ̄) := by
  have hLu : IsUnramifiedOutside S Lq := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hLqle
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((π : Lq) : ℚ̄) (Nat.pos_of_ne_zero hM)
  have hαint : IsIntegral Lq α := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hM) ?_
    rw [hα]
    exact isIntegral_algebraMap (x := (π : Lq))
  let E : IntermediateField Lq ℚ̄ := IntermediateField.adjoin Lq {α}
  have : FiniteDimensional Lq E := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField E := NumberField.of_module_finite Lq E
  have hβ : IntermediateField.AdjoinSimple.gen Lq α ^ M = algebraMap Lq E (π : Lq) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hα]
    rfl
  have hEu : IsUnramifiedOutside (placesOver S) E := by
    intro w hw
    refine Global.Kummer.isUnramifiedIn_of_pow_eq π hβ (adjoin_gen_eq_top Lq α) w ?_ (hπ w)
    intro hmem
    have hv : underPlace (F := K.1) w ∉ S := fun h => hw (mem_placesOver_iff.2 h)
    apply hMS _ hv
    change ((M : ℕ) : 𝓞 K.1) ∈ Ideal.comap (algebraMap (𝓞 K.1) (𝓞 Lq)) w.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hmem
  have hEF := (isUnramifiedOutside_restrictScalars_iff S hLu E).2 hEu
  have : FiniteDimensional K.1 (E.restrictScalars K.1) := FiniteDimensional.trans K.1 Lq E
  exact ⟨α, le_maxUnramifiedOutside S hEF (IntermediateField.mem_adjoin_simple_self Lq α), hα⟩

theorem exists_pow_eq_of_dvd_log_valuation (M : ℕ) (hM : M ≠ 0)
    (hMS : ∀ v ∉ S, ((M : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (π : (levelOfField L).1ˣ)
    (hπ : ∀ W : HeightOneSpectrum (𝓞 (levelOfField L).1),
      (M : ℤ) ∣ WithZero.log (W.valuation (levelOfField L).1 (π : (levelOfField L).1))) :
    ∃ α : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ,
      ((α : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ^ M = ((π : (levelOfField L).1) : ℚ̄) := by
  have hLqf : FiniteDimensional K.1 (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) :=
    LinearEquiv.finiteDimensional (L.equivMap (maxUnramifiedOutside K.1 ℚ̄ S).val).toLinearEquiv
  have hLqle : L.map (maxUnramifiedOutside K.1 ℚ̄ S).val ≤ maxUnramifiedOutside K.1 ℚ̄ S := by
    rintro z ⟨w, -, rfl⟩
    exact w.2
  have : NumberField (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) := NumberField.of_module_finite K.1 _
  obtain ⟨α, hαS, hα⟩ := exists_mem_pow_eq_of_dvd_log_valuation
    (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) hLqle M hM hMS π hπ
  have hα0 : (⟨α, hαS⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ≠ 0 := by
    intro h
    have h' : α = 0 := congrArg Subtype.val h
    rw [h', zero_pow hM] at hα
    exact (π : (levelOfField L).1ˣ).ne_zero (Subtype.ext hα.symm)
  exact ⟨Units.mk0 _ hα0, hα⟩

end

end PicInf

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace PicInf

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal
  FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

variable (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]

omit [FiniteDimensional K.1 L] in

theorem ordEmb_galUnitsHom_eq {v : HeightOneSpectrum (𝓞 K.1)}
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S)
    (x : galUnramifiedOutside K.1 ℚ̄ S) (x' : ℚ̄ →ₐ[K.1] ℚ̄)
    (hx' : ∀ z : maxUnramifiedOutside K.1 ℚ̄ S, x' z = ((x z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄))
    (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    ordEmb S ι hv (Additive.ofMul (galUnitsHom K.1 _ x y)) = ordEmbFun (ι.comp x') (maxUnitsToUnits S y) := by
  obtain ⟨N, hKN, hgal, hNS, hyN⟩ := exists_galois_level S (y : maxUnramifiedOutside K.1 ℚ̄ S).2
  have := hKN
  have : Normal K.1 N.1 := hgal.to_normal
  let gN : N.1 ≃ₐ[K.1] N.1 := x'.restrictNormal' N.1
  have hgN : ∀ z : N.1, ((gN z : N.1) : ℚ̄) = x' z := fun z => AlgHom.restrictNormal_commutes x' N.1 z
  have hw := placeOfEmbedding_eq_inv_smul ι gN (ι.comp x') fun z => by
    rw [AlgHom.comp_apply, hgN]
  have hmem : ((maxUnitsToUnits S (galUnitsHom K.1 _ x y) : ℚ̄ˣ) : ℚ̄) ∈ N.1 := by
    change ((x (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1
    rw [← hx', ← hgN ⟨_, hyN⟩]
    exact (gN _).2
  have e1 := valuation_placeOfEmbedding_eq S ι hv N hNS _ hmem
  have e2 := valuation_placeOfEmbedding_eq S (ι.comp x') hv N hNS (maxUnitsToUnits S y) hyN
  rw [hw, valuation_inv_smul_placesOver] at e2
  have key : (placeOfEmbedding ι N).1.valuation N.1 ⟨_, hmem⟩ =
      (placeOfEmbedding ι N).1.valuation N.1 (gN ⟨_, hyN⟩) := by
    congr 1
    apply Subtype.ext
    change ((x (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
      ((gN ⟨_, hyN⟩ : N.1) : ℚ̄)
    rw [hgN, hx']
  have := WithZero.exp_injective (e1.symm.trans (key.trans e2))
  rw [ordEmb_apply]
  omega

omit [FiniteDimensional K.1 L] in

theorem placeOfEmbedding_congr_of_eqOn {v : HeightOneSpectrum (𝓞 K.1)} (F : FiniteSubfield) [Fact (K ≤ F)]
    (ι₁ ι₂ : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (h : ∀ z : F.1, ι₁ z = ι₂ z) :
    placeOfEmbedding ι₁ F = placeOfEmbedding ι₂ F :=
  (eq_placeOfEmbedding ι₁ F (completionEmbedding ι₂ F) fun z => by
    rw [completionEmbedding_algebraMap]
    exact (h z).symm).symm

omit [FiniteDimensional K.1 L] in

theorem exists_algEquiv_of_placeOfEmbedding_eq {v : HeightOneSpectrum (𝓞 K.1)} (F : FiniteSubfield)
    [Fact (K ≤ F)] (ι₁ ι₂ : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (h : placeOfEmbedding ι₁ F = placeOfEmbedding ι₂ F) :
    ∃ σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      ∀ z : F.1, ι₁ z = σ (ι₂ z) := by
  have key : ∀ w : PlacesOver F.1 v, w = placeOfEmbedding ι₁ F →
      ∃ c : w.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1),
        ∀ z : F.1, c (algebraMap F.1 _ z) = ι₁ z := by
    rintro w rfl
    exact ⟨completionEmbedding ι₁ F, completionEmbedding_algebraMap ι₁ F⟩
  obtain ⟨c₁, hc₁⟩ := key (placeOfEmbedding ι₂ F) h.symm
  have := finiteDimensional_adicCompletion_placesOver (K := K) (E := F) (placeOfEmbedding ι₂ F)
  let c₂ := completionEmbedding ι₂ F
  let : Algebra ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) := c₂.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a => (c₂.commutes a).symm
  have : Algebra.IsAlgebraic ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion K.1) _
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := v.adicCompletion K.1)
    (L := (placeOfEmbedding ι₂ F).1.adicCompletion F.1) (M := AlgebraicClosure (v.adicCompletion K.1))
    (E := AlgebraicClosure (v.adicCompletion K.1)) c₁
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun z => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  have e := DFunLike.congr_fun hφ (algebraMap F.1 _ z)
  change φ (c₂ (algebraMap F.1 _ z)) = c₁ (algebraMap F.1 _ z) at e
  rw [← hc₁, ← e, completionEmbedding_algebraMap]

theorem placeOfEmbedding_comp_eq_iff [Normal K.1 L] (ιs : LocalEmbeddings K)
    (v v' : HeightOneSpectrum (𝓞 K.1)) (x : galUnramifiedOutside K.1 ℚ̄ S) (x' : ℚ̄ →ₐ[K.1] ℚ̄)
    (hx' : ∀ z : maxUnramifiedOutside K.1 ℚ̄ S, x' z = ((x z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) :
    (placeOfEmbedding ((ιs.fin v').comp x') (levelOfField L)).1 =
        (placeOfEmbedding (ιs.fin v) (levelOfField L)).1 ↔
      v' = v ∧ ∃ z ∈ (decompHomS (v.adicCompletion K.1) S (ιs.fin v)).range,
        ∃ u ∈ L.fixingSubgroup, x = z * u := by
  constructor
  · intro h
    have hvv : v' = v := by
      have h1 := (placeOfEmbedding ((ιs.fin v').comp x') (levelOfField L)).2
      have h2 := (placeOfEmbedding (ιs.fin v) (levelOfField L)).2
      rw [h] at h1
      exact HeightOneSpectrum.ext (h1.over.trans h2.over.symm)
    subst hvv
    refine ⟨rfl, ?_⟩
    obtain ⟨σ, hσ⟩ := exists_algEquiv_of_placeOfEmbedding_eq (levelOfField L) ((ιs.fin v').comp x')
      (ιs.fin v') (Subtype.ext h)
    refine ⟨decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ, ⟨σ, rfl⟩,
      (decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ)⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro w hw
    have hxw : x w = decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w := by
      apply Subtype.val_injective
      apply (ιs.fin v').injective
      have h1 := hσ ⟨(w : ℚ̄), (mem_levelOfField L).2 ⟨w, hw, rfl⟩⟩
      have h2 := decompHom_apply (Kv := v'.adicCompletion K.1)
        ((ιs.fin v').comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ w
      change (ιs.fin v') (x' (w : ℚ̄)) = σ ((ιs.fin v') (w : ℚ̄)) at h1
      rw [hx'] at h1
      change (ιs.fin v') ((x w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
        (ιs.fin v') ((decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
      rw [h1]
      exact h2.symm
    rw [AlgEquiv.mul_apply, hxw, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · rintro ⟨rfl, z, ⟨σ, rfl⟩, u, hu, rfl⟩
    refine congrArg Subtype.val ?_
    rw [← placeOfEmbedding_comp_algEquiv (ιs.fin v') σ]
    apply placeOfEmbedding_congr_of_eqOn
    rintro ⟨zz, hzz⟩
    obtain ⟨w, hw, rfl⟩ := (mem_levelOfField L).1 hzz
    change (ιs.fin v') (x' (w : ℚ̄)) = σ ((ιs.fin v') (w : ℚ̄))
    have e1 : (decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ * u) w =
        decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ (u w) :=
      AlgEquiv.mul_apply _ _ w
    have e2 : u w = w := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hu w hw
    have e3 : x' (w : ℚ̄) = ((decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w :
        maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
      (hx' w).trans (congrArg Subtype.val (e1.trans (congrArg _ e2)))
    exact (congrArg (ιs.fin v') e3).trans (decompHom_apply (Kv := v'.adicCompletion K.1)
      ((ιs.fin v').comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ w)

end

end PicInf

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K)

def gsDecomp (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S}) :
    Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →*
      galUnramifiedOutside K.1 ℚ̄ S :=
  decompHomS (v.1.adicCompletion K.1) S (ιs.fin v.1)

theorem continuous_gsDecomp (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S}) :
    Continuous (gsDecomp K S ιs v) :=
  continuous_decompHomS (Kv := v.1.adicCompletion K.1) S _

abbrev gsDiv (A : Type) [AddCommGroup A] : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S) :=
  divFunRep (gsDecomp K S ιs) A

instance isDiscreteRep_gsDiv (A : Type) [AddCommGroup A] : IsDiscreteRep (gsDiv K S ιs A) :=
  have := galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S
  isDiscreteRep_divFunRep _ _

theorem isLocallyConstant_galUnitsHom_apply (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    IsLocallyConstant fun x : galUnramifiedOutside K.1 ℚ̄ S => galUnitsHom K.1 _ x y := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho := isOpen_stabilizer (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (Additive.ofMul y)
  have hn := (ho.preimage (continuous_const_mul x⁻¹)).mem_nhds
    (show x⁻¹ * x ∈ (stabilizer (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ (Additive.ofMul y) :
      Set (galUnramifiedOutside K.1 ℚ̄ S)) by rw [inv_mul_cancel]; exact one_mem _)
  filter_upwards [hn] with x' hx'
  have hs' : galUnitsHom K.1 _ (x⁻¹ * x') y = y := congrArg Additive.toMul ((mem_stabilizer _ _ _).1 hx')
  have : x' = x * (x⁻¹ * x') := by rw [mul_inv_cancel_left]
  rw [this, map_mul]
  change galUnitsHom K.1 _ x (galUnitsHom K.1 _ (x⁻¹ * x') y) = _
  rw [hs']

def unitsDivFun (y : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : divFun (gsDecomp K S ιs) ℤ :=
  ⟨fun v x => ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x y.toMul)), by
    refine ⟨(finite_ordEmb_ne_zero S ιs y.toMul).subset fun v hv => ?_, fun v => ⟨?_, fun σ x => ?_⟩⟩
    · by_contra h
      exact hv (funext fun σ => by_contra fun hσ => h ⟨σ, hσ⟩)
    · exact (isLocallyConstant_galUnitsHom_apply K S y.toMul).comp _
    · show ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ (gsDecomp K S ιs v σ * x) y.toMul)) =
        ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x y.toMul))
      rw [map_mul]
      exact ordEmb_decompHomS S (ιs.fin v.1) v.2 σ _⟩


def unitsDivHom : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ →+ divFun (gsDecomp K S ιs) ℤ where
  toFun := unitsDivFun K S ιs
  map_zero' := Subtype.ext (funext fun v => funext fun x => by
    change ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x 1)) = 0
    rw [map_one, ofMul_one, map_zero])
  map_add' y z := Subtype.ext (funext fun v => funext fun x => by
    change ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x (y.toMul * z.toMul))) =
      ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x y.toMul)) +
        ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x z.toMul))
    rw [map_mul, ofMul_mul, map_add])

def unitsDiv : galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ⟶ gsDiv K S ιs ℤ :=
  Rep.ofHom ⟨uliftIntLinearMap (unitsDivHom K S ιs), fun σ => LinearMap.ext fun y =>
    Subtype.ext (funext fun v => funext fun x => by
      change ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x (galUnitsHom K.1 _ σ y.toMul))) =
        ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ (x * σ) y.toMul))
      rw [map_mul]
      rfl)⟩

theorem coe_unitsDiv_hom_apply (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    (((unitsDiv K S ιs).hom (Additive.ofMul y) : divFun (gsDecomp K S ιs) ℤ) :
      {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ) =
      fun v x => ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x y)) :=
  rfl

theorem divFunEval_unitsDiv (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})
    (y : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    (divFunEval (gsDecomp K S ιs) ℤ v).hom ((unitsDiv K S ιs).hom y) = ordEmb S (ιs.fin v.1) v.2 y := by
  rw [divFunEval_hom_apply]
  change ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ 1 y.toMul)) = _
  rw [map_one]
  rfl

theorem unitsDiv_eq_zero_iff (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    (unitsDiv K S ιs).hom (Additive.ofMul y) = 0 ↔ y ∈ sUnitsMax K.1 ℚ̄ S := by
  rw [mem_sUnitsMax_iff_ordEmb S ιs]
  constructor
  · intro h v hv σ
    have := congrFun (congrFun (congrArg Subtype.val h) ⟨v, hv⟩) σ
    exact this
  · intro h
    exact Subtype.ext (funext fun v => funext fun x => h v.1 v.2 x)

theorem sUnitsSubmodule_le_ker_unitsDiv :
    sUnitsSubmodule K.1 ℚ̄ S ≤ LinearMap.ker (unitsDiv K S ιs).hom.toLinearMap := fun y hy =>
  (unitsDiv_eq_zero_iff K S ιs y.toMul).2 hy

def sUnitsQuotDiv : galUnitsModSUnits K.1 ℚ̄ S ⟶ gsDiv K S ιs ℤ :=
  Rep.ofHom ⟨(sUnitsSubmodule K.1 ℚ̄ S).liftQ (unitsDiv K S ιs).hom.toLinearMap
      (sUnitsSubmodule_le_ker_unitsDiv K S ιs), fun σ => by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro y
    exact congrArg (fun f : _ →ₗ[ULift ℤ] _ => f y) ((unitsDiv K S ιs).hom.isIntertwining' σ)⟩

theorem sUnitsQuotSequence_g_comp_sUnitsQuotDiv :
    (sUnitsQuotSequence K.1 ℚ̄ S).g ≫ sUnitsQuotDiv K S ιs = unitsDiv K S ιs := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  rfl

theorem sUnitsQuotDiv_injective : Function.Injective (sUnitsQuotDiv K S ιs).hom := by
  have h : LinearMap.ker (sUnitsQuotDiv K S ιs).hom.toLinearMap = ⊥ :=
    Submodule.ker_liftQ_eq_bot _ _ _ fun y hy => (unitsDiv_eq_zero_iff K S ιs y.toMul).1 hy
  exact LinearMap.ker_eq_bot.1 h

def principalDivSubmodule : Submodule (ULift.{0} ℤ) (gsDiv K S ιs ℤ) :=
  LinearMap.range (sUnitsQuotDiv K S ιs).hom.toLinearMap

theorem principalDivSubmodule_le_comap (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    principalDivSubmodule K S ιs ≤ (principalDivSubmodule K S ιs).comap ((gsDiv K S ιs ℤ).ρ σ) := by
  rintro _ ⟨p, rfl⟩
  refine ⟨(galUnitsModSUnits K.1 ℚ̄ S).ρ σ p, ?_⟩
  exact congrArg (fun f : _ →ₗ[ULift ℤ] _ => f p) ((sUnitsQuotDiv K S ιs).hom.isIntertwining' σ)

def picInfRep : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S) :=
  (gsDiv K S ιs ℤ).quotient (principalDivSubmodule K S ιs) (principalDivSubmodule_le_comap K S ιs)

instance isDiscreteRep_picInfRep : IsDiscreteRep (picInfRep K S ιs) :=
  isDiscreteRep_quotient _ _ _

def picQuot : gsDiv K S ιs ℤ ⟶ picInfRep K S ιs :=
  Rep.mkQ _ (principalDivSubmodule K S ιs) (principalDivSubmodule_le_comap K S ιs)

theorem picQuot_surjective : Function.Surjective (picQuot K S ιs).hom :=
  Submodule.mkQ_surjective _

def picSequence : ShortComplex (Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) :=
  ShortComplex.mk (sUnitsQuotDiv K S ιs) (picQuot K S ιs) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro p
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨p, rfl⟩)

theorem picSequence_shortExact : (picSequence K S ιs).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro f hf
    obtain ⟨p, hp⟩ := (Submodule.Quotient.mk_eq_zero _).1 hf
    exact ⟨p, hp⟩
  mono_f := (Rep.mono_iff_injective _).2 (sUnitsQuotDiv_injective K S ιs)
  epi_g := (Rep.epi_iff_surjective _).2 (picQuot_surjective K S ιs)

namespace PicInf

variable {K S ιs}

def Good (ℓ : ℕ) (f : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ) : Prop :=
  ∃ N : ℕ, N.Coprime ℓ ∧ ∃ y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ∀ v x,
    ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ x y)) = N * f v x

theorem good_zero (ℓ : ℕ) : Good (S := S) (ιs := ιs) ℓ 0 :=
  ⟨1, Nat.coprime_one_left ℓ, 1, fun v x => by
    rw [map_one, ofMul_one, map_zero, Pi.zero_apply, Pi.zero_apply, mul_zero]⟩

theorem Good.add {ℓ : ℕ}
    {f g : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ}
    (hf : Good (ιs := ιs) ℓ f) (hg : Good (ιs := ιs) ℓ g) : Good (ιs := ιs) ℓ (f + g) := by
  obtain ⟨N₁, h₁, y₁, hy₁⟩ := hf
  obtain ⟨N₂, h₂, y₂, hy₂⟩ := hg
  refine ⟨N₁ * N₂, Nat.Coprime.mul_left h₁ h₂, y₁ ^ N₂ * y₂ ^ N₁, fun v x => ?_⟩
  rw [map_mul, map_pow, map_pow, ofMul_mul, ofMul_pow, ofMul_pow, map_add, map_nsmul, map_nsmul,
    hy₁, hy₂, Pi.add_apply, Pi.add_apply, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem Good.zsmul {ℓ : ℕ} {f : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ}
    (hf : Good (ιs := ιs) ℓ f) (c : ℤ) : Good (ιs := ιs) ℓ (c • f) := by
  obtain ⟨N, h, y, hy⟩ := hf
  refine ⟨N, h, y ^ c, fun v x => ?_⟩
  rw [map_zpow, ofMul_zpow, map_zsmul, hy, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem good_sum {ℓ : ℕ} {ι : Type} (T : Finset ι)
    (f : ι → {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ)
    (hf : ∀ i ∈ T, Good (ιs := ιs) ℓ (f i)) : Good (ιs := ιs) ℓ (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact good_zero ℓ
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a T)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem Good.translate {ℓ : ℕ}
    {f : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ}
    (hf : Good (ιs := ιs) ℓ f) (g : galUnramifiedOutside K.1 ℚ̄ S) :
    Good (ιs := ιs) ℓ (fun v x => f v (x * g)) := by
  obtain ⟨N, h, y, hy⟩ := hf
  refine ⟨N, h, galUnitsHom K.1 _ g y, fun v x => ?_⟩
  rw [← hy v (x * g), map_mul]
  rfl

end PicInf

namespace PicInf

variable {K S ιs}

open Classical in

noncomputable def zuInd (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})
    (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) : galUnramifiedOutside K.1 ℚ̄ S → ℤ :=
  fun g => if ∃ z ∈ (gsDecomp K S ιs v).range, ∃ u ∈ U, g = z * u then 1 else 0

open Classical in

theorem good_single_of_base {ℓ : ℕ} (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})
    (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) [hUn : U.Normal]
    (hU : IsOpen (U : Set (galUnramifiedOutside K.1 ℚ̄ S)))
    (hbase : Good (ιs := ιs) ℓ (Pi.single v (zuInd (ιs := ιs) v U)))
    (φ : galUnramifiedOutside K.1 ℚ̄ S → ℤ) (hφU : ∀ x, ∀ u ∈ U, φ (x * u) = φ x)
    (hφZ : ∀ z ∈ (gsDecomp K S ιs v).range, ∀ x, φ (z * x) = φ x) :
    Good (ιs := ιs) ℓ (Pi.single v φ) := by
  have : Finite (galUnramifiedOutside K.1 ℚ̄ S ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  have := Fintype.ofFinite (galUnramifiedOutside K.1 ℚ̄ S ⧸ U)
  set Z := (gsDecomp K S ιs v).range with hZ
  induction' hn : (Finset.univ.filter (fun q : galUnramifiedOutside K.1 ℚ̄ S ⧸ U =>
    ∃ x : galUnramifiedOutside K.1 ℚ̄ S, (x : galUnramifiedOutside K.1 ℚ̄ S ⧸ U) = q ∧ φ x ≠ 0)).card
    using Nat.strong_induction_on with n ih generalizing φ
  by_cases h0 : ∀ x, φ x = 0
  · have : φ = 0 := funext h0
    rw [this, Pi.single_zero]
    exact good_zero ℓ
  simp only [not_forall] at h0
  obtain ⟨x₀, hx₀⟩ := h0

  obtain ⟨χ, hχ⟩ : ∃ χ : galUnramifiedOutside K.1 ℚ̄ S → ℤ,
      χ = fun g => zuInd (ιs := ιs) v U (g * x₀⁻¹) := ⟨_, rfl⟩
  have hmemD : ∀ g, (∃ z ∈ Z, ∃ u ∈ U, g * x₀⁻¹ = z * u) ↔ ∃ z ∈ Z, ∃ u ∈ U, g = z * x₀ * u := by
    intro g
    constructor
    · rintro ⟨z, hz, u, hu, h⟩
      refine ⟨z, hz, x₀⁻¹ * u * x₀, hUn.conj_mem' u hu x₀, ?_⟩
      calc g = g * x₀⁻¹ * x₀ := by group
        _ = _ := by rw [h]; group
    · rintro ⟨z, hz, u, hu, rfl⟩
      refine ⟨z, hz, x₀ * u * x₀⁻¹, hUn.conj_mem u hu x₀, by group⟩
  have hφD : ∀ z ∈ Z, ∀ u ∈ U, φ (z * x₀ * u) = φ x₀ := by
    intro z hz u hu
    rw [hφU _ u hu, hφZ z hz]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : galUnramifiedOutside K.1 ℚ̄ S → ℤ, ψ = fun g => φ g - φ x₀ * χ g := ⟨_, rfl⟩
  have hχ1 : ∀ g, χ g = if ∃ z ∈ Z, ∃ u ∈ U, g = z * x₀ * u then 1 else 0 := by
    intro g
    simp only [hχ, zuInd, ← hZ, hmemD g]
  have hsplit : Pi.single v φ = Pi.single v ψ + (φ x₀) • fun v' x =>
      (Pi.single v (zuInd (ιs := ιs) v U) :
        {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ) v' (x * x₀⁻¹) := by
    funext v' x
    by_cases hv : v' = v
    · subst hv
      simp [hψ, hχ]
    · simp [Pi.single_eq_of_ne hv]
  rw [hsplit]
  refine Good.add ?_ ((hbase.translate x₀⁻¹).zsmul (φ x₀))

  refine ih _ ?_ ψ ?_ ?_ rfl
  · rw [← hn]
    apply Finset.card_lt_card
    refine ⟨fun q hq => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      obtain ⟨x, rfl, hx⟩ := hq
      refine ⟨x, rfl, fun hφx => hx ?_⟩
      have : χ x = 0 := by
        rw [hχ1]
        split_ifs with hD
        · obtain ⟨z, hz, u, hu, rfl⟩ := hD
          exact absurd (hφD z hz u hu ▸ hφx) hx₀
        · rfl
      simp [hψ, hφx, this]
    · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ _, x₀, rfl, hx₀⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      obtain ⟨x, hx, hψx⟩ := this
      obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, x = x₀ * u := by
        have h := QuotientGroup.eq.1 hx
        refine ⟨x₀⁻¹ * x, ?_, by group⟩
        have := U.inv_mem h
        rwa [mul_inv_rev, inv_inv] at this
      apply hψx
      have hD : ∃ z ∈ Z, ∃ u' ∈ U, x₀ * u = z * x₀ * u' := ⟨1, Z.one_mem, u, hu, by rw [one_mul]⟩
      simp only [hψ, hχ1, if_pos hD, hφU x₀ u hu, mul_one, sub_self]
  · intro x u hu
    have hAB : (∃ z ∈ Z, ∃ u' ∈ U, x * u = z * x₀ * u') ↔ ∃ z ∈ Z, ∃ u' ∈ U, x = z * x₀ * u' := by
      constructor
      · rintro ⟨z, hz, u', hu', h⟩
        refine ⟨z, hz, u' * u⁻¹, U.mul_mem hu' (U.inv_mem hu), ?_⟩
        rw [← mul_assoc, ← h, mul_inv_cancel_right]
      · rintro ⟨z, hz, u', hu', rfl⟩
        exact ⟨z, hz, u' * u, U.mul_mem hu' hu, mul_assoc _ _ _⟩
    simp only [hψ, hφU x u hu, hχ1, hAB]
  · intro z hz x
    have hAB : (∃ z' ∈ Z, ∃ u' ∈ U, z * x = z' * x₀ * u') ↔ ∃ z' ∈ Z, ∃ u' ∈ U, x = z' * x₀ * u' := by
      constructor
      · rintro ⟨z', hz', u', hu', h⟩
        refine ⟨z⁻¹ * z', Z.mul_mem (Z.inv_mem hz) hz', u', hu', ?_⟩
        simp only [mul_assoc] at h ⊢
        rw [← h, inv_mul_cancel_left]
      · rintro ⟨z', hz', u', hu', rfl⟩
        exact ⟨z * z', Z.mul_mem hz hz', u', hu', by simp only [mul_assoc]⟩
    simp only [hψ, hφZ z hz, hχ1, hAB]

end PicInf

namespace PicInf

variable {K S ιs}

theorem exists_normal_level (φ : galUnramifiedOutside K.1 ℚ̄ S → ℤ) (hφ : IsLocallyConstant φ) :
    ∃ L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S), FiniteDimensional K.1 L ∧ Normal K.1 L ∧
      ∀ x, ∀ u ∈ L.fixingSubgroup, φ (x * u) = φ x := by
  have := (galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S).1
  obtain ⟨V, hV, hVφ⟩ := exists_mem_nhds_one_forall_mul_eq hφ
  obtain ⟨E, hEf, hEn, hEV⟩ := (krullTopology_mem_nhds_one_iff_of_normal K.1 _ V).1 hV
  exact ⟨E, hEf, hEn, fun x u hu => hVφ x u (hEV hu)⟩

open Classical in

theorem eq_sum_single (f : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ)
    (T : Finset {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S}) (hT : ∀ v ∉ T, f v = 0) :
    f = ∑ v ∈ T, Pi.single v (f v) := by
  funext v
  rw [Finset.sum_apply, Finset.sum_pi_single]
  split_ifs with h
  · rfl
  · exact hT v h

open Classical in

theorem good_single {ℓ : ℕ}
    (hbase : ∀ (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})
      (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L] [Normal K.1 L],
      Good (ιs := ιs) ℓ (Pi.single v (zuInd (ιs := ιs) v L.fixingSubgroup)))
    (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S}) (φ : galUnramifiedOutside K.1 ℚ̄ S → ℤ)
    (hφ : IsLocallyConstant φ) (hZ : ∀ σ x, φ (gsDecomp K S ιs v σ * x) = φ x) :
    Good (ιs := ιs) ℓ (Pi.single v φ) := by
  obtain ⟨L, hLf, hLn, hL⟩ := exists_normal_level _ hφ
  have : IsGalois K.1 L := ⟨⟩
  have : IsGalois K.1 (maxUnramifiedOutside K.1 ℚ̄ S) := isGalois_maxUnramifiedOutside S
  exact good_single_of_base v L.fixingSubgroup (L.fixingSubgroup_isOpen) (hbase v L) φ hL
    (fun z hz x => by
      obtain ⟨σ, rfl⟩ := hz
      exact hZ σ x)

end PicInf

namespace PicInf

variable {K S ιs}

def levelWith (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]
    (α : ℚ̄) : FiniteSubfield :=
  ⟨(levelOf K α).1 ⊔ (levelOfField L).1, inferInstance⟩

instance fact_le_levelWith (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S))
    [FiniteDimensional K.1 L] (α : ℚ̄) : Fact (K ≤ levelWith L α) :=
  ⟨le_trans (fact_le_levelOf α).out (le_sup_left (a := (levelOf K α).1))⟩

theorem levelWith_le (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]
    {α : ℚ̄} (hα : α ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    ∀ z ∈ (levelWith L α).1, z ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have h1 : (levelOf K α).1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ := by
    refine sup_le (fun z hz => ?_) ?_
    · exact (maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem ⟨z, hz⟩
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact hα
  have h2 : (levelOfField L).1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ :=
    fun z hz => mem_maxUnramifiedOutside_of_mem_levelOfField L hz
  exact fun z hz => (sup_le h1 h2) hz

theorem ordEmbFun_root (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]
    {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S)
    (M : ℕ) (π : (levelOfField L).1ˣ) (α : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (hα : ((α : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ^ M = ((π : (levelOfField L).1) : ℚ̄)) :
    (M : ℤ) * ordEmbFun ι (maxUnitsToUnits S α) =
      -WithZero.log ((placeOfEmbedding ι (levelOfField L)).1.valuation (levelOfField L).1
        (π : (levelOfField L).1)) := by
  set a : ℚ̄ := ((α : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) with ha
  have haS : a ∈ maxUnramifiedOutside K.1 ℚ̄ S := (α : maxUnramifiedOutside K.1 ℚ̄ S).2

  let πq : ℚ̄ˣ := Units.map ((levelOfField L).1.val.toRingHom.toMonoidHom) π
  have hπq : (πq : ℚ̄) = ((π : (levelOfField L).1) : ℚ̄) := rfl
  have hπL : (πq : ℚ̄) ∈ (levelOfField L).1 := (π : (levelOfField L).1).2
  have e1 := valuation_placeOfEmbedding_eq S ι hv (levelOfField L)
    (fun z hz => mem_maxUnramifiedOutside_of_mem_levelOfField L hz) πq hπL

  have hF := levelWith_le L haS
  have haF : ((maxUnitsToUnits S α : ℚ̄ˣ) : ℚ̄) ∈ (levelWith L a).1 :=
    (le_sup_left (a := (levelOf K a).1)) (mem_levelOf a)
  have hπF : (πq : ℚ̄) ∈ (levelWith L a).1 := (le_sup_right (a := (levelOf K a).1)) hπL
  have e2 := valuation_placeOfEmbedding_eq S ι hv (levelWith L a) hF (maxUnitsToUnits S α) haF
  have e3 := valuation_placeOfEmbedding_eq S ι hv (levelWith L a) hF πq hπF
  have hpow : (⟨(πq : ℚ̄), hπF⟩ : (levelWith L a).1) = ⟨((maxUnitsToUnits S α : ℚ̄ˣ) : ℚ̄), haF⟩ ^ M := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    exact hα.symm
  rw [hpow, map_pow, e2, ← WithZero.exp_nsmul] at e3
  have e4 := congrArg WithZero.log e3
  rw [WithZero.log_exp, WithZero.log_exp] at e4
  have e5 : -WithZero.log ((placeOfEmbedding ι (levelOfField L)).1.valuation (levelOfField L).1
      (π : (levelOfField L).1)) = ordEmbFun ι πq := by
    have : (⟨(πq : ℚ̄), hπL⟩ : (levelOfField L).1) = (π : (levelOfField L).1) := rfl
    rw [← this, e1, WithZero.log_exp, neg_neg]
  rw [e5]
  simp only [smul_neg, nsmul_eq_mul] at e4
  linarith

end PicInf

namespace PicInf

variable {K S ιs}

open Classical in

theorem good_base (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})
    (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L] [Normal K.1 L] :
    Good (ιs := ιs) ℓ (Pi.single v (zuInd (ιs := ιs) v L.fixingSubgroup)) := by
  obtain ⟨a, N, hN, hh⟩ := Nat.exists_eq_pow_mul_and_not_dvd (classNumber_ne_zero (levelOfField L).1) ℓ
    hℓ.one_lt.ne'
  have hval : ∀ W : HeightOneSpectrum (𝓞 (levelOfField L).1),
      W.valuation (levelOfField L).1
        (Global.SUnit.placeUnit (placeOfEmbedding (ιs.fin v.1) (levelOfField L)).1 : (levelOfField L).1) =
        if W = (placeOfEmbedding (ιs.fin v.1) (levelOfField L)).1 then
          WithZero.exp (-(classNumber (levelOfField L).1 : ℤ)) else 1 := by
    intro W
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, Global.SUnit.valuationOfNeZero_placeUnit]
    split_ifs <;> rfl
  have hMS : ∀ w ∉ S, ((ℓ ^ a : ℕ) : 𝓞 K.1) ∉ w.asIdeal := by
    intro w hw hmem
    rw [Nat.cast_pow] at hmem
    exact hw (hS w (w.isPrime.mem_of_pow_mem _ hmem))
  have hdvd : ∀ W : HeightOneSpectrum (𝓞 (levelOfField L).1),
      ((ℓ ^ a : ℕ) : ℤ) ∣ WithZero.log (W.valuation (levelOfField L).1
        (Global.SUnit.placeUnit (placeOfEmbedding (ιs.fin v.1) (levelOfField L)).1 : (levelOfField L).1)) := by
    intro W
    rw [hval W]
    split_ifs
    · rw [WithZero.log_exp, hh]
      exact ⟨-(N : ℤ), by push_cast; ring⟩
    · rw [WithZero.log_one]
      exact dvd_zero _
  obtain ⟨α, hα⟩ := exists_pow_eq_of_dvd_log_valuation L (ℓ ^ a) (pow_ne_zero a hℓ.ne_zero) hMS
    (Global.SUnit.placeUnit (placeOfEmbedding (ιs.fin v.1) (levelOfField L)).1) hdvd
  refine ⟨N, (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hN)), α, fun v' x => ?_⟩

  let x' : ℚ̄ →ₐ[K.1] ℚ̄ := ((x : maxUnramifiedOutside K.1 ℚ̄ S ≃ₐ[K.1] maxUnramifiedOutside K.1 ℚ̄ S).liftNormal ℚ̄)
  have hx' : ∀ z : maxUnramifiedOutside K.1 ℚ̄ S, x' z = ((x z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
    fun z => AlgEquiv.liftNormal_commutes _ _ z
  rw [ordEmb_galUnitsHom_eq (ιs.fin v'.1) v'.2 x x' hx' α]
  have hroot := ordEmbFun_root L ((ιs.fin v'.1).comp x') v'.2 (ℓ ^ a)
    (Global.SUnit.placeUnit (placeOfEmbedding (ιs.fin v.1) (levelOfField L)).1) α hα
  rw [hval] at hroot
  have hiff := placeOfEmbedding_comp_eq_iff L ιs v.1 v'.1 x x' hx'
  have hM0 : ((ℓ ^ a : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero a hℓ.ne_zero
  by_cases hpl : (placeOfEmbedding ((ιs.fin v'.1).comp x') (levelOfField L)).1 =
      (placeOfEmbedding (ιs.fin v.1) (levelOfField L)).1
  · rw [if_pos hpl, WithZero.log_exp, neg_neg, hh] at hroot
    obtain ⟨hvv, z, hz, u, hu, hxzu⟩ := hiff.1 hpl
    have hvv' : v' = v := Subtype.ext hvv
    subst hvv'
    rw [Pi.single_eq_same, zuInd, if_pos ⟨z, hz, u, hu, hxzu⟩, mul_one]
    push_cast at hroot
    have hM0' : ((ℓ : ℤ)) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast hℓ.ne_zero)
    exact mul_left_cancel₀ hM0' hroot
  · rw [if_neg hpl, WithZero.log_one, neg_zero] at hroot
    have h0 := (mul_eq_zero.1 hroot).resolve_left hM0
    rw [h0]
    by_cases hvv : v' = v
    · subst hvv
      rw [Pi.single_eq_same, zuInd, if_neg, mul_zero]
      exact fun hx => hpl (hiff.2 ⟨rfl, hx⟩)
    · rw [Pi.single_eq_of_ne hvv, Pi.zero_apply, mul_zero]

end PicInf

open PicInf Classical in

theorem exists_coprime_smul_picInfRep (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (m : (picInfRep K S ιs).V) : ∃ N : ℕ, N.Coprime ℓ ∧ N • m = 0 := by
  obtain ⟨f, rfl⟩ := picQuot_surjective K S ιs m
  have hgood : Good (ιs := ιs) ℓ (f : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} →
      galUnramifiedOutside K.1 ℚ̄ S → ℤ) := by
    have hf := (mem_divFun _ _).1 f.2
    rw [eq_sum_single (f : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ)
      hf.1.toFinset (fun v hv => by simpa using hv)]
    refine good_sum _ _ fun v _ => ?_
    exact good_single (fun v L _ _ => good_base ℓ hℓ hS v L) v _ (hf.2 v).1 (hf.2 v).2
  obtain ⟨N, hN, y, hy⟩ := hgood
  refine ⟨N, hN, ?_⟩
  have hdiv : N • f = (unitsDiv K S ιs).hom (Additive.ofMul y) := by
    apply Subtype.ext
    funext v x
    have e := congrFun (congrFun (AddSubgroup.coe_nsmul _ f N) v) x
    refine e.trans ?_
    rw [coe_unitsDiv_hom_apply]
    change N • (f : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} → galUnramifiedOutside K.1 ℚ̄ S → ℤ) v x = _
    rw [nsmul_eq_mul]
    exact (hy v x).symm
  rw [← map_nsmul, hdiv, ← sUnitsQuotSequence_g_comp_sUnitsQuotDiv]
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨(sUnitsQuotSequence K.1 ℚ̄ S).g.hom (Additive.ofMul y), rfl⟩

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem eq_zero_of_coprime_nsmul_eq_zero {A : Type*} [AddCommGroup A] {ℓ N k : ℕ} (hN : N.Coprime ℓ)
    {x : A} (h1 : N • x = 0) (h2 : ℓ ^ k • x = 0) : x = 0 := by
  have hd : addOrderOf x ∣ Nat.gcd N (ℓ ^ k) :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h1) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  rw [Nat.Coprime.gcd_eq_one (hN.pow_right k), Nat.dvd_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.1 hd

theorem exists_primary_map_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) {ℓ : ℕ}
    (hℓ : ℓ.Prime) {y : A} (hy : IsOfFinAddOrder y) {k : ℕ} (hk : ℓ ^ k • f y = 0) :
    ∃ y' : A, (∃ j : ℕ, ℓ ^ j • y' = 0) ∧ f y' = f y := by
  set M := addOrderOf y
  have hM : M ≠ 0 := (IsOfFinAddOrder.addOrderOf_pos hy).ne'
  set a := M.factorization ℓ
  set N := M / ℓ ^ a
  have hMN : ℓ ^ a * N = M := Nat.ordProj_mul_ordCompl_eq_self M ℓ
  have hN : Nat.Coprime N ℓ := (Nat.coprime_ordCompl hℓ hM).symm
  set a' := max a k
  have hc : IsCoprime (N : ℤ) ((ℓ ^ a' : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (hN.pow_right a')
  obtain ⟨u, w, huw⟩ := hc
  have hyN : (ℓ ^ a' * N) • y = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.1
    change M ∣ ℓ ^ a' * N
    rw [← hMN]
    exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow ℓ (le_max_left a k)) N
  have hfk : ℓ ^ a' • f y = 0 := by
    have ha' : a' = (a' - k) + k := (Nat.sub_add_cancel (le_max_right a k)).symm
    rw [ha', pow_add, mul_smul, hk, smul_zero]
  refine ⟨(u * N) • y, ⟨a', ?_⟩, ?_⟩
  · calc ℓ ^ a' • (u * N) • y = ((ℓ ^ a' : ℕ) : ℤ) • (u * N) • y := (Nat.cast_smul_eq_nsmul ℤ _ _).symm
      _ = u • ((ℓ ^ a' * N : ℕ) : ℤ) • y := by
        rw [smul_smul, smul_smul]
        congr 1
        push_cast
        ring
      _ = 0 := by rw [Nat.cast_smul_eq_nsmul, hyN, smul_zero]
  · rw [map_zsmul]
    have h2 : (w * ((ℓ ^ a' : ℕ) : ℤ)) • f y = 0 := by
      rw [mul_smul, Nat.cast_smul_eq_nsmul, hfk, smul_zero]
    calc (u * N) • f y = (u * N + w * ((ℓ ^ a' : ℕ) : ℤ)) • f y - (w * ((ℓ ^ a' : ℕ) : ℤ)) • f y := by
          rw [add_smul, add_sub_cancel_right]
      _ = f y := by rw [huw, one_smul, h2, sub_zero]

section LES

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃]
  (hS : S.ShortExact)

include hS in

theorem exists_δ_eq_of_cohomologyMap_f_eq_zero (i j : ℕ) (hij : i + 1 = j) (x : cohomology S.X₁ j)
    (hx : (cohomologyMap S.f j).hom x = 0) : ∃ y : cohomology S.X₃ i, (δ hS i j hij).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS i j hij) x hx

include hS in

theorem exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero (i : ℕ) (x : cohomology S.X₂ i)
    (hx : (cohomologyMap S.g i).hom x = 0) : ∃ y : cohomology S.X₁ i, (cohomologyMap S.f i).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS i) x hx

include hS in

theorem exists_cohomologyMap_g_eq_of_δ_eq_zero (i j : ℕ) (hij : i + 1 = j) (x : cohomology S.X₃ i)
    (hx : (δ hS i j hij).hom x = 0) : ∃ y : cohomology S.X₂ i, (cohomologyMap S.g i).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hS i j hij) x hx

include hS in

theorem eq_zero_of_mem_range_δ_of_coprime (i j : ℕ) (hij : i + 1 = j) {x : cohomology S.X₁ j}
    (hx : ∃ y : cohomology S.X₃ i, (δ hS i j hij).hom y = x) (ℓ : ℕ)
    (hM : ∀ y : cohomology S.X₃ i, ∃ N : ℕ, N.Coprime ℓ ∧ N • y = 0) (k : ℕ) (hk : ℓ ^ k • x = 0) :
    x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨N, hN, hNy⟩ := hM y
  refine eq_zero_of_coprime_nsmul_eq_zero hN ?_ hk
  rw [← map_nsmul, hNy, map_zero]

omit hS in

theorem cohomologyMapAlong_cohomologyMap_apply {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] {C : Rep.{u} k H} [IsDiscreteRep C] (g : A ⟶ B) (f : Rep.res φ B ⟶ C) (n : ℕ)
    (x : cohomology A n) :
    (cohomologyMapAlong φ hφ f n).hom ((cohomologyMap g n).hom x) =
      (cohomologyMapAlong φ hφ ((Rep.resFunctor φ).map g ≫ f) n).hom x := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap]
  have := cohomologyMapAlong_comp (φ := MonoidHom.id G) (hφ := continuous_id) g φ hφ f n
  exact (congrArg (fun m => m.hom x) this).symm

end LES

section Instances

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K)

instance compactSpace_galUnramifiedOutside_finiteSubfield :
    CompactSpace (galUnramifiedOutside K.1 ℚ̄ S) :=
  (galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S).1

instance totallyDisconnectedSpace_galUnramifiedOutside_finiteSubfield :
    TotallyDisconnectedSpace (galUnramifiedOutside K.1 ℚ̄ S) :=
  (galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S).2.2

instance isDiscreteRep_picSequence_X₁ : IsDiscreteRep (picSequence K S ιs).X₁ :=
  inferInstanceAs (IsDiscreteRep (sUnitsQuotSequence K.1 ℚ̄ S).X₃)

instance isDiscreteRep_picSequence_X₂ : IsDiscreteRep (picSequence K S ιs).X₂ :=
  inferInstanceAs (IsDiscreteRep (gsDiv K S ιs ℤ))

instance isDiscreteRep_picSequence_X₃ : IsDiscreteRep (picSequence K S ιs).X₃ :=
  inferInstanceAs (IsDiscreteRep (picInfRep K S ιs))

instance isDiscreteRep_galUnitsModSUnits_finiteSubfield :
    IsDiscreteRep (galUnitsModSUnits K.1 ℚ̄ S) :=
  isDiscreteRep_sUnitsQuotSequence_X₃ K.1 ℚ̄ S

end Instances

section SUnits

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

abbrev sUnitsH2Map : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₁ 2 ⟶
    cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₂ 2 :=
  cohomologyMap (sUnitsQuotSequence K.1 ℚ̄ S).f 2

variable (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 1000000 in
include hℓ hS in
theorem eq_zero_of_sUnitsH2Map_eq_zero_of_localEmbeddings (ιs : LocalEmbeddings K)
    (y : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₁ 2) (k : ℕ)
    (hy : ℓ ^ k • y = 0) (h : (sUnitsH2Map K S).hom y = 0) : y = 0 := by
  have hE := sUnitsQuotSequence_shortExact K.1 ℚ̄ S
  obtain ⟨p, rfl⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hE 1 2 rfl y h
  have hp : ℓ ^ k • p = 0 := by
    obtain ⟨z, hz⟩ := exists_cohomologyMap_g_eq_of_δ_eq_zero hE 1 2 rfl (ℓ ^ k • p)
      (by rw [map_nsmul]; exact hy)
    have : Subsingleton (cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₂ 1) :=
      subsingleton_cohomology_one_galUnits
    rw [← hz, Subsingleton.elim z 0, map_zero]
  have hP := picSequence_shortExact K S ιs
  have hD : Subsingleton (cohomology (picSequence K S ιs).X₂ 1) :=
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_one_divFunRep_int (gsDecomp K S ιs))
  obtain ⟨q, hq⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hP 0 1 rfl
    (p : cohomology (picSequence K S ιs).X₁ 1) (Subsingleton.elim _ _)
  have hp0 : (p : cohomology (picSequence K S ιs).X₁ 1) = 0 :=
    eq_zero_of_mem_range_δ_of_coprime hP 0 1 rfl ⟨q, hq⟩ ℓ
      (fun y => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ιs) ℓ
        (exists_coprime_smul_picInfRep K S ιs ℓ hℓ hS) 0 y) k hp
  have hp0' : p = 0 := hp0
  rw [hp0', map_zero]

include hℓ hS in

theorem eq_zero_of_sUnitsH2Map_eq_zero (y : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₁ 2) (k : ℕ)
    (hy : ℓ ^ k • y = 0) (h : (sUnitsH2Map K S).hom y = 0) : y = 0 :=
  eq_zero_of_sUnitsH2Map_eq_zero_of_localEmbeddings K S ℓ hℓ hS (nonempty_localEmbeddings K).some y k hy h

end SUnits

section Local

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K)

def gsQuotMor : galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ⟶ galUnitsModSUnits K.1 ℚ̄ S :=
  (sUnitsQuotSequence K.1 ℚ̄ S).g

theorem gsQuotMor_comp_sUnitsQuotDiv : gsQuotMor K S ≫ sUnitsQuotDiv K S ιs = unitsDiv K S ιs :=
  sUnitsQuotSequence_g_comp_sUnitsQuotDiv K S ιs

theorem gsQuotMor_sUnitsToUnits_apply (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    (cohomologyMap (gsQuotMor K S) 2).hom
      ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y) = 0 := by
  have h := cohomologyMap_f_comp_g (S := sUnitsQuotSequence K.1 ℚ̄ S) 2
  exact congrArg (fun m => ModuleCat.Hom.hom m y) h

theorem exists_sUnitsToUnits_eq_of_gsQuotMor (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2)
    (hx : (cohomologyMap (gsQuotMor K S) 2).hom x = 0) :
    ∃ y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2,
      (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y = x :=
  exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero (sUnitsQuotSequence_shortExact K.1 ℚ̄ S) 2 x hx

theorem exists_δ_pic_eq (p : cohomology (galUnitsModSUnits K.1 ℚ̄ S) 2)
    (hp : (cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom p = 0) :
    ∃ r : cohomology (picInfRep K S ιs) 1, (δ (picSequence_shortExact K S ιs) 1 2 rfl).hom r = p :=
  exists_δ_eq_of_cohomologyMap_f_eq_zero (picSequence_shortExact K S ιs) 1 2 rfl p hp

theorem divFunEval_sUnitsQuotDiv_apply (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    (cohomologyMapAlong (gsDecomp K S ιs v) (continuous_gsDecomp K S ιs v)
        (divFunEval (gsDecomp K S ιs) ℤ v) 2).hom
      ((cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom ((cohomologyMap (gsQuotMor K S) 2).hom x)) =
      (cohomologyMapAlong (decompHomS (v.1.adicCompletion K.1) S (ιs.fin v.1))
        (continuous_decompHomS (Kv := v.1.adicCompletion K.1) S (ιs.fin v.1))
        (ordEmbMor S (ιs.fin v.1) v.2) 2).hom x := by
  have e : (cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom ((cohomologyMap (gsQuotMor K S) 2).hom x) =
      (cohomologyMap (unitsDiv K S ιs) 2).hom x := by
    rw [← gsQuotMor_comp_sUnitsQuotDiv K S ιs, cohomologyMap_comp]
    rfl
  have hm : (Rep.resFunctor (gsDecomp K S ιs v)).map (unitsDiv K S ιs) ≫
      divFunEval (gsDecomp K S ιs) ℤ v = (ordEmbMor S (ιs.fin v.1) v.2 :
        Rep.res (gsDecomp K S ιs v) (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) ⟶
          trivRep Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) ℤ) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    exact (divFunEval_unitsDiv K S ιs v y).trans (ordEmbMor_hom_apply S (ιs.fin v.1) v.2 y).symm
  refine (congrArg (fun z => (cohomologyMapAlong (gsDecomp K S ιs v) (continuous_gsDecomp K S ιs v)
    (divFunEval (gsDecomp K S ιs) ℤ v) 2).hom z) e).trans ?_
  exact (cohomologyMapAlong_cohomologyMap_apply (gsDecomp K S ιs v) (continuous_gsDecomp K S ιs v)
    (unitsDiv K S ιs) (divFunEval (gsDecomp K S ιs) ℤ v) 2 x).trans
    (congrArg (fun m => (cohomologyMapAlong (gsDecomp K S ιs v) (continuous_gsDecomp K S ιs v) m 2).hom x) hm)

theorem gsLocalRes_sUnitsToUnits_eq_zero (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2)
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) :
    (gsLocalRes S (ιs.fin v) 2).hom
      (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2
        ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y)) = 0 := by
  refine (gsLocalRes_eq_zero_iff S (ιs.fin v) hv _).2 ?_
  refine (divFunEval_sUnitsQuotDiv_apply K S ιs ⟨v, hv⟩ _).symm.trans ?_
  refine (congrArg (fun z => (cohomologyMapAlong (gsDecomp K S ιs ⟨v, hv⟩)
    (continuous_gsDecomp K S ιs ⟨v, hv⟩) (divFunEval (gsDecomp K S ιs) ℤ ⟨v, hv⟩) 2).hom
      ((cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom z)) (gsQuotMor_sUnitsToUnits_apply K S y)).trans ?_
  exact (congrArg (fun z => (cohomologyMapAlong (gsDecomp K S ιs ⟨v, hv⟩)
    (continuous_gsDecomp K S ιs ⟨v, hv⟩) (divFunEval (gsDecomp K S ιs) ℤ ⟨v, hv⟩) 2).hom z)
      (LinearMap.map_zero _)).trans (LinearMap.map_zero _)

variable (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem exists_sUnitsToUnits_eq (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2)
    (k : ℕ) (hx : ℓ ^ k • x = 0)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 K.1), v ∉ S → (gsLocalRes S (ιs.fin v) 2).hom
      (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2 x) = 0) :
    ∃ y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2,
      (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y = x := by
  have hd : (cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom ((cohomologyMap (gsQuotMor K S) 2).hom x) = 0 :=
    eq_zero_of_divFunEval_eq_zero (gsDecomp K S ιs) (continuous_gsDecomp K S ιs)
      ((cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom ((cohomologyMap (gsQuotMor K S) 2).hom x))
      fun v => (divFunEval_sUnitsQuotDiv_apply K S ιs v x).trans
        ((gsLocalRes_eq_zero_iff S (ιs.fin v.1) v.2 x).1 (hloc v.1 v.2))
  have hpk : ℓ ^ k • (cohomologyMap (gsQuotMor K S) 2).hom x = 0 := by
    rw [← map_nsmul, hx, map_zero]
  have hp0 : (cohomologyMap (gsQuotMor K S) 2).hom x = 0 :=
    eq_zero_of_mem_range_δ_of_coprime (picSequence_shortExact K S ιs) 1 2 rfl
      (exists_δ_pic_eq K S ιs _ hd) ℓ
      (fun z => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ιs) ℓ
        (exists_coprime_smul_picInfRep K S ιs ℓ hℓ hS) 1 z) k hpk
  exact exists_sUnitsToUnits_eq_of_gsQuotMor K S x hp0

end Local

section Brauer

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem eq_zero_of_sUnitsBrauer_eq_zero (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) (k : ℕ)
    (hy : ℓ ^ k • y = 0) (h : sUnitsBrauer K S y = 0) : y = 0 := by
  refine eq_zero_of_sUnitsH2Map_eq_zero K S ℓ hℓ hS y k hy ?_
  have h1 := gsBrauerInfl_injective K S (h.trans (map_zero _).symm)
  exact (cohomologyULiftIntAddEquiv _ 2).injective (h1.trans (map_zero _).symm)

variable (ιs : LocalEmbeddings K)

theorem brauerLocal_sUnitsBrauer_inr (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2)
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) : brauerLocal ιs (sUnitsBrauer K S y) (.inr v) = 0 :=
  (brauerLocal_gsBrauerInfl_inr K S ιs v _).trans (gsLocalRes_sUnitsToUnits_eq_zero K S ιs y v hv)

include hℓ hS in

theorem exists_sUnitsBrauer_eq_iff (x : cohomology (unitsLimitRep K) 2) (k : ℕ) (hx : ℓ ^ k • x = 0) :
    (∃ y, sUnitsBrauer K S y = x) ↔
      ∀ v : HeightOneSpectrum (𝓞 K.1), v ∉ S → brauerLocal ιs x (.inr v) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ v hv
    exact brauerLocal_sUnitsBrauer_inr K S ιs y v hv
  · intro hloc
    obtain ⟨z, rfl⟩ := exists_gsBrauerInfl_eq K S ℓ hℓ hS x k hx
    have hz0 : ℓ ^ k • z = 0 := gsBrauerInfl_injective K S
      ((map_nsmul (gsBrauerInfl K S 2).hom (ℓ ^ k) z).trans (hx.trans (map_zero _).symm))
    have hz : ℓ ^ k • (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).symm z = 0 :=
      (map_nsmul (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).symm
        (ℓ ^ k) z).symm.trans ((congrArg _ hz0).trans (map_zero _))
    obtain ⟨y, hy⟩ := exists_sUnitsToUnits_eq K S ιs ℓ hℓ hS _ k hz fun v hv =>
      (congrArg (gsLocalRes S (ιs.fin v) 2).hom (AddEquiv.apply_symm_apply _ z)).trans
        ((brauerLocal_gsBrauerInfl_inr K S ιs v z).symm.trans (hloc v hv))
    exact ⟨y, (congrArg (fun t => (gsBrauerInfl K S 2).hom
      ((cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) t)) hy).trans
        (congrArg (gsBrauerInfl K S 2).hom (AddEquiv.apply_symm_apply _ z))⟩

def brauerPrimaryOutside : AddSubgroup (cohomology (unitsLimitRep K) 2) where
  carrier := {x | (∃ k : ℕ, ℓ ^ k • x = 0) ∧
    ∀ v : HeightOneSpectrum (𝓞 K.1), v ∉ S → brauerLocal ιs x (.inr v) = 0}
  add_mem' {a b} ha hb := by
    obtain ⟨⟨m, hm⟩, ha'⟩ := ha
    obtain ⟨⟨n, hn⟩, hb'⟩ := hb
    refine ⟨⟨m + n, ?_⟩, fun v hv => ?_⟩
    · have h1 : ℓ ^ (m + n) • a = 0 := by rw [pow_add, mul_comm, mul_smul, hm, smul_zero]
      have h2 : ℓ ^ (m + n) • b = 0 := by rw [pow_add, mul_smul, hn, smul_zero]
      rw [smul_add, h1, h2, add_zero]
    · rw [map_add, DFinsupp.add_apply, ha' v hv, hb' v hv, add_zero]
  zero_mem' := ⟨⟨0, smul_zero _⟩, fun v _ => by rw [map_zero, DFinsupp.zero_apply]⟩
  neg_mem' {a} ha := by
    obtain ⟨⟨m, hm⟩, ha'⟩ := ha
    refine ⟨⟨m, by rw [smul_neg, hm, neg_zero]⟩, fun v hv => ?_⟩
    rw [map_neg, DFinsupp.neg_apply, ha' v hv, neg_zero]

def sUnitsBrauerPrimary :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ →+ brauerPrimaryOutside K S ℓ ιs :=
  ((sUnitsBrauer K S).comp (AddCommGroup.primaryComponent _ ℓ).subtype).codRestrict _ fun y => by
    obtain ⟨k, hk⟩ := y.2
    refine ⟨⟨k, ?_⟩, fun v hv => brauerLocal_sUnitsBrauer_inr K S ιs y.1 v hv⟩
    exact (map_nsmul (sUnitsBrauer K S) (ℓ ^ k) y.1).symm.trans ((congrArg _ hk).trans (map_zero _))

theorem coe_sUnitsBrauerPrimary_apply (y : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ) :
    (sUnitsBrauerPrimary K S ℓ ιs y : cohomology (unitsLimitRep K) 2) = sUnitsBrauer K S y :=
  rfl

set_option maxHeartbeats 2000000 in
include hℓ hS in

theorem sUnitsBrauerPrimary_bijective : Function.Bijective (sUnitsBrauerPrimary K S ℓ ιs) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · obtain ⟨m, hm⟩ := a.2
    obtain ⟨n, hn⟩ := b.2
    have hab' : sUnitsBrauer K S (a.1 - b.1) = 0 := by
      rw [map_sub, ← coe_sUnitsBrauerPrimary_apply, ← coe_sUnitsBrauerPrimary_apply, hab, sub_self]
    have h1 : ℓ ^ (m + n) • a.1 = 0 := by rw [pow_add, mul_comm (ℓ ^ m), mul_smul, hm, smul_zero]
    have h2 : ℓ ^ (m + n) • b.1 = 0 := by rw [pow_add, mul_smul, hn, smul_zero]
    have hk : ℓ ^ (m + n) • (a.1 - b.1) = 0 := by rw [smul_sub, h1, h2, sub_zero]
    exact Subtype.ext (sub_eq_zero.1 (eq_zero_of_sUnitsBrauer_eq_zero K S ℓ hℓ hS _ (m + n) hk hab'))
  · obtain ⟨⟨k, hk⟩, hx⟩ := x.2
    obtain ⟨y, hy⟩ := (exists_sUnitsBrauer_eq_iff K S ℓ hℓ hS ιs x.1 k hk).2 hx
    obtain ⟨y', ⟨j, hj⟩, hy'⟩ := exists_primary_map_eq (sUnitsBrauer K S) hℓ
      (isTorsion_cohomology _ (by norm_num) y) (k := k) (by rw [hy]; exact hk)
    exact ⟨⟨y', j, hj⟩, Subtype.ext (hy'.trans hy)⟩

noncomputable def sUnitsBrauerPrimaryEquiv :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ ≃+ brauerPrimaryOutside K S ℓ ιs :=
  AddEquiv.ofBijective (sUnitsBrauerPrimary K S ℓ ιs) (sUnitsBrauerPrimary_bijective K S ℓ hℓ hS ιs)

end Brauer

section Local

open DirectSum

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (ιs : LocalEmbeddings K)

def localPrimaryKernel : AddSubgroup (⨁ v : Place K.1, localGaloisCohomology K 2 v) where
  carrier := {t | (∃ k : ℕ, ℓ ^ k • t = 0) ∧ (∀ v : HeightOneSpectrum (𝓞 K.1), v ∉ S → t (.inr v) = 0) ∧
    sumPlaceInv K t = 0}
  add_mem' {a b} ha hb := by
    obtain ⟨⟨m, hm⟩, ha', ha''⟩ := ha
    obtain ⟨⟨n, hn⟩, hb', hb''⟩ := hb
    refine ⟨⟨m + n, ?_⟩, fun v hv => ?_, ?_⟩
    · have h1 : ℓ ^ (m + n) • a = 0 := by rw [pow_add, mul_comm (ℓ ^ m), mul_smul, hm, smul_zero]
      have h2 : ℓ ^ (m + n) • b = 0 := by rw [pow_add, mul_smul, hn, smul_zero]
      rw [smul_add, h1, h2, add_zero]
    · rw [DFinsupp.add_apply, ha' v hv, hb' v hv, add_zero]
    · rw [map_add, ha'', hb'', add_zero]
  zero_mem' := ⟨⟨0, smul_zero _⟩, fun v _ => DFinsupp.zero_apply _, map_zero _⟩
  neg_mem' {a} ha := by
    obtain ⟨⟨m, hm⟩, ha', ha''⟩ := ha
    refine ⟨⟨m, by rw [smul_neg, hm, neg_zero]⟩, fun v hv => ?_, ?_⟩
    · rw [DFinsupp.neg_apply, ha' v hv, neg_zero]
    · rw [map_neg, ha'', neg_zero]

def brauerLocalPrimary : brauerPrimaryOutside K S ℓ ιs →+ localPrimaryKernel K S ℓ :=
  ((brauerLocal ιs).comp (brauerPrimaryOutside K S ℓ ιs).subtype).codRestrict _ fun x => by
    obtain ⟨⟨k, hk⟩, hx⟩ := x.2
    refine ⟨⟨k, ?_⟩, hx, brauerSumInv_eq_zero ιs x.1⟩
    exact (map_nsmul (brauerLocal ιs) (ℓ ^ k) x.1).symm.trans ((congrArg _ hk).trans (map_zero _))

theorem brauerLocalPrimary_bijective : Function.Bijective (brauerLocalPrimary K S ℓ ιs) := by
  refine ⟨fun a b hab => Subtype.ext (brauerLocal_injective ιs (congrArg Subtype.val hab)), fun t => ?_⟩
  obtain ⟨⟨k, hk⟩, ht, ht'⟩ := t.2
  obtain ⟨x, hx⟩ := (sumPlaceInv_eq_zero_iff ιs t.1).1 ht'
  have hxk : ℓ ^ k • x = 0 := brauerLocal_injective ιs
    ((map_nsmul (brauerLocal ιs) (ℓ ^ k) x).trans ((congrArg _ hx).trans (hk.trans (map_zero _).symm)))
  refine ⟨⟨x, ⟨k, hxk⟩, fun v hv => (congrArg (fun s => s (.inr v)) hx).trans (ht v hv)⟩, Subtype.ext hx⟩

set_option maxHeartbeats 2000000 in

noncomputable def sUnitsH2PrimaryEquiv :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ ≃+ localPrimaryKernel K S ℓ :=
  (sUnitsBrauerPrimaryEquiv K S ℓ hℓ hS ιs).trans
    (AddEquiv.ofBijective (brauerLocalPrimary K S ℓ ιs) (brauerLocalPrimary_bijective K S ℓ ιs))

theorem coe_sUnitsH2PrimaryEquiv_apply
    (y : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ) :
    (sUnitsH2PrimaryEquiv K S ℓ hℓ hS ιs y : ⨁ v : Place K.1, localGaloisCohomology K 2 v) =
      brauerLocal ιs (sUnitsBrauer K S y) :=
  rfl

end Local

end

end GroundTheory.ProfCoh
end
