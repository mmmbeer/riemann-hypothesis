import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import GroundTheory.GlobalFields.GlobalArtinMap.Kernel
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
import ReciprocityTheory.GaloisValuations.Global
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace PositivityTheory.FamInh

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

omit [IsAlgClosure K Ω] in

theorem exists_place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  let P : Ideal (𝓞 L) := (primeBelow (F := L) A).under (𝓞 L)
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x => Iff.rfl
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, ⟨hu⟩⟩

theorem mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := K) A := by
  refine ⟨hσ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den K A hx
  have hσx : A.valuation (σ x) ≤ 1 := by
    rw [A.valuation_le_one_iff, apply_mem_iff_of_mem_Dec hσ, ← A.valuation_le_one_iff]
    exact hx
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s * (σ x - x) = (σ t - t) - (σ s - s) * σ x := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s * (σ x - x)) < 1 := by
    rw [key]
    apply Valuation.map_sub_lt _ (h t ht)
    rw [Valuation.map_mul]
    calc A.valuation (σ s - s) * A.valuation (σ x) ≤ A.valuation (σ s - s) * 1 := mul_le_mul_right hσx _
      _ < 1 := by rw [mul_one]; exact h s hs
  rwa [Valuation.map_mul, hs1, one_mul] at hv

variable [IsGalois K L]

omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem coe_res_smul (σ : G K Ω) (x : 𝓞 L) :
    algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) :=
  AlgEquiv.restrictNormal_commutes σ L (x : L)

omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem res_restrictScalars (g : Ω ≃ₐ[L] Ω) : AlgEquiv.restrictNormalHom L (g.restrictScalars K : G K Ω) = 1 := by
  ext x
  apply (algebraMap L Ω).injective
  exact (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L x).trans (g.commutes x)

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem res_mem_stabilizer (hw : IsPlaceOver A w) {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ← hw, ← hw, coe_res_smul,
    valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ)]

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem val_int_le_one (A : ValuationSubring Ω) (x : 𝓞 L) : A.valuation (algebraMap L Ω (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A
    (x.isIntegral_coe.map ((algebraMap L Ω).toIntAlgHom)))

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem res_mem_inertia (hw : IsPlaceOver A w) {σ : G K Ω} (hσ : σ ∈ Ine (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) := by
  intro x
  show _ ∈ w.asIdeal
  rw [← hw]
  have := hσ.2 _ (val_int_le_one A x)
  rw [← coe_res_smul, ← map_sub] at this
  exact this

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem res_isArithFrobAt {v : HeightOneSpectrum (𝓞 K)} (hw : IsPlaceOver A w) [h : w.asIdeal.LiesOver v.asIdeal]
    {σ : G K Ω} (hσ : IsFrob (F := K) A (normV v) σ) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L σ) w.asIdeal := by
  intro x
  rw [← hw, ← h.over]
  have := hσ.2 _ (val_int_le_one A x)
  rw [← coe_res_smul, ← map_pow, ← map_sub] at this
  exact this

theorem exists_lift_dec (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    ∃ σ ∈ Dec (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ0, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ
  have h1 : ∀ x : 𝓞 L, (σ0 • A).valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ w.asIdeal := by
    intro x
    rw [smul_valuation_lt_one_iff, ← coe_res_smul, hw, map_inv, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      MulAction.mem_stabilizer_iff.1 hτ]
  obtain ⟨g, hg⟩ := exists_smul_eq_of_over (F := L) h1 hw
  refine ⟨g.restrictScalars K * σ0, ?_, ?_⟩
  · rw [mem_Dec, mul_smul]
    exact hg
  · rw [map_mul, res_restrictScalars, one_mul]

def intAut (L : Type) [Field L] [NumberField L] [Algebra L Ω] (σ : G K Ω) : IntCl L Ω ≃+* IntCl L Ω where
  toFun b := ⟨σ b, ((isIntegral_int_of_isIntegral b.2).map (σ.toAlgHom.restrictScalars ℤ)).tower_top⟩
  invFun b := ⟨σ.symm b, ((isIntegral_int_of_isIntegral b.2).map (σ.symm.toAlgHom.restrictScalars ℤ)).tower_top⟩
  left_inv b := Subtype.ext (σ.symm_apply_apply _)
  right_inv b := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ _ _)
  map_add' a b := Subtype.ext (map_add σ _ _)

theorem exists_lift_ine (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L} (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[K] L)) :
    ∃ σ ∈ Ine (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ, hσ, rfl⟩ := exists_lift_dec hw (Ideal.inertia_le_stabilizer _ hτ)
  letI : TopologicalSpace (IntCl L Ω) := ⊥
  haveI : DiscreteTopology (IntCl L Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl L Ω
  haveI := isInvariant_intCl L Ω
  set Q := primeBelow (F := L) A with hQ
  haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hw).symm⟩
  have hmap : Q = Q.map (intAut L σ : IntCl L Ω →+* IntCl L Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
    exact (valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ) (b : Ω)).symm
  let φ : (IntCl L Ω ⧸ Q) ≃ₐ[𝓞 L ⧸ w.asIdeal] (IntCl L Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q (intAut L σ) hmap) (by
      intro r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q (intAut L σ (algebraMap (𝓞 L) (IntCl L Ω) x)) =
        Ideal.Quotient.mk Q (algebraMap (𝓞 L) (IntCl L Ω) x)
      rw [Ideal.Quotient.eq, mem_primeBelow]
      have h1 := (hw _).2 (hτ x)
      change A.valuation (σ (algebraMap L Ω (x : L)) - algebraMap L Ω (x : L)) < 1
      rw [← coe_res_smul, ← map_sub]
      exact h1)
  obtain ⟨⟨ρ, hρQ⟩, hρ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[L] Ω) w.asIdeal Q φ
  have hρQ' : ρ • Q = Q := hρQ
  have hcong : ∀ b : IntCl L Ω, A.valuation (σ (b : Ω) - ρ (b : Ω)) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (ρ • b) = Ideal.Quotient.mk Q (intAut L σ b) :=
      DFunLike.congr_fun hρ (Ideal.Quotient.mk Q b)
    exact Ideal.Quotient.eq.1 h1.symm
  have hdec : ρ • A = A := by
    refine eq_of_valuation_lt_one_iff L fun b hb => ?_
    let b' : IntCl L Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := L) (ρ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hρQ']
  have hρD : (ρ.restrictScalars K : G K Ω) ∈ Dec (F := K) A := hdec
  refine ⟨(ρ.restrictScalars K)⁻¹ * σ, mem_Ine_of_integral
    ((Dec (F := K) A).mul_mem ((Dec (F := K) A).inv_mem hρD) hσ) fun b hb => ?_, ?_⟩
  · rw [← valuation_apply_lt_one_iff hρD, map_sub, AlgEquiv.mul_apply, mul_inv_apply]
    exact hcong ⟨b, hb.tower_top⟩
  · rw [map_mul, map_inv, res_restrictScalars, inv_one, one_mul]

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in

theorem inertia_eq_bot_iff (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ ↔ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  rw [← Subgroup.card_eq_one, Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L)]

end PositivityTheory.FamInh

end
end

section
noncomputable section

open NumberField IsDedekindDomain Topology GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace PositivityTheory.FamInh

theorem isOpen_connInf (E : Type) [Field E] [NumberField E] :
    IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) :
      Set (InfiniteAdeleRing E)ˣ) := by
  haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E) :=
    inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))
  have he : IsOpenEmbedding (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
    Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := he.locallyConnectedSpace
  exact isOpen_connectedComponent

theorem ofInfinite_eq_map (E : Type) [Field E] [NumberField E] (y : (InfiniteAdeleRing E)ˣ) :
    (ofInfinite y : IdeleGroup E) =
      Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) y :=
  Units.ext rfl

theorem comap_connectedComponent (E : Type) [Field E] [NumberField E] :
    (Subgroup.connectedComponentOfOne (GroundTheory.Global.IdeleClassGroup E)).comap (GroundTheory.Global.IdeleClassGroup.mk E) =
      ((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E).topologicalClosure := by
  apply le_antisymm
  · intro x hx
    have hx' : IdeleClassGroup.mk E x ∈ connectedComponent (1 : IdeleClassGroup E) := hx
    show x ∈ closure (((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E : Subgroup (IdeleGroup E)) :
      Set (IdeleGroup E))
    rw [mem_closure_iff_nhds]
    intro t ht
    have hc : Continuous fun u : (FiniteAdeleRing (𝓞 E) E)ˣ => x * (ofFinite u : IdeleGroup E)⁻¹ :=
      continuous_const.mul continuous_ofFinite.inv
    have hW : (fun u : (FiniteAdeleRing (𝓞 E) E)ˣ => x * (ofFinite u : IdeleGroup E)⁻¹) ⁻¹' t ∈ 𝓝 1 :=
      hc.continuousAt.preimage_mem_nhds (by simpa using ht)
    obtain ⟨S, n, -, hn0, hsub⟩ := exists_finiteLevel_subset hW
    have hsupp : (Function.support n).Finite :=
      S.finite_toSet.subset fun v hv => by
        by_contra h
        exact hv (hn0 v h)
    let V : Subgroup (IdeleGroup E) :=
      (Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ).comap (toInfinite E) ⊓
        (finiteLevel n).comap (toFinite E)
    have hV : IsOpen (V : Set (IdeleGroup E)) :=
      ((isOpen_connInf E).preimage (continuous_toInfinite E)).inter
        ((isOpen_finiteLevel hsupp).preimage (continuous_toFinite E))
    have hVo : IsOpen ((V.map (IdeleClassGroup.mk E) : Subgroup (IdeleClassGroup E)) : Set (IdeleClassGroup E)) :=
      IdeleClassGroup.isOpenMap_mk E _ hV
    have hcl : IsClopen ((V.map (IdeleClassGroup.mk E) : Subgroup (IdeleClassGroup E)) : Set (IdeleClassGroup E)) :=
      ⟨Subgroup.isClosed_of_isOpen _ hVo, hVo⟩
    obtain ⟨y, hy, hyx⟩ := hcl.connectedComponent_subset (one_mem _) hx'
    have hk : x * y⁻¹ ∈ (IdeleClassGroup.mk E).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, mul_inv_cancel]
    rw [IdeleClassGroup.ker_mk] at hk
    refine ⟨x * (ofFinite (toFinite E y))⁻¹, hsub hy.2, ?_⟩
    have e : x * (ofFinite (toFinite E y))⁻¹ = (x * y⁻¹) * ofInfinite (toInfinite E y) := by
      have h := ofFinite_mul_ofInfinite y
      generalize ofFinite (toFinite E y) = a at h ⊢
      generalize ofInfinite (toInfinite E y) = b at h ⊢
      subst h
      rw [mul_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact Subgroup.mul_mem_sup hk ⟨toInfinite E y, hy.1, (ofInfinite_eq_map E _).symm⟩
  · refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
    · rintro _ ⟨k, rfl⟩
      show IdeleClassGroup.mk E (diagonal E k) ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup E)
      rw [IdeleClassGroup.mk_diagonal]
      exact one_mem _
    · rintro _ ⟨y, hy, rfl⟩
      let f : (InfiniteAdeleRing E)ˣ →* IdeleClassGroup E := (IdeleClassGroup.mk E).comp
        (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)))
      have hf : Continuous f := (IdeleClassGroup.continuous_mk E).comp
        (Continuous.units_map _ (continuous_id.prodMk continuous_const))
      have h := hf.image_connectedComponent_subset 1 ⟨y, hy, rfl⟩
      rw [map_one] at h
      exact h
    · exact isClosed_connectedComponent.preimage (IdeleClassGroup.continuous_mk E)

end PositivityTheory.FamInh

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal
open GroundTheory.LocalField GroundTheory.Global GroundTheory.Global.SemiLocal

namespace PositivityTheory.FamInh

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def art0 : Ideles E →* Gab E Ω :=
  (topologicalAbelianizationEquiv E Ω).symm.toMulEquiv.toMonoidHom.comp
    ((artinMap E Ω).comp (GroundTheory.Global.IdeleClassGroup.mk E))

theorem isOpenQuotientMap_art0 : IsOpenQuotientMap (art0 E Ω) := by
  have h1 : IsOpenQuotientMap (GroundTheory.Global.IdeleClassGroup.mk E) := QuotientGroup.isOpenQuotientMap_mk
  have h2 : IsOpenQuotientMap (QuotientGroup.mk : GroundTheory.Global.IdeleClassGroup E → GroundTheory.Global.IdeleClassGroup E ⧸
      Subgroup.connectedComponentOfOne (GroundTheory.Global.IdeleClassGroup E)) := QuotientGroup.isOpenQuotientMap_mk
  have h3 := (artinQuotientEquiv (K := E) (Ω := Ω)).toHomeomorph.isOpenQuotientMap
  have h4 := (topologicalAbelianizationEquiv E Ω).symm.toHomeomorph.isOpenQuotientMap
  exact h4.comp (h3.comp (h2.comp h1))

theorem ker_art0 : (art0 E Ω).ker = ((diagUnits E).range ⊔ infConn E).topologicalClosure := by
  rw [← comap_connectedComponent, ← ker_artinMap (K := E) (Ω := Ω)]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker]
  exact (topologicalAbelianizationEquiv E Ω).symm.toMulEquiv.map_eq_one_iff

variable {E Ω}

def res (L : IntermediateField E Ω) [IsAbelianGalois E L] : Gab E Ω →* (L ≃ₐ[E] L) :=
  (restrictAb L (le_maximalAbelianExtension L)).comp (topologicalAbelianizationEquiv E Ω).toMulEquiv.toMonoidHom

theorem res_toAb (L : IntermediateField E Ω) [IsAbelianGalois E L] (σ : G E Ω) :
    res L (toAb E Ω σ) = AlgEquiv.restrictNormalHom L σ :=
  restrictAb_topologicalAbelianizationEquiv L (le_maximalAbelianExtension L) σ

theorem continuous_res (L : IntermediateField E Ω) [IsAbelianGalois E L] : Continuous (res L) :=
  (continuous_restrictAb L (le_maximalAbelianExtension L)).comp (topologicalAbelianizationEquiv E Ω).continuous

theorem localIdele_eq (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    localIdele E v x = IdeleGroup.finiteEmbedding v x := rfl

theorem res_art0 (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L]
    (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    res L (art0 E Ω (localIdele E v x)) = localSymbol L v x := by
  rw [← restrictAb_artinMap_finiteEmbedding L v x, localIdele_eq]
  exact congrArg (restrictAb L (le_maximalAbelianExtension L))
    ((topologicalAbelianizationEquiv E Ω).apply_symm_apply _)

omit [NumberField E] [IsAlgClosure E Ω] in
theorem continuous_toAb : Continuous (toAb E Ω) := QuotientGroup.continuous_mk

theorem mem_of_forall_res {H : Subgroup (Gab E Ω)} (hH : IsClosed (H : Set (Gab E Ω))) {g : Gab E Ω}
    (h : ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L], H ≤ (res L).ker →
      res L g = 1) : g ∈ H := by
  obtain ⟨σ, rfl⟩ := toAb_surjective g
  let H' : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H.comap (toAb E Ω), hH.preimage continuous_toAb⟩
  have hfix := InfiniteGalois.fixingSubgroup_fixedField H'
  have : σ ∈ (IntermediateField.fixedField H'.1).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hab : y ∈ maximalAbelianExtension E Ω := by
      refine IntermediateField.fixedField_le (fun τ hτ => ?_) hy
      show toAb E Ω τ ∈ H
      rw [show toAb E Ω τ = 1 from (QuotientGroup.eq_one_iff τ).2 hτ]
      exact H.one_mem
    obtain ⟨L0, _, _, hL0⟩ := exists_finite_abelian_mem hab
    let L : IntermediateField E Ω := L0 ⊓ IntermediateField.fixedField H'.1
    have : FiniteDimensional E L :=
      FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : L ≤ L0)).toLinearMap
        (IntermediateField.inclusion (inf_le_left : L ≤ L0)).injective
    have : IsAbelianGalois E L := IsAbelianGalois.of_algHom (IntermediateField.inclusion (inf_le_left : L ≤ L0))
    have h1 := h L fun a ha => by
      obtain ⟨τ, rfl⟩ := toAb_surjective a
      rw [MonoidHom.mem_ker, res_toAb, ← MonoidHom.mem_ker, L.restrictNormalHom_ker,
        IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      exact (IntermediateField.mem_fixedField_iff _ z).1 hz.2 τ ha
    rw [res_toAb, ← MonoidHom.mem_ker, L.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff] at h1
    exact h1 y ⟨hL0, hy⟩
  rw [hfix] at this
  exact this

theorem eq_of_forall_res {H H' : Subgroup (Gab E Ω)} (hH : IsClosed (H : Set (Gab E Ω)))
    (hH' : IsClosed (H' : Set (Gab E Ω)))
    (h : ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
      H ≤ (res L).ker ↔ H' ≤ (res L).ker) : H = H' :=
  le_antisymm (fun _ hg => mem_of_forall_res hH' fun L _ _ hL => (h L).2 hL hg)
    (fun _ hg => mem_of_forall_res hH fun L _ _ hL => (h L).1 hL hg)

instance : T2Space (Gab E Ω) := by
  have : T2Space (maximalAbelianExtension E Ω ≃ₐ[E] maximalAbelianExtension E Ω) := krullTopology_t2
  exact (topologicalAbelianizationEquiv E Ω).symm.toHomeomorph.t2Space

theorem isClosed_map_toAb {S : Subgroup (G E Ω)} (hS : IsClosed (S : Set (G E Ω))) :
    IsClosed ((S.map (toAb E Ω) : Subgroup (Gab E Ω)) : Set (Gab E Ω)) :=
  (hS.isCompact.image continuous_toAb).isClosed

theorem isAlgClosure_top (L : IntermediateField E Ω) : IsAlgClosure L Ω :=
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) L⟩

variable {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem ine_le_ker_iff (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L]
    {w : HeightOneSpectrum (𝓞 L)} (hw : IsPlaceOver A w) :
    (Ine (F := E) A).map (toAb E Ω) ≤ (res L).ker ↔ w.asIdeal.inertia (L ≃ₐ[E] L) = ⊥ := by
  have := isAlgClosure_top L
  constructor
  · intro h
    rw [eq_bot_iff]
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := exists_lift_ine hw hτ
    rw [← res_toAb]
    exact h ⟨σ, hσ, rfl⟩
  · rintro h _ ⟨σ, hσ, rfl⟩
    rw [MonoidHom.mem_ker, res_toAb, ← Subgroup.mem_bot, ← h]
    exact res_mem_inertia hw hσ

theorem map_units_eq (hA : IsPlaceOver A v) :
    (unitFiltrationUnits (v.adicCompletion E) 0).map ((art0 E Ω).comp (localIdele E v)) =
      (Ine (F := E) A).map (toAb E Ω) := by
  refine eq_of_forall_res ?_ (isClosed_map_toAb (isClosed_Ine A)) fun L _ _ => ?_
  · exact ((isCompact_unitFiltrationUnits 0).image ((isOpenQuotientMap_art0 E Ω).continuous.comp
      (IdeleGroup.continuous_finiteEmbedding v))).isClosed
  · have := isAlgClosure_top L
    obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
    rw [ine_le_ker_iff L hw, inertia_eq_bot_iff v w]
    constructor
    · intro h
      refine ramificationIdx_eq_one_of_units_le_ker_localSymbol (v := v) (fun x hx => ?_) w
      rw [MonoidHom.mem_ker, ← res_art0]
      exact h ⟨x, hx, rfl⟩
    · rintro h _ ⟨x, hx, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, res_art0]
      refine units_le_ker_localSymbol L v ⟨w, hwv⟩ h ?_
      have h1 := mem_unitFiltrationUnits_zero_iff_valued.1 hx
      have h2 := mem_unitFiltrationUnits_zero_iff_valued.1 (Subgroup.inv_mem _ hx)
      exact (Submonoid.mem_units_iff _ _).2 ⟨h1.le, h2.le⟩

theorem unif_frob (hA : IsPlaceOver A v) {π : (v.adicCompletion E)ˣ} (hπ : ord (π : v.adicCompletion E) = 1)
    {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) :
    (toAb E Ω σ)⁻¹ * art0 E Ω (localIdele E v π) ∈ (Ine (F := E) A).map (toAb E Ω) := by
  refine mem_of_forall_res (isClosed_map_toAb (isClosed_Ine A)) fun L _ _ hL => ?_
  have := isAlgClosure_top L
  obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
  rw [ine_le_ker_iff L hw] at hL
  rw [map_mul, map_inv, res_toAb, res_art0, localSymbol_eq_arithFrobAt v w ((inertia_eq_bot_iff v w).1 hL) hπ]
  have h := (res_isArithFrobAt hw hσ).mul_inv_mem_inertia
    (IsArithFrobAt.arithFrobAt (𝓞 E) (L ≃ₐ[E] L) w.asIdeal)
  rw [hL, Subgroup.mem_bot, mul_inv_eq_one] at h
  rw [h, inv_mul_cancel]

theorem closure_range_eq (hA : IsPlaceOver A v) :
    ((art0 E Ω).comp (localIdele E v)).range.topologicalClosure = (Dec (F := E) A).map (toAb E Ω) := by
  refine eq_of_forall_res (Subgroup.isClosed_topologicalClosure _) (isClosed_map_toAb (isClosed_Dec A))
    fun L _ _ => ?_
  have := isAlgClosure_top L
  obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
  constructor
  · rintro h _ ⟨σ, hσ, rfl⟩
    obtain ⟨x, hx⟩ := exists_localSymbol_eq (v := v) ⟨w, hwv⟩ (res_mem_stabilizer hw hσ)
    rw [MonoidHom.mem_ker, res_toAb, ← hx, ← res_art0]
    exact h (Subgroup.le_topologicalClosure _ ⟨x, rfl⟩)
  · intro h
    have : T2Space (L ≃ₐ[E] L) := krullTopology_t2
    refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage (continuous_res L))
    rintro _ ⟨x, rfl⟩
    obtain ⟨σ, hσ, e⟩ := exists_lift_dec hw (localSymbol_mem_stabilizer L v ⟨w, hwv⟩ x)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, res_art0, ← e, ← res_toAb]
    exact h ⟨σ, hσ, rfl⟩

theorem art0_unit_iff (hA : IsPlaceOver A v) (g : Gab E Ω) :
    (∃ x, IsUnitAt v x ∧ art0 E Ω (localIdele E v x) = g) ↔ g ∈ (Ine (F := E) A).map (toAb E Ω) := by
  rw [← map_units_eq hA]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, mem_unitFiltrationUnits_zero_iff_valued.2 hx, e⟩,
    fun ⟨x, hx, e⟩ => ⟨x, mem_unitFiltrationUnits_zero_iff_valued.1 hx, e⟩⟩

theorem art0_unif_iff (hA : IsPlaceOver A v) (g : Gab E Ω) :
    (∃ x, IsUnifAt v x ∧ art0 E Ω (localIdele E v x) = g) ↔
      ∃ σ : G E Ω, IsFrob (F := E) A (normV v) σ ∧ toAb E Ω σ = g := by
  obtain ⟨π, hπ, hπv⟩ := exists_ord_eq_one_valued v
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨F, hF⟩ := exists_isFrob hA
    have hu : IsUnitAt v (π⁻¹ * x) := by
      unfold IsUnitAt
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hπv, hx, inv_mul_cancel₀ WithZero.exp_ne_zero]
    obtain ⟨ι, hι, e⟩ := Subgroup.mul_mem _ (unif_frob hA hπ hF) ((art0_unit_iff hA _).1 ⟨_, hu, rfl⟩)
    refine ⟨F * ι, isFrob_mul_of_mem_Ine hF hι, ?_⟩
    rw [map_mul, e, map_mul, map_mul, map_inv, map_inv]
    group
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨u, hu, e⟩ := (art0_unit_iff hA _).2 (unif_frob hA hπ hσ)
    refine ⟨π * u⁻¹, ?_, ?_⟩
    · unfold IsUnifAt
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hπv, hu, inv_one, mul_one]
    · rw [map_mul, map_mul, map_inv, map_inv, e]
      group

theorem isGlobalArtin_inv : IsGlobalArtin (art0 E Ω)⁻¹ where
  quot := (Homeomorph.inv (Gab E Ω)).isOpenQuotientMap.comp (isOpenQuotientMap_art0 E Ω)
  ker := by
    rw [← ker_art0 E Ω]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
  ine v A hA g := by
    simp only [MonoidHom.inv_apply, inv_eq_iff_eq_inv]
    rw [art0_unit_iff hA, Subgroup.inv_mem_iff]
    rfl
  frob v A hA g := by
    simp only [MonoidHom.inv_apply, map_inv, inv_eq_iff_eq_inv]
    exact art0_unif_iff hA _
  dec v A hA := by
    rw [← closure_range_eq hA]
    congr 1
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x⁻¹, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x⁻¹, by simp⟩

end PositivityTheory.FamInh

end
end
