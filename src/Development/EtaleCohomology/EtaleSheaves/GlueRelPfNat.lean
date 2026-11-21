import Development.EtaleCohomology.EtaleSheaves.GlueRelPfCone

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex AlgebraicGeometry LateralTheory.E.E4
  LateralTheory.E.LeafLocStalkPf

namespace LateralTheory.E.GlueRelPfNat
variable (R : Type) [CommRing R]

theorem map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) :
    (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff φ₁ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.map, mappingCone.inl_desc,
      Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inl_fst, ← Cochain.comp_assoc_of_third_is_zero_cochain,
      mappingCone.inl_fst]
    simp
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp [mappingCone.map]

theorem sq {Y X V : Scheme.{0}} (f : Y ⟶ X) (v : V ⟶ X) :
    cechAug (pullback.snd f v) ≫ sch.map v = LateralTheory.E.LocSurjPf.bcMap f v ≫ cechAug f := by
  ext n : 1
  simp only [NatTrans.comp_app]
  simp [cechAug, LateralTheory.E.LocSurjPf.bcMap, sch, Arrow.mapCechNerve, Arrow.augmentedCechNerve]
  exact (WidePullback.lift_base _ _ _ _).symm

end LateralTheory.E.GlueRelPfNat
