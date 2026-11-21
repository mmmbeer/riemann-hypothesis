import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8.ExciseCut

def relMap (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) (i n : ℤ) :
    HK (ZMod q) (mappingCone ((chains _).map (sch.map ι))) (tw q i) n →+
      HK (ZMod q) (mappingCone ((chains _).map (sch.map ι'))) (tw q i) n :=
  HK.pull (ZMod q) (mappingCone.map ((chains _).map (sch.map ι')) ((chains _).map (sch.map ι))
    ((chains _).map (sch.map g)) ((chains _).map (sch.map f)) (by simp only [← Functor.map_comp, w])) (tw q i) n

def relMapBC (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) {T : Scheme.{0}} (s : T ⟶ X) (i n : ℤ) :=
  relMap q (pullback.map (ι' ≫ f) s f s ι' (𝟙 T) (𝟙 X) (by simp) (by simp)) (pullback.snd ι s)
    (pullback.map (ι' ≫ f) s ι s g (𝟙 T) (𝟙 X) (by simp [w]) (by simp)) (pullback.snd f s) (by rw [pullback.lift_snd, pullback.lift_snd]) i n

def LeafConeZero : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R),
  (∀ n, Function.Bijective (HK.pull R φ F n)) → ∀ n, Subsingleton (HK R (mappingCone φ) F n)

def ExcisionRelationSquare : Prop := Base → ∀ (q : ℕ) [NeZero q] {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z)
  (f : X' ⟶ X) (w : ι' ≫ f = g ≫ ι) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact ι] [QuasiSeparated ι]
  [QuasiCompact ι'] [QuasiSeparated ι'], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ,
  (∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ X), SH A → ∀ n,
    Function.Bijective (relMapBC q ι' ι g f w s i n)) →
  ∀ n, Function.Bijective (relMap q ι' ι g f w i n)

def LeafExciseLocal : Prop := Base → ∀ (q : ℕ) [NeZero q] {X' X Z : Scheme.{0}} (f : X' ⟶ X) [IsProper f]
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsUnit (q : Γ(X, ⊤)) → ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ →
  IsIso (f ∣_ U) → ∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ X), SH A → ∀ i n : ℤ,
  Function.Bijective (relMapBC q (pullback.fst f ι) ι (pullback.snd f ι) f pullback.condition s i n)

theorem goal_of (h1 : ExcisionRelationSquare) (h2 : LeafExciseLocal) : EtaleExcise := by
  intro base q _ X' X Z _ f _ ι _ hq U hU hiso n i
  exact h1 base q (pullback.fst f ι) ι (pullback.snd f ι) f pullback.condition hq i
    (fun A _ s hA m => h2 base q f ι hq U hU hiso A s hA i m) n

end LateralTheory.E.E8.ExciseCut
end
end

section
noncomputable section
open CategoryTheory Limits Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC Pretriangulated

namespace LateralTheory.E.E8.ExciseCut.ConeZeroPf

universe u v

theorem tri_zero {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]
    (T : Triangle D) (hT : T ∈ distTriang D) (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧)
    (hb : ∀ n, Function.Bijective (fun g : T.obj₂ ⟶ Y n => T.mor₁ ≫ g)) (n : ℤ) (x : T.obj₃ ⟶ Y n) : x = 0 := by
  have hy : T.mor₂ ≫ x = 0 := by
    apply (hb n).1
    simp only [comp_zero, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]
  obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ T hT x hy
  obtain ⟨h, hh⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (g ≫ (e n).hom)
  obtain ⟨k, rfl⟩ := (hb (n - 1)).2 h
  have : g = (CategoryTheory.shiftFunctor D (1 : ℤ)).map (T.mor₁ ≫ k) ≫ (e n).inv := by
    rw [hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, Functor.map_comp]
  simp only [← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]

variable (R : Type) [CommRing R]

theorem pull_toHom {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    CohomologyClass.toHom (HK.pull R φ F n x) =
      (HomotopyCategory.quotient _ _).map φ ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  have : zcomp (Cocycle.ofHom φ) b (zero_add n) = b.precomp φ := by
    ext p q hpq
    simp [zcomp, Cocycle.precomp]
  change CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add n))) = _
  rw [this, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

theorem hb' {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (hb : ∀ n, Function.Bijective (HK.pull R φ F n)) (n : ℤ) :
    Function.Bijective (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧) =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map φ ≫ g) := by
  have : (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧) =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map φ ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R φ F n) ∘ (CohomologyClass.homAddEquiv.symm) := by
    funext g
    simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, pull_toHom]
    congr 1
    exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm
  rw [this]
  exact CohomologyClass.homAddEquiv.bijective.comp ((hb n).comp CohomologyClass.homAddEquiv.symm.bijective)

def shIso (E : Cx R) (n : ℤ) :
    (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj (E⟦n⟧) ≅
      ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj (E⟦n - 1⟧))⟦(1 : ℤ)⟧ :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).mapIso
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex (Shv R) ℤ) (n - 1) 1 n (by omega)).app E) ≪≫
    ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app (E⟦n - 1⟧)

end LateralTheory.E.E8.ExciseCut.ConeZeroPf

open LateralTheory.E.E8.ExciseCut.ConeZeroPf in
theorem LateralTheory.E.E8.ExciseCut.LeafConeZero_of : LateralTheory.E.E8.ExciseCut.LeafConeZero := by
  intro R _ K L φ F hb n
  refine ⟨fun x y => ?_⟩
  apply (CohomologyClass.toHom_bijective _ _ _).1
  have hz := fun x : HK R (mappingCone φ) F n =>
    tri_zero (mappingCone.triangleh φ) (HomotopyCategory.mappingCone_triangleh_distinguished φ)
      (fun n => (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧))
      (shIso R (res R F)) (hb' R φ F hb) n (CohomologyClass.toHom x)
  exact (hz x).trans (hz y).symm
end
end
