import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateHonda
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntOfCompatibleZmodPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CohomZeroEquivContinuous
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSepClosedResidueFieldPowerSeriesComplex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeOnCechNerveExactAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PreservesFiniteLimitsTensorLeftSheafify
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingSieveMemEtaleTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsPullbackAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyEquivEllAdicCohomology
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReduceToAffineSource
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocModuleUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BcDatumNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfEtaleSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFiniteEtaleOfExistsUniqueLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraFiniteFinrankLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraInjectiveClearDenom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointUpToIntegerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniqueAdditiveScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointCancelNonzeroMultiple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomExtPoints
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotFrobGUnitRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetFixingPointLocallyFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
import ReciprocityTheory.ReductiveGroups.Lattices.LatUnrCharA

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

noncomputable section

namespace GlobalTheory.Et.CovChar.Trip

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev Tr : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Tr f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    simp only [Category.assoc]
    rw [pullback.condition (f := f) (g := f), pullback.condition_assoc, pullback.condition (f := f) (g := f)])

@[reassoc (attr := simp)] theorem pr13_fst : pr13 f ≫ pullback.fst f f = pullback.fst _ _ ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem pr13_snd : pr13 f ≫ pullback.snd f f = pullback.snd _ _ ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

variable (R : Type) [CommRing R]

def d1 : (freeOn R).obj (pullback f f) ⟶ (freeOn R).obj Y :=
  (freeOn R).map (pullback.snd f f) - (freeOn R).map (pullback.fst f f)

def d2 : (freeOn R).obj (Tr f) ⟶ (freeOn R).obj (pullback f f) :=
  (freeOn R).map (pullback.snd _ _) - (freeOn R).map (pr13 f) + (freeOn R).map (pullback.fst _ _)

theorem d2_comp : d2 f R ≫ d1 f R = 0 := by
  simp only [d1, d2, Preadditive.sub_comp, Preadditive.add_comp, Preadditive.comp_sub, ← Functor.map_comp,
    pr13_fst, pr13_snd, pullback.condition]
  abel

end GlobalTheory.Et.CovChar.Trip
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et GlobalTheory.Et.CovChar.Trip

noncomputable section
namespace GlobalTheory.Et.CovChar.Trip.CechLevels
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev L (n : ℕ) : Scheme.{0} := widePullback X (fun _ : Fin (n+1) => Y) (fun _ => f)

def e0 : L f 0 ≅ Y where
  hom := WidePullback.π _ 0
  inv := WidePullback.lift f (fun _ => 𝟙 Y) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j; simp [WidePullback.lift_π]
    · simp [WidePullback.lift_base, WidePullback.π_arrow]
  inv_hom_id := by simp [WidePullback.lift_π]

def e1 : L f 1 ≅ pullback f f where
  hom := pullback.lift (WidePullback.π _ 0) (WidePullback.π _ 1) (by simp)
  inv := WidePullback.lift (pullback.fst f f ≫ f) ![pullback.fst f f, pullback.snd f f]
    (by intro j; fin_cases j <;> simp [pullback.condition])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_snd]; simp
    · simp only [Category.assoc, WidePullback.lift_base]; erw [pullback.lift_fst_assoc]; simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc]; erw [pullback.lift_fst]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_snd]; simp [WidePullback.lift_π]

def e2 : L f 2 ≅ Tr f where
  hom := pullback.lift (pullback.lift (WidePullback.π _ 0) (WidePullback.π _ 1) (by simp))
    (pullback.lift (WidePullback.π _ 1) (WidePullback.π _ 2) (by simp)) (by
      erw [pullback.lift_snd, pullback.lift_fst])
  inv := WidePullback.lift (pullback.fst _ _ ≫ pullback.fst f f ≫ f)
    ![pullback.fst _ _ ≫ pullback.fst f f, pullback.fst _ _ ≫ pullback.snd f f, pullback.snd _ _ ≫ pullback.snd f f]
    (by
      intro j; fin_cases j
      · simp
      · show (pullback.fst _ _ ≫ pullback.snd f f) ≫ f = _
        rw [Category.assoc, ← pullback.condition (f := f) (g := f)]
      · show (pullback.snd _ _ ≫ pullback.snd f f) ≫ f = _
        rw [Category.assoc, ← pullback.condition (f := f) (g := f),
          ← pullback.condition_assoc (f := pullback.snd f f) (g := pullback.fst f f),
          ← pullback.condition (f := f) (g := f)])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst_assoc, pullback.lift_fst]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst_assoc, pullback.lift_snd]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_snd_assoc, pullback.lift_snd]; simp
    · simp only [Category.assoc, WidePullback.lift_base]; erw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]; simp
  inv_hom_id := by
    apply pullback.hom_ext <;> apply pullback.hom_ext
    · simp only [Category.assoc]; erw [pullback.lift_fst_assoc, pullback.lift_fst]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_fst_assoc, pullback.lift_snd]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_snd_assoc, pullback.lift_fst]; simp [WidePullback.lift_π]; exact pullback.condition
    · simp only [Category.assoc]; erw [pullback.lift_snd_assoc, pullback.lift_snd]; simp [WidePullback.lift_π]

theorem face_π {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.δ i ≫ WidePullback.π (fun _ => f) j = WidePullback.π (fun _ => f) (i.succAbove j) := by
  simp only [SimplicialObject.δ, Arrow.cechNerve_map]
  erw [WidePullback.lift_π]
  rfl

theorem cech_nerve_face_one_zero : (Arrow.mk f).cechNerve.δ (0 : Fin 2) ≫ (e0 f).hom = (e1 f).hom ≫ pullback.snd f f := by
  erw [pullback.lift_snd]; exact face_π f 0 0
theorem cech_nerve_face_one_one : (Arrow.mk f).cechNerve.δ (1 : Fin 2) ≫ (e0 f).hom = (e1 f).hom ≫ pullback.fst f f := by
  erw [pullback.lift_fst]; exact face_π f 1 0

theorem cech_nerve_face_two_zero : (Arrow.mk f).cechNerve.δ (0 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pullback.snd _ _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc]; erw [pullback.lift_fst, pullback.lift_snd_assoc, pullback.lift_fst]; exact face_π f 0 0
  · simp only [Category.assoc]; erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]; exact face_π f 0 1
theorem cech_nerve_face_two_one : (Arrow.mk f).cechNerve.δ (1 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pr13 f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pr13_fst]; erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]; exact face_π f 1 0
  · simp only [Category.assoc, pr13_snd]; erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]; exact face_π f 1 1
theorem cech_nerve_face_two_two : (Arrow.mk f).cechNerve.δ (2 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pullback.fst _ _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc]; erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]; exact face_π f 2 0
  · simp only [Category.assoc]; erw [pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd]; exact face_π f 2 1

end GlobalTheory.Et.CovChar.Trip.CechLevels

namespace GlobalTheory.Et.CovChar.Trip
open CechLevels in

theorem free_sheaf_cech_degree_two_exact (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X) :
    (ShortComplex.mk (d2 f R) (d1 f R) (d2_comp f R)).Exact := by
  have h := freeOn_cechNerve_exactAt (R := R) f 0
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at h
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  refine ShortComplex.isoMk ((freeOn R).mapIso (e2 f)) ((freeOn R).mapIso (e1 f)) ((freeOn R).mapIso (e0 f)) ?_ ?_
  · have hd : ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 2 1 =
        (freeOn R).map ((Arrow.mk f).cechNerve.δ (0 : Fin 3)) - (freeOn R).map ((Arrow.mk f).cechNerve.δ (1 : Fin 3))
          + (freeOn R).map ((Arrow.mk f).cechNerve.δ (2 : Fin 3)) := by
      erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
      simp [Fin.sum_univ_three, SimplicialObject.δ, sub_eq_add_neg]
    change _ = ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 2 1 ≫ _
    rw [hd]
    simp only [d2, Functor.mapIso_hom, Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp,
      Preadditive.sub_comp, ← Functor.map_comp, cech_nerve_face_two_zero, cech_nerve_face_two_one, cech_nerve_face_two_two]
    simp only [Functor.map_comp]
    erw [Preadditive.comp_add, Preadditive.comp_sub]
    rfl
  · have hd : ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 1 0 =
        (freeOn R).map ((Arrow.mk f).cechNerve.δ (0 : Fin 2)) - (freeOn R).map ((Arrow.mk f).cechNerve.δ (1 : Fin 2)) := by
      erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
      simp [Fin.sum_univ_two, SimplicialObject.δ, sub_eq_add_neg]
    change _ = ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 1 0 ≫ _
    rw [hd]
    simp only [d1, Functor.mapIso_hom, Preadditive.comp_sub,
      Preadditive.sub_comp, ← Functor.map_comp, cech_nerve_face_one_zero, cech_nerve_face_one_one]
    simp only [Functor.map_comp]
    erw [Preadditive.comp_sub]
    rfl
end GlobalTheory.Et.CovChar.Trip

example : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X), (ShortComplex.mk (d2 f R) (d1 f R) (d2_comp f R)).Exact :=
  fun R _ _ _ f => GlobalTheory.Et.CovChar.Trip.free_sheaf_cech_degree_two_exact R f
end
end

section
open Polynomial Module

namespace GlobalTheory.SemisimpleConj

variable {K : Type} [Field K]

noncomputable def actX (K : Type) [Field K] (M : Type) [AddCommGroup M] [Module K[X] M] [Module K M]
    [IsScalarTower K K[X] M] : Module.End K M :=
  Algebra.lsmul K K M (X : K[X])

section
variable {M : Type} [AddCommGroup M] [Module K[X] M] [Module K M] [IsScalarTower K K[X] M]

instance finiteDimensional_submodule [FiniteDimensional K M] (S : Submodule K[X] M) :
    FiniteDimensional K S :=
  FiniteDimensional.of_injective ((S.subtype).restrictScalars K) Subtype.val_injective

end

section
variable {M N : Type} [AddCommGroup M] [Module K[X] M] [Module K M] [IsScalarTower K K[X] M]
  [AddCommGroup N] [Module K[X] N] [Module K N] [IsScalarTower K K[X] N]

end

end GlobalTheory.SemisimpleConj
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonObj GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped TensorProduct

namespace GlobalTheory.AV.ProdRed

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def inl (A B : AbVar K) : A ⟶ prod A B := prodLift (𝟙 A) 0

def inr (A B : AbVar K) : B ⟶ prod A B := prodLift 0 (𝟙 B)

end GlobalTheory.AV.ProdRed
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoByTwo

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def inl (A : AbVar K) : A ⟶ prod A A := prodLift (𝟙 A) 0

def inr (A : AbVar K) : A ⟶ prod A A := prodLift 0 (𝟙 A)

end GlobalTheory.TwoByTwo

namespace GlobalTheory.TwoByTwo

end GlobalTheory.TwoByTwo
end
end

section
open CategoryTheory GlobalTheory.AV GlobalTheory.AV.AbVar

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry Limits MonObj GlobalTheory.Published.AbVarRed GlobalTheory.SS.FrobModel
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AV.FrobEx

theorem frobOver_ptOver (K : Type) [Field K] [Fintype K] :
    frobOver (ptOver K (AlgebraicClosure K)) =
      specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  apply Over.OverMorphism.ext
  change absFrob (ptOver K (AlgebraicClosure K)) = Spec.map (CommRingCat.ofHom
    ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      AlgebraicClosure K →+* AlgebraicClosure K))
  haveI : IsAffine (ptOver K (AlgebraicClosure K)).left := inferInstanceAs (IsAffine (Spec _))
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).inv]
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  have e : ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) :
      AlgebraicClosure K →+* AlgebraicClosure K) c) = c ^ Fintype.card K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic_apply K (AlgebraicClosure K) c
  exact ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv.hom e).trans (map_pow _ c _)).symm

theorem isFrob_frobOver (K : Type) [Field K] [Fintype K] (A : AbVar K) :
    letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1
    IsFrob (A := A) (Hom.mk (frobOver A.X)) := by
  letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1
  intro x
  rw [mk_hom, ← frobOver_comm, frobOver_ptOver]
  rfl

end GlobalTheory.AV.FrobEx
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FrobPow

theorem frobOver_left_apply {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) (x : X.left) :
    (GlobalTheory.SS.FrobModel.frobOver X).left x = x := rfl

theorem frobOver_appLE {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) (U : X.left.Opens)
    (h : U ≤ (GlobalTheory.SS.FrobModel.frobOver X).left ⁻¹ᵁ U) (s : Γ(X.left, U)) :
    ((GlobalTheory.SS.FrobModel.frobOver X).left.appLE U U h).hom s = s ^ Fintype.card k :=
  GlobalTheory.AbLaw.rs_self (X := X.left) h (s ^ Fintype.card k)

theorem exists_isFrob_pow : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K), ∃ π : End A, IsFrob π ∧
    (∀ x : A.X.left, (Hom.hom (A := A) (B := A) π).left x = x) ∧
    ∀ (U : A.X.left.Opens) (h : U ≤ (Hom.hom (A := A) (B := A) π).left ⁻¹ᵁ U) (s : Γ(A.X.left, U)),
      ((Hom.hom (A := A) (B := A) π).left.appLE U U h).hom s = s ^ Fintype.card K := by
  intro K _ _ A
  letI : IsMonHom (GlobalTheory.SS.FrobModel.frobOver A.X) := (GlobalTheory.SS.FrobModel.frobG_frobOver A.X).1
  exact ⟨Hom.mk (GlobalTheory.SS.FrobModel.frobOver A.X), GlobalTheory.AV.FrobEx.isFrob_frobOver K A,
    fun x => frobOver_left_apply A.X x, fun U h s => frobOver_appLE A.X U h s⟩

end GlobalTheory.AV.FrobPow
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_endomorphism : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K), ∃ π : End A, IsFrob π ∧ (∀ x : A.X.left, (Hom.hom (A := A) (B := A) π).left x = x) ∧ ∀ (U : A.X.left.Opens) (h : U ≤ (Hom.hom (A := A) (B := A) π).left ⁻¹ᵁ U) (s : Γ(A.X.left, U)), ((Hom.hom (A := A) (B := A) π).left.appLE U U h).hom s = s ^ Fintype.card K := by
  first | exact @GlobalTheory.AV.FrobPow.exists_isFrob_pow | exact GlobalTheory.AV.FrobPow.exists_isFrob_pow | (intros; apply GlobalTheory.AV.FrobPow.exists_isFrob_pow; all_goals assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem frob_isFrob_unique : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K),
    IsFrob (frob A) ∧ ∀ π : End A, IsFrob π → π = frob A := by
  intro K _ _ A
  have hex : ∃ π : End A, IsFrob π := by
    obtain ⟨π, hπ, -⟩ := GlobalTheory.T.exists_frobenius_endomorphism K A
    exact ⟨π, hπ⟩
  have hf : IsFrob (frob A) := by
    unfold frob
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hf, fun π hπ => ?_⟩
  apply GlobalTheory.AV.AbVar.ext_of_pt_eq
  intro x
  rw [hπ x, hf x]

end GlobalTheory.AV.AbVar
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_endomorphism_unique : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K), IsFrob (frob A) ∧ ∀ π : End A, IsFrob π → π = frob A := by
  atlas_forward_decl GlobalTheory.AV.AbVar.frob_isFrob_unique
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem frob_tend_galT (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K) :
    tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  have h := (GlobalTheory.T.frobenius_endomorphism_unique K A).1
  refine LinearMap.ext fun t => Tate.ext fun n => ?_
  exact h (t.lev n)

theorem frob_tate (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K) :
    tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) ∧
    vend l A (toEnd0 A (frob A)) = galV l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  refine ⟨frob_tend_galT K l A, ?_⟩
  have hv : vend l A (toEnd0 A (frob A)) =
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)) (tend l A (frob A)) := by
    simp [vend, toEnd0, Algebra.TensorProduct.lift_tmul]
  rw [hv, frob_tend_galT K l A]
  rfl

end GlobalTheory.AV.AbVar
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_tate_galois_action : ∀ (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K), tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) ∧ vend l A (toEnd0 A (frob A)) = galV l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  atlas_forward_decl GlobalTheory.AV.AbVar.frob_tate
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AV.GalPow

theorem exists_pow_card_of_finset {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : L ≃ₐ[K] L) (X : Finset L) :
    ∃ i : ℕ, ∀ x ∈ X, σ x = x ^ Fintype.card K ^ i := by
  let M := IntermediateField.adjoin K (X : Set L)
  have : FiniteDimensional K M := IntermediateField.finiteDimensional_adjoin fun x _ =>
    Algebra.IsIntegral.isIntegral x
  have : Finite M := Module.finite_of_finite K
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K M).2
    (σ.restrictNormal M)
  refine ⟨i, fun x hx => ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes σ M ⟨x, IntermediateField.subset_adjoin _ _ hx⟩
  rw [← hi] at h1
  dsimp only at h1
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h1
  simpa using h1.symm

theorem exists_frob_pow_on_finset : ∀ (K : Type) [Field K] [Fintype K] (σ : Gal K) (X : Over (Sp K)) (s : Finset (ptOver K (AlgebraicClosure K) ⟶ X)), LocallyOfFiniteType X.hom → ∃ m : ℕ, ∀ x ∈ s, specAut σ ≫ x = specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) ≫ x := by
  classical
  intro K _ _ σ X s hX
  set Φ := FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) with hΦ
  have hF : ∀ x : ptOver K (AlgebraicClosure K) ⟶ X, ∃ t : Finset (AlgebraicClosure K), ∀ τ : Gal K,
      (∀ a ∈ t, τ a = a) → specAut τ ≫ x = x := fun x =>
    GlobalTheory.PtFin.exists_finset_fix K (AlgebraicClosure K) X hX x
  choose F hF using hF
  obtain ⟨i, hi⟩ := exists_pow_card_of_finset σ (s.biUnion F)
  have hΦi : ∀ a : AlgebraicClosure K, (Φ ^ i) a = a ^ Fintype.card K ^ i := fun a => by
    rw [AlgEquiv.coe_pow, hΦ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  refine ⟨i, fun x hx => ?_⟩
  set τ : Gal K := (Φ ^ i)⁻¹ * σ with hτ
  have hτfix : ∀ a ∈ F x, τ a = a := fun a ha => by
    have h1 := hi a (Finset.mem_biUnion.2 ⟨x, hx, ha⟩)
    rw [hτ, AlgEquiv.mul_apply, h1, ← hΦi]
    exact (Φ ^ i).symm_apply_apply a
  have hτx : specAut τ ≫ x = x := hF x τ hτfix
  have hσ : σ = Φ ^ i * τ := by rw [hτ, mul_inv_cancel_left]
  rw [hσ, specAut_mul, Category.assoc, hτx]

end GlobalTheory.AV.GalPow
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_fixed_frobenius_power : ∀ (K : Type) [Field K] [Fintype K] (σ : Gal K) (X : Over (Sp K)) (s : Finset (ptOver K (AlgebraicClosure K) ⟶ X)), LocallyOfFiniteType X.hom → ∃ m : ℕ, ∀ x ∈ s, specAut σ ≫ x = specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) ≫ x := by
  first | exact @GlobalTheory.AV.GalPow.exists_frob_pow_on_finset | exact GlobalTheory.AV.GalPow.exists_frob_pow_on_finset | (intros; apply GlobalTheory.AV.GalPow.exists_frob_pow_on_finset; all_goals assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K] [Fintype K]

local notation "Fr" K => FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)


variable (l : ℕ) [Fact l.Prime]





abbrev tv (A : AbVar K) : Tl l A →ₗ[ℤ_[l]] Vl l A := TensorProduct.mk ℤ_[l] ℚ_[l] (Tl l A) 1

instance isLocalizedModule_tv (A : AbVar K) : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (tv l A) := by
  rw [isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l]]
  exact TensorProduct.isBaseChange _ _ _



theorem tv_injective (hl : (l : K) ≠ 0) (A : AbVar K) : Function.Injective (tv l A) := by
  haveI := (tl_free_finrank K l hl A).1
  intro u v h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ_[l]) (tv l A)).1 h
  exact smul_right_injective (Tl l A) (nonZeroDivisors.coe_ne_zero c) hc



end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar


end GlobalTheory.AV.AbVar
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.TateHondaBridge

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AV GlobalTheory.AV.AbVar ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Published.AbVarRed

def toAbVar {k : Type} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A] (hA : IsAbelianScheme A) :
    AbVar k where
  X := A
  ab := hA
  dim := (GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA).choose
  smooth := (GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA).choose_spec

end GlobalTheory.TateHondaBridge

end
end

section
open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_prime_cast_ne_zero_of_field (k : Type) [Field k] : ∃ l : ℕ, l.Prime ∧ (l : k) ≠ 0 := by
  obtain ⟨l, hl, hlp⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  refine ⟨l, hlp, fun h => ?_⟩
  rw [CharP.cast_eq_zero_iff k (ringChar k)] at h
  rcases hlp.eq_one_or_self_of_dvd _ h with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

theorem minpoly_int_coeff_zero_ne_zero {F : Type} [Field F] [NumberField F] (x : 𝓞 F) (hx : x ≠ 0) :
    (minpoly ℤ x).coeff 0 ≠ 0 := by
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hxF : (x : F) ≠ 0 := by exact_mod_cast hx
  have h1 := minpoly.coeff_zero_ne_zero (A := ℚ) (IsIntegral.of_finite ℚ (x : F)) hxF
  have h2 : minpoly ℚ (x : F) = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ F hi
  rw [h2, coeff_map] at h1
  intro h; exact h1 (by rw [h, map_zero])

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem norm_natAbs_eq_minpoly_coeff_zero_pow {F : Type} [Field F] [NumberField F] (x : 𝓞 F) :
    ∃ r : ℕ, r * (minpoly ℤ x).natDegree = Module.finrank ℚ F ∧
      (Algebra.norm ℤ x).natAbs = ((minpoly ℤ x).coeff 0).natAbs ^ r := by
  obtain ⟨r, -, hr⟩ := ReciprocityTheory.ChartRestriction.T1.lat_cp_eq_minpoly_pow x
  have hm : (minpoly ℤ x).Monic := minpoly.monic (RingOfIntegers.isIntegral x)
  refine ⟨r, ?_, ?_⟩
  · rw [← ReciprocityTheory.ChartRestriction.T1.lat_cp_natDegree x, hr, hm.natDegree_pow]
  · have e : Algebra.norm ℤ x = (-1) ^ Module.finrank ℤ (𝓞 F) * (ReciprocityTheory.ChartRestriction.T1.lat_cp x).coeff 0 := by
      rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]; rfl
    rw [e, hr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_pow]
    simp

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem deg_eq_coeff_zero_pow_of_aeval {k : Type} [Field k] (A : AbVar k) (f : End A) (m : ℤ[X]) (hm : m.Monic)
    (hp : Prime m) (hf : aeval f m = 0) :
    ∃ e : ℕ, e * m.natDegree = 2 * A.dim ∧ (deg (A := A) (B := A) f : ℤ) = m.coeff 0 ^ e := by
  obtain ⟨l, hl, hl0⟩ := exists_prime_cast_ne_zero_of_field k
  haveI := Fact.mk hl
  obtain ⟨-, -, -, hfin, hrank⟩ := GlobalTheory.AV.AbVar.tl_free_finrank k l hl0 A
  haveI := hfin
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.endCharpoly_tate_det_degree_trace k l hl0 A f
  have h1' := @h1 hfin
  have inj : Function.Injective (algebraMap ℤ ℚ_[l]) := RingHom.injective_int _
  let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
    (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp (tend l A)
  have hψ : ψ f = vmap l (A := A) (B := A) f := rfl
  have hT : aeval (vmap l (A := A) (B := A) f) m = 0 := by
    rw [← hψ]
    have := Polynomial.hom_eval₂ m (algebraMap ℤ (End A)) ψ f
    rw [← aeval_def, hf, map_zero, Subsingleton.elim (ψ.comp (algebraMap ℤ (End A))) (algebraMap ℤ _),
      ← aeval_def] at this
    exact this.symm
  have hdvd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank (vmap l (A := A) (B := A) f) (m.map (algebraMap ℤ ℚ_[l]))
    (by rw [aeval_map_algebraMap]; exact hT)
  rw [← h1', ← Polynomial.map_pow] at hdvd
  have hQm : (charpoly f).Monic :=
    Polynomial.monic_of_injective inj (by rw [h1']; exact LinearMap.charpoly_monic _)
  rw [map_dvd_map _ inj hQm] at hdvd
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp _).1 hdvd
  have hQ : charpoly f = m ^ i := eq_of_monic_of_associated hQm (hm.pow i) hi
  have hdeg : (charpoly f).natDegree = 2 * A.dim := by
    rw [← Polynomial.natDegree_map_eq_of_injective inj, h1', LinearMap.charpoly_natDegree, hrank]
  refine ⟨i, ?_, ?_⟩
  · rw [← hdeg, hQ, hm.natDegree_pow]
  · have e := LinearMap.det_eq_sign_charpoly_coeff (vmap l (A := A) (B := A) f)
    rw [h3, ← h1', coeff_map, hrank, pow_mul, neg_one_sq, one_pow, one_mul, hQ, coeff_zero_eq_eval_zero,
      eval_pow, ← coeff_zero_eq_eval_zero] at e
    apply Int.cast_injective (α := ℚ_[l])
    rw [Int.cast_natCast, e, eq_intCast, Int.cast_pow]

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_and_deg_eq_norm_pow : ∀ (k : Type) [Field k] (A : AbVar k) (F : Type) [Field F] [NumberField F]
    (ι : 𝓞 F →+* End A) (d : ℕ), 2 * A.dim = d * Module.finrank ℚ F → ∀ x : 𝓞 F, x ≠ 0 →
      IsIsogeny (A := A) (B := A) (ι x) ∧ deg (A := A) (B := A) (ι x) = (Algebra.norm ℤ x).natAbs ^ d := by
  intro k _ A F _ _ ι d hd x hx
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hm : (minpoly ℤ x).Monic := minpoly.monic hi
  have hp : Prime (minpoly ℤ x) := (minpoly.irreducible hi).prime
  have hf : aeval (ι x) (minpoly ℤ x) = 0 := by
    have := Polynomial.hom_eval₂ (minpoly ℤ x) (algebraMap ℤ (𝓞 F)) ι x
    rw [← aeval_def, minpoly.aeval, map_zero, Subsingleton.elim (ι.comp (algebraMap ℤ (𝓞 F))) (algebraMap ℤ _),
      ← aeval_def] at this
    exact this.symm
  obtain ⟨e, he, hdeg⟩ := deg_eq_coeff_zero_pow_of_aeval A (ι x) (minpoly ℤ x) hm hp hf
  obtain ⟨r, hr, hN⟩ := norm_natAbs_eq_minpoly_coeff_zero_pow x
  have hpos : 0 < (minpoly ℤ x).natDegree := minpoly.natDegree_pos hi
  have her : e = d * r := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [he, hd, ← hr, mul_assoc]
  have hdeg' : deg (A := A) (B := A) (ι x) = ((minpoly ℤ x).coeff 0).natAbs ^ e := by
    have := congrArg Int.natAbs hdeg
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at this
  have hval : deg (A := A) (B := A) (ι x) = (Algebra.norm ℤ x).natAbs ^ d := by
    rw [hdeg', hN, ← pow_mul, her, mul_comm]
  refine ⟨?_, hval⟩
  by_contra h
  have h0 : deg (A := A) (B := A) (ι x) = 0 := by
    classical
    unfold deg
    rw [if_neg h]
  rw [hdeg'] at h0
  exact minpoly_int_coeff_zero_ne_zero x hx (Int.natAbs_eq_zero.1 (pow_eq_zero_iff'.1 h0).1)

end GlobalTheory.AV.AbVar
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.OActDeg

def endHom {k : Type} [Field k] (X : GlobalTheory.AV.AbVar k) (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) X.X) :
    𝓞 F →+* CategoryTheory.End X where
  toFun c := GlobalTheory.AV.AbVar.Hom.mk (A := X) (B := X) (ρ.act c) (h := ρ.hom c)
  map_one' := by
    apply GlobalTheory.AV.AbVar.hom_ext
    simp [ρ.one]
  map_mul' a b := by
    apply GlobalTheory.AV.AbVar.hom_ext
    change ρ.act (a * b) = ρ.act b ≫ ρ.act a
    rw [mul_comm, ρ.mul]
  map_zero' := by
    apply GlobalTheory.AV.AbVar.hom_ext
    rw [GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.zero_hom]
    have h := ρ.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  map_add' a b := by
    apply GlobalTheory.AV.AbVar.hom_ext
    rw [GlobalTheory.AV.AbVar.add_hom, GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.mk_hom, ρ.add]

theorem isFinite_and_finrank_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  intro k _ _ A _ hA F _ _ ρ l d hl hl0 hcard c hc
  let X : GlobalTheory.AV.AbVar k := GlobalTheory.TateHondaBridge.toAbVar A hA
  have h2 := GlobalTheory.abMulN_holds k A X.dim l hA X.smooth hl0
  rw [hcard] at h2
  have hdim : 2 * X.dim = d * Module.finrank ℚ F :=
    (Nat.pow_right_injective hl.two_le h2).symm
  obtain ⟨hiso, hdeg⟩ := GlobalTheory.AV.AbVar.isIsogeny_and_deg_eq_norm_pow k X F (endHom X F ρ) d hdim c hc
  refine ⟨hiso.1, ?_⟩
  classical
  rw [← hdeg]
  unfold GlobalTheory.AV.AbVar.deg
  rw [if_pos hiso]
  rfl

end GlobalTheory.AV.OActDeg

end
end
