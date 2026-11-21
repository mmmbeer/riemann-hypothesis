import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Test

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Scheme.{0}}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_epsMul_one (R : Type) [CommRing R] : spMap (epsMul (1 : R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [epsMul]

theorem latDR_subset_latHT {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB H X) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X) : latDR t x ⊆ latHT t p x := by
  rintro v ⟨xO, hx, vO, hv, e⟩
  refine ⟨xO, hx, 0, vO, hv, by rw [pow_zero, sp_epsMul_one, Category.id_comp, e], fun n c g _ => ?_⟩
  simp

abbrev torus (X : Scheme.{0}) : SAB H X :=
  GlobalTheory.Models.Inhab.trivTriple H (splitTorus X (𝓞 E)) (GlobalTheory.Diag.isSemiAbelian _ _) (GlobalTheory.Diag.diagAct _ _ _)

def charUnit {A : Type} [CommRing A] {g : Sp A ⟶ X} (w : Over.mk g ⟶ splitTorus X (𝓞 E)) (a : 𝓞 E) : Aˣ :=
  ⟨GlobalTheory.Diag.charVal w a, GlobalTheory.Diag.charVal w (-a), by rw [← GlobalTheory.Diag.charVal_add, add_neg_cancel, GlobalTheory.Diag.charVal_zero],
    by rw [← GlobalTheory.Diag.charVal_add, neg_add_cancel, GlobalTheory.Diag.charVal_zero]⟩

def torusChar {O : Type} [CommRing O] (x : Sp O ⟶ X) (q : ℕ) (a : 𝓞 E) : TorsChar (torus H X) x q where
  χ _ _ _ _ g := charUnit g a
  mul _ _ _ _ g g' _ _ := Units.ext (GlobalTheory.Diag.charVal_mul g g' a)
  nat B B' _ _ _ _ _ _ φ g g' _ h :=
    (GlobalTheory.Diag.left_eq_iff φ.toRingHom (by rw [← Category.assoc, sp_comp]; congr 2; exact φ.comp_algebraMap.symm) g' g).1 h a


end Lat

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_flagPt {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (Ω : Type) [Field Ω]
    (y : Sp Ω ⟶ gen Z) : ∃ z : FlagPt Z Ω, z.y = y := by
  have h : y ≫ genStr Z = spMap (Spec.preimage (y ≫ genStr Z)).hom := (Spec.map_preimage _).symm
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z Ω _ y h
  exact ⟨⟨_, y, h, f.v, f.tan, f.eig, f.basis⟩, rfl⟩

instance intO_valRing (C : Type) [NormedField C] [IsUltrametricDist C] : ValuationRing (intO C) := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  by_cases h : ‖(a : C)‖ ≤ ‖(b : C)‖
  · by_cases hb : (b : C) = 0
    · refine ⟨1, Or.inr (Subtype.ext ?_)⟩
      rw [hb, norm_zero, norm_le_zero_iff] at h
      simp [h, hb]
    · refine ⟨⟨a / b, show ‖(a / b : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩,
        Or.inr (Subtype.ext ?_)⟩
      simp [mul_div_cancel₀ _ hb]
  · have ha : (a : C) ≠ 0 := fun h0 => h (by simp [h0])
    refine ⟨⟨b / a, show ‖(b / a : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ (le_of_not_ge h) (norm_nonneg _)⟩,
      Or.inl (Subtype.ext ?_)⟩
    simp [mul_div_cancel₀ _ ha]

instance intO_frac (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, show ‖z⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_not_ge h)⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

theorem latDR_nonempty (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (x : Sp C ⟶ Z.X) : (latDR Z.t x).Nonempty := by
  have := isProper_toroidalModel_structureMap Z
  let φ : 𝓞 c.F →+* C := (Spec.preimage (x ≫ Z.s)).hom
  have hφ : ∀ a, φ a ∈ intO C := fun a => by
    have h1 : IsIntegral (intO C) (φ a) := (RingOfIntegers.isIntegral a).map_of_comp_eq (Int.castRingHom _) φ
      (RingHom.ext_int _ _)
    classical
    let _ : GCDMonoid (intO C) := IsBezout.toGCDDomain _
    have : IsIntegrallyClosed (intO C) := GCDMonoid.toIsIntegrallyClosed
    obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := intO C) (K := C)).1 h1
    exact hb ▸ b.2
  have hv : ValuativeCriterion.Existence Z.s := by
    have h := (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s)
    exact h.1
  let S : ValuativeCommSq Z.s :=
    { R := intO C, K := C, i₁ := x, i₂ := spMap (φ.codRestrict _ hφ)
      commSq := ⟨by
        rw [← Spec.map_preimage (x ≫ Z.s)]
        exact Spec.map_comp (CommRingCat.ofHom (φ.codRestrict _ hφ)) (CommRingCat.ofHom (intO C).subtype)⟩ }
  obtain ⟨⟨xO, h1, -⟩⟩ := (hv S).exists_lift
  let p : tEpsG xO ⟶ Over.mk xO := Over.homMk (spMap (algebraMap _ (DualNumber _))) rfl
  refine ⟨_, xO, h1, (1 : tEpsG xO ⟶ Z.t.G).left, ⟨Over.w _, ?_⟩, rfl⟩
  rw [← MonObj.comp_one p, Over.comp_left, ← Category.assoc]
  change (_ ≫ spMap _) ≫ _ = _
  rw [GlobalTheory.Diag.fstHom_base, Category.id_comp]

end Pts

def arReal (Tau : Type) (N g : ℕ) : ArIn Tau N g Unit where
  A _ := ℝ
  num _ M := M.prod
  root a R _ _ := if a 2 then R else 1
  whole _ _ _ _ := 1



section Stages

variable {D : D7} {N j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (P : PadPkg D N j Comp jC ng)

open PadPkg in

def admissibleStageOfPackage : AdmSt D N j jC :=
  ⟨fun p _ la => P.Mp p la, fun p _ la z => md P p la z, fun p _ la z => P.CurveM p la z,
    fun p _ la z => P.degM p la z, fun p _ la => P.htMdl p la⟩

end Stages


section Sign

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Sign

section Phi

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

def admissibleTrivialStage (D : D7) {N j : ℕ} (hj : j ≤ N) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : AdmSt D N j jC where
  admitted _ _ _ := Unit
  mdl p _ la _ := GlobalTheory.trivialAdmissibleModel D p (jC p la) N j hj
  Crv _ _ _ _ := DV.Rt D.what₂.Tau N → ℝ
  deg _ _ _ _ c := c
  ht _ _ _ := ()

end Phi

end GlobalTheory.ShFam.Pad.Test
