import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.Inhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def trivTriple (H : Host E) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (a : OAct (𝓞 E) G) : SAB H S where
  G := G
  semi := hG
  act := a
  PP := UU.trivRig G
  cub := UU.trivCub G
  sym := PrimNorm.isSymmetric_of_hasGen _ ⟨UU.unitGen _ _, UU.unitGen_isGen _ _⟩
  adj := fun _ => ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (Out.Inh.linComb_triv_g _ _))⟩
  prim := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (fun _ _ => rfl))⟩

def zeroTriple (H : Host E) (S : Scheme.{0}) : SAB H S :=
  trivTriple H (𝟙_ (Over S)) (isSemiAbelian_of_isAbelianScheme _ (UU.isAbelianScheme_unit S))
    ⟨fun _ => 𝟙 _, fun _ => inferInstance, rfl, fun _ _ => toUnit_unique _ _, fun _ _ => toUnit_unique _ _⟩

theorem isProper_zeroTriple (S : Scheme.{0}) : IsProper (zeroTriple H S).G.hom :=
  (UU.isAbelianScheme_unit S).proper

theorem abLocus_eq_univ {S : Scheme.{0}} (G : Over S) (h : IsProper G.hom) : abLocus G = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ _ _ => inferInstance

theorem abOpen_and_splitFib {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : AbOpen t.G ∧ SplitFib t.G := by
  refine ⟨⟨⊤, (abLocus_eq_univ _ h).symm, inferInstance⟩, fun x => ?_⟩
  exact ⟨S.residueField x, inferInstance, Algebra.id _, inferInstance, inferInstance, _,
    ZJ.isGt_splitExtOfAbelian _ (isAbelianScheme_pullback_obj _ t.G ⟨t.semi.comm, t.semi.smooth, h, t.semi.geomConnected⟩)⟩

theorem good_zeroTriple (S : Scheme.{0}) : Good (zeroTriple H S) := by
  obtain ⟨h₁, h₂⟩ := abOpen_and_splitFib (zeroTriple H S) (isProper_zeroTriple S)
  refine ⟨h₁, h₂, fun x => ⟨⊤, trivial, fun _ => 1, fun i j => ?_, fun y _ => ⟨y, PUnit.unit, rfl, ?_⟩⟩⟩
  · exact (map_one _).trans ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).symm
  · rw [Scheme.basicOpen_one]
    exact ⟨trivial, trivial⟩

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

section General

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

def ofTriple (hn : Geo.Tor.IsNormalScheme X) (hp : IsProjOver s) (hf : Flat s) (W : (pullback s (spMap β)).Opens)
    (hW : pullback.fst s (spMap β) ⁻¹' abLocus t.G = W) (hd : Dense (W : Set (pullback s (spMap β) : Scheme)))
    (t₀ : SAB H W.toScheme) (m : SABMap t₀ t (W.ι ≫ pullback.fst _ _)) : Cpt (W.ι ≫ pullback.snd _ _) t₀ β :=
  ⟨X, s, hn, hp, hf, W.ι, rfl, inferInstance, by rwa [Scheme.Opens.range_ι], t, m, by rwa [Scheme.Opens.range_ι]⟩

end General

section Above

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}



end Above

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  have := ProjSpace.Model.isIso_str_zero (R := R)
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Inhab

end
