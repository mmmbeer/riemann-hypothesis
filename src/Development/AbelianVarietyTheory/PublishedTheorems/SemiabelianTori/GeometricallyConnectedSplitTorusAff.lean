import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

def SemiAbelianHomExtension : Prop :=
  ∀ (S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S →
    ∀ (U : S.Opens), Dense (U : Set S) →
    ∀ (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H →
    ∀ f : (Over.pullback U.ι).obj G ⟶ (Over.pullback U.ι).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback U.ι).map F = f

namespace SemiAbelianHomExtension

open ExtUnique

variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]

theorem quasiCompact_and_dominant (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (j : U ⟶ S) [IsOpenImmersion j]
    [IsDominant j] : QuasiCompact j ∧ IsSchemeTheoreticallyDominant j :=
  have := GlobalTheory.IsNormalScheme.of_pred hS
  dense_openImmersion j

theorem of_isGrpPullback (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ)
    (f : G' ⟶ H') [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, -⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨-, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  let V : S.Opens := j.opensRange
  have hV : Dense (V : Set S) := j.denseRange
  let e : V.toScheme ⟶ U := j.isoOpensRange.inv
  have he : e ≫ j = V.ι := j.isoOpensRange_inv_comp
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G V.ι)
    (((isGrpPullback_pullback G' e).comp hφ).congr he rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (((isGrpPullback_pullback H' e).comp hψ).congr he rfl)
    (isGrpPullback_pullback H V.ι)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h S hS V hV G H hG hH (a.hom ≫ (Over.pullback e).map f ≫ b.hom) inferInstance
  have key : f.left ≫ ψ = φ ≫ F.left := by
    have h₁ := pullback_map_left_fst V.ι F
    rw [hF', Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc,
      ← Category.assoc ((Over.pullback e).map f).left, pullback_map_left_fst, Category.assoc,
      Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi (pullback.fst G'.hom e)).1 ((cancel_epi a.hom.left).1 h₁)
  exact ⟨F, ⟨hF, key⟩, fun F' hF' => over_hom_ext_of_isPullback hφ.1 (hF'.2.symm.trans key)⟩

theorem of_isOpenImmersion (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsOpenImmersion j] [IsDominant j] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H)
    [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f := by
  obtain ⟨F, ⟨hF, hF'⟩, hu⟩ := h.of_isGrpPullback hS hG hH (isGrpPullback_pullback G j)
    (isGrpPullback_pullback H j) f
  refine ⟨F, ⟨hF, ?_⟩, fun F' hF' => hu F' ⟨hF'.1, ?_⟩⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pullback_map_left_fst j F).trans hF'.symm
    · exact (Over.w _).trans (Over.w _).symm
  · rw [← hF'.2]
    exact pullback_map_left_fst j F'


theorem existsUnique_oAct_of_isGrpPullback (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {G : Over S} [GrpObj G] (hG : IsSemiAbelian G) {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G j φ) {O : Type} [CommRing O] (i : OAct O G') :
    ∃! a : OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  refine ExtUnique.existsUnique_oAct_of_isGrpPullback hφ i fun x => ?_
  have := i.hom x
  obtain ⟨F, ⟨-, hF⟩, -⟩ := h.of_isGrpPullback hS hG hG hφ hφ (i.act x)
  exact ⟨F, hF⟩


theorem existsUnique_iso_of_isGrpPullback (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U}
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ)
    (hψ : IsGrpPullback H' H j ψ) (e : G' ≅ H') [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ e.hom.left ≫ ψ = φ ≫ E.hom.left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨F, ⟨hF, hF'⟩, hu⟩ := h.of_isGrpPullback hS hG hH hφ hψ e.hom
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := h.of_isGrpPullback hS hH hG hψ hφ e.inv
  obtain ⟨h₁, h₂⟩ := comp_eq_id_of_isPullback hφ.1 hψ.1 e F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, ⟨hF, hF'⟩, fun E hE => Iso.ext (hu E.hom hE)⟩

theorem existsUnique_iso_of_extensions (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {A : Over U} [GrpObj A] {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ H.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A H j ψ) :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ φ ≫ E.hom.left = ψ := by
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  simpa [eq_comm] using h.existsUnique_iso_of_isGrpPullback hS hG hH hφ hψ (Iso.refl A)

omit [AlgebraicGeometry.IsNoetherian S] in

theorem act_comp_of_isPullback {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {G H : Over S} [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom] {G' H' : Over U} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsPullback φ G'.hom G.hom j)
    {O : Type} [CommRing O] (a : OAct O G) (b : OAct O H) (a' : OAct O G') (b' : OAct O H')
    (ha : ∀ x, (a'.act x).left ≫ φ = φ ≫ (a.act x).left) (hb : ∀ x, (b'.act x).left ≫ ψ = ψ ≫ (b.act x).left)
    (f : G' ⟶ H') (hf : ∀ x, a'.act x ≫ f = f ≫ b'.act x) (F : G ⟶ H) (hF : f.left ≫ ψ = φ ≫ F.left) (x : O) :
    a.act x ≫ F = F ≫ b.act x := by
  refine over_hom_ext_of_isPullback hφ ?_
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← ha, Category.assoc, ← hF, ← Category.assoc,
    ← Over.comp_left, hf, Over.comp_left, Category.assoc, hb, ← Category.assoc, hF, Category.assoc]

section Dvr

variable (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
  [IsFractionRing T K]

theorem isOpenImmersion_generic_dvr : IsOpenImmersion (spMap (algebraMap T K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have : IsLocalization.Away ϖ K := by
    refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, by
      rw [IsFractionRing.injective T K hxy]⟩⟩
    · rintro ⟨_, n, rfl⟩
      exact IsUnit.mk0 _ (by simp [hϖ.ne_zero])
    · obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors T) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
      refine ⟨⟨a * (u⁻¹ : Tˣ), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have hab' : z * algebraMap T K (u * ϖ ^ n) = algebraMap T K a := hu ▸ hab
      change z * algebraMap T K (ϖ ^ n) = algebraMap T K (a * (u⁻¹ : Tˣ))
      rw [map_mul, ← hab', _root_.mul_assoc, ← map_mul, mul_right_comm, Units.mul_inv, _root_.one_mul]
  exact IsOpenImmersion.of_isLocalization ϖ

theorem isDominant_generic_dvr : IsDominant (spMap (algebraMap T K)) :=
  have := (spec_fractionRing T K).1
  have := (spec_fractionRing T K).2
  inferInstance

theorem isNormalScheme_dvr : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp T) :=
  GlobalTheory.IsNormalScheme.pred _

variable {T K}

theorem dvr (h : SemiAbelianHomExtension) {G H : Over (Sp T)} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj H)
    [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f :=
  have := isOpenImmersion_generic_dvr T K
  have := isDominant_generic_dvr T K
  h.of_isOpenImmersion (isNormalScheme_dvr T) _ hG hH f


end Dvr

section Model

open scoped TensorProduct





theorem isAbelianScheme_unit (S : Scheme.{0}) : IsAbelianScheme (𝟙_ (Over S)) := by
  refine ⟨inferInstance, inferInstanceAs (Smooth (𝟙 S)), inferInstanceAs (IsProper (𝟙 S)), ?_⟩
  change GeometricallyConnected (𝟙 S)
  refine ⟨fun K _ y Z fst snd H => ?_⟩
  have : IsIso snd := H.isIso_snd_of_isIso
  exact snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous




end Model

end SemiAbelianHomExtension

end GlobalTheory.Published
