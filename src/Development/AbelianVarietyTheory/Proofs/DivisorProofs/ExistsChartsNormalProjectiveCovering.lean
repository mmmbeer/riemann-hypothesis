import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersion

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

theorem chart_inter_factor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ (R1 R2 : Type) [CommRing R1] [CommRing R2] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → ∃ (A : Type) (_ : CommRing A) (w : Sp A ⟶ X) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion w ∧ spMap a1 ≫ ξ1 = w ∧ spMap a2 ≫ ξ2 = w ∧ Set.range w = Set.range ξ1 ∩ Set.range ξ2 := by
  intro R _ X s hP R1 R2 _ _ ξ1 ξ2 h1 h2
  obtain ⟨N, i, hi, hs⟩ := hP
  have : IsProper (PSpace.str R N) := isProper_str R N
  have : IsProper s := by rw [← hs]; infer_instance
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  have hU : IsAffineOpen (ξ1.opensRange ⊓ ξ2.opensRange) :=
    (isAffineOpen_opensRange ξ1).inf (isAffineOpen_opensRange ξ2)
  have hr1 : Set.range hU.fromSpec.base ⊆ Set.range ξ1.base := by
    rw [hU.range_fromSpec]; intro x hx; exact hx.1
  have hr2 : Set.range hU.fromSpec.base ⊆ Set.range ξ2.base := by
    rw [hU.range_fromSpec]; intro x hx; exact hx.2
  refine ⟨Γ(X, ξ1.opensRange ⊓ ξ2.opensRange), inferInstance, hU.fromSpec,
    (Spec.preimage (IsOpenImmersion.lift ξ1 hU.fromSpec hr1)).hom,
    (Spec.preimage (IsOpenImmersion.lift ξ2 hU.fromSpec hr2)).hom, inferInstance, ?_, ?_, ?_⟩
  · simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  · simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  · show Set.range hU.fromSpec.base = _
    rw [hU.range_fromSpec]
    rfl

end GlobalTheory.UnitGlue
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_intersection_charts : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ (R1 R2 : Type) [CommRing R1] [CommRing R2] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → ∃ (A : Type) (_ : CommRing A) (w : Sp A ⟶ X) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion w ∧ spMap a1 ≫ ξ1 = w ∧ spMap a2 ≫ ξ2 = w ∧ Set.range w = Set.range ξ1 ∩ Set.range ξ2 := by
  atlas_forward_decl GlobalTheory.UnitGlue.chart_inter_factor
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlueTransport

theorem radical_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : ℕ) {a : R}
    (ha : a ∈ (Ideal.span {(p : R)}).radical) : f a ∈ (Ideal.span {(p : S)}).radical := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n, ?_⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  obtain ⟨c, hc⟩ := hn
  exact ⟨f c, by rw [← map_pow, hc, map_mul, map_natCast]⟩

theorem specMap_appLE {R A : Type} [CommRing R] [CommRing A] (a : R →+* A) (O : (Sp A).Opens)
    (e : O ≤ spMap a ⁻¹ᵁ ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (spMap a).appLE ⊤ O e =
    CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op := by
  have h1 : (spMap a).appLE ⊤ O e =
      (spMap a).appLE ⊤ ⊤ le_top ≫ (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op :=
    (Scheme.Hom.appLE_map _ _ _).symm
  have e1 : (spMap a).appTop = (spMap a).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  rw [h1, ← e1, Scheme.ΓSpecIso_inv_naturality_assoc]

theorem appLE_chart {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A] (c : Sp R ⟶ X)
    [IsOpenImmersion c] (a : R →+* A) (w : Sp A ⟶ X) (hw : spMap a ≫ c = w) (U : X.Opens)
    (hU : U ≤ c ''ᵁ ⊤) (O : (Sp A).Opens) (hO : O ≤ w ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (c.appIso ⊤).inv ≫ X.presheaf.map (homOfLE hU).op ≫
      w.appLE U O hO =
    CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op := by
  subst hw
  rw [Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_comp_appLE (spMap a) c (c ''ᵁ ⊤) ⊤ O
    (by rw [Scheme.Hom.preimage_image_eq]) le_top, Scheme.Hom.appIso_inv_appLE_assoc]
  erw [Scheme.Hom.map_appLE]
  exact specMap_appLE a O _

end GlobalTheory.UnitGlueTransport

namespace GlobalTheory.UnitGlueTransport

variable {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens} {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]}
  (h : ∀ x : X, UnitChartAt p Xw K x)

theorem ev_transport (x : X) {A : Type} [CommRing A] (w : Sp A ⟶ X) (a : cR h x →+* A)
    (hw : spMap a ≫ cξ h x = w) (W : X.Opens) (hW : W ≤ Uc h x ⊓ Xp X p)
    (θ : Localization.Away (p : A) →+* Γ(Sp A, w ⁻¹ᵁ W))
    (hθ : θ.comp (algebraMap A _) = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op).hom)
    (χ : Localization.Away (p : cR h x) →+* Localization.Away (p : A))
    (hχ : χ.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a)
    (c : Localization.Away (p : cR h x)) :
    (w.app W).hom ((X.presheaf.map (homOfLE hW).op).hom (ev h x c)) = θ (χ c) := by
  have m : (Scheme.ΓSpecIso (CommRingCat.of (cR h x))).inv ≫ ((cξ h x).appIso ⊤).inv ≫
      X.presheaf.map (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ cξ h x ''ᵁ ⊤)).op ≫
      X.presheaf.map (homOfLE hW).op ≫ w.appLE W (w ⁻¹ᵁ W) le_rfl =
      CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op := by
    have hc := appLE_chart (cξ h x) a w hw W (hW.trans inf_le_left) (w ⁻¹ᵁ W) le_rfl
    erw [Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]
    erw [Scheme.Hom.map_appLE] at hc
    exact hc
  have key : ((w.app W).hom.comp (X.presheaf.map (homOfLE hW).op).hom).comp (ev h x) = θ.comp χ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : cR h x))
    ext r
    have e1 := congrArg (fun f => f.hom r) m
    have e2 := congrArg (fun f => f (a r)) hθ
    have e3 := congrArg (fun f => f r) hχ
    simp only [RingHom.comp_apply] at e2 e3 ⊢
    rw [e3, e2]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1
    rw [ev, IsLocalization.Away.lift, IsLocalization.lift_eq, Scheme.Hom.app_eq_appLE]
    exact e1
  exact congrArg (fun f => f c) key

end GlobalTheory.UnitGlueTransport

namespace GlobalTheory.UnitGlueTransport

theorem ratioProp_of_chart : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (A : Type) [CommRing A] (w : Sp A ⟶ X) (a1 : cR h x →+* A) (a2 : cR h y →+* A), IsOpenImmersion w → spMap a1 ≫ cξ h x = w → spMap a2 ≫ cξ h y = w → Set.range w = Set.range (cξ h x) ∩ Set.range (cξ h y) → ∀ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical → (∀ (χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A)), χ1.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap (cR h y) _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (cu h y : Localization.Away (p : cR h y)) = χ1 (cu h x : Localization.Away (p : cR h x))) → ∃ u' : Γ(X, Uc h x ⊓ Uc h y)ˣ, RatioProp h x y u' := by
  intro p _ X Xw K h x y A _ w a1 a2 hw hw1 hw2 hrange u hu hχ
  have hVeq : Uc h x ⊓ Uc h y = w.opensRange := by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_inf, Uc, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.coe_opensRange]
    exact hrange.symm
  set V := Uc h x ⊓ Uc h y with hVdef
  set W := V ⊓ Xp X p with hWdef
  have hWV : W ≤ V := inf_le_left
  have hWx : W ≤ Uc h x ⊓ Xp X p := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hWy : W ≤ Uc h y ⊓ Xp X p := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hιiso : IsIso (w.app W) := Scheme.Hom.isIso_app w W (hWV.trans hVeq.le)
  have hιinj : Function.Injective (w.app W).hom := (ConcreteCategory.bijective_of_isIso (w.app W)).1
  have hV : ⊤ ≤ w ⁻¹ᵁ V := by rw [hVeq, Scheme.Hom.preimage_opensRange]
  have hφ : IsIso (w.appLE V ⊤ hV) := by
    have h1 : IsIso (w.app V) := Scheme.Hom.isIso_app w V hVeq.le
    have h2 : (⊤ : (Sp A).Opens) = w ⁻¹ᵁ V := le_antisymm hV le_top
    have h3 : IsIso (homOfLE hV) := by
      have : homOfLE hV = eqToHom h2 := rfl
      rw [this]; infer_instance
    rw [Scheme.Hom.appLE]; infer_instance
  let φ := w.appLE V ⊤ hV ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom
  let e : Γ(X, V) ≃+* A := RingEquiv.ofBijective φ.hom (ConcreteCategory.bijective_of_isIso φ)
  have he : ∀ z, (w.appLE V ⊤ hV).hom (e.symm z) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom z := by
    intro z
    have h0 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((w.appLE V ⊤ hV).hom (e.symm z)) = z :=
      e.apply_symm_apply z
    have h1 : (w.appLE V ⊤ hV).hom (e.symm z) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((w.appLE V ⊤ hV).hom (e.symm z))) := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    exact h1.trans (congrArg _ h0)
  let u' : Γ(X, V)ˣ := Units.map e.symm.toRingHom.toMonoidHom u
  refine ⟨u', ?_⟩
  unfold RatioProp
  refine ⟨?_, ?_⟩
  · let gB : A →+* Γ(Sp A, w ⁻¹ᵁ W) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op).hom
    have hpB : IsUnit ((p : Γ(Sp A, w ⁻¹ᵁ W))) := by
      have h0 := (isUnit_natCast_res h x).map ((w.app W).hom.comp (X.presheaf.map (homOfLE hWx).op).hom)
      erw [map_natCast, map_natCast] at h0
      exact h0
    have hgp : IsUnit (gB (p : A)) := by rw [map_natCast]; exact hpB
    let θ : Localization.Away (p : A) →+* Γ(Sp A, w ⁻¹ᵁ W) := IsLocalization.Away.lift (p : A) hgp
    have hθ : θ.comp (algebraMap A _) = gB := IsLocalization.Away.lift_comp _ hgp
    have hp1 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a1) (p : cR h x)) := by
      rw [map_natCast, ← map_natCast (algebraMap A (Localization.Away (p : A))) p]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hp2 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a2) (p : cR h y)) := by
      rw [map_natCast, ← map_natCast (algebraMap A (Localization.Away (p : A))) p]
      exact IsLocalization.Away.algebraMap_isUnit _
    let χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A) := IsLocalization.Away.lift _ hp1
    let χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A) := IsLocalization.Away.lift _ hp2
    have hχ1 : χ1.comp (algebraMap _ _) = (algebraMap A _).comp a1 := IsLocalization.Away.lift_comp _ hp1
    have hχ2 : χ2.comp (algebraMap _ _) = (algebraMap A _).comp a2 := IsLocalization.Away.lift_comp _ hp2
    have key := hχ χ1 χ2 hχ1 hχ2
    have ex := ev_transport h x w a1 hw1 W hWx θ hθ χ1 hχ1 (cu h x)
    have ey := ev_transport h y w a2 hw2 W hWy θ hθ χ2 hχ2 (cu h y)
    have eu : (w.app W).hom ((X.presheaf.map (homOfLE hWV).op).hom (u' : Γ(X, V))) = gB u := by
      have m : X.presheaf.map (homOfLE hWV).op ≫ w.app W =
          w.appLE V ⊤ hV ≫ (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op := by
        rw [Scheme.Hom.app_eq_appLE]
        erw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
      have m' := congrArg (fun f => f.hom (u' : Γ(X, V))) m
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at m'
      rw [m']
      have : (u' : Γ(X, V)) = e.symm (u : A) := rfl
      rw [this, he]
      rfl
    have goalEq : (w.app W).hom ((X.presheaf.map (homOfLE hWV).op).hom (u' : Γ(X, V))) *
        (w.app W).hom ((X.presheaf.map (homOfLE hWy).op).hom (ev h y (cu h y))) =
        (w.app W).hom ((X.presheaf.map (homOfLE hWx).op).hom (ev h x (cu h x))) := by
      rw [eu, ey, ex, ← key, map_mul]
      congr 1
      exact (congrArg (fun f => f (u : A)) hθ).symm
    apply Units.ext
    apply hιinj
    rw [Units.val_mul, map_mul]
    exact goalEq
  · have h0 : ((u' : Γ(X, V)) - 1) = e.symm ((u : A) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [h0]
    exact radical_map e.symm.toRingHom p hu

end GlobalTheory.UnitGlueTransport
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_ratio_on_chart_overlap : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (A : Type) [CommRing A] (w : Sp A ⟶ X) (a1 : cR h x →+* A) (a2 : cR h y →+* A), IsOpenImmersion w → spMap a1 ≫ cξ h x = w → spMap a2 ≫ cξ h y = w → Set.range w = Set.range (cξ h x) ∩ Set.range (cξ h y) → ∀ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical → (∀ (χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A)), χ1.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap (cR h y) _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (cu h y : Localization.Away (p : cR h y)) = χ1 (cu h x : Localization.Away (p : cR h x))) → ∃ u' : Γ(X, Uc h x ⊓ Uc h y)ˣ, RatioProp h x y u' := by
  atlas_forward_decl GlobalTheory.UnitGlueTransport.ratioProp_of_chart
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue.IsLBProof

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    res h2 (res h1 u) = res (h2.trans h1) u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_inj {X : Scheme.{0}} [IsIntegral X] (P : X.Opens) (hP : (P : Set X).Nonempty) (V : X.Opens) :
    Function.Injective (res (inf_le_left : V ⊓ P ≤ V)) := by
  by_cases hV : (V : Set X).Nonempty
  · have hne : ((V ⊓ P : X.Opens) : Set X).Nonempty := by
      obtain ⟨z, _, hz⟩ := (PreirreducibleSpace.isPreirreducible_univ (X := X)) _ _ V.isOpen P.isOpen
        (by simpa using hV) (by simpa using hP)
      exact ⟨z, hz⟩
    haveI : Nonempty (V ⊓ P : X.Opens) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    intro a b hab
    have hi := map_injective_of_isIntegral X (homOfLE (inf_le_left : V ⊓ P ≤ V))
    ext
    apply hi
    have := congrArg (fun w : Γ(X, V ⊓ P)ˣ => (w : Γ(X, V ⊓ P))) hab
    simpa [res] using this
  · have hb : V = ⊥ := by
      ext z; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hz; exact hV ⟨z, hz⟩
    subst hb
    intro a b _
    exact Subsingleton.elim a b

theorem ratio_res {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens} {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]}
    (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (u : Γ(X, Uc h x ⊓ Uc h y)ˣ) (hu : RatioProp h x y u)
    (W : X.Opens) (hW : W ≤ Uc h x ⊓ Uc h y ⊓ Xp X p) :
    res (hW.trans inf_le_left) u *
      res (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (Cx h y) =
    res (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (Cx h x) := by
  have := congrArg (res hW) hu.1
  rwa [map_mul, res_res', res_res', res_res'] at this

end GlobalTheory.UnitGlue.IsLBProof

namespace GlobalTheory.UnitGlue

open GlobalTheory.UnitGlue.IsLBProof in

theorem glueLB_isLB : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), IsIntegral X → (Xw : Set X).Nonempty → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (∀ x y : X, ∃ u, RatioProp h x y u) → (glueLB h).IsLB := by
  intro p _ X Xw K h hI hw hle hex
  have hP : ((Xp X p : X.Opens) : Set X).Nonempty := hw.mono hle
  have hR : ∀ x y, RatioProp h x y (gU h x y) := fun x y => by
    unfold gU; rw [dif_pos (hex x y)]; exact (hex x y).choose_spec
  refine ⟨?_, fun (i : X) => ?_, fun (i j k : X) => ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨x, ?_⟩
    obtain ⟨y, hy⟩ := (c_spec h x).2.1
    show x ∈ ((cξ h x ''ᵁ ⊤ : X.Opens) : Set X)
    exact ⟨y, trivial, hy⟩
  · show res (le_inf le_rfl le_rfl : Uc h i ≤ Uc h i ⊓ Uc h i) (gU h i i) = 1
    apply res_inj (Xp X p) hP (Uc h i)
    rw [res_res', map_one]
    have hW : Uc h i ⊓ Xp X p ≤ Uc h i ⊓ Uc h i ⊓ Xp X p := le_inf (le_inf inf_le_left inf_le_left) inf_le_right
    have h1 := ratio_res h i i _ (hR i i) _ hW
    have h2 : res (hW.trans inf_le_left) (gU h i i) = 1 := by
      have h3 := h1
      rw [mul_eq_right] at h3
      exact h3
    exact h2
  · show res (inf_le_left : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h i ⊓ Uc h j) (gU h i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h j ⊓ Uc h k) (gU h j k) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h i ⊓ Uc h k) (gU h i k)
    apply res_inj (Xp X p) hP _
    rw [map_mul, res_res', res_res', res_res']
    have hT : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h i ⊓ Uc h j ⊓ Xp X p :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hT2 : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h j ⊓ Uc h k ⊓ Xp X p :=
      le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right)) inf_le_right
    have hT3 : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h i ⊓ Uc h k ⊓ Xp X p :=
      le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)) inf_le_right
    have hij := ratio_res h i j _ (hR i j) _ hT
    have hjk := ratio_res h j k _ (hR j k) _ hT2
    have hik := ratio_res h i k _ (hR i k) _ hT3
    apply mul_right_cancel (b := res (hT2.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (Cx h k))
    rw [_root_.mul_assoc, hjk, hij, hik]

end GlobalTheory.UnitGlue
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_line_bundle_invertible : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), IsIntegral X → (Xw : Set X).Nonempty → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (∀ x y : X, ∃ u, RatioProp h x y u) → (glueLB h).IsLB := by
  atlas_forward_decl GlobalTheory.UnitGlue.glueLB_isLB
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem natCast_eq_zero_reducedSpecialFibre {F : Type} [Field F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) (hp : (p : F) ∈ V.nonunits) {X : Scheme.{0}} (s : X ⟶ Sp V)
    (U : (reducedSpecialFibre s).Opens) : (p : Γ(reducedSpecialFibre s, U)) = 0 := by
  obtain ⟨ha, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hp
  have hpV : ((p : V) : V) ∈ IsLocalRing.maximalIdeal V := by
    convert hm using 1
    ext
    simp
  have hk : (p : IsLocalRing.ResidueField V) = 0 := by
    rw [← map_natCast (IsLocalRing.residue V) p]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hpV
  let q : reducedSpecialFibre s ⟶ Spec (.of (IsLocalRing.ResidueField V)) :=
    (specialFibre s).nilradical.subschemeι ≫ pullback.snd _ _
  have e : (p : Γ(reducedSpecialFibre s, U)) =
      ((reducedSpecialFibre s).presheaf.map (homOfLE le_top).op).hom
        (q.appTop.hom ((Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField V))).inv.hom
          (p : IsLocalRing.ResidueField V))) := by
    simp only [map_natCast]
  rw [e, hk]
  simp only [map_zero]

theorem pullU_reducedSpecialι_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) (hp : (p : F) ∈ V.nonunits) {X : Scheme.{0}} (s : X ⟶ Sp V)
    (W : X.Opens) (u : Γ(X, W)ˣ) (hu : ((u : Γ(X, W)) - 1) ∈ (Ideal.span {(p : Γ(X, W))}).radical) :
    pullU (reducedSpecialι s) W u = 1 := by
  haveI : IsReduced (reducedSpecialFibre s) := GlobalTheory.RedFibreField.isReduced_nilradical_subscheme _
  obtain ⟨n, hn⟩ := hu
  rw [Ideal.mem_span_singleton] at hn
  have h0 : (((reducedSpecialι s).app W).hom (u : Γ(X, W)) - 1) ^ n = 0 := by
    have hd := map_dvd ((reducedSpecialι s).app W).hom hn
    rw [map_natCast, natCast_eq_zero_reducedSpecialFibre V p hp s, map_pow, map_sub, map_one] at hd
    exact zero_dvd_iff.1 hd
  have h1 : ((reducedSpecialι s).app W).hom (u : Γ(X, W)) - 1 = 0 :=
    IsReduced.eq_zero _ ⟨n, h0⟩
  ext
  exact sub_eq_zero.1 h1

theorem gU_ratioProp {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens}
    {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]} (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X)
    (hR : ∃ u, RatioProp h x y u) : RatioProp h x y (gU h x y) := by
  unfold gU
  rw [dif_pos hR]
  exact hR.choose_spec

theorem glueLB_reducedSpecial_gen : ∀ (F : Type) [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → ∃ t : ((glueLB h).pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen := by
  intro F _ V _ p _ hp X s Xw K h hR
  refine ⟨⟨fun _ => 1⟩, ?_⟩
  intro i j
  rw [map_one, map_one, _root_.mul_one]
  symm
  have key : ∀ (W : (reducedSpecialFibre s).Opens) (k : PUnit)
      (hh : W ≤ reducedSpecialι s ⁻¹ᵁ ((glueLB h).U (i k) ⊓ (glueLB h).U (j k))),
      res hh (pullU (reducedSpecialι s) _ ((glueLB h).g (i k) (j k))) ^ (1 : ℤ) = 1 := by
    intro W k hh
    rw [pullU_reducedSpecialι_eq_one V p hp s (W := (glueLB h).U (i k) ⊓ (glueLB h).U (j k))
      (u := (glueLB h).g (i k) (j k)) (gU_ratioProp h _ _ (hR _ _)).2, map_one, one_zpow]
  exact @Finset.prod_eq_one PUnit (Γ(reducedSpecialFibre s,
    LB.wchart (glueLB h) (fun _ : PUnit => reducedSpecialι s) i ⊓
      LB.wchart (glueLB h) (fun _ : PUnit => reducedSpecialι s) j)ˣ) Finset.univ _ _ (fun k _ => key _ k _)

end GlobalTheory.UnitGlue
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_bundle_special_fibre_generator : ∀ (F : Type) [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → ∃ t : ((glueLB h).pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen := by
  atlas_forward_decl GlobalTheory.UnitGlue.glueLB_reducedSpecial_gen
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem mem_genericι_preimage_Xp (F : Type) [Field F] [NumberField F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V)
    (y : genericFibre s) : y ∈ genericι s ⁻¹ᵁ Xp X p := by
  have hK : IsUnit ((p : ℕ) : FractionRing V) := by
    refine IsUnit.mk0 _ ?_
    rw [← map_natCast (algebraMap V (FractionRing V))]
    refine (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ?_
    intro h0
    have := congrArg (fun v : V => (v : F)) h0
    simp at this
    exact (Fact.out : p.Prime).ne_zero this
  have hU : IsUnit ((p : ℕ) : Γ(genericFibre s, genericι s ⁻¹ᵁ ⊤)) := by
    have := hK.map (((genericFibre s).presheaf.map
      (homOfLE (le_top : genericι s ⁻¹ᵁ ⊤ ≤ genericStr s ⁻¹ᵁ ⊤)).op).hom.comp
      (((genericStr s).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom))
    simpa only [map_natCast] using this
  show y ∈ genericι s ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤))
  rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit _ hU]
  trivial

theorem germ_res_res_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {A : X.Opens} {W W' : Y.Opens} (h1 : W ≤ W')
    (h2 : W' ≤ f ⁻¹ᵁ A) (c : Γ(X, A)ˣ) (y : Y) (hy : y ∈ W) :
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU y hy (res h1 (res h2 (pullU f A c))) =
      Units.map (f.stalkMap y).hom (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU (f.base y) (h2 (h1 hy)) c) := by
  rw [ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res,
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU]

theorem germ_res_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {A : X.Opens} {W : Y.Opens}
    (h2 : W ≤ f ⁻¹ᵁ A) (c : Γ(X, A)ˣ) (y : Y) (hy : y ∈ W) :
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU y hy (res h2 (pullU f A c)) =
      Units.map (f.stalkMap y).hom (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU (f.base y) (h2 hy) c) := by
  rw [ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU]

theorem sigGen_isGen_of_ratio : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → (sigGen h s).IsGen := by
  intro F _ _ V _ p _ X s Xw K h hR
  have hc : ∀ j : PUnit → X, LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤
      genericι s ⁻¹ᵁ (Uc h (j PUnit.unit) ⊓ Xp X p) := fun j y hy =>
    ⟨Set.mem_iInter.1 hy PUnit.unit, mem_genericι_preimage_Xp F V p X s y⟩
  intro (i : PUnit → X) (j : PUnit → X)
  have hsi : (sigGen h s).s i = res (hc i) (pullU (genericι s) _ (Cx h (i PUnit.unit))) := dif_pos (hc i)
  have hsj : (sigGen h s).s j = res (hc j) (pullU (genericι s) _ (Cx h (j PUnit.unit))) := dif_pos (hc j)
  have hg : GlobalTheory.UnitGlue.gU h (i PUnit.unit) (j PUnit.unit) = (hR (i PUnit.unit) (j PUnit.unit)).choose :=
    dif_pos (hR _ _)
  have hr := ((hR (i PUnit.unit) (j PUnit.unit)).choose_spec).1
  rw [← hg] at hr
  rw [hsi, hsj]
  apply ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.unit_ext
  intro y hy
  have hxi : (genericι s).base y ∈ Uc h (i PUnit.unit) := Set.mem_iInter.1 hy.1 PUnit.unit
  have hxj : (genericι s).base y ∈ Uc h (j PUnit.unit) := Set.mem_iInter.1 hy.2 PUnit.unit
  have hx : (genericι s).base y ∈ Uc h (i PUnit.unit) ⊓ Uc h (j PUnit.unit) ⊓ Xp X p := ⟨⟨hxi, hxj⟩, mem_genericι_preimage_Xp F V p X s y⟩
  have hr' := congrArg (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU _ hx) hr
  simp only [map_mul, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res] at hr'
  have hle : ((glueLB h).pull (genericι s)).U i ⊓ ((glueLB h).pull (genericι s)).U j ≤
      genericι s ⁻¹ᵁ (Uc h (i PUnit.unit) ⊓ Uc h (j PUnit.unit)) := fun z hz =>
    ⟨Set.mem_iInter.1 hz.1 PUnit.unit, Set.mem_iInter.1 hz.2 PUnit.unit⟩
  have hgl : ((glueLB h).pull (genericι s)).g i j =
      res hle (pullU (genericι s) _ (GlobalTheory.UnitGlue.gU h (i PUnit.unit) (j PUnit.unit))) :=
    by
      have e := Fintype.prod_unique (fun k : PUnit => (res (fun z hz => ⟨Set.mem_iInter.1 hz.1 k, Set.mem_iInter.1 hz.2 k⟩ :
        LB.wchart (glueLB h) (fun _ : PUnit => genericι s) i ⊓ LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤
          genericι s ⁻¹ᵁ (Uc h (i k) ⊓ Uc h (j k)))
        (pullU (genericι s) (Uc h (i k) ⊓ Uc h (j k)) (GlobalTheory.UnitGlue.gU h (i k) (j k)))) ^ (1:ℤ))
      exact e.trans (zpow_one _)
  rw [hgl, map_mul]
  refine (germ_res_res_pull (genericι s) _ _ _ y hy).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (germ_res_pull (genericι s) hle _ y hy).symm
    (germ_res_res_pull (genericι s) _ _ _ y hy).symm)
  rw [← map_mul, ← hr']

end GlobalTheory.UnitGlue
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_generator_is_generator : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → (sigGen h s).IsGen := by
  atlas_forward_decl GlobalTheory.UnitGlue.sigGen_isGen_of_ratio
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_point_factors_open_immersion : ∀ (S : Type) [CommRing S] [IsLocalRing S] (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (yb : Sp S ⟶ X), IsOpenImmersion ξ → yb (IsLocalRing.closedPoint S) ∈ Set.range ξ → ∃ φ : R →+* S, spMap φ ≫ ξ = yb := by
  first | exact @GlobalTheory.localSpec_fac_of_closedPoint_mem_range | exact GlobalTheory.localSpec_fac_of_closedPoint_mem_range | (intros; apply GlobalTheory.localSpec_fac_of_closedPoint_mem_range <;> assumption)
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue.EvalPt

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem norm_algebraMap_unit (p : ℕ) [Fact p.Prime] (u : (𝓞_ℂ_[p])ˣ) :
    ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (u : 𝓞_ℂ_[p])‖ = 1 := by
  have hm : ∀ a : 𝓞_ℂ_[p], ‖(a : ℂ_[p])‖ ≤ 1 := fun a => by
    have this : (Valued.v (a : ℂ_[p]) : NNReal) ≤ 1 := a.2
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).2 this
  have h1 : ((u : 𝓞_ℂ_[p]) : ℂ_[p]) * ((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) = 1 := by
    exact_mod_cast u.mul_inv
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  have h3 := hm (u : 𝓞_ℂ_[p])
  have h4 := hm ((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p])
  show ‖((u : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1
  nlinarith [norm_nonneg ((u : 𝓞_ℂ_[p]) : ℂ_[p]), norm_nonneg (((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) : ℂ_[p])]

theorem isUnit_natCast_fraction {F : Type} [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ)
    [Fact p.Prime] : IsUnit (p : FractionRing V) := by
  refine IsUnit.mk0 _ ?_
  intro h0
  have hV : (p : V) = 0 :=
    IsFractionRing.injective V (FractionRing V) (by rw [map_natCast, h0, map_zero])
  have hF : (p : F) = 0 := by
    have := map_natCast V.subtype p
    rw [hV, map_zero] at this
    exact this.symm
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hF

theorem isUnit_natCast_generic {F : Type} [Field F] [NumberField F] {V : ValuationSubring F}
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (s : X ⟶ Sp V)
    (U : (genericFibre s).Opens) : IsUnit (p : Γ(genericFibre s, U)) := by
  have h1 : IsUnit (p : Γ(Spec (.of (FractionRing V)), ⊤)) := by
    have := (isUnit_natCast_fraction V p).map (Scheme.ΓSpecIso (.of (FractionRing V))).inv.hom
    rwa [map_natCast] at this
  have h2 := h1.map (genericStr s).appTop.hom
  rw [map_natCast] at h2
  have h3 := h2.map ((genericFibre s).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
  rwa [map_natCast] at h3

theorem preimage_Xp_generic {F : Type} [Field F] [NumberField F] {V : ValuationSubring F}
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (s : X ⟶ Sp V) :
    genericι s ⁻¹ᵁ Xp X p = ⊤ := by
  rw [Xp, Scheme.preimage_basicOpen, map_natCast]
  exact Scheme.basicOpen_of_isUnit _ (isUnit_natCast_generic p s _)

theorem appLE_congr {T Z : Scheme.{0}} {f g : T ⟶ Z} (e : f = g) (U : Z.Opens) (V : T.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) : f.appLE U V hV = g.appLE U V (e ▸ hV) := by
  subst e; rfl

theorem appLE_top_top {T Z : Scheme.{0}} (f : T ⟶ Z) (hV : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ hV = f.appTop :=
  Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)

end GlobalTheory.UnitGlue.EvalPt

namespace GlobalTheory.UnitGlue.EvalPt
open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem evalPt_norm : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x : X) (φ : cR h x →+* 𝓞_ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ X), spMap φ ≫ cξ h x = yb → ∀ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : ((glueLB h).pull yb).Gen) (cc : ℂ_[p]ˣ), GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s (glueLB h) (sigGen h s) yb y e cc → ∃ ψ : Localization.Away (p : cR h x) →+* ℂ_[p], ψ.comp (algebraMap (cR h x) _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ ∧ ‖ψ (cu h x : Localization.Away (p : cR h x))‖ = ‖(cc : ℂ_[p])‖ := by
  intro F _ _ V _ p _ X s Xw K h x φ yb hyb y hy e cc hc
  subst hyb
  let j : PUnit → (glueLB h).ι := fun _ => x
  have hW : ∀ {T : Scheme.{0}} (f : T ⟶ X),
      LB.wchart (glueLB h) (fun _ : PUnit => f) j = f ⁻¹ᵁ Uc h x :=
    fun f => TopologicalSpace.Opens.ext (by ext z; simp [LB.wchart, glueLB, j])
  have hYb : (spMap φ ≫ cξ h x) ⁻¹ᵁ Uc h x = ⊤ := by
    change spMap φ ⁻¹ᵁ (cξ h x ⁻¹ᵁ (cξ h x ''ᵁ ⊤)) = ⊤
    rw [Scheme.Hom.preimage_image_eq]
    rfl
  have hYg : y ⁻¹ᵁ (genericι s ⁻¹ᵁ Uc h x) = ⊤ := by
    change (y ≫ genericι s) ⁻¹ᵁ Uc h x = ⊤
    rw [hy]
    change Spec.map _ ⁻¹ᵁ ((spMap φ ≫ cξ h x) ⁻¹ᵁ Uc h x) = ⊤
    rw [hYb]
    rfl
  have h₁ : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤ y ⁻¹ᵁ ((glueLB h).pull (genericι s)).U j := by
    change ⊤ ≤ y ⁻¹ᵁ LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j
    rw [hW, hYg]
  have h₂ : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ⁻¹ᵁ ((glueLB h).pull (spMap φ ≫ cξ h x)).U j := by
    change ⊤ ≤ Spec.map _ ⁻¹ᵁ LB.wchart (glueLB h) (fun _ : PUnit => spMap φ ≫ cξ h x) j
    rw [hW, hYb]
    exact le_top
  have hcond : LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤ genericι s ⁻¹ᵁ (Uc h x ⊓ Xp X p) := by
    rw [hW]
    intro z hz
    show z ∈ genericι s ⁻¹ᵁ Uc h x ⊓ genericι s ⁻¹ᵁ Xp X p
    rw [preimage_Xp_generic p s]
    exact ⟨hz, trivial⟩
  have hsig : (sigGen h s).s j = res hcond (pullU (genericι s) _ (Cx h x)) := dif_pos hcond
  have key := hc j ⊤ h₁ h₂
  rw [hsig] at key
  let χ : Γ(X, Uc h x ⊓ Xp X p) ⟶ Γ(Spec (.of ℂ_[p]), ⊤) :=
    (genericι s).appLE (Uc h x ⊓ Xp X p) _ hcond ≫ y.appLE _ ⊤ h₁
  let ψ : Localization.Away (p : cR h x) →+* ℂ_[p] :=
    (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.comp (χ.hom.comp (ev h x))
  have hψc : ψ (cu h x : Localization.Away (p : cR h x)) = (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res h₁ (pullU y _ (res hcond (pullU (genericι s) _ (Cx h x))))) : Γ(Spec (.of ℂ_[p]), ⊤)) := rfl
  have hF1 : (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res (U := ⊤) (V := ⊤) le_top (constUnit (𝟙 (Spec (.of ℂ_[p]))) cc) : Γ(Spec (.of ℂ_[p]), ⊤))) = cc := by
    have hid : (homOfLE (le_top : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    simp [res, constUnit, hid]
  have htop : (⊤ : (Sp 𝓞_ℂ_[p]).Opens) ≤ ((glueLB h).pull (spMap φ ≫ cξ h x)).U j := by
    change ⊤ ≤ LB.wchart (glueLB h) (fun _ : PUnit => spMap φ ≫ cξ h x) j
    rw [hW, hYb]
  have hM : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).app
        (((glueLB h).pull (spMap φ ≫ cξ h x)).U j) ≫
      (Spec (.of ℂ_[p])).presheaf.map (homOfLE h₂).op ≫ (Scheme.ΓSpecIso (.of ℂ_[p])).hom =
      (Sp 𝓞_ℂ_[p]).presheaf.map (homOfLE htop).op ≫ (Scheme.ΓSpecIso (.of 𝓞_ℂ_[p])).hom ≫
        CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by
    have e1 : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).app
        (((glueLB h).pull (spMap φ ≫ cξ h x)).U j) ≫ (Spec (.of ℂ_[p])).presheaf.map (homOfLE h₂).op =
        (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).appLE _ ⊤ h₂ := rfl
    rw [← Category.assoc, e1, ← Scheme.Hom.map_appLE _ (U := ⊤) (by simp) (homOfLE htop).op,
      Category.assoc]
    erw [appLE_top_top]
    rw [Scheme.ΓSpecIso_naturality]
  have hF2 : (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res h₂ (pullU (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))) _ (e.s j))) :
        Γ(Spec (.of ℂ_[p]), ⊤)) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] ((Units.map (Scheme.ΓSpecIso (.of 𝓞_ℂ_[p])).hom.hom.toMonoidHom
        (res htop (e.s j)) : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) := by
    have := congrArg (fun m => m.hom ((e.s j : Γ(Sp 𝓞_ℂ_[p], ((glueLB h).pull (spMap φ ≫ cξ h x)).U j)))) hM
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hinvapp : ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (Uc h x) =
      (Sp (cR h x)).presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op := by
    show ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (cξ h x ''ᵁ ⊤) = _
    rw [Iso.inv_comp_eq, Scheme.Hom.appIso_hom, Category.assoc, ← Functor.map_comp]
    simp [Uc]
  have hinvapp' : ∀ {Z : CommRingCat.{0}} (k : Γ(Sp (cR h x), cξ h x ⁻¹ᵁ Uc h x) ⟶ Z),
      ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (Uc h x) ≫ k =
        (Sp (cR h x)).presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op ≫ k := by
    intro Z k
    rw [← hinvapp]
    exact (Category.assoc _ _ _).symm
  have hmor : (Scheme.ΓSpecIso (.of (cR h x))).inv ≫ ((cξ h x).appIso ⊤).inv ≫
      X.presheaf.map (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ Uc h x)).op ≫ χ ≫
        (Scheme.ΓSpecIso (.of ℂ_[p])).hom =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by
    rw [show χ = _ from Scheme.Hom.appLE_comp_appLE y (genericι s) _ _ _ hcond h₁]
    erw [reassoc_of% (Scheme.Hom.map_appLE (y ≫ genericι s) _ (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ Uc h x)).op)]
    rw [appLE_congr (hy.trans (Category.assoc _ _ _).symm), Scheme.Hom.comp_appLE, Category.assoc]
    erw [hinvapp']
    erw [reassoc_of% (Scheme.Hom.map_appLE (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ spMap φ) _ (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op)]
    erw [appLE_top_top]
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, reassoc_of% (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)), Iso.inv_hom_id_assoc]
  refine ⟨ψ, ?_, ?_⟩
  · ext r
    have := congrArg (fun m => m.hom r) hmor
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    show (Scheme.ΓSpecIso _).hom.hom (χ.hom (ev h x (algebraMap _ _ r))) = algebraMap 𝓞_ℂ_[p] ℂ_[p] (φ r)
    rw [← this, ev, IsLocalization.Away.lift, IsLocalization.lift_eq]
    rfl
  · have key' := congrArg (fun u : Γ(Spec (.of ℂ_[p]), ⊤)ˣ =>
      (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom (u : Γ(Spec (.of ℂ_[p]), ⊤))) key
    dsimp only at key'
    rw [Units.val_mul, map_mul] at key'
    rw [hψc, key', hF1, hF2, norm_mul, norm_algebraMap_unit, _root_.mul_one]
end GlobalTheory.UnitGlue.EvalPt
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_point_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x : X) (φ : cR h x →+* 𝓞_ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ X), spMap φ ≫ cξ h x = yb → ∀ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : ((glueLB h).pull yb).Gen) (cc : ℂ_[p]ˣ), GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s (glueLB h) (sigGen h s) yb y e cc → ∃ ψ : Localization.Away (p : cR h x) →+* ℂ_[p], ψ.comp (algebraMap (cR h x) _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ ∧ ‖ψ (cu h x : Localization.Away (p : cR h x))‖ = ‖(cc : ℂ_[p])‖ := by
  atlas_forward_decl GlobalTheory.UnitGlue.EvalPt.evalPt_norm
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

theorem exists_glued_bundle : (∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → IsOpenImmersion w → spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∃ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical ∧ ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1))) → DensSt → ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x : X, UnitChartAt p Xw K x) → ∃ D : LB X, D.IsLB ∧ (∃ t : (D.pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen) ∧ ∃ sig : (D.pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s)).Gen, sig.IsGen ∧ ∀ yb, IsTest p Xw yb → ∀ (y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s), y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : (D.pull yb).Gen) (cc : ℂ_[p]ˣ), e.IsGen → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s D sig yb y e cc → ∀ κ ∈ K yb, ‖(cc : ℂ_[p])‖ = ‖κ‖ := by
  intro ZetaZeros hDens F _ _ V _ p _ hp X s Xw hXi hXn hproj hflat hXw hne K hK h
  have hR : ∀ x y : X, ∃ u, RatioProp h x y u := by
    intro x y
    obtain ⟨A, _, w, a1, a2, hw, h1, h2, hr⟩ :=
      GlobalTheory.T.exists_affine_intersection_charts V X s hproj (cR h x) (cR h y) (cξ h x) (cξ h y) inferInstance inferInstance
    obtain ⟨u, hu1, hu2⟩ := ZetaZeros F V p hp hDens X s Xw hXi hXn hproj hflat hXw hne K hK (cR h x) (cR h y) A (cξ h x)
      (cξ h y) w (cu h x) (cu h y) a1 a2 inferInstance inferInstance hw h1 h2 (c_spec h x).2.2 (c_spec h y).2.2
    exact GlobalTheory.T.unit_ratio_on_chart_overlap p X Xw K h x y A w a1 a2 hw h1 h2 hr u hu1 hu2
  refine ⟨glueLB h, GlobalTheory.T.glued_line_bundle_invertible p X Xw K h hXi hne hXw hR, GlobalTheory.T.glued_bundle_special_fibre_generator F V p hp X s Xw K h hR, sigGen h s,
    GlobalTheory.T.glued_generator_is_generator F V p X s Xw K h hR, ?_⟩
  intro yb hyb y hy e cc _ hco κ hκ
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.local_point_factors_open_immersion 𝓞_ℂ_[p] X (cR h (yb (IsLocalRing.closedPoint 𝓞_ℂ_[p]))) (cξ h _) yb inferInstance
    (c_spec h _).2.1
  obtain ⟨ψ, hψ, hn⟩ := GlobalTheory.T.chart_point_generic_fibre F V p X s Xw K h _ φ yb hφ y hy e cc hco
  have hc := (c_spec h _).2.2 φ (by rw [hφ]; exact hyb) ψ hψ κ (by rw [hφ]; exact hκ)
  rw [← hn]
  set a := ψ (cu h (yb (IsLocalRing.closedPoint 𝓞_ℂ_[p])) : Localization.Away _)
  have e1 : a = (a - κ) + κ := by ring
  rw [e1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hc.ne, max_eq_right hc.le]

end GlobalTheory.UnitGlue
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charts_normal_projective_covering : (∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → IsOpenImmersion w → spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∃ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical ∧ ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1))) → DensSt → ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x : X, UnitChartAt p Xw K x) → ∃ D : LB X, D.IsLB ∧ (∃ t : (D.pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen) ∧ ∃ sig : (D.pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s)).Gen, sig.IsGen ∧ ∀ yb, IsTest p Xw yb → ∀ (y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s), y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : (D.pull yb).Gen) (cc : ℂ_[p]ˣ), e.IsGen → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s D sig yb y e cc → ∀ κ ∈ K yb, ‖(cc : ℂ_[p])‖ = ‖κ‖ := by
  atlas_forward_decl GlobalTheory.UnitGlue.exists_glued_bundle
end
end
