import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOfTest

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem factor {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (ξ' : Spec (CommRingCat.of Ω') ⟶ X) (e : genPt ξ' = genPt ξ) :
    ∃ i : Ω →+* Ω', ξ' = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
  have key : ∀ (x x' : X) (_ : x' = x) (φ : X.presheaf.stalk x ⟶ CommRingCat.of Ω) [IsIso φ]
      (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of Ω'), ∃ i : Ω →+* Ω',
      Spec.map φ' ≫ X.fromSpecStalk x' = Spec.map (CommRingCat.ofHom i) ≫ Spec.map φ ≫ X.fromSpecStalk x := by
    intro x x' e φ _ φ'
    subst e
    refine ⟨(inv φ ≫ φ').hom, ?_⟩
    rw [CommRingCat.ofHom_hom, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id_assoc]
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h.bij
  obtain ⟨i, hi⟩ := @key _ _ e (Scheme.stalkClosedPointTo ξ) this (Scheme.stalkClosedPointTo ξ')
  refine ⟨i, ?_⟩
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ').symm.trans (hi.trans
    (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))

theorem spec_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

def SplitOver {O F : Type} [CommRing O] [Field F] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of O))
    (β : O →+* F) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (cst : F →+* Ω), IsCptGen ξ →
    ξ ≫ s = Spec.map (CommRingCat.ofHom (cst.comp β)) → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ cst.range





variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}




section
variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}


end


end GlobalTheory.CompanionTheory.Ar.TowerOfTest
