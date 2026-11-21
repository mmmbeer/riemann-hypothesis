import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ArcClauseOfNotFrac

section
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure MultiWit (Y : Model Xo c β) {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} (a : ArcIn Dw l β A b) {r : ℕ}
    (δ : Fin r → LinearMap.BilinForm ℤ a.D₀.X) {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (f : A →+* R)
    (u : Fin r → R) {R' : Type} [CommRing R'] (ι : R →+* R') (y : Sp R' ⟶ Xo.XF c) where

  t : SAB H (Sp R)

  t' : SAB H (Sp R')

  m₁ : SABMap t' t (spMap ι)

  m₂ : SABMap t' Y.t (y ≫ Y.j)

  P : PELUnif I t

  φ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left

  he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A

  w : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ)

  e : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X

  spec :
    letI := H.starRing
    IsGrpPullback P.D.toPre.P.A a.D₀.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.D.toPre.P.A) (fun _ => 1)) P.D.toPre.rig
      (rigPullOf φ (spMap f) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (P.oD.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ x, (P.D.toPre.c (e x)).left ≫ φ = spMap f ≫ (a.D₀.c x).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing A) F] (uF : Fin r → F),
      (∀ x, algebraMap (FractionRing A) F (algebraMap A _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
      (∀ i, uF i = algebraMap (FractionRing R) F (algebraMap R _ (u i))) →
      (∀ x, GenRel w (LB.pullGen _ _ _ (P.D.toPre.psi (e x)) (Out.jFK (R := R) F))
        (LB.pullGen _ _ _ (a.D₀.psi x) (Out.jFK (R := A) F)) (∏ i, uF i ^ (δ i x x / 2))) ∧
      ∀ (s : R' →+* F), (∀ x, s (ι x) = algebraMap (FractionRing R) F (algebraMap R _ x)) →
        ∀ (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing A) k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G),
          ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
            (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
              HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v)) →
          ∀ (q₀ : Out.QkPt a.D₀ F k) (q : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := R) F ⟶ P.A.A)
            (x' : Sp F ⟶ t'.G.left),
            QkExt (algebraMap _ F) p₀ q₀ → q.y = e q₀.y →
            (∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (∏ i, uF i ^ (δ i q₀.y z / k))) →
            x' ≫ t'.G.hom = spMap s →
            x' ≫ m₁.φ = x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) →
            x' ≫ m₂.φ = spMap s ≫ y ≫ σ.left ≫ Y.m.φ →
            P.ToA F k q x

section General

variable {Y : Model Xo c β} {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : A →+* R} {R' : Type} [CommRing R'] {ι : R →+* R'}
  {y : Sp R' ⟶ Xo.XF c}


variable {r : ℕ} {δ : Fin r → LinearMap.BilinForm ℤ a.D₀.X} {u : Fin r → R}

def MultiWit.LieImg (W : MultiWit Y a δ I f u ι y) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR R ⟶ W.t.G) : Prop :=
  ∀ (n : ℕ) (vn : Sp (DualNumber (R ⧸ I ^ (n + 1))) ⟶ (Out.thickObj R I n W.t.G).left),
    vn ≫ (Out.fstG I n W.t.G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ v.left →
    ∀ x, GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn)
      (LB.pullGen _ _ _ (ν.s x) (spMap (dualMap ((Ideal.Quotient.mk (I ^ (n + 1))).comp f))))

end General

instance MultiRing.isDomain_series (K : Type) [Field K] (r : ℕ) : IsDomain (MvPowerSeries (Fin r) K) :=
  GlobalTheory.CohenStructure.isDomain_mvPowerSeries K r

end GlobalTheory.LocM.FJ
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
open Formalism.MainNotions.DIV.Cons (intO)

noncomputable section

namespace GlobalTheory.LocM.FJ.MultiData

theorem psiCoord_rescale {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (q : D.X → (FractionRing R)ˣ)
    {χ : D.X} {r s : R} (hr : PsiCoord D χ r)
    (hq : ((q χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s) :
    PsiCoord (GlobalTheory.TauTwist.rescale D q) χ (s * r) := by
  obtain ⟨x, ⟨j, h, hj, rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 hr
  refine (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D q) χ (s * r)).2
    ⟨q χ * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi χ) j h, ⟨j, h, hj, ?_⟩, ?_⟩
  · dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
    rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
    congr 1
    ext
    show (q χ : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (q χ : FractionRing R)))
    rw [CategoryTheory.Functor.map_id]
    exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
  · rw [Units.val_mul, hq, e, map_mul]

theorem exists_unit_psiCoord {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : Out.DegPre R) (χ : D.X)
    (h : PsiUnitOn D χ Set.univ) : ∃ v : Rˣ, PsiCoord D χ v := by
  obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D χ
  have hh := GlobalTheory.PsiCoordLocal.generic_le D χ j hj
  obtain ⟨s, hs, e⟩ := h j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
  obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 s
  have hu : IsUnit r := (MulEquiv.isUnit_map
    (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤) GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 hs
  exact ⟨hu.unit, j, hj, hh, e⟩

end GlobalTheory.LocM.FJ.MultiData

namespace GlobalTheory.LocM.FJ.MultiData

end GlobalTheory.LocM.FJ.MultiData
end
end
