import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.MBLit

abbrev Qb : Type := AlgebraicClosure ℚ

def IsSemiStable {S : Scheme.{0}} (G : Over S) [GrpObj G] : Prop :=
  IsCommMonObj G ∧ Smooth G.hom ∧ IsSeparated G.hom ∧ QuasiCompact G.hom ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S), ∃ (G₀ : Over (Spec (.of Ω))) (_ : GrpObj G₀)
      (j : G₀ ⟶ (Over.pullback p).obj G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Nonempty (TorusExtension G₀)

def InK {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : LB A.left) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    ∃ c : LB.Gen ((Out.translDiff A M x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen

section CubicalWeight

variable {k : Type} [CommRing k] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {M : RigLB G} {σ : k →+* ℂ}

def IsCubist (c : CubicalStr G M) (Φ : Weight G.hom σ M.L) : Prop :=
  Φ.IsCInf ∧
  (∀ (j : PUnit → M.L.ι) (y : CxPts (𝟙_ (Over (Sp k))).hom σ), y ∈ ptsIn _ σ ((M.L.pull (eSec G)).U j) →
    Real.log (‖ev _ σ _ (M.rig.s j).val y‖ ^ 2) = Φ.φ (j PUnit.unit) (PtsOver.map (eSec G) (Over.w _) _ y)) ∧
  ∀ (j : (Theta G M.L).ι) (y : CxPts (G3 G).hom σ), y ∈ ptsIn _ σ ((Theta G M.L).U j) →
    Real.log (‖ev _ σ _ (c.t.s j).val y‖ ^ 2) =
      ∑ I : thK, (thε I : ℝ) * Φ.φ (j I) (PtsOver.map (thφ G (x3 G) I) (Over.w _) _ y)

omit [IsCommMonObj G] in

def addPt (x y : CxPts G.hom σ) : CxPts G.hom σ :=
  ⟨((Over.homMk x.1 x.2 : Over.mk (spMap σ) ⟶ G) * Over.homMk y.1 y.2).left, Over.w _⟩

omit [IsCommMonObj G] in

def IsHaar (ν : Measure (CxPts G.hom σ)) : Prop := IsProbabilityMeasure ν ∧ ∀ x, ν.map (addPt x) = ν

omit [GrpObj G] [IsCommMonObj G] in

def prodAt {L : LB G.left} (Φ : Weight G.hom σ L) (s t : L.Sec) (y : CxPts G.hom σ) : ℂ :=
  starRingEnd ℂ (ev _ σ _ (s.f (pick Φ.isLB y)) y) * ev _ σ _ (t.f (pick Φ.isLB y)) y *
    (Real.exp (-Φ.φ (pick Φ.isLB y) y) : ℝ)

end CubicalWeight

structure Model (A : Over (Sp Qb)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] [NumberField K] (e : K →+* Qb) :
    Type 1 where

  G : Over (Sp (𝓞 K))
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiStable G

  i : A.left ⟶ G.left
  fib : IsGrpPullback A G (spMap (e.comp (algebraMap (𝓞 K) K))) i

  M : RigLB G

  cub : CubicalStr G M

  Φ : ∀ σ : K →+* ℂ, Weight G.hom (σ.comp (algebraMap (𝓞 K) K)) M.L
  isCubical : ∀ σ, IsCubist cub (Φ σ)
  conj : ∀ σ, (Φ σ).IsConj (Φ ((starRingEnd ℂ).comp σ))

  w : LB.Iso (M.L.pull i) L
  gen : w.IsGen
  ker : ∃ (Z : Scheme.{0}) (ζ : Z ⟶ G.left), IsImmersion ζ ∧ IsFinite (ζ ≫ G.hom) ∧ Flat (ζ ≫ G.hom) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Qb) (x : Over.mk t ⟶ A),
      InK A (lbPow L 2) x ↔ ∃ y : Sp R ⟶ Z, y ≫ ζ = x.left ≫ i

attribute [instance] Model.grp Model.comm

namespace Model

variable {A : Over (Sp Qb)} [GrpObj A] {L : LB A.left} {K : Type} [Field K] [NumberField K] {e : K →+* Qb}

end Model

end GlobalTheory.MBLit

end
