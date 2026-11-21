import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAdicColimitOfIsFiniteNoetherian

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv.Transport

abbrev Frame {X Y : Scheme.{0}} (L : LB X) (ψ : Y ⟶ X) : Type :=
  LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1)

abbrev cocφ {X : Scheme.{0}} {G : Over X} [GrpObj G] {O : Type} [CommRing O] (a : OAct O G) (bar : O → O) (c : O) :
    Fin 4 → (G.left ⟶ G.left) :=
  ![(a.act (1 + c * bar c)).left, (a.act c).left, 𝟙 _, (a.act (c * bar c)).left]

abbrev cocε : Fin 4 → ℤ := ![1, -2, -1, -1]

section Defs

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def Lies {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left),
    y ≫ fGl I G e = r ≫ x' → y ≫ pGl U e = r ≫ b

def FrRel {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) (g' : Frame U.LG.L x')
    (g : Frame D.toPre.P.L b) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left), y ≫ fGl I G e = r ≫ x' →
    ∀ (z : Z) (JM) (JL), Good D.toPre.P.L z JM → Good U.LG.L z JL →
      val g r z JM = wVal U e z JM JL y * val g' r z JL

def RosLevel (f g : G ⟶ G) (a b : D.toPre.P.A ⟶ D.toPre.P.A)
    (uG : LB.Gen (LB.LinComb U.LG.L (rosatiφ G f g) rosatiε))
    (uB : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a b) rosatiε)) : Prop :=
  ∀ (e : ℕ) (T : Over (Sp (R ⧸ I ^ (e + 1)))) (x y : T ⟶ thickObj R I e G) (z : T.left) (JM) (JL),
    Good D.toPre.P.L z JM → Good U.LG.L z JL →
      val uB (Z := T.left) (lift (push (U.gt e).pG x) (push (U.gt e).pG y)).left z JM =
        wVal U e z JM JL ((x ≫ (Over.pullback (thick R I e)).map f) * y).left *
          (wVal U e z JM JL (x ≫ (Over.pullback (thick R I e)).map f).left)⁻¹ * (wVal U e z JM JL y.left)⁻¹ *
          (wVal U e z JM JL (x * (y ≫ (Over.pullback (thick R I e)).map g)).left)⁻¹ * wVal U e z JM JL x.left *
          wVal U e z JM JL (y ≫ (Over.pullback (thick R I e)).map g).left *
          val uG (Z := T.left) (lift (push (fstG I e G) x) (push (fstG I e G) y)).left z JL

end Defs

end GlobalTheory.RayEv.Transport
