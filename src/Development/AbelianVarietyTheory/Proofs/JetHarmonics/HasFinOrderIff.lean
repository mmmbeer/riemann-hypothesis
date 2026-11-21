import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.RigidNormaliserGenerators
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DiagonalActionLiftPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GeneratorsCompare

open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]

def PtSame (b : TF (R := R) F ⟶ G) (x : TFK (R := R) F ⟶ A.A) : Prop :=
  b.left = (x ≫ U.gen.inv).left ≫ pullback.fst G.hom (jK R)

variable (k : ℕ) (W : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))))

end GlobalTheory.GeneratorsCompare
