import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.IsTorus

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels

def IsExtensionByTorus {k : Type} [Field k] {T G B : Over (Spec (CommRingCat.of k))}
    [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsTorus T ∧ IsAbelianScheme B ∧ IsMonHom i ∧ IsMonHom q ∧
    Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
    IsPullback i (toUnit T) q (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B)

end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels
