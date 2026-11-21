import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

def cechComplex (P : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) {U V : Scheme.{0}} (π : V ⟶ U) :
    CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj ((Arrow.mk π).cechNerve.rightOp ⋙ P)

def CechAcyclic (P : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) {U V : Scheme.{0}} (π : V ⟶ U) : Prop :=
  ∀ n : ℕ, (cechComplex P π).ExactAt (n + 1)

end GlobalTheory.Et

end
