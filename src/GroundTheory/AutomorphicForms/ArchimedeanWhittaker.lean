import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Uniqueness

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix
open scoped Matrix.Norms.L2Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def toTopRep (σ : UnitaryRep (GL (Fin 2) ℝ) H) : UnitaryRep FiltrationCocycleLiftCriterion H where
  toHom := σ.toHom.comp FiltrationCocycleLiftCriterion.subtype
  continuous_orbit' v := (σ.continuous_orbit v).comp continuous_subtype_val

@[simp] theorem toTopRep_apply (σ : UnitaryRep (GL (Fin 2) ℝ) H) (g : FiltrationCocycleLiftCriterion) :
    toTopRep σ g = σ (g : GL (Fin 2) ℝ) := rfl

end GroundTheory.Automorphic.ArchWhittaker
