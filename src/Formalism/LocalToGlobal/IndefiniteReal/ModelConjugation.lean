import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DiscreteSeriesHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

namespace Formalism.IndefR.LowestKTypeSmoothness

attribute [local instance] Formalism.BasicNotions.Host.cmStar


variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

end Formalism.IndefR.LowestKTypeSmoothness

end
end

section
noncomputable section

open Matrix
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.IndefR.ModelConjugation

open PI.ZuckTensorWork

variable {n : ℕ}

def toCj (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H ≃ₗᵢ⋆[ℂ] Cj H where
  toFun := Cj.mk
  invFun := Cj.un
  map_add' _ _ := rfl
  map_smul' c x := Cj.mk_smul c x
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl


def Rm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if j = Fin.rev i then 1 else 0






section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ModelConjAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : Formalism.IndefR.Mult.DSModel V S) (v : NumberField.InfinitePlace X.B.I.F)
    (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin X.B.I.n) ℂ) (A' : Matrix (Fin X.B.I.n) (Fin V.rank) ℂ) : Prop :=
  ∃ U : X.B.H v ≃ₗᵢ⋆[ℂ] M.H τ,
    (∀ m ∈ Formalism.MainNotions.S.UJset (X.B.I.ε v), ∀ x, U (X.B.σ v m x) = M.σ τ (A * m * A') (U x)) ∧
    U (X.B.w v) ∈ M.sm τ ∧ ‖U (X.B.w v)‖ = 1


end Rec

end Formalism.IndefR.ModelConjugation
end
end
