import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.SiegelWeilFiniteVolumeCase
import Formalism.SharpRestriction.CuspSpanNormBounds.MassRatioBoundPower
import Mathlib
import Formalism.PeriodIntegrals.GaugeGap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameIso.MulFirstColumnOfUnitColumn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.VolumeCarry

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sig_apply (D : D7) (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hE_repr (D : D7) (W : HSpace D.host.E) (x y : W.V) :
    hE D.sp.cm.sig W.gram (W.frame.repr x) (W.frame.repr y) = W.hT x y := by
  conv_rhs => rw [← W.frame.sum_repr x, ← W.frame.sum_repr y]
  simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply,
    map_smul, smul_eq_mul, sig_apply, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

end Gen

end Formalism.L2.GlobalTheoryTheory.VolumeCarry

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.VolumeCarry

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def frameMat (D : D7) (W W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V) :
    Matrix (Fin W.rank) (Fin W'.rank) D.host.E :=
  fun i j => W.frame.repr (ι (W'.frame j)) i

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

end Gen

theorem gram_frameMat (D : D7) (W W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V)
    (h1 : HSpace.IsIsomEmb W' W ι) :
    W'.gram = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat D W W' ι) * W.gram * frameMat D W W' ι := by
  ext i j
  have e1 : W'.gram i j = W.hT (ι (W'.frame i)) (ι (W'.frame j)) := (h1 _ _).symm
  rw [e1, ← hE_repr D W]
  simp only [hE, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, frameMat,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end Formalism.L2.GlobalTheoryTheory.VolumeCarry

end
end
