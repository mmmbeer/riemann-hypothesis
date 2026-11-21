import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation

section
noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.PuBndC

def rr (h : M22) : ℝ := ‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2

def dd (h : M22) : ℝ := ‖(Matrix.of h).det‖

def yy (h : M22) : ℝ := dd h ^ 2 / rr h ^ 2

def Fh (σ : ℝ) (h : M22) : ℝ :=
  rr h ^ (σ - 2) * dd h ^ (-2 * σ) * (1 + |Real.log (yy h)|) / ((1 + yy h) ^ 2 * (1 + ‖h‖) ^ 6)

end GlobalTheory.CompanionTheory.PuBndC
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.PuBndC

end GlobalTheory.CompanionTheory.PuBndC
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.PuBndC

namespace GlobalTheory.CompanionTheory.PuBndC.RowSwap

def rowSwap (h : M22) : M22 := fun i => h (Equiv.swap 0 1 i)

@[simp] theorem rowSwap_zero (h : M22) : rowSwap h 0 = h 1 := by simp [rowSwap]

@[simp] theorem rowSwap_one (h : M22) : rowSwap h 1 = h 0 := by simp [rowSwap]

theorem rowSwap_rowSwap (h : M22) : rowSwap (rowSwap h) = h := by
  funext i
  simp [rowSwap]

theorem measurePreserving_rowSwap : MeasurePreserving rowSwap (volume : Measure M22) volume := by
  have hm := volume_measurePreserving_piCongrLeft (fun _ : Fin 2 => Fin 2 → ℂ) (Equiv.swap (0 : Fin 2) 1)
  have e : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Fin 2 → ℂ) (Equiv.swap (0 : Fin 2) 1)) : M22 → M22) = rowSwap := by
    funext h i
    simp only [MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk, Equiv.piCongrLeft_apply, rowSwap, Equiv.symm_swap]
    exact eq_rec_constant _ _
  rw [← e]
  exact hm

def rowSwapEquiv : M22 ≃ᵐ M22 where
  toFun := rowSwap
  invFun := rowSwap
  left_inv := rowSwap_rowSwap
  right_inv := rowSwap_rowSwap
  measurable_toFun := measurePreserving_rowSwap.measurable
  measurable_invFun := measurePreserving_rowSwap.measurable







end GlobalTheory.CompanionTheory.PuBndC.RowSwap
end
end
