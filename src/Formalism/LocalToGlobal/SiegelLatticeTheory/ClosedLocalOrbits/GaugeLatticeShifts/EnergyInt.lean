import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay Formalism.L2.SG.WuDecayPf
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

end Defs

def StIntOfLint : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf),
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ →
      Formalism.L2.SG.TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

end Formalism.L2.SG.RealObj.StepIntOf

namespace Formalism.L2.SG.RealObj.StepIntOf.Steps

open Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_rank_one_le {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (v : V) (w : V') :
    ‖Formalism.L2.SG.TermOp.rk1 v w‖ ≤ ‖v‖ * ‖w‖ := by
  unfold Formalism.L2.SG.TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem stIntOfLint : StIntOfLint := by
  intro D X u u' γ hfin
  unfold Formalism.L2.SG.TermOp.OOInt
  rw [integrableOn_univ]
  have hW : Continuous (X.Wu u) := (X.Wu_spec u).2.2.1
  have hW' : Continuous (X.Wu u') := (X.Wu_spec u').2.2.1
  have hW'' : Continuous fun x : X.B.I.Ginf => X.Wu u' (γ⁻¹ * x) := hW'.comp (continuous_const.mul continuous_id)
  have hc : Continuous fun x : X.B.I.Ginf => Formalism.L2.SG.TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) := by
    rw [continuous_clm_apply]
    intro ξ
    simp only [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply]
    exact (hW''.inner continuous_const).smul hW
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  simp only []
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_rank_one_le _ _)

end Formalism.L2.SG.RealObj.StepIntOf.Steps

namespace Formalism.L2.SG.RealObj.StepIntOf.Theta

open Formalism.L2.SG.RealObj.StepIntOf

section

variable {D : D7} (X : HidaSetting D)

end

end Formalism.L2.SG.RealObj.StepIntOf.Theta

namespace Formalism.L2.SG.RealObj.StepIntOf

end Formalism.L2.SG.RealObj.StepIntOf
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInt

def LocOrbG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ → ∀ v : InfinitePlace X.B.I.F,
      ∫⁻ x, ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤

def StepIntG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

theorem lint_prod {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ x, ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hm : ∀ v, Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε v) =>
      ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ) := by
    intro v
    exact ((X.Wloc_cont u v).enorm.measurable).mul
      (((X.Wloc_cont u' v).comp (continuous_const.mul continuous_id)).enorm.measurable)
  rw [← Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod (fun v => Formalism.REAL.muG (X.B.I.ε v)) _ hm]
  simp_rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu, ← Finset.prod_mul_distrib]
  rfl

theorem stepIntG_of_loc (h : LocOrbG) : StepIntG := by
  intro D hG X u u' sc hsc c hc γ hγ
  apply Formalism.L2.SG.RealObj.StepIntOf.Steps.stIntOfLint D X u u' γ
  rw [lint_prod]
  exact ENNReal.prod_lt_top fun v _ => h D hG X u u' sc hsc c hc γ hγ v

end Formalism.L2.SG.RealObj.EnergyInt
end
end
