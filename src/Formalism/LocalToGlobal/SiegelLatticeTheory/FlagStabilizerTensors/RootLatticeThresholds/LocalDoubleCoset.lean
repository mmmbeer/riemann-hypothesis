import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinJF

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocalDoubleCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Move {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (γ γ' : Formalism.MainNotions.S.MatKR k r) : Prop :=
  ∃ n ∈ Formalism.QuantumDeterminants.Nset k r, ∃ s ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ s' ∈ Formalism.QuantumDeterminants.UWset k r z', ∃ n' ∈ Formalism.QuantumDeterminants.Nset k r,
    γ' = (s * n) * γ * (n' * s')

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

end Formalism.L2.SG.Pf.LocalDoubleCoset
