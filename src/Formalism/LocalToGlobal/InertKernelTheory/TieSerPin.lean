import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

def srOf {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    MvPowerSeries (X.ZA j) Y.Kc :=
  ((Y.eS j La * (Y.eT j La')⁻¹ : X.G.Kf)) • Y.ThF j La La'

def TieSerOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ), TieSerAt (Y := Y) (srOf Y) j

def TieSerPin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ),
    TieSerAt (Y := Y) Sr j → ∀ La ∈ Y.Rep j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      Sr j La (c', L') = srOf Y j La (c', L')

end Formalism.L2.KerInert.SecondKernelSeries
