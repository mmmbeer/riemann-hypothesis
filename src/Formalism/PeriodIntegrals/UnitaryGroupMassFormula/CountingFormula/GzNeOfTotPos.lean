import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalModelsSplitCofinite

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaIntCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιE x ∈ (D.s.atP p).O

def DetGaNe : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D), GZ T T' Z ≠ 0 → (Ga T T' Z).det ≠ 0

end PI.UnitaryGroupMassFormula.CntFormula
