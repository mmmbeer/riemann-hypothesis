import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Struct

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

variable {Sh : Shape}

abbrev Pos (Sh : Shape) : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v)

def ETI.s1 (t : ETI Sh) : Fin (Sh.n' t.1) := FormalGroupSystem.posSub t.2.1 (2 * t.2.2.1)

def ETI.s2 (t : ETI Sh) : Fin (Sh.n' t.1) := FormalGroupSystem.posSub (posAdd t.2.1 1) (2 * t.2.2.2.1)

def ETI.j (t : ETI Sh) : ℕ := 2 * t.2.2.1 + 1

def ETI.j' (t : ETI Sh) : ℕ := 2 * t.2.2.2.1

def ETI.ty (t : ETI Sh) : ℕ := t.2.2.2.2.val

def ETI.IsB (t : ETI Sh) : Prop := t.ty = 1 ∧ t.2.2.2.1 = 0

instance (t : ETI Sh) : Decidable t.IsB := inferInstanceAs (Decidable (_ ∧ _))

end PI.UnitaryGroupMassFormula.PadicGainBound
