import Formalism.LocalToGlobal.IndefiniteReal.DatumFock

noncomputable section

open Matrix

namespace Formalism.IndefR.FockModel₂

abbrev KVar (p q n : ℕ) : Type := (Fin p ⊕ Fin q) × Fin n

variable {p q n : ℕ}

def IsUpperUni {k : ℕ} (u : Matrix (Fin k) (Fin k) ℂ) : Prop := ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1)

def IsLowerUni {k : ℕ} (u : Matrix (Fin k) (Fin k) ℂ) : Prop := IsUpperUni uᵀ

section Fock

open Formalism.BasicNotions Formalism.IndefR.Datum

variable {D : Formalism.BasicNotions.D7} {m n : ℕ}

end Fock

end Formalism.IndefR.FockModel₂

end
