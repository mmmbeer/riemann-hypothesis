import Formalism.SharpRestriction.LevelLetterCocycles.ExistsGoodPlacesEveryConjugate
import Formalism.SharpRestriction.SmoothDesignExistence.EvSplit
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.MainNotions

end Formalism.MainNotions
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAtAll (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (C.twI w) ∧ TwGoodAll D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

end Formalism.MainNotions
end
end
