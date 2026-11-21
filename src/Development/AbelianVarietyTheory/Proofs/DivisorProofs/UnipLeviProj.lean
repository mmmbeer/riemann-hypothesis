import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.WhitHered

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def unipLevi {c : ℕ} (m : Fin c → ℕ) : Subgroup (Levi k fun a => Fin (m a)) :=
  Subgroup.pi Set.univ fun a => unipB k (Fin (m a))

variable {k}

variable {N c : ℕ} {m : Fin c → ℕ}

end GlobalTheory.WhitHered

end
