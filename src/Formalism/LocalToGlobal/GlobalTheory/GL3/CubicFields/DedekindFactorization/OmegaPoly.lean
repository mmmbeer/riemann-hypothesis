import Mathlib

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open Polynomial

def chiD (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
