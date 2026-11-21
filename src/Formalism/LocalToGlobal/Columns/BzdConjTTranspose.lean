import Mathlib
import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end SlopeTestRemainingChoices

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

instance bzd_finite : Module.Finite K (StdV K lam) := Module.Finite.of_basis (bVV K (oneW lam))

end Std


end Formalism.L2.Col
