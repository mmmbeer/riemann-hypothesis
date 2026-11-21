import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1



omit [IsUltrametricDist K] in
private theorem Rl.neg {x y : K} (h : Rl x y) : Rl (-x) (-y) := by
  refine ⟨by simpa using h.1, ?_⟩
  rw [show -x - -y = -(x - y) by ring, norm_neg]
  exact h.2





end Rel

end UpperTheory.V.Sd
