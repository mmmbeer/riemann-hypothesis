import Mathlib

namespace Formalism.SL.MV

open Finset

noncomputable def kern {ι Mv : Type} [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (i j : ι) : ℝ :=
  ∑ m ∈ univ.filter (fun m => src m = i ∧ tgt m = j), μ m

end Formalism.SL.MV
