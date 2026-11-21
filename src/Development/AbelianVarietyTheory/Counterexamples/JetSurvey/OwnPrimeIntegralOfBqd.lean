import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlace

noncomputable section

namespace GlobalTheory.OwnPrimeRam

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections

example : Nat.Prime 211 ∧ 211 % 8 = 3 ∧ 211 % 15 = 1 := by norm_num

end GlobalTheory.OwnPrimeRam
