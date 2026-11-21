import Formalism.WindowSums.AnnihilatorPolynomials.LeOfPowMemIdealOfDistinctTerms
import Formalism.WindowSums.AnnihilatorPolynomials.FirstCoefficientBoundHolds
import Formalism.WindowSums.AnnihilatorPolynomials.EvalOneSmulDecomposition
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
import Formalism.WindowSums.AnnihilatorPolynomials.ValProd
import Formalism.WindowSums.AnnihilatorPolynomials.WindowSum
import Formalism.WindowSums.AnnihilatorPolynomials.Lagrange
import Formalism.WachModuleLifts.StatementW

section
noncomputable section

namespace Formalism.WindowSums

open Formalism.CL.W

def PM {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A] {B : Base p A} {η : ℕ}
    {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (M : ℕ) : Set D :=
  {x | ∃ n ∈ W.N, x = B.π₀ ^ M • n}

end Formalism.WindowSums
end
end

section
namespace Formalism.WindowSums

theorem arc_ZpowVal : ZpowVal := valuation_zpow_sub_one
theorem arc_ValProd : ValProd := valProd_of valuation_zpow_sub_one
theorem arc_KillerVal : KillerVal := killerVal_of valuation_zpow_sub_one
theorem arc_KillerKills : KillerKills := annihilatorPoly_kills
theorem arc_WindowSum : WindowSum := sum_padicValInt_le
theorem arc_Lagrange : Lagrange := lagrange_annihilation

end Formalism.WindowSums
end
