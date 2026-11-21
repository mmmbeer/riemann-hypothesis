import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteExtensionTopology.Imports

noncomputable section

namespace PI.UnitaryGroupMassFormula.FinExtTop

open PI.FinExtTop

theorem torsionFree_pi_matrix (O' : Type) [CommRing O'] [IsDomain O'] (X' d : Type) [Fintype d]
    [DecidableEq d] : Module.IsTorsionFree O' (X' → Matrix d d (FractionRing O')) where
  isSMulRegular r hr f g h := by
    have hr0 : algebraMap O' (FractionRing O') r ≠ 0 := by
      intro h0
      exact hr.ne_zero ((IsFractionRing.injective O' (FractionRing O')).eq_iff.1
        (h0.trans (map_zero _).symm))
    have h' : algebraMap O' (FractionRing O') r • f = algebraMap O' (FractionRing O') r • g := by
      simpa only [algebraMap_smul] using h
    exact ((IsUnit.mk0 _ hr0).smul_left_cancel).1 h'

end PI.UnitaryGroupMassFormula.FinExtTop
