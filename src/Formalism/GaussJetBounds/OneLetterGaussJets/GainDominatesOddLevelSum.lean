import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CapLeOddShiftBound
import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbitsLogLoss
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.TheoremAMonomialOfLemmas
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.ThmAGen7Of
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.ThmAGeneric7Of
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.TwoFormsOfTheoremA
import Formalism.GaussJetBounds.OneLetterGaussJets.MinWeightSumAddCostAbsBound
import Formalism.GaussJetBounds.GaussJetProofs.IntegralOperatorsOnJets
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CompanionTheory
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.OneLetterUnramifiedBound

section
universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

theorem thmAAssembly7 : ThmAAssembly7 := gauss_jet_bound_of_parts
theorem thmAJet7 : ThmAJet7.{u} := thmAJet7_of thmAAssembly7
theorem thmAOp7 : ThmAOp7.{u} := thmAOp7_of thmAJet7
theorem thmAGen7 : ThmAGen7.{u} := thmAGen7_of thmAOp7
theorem thmAFrame7 : ThmAFrame7.{u} := thmAFrame7_of thmAGen7
theorem thmAGeneric7 : ThmAGeneric7.{u} := thmAGeneric7_of thmAFrame7
theorem thmAGauss7 : ThmAGauss7 := thmAGauss7_of thmAGeneric7
theorem thmAWeyl7 : ThmAWeyl7 := thmAWeyl7_of thmAGauss7
theorem thmAEntry7 : ThmAEntry7 := thmAEntry7_of thmAWeyl7

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
end

section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
end
end

section
universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

theorem propSix7 : PropSix7 := proposition_six
theorem gain_dominates_oddLevel_sum : GainDominatesInnerSum := gain_ge_inner_sum
theorem normCor7 : NormCor7 := by
  intro l d _ hl hd he TT nu1 nu2 size k L w E pi y hpi0 hpi1 hk hw hE hD1 hD2 hy
  refine hy.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le ?_)
  have h6 := propSix7 l d hl hd he TT k (fun s => (Dl d TT nu1 size s : ℝ)) w E hk hw hE hD1 hD2
  have hsum : ∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s ≤ ∑ s ∈ TT, topTerm l d TT nu1 nu2 s :=
    Finset.sum_le_sum fun s _ => gain_dominates_oddLevel_sum l d (by omega) TT nu1 nu2 s
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [h6.1, h6.2]
theorem oneLetterGauss7 : OneLetterGauss7 := one_letter_gauss_bound

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
end
