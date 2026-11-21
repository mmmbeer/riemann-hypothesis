import Mathlib
import Development.AutomorphicSpectrum.ParallelStatements.FiniteSums.BesselPeriodFreeData
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicFormsHyp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv Formalism.IndefR.Mi
  Formalism.IndefR.Mult MeasureTheory Matrix GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.BesselPeriodFreeData
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SepInhab

end GlobalTheory.CompanionTheory.SepInhab

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv Formalism.IndefR.Mi Formalism.IndefR.Mult MeasureTheory Matrix GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.BesselPeriodFreeData GlobalTheory.CompanionTheory.SepInhab
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatMxCovol

theorem exists_isCovolOne_ratMx : ∀ (D : D7) (m n : ℕ), ∃ (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)),
    IsCovolOne (ratMx D m n) μ 𝓕 := by
  intro D m n
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  exact GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (Mx D m n) (ratMx D m n) ⟨i5, K, hK, hc⟩

end GlobalTheory.CompanionTheory.RatMxCovol
end
