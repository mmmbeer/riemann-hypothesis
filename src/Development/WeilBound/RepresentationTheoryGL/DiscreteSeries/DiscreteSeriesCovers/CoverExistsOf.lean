import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.InConeRefl
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DiscreteSeriesSU.GapInv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCover
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroupStatement

section
noncomputable section

namespace PositivityTheory.RgDs

open ReciprocityTheory.ChartRestriction.DS

theorem model_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ ∧
        ∀ (η : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ η S → InCone (lowK ε lam) η := by
  obtain ⟨T⟩ := HW.kType_exists ε lam hl
  obtain ⟨μ, hμ⟩ := S7.exists_mu hl
  have hP : IsPsiFor ε lam T (S7.PsiM T μ) :=
    ⟨fun k₁ k₂ g hg => S7.psiM_equiv T μ k₁ k₂ hg, S7.psiM_one T μ, S7.psiM_smooth T μ hμ,
      fun g hg => S7.psiM_casimir T μ hμ hg, hL n ε lam T μ hl hμ⟩
  exact ⟨_, inferInstance, inferInstance, _, hH n ε lam T _ hl hP (hK n ε lam T μ hl hμ hP)⟩

theorem dsExists_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) : GlobalTheory.Dec.DSExists := by
  intro n ε lam hl
  obtain ⟨H, _, _, σ, h, -⟩ := model_of hL hK hH ε lam hl
  exact ⟨H, _, _, σ, h⟩

end PositivityTheory.RgDs
end
end

section
noncomputable section

namespace PositivityTheory.RgDs

open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.CoverDS GlobalTheory.Dec

theorem upqExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesUpqExists :=
  GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE

theorem exists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesExists :=
  GlobalTheory.Published.discreteSeriesExists_iff_upq.2 (upqExists_of hE)

theorem coverExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesCoverExists :=
  GlobalTheory.Published.CoverSeries.of_upq (upqExists_of hE) (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)

end PositivityTheory.RgDs
end
end
