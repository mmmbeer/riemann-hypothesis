import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.DiscreteSeriesSU.GapInv
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

namespace CompanionTheory.RgDs

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

theorem kTypesAbove_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) : GlobalTheory.Dec.KTypesAbove := by
  intro n ε lam H _ _ σ hl hσ μ S hS
  obtain ⟨G, _, _, π, hπ, hc⟩ := model_of hL hK hH ε lam hl
  obtain ⟨S', hS'⟩ := GlobalTheory.LowestKTypeDetermines.exists_ktype_of_uEquiv
    (CompanionTheory.DiscreteSeriesGap.GapInv.dsUnique_dec n ε lam H σ G π hl hσ hπ) ⟨S, hS⟩
  exact hc μ S' hS'

end CompanionTheory.RgDs
end
end

section
noncomputable section

namespace CompanionTheory.RgDs

open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.CoverDS GlobalTheory.Dec

theorem upqExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesUpqExists :=
  GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE

theorem exists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesExists :=
  GlobalTheory.Published.discreteSeriesExists_iff_upq.2 (upqExists_of hE)

theorem coverExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesCoverExists :=
  GlobalTheory.Published.CoverSeries.of_upq (upqExists_of hE) (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)

def ClassUsed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (π : Matrix (Fin n) (Fin n) ℂ → (G →L[ℂ] G)), GlobalTheory.DSId.IsHCDS ε lam π ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
        Formalism.MainNotions.S.IsDS ε lam σ → UEquiv ε σ π

theorem classUsed_of (hE : DSExists) (hK : KTypesAbove) (hI : DSInfChar) : ClassUsed := by
  intro n ε lam hl
  obtain ⟨G, _, _, π, hπ⟩ := hE n ε lam hl
  refine ⟨G, _, _, π, ⟨⟨hπ.1, hπ.2.1, hπ.2.2.1, hπ.2.2.2.1, hπ.2.2.2.2.1⟩, hI n ε lam G π hl hπ, ?_,
    hK n ε lam G π hl hπ⟩, fun H _ _ σ hσ => CompanionTheory.DiscreteSeriesGap.GapInv.dsUnique_dec n ε lam H σ G π hl hσ hπ⟩
  obtain ⟨S, hS⟩ := hπ.2.2.2.2.2.1
  exact ⟨S, hS, fun S' hS' => CompanionTheory.DiscreteSeriesGap.GapInv.lowKMultOne_dec n ε lam G π hl hπ S' S hS' hS⟩

end CompanionTheory.RgDs
end
end
