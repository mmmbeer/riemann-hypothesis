import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IntegrableOfIsAniso
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstantOneNotCuspidalOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRecordOfLocStage

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil GlobalTheory.Cusp.Model GlobalTheory.CuspDecay.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspSpectrum.Model

theorem exists_measure (D : D7) (V : HSp D) :
    ∃ μ : Measure (GA D V), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  ⟨Measure.haar, inferInstance, AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ inferInstance⟩

theorem exists_ne_zero : ∃ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (_ : μ.IsHaarMeasure)
    (_ : μ.IsMulRightInvariant), V.rank = 1 ∧ ∃ f ∈ CcGA V, RcuspOp V μ f ≠ 0 := by
  obtain ⟨D⟩ := Mem.nonempty_record_of_locStage
  obtain ⟨μ, _, _⟩ := exists_measure D (line D)
  obtain ⟨v, hv, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (L2cusp_ne_bot μ (wittIndex_line D))
  obtain ⟨f, hf, h⟩ := exists_RcuspOp_ne_zero (v := ⟨v, hv⟩) fun e => h0 (congrArg Subtype.val e)
  exact ⟨D, line D, μ, ‹_›, ‹_›, rfl, f, hf, fun e => h (by rw [e]; rfl)⟩

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]



end GlobalTheory.CuspSpectrum.Model

end
end

section
noncomputable section

open scoped ComplexConjugate NNReal ENNReal
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp GlobalTheory.MixModel
open GlobalTheory.Mem.Th (InfF CptF)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause DoublingIso)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RallisIP.Model

variable {D : D7} {A B : HSp D}

theorem exists_splitting (D : D7) (k : ℕ) : ∃ χ, IsHeckeChar D χ ∧ ResEta D χ k := by
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hr := hη.2.2.1
  exact ⟨η ^ k, ⟨by
    have : ((η ^ k : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ k := by funext x; simp
    rw [this]; exact hη.1.1.pow k, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩,
    hr.1, fun e he a => by rw [MonoidHom.pow_apply, hr.2 e he a, pow_one]⟩

theorem hypotheses_inhabited (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) (hD : DoublingIso D) (n k : ℕ) :
    ∃ (A B : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χA χB : (AE D)ˣ →* Circle)
      (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
      (ωd : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (θ : InfF D) (C : CptF A) (m : Measure (GA D A)) (_ : m.IsHaarMeasure)
      (_ : m.IsMulRightInvariant) (mH : Measure (GA D B)) (U : Submodule ℂ (DividedPowerChartLift A m)),
      A.rank = n ∧ B.rank = k ∧ Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∧ IsWeilDatumO ψ A B χA χB ω ∧
        IsWeilDatumO ψ (dblSp A) B 1 χB ωd ∧ ThetaClause ψ A B χB ω ωd ∧ IsMaj A a ∧ IsCovolOne (ratL B A) ν 𝓕 ∧
        IsInfFam θ ∧ A.SigOK ∧ IsCartanFrame A C ∧ mH.IsHaarMeasure ∧ IsIrredSubrep (RG A m) U ∧ U ≤ L2cusp A m ∧
        LowerLiftsZero m ψ B χA χB (AutMult.formsIn A m (A0 θ A C) U) ∧
        (fun _ => (1 : ℂ)) ∈ AutMult.formsIn A m (A0 θ A C) U := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  let A : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  let B : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral k
  have hA : IsAniso A := GlobalTheory.ThetaMean.Model.isAniso_posSpace n
  have hB : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 :=
    (wittIdx_eq_wittIndex B).trans (wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.ThetaMean.Model.isAniso_posSpace k))
  have hs : A.SigOK := Examples₂.posSpace_sigOK _ _
  obtain ⟨χA, h1, h2⟩ := exists_splitting D A.rank
  obtain ⟨χB, h3, h4⟩ := exists_splitting D B.rank
  obtain ⟨ω, hω⟩ := H D ψ A B χA χB hψ h1 h3 h2 h4
  obtain ⟨ωd, hωd, hc, -⟩ := hD ψ A B χA χB ω hω
  obtain ⟨a, ha⟩ := exists_isMaj A
  obtain ⟨ν, 𝓕, hν⟩ := exists_isCovolOne D B.rank A.rank
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨C, hC⟩ := exists_isCartanFrame A hs
  haveI hr := AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A Measure.haar inferInstance
  have hcc : (fun _ => (1 : ℂ)) ∈ cuspCont A := ⟨continuous_const, fun _ _ _ => rfl, fun r C hC => absurd hC (hA r C)⟩
  refine ⟨A, B, ψ, χA, χB, ω, ωd, a, ν, 𝓕, θ, C, Measure.haar, inferInstance, hr, Measure.haar, _, rfl, rfl, hB, hω, hωd,
    hc, ha, hν, hθ, hs, hC, inferInstance, isIrredSubrep_const, ?_, lowerLiftsZero_of_wittIdx_eq_zero hB _ _ _ _ _, ?_, _,
    Submodule.mem_span_singleton_self _, MemL2Quotient.lift_toL2_ae_eq _⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (toL2_mem_cuspidal _ hcc)
  · exact ⟨⟨isAutFunSm_const θ A 1, .of_invariant fun _ _ _ => rfl⟩, hcc⟩

theorem vol_pos (mH : Measure (GA D B)) [mH.IsHaarMeasure] : 0 < (autMeasure B mH).real Set.univ :=
  ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 (NeZero.ne _)) (measure_ne_top _ _)

theorem petersson_smul_measure (μ : Measure (GA D A)) (c : ℝ≥0) (φ φ' : GA D A → ℂ) :
    petersson A (c • μ) φ φ' = c * petersson A μ φ φ' := by
  have e : AutomorphicL2Unitary.quotMeasure (GQ A) (c • μ) = c • AutomorphicL2Unitary.quotMeasure (GQ A) μ := quotMeasure_smul (c : ℝ≥0∞)
  rw [petersson, pet, e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rfl

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)}





end GlobalTheory.RallisIP.Model

end
end
