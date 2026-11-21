import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLw
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IntegrableOfIsAniso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero

noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelFormula.Model

variable {D : D7}

theorem two_mul_finrank_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) (W : Submodule E B.V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) : 2 * Module.finrank E W ≤ B.rank := by
  let b := Module.finBasis E W
  have hl : LinearIndependent E fun i => B.hT (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0 := by
      rw [← hc]; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
    have h2 : (∑ i, star (c i) • b i : W) = 0 := Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)
    simpa using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))
  rw [finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq] at h3
  have h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator := fun y hy => by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact hW _ (b i).2 _ hy
    | zero => rfl
    | add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
    | smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]
  have := Submodule.finrank_mono h4
  omega

theorem bddAbove_witt {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    BddAbove {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0} :=
  ⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_le B W hW; omega⟩

theorem two_mul_wittIdx_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    2 * Formalism.MainNotions.SchurIrreducible.wittIdx B ≤ B.rank := by
  obtain ⟨W, h, hW⟩ := Nat.sSup_mem (s := {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧
    ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}) ⟨_, ⊥, rfl, by simp⟩ (bddAbove_witt B)
  rw [Formalism.MainNotions.SchurIrreducible.wittIdx, ← h]
  exact two_mul_finrank_le B W hW

theorem range_of_two_mul_lt {A B : HSp D} (h : 2 * A.rank < B.rank) : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
  have := two_mul_wittIdx_le B
  omega

abbrev pos (D : D7) (n : ℕ) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n

theorem wittIdx_pos (n : ℕ) : Formalism.MainNotions.SchurIrreducible.wittIdx (pos D n) = 0 :=
  Formalism.MainNotions.J.wittIdx_zero _ (Formalism.MainNotions.J.aniso_of_definite _ D.host.φ₀ (D.sp.cm.cmUnram.2.1 D.host.φ₀)
    (Examples₂.posSpace_sigOK _ _) fun _ => .inl rfl)

theorem wittIdx_dblSp (V : HSp D) : Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) = V.rank := by
  have h1 : 2 * Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) ≤ V.rank + V.rank := two_mul_wittIdx_le (dblSp V)
  let f : V.V →ₗ[D.host.E] (dblSp V).V := LinearMap.prod LinearMap.id LinearMap.id
  have hf : Function.Injective f := fun x y h => congrArg Prod.fst h
  have h2 : V.rank ≤ Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) := le_csSup (bddAbove_witt _)
    ⟨LinearMap.range f, (LinearMap.finrank_range_of_inj hf).trans V.rank_eq, by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      change V.hT x y + -V.hT x y = 0
      exact add_neg_cancel _⟩
  omega

theorem data_exist (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (A B : HSp D) :
    ∃ (m : Measure (GA D B)) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (f : WO (dblSp A) B → ℂ)
      (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)),
      m.IsHaarMeasure ∧ IsWeilDatumO ψ (dblSp A) B 1 χ ω ∧ IsThetaFunO ψ (dblSp A) B f ∧ f ≠ 0 ∧
        IsCovolOne (ratL B A) ν 𝓖 := by
  obtain ⟨ψ, A', B', χ, ω', -, -, -, -, hA, hB, -, h', -⟩ := GlobalTheory.ThetaMean.Model.hypotheses_inhabited H D A.rank B.rank
  obtain ⟨ω, hω⟩ := H D ψ (dblSp A) B 1 χ h'.std h'.hecS h'.hecT
    (by have := h'.resS; change ResEta D 1 (A'.rank + A'.rank) at this; rwa [hA] at this) (hB ▸ h'.resT)
  obtain ⟨f, hf, h0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hω.std (dblSp A) B
  obtain ⟨ν, 𝓖, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank A.rank
  exact ⟨Measure.haar, ψ, χ, ω, f, ν, 𝓖, inferInstance, hω, hf, h0, hν⟩








end GlobalTheory.SiegelFormula.Model

end
