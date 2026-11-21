import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TPeriodInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite

noncomputable section

namespace GlobalTheory.NRows.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

theorem used_loc (D : D7) (i : D.nd.Loc) : D.nd.mu i = D.what₂.mu0 ∨ ∃ w, D.nd.mu i = D.what₂.muAt w :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem lamPos_of_used {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem lamLoc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  lamPos_of_used h (used_loc D i) (D.nd.j_range i).1 (D.nd.j_range i).2

theorem up_injective {D : D7} {μ} {j : ℕ} (h : LamPos D μ j) (hI : DirectSum.IsInternal (D.what₂.isot j)) :
    Function.Injective (D.what₂.thetaT μ j) := by
  have hs : Function.Surjective (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hI.submodule_iSup_eq_top, iSup_le_iff]
    intro σ f hf
    by_cases h0 : D.what₂.isot j σ = ⊥
    · rw [h0] at hf
      rw [(Submodule.mem_bot ℂ).1 hf]
      exact zero_mem _
    · have hl : ((D.what₂.lamP μ j σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h σ).2 h0).ne'
      refine ⟨((D.what₂.lamP μ j σ : ℝ) : ℂ)⁻¹ • f, ?_⟩
      rw [map_smul, LinearMap.comp_apply, (h σ).1 f hf, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hi := LinearMap.injective_iff_surjective.2 hs
  rw [LinearMap.coe_comp] at hi
  exact hi.of_comp

theorem rank_of {D : D7} (hI : SumRepresentations.adm8 D) (h : LamUsed D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := by
  intro j hj w hw
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used h (Or.inr ⟨w, e⟩) h1 h2) (hI j h1 h2)
  have b := up_injective (lamPos_of_used h (Or.inl rfl) h1 h2) (hI j h1 h2)
  unfold SizeData₂.zeroSpaceRankAtPlace SizeData₂.dZ0 Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj a, LinearMap.finrank_range_of_inj b]






theorem baseChange_preserves_unitary_of {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (h : PartsGive D) (I : Inputs hL D) (a : RowsA D) (b : RowsB D) :
    SumRepresentations.Conclusion1 D :=
  h ⟨⟨a.tie0, I.hypO, base_change_automorphic_of D I.bc I.c1, a.a2, b.a3, b.a4, a.a5⟩, a.temp⟩ a.tieLab b.rowSize a.hecke
    (lamLoc I.lam) b.thetaOne a.g4p


section Read
variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
  (X : GlobalTheory.NJoin.RealAt D cf nch tp)

end Read

def PartNe (D : D7) : Prop := 0 < D.R.m ∧ ∃ σ : D.what₂.FT, ∀ j : Fin D.R.m, ∃ f ∈ D.what₂.isot (j.1 + 1) σ, f ≠ 0












theorem unitaryRealisationReading_of_idempotent_acts_via_levelGroup {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (h : ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1))
      (l : (X.R.cV j).W →ₗ[ℂ] ℂ),
      Formalism.IndefR.Links.gaL (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) X.R.eG
        (Formalism.IndefR.Links.RealDat.eC (A := X.A) (Formalism.IndefR.Links.sg0 D X.A)) (fun g => l (X.fn hμ j f g)) =
        fun g => l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g)) : GoodIdempotentReadsAsGoodTypeProjector X := by
  intro μ hμ j f y hy
  unfold GlobalTheory.DownLift.GoodVt
  rw [hy]
  constructor
  · intro hf l
    rw [h μ hμ j f l, hf]
  · intro hg
    apply (X.IL.jMt μ hμ j).injective
    apply Subtype.ext
    funext g
    have key : ∀ l : (X.R.cV j).W →ₗ[ℂ] ℂ,
        l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g - X.fn hμ j f g) = 0 := fun l => by
      rw [map_sub, sub_eq_zero]
      exact congrFun ((h μ hμ j f l).symm.trans (hg l)) g
    exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (V := (X.R.cV j).W) _).1 key)



end GlobalTheory.NRows.Model

end
