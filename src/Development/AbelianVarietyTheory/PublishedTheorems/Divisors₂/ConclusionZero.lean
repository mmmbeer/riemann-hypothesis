import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicStd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermThetaHeckeIsotropic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsPairResThetaInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerModelCenterEquivariant

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelSchwartz.Model

open GlobalTheory.StdUnn

variable {D : D7} {n : ℕ}



theorem leftInv_term {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hχ : IsHeckeChar D χ)
    (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) : LeftInv (P D n ⊓ GF D n) fun γ => (ω γ Φ).1 0 := by
  intro γ hγ g
  obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
  obtain ⟨u, hu⟩ := LeftInvSect.det_rat hr a ha
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact absE_inclR u
  have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact hχ.2 u
  obtain ⟨m, v, b, e, hm, hv⟩ := LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (γ * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
  show (ω (γ * g) Φ).1 0 = (ω g Φ).1 0
  rw [e', hω.levi m _ hm, h1, h2, z1, hω.unip v b hv, z2]
  simp [halfTr, npow]

theorem term_one {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hχ : IsHeckeChar D χ)
    (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) :
    Eis.term (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1 (mk _ 1) = Φ.1 0 := by
  rw [Eis.term_mk (leftInv_term hχ hω Φ)]
  simp



end GlobalTheory.SiegelSchwartz.Model

end
end

section
noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.Core.Rk.SW (sch)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AnisoStdModel
open GlobalTheory.StdUnn GlobalTheory.RegSch GlobalTheory.Published

variable {D : D7} {n : ℕ}

theorem data (D : D7) (A V : HSp D) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank A.rank)) (𝓕 : Set (Mx D V.rank A.rank))
    (ω : G D A.rank →* Module.End ℂ (schwartzA θ V.rank A.rank)) (H : G D A.rank → ℝ≥0) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank A.rank),
    IsCharAF D.host.F ψ ∧ IsHeckeChar D χ ∧ ResEta D χ V.rank ∧ IsInfFam θ ∧ IsCovolOne (ratMx D V.rank A.rank) μ 𝓕 ∧
      IsWeilSch ψ χ θ V μ ω ∧ IsHeight H ∧ ν.IsHaarMeasure ∧ KFin ω Φ ∧ Φ ≠ 0 ∧
      (IsAniso V → ∀ g, Integrable (AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g)) (autMeasure V ν)) := by
  obtain ⟨ψ, χ, om, a, θ, sS, sB, m, 𝓨, ν, f, hW, ha, -, hθ, hS, hB, hK, hm, hν, hf, hf0⟩ :=
    GlobalTheory.SiegelWeilMiddle.Model.all_hypotheses_inhabited D A V
  have hfK := GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ _ V 1 χ om sS sB hW hθ hS hB _ (isCompact_Khat A a) hK f hf
  obtain ⟨μ, hskew, hconj⟩ := GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hchart⟩ := GlobalTheory.StdUnn.chart_exists D A μ hskew
  obtain ⟨p, hp⟩ := hconj A a ha κ hchart
  obtain ⟨omS, htr⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A V χ om hW m 𝓨 hm θ hθ κ
  have hP : Pass ψ θ A V χ om m 𝓨 μ κ omS := ⟨hW, hm, hθ, hskew, hchart, htr⟩
  obtain ⟨lam, hlam, hψ, -⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ hW.std θ hθ μ hskew
  obtain ⟨hχ, hr⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hW.hecT hW.resT
  have hSS := GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A V m 𝓨 hm
  have h1 : IsThetaFunO ψ (dblSp A) V (om ((p : GA D (dblSp A))⁻¹, 1) f) := hW.om_pres _ _ hf.1
  let Φ : schwartzA θ V.rank A.rank := ⟨_, hSS.1 _ h1⟩
  refine ⟨_, _, θ, m, 𝓨, omS, _, ν, Φ, hψ, hχ, hr, hθ, hm, pass_isWeilSch D ψ θ A V χ om m 𝓨 μ κ omS hP lam hlam,
    isHeight_hgtStd D A μ hskew κ hchart a p hp, hν, kfin_of_conj D ψ θ A V χ om m 𝓨 μ κ omS hP a p hp f hf.1 hfK 1 Φ rfl,
    fun h0 => hf0 ?_, fun hV g => ?_⟩
  · have hz : IsThetaFunO ψ (dblSp A) V 0 := by
      simpa using (GlobalTheory.StdUnn.sch_linear D ψ hW.std A V m 𝓨 hm f f hf.1 hf.1 0).2.1
    have hz' : sch ψ A V m 𝓨 0 = 0 := by
      simpa using (GlobalTheory.StdUnn.sch_linear D ψ hW.std A V m 𝓨 hm f f hf.1 hf.1 0).2.2.2
    have h2 : om ((p : GA D (dblSp A))⁻¹, 1) f = 0 := hSS.2.2 _ _ h1 hz ((congrArg Subtype.val h0).trans hz'.symm)
    have h3 := congrArg (om ((p : GA D (dblSp A)), 1)) h2
    rwa [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one,
      Module.End.one_apply, map_zero] at h3
  · haveI := hν
    have e : theta omS Φ g = fun h => thetaKO om (κ.symm g) h (om ((p : GA D (dblSp A))⁻¹, 1) f) := funext fun h => by
      have := FirstTermHeckeIso.theta_chart hP h1 Φ rfl (κ.symm g) 1 h
      simpa [Prod.mk_one_one] using this
    rw [e]
    exact GlobalTheory.ThetaMean.integrable_theta hW h1 (GlobalTheory.Mem.AnisoQuotient.exists_compact D V hV) _

theorem ranks (D : D7) (n m : ℕ) : ∃ A V : HSp D, A.rank = n ∧ V.rank = m ∧ IsAniso V :=
  ⟨GlobalTheory.OrthSumSp.posSp D n, GlobalTheory.OrthSumSp.posSp D m, rfl, rfl, GlobalTheory.RegSW.WeakModel.isAniso_pos D m⟩


end GlobalTheory.AnisoStdModel

end
end
