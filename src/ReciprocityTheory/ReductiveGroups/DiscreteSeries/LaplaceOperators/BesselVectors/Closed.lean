import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.FamilyGapImplicationHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.SIntShiftEqSmul
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroCayley
import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ParitySignEqGapSign
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Imports
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NVHTop

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopClm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem opNorm_le_one_of_isometry (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) : ‖A‖ ≤ 1 := A.opNorm_le_bound zero_le_one fun v => by rw [hA, one_mul]

theorem integral_ne_zero_of_apply (s : α → ℂ) (A : α → V →L[ℂ] V) (hA : AEStronglyMeasurable A μ)
    (hu : ∀ᵐ p ∂μ, ∀ v, ‖A p v‖ = ‖v‖) (ξ : V) (h : ∫ p, s p • A p ξ ∂μ ≠ 0) :
    ∫ p, s p • A p ∂μ ≠ 0 := by
  intro h0
  apply h
  have hξ : ξ ≠ 0 := by
    rintro rfl
    simp at h
  have hξn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
  by_cases hint : Integrable (fun p => s p • A p) μ
  · have h1 := ContinuousLinearMap.integral_apply hint ξ
    rw [h0] at h1
    simpa using h1.symm
  · apply integral_undef
    intro hint2
    apply hint
    have hAξ : AEStronglyMeasurable (fun p => A p ξ) μ :=
      (ContinuousLinearMap.apply ℂ V ξ).continuous.comp_aestronglyMeasurable hA
    have hnC : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξn
    have hs : AEStronglyMeasurable s μ := by
      have h1 : AEStronglyMeasurable
          (fun p => ⟪A p ξ, s p • A p ξ⟫_ℂ / (((‖ξ‖ : ℝ) : ℂ) ^ 2)) μ :=
        (continuous_id.div_const (((‖ξ‖ : ℝ) : ℂ) ^ 2)).comp_aestronglyMeasurable
          (hAξ.inner hint2.aestronglyMeasurable)
      refine h1.congr ?_
      filter_upwards [hu] with p hp
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hp ξ]
      first
      | (field_simp; done)
      | (field_simp; rfl)
      | (rw [mul_div_assoc, div_self (pow_ne_zero _ hnC), mul_one])
    refine Integrable.mono' (g := fun p => ‖ξ‖⁻¹ * ‖s p • A p ξ‖) (hint2.norm.const_mul _)
      (hs.smul hA) ?_
    filter_upwards [hu] with p hp
    calc ‖s p • A p‖ ≤ ‖s p‖ * ‖A p‖ := norm_smul_le _ _
      _ ≤ ‖s p‖ * 1 := mul_le_mul_of_nonneg_left (opNorm_le_one_of_isometry _ hp) (norm_nonneg _)
      _ = ‖ξ‖⁻¹ * ‖s p • A p ξ‖ := by
        rw [norm_smul, hp ξ]
        field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap.TopClm
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopPi

open ReciprocityTheory.ChartRestriction.DS.Lap

variable {k r : ℕ}

theorem inv_mem_UWset {z : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UWset k r z) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := by
  obtain ⟨hgH, hfix, hz⟩ := hg
  have hinv : g⁻¹ * g = 1 := ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hgH
  have key : ∀ y, g *ᵥ y = y → g⁻¹ *ᵥ y = y := by
    intro y hy
    calc g⁻¹ *ᵥ y = g⁻¹ *ᵥ (g *ᵥ y) := by rw [hy]
      _ = (g⁻¹ * g) *ᵥ y := by rw [Matrix.mulVec_mulVec]
      _ = y := by rw [hinv, Matrix.one_mulVec]
  exact ⟨inv_mem_UH' hgH, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem isClosed_UWset (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (Formalism.QuantumDeterminants.UWset k r z) := by
  have hU : IsClosed {g : Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h1 : IsClosed {g : Mat k r | ∀ a : Fin r,
      g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) ∧
        g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun a =>
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  have h2 : IsClosed {g : Mat k r | g *ᵥ z = z} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  exact hU.inter (h1.inter h2)

theorem piInv_facts (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) {Vp : Type} [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π) (hμW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hμN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹) (μW.prod μN) ∧
      ∀ᵐ p ∂(μW.prod μN), ∀ v : Vp, ‖π (Matrix.of p.1)⁻¹ v‖ = ‖v‖ := by
  have hπU := hcTypeW_uRep k r z u Vp π hz hT hπ
  have := hμW.1
  have := hμN.1
  have hof : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mat k r) :=
    continuous_fst
  have hTae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hμW.2.2.1)
  have hTc : IsClosed {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z} :=
    (isClosed_UWset z).preimage hof
  have hπc : ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) := continuousOn_clm_apply.2 hπU.2.2
  have hinv : ContinuousOn (fun g : Mat k r => g⁻¹) (Formalism.QuantumDeterminants.UWset k r z) := by
    intro g hg
    have hgi : g⁻¹ * g = 1 := ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hg.1
    have hu : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hgi
    have hc := NormedRing.inverse_continuousAt hu.unit
    rw [IsUnit.unit_spec] at hc
    exact (continuousAt_matrix_inv g hc).continuousWithinAt
  have hcont : ContinuousOn (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹)
      {p | Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z} :=
    hπc.comp (hinv.comp hof.continuousOn fun p hp => hp) fun p hp => inv_mem_UWset hp
  refine ⟨?_, ?_⟩
  · have h := hcont.aestronglyMeasurable (μ := μW.prod μN) hTc.measurableSet
    have hTae' : ∀ᵐ p ∂(μW.prod μN),
        p ∈ {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z} := hTae
    rw [Measure.restrict_eq_self_of_ae_mem hTae'] at h
    exact h
  · filter_upwards [hTae] with p hp v
    exact hπU.2.1 _ (inv_mem_UWset hp) v

end ReciprocityTheory.ChartRestriction.DS.Lap.TopPi
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopNV

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def BesselNVUnder (Gap : ℕ → ∀ r : ℕ, (Fin (2 * r + 2) → ℝ) → Prop) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.InterlacingCondition k r u v b →
    Formalism.MainNotions.CayleySignature.HalfIntegralDifference k r u v b → Gap k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Formalism.MainNotions.CayleySignature.Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDSHpk k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Formalism.MainNotions.CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), Formalism.MainNotions.S.IsHCTypeW k r z u π →
  ∀ w : H, Formalism.MainNotions.S.IsLowUnitH k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
  ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Formalism.MainNotions.CayleySignature.Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
          star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

def BesselNVG : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.InterlacingCondition k r u v b →
    Formalism.MainNotions.CayleySignature.HalfIntegralDifference k r u v b → Formalism.MainNotions.CayleySignature.GapBig k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Formalism.MainNotions.CayleySignature.Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDSHpk k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Formalism.MainNotions.CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), Formalism.MainNotions.S.IsHCTypeW k r z u π →
  ∀ w : H, Formalism.MainNotions.S.IsLowUnitH k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
  ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Formalism.MainNotions.CayleySignature.Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
          star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

theorem urep_of_isDSHpk {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)}
    (hd : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ := by
  obtain ⟨P, hP, hDS⟩ := hd
  have h1 : P⁻¹ * P = 1 := bridge_inv_mul k r ε P hP
  have hback : (fun g => σ (P⁻¹ * (P * g * P⁻¹) * P)) = σ := by
    funext g
    have : P⁻¹ * (P * g * P⁻¹) * P = g := by
      calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = g := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    rw [this]
  have := ReciprocityTheory.ChartRestriction.DS.isURepOn_UH_of hP hDS.2.2.1
  rwa [hback] at this

theorem inner_shift {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ)
    {x₀ g x : Mat k r} (hx₀ : x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (w : H) :
    ⟪σ x₀ w, σ g (σ x w)⟫_ℂ = ⟪w, σ (x₀⁻¹ * (g * x)) w⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hnorm, -⟩ := hσ
  have hinv : x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := S0.Core.inv_mem_UH k r x₀ hx₀
  have hgx : g * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := S0.Core.mul_mem_UH k r hg hx
  have hxx : x₀ * x₀⁻¹ = 1 := S0.Core.mul_inv_UH k r hx₀
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := (σ x₀ : H →ₗ[ℂ] H), norm_map' := hnorm x₀ hx₀ }
  have key : σ x₀ (σ x₀⁻¹ (σ (g * x) w)) = σ (g * x) w := by
    have hc := hmul x₀ hx₀ x₀⁻¹ hinv
    rw [hxx, h1] at hc
    have := congrArg (fun A : H →L[ℂ] H => A (σ (g * x) w)) hc
    simpa using this.symm
  calc ⟪σ x₀ w, σ g (σ x w)⟫_ℂ = ⟪σ x₀ w, σ (g * x) w⟫_ℂ := by
        simp only [hmul g hg x hx, ContinuousLinearMap.comp_apply]
    _ = ⟪f w, f (σ x₀⁻¹ (σ (g * x) w))⟫_ℂ := by
        change _ = ⟪σ x₀ w, σ x₀ (σ x₀⁻¹ (σ (g * x) w))⟫_ℂ
        rw [key]
    _ = ⟪w, σ x₀⁻¹ (σ (g * x) w)⟫_ℂ := f.inner_map_map _ _
    _ = ⟪w, σ (x₀⁻¹ * (g * x)) w⟫_ℂ := by
        simp only [hmul x₀⁻¹ hinv (g * x) hgx, ContinuousLinearMap.comp_apply]

theorem besselNVG_of (hB : BAtTargetStatement) (hSZ : SigZeroStatement) : BesselNVG := by
  intro k r z c u v b hk2 hke hz hT hc hu hlam hint hhalf hgap H _ _ _ σ hd Vp _ _ _ π hπ w hw μW μN hμW hμN
  have : CompleteSpace Vp := FiniteDimensional.complete ℂ Vp
  have hset48 : Formalism.MainNotions.CayleySignature.RealPlaceNumericalSetting k r z c u v b :=
    ⟨by omega, hke, hz, hT, hc, hu, hlam, hint, hhalf, hgap⟩
  obtain ⟨h, hset⟩ := gapBig_gapLap k r z c u v b hset48
  have hgl := hset.2.2.2.2.2.2.2.2.2.2
  obtain ⟨H₀, i₁, i₂, i₃, σ₀, hd₀, -, hcoef⟩ := hSZ k r z c u v b h hset
  have hσU : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ := urep_of_isDSHpk hd
  obtain ⟨P, hP, hDS⟩ := hd
  obtain ⟨P', hP', hlow⟩ := hw
  obtain ⟨P₀, hP₀, hDS₀⟩ := hd₀
  have hDS' := (cayleyIndep k r _ _ H σ P P' hP hP' hDS).1
  have hDS₀' := (cayleyIndep k r _ _ H₀ σ₀ P₀ P' hP₀ hP' hDS₀).1
  obtain ⟨w₀, hlow₀, hsame⟩ := dsUniv (2 * r + k + 1) _ _ hlam h hgl H (fun g => σ (P'⁻¹ * g * P'))
    H₀ (fun g => σ₀ (P'⁻¹ * g * P')) hDS' hDS₀' w hlow
  have hcoefUH : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ⟪w₀, σ₀ g w₀⟫_ℂ = ⟪w, σ g w⟫_ℂ := by
    intro g hg
    obtain ⟨hgJ, hback⟩ := bridge_conj k r _ P' hP' g hg
    have hg' := hsame _ hgJ
    rwa [hback] at hg'
  obtain ⟨-, -, T, μ, P₁, v₁, c₁, hv₁, hc₁, hμ, hP₁, hpsi⟩ := hcoef w₀ ⟨P', hP', hlow₀⟩
  have hBD : IsBData z c u π μW μN := ⟨hz, hT, hc, hπ, hμW, hμN⟩
  obtain ⟨ξ, x₀, x, hx₀, hx, hne⟩ := hB k r z c u v b h hset T μ P₁ z c Vp π μW μN hμ hP₁ hBD v₁ hv₁
  have hshift := sInt_shift_eq_smul z μW μN hμW hμN (Formalism.MainNotions.S.psiGen k r z c) π
    (fun y => ⟪w, σ y w⟫_ℂ) (psiCoef T μ P₁ v₁ v₁) c₁
    (fun y hy => by rw [← hcoefUH y hy]; exact hpsi y hy) ξ x₀ x hx₀ hx
  have hS : sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π (fun y => ⟪w, σ (x₀⁻¹ * y) w⟫_ℂ) ξ x ≠ 0 := by
    rw [hshift]
    exact smul_ne_zero hc₁ hne
  obtain ⟨hA, huA⟩ := TopPi.piInv_facts z u π μW μN hz hT hπ hμW hμN
  refine ⟨x, x₀, hx, hx₀, ?_⟩
  refine TopClm.integral_ne_zero_of_apply (μ := μW.prod μN)
    (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
        star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2)))
    (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹) hA huA ξ ?_
  have := hμW.1
  have := hμN.1
  have hae₁ : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hμW.2.2.1)
  have hae₂ : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hμN.2.2.1)
  have heq : (∫ p, (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
      star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ ξ ∂(μW.prod μN)) =
      sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π (fun y => ⟪w, σ (x₀⁻¹ * y) w⟫_ℂ) ξ x := by
    unfold sInt chiInv
    refine integral_congr_ae ?_
    filter_upwards [hae₁, hae₂] with p h₁ h₂
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      S0.Core.mul_mem_UH k r h₁.1 h₂.1
    rw [inner_shift hσU hx₀ hg hx w, mul_smul]
  rw [heq]
  exact hS

end ReciprocityTheory.ChartRestriction.DS.Lap.TopNV
end
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopFinal

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

theorem bAtTarget_of (hNV : NVStatement) : BAtTargetStatement := by
  intro k r z c u v b h hS
  obtain ⟨hk, -, -, -, -, -, hHC, hI, hH, hL, hG⟩ := hS
  exact hNV k r u v b h hk hHC hI hH hL hG

theorem besselNVG_of_nv (hNV : NVStatement) : TopNV.BesselNVG :=
  TopNV.besselNVG_of (bAtTarget_of hNV) (sigZero fun m => S7.psiAll (n := m))

end ReciprocityTheory.ChartRestriction.DS.Lap.TopFinal
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed

theorem nvAll : NVStatement := nv NVHTop.intS

theorem besselNVG : TopNV.BesselNVG := TopFinal.besselNVG_of_nv nvAll

end ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed
end
