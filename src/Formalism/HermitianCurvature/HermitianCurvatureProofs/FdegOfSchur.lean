import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvSig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem unit_of_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  obtain ⟨-, h2, -⟩ := PI.WBL.Cv.grpAll k r 0
  exact ⟨(h2 g hg).1, (h2 g hg).2.1⟩

theorem inv_inv_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹⁻¹ = g :=
  Matrix.inv_eq_left_inv (unit_of_uh hg).1

theorem inner_sig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hU : PI.WBL.Cv.SigU σ) {a : Mx k r} (ha : a ∈ UH (Hpk k r)) (u v : H) :
    ⟪σ a u, v⟫_ℂ = ⟪u, σ a⁻¹ v⟫_ℂ := by
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ a : H →ₗ[ℂ] H), norm_map' := hU.2.2 a ha }
  have hai : a⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_inv ha
  have hv : σ a (σ a⁻¹ v) = v := by
    rw [← ContinuousLinearMap.comp_apply, ← hU.2.1 a ha _ hai, (unit_of_uh ha).1, hU.1]; rfl
  calc ⟪σ a u, v⟫_ℂ = ⟪T u, T (σ a⁻¹ v)⟫_ℂ := by
        show ⟪σ a u, v⟫_ℂ = ⟪σ a u, σ a (σ a⁻¹ v)⟫_ℂ
        rw [hv]
    _ = ⟪u, σ a⁻¹ v⟫_ℂ := T.inner_map_map _ _

theorem adjoint_of_iso {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] E) (hAB : A.comp B = 1) (hA : ∀ v, ‖A v‖ = ‖v‖) :
    ContinuousLinearMap.adjoint A = B := by
  let T : E →ₗᵢ[ℂ] E := { toLinearMap := (A : E →ₗ[ℂ] E), norm_map' := hA }
  refine ((ContinuousLinearMap.eq_adjoint_iff B A).mpr fun x y => ?_).symm
  have hx : A (B x) = x := by rw [← ContinuousLinearMap.comp_apply, hAB]; rfl
  calc ⟪B x, y⟫_ℂ = ⟪T (B x), T y⟫_ℂ := (T.inner_map_map _ _).symm
    _ = ⟪x, A y⟫_ℂ := by show ⟪A (B x), A y⟫_ℂ = _; rw [hx]

theorem adjoint_pi {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (E →L[ℂ] E)} (hrep : IsCRepOn (UWset k r z) π)
    (hun : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {h : Mx k r} (hh : h ∈ UWset k r z) :
    ContinuousLinearMap.adjoint (π h) = π h⁻¹ := by
  refine adjoint_of_iso _ _ ?_ (hun h hh)
  rw [← hrep.2 h hh _ (WeylGroupFacts.uw_inv hh), (unit_of_uh hh.1).1, hrep.1]

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem measurePreserving_invM_of_isHaarOn {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (h : B.IsHaarOn (UWset k r z) μ) :
    MeasurePreserving (B7.invM (k := k) (r := r)) μ μ :=
  ⟨B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μ (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) h⟩

theorem mp_inv_N {μ : Measure (Mt k r)} (h : B.IsHaarOn (Nset k r) μ) :
    MeasurePreserving (B7.invM (k := k) (r := r)) μ μ :=
  ⟨B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) h⟩

end Formalism.FourierDecayAlt.P.S3dx6
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def aInt {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 a : H) (t : Mx k r) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (psi k r z c (Matrix.of p.2) * ⟪a, σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹ * t) w0⟫_ℂ) • π (Matrix.of p.1)

def bInt {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wq →L[ℂ] Wq)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 y : H) (t γ : Mx k r) (p : Mt k r × Mt k r) : Wq →L[ℂ] Wq :=
  (star (psi k r z c (Matrix.of p.2)) * ⟪w0, σ (t⁻¹ * γ * Matrix.of p.2 * Matrix.of p.1) y⟫_ℂ) •
    π (Matrix.of p.1)⁻¹

theorem aInt_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) (w0 a : H) {t : Mx k r} (ht : t ∈ UH (Hpk k r))
    {p : Mt k r × Mt k r} (hp1 : Matrix.of p.1 ∈ UWset k r z) (hp2 : Matrix.of p.2 ∈ Nset k r) :
    beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p) = aInt z c π σ w0 a t p := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp1 hp2
  have hh : Matrix.of p1 ∈ UH (Hpk k r) := hp1.1
  have hn : Matrix.of p2 ∈ UH (Hpk k r) := hp2.1
  have hinv : ((Matrix.of p1)⁻¹)⁻¹ = Matrix.of p1 :=
    Matrix.inv_eq_left_inv (PI.WBL.Cv.uh_inv hh).1
  have hmul : σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) =
      (σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹)).comp (σ t) :=
    hU.2.1 _ (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hh).2.2 (PI.WBL.Cv.uh_inv hn).2.2) t ht
  have hpsi := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z c hz (Matrix.of p2) hp2
  show (⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹) (σ t w0)⟫_ℂ *
      star (psi k r z c (Matrix.of p2)⁻¹)) • π ((Matrix.of p1)⁻¹)⁻¹ =
    (psi k r z c (Matrix.of p2) * ⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) w0⟫_ℂ) •
      π (Matrix.of p1)
  rw [hinv, hpsi, hmul, ContinuousLinearMap.comp_apply, mul_comm]

private theorem ae_mem_uwset_prod_nset_of_isHaarOn {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
  haveI : IsFiniteMeasureOnCompacts μW := ⟨fun K hK => hW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μN := ⟨fun K hK => hN.finite_compact K hK⟩
  rw [ae_iff]
  apply measure_mono_null (t := ((UWset k r z)ᶜ : Set (Mt k r)) ×ˢ (Set.univ : Set (Mt k r)) ∪
    (Set.univ : Set (Mt k r)) ×ˢ ((Nset k r)ᶜ : Set (Mt k r)))
  · intro p hp
    simp only [Set.mem_setOf_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨hp, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, hp⟩
  · apply measure_union_null
    · rw [Measure.prod_prod, hW.conc, zero_mul]
    · rw [Measure.prod_prod, hN.conc, mul_zero]

theorem sideA {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) (w0 a : H) {t : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hI : Integrable (beInt z c π σ (σ t w0) a) (μW.prod μN)) :
    Integrable (aInt z c π σ w0 a t) (μW.prod μN) ∧
      ∫ p, aInt z c π σ w0 a t p ∂(μW.prod μN) = be z c π σ μW μN (σ t w0) a := by
  haveI : IsFiniteMeasureOnCompacts μW := ⟨fun K hK => hW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μN := ⟨fun K hK => hN.finite_compact K hK⟩
  have hmp : MeasurePreserving (Prod.map (B7.invM (k := k) (r := r)) (B7.invM (k := k) (r := r)))
      (μW.prod μN) (μW.prod μN) :=
    (measurePreserving_invM_of_isHaarOn hW).prod (mp_inv_N hN)
  have hae : (fun p => beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p)) =ᵐ[μW.prod μN]
      aInt z c π σ w0 a t := by
    filter_upwards [ae_mem_uwset_prod_nset_of_isHaarOn hW hN] with p hp
    exact aInt_eq hz c π hU w0 a ht hp.1 hp.2
  have hcomp : Integrable (fun p => beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p))
      (μW.prod μN) :=
    (hmp.integrable_comp hI.aestronglyMeasurable).mpr hI
  refine ⟨hcomp.congr hae, ?_⟩
  rw [← integral_congr_ae hae]
  unfold be
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hI.aestronglyMeasurable)]

theorem integral_adjoint {α : Type*} [MeasurableSpace α] {μ : Measure α} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {f : α → (E →L[ℂ] F)} (hf : Integrable f μ) :
    Integrable (fun x => ContinuousLinearMap.adjoint (f x)) μ ∧
      ∫ x, ContinuousLinearMap.adjoint (f x) ∂μ = ContinuousLinearMap.adjoint (∫ x, f x ∂μ) := by
  let L : (E →L[ℂ] F) ≃ₗᵢ[ℝ] (F →L[ℂ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := F)).toIsometryEquiv.toRealLinearIsometryEquivOfMapZero
      (map_zero (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := F)))
  have hL : ∀ g, L g = ContinuousLinearMap.adjoint g := fun g => rfl
  refine ⟨?_, ?_⟩
  · have := L.toLinearIsometry.toContinuousLinearMap.integrable_comp hf
    simpa [hL] using this
  · have := L.toLinearIsometry.toContinuousLinearMap.integral_comp_comm hf
    simpa [hL] using this

end Formalism.FourierDecayAlt.P.S3dx6
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gN_mt_cont : Continuous fun x : Mt k r => B.gN (Matrix.of x) := by
  unfold B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem conv_pt (hNI : NormInv) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) {t g : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) := by
  obtain ⟨_, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)
  have htg : t⁻¹ * g ∈ UH (Hpk k r) := hmul _ (hinv t ht).2 _ hg
  have hA : 1 ≤ B.gN t := ((hNI k r).2 t ht).2
  have hG : 1 ≤ B.gN g := ((hNI k r).2 g hg).2
  have hC : 1 ≤ B.gN (t⁻¹ * g) := ((hNI k r).2 _ htg).2

  have hsub : B.gN g ≤ B.gN t * B.gN (t⁻¹ * g) := by
    have h1 : t * (t⁻¹ * g) = g := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hinv t ht).1, one_mul]
    calc B.gN g = B.gN (t * (t⁻¹ * g)) := by rw [h1]
      _ ≤ _ := (hNI k r).1 _ _
  have hA0 : 0 < B.gN t := by linarith
  have hC0 : 0 < B.gN (t⁻¹ * g) := by linarith
  have hG0 : 0 < B.gN g := by linarith
  have h1 : B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b) ≤ B.gN g ^ (-b) := by
    rw [← Real.mul_rpow hA0.le hC0.le, Real.rpow_neg (by positivity), Real.rpow_neg hG0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hG0 b) (Real.rpow_le_rpow hG0.le hsub hb)
  have h2 : B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN (t⁻¹ * g) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a)
      ≤ B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-b) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA0.le _)
    _ = B.gN t ^ (b - a) * (B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b)) := by
        rw [← mul_assoc, ← Real.rpow_add hA0, show b - a + -b = -a by ring]
    _ ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA0.le _)

def trivS {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r ℂ ℂ where
  z := D.z
  z' := D.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := D.μG
  μW := D.μW
  μN := D.μN
  μW' := D.μW'
  μsec := D.μsec
  χ := D.χ
  k_pos := D.k_pos
  z_mem := D.z_mem
  z'_mem := D.z'_mem
  T_pos := D.T_pos
  T'_pos := D.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := D.haarG
  haarW := D.haarW
  haarN := D.haarN
  haarW' := D.haarW'
  sec := D.sec
  χ_smooth := D.χ_smooth
  χ_supp := D.χ_supp
  χ_int := D.χ_int





def fZ (b : ℝ) (g : B.Mat k r) : ℂ →L[ℂ] ℂ := ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)



end Formalism.FourierDecayAlt.P.S3dx6
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_nonneg (g : Mx k r) : 0 ≤ B.gN g := Real.sqrt_nonneg _

end Formalism.FourierDecayAlt.P.S3dx6
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def phiF (D : B.RealPlaceData k r Wp Wq) (σ : Mx k r → (H →L[ℂ] H)) (w0 x y : H) (X0 : Wq →L[ℂ] Wp) (γ : Mx k r)
    (q : B.SS k r × Mt k r) : Wq →L[ℂ] Wp :=
  (aInt D.z cStd D.π σ w0 x (Matrix.of q.2) q.1.1).comp
    (X0.comp (bInt D.z' cStd D.π' σ w0 y (Matrix.of q.2) γ q.1.2))

theorem continuous_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous fun g : Mt k r => psi k r z c (Matrix.of g) := by
  have hl := B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

attribute [local instance] B7.properFD

end Formalism.FourierDecayAlt.P.S3dx6
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem one_mem_uh : (1 : Mx k r) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_DD {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    {t : Mx k r} (ht : t ∈ UH (Hpk k r)) : σ t w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨t, ht, rfl⟩

theorem fdeg_of_schur {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {μG : Measure (Mt k r)} {w0 : H} (hw : w0 ≠ 0) {d : ℝ} (hd : 0 < d)
    (hS : ∫ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ ∂μG =
      ⟪w0, w0⟫_ℂ * ⟪w0, w0⟫_ℂ / (d : ℂ)) :
    PI.BesselPeriodGGP.fdegH μG σ w0 = d := by

  have hpt : ∀ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ =
      ((‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [show star ⟪w0, σ (Matrix.of x) w0⟫_ℂ = (starRingEnd ℂ) ⟪w0, σ (Matrix.of x) w0⟫_ℂ from rfl,
      RCLike.mul_conj]
    norm_cast
  simp_rw [hpt] at hS
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hS
  have hI : (∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG) = ‖w0‖ ^ 4 / d := by
    have h2 : ((‖w0‖ ^ 4 / d : ℝ) : ℂ) = (‖w0‖ : ℂ) ^ 2 * (‖w0‖ : ℂ) ^ 2 / (d : ℂ) := by
      push_cast; ring
    exact_mod_cast hS.trans h2.symm
  have hw' : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw
  simp only [PI.BesselPeriodGGP.fdegH]
  rw [hI]
  field_simp

end Formalism.FourierDecayAlt.P.S3dx6
end
end
