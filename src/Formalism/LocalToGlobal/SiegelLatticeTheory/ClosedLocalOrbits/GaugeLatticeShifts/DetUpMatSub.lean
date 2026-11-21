import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates

section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

namespace JL

def RightInvS : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μ →
    ∀ s ∈ SLoc ε e z, μ.map (fun x => x * s) = μ

theorem frameLoc_swap {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ}
    (hF : FrameLoc ε k e z z' T T') : FrameLoc ε k e z' z T' T :=
  ⟨hF.dim, hF.k_pos, hF.sig, hF.e_li, hF.ee, hF.ez', hF.ez, hF.zz', hF.zz, hF.T'_pos, hF.T_pos⟩

theorem lintegral_mul_right_of_map {n : ℕ} {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε))
    (t : Formalism.REAL.UJ ε) (hμ : μ.map (fun x => x * t) = μ) (F : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂μ := by
  have hE : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  calc ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂(μ.map (fun x => x * t)) := (hE.lintegral_map F).symm
    _ = ∫⁻ x, F x ∂μ := by rw [hμ]

theorem inner_dc {n : ℕ} {ε : Fin n → Bool} (μS μS' : Measure (Formalism.REAL.UJ ε))
    (s₁ s₁' g : Formalism.REAL.UJ ε) (h₁ : μS.map (fun x => x * s₁) = μS)
    (h₁' : μS'.map (fun x => x * s₁') = μS') (φ : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ s, ∫⁻ s', φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) ∂μS' ∂μS = ∫⁻ s, ∫⁻ s', φ (s * g * s'⁻¹) ∂μS' ∂μS := by
  have key : ∀ s s' : Formalism.REAL.UJ ε,
      φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) = φ ((s * s₁) * g * (s' * s₁')⁻¹) := by
    intro s s'
    congr 1
    group
  have inner : ∀ x : Formalism.REAL.UJ ε,
      ∫⁻ s', φ (x * g * (s' * s₁')⁻¹) ∂μS' = ∫⁻ s', φ (x * g * s'⁻¹) ∂μS' := fun x =>
    lintegral_mul_right_of_map μS' s₁' h₁' (fun y => φ (x * g * y⁻¹))
  simp_rw [key, inner]
  exact lintegral_mul_right_of_map μS s₁ h₁ (fun x => ∫⁻ s', φ (x * g * s'⁻¹) ∂μS')

theorem measurableSet_goodLoc (r : ℕ) (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  have hD : ∀ l, Continuous fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l := by
    intro l
    by_cases h : l ≤ r + 1
    · simp only [Dl, dif_pos h]
      exact (continuous_id.matrix_diagonal.matrix_submatrix _ _).matrix_det
    · simp only [Dl, dif_neg h]
      exact continuous_const
  have hG : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv]
    exact ((hD (r + 1)).norm.pow 2).sub (continuous_const.mul ((hD r).norm.pow 2))
  have h0 : MeasurableSet {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun l => (measurable_pi_apply l) (measurableSet_singleton 0).compl
  unfold GoodLoc
  rw [Set.ofPred_and]
  exact h0.inter (measurableSet_lt measurable_const hG.measurable)

end JL

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

abbrev MZ (r : ℕ) : Type := Fin (r + 1) → Fin (r + 1) → ℂ

abbrev UC (r : ℕ) : Type := {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → ℂ

def upMat {r : ℕ} (y : UC r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun a b => if a = b then 1 else if h : a < b then y ⟨(a, b), h⟩ else 0

def ZAct : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (s s' g : Formalism.REAL.UJ ε)
    (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
    (∀ b, uMat s⁻¹ *ᵥ f b = ∑ a, P a b • f a) → (∀ b, uMat s'⁻¹ *ᵥ f' b = ∑ a, P' a b • f' a) →
    Zhat ε f f' (uMat (s * g * s'⁻¹)) = Pᴴ * Zhat ε f f' (uMat g) * P'

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem hJ_sum_sum' {n : ℕ} (ε : Fin n → Bool) {ι : Type} [Fintype ι] (a b : ι → ℂ) (x y : ι → Fin n → ℂ) :
    hJ ε (∑ j, a j • x j) (∑ k, b k • y k) = ∑ j, ∑ k, conj (a j) * b k * hJ ε (x j) (y k) := by
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, star_sum, star_smul,
    dotProduct_sum, sum_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hJ_adj {n : ℕ} {ε : Fin n → Bool} (s : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat s *ᵥ y) = hJ ε (uMat s⁻¹ *ᵥ x) y := by
  have hU : (uMat s)ᴴ * Formalism.REAL.Jm ε * uMat s = Formalism.REAL.Jm ε := s.2
  have hinv : uMat s * uMat s⁻¹ = 1 := by
    simp [Formalism.MainNotions.S.uMat]
  have hJc : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rw [Pi.star_apply]
    split_ifs <;> simp
  have h1 : (uMat s)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s⁻¹ := by
    calc (uMat s)ᴴ * Formalism.REAL.Jm ε = (uMat s)ᴴ * Formalism.REAL.Jm ε * (uMat s * uMat s⁻¹) := by
          rw [hinv, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * uMat s⁻¹ := by rw [← Matrix.mul_assoc, hU]
  have key : (uMat s⁻¹)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s := by
    have h2 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJc] at h2
    exact h2.symm
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key]

theorem zAct : ZAct := by
  intro n r ε f f' s s' g P P' hP hP'
  ext a b
  have hu : uMat (s * g * s'⁻¹) = uMat s * uMat g * uMat s'⁻¹ := by
    simp [Formalism.MainNotions.S.uMat]
  have hw : uMat g *ᵥ (uMat s'⁻¹ *ᵥ f' b) = ∑ d, P' d b • (uMat g *ᵥ f' d) := by
    rw [hP' b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  rw [Formalism.L2.SG.RealObj.Zhat, hu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJ_adj, hP a, hw,
    hJ_sum_sum']
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.L2.SG.RealObj.Zhat, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem upMat_lower {r : ℕ} (y : UC r) (a b : Fin (r + 1)) (h : b < a) : upMat y a b = 0 := by
  have h1 : a ≠ b := ne_of_gt h
  have h2 : ¬ a < b := not_lt.mpr h.le
  simp [upMat, h1, h2]

theorem upMat_diag {r : ℕ} (y : UC r) (a : Fin (r + 1)) : upMat y a a = 1 := by
  simp [upMat]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end
