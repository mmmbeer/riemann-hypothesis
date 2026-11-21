import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansion
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

section
noncomputable section

open PositivityTheory.jumpWindows
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothVectors

theorem contDiffOn_of_fderiv_family {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {U : Set E} (hU : IsOpen U)
    (o : P → E → F) (S : Set P) (A : Fin n → E → E →L[ℝ] ℝ)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (h : ∀ v ∈ S, ∃ w : Fin n → P, (∀ i, w i ∈ S) ∧
      ∀ M ∈ U, HasFDerivAt (o v) (∑ i, (A i M).smulRight (o (w i) M)) M) :
    ∀ v ∈ S, ContDiffOn ℝ ∞ (o v) U := by
  have key : ∀ m : ℕ, ∀ v ∈ S, ContDiffOn ℝ m (o v) U := by
    intro m
    induction m with
    | zero =>
      intro v hv
      obtain ⟨w, -, hw⟩ := h v hv
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun M hM => (hw M hM).continuousAt.continuousWithinAt
    | succ m ih =>
      intro v hv
      obtain ⟨w, hwS, hw⟩ := h v hv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun M hM => (hw M hM).differentiableAt.differentiableWithinAt, fun hm => ?_, ?_⟩
      · exact absurd hm (by simp)
      · refine ContDiffOn.congr (f := fun M => ∑ i, (A i M).smulRight (o (w i) M)) ?_
          fun M hM => (hw M hM).fderiv
        exact ContDiffOn.sum fun i _ =>
          (contDiffOn_infty.1 (hA i) m).smulRight (ih (w i) (hwS i))
  intro v hv
  exact contDiffOn_infty.2 fun m => key m v hv

section Chart

variable {ι : Type} [Fintype ι] {a : ℕ}

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chart : LieI ι a ≃L[ℝ] Matrix (Fin a) (Fin a) (ι → ℂ) :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

end Norm

end Chart

section Orbit

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

end Orbit

end GlobalTheory.CompanionTheory.SmoothVectors

end
end

section
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem contDiffOn_of_right_family : ∀ (n : ℕ) (V P : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (o : P → Mat n → V) (d : (Bool × Fin n × Fin n) → P → P), (∀ v, ∀ z ∈ GLs n, DifferentiableAt ℝ (o v) z) → (∀ v p, ∀ z ∈ GLs n, Rd (bs p) (o v) z = o (d p v) z) → ∀ v, ContDiffOn ℝ ∞ (o v) (GLs n) := by
  intro n V P _ _ o d hdiff hR v
  obtain ⟨A, hA, hfr⟩ := GlobalTheory.T.derivative_right_basis_expansion n
  let e := Fintype.equivFin (Bool × Fin n × Fin n)
  refine GlobalTheory.CompanionTheory.SmoothVectors.contDiffOn_of_fderiv_family isOpen_GLs o Set.univ
    (fun i => A (e.symm i)) (fun i => hA _) ?_ v (Set.mem_univ v)
  intro u _
  refine ⟨fun i => d (e.symm i) u, fun i => Set.mem_univ _, fun z hz => ?_⟩
  have hD := hfr V (fderiv ℝ (o u) z) z hz
  have hsum : (∑ i, (A (e.symm i) z).smulRight (o (d (e.symm i) u) z))
      = ∑ p, (A p z).smulRight (o (d p u) z) :=
    e.symm.sum_comp (fun p => (A p z).smulRight (o (d p u) z))
  have hval : ∀ p, fderiv ℝ (o u) z (z * bs p) = o (d p u) z := fun p => hR u p z hz
  have h2 : fderiv ℝ (o u) z = ∑ p, (A p z).smulRight (o (d p u) z) :=
    hD.trans (Finset.sum_congr rfl fun p _ => congrArg (fun y : V => (A p z).smulRight y) (hval p))
  exact (hdiff u z hz).hasFDerivAt.congr_fderiv (h2.trans hsum.symm)

end GlobalTheory.CompanionTheory.PresSobA
end
end

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_derivative_system_smooth : ∀ (n : ℕ) (V P : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (o : P → Mat n → V) (d : (Bool × Fin n × Fin n) → P → P), (∀ v, ∀ z ∈ GLs n, DifferentiableAt ℝ (o v) z) → (∀ v p, ∀ z ∈ GLs n, Rd (bs p) (o v) z = o (d p v) z) → ∀ v, ContDiffOn ℝ ∞ (o v) (GLs n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family
end
end
