import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
import CompanionTheory.HarishChandraModules.NonemptyRepresentations.ExpEntry
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket

section
open Matrix Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.HolCoef

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def cone : Set (B.Mat 4 0) := {g | g 4 4 ≠ 0}

def minor2 (g : B.Mat 4 0) : ℂ := (g.submatrix ![3, 4] ![3, 4]).det

def minor3 (g : B.Mat 4 0) : ℂ := (g.submatrix ![2, 3, 4] ![2, 3, 4]).det

def minor4 (g : B.Mat 4 0) : ℂ := (g.submatrix ![1, 2, 3, 4] ![1, 2, 3, 4]).det

def coef (p N : ℕ) (g : B.Mat 4 0) : ℂ := (g 4 4 ^ N)⁻¹ * (minor2 g ^ p * minor3 g ^ p * minor4 g)

def wt (p N : ℕ) : Fin (2 * 0 + 4 + 1) → ℂ := ![0, 1, (p : ℂ) + 1, 2 * (p : ℂ) + 1, 2 * (p : ℂ) + 1 - N]

def eul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b c d : Fin (2 * 0 + 4 + 1)) (f : B.Mat 4 0 → E) :
    B.Mat 4 0 → E := fun g => g c d • fderiv ℂ f g (Matrix.single a b 1)

section deriv

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_exp_real (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => CompanionTheory.D.Inhab.exp_entry n X i j

theorem rdV_eq_fderiv (X g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : DifferentiableAt ℂ f g) : RdV X f g = fderiv ℂ f g (g * X) := by
  unfold RdV
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ := (LinearMap.mulLeft ℝ g).toContinuousLinearMap
  have h1 : HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_real X)
  have h2 : HasFDerivAt f ((fderiv ℂ f g).restrictScalars ℝ) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
    rw [Matrix.mul_one]
    exact hf.hasFDerivAt.restrictScalars ℝ
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv



end deriv

end GlobalTheory.CompanionTheory.HolCoef
end
end

section
open Formalism.REAL Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.HolCoef.CapLW

section perm

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

omit [Algebra ℂ A] in
theorem glRel_perm {E : Fin n → Fin n → A} (hE : GlRel E) (σ : Equiv.Perm (Fin n)) :
    GlRel fun a b => E (σ a) (σ b) := by
  intro a b c d
  simpa only [σ.injective.eq_iff] using hE (σ a) (σ b) (σ c) (σ d)

theorem qdet_perm {E : Fin n → Fin n → A} (hE : GlRel E) (σ : Equiv.Perm (Fin n)) (u : ℂ) :
    qdet (fun a b => E (σ a) (σ b)) u = qdet E u := by
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => if c = σ a then 1 else 0
  let Q : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun b d => if d = σ b then 1 else 0
  have hQP : Q * P = 1 := by
    ext b a
    simp [P, Q, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h := (Formalism.FourierDecayAlt.P.contractions_covariant A n E P Q hE hQP (mul_eq_one_comm.1 hQP) u 0 0 0 0).1
  rw [← h]
  congr 1
  funext a b
  simp [Formalism.FourierDecayAlt.Q.Econj, P, Q, ite_smul]

end perm

section order

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end order

end GlobalTheory.CompanionTheory.HolCoef.CapLW
end
end
