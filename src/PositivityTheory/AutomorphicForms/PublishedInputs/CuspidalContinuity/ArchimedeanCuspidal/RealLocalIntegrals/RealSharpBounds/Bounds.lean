import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.B

def eta (h : M22) : Fin 2 → ℝ := fun j => (Matrix.of h)⁻¹ 1 j

def innB (Ψ : M23 → ℂ) (h : M22) (β : ℝ) : ℂ :=
  ∫ x : Fin 2 → ℝ, Ψ (Matrix.of.symm (Matrix.of h * blk x)) * psiR (-(β * x 1))

def rt (g : GL (Fin 3) ℝ) (Ψ : M23 → ℂ) (X : M23) : ℂ :=
  Ψ (Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ)))

def maj (k N : ℕ) (a b : ℝ) (h : M22) : ℝ :=
  ‖Wm k (Matrix.diagonal ![a, 1] * (Matrix.of h)⁻¹)‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) /
    ((1 + ‖h‖) ^ N * (1 + |b| * ‖eta h‖) ^ N)

def IbpBound : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ (Ψ : M23 → ℂ) (B : ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
  (∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n Ψ X‖ ≤ B) →
  ∀ (h : M22) (β : ℝ), (Matrix.of h).det ≠ 0 →
    ‖innB Ψ h β‖ ≤ C * B * |(Matrix.of h).det|⁻¹ / ((1 + ‖h‖) ^ N * (1 + |β| * ‖eta h‖) ^ N)

def MajScaled : Prop := ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ C : ℝ, ∀ (a b : ℝ), a ≠ 0 → b ≠ 0 →
  Integrable (maj k N a b) ∧ ∫ h, maj k N a b h ≤ C * |a| ^ (1 / 2 : ℝ) * |a * b| ^ (-ε)

end Ad3.LR.B
