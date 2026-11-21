import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped FourierTransform

namespace Ad3.LR.C

def cr (e : Bool) (s : ℂ) (r : ℝ) : ℂ := (if e ∧ r < 0 then -1 else 1) * ((|r| : ℝ) : ℂ) ^ s

def ge (ε u : ℝ) : ℝ := Real.exp (-Real.pi * ε ^ 2 * u ^ 2)

def Ae (Φ : Sw) (ε : ℝ) (h : M22) (v : ℝ) : ℂ :=
  ∫ z : Fin 2 → ℝ, Φ (Matrix.of.symm (Matrix.of h * blk z)) * psiR (-(z 1)) * ge ε (z 0 - v)

def Dk (N : ℕ) (h : M22) : ℝ :=
  (max |(Matrix.of h).det| (|h 0 0 * h 0 1 + h 1 0 * h 1 1| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2)))⁻¹ / (1 + ‖h‖) ^ N

def UnipotentJointIntegrability : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 → ∀ u : ℝ,
  Integrable (fun p : ℝˣ × M22 => chR δ s p.1 * sg p.1 * (((|(p.1 : ℝ)|)⁻¹ : ℝ) : ℂ) *
    (Wm k (Matrix.of p.2)⁻¹ * sg (Matrix.of p.2).det * ((|(Matrix.of p.2).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      B.innB (B.rt (cyc u) Φ) p.2 (p.1 : ℝ)⁻¹)) (mulR.prod volume)

def TateFunctionalEquationComplex : Prop := ∀ (f : ℝ → ℂ) (e : Bool) (s : ℂ), 0 < s.re → s.re < 1 → Integrable f →
  Integrable (fun w => f w * ((|w| ^ (s.re - 1) : ℝ) : ℂ)) → Integrable (fun r => 𝓕 f r * ((|r| ^ (-s.re) : ℝ) : ℂ)) →
  z1 (𝓕 f) e (1 - s) = gT e s * z1 f e s

def UnipotentTateFunctionalEquation : Prop := ∀ (Ψ : M23 → ℂ) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 → ContDiff ℝ (⊤ : ℕ∞) Ψ →
  (∀ n : ℕ, ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m Ψ X‖ ≤ C) →
  ∀ h : M22, (Matrix.of h).det ≠ 0 →
    ∫ t : ℝˣ, chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) * B.innB Ψ h (t : ℝ)⁻¹ ∂mulR =
      cr (!δ) 0 (-1) * gT (!δ) s * ∫ x : Fin 2 → ℝ, cr (!δ) (s - 1) (x 1) * Ψ (Matrix.of.symm (Matrix.of h * blk x))

def ParsB : Prop := ∀ (Φ : Sw) (N : ℕ), ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (h : M22) (v : ℝ),
  (Matrix.of h).det ≠ 0 → ‖Ae Φ ε h v‖ ≤ C * Dk N h

end Ad3.LR.C
