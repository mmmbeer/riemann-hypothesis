import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix

namespace Ad3.K.LC

abbrev M23 : Type := Fin 2 → Fin 3 → ℂ
abbrev M22 : Type := Fin 2 → Fin 2 → ℂ

abbrev Sw : Type := SchwartzMap (M23 × (Fin 2 → ℂ)) ℂ

def blk (x : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 3) ℂ := !![1, 0, x 0; 0, 1, x 1]

def rowv (t y : ℂ) (h : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → ℂ := Matrix.vecMul ![t, t * y] h⁻¹

def inn (Ψ : Sw) (g : GL (Fin 3) ℂ) (h : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) : ℂ :=
  ∫ p : (Fin 2 → ℂ) × ℂ, Ψ (Matrix.of.symm (h * blk p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), rowv t p.2 h) *
    psiC (-(p.1 1)) * psiC (-p.2)

def ph (n : ℤ) (z : ℂ) : ℂ := (z / (‖z‖ : ℂ)) ^ n

def sec (k : ℕ) (Ψ : Sw) (g : GL (Fin 3) ℂ) : ℂ :=
  ((‖(g : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) *
    ∫ h : M22, (∫ t : ℂ, inn Ψ g (Matrix.of h) t * ph (4 * (k : ℤ) - 4) t) *
      ph (-(2 * (k : ℤ) - 2)) (Matrix.of h).det * ((‖(Matrix.of h).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)

def StLin : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ Ψ : Sw) (c : ℂ),
  sec k (Φ + Ψ) = sec k Φ + sec k Ψ ∧ sec k (c • Φ) = c • sec k Φ

def StStable : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (h : GL (Fin 3) ℂ),
  ∃ Φ' : Sw, (fun g => sec k Φ (g * h)) = sec k Φ'

def StSmooth : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Φ : Sw, SmoothC (sec k Φ)

end Ad3.K.LC
