import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR

abbrev M23 : Type := Fin 2 → Fin 3 → ℝ
abbrev M22 : Type := Fin 2 → Fin 2 → ℝ

abbrev Sw : Type := SchwartzMap M23 ℂ

def sg (t : ℝ) : ℂ := if t < 0 then -1 else 1

def Wm (k : ℕ) (h : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  if 0 < h.det then
    ((h.det ^ ((2 * (k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((h 1 1 : ℂ) - (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
      Complex.exp (-2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) - (h 0 0 : ℂ) * Complex.I) / ((h 1 1 : ℂ) - (h 1 0 : ℂ) * Complex.I)))
  else 0

def blk (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, x 0; 0, 1, x 1]

def inn (Φ : Sw) (g : GL (Fin 3) ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∫ x : Fin 2 → ℝ, Φ (Matrix.of.symm (h * blk x * (g : Matrix (Fin 3) (Fin 3) ℝ))) * psiR (-(x 1))

def sec (k : ℕ) (Φ : Sw) (g : GL (Fin 3) ℝ) : ℂ :=
  sg (g : Matrix (Fin 3) (Fin 3) ℝ).det * ((|(g : Matrix (Fin 3) (Fin 3) ℝ).det| : ℝ) : ℂ) *
    ∫ h : M22, Wm k (Matrix.of h)⁻¹ * inn Φ g (Matrix.of h) * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

def StLin : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ Ψ : Sw) (c : ℂ),
  sec k (Φ + Ψ) = sec k Φ + sec k Ψ ∧ sec k (c • Φ) = c • sec k Φ

def StStable : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (h : GL (Fin 3) ℝ),
  ∃ Φ' : Sw, (fun g => sec k Φ (g * h)) = sec k Φ'

def StSmooth : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Φ : Sw, SmoothR (sec k Φ)

end Ad3.LR
