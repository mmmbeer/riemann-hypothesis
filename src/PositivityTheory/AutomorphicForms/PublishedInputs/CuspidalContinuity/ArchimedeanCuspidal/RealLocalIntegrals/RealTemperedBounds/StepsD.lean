import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.CrdTemperate

noncomputable section

open MeasureTheory Matrix LineDeriv

namespace Ad3.LR

def rpol (a b : Fin 2) (h : M22) : M22 := fun r c => if r = b then h a c else 0

def w0 (k : ℕ) (h : M22) : ℂ :=
  Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

def Lop (a b : Fin 2) (w : M22 → ℂ) (h : M22) : ℂ :=
  -(fderiv ℝ w h (rpol a b h)) - 2 * (if a = b then w h else 0)

def Lt (v : ℂ) (a b : Fin 2) (w : M22 → ℂ) (h : M22) : ℂ := (if a = b then v * w h else 0) + Lop a b w h

def DInt2 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (v v' : ℂ) (a b c d : Fin 2) (Φ : Sw) (g : GL (Fin 3) ℝ),
  Integrable (fun h : M22 => Lt v a b (Lt v' c d (w0 k)) h * inn Φ g (Matrix.of h))

def DNull : Prop := volume {h : M22 | (Matrix.of h).det = 0} = 0

end Ad3.LR
