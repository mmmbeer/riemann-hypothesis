import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerRealPlaces.RealZetaIntegralGL2

noncomputable section

open MeasureTheory Matrix Complex
open Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR

namespace GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst

abbrev Mt : Type := Matrix (Fin 2) (Fin 2) ℝ

abbrev Yc : Type := (Fin 2 → ℝ) × ℝ

def nv (v : Fin 2 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2

def Psi (ε : Bool) (p : ℝˣ × ℝˣ × ℝ) : Yc := ((hIw ε p).val 1, (hIw ε p).val.det)

def sec2 (y : Yc) : Mt :=
  !![y.2 * y.1 1 / nv y.1, -(y.2 * y.1 0) / nv y.1; y.1 0, y.1 1]

def Uf (k : ℕ) (n : ℤ) (s : ℂ) (h g : Mt) : ℂ :=
  ((|h.det| : ℝ) : ℂ) ^ s * Wm k (h * g⁻¹) * phi2h k n ((h * g⁻¹) 1) * WthR n (glOf h) *
    (phi1 n g * sg g.det * ((|g.det| : ℝ) : ℂ) ^ (-(3 / 2) : ℂ))

def Vf (k : ℕ) (n : ℤ) (s : ℂ) (h g : Mt) : ℂ :=
  ((|h.det| : ℝ) : ℂ) ^ s * Wm k h * phi2h k n (h 1) *
    (phi1 n g * sg g.det * ((|g.det| : ℝ) : ℂ) ^ (s - 3 / 2) * WthR n (glOf h * glOf g))

end GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst

end
