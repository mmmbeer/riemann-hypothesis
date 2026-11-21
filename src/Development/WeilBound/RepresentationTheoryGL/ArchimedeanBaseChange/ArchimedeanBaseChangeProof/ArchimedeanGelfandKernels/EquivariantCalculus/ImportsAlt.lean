import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Calc2

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Cf (n : ℕ) := EuclideanSpace ℝ (Bool × Fin n × Fin n)

def crd (v : Cf n) : Mat n := ∑ p, v p • bs p

def ex (v : Cf n) : Mat n := NormedSpace.exp (crd v)

def s2 (n : ℕ) : ℝ := ⨍ v in Metric.ball (0 : Cf n) 1, ‖v‖ ^ 2

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Ld (Y : Mat n) (f : Mat n → V) : Mat n → V := fun g => fderiv ℝ f g (Y * g)

def Lw : List (Bool × Fin n × Fin n) → (Mat n → V) → (Mat n → V)
  | [] => id
  | p :: w => fun f => Ld (bs p) (Lw w f)

def kp (X : Mat n) : Mat n := (1 / 2 : ℂ) • (X - Xᴴ)

end Ops

def cop {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  ∑' j : ℕ, ((t ^ (2 * j) / ((2 * j).factorial : ℝ) : ℝ) : ℂ) • A ^ j

end PositivityTheory.RgBcC.Calc2
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Calc2.L

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Calc2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def co (Y : Mat n) (p : Bool × Fin n × Fin n) : ℝ := if p.1 then (Y p.2.1 p.2.2).re else (Y p.2.1 p.2.2).im

end PositivityTheory.RgBcC.Calc2.L
end
end
