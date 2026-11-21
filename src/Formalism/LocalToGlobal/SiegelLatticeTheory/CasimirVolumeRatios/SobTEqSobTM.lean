import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeDeepQ

noncomputable section

namespace Formalism.L2.S.S7.DeepK

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal NNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.BridgeDeepQ
open Formalism.HermitianLatticeCounting.S7 (P0 b1 beP)

variable (X : CData)

abbrev dimG : ℕ := X.I.n ^ 2 * X.I.f

def hsInner (A B : Matrix (Fin X.I.n) (Fin X.I.n) ℂ) : ℝ := (Matrix.trace (A * Bᴴ)).re

def IsFrame (pl : Fin (dimG X) → InfinitePlace X.I.F) (E : Fin (dimG X) → Matrix (Fin X.I.n) (Fin X.I.n) ℂ) : Prop :=
  (∀ j, Formalism.REAL.inG (X.I.ε (pl j)) (E j)) ∧
    (∀ j k, pl j = pl k → hsInner X (E j) (E k) = if j = k then 1 else 0) ∧
    ∀ v A, Formalism.REAL.inG (X.I.ε v) A → A ∈ Submodule.span ℝ (E '' {j | pl j = v})

def thetaP (c : Fin (dimG X) → ℝ → X.I.Ginf) (t : Fin (dimG X) → ℝ) : ℕ → X.I.Ginf
  | 0 => 1
  | m + 1 => thetaP c t m * (if h : m < dimG X then c ⟨m, h⟩ (t ⟨m, h⟩) else 1)

def theta (c : Fin (dimG X) → ℝ → X.I.Ginf) (t : Fin (dimG X) → ℝ) : X.I.Ginf := thetaP X c t (dimG X)

end Formalism.L2.S.S7.DeepK

end
