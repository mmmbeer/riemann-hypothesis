import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Base

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def RwLin : Prop :=
  ∀ (n : ℕ) (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ι : Type) [Fintype ι] (L : ι → V →L[ℝ] W) (f : ι → Mat n → V), (∀ i, ContDiffOn ℝ ∞ (f i) (GLs n)) →
    ∀ (w : List (Bool × Fin n × Fin n)), ∀ x ∈ GLs n, Rw w (fun y => ∑ i, L i (f i y)) x = ∑ i, L i (Rw w (f i) x)

end GlobalTheory.CompanionTheory.WaveK.Base
