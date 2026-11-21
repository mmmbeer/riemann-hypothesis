import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness

section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp

section LeftTranslation

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]





end LeftTranslation

end GlobalTheory.CompanionTheory.WaveCp
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.RepUnique


end GlobalTheory.CompanionTheory.WaveCp.RepUnique
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.SqInt

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end GlobalTheory.CompanionTheory.WaveCp.SqInt
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Calculus

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]








end Calculus

def co (p : Bool × Fin n × Fin n) : Mat n →L[ℝ] ℝ :=
  (if p.1 then Complex.reCLM else Complex.imCLM).comp
    (LinearMap.toContinuousLinearMap
      ((Matrix.entryLinearMap ℝ ℂ p.2.1 p.2.2 : Mat n →ₗ[ℝ] ℂ)))


section Conv

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

def cvl (φ : Mat n → ℂ) (y : Lp V 2 μ) : Mat n → V :=
  fun x => ∫ z : G n, φ (x * (z⁻¹ : G n).val) • (y : G n → V) z ∂μ

end Conv

section Classes

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] {μ : Measure (G n)}





end Classes


end GlobalTheory.CompanionTheory.WaveCp.Rep
end
end
