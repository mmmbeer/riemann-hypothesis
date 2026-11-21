import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerRealPlaces.RealZetaIntegralGL2
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding

noncomputable section
open MeasureTheory Matrix Complex
open Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR

namespace GlobalTheory.CompanionTheory.GL2LocalData.RD

open GlobalTheory.CompanionTheory.TateR in

def negE : (ℝˣ × ℝˣ × ℝ) ≃ᵐ (ℝˣ × ℝˣ × ℝ) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.mulRight (-1 : ℝˣ)) (MeasurableEquiv.refl _)

def Jv (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![-y 1, y 0]

def sq (y : Fin 2 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2

def cols (a b : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a 0, b 0; a 1, b 1]

def fr (y : Fin 2 → ℝ) (D ρ : ℝ) : M22 := Matrix.of.symm (cols y ((D / sq y) • Jv y + ρ • y))

end GlobalTheory.CompanionTheory.GL2LocalData.RD
