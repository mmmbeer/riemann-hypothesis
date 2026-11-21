import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.GelfandEvenSmoothness.IntSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Mult

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def GelfEven : Prop := ∀ (n : ℕ) (ψ : Fin n → ℂ), GlobalTheory.Dec.gelfVal (-ψ) 2 = GlobalTheory.Dec.gelfVal ψ 2

end PositivityTheory.RgBcC.Mult
