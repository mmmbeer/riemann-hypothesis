import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

namespace UpperTheory.ConvolutionTheory.Dr

structure Carries {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n) (V : Submodule ℂ (LL μ)) : Prop where
  summand : IsSummand μ V
  carrier_eq : Fb.carrier π = formsIn μ V

def ExCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∃! π : TR.CuspSub E n, Carries μ π V

end UpperTheory.ConvolutionTheory.Dr

end
