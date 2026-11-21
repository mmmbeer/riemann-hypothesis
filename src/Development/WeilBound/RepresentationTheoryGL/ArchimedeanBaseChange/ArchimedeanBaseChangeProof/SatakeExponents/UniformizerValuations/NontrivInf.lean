import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.InertDeltaFirstCaseEqPower

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FBL

def MuInert : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (w : Pl E), ¬ IsSplitAt w →
  ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (φ : GLw a w × GLw b w → ℂ), Match n a b w 1 f φ → Match n a b w μ f φ

theorem muInert : MuInert := by
  intro E _ _ _ n a b w hw μ f φ h Q₁ Q₂ h1 h2 h3 h4 h5 h6 h7
  rw [h Q₁ Q₂ h1 h2 h3 h4 h5 h6 h7, PositivityTheory.Rg.Bc.ArchbcB.B.M4.V1.delta_inert w hw μ, PositivityTheory.Rg.Bc.ArchbcB.B.M4.V1.delta_inert w hw 1]

def LpowMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w))
  (g : UL n w → ℂ), IsOpen (K' : Set (UL n w)) → K' ≤ KL n w → IsHecke K' g → ∀ m k : ℕ, U.lpow K' (U.lpow K' g m) k = U.lpow K' g (m * k)

def EllHom : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) [MeasurableSpace (GA E a)]
  [MeasurableSpace (GA E b)] (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (c : ℂ) (φ : GA E a × GA E b → ℂ),
    ellSum2 μ₁ μ₂ (c • φ) = c * ellSum2 μ₁ μ₂ φ

def NontrivInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → Nontrivial (InfinitePlace E)

end PositivityTheory.Rg.BcB.F.FBL

end
