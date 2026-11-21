import Formalism.LocalToGlobal.Divisibility.JetBounds.IsExpansion

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

def EmbLower : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime]
    (ι : K →+* ℂ_[l]), EmbAt w l ι → ∀ (a : K) (s : ℝ), a ≠ 0 → ‖ι a‖ ≤ ‖(l : ℂ_[l])‖ ^ s →
      (ramw w : ℝ) * s ≤ (vw w a : ℝ)

def EmbInt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime]
    (ι : K →+* ℂ_[l]), EmbAt w l ι → ∀ a : K, (a = 0 ∨ 0 ≤ vw w a) → ‖ι a‖ ≤ 1

def PathBound : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime] (J A B : Type) [Fintype J] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (X : PathData K l J A B) (ι : K →+* ℂ_[l]) (D : ℕ) (j1 : J) (s : J → ℝ) (φ : A) (F : B),
    (∀ π, ‖ι (X.x π φ)‖ ≤ 1) → (∀ π, ‖ι (X.y π F)‖ ≤ 1) → LastInt X → UnitsInt X → StabDvd X D j1 →
    (∀ π j, ‖X.e π j‖ ≤ ‖(l : ℂ_[l])‖ ^ (s j)) →
      ‖X.val ι φ F‖ ≤ ‖(l : ℂ_[l])‖ ^ (∑ j, (s j - (padicValNat l D : ℝ)))

section Final

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df1 : DefSide Bs}

def LocalValuationBoundAt (Dc : DefCols Df1) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt t, Dc.Pt u t φ F = 0 ∨ sgw ≤ (vw w (Dc.Pt u t φ F) : ℝ)

end Final

end Formalism.L2.DIV
