import Formalism.SizeWindowBrackets.RealSlopeBoundsSplit
import Formalism.RankGapBounds.MeanBoundSecondForm

open Real

namespace Formalism.LFunctionChainParameters.PhiMonotonicityLemmas

noncomputable section

def phi (H u : ℝ) : ℝ := u * Real.log (1 + H / u)

def ErrF (del u HH η e : ℝ) : ℝ :=
  (1 - del)⁻¹ * (4 * phi HH u + (η + 4 * Real.sqrt e) * HH)

def ConclF (s mu logI del u HH η e : ℝ) : Prop :=
  s - logI - ErrF del u HH η e ≤ mu

def CorFinalModel : Prop :=
  ∃ s mu logI del u U HH η e e0 de C1 b x c : ℝ, 2 ≤ x ∧ 0 ≤ c ∧ 0 < b ∧ 0 < HH ∧
    HH ≤ x ^ c * b ∧ 0 < u ∧ u ≤ U ∧ 0 < del ∧ del ≤ 1 / 7 ∧ 0 < de ∧ 0 < e0 ∧ 0 < C1 ∧
    x ^ (-c) ≤ 1 / 20 ∧ η = 5 * x ^ (-c) + C1 * Real.sqrt de ∧ e = 2 * e0 ∧ e ≤ 1 / 4 ∧
    C1 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ x ^ (-c) ∧ 0 ≤ logI ∧ s - mu ≤ HH ∧
    s - logI - ErrF del u HH η e = mu

def SlopeExcessBoundExponentZero : Prop :=
  ∀ s mu W HH b x C : ℝ, 2 ≤ x → 0 < b → 0 ≤ W → 0 ≤ C → HH ≤ x ^ (0 : ℝ) * b → s - mu ≤ HH →
    s ≤ mu + C * Real.log x * W + 7 * b

open Formalism.LFunctionChainParameters.WeightedMeanLemmas in

def CorFamily (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 A A' V mu del HH η e b x c : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → (∀ u, muN u ≤ muMaxN u) →
    Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    (∀ u, muMaxM u ≤ A) → (∀ u, -A' ≤ muM u) → (∀ u u', |h u - h u'| ≤ V) →
    2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH → HH ≤ x ^ c * b → del ≤ 1 / 7 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b →
    ConclF (sF d muN h) mu (Real.log (Fintype.card ι : ℝ)) del (uF d muMaxN muN h) HH η e →
    sF d muN h ≤ mu + Real.log (Fintype.card ι : ℝ)
      + 5 * (c + 1) * Real.log x * (A + A' + V + wmean d (fun u => dr u + BE u) + b) + 7 * b

section SizeData₂

open Formalism.RankGapBounds.WeightedMeanData

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

end SizeData₂

end

end Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
