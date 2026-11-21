import Formalism.SizeWindowBrackets.GaloisToProductIsIso
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.SecondKindBucket
import Formalism.SizeWindowBrackets.SlopeExcessBoundExponentZero
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.CosetIndexLemmas

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def gI (h : H) (i : ℕ) : E0 × H := (if Odd i then ((1, 1) : E0) else ((1, 0) : E0), i • h)

end

def hAt (e d : ℕ) (hd : d.Coprime (2 ^ (e + 2))) : HA e :=
  Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitOfCoprime d hd))

def delta1 (x ε : ℝ) : ℝ := x ^ (-(ε / 8))

def bracketSizeWindowBrackets (c C ε x : ℝ) (n nT2 m : ℕ) (k : ℝ) : ℝ :=
  x ^ (C * ε) * (c * x / m + c * x * m / k + 4 * m * x ^ ε / delta1 x ε
      + 2 * k * ((nT2 : ℝ) / n) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2))
    + 2 * x ^ ((1 : ℝ) / 2 + ε) + 2 / x

def GrowthBracketBoundOfSizeWindows : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err → aE ≤ x * b →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    ((nT2 : ℝ) / n) / 2 * Gx ≤ bracketSizeWindowBrackets 1 C ε x n nT2 m k

def RoundingRd : Prop :=
  ∀ (ι : Type) (W : Finset ι) (pr : ι → ℕ) (l sg sg' : ι → ℝ) (R : Finset ℕ) (X'' : ℝ) (g₁ g₂ T : ℕ),
    (∀ w ∈ W, 0 ≤ l w) → (∀ p ∈ R, ∑ w ∈ W.filter (fun w => pr w = p), l w = Real.log p) →
    (∀ w ∈ W, sg w - sg' w ≤ 1) → (∀ w ∈ W, pr w ∉ R → sg w - sg' w ≤ 0) →
    (∀ p ∈ R, p.Prime ∧ ((p : ℝ) ≤ X'' ∨ p = g₁ ∨ p = g₂ ∨ p = T)) → 0 ≤ X'' →
    Real.log g₁ ≤ X'' → Real.log g₂ ≤ X'' → Real.log T ≤ X'' →
    ∑ w ∈ W, 2 * l w * (sg w - sg' w) ≤ (2 * Real.log 4 + 6) * X''

open Formalism.LFunctionChainParameters.WeightedMeanLemmas in

def LatticeSlopeSpread (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE lT : ι → ℝ) (Sg0 c nT a La mk mB0 sa lk : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    0 ≤ c → 0 ≤ nT * a → 0 ≤ La → 0 ≤ mk → 0 ≤ mB0 →
    (∀ u, muMaxM u ≤ c * (nT * a) * La) → (∀ u, -(c * (nT * a) * La * (1 + mk)) ≤ muM u) →
    (∀ u u', |(h u + sa * lT u) - (h u' + sa * lT u')| ≤ c * (nT * a * La + mB0)) →
    (∀ u u', |lT u - lT u'| ≤ c * lk) → lk ≤ La → 0 ≤ sa → sa ≤ 2 * (nT * a) → (∀ u, dr u ≤ c * mB0) →
    uF d muMaxN muN h ≤ 5 * c * (nT * a) * La * (1 + mk) + 2 * c * mB0 + wmean d BE

open Formalism.LFunctionChainParameters.PhiMonotonicityLemmas in

def SpreadCorollaryConclusion : Prop :=
  ∀ s mu logI k del u cU nT a La m mB0 Loss HH η e b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH →
    HH ≤ x ^ c * b → 0 ≤ u → a = x * b → 1 ≤ nT → 1 ≤ La → 0 ≤ mB0 → 0 ≤ Loss → 0 ≤ cU → 0 ≤ m → m ≤ k → 0 < k →
    u ≤ cU * (nT * a * La * (1 + m / k) + mB0 + Loss) → del ≤ 1 / 7 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → logI ≤ k → k ≤ b →
    ConclF s mu logI del u HH η e →
    s ≤ mu + (5 * (c + 1) * (2 * cU + 1) + 2) * Real.log x * (nT * a * La + mB0 + Loss) + 7 * b

def SgWindowEv : Prop :=
  ∀ ε cH C1 e : ℝ, 0 < ε → 0 ≤ C1 → ∃ x₀ : ℝ, ∀ x f m T de e0 : ℝ, x₀ ≤ x → f ≤ x ^ e → 1 ≤ m → 0 < T →
    m * x ^ ε / 2 ≤ Real.log T → de ≤ 2 * f / T → Real.sqrt e0 ≤ Real.exp (-(x ^ (ε / 8))) →
    C1 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ x ^ (-cH)

def DelEv : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x del : ℝ, x₀ ≤ x → del ≤ Real.exp (-(x ^ (ε / 7))) → del ≤ 1 / 7

def RoundWindowEv : Prop :=
  ∀ ε c : ℝ, 0 < ε → 0 ≤ c → ∃ x₀ : ℝ, ∀ x m n : ℝ, x₀ ≤ x → m ≤ x ^ ((1 : ℝ) / 2 + ε / 2) → 1 ≤ n →
    c * m * x ^ ε ≤ Formalism.LFunctionChainParameters.LErr.XppTx x ε n

end Formalism.LFunctionChainParameters.CosetIndexLemmas
