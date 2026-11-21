import Mathlib
import Formalism.QuotientMetricDivisors.BoundsChain
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.QuotientMetricDivisors.RatHermLcvTwist

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def PrimeSumSq : Prop :=
  (∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
    ∑ p ∈ s, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 999 / 1000) ∧
  Summable (fun p : Nat.Primes => 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) ∧
  ∑' p : Nat.Primes, 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 < 1

def PlaceSumNat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w (n : K) : ℝ)).Finite ∧
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (n : K) : ℝ) = Real.log (n : ℝ) ∧
    ∀ S : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ S, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ)

def UntwistedChoice : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S Tw : Finset Pl) (D : ℕ), 0 < D → Tw ⊆ S →
    ∀ (l ell : Pl → ℝ) (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w ∈ S, w ∉ Tw → ∀ j, I w j + Ic w j + jT w j = 0) →
    (∀ w ∈ S, w ∉ Tw → ∀ j, F w j = 0) →
    (∀ w ∈ Tw, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ Tw, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    ∃ err' Jx' η' : Pl → J → ℝ,
      (∀ w ∈ Tw, ∀ j, err' w j = err w j ∧ Jx' w j = Jx w j ∧ η' w j = η w j) ∧
      (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err' w j) + 2 / ell w ^ 2) * D) ∧
      (∀ w ∈ S, ∀ j, jT w j ≤ Jx' w j * D + η' w j) ∧
      (∀ j, ∑ w ∈ S, l w * (err' w j + Jx' w j) = ∑ w ∈ Tw, l w * (err w j + Jx w j)) ∧
      (∀ j, ∑ w ∈ S, l w * η' w j / D = ∑ w ∈ Tw, l w * η w j / D) ∧
      (∀ j, ∑ w ∈ S, l w * F w j = ∑ w ∈ Tw, l w * F w j)

end Formalism.DivisionValues
