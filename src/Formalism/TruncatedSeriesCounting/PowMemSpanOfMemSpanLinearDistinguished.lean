import Mathlib
import Formalism.GaussValuationBounds.Statement

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open PowerSeries

def PowMemSpanOfMemSpanLinearDistinguished : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime] (ε u p₂ : PowerSeries O) (w B η c : ℕ),
    p₂ ∈ Ideal.span {PowerSeries.C (ℓ : O), (Formalism.WindowSums.p1 ℓ ε u) ^ ℓ} →
    (c : ℝ) ≤ (w : ℝ) - (B : ℝ) / (ℓ : ℝ) - (η : ℝ) / (ℓ : ℝ) ^ 2 →
    p₂ ^ w ∈ Ideal.span {PowerSeries.C ((ℓ : O) ^ c),
      (Formalism.WindowSums.p1 ℓ ε u) ^ B * (PowerSeries.X : PowerSeries O) ^ η}

def KapWin : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell K D : ℕ) (a : Fin K → ℤ) (L : Fin K → ℕ) (JJ : Finset ℤ),
      JJ ⊆ Finset.univ.biUnion (fun k => Finset.Ico (a k) (a k + (L k : ℤ))) →
      (∀ i ∈ JJ, |i| ≤ (D : ℤ)) →
      (Formalism.WindowSums.PP ℓ χ ell JJ).eval 1 ≠ 0 ∧
      (PadicInt.valuation ((Formalism.WindowSums.PP ℓ χ ell JJ).eval 1) : ℝ) ≤
        (ell : ℝ) + ((∑ k, L k : ℕ) : ℝ) * (1 + ell) +
          ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)

def ColTwoStep : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z I : Submodule O M) (s s₀ : Finset M),
    I ≤ Z → s.card ≤ g → s₀.card ≤ g₀ → (↑s₀ : Set M) ⊆ Z →
    Submodule.span O (s : Set M) ⊔ I = Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g * e + g₀ * e' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

def Clusters {n : ℕ} (j : ℕ) (thick : ZMod n → Prop) : Prop :=
  ∀ t, thick t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (t - k)) ∨
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ thick (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ thick (t - k))

def CutsExist : Prop :=
  ∀ (n j : ℕ) [NeZero n] (thick : ZMod n → Prop) [DecidablePred thick],
    1 ≤ j → j + 1 ≤ n → Clusters j thick →
    ∃ (m : ℕ) (c : ℕ → ℤ), 1 ≤ m ∧ c m = c 0 + n ∧
      ∀ k < m,
        (∀ i : ℕ, 1 ≤ i → i ≤ j → ¬ thick ((c k + i : ℤ) : ZMod n)) ∧
        (j : ℤ) ≤ c (k + 1) - c k ∧ c (k + 1) - c k ≤ 3 * j + 1 ∧
        ((Finset.Ioc (c k) (c (k + 1))).filter (fun i : ℤ => thick (i : ZMod n))).card ≤ 2

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
