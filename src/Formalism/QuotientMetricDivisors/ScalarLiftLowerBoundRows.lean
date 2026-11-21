import Mathlib
import Formalism.QuotientMetricDivisors.Statement
import Formalism.LogFactorialIndices.StatementSize

open Finset NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

def LPrimeBound : Prop :=
  ∀ (x L b a rd La g nV L' Cg Cn : ℝ),
    1 ≤ x → 0 ≤ L → b = Real.exp L → a = x * b → 1 ≤ rd → La = Real.log (a * rd) →
    0 < g → Real.log g ≤ Cg * L → 0 < nV → Real.log nV ≤ Cn * Real.log x → 0 ≤ Cg → 0 ≤ Cn →
    L' = Real.log (b * rd * g * nV) →
      L' ≤ (1 + Cg + Cn) * La ∧ L ≤ La

def ScalarLiftLowerBoundRows : Prop :=
  ∀ (J Pl Emb Frm : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Frm]
    [Nonempty Frm] (n : ℕ)
    (loglam : J → Frm → Emb → ℝ) (Hp Hm : J → Pl → ℕ) (r : J → Pl → Fin n → ℕ)
    (c' : J → Pl → Fin n → ℝ) (w : J → Pl → ℝ)
    (mlam f m nV N L' La A Sc cs C1 C2 : ℝ),

    (∀ j π s, (∑ ρ, Real.log ((Hp j ρ : ℝ) * (Hm j ρ : ℝ))) - C1 * f * nV ^ 2 * L' ≤ loglam j π s) →
    (∀ j ρ, 0 < Hp j ρ) → (∀ j ρ, 0 < Hm j ρ) →
    0 ≤ nV → nV ≤ N → L' ≤ C2 * La → 0 ≤ La → 0 ≤ f → 0 ≤ C1 → 0 ≤ C2 →
    (Fintype.card J : ℝ) = m →
    mlam = (∑ s, Finset.univ.inf' Finset.univ_nonempty (fun π : Frm => ∑ j, loglam j π s)) /
      (Fintype.card Emb : ℝ) →

    (∀ j ρ, (∑ i, Real.log ((r j ρ i).factorial : ℝ)) ≤ Real.log (Hp j ρ : ℝ)) →

    (∀ j ρ i, 1 ≤ w j ρ + c' j ρ i - cs * N ∧ w j ρ + c' j ρ i - cs * N ≤ (r j ρ i : ℝ) ∧
      c' j ρ i ≤ Sc) →
    (∀ j ρ, w j ρ + Sc ≤ A) → La = Real.log A → (n : ℝ) ≤ N → (Fintype.card Pl : ℝ) ≤ f → 0 ≤ cs →
      (∑ j, ∑ ρ, ∑ i, (Formalism.LatticeIndexTer.ph (w j ρ + c' j ρ i) + 1)) -
        (C1 * C2 + cs) * m * f * N ^ 2 * La ≤ mlam

def PrimeLogSum : Prop :=
  ∀ (Y : ℝ), 1 ≤ Y → ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y + Real.log 4

end Formalism.DivisionValues
