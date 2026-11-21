import Mathlib
import Formalism.MeanHeightDescent.CombinedAverageDegreeBound

open Finset

noncomputable section

namespace Formalism.HermiteSiegelSlopes

def MonomialMean : Prop :=
  ∀ (D a : ℕ) (i : Fin D), 1 ≤ D →
    Fintype.card (Sym (Fin D) a) = (a + D - 1).choose (D - 1) ∧
    D * ∑ α : Sym (Fin D) a, Multiset.count i (α : Multiset (Fin D))
      = a * (a + D - 1).choose (D - 1)

def HSClaim : Prop :=
  ∀ (D T : ℕ) (δ d h J g lamb η lρ1 lρ lβ lΛD lΛT C0 rkP cor degP degQ degMT : ℝ)
    (lA degGr : ℕ → ℝ),
    1 ≤ D → D + 1 ≤ T → 0 < δ → 0 < d → 0 ≤ g → 0 ≤ lβ → 0 ≤ lΛD → 0 ≤ lΛT → 4 ≤ C0 →

    0 ≤ lρ1 → lρ1 ≤ lρ → Real.log D ≤ lρ → 26 * Real.log 2 ≤ lρ → lamb ≤ lρ1 →
    ((D : ℝ) + 1) * h + D * lamb - g ≤ η → η ≤ ((D : ℝ) + 1) * h + D * lamb →

    (∀ a < T - D, lA a ≤ ((T : ℝ) + D + 1) / 2 * lβ
        + Real.log (34 * (2 ^ (D + 1) * Real.pi ^ D / ((D - 1).factorial : ℝ))
            * ((a + D - 1).choose (D - 1) : ℝ)) / 2
        + D * (Real.log D / 2 + lρ1)) →
    (∀ a < T - D, ((a + D - 1).choose (D - 1) : ℝ) * δ *
        (-J + ((T : ℝ) - a - D - 3) * η - a * lamb - lA a) ≤ degGr a) →

    0 ≤ rkP → 0 ≤ cor → rkP + cor = d - ((T - 1).choose D : ℝ) * δ →
    -(rkP * (((T : ℝ) - D) * (lβ / 2 + lρ1) + lΛD)) ≤ degP →
    -(cor * lΛT) ≤ degQ →
    (∑ a ∈ range (T - D), degGr a) + degP + degQ ≤ degMT →
    (1 - (1 - ((T - 1).choose D : ℝ) * δ / d)) *
        ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - C0 * (D : ℝ) ^ 2 * (lρ + Real.log T)
          - ((T : ℝ) + D + 1) * lβ - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2))
      - (1 - ((T - 1).choose D : ℝ) * δ / d) *
        ((T : ℝ) * (Real.log 2 + lρ + lβ / 2) + lΛD + lΛT) ≤ degMT / d

end Formalism.HermiteSiegelSlopes
