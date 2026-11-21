import Mathlib

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Real

def TieBoundN : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (Γ : AddSubgroup V) (x : V),
      (∀ y ∈ Γ, B x x / 2 ≤ B (x + y) (x + y) / 2) →
      ∀ g ∈ Γ, ∀ N : ℕ, 2 ≤ N →
        B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 =
            (N : ℝ) * B x g + (N : ℝ) ^ 2 * (B g g / 2) ∧
        (N : ℝ) * ((N : ℝ) - 1) * (B g g / 2) ≤
            B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 ∧
        (0 < B g g → B x x / 2 < B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2)

def AlternatingBinomial : Prop :=
  ∀ (σ R : Type) [Fintype σ] [DecidableEq σ] [CommRing R] (a : σ → ℕ) (T : σ → R),
    ∑ e ∈ Fintype.piFinset (fun j => Finset.range (a j + 1)),
        (-1 : R) ^ (∑ j, (a j - e j)) * ((∏ j, (a j).choose (e j) : ℕ) : R) *
          ∏ j, (1 + T j) ^ (e j) =
      ∏ j, T j ^ (a j)

def DetProductRest : Prop :=
  ∀ (i c : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
    ((2 : ℝ) ^ c + ε) ^ i - (2 : ℝ) ^ (c * i) ≤ (i : ℝ) * ε * ((2 : ℝ) ^ c + 1) ^ i

def MinimumChainBounds : Prop :=
  ∀ (dp lmax2 φ RR PP r₁ r E0 minQ δ : ℝ), 0 ≤ dp → 0 ≤ φ → 0 ≤ RR → 1 ≤ r₁ → 0 ≤ r →
    minQ ≤ dp * lmax2 / (4 * r₁ ^ 2) → lmax2 ≤ 2 * RR * dp ^ 2 * φ → E0 ≤ r * minQ →
    r * dp ^ 3 ≤ PP →
    minQ ≤ RR * dp ^ 3 * φ / (2 * r₁ ^ 2) ∧ E0 ≤ r * RR * dp ^ 3 * φ / (2 * r₁ ^ 2) ∧
      E0 ≤ RR * PP * φ ∧
      (φ ≤ r₁ ^ 4 * E0 → φ ≤ 2 * r₁ ^ 4 * E0 / 2) ∧
      (2 * r₁ ^ 4 * r) * δ - 2 * r₁ ^ 4 * E0 = 2 * r₁ ^ 4 * (r * δ - E0)

end Formalism.LatticeBaseChangeAlt
