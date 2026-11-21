import Mathlib

noncomputable section

namespace Formalism.CG

open Finset

def NetExponent : Prop :=
  (∀ k c : ℚ,
    (k + c) ^ 2 - c * (c - 1) / 2 - (c - 1) * k - k * (k - 1) / 2
        = k ^ 2 / 2 + k * c + c ^ 2 / 2 + c / 2 + 3 * k / 2 ∧
    k ^ 2 / 2 + k * c + c ^ 2 / 2 + c / 2 + 3 * k / 2 = (k + c) * (k + c + 1) / 2 + k ∧
    k ^ 2 - k * (k - 1) / 2 = k * (k + 1) / 2) ∧
  (∀ k c p : ℚ, c * (c - 1) / 2 + (c - p) * k + (p - 1) * k = c * (c - 1) / 2 + (c - 1) * k) ∧
  (∀ k m : ℚ,
    ((k + m - 1) * (k + m) - k * (k + 1)) / 2 + k = (2 * k * (m - 1) + m * (m - 1)) / 2 + k ∧
    (2 * k * (m - 1) + m * (m - 1)) / 2 + k = k * m + m * (m - 1) / 2 ∧
    k * m + m * (m - 1) / 2 = m * (2 * k + m - 1) / 2) ∧
  (∀ k c : ℕ, 1 ≤ c →
    (c * (c - 1) / 2 + (c - 1) * k + k * (k - 1) / 2) + ((k + c) * (k + c + 1) / 2 + k)
      = (k + c) ^ 2) ∧
  (∀ k : ℕ, k * (k - 1) / 2 + k * (k + 1) / 2 = k ^ 2)

def NetCardGL : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ),
    Nat.card (GL (Fin n) F)
      = Fintype.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (Fintype.card F ^ i - 1) ∧
    (Nat.card (GL (Fin n) F) : ℝ)
      = (Fintype.card F : ℝ) ^ (n ^ 2) * ∏ i ∈ Icc 1 n, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)

def netHasPattern {F : Type} [Field F] {n : ℕ} (S : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (i, j) ∉ S → A i j = if i = j then 1 else 0

def NetPatternGroup : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (S : Finset (Fin n × Fin n)),
    (∀ x ∈ S, x.1 < x.2) → (∀ i j l, (i, j) ∈ S → (j, l) ∈ S → (i, l) ∈ S) →
    ∃ H : Subgroup (GL (Fin n) F),
      (∀ A : GL (Fin n) F, A ∈ H ↔ netHasPattern S (A : Matrix (Fin n) (Fin n) F)) ∧
      Nat.card H = Fintype.card F ^ S.card

def netFull (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun x => x.1 < x.2

def netPattern (k c p0 : ℕ) : Finset (Fin (k + c) × Fin (k + c)) :=
  univ.filter fun x => x.1 < x.2 ∧ ¬ (p0 ≤ x.1.val ∧ x.2.val = p0 + k)

def NetPatternCard : Prop :=
  (∀ n : ℕ, (netFull n).card = n * (n - 1) / 2 ∧
    ∀ i j l, (i, j) ∈ netFull n → (j, l) ∈ netFull n → (i, l) ∈ netFull n) ∧
  (∀ k c p0 : ℕ, p0 < c →
    (netPattern k c p0).card = c * (c - 1) / 2 + (c - 1) * k + k * (k - 1) / 2 ∧
    ∀ i j l, (i, j) ∈ netPattern k c p0 → (j, l) ∈ netPattern k c p0 → (i, l) ∈ netPattern k c p0)

def NetReturnOfA : Prop :=
  ∀ (ι : Type) [DecidableEq ι] (P TT : Finset ι), TT ⊆ P → ∀ (n a : ι → ℝ) (R1 R2 m k : ℝ),
    1 ≤ m → 0 < k → m - 1 ≤ 2 * k →
    (∀ t ∈ TT, |n t - a t| ≤ R1) → (∀ τ ∈ P \ TT, |n τ| ≤ R2) → 0 ≤ R2 →
    |(∑ τ ∈ P, n τ) * (m * (1 + (m - 1) / (2 * k)))
        - (m * ∑ t ∈ TT, a t + m * (m - 1) / (2 * k) * ∑ t ∈ TT, a t)|
      ≤ 2 * m * ((TT.card : ℝ) * R1 + (P.card : ℝ) * R2)

def NetUnitMean : Prop :=
  ∀ (Λ : Type) [Fintype Λ] (y X : Λ → ℝ) (lg : ℝ), (∀ w w', y w = y w') → ∑ w, y w = lg →
    ∑ w, y w * X w = lg * ((∑ w, X w) / (Fintype.card Λ : ℝ))

def NetBalanceG : Prop :=
  ∀ (J T P : Finset ℕ) (D del : ℝ), 0 < D → 0 < del →
    ∀ (colL colLb : ℝ) (aL aLb Dpi Dp Dm eta etab top : ℕ → ℝ) (k : ℝ) (w e1 e2 : ℕ → ℕ → ℝ)
      (Ecol CA rL rLb Etw : ℝ),
    -(∑ j ∈ J, Dpi j) - Ecol ≤ colL + colLb →
    ∑ j ∈ J, (aL j + aLb j) ≤ ∑ j ∈ J, (-2 * (Dp j + Dm j) * D + eta j + etab j)
        + 2 * (J.card : ℝ) * (CA * D + (rL + rLb) / del) + Etw →
    (∀ j ∈ J, Dpi j ≤ ∑ t ∈ T, top t + ∑ τ ∈ P, (k * w j τ + e1 j τ)) →
    (∀ j ∈ J, ∑ τ ∈ P, ((k - 1) * w j τ - e2 j τ) ≤ Dp j + Dm j) →
    ∀ (n : ℕ → ℝ) (R1 R2 : ℝ), T ⊆ P → 1 ≤ J.card → 0 < k → (J.card : ℝ) - 1 ≤ 2 * k →
    (∀ t ∈ T, |n t - top t| ≤ R1) → (∀ τ ∈ P \ T, |n τ| ≤ R2) → 0 ≤ R2 →
      -(∑ j ∈ J, ∑ τ ∈ P, w j τ)
        + (J.card : ℝ) * ((J.card : ℝ) - 1) / (2 * k) * ∑ t ∈ T, top t
        - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) + ∑ j ∈ J, (eta j + etab j) / (2 * D)
            + Ecol + (J.card : ℝ) * (CA + (rL + rLb) / (del * D)) + Etw / (2 * D)
            + 2 * (J.card : ℝ) * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2))
      ≤ ((2 * colL + 2 * colLb) / 2 - (∑ j ∈ J, (aL j + aLb j) / D) / 2)
        + (∑ τ ∈ P, n τ) * ((J.card : ℝ) * (1 + ((J.card : ℝ) - 1) / (2 * k)))

def NetBalanceMean : Prop :=
  ∀ (Λ : Type) [Fintype Λ] [Nonempty Λ] (c : Λ → Λ), Function.Involutive c →
    ∀ (y : Λ → ℝ) (lg : ℝ), (∀ u u', y u = y u') → ∑ u, y u = lg → 0 ≤ lg →
    ∀ (J T P : Finset ℕ) (D del : ℝ), 0 < D → 0 < del →
    ∀ (col r : Λ → ℝ) (a eta : ℕ → Λ → ℝ) (Dpi Dp Dm top : ℕ → ℝ) (k : ℝ) (w e1 e2 : ℕ → ℕ → ℝ)
      (Ecol CA Etw : ℝ),
    (∀ u, -(∑ j ∈ J, Dpi j) - Ecol ≤ col u + col (c u)) →
    (∀ u, ∑ j ∈ J, (a j u + a j (c u)) ≤
        ∑ j ∈ J, (-2 * (Dp j + Dm j) * D + eta j u + eta j (c u))
        + 2 * (J.card : ℝ) * (CA * D + (r u + r (c u)) / del) + Etw) →
    (∀ j ∈ J, Dpi j ≤ ∑ t ∈ T, top t + ∑ τ ∈ P, (k * w j τ + e1 j τ)) →
    (∀ j ∈ J, ∑ τ ∈ P, ((k - 1) * w j τ - e2 j τ) ≤ Dp j + Dm j) →
    ∀ (n : ℕ → ℝ) (R1 R2 : ℝ), T ⊆ P → 1 ≤ J.card → 0 < k → (J.card : ℝ) - 1 ≤ 2 * k →
    (∀ t ∈ T, |n t - top t| ≤ R1) → (∀ τ ∈ P \ T, |n τ| ≤ R2) → 0 ≤ R2 →
      lg * (-(∑ j ∈ J, ∑ τ ∈ P, w j τ)
        + (J.card : ℝ) * ((J.card : ℝ) - 1) / (2 * k) * ∑ t ∈ T, top t
        - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ)
            + ∑ j ∈ J, ((∑ u, eta j u) / (Fintype.card Λ : ℝ)) / D
            + Ecol
            + (J.card : ℝ) * (CA + ((∑ u, (r u + r (c u))) / (Fintype.card Λ : ℝ)) / (del * D))
            + Etw / (2 * D)
            + 2 * (J.card : ℝ) * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2)))
      ≤ ∑ u, y u * (2 * col u - ∑ j ∈ J, a j u / D)
        + (∑ τ ∈ P, n τ) * ((J.card : ℝ) * (1 + ((J.card : ℝ) - 1) / (2 * k))) * lg

end Formalism.CG
