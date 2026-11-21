import Mathlib

namespace Formalism.GM

open Finset Polynomial

noncomputable def gch (x : ℚ) (k : ℕ) : ℚ := (descPochhammer ℚ k).eval x / (k.factorial : ℚ)

def BinomRatio : Prop :=
  ∀ (x : ℚ) (l J : ℕ), l ≤ J → gch x J * gch (J : ℚ) l = gch x l * gch (x - l) (J - l)

def DetBlockLead : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K[X]) (D : ℕ) (e : Fin n → ℕ),
    (∀ i, e i ≤ D) → (∀ i j, (A i j).natDegree + max (e i) (e j) ≤ D) →
      (A.det).natDegree ≤ ∑ i, (D - e i) ∧
      (A.det).coeff (∑ i, (D - e i)) =
        (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ∧
      ((Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ≠ 0 →
        (A.det).natDegree = ∑ i, (D - e i) ∧
        (A.det).leadingCoeff = (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det)

def LegendreDigits : Prop :=
  ∀ (p m : ℕ), p.Prime →
    (m : ℝ) / ((p : ℝ) - 1) - (padicValNat p m.factorial : ℝ) ≤ (Nat.log p m : ℝ) + 1

noncomputable def vmin (p : ℕ) {K : Type} [NormedField K] (h : ℕ) (x : K) : ℝ :=
  -Real.logb p (max ‖x‖ ((p : ℝ) ^ (-(h : ℤ))))

open Classical in

def DiscsDisjoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (t₀ : ℤ) (Y₀ h : ℕ), Y₀ ≤ p ^ h →
    ∑ t ∈ Ico t₀ (t₀ + Y₀), (roots.filter (fun ζ => ‖(t : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card ≤ roots.card

open Classical in

def WindowMean : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (lam La₀ E : ℝ) (n₀ del₀ : ℕ) (t₀ : ℤ) (Y₀ h : ℕ) (β : ℤ → ℕ),
    0 < Y₀ → Y₀ ≤ p ^ h → 0 < E →
    roots.card ≤ del₀ * n₀ →
    lam + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * La₀ →
    (∀ t ∈ Ico t₀ (t₀ + Y₀),
      (β t : ℝ) * E ≤ (lam + (roots.map (fun ζ => vmin p h ((t : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) →
    (∑ t ∈ Ico t₀ (t₀ + Y₀), (β t : ℝ)) / (Y₀ : ℝ) ≤
      (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)

open Classical in

def FrameCount : Prop :=
  ∀ (r Q b : ℕ) (c : ℤ), 2 ≤ r → 0 < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 8 * r * b / Q) ≤
      ((univ.filter (fun e : Fin r → Fin Q =>
        (∀ i, (e i : ℕ) + 4 * b < Q) ∧ (∑ i, ((e i : ℕ) : ℤ)) ≡ c [ZMOD Q])).card : ℝ)

def TrueRing : Prop :=
  ∀ (R : Type) [CommRing R] (r Q : ℕ), 0 < Q →
    Function.Bijective (fun f : (Fin r → Fin Q) → MvPolynomial (Fin r) R =>
      ∑ e, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => ((e i : ℕ)))) (1 : R) *
        MvPolynomial.expand Q (f e))

end Formalism.GM
