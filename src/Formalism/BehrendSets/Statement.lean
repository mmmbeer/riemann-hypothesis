import Mathlib

open Finset Real

noncomputable section

namespace Formalism.BehrendSets

abbrev OrdGrp (s : ℕ) : Type :=
  (ZMod (2 ^ (s + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (s + 2)))ˣ)

def frob (s l : ℕ) (hl : Nat.Coprime l (2 ^ (s + 2))) : OrdGrp s :=
  QuotientGroup.mk (ZMod.unitOfCoprime l hl)

def PmOne (M l : ℕ) : Prop := 2 ≤ l ∧ ((l : ℤ) ≡ 1 [ZMOD M] ∨ (l : ℤ) ≡ -1 [ZMOD M])

open Classical in
def SumSq : Prop := ∀ M Y : ℕ, 2 ≤ M →
  ∑ l ∈ (range Y).filter (PmOne M), Real.log l / (l : ℝ) ^ 2 ≤ 40 * Real.log M / (M : ℝ) ^ 2

open Classical in
def SumLin : Prop := ∀ M Y : ℕ, 2 ≤ M →
  ∑ l ∈ (range (Y + 1)).filter (PmOne M), Real.log l / (l : ℝ) ≤ 8 * (1 + Real.log Y) ^ 2 / (M : ℝ)

open Classical in

def ShortOrdSq : Prop := ∀ (s Lw Y : ℕ), 1 ≤ Lw → 8 * Lw ≤ 2 ^ s →
  ∑ l ∈ (range Y).filter
      (fun l => 2 ≤ l ∧ ∃ hl : Nat.Coprime l (2 ^ (s + 2)), orderOf (frob s l hl) ≤ 4 * Lw),
    Real.log l / (l : ℝ) ^ 2 ≤ 80 * (Lw : ℝ) ^ 2 * Real.log ((2 : ℝ) ^ s) / ((2 : ℝ) ^ s) ^ 2

open Classical in

def ShortOrdLin : Prop := ∀ (s Y : ℕ) (B : ℝ), 0 ≤ B →
  ∑ l ∈ (range (Y + 1)).filter
      (fun l => 2 ≤ l ∧ ∃ hl : Nat.Coprime l (2 ^ (s + 2)), ((orderOf (frob s l hl) : ℕ) : ℝ) < B),
    Real.log l / (l : ℝ) ≤ 2 * B * (1 + Real.log Y) ^ 2 / (2 : ℝ) ^ s

def BehrendFree (K : ℕ) (T : Finset ℕ) : Prop :=
  ∀ α β γ : ℤ, α ≠ 0 → β ≠ 0 → γ ≠ 0 → α + β + γ = 0 →
    |α| ≤ (K : ℤ) → |β| ≤ (K : ℤ) → |γ| ≤ (K : ℤ) →
    ∀ x₁ ∈ T, ∀ x₂ ∈ T, ∀ x₃ ∈ T,
      α * (x₁ : ℤ) + β * (x₂ : ℤ) + γ * (x₃ : ℤ) = 0 → x₁ = x₂ ∧ x₂ = x₃

def thick (n : ℕ) (T : Finset ℕ) (u : ZMod n) : Finset (ZMod n) :=
  T.image (fun t : ℕ => ((t : ℕ) : ZMod n) + u)

open Classical in
def WindowTwo : Prop := ∀ (n L : ℕ) [NeZero n] (T : Finset ℕ),
  (∀ t ∈ T, 8 * L * t < n) → BehrendFree (2 * L) T →
  ∀ h u t₀ : ZMod n, 2 * L < addOrderOf h → ∀ j : ℤ,
    ((Finset.Ico j (j + 2 * (L : ℤ))).filter (fun i : ℤ => t₀ + i • h ∈ thick n T u)).card ≤ 2

open Classical in
def TranslateMean : Prop := ∀ (n : ℕ) [NeZero n] (T : Finset ℕ), (∀ t ∈ T, t < n) →
  ∀ {ι : Type} (I : Finset ι) (pos : ι → ZMod n),
    ∑ u : ZMod n, (I.filter (fun i => pos i ∈ thick n T u)).card = I.card * T.card

def wt {α : Type} [DecidableEq α] (X : Finset α) (δ : ℝ) (T : Finset α) : ℝ :=
  δ ^ T.card * (1 - δ) ^ (X \ T).card

open Classical in
def prob {α : Type} [DecidableEq α] (X : Finset α) (δ : ℝ) (P : Finset α → Prop) : ℝ :=
  ∑ T ∈ X.powerset.filter P, wt X δ T

def expect {α : Type} [DecidableEq α] (X : Finset α) (δ : ℝ) (Y : Finset α → ℝ) : ℝ :=
  ∑ T ∈ X.powerset, wt X δ T * Y T

def Select : Prop := ∀ {α : Type} [DecidableEq α] (X : Finset α) (δ lam : ℝ) (Y : Finset α → ℝ),
  0 ≤ δ → δ ≤ 1 → (∀ T, 0 ≤ Y T) → 0 < lam → 2 * (X.card : ℝ) * δ * (1 - δ) < lam ^ 2 →
  ∃ T ⊆ X, |(T.card : ℝ) - δ * X.card| ≤ lam ∧ Y T ≤ 2 * expect X δ Y

def orbitWindows (n : ℕ) (h t₀ : ZMod n) (L : ℕ) : Finset (Finset (ZMod n)) :=
  (range (addOrderOf h)).image (fun j => (range L).image (fun i => t₀ + (j + i) • h))

open Classical in

def BadMean : Prop := ∀ {α : Type} [DecidableEq α] {ι : Type} (X : Finset α) (δ : ℝ) (L K : ℕ)
  (I : Finset ι) (pt : ι → α) (c : ι → ℝ) (𝒲 : ι → Finset (Finset α)),
  0 ≤ δ → δ ≤ 1 → (L : ℝ) * δ ≤ 1 → (∀ i, 0 ≤ c i) → (∀ i, ∀ W ∈ 𝒲 i, W.card ≤ L) →
  expect X δ (fun T => ∑ i ∈ I,
      c i * (if pt i ∈ T ∧ ∃ W ∈ 𝒲 i, K + 1 ≤ (T ∩ W).card then 1 else 0))
    ≤ ∑ i ∈ I, c i * (δ * (𝒲 i).card * ((L : ℝ) * δ) ^ K)

end Formalism.BehrendSets
