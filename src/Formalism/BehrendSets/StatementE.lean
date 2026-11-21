import Formalism.BehrendSets.Statement

open Finset Real

noncomputable section

namespace Formalism.BehrendSets

open Classical in
def OrdSqJ : Prop := ∀ (s J Y : ℕ), 1 ≤ s → 1 ≤ J →
  ∑ l ∈ (range Y).filter
      (fun l => 2 ≤ l ∧ ∃ hl : Nat.Coprime l (2 ^ (s + 2)), orderOf (frob s l hl) ≤ J),
    Real.log l / (l : ℝ) ^ 2 ≤ 10 * (J : ℝ) ^ 2 * Real.log (2 * (2 : ℝ) ^ s) / ((2 : ℝ) ^ s) ^ 2

def SpaceFreePos (Lw : ℕ) (S : Finset ℕ) : Prop :=
  ∀ i j : ℤ, 0 < i → i < j → j ≤ (Lw : ℤ) →
    ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
      j * ((s₂ : ℤ) - (s₁ : ℤ)) ≠ i * ((s₃ : ℤ) - (s₁ : ℤ))

open Classical in
def Spacing : Prop := ∀ (n Lw : ℕ) [NeZero n] (S : Finset ℕ),
  (∀ s ∈ S, 4 * Lw * s < n) → SpaceFreePos Lw S →
  ∀ h u t : ZMod n, Lw < addOrderOf h → ∀ j₀ : ℤ,
    ((Finset.Icc j₀ (j₀ + (Lw : ℤ))).filter (fun i : ℤ => t + i • h ∈ thick n S u)).card ≤ 2

open Classical in
def TopsBadSplit : Prop := ∀ {α : Type} [DecidableEq α] (X : Finset α) (δ : ℝ) (L K : ℕ) (t : α)
  (𝒲 : Finset (Finset α)), 0 ≤ δ → δ ≤ 1 → (∀ W ∈ 𝒲, W.card ≤ L) →
  prob X δ (fun T => t ∈ T ∧ ∃ W ∈ 𝒲, K + 1 ≤ (T ∩ W).card)
    ≤ δ * (((𝒲.filter (fun W => t ∈ W)).card : ℝ) * ((L : ℝ) * δ) ^ K
        + ((𝒲.filter (fun W => t ∉ W)).card : ℝ) * ((L : ℝ) * δ) ^ (K + 1))

open Classical in
def SelectGen : Prop := ∀ (n : ℕ) [NeZero n] (δ : ℝ) {ι : Type} (I : Finset ι) (ω β : ι → ℝ)
  (Bad : ι → ZMod n → Finset (ZMod n) → Prop),
  0 ≤ δ → δ ≤ 1 → 16 ≤ δ * n → (∀ p, 0 ≤ ω p) →
  (∀ p ∈ I, ∀ t, prob (Finset.univ : Finset (ZMod n)) δ (fun T => t ∈ T ∧ Bad p t T) ≤ δ * β p) →
  ∃ T : Finset (ZMod n), δ * n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * n ∧
    ∑ p ∈ I, ω p * ((T.filter (fun t => Bad p t T)).card : ℝ) ≤ 4 * δ * n * ∑ p ∈ I, ω p * β p

open Classical in
def SelectTops : Prop := ∀ (n : ℕ) [NeZero n] (δ : ℝ) (L₂ K : ℕ) {ι : Type} (I : Finset ι)
  (ω : ι → ℝ) (hh : ι → ZMod n),
  0 ≤ δ → δ ≤ 1 → 16 ≤ δ * n → 1 ≤ L₂ → (∀ p, 0 ≤ ω p) →
  ∃ T : Finset (ZMod n), δ * n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * n ∧
    ∑ p ∈ I, ω p * ((T.filter (fun t => ∃ W ∈ orbitWindows n (hh p) t L₂, K + 1 ≤ (T ∩ W).card)).card : ℝ)
      ≤ 4 * δ * n * ∑ p ∈ I, ω p *
          ((addOrderOf (hh p) : ℝ) * ((L₂ : ℝ) * δ) ^ K * (1 + L₂ * δ) + L₂ * ((L₂ : ℝ) * δ) ^ K)

def TrivStab : Prop := ∀ (E : Type) [Field E] [NumberField E] (k g : ℕ), g.Prime →
  Module.finrank ℚ E * k < g - 1 →
  ∀ Γ : Subgroup (GL (Fin k) E), Finite Γ → IsPGroup g Γ → Γ = ⊥

def vand {r : ℕ} (u : Fin r → ℝ) : ℝ := ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (u i - u j)

def dimV {r : ℕ} (u : Fin r → ℝ) : ℝ := vand u / ∏ i : Fin r, ((i : ℕ).factorial : ℝ)

end Formalism.BehrendSets
