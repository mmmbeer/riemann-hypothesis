import Mathlib

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

def FiltProd : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (F : ℕ → Submodule R V) (c : ℕ → R) (k a : ℕ),
    (∀ i, k ≤ i → i < k + a → ∀ x ∈ F i, T x - c i • x ∈ F (i + 1)) →
    ∀ x ∈ F k, aeval T (∏ i ∈ Finset.Ico k (k + a), (X - C (c i))) x ∈ F (k + a)

def ContractBij : Prop :=
  ∀ (R P : Type) [CommRing R] [AddCommGroup P] [Module R P] (I : Ideal R) [IsAdicComplete I P]
    (f : P →+ P),
    (∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P)) →
    Function.Bijective (fun x => f x - x)

def ColengthTwoStep : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (l g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) (s s₀ : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    s₀.card ≤ g₀ → (s₀ : Set M) ⊆ Z →
    (∀ p ∈ Z, (l ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (l ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) * Module.length O (O ⧸ Ideal.span {(l : O)})

def DigitLemma : Prop :=
  ∀ (l a c ρ : ℕ) (m : ℤ), l.Prime → 1 ≤ a → 0 < c → c < l ^ a - 1 → 1 ≤ ρ →
    (l ^ a - 1) ∣ c * (l ^ ρ - 1) → |m| < l →
    padicValInt l ((c : ℤ) + m * ((l : ℤ) ^ a - 1)) ≤ ρ

def LagrangeBoundT : Prop :=
  ∀ (l a A' r' : ℕ) (Cc : Finset ℕ), l.Prime → 1 ≤ a → 2 * A' < l →
    (∀ c ∈ Cc, c < l ^ a - 1) →
    (∀ c ∈ Cc, ∀ c' ∈ Cc, c ≠ c' → ∃ ρ, 1 ≤ ρ ∧ ρ ≤ r' ∧
      ((l : ℤ) ^ a - 1) ∣ ((c : ℤ) - c') * ((l : ℤ) ^ ρ - 1)) →
    ∀ c ∈ Cc, ∀ n < A',
      (∑ c' ∈ Cc, ∑ n' ∈ Finset.range (2 * A'),
        if c' = c ∧ n' = n then 0
        else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1))))
      ≤ (Cc.card - 1) * r'

def LagrangeT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (D₁ D₂ : Finset ℤ) (ρ : ℕ), Disjoint D₁ D₂ →
    (∀ i ∈ D₁, (∑ j ∈ D₂, padicValInt l (i - j)) + ∑ j ∈ D₁.erase i, padicValInt l (i - j) ≤ ρ) →
    C ((l : ℤ_[l]) ^ ρ) ∈ Ideal.span ({∏ i ∈ D₁, (X - C ((i : ℤ) : ℤ_[l])),
      ∏ j ∈ D₂, (X - C ((j : ℤ) : ℤ_[l]))} : Set ℤ_[l][X])

def frob {O : Type} [CommRing O] (l : ℕ) (f : PowerSeries O) : PowerSeries O :=
  PowerSeries.mk fun n => if l ∣ n then PowerSeries.coeff (n / l) f else 0

def LiftExp : Prop :=
  ∀ (l h : ℕ) (J : Finset ℤ), l.Prime → l ≠ 2 → J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) → (0 : ℤ) ∉ J →
    2 * (2 * (2 * h) + padicValNat l (2 * (2 * h)).factorial) +
      ((∑ j ∈ J, (1 + padicValInt l j)) + h + padicValNat l h.factorial) ≤ 18 * h

def GLCardVal : Prop :=
  ∀ (g g' r : ℕ) [Fact g.Prime] [Fact g'.Prime], g ≠ g' →
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g))) = r * (r - 1) / 2 ∧
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g'))) =
      ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1)

end Formalism.IrreducibleCountingLemmas.WindowSums
