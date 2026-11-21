import Mathlib

open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

open scoped ComplexOrder

def SubstitutionAdaptive : Prop :=
  ∀ (k : Type) [CommRing k] (ℓ r s : ℕ) (F : Fin s → MvPowerSeries (Fin r) k) (B : List ℕ → ℕ),
    2 ≤ ℓ → (∀ i, F i ≠ 0) →
    ∃ e : Fin r → ℕ, StrictMono e ∧
      (∀ j : Fin r, B (List.ofFn fun i : Fin (j : ℕ) => e (Fin.castLE (Nat.le_of_lt j.isLt) i)) ≤ e j) ∧
      ∀ i, (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ (ℓ ^ e j)) (F i) :
        PowerSeries k) ≠ 0

def PermFixedSet : Prop :=
  ∀ N a : ℕ, 0 < a → a < N →
    8 * (univ.filter (fun σ : Equiv.Perm (Fin N) =>
      ∃ S : Finset (Fin N), S.card = a ∧ S.map σ.toEmbedding = S)).card ≤ 7 * N.factorial

def DiscardKernel : Prop :=
  ∀ (m n : ℕ) (B : Matrix (Fin m) (Fin n) ℂ) (Pi : Matrix (Fin m) (Fin m) ℂ) (c : ℝ),
    Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ c →
    ((c : ℂ) • (B.conjTranspose * B) - (c : ℂ) • (B.conjTranspose * (1 - Pi) * B)).PosSemidef

end Formalism.CyclotomicNorms
