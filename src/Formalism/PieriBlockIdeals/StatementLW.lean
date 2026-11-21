import Mathlib

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

def KapBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h : ℕ) (kap s : ι → ℤ), 2 ≤ l →
    (∀ i, 0 ≤ s i ∧ s i ≤ (h : ℤ)) →
    (∀ i, 0 ≤ (l : ℤ) * kap (σ i) + s i - kap i ∧ (l : ℤ) * kap (σ i) + s i - kap i ≤ (h : ℤ)) →
    ∀ i, ((l : ℤ) - 1) * |kap i| ≤ (h : ℤ)

def CharpolyBlocks : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (b : Fin n → ℕ)
    (S : Finset (Fin n)) (r : Fin n → K), M.BlockTriangular b →
    (∀ s ∈ S, ∀ j, b j = b s → j = s) → M.charpoly = ∏ u, (X - C (r u)) →
    Multiset.map (fun s => M s s) S.val ≤ Multiset.map r Finset.univ.val

end Formalism.CohomologicalDescent
