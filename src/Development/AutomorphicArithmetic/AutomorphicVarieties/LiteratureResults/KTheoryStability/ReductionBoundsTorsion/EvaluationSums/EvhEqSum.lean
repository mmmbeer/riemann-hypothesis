import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
import Mathlib

section
noncomputable section

namespace PositivityTheory.KB.ChainCochainPairing

variable {Y : Type}

def cob {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : (Fin (m + 2) → Y) → ℝ :=
  fun y => ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F fun j => y (i.succAbove j)

def pr : (n : ℕ) → ((Fin (n + 1) → Y) → ℝ) → (Fin n → Y) → (Fin n → Y) → ℝ
  | 0, _, _, _ => 0
  | n + 1, F, a, b => F (Fin.cons (a 0) b) - pr n (fun x => F (Fin.cons (a 0) x)) (Fin.tail a) (Fin.tail b)

theorem cons_smul {H : Type} [Monoid H] [MulAction H Y] {n : ℕ} (h : H) (v : Y) (x : Fin n → Y) :
    (Fin.cons (h • v) (fun j => h • x j) : Fin (n + 1) → Y) = fun j => h • (Fin.cons v x : Fin (n + 1) → Y) j := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cons_succAbove_succ {n : ℕ} (v : Y) (x : Fin (n + 1) → Y) (i : Fin (n + 1)) :
    (fun j : Fin (n + 1) => (Fin.cons v x : Fin (n + 2) → Y) ((Fin.succ i).succAbove j)) =
      Fin.cons v fun j => x (i.succAbove j) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.succ_succAbove_succ]

theorem succAbove_succ_eq_cons {n : ℕ} (a : Fin (n + 2) → Y) (i : Fin (n + 1)) :
    (fun j : Fin (n + 1) => a ((Fin.succ i).succAbove j)) =
      Fin.cons (a 0) fun j => Fin.tail a (i.succAbove j) := by
  conv_lhs => rw [← Fin.cons_self_tail a]
  exact cons_succAbove_succ _ _ _

end PositivityTheory.KB.ChainCochainPairing
end
end

section
noncomputable section

namespace PositivityTheory.KB.ChainCochainPairing

variable {G : Type} [Group G]

def evh {m : ℕ} (Φ : (Fin (m + 1) → G) → ℝ) : Chn G m →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun g => Φ (Fin.partialProd g)







end PositivityTheory.KB.ChainCochainPairing
end
end
