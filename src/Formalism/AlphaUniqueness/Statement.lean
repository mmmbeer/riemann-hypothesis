import Mathlib

open Finset

noncomputable section

namespace Formalism.K

section Gauss
variable {M : Type*} [AddCommGroup M]

def polar (Q : M → ℂ) (x y : M) : ℂ :=
  Q (x + y) * (starRingEnd ℂ) (Q x) * (starRingEnd ℂ) (Q y)

structure IsUQuad (Q : M → ℂ) : Prop where
  norm_eq : ∀ x, ‖Q x‖ = 1
  neg : ∀ x, Q (-x) = Q x
  polar_add : ∀ x x' y, polar Q (x + x') y = polar Q x y * polar Q x' y

def Nondeg (Q : M → ℂ) : Prop := ∀ y, (∀ x, polar Q x y = 1) → y = 0

def gsum [Fintype M] (Q : M → ℂ) : ℂ := ∑ x, Q x

def prim (p : ℕ) : AddSubgroup M where
  carrier := {x | ∃ k : ℕ, p ^ k • x = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have h1 : (p ^ (a + b)) • x = 0 := by rw [pow_add, mul_comm (p ^ a), mul_smul, ha, smul_zero]
    have h2 : (p ^ (a + b)) • y = 0 := by rw [pow_add, mul_smul, hb, smul_zero]
    rw [smul_add, h1, h2, add_zero]
  neg_mem' := by
    rintro x ⟨k, hk⟩
    exact ⟨k, by rw [smul_neg, hk, neg_zero]⟩

end Gauss

section Alpha
variable {L : Type*} [AddCommGroup L]

def qRef (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ) (x : L) : ZMod 2 :=
  ∑ i ∈ range l, ∑ j ∈ Ico (i + 1) l, ψ ((σ ^ i) x) ((σ ^ j) x)

end Alpha

end Formalism.K
