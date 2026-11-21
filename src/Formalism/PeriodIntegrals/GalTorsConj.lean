import Mathlib

noncomputable section

namespace PI.GalTorsConj

open Classical
open scoped Pointwise

def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}

def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2

def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3

def liftM (M : IntermediateField ℚ ℂ) (x : ℂ) : M := if h : x ∈ M then ⟨x, h⟩ else 0

def lamConj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ :=
  Classical.epsilon (fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)))

def cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) : ℂ := ρ (liftM M x)

def wpF (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ :=
  1 / z ^ 2 + ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, (1 / (z - (w : ℂ)) ^ 2 - 1 / (w : ℂ) ^ 2)

def wpD (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := -2 * ∑' w : Λ, 1 / (z - (w : ℂ)) ^ 3

def InRationalLattice (Λ : AddSubgroup ℂ) (x : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ (m : ℂ) * x ∈ Λ

end PI.GalTorsConj
