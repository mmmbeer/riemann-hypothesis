import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData

open Formalism.L2.Col

section Local

variable (g : ℕ) [Fact g.Prime]

abbrev Aut (N : ℕ) : Type := (Fin N → ℚ_[g]) ≃ₗ[ℚ_[g]] (Fin N → ℚ_[g])

abbrev HomQ (a b : ℕ) : Type := (Fin a → ℚ_[g]) →ₗ[ℚ_[g]] (Fin b → ℚ_[g])

abbrev Lat (N : ℕ) : Type := Submodule ℤ_[g] (Fin N → ℚ_[g])

def diagLat (N : ℕ) (e : ℕ → ℕ) : Lat g N :=
  Submodule.span ℤ_[g]
    (Set.range fun l : Fin N => (g : ℚ_[g]) ^ e l.1 • (Pi.single l 1 : Fin N → ℚ_[g]))

def stdLat (N : ℕ) : Lat g N := diagLat g N fun _ => 0

def lamSt (n c : ℕ) : Lat g (n + c) := diagLat g (n + c) fun l => if l < n then 0 else l - n + 1

variable {g}

def GLlat {N : ℕ} (Λ : Lat g N) : Subgroup (Aut g N) where
  carrier := {κ | ∀ v, κ v ∈ Λ ↔ v ∈ Λ}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb v => (ha (b v)).trans (hb v)
  inv_mem' := fun {a} ha v => by
    have h := ha (a.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def InG {N : ℕ} (Λ : Lat g N) (v : Fin N → ℚ_[g]) : Prop := ∃ u ∈ Λ, v = (g : ℚ_[g]) • u

def Into {a b : ℕ} (Λ' : Lat g a) (Λ : Lat g b) (x : HomQ g a b) : Prop := ∀ v ∈ Λ', x v ∈ Λ

def InjMod {a b : ℕ} (Λ' : Lat g a) (Λ : Lat g b) (x : HomQ g a b) : Prop :=
  ∀ v ∈ Λ', InG Λ (x v) → InG Λ' v

end Local

def e₁ (n c : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 c, (i * n + i * (i - 1) / 2)

def dimN (n c : ℕ) : ℕ := c * (c - 1) / 2 + (c - 1) * n

def expS (n c : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 c, ∑ i' ∈ Finset.Ico 1 i, (i - i') + n * ∑ i ∈ Finset.Icc 2 c, i

def expSup (n c : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 c, (n + i)

section Clauses

variable (g : ℕ) [Fact g.Prime] (hyp : Bool) (n' n c : ℕ)

end Clauses

example : e₁ 5 2 = 16 ∧ dimN 5 2 = 6 ∧ expS 5 2 = 11 ∧ expSup 5 2 = 13 := by decide

example {g : ℕ} [Fact g.Prime] {a : ℕ} (Λ : Lat g a) :
    Into Λ Λ LinearMap.id ∧ InjMod Λ Λ LinearMap.id := ⟨fun _ h => h, fun _ _ h => h⟩

end GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData
