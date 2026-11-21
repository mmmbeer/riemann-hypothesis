import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors

open Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.SerOSys

theorem twoBlock_eq_zero_iff {n a : ℕ} (i : Fin n) : twoBlock n a i = 0 ↔ (i : ℕ) < a := by
  unfold twoBlock
  by_cases h : (i : ℕ) < a
  · simp [h]
  · simp only [h, if_false, iff_false]
    decide

theorem twoBlock_eq_one_iff {n a : ℕ} (i : Fin n) : twoBlock n a i = 1 ↔ a ≤ (i : ℕ) := by
  unfold twoBlock
  by_cases h : (i : ℕ) < a
  · simp only [h, if_true]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (by omega)⟩
  · simp only [h, if_false]
    exact ⟨fun _ => by omega, fun _ => trivial⟩

def firstBlock (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 0} ≃ Fin a where
  toFun i := ⟨i.1, (twoBlock_eq_zero_iff i.1).1 i.2⟩
  invFun j := ⟨⟨j, by omega⟩, (twoBlock_eq_zero_iff _).2 j.2⟩
  left_inv i := by rcases i with ⟨⟨i, hi⟩, h⟩; rfl
  right_inv j := by rcases j with ⟨j, hj⟩; rfl

def secondBlock (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 1} ≃ Fin b where
  toFun i := ⟨i.1 - a, by have := (twoBlock_eq_one_iff i.1).1 i.2; have := i.1.2; omega⟩
  invFun j := ⟨⟨a + j, by omega⟩, (twoBlock_eq_one_iff _).2 (by simp)⟩
  left_inv i := by
    rcases i with ⟨⟨i, hi⟩, h⟩
    have hai : a ≤ i := (twoBlock_eq_one_iff _).1 h
    apply Subtype.ext
    apply Fin.ext
    show a + (i - a) = i
    omega
  right_inv j := by
    rcases j with ⟨j, hj⟩
    apply Fin.ext
    simp

def twoRep {K : Type} [Field K] [Fintype K] [DecidableEq K] {a b : ℕ} (ρ : FDRep ℂ (GL (Fin a) K))
    (ρ' : FDRep ℂ (GL (Fin b) K)) : ∀ c : Fin 2, FDRep ℂ (GL {i : Fin (a + b) // twoBlock (a + b) a i = c} K)
  | 0 => transp (firstBlock a b).symm ρ
  | 1 => transp (secondBlock a b).symm ρ'

end GlobalTheory.SerOSys
