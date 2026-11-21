import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementE
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementC

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def genPoint {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : MvPolynomial (LVar ι ζ n) (GenField k n) :=
  sharpHom isVec S (genMat k n) (genMat k n)⁻¹
    (map ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) G)

def Carries {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) (N : Submodule k (MvPolynomial (LVar ι ζ n) k)) : Prop :=
  genPoint isVec S G ∈ Submodule.span (GenField k n)
    ((fun f => map ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) f) '' (N : Set _))

def genSpace {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : Submodule k (MvPolynomial (LVar ι ζ n) k) :=
  sInf {N | Carries isVec S G N}

def HasWeight {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (f : MvPolynomial (LVar ι ζ n) k) (ν : Fin n → ℤ) : Prop :=
  ∀ m : Fin n, IsWeightedHomogeneous
    (fun x : LVar ι ζ n => match x with
      | Sum.inl (i, a) => if i ∈ S ∧ a = m then (if isVec i then (1 : ℤ) else -1) else 0
      | Sum.inr _ => 0) f (ν m)

def IsWeightOf {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (N : Submodule k (MvPolynomial (LVar ι ζ n) k)) (ν : Fin n → ℤ) : Prop :=
  ∃ f ∈ N, f ≠ 0 ∧ HasWeight isVec S f ν

def GenSpaceFacts : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k),
    Carries isVec S G (genSpace isVec S G) ∧ G ∈ genSpace isVec S G ∧
    Module.Finite k (genSpace isVec S G) ∧
    genSpace isVec S G = Submodule.span k {f | f ∈ genSpace isVec S G ∧ ∃ ν, HasWeight isVec S f ν} ∧
    (∀ (h : (Matrix (Fin n) (Fin n) k)ˣ), ∀ f ∈ genSpace isVec S G,
      sharpHom isVec S (↑h : Matrix _ _ k) (↑h⁻¹ : Matrix _ _ k) f ∈ genSpace isVec S G) ∧
    ∀ (π : Equiv.Perm (Fin n)) (ν : Fin n → ℤ),
      IsWeightOf isVec S (genSpace isVec S G) ν → IsWeightOf isVec S (genSpace isVec S G) (ν ∘ π)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
