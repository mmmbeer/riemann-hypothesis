import Mathlib
import Formalism.NormUnitaryBounds.Statement

open MvPolynomial Finset

noncomputable section

namespace Formalism.HadamardInequality

open Classical in

def FreeOrbits : Prop :=
  ∀ (G X : Type) [Group G] [Fintype G] [MulAction G X] [Fintype X] (Z : Subgroup G) (ε : ℝ),
    (∀ z ∈ Z, ∀ x : X, z • x = x) →
    (∑ g ∈ univ.filter (fun g : G => g ∉ Z), (Nat.card (MulAction.fixedBy X g) : ℝ)) ≤
      ε * Fintype.card X →
    (Nat.card (MulAction.orbitRel.Quotient G X) : ℝ) * Fintype.card G ≤
      ((Nat.card Z : ℝ) + ε) * Fintype.card X

def freeOrbits (G X : Type) [Group G] [MulAction G X] (Z : Subgroup G) : Type :=
  {ω : MulAction.orbitRel.Quotient G X //
    ∃ x : X, (Quotient.mk (MulAction.orbitRel G X) x) = ω ∧ MulAction.stabilizer G x = Z}

open Classical in

def FreeFree : Prop :=
  ∀ (G X : Type) [Group G] [Fintype G] [MulAction G X] [Fintype X] (Z : Subgroup G) (ε : ℝ),
    (∀ z ∈ Z, ∀ x : X, z • x = x) →
    (∑ g ∈ univ.filter (fun g : G => g ∉ Z), (Nat.card (MulAction.fixedBy X g) : ℝ)) ≤
      ε * Fintype.card X →
    (Nat.card Z : ℝ) * (1 - ε) * Fintype.card X ≤
      (Nat.card (freeOrbits G X Z) : ℝ) * Fintype.card G

def equivFns (K G X V : Type) [Field K] [Group G] [MulAction G X] [AddCommGroup V] [Module K V]
    [DistribMulAction G V] [SMulCommClass G K V] : Submodule K (X → V) where
  carrier := {φ | ∀ (g : G) (x : X), φ (g • x) = g • φ x}
  add_mem' := by
    intro a b ha hb g x
    simp only [Set.mem_ofPred_eq] at ha hb
    simp [ha g x, hb g x, smul_add]
  zero_mem' := by intro g x; simp
  smul_mem' := by
    intro c a ha g x
    simp only [Set.mem_ofPred_eq] at ha
    simp [ha g x, smul_comm]

def FreeEquivDim : Prop :=
  ∀ (K G X V : Type) [Field K] [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [DistribMulAction G V]
    [SMulCommClass G K V] (Z : Subgroup G), (∀ z ∈ Z, ∀ v : V, z • v = v) →
    Module.finrank K V * Nat.card (freeOrbits G X Z) ≤ Module.finrank K (equivFns K G X V) ∧
      Module.finrank K (equivFns K G X V) ≤
        Module.finrank K V * Nat.card (MulAction.orbitRel.Quotient G X)

open Classical in

def FreeConsequence : Prop :=
  ∀ (K G X V : Type) [Field K] [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [DistribMulAction G V]
    [SMulCommClass G K V] (Z : Subgroup G) (ε : ℝ), 0 ≤ ε → ε ≤ 1 / 4 →
    (∀ z ∈ Z, ∀ v : V, z • v = v) → (∀ z ∈ Z, ∀ x : X, z • x = x) →
    (∑ g ∈ univ.filter (fun g : G => g ∉ Z), (Nat.card (MulAction.fixedBy X g) : ℝ)) ≤
      ε * Fintype.card X →
    (Module.finrank K V : ℝ) * Nat.card (MulAction.orbitRel.Quotient G X) ≤
      (1 + 3 * ε) * Module.finrank K (equivFns K G X V)

def LHyp {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (ϖ : R) (U D : V →ₗ[R] V)
    (S B : ℕ → Submodule R V) (a d I : ℕ) : Prop :=
  (∀ s, S s ≤ B s) ∧
  (∀ s, Module.Free R (S s) ∧ Module.Finite R (S s) ∧ Module.finrank R (S s) ≤ d) ∧
  (∀ s, Module.length R (B s ⧸ (S s).comap (B s).subtype) ≤ (I : ℕ∞)) ∧
  (∀ s, ∀ φ ∈ S (s + 1), D φ ∈ B s ∧ U (D φ) = ϖ ^ a • φ)

def L3 : Prop :=
  ∀ (R V : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup V]
    [Module R V] (ϖ : R), Irreducible ϖ →
    ∀ (U D : V →ₗ[R] V) (S B : ℕ → Submodule R V) (a d I : ℕ), LHyp ϖ U D S B a d I →
    ∀ j s : ℕ, j ≤ s →
      Module.length R (S s ⧸ (S s ⊓ (S (s - j)).map (U ^ j)).comap (S s).subtype) ≤
        ((j * (a * d + I) : ℕ) : ℕ∞)

def typ {G n : ℕ} (i : Fin n → Fin G) : Fin G → ℕ := fun j => (univ.filter fun m => i m = j).card

def polyMap {K W : Type} [Field K] [AddCommGroup W] [Module K W] (m d : ℕ)
    (w : (Fin m → ℕ) → W) (g : Fin m → K) : W :=
  ∑ e ∈ Fintype.piFinset (fun _ : Fin m => range (d + 1)), (∏ i, g i ^ e i) • w e

def rowSubst {N n r : ℕ} (x₀ : Fin n → ℂ) (y : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (p : Fin (N + 1) × Fin n) : MvPolynomial ((Fin N × Fin r) ⊕ Fin N) ℂ :=
  Fin.cases (motive := fun _ => Fin n → MvPolynomial ((Fin N × Fin r) ⊕ Fin N) ℂ)
    (fun k => C (x₀ k))
    (fun j k => (∑ i, X (Sum.inl (j, i)) * C (y i k)) + X (Sum.inr j) * C (z k)) p.1 p.2

def vlen {n : ℕ} (x : Fin n → ℂ) : ℝ := Real.sqrt (∑ k, ‖x k‖ ^ 2)

def RowBound : Prop :=
  ∀ (N n r : ℕ) (ν : Fin (N + 1) → ℕ) (F : MvPolynomial (Fin (N + 1) × Fin n) ℂ),
    F ∈ weightedHomogeneousSubmodule ℂ (Formalism.NormUnitaryCountingLemmas.blockWt (N + 1) n) ν →
    ∀ (x₀ : Fin n → ℂ) (y : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (Rb : ℝ),
    (∀ i, vlen (y i) ≤ Rb) → vlen z ≤ 1 →
    ∀ e, ‖coeff e (aeval (rowSubst x₀ y z) F)‖ ≤
      Formalism.NormUnitaryCountingLemmas.bnorm F * vlen x₀ ^ ν 0 * ((r : ℝ) * Rb + 1) ^ (∑ j : Fin N, ν j.succ)

def Hadamard : Prop :=
  ∀ (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ), ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2

def HadamardMax : Prop :=
  ∀ (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ) (M : ℝ), (∀ i j, ‖A i j‖ ≤ M) →
    ‖A.det‖ ^ 2 ≤ ((ρ : ℝ) * M ^ 2) ^ ρ

end Formalism.HadamardInequality
