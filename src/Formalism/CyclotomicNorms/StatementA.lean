import Mathlib

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

abbrev wt (x : ℝ) : WithTop ℝ := (x : WithTop ℝ)

def Newton : Prop :=
  ∀ (L : Type) [Field L] (v : AddValuation L (WithTop ℝ)) (ℓ e : ℕ) (f : L[X]) (c : ℝ),
    ℓ.Prime → 0 < e → v (ℓ : L) = wt 1 →
    (∀ i, v (f.coeff i) = ⊤ ∨ ∃ n : ℕ, v (f.coeff i) = wt ((n : ℝ) / e)) →
    v (f.coeff 0) = wt c →
    ∃ X : Finset ℕ, (X.card : ℝ) ≤ e * c ∧
      ∀ j : ℕ, 1 ≤ j → j ∉ X → ∀ z : L, IsPrimitiveRoot z (ℓ ^ j) →
        v (f.eval (z - 1)) ≤ wt c

def Evaluation : Prop :=
  ∀ (L : Type) [Field L] (v : AddValuation L (WithTop ℝ)) (ℓ e w j : ℕ) (F : L[X]) (z : L),
    ℓ.Prime → 0 < e → v (ℓ : L) = wt 1 →
    (∀ i, v (F.coeff i) = wt 0 ∨ wt (1 / e) ≤ v (F.coeff i)) →
    (∃ i ≤ w, v (F.coeff i) = wt 0) →
    IsPrimitiveRoot z (ℓ ^ j) → ((e * w : ℕ) : ℝ) < ((ℓ ^ j).totient : ℝ) →
    v (F.eval (z - 1)) ≤ wt ((w : ℝ) / ((ℓ ^ j).totient : ℝ))

def evalAt (k : Type) {M W : Type} [CommRing k] [AddMonoid M] [AddCommGroup W] [Module k W]
    (x : M) : (M →+ W) →ₗ[k] W where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coboundary {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : Representation R G W) (n : ℕ) (f : (Fin n → G) → W) : (Fin (n + 1) → G) → W :=
  fun g => ρ (g 0) (f fun i => g i.succ) +
    ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)

def CentralScalar : Prop :=
  ∀ (G R W : Type) [Group G] [TopologicalSpace G] [CommRing R] [AddCommGroup W] [Module R W]
    [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R G W) (z : G) (c : R),
    z ∈ Subgroup.center G → IsUnit (c - 1) → (∀ w, ρ z w = c • w) →
    (∀ w : W, (∀ g, ρ g w = w) → w = 0) ∧
    ∀ (n : ℕ) (f : (Fin (n + 1) → G) → W), Continuous f → coboundary ρ (n + 1) f = 0 →
      ∃ h : (Fin n → G) → W, Continuous h ∧ coboundary ρ n h = f

def Cycles : Prop :=
  ∀ (G k V P : Type) [Group G] [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Fintype P] (ρ : Representation k G V) (N : ℕ) (D I : P → Subgroup G)
    (χ : P → Fin N → G → k) (flag : P → Fin (N + 1) → Submodule k V),
    Module.finrank k V = N →
    (∀ v, I v ≤ D v) → (∀ v, ∀ d ∈ D v, ∀ x ∈ I v, d * x * d⁻¹ ∈ I v) →

    (∀ v (i : Fin (N + 1)), Module.finrank k (flag v i) = i) →
    (∀ v (i : Fin N), flag v i.castSucc ≤ flag v i.succ) →
    (∀ v i, ∀ x ∈ flag v i, ∀ y ∈ I v, ρ y x ∈ flag v i) →

    (∀ v (i : Fin N), ∀ x ∈ flag v i.succ, ∀ y ∈ I v,
      ρ y x - χ v i y • x ∈ flag v i.castSucc) →

    (∀ v (i j : Fin N), i ≠ j → ∃ y ∈ I v, χ v i y ≠ χ v j y) →
    (∀ v (i : Fin N), ∀ d ∈ D v, ∃ j : Fin N, ∀ y ∈ I v, χ v j y = χ v i (d⁻¹ * y * d)) →

    (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ S : Finset (Fin N), S.card = a ∧
      ∀ i ∈ S, ∀ d ∈ D v, ∃ j ∈ S, ∀ y ∈ I v, χ v j y = χ v i (d⁻¹ * y * d)) →
    ∀ W : Submodule k V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤

end Formalism.CyclotomicNorms
