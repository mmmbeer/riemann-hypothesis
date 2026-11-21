import Mathlib

namespace Formalism.SA.A

open Matrix

variable {O K : Type} [CommRing O] [CommRing K] [Algebra O K]

def e (R : Type) [CommRing R] (n : ℕ) : Fin (n+1) → R := Pi.single (Fin.last n) 1

def IsInt (O : Type) {K : Type} [CommRing O] [CommRing K] [Algebra O K] {ι : Type}
    (v : ι → K) : Prop :=
  ∀ i, v i ∈ Set.range (algebraMap O K)

abbrev toK {n : ℕ} (Z : Matrix (Fin (n+1)) (Fin (n+1)) O) : Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Z.map (algebraMap O K)

noncomputable def kap (K : Type) [CommRing K] [Algebra O K] {n : ℕ}
    (Z : Matrix (Fin (n+1)) (Fin (n+1)) O) : K :=
  (toK (K := K) Z)⁻¹ (Fin.last n) (Fin.last n)

noncomputable def yp (K : Type) [CommRing K] [Algebra O K] {n : ℕ}
    (g Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O) : Fin (n+1) → K :=
  (toK (K := K) Z₁)⁻¹ *ᵥ ((toK (K := K) g)⁻¹ *ᵥ e K n - e K n)

noncomputable def xp (K : Type) [CommRing K] [Algebra O K] {n : ℕ}
    (g' Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O) : Fin (n+1) → K :=
  (e K n ᵥ* toK (K := K) g' - e K n) ᵥ* (toK (K := K) Z₁)⁻¹

def LL (K : Type) [CommRing K] [Algebra O K] {n : ℕ} (Z₁ Z₂ : Matrix (Fin (n+1)) (Fin (n+1)) O) :
    Set (Matrix (Fin (n+1)) (Fin (n+1)) O × Matrix (Fin (n+1)) (Fin (n+1)) O) :=
  {p | IsUnit p.1 ∧ IsUnit p.2 ∧ p.1 * Z₁ = Z₂ * p.2 ∧
    IsInt O (yp K p.1 Z₁) ∧ IsInt O (xp K p.2 Z₁)}

def LL' (K : Type) [CommRing K] [Algebra O K] {n : ℕ} (Z₁ Z₂ : Matrix (Fin (n+1)) (Fin (n+1)) O) :
    Set (Matrix (Fin (n+1)) (Fin (n+1)) O × Matrix (Fin (n+1)) (Fin (n+1)) O) :=
  {p | p ∈ LL K Z₁ Z₂ ∧ p.1 *ᵥ e O n = e O n ∧ e O n ᵥ* p.2 = e O n}

def KK {n : ℕ} (Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O) : Set (Matrix (Fin (n+1)) (Fin (n+1)) O) :=
  {M | IsUnit (1 + Z₁ * M)}

def kmul {n : ℕ} (Z₁ M M' : Matrix (Fin (n+1)) (Fin (n+1)) O) : Matrix (Fin (n+1)) (Fin (n+1)) O :=
  M + M' + M * Z₁ * M'

def act {n : ℕ} (Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O)
    (p : Matrix (Fin (n+1)) (Fin (n+1)) O × Matrix (Fin (n+1)) (Fin (n+1)) O)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) O) :
    Matrix (Fin (n+1)) (Fin (n+1)) O × Matrix (Fin (n+1)) (Fin (n+1)) O :=
  (p.1 * (1 + Z₁ * M), p.2 * (1 + M * Z₁))

def Primitive (R : Type) {Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (v : Q) : Prop :=
  ∃ f : Q →ₗ[R] R, f v = 1

def blk {R : Type} {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (b c : Fin (m+1) → R) (d : R) :
    Matrix (Fin (m+1) ⊕ Unit) (Fin (m+1) ⊕ Unit) R :=
  Matrix.fromBlocks A (Matrix.of fun i (_ : Unit) => b i) (Matrix.of fun (_ : Unit) j => c j)
    (Matrix.of fun _ _ => d)

end Formalism.SA.A
