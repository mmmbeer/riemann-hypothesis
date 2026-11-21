import Mathlib

open Finset

noncomputable section

namespace Formalism.GaloisIrreducibility

def IsSubSum (d : Multiset ℕ) (a : ℕ) : Prop := ∃ s ≤ d, s.sum = a

def IsOrbit {α : Type*} (f : α → α) (O : Finset α) : Prop :=
  (∀ x ∈ O, f x ∈ O) ∧ ∀ x ∈ O, ∀ y ∈ O, ∃ n : ℕ, f^[n] x = y

def PermSubSumInv : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (a : ℕ),
    IsSubSum σ.partition.parts a → ∃ A : Finset α, (∀ x ∈ A, σ x ∈ A) ∧ A.card = a

def OrbitSubSum : Prop :=
  ∀ (α ι : Type) (f : α → α) (O : ι → Finset α) (I : Finset ι) (M' : Multiset α),
    (∀ i ∈ I, IsOrbit f (O i)) → M' ≤ ∑ i ∈ I, (O i).val → M'.map f = M' →
    ∃ J ⊆ I, M'.card = ∑ i ∈ J, (O i).card

def RestrictRoots : Prop :=
  ∀ (K V : Type) [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (τ : Module.End K V) (F : V ≃ₗ[K] V) (q : ℕ),
    (∀ v, F (τ v) = (τ ^ q) (F v)) →
    ∀ (W : Submodule K V) (hτ : ∀ v ∈ W, τ v ∈ W), (∀ v ∈ W, F v ∈ W) →
      (LinearMap.charpoly (τ.restrict hτ)).roots ≤ (LinearMap.charpoly τ).roots ∧
      ((LinearMap.charpoly (τ.restrict hτ)).roots).map (fun x => x ^ q) =
        (LinearMap.charpoly (τ.restrict hτ)).roots

def LemmaA : Prop :=
  ∀ (K V ι : Type) [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (τ : Module.End K V) (F : V ≃ₗ[K] V) (q : ℕ)
    (O : ι → Finset K) (I : Finset ι),
    (∀ v, F (τ v) = (τ ^ q) (F v)) →
    (∀ i ∈ I, IsOrbit (fun x : K => x ^ q) (O i)) →
    (LinearMap.charpoly τ).roots = ∑ i ∈ I, (O i).val →
    ∀ W₁ W₂ : Submodule K V, W₁ ≤ W₂ →
      (∀ v ∈ W₁, τ v ∈ W₁) → (∀ v ∈ W₁, F v ∈ W₁) →
      (∀ v ∈ W₂, τ v ∈ W₂) → (∀ v ∈ W₂, F v ∈ W₂) →
      ∃ J ⊆ I, Module.finrank K W₂ - Module.finrank K W₁ = ∑ i ∈ J, (O i).card

def Irred : Prop :=
  ∀ (K V P ι : Type) [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (τ : P → Module.End K V) (F : P → V ≃ₗ[K] V) (q : P → ℕ)
    (O : P → ι → Finset K) (I : P → Finset ι),
    (∀ v x, F v (τ v x) = (τ v ^ q v) (F v x)) →
    (∀ v, ∀ i ∈ I v, IsOrbit (fun x : K => x ^ q v) (O v i)) →
    (∀ v, (LinearMap.charpoly (τ v)).roots = ∑ i ∈ I v, (O v i).val) →
    (∀ a : ℕ, 1 ≤ a → 2 * a ≤ Module.finrank K V →
      ∃ v, ¬ IsSubSum ((I v).val.map fun i => (O v i).card) a) →
    ∀ W : Submodule K V, (∀ v, ∀ x ∈ W, τ v x ∈ W) → (∀ v, ∀ x ∈ W, F v x ∈ W) →
      W = ⊥ ∨ W = ⊤

open Classical in

def ShareBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (T : ι → Type) [∀ v, Fintype (T v)]
    (w : ∀ v, T v → ℝ) (μ : (∀ v, T v) → ℝ) (K c : ℝ) (P : Finset (Finset ι)) (A : Finset ℕ)
    (bad : ℕ → ∀ v, T v → Prop),
    0 ≤ K → (∀ v t, 0 ≤ w v t) → (∀ v, ∑ t, w v t ≤ 1) → (∀ x, μ x ≤ K * ∏ v, w v (x v)) →
    (∀ a ∈ A, ∀ S ∈ P, ∀ v ∈ S, ∑ t ∈ univ.filter (bad a v), w v t ≤ c) →
    ∑ x ∈ univ.filter (fun x => ∃ S ∈ P, ∃ a ∈ A, ∀ v ∈ S, bad a v (x v)), μ x
      ≤ K * ∑ S ∈ P, ∑ a ∈ A, c ^ S.card

open Classical in

def ShareN : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (T : ι → Type) [∀ v, Fintype (T v)]
    (w : ∀ v, T v → ℝ) (μ : (∀ v, T v) → ℝ) (K c : ℝ) (N J : ℕ) (P : Finset (Finset ι))
    (bad : ℕ → ∀ v, T v → Prop),
    P.card ≤ 2 → (∀ S ∈ P, S.card = J) → 0 ≤ K → 0 ≤ c →
    (∀ v t, 0 ≤ w v t) → (∀ v, ∑ t, w v t ≤ 1) → (∀ x, μ x ≤ K * ∏ v, w v (x v)) →
    (∀ a ∈ Icc 1 (N / 2), ∀ S ∈ P, ∀ v ∈ S, ∑ t ∈ univ.filter (bad a v), w v t ≤ c) →
    ∑ x ∈ univ.filter (fun x => ∃ S ∈ P, ∃ a ∈ Icc 1 (N / 2), ∀ v ∈ S, bad a v (x v)), μ x
      ≤ N * K * c ^ J

def ResiduesLe : Prop :=
  ∀ (l j D : ℕ), l.Prime → 1 ≤ D →
    ((Finset.range (l ^ j)).filter (fun x => x ^ D ≡ 1 [MOD l ^ j])).card ≤ 2 * D

def FewLargeParts : Prop :=
  ∀ (n : ℕ) (B : ℝ) (S : Finset ℕ), 1 ≤ n → 0 < B → (∀ l ∈ S, l.Prime) → S.Nonempty →
    (∀ l ∈ S, B < ((l ^ padicValNat l n : ℕ) : ℝ)) → B ^ S.card < n

def CardGL : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (N : ℕ),
    Fintype.card (GL (Fin N) K) ≤ Fintype.card K ^ (N ^ 2)

def OneNonUnit : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : ℕ) (A : Matrix (Fin s) (Fin s) R),
    s - 1 ≤ (A.map (IsLocalRing.residue R)).rank →
    ∃ P Q : GL (Fin s) R, ∃ d : R,
      (P : Matrix (Fin s) (Fin s) R) * A * (Q : Matrix (Fin s) (Fin s) R) =
        Matrix.diagonal (fun i : Fin s => if (i : ℕ) = s - 1 then d else 1)

def PowerPCycle : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (p : ℕ), p.Prime →
    p ∈ σ.cycleType → Fintype.card α < 2 * p →
    ∃ k : ℕ, (σ ^ k).IsCycle ∧ (σ ^ k).support.card = p

def PrimitiveOfPCycle : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α))
    (σ : Equiv.Perm α) (p : ℕ),
    p.Prime → σ ∈ G → σ.IsCycle → σ.support.card = p → Fintype.card α < 2 * p →
    MulAction.IsPretransitive G α → MulAction.IsPreprimitive G α

def JordanPrime : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α))
    (σ : Equiv.Perm α) (p : ℕ),
    p.Prime → σ ∈ G → σ.IsCycle → σ.support.card = p → p + 3 ≤ Fintype.card α →
    MulAction.IsPreprimitive G α → alternatingGroup α ≤ G

def AltNotSolvable : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α], 5 ≤ Fintype.card α →
    ¬ Group.IsSolvable (alternatingGroup α)

def NoSolvableTransitive : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α))
    (σ : Equiv.Perm α) (p : ℕ),
    p.Prime → σ ∈ G → p ∈ σ.cycleType → Fintype.card α < 2 * p → p + 3 ≤ Fintype.card α →
    MulAction.IsPretransitive G α → ¬ Group.IsSolvable G

def BBAtMostThree : Prop :=
  ∀ (g d : ℕ) (S : Finset ℕ), 2 ≤ g → 1 ≤ d → (∀ l ∈ S, l.Prime) →
    (∀ l ∈ S, (g : ℝ) ^ ((d : ℝ) / 4) < ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) →
    S.card ≤ 3

end Formalism.GaloisIrreducibility
