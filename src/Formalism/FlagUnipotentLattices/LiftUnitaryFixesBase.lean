import Mathlib
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

noncomputable section

open scoped BigOperators
open Matrix

namespace Formalism.HermitianLatticeCounting.S6

def superSum {R : Type} [AddCommMonoid R] {j : ℕ} (A : Matrix (Fin j) (Fin j) R) : R :=
  ∑ a : Fin j, if h : a.val + 1 < j then A a ⟨a.val + 1, h⟩ else 0

def Zj {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] {H : HermSpace K V}
    {r : ℕ} (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) : Matrix (Fin j) (Fin j) K :=
  (Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r)))

def InULift {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
    (H : HermSpace K V) (Wt : Submodule K V) (g : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (g x) (g y) = H.B x y) ∧ ∀ y : V, (∀ w ∈ Wt, H.B y w = 0) → g y = y

def LiftUnitaryFixesBase : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (Wt : Submodule K V) (g : V →ₗ[K] V), IsLift F F' Wt → InULift H Wt g →
      (∀ y ∈ V0 F F', g y = y) ∧ (∀ a : Fin (r + 1), g (F.e a) = F.e a) ∧
      (∀ a : Fin (r + 1), g (F'.e a) = F'.e a)

def LiftAniso : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (Wt : Submodule K V), F.Aniso → F'.Aniso → IsLift F F' Wt →
      ∀ w ∈ Wt, H.B w w = 0 → w = 0

def LiftUnitary : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (Wt : Submodule K V) (h : Wt →ₗ[K] Wt),
    F.Aniso → F'.Aniso → IsLift F F' Wt → (∀ x y : Wt, H.B (h x : V) (h y : V) = H.B (x : V) (y : V)) →
      ∃! g : V →ₗ[K] V, InULift H Wt g ∧ Function.Bijective g ∧ ∀ w : Wt, g (w : V) = (h w : V)

def LiftIsoW : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) (Wt : Submodule K V),
    NFFull F F' j hj c → IsLift F F' Wt →
      (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃! wt : V, wt ∈ Wt ∧ w - wt ∈ F.X) ∧
      (∀ w : V, (∀ a : Fin (r + 1), H.B (F'.e a) w = 0) → ∃! wt : V, wt ∈ Wt ∧ w - wt ∈ F'.X)

def RelIndexInter : Prop :=
  ∀ (G : Type) [AddCommGroup G] (Lam₁ M W La : AddSubgroup G), La ≤ M ⊓ W →
    (Lam₁ ⊓ W).relIndex La ∣ Lam₁.relIndex M

def IndexChain : Prop :=
  ∀ (G : Type) [AddCommGroup G] (Lam₁ L W La : AddSubgroup G), Lam₁ ⊓ W ≤ La → La ≤ L ⊓ W →
    Lam₁.relIndex L ≠ 0 →
      La.relIndex (L ⊓ W) * (Lam₁ ⊓ W).relIndex La = (Lam₁ ⊓ W).relIndex (L ⊓ W) ∧
      (Lam₁ ⊓ W).relIndex (L ⊓ W) ≤ Lam₁.relIndex L

def mI (f : ℕ) (v dF : ℝ) (Lv : ℕ → ℝ) (i : ℕ) : ℝ :=
  (((i - 1).factorial : ℝ) * (v / Real.pi) ^ i) ^ f * (Real.sqrt dF)⁻¹ * Lv i

def PairsLoss : Prop :=
  ∀ (C s k : ℕ) (D' D'' NT Hh S' S'' : ℝ), s ≤ k → 1 ≤ Hh → 1 ≤ S' → 1 ≤ S'' → 0 ≤ D' → 0 ≤ D'' →
    0 ≤ NT → D' ≤ Hh * S' ^ 2 → D'' ≤ Hh * S'' ^ 2 → NT ≤ Hh →
      (D' * D'' * NT) ^ (C * s) ≤ Hh ^ (3 * C * s) * (S' * S'') ^ (2 * C * k)

def RatioSum : Prop :=
  ∀ (C k f : ℕ) (g Hh : ℝ), 0 < g → 1 ≤ Hh →
    ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2 →
      ∑ s ∈ Finset.Icc 1 (k - 1),
        ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ 1

def RatioBound : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ C₀ : ℕ, ∀ (k r f : ℕ) (b g : ℝ), 2 ≤ b → 1 ≤ f → Real.log f ≤ (r : ℝ) ^ 2 →
    C₀ * (2 * r + 2) ^ 2 ≤ k → ((k : ℝ) * b) ^ 8 ≤ g →
      ((C : ℝ) / g) ^ (k * f) * (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2

def SEqKClose : Prop :=
  ∀ (C k f : ℕ) (g Hh NT : ℝ), 4 ≤ C → 0 < g → 1 ≤ Hh → 0 ≤ NT → NT ≤ Hh →
    ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2 →
      (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hh ^ ((C - 1) * k) ≤ 1

end Formalism.HermitianLatticeCounting.S6
