import Mathlib
import Formalism.FlagUnipotentLattices.IdealCountLeW

noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def IotaCount : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] (h : U →ₗ[E] U →ₗ⋆[E] E) (g : E)
    (L₀ L₀' La : Submodule (𝓞 E) U) (e : ℕ) (s : Fin e → U) (S : Finset (U → U)),
    g ∈ (algebraMap (𝓞 E) E).range → star g = g → g ≠ 0 →
    (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ (algebraMap (𝓞 E) E).range) → La ≤ L₀ ⊓ L₀' →
    L₀' ≤ La ⊔ Submodule.span (𝓞 E) (Set.range s) → (∀ i, s i ∈ L₀') →
    L₀.toAddSubgroup.relIndex (hdual h (algebraMap (𝓞 E) E).range La.toAddSubgroup) ≠ 0 →
    (∀ ι' ∈ S, (∀ x ∈ L₀', ι' x ∈ L₀) ∧
      (∀ a : 𝓞 E, ∀ x ∈ L₀', ∀ y ∈ L₀', ∃ l ∈ L₀, ι' (a • x + y) - (a • ι' x + ι' y) = g • l) ∧
      (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ (algebraMap (𝓞 E) E).range, h (ι' x) (ι' y) - h x y = g * t) ∧
      (∀ x ∈ La, ∃ l ∈ L₀, ι' x - x = g • l)) →
    (∀ ι₁ ∈ S, ∀ ι₂ ∈ S, (∀ l' ∈ L₀', ∃ l ∈ L₀, ι₁ l' - ι₂ l' = g • l) → ι₁ = ι₂) →
      S.card ≤ L₀.toAddSubgroup.relIndex (hdual h (algebraMap (𝓞 E) E).range La.toAddSubgroup) ^ e

def QuotGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] [Module.Projective (𝓞 E) M] (I : Ideal (𝓞 E)), I ≠ ⊥ →
      ∃ s : Fin (Module.finrank (𝓞 E) M) → M ⧸ (I • (⊤ : Submodule (𝓞 E) M)),
        Submodule.span (𝓞 E) (Set.range s) = ⊤

def EmbGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (A : Submodule (𝓞 E) V) (Q : Type) [AddCommGroup Q]
    [Module (𝓞 E) Q] [Finite Q] (φ : Q →ₗ[𝓞 E] V ⧸ A), Function.Injective φ →
      ∃ s : Fin (Module.finrank E V) → Q, Submodule.span (𝓞 E) (Set.range s) = ⊤

def DualGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] (h : U →ₗ[E] U →ₗ⋆[E] E) (M N : Submodule (𝓞 E) U) (e : ℕ)
    (s : Fin e → U), N ≤ M → N.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 →
    M ≤ N ⊔ Submodule.span (𝓞 E) (Set.range s) → (∀ i, s i ∈ M) →
      ∃ t : Fin e → U, (∀ i, t i ∈ hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) ∧
        ∀ x ∈ hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup, ∃ c : Fin e → 𝓞 E,
          x - ∑ i, c i • t i ∈ hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup

def DualQuotGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] (h : U →ₗ[E] U →ₗ⋆[E] E) (M N : Submodule (𝓞 E) U) (e : ℕ)
    (s : Fin e → U) (w : U), N ≤ M → N.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 →
    M ≤ N ⊔ Submodule.span (𝓞 E) (Set.range s) → (∀ i, s i ∈ M) →
    M.toAddSubgroup ≤ hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup →
    w ∈ hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup →
    (∀ x ∈ hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup, ∃ a : 𝓞 E, x - a • w ∈ M) →
      ∃ t : Fin (2 * e + 1) → U, (∀ i, t i ∈ hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) ∧
        ∀ x ∈ hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup, ∃ c : Fin (2 * e + 1) → 𝓞 E,
          x - ∑ i, c i • t i ∈ N

def BetweenGen : Prop :=
  ∀ (R U : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup U] [Module R U] (A D L : Submodule R U) (e : ℕ)
    (t : Fin e → U), A ≤ L → L ≤ D → A.toAddSubgroup.relIndex D.toAddSubgroup ≠ 0 →
    D ≤ A ⊔ Submodule.span R (Set.range t) → (∀ i, t i ∈ D) →
      ∃ u : Fin e → U, (∀ i, u i ∈ L) ∧ L ≤ A ⊔ Submodule.span R (Set.range u)

def PCount : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] [Module.Projective (𝓞 E) M] (I : Ideal (𝓞 E)), I ≠ ⊥ →
      {P : Submodule (𝓞 E) M | I • (⊤ : Submodule (𝓞 E) M) ≤ P}.Finite ∧
        {P : Submodule (𝓞 E) M | I • (⊤ : Submodule (𝓞 E) M) ≤ P}.ncard ≤
          Ideal.absNorm I ^ (Module.finrank (𝓞 E) M ^ 2)

def IotaCountFull : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] (h : U →ₗ[E] U →ₗ⋆[E] E) (g : E)
    (L₀ L₀' La : Submodule (𝓞 E) U) (e : ℕ) (s : Fin e → U) (w : U) (S : Finset (U → U)),
    g ∈ (algebraMap (𝓞 E) E).range → star g = g → g ≠ 0 →
    (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ (algebraMap (𝓞 E) E).range) → La ≤ L₀ ⊓ L₀' →
    L₀ ≤ La ⊔ Submodule.span (𝓞 E) (Set.range s) → (∀ i, s i ∈ L₀) →
    w ∈ hdual h (algebraMap (𝓞 E) E).range L₀.toAddSubgroup →
    (∀ x ∈ hdual h (algebraMap (𝓞 E) E).range L₀.toAddSubgroup, ∃ a : 𝓞 E, x - a • w ∈ L₀) →
    L₀'.toAddSubgroup ≤ hdual h (algebraMap (𝓞 E) E).range La.toAddSubgroup →
    La.toAddSubgroup.relIndex (hdual h (algebraMap (𝓞 E) E).range La.toAddSubgroup) ≠ 0 →
    (∀ ι' ∈ S, (∀ x ∈ L₀', ι' x ∈ L₀) ∧
      (∀ a : 𝓞 E, ∀ x ∈ L₀', ∀ y ∈ L₀', ∃ l ∈ L₀, ι' (a • x + y) - (a • ι' x + ι' y) = g • l) ∧
      (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ (algebraMap (𝓞 E) E).range, h (ι' x) (ι' y) - h x y = g * t) ∧
      (∀ x ∈ La, ∃ l ∈ L₀, ι' x - x = g • l)) →
    (∀ ι₁ ∈ S, ∀ ι₂ ∈ S, (∀ l' ∈ L₀', ∃ l ∈ L₀, ι₁ l' - ι₂ l' = g • l) → ι₁ = ι₂) →
      S.card ≤ L₀.toAddSubgroup.relIndex (hdual h (algebraMap (𝓞 E) E).range La.toAddSubgroup) ^ (2 * e + 1)

def IotaCountFullAsm : Prop := DualQuotGen → BetweenGen → IotaCount → IotaCountFull

def OmSumLong : Prop :=
  ∀ (C₁ C₂ j r k f : ℕ) (g' i' b₁ Del Db NT H : ℝ), 1 ≤ r → j ≤ r → 1 ≤ g' → 1 ≤ i' → 0 ≤ b₁ → g' * i' ≤ Del →
    1 ≤ Db → 1 ≤ NT → 0 ≤ H →
      i' ^ ((k : ℝ) + (1 + Real.logb 2 (2 * f))) * (b₁ ^ k * (g' * i') ^ (r - j) * NT ^ (C₁ * r)) *
          (H * Db ^ (C₂ * r) * (Del * Db * NT) ^ (C₂ * r ^ 2)) ≤
        (i' * b₁) ^ k * i' ^ (1 + Real.logb 2 (2 * f)) * H * (Db * Del * NT) ^ ((C₁ + 2 * C₂ + 1) * r ^ 2)

end Formalism.HermitianLatticeCounting.S6
