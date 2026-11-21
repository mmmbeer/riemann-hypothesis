import Mathlib
import Formalism.HyperbolicPlaceProducts.Statement
import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality

open Module NumberField

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

abbrev TorsionIndex : Prop := Formalism.SLP.TorsionIndex

abbrev EntriesOfSignaturePreserving : Prop := Formalism.SLP.GlobalBoundRefinements.EntriesOfSignaturePreserving

abbrev DetIndexProductHyperbolicInequality : Prop := Formalism.SLP.GlobalBoundRefinements.DetIndexProductHyperbolicInequality

def perpR {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
    (B : V →ₗ[K] V →ₛₗ[σ] K) (A : Submodule K V) : Submodule K V :=
  ⨅ a : A, LinearMap.ker (B a)

def PerpCompl : Prop :=
  ∀ (K U : Type) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (σ : K →+* K), (∀ x, σ (σ x) = x) →
    ∀ (B : U →ₗ[K] U →ₛₗ[σ] K), (∀ x : U, (∀ y : U, B y x = 0) → x = 0) →
    (∀ x : U, (∀ y : U, B x y = 0) → x = 0) →
    ∀ (r : ℕ) (A A' : Submodule K U), finrank K U = 2 * (r + 1) →
      finrank K A = r + 1 → finrank K A' = r + 1 → A ⊔ A' = ⊤ →
      finrank K (perpR B A) = r + 1 ∧ finrank K (perpR B A') = r + 1 ∧
        IsCompl (perpR B A) (perpR B A')

def CofactorVec : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R),
    (∀ a : Fin (r + 1), ∑ b, Z.adjugate (Fin.last r) b * Z b a =
        if a = Fin.last r then Z.det else 0) ∧
      Z.adjugate (Fin.last r) (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det

def SignaturePreservingEntryNorms : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (T T' : ℝ) (D Dr : ℂ),
    M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J → 0 < T → 0 < T' →
    0 < ‖D‖ ^ 2 - T * T' * ‖Dr‖ ^ 2 →
    ‖M 1 0‖ ^ 2 = T * T' * ‖Dr‖ ^ 2 / (‖D‖ ^ 2 - T * T' * ‖Dr‖ ^ 2) →
    (Dr ≠ 0 →
      let ch := ‖D / Dr‖ / Real.sqrt (T * T')
      let sh := Real.sqrt (ch ^ 2 - 1)
      ‖M 1 0‖ = 1 / sh ∧ ‖M 0 1‖ = 1 / sh ∧ ‖M 0 0‖ = ch / sh ∧ ‖M 1 1‖ = ch / sh) ∧
    (Dr = 0 → M 1 0 = 0 ∧ M 0 1 = 0 ∧ ‖M 0 0‖ = 1 ∧ ‖M 1 1‖ = 1)

def IsInt {E : Type*} [Field E] [NumberField E] (x : E) : Prop :=
  ∃ y : 𝓞 E, (y : E) = x

def LocIn {E : Type*} [Field E] [NumberField E] (P : Ideal (𝓞 E)) (x : E) (N : ℕ) : Prop :=
  ∃ y z : 𝓞 E, y ∉ P ∧ (y : E) * x = (N : E) * (z : E)

def ZZ {E : Type*} [Field E] [NumberField E] (g : ℕ) : Set (E × E) :=
  {p | IsInt p.1 ∧ IsInt p.2 ∧ ∃ w : 𝓞 E, p.1 + p.2 = (g : E) * (w : E)}

def ZZgPreserve : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (a b c d : E),
    (∀ p ∈ (ZZ g : Set (E × E)), (a * p.1 + b * p.2, c * p.1 + d * p.2) ∈ (ZZ g : Set (E × E))) →
    IsInt ((g : E) * a) ∧ IsInt ((g : E) * b) ∧ IsInt ((g : E) * c) ∧ IsInt ((g : E) * d) ∧
      IsInt (a - b) ∧ IsInt (c - d)

def LocalCongr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : Ideal (𝓞 E)) (T T' : ℕ) (a b c d : E),
    P.IsPrime → 0 < T → 0 < T' →
    (∀ u v : E, LocIn P ((T : E) * u) 1 → LocIn P ((T' : E) * v) 1 →
      LocIn P ((a - 1) * u + b * v) 1 ∧ LocIn P (c * u + (d - 1) * v) 1) →
    LocIn P (a - 1) T ∧ LocIn P c T ∧ LocIn P b T' ∧ LocIn P (d - 1) T'

def SInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (T T' g : ℕ) (s b c : E),
    0 < T → 0 < T' →
    s = (T' : E) * c * σ c / (T : E) → s = (T : E) * b * σ b / (T' : E) →
    IsInt ((g : E) * b) → IsInt ((g : E) * c) →
    (∀ P : Ideal (𝓞 E), P.IsPrime → (T : 𝓞 E) ∈ P → LocIn P c T) →
    (∀ P : Ideal (𝓞 E), P.IsPrime → (T' : 𝓞 E) ∈ P → LocIn P b T') →
    ∃ β : 𝓞 E, (g : E) ^ 2 * s = (T : E) * (T' : E) * (β : E)

def CMRoot : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (q : ℝ) (x : InfinitePlace E → ℝ),
    (∀ w : InfinitePlace E, w.IsComplex) → 0 < q → (∀ w, 0 ≤ x w) →
    q ^ finrank ℚ E ≤ ∏ w : InfinitePlace E, (x w ^ 2) ^ w.mult →
    q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2) ≤ ∏ w : InfinitePlace E, x w

def ThmB : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E),
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = starRingEnd ℂ (φ x)) →
    (∀ w : InfinitePlace E, w.IsComplex) →
    ∀ (T T' g : ℕ) (a b c d : E) (x : InfinitePlace E → ℝ), 3 ≤ T → 3 ≤ T' → 1 ≤ g →
    (∀ (φ : E →+* ℂ) (u v : ℂ),
      T * ‖φ a * u + φ b * v‖ ^ 2 - T' * ‖φ c * u + φ d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) →
    (∀ p ∈ (ZZ g : Set (E × E)), (a * p.1 + b * p.2, c * p.1 + d * p.2) ∈ (ZZ g : Set (E × E))) →
    (∀ P : Ideal (𝓞 E), P.IsPrime → ((T : 𝓞 E) ∈ P ∨ (T' : 𝓞 E) ∈ P) →
      LocIn P (a - 1) T ∧ LocIn P c T ∧ LocIn P b T' ∧ LocIn P (d - 1) T') →
    (∀ w : InfinitePlace E, 0 ≤ x w) →
    (∀ w : InfinitePlace E, (T' : ℝ) * w c ^ 2 / T ≤ x w ^ 2) →
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨
      ((T : ℝ) * T' / (g : ℝ) ^ 2) ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2) ≤
        ∏ w : InfinitePlace E, x w

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
