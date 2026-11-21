import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnfoldingOperatorConditions

open Formalism.L2.Col Formalism.L2.Col.Loc

variable {E : Type} [Field E] [NumberField E]

def IsLatAt (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  ∃ g : (Fin N → E) ≃ₗ[E] (Fin N → E), ∀ v, v ∈ Λ ↔ ∀ l, IntAt P (g.symm v l)

def aux (E : Type) [Field E] (n c i : ℕ) : Fin (n + c) → E := eN E (n + c) (n + (i - 1))

def unfoldedCoordinate {E : Type} [Field E] (n c i : ℕ) (v : Fin (n + c) → E) : E := atN v (n + (i - 1))

def CoordinateImageOfLattice (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ} (Λ : Submodule (𝓞 E) (Fin (n + c) → E)) (i : ℕ) (m : ℤ) : Prop :=
  ∀ s : E, (∃ v ∈ Λ, v ∈ Ufl E n c i ∧ unfoldedCoordinate n c i v = s) ↔ ∃ u : E, IntAt P u ∧ s = (qOf P : E) ^ m * u

structure CondO {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (D : ℕ) : Prop where
  add : ∀ x y : E, IntAt P ((qOf P : E) ^ D * x) → IntAt P ((qOf P : E) ^ D * y) → psi (x + y) = psi x * psi y
  int : ∀ x : E, IntAt P x → psi x = 1
  ne : psi ((qOf P : E)⁻¹) ≠ 1

def Concl (P : HeightOneSpectrum (𝓞 E)) {n' n c : ℕ} (e' : ℕ → ℤ) (z : Fin n' → E) (Λ : Submodule (𝓞 E) (Fin (n + c) → E))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : Prop :=
  (∃ e : ℕ → ℤ, ∀ i, 1 ≤ i → i ≤ c → CoordinateImageOfLattice P Λ i (e i) ∧ e' (i + 1) - 1 ≤ e i ∧ e i ≤ e' i) ∧
    ((qOf P : E) ^ e' 1) • (aux E n c 1 + inX E n c (xj z)) ∈ Λ

example : aux ℚ 2 3 1 = ![0, 0, 1, 0, 0] := by
  funext l; fin_cases l <;> simp [aux, eN]

example : unfoldedCoordinate 2 3 2 (aux ℚ 2 3 2) = 1 := by
  simp [unfoldedCoordinate, aux, atN, eN]

end GlobalTheory.IndefiniteRowSideFullHecke.UnfoldingOperatorConditions
