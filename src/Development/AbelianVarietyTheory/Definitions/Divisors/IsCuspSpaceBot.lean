import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSelfDualFor
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace GlobalTheory.GamMul

section Blocks

variable {R : Type} [CommRing R]

def put (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
      X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0

def eye (R : Type) [CommRing R] (n o₁ o₂ p : ℕ) : Matrix (Fin n) (Fin n) R :=
  put n o₁ o₂ (1 : Matrix (Fin p) (Fin p) R)

open Classical in

def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : GL (Fin n) R := if h : IsUnit M then h.unit else 1

def uni (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) : GL (Fin n) R := toGL (1 + put n o₁ o₂ X)

def dg (n o : ℕ) {p : ℕ} (g : GL (Fin p) R) : GL (Fin n) R :=
  toGL (1 - eye R n o o p + put n o o (g : Matrix (Fin p) (Fin p) R))

def shuf (R : Type) [CommRing R] (n m : ℕ) : GL (Fin n) R := toGL (eye R n 0 m (n - m) + eye R n (n - m) 0 m)

theorem toGL_val {n : ℕ} (g : GL (Fin n) R) : toGL (g : Matrix (Fin n) (Fin n) R) = g := by
  unfold toGL
  rw [dif_pos g.isUnit]
  exact Units.ext rfl

end Blocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mint [MeasurableSpace k] (μ : Measure k) {p q : ℕ} (F : Matrix (Fin p) (Fin q) k → ℂ) : ℂ :=
  ∫ x : Fin p → Fin q → k, F (Matrix.of x) ∂(Measure.pi fun _ => Measure.pi fun _ => μ)

def box (p q : ℕ) (c : kˣ) : Set (Matrix (Fin p) (Fin q) k) := {X | ∀ i j, valuation k (X i j) ≤ valuation k (c : k)}

def ad {m : ℕ} (s : ℂ) (g : GL (Fin m) k) : ℂ := (absPow k s (GeneralLinearGroup.det g) : ℂ)

def IsTest₂ {m₁ m₂ : ℕ} (ψ : AddChar k Circle) (F : GL (Fin m₁) k → GL (Fin m₂) k → ℂ) : Prop :=
  (∀ u ∈ unipB k (Fin m₁), ∀ a b, F (u * a) b = (ψ (superDiag u) : ℂ) * F a b) ∧
  (∀ u ∈ unipB k (Fin m₂), ∀ a b, F a (u * b) = (ψ (superDiag u) : ℂ) * F a b) ∧
  IsLocallyConstant (Function.uncurry F) ∧
  ∃ (C₁ : Set (GL (Fin m₁) k)) (C₂ : Set (GL (Fin m₂) k)), IsCompact C₁ ∧ IsCompact C₂ ∧ ∀ a b, F a b ≠ 0 →
    (∃ u ∈ unipB k (Fin m₁), ∃ c ∈ C₁, a = u * c) ∧ ∃ u ∈ unipB k (Fin m₂), ∃ c ∈ C₂, b = u * c

def vol [MeasurableSpace k] (μ : Measure k) {p q : ℕ} (Λ : Set (Matrix (Fin p) (Fin q) k)) : ℂ :=
  mint μ (Λ.indicator fun _ => 1)

end GlobalTheory.GamMul

end
