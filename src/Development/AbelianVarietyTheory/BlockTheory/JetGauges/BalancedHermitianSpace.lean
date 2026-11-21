import Mathlib

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace

open NumberField NumberField.IsCMField TensorProduct

abbrev Bil (Y : Type) [AddCommGroup Y] : Type := Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ

section Forms

variable {Y : Type} [AddCommGroup Y]

def quad (β : Bil Y) (x : Y) : ℝ := β x x / 2

def IsIntegralFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z

def IsPositiveFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a, 0 ≤ (β : Bil Y) a a) → β ≠ 0 → 0 < l β

def IsAdmissible (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  IsIntegralFn S l ∧ IsPositiveFn S l

def leastExponent (S : Submodule ℝ (Bil Y)) (b : S) : ℝ :=
  sInf {x | ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l ∧ x = l b}

def evalSum (S : Submodule ℝ (Bil Y)) {k : ℕ} (x x' : Fin k → Y) : S →ₗ[ℝ] ℝ where
  toFun β := ∑ i, (β : Bil Y) (x i) (x' i)
  map_add' β γ := by simp [Finset.sum_add_distrib]
  map_smul' r β := by simp [Finset.mul_sum]

def HasShortFrame (β : Bil Y) (r : ℝ) : Prop :=
  ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧ ∀ i, quad β (v i) ≤ r

end Forms

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def HasTraceOne : Prop := ∃ w : 𝓞 E, w + ringOfIntegersComplexConj E w = 1

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def IsBalanced (β : Bil Y) : Prop :=
  (∀ x y, β x y = β y x) ∧
    ∀ (a : 𝓞 E) (x y : Y), β (a • x) y = β x (ringOfIntegersComplexConj E a • y)

def IsBalancedSpace (S : Submodule ℝ (Bil Y)) : Prop := ∀ β, β ∈ S ↔ IsBalanced E β

def balancedSpace (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] : Submodule ℝ (Bil Y) where
  carrier := {β | IsBalanced E β}
  add_mem' hβ hγ := ⟨fun x y => by simp [hβ.1 x y, hγ.1 x y], fun a x y => by simp [hβ.2 a x y, hγ.2 a x y]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' r β hβ := ⟨fun x y => by simp [hβ.1 x y], fun a x y => by simp [hβ.2 a x y]⟩

theorem IsBalancedSpace.eq {S : Submodule ℝ (Bil Y)} (h : IsBalancedSpace E S) : S = balancedSpace E Y :=
  Submodule.ext h

def SpansOverField {k : ℕ} (x : Fin k → Y) : Prop :=
  Submodule.span E (Set.range fun b => ((1 : E) ⊗ₜ[𝓞 E] x b : E ⊗[𝓞 E] Y)) = ⊤

omit [NumberField E] [IsCMField E] in

def AdmissibleAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, IsAdmissible S l ↔
    IsPositiveFn S l ∧ ∃ (k : ℕ) (x x' : Fin k → Y), l = evalSum S x x'

open NumberField NumberField.IsCMField TensorProduct in
variable (E : Type) [Field E] [NumberField E] [IsCMField E] in
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] in
omit [NumberField E] [IsCMField E] [Module (𝓞 E) Y] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum (S : Submodule ℝ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y))
    {k : ℕ} (x x' : Fin k → Y) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsIntegralFn S (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.evalSum S x x') := by
  intro β hβ
  choose f hf using hβ
  refine ⟨∑ i, f (x i) (x' i), ?_⟩
  show ∑ i, (β : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y) (x i) (x' i) = _
  push_cast
  exact Finset.sum_congr rfl fun i _ => hf _ _

end GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
