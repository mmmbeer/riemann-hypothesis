import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod

open MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds

open Formalism.BasicNotions Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n n' : ℕ}

def nsqOne (lam : DomWeight n) (f : nablaSq ℂ n lam) : ℝ :=
  (normFock lam (f : MvPolynomial (Fin n × Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ)).re

def NormLeOne {lam : DomWeight n} {lam' : DomWeight n'} (A : nablaSq ℂ n lam →ₗ[ℂ] nablaSq ℂ n' lam') (c : ℝ) :
    Prop :=
  0 ≤ c ∧ ∀ f, nsqOne lam' (A f) ≤ c ^ 2 * nsqOne lam f

def tenV (lam : ι → DomWeight n) (f : ∀ τ, nablaSq ℂ n (lam τ)) : VV ℂ lam :=
  ⟨ten fun τ => (f τ : MvPolynomial (Fin n × Fin n) ℂ),
    Submodule.subset_span ⟨fun τ => (f τ : MvPolynomial (Fin n × Fin n) ℂ), fun τ => (f τ).2, rfl⟩⟩

def IsTensorMap {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') : Prop :=
  ∀ f : ∀ τ, nablaSq ℂ n (lam τ), T (tenV lam f) = tenV lam' fun τ => A τ (f τ)

theorem IsTensorMap.unique {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    {A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)} {T T' : VV ℂ lam →ₗ[ℂ] VV ℂ lam'}
    (h : IsTensorMap A T) (h' : IsTensorMap A T') : T = T' := by
  apply LinearMap.ext
  rintro ⟨F, hF⟩
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact (h fun τ => ⟨f τ, hf τ⟩).trans (h' fun τ => ⟨f τ, hf τ⟩).symm
  | zero => exact (map_zero T).trans (map_zero T').symm
  | add x y hx hy ihx ihy =>
    have e : T (⟨x, hx⟩ + ⟨y, hy⟩) = T' (⟨x, hx⟩ + ⟨y, hy⟩) := by rw [map_add, map_add, ihx, ihy]
    exact e
  | smul a x hx ih =>
    have e : T (a • ⟨x, hx⟩) = T' (a • ⟨x, hx⟩) := by rw [map_smul, map_smul, ih]
    exact e

example (lam : ι → DomWeight n) : IsTensorMap (lam := lam) (lam' := lam) (fun _ => LinearMap.id) LinearMap.id :=
  fun _ => rfl

example (lam : DomWeight n) : NormLeOne (lam := lam) (lam' := lam) LinearMap.id 1 :=
  ⟨zero_le_one, fun f => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds
