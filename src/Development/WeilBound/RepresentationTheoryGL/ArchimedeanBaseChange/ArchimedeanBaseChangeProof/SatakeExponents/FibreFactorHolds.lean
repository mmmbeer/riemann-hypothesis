import Mathlib

noncomputable section

open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def ExpSum : Prop := ∀ (ι : Type) [Fintype ι] (c lam : ι → ℂ) (ρ C : ℝ) (N : ℕ), 0 ≤ ρ →
  (∀ᶠ k : ℕ in Filter.atTop, ‖∑ i, c i * lam i ^ k‖ ≤ C * (1 + k) ^ N * ρ ^ k) →
  ∀ μ : ℂ, ρ < ‖μ‖ → ∑ i with lam i = μ, c i = 0

def OneFactor : Prop := ∀ (B : Type) [CommRing B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, B →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (p : B →⋆ₐ[ℂ] ℂ),
  (∀ b, ∃ s, ‖p b‖ ≤ ‖R s b‖) → ∃ s, ∀ b, ‖p b‖ ≤ ‖R s b‖

def fibre {A : Type} [CommRing A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] {ι : Type} (As : ι → Type)
    [∀ s, CommRing (As s)] [∀ s, Algebra ℂ (As s)] [∀ s, StarRing (As s)] [∀ s, StarModule ℂ (As s)]
    (ev : ∀ s, As s →⋆ₐ[ℂ] A) : StarSubalgebra ℂ (A × ∀ s, As s) where
  carrier := {x | ∀ s, ev s (x.2 s) = x.1}
  mul_mem' := fun {x y} hx hy s => by simp [hx s, hy s]
  add_mem' := fun {x y} hx hy s => by simp [hx s, hy s]
  algebraMap_mem' := fun z s => by simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := fun {x} hx s => by simp [map_star, hx s]

def FibreFactor : Prop := ∀ (A : Type) [CommRing A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (ι : Type) (As : ι → Type)
  [∀ s, CommRing (As s)] [∀ s, Algebra ℂ (As s)] [∀ s, StarRing (As s)] [∀ s, StarModule ℂ (As s)]
  (ev : ∀ s, As s →⋆ₐ[ℂ] A), (∀ s, Function.Surjective (ev s)) → ∀ (p : A →⋆ₐ[ℂ] ℂ) (s : ι) (ν : As s → ℝ),
  (∀ x ∈ fibre As ev, ‖p x.1‖ ≤ ν (x.2 s)) → ∀ b, ‖p (ev s b)‖ ≤ ν b

end PositivityTheory.Rg.BcB.F

end
