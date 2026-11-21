import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConclusionRankZero

noncomputable section

open GlobalTheory.WeilM GlobalTheory.Published.HoweDualityFiniteModel
open scoped Matrix

namespace GlobalTheory.LinPair.Model

section General

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]
  {ψ : AddChar k ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle}
  {Cy : Matrix β ν E} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)} {l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ}

theorem comm {G H Y : Type} [Group G] [Group H] (om : G × H →* Module.End ℂ (Y → ℂ)) (g : G) (h : H) (φ : Y → ℂ) :
    om (1, h) (om (g, 1) φ) = om (g, 1) (om (1, h) φ) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]; simp




omit [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E] [DecidableEq α]
  [DecidableEq β] [DecidableEq ν] in

theorem isYInv_eval_zero (hd : ∀ z : Matrix α ν E, (d.e (z * Cyᵀ)).1 = 0) :
    IsYInv c ψ d Cy (LinearMap.proj (0 : κ → k)) := by
  intro z φ _
  simp [Darboux.rho, schr, hd]

end General

section Abstract







end Abstract

section Witt

variable {k E : Type} [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E)



end Witt

section RankZero

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)

omit [Invertible (2 : k)] in
theorem lagr_plane : IsLagr c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) (!![1; 0] : Matrix (Fin 2) (Fin 1) E) := by
  refine ⟨?_, !![0; 1], Matrix.fromRows !![1, 0] !![0, 1], ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Subsingleton.elim i j]

variable [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]


def RankZero (ψ : AddChar k ℂ) : Prop :=
  ∃ (JA : Matrix (Fin 0) (Fin 0) E) (JB : Matrix (Fin 2) (Fin 2) E) (Cy : Matrix (Fin 2) (Fin 1) E)
    (co : Darboux (symp c (-1) JA JB) Empty) (om : UG c JA × UG c JB →* Module.End ℂ ((Empty → k) → ℂ))
    (l : ((Empty → k) → ℂ) →ₗ[ℂ] ℂ),
    IsHerm c JA ∧ (∀ i j, c (JB j i) = -JB i j) ∧
    JB.det ≠ 0 ∧ IsLagr c JB Cy ∧ IsLinPair c ψ (-1) JA JB co 1 Cy om ∧ IsUWeilPair c (sbClass k) ψ (-1) JA JB co 1 1 om ∧
    IsYForm c ψ co Cy l ∧ IsCoinvQuot om om


end RankZero


end GlobalTheory.LinPair.Model

end
