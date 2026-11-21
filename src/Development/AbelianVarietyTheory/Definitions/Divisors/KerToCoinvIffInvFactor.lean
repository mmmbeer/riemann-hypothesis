import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RallisCoinvariants
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DegeneratePrincipalSeriesUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantLinOm

noncomputable section

open GlobalTheory.WeilM GlobalTheory.LinPair
open scoped Matrix

namespace GlobalTheory.RallisSplit

theorem vanish_locAug_iff {G H Y : Type} [Group G] [Group H] [TopologicalSpace Y] (om : G × H →* Module.End ℂ (Y → ℂ))
    (T : (Y → ℂ) →ₗ[ℂ] ℂ) : (∀ z ∈ locAug om, T z = 0) ↔ ∀ g : G, ∀ φ ∈ SB Y, T (om (g, 1) φ) = T φ := by
  refine ⟨fun h g φ hφ => ?_, fun h z hz => ?_⟩
  · rw [← sub_eq_zero, ← map_sub]
    exact h _ (Submodule.subset_span ⟨g, φ, hφ, rfl⟩)
  · refine (Submodule.span_le (p := LinearMap.ker T)).2 ?_ hz
    rintro _ ⟨g, φ, hφ, rfl⟩
    exact LinearMap.mem_ker.2 (by rw [map_sub, h g φ hφ, sub_self])

theorem secSpace_ne_bot {G H Y : Type} [Group G] [Group H] [TopologicalSpace Y] (om : G × H →* Module.End ℂ (Y → ℂ))
    {l : (Y → ℂ) →ₗ[ℂ] ℂ} (hl : ∃ φ ∈ SB Y, l φ ≠ 0) : secSpace om l ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := hl
  intro e
  have h : secMap om l φ ∈ secSpace om l := ⟨φ, hφ, rfl⟩
  rw [e, Submodule.mem_bot] at h
  have := congrFun h 1
  rw [secMap_apply, show ((1 : G), (1 : H)) = 1 from rfl, map_one] at this
  exact h0 this

example (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E]
    (c : E →ₐ[k] E) (δ : E) (hq : IsQuad c δ) (ψ : AddChar k ℂ) (h1 : Continuous ψ) (h2 : ∀ t, ‖ψ t‖ = 1) (h3 : ψ ≠ 1) :
    ∃ (JA JB : Matrix (Fin 2) (Fin 2) E) (Cy : Matrix (Fin 2) (Fin 1) E) (co : Darboux (symp c 1 JA JB) (Fin 4))
      (om : UG c JA × UG c JB →* Module.End ℂ ((Fin 4 → k) → ℂ)) (l : ((Fin 4 → k) → ℂ) →ₗ[ℂ] ℂ),
      (∀ i j, c (1 * JB j i) = -(1 * JB i j)) ∧ JB.det ≠ 0 ∧ IsHerm c JA ∧ ResEtaPow (R := k) ⊥ (1 : Eˣ →* Circle) 2 ∧
      IsLinPair c ψ 1 JA JB co 1 Cy om ∧ IsYForm c ψ co Cy l ∧ (∀ z ∈ locAug om, l z = 0) ∧ secSpace om l ≠ ⊥ := by
  obtain ⟨Cy, co, om, l, h, hl⟩ := GlobalTheory.HypPair.exists_linPair k E c δ hq ψ h1 h2 h3
  exact ⟨_, _, Cy, co, om, l, fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp,
    ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp⟩, fun a => by simp, h, hl,
    (vanish_locAug_iff om l).2 (h.lin l hl.1), secSpace_ne_bot om hl.2⟩

example {G H Y : Type} [Group G] [Group H] [TopologicalSpace Y] : locAug (1 : G × H →* Module.End ℂ (Y → ℂ)) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨g, φ, -, rfl⟩
  simp

example {G H Y : Type} [Group G] [Group H] (l : (Y → ℂ) →ₗ[ℂ] ℂ) (φ : Y → ℂ) :
    secMap (1 : G × H →* Module.End ℂ (Y → ℂ)) l φ = fun _ => l φ := rfl

end GlobalTheory.RallisSplit

end
