import Mathlib

open NumberField IsDedekindDomain
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable (K : Type) [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

def rkL (M : Submodule (𝓞 K) V) : ℕ := Module.finrank K (Submodule.span K (M : Set V))

variable (V) in

structure PtNorms where

  Pt : HeightOneSpectrum (𝓞 K) → Type

  nrm : ∀ v, Pt v → V → ℝ
  nonneg : ∀ v y f, 0 ≤ nrm v y f
  add_le : ∀ v y f g, nrm v y (f + g) ≤ max (nrm v y f) (nrm v y g)
  smul : ∀ v y (a : K) f, nrm v y (a • f) = FinitePlace.mk v a * nrm v y f

variable {K}

def PtNorms.supLat [IsScalarTower (𝓞 K) K V] (P : PtNorms K V) (W : Submodule K V) : Submodule (𝓞 K) V where
  carrier := {f | f ∈ W ∧ ∀ v y, P.nrm v y f ≤ 1}
  add_mem' := fun {f g} hf hg =>
    ⟨W.add_mem hf.1 hg.1, fun v y => (P.add_le v y f g).trans (max_le (hf.2 v y) (hg.2 v y))⟩
  zero_mem' := ⟨W.zero_mem, fun v y => by
    have h := P.smul v y 0 0
    rw [zero_smul, map_zero, zero_mul] at h
    rw [h]; exact zero_le_one⟩
  smul_mem' := fun a f hf => by
    have e : a • f = (algebraMap (𝓞 K) K a) • f := (algebraMap_smul K a f).symm
    refine ⟨by rw [e]; exact W.smul_mem _ hf.1, fun v y => ?_⟩
    rw [e, P.smul]
    have h1 : FinitePlace.mk v (algebraMap (𝓞 K) K a) ≤ 1 := by
      rw [FinitePlace.mk_apply]; exact FinitePlace.norm_le_one K v a
    exact mul_le_one₀ h1 (P.nonneg v y f) (hf.2 v y)

end GlobalTheory.CompanionTheory.Ar.Deg
