import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormOneOfPair
import Formalism.HermitianLattices.StatementLat

section
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def quasiRefl (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - a • (h u).smulRight u

theorem quasiRefl_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) (v : V) :
    quasiRefl h u a v = v - (a * h u v) • u := by
  first
  | simp [quasiRefl, smul_smul]
  | rw [quasiRefl, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, smul_smul]

theorem quasiRefl_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {a b : K}
    (hab : a + b = a * b * h u u) : quasiRefl h u a ∘ₗ quasiRefl h u b = LinearMap.id := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [quasiRefl_apply, quasiRefl_apply]
  simp only [map_sub, map_smul, map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
  rw [sub_sub, ← add_smul, sub_eq_self, smul_eq_zero]
  left
  linear_combination (h u v) * hab

end Formalism.HermitianLattices.Ext.L3.WA
end
end

section
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

structure IsSelfDualMod (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (M : AddSubgroup V) : Prop where
  smul_mem : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M
  int : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S
  dual : ∀ x : V, (∀ m ∈ M, h m x ∈ S) → x ∈ M
  span : ∀ x : V, ∃ t : K, t ≠ 0 ∧ t • x ∈ M

variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

end Formalism.HermitianLattices.Ext.L3.WA
end
end
