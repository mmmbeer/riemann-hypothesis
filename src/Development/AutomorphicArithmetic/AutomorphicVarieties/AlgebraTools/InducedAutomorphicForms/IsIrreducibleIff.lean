import Mathlib

noncomputable section

namespace UpperTheory.V.AlgebraTools

section Irr

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

def StableOn (ρ : Representation k G V) (H : Subgroup G) (W : Submodule k V) : Prop :=
  ∀ h ∈ H, ∀ v ∈ W, ρ h v ∈ W

def IrrOn (ρ : Representation k G V) (H : Subgroup G) : Prop :=
  ∀ W : Submodule k V, StableOn ρ H W → W = ⊥ ∨ W = ⊤

theorem IrrOn.mono {ρ : Representation k G V} {H H' : Subgroup G} (h : IrrOn ρ H) (hle : H ≤ H') : IrrOn ρ H' :=
  fun W hW => h W fun g hg => hW g (hle hg)


def matRep {n : Type} [Fintype n] [DecidableEq n] (r : G →* GL n k) : Representation k G (n → k) where
  toFun g := Matrix.toLin' (r g : Matrix n n k)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

@[simp] theorem matRep_apply {n : Type} [Fintype n] [DecidableEq n] (r : G →* GL n k) (g : G) (v : n → k) :
    matRep r g v = (r g : Matrix n n k).mulVec v := by
  simp [matRep]

end Irr

def subst {k n : Type} [CommRing k] [Fintype n] (A : Matrix n n k) : MvPolynomial n k →ₐ[k] MvPolynomial n k :=
  MvPolynomial.aeval fun i => ∑ j, A j i • MvPolynomial.X j

theorem subst_X {k n : Type} [CommRing k] [Fintype n] (A : Matrix n n k) (i : n) :
    subst A (MvPolynomial.X i) = ∑ j, A j i • MvPolynomial.X j := by
  simp [subst]

theorem subst_one {k n : Type} [CommRing k] [Fintype n] [DecidableEq n] :
    subst (1 : Matrix n n k) = AlgHom.id k _ := by
  ext1 i
  simp [subst, Matrix.one_apply]

theorem subst_mul {k n : Type} [CommRing k] [Fintype n] (A B : Matrix n n k) :
    subst (A * B) = (subst A).comp (subst B) := by
  ext1 i
  simp only [AlgHom.comp_apply, subst_X, map_sum, map_smul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

end UpperTheory.V.AlgebraTools
