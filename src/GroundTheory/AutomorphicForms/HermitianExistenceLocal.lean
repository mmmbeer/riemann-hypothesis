import Mathlib
import GroundTheory.AutomorphicForms.HermitianLocalForms

section
noncomputable section

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain GroundTheory.Global NumberField.InfinitePlace.Completion

def Rep {F : Type*} [Field F] (d : F) {n : ℕ} (a : Fin n → F) (c : F) : Prop :=
  ∃ s : Fin n → F, (∀ i, SqNorm d (s i)) ∧ ∑ i, a i * s i = c

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]

end Local

section Real

variable {K : Type*} [Field K] {w : InfinitePlace K}

end Real

section Global

universe u

variable {K : Type u} [Field K] [NumberField K]

end Global

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Global

section Diagonalize

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
  [Algebra.IsSeparable F A]


end Diagonalize

section LocCongr

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def LocCongr (K : Type*) [Field K] [Algebra K E] [Algebra.IsQuadraticExtension K E] (R : Type*)
    [CommRing R] [Algebra K R] (H H' : Matrix ι ι E) : Prop :=
  IsCongr (conjBase K E R) (H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E))
    (H'.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E))

variable {R : Type*} [CommRing R] [Algebra K R]

theorem LocCongr.trans {H H' H'' : Matrix ι ι E} (h : LocCongr K R H H') (h' : LocCongr K R H' H'') :
    LocCongr K R H H'' :=
  IsCongr.trans h h'

theorem LocCongr.symm {H H' : Matrix ι ι E} (h : LocCongr K R H H') : LocCongr K R H' H :=
  IsCongr.symm h

omit [Algebra.IsQuadraticExtension K E] in

theorem IsCongr.submatrix {B : Type*} [CommRing B] {s : B →+* B} {κ : Type*} [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) {H H' : Matrix ι ι B} (h : IsCongr s H H') :
    IsCongr s (H.submatrix e e) (H'.submatrix e e) := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.submatrix e e, by rwa [det_submatrix_equiv_self], ?_⟩
  rw [← submatrix_map, transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

theorem LocCongr.submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    {H H' : Matrix ι ι E} (h : LocCongr K R H H') :
    LocCongr K R (H.submatrix e e) (H'.submatrix e e) := by
  unfold LocCongr at *
  rw [← submatrix_map, ← submatrix_map]
  exact IsCongr.submatrix e h

variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

variable (R) in

def HermitianForm.IsometricAt (h : HermitianForm K E V) (h' : HermitianForm K E V') : Prop :=
  ∃ (n : ℕ) (b : Basis (Fin n) E V) (b' : Basis (Fin n) E V'),
    LocCongr K R (gram h'.toSesq b') (gram h.toSesq b)

end LocCongr

section Coordinates

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : K} {ψ : E ≃ₐ[K] QuadraticAlgebra K d 0} (hψ : ∀ x, ψ (conj K E x) = star (ψ x))
include hψ

end Coordinates

section Main

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V] [AddCommGroup V']
  [Module E V'] [FiniteDimensional E V']

variable [NumberField K]

end Main

section Disc

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {d : K} {ψ : E ≃ₐ[K] QuadraticAlgebra K d 0}

variable [NumberField K]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V] [AddCommGroup V']
  [Module E V'] [FiniteDimensional E V']

end Disc

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] {ι : Type*} [Fintype ι] [DecidableEq ι]



omit [Fintype ι] [DecidableEq ι] in

theorem IsHermitianFor.map {s : A →+* A} {t : B →+* B} (φ : A →+* B) (hφ : ∀ x, φ (s x) = t (φ x))
    {H : Matrix ι ι A} (hH : IsHermitianFor s H) : IsHermitianFor t (H.map φ) := by
  unfold IsHermitianFor at *
  conv_rhs => rw [← hH]
  ext i j
  simp [hφ]

end Transport

section Split

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]


def sqSplitEquiv (h2 : (2 : F) ≠ 0) {d r : F} (hr : r ≠ 0) (hd : r ^ 2 = d) :
    QuadraticAlgebra F d 0 ≃+* F × F where
  toFun z := (z.re + r * z.im, z.re - r * z.im)
  invFun p := ⟨(p.1 + p.2) / 2, (p.1 - p.2) / (2 * r)⟩
  left_inv z := by
    ext <;> simp <;> field_simp <;> ring
  right_inv p := by
    ext <;> simp <;> field_simp <;> ring
  map_mul' z w := by
    subst hd
    ext <;> simp <;> ring
  map_add' z w := by
    ext <;> simp <;> ring



end Split

section OfGram

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HermitianForm.ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) : HermitianForm F A (ι → A) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F A) (RingHom.id A)
    (fun x y => ∑ i, ∑ j, conj F A (x i) * H i j * y j)
    (fun x x' y => by
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  isSymm := ⟨fun x y => by
    simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : conj F A (H j i) = H i j := congrFun (congrFun hH i) j
    rw [this]
    ring⟩
  nonsingular := by
    refine bijective_of_injective_sesq _ ?_
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hv : Matrix.vecMul (fun i => conj F A (x i)) H = 0 := by
      funext j
      have := LinearMap.congr_fun hx (Pi.single j 1)
      rw [LinearMap.mk₂'ₛₗ_apply] at this
      simpa [vecMul, dotProduct, Pi.single_apply] using this
    have hinj := (Matrix.vecMul_injective_iff_isUnit (A := H)).2
      ((Matrix.isUnit_iff_isUnit_det H).2 hu)
    have h0 := hinj (hv.trans (Matrix.zero_vecMul H).symm)
    funext i
    have := congrFun h0 i
    rw [← conj_conj (F := F) (x i), this]
    simp

theorem HermitianForm.ofGram_apply (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) (x y : ι → A) :
    (HermitianForm.ofGram H hH hu).toSesq x y = ∑ i, ∑ j, conj F A (x i) * H i j * y j :=
  rfl

theorem gram_ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) :
    gram (HermitianForm.ofGram H hH hu).toSesq (Pi.basisFun A ι) = H := by
  ext i j
  rw [gram_apply, HermitianForm.ofGram_apply]
  simp [Pi.single_apply]


end OfGram

section LocalField

variable {F A : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A] [Algebra.IsSeparable F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


end LocalField

section Diagonal

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]



end Diagonal

end GroundTheory.Automorphic
end
end
