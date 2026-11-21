import Mathlib

open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorProductAction

section Defs

variable (Λ : Type) [CommRing Λ] (O : Type) [CommRing O] [Algebra Λ O]

noncomputable def tensorAction (R : Type) [CommRing R] [Algebra Λ R]
    (T : Type) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower Λ O T] :
    R ⊗[Λ] O →ₐ[R] Module.End R (R ⊗[Λ] T) :=
  Algebra.TensorProduct.lift (Algebra.ofId R _)
    ((Module.End.baseChangeHom Λ R T).comp (Algebra.lsmul Λ Λ T))
    (fun r _ => Algebra.commute_algebraMap_left r _)

@[reducible] noncomputable def tensorModule (R : Type) [CommRing R] [Algebra Λ R]
    (T : Type) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower Λ O T] :
    Module (R ⊗[Λ] O) (R ⊗[Λ] T) :=
  Module.compHom (R ⊗[Λ] T) (tensorAction Λ O R T).toRingHom

noncomputable def act (R : Type) [CommRing R] [Algebra Λ R]
    (X : Type) [AddCommGroup X] [Module R X] [Module (R ⊗[Λ] O) X]
    [IsScalarTower R (R ⊗[Λ] O) X] (a : O) : X →ₗ[R] X :=
  Algebra.lsmul R R X ((1 : R) ⊗ₜ[Λ] a : R ⊗[Λ] O)

variable {Λ O}
variable {R : Type} [CommRing R] [Algebra Λ R] (C : Type) [Field C] [Algebra R C]
  (τ : O →ₐ[Λ] R)
  (X : Type) [AddCommGroup X] [Module R X] [Module (R ⊗[Λ] O) X] [IsScalarTower R (R ⊗[Λ] O) X]

noncomputable def coeigen : Submodule C (C ⊗[R] X) :=
  Submodule.span C
    {z | ∃ (a : O) (y : C ⊗[R] X),
      z = (act Λ O R X a).baseChange C y - algebraMap R C (τ a) • y}

noncomputable def toEigen : X →ₗ[R] (C ⊗[R] X) ⧸ coeigen C τ X :=
  ((coeigen C τ X).mkQ.restrictScalars R).comp (TensorProduct.mk R C X 1)

noncomputable def eigenQuot : Submodule R ((C ⊗[R] X) ⧸ coeigen C τ X) :=
  LinearMap.range (toEigen C τ X)

noncomputable def evalAt : R ⊗[Λ] O →+* R :=
  (Algebra.TensorProduct.lift (AlgHom.id R R) τ (fun _ _ => Commute.all _ _)).toRingHom

end Defs

example (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k l] :
    IsLocalRing (WittVector l k) ∧
    Function.Surjective
      (WittVector.constantCoeff.comp (RingHom.id (WittVector l k)) : WittVector l k →+* k) ∧
    (l : WittVector l k) ∈ (WittVector l k)⁰ := by
  refine ⟨inferInstance, fun x => ⟨WittVector.teichmuller l x, by simp⟩, ?_⟩
  exact mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)

end GlobalTheory.IndefiniteRowSideFullHecke.TensorProductAction
