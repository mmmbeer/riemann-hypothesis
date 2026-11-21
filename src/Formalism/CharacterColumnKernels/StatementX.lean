import Formalism.CharacterColumnKernels.Statement

open Finset Polynomial

noncomputable section

namespace Formalism.NG

def StatHomQuot : Prop :=
  ∀ (R O M NN : Type*) [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] [AddCommGroup NN] [Module R NN]
    (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R) (n : g → NN),
    Submodule.span R (Set.range n) = ⊤ → (∀ i, ∑ j, Θ i j • n j = 0) →
    (∀ φ : NN →ₗ[R] M, (fun j => φ (n j)) ∈ LinearMap.ker (relMap O M Θ)) ∧
    Function.Injective (fun (φ : NN →ₗ[R] M) (j : g) => φ (n j)) ∧
    Module.length O (NN →ₗ[R] M) ≤ Module.length O (LinearMap.ker (relMap O M Θ))

def matEnd (O M : Type*) [CommRing O] [AddCommGroup M] [Module O M] (d : Type*) [Fintype d]
    [DecidableEq d] : Matrix d d O →+* Module.End O (d → M) where
  toFun A := relMap O M A
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, Matrix.one_apply, ite_smul, Finset.sum_ite_eq]
  map_mul' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    show (∑ j, (A * B) i j • v j) = ∑ k, A i k • ∑ j, B k j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  map_zero' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap]
  map_add' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, add_smul, Finset.sum_add_distrib]

def LatQ {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type*) [Fintype d] [DecidableEq d] (_ρ : R →+* Matrix d d O) : Type _ := d → KO O

section LatQ
variable {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (d : Type*) [Fintype d] [DecidableEq d] (ρ : R →+* Matrix d d O)

instance : AddCommGroup (LatQ O d ρ) := inferInstanceAs (AddCommGroup (d → KO O))
instance : Module O (LatQ O d ρ) := inferInstanceAs (Module O (d → KO O))
instance : Module R (LatQ O d ρ) :=
  Module.compHom (d → KO O) ((matEnd O (KO O) d).comp ρ)

end LatQ

def StatKerHomBlock : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (g d : Type) [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)] (Θ : Matrix g g R),
    Module.length O (LinearMap.ker (matQ O (bigMat ρ Θ))) =
      Module.length O (Coker Θ →ₗ[R] LatQ O d ρ)

def StatKerHomRect : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m g d : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)] (P : Matrix m g R),
    Module.length O (LinearMap.ker (relMap O (KO O)
        (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2))) =
      Module.length O (Coker P →ₗ[R] LatQ O d ρ)

end Formalism.NG
