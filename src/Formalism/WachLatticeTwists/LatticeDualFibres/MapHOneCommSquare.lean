import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

universe u

open ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

def MapHOneCommSquare : Prop :=
  ∀ (R G M M₁ M₂ M₃ : Type u) [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M]
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [IsTopologicalAddGroup M₁]
    [ContinuousConstSMul R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [IsTopologicalAddGroup M₂]
    [ContinuousConstSMul R M₂]
    [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [IsTopologicalAddGroup M₃]
    [ContinuousConstSMul R M₃]
    (ρ : Representation R G M) (ρ₁ : Representation R G M₁) (ρ₂ : Representation R G M₂)
    (ρ₃ : Representation R G M₃)
    (u : M →ₗ[R] M₁) (v : M₁ →ₗ[R] M₃) (u' : M →ₗ[R] M₂) (v' : M₂ →ₗ[R] M₃)
    (hu : Continuous u) (hv : Continuous v) (hu' : Continuous u') (hv' : Continuous v')
    (eu : ∀ g m, u (ρ g m) = ρ₁ g (u m)) (ev : ∀ g m, v (ρ₁ g m) = ρ₃ g (v m))
    (eu' : ∀ g m, u' (ρ g m) = ρ₂ g (u' m)) (ev' : ∀ g m, v' (ρ₂ g m) = ρ₃ g (v' m)),
    (∀ m, v (u m) = v' (u' m)) →
    ∀ x : H1 ρ, mapH1 ρ₁ ρ₃ v hv ev (mapH1 ρ ρ₁ u hu eu x) =
      mapH1 ρ₂ ρ₃ v' hv' ev' (mapH1 ρ ρ₂ u' hu' eu' x)

def StatConnTors : Prop :=
  ∀ (O G T V A : Type u) [CommRing O] [IsDomain O] [Group G] [TopologicalSpace G]
    [AddCommGroup T] [Module O T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul O T]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul O V]
    [AddCommGroup A] [Module O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul O A]
    (ρT : Representation O G T) (ρV : Representation O G V) (ρA : Representation O G A)
    (j : T →ₗ[O] V) (q : V →ₗ[O] A),
    Topology.IsEmbedding j → (∀ g m, j (ρT g m) = ρV g (j m)) → (∀ g m, q (ρV g m) = ρA g (q m)) →
    Function.Surjective q → LinearMap.ker q = LinearMap.range j → ContAction ρV →
    (∀ c : O, c ≠ 0 → Function.Bijective fun v : V => c • v) →
    (∀ a : A, ∃ c : O, c ≠ 0 ∧ c • a = 0) →
    ∃ δ : H0 ρA →ₗ[O] H1 ρT, LinearMap.range δ = Submodule.torsion O (H1 ρT)

end Formalism.RepresentationBoundsCohomology.LOC
