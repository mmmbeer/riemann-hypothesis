import Formalism.WachLatticeTwists.RealClassMaps.Statement
import Formalism.WachLatticeTwists.TorsionKernelSplitting.WachTwistSplitTheoremHZero

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

section Defs
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

def zcRow (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T') :
    Submodule O (Γ → T₂) :=
  (Z1 D.ρTl').comap (v.toLinearMap.compLeft Γ)

def clsRowV (D : LatData O Γ VT VT') {V₂ : Type} [AddCommGroup V₂] [Module O V₂] (w : V₂ ≃ₗ[O] VT')
    (f : Γ → V₂) : H1 D.ρT' := by
  classical
  exact if h : (fun g => w (f g)) ∈ Z1 D.ρT' then Submodule.Quotient.mk ⟨_, h⟩ else 0

def gRow (D : LatData O Γ VT VT') {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [TopologicalSpace T₁]
    [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O Γ T₁) (π : T₁ →ₗ[O] T₂) (v : T₂ ≃ₗ[O] D.T')
    (hc : Continuous fun t => v (π t)) (he : ∀ g t, v (π (ρ₁ g t)) = D.ρTl' g (v (π t))) :
    H1 ρ₁ →ₗ[O] H1 D.ρTl' :=
  mapH1 ρ₁ D.ρTl' (v.toLinearMap ∘ₗ π) hc he

end Defs

def StatKRowRange : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (M : Type) [AddCommGroup M] [Module O M] (ρM : Representation O G M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)), IsOpen (D.T : Set VT) →
    LinearMap.range (kRow D ρM u hu) = lcH1 ρM

def StatResLC : Prop :=
  ∀ (O G M : Type) [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (Dw : Subgroup G),
    lcH1 ρ ≤ (lcH1 (resRep ρ Dw)).comap (resH1 ρ Dw)

def StatClassMapReal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (T₂ : Type) [AddCommGroup T₂] [Module O T₂] (ρ₂ : Representation O G T₂) (v : T₂ ≃ₗ[O] D.T'),
    (∀ g t, v (ρ₂ g t) = D.ρTl' g (v t)) → ∀ Fs : Submodule O (H1 D.ρTl'),
    IsClassMap ρ₂ (zcRow D v) (clsRow D v) Fs

def StatClsVReal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (T₂ V₂ : Type) [AddCommGroup T₂] [Module O T₂] [AddCommGroup V₂] [Module O V₂]
    (ρV : Representation O G V₂) (iV : T₂ →ₗ[O] V₂) (v : T₂ ≃ₗ[O] D.T') (w : V₂ ≃ₗ[O] VT'),
    (∀ t, w (iV t) = (v t : VT')) → (∀ g x, w (ρV g x) = D.ρT' g (w x)) →
    ∀ a ∈ zcRow D v, D.j' (clsRow D v a) = clsRowV D w (fun g => iV (a g)) ∧
      (clsRowV D w (fun g => iV (a g)) = 0 → (fun g => iV (a g)) ∈ coB1 ρV)

def StatPsiCont : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (A : Type) [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
    (Y : Submodule A A), PadicCoeff p O → IsFGTop O A → ∀ ψ : Y →ₗ[O] KO O, Continuous ψ

end Formalism.RepresentationBoundsCohomology.FIN
