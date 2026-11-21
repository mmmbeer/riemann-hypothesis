import Formalism.AdmissibleDesigns.NonemptyPl
import Formalism.AdmissibleDesigns.DisplayForms
import Formalism.AdmissibleDesigns.RankReductionIdempotentOne
import Formalism.AdmissibleDesigns.FgTopContinuousLinearMap
import Formalism.AdmissibleDesigns.HigherColumnInvariantsBound
import Formalism.AdmissibleDesigns.KernelLengthHigherColumns

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open Formalism.RepresentationBoundsCohomology.SF
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef bcT bcR bcM bcChar ChainHyp ChainAB blockPoly PrimHyp AbsIrr BlockDiagonalIrreducibleAt)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def RealDisplayAllK (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R')
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (Aw : ℕ → ValuationSubring Ω) (pl : ℕ → HeightOneSpectrum (𝓞 Ek))
      (Av : HeightOneSpectrum (𝓞 Ek) → ValuationSubring Ω) (j e' : ℕ → ℕ)
      (what₂ qs : Finset ℕ) (s H0 : ℕ∞) (Sha : ℕ → ℕ∞)
      (cB : ℕ) (cT : Fin (t + 1) → ℕ → ℕ),
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ ((decs Ek Aw) w)))
    let c1 : Fin (t + 1) := ⟨1, by omega⟩

    ∀ (L : Type) [AddCommGroup L] [Module R' L] [Module O L] [SMulCommClass R' O L]
      (tens : L →ₗ[O] KO O →ₗ[O] blockRestrictedRepresentationType bl ρk 0) (v₁ : L) (κ : ∀ l, Fin (j (colIdx l)) → (Ω ≃ₐ[Ek] Ω) → L)
      (V : Type) [AddCommGroup V] [Module R' V] [Module O V] [Module (FractionRing O) V]
      [IsScalarTower O (FractionRing O) V] [SMulCommClass R' (FractionRing O) V]
      (iL : L →ₗ[O] V) (qV : V →ₗ[O] blockRestrictedRepresentationType bl ρk 0)
      (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) ((decs Ek Aw) (colIdx l)))))
      (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) ((decs Ek Aw) (colIdx l))))
      (F : ∀ c w, Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w))))
      (Vo VS : Type) (Io : Vo → Subgroup (Ω ≃ₐ[Ek] Ω)) (IS : VS → Subgroup (Ω ≃ₐ[Ek] Ω))
      (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
      [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
      (ρ₁ : Representation O (Ω ≃ₐ[Ek] Ω) T₁) (ρ₂ : Representation O (Ω ≃ₐ[Ek] Ω) T₂) (inc : T₁ →ₗ[O] R')
      (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O) (lam : blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O)

      (VT VT' : ℕ → Type)
      [∀ w, AddCommGroup (VT w)] [∀ w, Module O (VT w)] [∀ w, TopologicalSpace (VT w)]
      [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul O (VT w)]
      [∀ w, Module (FractionRing O) (VT w)] [∀ w, IsScalarTower O (FractionRing O) (VT w)]
      [∀ w, AddCommGroup (VT' w)] [∀ w, Module O (VT' w)] [∀ w, TopologicalSpace (VT' w)]
      [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul O (VT' w)]
      [∀ w, Module (FractionRing O) (VT' w)] [∀ w, IsScalarTower O (FractionRing O) (VT' w)]
      (Dat : ∀ w, LatData O ((decs Ek Aw) w) (VT w) (VT' w))
      (uD : ∀ w, blockRestrictedRepresentationType bl ρk 0 ≃ₗ[O] (VT w ⧸ (Dat w).T))
      (huD : ∀ w g m, uD w (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ) ((decs Ek Aw) w) g m) = (Dat w).ρA g (uD w m))
      (vD : ∀ w, T₂ ≃ₗ[O] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
      (heD : ∀ w g t, vD w (π (resRep ρ₁ ((decs Ek Aw) w) g t)) = (Dat w).ρTl' g (vD w (π t)))

      (Fs : ∀ w, Submodule O (H1 (Dat w).ρTl')) (Hf₁ : ∀ w, Submodule O (H1 (resRep ρ₁ ((decs Ek Aw) w))))
      (I : ∀ w, Subgroup ((decs Ek Aw) w)) (γQ : ∀ w, (decs Ek Aw) w) (ζ : ℕ → Tc)
      (ζO : ℕ → O) (nQ : ∀ w, (decs Ek Aw) w → ℕ) (u : ι → (Ω ≃ₐ[Ek] Ω) → O)
      (s₀ : ℕ) (y : Oˣ)

      [∀ w, Module (FractionRing O) (H1 (Dat w).ρT)] [∀ w, IsScalarTower O (FractionRing O) (H1 (Dat w).ρT)]
      [∀ w, Module (FractionRing O) (H1 (Dat w).ρT')] [∀ w, IsScalarTower O (FractionRing O) (H1 (Dat w).ρT')]
      (HfW : ∀ w, Submodule (FractionRing O) (H1 (Dat w).ρT))
      (Hf₂ : ∀ w, Submodule (FractionRing O) (H1 (Dat w).ρT')),

    let gR : ∀ w, H1 (resRep ρ₁ ((decs Ek Aw) w)) →ₗ[O] H1 (Dat w).ρTl' :=
      fun w => gRow (Dat w) (resRep ρ₁ ((decs Ek Aw) w)) π (vD w) (hpD w) (heD w)
    let Im : ∀ w, Submodule O (H1 (Dat w).ρTl') := fun w => (Hf₁ w).map (gR w)

    ∀ (Pe : Type) [AddCommGroup Pe] [Module R' Pe] [Module O Pe] [SMulCommClass R' O Pe]
      (ince : Pe →ₗ[R'] R') (eve : Pe →ₗ[O] L) (heve : ∀ a, eve a = ince a • v₁)
      (PE : Type) [AddCommGroup PE] [Module R' PE] [Module O PE] [SMulCommClass R' O PE]
      (incE : PE →ₗ[R'] R') (evE : PE →ₗ[O] ↥(Ideal.span {δO}))
      (hevE : ∀ g a, evE (uElt r χ g • a) = evE a)
      (Hfe₁ : ∀ l : ι, Submodule O (H1z (resRep (uRep O (M := Pe) r χ) ((decs Ek Aw) (colIdx l)))))
      (HfE₁ : ∀ l : ι, Submodule O (H1z (resRep (uRep O (M := PE) r χ) ((decs Ek Aw) (colIdx l)))))
      (HfE₂ : ∀ l : ι,
        Submodule O (H1z (Representation.trivial O ((decs Ek Aw) (colIdx l)) ↥(Ideal.span {δO}))))
      (uz : ∀ l : ι, coZ1s (Representation.trivial O ((decs Ek Aw) (colIdx l)) ↥(Ideal.span {δO}))),

    Function.Injective (algebraMap ℤ_[ℓ] O) → PadicCoeff ℓ O → FracTop O → IsFGTop O R' → IsCycG ℓ ε →
    Continuous inc → (Continuous fun g : (Ω ≃ₐ[Ek] Ω) => uElt r χ g) →
    (∀ v, IsPlaceOver (Av v) v) → (ℓ ≠ 2 ∨ InfinitePlace.nrRealPlaces Ek = 0) →
    1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ((ε gI : Oˣ) : O) - 1 = (ℓ : O) ^ s₀ * (y : O) →

    Function.Surjective eve → Function.Surjective evE → (∀ a, ∃ c : R', incE a = c * E) →
    (∀ a (m : blockRestrictedRepresentationType bl ρk c1), incE a • m = ((evE a : ↥(Ideal.span {δO})) : O) • m) →

    (∀ l (g : (decs Ek Aw) (colIdx l)),
      (((uz l : (decs Ek Aw) (colIdx l) → ↥(Ideal.span {δO})) g : ↥(Ideal.span {δO})) : O) = δO * u l g) →
    (∀ l, Submodule.mkQ _ (uz l) ∈ HfE₂ l) →

    (∀ l, LiftO ℓ (Hfe₁ l) (Ff l)
      (mapH1 _ _ eve (ev_equiv r χ ((decs Ek Aw) (colIdx l)) ince v₁ eve heve)) (e' (colIdx l))) →
    (∀ l, LiftO ℓ (HfE₁ l) (HfE₂ l)
      (mapH1 _ _ evE (ev_equiv_triv r χ ((decs Ek Aw) (colIdx l)) evE hevE)) (e' (colIdx l))) →

    (∀ x', p x' ∉ Z →
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : (Ω ≃ₐ[Ek] Ω), ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ Lx : Submodule (FractionRing O) ((decs Ek Aw) (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l))) ≤ Lx ∧
        (∀ (f : Pe →ₗ[R'] EvalSp O d R' x')
          (z : coZ1s (resRep (uRep O (M := Pe) r χ) ((decs Ek Aw) (colIdx l)))), Submodule.mkQ _ z ∈ Hfe₁ l →
          (fun g : (decs Ek Aw) (colIdx l) => f ((z : (decs Ek Aw) (colIdx l) → Pe) g)) ∈ Lx) ∧
        (∀ (f : PE →ₗ[R'] EvalSp O d R' x')
          (z : coZ1s (resRep (uRep O (M := PE) r χ) ((decs Ek Aw) (colIdx l)))), Submodule.mkQ _ z ∈ HfE₁ l →
          (fun g : (decs Ek Aw) (colIdx l) => f ((z : (decs Ek Aw) (colIdx l) → PE) g)) ∈ Lx) ∧
        Module.rank (FractionRing O)
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l)))).comap
              Lx.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l)))) : ℕ))) →

    InRhoFixReal2 (blockRestrictedRepresentationType bl ρk 0) r χ e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam →

    (∀ w ∈ what₂, (Aw w).valuation (ℓ : Ω) < 1 ∧ IsPlaceOver (Aw w) (pl w) ∧
      (∀ g : (decs Ek Aw) w, (Dat w).ε g = ε g) ∧ RealLat (Dat w) ∧
      (∀ (g : (decs Ek Aw) w) t, vD w (ρ₂ g t) = (Dat w).ρTl' g (vD w t)) ∧
      (∀ t m, γ t m = pairKO (Dat w).bT (Dat w).T (uD w m) (vD w t)) ∧
      (∀ a, a ∈ HfW w ↔ ∀ b ∈ Hf₂ w, cupFG (Dat w) a b = 0) ∧
      F 0 w = (((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w)) ∧
      Fs w = ((Hf₂ w).restrictScalars O).comap (Dat w).j' ∧ Im w ≤ Fs w) →

    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ ((decs Ek Aw) w))) ≤ H0) ∧
      (∀ w ∈ what₂, F c w = ⊥ ∧
        cT c w ≤ cB ∧
        (∀ ψ : Ymod r χ E →ₗ[O] blockRestrictedRepresentationType bl ρk c, (∀ g ∈ (decs Ek Aw) w, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
          ∀ z : coZ1s (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)),
            (∀ g : (decs Ek Aw) w, (z : (decs Ek Aw) w → blockRestrictedRepresentationType bl ρk c) g = ψ (yY r χ E (g : (Ω ≃ₐ[Ek] Ω)))) →
            ((ℓ : O) ^ cT c w) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w))) ∈ F c w) ∧
        Module.length O (↥(lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c w) ((ℓ : O) ^ cT c w)) ⧸ (F c w).comap (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c w) ((ℓ : O) ^ cT c w)).subtype) ≤
          eO * (cT c w : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 1)) ∧
      InChiFixReal (blockRestrictedRepresentationType bl ρk c) r χ E colIdx (decs Ek Aw) what₂ qs
        (Sha ((c : ℕ) - 1)) (F c) Io IS I γQ ζ ζO nQ) →

    ((∀ l, ∀ g ∈ I (colIdx l), u l (g : (Ω ≃ₐ[Ek] Ω)) = 0) ∧ (∀ l, ∃ g ∈ (decs Ek Aw) (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     (∀ w ∈ what₂, F c1 w = lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓
         unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ((Ine (F := Ek) (Aw w)).subgroupOf ((decs Ek Aw) w)) ∧
       cT c1 w ≤ cB ∧
       (∀ ψ : Ymod r χ E →ₗ[O] blockRestrictedRepresentationType bl ρk c1, (∀ g ∈ (decs Ek Aw) w, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
         ∀ z : coZ1s (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)),
           (∀ g : (decs Ek Aw) w, (z : (decs Ek Aw) w → blockRestrictedRepresentationType bl ρk c1) g = ψ (yY r χ E (g : (Ω ≃ₐ[Ek] Ω)))) →
           ((ℓ : O) ^ cT c1 w) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w))) ∈ F c1 w) ∧
       Module.length O (↥(lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c1 w) ((ℓ : O) ^ cT c1 w)) ⧸ (F c1 w).comap (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c1 w) ((ℓ : O) ^ cT c1 w)).subtype) ≤
         eO * (cT c1 w : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 1)) ∧
     InChiLoc (blockRestrictedRepresentationType bl ρk c1) r χ E (decs Ek Aw) qs (F c1) Io IS I γQ ζ ζO nQ ∧

     (∀ v, (∃ a, Ine (F := Ek) (Av v) ≤ Io a) ∨ (∃ a, Ine (F := Ek) (Av v) ≤ IS a) ∨
        ∃ w ∈ what₂ ∪ qs ∪ univ.image colIdx, ∃ J : Subgroup ((decs Ek Aw) w),
          F c1 w ≤ unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) J ∧
          Ine (F := Ek) (Av v) ≤ J.map ((decs Ek Aw) w).subtype)) →
    (lhs ≤
      ∑ w ∈ what₂, Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype) +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + eO * (padicValNat ℓ (classNumber Ek) : ℕ∞) +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)) ∧
    vδ = eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) ∧
    vδ ≤ eO * ((t * s₀ + padicValNat ℓ t.factorial : ℕ) : ℕ∞)

end Formalism.MainNotions.N.K
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open Formalism.RepresentationBoundsCohomology.SF
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open Formalism.RepresentationBoundsCohomology.T2
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef bcT bcR bcM bcChar ChainHyp ChainAB blockPoly PrimHyp AbsIrr BlockDiagonalIrreducibleAt)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem realDisplayAllK_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayAllK ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ t ht bl ρk δO ε gI lhs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcard1, -, -, -, -, -, -, hOne0⟩ := hR
  obtain ⟨p1, -, -, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha cB cT cols eO vδ N h0 c1
    L _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ ince eve heve PE _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne

  obtain ⟨f1, f2, f3, f4, f6, f7, f8, f9, f11⟩ := hFix
  have hres : ∀ (c : Fin (t + 1)) (w : ℕ), lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ≤
      (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))).comap
        (resH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)) :=
    fun c w => resLC O _ _ (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)
  have hFix2 : InRhoFixReal (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz
      (lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ)) (F 0) Io ε ρ₁ ρ₂ inc π γ lam Dat uD huD vD Fs Im := by
    refine ⟨f1, f2, f3, f4, fun w hw => ?_, f6, f7, f8, f9, fun w hw => ?_, f11⟩
    · rw [kRowRange O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w) (hRows w hw).2.2.2.1.openT]
      exact hres 0 w
    · exact inRowReal_of ℓ r χ E (decs Ek Aw w) ρ₁ inc π (Dat w) (vD w) (hpD w) (heD w) (Fs w) (Hf₁ w) hO hA hinc
        (hur.comp continuous_subtype_val) (hRows w hw).2.2.2.2.2.2.2.2.2
  have hk : ∀ w, Function.Injective (kRow (Dat w) _ (uD w) (huD w)) :=
    fun w => kRowInj O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w)
  have hcycw : ∀ w, IsCycOn ℓ (decs Ek Aw w) (ε.comp (decs Ek Aw w).subtype) :=
    fun w g n ζ h => hcyc g.1 n ζ h
  have hnu : ¬ IsUnit (ℓ : O) := fun h => (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hO.p_mem)) h
  have hKO : ∀ c : Fin (t + 1), c ≠ 0 → Nonempty (blockRestrictedRepresentationType bl ρk c ≃ₗ[O] KO O) :=
    fun c hc => blk_ko bl ρk c (hcard1 c hc)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hFix2
  have key : ∀ w, w ∈ what₂ →
      ∃ (pr : LinearMap.range (kRow (Dat w) _ (uD w) (huD w)) →ₗ[O] H1 (Dat w).ρTl' →ₗ[O] KO O)
      (pair : H1 (Dat w).ρT →ₗ[FractionRing O] H1 (Dat w).ρT' →ₗ[FractionRing O] FractionRing O),
      BKIn (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (qK (Dat w) _ (hk w)) (Dat w).j' pr pair (HfW w) (Hf₂ w)
        ((((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w))) (Fs w) ∧
      InRowRhoNoBK (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ
        (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (clsRow (Dat w) (vD w)) pr (Fs w) (Im w) := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hRows w hw
    exact rowRhoReal ℓ O (VT w) (VT' w) Ek Ω (Aw w) a1 R' Tc (blockRestrictedRepresentationType bl ρk 0) r χ E ε T₁ T₂ ρ₁ ρ₂ inc π γ
      (Dat w) (uD w) (huD w) (vD w) (HfW w) (Hf₂ w) (Fs w) (Im w) hO hFr hA (hcycw w) a3 a4 e8 a5 a6 a7 a9
      (e10 w hw) (hk w)
  choose! pr pair hpp using key
  let HcG : ∀ c : Fin (t + 1), Submodule O (H1z (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)) :=
    fun c => lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)
  let HcR : ∀ (c : Fin (t + 1)) (w : ℕ),
      Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))) := fun c =>
    Fin.cases (motive := fun c => ∀ w : ℕ,
        Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))))
      (fun w => LinearMap.range (kRow (Dat w) _ (uD w) (huD w)))
      (fun c' w => lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c'.succ) r χ) (decs Ek Aw w))) c
  have hBK' : ∀ w ∈ what₂, BKIn (HcR 0 w) (qK (Dat w) _ (hk w)) (Dat w).j' (pr w) (pair w) (HfW w) (Hf₂ w)
      (F 0 w) (Fs w) := by
    intro w hw
    rw [(hRows w hw).2.2.2.2.2.2.2.1]
    exact (hpp w hw).1
  have hFix' : InRhoFix (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (HcG 0)
      (HcR 0) (F 0) Io ε ρ₁ ρ₂ inc π γ lam (fun w => clsRow (Dat w) (vD w)) pr Fs Im :=
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, fun w hw => (hpp w hw).2, e11⟩
  obtain ⟨a1, a2, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, a7, a8, a9, a10, a11, a12, a13⟩ := hFix'

  choose Kc Kz hKc1 hKc2 hKc3 using fun l => colK O R' Tc (Ω ≃ₐ[Ek] Ω) Pe L r χ (decs Ek Aw (colIdx l)) ince v₁ eve heve hse
    (Hfe₁ l) (Ff l) ℓ (e' (colIdx l)) (j (colIdx l)) (κ l) (κz l) (c8 l).1 (c8 l).2.2.1 (hLe l)
  choose k0 kz hk01 hk02 hk03 hk04 using fun l => colk O R' Tc (Ω ≃ₐ[Ek] Ω) PE (blockRestrictedRepresentationType bl ρk c1) r χ E δO (decs Ek Aw (colIdx l)) incE
    evE hincE hact hevE hsE (HfE₁ l) (HfE₂ l) ℓ (e' (colIdx l)) (u l) (uz l) (huz l) (hu l) (hLE l)
  have hcont : ∀ (c : Fin (t + 1)) φ, Submodule.mkQ _ (colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ
      (fun l => decs Ek Aw (colIdx l)) (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG c :=
    fun c φ => colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ
  have hRowsA : ∀ w ∈ what₂, InRowRho (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ (HcR 0 w) (F 0 w)
      (clsRow (Dat w) (vD w)) (pr w) (Fs w) (Im w) := by
    intro w hw
    obtain ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7⟩ := a12 w hw
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hBK' w hw
    exact ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7,
      rowBK O _ (HcR 0 w) (H1 (Dat w).ρT) (H1 (Dat w).ρTl') (H1 (Dat w).ρT') (qK (Dat w) _ (hk w)) (Dat w).j'
        (pr w) (pair w) (HfW w) (Hf₂ w) (F 0 w) (Fs w) f2 f3 f4 f5 f6 f7⟩

  have hC' : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      InChi (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx (decs Ek Aw) j Kc k0 ℓ cB what₂ qs (fun w => ReciprocityTheory.Gal.locDeg (pl w))
        (cT c) (Sha ((c : ℕ) - 1)) (HcG c) (HcR c) (F c) Io IS I γQ ζ ζO nQ := by
    intro c hc2
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    obtain ⟨c', rfl⟩ : ∃ c', c = Fin.succ c' := ⟨c.pred hc0, (Fin.succ_pred _ _).symm⟩
    obtain ⟨-, hrw, ⟨i1, i3, i4⟩, i5⟩ := hC _ hc2
    refine ⟨fun w hw => ⟨?_, (hrw w hw).2.1, (hrw w hw).2.2.1, (hrw w hw).2.2.2⟩, i1, hcont _, fun w _ => hres _ w,
      i3, i4, i5⟩
    rw [(hrw w hw).1]
    exact bot_le
  obtain ⟨o4, o5, o6, o7, ⟨i1, i3, i4⟩, o10⟩ := hOne
  have hc1 : c1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [c1] at this
  have hOneA : InChi (blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ colIdx (decs Ek Aw) j Kc k0 ℓ cB what₂ qs
      (fun w => ReciprocityTheory.Gal.locDeg (pl w)) (cT c1) (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞))
      (HcG c1) (HcR c1) (F c1) Io IS I γQ ζ ζO nQ := by
    refine ⟨fun w hw => ⟨?_, (o7 w hw).2.1, (o7 w hw).2.2.1, (o7 w hw).2.2.2⟩, i1, hcont _, fun w _ => hres _ w,
      i3, i4, ?_⟩
    · rw [(o7 w hw).1]
      exact inf_le_left
    · refine vhEInChi Ek Ω Av hAv ℓ O hreal R' Tc (blockRestrictedRepresentationType bl ρk c1) (hKO _ hc1) r χ p1
        (decs Ek Aw) (what₂ ∪ qs ∪ univ.image colIdx) (HcG c1) (F c1) Vo VS Io IS ?_ o10
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, rfl, hc⟩
  obtain ⟨hv1, hv2⟩ := theorem_n_five_delta_clause O ℓ Fact.out hnu s₀ hs1 hs2 (ε gI) y u₁ hε t
  refine ⟨?_, ?_, ?_⟩
  · exact hF ι colIdx hinj (decs Ek Aw) j e' Kc k0
      (fun x' hx' => by
        obtain ⟨q5, q6⟩ := hrat0 x' hx'
        refine ⟨q5, fun l => ?_⟩
        obtain ⟨Lx, w1, w2, w3, w4⟩ := q6 l
        exact ⟨Lx, w1, fun a s _ => colFun O R' Tc (Ω ≃ₐ[Ek] Ω) Pe (EvalSp O d R' x') r χ (decs Ek Aw (colIdx l)) ince
            (Hfe₁ l) (Lx : Set _) w2 (Kc l a) (Kz l a) (hKc1 l a) (hKc2 l a) s,
          fun s _ => colFun O R' Tc (Ω ≃ₐ[Ek] Ω) PE (EvalSp O d R' x') r χ (decs Ek Aw (colIdx l)) incE (HfE₁ l)
            (Lx : Set _) w3 (k0 l) (kz l) (hk01 l) (hk02 l) s, w4⟩)
      ℓ cB what₂ qs (fun w => ReciprocityTheory.Gal.locDeg (pl w)) s (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞)) H0 Sha
      (fun l g => hk03 l g) L tens v₁ κ HcG HcR F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂
      inc π γ lam (fun w => H1 (Dat w).ρTl') (fun w => clsRow (Dat w) (vD w)) pr Fs Im cT I γQ ζ ζO nQ u
      (inputs_from_selmer_inj O R' Tc (Ω ≃ₐ[Ek] Ω) (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ ι colIdx (decs Ek Aw) j e' Kc k0 ℓ what₂ s L tens v₁ κ V
        iL qV Ff κz (HcG 0) (HcR 0) (F 0) Vo Io ε T₁ T₂ ρ₁ ρ₂ inc π γ lam (fun w => H1 (Dat w).ρTl')
        (fun w => clsRow (Dat w) (vD w)) pr Fs Im
        ⟨a1, a2, fun l a g hg => hKc3 l a g hg, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, hcont 0, a7, a8,
          a9, a10, a11, hRowsA, a13⟩)
      (fun c hc2 => ⟨(hC c hc2).1, hC' c hc2⟩)
      ⟨fun l g hg m => hk04 l g hg m, o4, o5, o6, hOneA⟩
  · show IsDiscreteValuationRing.addVal O δO = _
    rw [hδO]
    exact hv1
  · show IsDiscreteValuationRing.addVal O δO ≤ _
    rw [hδO]
    exact hv2

end Formalism.MainNotions.N.K
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG Formalism.MainNotions.N.RepresentationBoundsCohomology

variable {D : D7} (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem normalized_ring_data (hN : NormAt D.nd r ρ π)
    (hG1 : ∀ (γ : GE D.nd) (k : ℕ), (fun x : D.nd.X i => ((rO D.nd i r x γ).charpolyRev).coeff k) ∈ D.nd.T i)
    (hres : Submodule.span (kk D.nd i)
      (Set.range (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π))) = ⊤)
    (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hI : IdemHyp (D.nd.O i) (D.nd.T i) (repX D.nd r) π (blk D.R) eB e₁)
    (hX : DistinctEigenvalueCornerPerturbation (D.nd.O i) (D.nd.T i) (repX D.nd r) π D.R.t g0 eB s) :
    ∃ Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (blk D.R),
      RingDef (D.nd.O i) (D.nd.T i) (repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd ∧
      vcc (D.nd.T i) (D.nd.Z i : Set (D.nd.X i)) (Dd.p Dd.π') =
        Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ∧
      ∃ (_ : IsNoetherian Dd.R' Dd.R')
        (_ : ∀ x', IsScalarTower Dd.T' Dd.R' (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'))
        (_ : ∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (blk D.R) Dd.ρk k))
        (_ : ∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (blk D.R) Dd.ρk k))
        (_ : ∀ k, IsScalarTower (D.nd.O i) Dd.R' (blockRestrictedRepresentationType (blk D.R) Dd.ρk k)),
        Dd.Top (D.nd.T i) (one_le_letterBlockLength D.R) ∧
        ∀ [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
          [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [TopologicalSpace Dd.R']
          [IsTopologicalAddGroup Dd.R'] [ContinuousConstSMul (D.nd.O i) Dd.R'] [ContinuousMul Dd.R'],
          RealDisplayAllK (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
            Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ D.R.t (one_le_letterBlockLength D.R) (blk D.R) Dd.ρk Dd.δO
            (epsU D.nd i) g0 (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)) := by
  obtain ⟨Dd, hD, ⟨i1, i2, -, i4, i5⟩, i3, hT⟩ := ring_objects_exist (D.nd.O i) (D.nd.X i) (D.nd.T i) (Fin D.R.nV) (GE D.nd)
    (repX D.nd r) π D.R.t (one_le_letterBlockLength D.R) (blk D.R) (chiU D.nd i 1) (epsU D.nd i) (primHyp_of D.nd r ρ π hN hG1)
    (absIrr_of_res D.nd r ρ π hN hres) eB e₁ hI g0 s hX
  have hFree := fun Z => displayFree (D.nd.O i) (D.nd.X i) (D.nd.T i) (Fin D.R.nV) (GE D.nd) (repX D.nd r) π D.R.t
    (one_le_letterBlockLength D.R) (blk D.R) (chiU D.nd i 1) (epsU D.nd i) (primHyp_of D.nd r ρ π hN hG1)
    (absIrr_of_res D.nd r ρ π hN hres) eB e₁ hI g0 s hX Dd hD hT Z
  have hp : Dd.p Dd.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD
    exact h
  have hv : vcc (D.nd.T i) (D.nd.Z i : Set (D.nd.X i)) (Dd.p Dd.π') =
      Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) := by
    rw [hp, Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt]
  refine ⟨Dd, hD, hv, i1, i2, i3, i4, i5, hT, ?_⟩
  intro _ _ _ _ _ _ _
  exact realDisplayAllK_of (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
    Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ Dd.δ D.R.t (one_le_letterBlockLength D.R) (blk D.R) Dd.ρk Dd.δO
    (epsU D.nd i) g0 _ (D.nd.T i) Dd.T' Dd.q Dd.b Dd.π' Dd.ρπ Dd.sE Dd.tE (chiU D.nd i 1 g0) hT
    (hFree (D.nd.Z i : Set (D.nd.X i))) (Formalism.RepresentationBoundsCohomology.SF.deltaO_eq hD) hv.symm

end Formalism.MainNotions.N.K

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.St

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
  (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ)

theorem rhoTwo_eq (g : Ω ≃ₐ[Ek] Ω) (y : {a // bl a = 0} → O) :
    rhoTwo (ρk 0) r χ ε g y = KLat.rho2 r χ bl ρk ε g y := by
  simp [rhoTwo, KLat.rho2, KLat.repL', KLat.M0]
  rfl

theorem pi_equiv2 (e₁ : R') (w : {a // bl a = 0} → O) (g : Ω ≃ₐ[Ek] Ω) (b : FirstSummandSubmodule O e₁) :
    piM (ρk 0) e₁ w (firstSummandRep O r χ e₁ ε g b) = KLat.rho2 r χ bl ρk ε g (piM (ρk 0) e₁ w b) := by
  rw [← rhoTwo_eq]
  apply pi_equiv

end Gen

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

variable {D : D7} (i : D.nd.Loc)

instance fracAdd : IsTopologicalAddGroup (FractionRing (D.nd.O i)) := Topo.fracTop_addGroup_O i
instance fracSmul : ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i)) := Topo.fracTop_smul_O i

instance rSmul {D : D7} (i : D.nd.Loc)
    (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)) :
    ContinuousConstSMul (D.nd.O i) Dd.R' := Topo.rTop_constSMul_RD i Dd

section Rec

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Lr : Type := LatM (D.nd.O i) (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev Vr : Type := LatM (D.nd.O i) (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev rho1 := firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)

abbrev rho2 := KLat.rho2 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i)

theorem hKm : ContinuousMul (FractionRing (D.nd.O i)) := by
  infer_instance

theorem hEps : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
  KLat.eps_cont_nf (D.nd.l i) (Topo.padicCoeff_O i) (epsU D.nd i) (Topo.isCyc_eps i)

theorem hM0 (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) :
    ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KLat.block_zero_continuous Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (Topo.padicCoeff_O i) (Topo.fgTop_RD i r π g0 eB e₁ s Dd hD)
    (Topo.uElt_cont i r π g0 eB e₁ s Dd hD hc)

variable (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

abbrev DatS (w : ℕ) := KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev uDS (w : ℕ) := KLat.uD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev vDS (w : ℕ) := KLat.vD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev modS (w : ℕ) := KLat.modT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev modS' (w : ℕ) := KLat.modT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

theorem huDS (w : ℕ) (g : decs D.host.E (Aw i dc) w) (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :
    uDS i r π dc g0 eB e₁ s Dd hD hc w
        (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ) ((decs D.host.E (Aw i dc)) w) g m) =
      (DatS i r π dc g0 eB e₁ s Dd hD hc w).ρA g (uDS i r π dc g0 eB e₁ s Dd hD hc w m) :=
  KLat.huD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w g m

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

abbrev piS := piDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk

theorem hpDS (w : ℕ) :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    Continuous fun t => vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk t) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KLat.hpD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (piS i Dd hT hrk)
    (piM_cont (Topo.padicCoeff_O i) (Topo.fgTop_RD i r π g0 eB e₁ s Dd hD) (Dd.ρk 0) Dd.e₁
      (wDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk)) (Topo.fracTop_O i) w

theorem heDS (w : ℕ) (g : decs D.host.E (Aw i dc) w) (t : FirstSummandSubmodule (D.nd.O i) Dd.e₁) :
    vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk (resRep (rho1 i Dd) ((decs D.host.E (Aw i dc)) w) g t)) =
      (DatS i r π dc g0 eB e₁ s Dd hD hc w).ρTl' g (vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk t)) :=
  KLat.heD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (rho1 i Dd) (piS i Dd hT hrk)
    (fun g x => pi_equiv2 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) Dd.e₁ _ g x) w g t

abbrev v1S := v1Dd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk
abbrev eveS := eveDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk
abbrev evES := evEDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT
abbrev lamS := lamDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk

theorem hevES (g : GE D.nd) (a : LeftId (D.nd.O i) Dd.E) :
    evES i Dd hT (uElt Dd.r Dd.χ g • a) = evES i Dd hT a :=
  evEM_inv Dd.r Dd.χ _ _ _ _ (top_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT).2.2.2.2 g a

end Rec

end Formalism.MainNotions.N.K.St

end
end
