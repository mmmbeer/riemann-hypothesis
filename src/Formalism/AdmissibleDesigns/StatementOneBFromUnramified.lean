import Formalism.AdmissibleDesigns.BKaClause
import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
import Formalism.AdmissibleDesigns.TheoremFromNormalizedOpenThree
import Formalism.AdmissibleDesigns.LocRepTriv
import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.AdmissibleDesigns.LocCont
import Formalism.AdmissibleDesigns.TheoremN5OfNormalizedItems
import Formalism.AdmissibleDesigns.IsDROfWpIso
import Formalism.AdmissibleDesigns.MemIntegralSpanIffImage
import Formalism.AdmissibleDesigns.UnramifiedInputOfAdmitted
import Formalism.AdmissibleDesigns.HRhoFull
import Formalism.AdmissibleDesigns.FirstCharacterIndexNeZero
import Formalism.AdmissibleDesigns.RowDROfWpIso
import Formalism.AdmissibleDesigns.RhoContOf
import Formalism.AdmissibleDesigns.RowTopOf
import Formalism.AdmissibleDesigns.FiniteClassesLocalEq
import Formalism.AdmissibleDesigns.EKSymmCont
import Formalism.AdmissibleDesigns.PiEquiv2
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseLin
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BlochKatoAnnihilatorAboveL
import Development.AutomorphicArithmetic.ResidueCharacters.LenLeTorsion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLattices
import Formalism.AdmissibleDesigns.AdmG5OfAdm51AdmG5
import Formalism.SharpRestriction.LevelLetterCocycles.QpowOfTw
import Formalism.SharpRestriction.LevelLetterCocycles.WildPro

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KHf

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem exists_Lx {Pe : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    {PE : Type} [AddCommGroup PE] [Module R' PE] [Module (D.nd.O i) PE] [SMulCommClass R' (D.nd.O i) PE]
    (hPe : ∀ (c : D.nd.O i) (m : Pe), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (hPE : ∀ (c : D.nd.O i) (m : PE), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (j : ℕ → ℕ) (x' : X') (l : K.Col i dc)
    (hO : letI := evalModO i (R' := R') x'
      haveI := evalTower i (R' := R') x'
      OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)))
    (hdim : DimLx i dc r χ j x' l) :
    ∃ Lx : Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc (K.colIdx i dc l)) → EvalSp (D.nd.O i) d R' x'),
      LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
        (Γn i dc (K.colIdx i dc l))) ≤ Lx ∧
      (∀ (f : Pe →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := Pe) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → Pe) g)) ∈ Lx) ∧
      (∀ (f : PE →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := PE) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := PE) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → PE) g)) ∈ Lx) ∧
      Module.rank (FractionRing (D.nd.O i))
          (Lx ⧸ (LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))).comap Lx.subtype) ≤
        (j (K.colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
          (LinearMap.ker (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))) : ℕ) := by
  refine ⟨Lx i dc r χ x' l, ?_, ?_, ?_, hdim⟩
  · apply colD_le_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption

end Formalism.MainNotions.N.KHf

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem contW_rec (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l :=
  contW_of i dc ρ π (K.Norm.rhoCont_of i r ρ π hd hc) l

end Formalism.MainNotions.N.KOrb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StA

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1
  omega

theorem card_pos (D : D7) : 0 < Fintype.card (Fin D.R.nV) := by
  rw [Fintype.card_fin]
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1 + D.R.t
  omega

theorem jN_eq {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (dc : TruncatedSeriesCountingIdentities.Decl D i) : jN i ρ π dc = KHf.jK i dc ρ π := rfl

theorem leftId_alg {O : Type} [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A) (c : O) (m : LeftId O x) :
    c • m = (algebraMap O A c) • m := by
  exact Subtype.ext (Algebra.smul_def c m.1)

section Cols

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem colUz : ∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
    (((KFin.uz i dc Dd.δO l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g :
      ↥(Ideal.span {Dd.δO})) : D.nd.O i) = Dd.δO * KFin.u i dc l g := by
  intro l g
  first
  | (show Dd.δO * KFin.uCol i dc l g = Dd.δO * KFin.u i dc l g
     rw [KFin.u, dif_pos (show ((g : GE D.nd)) ∈ KFin.Γc i dc l from g.2)])
  | (simp [KFin.uz, KFin.uzOf, KFin.u, g.2])


theorem column_unramified_character : (∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), KFin.u i dc l (g : GE D.nd) = 0) ∧
    (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), KFin.u i dc l g = 1) :=
  ⟨fun l => KFin.u_I i dc l (KUnr.unrHom i dc l), fun l => KFin.u_one i dc l (KUnr.unrHom i dc l)⟩

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem colLx_of_ringDef
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCr : ∀ x' l, KDim.CrysX i dc Dd.r Dd.χ x' l) (hNeg : ∀ x' l, KDim.NegX i dc Dd.r Dd.χ ρ π x' l)
    (hFin : ∀ x' l, KDim.FinX i dc Dd.r Dd.χ x' l) (hCrW : ∀ l, KDim.CrysW i dc ρ π l) :
    ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ) := by
  intro x' _ l
  have hO := KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l)
  have hdim : KHf.DimLx i dc Dd.r Dd.χ (KHf.jK i dc ρ π) x' l :=
    KDim.dimLx_of_font i dc Dd.r Dd.χ ρ π r x' l (card_pos D) (r_pos D) hBK hG2 hFont
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l hO) (hCr x' l) (hNeg x' l) (hFin x' l) (hCrW l)
      (KOrb.contW_rec i dc r ρ π hDec hc l)
  rw [jN_eq]
  exact KHf.exists_Lx i dc Dd.r Dd.χ (leftId_alg Dd.e₁) (leftId_alg Dd.E) (KHf.jK i dc ρ π) x' l hO hdim

end Cols

end Formalism.MainNotions.N.K.StA

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StA

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Cols2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem colLx
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) :
    ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ) := by
  have hρ := K.Norm.rhoCont_of i r ρ π hDec hc
  refine colLx_of_ringDef i r ρ π dc g0 eB e₁ s Dd hD hc hBK hG2 hFont hDec
    (fun x' l => K.Font.crysX_of (i := i) (dc := dc) (r := r) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s)
      (Dd := Dd) ρ hG2 hD x' l)
    (fun x' l => K.Font.negX_of (i := i) (dc := dc) (r := r) (ρ := ρ) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁)
      (s := s) (Dd := Dd) hFont hG2 hDec hc hρ hD x' l)
    (fun x' l => KTate.finX (i := i) (dc := dc) (r := Dd.r) (χ := Dd.χ) hFin x' l
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l (KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l))))
    (fun l => K.Font.crysW_of (i := i) (dc := dc) (r := r) (ρ := ρ) (π := π) hFont hG2 hDec hc hρ l)

end Cols2

end Formalism.MainNotions.N.K.StA

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Final

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Open

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def ColOpen : Prop :=
  ∃ (κ : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) → GE D.nd → Lr i Dd)
      (κz : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) →
      coZ1s (resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) (colIdx i dc l))))
      (u : Col i dc → GE D.nd → D.nd.O i)
      (uz : ∀ l : Col i dc,
      coZ1s (Representation.trivial (D.nd.O i) ↥(decs D.host.E (Aw i dc) (colIdx i dc l)) ↥(Ideal.span {Dd.δO}))),
      (∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
      (((uz l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g : ↥(Ideal.span {Dd.δO})) :
        D.nd.O i) = Dd.δO * u l g) ∧
      (KHf.UnrFin i dc Dd.δO uz) ∧
      (∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ)) ∧
      (InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk) κ
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) κz (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk)) ∧
      ((∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), u l (g : GE D.nd) = 0) ∧
      (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), u l g = 1))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def TBOpen : Prop :=
      (∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈ FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def ChiOpen : Prop :=
      (∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
      InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
        (qsN i dc) (ShaN i ((c : ℕ) - 1)) (FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
        (QS.ζO i dc) (QS.nQ i dc))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def FirstLocalConditionOpen : Prop :=
      (InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
      (FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc))

end Open

section Final

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem row_bound_normalized_lattice (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (cB : ℕ) (h : EmbeddingTypes.admTB i r π dc cB) :
    EmbeddingTypes.admTB i (Norm.rN i r ρ π) π dc cB := by
  intro w hw hrow C hC
  have ht : Norm.IsConjM ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)) ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (Norm.rN i r ρ π) π)) :=
    Norm.conj_locC i C (Norm.conj_twistM _ (Norm.conjK i r ρ π hd π) _)
  have hset : (fun τ => {a | Formalism.WeaklyAdmissibleFiltrations.IsJumpV (Br.PD D.loc D.nbr i w hw)
      (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (Norm.rN i r ρ π) π))) τ a}) =
      (fun τ => {a | Formalism.WeaklyAdmissibleFiltrations.IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a}) :=
    funext fun τ => Set.ext fun a => ((Norm.jd _ ht).2.2 τ a).symm
  have := h w hw hrow C hC
  rw [← hset] at this
  exact this

variable (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def OnRing (Q : ∀ (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
      (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
      [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
      (_hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i)
        g0 eB e₁ s Dd)
      (_hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π)) (_hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
      (_hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1), Prop) : Prop :=
  TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (Norm.rN i r ρ π) ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i (Norm.rN i r ρ π) dc e' →
    EmbeddingTypes.admTB i (Norm.rN i r ρ π) π dc cB → π ∈ D.nd.Z i →
    ∀ (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
      (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
      [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
      (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i)
        g0 eB e₁ s Dd)
      (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π)) (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
      (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1),
      Q g0 eB e₁ s Dd hD hc hT hrk

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def RemainingInputsRankFive : Prop :=
  OnRing i r ρ π dc lenRow e' cB (fun g0 eB e₁ s Dd _ hD hc hT hrk =>
    ColOpen i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk ∧
    TBOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc cB ∧
    ChiOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    FirstLocalConditionOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    StD.RowDR i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    Sel.RowTie i dc (Norm.rN i r ρ π) ρ π (rowLenS i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc hT hrk))

end Final

section Stmts

end Stmts

section EmbeddingTypes

end EmbeddingTypes

section Land

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)

abbrev UnrIn : Prop := StD.UnrIn i dc

theorem unramified_input_of_admitted (h : EmbeddingTypes.UnramifiedTrivialH1f i dc) : UnrIn i dc := by
  intro w hw hc
  have h1 := h w hw hc (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)
  unfold WeaklyAdmissibleFiltrations.UnrTriv at h1
  exact h1.ge

end Land

section WithCols

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def RhoOpenA : Prop :=
      (InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk) (KFin.κ i dc Dd ρ π)
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) (KFin.κz i dc Dd ρ π) (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk))

end WithCols

section FinalA

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def RemainingInputsAfterColumns : Prop :=
  OnRing i r ρ π dc lenRow e' cB (fun g0 eB e₁ s Dd _ hD hc hT hrk =>
    RhoOpenA i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk ∧
    TBOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc cB ∧
    ChiOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    FirstLocalConditionOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    StD.RowDR i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    Sel.RowTie i dc (Norm.rN i r ρ π) ρ π (rowLenS i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc hT hrk))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem theorem_n5_of_ring_inputs (g1 : TruncatedSeriesCountingIdentities.admG1 i r) (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g3 : TruncatedSeriesCountingIdentities.admG3 i r ρ π) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (g6 : TruncatedSeriesCountingIdentities.admG6 i r) (ct : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (a51 : LargeLevelLemmas.adm51 i r ρ π) (hG : K.SelfGood i)
    (hP : OnRing i r ρ π dc lenRow e' cB (fun g0 eB e₁ s Dd _ hD hc hT hrk =>
      SelmerInequalityThree i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk lenRow cB)) :
    TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB →
      TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hR hL hTB
  have hR' := Norm.row_normalized i r ρ π dcm dc lenRow hR
  have hL' := Norm.lift_normalized i r ρ π dcm dc e' hL
  have hT' := row_bound_normalized_lattice i r ρ π dc dcm cB hTB
  refine H0.theorem_of_display_and_g2 i r ρ π dc lenRow e' cB (fun _ _ hπ _ _ => ?_) g2 g5x
  have hN := Norm.normAt_rN i r ρ π
  have hG1 := Norm.admG1_rN i r ρ π dcm g1
  obtain ⟨g0, -, ⟨u0, hcyc⟩, eB, e₁, s, hI, hX⟩ := Norm.design_normalized_of_admitted i r ρ π a51 hπ
  obtain ⟨Dd, hD, -, i1, i2, i3, i4, i5, hTop, hK⟩ :=
    normalized_ring_data i (Norm.rN i r ρ π) ρ π hN hG1 g3.2.2 g0 eB e₁ s hI hX
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
  have hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π) := Norm.continuity_normalized i r ρ π (Norm.rhoCont_of i r ρ π dcm ct) ct
  exact selmer_inequality_three i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hTop (rank_reduction_idempotent_one Dd hI hD) lenRow e' cB hN
    (RepresentationBoundsCohomology.primHyp_of D.nd (Norm.rN i r ρ π) ρ π hN hG1) u0 hcyc hK (Norm.admG6_rN i r ρ π dcm g6) hL' hG
    (hP hR' hL' hT' hπ g0 eB e₁ s Dd hD hc hTop (rank_reduction_idempotent_one Dd hI hD))

end FinalA

section StmtsA

end StmtsA

section FinalB

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem plugOpen3_B (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (hUn : StD.UnrIn i dc) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (bka : LargeLevelLemmas.BlochKatoAnnihilators i) (hG : K.SelfGood i) (hR : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow)
    (hRho : RhoOpenA i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk) (hTB : TBOpen i r π dc g0 eB e₁ s Dd hD hc cB)
    (hChi : ChiOpen i r π dc g0 eB e₁ s Dd hD hc) (hLoc1 : FirstLocalConditionOpen i r π dc g0 eB e₁ s Dd hD hc)
    (hRT : StD.RowTieIn i r ρ π dc g0 eB e₁ s Dd hD hc) :
    SelmerInequalityThree i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk lenRow cB :=
  ⟨KFin.κ i dc Dd ρ π, KFin.κz i dc Dd ρ π, KFin.u i dc, KFin.uz i dc Dd.δO, StA.colUz i dc Dd,
    StD.unrFin_of i dc Dd.δO hUn, StA.colLx i r ρ π dc g0 eB e₁ s Dd hD hc hBK hG2 hFont hDec hFin, hRho,
    StD.bKa_clause i r π dc g0 eB e₁ s Dd hD hc bka hG (StD.rowDR_of_fontaine i r ρ π dc g0 eB e₁ s Dd hD hc hFont hG2 hDec hN),
    hTB, hChi, StA.column_unramified_character i dc, hLoc1,
    StD.tie_clause i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk lenRow hG hR (StD.row_match_from_comparison i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk hRT)⟩

end FinalB

section FinalB2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def RemainingInputsLastLayer : Prop :=
  OnRing i r ρ π dc lenRow e' cB (fun g0 eB e₁ s Dd _ hD hc hT hrk =>
    RhoOpenA i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk ∧
    TBOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc cB ∧
    ChiOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    FirstLocalConditionOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    StD.RowTieIn i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem theorem_n5_of_open_b (g1 : TruncatedSeriesCountingIdentities.admG1 i r) (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g3 : TruncatedSeriesCountingIdentities.admG3 i r ρ π) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (g6 : TruncatedSeriesCountingIdentities.admG6 i r) (bk : TruncatedSeriesCountingIdentities.admBK i) (bka : LargeLevelLemmas.BlochKatoAnnihilators i) (ct : TruncatedSeriesCountingIdentities.FamilyContinuous i r)
    (dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (font : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (a51 : LargeLevelLemmas.adm51 i r ρ π)
    (unr : StD.UnrIn i dc) (hG : K.SelfGood i) (hO : RemainingInputsLastLayer i r ρ π dc lenRow e' cB) :
    TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB →
      TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hR hL hTB
  refine theorem_n5_of_ring_inputs i r ρ π dc lenRow e' cB g1 g2 g3 g5x g6 ct dcm a51 hG ?_ hR hL hTB
  intro hR' hL' hTB' hZ g0 eB e₁ s Dd _ hD hc hT hrk
  obtain ⟨hRho, hTBo, hChi, hLoc1, hRT⟩ := hO hR' hL' hTB' hZ g0 eB e₁ s Dd hD hc hT hrk
  exact plugOpen3_B i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk lenRow cB bk
    (Norm.admG2_rN (hd := dcm) (h := g2)) font (Norm.decomposes_normalized (i := i) (r := r) (ρ := ρ) (π := π)) fin unr
    (Norm.normAt_rN (i := i) (r := r) (ρ := ρ) (π := π)) bka hG hR' hRho hTBo hChi hLoc1 hRT

end FinalB2

section StmtsB

end StmtsB

end Formalism.MainNotions.N.K.Final

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open Classical Matrix

namespace Formalism.MainNotions.N.K.RowB

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf Formalism.MainNotions.N.KRow NumberField IsDedekindDomain Formalism.NG Formalism.BasicNotions

section Lat

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

theorem phiW_rhoT' (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (g : Br.G D.nbr i _ hn) (v : TrV (eK (D.nbr i _ hn)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n)) (a : Fin D.R.r) :
    Font.phiW i dc n hn (repL (eK (D.nbr i _ hn))
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT' (Br.iota D.nbr i _ hn) g v) a =
    ∑ b, eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) *
        Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹) (H0.e0 b) (H0.e0 a))) *
      Font.phiW i dc n hn v b := by
  show eK (D.nbr i _ hn) ((((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) •
      ((KLat.matK (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹)))ᵀ *ᵥ
        (v : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)))) (H0.e0 a)) = _
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.smul_sum, map_sum]
  refine (Equiv.sum_comp (H0.e0 (D := D)) _).symm.trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [Matrix.transpose_apply, KLat.matK, Matrix.map_apply, Algebra.smul_def, ← mul_assoc, ← map_mul, map_mul]
  rfl

variable {i dc Dd hK hε hM} in

theorem rowMat_at
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsMatLat (ρ := repL (eK (D.nbr i _ hn))
        (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT' (Br.iota D.nbr i _ hn))
      (latT (eK (D.nbr i _ hn)) (D.nbr i _ hn).eO
        (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).T'.subtype (heO_br i dc hn))
      (⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (T2O D.nd i ρ π))) := by
  refine ⟨Font.phiW i dc n hn, fun g v => funext fun a => ?_, fun v => ?_⟩
  · rw [phiW_rhoT']
    show _ = ∑ b, Br.loc D.nbr i _ hn (T2O D.nd i ρ π) g a b * Font.phiW i dc n hn v b
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Font.loc_apply]
    show eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) *
          Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹) (H0.e0 b) (H0.e0 a))) * _ =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) *
          WpO D.nd i ρ π ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹ b a)) * _
    rw [H0.unipotent_block_zero_entry hD hN]
  · rw [KRow.mem_latT]
    constructor
    · rintro ⟨m, rfl⟩ j
      obtain ⟨y, hy⟩ := Submodule.mem_one.1 (m.2 _ (KLat.unit_mem_latT (H0.e0 (D := D) j)))
      refine ⟨(D.nbr i _ hn).eO y, ?_⟩
      rw [heO_br i dc hn, hy]
      show _ = eK (D.nbr i _ hn) ((m : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 j))
      congr 1
      show (fun k => if H0.e0 (D := D) j = k then (1 : FractionRing (D.nd.O i)) else 0) ⬝ᵥ
        (m : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) = _
      simp [dotProduct]
    · intro h
      choose z hz using h
      refine ⟨KLat.vD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n
        (fun b => (D.nbr i _ hn).eO.symm (z ((H0.e0 (D := D)).symm b))), ?_⟩
      funext b
      apply (eK (D.nbr i _ hn)).injective
      show eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        ((D.nbr i _ hn).eO.symm (z ((H0.e0 (D := D)).symm b)))) = eK (D.nbr i _ hn) (v b)
      rw [← heO_br i dc hn, RingEquiv.apply_symm_apply, hz]
      show eK (D.nbr i _ hn) (v (H0.e0 ((H0.e0 (D := D)).symm b))) = _
      rw [Equiv.apply_symm_apply]

variable {i dc Dd hK hε hM} in

theorem orbC_dat (n : ℕ) :
    KHf.OrbC i dc (n := n)
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT' := by
  intro hn v
  have hι : Continuous fun g : Br.G D.nbr i _ hn => ((Br.iota D.nbr i _ hn g : _) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i _ hn)
  have hf : (fun g => repL (eK (D.nbr i _ hn))
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT' (Br.iota D.nbr i _ hn) g v) =
      fun g => (Font.phiW i dc n hn).symm (fun a => ∑ b, eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) *
          Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹) (H0.e0 b) (H0.e0 a))) *
        Font.phiW i dc n hn v b) := by
    funext g
    apply (Font.phiW i dc n hn).injective
    rw [LinearEquiv.apply_symm_apply]
    funext a
    exact phiW_rhoT' i dc Dd hK hε hM n hn g v a
  rw [hf]
  refine (LinearMap.continuous_on_pi (Font.phiW i dc n hn).symm.toLinearMap).comp
    (continuous_pi fun a => continuous_finsetSum _ fun b _ => ((KOrb.eK_alg_cont i hn).comp ?_).mul continuous_const)
  exact (hε.comp hι).mul ((hM (H0.e0 b) (H0.e0 a)).comp (continuous_inv.comp hι))

end Lat

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

theorem rowMat_S (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (St.DatS i r π dc g0 eB e₁ s Dd hD hc) ρ π := by
  intro n _ hn
  exact rowMat_at (hD := hD) (hN := hN) (n := n) (hn := hn) ..

theorem orbC_S : ∀ n ∈ K.rowsN i dc, KHf.OrbC i dc (n := n) (St.DatS i r π dc g0 eB e₁ s Dd hD hc n).ρT' := by
  intro n _
  exact orbC_dat n

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

end Rec

section RecN

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i)
    g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π))
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

theorem rowMat_SN :
    KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (St.DatS i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc) ρ π := by
  exact rowMat_S i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc (Norm.normAt_rN i r ρ π)

end RecN

end Formalism.MainNotions.N.K.RowB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

theorem sub_of_fam {LL : Type} [Field LL] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} {ιx : Type} {k : ℕ}
    {Ms : ιx → G → Matrix (Fin k) (Fin k) LL} {I : Type} (xx : I → ιx)
    (Ψ : I → V →ₗ[LL] (Fin k → LL)) (hinj : ∀ v, (∀ a, Ψ a v = 0) → v = 0)
    (heq : ∀ a g v, Ψ a (ρ g v) = (Ms (xx a) g).mulVec (Ψ a v)) : IsSubOfSums ρ Ms := by
  obtain ⟨m, xs, hxs⟩ := KLift.fin_sel Ψ hinj
  refine ⟨m, xx ∘ xs, LinearMap.pi fun a => Ψ (xs a), fun v w hvw => ?_, fun g v => funext fun a => heq _ g v⟩
  rw [← sub_eq_zero]
  refine hxs _ fun a => ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hvw a

theorem orb_of_sub {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    (h : IsSubOfSums ρ Ms) (hMs : ∀ x, Continuous (Ms x)) (v : V) : Continuous fun g => ρ g v := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := h
  exact KLift.cont_of_inj xs φ hφ heq hMs v

end Gen

section Fin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}




end Fin

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def kap1 : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i]
    (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) where
  toFun p := (((p : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lattice_inclusion_injective : Function.Injective (kap1 i Dd) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem idempotent_part_representation_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (p : FirstSummandSubmodule (D.nd.O i) Dd.e₁) (x' : Dd.X') :
    kap1 i Dd (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i) g p) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 g : D.nd.O i) * ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)) •
        (kap1 i Dd p x' * (rO D.nd i r (Dd.p x') g⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
  show (((((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) • (((Dd.χ g : (Dd.T')ˣ) : Dd.T') •
    ((p : Dd.R') * Dd.r g⁻¹)) : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' = _
  rw [Subalgebra.coe_smul, Pi.smul_apply, hsm, hχ, Subalgebra.coe_mul, Pi.mul_apply, hr', map_mul, mul_smul,
    ← algebraMap_smul (FractionRing (D.nd.O i)) ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i), smul_comm]
  rfl

theorem locC_apply {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i _ hn) (a b : Fin k) :
    TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) M g a b = eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (M ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b)) := by
  rw [← KLift.heO_br i dc hn]
  rfl

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowSub_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    [Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)] [Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)]
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsSubOfSums (repL (eK (D.nbr i _ hn))
        (locRep (resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x))) := by
  set ρP := resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n) with hρP
  set e := eK (D.nbr i _ hn)
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) (kap1 i Dd)
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = kap1 i Dd m := by
    intro m s
    rw [← map_smul, KLift.smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [lattice_inclusion_injective i Dd (h1.symm.trans (map_zero (kap1 i Dd)).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Γn i dc n)) v x', Λ (locRep ρP γ v) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 (γ : GE D.nd) : D.nd.O i) * ((epsU D.nd i (γ : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (Λ v x' * (rO D.nd i r (Dd.p x') (γ : GE D.nd)⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
    intro γ v x'
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply KLift.smul_cancel s
      have h1 := congrFun (hΛs (ρP γ m) s) x'
      have h2 := congrFun (hΛs m s) x'
      rw [Pi.smul_apply] at h1 h2
      rw [h1, smul_comm, ← Matrix.smul_mul, h2]
      exact idempotent_part_representation_at i r Dd hr' hsm hχ (γ : GE D.nd) m x'
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)) →ₗ[Br.LLw (D.nbr i _ hn)]
      (Fin D.R.nV → Br.LLw (D.nbr i _ hn)) := fun q =>
    { toFun := fun v j => e ((Λ (KLift.untr e v)) q.1 q.2 j)
      map_add' := fun v w => funext fun j => by
        show e ((Λ (KLift.untr e v + KLift.untr e w)) q.1 q.2 j) = _
        rw [map_add]
        simp [map_add]
      map_smul' := fun c v => funext fun j => by
        show e ((Λ (e.symm c • KLift.untr e v)) q.1 q.2 j) = c * e ((Λ (KLift.untr e v)) q.1 q.2 j)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁))) :=
    KLift.finDim_of_lat (Ow := Br.Ow (D.nbr i _ hn)) (Qp := ℚ_[D.nd.l i])
      (KLift.latOf e (D.nbr i _ hn).eO mkK (Br.iota D.nbr i _ hn) (KLift.heO_br i dc hn) (locRep ρP) ρP KLift.mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) KLift.mkK_span)
  refine sub_of_fam (fun q => Dd.p q.1) Ψ (fun v hv => ?_) (fun q g v => ?_)
  · have h0 : Λ (KLift.untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', a)) b
      simpa [Ψ] using this
    exact hΛi _ h0
  · funext j
    have key : ∀ γ : ↥(Γn i dc n), (γ : GE D.nd) = ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) →
        e ((Λ (locRep ρP γ (KLift.untr e v))) q.1 q.2 j) =
          (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r (Dd.p q.1)) g).mulVec (Ψ q v) j := by
      intro γ hγ
      rw [hΛe, hγ]
      simp only [Matrix.mulVec, dotProduct, locC_apply i dc hn, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
        Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rDuO, twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk,
        Matrix.transpose_apply, Ψ, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
      rw [show eK (D.nbr i _ hn) = e from rfl]
      have hc : ∀ x y z w : Br.LLw (D.nbr i _ hn), x * y * (z * w) = x * y * w * z := fun x y z w => by ring
      exact hc _ _ _ _
    exact key (Br.iota D.nbr i _ hn g) rfl

end Rec

end Formalism.MainNotions.N.KRowA

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section FinT

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}

theorem rFree [Module.Finite O R'] : Module.Free O R' := by
  haveI hK : Module.IsTorsionFree O (FractionRing O) := inferInstance
  haveI : Module.IsTorsionFree O (X' → Matrix d d (FractionRing O)) :=
    Module.IsTorsionFree.mk fun r hr x y hxy => by
      funext a i j
      have h := congrFun (congrFun (congrFun hxy a) i) j
      exact hK.isSMulRegular hr h
  haveI : Module.IsTorsionFree O R' := inferInstance
  exact Module.free_of_finite_type_torsion_free'

theorem idempotent_submodule_finite [Module.Finite O R'] (e₁ : R') : Module.Finite O (FirstSummandSubmodule O e₁) := by
  haveI : IsNoetherian O R' := isNoetherian_of_isNoetherianRing_of_finite O R'
  exact Module.Finite.of_injective (FirstSummandSubmodule O e₁).subtype Subtype.val_injective

theorem idempotent_submodule_free [Module.Finite O R'] (e₁ : R') : Module.Free O (FirstSummandSubmodule O e₁) := by
  haveI := idempotent_submodule_finite (R' := R') e₁
  haveI hK : Module.IsTorsionFree O (FractionRing O) := inferInstance
  haveI : Module.IsTorsionFree O (X' → Matrix d d (FractionRing O)) :=
    Module.IsTorsionFree.mk fun r hr x y hxy => by
      funext a i j
      have h := congrFun (congrFun (congrFun hxy a) i) j
      exact hK.isSMulRegular hr h
  haveI : Module.IsTorsionFree O R' := inferInstance
  haveI : Module.IsTorsionFree O (FirstSummandSubmodule O e₁) := inferInstance
  exact Module.free_of_finite_type_torsion_free'

end FinT

section RecTop

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem idempotent_part_finite_and_free (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) ∧ Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  haveI := Formalism.MainNotions.N.K.Topo.finite_R' hD
  exact ⟨idempotent_submodule_finite Dd.e₁, idempotent_submodule_free Dd.e₁⟩

def eL {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i _ hn)) (FractionRing (D.nd.O i)) →ₗ[Br.LLw (D.nbr i _ hn)] Br.LLw (D.nbr i _ hn) where
  toFun k := eK (D.nbr i _ hn) k
  map_add' a b := map_add (eK (D.nbr i _ hn)) a b
  map_smul' c k := by
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * (show FractionRing (D.nd.O i) from k)) =
      c * eK (D.nbr i _ hn) (show FractionRing (D.nd.O i) from k)
    rw [map_mul, RingEquiv.apply_symm_apply]

theorem rowTop1_S (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    KRow.RowTop1 i dc (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  haveI := K.Topo.finite_RD i r π g0 eB e₁ s Dd hD
  haveI : Module.Free (D.nd.O i) Dd.R' := rFree
  haveI := K.Topo.rTop_isModuleTopology (D.nd.O i) Dd.R'
  haveI := K.Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  haveI := K.Topo.rTop_smul (D.nd.O i) Dd.R'
  intro n _ hw c hc
  let b := Module.Free.chooseBasis (D.nd.O i) Dd.R'
  have hco : ∀ j, Continuous fun γ => b.equivFun ((c γ : Dd.R')) j := by
    intro j
    let f : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i] FractionRing (D.nd.O i) :=
      (Algebra.linearMap (D.nd.O i) (FractionRing (D.nd.O i))) ∘ₗ (b.coord j) ∘ₗ (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype
    let ℓ := (eL i dc hw).comp (trL (eK (D.nbr i _ hw)) (liftK f))
    have hℓ : Continuous ℓ := IsModuleTopology.continuous_of_linearMap ℓ
    have h1 : Continuous fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) := by
      have e1 : (fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))))) =
          fun g => ℓ (KRow.tr (eK (D.nbr i _ hw)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hw g)))) := by
        funext g
        show _ = eK (D.nbr i _ hw) (liftK f (mkK (c (Br.iota D.nbr i _ hw g))))
        rw [liftK_mkK]
        rfl
      rw [e1]
      exact hℓ.comp hc
    have h2 : Continuous fun g => (D.nbr i _ hw).eO (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))) := by
      refine continuous_induced_rng.2 ?_
      have e2 : ((↑) ∘ fun g => (D.nbr i _ hw).eO (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) =
          fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
            (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) :=
        funext fun g => (Br.toLLK_alg (D.nbr i _ hw) _).symm
      rw [e2]
      exact h1
    have h3 : Continuous fun g => b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')) := by
      have := (D.nbr i _ hw).eO_symm_cont.comp h2
      simpa [Function.comp_def] using this
    have heq : (fun γ => b.equivFun ((c γ : Dd.R')) j) =
        (fun g => b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))) ∘ (Br.ιHomeo (D.nbr i _ hw)).symm := by
      funext γ
      simp only [Basis.equivFun_apply, Basis.coord_apply]
      exact congrArg (fun γ' => b.repr ((c γ' : Dd.R')) j) (((D.nbr i _ hw).e.symm_apply_apply γ).symm)
    rw [heq]
    exact h3.comp (Br.ιHomeo (D.nbr i _ hw)).symm.continuous
  have hv : Continuous fun γ => ((c γ : Dd.R')) := by
    have e3 : (fun γ => ((c γ : Dd.R'))) = fun γ => b.equivFun.symm (fun j => b.equivFun ((c γ : Dd.R')) j) :=
      funext fun γ => (b.equivFun.symm_apply_apply _).symm
    rw [e3]
    exact (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap).comp (continuous_pi hco)
  exact continuous_induced_rng.2 hv

end RecTop

end Formalism.MainNotions.N.KRowA

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Ms

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem rDuO_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (x : D.nd.X i) : Continuous (rDuO D.nd i r x) := by
  have hce : Continuous fun g : GE D.nd => ((((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) * ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [MonoidHom.mul_apply, Units.val_mul]
    rw [e]
    exact (D.nd.chi_cont i 1).mul (K.St.hEps i)
  have hM : Continuous fun g : GE D.nd => (rO D.nd i r x g⁻¹).transpose :=
    ((hc x).comp continuous_inv).matrix_transpose
  exact hce.smul hM

theorem locC_du_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Continuous ⇑(TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)) := by
  have hinc : Continuous (TruncatedSeriesCountingIdentities.CoefExt.inc C) :=
    continuous_induced_rng.2 (by exact continuous_subtype_val)
  have h1 : Continuous fun g : Br.G D.nbr i w hw =>
      rDuO D.nd i r x ((Br.iota D.nbr i w hw g : _) : GE D.nd) :=
    (rDuO_cont i r hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact ((h1.matrix_map (D.nbr i w hw).eO_cont).matrix_map continuous_subtype_val).matrix_map hinc

end Ms

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

open Formalism.MainNotions.N.K Formalism.MainNotions.N.K.St

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)

include hD

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowSub_S :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    KRow.RowSub (ρ₁ := rho1 i Dd) i dc r := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  obtain ⟨hr', hsm, hχ⟩ := KLift.ringDef_lift i r Dd hD
  haveI := (idempotent_part_finite_and_free i r π g0 eB e₁ s Dd hD).1
  haveI := (idempotent_part_finite_and_free i r π g0 eB e₁ s Dd hD).2
  intro n _ hn
  exact rowSub_at i dc r Dd hr' hsm hχ hn

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowOrb_S (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    KRow.RowOrb (ρ₁ := rho1 i Dd) i dc := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  intro n hn hw v
  exact orb_of_sub (LL := Br.LLw (D.nbr i _ hw)) (rowSub_S i r π dc g0 eB e₁ s Dd hD n hn hw)
    (fun x => by exact locC_du_cont i r hc hw (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) x) v

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowTop_S :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    KRow.RowTop i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  apply KRow.rowTop_of
  · intro n _ hn
    exact KOrb.topMatch_pi (i := i) (hw := hn) _
  · exact rowTop1_S (i := i) (r := r) (π := π) (dc := dc) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s)
      (Dd := Dd) (hD := hD)

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem row_lattice_finite_free (n : ℕ) :
    Module.Finite (D.nd.O i) (DatS i r π dc g0 eB e₁ s Dd hD hc n).T' ∧
    Module.Free (D.nd.O i) (DatS i r π dc g0 eB e₁ s Dd hD hc n).T' ∧
    ∀ v : KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n, ∃ c : D.nd.O i, c ≠ 0 ∧
      ∃ t : (DatS i r π dc g0 eB e₁ s Dd hD hc n).T', (t : KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n) = c • v := by
  refine ⟨Module.Finite.equiv (vDS i r π dc g0 eB e₁ s Dd hD hc n),
    Module.Free.of_equiv (vDS i r π dc g0 eB e₁ s Dd hD hc n), fun v => ?_⟩
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (D.nd.O i)) Finset.univ v
  choose y hy using fun a => hb a (Finset.mem_univ a)
  refine ⟨(b : D.nd.O i), nonZeroDivisors.coe_ne_zero b, vDS i r π dc g0 eB e₁ s Dd hD hc n y, funext fun a => ?_⟩
  show algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (y a) = _
  rw [hy a]
  rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowFin_S :
    KRow.RowFin i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  unfold KRow.RowFin
  have hT1 := idempotent_part_finite_and_free (i := i) (r := r) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s) (Dd := Dd) (hD := hD)
  exact ⟨hT1.1, hT1.2, fun n _ => row_lattice_finite_free i r π dc g0 eB e₁ s Dd hD hc n⟩

end Rec

end Formalism.MainNotions.N.KRowA

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.BR Formalism.NG
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

open Formalism.MainNotions.N.K Formalism.MainNotions.N.K.St

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowTieIn_of
    (hMat : KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) ρ π)
    (hcob : ∀ n ∈ rowsN i dc, KHf.OrbC i dc (n := n) (DatS i r π dc g0 eB e₁ s Dd hD hc n).ρT') :
    StD.RowTieIn i r ρ π dc g0 eB e₁ s Dd hD hc := by
  refine ⟨?_, ?_, hMat, ?_, ?_, hcob⟩
  · first
    | exact rowSub_S (hc := hc) ..
    | exact rowSub_S ..
    | (have hD' := hD
       obtain ⟨-, -, -, -, -, -, hr', -, hsm, -, -, hχ, -⟩ := hD'
       have hFF := idempotent_part_finite_and_free (hD := hD) ..
       haveI := hFF.1
       haveI := hFF.2
       intro n _ hn
       exact rowSub_at (hr' := hr') (hsm := hsm) (hχ := hχ) (hn := hn) ..)
  · first
    | exact rowOrb_S (hc := hc) ..
    | exact rowOrb_S i r π dc g0 eB e₁ s Dd hD hc
  · first
    | exact rowTop1_S i dc r π g0 eB e₁ s Dd hD
    | exact rowTop1_S (dc := dc) (hD := hD)
    | exact fun n hn hn' c hcont => rowTop1_S (hD := hD) .. n hn hn' c hcont
  · first
    | exact rowFin_S ..
    | exact rowFin_S i r π dc g0 eB e₁ s Dd hD hc

end Formalism.MainNotions.N.KRowA

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Closed

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Plug

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (cB : ℕ)

include hD hc in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem tbTarget_row (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hTB : EmbeddingTypes.admTB i r π dc cB) (hG : K.SelfGood i)
    (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    TB.TBTarget i dc Dd cB :=
  haveI := Topo.finite_RD i r π g0 eB e₁ s Dd hD
  TBb.trivial_bound_target_of_psi i dc r ρ π g0 eB e₁ s Dd cB hD hN hc (TB.trivialBoundAtRows_of_admTB i dc r π cB hG hTB) hTie
    (fun _w hw _ c _ Cd => TBa.ytTarget_of π ρ (Topo.finite_RD i r π g0 eB e₁ s Dd hD) hF hG2 hw
      (TBa.ytEmbW_of i dc r Dd hw (StC.embRW_of i dc r Dd hD hw) (TBa.lineW_of i r ρ π hdec hw))
      (KOrb.msContW i r hc hw) c Cd)

end Plug

section PlugN

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i)
    g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π))
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem open_inputs_at_normalized (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g4 : TruncatedSeriesCountingIdentities.admG4 i r) (g5 : TruncatedSeriesCountingIdentities.admG5 i r) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (font : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (tie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hG : K.SelfGood i) (hQP : QS.QPow i) (hTB : EmbeddingTypes.admTB i (Norm.rN i r ρ π) π dc cB) :
    Final.RhoOpenA i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk ∧
    Final.TBOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc cB ∧
    Final.ChiOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    Final.FirstLocalConditionOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    StD.RowTieIn i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc := by
  have hN := Norm.normAt_rN i r ρ π
  have g4' := Norm.admG4_rN i r ρ π dcm g4
  have g5' := Norm.admG5_rN i r ρ π dcm g5
  have g2' := Norm.admG2_rN i r ρ π dcm g2
  have dcm' := Norm.decomposes_normalized i r ρ π
  refine ⟨StB.hRho_rN i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk g4 dcm fin, ?_, ?_, ?_, ?_⟩
  · exact StC.tb_of_target i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc cB
      (tbTarget_row i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc cB hN hTB hG tie font g2' dcm')
  · exact StC.chi_of i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hN g4' dcm' g5' g5x hQP
  · exact StC.first_local_clause_of i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hN g4' dcm' g5' g5x hQP
  · exact KRowA.rowTieIn_of i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc
      (RowB.rowMat_SN i r ρ π dc g0 eB e₁ s Dd hD hc) (RowB.orbC_S i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc)

end PlugN

section Inputs

theorem wildTriv_holds : Formalism.MainNotions.N.WildTriv := by
  intro E Ω _ _ _ _ _ l hl v A hA hv M _ φ hker htors σ hσ
  unfold IsPlaceOver at hA
  haveI := v.isPrime
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  obtain ⟨p, hp⟩ : ∃ p, CharP (𝓞 E ⧸ v.asIdeal) p := ⟨ringChar _, ringChar.charP _⟩
  have hpp : p.Prime := CharP.char_is_prime (𝓞 E ⧸ v.asIdeal) p
  have hpv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hpl : p ≠ l := by
    rintro rfl
    exact hv hpv
  have hval : A.valuation ((p : ℕ) : Ω) < 1 := by
    have h := (hA (p : 𝓞 E)).mpr hpv
    simpa [map_natCast] using h
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hpp hval σ hσ φ.ker hker
  obtain ⟨n, hn⟩ := htors σ
  have h1 : φ σ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp hk
  have hcop : Nat.Coprime (p ^ k) (l ^ n) := Nat.Coprime.pow k n ((Nat.coprime_primes hpp hl).mpr hpl)
  have hc2 : Nat.Coprime (orderOf (φ σ)) (l ^ n) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hcop
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc2 (orderOf_dvd_of_pow_eq_one hn))

theorem selfGood_rec {D : D7} (i : D.nd.Loc) : K.SelfGood i :=
  fun w hw => D.self_good i w hw

theorem qPow_rec {D : D7} (i : D.nd.Loc) : QS.QPow i :=
  Formalism.MainNotions.N.qpow_of_tw wildTriv_holds D i

end Inputs

section Closed

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem theorem_n5_from_inputs (g1 : TruncatedSeriesCountingIdentities.admG1 i r) (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g3 : TruncatedSeriesCountingIdentities.admG3 i r ρ π) (g4 : TruncatedSeriesCountingIdentities.admG4 i r)
    (g5 : TruncatedSeriesCountingIdentities.admG5 i r) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (g6 : TruncatedSeriesCountingIdentities.admG6 i r) (bk : TruncatedSeriesCountingIdentities.admBK i) (bka : LargeLevelLemmas.BlochKatoAnnihilators i)
    (ct : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (font : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i)
    (tie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (a51 : LargeLevelLemmas.adm51 i r ρ π) (unr : StD.UnrIn i dc) :
    TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB →
      TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hROW hLIFT hTB
  refine Final.theorem_n5_of_open_b (i := i) (r := r) (ρ := ρ) (π := π) (dc := dc) (lenRow := lenRow) (e' := e') (cB := cB)
    g1 g2 g3 g5x g6 bk bka ct dcm font fin a51 unr (selfGood_rec i) ?_ hROW hLIFT hTB
  intro _ _ hTB' _ g0 eB e₁ s Dd _ hD hc hT hrk
  haveI : ∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k) := by
    intro k
    refine ⟨fun f a m => ?_⟩
    have hD' := hD
    dsimp only [RingDef] at hD'
    obtain ⟨-, -, -, -, -, -, -, -, h9, -, h11, -, -, -, -, -, h17, h18, -, -, -, -⟩ := hD'
    have hπ : Dd.ρπ (f • a) = ((f : Dd.X' → D.nd.O i) Dd.π') • Dd.ρπ a := by
      apply Matrix.map_injective (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
      dsimp only
      rw [h17, h9, ← h17 a]
      ext u v
      simp [map_mul]
    have hk : Dd.ρk k (f • a) = ((f : Dd.X' → D.nd.O i) Dd.π') • Dd.ρk k a := by
      rw [← h18, ← h18, hπ]
      ext u v
      rfl
    rw [h11 f k (a • m)]
    refine funext fun j => ?_
    show (∑ x, (Dd.ρk k (f • a)) j x • m x) = ((f : Dd.X' → D.nd.O i) Dd.π') • ∑ x, (Dd.ρk k a) j x • m x
    rw [hk]
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  exact open_inputs_at_normalized (i := i) (r := r) (ρ := ρ) (π := π) (dc := dc) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s)
    (Dd := Dd) (hD := hD) (hc := hc) (hT := hT) (hrk := hrk) (cB := cB)
    g2 g4 g5 g5x dcm font fin tie (selfGood_rec i) (qPow_rec i) hTB'

end Closed

section Stmts

end Stmts

end Formalism.MainNotions.N.K.Closed

end
end
