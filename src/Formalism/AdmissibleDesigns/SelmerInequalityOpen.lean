import Formalism.AdmissibleDesigns.PiEquiv2
import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.AdmissibleDesigns.TheoremN5OfNormalizedItems
import Formalism.AdmissibleDesigns.GlobalIndexTheoremPlacesOfRNAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents

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

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

abbrev HfWS (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.HfW i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev Hf₂S (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Hf₂ i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev FsS (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Fs i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev Hf₁S (w : ℕ) :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    Submodule (D.nd.O i) (H1 (resRep (rho1 i Dd) (KHf.Γn i dc w))) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KHf.Hf₁ i dc (rho1 i Dd) w

def FirstBlockLocalConditions (w : ℕ) : Submodule (D.nd.O i) (H1z (QS.resU i dc Dd 0 w)) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Fρ i dc (rowsN i dc) (fun n => QS.resU i dc Dd 0 n)
    (fun n => (((HfWS i r π dc g0 eB e₁ s Dd hD hc n).restrictScalars (D.nd.O i)).map (DatS i r π dc g0 eB e₁ s Dd hD hc n).q).map
      (kRow (DatS i r π dc g0 eB e₁ s Dd hD hc n) _ (uDS i r π dc g0 eB e₁ s Dd hD hc n) (huDS i r π dc g0 eB e₁ s Dd hD hc n)))
    (fun n => KHf.F0col i dc n (resRep (uRep (D.nd.O i) (M := Vr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n))
      (QS.resU i dc Dd 0 n) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)) w

abbrev FS := QS.Fall i dc Dd (FirstBlockLocalConditions i r π dc g0 eB e₁ s Dd hD hc)

theorem FS_pos (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) (w : ℕ) : FS i r π dc g0 eB e₁ s Dd hD hc c w = QS.Fpos i dc Dd c w := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.2 hc0
  unfold FS QS.Fall
  first
    | rfl
    | simp only [Fin.cases_succ]
    | exact Fin.cases_succ _

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

abbrev ImS (w : ℕ) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  (Hf₁S i r π dc g0 eB e₁ s Dd hD w).map (gRow (DatS i r π dc g0 eB e₁ s Dd hD hc w) (resRep (rho1 i Dd) (decs D.host.E (Aw i dc) w))
    (piS i Dd hT hrk) (vDS i r π dc g0 eB e₁ s Dd hD hc w) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w) (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w))

def rowLenS (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (FsS i r π dc g0 eB e₁ s Dd hD hc w ⧸ (ImS i r π dc g0 eB e₁ s Dd hD hc hT hrk w).comap (FsS i r π dc g0 eB e₁ s Dd hD hc w).subtype)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem selmer_inequality_of_inputs [IsNoetherian Dd.R' Dd.R']
    [∀ x', IsScalarTower Dd.T' Dd.R' (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')]
    [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    [∀ k, IsScalarTower (D.nd.O i) Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (hP : Formalism.RepresentationBoundsCohomology.ringDataObjects.PrimHyp (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (RepresentationBoundsCohomology.blk D.R) (chiU D.nd i 1) (epsU D.nd i))
    (u0 : ℤ_[D.nd.l i]ˣ)
    (hcyc : ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u0 : ℤ_[D.nd.l i]))
    (hK : ∀ [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
          [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [TopologicalSpace Dd.R']
          [IsTopologicalAddGroup Dd.R'] [ContinuousConstSMul (D.nd.O i) Dd.R'] [ContinuousMul Dd.R'],
          RealDisplayAllK (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
            Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ D.R.t (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) (RepresentationBoundsCohomology.blk D.R) Dd.ρk Dd.δO
            (epsU D.nd i) g0 (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)))
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (κ : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) → GE D.nd → Lr i Dd)
    (κz : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) →
      coZ1s (resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) (colIdx i dc l))))
    (u : Col i dc → GE D.nd → D.nd.O i)
    (uz : ∀ l : Col i dc,
      coZ1s (Representation.trivial (D.nd.O i) ↥(decs D.host.E (Aw i dc) (colIdx i dc l)) ↥(Ideal.span {Dd.δO})))
    (hUz : ∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
      (((uz l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g : ↥(Ideal.span {Dd.δO})) :
        D.nd.O i) = Dd.δO * u l g)
    (hUnr : KHf.UnrFin i dc Dd.δO uz)
    (hL1 : ∀ l, LiftO (D.nd.l i) (KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l)
      (KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l)
      (mapH1 _ _ (eveS i Dd hT hrk) (ev_equiv Dd.r Dd.χ (decs D.host.E (Aw i dc) (colIdx i dc l))
        (incl (D.nd.O i) Dd.e₁) (v1S i Dd hT hrk) (eveS i Dd hT hrk) (fun a => rfl))) (e'N i dc e' (colIdx i dc l)))
    (hL2 : ∀ l, LiftO (D.nd.l i) (KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l) (KHf.HfE₂ i dc Dd.δO l)
      (mapH1 _ _ (evES i Dd hT) (ev_equiv_triv Dd.r Dd.χ (decs D.host.E (Aw i dc) (colIdx i dc l)) (evES i Dd hT)
        (hevES i Dd hT))) (e'N i dc e' (colIdx i dc l)))
    (hG6 : QS.NoFixedVectorOffZ i Dd)
    (hLx : ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
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
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ))
    (hRho : InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk) κ
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) κz (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk))
    (hBKa : ∀ w ∈ rowsN i dc, ∀ a, a ∈ HfWS i r π dc g0 eB e₁ s Dd hD hc w ↔
      ∀ b ∈ Hf₂S i r π dc g0 eB e₁ s Dd hD hc w, cupFG (DatS i r π dc g0 eB e₁ s Dd hD hc w) a b = 0)
    (hTB : ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈ FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1))
    (hChi : ∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
      InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
        (qsN i dc) (ShaN i ((c : ℕ) - 1)) (FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
        (QS.ζO i dc) (QS.nQ i dc))
    (hU1 : (∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), u l (g : GE D.nd) = 0) ∧
      (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), u l g = 1))
    (hLoc1 : InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
      (FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc))
    (hCover : ∀ v, (∃ a, Ine (F := D.host.E) (Av (D := D) v) ≤ QS.Io i a) ∨
      (∃ a, Ine (F := D.host.E) (Av (D := D) v) ≤ QS.IS i a) ∨
        ∃ w ∈ rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc), ∃ J : Subgroup ((decs D.host.E (Aw i dc)) w),
          FS i r π dc g0 eB e₁ s Dd hD hc QS.c1 w ≤ unrH1 (QS.resU i dc Dd QS.c1 w) J ∧
          Ine (F := D.host.E) (Av (D := D) v) ≤ J.map ((decs D.host.E (Aw i dc)) w).subtype)
    (hCR : ∀ l : Col i dc, colIdx i dc l ∉ rowsN i dc) (hRQ : ∀ w ∈ rowsN i dc, w ∉ qsN i dc)
    (hTie : TieRow i dc (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) lenRow) :
    SelmerLengthInequality i ρ π dc lenRow e' cB := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  haveI := Topo.rTop_mul_RD i r π g0 eB e₁ s Dd hD
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩ := Topo.topoHyps i r π dc g0 eB e₁ s Dd hD hc u0 hcyc
  have hA := tensor_lattice_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk (epsU D.nd i)
  have hL := fun w => KLat.rowLat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (D.nd.l i) (Topo.padicCoeff_O i) (Topo.fracTop_O i) w
  have H := hK (Col i dc) (colIdx i dc) (colIdx_inj i dc) (Aw i dc) (plOf i dc) (Av (D := D)) (jN i ρ π dc)
    (e'N i dc e') (rowsN i dc) (qsN i dc) (sN i ρ π) (invariantsLengthSup i dc) (ShaN i) cB (fun _ _ => cB)
    (Lr i Dd) (tensM _ _ _) (v1S i Dd hT hrk) κ (Vr i Dd) (iLM _ _ _) (qVM _ _ _)
    (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) κz (FS i r π dc g0 eB e₁ s Dd hD hc)
    (QS.Vo i) (QS.VS i) (QS.Io i) (QS.IS i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) ({a // RepresentationBoundsCohomology.blk D.R a = 0} → D.nd.O i)
    (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk) (gamM (Dd.ρk 0)) (lamS i Dd hT hrk)
    (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) (uDS i r π dc g0 eB e₁ s Dd hD hc) (huDS i r π dc g0 eB e₁ s Dd hD hc) (vDS i r π dc g0 eB e₁ s Dd hD hc) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk) (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk)
    (FsS i r π dc g0 eB e₁ s Dd hD hc) (Hf₁S i r π dc g0 eB e₁ s Dd hD) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc)
    u (D.nd.s0 i) (Topo.yU i u0) (HfWS i r π dc g0 eB e₁ s Dd hD hc) (Hf₂S i r π dc g0 eB e₁ s Dd hD hc)
    (LeftId (D.nd.O i) Dd.e₁) (incl _ Dd.e₁) (eveS i Dd hT hrk) (fun a => rfl)
    (LeftId (D.nd.O i) Dd.E) (incl _ Dd.E) (evES i Dd hT) (hevES i Dd hT)
    (fun l => KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l)
    (fun l => KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l) (fun l => KHf.HfE₂ i dc Dd.δO l) uz
  have hrows : ∀ w ∈ rowsN i dc, FS i r π dc g0 eB e₁ s Dd hD hc 0 w = (((HfWS i r π dc g0 eB e₁ s Dd hD hc w).restrictScalars (D.nd.O i)).map (DatS i r π dc g0 eB e₁ s Dd hD hc w).q).map
      (kRow (DatS i r π dc g0 eB e₁ s Dd hD hc w) _ (uDS i r π dc g0 eB e₁ s Dd hD hc w) (huDS i r π dc g0 eB e₁ s Dd hD hc w)) := by
    intro w hw
    show FirstBlockLocalConditions i r π dc g0 eB e₁ s Dd hD hc w = _
    unfold FirstBlockLocalConditions KHf.Fρ
    rw [if_pos hw]
  obtain ⟨hineq, hv, -⟩ := H t1 t2 t3 t4 t5 (inc_cont (O := D.nd.O i) Dd.e₁) t6 t7 t8 t9 t10 t11 hA.2.2.1 hA.2.2.2.2.1 hA.2.2.2.2.2.1
    hA.2.2.2.2.2.2.1 hUz hUnr hL1 hL2 (fun x' hx => ⟨hG6 x' hx, hLx x' hx⟩) hRho
    (fun w hw => ⟨(t12 w hw).1, (t12 w hw).2, (hL w).1, (hL w).2.1, (hL w).2.2.1, (hL w).2.2.2, hBKa w hw,
      hrows w hw, rfl,
      KHf.im_le_Fs i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w (rho1 i Dd) (piS i Dd hT hrk) (vDS i r π dc g0 eB e₁ s Dd hD hc w) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w)
        (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w)⟩)
    (fun c hc2 => ⟨H0.kernel_length_higher_columns dc hN hD c hc2,
      fun w hw => ⟨by
        have hc0 : c ≠ 0 := fun h => by rw [h] at hc2; simp at hc2
        have hc1 : (c : ℕ) ≠ 1 := by omega
        rw [FS_pos i r π dc g0 eB e₁ s Dd hD hc c hc0 w]
        unfold QS.Fpos
        rw [if_neg (hRQ w hw), if_pos hw, if_neg hc1], le_rfl, hTB c (by omega) w hw⟩, hChi c hc2⟩)
    ⟨hU1.1, hU1.2, fun l => by
        rw [FS_pos i r π dc g0 eB e₁ s Dd hD hc _ (by intro h; have := congrArg Fin.val h; simp at this) _]
        unfold QS.Fpos
        by_cases hq : colIdx i dc l ∈ qsN i dc
        · rw [if_pos hq] <;> exact le_rfl
        · rw [if_neg hq, if_neg (hCR l), if_pos rfl] <;> exact le_rfl,
      fun w hw => ⟨by
        rw [FS_pos i r π dc g0 eB e₁ s Dd hD hc _ (by intro h; have := congrArg Fin.val h; simp at this) _]
        unfold QS.Fpos
        rw [if_neg (hRQ w hw), if_pos hw, if_pos rfl], le_rfl, hTB QS.c1 le_rfl w hw⟩, hLoc1, hCover⟩
  exact ⟨rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk, H0.h0d i dc Dd, IsDiscreteValuationRing.addVal (D.nd.O i) Dd.δO,
    Fintype.card {a // RepresentationBoundsCohomology.blk D.R a = 0}, hv, card_first_block (D := D), hineq, hTie,
    H0.invariants_display_match i r ρ π dc g0 eB e₁ s Dd hD hN⟩

end Formalism.MainNotions.N.K.St

end
end

section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology.J8

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.MainNotions.N
  Formalism.MainNotions.N.RepresentationBoundsCohomology

section Gen

theorem rank_submatrix_le' {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix n n K) (f g : m → n) : (M.submatrix f g).rank ≤ M.rank := by
  exact Matrix.rank_submatrix_le M f g

theorem castAdd_ne_natAdd {r t : ℕ} (b : Fin r) (c : Fin t) : Fin.castAdd t b ≠ Fin.natAdd r c := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
  omega

theorem lt_rank_of {K : Type} [Field K] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (hc : ∀ c d : Fin t, M (Fin.natAdd r c) (Fin.natAdd r d) = if c = d then 1 else 0)
    (hcb : ∀ (c : Fin t) (b : Fin r), M (Fin.natAdd r c) (Fin.castAdd t b) = 0)
    (hac : ∀ (a : Fin r) (c : Fin t), M (Fin.castAdd t a) (Fin.natAdd r c) = 0)
    (a b : Fin r) (hab : M (Fin.castAdd t a) (Fin.castAdd t b) ≠ 0) : t + 1 ≤ M.rank := by
  classical
  let f : Fin (t + 1) → Fin (r + t) := Fin.cons (Fin.castAdd t a) (Fin.natAdd r)
  let g : Fin (t + 1) → Fin (r + t) := Fin.cons (Fin.castAdd t b) (Fin.natAdd r)
  let w : Fin (t + 1) → K := Fin.cons (M (Fin.castAdd t a) (Fin.castAdd t b)) (fun _ => 1)
  have h1 : M.submatrix f g = Matrix.diagonal w := by
    ext p q
    cases p using Fin.cases with
    | zero =>
      cases q using Fin.cases with
      | zero => simp [f, g, w]
      | succ q => simp [f, g, w, hac, (Fin.succ_ne_zero q).symm]
    | succ p =>
      cases q using Fin.cases with
      | zero => simp [f, g, w, hcb, Fin.succ_ne_zero p]
      | succ q =>
        by_cases hpq : p = q
        · subst hpq
          simp [f, g, w, hc]
        · simp [f, g, w, hc, hpq]
  have h2 := rank_submatrix_le' M f g
  rw [h1, Matrix.rank_diagonal] at h2
  have hw : ∀ p, w p ≠ 0 := by
    intro p
    cases p using Fin.cases with
    | zero => simpa [w] using hab
    | succ p => simp [w]
  have h3 : Fintype.card {p // w p ≠ 0} = t + 1 := by
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hw), Fintype.card_fin]
  omega

theorem eq_diag_of {K : Type} [Field K] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (B : Matrix (Fin r) (Fin r) K)
    (hM : ∀ u, eG r t K (M *ᵥ u) = (B *ᵥ (eG r t K u).1, (eG r t K u).2)) (hrk : M.rank = t) :
    M = Matrix.diagonal fun a => if blkG r t a = 0 then (0 : K) else 1 := by
  classical
  have hent : ∀ x y, (M *ᵥ Pi.single y (1 : K)) x = M x y := by
    intro x y
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : ∀ (d : Fin t) y, M (Fin.natAdd r d) y = if Fin.natAdd r d = y then 1 else 0 := by
    intro d y
    have h := congrFun (congrArg Prod.snd (hM (Pi.single y 1))) d
    simp only [eG_apply] at h
    rw [← hent, h, Pi.single_apply]
  have h1 : ∀ a y, M (Fin.castAdd t a) y = (B *ᵥ fun b => (Pi.single y (1 : K) : Fin (r + t) → K) (Fin.castAdd t b)) a := by
    intro a y
    have h := congrFun (congrArg Prod.fst (hM (Pi.single y 1))) a
    simp only [eG_apply] at h
    rw [← hent, h]
  have hac : ∀ (a : Fin r) (c : Fin t), M (Fin.castAdd t a) (Fin.natAdd r c) = 0 := by
    intro a c
    rw [h1]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, castAdd_ne_natAdd]
  have hc : ∀ c d : Fin t, M (Fin.natAdd r c) (Fin.natAdd r d) = if c = d then 1 else 0 := by
    intro c d
    rw [h2]
    by_cases hcd : c = d
    · subst hcd
      simp
    · rw [if_neg hcd, if_neg]
      intro h
      apply hcd
      have h3 := congrArg Fin.val h
      simp at h3
      exact Fin.ext h3
  have hcb : ∀ (c : Fin t) (b : Fin r), M (Fin.natAdd r c) (Fin.castAdd t b) = 0 := by
    intro c b
    rw [h2, if_neg (fun h => castAdd_ne_natAdd b c h.symm)]
  have hB0 : ∀ a b, M (Fin.castAdd t a) (Fin.castAdd t b) = 0 := by
    intro a b
    by_contra hab
    have := lt_rank_of M hc hcb hac a b hab
    omega
  ext x y
  cases x using Fin.addCases with
  | left a =>
    cases y using Fin.addCases with
    | left b => simp [hB0, Matrix.diagonal_apply, blkG_castAdd]
    | right c => simp [hac, Matrix.diagonal_apply, blkG_castAdd]
  | right c =>
    rw [h2]
    simp [Matrix.diagonal_apply, blkG_natAdd, Fin.succ_ne_zero]

theorem transfer {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (L L' : V ≃ₗ[K] W) (φ : V → V) (F Hm : W → W)
    (h1 : ∀ u, L (φ u) = Hm (L u)) (h2 : ∀ u, L' (φ u) = Hm (L' u)) (h3 : ∀ u, L (φ u) = F (L u)) :
    ∀ u, L' (φ u) = F (L' u) := by
  have hF : ∀ w, Hm w = F w := by
    intro w
    obtain ⟨u, rfl⟩ := L.surjective w
    rw [← h1, h3]
  intro u
  rw [h2, hF]

end Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

def Dg (γ : GE N) (z : (Fin R.r → KK N i) × (Fin R.t → KK N i)) : (Fin R.r → KK N i) × (Fin R.t → KK N i) :=
  ((mapM (toK N i) (rhoO N i ρ π) γ).mulVec z.1,
    fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) γ : (N.O i)ˣ) : N.O i) * z.2 c)

theorem act_inR {a : N.X i → MatN N i} (ha : InR N i r a) :
    ∃ Hm : (Fin R.r → KK N i) × (Fin R.t → KK N i) → (Fin R.r → KK N i) × (Fin R.t → KK N i),
      ∀ L : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      (∀ γ u, L ((mapM (toK N i) (rO N i r π) γ).mulVec u) = Dg N ρ π γ (L u)) →
      ∀ u, L (((a π).map (toK N i)).mulVec u) = Hm (L u) := by
  obtain ⟨m, f, g, -, rfl⟩ := ha
  refine ⟨fun z => ∑ k, toK N i (f k π) • Dg N ρ π (g k) z, fun L hL u => ?_⟩
  have h : (((∑ k, fun x => f k x • rO N i r x (g k)) π).map (toK N i)).mulVec u =
      ∑ k, toK N i (f k π) • (mapM (toK N i) (rO N i r π) (g k)).mulVec u := by
    rw [Finset.sum_apply]
    change ((toK N i).mapMatrix (∑ k, f k π • rO N i r π (g k))).mulVec u = _
    rw [map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Matrix.smul_mulVec]
    congr 1
    ext a b
    simp [mapM, Matrix.smul_apply]
  rw [h, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, hL]

theorem tSpan_of_inR {a : N.X i → MatN N i} (ha : InR N i r a) : a ∈ tSpan (N.T i) (repX N r) := by
  have h := Inst.inSpan_tSpan N i (N.T i) (rO N i r) (N.O i) ha
  have e1 : (fun x => (a x).map (algebraMap (N.O i) (N.O i))) = a := by
    funext x
    exact Inst.map_self _
  have e2 : Inst.repF N i (rO N i r) (N.O i) = repX N r := by
    ext γ x : 2
    rw [Inst.repF_apply, Inst.map_self]
    rfl
  rw [e1, e2] at h
  exact h

theorem rr_inj {S : IdempotentChoiceData N i} (hG : GoodCongruenceObjects N r ρ π S) (x' : S.X') :
    Function.Injective (fun c : Fin R.t => S.rr (1 + (c : ℕ)) x') := by
  classical
  obtain ⟨b, hbT, -, hind⟩ := Inst.descent_hyps N hG
  have hG' := hG
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, -, hcard⟩, hroots, -⟩ := hG'
  have hcF : Fintype.card {y // S.p y = S.p x'} = R.t.factorial := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard (S.p x')
  let Φ : {y // S.p y = S.p x'} → (Fin R.t → N.O i) := fun y c => S.rr (1 + (c : ℕ)) y.1
  have hinj : Function.Injective Φ := by
    intro y z hyz
    apply Inst.sep_of_indep hcF (fun k (y : {y // S.p y = S.p x'}) => b k y.1)
      (fun a ha => hind (S.p x') a (fun y hy => ha ⟨y, hy⟩)) y z
    intro k
    refine Inst.T'_eq_of_rr N hG (y.2.trans z.2.symm) (fun c hc => ?_) (b k) (hbT k)
    have hc' := Finset.mem_Icc.mp hc
    have h1 := congrFun hyz ⟨c - 1, by omega⟩
    simpa [Φ, show 1 + (c - 1) = c by omega] using h1
  have hP : ∀ y : {y // S.p y = S.p x'}, ∏ c, (Polynomial.X - Polynomial.C (Φ y c)) =
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) := by
    intro y
    have h1 : ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c y.1)) =
        ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) := by
      rw [hroots y.1, hroots x', y.2]
    rw [← h1]
    have h2 : Finset.Icc 1 R.t = Finset.Ico 1 (R.t + 1) := by
      ext c
      simp [Finset.mem_Icc, Finset.mem_Ico]
    rw [h2, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Fin.prod_univ_eq_prod_range
        (fun c => (Polynomial.X : Polynomial (N.O i)) - Polynomial.C (S.rr (1 + c) y.1))]
  exact Inst.inj_of_card Φ hinj _ hP hcF.ge ⟨x', rfl⟩

theorem prod_Icc_fin (t : ℕ) (F : ℕ → Polynomial (N.O i)) :
    ∏ c ∈ Finset.Icc 1 t, F c = ∏ c : Fin t, F (1 + (c : ℕ)) := by
  rw [Fin.prod_univ_eq_prod_range (fun c => F (1 + c)) t, Finset.range_eq_Ico]
  simp_rw [add_comm 1]
  rw [Finset.prod_Ico_add' F 0 t 1, zero_add]
  rfl

section Comp

open Formalism.NG

end Comp

end Formalism.MainNotions.N.RepresentationBoundsCohomology.J8

end
end

section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Norm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.MainNotions.N
  Formalism.MainNotions.N.RepresentationBoundsCohomology Formalism.MainNotions.N.RepresentationBoundsCohomology.J8

section Gen2

variable {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem blockPoly_conj (P Q e a : Matrix n n K) (h1 : P * Q = 1) :
    blockPoly (P * e * Q) (P * a * Q) = blockPoly e a := by
  rw [blockPoly_eq, blockPoly_eq]
  have hm : ∀ M N : Matrix n n K, (M * N).map (Polynomial.C (R := K)) =
      M.map (Polynomial.C (R := K)) * N.map (Polynomial.C (R := K)) :=
    fun M N => Matrix.map_mul
  have h1' : P.map (Polynomial.C (R := K)) * Q.map (Polynomial.C (R := K)) = 1 := by
    rw [← hm, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  set P' := P.map (Polynomial.C (R := K))
  set Q' := Q.map (Polynomial.C (R := K))
  have e1 : (Polynomial.X : Polynomial K) • (P' * e.map Polynomial.C * Q') - P' * a.map Polynomial.C * Q' + 1 -
      P' * e.map Polynomial.C * Q' =
      P' * ((Polynomial.X : Polynomial K) • e.map Polynomial.C - a.map Polynomial.C + 1 - e.map Polynomial.C) * Q' := by
    rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.sub_mul,
      Matrix.mul_one, h1', Matrix.mul_smul, Matrix.smul_mul]
  rw [hm, hm, hm, hm, e1, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det P'), mul_assoc,
    ← Matrix.det_mul, h1', Matrix.det_one, mul_one]

theorem rank_conj {F : Type} [Field F] (P Q M : Matrix n n F) (h1 : P * Q = 1) (_h2 : Q * P = 1) :
    (P * M * Q).rank = M.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_left_inverse h1),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse h1)]

end Gen2

section D51

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

def cInt (P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (A : MatN D.nd i) : MatN D.nd i :=
  if h : ∃ M : MatN D.nd i, M.map (toK D.nd i) = P * A.map (toK D.nd i) * Q then h.choose else 0

theorem cInt_spec {P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)} {A : MatN D.nd i}
    (h : ∃ M : MatN D.nd i, M.map (toK D.nd i) = P * A.map (toK D.nd i) * Q) :
    (cInt i P Q A).map (toK D.nd i) = P * A.map (toK D.nd i) * Q := by
  unfold cInt
  rw [dif_pos h]
  exact h.choose_spec

def phiC (P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (a : D.nd.X i → MatN D.nd i) :
    D.nd.X i → MatN D.nd i :=
  Function.update a π (cInt i P Q (a π))

theorem phiC_ne (P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (a : D.nd.X i → MatN D.nd i)
    {x : D.nd.X i} (hx : x ≠ π) : phiC i π P Q a x = a x :=
  Function.update_of_ne hx _ _

theorem phiC_self (P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (a : D.nd.X i → MatN D.nd i) :
    phiC i π P Q a π = cInt i P Q (a π) :=
  Function.update_self _ _ _

theorem map_smul_toK (c : D.nd.O i) (A : MatN D.nd i) :
    (c • A).map (toK D.nd i) = toK D.nd i c • A.map (toK D.nd i) := by
  ext a b
  simp [Matrix.smul_apply]

theorem inR_phiC {P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)}
    (hconj : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q)
    {a : D.nd.X i → MatN D.nd i} (ha : InR D.nd i r a) :
    InR D.nd i (rN i r ρ π) (phiC i π P Q a) ∧
      (phiC i π P Q a π).map (toK D.nd i) = P * (a π).map (toK D.nd i) * Q := by
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  have hπ : ((∑ k, fun x => f k x • rO D.nd i (rN i r ρ π) x (g k)) π).map (toK D.nd i) =
      P * ((∑ k, fun x => f k x • rO D.nd i r x (g k)) π).map (toK D.nd i) * Q := by
    simp only [Finset.sum_apply]
    change (toK D.nd i).mapMatrix (∑ k, f k π • rO D.nd i (rN i r ρ π) π (g k)) =
      P * (toK D.nd i).mapMatrix (∑ k, f k π • rO D.nd i r π (g k)) * Q
    rw [map_sum, map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_smul_toK, map_smul_toK, hconj, Matrix.mul_smul,
      Matrix.smul_mul]
  have heq : phiC i π P Q (∑ k, fun x => f k x • rO D.nd i r x (g k)) =
      ∑ k, fun x => f k x • rO D.nd i (rN i r ρ π) x (g k) := by
    funext x
    by_cases hx : x = π
    · subst hx
      rw [phiC_self]
      apply Matrix.map_injective (toK_inj i)
      show (cInt i P Q _).map (toK D.nd i) = _
      rw [cInt_spec i ⟨_, hπ⟩]
      exact hπ.symm
    · rw [phiC_ne i π P Q _ hx]
      simp only [Finset.sum_apply, rO_rN_ne i r ρ π hx]
  refine ⟨⟨m, f, g, hf, heq⟩, ?_⟩
  rw [heq]
  exact hπ

theorem phiC_rel {P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)} (hQP : Q * P = 1)
    {a b c : D.nd.X i → MatN D.nd i} (hab : a * b = c)
    (ha : (phiC i π P Q a π).map (toK D.nd i) = P * (a π).map (toK D.nd i) * Q)
    (hb : (phiC i π P Q b π).map (toK D.nd i) = P * (b π).map (toK D.nd i) * Q)
    (hc : (phiC i π P Q c π).map (toK D.nd i) = P * (c π).map (toK D.nd i) * Q) :
    phiC i π P Q a * phiC i π P Q b = phiC i π P Q c := by
  funext x
  by_cases hx : x = π
  · subst hx
    apply Matrix.map_injective (toK_inj i)
    show (phiC i x P Q a x * phiC i x P Q b x).map (toK D.nd i) = (phiC i x P Q c x).map (toK D.nd i)
    rw [Matrix.map_mul, ha, hb, hc, ← congrFun hab x, Pi.mul_apply, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  · rw [Pi.mul_apply, phiC_ne i π P Q _ hx, phiC_ne i π P Q _ hx, phiC_ne i π P Q _ hx, ← Pi.mul_apply, hab]

theorem phiC_zero {P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)} :
    (phiC i π P Q 0 π).map (toK D.nd i) = P * ((0 : D.nd.X i → MatN D.nd i) π).map (toK D.nd i) * Q ∧
      phiC i π P Q 0 = 0 := by
  have h0 : ∃ M : MatN D.nd i, M.map (toK D.nd i) = P * ((0 : D.nd.X i → MatN D.nd i) π).map (toK D.nd i) * Q :=
    ⟨0, by simp⟩
  have h1 : (phiC i π P Q 0 π).map (toK D.nd i) = P * ((0 : D.nd.X i → MatN D.nd i) π).map (toK D.nd i) * Q := by
    rw [phiC_self]
    exact cInt_spec i h0
  refine ⟨h1, ?_⟩
  funext x
  by_cases hx : x = π
  · subst hx
    apply Matrix.map_injective (toK_inj i)
    show (phiC i x P Q 0 x).map (toK D.nd i) = (0 : MatN D.nd i).map (toK D.nd i)
    rw [h1]
    simp
  · rw [phiC_ne i π P Q _ hx]

end D51

section D51b

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem design_normalized (S : IdempotentChoiceData D.nd i) (hG : GoodCongruenceObjects D.nd r ρ π S) : InertiaElementIdempotentChoice D.nd (rN i r ρ π) π := by
  obtain ⟨hbd, hχ, hρ⟩ := normAt_rN i r ρ π
  have hG0 := hG
  obtain ⟨⟨heB, he1, heBB, he11, heB1, he1B, hrkB, hrk1⟩, hdec, hact, -, hg0, hε, ⟨hX0m, heX, hXe, hX0π⟩,
    ⟨hT, -, -, -, hcard⟩, hroots, ⟨hπ, -⟩, -⟩ := hG0
  obtain ⟨P, Q, hPQ, hQP, hc⟩ := conjK_self i r ρ π ⟨S.e, hdec⟩
  have hA' : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q :=
    fun g => by
      have h := hc g
      beta_reduce at h
      rw [h, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  obtain ⟨heB', hmB⟩ := inR_phiC i r ρ π hA' heB
  obtain ⟨he1', hm1⟩ := inR_phiC i r ρ π hA' he1
  obtain ⟨hX0m', hmX⟩ := inR_phiC i r ρ π hA' hX0m
  have z := phiC_zero i π (P := P) (Q := Q)
  have heBB' := phiC_rel i π hQP heBB hmB hmB hmB
  have he11' := phiC_rel i π hQP he11 hm1 hm1 hm1
  have heB1' : phiC i π P Q S.eB * phiC i π P Q S.e1 = 0 := by
    rw [← z.2]
    exact phiC_rel i π hQP heB1 hmB hm1 z.1
  have he1B' : phiC i π P Q S.e1 * phiC i π P Q S.eB = 0 := by
    rw [← z.2]
    exact phiC_rel i π hQP he1B hm1 hmB z.1
  have heX' := phiC_rel i π hQP heX hmB hmX hmX
  have hXe' := phiC_rel i π hQP hXe hmX hmB hmX
  have hrk : ∀ (a : D.nd.X i → MatN D.nd i),
      (phiC i π P Q a π).map (toK D.nd i) = P * (a π).map (toK D.nd i) * Q →
      ∀ x, ((phiC i π P Q a x).map (toK D.nd i)).rank = ((a x).map (toK D.nd i)).rank := by
    intro a ha x
    by_cases hx : x = π
    · subst hx
      rw [ha, rank_conj P Q _ hPQ hQP]
    · rw [phiC_ne i π P Q a hx]
  have hrkB' : ∀ x, ((phiC i π P Q S.eB x).map (toK D.nd i)).rank = D.R.t := fun x => (hrk _ hmB x).trans (hrkB x)
  have hrk1' : ∀ x, ((phiC i π P Q S.e1 x).map (toK D.nd i)).rank = 1 := fun x => (hrk _ hm1 x).trans (hrk1 x)
  let e' : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)) :=
    (matEquiv Q P hQP hPQ).trans S.e
  have he' : ∀ u, e' u = S.e (Q.mulVec u) := fun u => rfl
  have hΦ : ∀ γ u, e' ((mapM (toK D.nd i) (rO D.nd i (rN i r ρ π) π) γ).mulVec u) = Dg D.nd ρ π γ (e' u) := by
    intro γ u
    rw [he', he']
    show S.e (Q.mulVec (((rO D.nd i (rN i r ρ π) π γ).map (toK D.nd i)).mulVec u)) = _
    rw [hA', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    exact hdec γ (Q.mulVec u)
  have hΨ : ∀ γ u, eG D.R.r D.R.t (KK D.nd i) ((mapM (toK D.nd i) (rO D.nd i (rN i r ρ π) π) γ).mulVec u) =
      Dg D.nd ρ π γ (eG D.R.r D.R.t (KK D.nd i) u) :=
    fun γ u => e_of_bd D.nd (rO D.nd i (rN i r ρ π) π γ) (hbd γ) (rhoO D.nd i ρ π γ) (hρ γ) _ (hχ γ) u
  have haB : InR' D.nd r S (fun x' => S.eB (S.p x')) := Inst.inR'_of_inR D.nd (r := r) hT heB
  have h3 : ∀ u, S.e (((S.eB π).map (toK D.nd i)).mulVec u) =
      (((S.ψρ (fun x' => S.eB (S.p x'))).map (toK D.nd i)).mulVec (S.e u).1,
        fun c => toK D.nd i (S.ψχ c (fun x' => S.eB (S.p x'))) * (S.e u).2 c) := by
    intro u
    have h := hact _ haB u
    beta_reduce at h
    rw [hπ] at h
    exact h
  have hconjv : ∀ (a : D.nd.X i → MatN D.nd i),
      (phiC i π P Q a π).map (toK D.nd i) = P * (a π).map (toK D.nd i) * Q →
      ∀ u, e' (((phiC i π P Q a π).map (toK D.nd i)).mulVec u) = S.e (((a π).map (toK D.nd i)).mulVec (Q.mulVec u)) := by
    intro a ha u
    rw [he', ha, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
  have h3' : ∀ u, e' (((phiC i π P Q S.eB π).map (toK D.nd i)).mulVec u) =
      (((S.ψρ (fun x' => S.eB (S.p x'))).map (toK D.nd i)).mulVec (e' u).1,
        fun c => toK D.nd i (S.ψχ c (fun x' => S.eB (S.p x'))) * (e' u).2 c) := by
    intro u
    rw [hconjv _ hmB u, h3, he']
  have hE : ∀ u, eG D.R.r D.R.t (KK D.nd i) (((phiC i π P Q S.eB π).map (toK D.nd i)).mulVec u) =
      (((S.ψρ (fun x' => S.eB (S.p x'))).map (toK D.nd i)).mulVec (eG D.R.r D.R.t (KK D.nd i) u).1,
        (eG D.R.r D.R.t (KK D.nd i) u).2) := by
    obtain ⟨Hm, hH⟩ := act_inR D.nd (rN i r ρ π) ρ π heB'
    have h := transfer e' (eG D.R.r D.R.t (KK D.nd i)) (fun u => ((phiC i π P Q S.eB π).map (toK D.nd i)).mulVec u)
      (fun z => (((S.ψρ (fun x' => S.eB (S.p x'))).map (toK D.nd i)).mulVec z.1,
        fun c => toK D.nd i (S.ψχ c (fun x' => S.eB (S.p x'))) * z.2 c)) Hm
      (hH e' hΦ) (hH _ hΨ) h3'
    intro u
    refine (h u).trans (Prod.ext rfl (funext fun c => ?_))
    show toK D.nd i (S.ψχ c (fun x' => S.eB (S.p x'))) * _ = _
    rw [Inst.psiChi_eB D.nd hG c, map_one, one_mul]
    rfl
  have heBπ : phiC i π P Q S.eB π = Matrix.diagonal fun a => if blk D.R a = 0 then (0 : D.nd.O i) else 1 := by
    have hD := eq_diag_of (r := D.R.r) (t := D.R.t) ((phiC i π P Q S.eB π).map (toK D.nd i)) _ hE (hrkB' π)
    apply Matrix.map_injective (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
    show (phiC i π P Q S.eB π).map (toK D.nd i) =
      (Matrix.diagonal fun a => if blk D.R a = 0 then (0 : D.nd.O i) else 1).map (toK D.nd i)
    rw [hD, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    by_cases h0 : blkG D.R.r D.R.t a = 0 <;> simp [h0]
  have hX0π' : ∀ u, e' (((phiC i π P Q S.X0 π).map (toK D.nd i)).mulVec u) =
      ((0 : Fin D.R.r → KK D.nd i), fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) S.g0 : (D.nd.O i)ˣ) : D.nd.O i) * (e' u).2 c) := by
    intro u
    rw [hconjv _ hmX u, hX0π, he']
  have hX0std : ∀ u, eG D.R.r D.R.t (KK D.nd i) (((phiC i π P Q S.X0 π).map (toK D.nd i)).mulVec u) =
      ((0 : Fin D.R.r → KK D.nd i), fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) S.g0 : (D.nd.O i)ˣ) : D.nd.O i) * (eG D.R.r D.R.t (KK D.nd i) u).2 c) := by
    obtain ⟨Hm, hH⟩ := act_inR D.nd (rN i r ρ π) ρ π hX0m'
    exact transfer e' (eG D.R.r D.R.t (KK D.nd i)) (fun u => ((phiC i π P Q S.X0 π).map (toK D.nd i)).mulVec u)
      (fun z => ((0 : Fin D.R.r → KK D.nd i), fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) S.g0 : (D.nd.O i)ˣ) : D.nd.O i) * z.2 c)) Hm
      (hH e' hΦ) (hH _ hΨ) hX0π'
  have hX0eq : phiC i π P Q S.X0 π =
      Matrix.diagonal fun a => if blk D.R a = 0 then 0 else rO D.nd i (rN i r ρ π) π S.g0 a a := by
    apply Matrix.map_injective (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    apply (eG D.R.r D.R.t (KK D.nd i)).injective
    refine (hX0std u).trans (Eq.symm ((e_of_diag D.nd (fun a => rO D.nd i (rN i r ρ π) π S.g0 a a) u).trans
      (Prod.ext rfl (funext fun c => ?_))))
    show toK D.nd i (rO D.nd i (rN i r ρ π) π S.g0 (Fin.natAdd D.R.r c) (Fin.natAdd D.R.r c)) * _ = _
    rw [hχ]
  have he1π : ∀ a b, (blk D.R a ≠ 0 ∨ blk D.R b ≠ 0) → phiC i π P Q S.e1 π a b = 0 := by
    intro a b hab
    rcases hab with ha | hb
    · have h' : (phiC i π P Q S.eB π * phiC i π P Q S.e1 π) a b = 0 :=
        congrFun (congrFun (congrFun heB1' π) a) b
      rw [heBπ] at h'
      simpa [Matrix.diagonal_mul, ha] using h'
    · have h' : (phiC i π P Q S.e1 π * phiC i π P Q S.eB π) a b = 0 :=
        congrFun (congrFun (congrFun he1B' π) a) b
      rw [heBπ] at h'
      simpa [Matrix.mul_diagonal, hb] using h'
  let s' : D.nd.X i → MatN D.nd i :=
    phiC i π P Q S.X0 - phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0 * phiC i π P Q S.eB
  have hI : IdemHyp (D.nd.O i) (D.nd.T i) (repX D.nd (rN i r ρ π)) π (blk D.R) (phiC i π P Q S.eB)
      (phiC i π P Q S.e1) :=
    ⟨tSpan_of_inR D.nd (rN i r ρ π) heB', tSpan_of_inR D.nd (rN i r ρ π) he1', heBB', he11', heB1', he1B',
      hrkB', hrk1', heBπ, he1π⟩
  have hX0t := tSpan_of_inR D.nd (rN i r ρ π) hX0m'
  have hs : s' ∈ tSpan (D.nd.T i) (repX D.nd (rN i r ρ π)) := by
    have h1 := smul_mem_tSpan (D.nd.T i) (repX D.nd (rN i r ρ π)) (f := -1) (neg_mem (D.nd.T i).one_mem)
      (mul_mem_tSpan (D.nd.T i) (repX D.nd (rN i r ρ π))
        (mul_mem_tSpan (D.nd.T i) (repX D.nd (rN i r ρ π)) (tSpan_of_inR D.nd (rN i r ρ π) heB')
        (repX_mem D.nd (rN i r ρ π) S.g0)) (tSpan_of_inR D.nd (rN i r ρ π) heB'))
    have h2 := add_mem_tSpan (D.nd.T i) (repX D.nd (rN i r ρ π)) hX0t h1
    have e : s' = phiC i π P Q S.X0 + fun x => algebraMap (D.nd.O i) (D.nd.O i) ((-1 : D.nd.X i → D.nd.O i) x) •
        (phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0 * phiC i π P Q S.eB) x := by
      funext x
      simp [s', sub_eq_add_neg]
    rw [e]
    exact h2
  have hes : phiC i π P Q S.eB * s' = s' := by
    show phiC i π P Q S.eB * (phiC i π P Q S.X0 - phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0 * phiC i π P Q S.eB) = _
    rw [mul_sub, heX', ← mul_assoc, ← mul_assoc, heBB']
  have hse : s' * phiC i π P Q S.eB = s' := by
    show (phiC i π P Q S.X0 - phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0 * phiC i π P Q S.eB) * phiC i π P Q S.eB = _
    rw [sub_mul, hXe', mul_assoc (phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0), heBB']
  have hsπ : s' π = 0 := by
    show phiC i π P Q S.X0 π - phiC i π P Q S.eB π * rO D.nd i (rN i r ρ π) π S.g0 * phiC i π P Q S.eB π = 0
    rw [hX0eq, heBπ]
    exact sub_eq_zero.mpr (diag_conj (r := D.R.r) (t := D.R.t) (rO D.nd i (rN i r ρ π) π S.g0) (hbd S.g0)).symm
  refine ⟨S.g0, hg0, hε, phiC i π P Q S.eB, phiC i π P Q S.e1, s', hI, hs, hes, hse, hsπ, fun x => ?_⟩
  have hx : phiC i π P Q S.eB x * repX D.nd (rN i r ρ π) S.g0 x * phiC i π P Q S.eB x + s' x = phiC i π P Q S.X0 x := by
    show phiC i π P Q S.eB x * repX D.nd (rN i r ρ π) S.g0 x * phiC i π P Q S.eB x +
      (phiC i π P Q S.X0 x - phiC i π P Q S.eB x * repX D.nd (rN i r ρ π) S.g0 x * phiC i π P Q S.eB x) =
      phiC i π P Q S.X0 x
    abel
  rw [hx]
  have hbp : blockPoly ((phiC i π P Q S.eB x).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
      ((phiC i π P Q S.X0 x).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) =
      blockPoly ((S.eB x).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
        ((S.X0 x).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
    by_cases hxπ : x = π
    · subst hxπ
      erw [hmB, hmX]
      exact blockPoly_conj P Q _ _ hPQ
    · rw [phiC_ne i π P Q _ hxπ, phiC_ne i π P Q _ hxπ]
  rw [hbp]
  have hne : 0 < Nat.card {x' // S.p x' = x} := by
    rw [hcard x]
    exact Nat.factorial_pos _
  obtain ⟨⟨x', hx'⟩⟩ := (Nat.card_pos_iff.mp hne).1
  subst hx'
  refine ⟨fun c => toK D.nd i (S.rr (1 + (c : ℕ)) x'),
    fun a b hab => rr_inj D.nd r ρ π hG x' (IsFractionRing.injective (D.nd.O i) (KK D.nd i) hab), ?_⟩
  rw [← blockPoly_map, blockPoly_eq, ← hroots x', prod_Icc_fin D.nd D.R.t, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  try rfl

theorem design_normalized_of_admitted (hA : LargeLevelLemmas.adm51 i r ρ π) (hZ : π ∈ D.nd.Z i) : InertiaElementIdempotentChoice D.nd (rN i r ρ π) π := by
  obtain ⟨S, hG⟩ := hA hZ
  exact design_normalized i r ρ π S hG


end D51b

end Formalism.MainNotions.N.K.Norm
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

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Places

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem col_not_row (l : Col i dc) : colIdx i dc l ∉ rowsN i dc := by
  intro h
  simp only [rowsN, colIdx, Finset.mem_image] at h
  obtain ⟨v, hv, hvi⟩ := h
  have hl : (l : HeightOneSpectrum (𝓞 D.host.E)) ∈ dc.col := l.2
  have hvl : v = l := idx_inj i dc (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
    (Finset.mem_union_left _ (Finset.mem_union_right _ hl)) hvi
  subst hvl
  exact Finset.disjoint_left.1 dc.disj hv hl

theorem row_not_q (w : ℕ) (hw : w ∈ rowsN i dc) : w ∉ qsN i dc := by
  intro hq
  simp only [rowsN, qsN, Finset.mem_image] at hw hq
  obtain ⟨v, hv, rfl⟩ := hw
  obtain ⟨u, hu, huv⟩ := hq
  have huv' : u = v := idx_inj i dc (Finset.mem_union_right _ hu)
    (Finset.mem_union_left _ (Finset.mem_union_left _ hv)) huv
  subst huv'
  exact D.nd.SQ_l i u (Or.inr hu) ((dc.cover u).1 (Or.inl hv))

end Places

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
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def PlugOpen : Prop :=
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
      (∀ l, LiftO (D.nd.l i) (KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l)
      (KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l)
      (mapH1 _ _ (eveS i Dd hT hrk) (ev_equiv Dd.r Dd.χ (decs D.host.E (Aw i dc) (colIdx i dc l))
        (incl (D.nd.O i) Dd.e₁) (v1S i Dd hT hrk) (eveS i Dd hT hrk) (fun a => rfl))) (e'N i dc e' (colIdx i dc l))) ∧
      (∀ l, LiftO (D.nd.l i) (KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l) (KHf.HfE₂ i dc Dd.δO l)
      (mapH1 _ _ (evES i Dd hT) (ev_equiv_triv Dd.r Dd.χ (decs D.host.E (Aw i dc) (colIdx i dc l)) (evES i Dd hT)
        (hevES i Dd hT))) (e'N i dc e' (colIdx i dc l))) ∧
      (QS.NoFixedVectorOffZ i Dd) ∧
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
      (∀ w ∈ rowsN i dc, ∀ a, a ∈ HfWS i r π dc g0 eB e₁ s Dd hD hc w ↔
      ∀ b ∈ Hf₂S i r π dc g0 eB e₁ s Dd hD hc w, cupFG (DatS i r π dc g0 eB e₁ s Dd hD hc w) a b = 0) ∧
      (∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈ FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1)) ∧
      (∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
      InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
        (qsN i dc) (ShaN i ((c : ℕ) - 1)) (FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
        (QS.ζO i dc) (QS.nQ i dc)) ∧
      ((∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), u l (g : GE D.nd) = 0) ∧
      (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), u l g = 1)) ∧
      (InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
      (FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc)) ∧
      (∀ v, (∃ a, Ine (F := D.host.E) (Av (D := D) v) ≤ QS.Io i a) ∨
      (∃ a, Ine (F := D.host.E) (Av (D := D) v) ≤ QS.IS i a) ∨
        ∃ w ∈ rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc), ∃ J : Subgroup ((decs D.host.E (Aw i dc)) w),
          FS i r π dc g0 eB e₁ s Dd hD hc QS.c1 w ≤ unrH1 (QS.resU i dc Dd QS.c1 w) J ∧
          Ine (F := D.host.E) (Av (D := D) v) ≤ J.map ((decs D.host.E (Aw i dc)) w).subtype) ∧
      (TieRow i dc (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) lenRow)

end Open

section Final

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)

end Final

end Formalism.MainNotions.N.K.St

end
end
