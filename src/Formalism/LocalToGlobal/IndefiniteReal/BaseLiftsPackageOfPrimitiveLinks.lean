import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.UnitaryTwoPackage

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

section Spec

variable {K : Type} [Field K]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type} [Fintype ι]

theorem exists_sum_of_mem_iSup {R M : Type} [Ring R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι]
    (Q : ι → Submodule R M) {y : M} (hy : y ∈ ⨆ p, Q p) : ∃ ys : ι → M, (∀ p, ys p ∈ Q p) ∧ ∑ p, ys p = y := by
  classical
  refine Submodule.iSup_induction Q (motive := fun y => ∃ ys : ι → M, (∀ p, ys p ∈ Q p) ∧ ∑ p, ys p = y) hy ?_ ?_ ?_
  · intro i x hx
    refine ⟨Pi.single i x, fun p => ?_, ?_⟩
    · by_cases h : p = i
      · subst h; simpa using hx
      · simp [h]
    · simp [Finset.sum_pi_single']
  · exact ⟨0, fun _ => zero_mem _, by simp⟩
  · rintro x y ⟨xs, hxs, rfl⟩ ⟨ys, hys, rfl⟩
    exact ⟨xs + ys, fun p => add_mem (hxs p) (hys p), by simp [Finset.sum_add_distrib]⟩

def specOp (U : ι → Submodule ℂ E) (a : ι → ℂ) : Module.End ℂ E :=
  ∑ p, a p • ((U p).starProjection : E →L[ℂ] E).toLinearMap

theorem specOp_apply (U : ι → Submodule ℂ E) (a : ι → ℂ) (x : E) :
    specOp U a x = ∑ p, a p • (U p).starProjection x := by
  simp [specOp, LinearMap.sum_apply]

theorem proj_mem (U : ι → Submodule ℂ E) (p : ι) (x : E) : (U p).starProjection x ∈ U p := by
  exact Submodule.starProjection_apply_mem (U p) x

variable (U : ι → Submodule ℂ E) (hU : ∀ p q, p ≠ q → ∀ x ∈ U p, ∀ y ∈ U q, ⟪x, y⟫_ℂ = 0)
include hU

theorem proj_of_mem [DecidableEq ι] {p q : ι} {x : E} (hx : x ∈ U q) :
    (U p).starProjection x = if p = q then x else 0 := by
  split_ifs with h
  · subst h
    exact Submodule.starProjection_eq_self_iff.2 hx
  · have ho : x ∈ (U p)ᗮ := (Submodule.mem_orthogonal _ _).2 fun u hu => hU p q h u hu x hx
    have h1 := Submodule.starProjection_eq_self_iff.2 ho
    rw [Submodule.starProjection_orthogonal_val] at h1
    exact sub_eq_self.1 h1

theorem specOp_of_mem {a : ι → ℂ} {q : ι} {x : E} (hx : x ∈ U q) : specOp U a x = a q • x := by
  classical
  rw [specOp_apply]
  simp only [proj_of_mem U hU hx, smul_ite, smul_zero]
  simp

theorem proj_specOp (a : ι → ℂ) (q : ι) (x : E) :
    (U q).starProjection (specOp U a x) = a q • (U q).starProjection x := by
  classical
  rw [specOp_apply, map_sum, Finset.sum_eq_single q]
  · rw [map_smul, Submodule.starProjection_eq_self_iff.2 (proj_mem U q x)]
  · intro p _ hp
    rw [map_smul, proj_of_mem U hU (proj_mem U p x), if_neg (Ne.symm hp), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ q) h

theorem sum_proj {x : E} (hx : x ∈ ⨆ p, U p) : ∑ p, (U p).starProjection x = x := by
  classical
  refine Submodule.iSup_induction U (motive := fun x => ∑ p, (U p).starProjection x = x) hx ?_ ?_ ?_
  · intro q x hx
    simp only [proj_of_mem U hU hx]
    simp
  · simp
  · intro x y hx hy
    simp only [map_add, Finset.sum_add_distrib, hx, hy]

omit hU in

theorem specOp_mem (a : ι → ℂ) (W : Submodule ℂ E) (hUW : ∀ p, U p ≤ W) (x : E) : specOp U a x ∈ W := by
  rw [specOp_apply]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hUW p (proj_mem U p x))

end Spec

section SpecW

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type} [Fintype ι]

theorem spec_eig (σ : K →+* ℂ) {H : Type} (P : ι → Submodule ℂ E) (W : Submodule ℂ E) (e : ι → H → K)
    (he : Function.Injective e) (hO : ∀ p q, p ≠ q → ∀ x ∈ P p ⊓ W, ∀ y ∈ P q ⊓ W, ⟪x, y⟫_ℂ = 0)
    (hS : (⨆ p, P p ⊓ W) = W) (c : ι) :
    P c ⊓ W = (⨅ T, LinearMap.ker (specOp (fun p => P p ⊓ W) (fun p => σ (e p T)) - σ (e c T) • LinearMap.id)) ⊓ W := by
  apply le_antisymm
  · intro x hx
    refine ⟨(Submodule.mem_iInf _).2 fun T => ?_, hx.2⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, specOp_of_mem (fun p => P p ⊓ W) hO hx]
    simp
  · rintro x ⟨hx, hW⟩
    have hT : ∀ T, specOp (fun p => P p ⊓ W) (fun p => σ (e p T)) x = σ (e c T) • x := fun T => by
      have h := (Submodule.mem_iInf _).1 hx T
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
      simpa using h
    have h0 : ∀ q, q ≠ c → (P q ⊓ W).starProjection x = 0 := by
      intro q hq
      obtain ⟨T, hTq⟩ : ∃ T, e q T ≠ e c T := by
        by_contra h
        push Not at h
        exact hq (he (funext h))
      have h1 := proj_specOp (fun p => P p ⊓ W) hO (fun p => σ (e p T)) q x
      rw [hT T, map_smul] at h1
      have h2 : (σ (e q T) - σ (e c T)) • (P q ⊓ W).starProjection x = 0 := by
        rw [sub_smul, ← h1, sub_self]
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact absurd (σ.injective (sub_eq_zero.1 h3)) hTq
      · exact h3
    have hx' : x ∈ ⨆ p, P p ⊓ W := by rw [hS]; exact hW
    have hsum := sum_proj (fun p => P p ⊓ W) hO hx'
    rw [Finset.sum_eq_single c (fun q _ hq => h0 q hq) (fun h => absurd (Finset.mem_univ c) h)] at hsum
    rw [← hsum]
    exact proj_mem (fun p => P p ⊓ W) c x

theorem spec_rat (σ : K →+* ℂ) {D : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (P : ι → Submodule ℂ E)
    (a : ι → K) (hO : ∀ p q, p ≠ q → ∀ x ∈ P p ⊓ LinearMap.range f, ∀ y ∈ P q ⊓ LinearMap.range f, ⟪x, y⟫_ℂ = 0)
    (hK : ∀ y : Fin D → K, y ∈ ⨆ p, (P p).comap (f.comp (cptL σ D))) :
    IsRat σ (relMat f (specOp (fun p => P p ⊓ LinearMap.range f) (fun p => σ (a p)) ∘ₗ f)) := by
  classical
  intro i k
  obtain ⟨ys, hys, hsum⟩ := exists_sum_of_mem_iSup _ (hK (Pi.single k 1))
  have hmem : ∀ p, f (cpt σ (ys p)) ∈ P p ⊓ LinearMap.range f := fun p => ⟨hys p, ⟨_, rfl⟩⟩
  have hcs : ∀ z : ι → Fin D → K, cpt σ (∑ p, z p) = ∑ p, cpt σ (z p) := fun z => by
    funext l
    simp [cpt, Finset.sum_apply]
  have hk : (Pi.single k 1 : Fin D → ℂ) = cpt σ (∑ p, ys p) := by
    rw [hsum]
    funext l
    by_cases h : l = k
    · subst h; simp [cpt]
    · simp [cpt, h]
  have key : (specOp (fun p => P p ⊓ LinearMap.range f) (fun p => σ (a p)) ∘ₗ f) (Pi.single k 1) =
      f (cpt σ (∑ p, a p • ys p)) := by
    rw [LinearMap.comp_apply, hk, hcs, map_sum, map_sum, hcs, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [specOp_of_mem (fun p => P p ⊓ LinearMap.range f) hO (hmem p), cpt_smul, map_smul]
  refine ⟨(∑ p, a p • ys p) i, ?_⟩
  simp only [relMat, Matrix.of_apply]
  rw [key, hf (solve_spec f (⟨_, rfl⟩ : f (cpt σ (∑ p, a p • ys p)) ∈ LinearMap.range f))]
  rfl

end SpecW

section Structs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} {cr : Crd A fc} {b : Bool}

theorem rowsK (hW : (lv (fc X.zs) b).WF) (h3 : X.H3 cr b) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    y ∈ ⨆ p, X.Ep cr b p := by
  have hle : (⨆ p, (lv (fc X.zs) b).Qp Bs.μ0 p) ≤ ⨆ p, X.Ep cr b p :=
    iSup_mono fun p x hx => (X.mem_Ep cr b p x).2 ((h3 p x).1 hx)
  exact hle (hW.Qp_top ▸ Submodule.mem_top)

theorem liftsK (ht : (lv (fc X.zs) b).Types) (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (h5 : X.H5 cr b)
    (hr : X.RATth cr b) (h3W : X.H3W cr b) (j : Bs.J) (y : Fin (X.dW b j) → K) : y ∈ ⨆ p, X.WpK b j p := by
  obtain ⟨x, rfl⟩ := (X.liftMat_bij cr b hk he hn h5 hr j Bs.μ0).2 y
  have hx : x ∈ ⨆ p, (lv (fc X.zs) b).Zp j Bs.μ0 p := by
    rw [ht j]
    exact Submodule.mem_top
  have hle : (⨆ p, (lv (fc X.zs) b).Zp j Bs.μ0 p).map (X.liftMat cr b j Bs.μ0).mulVecLin ≤ ⨆ p, X.WpK b j p := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun p => Submodule.map_le_iff_le_comap.2 fun z hz => by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, X.mem_WpK b j p, X.key_lift cr b h5 hr j Bs.μ0 z]
      exact (h3W j p z).1 hz
  exact hle (Submodule.mem_map_of_mem hx)

theorem heckeRows_spec (h2 : X.H2 cr b) (hE : X.PartsE b) (hQ : ∀ y, y ∈ ⨆ p, X.Ep cr b p) (cf : ConvFace Bs) :
    Nonempty (X.HeckeRowsC cr b cf) := by
  have hO' : ∀ p q, p ≠ q → ∀ x ∈ X.EEp p ⊓ LinearMap.range (X.iC cr b Bs.μ0),
      ∀ y ∈ X.EEp q ⊓ LinearMap.range (X.iC cr b Bs.μ0), ⟪x, y⟫_ℂ = 0 := by
    rw [h2.2.2]
    exact hE.1
  refine ⟨{ hC := fun T => specOp (fun p => X.EEp p ⊓ X.EEl b) (fun p => Bs.v0.embedding (cf.ev p T)),
            maps := fun T e _ => specOp_mem _ _ _ (fun _ => inf_le_right) e,
            rat := fun T => ?_,
            eig := fun c => spec_eig Bs.v0.embedding X.EEp (X.EEl b) cf.ev cf.ev_inj hE.1 hE.2 c }⟩
  have h := spec_rat Bs.v0.embedding (X.iC cr b Bs.μ0) h2.1 X.EEp (fun p => cf.ev p T) hO' hQ
  rw [h2.2.2] at h
  exact h

theorem heckeW_spec (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (hP : X.PartsW b)
    (hK : ∀ j y, y ∈ ⨆ p, X.WpK b j p) (cf : ConvFace Bs) : Nonempty (X.HeckeWC b cf) :=
  ⟨{ hC := fun j T => specOp (fun p => X.Wp j p ⊓ LinearMap.range (X.w0C b j)) (fun p => Bs.v0.embedding (cf.ev p T)),
     maps := fun _ _ _ => specOp_mem _ _ _ (fun _ => inf_le_right) _,
     rat := fun j T => spec_rat Bs.v0.embedding (X.w0C b j) (X.principal_form_injective b hk he hn j) (X.Wp j) (fun p => cf.ev p T)
       (hP j).1 (hK j),
     eig := fun j c => spec_eig Bs.v0.embedding (X.Wp j) (LinearMap.range (X.w0C b j)) cf.ev cf.ev_inj (hP j).1 (hP j).2 c }⟩

end CxData

end Structs

section Fields3

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

theorem heckeRB_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false cf) :=
  CxData.heckeRows_spec (hR.what₂ false).1 (hR.partsE false)
    (CxData.rowsK (hR.rowHyp false).wf (hR.rowHyp false).h3) cf

theorem heckeRC_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true cf) :=
  CxData.heckeRows_spec (hR.what₂ true).1 (hR.partsE true)
    (CxData.rowsK (hR.rowHyp true).wf (hR.rowHyp true).h3) cf

theorem heckeWB_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeWC false cf) :=
  CxData.heckeW_spec hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.partsW
    (CxData.liftsK hR.types0 hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh hR.liftHyp0.h3W) cf

end Fields3

end Formalism.IndefR.Cx
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Three2

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure HkDat3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) where

  Hk : Type

  ev : A3.fam3.base3.Ix → Hk → D.what₂.LL

  ev_inj : Function.Injective ev

namespace RealDat3

variable (R : RealDat3 D A3 Ks) (F : Face3 D A3)

def convOf (H : HkDat3 A3) : ConvFace A3.fam3.base3 where
  primes := R.toRealDat.fam_Sb ∧ R.toRealDat.fam_pl_onto ∧ R.in_onto
  symLevel := R.toRealDat.grp_levels F.lv2
  sg0 := A3.A.v0.embedding
  Hk := H.Hk
  ev := H.ev
  ev_inj := H.ev_inj

def PHecke : Prop := (∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE) ∧ ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW

def PGUnit : Prop :=
  (∀ (g : G) (x y : (R.toCx3 F).EE), ⟪R.gEx F g x, R.gEx F g y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    ∀ j (g : G) (x y : (R.toCx3 F).W j), ⟪R.gWx F j g x, R.gWx F j g y⟫_ℂ = ⟪x, y⟫_ℂ

def PGEquiv : Prop := GEquiv3 A3 (R.toCx3 F) (R.gEx F) ∧ LiftGroupEquivariance A3 (R.toCx3 F) (R.gWx F)

def PLevE : Prop :=
  LevType3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) false F.P0 F.ψ0 ∧
    LevType3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) true F.P1 F.ψ1

def PrincipalLevelBijective : Prop := PrincipalLevelBijectivity A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)

def PLevW : Prop :=
  LevelTypeOfLifts A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) false F.P0 F.ψ0

def PPos : Prop := 0 < R.kap ∧ ∀ i t p v, 0 < R.lam3 i t p v

def PThmA : Prop :=
  ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp3 i) fun p => R.lam3 i t p A3.A.v0

def PThmB : Prop := Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN R.kap

variable {R F}

theorem conv_of (hC : R.WeakCharacterisation F) (H : HkDat3 A3) : IndefConv A3.fam3.base3 R.mu (R.convOf F H) :=
  ⟨⟨hC.base.fam.Sb, hC.base.fam.pl_onto, hC.inert.onto⟩, hC.tup.mu_used, hC.base.grp.levels, rfl⟩

theorem kFormR_of (hM : R.toRealDat.IsModels) : (R.toCx3 F).KFormR := by
  first
    | exact RealDat.kFormR_of (R := R.toRealDat) (F := F.lv2) hM
    | exact RealDat.kFormR_of hM

theorem kFormL_of (hM : R.toRealDat.IsModels) : (R.toCx3 F).KFormL := by
  first
    | exact RealDat.kFormL_of (R := R.toRealDat) (F := F.lv2) hM
    | exact RealDat.kFormL_of hM

theorem jIsoR_of (hM : R.toRealDat.IsModels) : (R.toCx3 F).JIsoR F.cv := by
  first
    | exact RealDat.jIsoR_of (R := R.toRealDat) (F := F.lv2) hM
    | exact RealDat.jIsoR_of hM

theorem jIsoL_of (hM : R.toRealDat.IsModels) : (R.toCx3 F).JIsoL F.cv := by
  first
    | exact RealDat.jIsoL_of (R := R.toRealDat) (F := F.lv2) hM
    | exact RealDat.jIsoL_of hM

theorem kForm_of (h : R.toRealDat.LUnif) (b : Bool) : (R.toCx3 F).KForm b := RealDat.kForm (F := F.lv2) h b

theorem ewNorm (b : Bool) : (R.toCx3 F).EWnorm b := by
  first
    | exact RealDat.ewNorm (R := R.toRealDat) (F := F.lv2) b
    | exact RealDat.ewNorm b

theorem height_change_of_D0 (h : R.IsTup) : (R.toCx3 F).H0 := by
  refine ⟨h.mu_conj, fun w => ⟨h.mu_ne w, fun hne => ?_⟩⟩
  by_contra hw
  exact hne (h.mu_off w hw)

theorem prod_lamN (t : T) (p : A3.fam3.base3.Ix) :
    ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j : Fin D.R.m, R.lam3 j t p A3.A.v0 := by
  symm
  refine Finset.prod_bij (fun (i : Fin D.R.m) _ => (i : ℕ) + 1) ?_ ?_ ?_ ?_
  · intro i _
    have := i.isLt
    simp only [Finset.mem_Icc]
    omega
  · intro a₁ _ a₂ _ h
    exact Fin.ext (by omega)
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, Nat.sub_add_cancel (by omega)⟩
  · intro a _
    simp [lamN]

theorem adjoint_smul' {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (c : ℂ) (f : E →ₗ[ℂ] F) :
    LinearMap.adjoint (c • f) = starRingEnd ℂ c • LinearMap.adjoint f := map_smulₛₗ LinearMap.adjoint c f

theorem phase_cancel {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {c : ℂ} (hc : starRingEnd ℂ c * c = 1) (f : E →ₗ[ℂ] F)
    (w : F) : (c • f) (LinearMap.adjoint (c • f) w) = f (LinearMap.adjoint f w) := by
  simp only [adjoint_smul', LinearMap.smul_apply, map_smul, smul_smul]
  rw [hc, one_smul]

private theorem adjoint_tw_map {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) :
    LinearMap.adjoint (Tw.map s f) = Tw.map s (LinearMap.adjoint f) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [Tw.inner_eq, Tw.inner_eq]
  exact congrArg (cj s) (LinearMap.adjoint_inner_left f (Tw.out y) (Tw.out x))

private theorem tw_map_adjoint_apply_of_eigen {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F)
    (l : ℝ) (e : Tw s F) (he : f (LinearMap.adjoint f (Tw.out e)) = (l : ℂ) • Tw.out e) :
    Tw.map s f (LinearMap.adjoint (Tw.map s f) e) = (l : ℂ) • e := by
  rw [adjoint_tw_map]
  show Tw.mk s (f (LinearMap.adjoint f (Tw.out e))) = cj s (l : ℂ) • Tw.out e
  rw [he, cj_ofReal]
  rfl

private theorem smul_tw_map_adjoint_apply_of_unit_modulus {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {c : ℂ}
    (hc : starRingEnd ℂ c * c = 1) (f : E →ₗ[ℂ] F) (l : ℝ) (e : Tw s F)
    (he : f (LinearMap.adjoint f (Tw.out e)) = (l : ℂ) • Tw.out e) :
    (c • Tw.map s f) (LinearMap.adjoint (c • Tw.map s f) e) = (l : ℂ) • e := by
  rw [phase_cancel hc]
  exact tw_map_adjoint_apply_of_eigen f l e he


set_option maxHeartbeats 1000000 in
theorem thmAop_of (hph : R.phase) (h : R.PThmA) (b : Bool) : (R.toCx3 F).ThmAop b := by
  intro j t p w hw
  have hw1 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) w ∈ R.Wp3 j p := (Submodule.mem_inf.mp hw).1
  have hc : starRingEnd ℂ (R.phs j) * R.phs j = 1 := by
    rw [Complex.conj_mul', (hph j).1]; simp
  refine smul_tw_map_adjoint_apply_of_unit_modulus hc (R.thG j t) (R.lam3 j t p A3.A.v0) w ?_
  exact h j t p _ hw1

set_option maxHeartbeats 1000000 in
theorem thmBop_of (h : R.PThmB) (b : Bool) : (R.toCx3 F).ThmBop b := by
  intro t p e he
  have he1 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e ∈ R.EEp3 p := he.1
  have key : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.Th t) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.Th t)) e) =
      ((R.kap * ∏ j : Fin D.R.m, R.lam3 j t p A3.A.v0 : ℝ) : ℂ) • e := by
    rw [Tw.adjoint_map]
    show Tw.mk _ (R.Th t (LinearMap.adjoint (R.Th t) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e))) = _
    have h2 := h t p (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e) he1
    rw [LinearMap.comp_apply] at h2
    rw [h2, Tw.mk_smul, cj_ofReal, prod_lamN]
    rfl
  exact key

end RealDat3

structure PrimRows3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  heckeR : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint
  heckeL : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint
  hecke : R.PHecke F
  gUnit : R.PGUnit F
  gEquiv : R.PGEquiv F
  block : (R.toCx3 F).zs.InBlock
  rowTest : Formalism.IndefR.Rat.RowTest (R.toCx3 F)
  liftTest : Formalism.IndefR.Rat.LiftTest (R.toCx3 F)
  liftTestB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false
  liftOnto : ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW
  pos : ∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos
  posScal : R.PPos
  levE : R.PLevE F
  h2P : R.PrincipalLevelBijective F
  thmB : R.PThmB
  sumE : ∀ b, (R.toCx3 F).PartsE b
  unif : R.toRealDat.LUnif
  mLat : (R.toCx3 F).MLat false
  levW : R.PLevW F
  thmA : R.PThmA
  sumW : (R.toCx3 F).PartsW false
  scalConj : (R.toCx3 F).GalD F.cr false
  dimParts : (R.toCx3 F).DimParts false

structure UnusedChoiceStatements (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  ex : R.toRealDat.ExAt
  conj : R.toRealDat.PConj
  levelW : R.toRealDat.LLevelW F.lv2
  integral : R.toRealDat.LIntegral

structure CovolumeOntoIsometryConditions (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (H : HkDat3 A3) (C CH : ℝ) : Prop extends PrimRows3 R F where
  w1 : ∀ w, (R.toCx3 F).W1 F.cr (R.num F C CH) w → w ∈ R.twPl
  covol : ((R.toCx3 F).data F.cr false).L3 (R.num F C CH)
  onto : ((R.toCx3 F).data F.cr false).ON (R.num F C CH)
  lamLow : ((R.toCx3 F).data F.cr true).L6 (R.num F C CH)
  seeIso : (R.toCx3 F).SEEIso sEE
  miStar : (R.toCx3 F).MIstar2 (F.eV (R.toCx3 F).zs) sEE
  fun0 : ((R.toCx3 F).data F.cr false).FUN (R.num F C CH)

theorem complex_data_conditions_base_level_of_primitive_links {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) :
    ComplexDataConditionsBaseLevel A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) s (U2.eigensystemChoice A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hP.hecke.2.choose) hP.hecke.1.choose hP.hecke.2.choose (R.gEx F)
      (R.gWx F) where
  kFormR := RealDat3.kFormR_of hC.base.models
  kFormL := RealDat3.kFormL_of hC.base.models
  jIsoR := RealDat3.jIsoR_of hC.base.models
  jIsoL := RealDat3.jIsoL_of hC.base.models
  npTie := ⟨rfl, rfl⟩
  ok := hOk
  sep := hsep
  heckeR := hP.heckeR
  heckeL := hP.heckeL
  thetaR := hP.hecke.1.choose_spec
  thetaL := hP.hecke.2.choose_spec
  gUnit := hP.gUnit.1
  gEquiv := hP.gEquiv.1
  lev0 := hP.levE.1
  lev1 := hP.levE.2
  h2P := hP.h2P
  gUnitL := hP.gUnit.2
  gEquivL := hP.gEquiv.2
  lower_level_lift_type := hP.levW
  inBlock := hP.block
  rowTest := hP.rowTest
  liftTest := hP.liftTest
  pos := hP.pos
  h0 := RealDat3.height_change_of_D0 hC.tup
  h4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
  thmBop := RealDat3.thmBop_of hP.thmB
  partsE := hP.sumE
  kForm := RealDat3.kForm_of hP.unif false
  mLat := hP.mLat
  ewNorm := RealDat3.ewNorm false
  thmAop := RealDat3.thmAop_of hC.phase hP.thmA false
  partsW := hP.sumW
  base_lift_test := hP.liftTestB
  galD := hP.scalConj
  dimParts := hP.dimParts
  eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hP.hecke.2.choose (R.gWx F) hOk
    (RealDat3.kFormR_of hC.base.models) (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoR_of hC.base.models)
    (RealDat3.jIsoL_of hC.base.models) hP.rowTest hP.liftTest hP.heckeL hP.hecke.2.choose_spec hP.gUnit.2 hP.gEquiv.2 hP.levW
    hP.sumW (hP.liftOnto _ hP.hecke.2.choose_spec)).1
  typ0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hP.hecke.2.choose (R.gWx F) hOk
    (RealDat3.kFormR_of hC.base.models) (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoR_of hC.base.models)
    (RealDat3.jIsoL_of hC.base.models) hP.rowTest hP.liftTest hP.heckeL hP.hecke.2.choose_spec hP.gUnit.2 hP.gEquiv.2 hP.levW
    hP.sumW (hP.liftOnto _ hP.hecke.2.choose_spec)).2

theorem base_lifts_package_of_primitive_links {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    {sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH} {H : HkDat3 A3} {C CH : ℝ} (hC : R.WeakCharacterisation F)
    (hP : CovolumeOntoIsometryConditions R F sEE H C CH) :
    PrimitiveStatementsBaseLiftsOnly A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) s (U2.eigensystemChoice A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hP.hecke.2.choose) (F.eV (R.toCx3 F).zs) sEE C CH hP.hecke.1.choose
      hP.hecke.2.choose (R.gEx F) (R.gWx F) (R.convOf F H) where
  kFormR := RealDat3.kFormR_of hC.base.models
  kFormL := RealDat3.kFormL_of hC.base.models
  jIsoR := RealDat3.jIsoR_of hC.base.models
  jIsoL := RealDat3.jIsoL_of hC.base.models
  npTie := ⟨rfl, rfl⟩
  ok := hOk
  sep := hsep
  heckeR := hP.heckeR
  heckeL := hP.heckeL
  thetaR := hP.hecke.1.choose_spec
  thetaL := hP.hecke.2.choose_spec
  gUnit := hP.gUnit.1
  gEquiv := hP.gEquiv.1
  lev0 := hP.levE.1
  lev1 := hP.levE.2
  h2P := hP.h2P
  gUnitL := hP.gUnit.2
  gEquivL := hP.gEquiv.2
  lower_level_lift_type := hP.levW
  inBlock := hP.block
  rowTest := hP.rowTest
  liftTest := hP.liftTest
  eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hP.hecke.2.choose (R.gWx F) hOk
    (RealDat3.kFormR_of hC.base.models) (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoR_of hC.base.models)
    (RealDat3.jIsoL_of hC.base.models) hP.rowTest hP.liftTest hP.heckeL hP.hecke.2.choose_spec hP.gUnit.2 hP.gEquiv.2 hP.levW
    hP.sumW (hP.liftOnto _ hP.hecke.2.choose_spec)).1
  typ0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hP.hecke.2.choose (R.gWx F) hOk
    (RealDat3.kFormR_of hC.base.models) (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoR_of hC.base.models)
    (RealDat3.jIsoL_of hC.base.models) hP.rowTest hP.liftTest hP.heckeL hP.hecke.2.choose_spec hP.gUnit.2 hP.gEquiv.2 hP.levW
    hP.sumW (hP.liftOnto _ hP.hecke.2.choose_spec)).2
  pos := hP.pos
  h0 := RealDat3.height_change_of_D0 hC.tup
  w1 := hP.w1
  h4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
  thmBop := RealDat3.thmBop_of hP.thmB
  partsE := hP.sumE
  kForm := RealDat3.kForm_of hP.unif false
  mLat := hP.mLat
  ewNorm := RealDat3.ewNorm false
  thmAop := RealDat3.thmAop_of hC.phase hP.thmA false
  partsW := hP.sumW
  base_lift_test := hP.liftTestB
  galD := hP.scalConj
  dimParts := hP.dimParts
  l3 := hP.covol
  on := hP.onto
  l6 := hP.lamLow
  evTie := EvTie.evTie_of_ok hOk F _
  seeIso := hP.seeIso
  miStar := hP.miStar
  conv := RealDat3.conv_of hC H
  heckeRB := heckeRB_of (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP.toPrimRows3) _
  heckeWB := heckeWB_of (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP.toPrimRows3) _
  heckeRC := heckeRC_of (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP.toPrimRows3) _
  fun0 := hP.fun0

end Three2

section Geo3

open Formalism.L2.Geo Formalism.MainNotions Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Gm : DV.Geo D.what₂.LL} {Lv : Type} {Fam : ShimFam D Gm Lv} (Kp : FormsKPkg Fam) [Algebra Kp.fs.KO D.what₂.LL]

structure GeometricWeakCharacterisation (R : RealDat3 D A3 Kp.fs.KO) (F : Face3 D A3) (e : G ≃* Kp.Hb) : Prop where
  char : R.WeakCharacterisation F
  geo : GeoTied Kp R.toRealDat e
  conj : R.toRealDat.PConj

end Geo3

end Formalism.IndefR.Links

end
end
