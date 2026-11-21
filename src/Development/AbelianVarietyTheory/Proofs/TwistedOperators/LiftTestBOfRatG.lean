import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormsBasisInjective
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalOfRatAt

section
noncomputable section

open Module NumberField
open scoped InnerProductSpace

namespace GlobalTheory.LiftTestCompare

section Lin

open Matrix

variable {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

def FunTest (S : Set W) : Prop :=
  ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ W), (∀ w, (∀ i, ψ i w = 0) → w = 0) ∧ ∀ s ∈ S, ∀ i, ψ i s ∈ Set.range σ

end Lin

section Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem liftTest_of_liftTestB {b : Bool} (h : LiftTestB X b) : LiftTest X := fun j => by
  obtain ⟨N, ψ, h1, h2, -⟩ := h j
  exact ⟨N, ψ, h1, h2⟩

end Cx

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Real

section ArchimedeanLeafBounds

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem toCx3_liftTestB (b : Bool) :
    LiftTestB (R.toCx3 F) b ↔ LiftTestB (cxPhase R.toRealDat F.lv2 fun j => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j)) b := by
  rw [cxPhase_eq]
  simp only [cj_cj]
  exact Iff.rfl

end ArchimedeanLeafBounds

end GlobalTheory.LiftTestCompare
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open GlobalTheory.LiftTestCompare GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.LiftRat Formalism.IndefR.Cx Formalism.IndefR.Rat

namespace GlobalTheory.TwistField

section Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def readBasis (hU : R.LUnif) (i : Fin D.R.m) :
    Module.Basis (Fin (R.nW i)) ℂ (Tw (twAt D.what₂.embLL A.v0) (R.HW i (sg0 D A)).H) :=
  Module.Basis.mk (Tw.linInd _ ((hU i (sg0 D A)).1 _ _ (Pi.basisFun D.what₂.LL (Fin (R.nW i))).linearIndependent))
    (Tw.span_top _ (span_basis R hU i (sg0 D A))).ge

theorem readBasis_coord (hU : R.LUnif) (i : Fin D.R.m) (y : Fin (R.nW i) → D.what₂.LL) (k : Fin (R.nW i)) :
    (readBasis R hU i).coord k (Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y)) = A.v0.embedding (y k) := by
  have h1 : Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y) = ∑ l, A.v0.embedding (y l) • readBasis R hU i l := by
    rw [j_eq_sum]
    refine Finset.sum_congr (M := (R.HW i (sg0 D A)).H) rfl fun l _ => ?_
    rw [readBasis, Module.Basis.mk_apply]
    show _ = cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y l)) •
      (R.FW i).j (sg0 D A) (Pi.basisFun D.what₂.LL (Fin (R.nW i)) l)
    rw [emb_eq D.what₂.embLL A.v0, cj_cj]
  rw [h1, Module.Basis.coord_apply, Module.Basis.repr_sum_self]

end Read

theorem liftTestB_of_ratG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool), R.toRealDat.LUnif → GlobalTheory.TwistField.RatG R.toRealDat (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) b := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F b hU hG
  rw [toCx3_liftTestB]
  intro j
  refine ⟨R.toRealDat.nW j, fun k => (readBasis R.toRealDat hU j).coord k,
    fun w hw => (readBasis R.toRealDat hU j).forall_coord_eq_zero_iff.1 hw, ?_, ?_⟩
  · intro t k x
    obtain ⟨y, hy⟩ := hG j t x
    refine ⟨y k, ?_⟩
    show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0)
      (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.toRealDat.thG j t (R.toRealDat.jV j t x)))
    rw [← hy, readBasis_coord]
    rfl
  · intro k (l : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)))
    refine ⟨R.toRealDat.bL F.lv2 b j l k, ?_⟩
    have hc : cpt A3.A.v0.embedding (Pi.single l (1 : D.what₂.LL)) = Pi.single l 1 := by
      funext r
      by_cases h : r = l
      · subst h; simp [cpt]
      · simp [cpt, Pi.single_apply, h]
    have h : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H)
        ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1)) = (R.toRealDat.FW j).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b j l) := by
      have h0 := liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 b j (Pi.single l 1)
      have e1 : ∑ k, (Pi.single l (1 : D.what₂.LL) : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)) → D.what₂.LL) k • R.toRealDat.bL F.lv2 b j k = R.toRealDat.bL F.lv2 b j l := by
        simp [Pi.single_apply]
      rw [e1] at h0
      refine Eq.trans ?_ h0
      erw [hc] <;> rfl
    show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0)
      (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H)
        ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1))))
    rw [h, readBasis_coord]
    rfl

end GlobalTheory.TwistField
end
end
