import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.OXModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical in

def setLam {D : D7} (X : DivX D) (l : ℕ → D.what₂.FT → (D.what₂.LL →+* ℂ) → ℝ) : DivX D :=
  { X with
    logLam := fun j σ e => if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j σ) else l j σ e
    logLam_base := fun _ _ => if_pos rfl }





section Reading

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

open Classical in

def lamOf (_Z : R3.ReadL R F X0 Y) (lab : D.what₂.FT → A3.fam3.base3.Ix) (j : ℕ) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if h : j - 1 < D.R.m then
    if D.what₂.isot j σ = ⊥ then 0 else Real.log ((R3.s0Of R F).lam ⟨j - 1, h⟩ A3.A.μ0 (lab σ) (InfinitePlace.mk e))
  else 0


def LamVia (Z : R3.ReadL R F X0 Y) (cOf : D.what₂.FT → A3.fam3.base3.Ix) : Prop :=
  ∀ (i : Fin D.R.m) (c : A3.fam3.base3.Ix), (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) =
    Submodule.span ℂ ((Z.jW i) '' ((R3.s0Of R F).Wp i c : Set (Fin ((R3.s0Of R F).dW i) → D.what₂.LL)))

theorem overIx_of_via {Z : R3.ReadL R F X0 Y} {cOf} (h : LamVia Z cOf) (σ) : OverIx Z σ (cOf σ) := fun i => by
  rw [← h i]
  exact le_iSup (fun τ : {τ : D.what₂.FT // cOf τ = cOf σ} => D.what₂.isot ((i : ℕ) + 1) τ.1) ⟨σ, rfl⟩

theorem eq_of_overIx {Z : R3.ReadL R F X0 Y} {cOf} (h : LamVia Z cOf) {i : Fin D.R.m}
    (hi : iSupIndep (D.what₂.isot ((i : ℕ) + 1))) {σ c} (h0 : D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥) (hc : OverIx Z σ c) : c = cOf σ := by
  by_contra hne
  have h1 := hc i
  rw [← h i] at h1
  refine h0 ((hi σ).eq_bot_of_le (h1.trans (iSup_le fun τ => ?_)))
  exact le_iSup₂_of_le (f := fun j (_ : j ≠ σ) => D.what₂.isot ((i : ℕ) + 1) j) τ.1 (fun e => hne (τ.2.symm.trans (congrArg cOf e))) le_rfl

theorem logLam_eq {Z : R3.ReadL R F X0 Y} {X : DivX D} (hX : LamAre Z X) {cOf} (h : LamVia Z cOf) {i : Fin D.R.m}
    (hi : iSupIndep (D.what₂.isot ((i : ℕ) + 1))) {σ} (h0 : D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥) {e} (he : e ≠ D.what₂.embLL) :
    X.logLam ((i : ℕ) + 1) σ e = Real.log ((R3.s0Of R F).lam i A3.A.μ0 (cOf σ) (InfinitePlace.mk e)) := by
  obtain ⟨lab, hl, hv⟩ := hX
  rw [(hv i σ e he).1 h0, eq_of_overIx h hi h0 (hl σ ⟨_, overIx_of_via h σ⟩)]






end Reading

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}



end GlobalTheory.Mem.Top.Bl.OXModel

end
