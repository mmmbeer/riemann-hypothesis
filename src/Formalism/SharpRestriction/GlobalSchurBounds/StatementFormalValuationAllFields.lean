import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.KernelEntryData

noncomputable section

namespace Formalism.MainNotions.KernelEntryData

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions Finset

section Numbers

variable {n' : ℕ}

def Fv (p rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) : ℝ :=
  (gam p - 1 / (p : ℝ)) * ∑ s : Fin n', (low rb TT nu s : ℝ)

end Numbers

section Val

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)





end Val

section Core

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (Sh : Shape)

def InMM (vp : Kc) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∃ u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc, (∀ v s, u v s ∈ Oc) ∧
    Sh.InProd Oc p (fun v => Sh.hhV p v (u v)) (Sh.atPi vp Th)

def formalValuationLowerBound (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) : ℝ :=
  ∑ v, (gsum p (TT v) (nu v) + Fv p rb (TT v) (nu v) - de p Sh.r0 Sh.r1 rb (TT v) (nu v))

def FormalValuationOneSeries (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh),
    gaussGe p Oc (FormalGroupSystem.applyD (Sh.PI rb nu I) Th) (formalValuationLowerBound p Sh rb nu TT)

def FormalValuationBoundInHidaSetting : Prop :=
  ∀ (rb : ℕ) (nu : Sh.Wt) (vp : Kc) (Th : MvPowerSeries Sh.ZV Kc), HidaSetting p Oc Sh rb nu vp →
    InMM p Oc Sh vp Th → FormalValuationOneSeries p Oc Sh rb nu Th

end Core

def StatementFormalValuationAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape), FormalValuationBoundInHidaSetting p Oc Sh

section AtG

variable {p : ℕ} [Fact p.Prime]

def FL_G (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ c : ℝ,
    (∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      ∀ (φ : Y.Frm j La La') (I : (shX X j).ColCh),
        gaussGe p Y.Oc (FormalGroupSystem.applyD ((shX X j).PI (rbX X j) (nuX X j) I) (ThX Y j La La' φ)) c) →
    ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Kz j G) (c - X.dG j)

end AtG

end Formalism.MainNotions.KernelEntryData

end
