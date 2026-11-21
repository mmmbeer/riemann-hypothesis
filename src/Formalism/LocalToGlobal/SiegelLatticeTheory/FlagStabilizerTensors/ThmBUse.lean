import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.ThmBUse

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.FourierDecayAlt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core

variable {D : D7} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
  {Cl Nu : Type} (N : PN.NGData τ D.host.E D.R.rS Cl Nu)

def IsRowPt (D : D7) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  IsBPt D T T' w ∧ ∀ v, 0 < Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w)

def PtTie (T T' : ℕ) : Prop :=
  ∀ γ, PN.IsPt X N γ → ∃ w : Point D.host.E (D.R.rS + 1), RowsConc.toPts w = γ ∧ IsRowPt D T T' w

def WtTie (T T' A : ℕ) (Cw : ℝ) : Prop :=
  ∀ γ (w : Point D.host.E (D.R.rS + 1)), PN.IsPt X N γ → RowsConc.toPts w = γ → IsRowPt D T T' w →
    Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ * N.n γ * (N.NG γ * N.ND γ) ^ (A * (D.R.rS + 1) ^ 2) ≤
      Cw * (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
        normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2))

def JacobianSquareDominatedAtPoints {Ch Cg : ℝ} {T T' : ℕ} {b : ℝ} (Bd : BData D Ch Cg T T' b 0) (Cj : ℝ) : Prop :=
  ∀ γ (w : Point D.host.E (D.R.rS + 1)), PN.IsPt X N γ → RowsConc.toPts w = γ → IsRowPt D T T' w →
    ENNReal.ofReal (N.jacobianSquareBound γ) ≤ ENNReal.ofReal Cj * JSq D Bd w

def NormTie {Ch Cg : ℝ} {T T' : ℕ} {b : ℝ} (Bd : BData D Ch Cg T T' b 0) (Cw Cj Cb TB : ℝ) : Prop :=
  ENNReal.ofReal (Cw * Cj) *
      (ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D Bd) ≤ ENNReal.ofReal TB

def Ties (Ch Cg : ℝ) (T T' : ℕ) (b : ℝ) (A : ℕ) (Cb TB : ℝ) : Prop :=
  ∃ (Bd : BData D Ch Cg T T' b 0) (Cw Cj : ℝ), 0 ≤ Cw ∧ 0 ≤ Cj ∧
    (∀ v, AllGaps (Bd.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) ∧
    PtTie X N T T' ∧ WtTie X N T T' A Cw ∧ JacobianSquareDominatedAtPoints X N Bd Cj ∧ NormTie Bd Cw Cj Cb TB

end Core

section Sum

variable {D : D7} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
  {Cl Nu : Type} (N : PN.NGData τ D.host.E D.R.rS Cl Nu)

theorem term_le {T T' A : ℕ} {Ch Cg b Cw Cj : ℝ} (Bd : BData D Ch Cg T T' b 0) (hCw : 0 ≤ Cw)
    (hJ0 : ∀ γ, 0 ≤ N.jacobianSquareBound γ) (hW : WtTie X N T T' A Cw) (hJ : JacobianSquareDominatedAtPoints X N Bd Cj)
    (γ : PN.Pts D.host.E D.R.rS) (w : Point D.host.E (D.R.rS + 1)) (hγ : PN.IsPt X N γ)
    (hw : RowsConc.toPts w = γ) (hb : IsRowPt D T T' w) :
    ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ * N.n γ * (N.NG γ * N.ND γ) ^ (A * (D.R.rS + 1) ^ 2) * N.jacobianSquareBound γ) ≤
      ENNReal.ofReal Cw * ENNReal.ofReal Cj *
        (ENNReal.ofReal (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
          normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * JSq D Bd w) := by
  have h1 : ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ * N.n γ * (N.NG γ * N.ND γ) ^ (A * (D.R.rS + 1) ^ 2)) ≤
      ENNReal.ofReal Cw * ENNReal.ofReal (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
        normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) := by
    rw [← ENNReal.ofReal_mul hCw]
    exact ENNReal.ofReal_le_ofReal (hW γ w hγ hw hb)
  rw [ENNReal.ofReal_mul' (hJ0 γ)]
  calc _ ≤ (ENNReal.ofReal Cw * ENNReal.ofReal (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
          normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2))) * (ENNReal.ofReal Cj * JSq D Bd w) :=
        mul_le_mul' h1 (hJ γ w hγ hw hb)
    _ = _ := by ring

def jointNormBoundUnrotated (D : D7) (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    (∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    BSum D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X


end Sum

section Step

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData

def JointNormBoundUniform : Prop :=
  ∀ Aw Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, jointNormBoundUnrotated D Aw Ch Cg Cb

theorem J2of_nonneg' {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (γ : PN.Pts D.host.E D.R.rS) : 0 ≤ J2of Y u u' ν γ := by
  unfold J2of
  split_ifs <;> positivity

end Step

section Wt

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.L2.SG.NGData

def WtTieConc : Prop :=
  ∀ (D : D7) (T T' A : ℕ) (w : Point D.host.E (D.R.rS + 1)), IsRowPt D T T' w →
    Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (toPts w) * nPt D.host.rdE D.R.k (T * T') (toPts w) *
              (NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w)) ^ (A * (D.R.rS + 1) ^ 2) ≤
      1 * (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
        normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2))

theorem weight_normalized (h : WtTieConc) {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (A : ℕ) :
    WtTie (Y.tO u u') (NOf2 Y u u' νL νB ng) (Tu D u : ℕ) (Tu D u' : ℕ) A 1 := by
  intro γ w _ hw hb
  subst hw
  exact h D _ _ A w hb

end Wt

section FromStmtU

end FromStmtU

end Formalism.L2.SG.ThmBUse
