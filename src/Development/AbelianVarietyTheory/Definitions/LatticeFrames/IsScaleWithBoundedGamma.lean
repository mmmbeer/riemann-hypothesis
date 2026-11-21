import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

def TrueF (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    D = I.rec7 l Z ∧ I.IsTw ∧ ∃ w : World I l Z, IdE w.S.X

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem TrueF.elim {Q : D7 → Prop}
    (h : ∀ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z),
      I.IsTw → IdE w.S.X → Q (I.rec7 l Z)) {D : D7} (hD : TrueF D) : Q D := by
  obtain ⟨B, X, I, l, Z, rfl, h1, w, hw⟩ := hD
  exact h B X I l Z w h1 hw

def BigGap (D : D7) : Prop := D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)

def IsScaleWithBoundedGamma (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C' ∧ 1 ≤ large₂.CGam

theorem Row.mono {E E' : D7 → ℝ → ℝ → Prop} (hE : ∀ D L C', E' D L C' → E D L C') {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop}
    (h : Row E Q) : Row E' Q := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2
  ⟨C, a, b, hC, fun C' Cl ha hb D L u hD he hH => h C' Cl ha hb D L u hD (hE _ _ _ he) hH⟩

end GlobalTheory.Core.Rk

end
