import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def TrueS (D : D7) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Formalism.L2.SG.Pf.LocCP.LocTied D ∧ Nonempty (Formalism.L2.SG.SpectralTiesReal.STies D)

def e0 (D : D7) (C0 : ℝ) : ℝ := 2 * C0 / AdmissibleBoundsFromSource.Gam D + 2 * AdmissibleBoundsFromSource.xK D

def HasLed (D : D7) (L CG : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ large₂.CGam = CG

def DiagAtScale : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → 1 ≤ C0 → ∃ CG₀ : ℝ, ∀ CG : ℝ, CG₀ ≤ CG →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → TFrameAt D → HasLed D L CG → GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT → StandingNumericalData D C0 →
      ∀ u, GlobalTheory.Core.Rk.DiagS D u (e0 D C0)

def HD (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT ∧ GlobalTheory.Core.Deg.DataNW D ∧ TFrameAt D

def gamL (D : D7) (L C : ℝ) : ℝ := Real.exp (C * (D.R.m : ℝ) ^ 5 * D.R.f * L)

def SDiagAt (D : D7) (u : D.what₂.Word) (Γ c : ℝ) : Prop :=
  GlobalTheory.Core.Rk.hsDev D u ≤
    4 * ((Γ + 1) * (D.duS u : ℝ) ^ 2 / D.what₂.Dstar + (D.duS u : ℝ) * Real.exp (-(c * D.R.k * D.R.f * Real.log D.R.k))) +
      2 * (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def SDiag (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → HD D L C' Cl Cg cb Cu cT CT → ∀ u, SDiagAt D u (gamL D L CD) c

def OneLed (gen : Bool) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → GlobalTheory.Core.Deg.DataNW D → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (if gen then (Y.tO u u).genSet else (Y.tO u u).ngSet)) ≤
        gamL D large₂.sc.L C * ddC X Y u u
end GlobalTheory.Core.Diag
