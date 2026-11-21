import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg

open Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Formalism.MainNotions.DIV.Align Filter Topology

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EqualVolumeMeanCorrection

open Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr

section One
variable {D : D7} (Y : ShimX D.what₂.Tau)

def IsSlope (B : ℝ) (u : D.what₂.Tau → Fin Y.N → ℝ) (c : Y.Comp) (a : ℝ) : Prop :=
  (∀ᶠ s : ℚ in 𝓝[>] 0, 0 < Y.geoC (Y.Mbar B u s) c) ∧
    Tendsto (fun s : ℚ => Y.arSelfC (Y.Mbar B u s) c /
      (((dimY Y : ℝ) + 1) * Y.geoC (Y.Mbar B u s) c)) (𝓝[>] 0) (𝓝 a)

def bracket (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : ℝ :=
  (Real.log (bigB0 Y u g * NumberField.rootDiscr D.host.E) + |dlogL D 1|) * (∑ τ, ∑ i, |u τ i|) +
    (jS Y : ℝ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)

theorem IsSlope.unique {B : ℝ} {u : D.what₂.Tau → Fin Y.N → ℝ} {c : Y.Comp} {a b : ℝ}
    (ha : IsSlope Y B u c a) (hb : IsSlope Y B u c b) : a = b :=
  tendsto_nhds_unique ha.2 hb.2

end One

end GlobalTheory.IndefiniteRowSideFullHecke.EqualVolumeMeanCorrection

end
