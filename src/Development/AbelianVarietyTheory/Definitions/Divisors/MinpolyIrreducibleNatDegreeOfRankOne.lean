import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def SeesIrr (G : HTGroup p) (f : G.GAf → ℂ) : Prop :=
  ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h : G.GAf),
    f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 →
      Irreducible (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
        (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n

example (G : HTGroup p) (v wt Kf K' f') :
    cxTotal G v wt Kf (fun _ => 0) K' f' = fullSumIrr G wt Kf (fun _ => 0) 1 K' f' := by
  simp [cxTotal, cxSum, cxSumAt, fullSumIrr, Pair.term, Pair.termAt, pointSum]

example (G : HTGroup p) : SeesIrr G (fun _ => 0) := fun _ _ _ _ _ _ hf => absurd rfl hf

end GlobalTheory.LKCx
