import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def markedSumIrr (G : HTGroup p) (wt sel : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol) then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

def fullSumIrr (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ ∃ μ, (Quot.out q).Mark μ then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

end GlobalTheory.LKMid
