import Formalism.FormalGroupWitt.Statement

noncomputable section

open PowerSeries

universe u v

namespace Formalism.FG

open Formalism.G Formalism.LT

def shiftLogS (K : Type u) [Field K] (l : ℕ) (ε : ℤ) (m : ℕ) (j : ZMod m) :
    MvPowerSeries (ZMod m) K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then (((ε : K) * l) ^ e)⁻¹ else 0

def ltLogS (K : Type u) [Field K] (l : ℕ) (ε : ℤ) {ι : Type v} [DecidableEq ι] (r : ι) :
    MvPowerSeries ι K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single r ((l ^ 2) ^ e) then (((ε : K) * l) ^ e)⁻¹ else 0

def ShiftSOneLetter : Prop :=
  ∀ (K : Type u) [Field K] (l : ℕ) (ε : ℤ), shiftLogS K l ε 1 0 = ltLogS K l ε (0 : ZMod 1)

end Formalism.FG
