import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidueLevelMultiplicity

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

variable {E : Type} [Field E] [NumberField E]

abbrev resField (PP : Pl E) : Field (kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

theorem finite_res (PP : Pl E) : Finite (kP PP) :=
  Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

theorem finite_boundedLevelClassGroupFamily (Pg : Finset (Pl E)) (r : ℕ) : Finite (G0 Pg r) := by
  haveI := fun PP : Pl E => finite_res PP
  infer_instance

def lvlMult {K : Type} [Field K] {Pg : Finset (Pl E)} {r : ℕ} (P : LevelP Pg r K) (χ : G0 Pg r → K) : K :=
  haveI := finite_boundedLevelClassGroupFamily Pg r
  haveI : Fintype P.H := Fintype.ofFinite P.H
  (Nat.card P.H : K)⁻¹ * ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K)

def nbar (Pg : Finset (Pl E)) (k : ℕ) : ℕ := ∏ PP ∈ Pg, Nat.card (kP PP) ^ k

def MultNear {K : Type} [Field K] {Pg : Finset (Pl E)} {r : ℕ} (P : LevelP Pg r K) (χ : G0 Pg r → K)
    (N : ℕ) (δ : ℝ) : Prop :=
  ∃ n : ℕ, lvlMult P χ = (n : K) ∧ |(n : ℝ) - (N : ℝ)| ≤ δ * (N : ℝ)

end GlobalTheory.IndefiniteRowSideFullHecke.ResidueLevelMultiplicity
