import Mathlib
import Formalism.LocalToGlobal.Divisibility.Inputs
import Formalism.LocalToGlobal.ExponentGrids.SecondComplementClosedValuation
import Formalism.TranslateCocycles.StatementCEStep

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols SPer IndefNum IndefCore)
open Formalism.L2.GlobalTheoryTheory (Arith.Cst Arith.Lev Arith.Lev.admitted Arith.sg Arith.elt Arith.eltBar Arith.pOf Arith.EatT)

noncomputable section

namespace Formalism.AtG

section Defs

variable {K : Type} [Field K] [NumberField K]

def PerBd [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df.Mt t, Dc.Pt u t φ F = 0 ∨ s ≤ (vw w (Dc.Pt u t φ F) : ℝ)

def colRhs {J : Type} (s : Finset J) (g : ℕ) (nn : J → K) (cg : K) (E0 : ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  -(∑ j ∈ s, (vw w (nn j) : ℝ)) + (vw w cg : ℝ) - E0 * (vw w (g : K) : ℝ)

variable (K) in

def sgOf {J : Type} (s : Finset J) (g : ℕ) (gain F E : J → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (vw w (g : K) : ℝ) * ∑ j ∈ s, (gain j + F j - E j)

end Defs

def RootOfUnityIsUnit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K) (n : ℕ), 0 < n → c ^ n = 1 →
    ∀ w : HeightOneSpectrum (𝓞 K), vw w c = 0

def IntegerShiftClosedExponent : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N) (K : Type) [Field K] [NumberField K] (sd : K)
    (δ : Formalism.L2.DIV.Code N),
    Formalism.L2.DIV.shiftZ (fun w : HeightOneSpectrum (𝓞 K) => (Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w)
      = Formalism.L2.GlobalTheoryTheory.Arith.sgExp N C Lv sd δ

end Formalism.AtG
