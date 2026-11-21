import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

section Theta
variable {P : Type} [Fintype P]

def piH (z w : P → ℂ) : ℂ := ∑ p, z p * (starRingEnd ℂ) (w p)

end Theta

section Schur
variable {T : Type} [Fintype T] {n₀ : ℕ}

end Schur

def hookProd (n : ℕ) (ν : ℕ → ℕ) : ℕ :=
  ∏ r ∈ Finset.range n, ∏ c ∈ Finset.range (ν r),
    ((ν r - c - 1) + ((Finset.Ioo r n).filter (fun r' => c < ν r')).card + 1)

example : hookProd 2 (fun r => if r = 0 then 3 else 1) = 8 := by decide

variable (D : D7)

def nuNat (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ) : ℕ := ⌊DV.nuRow D u j τ r⌋₊

def nuSize (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : ℝ :=
  ∑ r ∈ Finset.range (D.R.N i), DV.nuRow D u (i + 1) τ r

def liftNormSq (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ) : ℝ :=
  Formalism.HN.opNormAt ((D.fm u).lat i).b ((D.fm u).lat i).X ((D.fm u).lat (i + 1)).b ((D.fm u).lat (i + 1)).X
    (InfinitePlace.mk s) ((D.fm u).KL i hK) ^ 2

def mainPh (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ τ, ((∑ r ∈ Finset.range (D.R.N i), phF (DV.nuRow D u (i + 1) τ r)) -
    nuSize D u i τ * Real.log (D.gx.Om τ s))

def mainHook (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ τ, (Real.log (hookProd (D.R.N i) (nuNat D u (i + 1) τ) : ℝ) - nuSize D u i τ * Real.log (D.gx.Om τ s))

def logLev (u : D.what₂.Word) : ℝ := Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * (D.mem u).A.T)

def restTerm (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  (D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * Real.log (D.gx.thOne s ^ 2) +
    C * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 * (L.sc.L + logLev D u)

def BoundPh (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) : Prop :=
  liftNormSq D u i hK s ≤ Real.exp (mainPh D u i s + restTerm D L C u i s)

def BoundHook (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) : Prop :=
  liftNormSq D u i hK s ≤ Real.exp (mainHook D u i s + restTerm D L C u i s)

def SizeAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ),
    BoundPh D L C u i hK s ∧ BoundHook D L C u i hK s

end GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

end
