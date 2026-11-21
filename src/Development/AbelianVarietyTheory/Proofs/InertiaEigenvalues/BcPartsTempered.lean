import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitLiftOfLiftParam

noncomputable section

namespace GlobalTheory.RowCuspPar

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

variable (D : D7)

def IsBCU (j : ℕ) (P : D.nbc.AU j) (Pa : List (Part D.naut.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
  rankIso D.nd D.naut Pa = D.R.nV ∧
  (∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Pa w = D.nbc.locAU j P w) ∧
  (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (isoLoc D.nd D.naut Pa w) ∧
    D.naut.frobEig (isoLoc D.nd D.naut Pa w) = ubc D.R.nV (D.nbc.satAU j P w)) ∧
  ∀ τ, isoInf D.nd D.naut Pa τ = D.nbc.infW j (D.nbc.wtAU j P) τ

def BcPartsTempered : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ (P : D.nbc.AU j) (Pa : List (Part D.naut.CG)), IsBCU D j P Pa →
    ∀ p ∈ Pa, ∀ w, IsSplitPl D.host w → D.naut.unr (D.naut.locG p.π w) → D.naut.tempered (D.naut.locG p.π w)

section Iso
variable {D}
open GlobalTheory.HeightCounting

theorem isoLoc_perm {Pa Pb : List (Part D.naut.CG)} (h : Pa.Perm Pb) (w : PlE D.host) :
    isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pb w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons p _ ih => simp only [List.foldr_cons, ih]
  | swap p q l =>
    simp only [List.foldr_cons]
    rw [← D.naut.lpSum_assoc, D.naut.lpSum_comm (spehLoc D.nd D.naut q w), D.naut.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem isoLoc_single (p : Part D.naut.CG) (hd : p.d = 1) (w : PlE D.host) :
    isoLoc D.nd D.naut [p] w = D.naut.locG p.π w := by
  obtain ⟨a, π, d⟩ := p
  simp only at hd
  subst hd
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

end Iso
end GlobalTheory.RowCuspPar
end
