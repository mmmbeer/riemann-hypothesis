import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.FrameExOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

def ExTb : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T : Finset (Pl E)),
  ∃ (T' : Finset (Pl E)) (b : ∀ w : Pl E, GLw n w), T'.Nonempty ∧
    (∀ w ∈ T', w ∈ F₀.Sec ∧ ¬ IsSplitAt w ∧ IsUnramU π w ∧ IsWitt n w (b w) ∧ w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad) ∧
    (∀ w, w ∉ T' → b w = F₀.d₀.b w) ∧ ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → w ∈ T'

def ExTbOf : Prop := Inert.InertPlaceEx → Inert.WittEx → InertInSec → ExTb

end PositivityTheory.Rg.BcB.F.FX

end
