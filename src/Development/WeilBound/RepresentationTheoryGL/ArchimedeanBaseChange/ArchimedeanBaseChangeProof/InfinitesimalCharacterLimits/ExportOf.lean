import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

attribute [local instance] borelH

theorem Tr.AllLeaves.mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → t.AllLeaves Q
  | _, .leaf V _, h => hPQ _ V h
  | _, .node t₁ t₂, h => ⟨Tr.AllLeaves.mono hPQ t₁ h.1, Tr.AllLeaves.mono hPQ t₂ h.2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation

end
