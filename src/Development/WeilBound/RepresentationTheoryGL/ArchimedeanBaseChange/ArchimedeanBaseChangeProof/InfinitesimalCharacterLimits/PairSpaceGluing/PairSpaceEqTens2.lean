import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Glue

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}


end Pair

inductive Shape : ℕ → Type
  | leaf (N : ℕ) : Shape N
  | node {r s : ℕ} : Shape r → Shape s → Shape (r + s)

def Shape.Pos : {N : ℕ} → Shape N → Prop
  | N, .leaf _ => 0 < N
  | _, .node σ₁ σ₂ => σ₁.Pos ∧ σ₂.Pos

end PositivityTheory.Rg.BcB.SpectralAccumulation.Glue

end
