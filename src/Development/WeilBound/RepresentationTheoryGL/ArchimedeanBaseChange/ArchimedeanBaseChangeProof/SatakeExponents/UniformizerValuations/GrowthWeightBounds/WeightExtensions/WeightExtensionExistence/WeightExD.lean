import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GrowthWeightBounds.DescentOffTorusOfFrame
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.AllLeavesMono

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE.FrameLocalData

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Loc0Ok (π : CuspSub E n) (μ : HChar E) (Sec : Set (Pl E)) (d₀ : LocData E n)
    (τ : ∀ w : Pl E, SmIrr (GLw n w)) : Prop where
  hSec : IsSection Sec
  ok₀ : d₀.Ok
  T₀ : d₀.T = ∅
  Bad₀ : d₀.Bad = ∅
  μloc : ∀ w, d₀.μ w = μ.loc w
  unif : ∀ w, IsUnifAt (d₀.ϖ w) ∧ IsUnifV E w (d₀.ϖ w : w.adicCompletion E)
  S₀ : ∀ w ∈ d₀.S₀, w ∈ Sec ∧ IsSplitAt w
  good : ∀ w ∈ Sec, w ∉ d₀.S₀ → w ∉ d₀.Bad → (∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w
  K'_lev : ∀ w ∈ d₀.S₀, IsLevel (MonoidHom.id _) (KL n w) ((d₀.K' w).subgroupOf (UL n w))
  hτ : ∀ w, π.IsLocComp w (τ w)
  τ_fix : ∀ w ∈ d₀.S₀, ∃ y ∈ fixed (τ w).ρ (d₀.K' w), y ≠ 0

def WeightExD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ φ : E →+* ℂ, ∃ lam : DomWeight n, π.HasInfChar φ (infOfWeight lam)

end PositivityTheory.Rg.BcB.F.FrE.FrameLocalData

end
