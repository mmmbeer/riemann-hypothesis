import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn heckePol)

namespace UpperTheory.Gal.Mod

def CorrOpEq : Prop := ∀ (l : ℕ) [Fact l.Prime] {S : Scheme.{0}} (c : TranscendenceTraces.Corr S S) [Etale c.p], c.w = Wt.const _ 1 →
  IsUnit (l : Γ(S, ⊤)) → ∀ T, IsCorrOp l c.p c.f T → T = DirectSum.lmap fun k : ℤ => c.opQ l k 0

end UpperTheory.Gal.Mod

end
