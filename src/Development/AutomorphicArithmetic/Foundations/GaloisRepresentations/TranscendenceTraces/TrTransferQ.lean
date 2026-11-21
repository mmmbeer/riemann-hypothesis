import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.WeilBound.CoreStatements.PadicHodgeComparison.NormalSchemeSpectra.IsNormalSch
import Development.EtaleCohomology.EtaleTrace.LTransferCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC PositivityTheory.AutomorphicGaloisHodgeTate

namespace UpperTheory.Gal.TranscendenceTraces

def Good (l : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) : Prop := IsFinite p ∧ IsLocallyNoetherian S ∧ Nml S ∧ IsUnit (l : Γ(S, ⊤))

def TrPushQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) [IsFinite h]
  [IsFinite p] (w : Wt Z), IsWt (h ≫ p) w → IsUnit (l : Γ(S, ⊤)) →
  trHQ l (h ≫ p) w n i ∘ₗ pullHQ l (sch.map h) n i = trHQ l p (w.push h) n i

open LateralTheory.EtaleTrace.Tr (Splits LSpl LLoc LTau)

def TrTransferQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p],
  IsUnit (l : Γ(S, ⊤)) → trHQ l p (Wt.const Z 1) n i = Tr.pushHQ l p n i

end UpperTheory.Gal.TranscendenceTraces

end
