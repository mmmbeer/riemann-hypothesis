import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove

noncomputable section
namespace UpperTheory.One.M
set_option maxHeartbeats 4000000

def Old.nMv (s : Sw) {D : D7} (m : Mv D) (_n : NormalizedHeckeDataPlaceholder D) : NormalizedHeckeDataPlaceholder m.D := False.elim s

def New.nMv (_ : TrivialCondition) {D : D7} (m : Mv D) (n : NTiedGPlaceholder D) : NTiedGPlaceholder m.D :=
  @NTiedGPlaceholder.mk _

def stA (s : Sw) {D : D7} (N : TwNew D) {hL : GlobalTheory.Published.LocalLanglandsGL} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (a : StA hL D cf rep)
    (rep' : N.toD7.what₂.FT → NG.FinTyp N.toD7.host.E N.toD7.R.r) (e : HEq rep' rep) :
    StA hL N.toD7 (N.cf cf) rep' where
  host := ⟨a.host.fr, a.host.jLL, a.host.embLL⟩
  jE := a.jE
  frame := a.frame
  A := LiTw.sideA N a.A
  cg := Old.cgMk s a.cg.e (Old.cgGood s a.cg) (Old.cgSurj a.cg) a.cg.zero a.cg.loc a.cg.tw a.cg.inf a.cg.csd
  au := a.au
  row := by obtain rfl : rep' = rep := eq_of_heq e; exact a.row
  fr := ⟨a.fr.jE, a.fr.eOm, a.fr.comm⟩
  fr_jE := a.fr_jE
  pht := { a.pht with }
  depth := by obtain rfl : rep' = rep := eq_of_heq e; exact a.depth
  elem := { a.elem with }
  val := { a.val with }
  labc := a.labc
  zeta := a.zeta
  omax := a.omax

end UpperTheory.One.M
