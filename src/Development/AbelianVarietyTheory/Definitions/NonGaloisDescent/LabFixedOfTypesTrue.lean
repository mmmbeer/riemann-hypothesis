import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OExt

noncomputable section
namespace GlobalTheory.CoefDuty.OPinModel
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.Mem.Col2

def LabFixed (D : D7) : Prop :=
  GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩

theorem labFixed_withLoc {D : D7} (L : LocAll (lay0 D)) : LabFixed (withLoc L) ↔ LabFixed D := Iff.rfl

theorem labFixed_iff {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) : LabFixed D ↔ LabFixed a.nt.D := by
  have e : ∀ D', D' = withLoc a.nt.L → (LabFixed D' ↔ LabFixed a.nt.D) := by
    rintro _ rfl
    exact labFixed_withLoc _
  exact e D a.nt.eq

theorem labFixed_of_typesTrue {D : D7} {P : PiBar D.host} {W : Omg D.host} (h : TypesTrue D.ntypes P W) : LabFixed D :=
  fun k => ⟨(h.teich k).symm, h.ser k⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem lab_of_rows {hL : GlobalTheory.Published.LocalLanglandsGL} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch} (c : NCore hL t n) : LabFixed c.a.nt.D :=
  (labFixed_iff c.a).1 fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩

theorem tame_of_pin {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    {a : NAt hL D cf nch tp} (h : OPin a) (k : Fin 2) (v : a.nt.D.nd.PlG k) :
    @Formalism.L2.NT.TameCoupled _ _ _ _ _ (a.nt.D.nd.plOm.1 (a.nt.D.naut.plGw k v)) _ ⟨a.nt.D.host.g_prime k⟩ (a.nt.A.grp.kv k v)
      (a.nt.D.ntypes.tg k v) (@GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
        (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)) := by
  rw [← h.gen k]
  exact a.nt.A.grp.tg_tame k v


example (hL : GlobalTheory.Published.LocalLanglandsGL) : NCondition := NX hL (OExt hL)
end GlobalTheory.CoefDuty.OPinModel
end
