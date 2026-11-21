import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.GroupLattices.ClassLocalOfEq
import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
import Formalism.LocalToGlobal.InertKernelTheory.DefsStabEq

section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.KernelStabilizer

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.KerInert.SecondKernelInstances

def StabEqRest {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} {Ch : Chain Lv}
    (KA : TwTie.KerAtMu D c Tw u μ w h Ch) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    Nat.card ((D.chTw u μ).stab j (KA.cls j a L)) = Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L}

set_option linter.unusedVariables false in

def TieStab0Inst : Prop :=
  ∀ (D : D7) (ex : TwForms D) (cc : LatCmp D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D cc ex u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j),
    DV.Used D μ → OrbitPlaces.Stab0 D → TieStabAt (Y := Y) u μ cls 0

set_option linter.unusedVariables false in

def StabilizerEqualityAtZero : Prop :=
  ∀ (D : D7) (Gt : GatTies D) (cc : LatCmp D) (Gd : Formalism.L2.G.GroupCompatibilityAll D Gt cc)
    (inQ : D.what₂.Tup → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F) → Prop)
    (T : Formalism.L2.Herm.TwChTied D inQ) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j),
    TieStabAt (Y := Y) u μ cls 0

def TieStabRestIff : Prop :=
  ∀ (D : D7) (ex : TwForms D) (cc : LatCmp D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D cc ex u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    StabEqRest KA ↔ ∀ j, 1 ≤ j → j ≤ D.R.m → TieStabAt (Y := Y) u μ KA.cls j

def TieStabAllInst : Prop :=
  ∀ (D : D7) (ex : TwForms D) (cc : LatCmp D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D cc ex u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    DV.Used D μ → OrbitPlaces.Stab0 D → StabEqRest KA → ∀ j, j ≤ D.R.m → TieStabAt (Y := Y) u μ KA.cls j

theorem stabilizer_base_instance : TieStab0Inst := by
  intro D ex cc u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y cls hU hS La hLa
  rw [hS.2 u μ hU _]
  exact (KA.stab_zero La.1 La.2 (Y.Rep_lat 0 La hLa)).symm


theorem stabilizer_restrict_iff : TieStabRestIff := by
  intro D ex cc u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y
  constructor
  · intro hR j h1 hj La hLa
    exact hR j h1 hj La.1 La.2 (Y.Rep_lat j La hLa)
  · intro hT j h1 hj a L hL
    have hjm : j ≤ Fl.mm := KA.fl_m ▸ hj
    obtain ⟨L0, ⟨hmem, γ, hγ⟩, -⟩ := Y.Rep_ex j hjm a L hL
    have hL0 : (Fl.Pj j).IsLatTup L0 := Y.Rep_lat j (a, L0) hmem
    have hc : KA.cls j a L0 = KA.cls j a L :=
      (KA.cls_iff j hj a a L0 L hL0 hL).2 ⟨rfl, γ, hγ⟩
    have h0 := hT j h1 hj (a, L0) hmem
    rw [← hc, h0, hγ, Formalism.L2.G.Pend.card_stab_smul (Lv.lev j a) γ L0]
    rfl

theorem stabilizer_all_instances : TieStabAllInst := by
  intro D ex cc u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y hU hS hR j hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    exact stabilizer_base_instance D ex cc u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y KA.cls hU hS
  · exact (stabilizer_restrict_iff D ex cc u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y).1 hR j hpos hj


end Formalism.L2.KerInert.KernelStabilizer
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.KernelStabilizer

namespace Formalism.L2.KerInert.SecondKernelStabilizers

def StabEqAny : Prop :=
  ∀ (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (I : CmpJ.CmpJIn Tw u μ w h Lv) (H : CmpJ.CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv) (hCh : _),
    StabEqRest (CmpJ.kerAtMu_any K H hS Gt Ch hCh)

def TieStabAny : Prop :=
  ∀ (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (I : CmpJ.CmpJIn Tw u μ w h Lv) (H : CmpJ.CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv) (hCh : _)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    DV.Used D μ → OrbitPlaces.Stab0 D → ∀ j, j ≤ D.R.m → TieStabAt (Y := Y) u μ (CmpJ.kerAtMu_any K H hS Gt Ch hCh).cls j

theorem stabilizer_any_level : TieStabAny := by
  intro D c Tw u μ w h _ Fl Lv K I H hS Gt Ch hCh std vp unif eO eO_spec dG dG_spec om Y hU hS0 j hj
  exact stabilizer_all_instances D Tw c u μ w h Fl Lv Ch (CmpJ.kerAtMu_any K H hS Gt Ch hCh) std vp unif eO eO_spec dG dG_spec om Y
    hU hS0 K.stab_eq j hj

end Formalism.L2.KerInert.SecondKernelStabilizers
end
end
