import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.Col
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def homIE {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (x : HomE D.host.E a b) : HomE X.E a b :=
  Matrix.toLin' ((LinearMap.toMatrix' x).map s.iE.symm)

def homRe {E : Type} [Field E] {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (x : HomE E a b) : HomE E a' b' :=
  (LinearEquiv.funCongrLeft E E (finCongr hb.symm)).toLinearMap ∘ₗ x ∘ₗ
    (LinearEquiv.funCongrLeft E E (finCongr ha.symm)).symm.toLinearMap

def rdH {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {X : Fields} (s : Seam D X) (rd : KerRead (D.chTw u μ) X)
    {p : ℕ} [Fact p.Prime] {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ)
    (La : Lv.comp j × (Fl.Pj j).Tup) (La' : Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup)
    (x : HomE D.host.E (D.R.N j) (D.R.N (j + 1))) : ℂ :=
  rd.Xi j (cls j La.1 La.2) (cls (j + 1) La'.1 La'.2) (homIE s x)

def RdAway {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {X : Fields} (p : ℕ) (rd : KerRead (D.chTw u μ) X) : Prop :=
  ∃ S₀ : Finset ℕ, p ∉ S₀ ∧ ∀ i c c' x, IntOff S₀ (rd.Xi i c c' x)

theorem intOff_zero (S : Finset ℕ) : IntOff S 0 := by
  refine ⟨zero_mem _, fun p _ lam _ => ?_⟩
  unfold TaylorLogMetric.lamC
  split_ifs with h
  · have e : (⟨0, h⟩ : TaylorLogMetric.Qbar) = 0 := rfl
    rw [e, map_zero, norm_zero]
    exact zero_le_one
  · rw [norm_zero]
    exact zero_le_one

section AtS

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  {X : Fields} (s : Seam D X) (rd : KerRead (D.chTw u μ) X)
  (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j)

open Classical in

def xiAt0 : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
    HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ :=
  fun j La La' z =>
    if hr : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1 = D.R.N j ∧ ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1 = D.R.N (j + 1) then
      rdH s rd cls j La La' (homRe hr.1 hr.2 (inFr ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG j La).symm ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG (j + 1) La').symm z))
    else 0


include I L0 in

theorem rankAt : ∀ j, j ≤ D.R.m → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1 = D.R.N j
  | 0, _, _ => by exact L0.A.rk
  | i + 1, hi, La => by exact ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk




end AtS

section Rec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} (I : CmpJIn ex.tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  (t : KerEntTied ex) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)

def xiAtRec : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
    HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ :=
  xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t.seam (t.rd u μ) KA.cls



end Rec

end Formalism.L2.PairingIndexBounds.F
