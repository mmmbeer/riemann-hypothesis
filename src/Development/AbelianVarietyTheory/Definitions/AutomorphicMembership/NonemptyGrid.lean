import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

def GridPin (D : D7) {I : Type} (Lc : Formalism.IndefR.Links.LevCh D I) (CF b : ℝ) : Prop :=
  ∃ G : GlobalTheory.ChiGrid.GridData Lc ⟨1, CF, b⟩,
    GlobalTheory.BigTop.Fun.FieldHas G (embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G)

def GridSt {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) : Prop :=
  GridPin (Dof x) x.m.z.R.toRealDat.toLevCh K.C.P.CF K.s.b

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

def SettingsFormsExistGrid : Prop := AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (SettingsLevel hL x') ∧ GridSt x'

def SeriesExistGrid : Prop := AllSt fun _ _ _ _ _ P x => SettingsLevel hL x → ∃ x' : St P, Nonempty (SeriesLevel hL x') ∧ (GridSt x → GridSt x')

def ModuliPointsExistGrid : Prop := AllSt fun _ _ _ _ _ P x => SeriesLevel hL x → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x') ∧ (GridSt x → GridSt x')

end GlobalTheory.HeightCounting.Up

end
end

section
noncomputable section

namespace GlobalTheory.HeightCounting.Up.GridModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.Links NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar





section Guard

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}



end Guard


variable (hL : GlobalTheory.Published.LocalLanglandsGL)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem settingsFormsExist_of_grid : SettingsFormsExistGrid hL → SettingsFormsExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem seriesExist_of_grid : SeriesExistGrid hL → SeriesExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem moduliPointsExist_of_grid : ModuliPointsExistGrid hL → SB2 hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

end GlobalTheory.HeightCounting.Up.GridModel

end
end

section
noncomputable section

namespace GlobalTheory.HeightCounting.Up.ListModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.Links NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000






section Guard

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}



end Guard

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem settingsFormsExist_of_grid : SettingsFormsExistList hL cDep → SettingsFormsExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem seriesExist_of_grid : SeriesExistList hL cDep → SeriesExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem moduliPointsExist_of_grid : ModuliPointsExistList hL cDep → SB2 hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.R3.Rw in

theorem chain (h0 : SettingsFormsExistList hL cDep) (h1 : SeriesExistList hL cDep) (h2 : ModuliPointsExistList hL cDep) (h3 : SC hL) :
    AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (LC hL x') ∧ ListSt cDep x' :=
  Step.trans (Step.and h0 (Step.and h1 (Step.and h2 h3))) (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => by
    obtain ⟨x0, ⟨l0⟩, p0⟩ := H.1 w a P x l
    obtain ⟨x1, ⟨l1⟩, p1⟩ := H.2.1 w a P x0 l0
    obtain ⟨x2, ⟨l2⟩, p2⟩ := H.2.2.1 w a P x1 l1
    obtain ⟨c⟩ := H.2.2.2 w a P x2 l2
    exact ⟨x2, ⟨⟨l2, c⟩⟩, p2 (p1 p0)⟩)

open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw in

theorem lev_at_state {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    x.m.z.R.toRealDat.toLevCh.C = cfOf x ∧ ∃ μ0, x.m.z.R.toRealDat.toLevCh.Is μ0 :=
  ⟨x.m.z.lev.C, _, x.m.z.lev.is⟩

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 in

theorem nonempty_grid {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (sc : Consts) (h3 : ∀ k, q0 (w.st Z).toD7 ≠ B.host.g k) :
    Nonempty (GridData z.R.toRealDat.toLevCh sc) := by
  refine GlobalTheory.ChiGridModel.nonempty_gridData _ _ z.lev.is sc B.g_cond B.pde_cond.1 B.pde_cond.2 h3 fun t PP hP hq => ?_
  have hprime := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (w.st Z).toD7).1
  have two : ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 B.host.E) ∈ PP.asIdeal → q0 (w.st Z).toD7 = p := fun p hp hm => by
    by_contra hne
    have hc : IsCoprime ((q0 (w.st Z).toD7 : ℕ) : 𝓞 B.host.E) ((p : ℕ) : 𝓞 B.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hprime hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hm)))
  have hd : f.del.UnrAt PP := f.isDel.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).1 (two _ B.host.pde_prime h)
  have hd' : f.del'.UnrAt PP := f.isDel'.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).2 (two _ B.host.pde'_prime h)
  have hps : ∀ v, (T.psi v).UnrAt PP := fun v => by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP hn
    have hmem := Ideal.absNorm_mem PP.asIdeal
    have e := two _ h1 hmem
    exact h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e.symm))))))
  refine (z.lev.is.Q_ram t PP).2 (Or.inl hP) ?_
  rw [z.lev.xiH t]
  have hm : w.I.xi (GlobalTheory.Mem.R3.ixOf w.I _ t) ∈ T.set f := w.xi_range ▸ ⟨_, rfl⟩
  rcases hm with (h | h | h) | ⟨v, h⟩
  · rw [h]; intro x _; rfl
  · exact h ▸ hd
  · exact (h : _ = _) ▸ hd'
  · rw [← h]
    unfold TwDat.xiTw
    split_ifs
    · exact HChar.UnrAt.mul hd' (hps v)
    · exact HChar.UnrAt.mul hd (hps v)

end GlobalTheory.HeightCounting.Up.ListModel

end
end
