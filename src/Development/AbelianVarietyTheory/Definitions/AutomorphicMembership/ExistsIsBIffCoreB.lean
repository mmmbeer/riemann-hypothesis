import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersAdmissible

noncomputable section

namespace GlobalTheory.Mem.Db

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.Mem.Df NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure NStd {B : Base} {C : Cols B} {W : RowsRest B C} (N : NStage B C W) : Prop where
  loc : IsEmpty N.nd.Loc
  cover : N.ntw.TwCover
  chiT : ∀ (k : Fin 2) (v : N.nd.PlG k), ∃ w : (ZMod (B.host.g k))ˣ, orderOf w = B.host.g k - 1 ∧
    ∀ j : Fin B.R.m, N.nd.chiT k v j = w ^ (2 * (j.1 + 1))

structure SStd (K : Ctx) {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) (cd : CDHaar) : Prop where
  del : S.s.Del = (Delv K.s K.cD : ℚ)
  scale : S.s.cdScale = Vol.trueScale cd
  dsig : ∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def GCols (K : Ctx) (w : ColW B f T) (G : GJStage B w.C) : Prop :=
  ∀ W V S N, GatNum K.s (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩)

structure ZDef (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 where
  hX : B.fields.Ok
  e : ∀ a : w.C.Tup, MtCx w.I a ≃ₗ[ℂ] Z.W.Amb a
  tru : DefTrue w.I w.l hX Z.W e
  std : StandIn Z.W
  etaF : Z.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  s : SStd K Z.S Z.G.cd
  n : NStd Z.N
  g : GCols K w Z.G

structure Side (w : ColW B f T) (Z : w.Lt) : Type 1 where
  th : ThetaX (w.D Z)
  th_io : th.TieIo
  nch : NChoice (w.D Z)
  n : NchT w Z ∅ nch
  xd : ThData (w.D Z)
  X : DivX (w.D Z)
  qp : TC.QpIs w.I X.Qp
  p0 : BaseLevelRowSide (w.D Z)
  amb0 : AmbForm (w.D Z) p0.s
  row : V4.RowLay (w.D Z) p0 X
  gauge : GlobalTheoryTheory.GenusMassVolumes.GaugeFam (w.D Z).host.F (w.D Z).host.E (w.D Z).sp.cm.sig
  gauge_def : gauge.IsGauge

structure CoreB (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 where
  isOver : K.Over B.toPre
  untw : T = TwDat.untw B T.pl
  forced : Forced K B T
  pin : ColPin w
  z : ZDef K w Z
  mu : V4.MuIsW (w.st Z) f T ∅ w.I.xi
  sd : Side w Z
  t : ColumnDataSplitPrimes K w Z
  Gy : G.LatInst (w.D Z)
  ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy
  gy : GyLay K (w.D Z) t.Gt t.cmp Gy
  kt : KerT t.toColT sd.X Gy ker
  entC : ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs sd.X (w.tw Z)),
    kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h
  col : ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1)
  amb : AmbForm (w.D Z) (RowSide.sharp (w.D Z))
  ambTrue : AmbTrue w.I w.l z.hX Z z.e amb
  mtStable : DQ.MtStableAt (w.D Z)
  cd : cdScaleTie (w.D Z)
  dsT : dsigTie (w.D Z)
  ds : ∀ τ, Formalism.L2.Theta.IsDsig (w.D Z) τ ((w.D Z).dsig τ)

def CoreB.obj {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : Obj2 (w.D Z) where
  gatT := b.t.Gt
  th := b.sd.th
  cmp := b.t.cmp
  tw := w.tw Z
  Gy := b.Gy
  errX := Formalism.L2.Herm.toErrXS b.t.full.1
  nch := b.sd.nch
  xd := b.sd.xd
  lev := b.t.full.1.base.lev0
  X := b.sd.X
  p0 := b.sd.p0
  ker := b.ker
  amb := b.amb
  amb0 := b.sd.amb0
  gauge := b.sd.gauge

def setDivZ {C : Cols B} (Z : TC.Later B C) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) : TC.Later B C :=
  { Z with V := { Z.V with div := (setDiv (assemble B C Z.W Z.V Z.S Z.N Z.G) N h).div } }

theorem D_setDivZ (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    w.D (setDivZ Z N h) = setDiv (w.D Z) N h := rfl

def IsB (K : Ctx) (D : D7) (O : Obj2 D) : Prop :=
  ∃ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z),
    (⟨D, O⟩ : Σ D : D7, Obj2 D) = ⟨w.D Z, b.obj⟩

def PinU : WP := fun K B f T w => Pinned K B f T w ∧ T = TwDat.untw B T.pl

def ForVol (w : ColW B f T) (P : w.Lt → Prop) : Prop :=
  ∀ (vol : HSpace B.host.E → ℝ) (cd : CDHaar), (∀ W, 0 < vol W) →
    (∀ Z : w.Lt, Z.G.vol = vol → Z.G.cd = cd → Formalism.L2.Herm.VolumeCompatible (w.D Z)) → ∃ Z : w.Lt, Z.G.vol = vol ∧ Z.G.cd = cd ∧ P Z

def HasB : WP := fun K _ _ _ w => ForVol w fun Z => Nonempty (CoreB K w Z)

theorem CoreB.isB {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : IsB K (w.D Z) b.obj := ⟨B, f, T, w, Z, b, rfl⟩

theorem IsB.ind {K : Ctx} {R : ∀ D : D7, Obj2 D → Prop}
    (h : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z), R (w.D Z) b.obj)
    {D : D7} {O : Obj2 D} (hD : IsB K D O) : R D O := by
  obtain ⟨B, f, T, w, Z, b, e⟩ := hD
  cases e
  exact h B f T w Z b





theorem CoreB.muAt_eq {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) (v : (w.D Z).what₂.places.Pl) :
    (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 := b.mu.off v (Set.notMem_empty v)

theorem CoreB.over {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : Over (w.D Z) K.P K.Lv := by
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := b.isOver
  exact ⟨sp, hT, hY, hA, hV, hz, w.st Z, h, rfl⟩


theorem ForVol.mono {w : ColW B f T} {P Q : w.Lt → Prop} (h : ForVol w P) (hPQ : ∀ Z, P Z → Q Z) : ForVol w Q :=
  fun vol cd hp ht => let ⟨Z, a, b, p⟩ := h vol cd hp ht; ⟨Z, a, b, hPQ Z p⟩


section Layers

variable {K : Ctx} {w : ColW B f T} {Z : w.Lt}

def CoreB.lay (b : CoreB K w Z) (hv : StandardLattice.VolumeEqMass₂ (w.D Z)) : Lay (w.D Z) :=
  { b.obj with
    ties := ⟨b.cd, b.dsT, b.sd.row.bu_def, twCoverPair_of_tie _ _ b.sd.n.tie, B.coeffGaloisSubfield_isGalois, b.sd.row.ft_occ⟩
    rrDef := b.sd.row.rrDef
    th_io := b.sd.th_io
    vram := b.gy.vram
    fills_all := b.gy.fills
    idx := b.sd.row.idx
    kap_def := b.sd.row.kap_def
    lam_def := b.sd.row.lam_def
    kapR_def := b.sd.row.kapR_def
    piG_lev := b.col.piG_lev
    piT_lev := b.col.piT_lev
    seen := b.col.seen
    tauOf := b.col.tauOf
    dgam := fun u μ => ⟨fun u' μ' i hi x => by
      rw [b.col.one u μ, ← b.col.one u' μ']
      exact ((w.D Z).chTw u' μ').dvd_DGam i hi x, b.col.one u μ⟩
    nch_tie := b.sd.n.tie
    rationalRoots_def := b.sd.row.rationalRoots_def
    duStar_def := (sizes_eq_count K (w.st Z) b.isOver hv b.z.s.dsig).1
    Dstar_def := (sizes_eq_count K (w.st Z) b.isOver hv b.z.s.dsig).2
    gauge_def := b.sd.gauge_def }

end Layers

example {K : Ctx} {D : D7} {O : Obj2 D} (h : IsB K D O) (v : D.what₂.places.Pl) : D.what₂.muAt v = D.what₂.mu0 :=
  IsB.ind (R := fun D _ => ∀ v, D.what₂.muAt v = D.what₂.mu0) (fun _ _ _ _ _ b => b.muAt_eq) h v

example {C : Cols B} (Z : TC.Later B C) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    (setDivZ Z N h).G = Z.G ∧ (setDivZ Z N h).V.div.h = h := ⟨rfl, rfl⟩

example (w : ColW B f T) (vol : HSpace B.host.E → ℝ) (cd : CDHaar) (hp : ∀ W, 0 < vol W)
    (ht : ∀ Z : w.Lt, Z.G.vol = vol → Z.G.cd = cd → Formalism.L2.Herm.VolumeCompatible (w.D Z)) : ¬ ForVol w fun _ => False :=
  fun h => let ⟨_, _, _, p⟩ := h vol cd hp ht; p

end GlobalTheory.Mem.Db

end
