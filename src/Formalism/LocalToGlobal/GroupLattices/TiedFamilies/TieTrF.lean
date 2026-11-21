import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev setGat : D7 := { D with gat := g', gat_d := hd' }

open Formalism.L2.Herm

structure FullTiedNoG (D : D7) extends AllTied D where
  levelZeroCompatibility : Lev0Tied D base.toHermCols atT
  ad : AdTied D base.toHermCols atT
  cof : CofTied D base.toHermCols atT
  piG : PiGConst D base.toHermCols atT levelZeroCompatibility
  stabMap : StabMapTied D base.toHermCols atT
  fvI : FvStepTied D base.toHermCols atT
  relDet : RelativeDeterminantCompatible D base
  std : StdTied D
  vpos : PositiveVolumeCompatible D
  baseL : BaseTied D base.toHermCols atT

def FullTiedNoG.toFull {D : D7} (X : FullTiedNoG D) (g : GTied D X.base) : FullTied D := { X with g := g }



def colsSet (H : HermCols D) : HermCols (setGat D g' hd') := { H with }

def hermSet (H : HermTied D) : HermTied (setGat D g' hd') := { H with }


set_option maxHeartbeats 4000000 in

def atTSet {u : D.what₂.Word}
    {e : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}}
    {eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (e v).1.asIdeal)} (A : AtT D u e eF) :
    AtT (setGat D g' hd') u e eF := { A with }

set_option maxHeartbeats 4000000 in
def allSet (H : AllTied D) : AllTied (setGat D g' hd') where
  base := hermSet D g' hd' H.base
  atT := fun u => atTSet D g' hd' (H.atT u)
  vol := H.vol

set_option maxHeartbeats 4000000 in
theorem adSet (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (h : AdTied D H aT) :
    AdTied (setGat D g' hd') (colsSet D g' hd' H) (fun u => atTSet D g' hd' (aT u)) :=
  { h with }

set_option maxHeartbeats 4000000 in

def fullSet (H : FullTiedNoG D) : FullTiedNoG (setGat D g' hd') where
  toAllTied := allSet D g' hd' H.toAllTied
  levelZeroCompatibility := H.levelZeroCompatibility
  ad := adSet D g' hd' _ _ H.ad
  cof := H.cof
  piG := H.piG
  stabMap := H.stabMap
  fvI := H.fvI
  relDet := H.relDet
  std := H.std
  vpos := H.vpos
  baseL := H.baseL


end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

open Formalism.L2.Forms

def atTTSet {u : D.what₂.Word} (A : AtTTied (D := D) u) : AtTTied (D := setGat D g' hd') u := { A with }

set_option maxHeartbeats 4000000 in
def clsSet {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied (D := D) u i hi) :
    ClsTied (D := setGat D g' hd') u i hi := { K with }

set_option maxHeartbeats 4000000 in
def valSet {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied (D := D) u i hi}
    (W : ValTied (D := D) u eV i hi K) : ValTied (D := setGat D g' hd') u eV i hi (clsSet D g' hd' K) := { W with }

set_option maxHeartbeats 4000000 in
def lvSet {u : D.what₂.Word} {A : AtTTied (D := D) u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied (D := D) u A i hi) :
    LvTied (D := setGat D g' hd') u (atTTSet D g' hd' A) i hi := { P with }

set_option maxHeartbeats 4000000 in
def clsPSet {u : D.what₂.Word} (K : ClsPTied (D := D) u) : ClsPTied (D := setGat D g' hd') u := { K with }

set_option maxHeartbeats 4000000 in
def valPSet {u : D.what₂.Word} {K : ClsPTied (D := D) u} (W : ValPTied (D := D) u K) :
    ValPTied (D := setGat D g' hd') u (clsPSet D g' hd' K) := { W with }

set_option maxHeartbeats 4000000 in
def tilSet {u : D.what₂.Word} {A : AtTTied (D := D) u} {K : ClsPTied (D := D) u} {P : LvTied (D := D) u A D.R.m le_rfl}
    (Tl : TilTied (D := D) u A K P) :
    TilTied (D := setGat D g' hd') u (atTTSet D g' hd' A) (clsPSet D g' hd' K) (lvSet D g' hd' P) := { Tl with }

set_option maxHeartbeats 4000000 in
def tilAdSet {u : D.what₂.Word} {A : AtTTied (D := D) u} {K : ClsPTied (D := D) u} {P : LvTied (D := D) u A D.R.m le_rfl}
    {Tl : TilTied (D := D) u A K P} {Km : ClsTied (D := D) u D.R.m le_rfl} (Ta : TilAd (D := D) Tl Km) :
    TilAd (D := setGat D g' hd') (tilSet D g' hd' Tl) (clsSet D g' hd' Km) := { Ta with }

set_option maxHeartbeats 8000000 in

def formsSet {u : D.what₂.Word} (T : FormsTied D u) : FormsTied (setGat D g' hd') u where
  atT := atTTSet D g' hd' T.atT
  cls := fun i hi => clsSet D g' hd' (T.cls i hi)
  val := fun i hi => valSet D g' hd' (T.val i hi)
  gl := T.gl
  gl_K := T.gl_K
  glev := T.glev
  lv := fun i hi => lvSet D g' hd' (T.lv i hi)
  fMe := T.fMe
  fv := T.fv
  upN := T.upN
  dnN := T.dnN
  norm := T.norm
  bw := T.bw
  clsP := clsPSet D g' hd' T.clsP
  valP := valPSet D g' hd' T.valP
  normP := T.normP
  glevP := T.glevP
  til := tilSet D g' hd' T.til
  tilLat := T.tilLat
  tilFv := T.tilFv
  tilAd := tilAdSet D g' hd' T.tilAd
  frExt := T.frExt
  eWz := T.eWz
  evz := T.evz
  jM := T.jM
  per := T.per
  DGam := T.DGam

set_option maxHeartbeats 4000000 in

def forms0Set {u : D.what₂.Word} (T : Forms0 D u) : Forms0 (setGat D g' hd') u where
  atT := atTTSet D g' hd' T.atT
  cls0 := clsSet D g' hd' T.cls0
  val0 := valSet D g' hd' T.val0
  gl := T.gl
  gl_K := T.gl_K
  glev0 := T.glev0
  lv0 := lvSet D g' hd' T.lv0
  fMe0 := T.fMe0
  fv0 := T.fv0
  up_natural_level_zero := T.up_natural_level_zero
  down_natural_level_zero := T.down_natural_level_zero
  norm0 := T.norm0
  bw0 := T.bw0

end Formalism.L2.G
end
end
