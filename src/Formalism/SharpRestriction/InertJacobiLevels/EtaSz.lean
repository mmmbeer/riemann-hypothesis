import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.TiesView
import Formalism.SharpRestriction.InertJacobiLevels.LambdaRealEqShiftedWeight

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

theorem FC.Large.mono {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large K' CH) (hK : K.le K') : C.Large K CH :=
  ⟨fun c hc => hK.1.trans (h.1 c hc), trivial, fun c hc => (hK.2.2.1 _).trans (h.2.2.1 c hc),
    fun c hc => (hK.2.2.2 _).trans (h.2.2.2 c hc)⟩

def fcOf (p t : ℝ) (o : Out) (M N : ℝ) : FC where
  Ct := t
  Cc := o.Cc
  CT2 := o.CT2
  CGam := M
  Csz := M
  Cr := 1
  CTu := o.CTu
  Cdg := o.Cdg
  C5 := o.C5
  full := o.full
  GK := ⟨M, N, N, N, N, N, N, N, N, N, N, 5, 4, 1, N⟩
  cX := ⟨1, ⟨12, 3, M⟩⟩
  P := ⟨N, N, N, N⁻¹, 10, N, N, o.CLw, o.Cj0, N, o.cw, N, N, N, N, N, N, o.CetaF, N, o.CYL, o.Cpde, o.CccK, M⟩
  T := ⟨p, o.eP, o.Cp, N, o.cTO, N, N⟩

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

abbrev KapI : Type := ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ


structure LatIn (D : D7) where
  Vram : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn
  len : D.what₂.Word → D.what₂.places.Pl → ℚ

def LatIn.zero (D : D7) : LatIn D := ⟨fun _ _ _ => ⊥, fun _ _ => 0⟩

structure TieHyp {D : D7} (gatT : GatTies D) (L0 : SizeData₂ D) (kapI : KapI) (ep : ℕ → ℕ) where

  hw : 1 ≤ L0.sc.w'' D.R.n

  hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i))

  hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0

  htw : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L0.sc.X'' D.R.n ∨
    D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨ w ∈ L0.supp

  pos : PosHyp gatT (instW L0 kapI ep)

  c : ℕ
  c_le : (c : ℝ) ≤ G.cG L0
  hcl : L0.Sc + ((D.R.k : ℝ) - 1) / 2 ≤ c

  hoff : ∀ u τ, (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → ∀ i : Fin D.R.k,
    |(((D.hcW u τ).u i : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c

  hw1 : ∀ τ, (c : ℝ) ≤ wj D 1 τ - G.kaJ D 1

namespace TieHyp

variable {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ} (H : TieHyp gatT L0 kapI ep)
  (K : G.Consts) (Cr : ℝ) (Λ : LatIn D)

def L : SizeData₂ D := tieL L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu

def Gx : G.Inst D (H.L K Cr Λ) := tieX L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu

def posL : PosHyp gatT (H.Gx K Cr Λ) where
  vOf := H.pos.vOf
  inj := H.pos.inj
  n_eq := H.pos.n_eq
  pos := H.pos.pos
  r_eq := H.pos.r_eq

def latHyp : LatHyp gatT (H.Gx K Cr Λ) := latHypOf gatT (H.Gx K Cr Λ) (H.posL K Cr Λ) H.c H.c_le H.hcl H.hoff H.hw1

def Gy : G.LatInst D := { (H.latHyp K Cr Λ).latInst with Vram := Λ.Vram }

theorem supp_sat (w : D.what₂.places.Pl) (h : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ (H.L K Cr Λ).sc.X'' D.R.n) :
    w ∈ (H.L K Cr Λ).supp :=
  tieL_supp_sat L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu w h

theorem tw_supp (w : D.what₂.places.Pl) (h : D.what₂.muAt w ≠ D.what₂.mu0) : w ∈ (H.L K Cr Λ).supp :=
  (mem_tieSupp L0 w).2 (H.htw w h)

theorem fills (w : D.what₂.places.Pl) : G.ParametersFill (H.Gx K Cr Λ) K w :=
  tieL_fills L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu (instW_fill L0 kapI ep) w



theorem latTied : G.LatTied gatT (H.Gx K Cr Λ) (H.Gy K Cr Λ) := (H.latHyp K Cr Λ).latTied (instW_fill L0 kapI ep)

theorem drop_iff (p : ℕ) :
    p ∈ (H.L K Cr Λ).drop ↔ NoGain (H.Gx K Cr Λ) K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T :=
  tieL_drop_iff L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu p



end TieHyp


open Classical in

def offShd (R : Ranks) (TTn : Finset ℕ) (sc : Scale) (offS : ℕ → ℕ → ℝ) (j t : ℕ) : ℝ :=
  if j ∈ Finset.Icc 1 R.m then offS j (t % R.n)
  else if t % R.n ∈ TTn then sc.b' / sc.x else sc.w'' R.n





end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def TieHyp.tiesAtY {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ}
    (H : TieHyp gatT L0 kapI ep) (C : FC) (Λ : LatIn D) (Gy : G.LatInst D)
    (hGy : G.LatTied gatT (H.Gx C.GK C.Cr Λ) Gy)
    (hl : ∀ w, G.LatticeLengthsAtPlace (H.Gx C.GK C.Cr Λ) Gy C.GK w) : TiesAt C (H.L C.GK C.Cr Λ) gatT where
  Gx := H.Gx C.GK C.Cr Λ
  Gy := Gy
  supp_sat := H.supp_sat C.GK C.Cr Λ
  tw_supp := H.tw_supp C.GK C.Cr Λ
  fills := H.fills C.GK C.Cr Λ
  lats0 := fun w u h1 h2 => (hl w).2 u h1 h2
  latTied := hGy
  drop_iff := fun p _ => H.drop_iff C.GK C.Cr Λ p

def TieHyp.tiesAt {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ}
    (H : TieHyp gatT L0 kapI ep) (C : FC) (Λ : LatIn D)
    (hl : ∀ w, G.LatticeLengthsAtPlace (H.Gx C.GK C.Cr Λ) (H.Gy C.GK C.Cr Λ) C.GK w) : TiesAt C (H.L C.GK C.Cr Λ) gatT where
  Gx := H.Gx C.GK C.Cr Λ
  Gy := H.Gy C.GK C.Cr Λ
  supp_sat := H.supp_sat C.GK C.Cr Λ
  tw_supp := H.tw_supp C.GK C.Cr Λ
  fills := H.fills C.GK C.Cr Λ
  lats0 := fun w u h1 h2 => (hl w).2 u h1 h2
  latTied := H.latTied C.GK C.Cr Λ
  drop_iff := fun p _ => H.drop_iff C.GK C.Cr Λ p

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure Shd0 where
  R : Ranks
  TTn : Finset ℕ
  T2 : Finset ℕ
  q : ℕ
  d : ℕ
  g : Fin 2 → ℕ
  pde : ℕ
  pde' : ℕ
  bits : ℕ → Bool
  etaSz : ℝ
  Sc : ℝ
  hP : ℕ → ℕ
  offS : ℕ → ℕ → ℝ
  kapI : KapI
  ep : ℕ → ℕ

def Shd0.shd (S : Shd0) (sc : Scale) (C : FC) : Shd where
  R := S.R
  TTn := S.TTn
  T2 := S.T2
  q := S.q
  d := S.d
  g := S.g
  pde := S.pde
  pde' := S.pde'
  bits := S.bits
  LaG := G.La C.GK sc
  etaSz := S.etaSz
  Sc := S.Sc
  hP := S.hP
  bs := fun h t => bsVal (2 ^ S.R.e) (h % 2 ^ S.R.e) (t % 2 ^ S.R.e)
  off := offShd S.R S.TTn sc S.offS
  kapI := S.kapI
  ep := S.ep

end Formalism.MainNotions.Inhab

end
end
