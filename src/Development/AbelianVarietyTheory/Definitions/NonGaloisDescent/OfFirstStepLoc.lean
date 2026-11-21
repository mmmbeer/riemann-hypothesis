import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwInputs

def RealSide.ofPins {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (p : GlobalTheory.Mem.R3.Pins R F cG)
    (h : GlobalTheory.Mem.R3.Holds R F) (g : GlobalTheory.RealGeo.InGeo geo) (f : Finite T) (hh : HostHyp D) (s : ∀ j, FWT.VStd D j)
    (z : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) : RealSide D :=
  { Γ := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, core := C, R := R, F := F, cG := cG, geo := geo,
    char := RealDat3.characterisation_of_weak p.char h.aux.ex, phs := p.phs, guard := p.keep.guard, valKs := p.keep.valKs,
    idem := by obtain ⟨_, _, _, h2, _⟩ := p.keep.grp; exact h2
    unif := h.prim.unif, integral := h.aux.integral, inGeo := g, finT := f, host := hh, std := s, size := z }

section Second

variable {D : D7} (X : RealSide D) (S : RatDat D.ntw) {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ} {Pq} {hL} {eig} {θ}
  (Bs : SideB D cf Rw low Pq S hL eig θ) (fi : ∀ i : Fin D.R.m, FormsIso (S.A ((i : ℕ) + 1)) (X.R.FW i))
  (geq : ∀ (i : Fin D.R.m) (g : S.G), X.cG (X.R.eG ((fi i).eG g)) = S.eG g)

def formsOf : NExpRealS X.R X.cG S :=
  ⟨fi, geq, Bs.rho, Bs.chiL, Bs.eF, fun i j b h1 h2 => ⟨1, one_ne_zero,
    fun x hx => by rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).1 hx,
    fun x hx => by rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).2 hx⟩, Bs.act⟩

def heckeOf : NExpRealH X.R X.cG S (formsOf X S Bs fi geq) :=
  { hL := hL, hs := Bs.hs, cHk := fun i b k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P) ^ k
    cHk_zero := fun _ _ _ => pow_zero _, cHk_unit := fun i b P => ((Bs.cHk i b P).isUnit.map _).pow _
    cHk_pow := fun _ _ _ _ => by rw [pow_one], hkEq := Bs.hkEq }

example : (heckeOf X S Bs fi geq).hL = hL := rfl

example (i : D.ntw.Tw) (b : Bool) (P : PlE D.host) : (heckeOf X S Bs fi geq).cHk i b 0 P = 1 := pow_zero _

end Second

end GlobalTheory.TwInputs

end
