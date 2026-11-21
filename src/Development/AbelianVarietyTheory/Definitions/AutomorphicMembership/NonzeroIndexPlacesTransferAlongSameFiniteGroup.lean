import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReplacementValuesBaseLevelTypePartsEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.RealGeo GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Tr

variable {B : Base} {C : Cols B} {a b : Late B C} {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : Top.TwDat B}
  {Wt : Set B.places.Pl}

def SameGrp.ofGrpTrue {f : Top.Fr B.toPre} (h : Top.GrpTrue a.N f) (h' : Top.GrpTrue b.N f) : SameGrp a b where
  e := Top.plEquiv a.N.naut b.N.naut
  pl := Top.TypesTrue.plGw_plEquiv h h'
  e0 g := (by with_unfolding_all exact ((h.typeIdempotent_coeff_across_layers h' g) :))

theorem LevOf.transfer (b : Late B C) {U : Set I.ι} {L : Links.LevCh a.D (TupU I U)} (h : LevOf a.st I U L) :
    LevOf b.st I U (levCh b L) :=
  ⟨levIs_tr b h.is, (by with_unfolding_all exact ((congrArg (chFr b) h.C) :)), (by with_unfolding_all exact (h.xiH :)), (by with_unfolding_all exact (h.Pg :)), (by with_unfolding_all exact (h.Q :)), (by with_unfolding_all exact (h.beta :))⟩

theorem GoodSet.transfer (s : SameGrp a b) {eR : Gc B px ≃* G0g a.D.nd} {Xg : Finset (Gc B px → B.LL)}
    (h : GoodSet a.st (px := px) eR Xg) : GoodSet b.st (px := px) (eR.trans s.iso) Xg := by
  have e : ∀ g, b.D.ntypes.e0.coeff ((eR.trans s.iso) g) = a.D.ntypes.e0.coeff (eR g) := fun g => s.e0 (eR g)
  obtain ⟨h1, h2⟩ := (goodSet_iff a.st (px := px) eR Xg).1 h
  refine (goodSet_iff b.st (px := px) _ Xg).2 ⟨fun χ => (h1 χ).trans (and_congr_right fun _ => ?_), fun g => (h2 g).trans (e g).symm⟩
  exact Eq.congr_left (Finset.sum_congr rfl fun g _ => congrArg (· * B.embLL (χ g)) (e g).symm)


def Dat.transfer (s : SameGrp a b) (z : Dat a.st I hX T Wt) : Dat b.st I hX T Wt :=
  @Dat.mk b.st px I hX T Wt
    (Xg := z.Xg)
    (tr := z.tr)
    (core := coreJ b z.core)
    (alg := (by with_unfolding_all exact ((Tr.alg (a := a) b z.alg) :)))
    (alg_eq := (by with_unfolding_all exact (z.alg_eq :)))
    (R := (by with_unfolding_all exact ((real3 (a := a) b z.R) :)))
    (cG := (by with_unfolding_all exact ((z.cG.trans s.iso) :)))
    (geo := (by with_unfolding_all exact ((geoHalf (a := a) b z.geo) :)))
    (pins := (by with_unfolding_all exact ((pins_tr (a := a) b s z.pins) :)))
    (lev := (by with_unfolding_all exact ((z.lev.transfer b) :)))
    (idG := (by with_unfolding_all exact (z.idG :)))
    (good := (by with_unfolding_all exact ((GoodSet.transfer s z.good) :)))
    (mu := (by with_unfolding_all exact (z.mu :)))
    (fieldValues_mem_fixedField := (by with_unfolding_all exact (z.fieldValues_mem_fixedField :)))
    (Ks_le := (by with_unfolding_all exact (z.Ks_le :)))

namespace Dat

variable (s : SameGrp a b) (z : Dat a.st I hX T Wt)































theorem nonzeroIndexPlaces_transferAlongSameFiniteGroup (F0 : HeightOneSpectrum (𝓞 B.LL) → Fin B.R.m → ℝ) : z.W1 F0 = (z.transfer s).W1 F0 :=
  (by with_unfolding_all exact ((congrArg (fun X : type_of% (z.R.toCx3 z.F) => {w : B.places.Pl | ∃ j,
    ∃ w' ∈ ({a.D.plEq w, Formalism.DivisionValues.conjPl (a.D.plEq w)} : Set (HeightOneSpectrum (𝓞 a.D.what₂.LL))),
      IndefData.Iw (Df := (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs) (((X.data z.F.cr false))) j
          (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
        Formalism.DivisionValues.jw (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).HT j
                  (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
          (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).Tl j
            (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ F0 w' j ≠ 0}) (toCx3_eq (a := a) b z.R z.F)) : _))

variable {z}

theorem holds_transfer (h : Holds z.R z.F) : Holds (z.transfer s).R (z.transfer s).F := (by with_unfolding_all exact ((holds_tr (a := a) b h) :))

theorem exAt_transfer (h : z.R.toRealDat.ExAt) : (z.transfer s).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr (a := a) b h) :))

theorem inGeo_transfer (h : InGeo z.geo) : InGeo (z.transfer s).geo := (by with_unfolding_all exact ((inGeo_tr (a := a) b h) :))


end Dat


section Rows

variable {ix : C.Tup ≃ I.ι} {p0 : BaseLevelRowSide a.D}

def RowsAre.tr (c : Refill a) (r : RowsAre a.st I hX T Wt ix p0) : RowsAre c.to.st I hX T Wt ix (baseLevelRowSideTransport c p0) :=
  @RowsAre.mk c.to.st px I hX T Wt ix (baseLevelRowSideTransport c p0)
    (z := r.z.transfer c.same)
    (intersectionNumber_baseChange := Dat.holds_transfer c.same r.intersectionNumber_baseChange)
    (Y := (by with_unfolding_all exact ((read c r.Y) :)))
    (Z := (by with_unfolding_all exact ((readL c r.Z) :)))
    (tup_ix := (by with_unfolding_all exact (r.tup_ix :)))

namespace RowsAre

variable (c : Refill a) (r : RowsAre a.st I hX T Wt ix p0)

end RowsAre

end Rows

example (a : Late B C) (g : G0g a.D.nd) : (SameGrp.ofN a.N a.V a.V a.S a.S a.G a.G).iso g = g := rfl

example (a : Late B C) : (Refill.ofSG a a.S a.G).to = a := rfl

example (s : SameGrp a b) (g : G0g a.D.nd) (k : Fin 2) (v : b.D.nd.PlG k) : s.iso g ⟨k, v⟩ = g ⟨k, (s.e k).symm v⟩ := rfl

example (s : SameGrp a b) (z : Dat a.st I hX T Wt) : ((z.transfer s).transfer s.symm).R.twPl = z.R.twPl :=
  (by with_unfolding_all exact ((Eq.refl z.R.twPl) :))

end GlobalTheory.Mem.R3

end
