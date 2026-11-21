import Mathlib
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.Divisibility.WeightFamilies

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DimensionConstantBounds

open Formalism.BasicNotions Formalism.MainNotions.WeightFamilies NumberField

def Z {D : D7} (L : SizeData₂ D) : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L

def grade {D : D7} (L : SizeData₂ D) (CP : ℝ) (e : ℕ) : ℝ := CP * Z L ^ e

def PP {D : D7} (L : SizeData₂ D) (CP : ℝ) : ℝ := grade L CP 12

def lrd (D : D7) : ℝ := Real.log D.host.rdE

def RR (D : D7) : ℝ := D.host.rdE ^ 7

def q (D : D7) : ℕ := min (D.host.g 0) (D.host.g 1)

def r1 : ℕ := 5

def g0 (D : D7) : ℕ := 2 * r1 ^ 4 * D.R.r

def dimFlag (D : D7) : ℕ := D.R.f * D.R.r.choose 2

def dimX (D : D7) (j : ℕ) : ℕ := D.R.f * (D.R.sigW j).1 * (D.R.sigW j).2

def cOf (D : D7) (P DF : ℝ) : ℝ := RR D * P * DF ^ 2 / (q D : ℝ)

def c {D : D7} (L : SizeData₂ D) (CP DF : ℝ) : ℝ := cOf D (PP L CP) DF

def LamStar (D : D7) : ℝ :=
  Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
    Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * (D.host.q : ℝ) * (D.host.d : ℝ))

def LamPlus (D : D7) (po : ℕ) : ℝ := LamStar D + 2 * Real.log (po : ℝ)

def PN {D : D7} (L : SizeData₂ D) : ℝ := 2 * L.sc.L + LamStar D + 4

def n0 (D : D7) (j : ℕ) : ℕ := D.R.r + 2 * g0 D * (dimX D j + 1)

def dimBoundMax (D : D7) : ℕ := D.R.r + 2 * g0 D * ((Finset.Icc 1 D.R.m).sup (dimX D) + 1)

def PUn (D : D7) (n : ℕ) : ℝ :=
  (D.R.f : ℝ) * (n : ℝ) * (2 * lrd D + 2 * Real.log ((D.R.f : ℝ) * (n : ℝ)) + 3)

def PU (D : D7) : ℝ := PUn D D.R.r

def PO {D : D7} (L : SizeData₂ D) : ℝ :=
  19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L + 198 * (D.R.f : ℝ) ^ 2 * L.sc.L

def sizeConstantAtWeight (D : D7) (nW : ℕ) : ℝ :=
  max (90 * ((D.R.f : ℝ) * (D.R.r : ℝ) + 1))
    (max (360 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3)
      (max (2 * (3 * (D.R.r : ℝ) + 3 + (D.R.r : ℝ) * Real.log (D.R.r : ℝ)))
        (max (nW : ℝ)
          (max (2 * (r1 : ℝ) ^ 4 * (D.R.r : ℝ))
            (max ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + 6) 11)))))

def sizeConstantAtParamsWeight {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : ℝ := sizeConstantAtWeight D T.nWn

def DivisibilityWeightConstant (D : D7) : ℝ :=
  72 * (r1 : ℝ) ^ 4 * (dimFlag D : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 * (D.R.m : ℝ) ^ 4

def fieldSize (K : Type) [Field K] [NumberField K] : ℝ :=
  Real.log (Module.finrank ℚ K : ℝ) +
    Real.log (|((discr K : ℤ) : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ)))

def GOf {D : D7} (L : SizeData₂ D) (PLam : ℝ) (po : ℕ) (o : ℝ) : ℝ :=
  PLam + (3 * L.sc.L + 2 * o) + 2 * (D.R.f : ℝ) * (D.R.r : ℝ) * LamPlus D po + 31 * Z L

def G {D : D7} (L : SizeData₂ D) (X : Prov D) (PLam : ℝ) (po : ℕ) : ℝ :=
  GOf L PLam po (max (fieldSize X.KO) (fieldSize D.host.E))

def DomWith {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (Coo CP : ℝ) : Prop :=
  10 ^ 3 ≤ CP ∧ (Coo * CP) ^ 20 ≤ Z L ∧
  PU D ≤ grade L CP 1 ∧ LamStar D ≤ grade L CP 1 ∧ PN L ≤ grade L CP 1 ∧
  PO L ≤ grade L CP 2 ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (n0 D j : ℝ) ≤ grade L CP 3) ∧
  sizeConstantAtParamsWeight T ≤ grade L CP 4 ∧ DivisibilityWeightConstant D ≤ grade L CP 10

def Dom {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (CP : ℝ) : Prop :=
  DomWith T 1 CP

def RingBound {D : D7} (L : SizeData₂ D) (X : Prov D) : Prop :=
  Real.log (degO X) ≤ PO L ∧ Real.log (rdO X) ≤ PO L

def Sizes {D : D7} (L : SizeData₂ D) (C : ℝ) : Prop :=
  L.sc.x ^ 2 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ∧
  logdE D / (2 * (D.R.f : ℝ)) + |L.logDerivativeAtOne| ≤ 2 * L.sc.L ∧
  L.sc.x ^ (-L.sc.eps) ≤ L.de2 ∧
  (∀ i, Real.log (D.host.g i : ℝ) ≤ 9 * L.sc.L + 1) ∧
  |L.logOm| ≤ C * L.sc.L ∧
  (Real.log (D.host.pde : ℝ) ≤ L.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ L.sc.L) ∧
  (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ D.host.rdE ^ 3

def Hyp {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (X : Prov D) (CP C : ℝ) : Prop :=
  Dom T CP ∧ RingBound L X ∧ Sizes L C

theorem Z_eq {D : D7} (L : SizeData₂ D) : Z L = zBase L := rfl

theorem PP_eq_PPv {D : D7} (L : SizeData₂ D) (CP : ℝ) : PP L CP = PPv D L CP 12 := by
  unfold PP grade PPv
  rw [Z_eq, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]


theorem RR_eq (D : D7) : RR D = RRv D 7 := by
  unfold RR RRv
  rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem f_pos (D : D7) : 0 < D.R.f := by
  unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega

theorem lrd_eq (D : D7) : lrd D = logdE D / (2 * (D.R.f : ℝ)) := by
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast f_pos D
  rw [logdE_eq_rd]; unfold lrd; field_simp

theorem half_f (D : D7) : (D.R.f : ℝ) / 2 = D.R.n := by
  unfold Ranks.f; push_cast; ring



end GlobalTheory.IndefiniteRowSideFullHecke.DimensionConstantBounds

end
