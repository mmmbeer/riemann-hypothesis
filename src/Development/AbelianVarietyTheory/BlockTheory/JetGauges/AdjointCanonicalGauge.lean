import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointCanonicalGauge

def SplitsCompletely (E : Type) [Field E] [NumberField E] (O : Type) [CommRing O] (g : ℕ) : Prop :=
  ((Ideal.span {(g : ℤ)}).primesOver O).ncard = Module.finrank ℚ E

section Defs

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra R k]

def IntBelow {n : ℕ} (g : ℕ) (f : PS k n d) : Prop :=
  ∀ m : Fin n × Fin d →₀ ℕ, ∑ p, m p < g → coeff m f ∈ (algebraMap R k).range

variable [Algebra ℚ k] {O : Type} [CommRing O] [StarRing O]

def IsBiaddGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0 ∧
    FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) ∧
    FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)

def colSum (B : FB R d O) (w0 : O) (n : ℕ) (h : PS k 2 d) : PS k n d :=
  ∑ i : Fin n, ev (n := n) ![pt k d i, comp1 (B.actK k w0) (pt k d i)] h

end Defs

example : CompleteSpace ℂ_[3] ∧ IsAlgClosed ℂ_[3] ∧ CharZero ℂ_[3] ∧ IsUltrametricDist ℂ_[3] :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointCanonicalGauge
