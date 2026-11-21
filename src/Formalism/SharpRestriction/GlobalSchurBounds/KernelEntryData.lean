import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

namespace Formalism.MainNotions.KernelEntryData

open Formalism.BasicNotions Formalism.MainNotions.G Finset

section Numbers

variable {n' : ℕ}

def lg (p : ℕ) (x : ℤ) : ℕ := FormalGroupSystem.lgp p x

def rho (p : ℕ) : ℝ := 1 / ((p : ℝ) ^ 2 - 1)

def gam (p : ℕ) : ℝ := (p : ℝ) * rho p

structure IsPart (r0 : ℕ) (nu : Fin n' → ℕ → ℤ) : Prop where
  nonneg : ∀ s i, 0 ≤ nu s i
  anti : ∀ s i, 1 ≤ i → nu s (i + 1) ≤ nu s i
  what₂ : ∀ s i, r0 < i → nu s i = 0

def al (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ :=
  if s ∈ TT then nu s 1 - nu s 2 else 0

def cap (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ :=
  if s ∈ TT then nu s 2 else nu s 1

def sz (rb : ℕ) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ := ∑ i ∈ Icc 1 rb, nu s i

def low (rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ := sz rb nu s - al TT nu s

def OtherPar (s s' : Fin n') : Prop := s'.val % 2 ≠ s.val % 2

instance (s s' : Fin n') : Decidable (OtherPar s s') := inferInstanceAs (Decidable (_ ≠ _))

def dLev (s s' : Fin n') : ℕ := (s'.val + n' - s.val) % n'

def DSet (TT : Finset (Fin n')) (s : Fin n') : Finset ℕ := (TT.filter fun s' => OtherPar s s').image (dLev s)

def gain (p : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') (e : ℕ) : ℝ :=
  max ((al TT nu s : ℝ) / (p : ℝ) ^ e - (cap TT nu (posAdd s e) : ℝ)) 0

def de (p r0 r1 rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) : ℝ :=
  ∑ s : Fin n', ((r1 : ℝ) * lg p (al TT nu s) + (r0 : ℝ) * (r1 : ℝ) * lg p (low rb TT nu s)) +
    ∑ s ∈ TT, ((lg p (al TT nu s) : ℝ)) ^ 2

def gsum (p : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) : ℝ :=
  ∑ s ∈ TT, ∑' e : ℕ, if 2 * e + 1 ∈ DSet TT s then 0 else gain p TT nu s (2 * e + 1)

def g0 (p r0 r1 rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) : ℝ :=
  gsum p TT nu - de p r0 r1 rb TT nu

def fact_gam : Prop :=
  ∀ p : ℕ, 2 ≤ p → gam p = (p : ℝ) / ((p : ℝ) ^ 2 - 1) ∧
    HasSum (fun e : ℕ => ((p : ℝ) ^ (2 * e + 1))⁻¹) (gam p) ∧ gam p = 1 / ((p : ℝ) - 1) - rho p

def fact_dinj : Prop := ∀ (n' : ℕ) (s s' s'' : Fin n'), dLev s s' = dLev s s'' → s' = s''

end Numbers

section Series

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

structure ValR : Prop where
  val : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc
  p_nonunit : ((p : Kc))⁻¹ ∉ Oc

def geV (x : Kc) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : Kc) ^ (-a) ∈ Oc

def gaussGe {τ : Type} (y : MvPolynomial τ Kc) (g : ℝ) : Prop := ∀ n, geV p Oc (MvPolynomial.coeff n y) g

def IntSer {σ : Type} (f : MvPowerSeries σ Kc) : Prop := ∀ n, MvPowerSeries.coeff n f ∈ Oc

def JetInt {σ : Type} (f : MvPowerSeries σ Kc) : Prop :=
  ∀ n : σ →₀ ℕ, (∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f ∈ Oc

end Series

structure Shape where
  nV : ℕ
  n' : Fin nV → ℕ
  r0 : ℕ
  r1 : ℕ

namespace Shape

variable (Sh : Shape)

abbrev ZV : Type := Σ v : Fin Sh.nV, FormalGroupSystem.Zidx (Sh.n' v) Sh.r0 Sh.r1

abbrev FrV : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × ℕ × Fin Sh.r0

abbrev Wt : Type := ∀ v : Fin Sh.nV, Fin (Sh.n' v) → ℕ → ℤ

abbrev ColCh : Type := ∀ v : Fin Sh.nV, Fin (Sh.n' v) → ℕ → ℕ → Fin Sh.r1

def colHt (rb : ℕ) (nu : Sh.Wt) (v : Fin Sh.nV) (s : Fin (Sh.n' v)) (c : ℕ) : ℕ :=
  ((Icc 1 rb).filter fun i => (c : ℤ) < nu v s i).card

def colFac (rb : ℕ) (nu : Sh.Wt) (I : Sh.ColCh) (v : Fin Sh.nV) (s : Fin (Sh.n' v)) (c : ℕ) :
    MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ) :=
  Matrix.det (Matrix.of fun (i i' : Fin (Sh.colHt rb nu v s c)) =>
    ∑ a : Fin Sh.r0,
      MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : Sh.FrV)) *
        MvPolynomial.X (⟨v, (s, a, I v s c i'.val)⟩ : Sh.ZV))

def PI (rb : ℕ) (nu : Sh.Wt) (I : Sh.ColCh) : MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ) :=
  ∏ v : Fin Sh.nV, ∏ s : Fin (Sh.n' v), ∏ c ∈ range (nu v s 1).toNat, Sh.colFac rb nu I v s c

variable {Kc : Type} [Field Kc] (Oc : Subring Kc)

def KG (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : AddSubgroup (MvPolynomial Sh.FrV Kc) :=
  AddSubgroup.closure {y | ∃ (I : Sh.ColCh) (g : MvPolynomial Sh.FrV Kc), (∀ n, MvPolynomial.coeff n g ∈ Oc) ∧
    y = g * FormalGroupSystem.applyD (Sh.PI rb nu I) Th}

variable (p : ℕ)

def sS (v : Fin Sh.nV) (e : Fin (Sh.n' v)) (a : Fin Sh.r0) (b : Fin Sh.r1) : MvPowerSeries Sh.ZV Kc :=
  fun n => ∑ l ∈ range (n.degree + 1),
    if n = Finsupp.single (⟨v, (FormalGroupSystem.posSub e (2 * l), a, b)⟩ : Sh.ZV) (p ^ (2 * l)) then (-1) ^ l else 0

def hhV (v : Fin Sh.nV) (u : Fin (Sh.n' v) → Kc) : MvPowerSeries Sh.ZV Kc :=
  ∑ s : Fin (Sh.n' v), MvPowerSeries.C (u s) *
    ∑ a : Fin Sh.r0, ∑ b : Fin Sh.r1, (Sh.sS p v s a b) ^ p * Sh.sS p v (posAdd s 1) a b

def InProd (h : Fin Sh.nV → MvPowerSeries Sh.ZV Kc) (F : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∃ g : (Fin Sh.nV → ℕ) → MvPowerSeries Sh.ZV Kc, (∀ i, IntSer Oc (g i)) ∧
    ∀ α : Sh.ZV →₀ ℕ, MvPowerSeries.coeff α F =
      ∑ i ∈ Fintype.piFinset (fun _ : Fin Sh.nV => range (α.degree + 1)),
        MvPowerSeries.coeff α (MvPowerSeries.C (∏ v, ((p : Kc) ^ i v)⁻¹) * (∏ v, h v ^ i v) * g i)

def atPi (vp : Kc) (Th : MvPowerSeries Sh.ZV Kc) : MvPowerSeries Sh.ZV Kc :=
  fun n => vp ^ n.degree * MvPowerSeries.coeff n Th

end Shape

section Core

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (Sh : Shape)

structure HidaSetting (rb : ℕ) (nu : Sh.Wt) (vp : Kc) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  valR : ValR p Oc
  vp_pow : vp ^ (p ^ 2 - 1) = (p : Kc)
  even : ∀ v, Even (Sh.n' v)
  two_le : ∀ v, 2 ≤ Sh.n' v
  part : ∀ v, IsPart Sh.r0 (nu v)
  rb_ge : Sh.r0 ≤ rb

def valuationLowerBound (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) : ℝ :=
  ∑ v, (gsum p (TT v) (nu v) - de p Sh.r0 Sh.r1 rb (TT v) (nu v))

def ValuationOneKernel (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∀ TT : ∀ v, Finset (Fin (Sh.n' v)), ∀ y ∈ Sh.KG Oc rb nu Th,
    gaussGe p Oc y (valuationLowerBound p Sh rb nu TT) ∧ gaussGe p Oc y 0

def KernelValuationBoundGains (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∀ TT : ∀ v, Finset (Fin (Sh.n' v)), ∀ y ∈ Sh.KG Oc rb nu Th,
    gaussGe p Oc y (∑ v, g0 p Sh.r0 Sh.r1 rb (TT v) (nu v))


end Core

def CorollaryNotationWeights : Prop :=
  ∀ (p n' k1 t j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ), 1 ≤ k1 →
    g0 p (FormalGroupSystem.NN k1 t (j - 1)) (FormalGroupSystem.NN k1 t j) (FormalGroupSystem.NN k1 t j) TT (fun s i => FormalGroupSystem.nu t lam0 w j s i) =
      FormalGroupSystem.gA p t TT lam0 w j

def OneTopOddLevelsGain : Prop :=
  ∀ (p r0 r1 rb n' : ℕ) (nu : Fin n' → ℕ → ℤ) (s : Fin n'), DSet {s} s = ∅ ∧
    g0 p r0 r1 rb {s} nu = ∑' e : ℕ, gain p {s} nu s (2 * e + 1) - de p r0 r1 rb {s} nu

def OneParityTopsNoExclusion : Prop :=
  ∀ (p r0 r1 rb n' : ℕ) (nu : Fin n' → ℕ → ℤ) (TT : Finset (Fin n')),
    (∀ s ∈ TT, ∀ s' ∈ TT, ¬ OtherPar s s') →
    g0 p r0 r1 rb TT nu = ∑ s ∈ TT, ∑' e : ℕ, gain p TT nu s (2 * e + 1) - de p r0 r1 rb TT nu

def NoTopGainNegDefect : Prop :=
  ∀ (p r0 r1 rb n' : ℕ) (nu : Fin n' → ℕ → ℤ), g0 p r0 r1 rb (∅ : Finset (Fin n')) nu = -de p r0 r1 rb ∅ nu

section AtG

variable {p : ℕ} [Fact p.Prime] (X : FormalGroupSystem.Sys p)

def shX (j : ℕ) : Shape := ⟨X.G.P.nV, X.G.P.n', FormalGroupSystem.NN X.G.P.m X.t j, FormalGroupSystem.NN X.G.P.m X.t (j + 1)⟩

def nuX (j : ℕ) : (shX X j).Wt := fun v s i => X.nuv v (j + 1) s i

def rbX (j : ℕ) : ℕ := FormalGroupSystem.NN X.G.P.m X.t (j + 1)

variable {X} (Y : FormalGroupSystem.Pend X)

def ThX (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Y.Frm j La La') : MvPowerSeries (shX X j).ZV Y.Kc :=
  X.ThZA Y.Kc j (Y.ThA j La La' φ)

def KernelSecondLevelBound (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∃ φ : Y.Frm j La La', ∀ (f : MvPowerSeries (shX X j).ZV Y.Kc) (g : ℝ),
      (∀ I : (shX X j).ColCh, gaussGe p Y.Oc (FormalGroupSystem.applyD ((shX X j).PI (rbX X j) (nuX X j) I) f) g) →
      ∀ G ∈ (X.Pj j).HtupW La.2, Y.inLatC (j + 1) g La'.2 (Y.kerF j La La' (FormalGroupSystem.linSub (Y.bc j La La' φ) f) G)

end AtG

section AtD

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

def ct {nH : ℕ} (rb : ℕ) (TT : Finset (Fin nH)) (nu : Fin nH → Fin 2 → ℕ → ℤ) (t : Fin nH) : ℤ :=
  sz rb (nu t) 0 - (if t ∈ TT then nu t 0 1 - nu t 0 2 else 0) + (if t ∈ TT then nu t 1 1 else 0)

end AtD

section At22

open TaylorLogMetric

def valuationRingCp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := Subring.closure {x | ‖x‖ ≤ 1}

variable (D : D7) {p d : ℕ} (Po : Pos D p d) (N N' : ℕ)

def sh22 : Shape := ⟨Fintype.card {v // v ∈ Po.V}, fun _ => d, N, N'⟩

def toT (x : (sh22 D Po N N').ZV) : TVar D Po N N' :=
  ((x.2.1.val : ZMod d), ((Fintype.equivFin {v // v ∈ Po.V}).symm x.1, x.2.2.1, x.2.2.2))

variable {N N'} [Fact p.Prime] [NeZero d]

def Th22 (lam : Qbar →+* ℂ_[p]) (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
    (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E) (ep : ℂ_[p])
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : MvPowerSeries (sh22 D Po N N').ZV ℂ_[p] :=
  FormalGroupSystem.resV (toT D Po N N') (atLin (fun k j => ep * chg D lam Po P P' k j) (fun j => MvPowerSeries.X j) F)

def DerTie (lam : Qbar →+* ℂ_[p]) (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
    (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E)
    (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
    (L' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E)) : Prop :=
  ∀ j : TVar D Po N N', ∃ (m : ℕ) (r : Fin m → ℂ_[p]) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E),
    (∀ k, IsIntP (r k)) ∧ (∀ k, y k ∈ YYl D L L') ∧
      ∀ k' : D.what₂.Tau × Fin N' × Fin N,
        chg D lam Po P P' k' j = ∑ k, r k * lamC lam (embT D k'.1 (y k k'.2.1 k'.2.2))

end At22

open TaylorLogMetric in

def JetIntegralityAwayFromD (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ D.host.d → ∀ (N N' : ℕ)
    (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
    (L' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
    admitted D N N' L L' → IsComb D T e lam L L' F → JetsInt D lam (YYl D L L') F

open TaylorLogMetric in

theorem jet_integrality_of_integral (D : D7) (T : Tor D) (e : FamE D) (h : int22 D T e) : JetIntegralityAwayFromD D T e :=
  fun p _ lam hp N N' L L' F hA hC => ((h p lam N N' L L' hA).1 hp F hC).2.1

open TaylorLogMetric in

def InertOrbitsEven (D : D7) : Prop :=
  ∀ (p d : ℕ) (_ : Pos D p d), p.Prime → jacobiSym (-(D.host.d : ℤ)) p = -1 → Even d

open TaylorLogMetric in

def ValuationThetaFamily (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → AllSplit D p →
    ∀ (ep : ℂ_[p]), ‖ep‖ = 1 → ∀ (d : ℕ) [NeZero d] (Po : Pos D p d) (N N' : ℕ)
      (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
      (L' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E))
      (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
      (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E)
      (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
      (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) →
      IsComb D T e lam L L' F → DerTie D Po lam P P' L L' →
      ∀ (rb : ℕ) (nu : (sh22 D Po N N').Wt), (∀ v, IsPart N (nu v)) → N ≤ rb →
        ValuationOneKernel p (valuationRingCp p) (sh22 D Po N N') rb nu (Th22 D Po lam P P' ep F)

open TaylorLogMetric in

def StatementValuationTheta (D : D7) : Prop :=
  ∀ (T : Tor D) (e : FamE D), InertOrbitsEven D → str22 D T e → int22 D T e → ValuationThetaFamily D T e

section Leaf

def ze3 (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) (i1 : Fin h) : PowerSeries K :=
  PowerSeries.mk fun n =>
    ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (FormalGroupSystem.posSub i1 k)) ^ (p ^ (2 * k + 1))) / (p : K) ^ (k + 1)

def c3 (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) (i0 : Fin h) : K :=
  PowerSeries.coeff (p ^ 3) (ze3 p t (posAdd i0 1))

def Sp (p n : ℕ) : ℕ := (Nat.digits p n).sum

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

def IsU (x : Kc) : Prop := x ≠ 0 ∧ x ∈ Oc ∧ x⁻¹ ∈ Oc

def H1 (vp : Kc) (A : MvPowerSeries (Fin 2) Kc) : Prop :=
  (∀ n : Fin 2 →₀ ℕ, vp ^ n.degree * MvPowerSeries.coeff n A ∈ Oc) ∧ IsU Oc (MvPowerSeries.constantCoeff A)

def H2 (Psi : MvPowerSeries (Fin 2) Kc) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, (n 1 < p → MvPowerSeries.coeff n Psi = 0) ∧
    geV p Oc (MvPowerSeries.coeff n Psi) (-1 + 1 / ((p : ℝ) - 1) - ((n 0 : ℝ) + (n 1 : ℝ)) * rho p)

def hits (m : ℕ × ℕ →₀ ℕ) : ℕ := ∑ x ∈ m.support.filter (fun x => x.2 = 1), m x

end Leaf

theorem al_eq {n' k1 : ℕ} (t j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (hk : 1 ≤ k1) (s : Fin n') : al TT (fun s i => FormalGroupSystem.nu t lam0 w j s i) s = FormalGroupSystem.al TT lam0 s := by
  unfold al FormalGroupSystem.al FormalGroupSystem.nu
  have h1 : (1 ≤ 1 ∧ 1 ≤ k1 + 1) := ⟨le_refl _, by omega⟩
  have h2 : (1 ≤ 2 ∧ 2 ≤ k1 + 1) := ⟨by omega, by omega⟩
  simp only [h1, h2, and_self, if_true]
  split_ifs <;> ring


section G
variable {p : ℕ} [Fact p.Prime] (X : FormalGroupSystem.Sys p)

theorem colExp_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ) :
    X.colExp j I (fun _ => 0) v s c = 0 := by
  unfold FormalGroupSystem.Sys.colExp
  split_ifs <;> simp




end G


end Formalism.MainNotions.KernelEntryData
