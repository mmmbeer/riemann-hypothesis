import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.SharpRestriction.InertJacobiLevels.TieTTwValsOfMem

section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.Inhab.GC

structure GHost (R : Ranks) where
  TT : Finset (R.A)
  T2 : Finset ℕ
  u0 : R.A
  cls : ℕ → PrimeClass

structure GD where
  R : Ranks
  host : GHost R
  hPf : ℕ → R.A

structure GParameters (D : GD) where
  sc : Scale
  Sc : ℝ
  etaSz : ℝ

def GParameters.lifts (D : GD) : Finset ℕ := Finset.Icc 1 D.R.m

abbrev HH (D : GD) : Type := D.R.A

def cG {D : GD} (L : GParameters D) : ℝ := 4 * L.Sc

def Nm (D : GD) : ℝ := (D.R.N D.R.m : ℝ)

def L1 (D : GD) (s : Scale) (p : ℕ) : ℕ := ⌈Real.logb p (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4)⌉₊

def L2 (D : GD) (s : Scale) : ℕ :=
  2 * sSup {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D s p}

def Nstar (D : GD) (s : Scale) : ℝ := 2 * (D.R.n : ℝ) * s.delta1

def rho (D : GD) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * (N1 s : ℝ) * La K s / D.R.k

def rhoB (D : GD) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * K.CN * Real.log s.x * La K s / D.R.k

def InBand (D : GD) (K : Consts) (s : Scale) (p : ℕ) : Prop :=
  s.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < s.X' ∧ ∃ d : ℕ, 1 ≤ d ∧
    s.X' * (1 - rhoB D K s) ≤ (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ s.X' * (1 + rhoB D K s)

def c0num {D : GD} (L : GParameters D) : ℝ := 2 * L.sc.b' + 2 * cG L

def hP (D : GD) (p : ℕ) : HH D := D.hPf p

abbrev IsResidueClassZero (D : GD) (p : ℕ) : Prop := D.host.cls p = PrimeClass.inertClass

abbrev IsSg (D : GD) (p : ℕ) : Prop := D.host.cls p = PrimeClass.signal

def partner (D : GD) (p : ℕ) (t : HH D) (e : ℕ) : Bool × HH D :=
  (decide (IsSg D p ∧ Odd e), t + e • hP D p)

def IsTopPl (D : GD) (z : Bool × HH D) : Prop := z.1 = false ∧ z.2 ∈ D.host.TT

def IsThickPl (D : GD) (z : Bool × HH D) : Prop :=
  z.1 = true ∧ z.2 ∈ D.host.T2.image (fun s : ℕ => D.R.dig s + D.host.u0)

def IsThinPl (D : GD) (z : Bool × HH D) : Prop := ¬ IsTopPl D z ∧ ¬ IsThickPl D z

structure Inst (D : GD) (L : GParameters D) where
  bs : HH D → HH D → HH D
  bs_orb : ∀ h t, ∃ i : ℕ, bs h t + i • h = t
  bs_step : ∀ h t, bs h (t + h) = bs h t
  off : ℕ → Bool × HH D → ℝ
  off_top : ∀ j z, IsTopPl D z → L.sc.b' / L.sc.x ≤ off j z ∧ off j z ≤ L.sc.b' / L.sc.x + L.etaSz
  off_thin : ∀ j z, IsThinPl D z → L.sc.w'' D.R.n ≤ off j z ∧ off j z ≤ L.sc.w'' D.R.n + L.etaSz
  off_thick : ∀ j z, IsThickPl D z → L.sc.b ≤ off j z ∧ off j z ≤ L.sc.b + L.etaSz + 1
  kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ
  ep : ℕ → ℕ

variable {D : GD} {L : GParameters D}

def fill (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (z : Bool × HH D) : ℝ :=
  (if z.1 = false ∧ z.2 ∈ D.host.TT then (b z.2 : ℝ) else 0) + X.off j z

def kaJ (D : GD) (j : ℕ) : ℝ := ((D.R.k : ℝ) + (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1)) / 2

def fillG (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (z : Bool × HH D) : ℝ := fill X b j z - kaJ D j

def stepP (D : GD) (p : ℕ) : HH D := if IsSg D p then 2 • hP D p else hP D p

def nP (D : GD) (p : ℕ) : ℕ :=
  if IsSg D p then 2 * addOrderOf (2 • hP D p) else addOrderOf (hP D p)

def reps (X : Inst D L) (p : ℕ) : Finset (HH D) := Finset.univ.image (X.bs (stepP D p))

def topsOn (X : Inst D L) (p : ℕ) (t0 : HH D) : Finset (HH D) :=
  D.host.TT.filter (fun t => X.bs (stepP D p) t = t0)

def Nv (X : Inst D L) (p : ℕ) (t0 : HH D) : ℕ := (topsOn X p t0).card

def topsPos (D : GD) (p : ℕ) (t0 : HH D) : Finset (Fin (addOrderOf (hP D p))) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • hP D p ∈ D.host.TT)

def wPos (D : GD) (p : ℕ) (t0 : HH D) (a : HH D → ℤ) : Fin (addOrderOf (hP D p)) → ℤ :=
  fun i => a (t0 + (i : ℕ) • hP D p)

def IsV (X : Inst D L) (p : ℕ) (t : HH D) : Prop :=
  ∃ i : ℕ, i < nP D p ∧ Even i ∧ X.bs (stepP D p) t + i • hP D p = t

def Good (_X : Inst D L) (p : ℕ) (t0 : HH D) : Prop :=
  IsGoodOrbit (addOrderOf (hP D p)) (topsPos D p t0) (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1
    (hG L.sc) L.sc.x

def DIIf (K : Consts) (L : GParameters D) (p n' : ℕ) : ℕ :=
  ⌈K.DII * NplusF L.sc n' * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) *
      Real.logb p L.sc.a + 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L +
      (rG L.sc : ℝ) * NplusF L.sc n' * c0num L⌉₊

def DIf (K : Consts) (L : GParameters D) (p n' : ℕ) : ℕ :=
  ⌈K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
      Real.logb p L.sc.a⌉₊

def tIIf (K : Consts) (L : GParameters D) (p n' N : ℕ) : ℝ :=
  K.tII * (rG L.sc : ℝ) * (N : ℝ) * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
    L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) + c0num L + (D.R.k : ℝ) * Qp L.sc p) +
    2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L

def kapIIf (K : Consts) (L : GParameters D) (N : ℕ) : ℝ :=
  min 1 (K.kII * (N : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) * L.sc.x ^ (-Scale.A))

def c6f (K : Consts) (L : GParameters D) (p n' : ℕ) : ℝ :=
  8 * ((DIf K L p n' : ℝ) + 1) + K.kappaThresholdTwo * NplusF L.sc n' * (D.R.k : ℝ) * Real.logb p L.sc.a +
    4 * NplusF L.sc n' * cG L + 2 * (n' : ℝ) * cG L

open Classical in
def tIf (K : Consts) (L : GParameters D) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
  (∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
      (if dMinus TT y = 0 then 0 else
        min (b y : ℝ) ((a (posAdd y (n' - dMinus TT y)) : ℝ) / (p : ℝ) ^ dMinus TT y))) +
    K.kappaThresholdOne * (TT.card : ℝ) * (N1 L.sc : ℝ) *
      (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) +
    K.kappaThresholdTwo * (TT.card : ℝ) * (Qp L.sc p * c6f K L p n' +
      (D.R.k : ℝ) * Qp L.sc p +
      (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) + 2 * (n' : ℝ) * cG L

def kapLoc (X : Inst D L) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
  if (p : ℝ) < L.sc.p0 D.R.k then kapIIf K L TT.card else X.kapI p n' TT a b

def al (L : GParameters D) (a : HH D → ℤ) (s : HH D) : ℝ := (a s : ℝ) - 2 * cG L

def capU (X : Inst D L) (b : HH D → ℤ) (p j : ℕ) (s : HH D) (e : ℕ) : ℝ :=
  fillG X b j (partner D p s e) + cG L

def IsDist (D : GD) (p : ℕ) (s s' : HH D) (e : ℕ) : Prop :=
  0 < e ∧ partner D p s e = (false, s') ∧ ∀ e', 0 < e' → e' < e → partner D p s e' ≠ (false, s')

def Excl (D : GD) (p : ℕ) (s : HH D) (e : ℕ) : Prop :=
  Odd e ∧ ∃ s' ∈ D.host.TT, s' ≠ s ∧ IsDist D p s s' e

def dl (X : Inst D L) (K : Consts) (p : ℕ) (t0 : HH D) : ℝ :=
  K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
    K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2

open Classical in
def g0 (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  (∑ s ∈ topsOn X p t0, ∑' e : ℕ,
    if Odd e ∧ ¬ Excl D p s e then max 0 (al L a s / (p : ℝ) ^ e - capU X b p j s e) else 0) -
    dl X K p t0

open Classical in
def gU (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  gam p * (∑ s ∈ topsOn X p t0, al L a s) -
    (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), ∑' e : ℕ,
      if Odd e then min (al L a s / (p : ℝ) ^ e) (capU X b p j s e) else 0) -
    dl X K p t0

open Classical in
def Pr (X : Inst D L) (K : Consts) (b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  if L.sc.p0 D.R.k ≤ (p : ℝ) then
    (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), (fillG X b j (false, s) - (b s : ℝ))) +
      K.Pr1 * (nP D p : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D)
  else (rG L.sc : ℝ) * ((Nv X p t0 : ℝ) * (2 * L.sc.b' + cG L) +
      (nP D p : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D))

def Dp (K : Consts) (L : GParameters D) (p : ℕ) : ℕ :=
  if (p : ℝ) < L.sc.p0 D.R.k then DIIf K L p (nP D p) else DIf K L p (nP D p)

def tv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  if (p : ℝ) < L.sc.p0 D.R.k then tIIf K L p (nP D p) (Nv X p t0)
  else tIf K L p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b)

def kapv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  kapLoc X K p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b)

def Cand (D : GD) (L : GParameters D) (K : Consts) (p : ℕ) : Prop :=
  p.Prime ∧ (p : ℝ) < L.sc.X' ∧ IsResidueClassZero D p ∧ L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) ∧
    (L.sc.p0 D.R.k ≤ (p : ℝ) → ¬ InBand D K L.sc p)

open Classical in
def goodReps (X : Inst D L) (p : ℕ) : Finset (HH D) := (reps X p).filter (fun t0 => Good X p t0)

def Sig (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  (D.R.m : ℝ) * ∑ t0 ∈ goodReps X p, kapv X K a b p t0

open Classical in
def VV (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : Finset (HH D) :=
  if Cand D L K p ∧ Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps) then goodReps X p else ∅

def Sv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  (⌈∑ j ∈ GParameters.lifts D, max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0)⌉ : ℤ)

open Classical in
def tauP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if VV X K a b p = ∅ then 0 else
    (X.ep p : ℝ) + ∑ t0 ∈ VV X K a b p,
      (D.R.m : ℝ) * ((⌈tv X K a b p t0⌉₊ : ℝ) + (Dp K L p : ℝ) + 1)

open Classical in
def ioP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if h : (VV X K a b p).Nonempty then
    2 * Sig X K a b p * (VV X K a b p).sup' h (fun t0 => Sv X K a b p t0)
  else 0

open Classical in
def gainP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) : ℝ :=
  if (IsResidueClassZero D p ∧ hP D p = 0) ∨ L.sc.X'' D.R.n < (p : ℝ) then 0 else
    (∑ t0 ∈ VV X K a b p, max (gU X K a b p j t0 - Pr X K b p j t0) (max (g0 X K a b p j t0) 0)) +
    ∑ t0 ∈ reps X p \ VV X K a b p, max (g0 X K a b p j t0) 0

open Classical in
def TTP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : Finset (HH D) :=
  if IsSg D p ∨ L.sc.X' ≤ (p : ℝ) then D.host.TT
  else D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ VV X K a b p)

end Formalism.MainNotions.Inhab.GC

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def viewD (D : D7) : GC.GD := ⟨D.R, ⟨D.host.TT, D.host.T2, D.host.u0, D.host.cls⟩, G.hP D⟩

def viewL {D : D7} (L : SizeData₂ D) : GC.GParameters (viewD D) := ⟨L.sc, L.Sc, L.etaSz⟩

def viewX {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : GC.Inst (viewD D) (viewL L) where
  bs := X.bs
  bs_orb := X.bs_orb
  bs_step := X.bs_step
  off := X.off
  off_top := X.off_top
  off_thin := X.off_thin
  off_thick := X.off_thick
  kapI := X.kapI
  ep := X.ep

section View

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ)








end View

structure GAll where
  D : GC.GD
  L : GC.GParameters D
  X : GC.Inst D L
  a : GC.HH D → ℤ
  b : GC.HH D → ℤ

theorem GAll.ext_val (A A' : GAll) (hR : A.D.R = A'.D.R)
    (hTT : A.D.host.TT.image Formalism.HC.Frame.A.val = A'.D.host.TT.image Formalism.HC.Frame.A.val)
    (hT2 : A.D.host.T2 = A'.D.host.T2) (hu0 : A.D.host.u0.val = A'.D.host.u0.val)
    (hcls : A.D.host.cls = A'.D.host.cls) (hhP : ∀ p, (A.D.hPf p).val = (A'.D.hPf p).val)
    (hsc : A.L.sc = A'.L.sc) (hSc : A.L.Sc = A'.L.Sc) (heta : A.L.etaSz = A'.L.etaSz)
    (hbs : ∀ (h t : GC.HH A.D) (h' t' : GC.HH A'.D), h.val = h'.val → t.val = t'.val →
      (A.X.bs h t).val = (A'.X.bs h' t').val)
    (hoff : ∀ j c (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.X.off j (c, t) = A'.X.off j (c, t'))
    (hkap : A.X.kapI = A'.X.kapI) (hep : A.X.ep = A'.X.ep)
    (ha : ∀ (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.a t = A'.a t')
    (hb : ∀ (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.b t = A'.b t') : A = A' := by
  obtain ⟨⟨R, ⟨TT, T2, u0, cls⟩, hPf⟩, ⟨sc, Sc, eta⟩,
    ⟨bs, bs_orb, bs_step, off, off_top, off_thin, off_thick, kapI, ep⟩, a, b⟩ := A
  obtain ⟨⟨R', ⟨TT', T2', u0', cls'⟩, hPf'⟩, ⟨sc', Sc', eta'⟩,
    ⟨bs', bs_orb', bs_step', off', off_top', off_thin', off_thick', kapI', ep'⟩, a', b'⟩ := A'
  dsimp only at hR hTT hT2 hu0 hcls hhP hsc hSc heta hbs hoff hkap hep ha hb
  subst hR hT2 hcls hsc hSc heta hkap hep
  have hTTe : TT = TT' := Finset.image_injective (fun x y h => Fin.ext h) hTT
  have hu0e : u0 = u0' := Fin.ext hu0
  have hPfe : hPf = hPf' := funext fun p => Fin.ext (hhP p)
  subst hTTe hu0e hPfe
  have hbse : bs = bs' := funext fun h => funext fun t => Fin.ext (hbs h t h t rfl rfl)
  have hoffe : off = off' := funext fun j => funext fun z => hoff j z.1 z.2 z.2 rfl
  have hae : a = a' := funext fun t => ha t t rfl
  have hbe : b = b' := funext fun t => hb t t rfl
  subst hbse hoffe hae hbe
  rfl

namespace GAll

variable (A : GAll) (K : G.Consts)

def Xpp : ℝ := A.L.sc.X'' A.D.R.n

def wPartV (j tv p e : ℕ) : ℝ := GC.fill A.X A.b j (GC.partner A.D p (A.D.R.ofNat tv) e)

def TTPv (p : ℕ) : Finset ℕ := (GC.TTP A.X K A.a A.b p).image Formalism.HC.Frame.A.val

open Classical in

def gainTotV (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ A.Xpp then 2 * Real.log p *
    ((if GC.IsResidueClassZero A.D p ∨ GC.IsSg A.D p then ∑ j ∈ GC.GParameters.lifts A.D, GC.gainP A.X K A.a A.b p j else 0) -
      GC.tauP A.X K A.a A.b p)
  else 0

open Classical in

def ioTotV (p : ℕ) : ℝ := if (p : ℝ) ≤ A.Xpp then 2 * Real.log p * GC.ioP A.X K A.a A.b p else 0

end GAll

def allOf {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : GAll := ⟨viewD D, viewL L, viewX X, G.aL L, G.bL L⟩


theorem host_cls_eq {R R' : Ranks} {H : Host R} {H' : Host R'} (hq : H.q = H'.q) (hd : H.d = H'.d)
    (hQS : H.QS = H'.QS) : H.cls = H'.cls := by
  have hN : H.toHostRaw.condN = H'.toHostRaw.condN := by
    simp only [Formalism.HC.HostRaw.condN, hq, hd, hQS]

  have hps : ∀ p, H.toHostRaw.psAt p = H'.toHostRaw.psAt p := by
    intro p
    unfold Formalism.HC.HostRaw.psAt
    by_cases hc : Nat.Coprime p H.toHostRaw.condN
    · have hc' : Nat.Coprime p H'.toHostRaw.condN := by
        rw [← hN]
        exact hc
      rw [dif_pos hc, dif_pos hc']
      have e := H.flPS (ZMod.unitOfCoprime p hc)
      have e' := H'.flPS (ZMod.unitOfCoprime p hc')
      rw [e, e']
      simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Formalism.HC.HostRaw.condN, hq, hd, hQS]
    · have hc' : ¬ Nat.Coprime p H'.toHostRaw.condN := by
        rw [← hN]
        exact hc
      rw [dif_neg hc, dif_neg hc']
  funext p
  unfold Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass
  rw [hps p]
  simp only [Formalism.HC.HostRaw.small, hq, hd, hQS]
  split_ifs <;> simp_all


section Tied

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts) (dr : Set ℕ)
  (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
  (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
  (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)




open Classical in
theorem tie_TTwVals_V (p : ℕ) (hp : p.Prime) :
    TTwVals (tieWeightData L0 X0 K dr len hw hg hu) p = if UnderSupp L0 p then {(allOf X0).TTPv K p} else ∅ :=
  tie_TTwVals L0 X0 K dr len hw hg hu p hp

end Tied


end Formalism.MainNotions.Inhab

end
end
