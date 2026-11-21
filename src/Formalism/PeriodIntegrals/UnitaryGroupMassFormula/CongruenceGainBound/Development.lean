import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StatementFormalValuationAllFields

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

def applyDs {σ τ Kc : Type} [Field Kc] (vp : Kc) (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    MvPolynomial τ Kc :=
  ∑ n ∈ P.support, ((∏ x ∈ n.support, ((n x).factorial : Kc)) * (vp ^ n.degree)⁻¹ * MvPowerSeries.coeff n f) •
    MvPolynomial.map (Int.castRingHom Kc) (MvPolynomial.coeff n P)

def term (p : ℕ) {Kc : Type} [Field Kc] (Sh : Shape) (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc) (i : Fin Sh.nV → ℕ)
    (g : MvPowerSeries Sh.ZV Kc) : MvPowerSeries Sh.ZV Kc :=
  MvPowerSeries.C (∏ v, ((p : Kc) ^ i v)⁻¹) * (∏ v, Sh.hhV p v (u v) ^ i v) * g

def degP (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) : ℕ := ∑ v, ∑ s, (sz rb (nu v) s).toNat

structure Counts (Sh : Shape) where
  ec : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin Sh.r1 → ℕ
  ih : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → ℕ → ℕ
  i0 : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin (Sh.n' v) → ℕ
  i2 : Fin Sh.nV → ℕ
  be : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin Sh.r0 → Fin Sh.r1 → ℕ
  N : ℕ

def Counts.hits {Sh : Shape} (D : Counts Sh) (v : Fin Sh.nV) (s' : Fin (Sh.n' v)) : ℕ :=
  ∑ s, ∑ e ∈ range D.N, if posAdd s e = s' then D.ih v s e else 0

def Counts.mtot {Sh : Shape} (D : Counts Sh) : ℕ :=
  ∑ v, ((∑ s, ∑ s', D.i0 v s s') + D.i2 v + ∑ s, ∑ e ∈ range D.N, D.ih v s e)

structure Counts.Ok (p : ℕ) {Sh : Shape} (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) (D : Counts Sh) : Prop where
  ec_sum : ∀ v s, ((∑ b, D.ec v s b : ℕ) : ℤ) = al (TT v) (nu v) s
  ih_supp : ∀ v s e, D.ih v s e ≠ 0 → s ∈ TT v ∧ Odd e ∧ e < D.N
  h1 : ∀ v s e, (D.ih v s e : ℤ) ≤ cap (TT v) (nu v) (posAdd s e)
  h2 : ∀ v s e, ((p ^ e * D.ih v s e : ℕ) : ℤ) ≤ al (TT v) (nu v) s
  zero_index_support : ∀ v s s', D.i0 v s s' ≠ 0 → s ∈ TT v ∧ s' ∈ TT v ∧ OtherPar s s'
  pair : ∀ v s s', s ∈ TT v → s' ∈ TT v → OtherPar s s' →
    ((p ^ dLev s s' * (D.i0 v s s' + D.ih v s (dLev s s')) : ℕ) : ℤ) ≤ al (TT v) (nu v) s
  b2 : ∀ v, ((p * D.i2 v : ℕ) : ℤ) ≤ ∑ s, low rb (TT v) (nu v) s
  be_sum : ∀ v s, ((∑ a, ∑ b, D.be v s a b : ℕ) : ℤ) = low rb (TT v) (nu v) s - D.hits v s
  be_le : ∀ v s a b, (D.be v s a b : ℤ) ≤ low rb (TT v) (nu v) s

def Counts.coef (p : ℕ) {Kc : Type} [Field Kc] (vp : Kc) {Sh : Shape} (rb : ℕ) (nu : Sh.Wt) (D : Counts Sh) : Kc :=
  (vp ^ degP Sh rb nu)⁻¹ * ((p : Kc) ^ D.mtot)⁻¹ *
    ((∏ v, ∏ s, ∏ b, ((D.ec v s b).factorial : Kc)) * (∏ v, ∏ s, ∏ e ∈ range D.N, ((D.ih v s e).factorial : Kc)) *
      (∏ v, ∏ s, ∏ a, ∏ b, ((D.be v s a b).factorial : Kc)))

def Gen (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (vp : Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt)
    (TT : ∀ v, Finset (Fin (Sh.n' v))) : Set (MvPolynomial Sh.FrV Kc) :=
  {y | ∃ D : Counts Sh, D.Ok p rb nu TT ∧ ∃ r : MvPolynomial Sh.FrV Kc, (∀ n, MvPolynomial.coeff n r ∈ Oc) ∧
    y = MvPolynomial.C (D.coef p vp rb nu) * r}

def SLin : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc)
    (Th : MvPowerSeries Sh.ZV Kc) (I : Sh.ColCh) (A : AddSubgroup (MvPolynomial Sh.FrV Kc)),
    HidaSetting p Oc Sh rb nu vp → InMM p Oc Sh vp Th →
    (∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) → ∀ (i : Fin Sh.nV → ℕ) (g : MvPowerSeries Sh.ZV Kc),
      IntSer Oc g → applyDs vp (Sh.PI rb nu I) (term p Sh u i g) ∈ A) →
    FormalGroupSystem.applyD (Sh.PI rb nu I) Th ∈ A

def SStruct : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp →
    ∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) →
    ∀ (i : Fin Sh.nV → ℕ) (g : MvPowerSeries Sh.ZV Kc), IntSer Oc g →
    ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh),
      applyDs vp (Sh.PI rb nu I) (term p Sh u i g) ∈ AddSubgroup.closure (Gen p Oc vp Sh rb nu TT)

def SVal : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))),
    ∀ y ∈ Gen p Oc vp Sh rb nu TT, gaussGe p Oc y (formalValuationLowerBound p Sh rb nu TT)

def S0 : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc), p.Prime → ValR p Oc →
    ∀ (m : ℕ) (al : Fin m → ℕ) (M : ℤ), (∀ k, (al k : ℤ) ≤ M) →
      geV p Oc ((∏ k, ((al k).factorial : Kc))) ((∑ k, (al k : ℝ)) / ((p : ℝ) - 1) - (m : ℝ) * (lg p M : ℝ))

end PI.UnitaryGroupMassFormula.PadicGainBound
