import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Development

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

abbrev UV (Sh : Shape) : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × Fin Sh.r1

abbrev AV (Sh : Shape) : Type := Sh.ZV ⊕ UV Sh

def IntA {σ τ Kc : Type} [Field Kc] (Oc : Subring Kc) (F : MvPowerSeries σ (MvPolynomial τ Kc)) : Prop :=
  ∀ n m, MvPolynomial.coeff m (MvPowerSeries.coeff n F) ∈ Oc

def subV (Sh : Shape) (Kc : Type) [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v))) :
    Sh.ZV → MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)
  | ⟨v, (s, a, b)⟩ => MvPowerSeries.X (Sum.inl ⟨v, (s, a, b)⟩) +
      if s ∈ TT v then
        MvPowerSeries.C (MvPolynomial.X (⟨v, (s, 0, a)⟩ : Sh.FrV)) * MvPowerSeries.X (Sum.inr ⟨v, (s, b)⟩)
      else 0

def subF (Sh : Shape) {Kc : Type} [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v))) (f : MvPowerSeries Sh.ZV Kc) :
    MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  MvPowerSeries.subst (subV Sh Kc TT) f

def abelian₂ {Sh : Shape} {Kc : Type} [Field Kc] (Q : MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ)) (e : UV Sh →₀ ℕ)
    (F : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)) : MvPolynomial Sh.FrV Kc :=
  MvPolynomial.C (∏ t ∈ e.support, ((e t).factorial : Kc)) *
    ∑ n ∈ Q.support, MvPolynomial.C (∏ x ∈ n.support, ((n x).factorial : Kc)) *
      MvPowerSeries.coeff (Finsupp.sumElim n e) F * MvPolynomial.map (Int.castRingHom Kc) (MvPolynomial.coeff n Q)

def QP (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) :
    MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ) :=
  ∏ v : Fin Sh.nV, ∏ s : Fin (Sh.n' v),
    ∏ c ∈ (range (nu v s 1).toNat).filter (fun c : ℕ => ¬ (s ∈ TT v ∧ nu v s 2 ≤ (c : ℤ))), Sh.colFac rb nu I v s c

def eV (Sh : Shape) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) : UV Sh →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun t =>
    if t.2.1 ∈ TT t.1 then
      ((range (nu t.1 t.2.1 1).toNat).filter (fun c : ℕ => nu t.1 t.2.1 2 ≤ (c : ℤ) ∧ I t.1 t.2.1 c 0 = t.2.2)).card
    else 0

abbrev ETI (Sh : Shape) : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × ℕ × ℕ × Fin 4

def zt (p : ℕ) (Sh : Shape) (Kc : Type) [Field Kc] (v : Fin Sh.nV) (sg : Fin (Sh.n' v)) (k : ℕ)
    (a : Fin Sh.r0) (b : Fin Sh.r1) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  MvPowerSeries.X (Sum.inl ⟨v, (sg, a, b)⟩) ^ (p ^ k)

def ut (p : ℕ) (Sh : Shape) (Kc : Type) [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v))) (v : Fin Sh.nV)
    (sg : Fin (Sh.n' v)) (k : ℕ) (a : Fin Sh.r0) (b : Fin Sh.r1) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  if sg ∈ TT v then
    MvPowerSeries.C (MvPolynomial.X (⟨v, (sg, 0, a)⟩ : Sh.FrV) ^ (p ^ k)) * MvPowerSeries.X (Sum.inr ⟨v, (sg, b)⟩) ^ (p ^ k)
  else 0

def S1 : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) (f : MvPowerSeries Sh.ZV Kc),
      applyDs vp (Sh.PI rb nu I) f =
        MvPolynomial.C ((vp ^ degP Sh rb nu)⁻¹) * abelian₂ (QP Sh rb nu TT I) (eV Sh nu TT I) (subF Sh TT f)

section abelian₂

variable {Sh : Shape} {Kc : Type} [Field Kc] (Q : MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ)) (e : UV Sh →₀ ℕ)

end abelian₂

end PI.UnitaryGroupMassFormula.PadicGainBound
