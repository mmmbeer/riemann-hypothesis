import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta
import Formalism.LocalToGlobal.UnitaryNorms.IotaABijective
import Formalism.QuotientMetricDivisors.RatHermLcvTwist

open NumberField IntermediateField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.L2.Host Formalism.DivisionValues

instance normalQb : Normal ℚ Qb :=
  haveI : IsAlgClosure ℚ Qb := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  IsAlgClosure.normal ℚ Qb

def conjQb (ι : Qb →+* ℂ) : Qb ≃ₐ[ℚ] Qb :=
  AlgEquiv.ofRingEquiv (f := (algC ((starRingEnd ℂ).comp ι)).trans (algC ι).symm) (fun r => by simp)

theorem conjQb_spec (ι : Qb →+* ℂ) (x : Qb) : ι (conjQb ι x) = starRingEnd ℂ (ι x) := by
  have key : conjQb ι x = (algC ι).symm (algC ((starRingEnd ℂ).comp ι) x) := rfl
  rw [key, ← algC_coe ι ((algC ι).symm (algC ((starRingEnd ℂ).comp ι) x)),
    RingEquiv.apply_symm_apply, algC_coe] <;> rfl

theorem conjQb_conjQb (ι : Qb →+* ℂ) (x : Qb) : conjQb ι (conjQb ι x) = x := by
  apply ι.injective
  rw [conjQb_spec, conjQb_spec, Complex.conj_conj]

def cLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : LL ≃ₐ[ℚ] LL := (conjQb ι).restrictNormal LL

theorem cLL_coe (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : LL) : ((cLL ι LL x : LL) : Qb) = conjQb ι x := by
  first
  | exact AlgEquiv.restrictNormal_commutes (conjQb ι) LL x
  | exact AlgEquiv.restrictNormal_commutes (conjQb ι) x

theorem cLL_cLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : LL) : cLL ι LL (cLL ι LL x) = x := by
  apply Subtype.ext
  rw [cLL_coe, cLL_coe, conjQb_conjQb]

@[reducible] def starLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : StarRing LL where
  star := cLL ι LL
  star_involutive := cLL_cLL ι LL
  star_mul a b := by rw [map_mul, mul_comm]
  star_add a b := map_add _ a b

def CoF (_ι : Qb →+* ℂ) (LL : Fld) : Type := LL

namespace CoF

variable (ι : Qb →+* ℂ) (LL : Fld)

instance : Field (CoF ι LL) := inferInstanceAs (Field LL)

instance [FiniteDimensional ℚ LL] : NumberField (CoF ι LL) where
  to_charZero := inferInstanceAs (CharZero LL)
  to_finiteDimensional := inferInstanceAs (FiniteDimensional ℚ LL)

instance [Normal ℚ LL] : StarRing (CoF ι LL) := starLL ι LL

def val : CoF ι LL →+* Qb := LL.val.toRingHom

theorem val_injective : Function.Injective (val ι LL) := by
  intro a b hab
  exact Subtype.ext hab

theorem val_mem (x : CoF ι LL) : val ι LL x ∈ LL := (show LL from x).property

def mk (x : Qb) (hx : x ∈ LL) : CoF ι LL := (⟨x, hx⟩ : LL)

@[simp] theorem val_mk (x : Qb) (hx : x ∈ LL) : val ι LL (mk ι LL x hx) = x := rfl

theorem val_star [Normal ℚ LL] (x : CoF ι LL) : val ι LL (star x) = conjQb ι (val ι LL x) := cLL_coe ι LL x

end CoF

def sig0 (ι : Qb →+* ℂ) (LL : Fld) : CoF ι LL →+* ℂ := ι.comp (CoF.val ι LL)

def v0 (ι : Qb →+* ℂ) (LL : Fld) : InfinitePlace (CoF ι LL) := InfinitePlace.mk (sig0 ι LL)

def K0 (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : Subfield (CoF ι LL) := cmMax (CoF ι LL)

def cmQb (ι : Qb →+* ℂ) : Fld where
  carrier := {a | ∀ τ : Qb →+* ℂ, τ (conjQb ι a) = starRingEnd ℂ (τ a)}
  mul_mem' := by
    intro a b ha hb τ
    rw [map_mul, map_mul, map_mul, map_mul, ha τ, hb τ]
  add_mem' := by
    intro a b ha hb τ
    rw [map_add, map_add, map_add, map_add, ha τ, hb τ]
  inv_mem' := by
    intro a ha τ
    rw [map_inv₀, map_inv₀, map_inv₀, map_inv₀, ha τ]
  algebraMap_mem' := by
    intro r τ
    rw [AlgEquiv.commutes]
    simp

def tauLL {L LL : Fld} [Normal ℚ LL] (h : L ≤ LL) (s : L →ₐ[ℚ] Qb) : L →ₐ[ℚ] LL :=
  ((s.liftNormal Qb).restrictNormal LL).comp (inclusion h)

theorem tauLL_coe {L LL : Fld} [Normal ℚ LL] (h : L ≤ LL) (s : L →ₐ[ℚ] Qb) (x : L) :
    ((tauLL h s x : LL) : Qb) = s x := by
  have h1 : algebraMap LL Qb ((s.liftNormal Qb).restrictNormal LL (inclusion h x)) =
      (s.liftNormal Qb) (algebraMap LL Qb (inclusion h x)) := by
    first
    | exact AlgHom.restrictNormal_commutes _ _ _
    | exact AlgHom.restrictNormal_commutes _ _
  have h2 : (s.liftNormal Qb) (algebraMap L Qb x) = algebraMap Qb Qb (s x) := by
    first
    | exact AlgHom.liftNormal_commutes _ _ _
    | exact AlgHom.liftNormal_commutes _ _
  exact h1.trans h2

def tauCo (ι : Qb →+* ℂ) {L LL : Fld} [Normal ℚ LL] (h : L ≤ LL) (s : L →ₐ[ℚ] Qb) : L →+* CoF ι LL :=
  (tauLL h s).toRingHom

theorem val_tauCo (ι : Qb →+* ℂ) {L LL : Fld} [Normal ℚ LL] (h : L ≤ LL) (s : L →ₐ[ℚ] Qb) (x : L) :
    CoF.val ι LL (tauCo ι h s x) = s x := tauLL_coe h s x

structure IsCoeffField {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (Ns : List ℕ) (S : Set Qb) (LL : Fld) : Prop where

  fin : FiniteDimensional ℚ LL

  normal : Normal ℚ LL

  host : H.EQ ≤ LL

  cyc : ∀ N ∈ Ns, cycQ N ≤ LL

  vals : S ⊆ (LL : Set Qb)

def coeffMin {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (Ns : List ℕ) (S : Set Qb) : Fld :=
  normalClosure ℚ (H.EQ ⊔ adjoin ℚ ((⋃ N ∈ Ns, mus N) ∪ S) : Fld) Qb

def DistinguishedEmbeddingConjugation : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : CoF ι LL), sig0 ι LL (star x) = starRingEnd ℂ (sig0 ι LL x)

def ConjugationAtDistinguishedPlace : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL], IsConjAt (v0 ι LL)

def TotComplex : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) (d : ℕ), 0 < d → KQ d ≤ LL → IsTotallyComplex (CoF ι LL)

def CmQbIndep : Prop :=
  ∀ ι ι' : Qb →+* ℂ, cmQb ι = cmQb ι' ∧ ∀ x ∈ cmQb ι, conjQb ι x = conjQb ι' x

def CycLeCm : Prop := ∀ (ι : Qb →+* ℂ) (N : ℕ), 0 < N → cycQ N ≤ cmQb ι

def SqLeCm : Prop := ∀ (ι : Qb →+* ℂ) (m : ℤ), sqQ m ≤ cmQb ι

def TauStar : Prop :=
  ∀ (ι : Qb →+* ℂ) (L LL : Fld) [Normal ℚ LL] (h : L ≤ LL), L ≤ cmQb ι →
    ∀ (s : L →ₐ[ℚ] Qb) (x y : L), (y : Qb) = conjQb ι x → star (tauCo ι h s x) = tauCo ι h s y

end Formalism.L2.DIV
