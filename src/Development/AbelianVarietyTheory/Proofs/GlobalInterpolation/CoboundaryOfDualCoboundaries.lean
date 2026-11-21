import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.GaloisValuations.ArithOfA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CocyclesCyclotomicFinrankThree

section
open NumberField IsDedekindDomain

namespace GlobalTheory.V.FrobQ

instance isAlgClosure_algebraicClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  let i : Algebra ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instAlgebra ℚ (R := ℚ)
  have h : IsAlgClosure ℚ (AlgebraicClosure ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _

end GlobalTheory.V.FrobQ
end

section
noncomputable section

namespace GlobalTheory.OrdLoc.Dcmp

open Formalism.ConjugateSelfDual Formalism.MainNotions.V

section Level

variable {G : Type} [Group G] [TopologicalSpace G] {R : Type} [CommRing R]

def finiteCocycles (γ : G →* Rˣ) : Set (G → R) :=
  {z | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (γ g : R) * z h}

def chR {H S T : Type} [Group H] [CommRing S] [CommRing T] (z : S →+* T) (χ : H →* Sˣ) : H →* Tˣ :=
  (Units.map z.toMonoidHom).comp χ

@[simp] theorem chR_apply {H S T : Type} [Group H] [CommRing S] [CommRing T] (z : S →+* T) (χ : H →* Sˣ) (g : H) :
    (chR z χ g : T) = z (χ g : S) := rfl

def diffId {H : Type} [Group H] (γ δ : H →* Rˣ) : Ideal R := Ideal.span (Set.range fun g => (γ g : R) - (δ g : R))

variable {l : ℕ} [Fact l.Prime]

def FinCount (χ : G →* ℤ_[l]ˣ) : Prop :=
  ∀ (R : Type) [CommRing R] [Finite R] (r : ℕ), (l : R) ^ r = 0 → ∀ (z : ℤ_[l] →+* R) (γ : G →* Rˣ),
    IsLocallyConstant (fun g => (γ g : R)) →
      (finiteCocycles γ).Finite ∧ (finiteCocycles γ).ncard = Nat.card (R ⧸ diffId γ (chR z χ)) * Nat.card R ^ 2

end Level

section Ints

variable (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E] [NormedAlgebra ℚ_[l] E]

def zE : ℤ_[l] →+* E := (algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom

theorem zE_apply (x : ℤ_[l]) : zE l E x = algebraMap ℚ_[l] E (x : ℚ_[l]) := rfl

theorem norm_zE (x : ℤ_[l]) : ‖zE l E x‖ = ‖x‖ := by
  rw [zE_apply, norm_algebraMap']; rfl

theorem zE_injective : Function.Injective (zE l E) :=
  (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective

theorem l_ne_zero : (l : E) ≠ 0 := by
  rw [← map_natCast (zE l E), map_ne_zero_iff _ (zE_injective l E)]
  exact_mod_cast (Fact.out : l.Prime).ne_zero

def Oi : Subring E where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rw [norm_neg]; exact ha

theorem mem_Oi {x : E} : x ∈ Oi l E ↔ ‖x‖ ≤ 1 := Iff.rfl

def zO : ℤ_[l] →+* Oi l E := (zE l E).codRestrict _ fun x => by
  rw [mem_Oi, norm_zE]; exact x.2

@[simp] theorem coe_zO (x : ℤ_[l]) : (zO l E x : E) = zE l E x := rfl

abbrev Qn (n : ℕ) : Type := Oi l E ⧸ Ideal.span {(l : Oi l E) ^ n}

def red (n : ℕ) : Oi l E →+* Qn l E n := Ideal.Quotient.mk _

def fac {m n : ℕ} (h : m ≤ n) : Qn l E n →+* Qn l E m :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h))

@[simp] theorem fac_red {m n : ℕ} (h : m ≤ n) (x : Oi l E) : fac l E h (red l E n x) = red l E m x := rfl

theorem red_surjective (n : ℕ) : Function.Surjective (red l E n) := Ideal.Quotient.mk_surjective

theorem red_eq_zero_iff_dvd (n : ℕ) (x : Oi l E) : red l E n x = 0 ↔ (l : Oi l E) ^ n ∣ x := by
  rw [red, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem dvd_iff_norm_le {a x : Oi l E} (ha : a ≠ 0) : a ∣ x ↔ ‖(x : E)‖ ≤ ‖(a : E)‖ := by
  have ha' : (a : E) ≠ 0 := fun h => ha (Subtype.ext h)
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) y.2
  · intro h
    refine ⟨⟨x / a, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_Oi, norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · show (x : E) = a * (x / a)
      field_simp

theorem lO_ne_zero : (l : Oi l E) ≠ 0 := fun h => l_ne_zero l E (by simpa using congrArg Subtype.val h)

theorem red_eq_zero_iff (n : ℕ) (x : Oi l E) : red l E n x = 0 ↔ ‖(x : E)‖ ≤ ‖(l : E)‖ ^ n := by
  rw [red_eq_zero_iff_dvd, dvd_iff_norm_le l E (pow_ne_zero _ (lO_ne_zero l E))]
  simp

theorem red_eq_iff (n : ℕ) (x y : Oi l E) : red l E n x = red l E n y ↔ ‖(x : E) - y‖ ≤ ‖(l : E)‖ ^ n := by
  rw [← sub_eq_zero, ← map_sub, red_eq_zero_iff]; rfl

theorem isLocallyConstant_red' (n : ℕ) : IsLocallyConstant (red l E n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hp : 0 < ‖(l : E)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l E)) n
  filter_upwards [Metric.closedBall_mem_nhds x hp] with y hy
  rw [red_eq_iff, ← dist_eq_norm]
  exact hy

def mulL (m n : ℕ) : Qn l E m →ₗ[Oi l E] Qn l E (m + n) :=
  Submodule.mapQ _ _ (LinearMap.mul _ _ ((l : Oi l E) ^ n)) fun x hx => by
    rw [Submodule.mem_comap, Ideal.mem_span_singleton, pow_add, mul_comm]
    exact mul_dvd_mul_left _ (Ideal.mem_span_singleton.1 hx)

@[simp] theorem mulL_red (m n : ℕ) (x : Oi l E) :
    mulL l E m n (red l E m x) = red l E (m + n) ((l : Oi l E) ^ n * x) := rfl

variable [FiniteDimensional ℚ_[l] E]

include l in
theorem properSpace : ProperSpace E := FiniteDimensional.proper ℚ_[l] E

instance compactSpace_Oi : CompactSpace (Oi l E) := by
  have := properSpace l E
  have h : IsCompact (Oi l E : Set E) := by
    convert isCompact_closedBall (0 : E) 1 using 1
    ext x
    simp [mem_Oi]
  exact isCompact_iff_compactSpace.1 h

instance finite_Qn (n : ℕ) : Finite (Qn l E n) := by
  have h := (isLocallyConstant_red' l E n).range_finite
  rw [(red_surjective l E n).range_eq] at h
  exact Set.finite_univ_iff.1 h

end Ints

section Kummer

abbrev DecA (A : ValuationSubring (AlgebraicClosure ℚ)) : Type := Lang.Dec (F := ℚ) A

def IneA (A : ValuationSubring (AlgebraicClosure ℚ)) : Subgroup (DecA A) :=
  (Lang.Ine (F := ℚ) A).subgroupOf (Lang.Dec (F := ℚ) A)

instance normal_IneA (A : ValuationSubring (AlgebraicClosure ℚ)) : (IneA A).Normal := Lang.normal_Ine_subgroupOf A

variable (l : ℕ) [Fact l.Prime]

def chi (A : ValuationSubring (AlgebraicClosure ℚ)) : DecA A →* ℤ_[l]ˣ :=
  (Lang.cycZ ℚ (AlgebraicClosure ℚ) l).comp (Lang.Dec (F := ℚ) A).subtype

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

end Kummer

end GlobalTheory.OrdLoc.Dcmp
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.V

namespace GlobalTheory.OrdLoc.Dcmp

open ReciprocityTheory.Gal (H0 H1 H2 Z2 B1 B2 ContAction charRep twDual cup20 TDual)

section Abstract

variable {n : ℕ} [NeZero n] {G : Type} [Group G] [TopologicalSpace G] {R : Type} [CommRing R] [Finite R]
  [Algebra (ZMod n) R] [TopologicalSpace R] [DiscreteTopology R]

variable (n) in

def mulRep (γ : G →* Rˣ) : Representation (ZMod n) G R where
  toFun g := LinearMap.mul (ZMod n) R (γ g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

omit [NeZero n] [TopologicalSpace G] [Finite R] [TopologicalSpace R] [DiscreteTopology R] in
@[simp] theorem mulRep_apply (γ : G →* Rˣ) (g : G) (x : R) : mulRep n γ g x = (γ g : R) * x := rfl

end Abstract

open NumberField IsDedekindDomain in
private lemma span_prime_isMaximal_ratRingOfIntegers {l : ℕ} [hl : Fact l.Prime] :
    (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal := by
  have hZ : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have hc := Ideal.comap_isMaximal_of_surjective (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toRingHom
    (Rat.ringOfIntegersEquiv).surjective (K := Ideal.span {((l : ℕ) : ℤ)})
  have heq : Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toRingHom
      (Ideal.span {((l : ℕ) : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    change Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) _ = _
    rw [← Ideal.map_symm, Ideal.map_span]
    simp
  rwa [heq] at hc

open NumberField IsDedekindDomain in
private lemma asIdeal_eq_span_of_prime_mem {l : ℕ} [Fact l.Prime] {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} :=
  (span_prime_isMaximal_ratRingOfIntegers.eq_of_le w.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 hw)).symm

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.OrdLoc.Dcmp.locDeg_rat {l : ℕ} [Fact l.Prime] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    _root_.ReciprocityTheory.Gal.locDeg v = 1 := by
  have hT : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ ({v} : Finset _) ↔ ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
    intro w
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact hv
    · intro hw
      exact HeightOneSpectrum.ext
        ((asIdeal_eq_span_of_prime_mem hw).trans (asIdeal_eq_span_of_prime_mem hv).symm)
  have h := _root_.ReciprocityTheory.Gal.sum_locDegree (F := ℚ) l {v} hT
  rw [Finset.sum_singleton, Module.finrank_self] at h
  exact h

variable {l : ℕ} [Fact l.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

end GlobalTheory.OrdLoc.Dcmp
end
end
