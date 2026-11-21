import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Section
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

section
noncomputable section

open Ideal IsLocalRing

namespace Reformulated.AutPerF

universe u

theorem isPrecomplete_pi {B : Type*} [CommRing B] (q : B) (ι : Type*)
    [IsPrecomplete (span {q}) B] : IsPrecomplete (span {q}) (ι → B) := by
  have key (n : ℕ) (x : ι → B) : x ∈ (span {q} ^ n • ⊤ : Submodule B (ι → B)) ↔
      ∀ i, x i ∈ (span {q} ^ n • ⊤ : Submodule B B) := by
    simp only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, rfl⟩
    · intro h
      choose y hy using h
      exact ⟨y, funext hy⟩
  refine ⟨fun f hf => ?_⟩
  have h (i : ι) := IsPrecomplete.prec (inferInstance : IsPrecomplete (span {q}) B)
    (f := fun n => f n i) (fun hmn => by
      have := hf hmn
      rw [SModEq.sub_mem, key] at this
      rw [SModEq.sub_mem]
      exact this i)
  choose L hL using h
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  exact SModEq.sub_mem.1 (hL i n)

variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
  [Fact ¬IsUnit (p : A)]

omit [Fact p.Prime] [CharZero A] in
theorem span_p_le_maximalIdeal : span {(p : A)} ≤ maximalIdeal A := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact (Fact.out : ¬IsUnit (p : A))

omit [CharZero A] in
theorem residueField_charP : CharP (ResidueField A) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast (residue A), residue_eq_zero_iff]
    exact (Fact.out : ¬IsUnit (p : A)))

omit [Fact ¬IsUnit (p : A)] in
theorem exists_maximalIdeal_pow_le_span_p : ∃ e : ℕ, maximalIdeal A ^ e ≤ span {(p : A)} := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (show (p : A) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hπ
  refine ⟨e, ?_⟩
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact ⟨u, hu.symm⟩

def modPToResidue : ModP A p →+* ResidueField A :=
  Ideal.Quotient.factor (span_p_le_maximalIdeal p A)

omit [Fact p.Prime] [CharZero A] in
theorem modPToResidue_mk (a : A) : modPToResidue p A (Ideal.Quotient.mk _ a) = residue A a := rfl

omit [Fact p.Prime] [CharZero A] in
theorem modPToResidue_surjective : Function.Surjective (modPToResidue p A) :=
  Ideal.Quotient.factor_surjective _

theorem ker_modPToResidue_le : RingHom.ker (modPToResidue p A) ≤
    RingHom.ker (iterateFrobenius (ModP A p) p (exists_maximalIdeal_pow_le_span_p p A).choose) := by
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, modPToResidue_mk, residue_eq_zero_iff] at hx
  rw [RingHom.mem_ker, iterateFrobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  refine (exists_maximalIdeal_pow_le_span_p p A).choose_spec
    (Ideal.pow_le_pow_right (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le ?_)
  exact Ideal.pow_mem_pow hx _

variable [CharP (ResidueField A) p] [PerfectRing (ResidueField A) p]

def residueSection : ResidueField A →+* ModP A p :=
  (RingHom.liftOfSurjective (modPToResidue p A) (modPToResidue_surjective p A)
    ⟨_, ker_modPToResidue_le p A⟩).comp
    (iterateFrobeniusEquiv (ResidueField A) p
      (exists_maximalIdeal_pow_le_span_p p A).choose).symm.toRingHom

theorem modPToResidue_residueSection (a : ResidueField A) :
    modPToResidue p A (residueSection p A a) = a := by
  obtain ⟨a, rfl⟩ := (iterateFrobeniusEquiv (ResidueField A) p
    (exists_maximalIdeal_pow_le_span_p p A).choose).surjective a
  obtain ⟨b, rfl⟩ := modPToResidue_surjective p A a
  rw [residueSection, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply, RingHom.liftOfSurjective_comp_apply]
  simp [iterateFrobenius_def, iterateFrobeniusEquiv_def]

variable [IsAdicComplete (span {(p : A)}) A]

def wittResidueToRing : WittVector p (ResidueField A) →+* A :=
  (Ainf.theta p A).comp (Ainf.ofWitt p (residueSection p A))

theorem residue_wittResidueToRing (x : WittVector p (ResidueField A)) :
    residue A (wittResidueToRing p A x) = x.coeff 0 := by
  rw [← modPToResidue_mk p, wittResidueToRing, RingHom.comp_apply, Ainf.theta,
    WittVector.mk_fontaineTheta, Ainf.ofWitt, WittVector.map_coeff, Tilt.coeff_ofPerfect]
  exact modPToResidue_residueSection p A _


theorem exists_sum_wittResidueToRing {π : A} (hπ : Irreducible π) (n : ℕ) (a : A) :
    ∃ (c : ℕ → WittVector p (ResidueField A)) (b : A),
      a = ∑ i ∈ Finset.range n, wittResidueToRing p A (c i) * π ^ i + π ^ n * b := by
  induction n with
  | zero => exact ⟨0, a, by simp⟩
  | succ n ih =>
    obtain ⟨c, b, rfl⟩ := ih
    have : b - wittResidueToRing p A (WittVector.teichmuller p (residue A b)) ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, map_sub, residue_wittResidueToRing,
        WittVector.teichmuller_coeff_zero, sub_self]
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    obtain ⟨d, hd⟩ := this
    refine ⟨Function.update c n (WittVector.teichmuller p (residue A b)), d, ?_⟩
    have hs : ∑ i ∈ Finset.range n, wittResidueToRing p A
        (Function.update c n (WittVector.teichmuller p (residue A b)) i) * π ^ i =
        ∑ i ∈ Finset.range n, wittResidueToRing p A (c i) * π ^ i :=
      Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.mem_range.1 hi).ne]
    rw [Finset.sum_range_succ, Function.update_self, hs]
    rw [sub_eq_iff_eq_add] at hd
    conv_lhs => rw [hd]
    ring

theorem wittResidueToRing_finite : (wittResidueToRing p A).Finite := by
  letI := (wittResidueToRing p A).toAlgebra
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_le_span_p p A
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton] at he
  obtain ⟨u, hu⟩ := he
  let f : (Fin e → WittVector p (ResidueField A)) →ₗ[WittVector p (ResidueField A)] A :=
    Fintype.linearCombination _ fun i => π ^ (i : ℕ)
  have hmap : (span {(p : WittVector p (ResidueField A))}).map
      (algebraMap (WittVector p (ResidueField A)) A) = span {(p : A)} := by
    simp [Ideal.map_span]
  haveI : IsHausdorff (span {(p : WittVector p (ResidueField A))}) A := by
    rw [← IsHausdorff.map_algebraMap_iff (S := A), hmap]
    infer_instance
  haveI := isPrecomplete_pi (p : WittVector p (ResidueField A)) (Fin e)
  refine Module.Finite.of_surjective f
    (surjective_of_mkQ_comp_surjective (I := span {(p : WittVector p (ResidueField A))}) ?_)
  intro y
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨c, b, rfl⟩ := exists_sum_wittResidueToRing p A hπ e a
  refine ⟨fun i => c i, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm,
    Submodule.Quotient.eq]
  have : f (fun i => c i) = ∑ i ∈ Finset.range e, wittResidueToRing p A (c i) * π ^ i := by
    rw [Finset.sum_range]
    simp [f, Fintype.linearCombination_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  rw [this, add_sub_cancel_left, hu, mul_assoc]
  have h2 : (p : A) * (u * b) = (p : WittVector p (ResidueField A)) • (u * b) := by
    rw [Algebra.smul_def, map_natCast]
  rw [h2]
  exact Submodule.smul_mem_smul (mem_span_singleton_self _) Submodule.mem_top

end Reformulated.AutPerF
end
end

section
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]

def BcrisPlus.liftFracWitt (g : WittVector p k →+* R) :
    FractionRing (WittVector p k) →+* BcrisPlus p R :=
  fracWittLift p ((algebraMap (Acris p R) (BcrisPlus p R)).comp
    ((algebraMap (Ainf p R) (Acris p R)).comp (Ainf.liftWitt p g))) (BcrisPlus.isUnit_p p R)

variable {p}

@[simp] theorem BcrisPlus.liftFracWitt_algebraMap (g : WittVector p k →+* R) (a : WittVector p k) :
    BcrisPlus.liftFracWitt p g (algebraMap _ _ a) =
      algebraMap (Acris p R) _ (algebraMap (Ainf p R) _ (Ainf.liftWitt p g a)) :=
  fracWittLift_algebraMap p _ _ a

end Reformulated.AutPerF
end
end

section
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

abbrev ResK : Type u := IsLocalRing.ResidueField (unitBall K)

abbrev KZero [CharP (ResK K) p] [PerfectRing (ResK K) p] : Type u :=
  FractionRing (WittVector p (ResK K))

variable [CompleteSpace K] [CharZero K] [Fact (‖(p : K)‖ < 1)]
  [IsDiscreteValuationRing (unitBall K)] [CharP (ResK K) p] [PerfectRing (ResK K) p]

def wittToInteger : WittVector p (ResK K) →+* unitBall K := wittResidueToRing p (unitBall K)

instance : Algebra (KZero p K) K :=
  (fracWittLift p ((unitBall K).subtype.comp (wittToInteger p K))
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))).toAlgebra

theorem KZero.algebraMap_algebraMap (a : WittVector p (ResK K)) :
    algebraMap (KZero p K) K (algebraMap _ _ a) = wittToInteger p K a :=
  fracWittLift_algebraMap p _ _ a

instance : Module.Finite (KZero p K) K := by
  classical
  letI := (wittToInteger p K).toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Submodule (WittVector p (ResK K)) (unitBall K)).FG :=
    Module.Finite.fg_top (self := wittResidueToRing_finite p (unitBall K))
  refine ⟨⟨s.image (fun x : unitBall K => (x : K)), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  have key (a : unitBall K) : (a : K) ∈ Submodule.span (KZero p K)
      (↑(s.image (fun x : unitBall K => (x : K))) : Set K) := by
    have ha : a ∈ Submodule.span (WittVector p (ResK K)) (s : Set (unitBall K)) := by
      rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by simpa using hy)
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      have : ((c • y : unitBall K) : K) = (algebraMap _ (KZero p K) c) • (y : K) := by
        rw [Algebra.smul_def, Algebra.smul_def, KZero.algebraMap_algebraMap]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ hy
  obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (p : unitBall K)) x
  simp only [map_pow, map_natCast] at h
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have : x = ((p : KZero p K) ^ n)⁻¹ • (a : K) := by
    rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hp),
      mul_comm]
    exact h
  rw [this]
  exact Submodule.smul_mem _ _ (key a)

instance : Algebra (KZero p K) (AlgCl K) :=
  ((algebraMap K (AlgCl K)).comp (algebraMap (KZero p K) K)).toAlgebra

instance : IsScalarTower (KZero p K) K (AlgCl K) := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : Algebra.IsAlgebraic (KZero p K) (AlgCl K) := Algebra.IsAlgebraic.trans _ K _

def wittToOCK : WittVector p (ResK K) →+* OCK K := (OCK.ofInteger K).comp (wittToInteger p K)



def kZeroToBcrisPlus : KZero p K →+* BcrisPlus p (OCK K) :=
  BcrisPlus.liftFracWitt p (wittToOCK p K)

def kZeroToBcris : KZero p K →+* Bcris p (OCK K) :=
  (algebraMap (BcrisPlus p (OCK K)) _).comp (kZeroToBcrisPlus p K)

def kZeroToBst : KZero p K →+* Bst p (OCK K) :=
  (algebraMap (Bcris p (OCK K)) _).comp (kZeroToBcris p K)



theorem algebraMap_wittVector_eq (a : WittVector p (ResK K)) :
    algebraMap (AlgCl K) (CK K) (algebraMap (KZero p K) (AlgCl K) (algebraMap _ _ a)) =
      wittToOCK p K a := by
  rw [IsScalarTower.algebraMap_apply (KZero p K) K (AlgCl K), KZero.algebraMap_algebraMap]
  rfl

def algClToBdRPlus : AlgCl K →+* BdRPlus p (OCK K) :=
  BdRPlus.wittSection (wittToOCK p K) (algebraMap (AlgCl K) (CK K)) (algebraMap_wittVector_eq p K)

@[simp] theorem thetaC_algClToBdRPlus (x : AlgCl K) :
    BdRPlus.thetaC p (OCK K) (algClToBdRPlus p K x) = (x : CK K) :=
  BdRPlus.thetaC_wittSection _ _ _ x



end Reformulated.AutPerF
end
end
