import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

section
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

theorem mem_span_of_approx {A : Type*} [CommRing A] (q ξ : A) [IsAdicComplete (span {q}) A]
    (K : Set A) (h : ∀ x ∈ K, ∃ a, ∃ y ∈ K, x = ξ * a + q * y) {x : A} (hx : x ∈ K) :
    x ∈ span {ξ} := by
  choose! a s hs hxs using h
  have hK : ∀ n, s^[n] x ∈ K := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hs _ ih
  let b : ℕ → A := fun n => ∑ i ∈ Finset.range n, q ^ i * a (s^[i] x)
  have hb : ∀ n, x = ξ * b n + q ^ n * s^[n] x := by
    intro n
    induction n with
    | zero => simp [b]
    | succ n ih =>
      have h1 := hxs _ (hK n)
      simp only [b] at ih ⊢
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      linear_combination ih + q ^ n * h1
  have hmem : ∀ (n : ℕ) (z : A), z ∈ (span {q} ^ n • ⊤ : Ideal A) ↔ q ^ n ∣ z := by
    intro n z
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {q}) (M := A) inferInstance (f := b) (by
    intro m n hle
    rw [SModEq.sub_mem, hmem]
    induction n, hle using Nat.le_induction with
    | base => simp
    | succ n hle ih =>
      simp only [b] at ih ⊢
      rw [Finset.sum_range_succ, ← sub_sub]
      exact dvd_sub ih ((pow_dvd_pow q hle).mul_right _))
  have : x - ξ * L = 0 := by
    refine IsHausdorff.haus (I := span {q}) (M := A) inferInstance _ fun n => ?_
    have h1 := hL n
    rw [SModEq.sub_mem, hmem] at h1 ⊢
    have : x - ξ * L - 0 = ξ * (b n - L) + q ^ n * s^[n] x := by linear_combination hb n
    rw [this]
    exact dvd_add (h1.mul_left _) (dvd_mul_right _ _)
  rw [sub_eq_zero.1 this]
  exact Ideal.mul_mem_right _ _ (mem_span_singleton_self _)

theorem eq_zero_of_forall_pow_dvd {A : Type*} [CommRing A] (q : A) [IsHausdorff (span {q}) A]
    {x : A} (h : ∀ n : ℕ, q ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (I := span {q}) (M := A) inferInstance _ fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  exact h n

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

theorem exists_pow_eq_of_isAlgClosed {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsAlgClosed (FractionRing R)] (a : R) {n : ℕ} (hn : 0 < n) : ∃ b : R, b ^ n = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R (FractionRing R) a) hn
  have hi : IsIntegral R z := IsIntegral.of_pow hn (hz ▸ isIntegral_algebraMap)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨b, IsFractionRing.injective R (FractionRing R) (by rw [map_pow, hz])⟩

namespace Tilt

variable (p R) in

def sharpEquiv : Tilt p R ≃* Perfection R p :=
  (Perfection.quotientMulEquiv p (span {(p : R)})).symm

theorem coeff_zero_sharpEquiv (x : Tilt p R) :
    Perfection.coeffMonoidHom R p 0 (sharpEquiv p R x) = PreTilt.untilt x :=
  Perfection.coeff_zero_symm_quotientMulEquiv x

theorem untilt_sharpEquiv_symm (y : Perfection R p) :
    PreTilt.untilt ((sharpEquiv p R).symm y) = Perfection.coeffMonoidHom R p 0 y := by
  rw [← coeff_zero_sharpEquiv, MulEquiv.apply_symm_apply]

theorem coeff_sharpEquiv_pow (x : Tilt p R) (n : ℕ) :
    Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ^ p ^ n = PreTilt.untilt x := by
  rw [Perfection.coeffMonoidHom_pow_p_pow_self, coeff_zero_sharpEquiv]

@[simp] theorem untilt_zero : PreTilt.untilt (0 : Tilt p R) = 0 := Perfection.teichmuller_zero

theorem isUnit_iff_isUnit_coeff [IsLocalRing R] (a : R) :
    IsUnit (Ideal.Quotient.mk (span {(p : R)}) a) ↔ IsUnit a := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), eq_comm, Ideal.Quotient.eq,
    mem_span_singleton] at hb
  obtain ⟨c, hc⟩ := hb
  by_contra ha
  have h1 : a * b ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ ha
  have h2 : (p : R) * c ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right _ _ (Fact.out : ¬IsUnit (p : R))
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [show (1 : R) = a * b + p * c by linear_combination hc]; exact add_mem h1 h2
  exact this isUnit_one

variable [IsDomain R]

theorem untilt_eq_zero_iff (x : Tilt p R) : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ untilt_zero⟩
  apply (sharpEquiv p R).injective
  refine Perfection.extMonoid fun n => ?_
  have h1 := coeff_sharpEquiv_pow x n
  have h2 := coeff_sharpEquiv_pow (0 : Tilt p R) n
  rw [h] at h1
  rw [untilt_zero] at h2
  rw [pow_eq_zero_iff (pow_pos (Fact.out : p.Prime).pos n).ne'] at h1 h2
  rw [h1, h2]

instance isDomain : IsDomain (Tilt p R) := by
  have : Nontrivial (Tilt p R) :=
    ⟨(CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one).1⟩
  have : NoZeroDivisors (Tilt p R) := ⟨fun {a b} h => by
    rw [← untilt_eq_zero_iff, map_mul, mul_eq_zero, untilt_eq_zero_iff, untilt_eq_zero_iff] at h
    exact h⟩
  exact NoZeroDivisors.to_isDomain _

theorem dvd_iff_untilt_dvd [IsIntegrallyClosed R] (x y : Tilt p R) :
    x ∣ y ↔ PreTilt.untilt x ∣ PreTilt.untilt y := by
  refine ⟨fun h => map_dvd _ h, fun h => ?_⟩
  by_cases hx : x = 0
  · subst hx
    rw [untilt_zero, zero_dvd_iff, untilt_eq_zero_iff] at h
    rw [h]
  have hp := (Fact.out : p.Prime).pos
  have hne : ∀ n, Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ≠ 0 := by
    intro n hn
    have h1 := coeff_sharpEquiv_pow x n
    rw [hn, zero_pow (pow_pos hp n).ne', eq_comm, untilt_eq_zero_iff] at h1
    exact hx h1
  have hd : ∀ n, Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ∣
      Perfection.coeffMonoidHom R p n (sharpEquiv p R y) := by
    intro n
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (pow_pos hp n).ne', coeff_sharpEquiv_pow,
      coeff_sharpEquiv_pow]
    exact h
  choose c hc using hd
  have hcp : ∀ n, c (n + 1) ^ p = c n := by
    intro n
    apply mul_left_cancel₀ (hne n)
    rw [← hc, ← Perfection.coeffMonoidHom_pow_p' (sharpEquiv p R x) n, ← mul_pow, ← hc,
      Perfection.coeffMonoidHom_pow_p']
  obtain ⟨z, hz⟩ : ∃ z : Perfection R p, ∀ n, Perfection.coeffMonoidHom R p n z = c n :=
    ⟨⟨c, hcp⟩, fun _ => rfl⟩
  refine ⟨(sharpEquiv p R).symm z, (sharpEquiv p R).injective ?_⟩
  rw [map_mul, MulEquiv.apply_symm_apply]
  refine Perfection.extMonoid fun n => ?_
  rw [map_mul, hc, hz]

variable [ValuationRing R]

instance valuationRing : ValuationRing (Tilt p R) :=
  { cond' := fun a b => by
      rcases ValuationRing.dvd_total (PreTilt.untilt a) (PreTilt.untilt b) with h | h
      · obtain ⟨c, hc⟩ := (dvd_iff_untilt_dvd a b).2 h
        exact ⟨c, Or.inl hc.symm⟩
      · obtain ⟨c, hc⟩ := (dvd_iff_untilt_dvd b a).2 h
        exact ⟨c, Or.inr hc.symm⟩ }

theorem isUnit_iff_isUnit_untilt (x : Tilt p R) : IsUnit x ↔ IsUnit (PreTilt.untilt x) := by
  rw [isUnit_iff_dvd_one, isUnit_iff_dvd_one, dvd_iff_untilt_dvd, map_one]

theorem isUnit_iff_isUnit_coeff_zero (x : Tilt p R) : IsUnit x ↔ IsUnit (PreTilt.coeff 0 x) := by
  rw [isUnit_iff_isUnit_untilt, ← PreTilt.mk_untilt_eq_coeff_zero, isUnit_iff_isUnit_coeff]

theorem untilt_surjective [IsAlgClosed (FractionRing R)] :
    Function.Surjective (PreTilt.untilt : Tilt p R → R) := by
  intro a
  choose r hr using fun b : R => exists_pow_eq_of_isAlgClosed b (Fact.out : p.Prime).pos
  refine ⟨(sharpEquiv p R).symm ⟨fun n => r^[n] a, fun n => ?_⟩, ?_⟩
  · beta_reduce
    rw [Function.iterate_succ_apply', hr]
  · exact (untilt_sharpEquiv_symm _).trans rfl

end Tilt

instance PFlat.nonempty_of_isAlgClosed [IsDomain R] [ValuationRing R]
    [IsAlgClosed (FractionRing R)] : Nonempty (PFlat p R) :=
  let ⟨x, hx⟩ := Tilt.untilt_surjective (p := p) (p : R)
  ⟨⟨x, hx⟩⟩

namespace Ainf

def xi (ϖ : PFlat p R) : Ainf p R := (p : Ainf p R) - teich p ϖ.1

@[simp] theorem theta_xi (ϖ : PFlat p R) : theta p R (xi ϖ) = 0 := by
  simp [xi, ϖ.2]

omit [IsAdicComplete (span {(p : R)}) R] in
theorem p_dvd_iff (x : Ainf p R) : (p : Ainf p R) ∣ x ↔ x.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
  rfl

omit [IsAdicComplete (span {(p : R)}) R] in
theorem p_dvd_sub_teich (x : Ainf p R) : (p : Ainf p R) ∣ x - teich p (x.coeff 0) := by
  rw [p_dvd_iff]
  change WittVector.constantCoeff (x - teich p (x.coeff 0)) = 0
  rw [map_sub]
  simp

theorem coeff_zero_xi (ϖ : PFlat p R) : (xi ϖ).coeff 0 = -ϖ.1 := by
  change WittVector.constantCoeff (xi ϖ) = _
  rw [xi, map_sub, map_natCast]
  simp

omit [IsAdicComplete (span {(p : R)}) R] in

theorem isUnit_iff_isUnit_coeff (x : Ainf p R) : IsUnit x ↔ IsUnit (x.coeff 0) := by
  refine ⟨fun h => h.map WittVector.constantCoeff, fun h => ?_⟩
  obtain ⟨c, hc⟩ := p_dvd_sub_teich x
  obtain ⟨t, ht⟩ := h.map (teich p)
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : Ainf p R)})
    (mem_span_singleton_self (p : Ainf p R))
  have := Ideal.mem_jacobson_bot.1 hj (c * ↑t⁻¹)
  have e : x = ((p : Ainf p R) * (c * ↑t⁻¹) + 1) * t := by
    rw [add_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, one_mul, ← hc, ht, sub_add_cancel]
  rw [e]
  exact this.mul t.isUnit

theorem mk_theta (x : Ainf p R) : Ideal.Quotient.mk (span {(p : R)}) (theta p R x) =
    Ideal.Quotient.mk _ (PreTilt.untilt (x.coeff 0)) := by
  rw [PreTilt.mk_untilt_eq_coeff_zero]; exact WittVector.mk_fontaineTheta x

variable [IsDomain R]

instance isDomain : IsDomain (Ainf p R) := inferInstanceAs (IsDomain (WittVector p (Tilt p R)))

instance charZero_of_charZero [CharZero R] : CharZero (Ainf p R) := (theta p R).charZero

theorem p_ne_zero : (p : Ainf p R) ≠ 0 := WittVector.p_nonzero p _

theorem xi_ne_zero [CharZero R] (ϖ : PFlat p R) : xi ϖ ≠ 0 := by
  intro h
  have h1 := coeff_zero_xi ϖ
  rw [h, WittVector.zero_coeff, eq_comm, neg_eq_zero] at h1
  have h2 := ϖ.2
  rw [h1, Tilt.untilt_zero, eq_comm, Nat.cast_eq_zero] at h2
  exact (Fact.out : p.Prime).ne_zero h2

variable [ValuationRing R]


theorem theta_surjective [IsAlgClosed (FractionRing R)] : Function.Surjective (theta p R) := by
  intro a
  obtain ⟨x, hx⟩ := Tilt.untilt_surjective (p := p) a
  exact ⟨teich p x, by rw [theta_teich, hx]⟩

theorem exists_eq_xi_mul_add (ϖ : PFlat p R) {x : Ainf p R} (hx : (p : R) ∣ theta p R x) :
    ∃ a y, x = xi ϖ * a + p * y := by
  rw [← mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, mk_theta,
    Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := (Tilt.dvd_iff_untilt_dvd ϖ.1 (x.coeff 0)).2 (by rw [ϖ.2]; exact hx)
  obtain ⟨d, hd⟩ := p_dvd_sub_teich x
  rw [hc, map_mul] at hd
  exact ⟨-teich p c, d + teich p c, by rw [xi]; linear_combination hd⟩

variable [CharZero R]

theorem ker_theta (ϖ : PFlat p R) : RingHom.ker (theta p R) = span {xi ϖ} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · refine mem_span_of_approx (p : Ainf p R) (xi ϖ) (RingHom.ker (theta p R)) ?_ hx
    intro x hx
    have hx' : theta p R x = 0 := hx
    obtain ⟨a, y, h⟩ := exists_eq_xi_mul_add ϖ (x := x) (by rw [hx']; exact dvd_zero _)
    refine ⟨a, y, ?_, h⟩
    rw [h] at hx'
    simpa [(Fact.out : p.Prime).ne_zero] using hx'
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact theta_xi ϖ

theorem theta_eq_zero_iff (ϖ : PFlat p R) (x : Ainf p R) : theta p R x = 0 ↔ xi ϖ ∣ x := by
  rw [← mem_span_singleton, ← ker_theta, RingHom.mem_ker]

theorem xi_dvd_of_dvd_p_pow_mul (ϖ : PFlat p R) {x : Ainf p R} {k : ℕ}
    (h : xi ϖ ∣ (p : Ainf p R) ^ k * x) : xi ϖ ∣ x := by
  rw [← theta_eq_zero_iff] at h ⊢
  simpa [(Fact.out : p.Prime).ne_zero] using h

theorem xi_pow_dvd_of_dvd_p_pow_mul (ϖ : PFlat p R) {n k : ℕ} {x : Ainf p R}
    (h : xi ϖ ^ n ∣ (p : Ainf p R) ^ k * x) : xi ϖ ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, rfl⟩ := xi_dvd_of_dvd_p_pow_mul ϖ ((dvd_pow_self _ n.succ_ne_zero).trans h)
    rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left (xi_ne_zero ϖ)] at h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h)

theorem xi_pow_dvd_of_forall (ϖ : PFlat p R) {n : ℕ} {x : Ainf p R}
    (h : ∀ k : ℕ, ∃ a b, x = (p : Ainf p R) ^ k * a + xi ϖ ^ n * b) : xi ϖ ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have h0 : theta p R x = 0 := eq_zero_of_forall_pow_dvd (p : R) fun k => by
      obtain ⟨a, b, e⟩ := h k
      exact ⟨theta p R a, by rw [e]; simp⟩
    obtain ⟨y, rfl⟩ := (theta_eq_zero_iff ϖ x).1 h0
    rw [pow_succ']
    refine mul_dvd_mul_left _ (ih fun k => ?_)
    obtain ⟨a, b, e⟩ := h k
    obtain ⟨a', rfl⟩ : xi ϖ ∣ a := xi_dvd_of_dvd_p_pow_mul ϖ (k := k)
      ⟨y - xi ϖ ^ n * b, by linear_combination -e⟩
    exact ⟨a', b, mul_left_cancel₀ (xi_ne_zero ϖ) (by linear_combination e)⟩


theorem eq_zero_of_forall_xi_pow_dvd (ϖ : PFlat p R) {x : Ainf p R}
    (h : ∀ n : ℕ, xi ϖ ^ n ∣ x) : x = 0 := by
  refine eq_zero_of_forall_pow_dvd (p : Ainf p R) fun k => ?_
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h0 : PreTilt.untilt (x.coeff 0) = 0 := eq_zero_of_forall_pow_dvd (p : R) fun n => by
      have h1 : (xi ϖ).coeff 0 ^ n ∣ x.coeff 0 := by
        have := map_dvd (WittVector.constantCoeff (p := p) (R := Tilt p R)) (h n)
        rwa [map_pow] at this
      rw [coeff_zero_xi] at h1
      have h2 : ϖ.1 ^ n ∣ x.coeff 0 := (pow_dvd_pow_of_dvd (dvd_neg.2 dvd_rfl) n).trans h1
      have h3 := map_dvd PreTilt.untilt h2
      rwa [map_pow, ϖ.2] at h3
    obtain ⟨y, rfl⟩ := (p_dvd_iff x).2 ((Tilt.untilt_eq_zero_iff _).1 h0)
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih fun n =>
      xi_pow_dvd_of_dvd_p_pow_mul ϖ (k := 1) (by simpa using h n))


end Ainf

def tateRoot (η : tateModule p R) : Tilt p R := (frobeniusEquiv (Tilt p R) p).symm η.1

theorem tateRoot_pow (η : tateModule p R) : tateRoot η ^ p = η.1 :=
  frobeniusEquiv_symm_pow_p (Tilt p R) p η.1

namespace Ainf

def omega (ε : tateModule p R) : Ainf p R := ∑ i ∈ Finset.range p, teich p (tateRoot ε) ^ i

theorem omega_mul (ε : tateModule p R) :
    omega ε * (teich p (tateRoot ε) - 1) = teich p ε.1 - 1 := by
  rw [omega, geom_sum_mul, ← map_pow, tateRoot_pow]

variable [IsDomain R]

theorem theta_omega {ε : tateModule p R} (hε : IsPrimitive ε) : theta p R (omega ε) = 0 := by
  have h := congrArg (theta p R) (omega_mul ε)
  rw [map_mul, map_sub, map_sub, map_one, theta_teich, theta_teich,
    show PreTilt.untilt ε.1 = 1 from ε.2, sub_self, mul_eq_zero] at h
  exact h.resolve_right (sub_ne_zero.2 hε)

variable [ValuationRing R] [CharZero R]

theorem associated_xi_omega (ϖ : PFlat p R) {ε : tateModule p R} (hε : IsPrimitive ε) :
    Associated (xi ϖ) (omega ε) := by
  obtain ⟨a, ha⟩ := (theta_eq_zero_iff ϖ _).1 (theta_omega hε)
  let ρ := IsLocalRing.residue (Tilt p R)
  have hc : CharP (IsLocalRing.ResidueField (Tilt p R)) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast ρ, CharP.cast_eq_zero, map_zero])
  have h1 : ρ ϖ.1 = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Tilt.isUnit_iff_isUnit_untilt, ϖ.2]
    exact Fact.out
  have h2 : ρ (tateRoot ε) = 1 := by
    rw [← sub_eq_zero, ← map_one ρ, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h3 := hu.pow p
    rw [sub_pow_char, tateRoot_pow, one_pow, Tilt.isUnit_iff_isUnit_coeff_zero, map_sub,
      ← PreTilt.mk_untilt_eq_coeff_zero, show PreTilt.untilt ε.1 = 1 from ε.2, map_one, map_one,
      sub_self, ← map_zero (Ideal.Quotient.mk (span {(p : R)})),
      Tilt.isUnit_iff_isUnit_coeff] at h3
    exact not_isUnit_zero h3
  have h4 := congrArg (WittVector.map (p := p) ρ) ha
  simp only [omega, xi, map_sum, map_pow, map_mul, map_sub, map_natCast,
    WittVector.map_teichmuller, h1, h2, map_one, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, WittVector.teichmuller_zero, sub_zero] at h4
  have h5 : WittVector.map (p := p) ρ a = 1 :=
    mul_left_cancel₀ (WittVector.p_nonzero p _) (h4.symm.trans (mul_one _).symm)
  have h6 : ρ (a.coeff 0) = 1 := by
    rw [← WittVector.map_coeff, h5, WittVector.one_coeff_zero]
  have hu : IsUnit a := by
    rw [isUnit_iff_isUnit_coeff, ← IsLocalRing.residue_ne_zero_iff_isUnit]
    exact h6 ▸ one_ne_zero
  exact ⟨hu.unit, ha.symm⟩

theorem exists_teich_sub_one_eq (ϖ : PFlat p R) {ε : tateModule p R} (hε : IsPrimitive ε) :
    ∃ b, teich p ε.1 - 1 = xi ϖ * b ∧ theta p R b ≠ 0 := by
  obtain ⟨u, hu⟩ := associated_xi_omega ϖ hε
  refine ⟨u * (teich p (tateRoot ε) - 1), by rw [← mul_assoc, hu, omega_mul], ?_⟩
  rw [map_mul, map_sub, map_one, theta_teich]
  exact mul_ne_zero (u.isUnit.map _).ne_zero (sub_ne_zero.2 hε)


end Ainf

namespace AinfInv

omit [IsAdicComplete (span {(p : R)}) R] in
theorem exists_p_pow_mul_eq (x : AinfInv p R) :
    ∃ (k : ℕ) (a : Ainf p R), (p : AinfInv p R) ^ k * x = algebraMap _ _ a := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (p : Ainf p R) x
  exact ⟨k, a, by rw [← h, map_natCast, mul_comm]⟩

variable [IsDomain R]

theorem algebraMap_injective : Function.Injective (algebraMap (Ainf p R) (AinfInv p R)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors Ainf.p_ne_zero)

instance isDomain : IsDomain (AinfInv p R) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Ainf.p_ne_zero (p := p) (R := R)))

variable [ValuationRing R]

theorem theta_surjective [IsAlgClosed (FractionRing R)] : Function.Surjective (theta p R) := by
  intro y
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (p : R) y
  obtain ⟨b, rfl⟩ := Ainf.theta_surjective (p := p) a
  obtain ⟨u, hu⟩ := isUnit_p (R := R) p
  refine ⟨algebraMap _ _ b * ↑(u⁻¹ ^ k), ?_⟩
  rw [map_mul, theta_algebraMap, ← h, map_natCast, mul_assoc, ← map_natCast (theta p R), ← map_pow,
    ← map_mul, ← hu]
  simp [← mul_pow]

variable [CharZero R]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] [ValuationRing R] in
theorem algebraMap_away_injective :
    Function.Injective (algebraMap R (Localization.Away (p : R))) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors
    (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))

theorem kerTheta_eq (ϖ : PFlat p R) :
    kerTheta p R = span {algebraMap (Ainf p R) (AinfInv p R) (Ainf.xi ϖ)} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨k, a, h⟩ := exists_p_pow_mul_eq x
    have h1 : theta p R (algebraMap _ _ a) = 0 := by
      rw [← h, map_mul, show theta p R x = 0 from hx, mul_zero]
    rw [theta_algebraMap, map_eq_zero_iff _ algebraMap_away_injective,
      Ainf.theta_eq_zero_iff ϖ] at h1
    rw [mem_span_singleton, ← ((isUnit_p (R := R) p).pow k).dvd_mul_left, h]
    exact map_dvd _ h1
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp [RingHom.mem_ker]

theorem algebraMap_mem_kerTheta_pow_iff (ϖ : PFlat p R) (n : ℕ) (x : Ainf p R) :
    algebraMap (Ainf p R) (AinfInv p R) x ∈ kerTheta p R ^ n ↔ Ainf.xi ϖ ^ n ∣ x := by
  rw [kerTheta_eq ϖ, Ideal.span_singleton_pow, mem_span_singleton, ← map_pow]
  refine ⟨fun ⟨y, hy⟩ => ?_, fun h => map_dvd _ h⟩
  obtain ⟨k, a, h⟩ := exists_p_pow_mul_eq y
  refine Ainf.xi_pow_dvd_of_dvd_p_pow_mul ϖ (k := k) ⟨a, algebraMap_injective ?_⟩
  rw [map_mul, map_mul, hy, ← h, map_pow (algebraMap (Ainf p R) (AinfInv p R)) (p : Ainf p R),
    map_natCast]
  ring


theorem eq_zero_of_forall_mem_kerTheta_pow (ϖ : PFlat p R) {x : AinfInv p R}
    (h : ∀ n : ℕ, x ∈ kerTheta p R ^ n) : x = 0 := by
  obtain ⟨k, a, e⟩ := exists_p_pow_mul_eq x
  have : a = 0 := Ainf.eq_zero_of_forall_xi_pow_dvd ϖ fun n =>
    (algebraMap_mem_kerTheta_pow_iff ϖ n a).1 (e ▸ Ideal.mul_mem_left _ _ (h n))
  rw [this, map_zero] at e
  exact (((isUnit_p (R := R) p).pow k).mul_right_eq_zero).1 e

theorem kerTheta_fg [IsAlgClosed (FractionRing R)] : (kerTheta p R).FG := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [kerTheta_eq ϖ]
  exact Submodule.fg_span_singleton _

end AinfInv

end Reformulated.AutPerF
end
end

section
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

section Adic

variable {A : Type u} [CommRing A]

theorem evalₐ_eq_zero_iff_dvd_of_eq_span {I : Ideal A} {a : A} (hI : I = span {a}) (n : ℕ)
    (x : AdicCompletion I A) :
    AdicCompletion.evalₐ I n x = 0 ↔ algebraMap A (AdicCompletion I A) a ^ n ∣ x := by
  have hfg : I.FG := hI ▸ Submodule.fg_span_singleton a
  have h1 : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0 := by
    constructor
    · intro h
      rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), h, map_zero]
    · intro h
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), h, map_zero]
  rw [h1, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hfg]
  have h2 : I ^ n = span {a ^ n} := by rw [hI, Ideal.span_singleton_pow]
  rw [h2, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem eq_zero_of_algebraMap_mul_eq_zero [IsDomain A] {I : Ideal A} {a : A} (hI : I = span {a})
    (ha : a ≠ 0) {x : AdicCompletion I A} (h : algebraMap A (AdicCompletion I A) a * x = 0) :
    x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ I (n + 1)) h
  rw [map_mul, AlgHom.commutes, ← hy, map_zero, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : ∀ m, I ^ m = span {a ^ m} := fun m => by rw [hI, Ideal.span_singleton_pow]
  rw [h2, mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h1
  rw [← factorPow_evalₐ I n.le_succ, ← hy, map_zero]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [h2, mem_span_singleton]
  exact h1

end Adic

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]

omit [Fact ¬IsUnit (p : R)] [CharZero R] [Fact p.Prime] in
theorem exists_dvd_p_pow {x : R} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (p : R) ^ n := by
  by_contra h
  push Not at h
  exact hx (eq_zero_of_forall_pow_dvd (p : R) fun n =>
    (ValuationRing.dvd_total x _).resolve_left (h n))

instance isFractionRing_away : IsFractionRing R (Localization.Away (p : R)) :=
  IsLocalization.isLocalization_of_is_exists_mul_mem _ (Submonoid.powers (p : R)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    (fun ⟨x, hx⟩ => by
      obtain ⟨n, c, hc⟩ := exists_dvd_p_pow (p := p) (nonZeroDivisors.ne_zero hx)
      exact ⟨c, n, by simp [hc, mul_comm]⟩)

variable (p R) in
omit [Fact ¬IsUnit (p : R)] in
theorem isField_away : IsField (Localization.Away (p : R)) :=
  (IsFractionRing.toField R (K := Localization.Away (p : R))).toIsField

namespace BdRPlus

omit [IsDomain R] [ValuationRing R] [CharZero R] in

def xi (ϖ : PFlat p R) : BdRPlus p R := algebraMap (Ainf p R) _ (Ainf.xi ϖ)

omit [IsDomain R] [ValuationRing R] [CharZero R] in
@[simp] theorem theta_algebraMap_ainf (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Ainf.theta p R x) :=
  AinfInv.theta_algebraMap x

theorem eval_eq_zero_iff (ϖ : PFlat p R) (n : ℕ) (x : BdRPlus p R) :
    eval p R n x = 0 ↔ xi ϖ ^ n ∣ x :=
  evalₐ_eq_zero_iff_dvd_of_eq_span (AinfInv.kerTheta_eq ϖ) n x

theorem theta_eq_zero_iff_dvd (ϖ : PFlat p R) (x : BdRPlus p R) :
    theta p R x = 0 ↔ xi ϖ ∣ x := by
  rw [← pow_one (xi ϖ), ← eval_eq_zero_iff, theta_eq_zero_iff]
  refine Iff.trans (Eq.congr_left (AdicCompletion.factorₐ_evalₐ_one _ _).symm)
    (map_eq_zero_iff _ ?_)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hy

theorem ker_theta (ϖ : PFlat p R) : RingHom.ker (theta p R) = span {xi ϖ} := by
  ext x
  rw [RingHom.mem_ker, theta_eq_zero_iff_dvd ϖ, mem_span_singleton]

theorem fil_eq_span (ϖ : PFlat p R) (n : ℕ) : fil p R n = span {xi ϖ ^ n} := by
  rw [fil, ker_theta ϖ, Ideal.span_singleton_pow]

theorem eq_zero_of_xi_mul_eq_zero (ϖ : PFlat p R) {x : BdRPlus p R} (h : xi ϖ * x = 0) : x = 0 :=
  eq_zero_of_algebraMap_mul_eq_zero (AinfInv.kerTheta_eq ϖ)
    ((map_ne_zero_iff _ AinfInv.algebraMap_injective).2 (Ainf.xi_ne_zero ϖ)) h

theorem eq_zero_of_forall_xi_pow_dvd (ϖ : PFlat p R) {x : BdRPlus p R}
    (h : ∀ n : ℕ, xi ϖ ^ n ∣ x) : x = 0 :=
  ext_eval fun n => by rw [map_zero, eval_eq_zero_iff ϖ]; exact h n

variable [IsAlgClosed (FractionRing R)]

theorem ker_eval (n : ℕ) : RingHom.ker (eval p R n) = fil p R n := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  ext x
  rw [RingHom.mem_ker, eval_eq_zero_iff ϖ, fil_eq_span ϖ, mem_span_singleton]

theorem ker_theta_eq_map : RingHom.ker (theta p R) =
    (AinfInv.kerTheta p R).map (algebraMap (AinfInv p R) (BdRPlus p R)) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := congrArg (Ideal.map (algebraMap (AinfInv p R) (BdRPlus p R))) (AinfInv.kerTheta_eq ϖ)
  rw [ker_theta ϖ, h, Ideal.map_span, Set.image_singleton]
  rfl

instance isAdicComplete_ker_theta : IsAdicComplete (RingHom.ker (theta p R)) (BdRPlus p R) := by
  rw [ker_theta_eq_map]
  exact AdicCompletion.isAdicComplete_self _ AinfInv.kerTheta_fg

instance isAdicComplete_fil_one : IsAdicComplete (fil p R 1) (BdRPlus p R) := by
  rw [fil, pow_one]
  infer_instance

omit [CharZero R] in

theorem theta_surjective : Function.Surjective (theta p R) := fun y =>
  let ⟨x, hx⟩ := AinfInv.theta_surjective (p := p) y
  ⟨algebraMap _ _ x, hx⟩

theorem isUnit_iff_theta_ne_zero (x : BdRPlus p R) : IsUnit x ↔ theta p R x ≠ 0 := by
  have := (isField_away p R).nontrivial
  refine ⟨fun h => (h.map _).ne_zero, fun h => ?_⟩
  obtain ⟨z, hz⟩ := (isField_away p R).mul_inv_cancel h
  obtain ⟨y, rfl⟩ := theta_surjective (p := p) z
  have h1 : x * y - 1 ∈ RingHom.ker (theta p R) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hz, map_one, sub_self]
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem exists_associated_xi_pow (ϖ : PFlat p R) {x : BdRPlus p R} (hx : x ≠ 0) :
    ∃ n : ℕ, Associated (xi ϖ ^ n) x := by
  classical
  have h : ∃ n : ℕ, ¬xi ϖ ^ (n + 1) ∣ x := by
    by_contra h
    push Not at h
    exact hx (eq_zero_of_forall_xi_pow_dvd ϖ fun n => (pow_dvd_pow _ n.le_succ).trans (h n))
  obtain ⟨u, hu⟩ : xi ϖ ^ Nat.find h ∣ x := by
    rcases e : Nat.find h with _ | m
    · simp
    · exact not_not.1 (Nat.find_min h (by omega))
  have hu' : IsUnit u := by
    rw [isUnit_iff_theta_ne_zero, Ne, theta_eq_zero_iff_dvd ϖ]
    intro hd
    apply Nat.find_spec h
    obtain ⟨v, rfl⟩ := hd
    exact ⟨v, hu.trans (by ring)⟩
  exact ⟨_, hu'.unit, hu.symm⟩

instance nontrivial : Nontrivial (BdRPlus p R) :=
  have := (isField_away p R).nontrivial
  (theta p R).domain_nontrivial

instance isDomain : IsDomain (BdRPlus p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have key : ∀ (n : ℕ) (y : BdRPlus p R), xi ϖ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y hy
      exact ih y (eq_zero_of_xi_mul_eq_zero ϖ (by rw [← mul_assoc, ← pow_succ', hy]))
  have : NoZeroDivisors (BdRPlus p R) := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    obtain ⟨n, u, rfl⟩ := exists_associated_xi_pow ϖ ha
    exact Or.inr ((Units.mul_right_eq_zero u).1 (key n _ (by rw [← mul_assoc, h])))⟩
  exact NoZeroDivisors.to_isDomain _

theorem xi_ne_zero (ϖ : PFlat p R) : xi ϖ ≠ 0 := fun h =>
  one_ne_zero (eq_zero_of_xi_mul_eq_zero ϖ (x := 1) (by rw [h, zero_mul]))

theorem prime_xi (ϖ : PFlat p R) : Prime (xi ϖ) := by
  have := (isField_away p R).isDomain
  rw [← Ideal.span_singleton_prime (xi_ne_zero ϖ), ← ker_theta]
  exact RingHom.ker_isPrime _

instance isDiscreteValuationRing : IsDiscreteValuationRing (BdRPlus p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨xi ϖ, (prime_xi ϖ).irreducible, exists_associated_xi_pow ϖ⟩

theorem maximalIdeal_eq : IsLocalRing.maximalIdeal (BdRPlus p R) = RingHom.ker (theta p R) := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_theta_ne_zero, not_not,
    RingHom.mem_ker]


instance isAdicComplete_maximalIdeal :
    IsAdicComplete (IsLocalRing.maximalIdeal (BdRPlus p R)) (BdRPlus p R) := by
  rw [maximalIdeal_eq]
  infer_instance

theorem irreducible_iff (π : BdRPlus p R) : Irreducible π ↔ RingHom.ker (theta p R) = span {π} := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, maximalIdeal_eq]

variable (p R) in

def residueFieldEquiv : IsLocalRing.ResidueField (BdRPlus p R) ≃+* Localization.Away (p : R) :=
  (Ideal.quotEquivOfEq maximalIdeal_eq).trans (RingHom.quotientKerEquivOfSurjective theta_surjective)

@[simp] theorem residueFieldEquiv_residue (x : BdRPlus p R) :
    residueFieldEquiv p R (IsLocalRing.residue _ x) = theta p R x := rfl

theorem algebraMap_injective : Function.Injective (algebraMap (AinfInv p R) (BdRPlus p R)) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine AinfInv.eq_zero_of_forall_mem_kerTheta_pow ϖ fun n => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← eval_algebraMap, hx, map_zero]


theorem ker_theta_eq_span_teich_sub_one {ε : tateModule p R} (hε : IsPrimitive ε) :
    RingHom.ker (theta p R) = span {algebraMap (Ainf p R) (BdRPlus p R) (Ainf.teich p ε.1 - 1)} := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  obtain ⟨b, hb, hb0⟩ := Ainf.exists_teich_sub_one_eq ϖ hε
  have hu : IsUnit (algebraMap (Ainf p R) (BdRPlus p R) b) := by
    rw [isUnit_iff_theta_ne_zero, theta_algebraMap_ainf]
    exact (map_ne_zero_iff _ AinfInv.algebraMap_away_injective).2 hb0
  rw [ker_theta ϖ, hb, map_mul, Ideal.span_singleton_mul_right_unit hu]
  rfl

end BdRPlus

namespace BdR

variable [IsAlgClosed (FractionRing R)]

instance field : Field (BdR p R) := IsFractionRing.toField (BdRPlus p R)

theorem algebraMap_injective : Function.Injective (algebraMap (BdRPlus p R) (BdR p R)) :=
  IsFractionRing.injective _ _

section Uniformizer

variable {π : BdRPlus p R} (hπ : RingHom.ker (BdRPlus.theta p R) = span {π})
include hπ

theorem algebraMap_ne_zero : algebraMap (BdRPlus p R) (BdR p R) π ≠ 0 :=
  (map_ne_zero_iff _ algebraMap_injective).2 ((BdRPlus.irreducible_iff π).2 hπ).ne_zero

theorem filNat_eq_span (n : ℕ) :
    filNat p R n = Submodule.span (BdRPlus p R) {algebraMap (BdRPlus p R) (BdR p R) π ^ n} := by
  rw [filNat, BdRPlus.fil, hπ, Ideal.span_singleton_pow, ← Ideal.submodule_span_eq,
    Submodule.map_span, Set.image_singleton, Algebra.linearMap_apply, map_pow]

theorem fil_eq_span (i : ℤ) :
    fil p R i = Submodule.span (BdRPlus p R) {algebraMap (BdRPlus p R) (BdR p R) π ^ i} := by
  have h0 := algebraMap_ne_zero hπ
  set t := algebraMap (BdRPlus p R) (BdR p R) π
  have hi : t ^ i * t ^ (-i).toNat = t ^ i.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]
    congr 1
    omega
  ext x
  rw [fil, filNat_eq_span hπ, filNat_eq_span hπ, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h _ (Submodule.mem_span_singleton_self _))
    refine Submodule.mem_span_singleton.2 ⟨c, mul_right_cancel₀ (pow_ne_zero (-i).toNat h0) ?_⟩
    rw [smul_mul_assoc, hi, hc]
  · intro h y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 h
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact Submodule.mem_span_singleton.2 ⟨c * d, by rw [smul_mul_smul_comm, hi]⟩

theorem mem_fil_iff (i : ℤ) (x : BdR p R) : x ∈ fil p R i ↔ ∃ c : BdRPlus p R,
    x = algebraMap (BdRPlus p R) (BdR p R) π ^ i * algebraMap (BdRPlus p R) (BdR p R) c := by
  rw [fil_eq_span hπ, Submodule.mem_span_singleton]
  simp only [Algebra.smul_def, mul_comm, eq_comm]

theorem isLocalization_away : IsLocalization.Away π (BdR p R) := by
  have hirr := (BdRPlus.irreducible_iff π).2 hπ
  refine IsLocalization.Away.mk π (algebraMap_ne_zero hπ).isUnit ?_ ?_
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (BdRPlus p R) z
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hirr
    refine ⟨n, a * ↑u⁻¹, ?_⟩
    have h0 := algebraMap_ne_zero hπ
    have hu : algebraMap (BdRPlus p R) (BdR p R) u ≠ 0 := (u.isUnit.map _).ne_zero
    rw [map_mul, map_mul, map_pow, map_units_inv]
    field_simp
  · intro a b h
    exact ⟨0, by rw [algebraMap_injective h]⟩

end Uniformizer

theorem fil_natCast (n : ℕ) : fil p R n = filNat p R n := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [fil_eq_span (BdRPlus.ker_theta ϖ), filNat_eq_span (BdRPlus.ker_theta ϖ), zpow_natCast]

theorem fil_zero : fil p R 0 = 1 := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [fil_eq_span (BdRPlus.ker_theta ϖ), zpow_zero, Submodule.one_eq_span]

theorem mem_fil_zero_iff (x : BdR p R) :
    x ∈ fil p R 0 ↔ ∃ c : BdRPlus p R, algebraMap _ _ c = x := by
  rw [fil_zero, Submodule.mem_one]

theorem algebraMap_mem_fil_iff (n : ℕ) (x : BdRPlus p R) :
    algebraMap _ (BdR p R) x ∈ fil p R n ↔ x ∈ BdRPlus.fil p R n := by
  rw [fil_natCast, filNat, Submodule.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => algebraMap_injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem fil_mul_fil (i j : ℤ) : fil p R i * fil p R j = fil p R (i + j) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := BdRPlus.ker_theta ϖ
  rw [fil_eq_span h, fil_eq_span h, fil_eq_span h, Submodule.span_mul_span,
    Set.singleton_mul_singleton, zpow_add₀ (algebraMap_ne_zero h)]

theorem mul_mem_fil {i j : ℤ} {x y : BdR p R} (hx : x ∈ fil p R i) (hy : y ∈ fil p R j) :
    x * y ∈ fil p R (i + j) := fil_mul_fil (p := p) (R := R) i j ▸ Submodule.mul_mem_mul hx hy

instance gradedMonoid : SetLike.GradedMonoid (fil p R) where
  one_mem := (mem_fil_zero_iff _).2 ⟨1, map_one _⟩
  mul_mem _ _ _ _ := mul_mem_fil

theorem fil_antitone : Antitone (fil p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := BdRPlus.ker_theta ϖ
  intro i j hij x hx
  obtain ⟨n, rfl⟩ := Int.le.dest hij
  obtain ⟨c, rfl⟩ := (mem_fil_iff h _ _).1 hx
  exact (mem_fil_iff h _ _).2 ⟨BdRPlus.xi ϖ ^ n * c, by
    rw [zpow_add₀ (algebraMap_ne_zero h), map_mul, map_pow, zpow_natCast, mul_assoc]⟩

theorem eq_zero_of_forall_mem_fil {x : BdR p R} (h : ∀ i, x ∈ fil p R i) : x = 0 := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  obtain ⟨c, rfl⟩ := (mem_fil_zero_iff x).1 (h 0)
  rw [BdRPlus.eq_zero_of_forall_xi_pow_dvd ϖ (x := c) fun n => ?_, map_zero]
  rw [← mem_span_singleton, ← BdRPlus.fil_eq_span, ← algebraMap_mem_fil_iff]
  exact h n

instance charZero : CharZero (BdR p R) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (BdR p R)).injective

end BdR

end Reformulated.AutPerF
end
end
