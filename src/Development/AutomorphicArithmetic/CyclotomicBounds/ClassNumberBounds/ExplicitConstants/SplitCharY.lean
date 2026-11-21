import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.UniformIffAboveThreshold
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ExistsHostDataWild
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ExistsIsPrimitiveRootIff

section
open Filter Set Real

namespace KStar.Consta.Params

variable (P : Params)

structure RowsAt (X x : ℝ) (q₁ d n cond : ℕ) (t : ℝ) : Prop where
  p12 : x ^ (2 * P.Ct + 5) < q₁ ∧ x ^ (2 * P.Ct + 5) < d
  log_first_prime_le : Real.log q₁ ≤ x ^ (P.eps / 5)
  log_d_le_alt : Real.log d ≤ x ^ (P.eps / 5) * Real.log x ^ 2
  log_conductor_le : Real.log cond ≤ 2 * x ^ (P.eps / 5) * Real.log x ^ 2
  p13x : 2 * x ^ (P.eps / 5) * Real.log x ^ 2 ≤ P.L x / 100
  exp_power_le_min : Real.exp (x ^ (P.eps / (6 * P.K))) ≤ min (q₁ : ℝ) d
  exp_power_le_sqrt_d : Real.exp (x ^ (P.eps / (5 * P.K))) ≤ Real.sqrt d
  p15x : 11 ≤ x ^ (P.eps / 5)
  inert_primes_large : ∀ p : ℕ, p.Prime → ¬ SplitsIn d p → P.z X < p ∧ x ^ (P.eps / (5 * P.K)) < p
  power_le_exp_power : x ^ (2 * P.Ct) ≤ Real.exp (x ^ (P.eps / (5 * P.K)))
  p46 : P.Lw x ≤ 11 * (P.Ct + 4) * Real.log x
  log_product_small : Real.log (n * P.q * t * q₁ * d) ≤ x ^ P.eps / 400 ∧ 9 * t ^ 2 < min (q₁ : ℝ) d
  del : P.delZ X ≤ P.delX x ∧ P.delX x ≤ 1 / 8
  x2 : P.Lbar < x ^ (P.eps / 8)
  x4 : 16 * P.binaryExponentBound ≤ x ^ (2 * P.eps / 3)
  fact : P.L x ≤ (P.N5.factorial : ℝ) * Real.sqrt d

end KStar.Consta.Params
end

section
open Filter Set Real

namespace KStar.Consta.Params

variable (P : Params)

noncomputable def L1 (k x : ℝ) (p : ℕ) : ℕ := ⌈Real.logb p ((k * x ^ Aexp) ^ 4)⌉₊

noncomputable def L2 (k x : ℝ) (S : Set ℕ) : ℕ := 2 * sSup (L1 k x '' S)

noncomputable def CT (o : ℕ) : ℝ := 2 * o * ((2 : ℝ) ^ P.Lbar + 2)

end KStar.Consta.Params
end

section
open Filter Set Real

namespace KStar.Consta

structure TopParams where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  Ct : ℝ
  Ct_nonneg : 0 ≤ Ct
  Cc : ℝ
  la : ℝ
  one_lt_la : 1 < la
  q : ℕ
  q_pos : 0 < q
  R : ℕ
  CK : ℝ
  eps_le : eps ≤ 2 * CK * Ct

noncomputable instance : Inhabited TopParams :=
  ⟨{ eps := 1 / 100, eps_pos := by norm_num, eps_lt := by norm_num, Ct := 401,
     Ct_nonneg := by norm_num, Cc := 1, la := 2, one_lt_la := by norm_num, q := 1,
     q_pos := one_pos, R := 1, CK := 1, eps_le := by norm_num }⟩

namespace TopParams

variable (T : TopParams)

noncomputable def B0 : ℝ := 2 * T.CK * T.Ct / T.eps

end TopParams

end KStar.Consta
end

section
open Filter Set Real

namespace KStar.Consta.Params

variable (P : Params)

structure RowsAtH (o : ℕ) (C X x : ℝ) (q₁ d n cond : ℕ) (t : ℝ) : Prop
    extends P.RowsAt X x q₁ d n cond t where
  loglog : 1 ≤ Real.log (Real.log x)
  cond_alt : Real.log cond ≤ 3 * P.z' X
  x4H : 16 * P.CT o ≤ x ^ (2 * P.eps / 3)
  power_le_size_over_log : 6 * x ^ 5 ≤ (q₁ : ℝ) / Real.log q₁ ∧ 6 * x ^ 5 ≤ (d : ℝ) / Real.log d
  cubic_delta_bounds : 385 * x ^ C * x ^ C * x ^ C * P.delX x ≤ 1 ∧ 385 * x ^ C * x ^ C * x ^ C * P.delZ X ≤ 1
  root_discriminant_power_bounds : ∀ rd : ℝ, Real.sqrt d ≤ rd → Real.exp (P.z X) ≤ rd ^ 7 ∧ x ^ (2 * P.Ct) ≤ rd ^ 7
  inert_prime_digit_bound : ∀ (l j : ℕ) (lA : ℝ), l.Prime → ¬ SplitsIn d l → lA ≤ x ^ 5 →
    IsLeast {i : ℕ | lA ≤ ((l : ℝ) - 1) ^ i} j →
      j ≤ P.jmax ∧ 2 * (j : ℝ) + 2 ≤ P.Lw x ∧ (j : ℝ) + 1 ≤ P.Jeps
  l2 : ∀ (k : ℝ) (S : Set ℕ), 1 ≤ k → k ≤ 2 * x ^ (9 / 2 + 10 * P.eps) →
    (∀ p ∈ S, p.Prime ∧ ¬ SplitsIn d p) → (L2 k x S : ℝ) ≤ P.Lbar
  de2 : x ^ (-P.eps) ≤ 1 / (4 * P.Lw x)
  pair : 8 * P.q < q₁ ∧ 8 * P.q < d ∧ jacobiSym (-(q₁ : ℤ)) d = -1

end KStar.Consta.Params
end

section
open NumberField KStar.Ram

namespace KStar.Consta

theorem exists_quadField {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) := by
  have : NeZero d := ⟨hd.ne_zero⟩
  have : NeZero (d : ℚ) := ⟨by exact_mod_cast hd.ne_zero⟩
  have : IsCyclotomicExtension {d} ℚ (CyclotomicField d ℚ) :=
    CyclotomicField.isCyclotomicExtension d ℚ
  obtain ⟨ψ, hψ⟩ := exists_isImagQuad (N := d) hd h4 dvd_rfl
  obtain ⟨E, hE⟩ := (fieldChars_lattice (N := d) (K := CyclotomicField d ℚ)).1.2
    (Subgroup.zpowers ψ)
  exact ⟨E, inferInstance, inferInstance, (quadratic_discr_iff (N := d) E d).2 ⟨ψ, hψ, hE⟩⟩

end KStar.Consta
end
