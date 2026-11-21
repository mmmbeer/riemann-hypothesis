import Formalism.MahlerMeasure.LevelLattice
import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp
import Mathlib

section
namespace Formalism.InvariantFactorPaths.KP.LL

open Finset

variable {K : Type} [Field K] [CharZero K]

noncomputable def tU (k A l : ℕ) : K :=
  (-1 : K) ^ l * ((k - 1).choose l : K) * ((A - k - l).factorial : K) / ((A - l).factorial : K)

noncomputable def tT (k A l : ℕ) : K :=
  (((l.factorial : ℕ) : K) ^ 2 * (((A + 1 - l).choose l : ℕ) : K))⁻¹ *
    ((-1 : K) ^ (k - l) / ((((k - l).factorial : ℕ) : K) ^ 2 * (((A - 2 * l).choose (k - l) : ℕ) : K)))

end Formalism.InvariantFactorPaths.KP.LL
end

section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)

theorem mulLeft_pow_apply (a f : MvPolynomial σ k) (m : ℕ) :
    ((LinearMap.mulLeft k a) ^ m) f = a ^ m * f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' a m, mul_assoc, ← ih, pow_succ']
    show LinearMap.mulLeft k a ((LinearMap.mulLeft k a ^ m) f) = _
    rw [LinearMap.mulLeft_apply]

private lemma pderiv_mul_of_pderiv_eq_zero (i : σ) (q f : MvPolynomial σ k) (h : pderiv i q = 0) :
    pderiv i (q * f) = q * pderiv i f := by
  rw [Derivation.leibniz, h, smul_zero, add_zero, smul_eq_mul]

theorem tieF_mul_free (q f : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) q = 0) (he : ∀ c, pderiv (e c) q = 0) :
    tieF w e (q * f) = q * tieF w e f := by
  have key : ∀ g : MvPolynomial σ k, tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g) := by
    intro g
    simp [tieF]
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pderiv_mul_of_pderiv_eq_zero _ _ _ (he c), pderiv_mul_of_pderiv_eq_zero _ _ _ (hw c)]

theorem tieF_pow_mul_free (q f : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) q = 0)
    (he : ∀ c, pderiv (e c) q = 0) (m : ℕ) :
    (tieF w e ^ m) (q * f) = q * (tieF w e ^ m) f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    show tieF w e ((tieF w e ^ m) (q * f)) = q * tieF w e ((tieF w e ^ m) f)
    rw [ih, tieF_mul_free w e q _ hw he]

noncomputable def ehP : MvPolynomial σ k := X zv * X sv + ∑ c, X (w c) * X (e c)

private lemma pderiv_X_pow_of_ne' (i j : σ) (h : i ≠ j) (n : ℕ) : pderiv i (X j ^ n : MvPolynomial σ k) = 0 := by
  classical
  rw [Derivation.leibniz_pow]
  simp [pderiv_X, Pi.single_apply, Ne.symm h]

theorem harmonicProjection_expand (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k) :
    M.tieP w e zv sv o n z x = ∑ m ∈ range (o + 1),
      (((-1 : k) ^ m) / (((m.factorial : k) ^ 2) * ((o + n + r + z - 1).choose m : k))) •
        (ehP w e zv sv ^ m * (X zv ^ z * (tieF w e ^ m) x)) := by
  have hE : ∀ (m : ℕ) (y : MvPolynomial σ k),
      (M.tieEh w e zv sv ^ m) y = ehP w e zv sv ^ m * y := by
    intro m y
    unfold M.tieEh
    exact mulLeft_pow_apply _ _ m
  unfold M.tieP
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [tieF_pow_mul_free w e _ x (fun c => pderiv_X_pow_of_ne' _ _ (hz c).1 z)
    (fun c => pderiv_X_pow_of_ne' _ _ (hz c).2 z) m, hE]

private lemma add_single_mem_support_of_mem_support_pderiv (i : σ) (p : MvPolynomial σ k) (t : σ →₀ ℕ) (ht : t ∈ (pderiv i p).support) :
    t + Finsupp.single i 1 ∈ p.support := by
  classical
  have hp : pderiv i p = ∑ s ∈ p.support, pderiv i (monomial s (coeff s p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [MvPolynomial.mem_support_iff, hp, MvPolynomial.coeff_sum] at ht
  obtain ⟨s, hs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  rw [pderiv_monomial, MvPolynomial.coeff_monomial] at hne
  split_ifs at hne with hst
  · have hsi : s i ≠ 0 := by
      intro h0
      apply hne
      rw [h0]
      simp
    have hts : t + Finsupp.single i 1 = s := by
      rw [← hst]
      ext j
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h
        omega
      · omega
    rw [hts]
    exact hs
  · exact absurd rfl hne

theorem tieF_pow_apply_eq_zero_of_min_lt [CharZero k] (hw : Function.Injective w) (he : Function.Injective e)
    (hwe : ∀ c d, w c ≠ e d) {o n : ℕ} {x : MvPolynomial σ k} (hx : BiHom w e o n x) :
    ∀ m, min o n < m → (tieF w e ^ m) x = 0 := by
  classical
  have hsupp : ∀ (y : MvPolynomial σ k) (t : σ →₀ ℕ), t ∈ (tieF w e y).support →
      ∃ c, t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 ∈ y.support := by
    intro y t ht
    have key : tieF w e y = ∑ c, pderiv (w c) (pderiv (e c) y) := by simp [tieF]
    rw [key] at ht
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
    exact ⟨c, add_single_mem_support_of_mem_support_pderiv _ _ _ (add_single_mem_support_of_mem_support_pderiv _ _ _ hc)⟩
  have hW1 : ∀ (t : σ →₀ ℕ) (c : Fin r),
      (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (w d)) = (∑ d, t (w d)) + 1 := by
    intro t c
    have h1 : ∀ d, (e c = w d) ↔ False := fun d => ⟨fun h => hwe d c h.symm, False.elim⟩
    simp [Finsupp.single_apply, hw.eq_iff, Finset.sum_add_distrib, h1]
  have hE1 : ∀ (t : σ →₀ ℕ) (c : Fin r),
      (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (e d)) = (∑ d, t (e d)) + 1 := by
    intro t c
    have h1 : ∀ d, (w c = e d) ↔ False := fun d => ⟨fun h => hwe c d h, False.elim⟩
    simp [Finsupp.single_apply, he.eq_iff, Finset.sum_add_distrib, h1]
  have claim : ∀ (j : ℕ) (t : σ →₀ ℕ), t ∈ ((tieF w e ^ j) x).support →
      (∑ d, t (w d)) + j = o ∧ (∑ d, t (e d)) + j = n := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have ht' : t ∈ x.support := by simpa using ht
      simpa using hx t ht'
    | succ j ih =>
      intro t ht
      have ht' : t ∈ (tieF w e ((tieF w e ^ j) x)).support := by
        rw [pow_succ'] at ht
        exact ht
      obtain ⟨c, hc⟩ := hsupp _ t ht'
      obtain ⟨h1, h2⟩ := ih _ hc
      rw [hW1] at h1
      rw [hE1] at h2
      constructor <;> omega
  intro m hm
  by_contra hne
  obtain ⟨t, ht⟩ := MvPolynomial.ne_zero_iff.mp hne
  obtain ⟨h1, h2⟩ := claim m t (MvPolynomial.mem_support_iff.mpr ht)
  omega

private lemma cast_choose_add_eq_factorial_div_of_charZero [CharZero k] (a b : ℕ) :
    (((a + b).choose b : ℕ) : k) = ((a + b).factorial : k) / ((a.factorial : k) * (b.factorial : k)) := by
  rw [eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)))]
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  rw [mul_assoc] at h
  exact_mod_cast h

private lemma factorial_choose_signed_sum_eq_zero [CharZero k] (N j : ℕ) (hj : 1 ≤ j) (hN : 2 * j + 1 ≤ N) :
    ∑ l ∈ range (j + 1), (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((N - 2 * l - 1).choose (j - l) : k)) *
      ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹ = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → k, ∀ l, c l = (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 *
      ((N - 2 * l - 1).choose (j - l) : k)) * ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → k, ∀ l, W l = if l ≤ j then c l * (((l : ℕ) : k) * ((N - l - j : ℕ) : k)) /
      ((j : k) * ((N - 2 * l : ℕ) : k)) else 0 := ⟨_, fun _ => rfl⟩
  have key : ∀ l ∈ range (j + 1), c l = W l - W (l + 1) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rcases Nat.eq_or_lt_of_le hl' with hlj | hlj
    · have hne : (((l : ℕ) : k) * ((N - 2 * l : ℕ) : k)) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
      rw [hW, hW, ← hlj, if_pos le_rfl, if_neg (by omega), sub_zero, show N - l - l = N - 2 * l by omega,
        mul_div_assoc, div_self hne, mul_one]
    · obtain ⟨u, hu⟩ : ∃ u, j = l + 1 + u := ⟨j - l - 1, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, N = 2 * j + 1 + v := ⟨N - 2 * j - 1, by omega⟩
      rw [hW, hW, if_pos hl', if_pos (by omega), hc, hc]
      rw [show N - l - j = u + 2 + v by omega, show N - 2 * l - 1 = u + 1 + v + (u + 1) by omega,
        show N - 2 * l = 2 * u + 3 + v by omega, show N - l = 2 * u + 3 + v + l by omega,
        show j - l = u + 1 by omega,
        show N - (l + 1) - j = u + 1 + v by omega, show N - 2 * (l + 1) - 1 = u + v + u by omega,
        show N - 2 * (l + 1) = 2 * u + 1 + v by omega, show N - (l + 1) = 2 * u + 1 + v + (l + 1) by omega,
        show j - (l + 1) = u by omega]
      rw [cast_choose_add_eq_factorial_div_of_charZero (u + 1 + v) (u + 1), cast_choose_add_eq_factorial_div_of_charZero (2 * u + 3 + v) l,
        cast_choose_add_eq_factorial_div_of_charZero (u + v) u, cast_choose_add_eq_factorial_div_of_charZero (2 * u + 1 + v) (l + 1), hu]
      have F1 : ((u + 1).factorial : k) = ((u + 1 : ℕ) : k) * (u.factorial : k) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have F2 : ((u + 1 + v).factorial : k) = ((u + 1 + v : ℕ) : k) * ((u + v).factorial : k) := by
        rw [show u + 1 + v = u + v + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have F3 : ((u + 1 + v + (u + 1)).factorial : k) =
          ((u + v + u + 2 : ℕ) : k) * ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show u + 1 + v + (u + 1) = u + v + u + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      have F4 : ((2 * u + 3 + v + l).factorial : k) =
          ((2 * u + 3 + v + l : ℕ) : k) * ((2 * u + 1 + v + (l + 1)).factorial : k) := by
        rw [show 2 * u + 3 + v + l = 2 * u + 1 + v + (l + 1) + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have F5 : ((2 * u + 3 + v).factorial : k) = ((u + v + u + 3 : ℕ) : k) * ((u + v + u + 2 : ℕ) : k) *
          ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show 2 * u + 3 + v = u + v + u + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        ring
      have F6 : ((l + 1).factorial : k) = ((l + 1 : ℕ) : k) * (l.factorial : k) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have F7 : ((2 * u + 1 + v).factorial : k) = ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show 2 * u + 1 + v = u + v + u + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      rw [F3, F4, F5, F7, F2, F1, F6]
      clear hW hc W c hl hl' hlj hu hv hj hN F1 F2 F3 F4 F5 F6 F7
      have nB1 : ((u.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB1 : ((u.factorial : ℕ) : k) = B1 at nB1 ⊢
      have nB2 : (((u + v).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB2 : (((u + v).factorial : ℕ) : k) = B2 at nB2 ⊢
      have nB3 : (((u + v + u).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB3 : (((u + v + u).factorial : ℕ) : k) = B3 at nB3 ⊢
      have nB4 : ((l.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB4 : ((l.factorial : ℕ) : k) = B4 at nB4 ⊢
      have nB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) = B5 at nB5 ⊢
      have nL1 : ((u + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL1 : ((u + 1 : ℕ) : k) = L1 at nL1 ⊢
      have nL2 : ((u + 1 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL2 : ((u + 1 + v : ℕ) : k) = L2 at nL2 ⊢
      have nL3 : ((u + v + u + 2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL3 : ((u + v + u + 2 : ℕ) : k) = L3 at nL3 ⊢
      have nL4 : ((u + v + u + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL4 : ((u + v + u + 1 : ℕ) : k) = L4 at nL4 ⊢
      have nL5 : ((2 * u + 3 + v + l : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL5 : ((2 * u + 3 + v + l : ℕ) : k) = L5 at nL5 ⊢
      have nL6 : ((u + v + u + 3 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL6 : ((u + v + u + 3 : ℕ) : k) = L6 at nL6 ⊢
      have nL7 : ((l + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL7 : ((l + 1 : ℕ) : k) = L7 at nL7 ⊢
      have nL8 : ((l + 1 + u : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL8 : ((l + 1 + u : ℕ) : k) = L8 at nL8 ⊢
      have nL9 : ((2 * u + 3 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL9 : ((2 * u + 3 + v : ℕ) : k) = liftZP_newton at nL9 ⊢
      have nL10 : ((2 * u + 1 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL10 : ((2 * u + 1 + v : ℕ) : k) = ParameterUpperBound at nL10 ⊢
      field_simp [nB1, nB2, nB3, nB4, nB5, nL1, nL2, nL3, nL4, nL5, nL6, nL7, nL8, nL9, nL10]
      subst hB1 hB2 hB3 hB4 hB5 hL1 hL2 hL3 hL4 hL5 hL6 hL7 hL8 hL9 hL10
      push_cast
      ring
  simp only [← hc]
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub', hW, hW, if_pos (Nat.zero_le _), if_neg (by omega)]
  simp

theorem decomp [CharZero k] (hr : 1 ≤ r) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k)
    (hv : ∀ m, min o n < m → (tieF w e ^ m) x = 0) :
    X zv ^ z * x = ∑ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) := by
  classical
  have hT : ∀ l m : ℕ, (tieF w e ^ m) ((tieF w e ^ l) x) = (tieF w e ^ (l + m)) x := by
    intro l m
    rw [add_comm, pow_add]
    rfl
  have hterm : ∀ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) =
      ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + m)) x)) := by
    intro l hl
    have hlL : l ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hsub : range (min o n - l + 1) ⊆ range (o - l + 1) := by
      intro m hm
      simp only [Finset.mem_range] at hm ⊢
      omega
    rw [harmonicProjection_expand w e zv sv hz, Finset.mul_sum, ← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [LinearMap.map_smul, hT]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul]
      ring
    · intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      have h0 : (tieF w e ^ (l + m)) x = 0 := hv (l + m) (by omega)
      simp [LinearMap.map_smul, hT, h0]
  have hre : ∀ l ∈ range (min o n + 1),
      ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + m)) x)) =
      ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) := by
    intro l hl
    have hlL : l ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [Finset.sum_Ico_eq_sum_range, show min o n + 1 - l = min o n - l + 1 by omega]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left]
  have hcomm : ∑ l ∈ range (min o n + 1), ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) =
      ∑ j ∈ range (min o n + 1), ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) :=
    Finset.sum_comm' (fun l j => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)
  have hid : ∀ j ∈ range (min o n + 1),
      ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) = if j = 0 then X zv ^ z * x else 0 := by
    intro j hj
    have hjL : j ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← Finset.sum_smul]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      simp
    · rw [if_neg (by omega)]
      have hc2 : ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) = 0 := by
        refine Eq.trans ?_ (factorial_choose_signed_sum_eq_zero (o + n + r + z) j hpos (by omega))
        refine Finset.sum_congr rfl fun l hl => ?_
        have hlj : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        rw [show o - l + (n - l) + r + z - 1 = o + n + r + z - 2 * l - 1 by omega]
      rw [hc2, zero_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_congr rfl hre, hcomm, Finset.sum_congr rfl hid]
  simp

end

end Formalism.InvariantFactorPaths.KP.LL
end

section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section intpol
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem intPol_iff_bnd (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖coeff m x‖ ≤ 1 := by
  constructor
  · rintro ⟨y, rfl⟩ m
    simp only [AlgHom.toLinearMap_apply, MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]
    exact PadicInt.norm_le_one (coeff m y)
  · intro h
    refine ⟨∑ m ∈ x.support, MvPolynomial.monomial m (⟨coeff m x, h m⟩ : ℤ_[p]), ?_⟩
    simp only [AlgHom.toLinearMap_apply, map_sum, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_monomial]
    conv_rhs => rw [x.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    erw [MvPolynomial.map_monomial]
    rfl

theorem smul_mem_of_norm (Λ : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) {s : ℚ_[p]} (hs : ‖s‖ ≤ 1)
    {v : MvPolynomial σ ℚ_[p]} (hv : v ∈ Λ) : s • v ∈ Λ := by
  have e : s • v = (show ℤ_[p] from ⟨s, hs⟩) • v := by
    rw [← algebraMap_smul ℚ_[p] (show ℤ_[p] from ⟨s, hs⟩) v]
    rfl
  rw [e]
  exact Λ.smul_mem _ hv

theorem span_map_mem {τ : Type} (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p])
    (S : Set (MvPolynomial σ ℚ_[p])) (Λ : Submodule ℤ_[p] (MvPolynomial τ ℚ_[p]))
    (h : ∀ v ∈ S, T v ∈ Λ) : ∀ v ∈ Submodule.span ℤ_[p] S, T v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => exact h v hv
  | zero => rw [map_zero]; exact Λ.zero_mem
  | add a b _ _ ha hb => rw [map_add]; exact Λ.add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul ℚ_[p] c a, map_smul, algebraMap_smul]
    exact Λ.smul_mem c ha

theorem free_X {v u : σ} (h : u ≠ v) : pderiv v (X u : MvPolynomial σ ℚ_[p]) = 0 := by
  exact MvPolynomial.pderiv_X_of_ne h

theorem free_mul {v : σ} {a b : MvPolynomial σ ℚ_[p]} (ha : pderiv v a = 0) (hb : pderiv v b = 0) :
    pderiv v (a * b) = 0 := by
  rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]

theorem free_pow {v : σ} {a : MvPolynomial σ ℚ_[p]} (ha : pderiv v a = 0) (n : ℕ) :
    pderiv v (a ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero]; exact Derivation.map_one_eq_zero _
  | succ n ih => rw [pow_succ]; exact free_mul ih ha

theorem free_ehP {r : ℕ} {w e : Fin r → σ} {zv sv v : σ} (h1 : zv ≠ v) (h2 : sv ≠ v) (h3 : ∀ c, w c ≠ v)
    (h4 : ∀ c, e c ≠ v) : pderiv v (ehP w e zv sv : MvPolynomial σ ℚ_[p]) = 0 := by
  unfold ehP
  rw [map_add, map_sum, free_mul (free_X h1) (free_X h2), zero_add]
  exact Finset.sum_eq_zero fun c _ => free_mul (free_X (h3 c)) (free_X (h4 c))

end intpol

end Formalism.InvariantFactorPaths.KP.LL
end

section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section block
variable {N r : ℕ} (D : BlockData N)

def wv (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i), c)
def ev (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i + 1), c)
def zi (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalZ N r D.T.t (Fin.castSucc i)
def si (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalS N r D.T.t (Fin.castSucc i)
def wU (c : Fin r) : BVar N r D.T.t := Sum.inl (Fin.castSucc D.uPos, c)
def zP (r : ℕ) : BVar N r D.T.t := scalZ N r D.T.t (Fin.last D.T.t)
def sP (r : ℕ) : BVar N r D.T.t := scalS N r D.T.t (Fin.last D.T.t)

variable {D}

theorem pos_succ_lt (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 + 1 < N := by
  obtain ⟨_, h2, _, h4⟩ := hB
  have := h2 i
  omega

theorem finPos_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (finPos N (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  show min (D.T.pos i) N = D.T.pos i
  omega

theorem finPos_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (finPos N (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) N = D.T.pos i + 1
  omega

theorem letterAt_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (D.letterAt (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  show min (D.T.pos i) (N - 1) = D.T.pos i
  omega

theorem letterAt_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (D.letterAt (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) (N - 1) = D.T.pos i + 1
  omega

theorem pos_inj (hB : D.BlockOK) {i i' : Fin D.T.t} (h : D.T.pos i = D.T.pos i') : i = i' := hB.1.1.injective h

theorem pos_ne_succ (hB : D.BlockOK) (i i' : Fin D.T.t) : D.T.pos i ≠ D.T.pos i' + 1 := by
  intro h
  obtain ⟨hi, hti, _⟩ := hB.1.2.1 i
  obtain ⟨hi', _, hfi'⟩ := hB.1.2.1 i'
  have e : D.LL.vec ⟨D.T.pos i, by omega⟩ = D.LL.vec ⟨D.T.pos i' + 1, hi'⟩ := congrArg D.LL.vec (Fin.ext h)
  rw [hti, hfi'] at e
  exact absurd e (by decide)

theorem pos_lt_u (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 < (D.uPos : ℕ) := hB.2.1 i

theorem deg_lettersAt_pos (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) = D.LL.deg (D.letterAt (D.T.pos i)) - j i := by
  simp only [BlockData.lettersAt]
  have hs : (∑ i', if ((D.letterAt (D.T.pos i) : Fin N) : ℕ) = D.T.pos i' ∨
      ((D.letterAt (D.T.pos i) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
    rw [Finset.sum_eq_single i]
    · simp [letterAt_pos_val hB]
    · intro b _ hb
      rw [if_neg]
      rw [letterAt_pos_val hB]
      rintro (h | h)
      · exact hb (pos_inj hB h).symm
      · exact pos_ne_succ hB i b h
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : D.letterAt (D.T.pos i) ≠ D.uPos := by
    intro h
    have h1 := congrArg Fin.val h
    rw [letterAt_pos_val hB] at h1
    have := pos_lt_u hB i
    omega
  rw [hs, if_neg hu, Nat.sub_zero]

theorem deg_lettersAt_pos_succ (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) = D.LL.deg (D.letterAt (D.T.pos i + 1)) - j i := by
  simp only [BlockData.lettersAt]
  have hs : (∑ i', if ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' ∨
      ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
    rw [Finset.sum_eq_single i]
    · simp [letterAt_succ_val hB]
    · intro b _ hb
      rw [if_neg]
      rw [letterAt_succ_val hB]
      rintro (h | h)
      · exact pos_ne_succ hB b i h.symm
      · exact hb (pos_inj hB (by omega)).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : D.letterAt (D.T.pos i + 1) ≠ D.uPos := by
    intro h
    have h1 := congrArg Fin.val h
    rw [letterAt_succ_val hB] at h1
    have := pos_lt_u hB i
    omega
  rw [hs, if_neg hu, Nat.sub_zero]

theorem deg_U (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (D.lettersAt j jp).deg D.uPos = D.LL.deg D.uPos - jp := by
  simp only [BlockData.lettersAt]
  rw [Finset.sum_eq_zero (fun b _ => by
      rw [if_neg]
      have := pos_lt_u hB b
      omega)]
  simp

end block

end Formalism.InvariantFactorPaths.KP.LL
end

section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M
open scoped Pointwise

section lat
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

noncomputable def Lat (j : Fin D.T.t → ℕ) (jp : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}

noncomputable def Pt (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (finPos N (D.T.pos i), c)) (fun c => Sum.inl (finPos N (D.T.pos i + 1), c))
    (scalZ N r D.T.t (Fin.castSucc i)) (scalS N r D.T.t (Fin.castSucc i))
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
    (D.T.z i) y

noncomputable def PL (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  L.foldr (fun i acc => Pt p D j jp i acc) y

noncomputable def Pplus (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (Fin.castSucc D.uPos, c)) (fun c => xiVar N r D.T.t c)
    (scalZ N r D.T.t (Fin.last D.T.t)) (scalS N r D.T.t (Fin.last D.T.t))
    (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus y

theorem Pall_eq (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    D.Pall p j jp y = Pplus p D jp (PL p D (List.finRange D.T.t) j jp y) := rfl

variable {p D}

theorem wv_chain (hB : D.BlockOK) (i : Fin D.T.t) (c : Fin r) :
    wv D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i), c) := by
  simp only [wv, chainEmb, Sum.inl.injEq, Prod.mk.injEq, and_true]
  apply Fin.ext
  rw [finPos_pos_val hB, Fin.coe_castSucc, letterAt_pos_val hB]

theorem ev_chain (hB : D.BlockOK) (i : Fin D.T.t) (c : Fin r) :
    ev D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i + 1), c) := by
  simp only [ev, chainEmb, Sum.inl.injEq, Prod.mk.injEq, and_true]
  apply Fin.ext
  rw [finPos_succ_val hB, Fin.coe_castSucc, letterAt_succ_val hB]

theorem chainEmb_inj : Function.Injective (chainEmb N r D.T.t) := by
  intro x y h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
  exact Prod.ext h.1 h.2

theorem xi_notin (c : Fin r) : xiVar N r D.T.t c ∉ Set.range (chainEmb N r D.T.t) := by
  rintro ⟨x, hx⟩
  simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at hx
  exact (Fin.castSucc_lt_last x.1).ne hx.1

theorem supp_gen {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]}
    {mon : BVar N r D.T.t →₀ ℕ} (hm : mon ∈ (rename (chainEmb N r D.T.t) y * g).support) :
    ∃ m1 ∈ y.support, ∃ m2 ∈ g.support, mon = Finsupp.mapDomain (chainEmb N r D.T.t) m1 + m2 := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  rw [MvPolynomial.support_rename_of_injective chainEmb_inj] at ha
  obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨m1, hm1, b, hb, rfl⟩

theorem xi_supp {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {m2 : BVar N r D.T.t →₀ ℕ} (hm2 : m2 ∈ g.support) :
    (∀ v, (∀ c, v ≠ xiVar N r D.T.t c) → m2 v = 0) ∧ ∑ c, m2 (xiVar N r D.T.t c) = b := by
  have h1 := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at h1
  have h2 := h1 hm2
  refine ⟨fun v hv => ?_, h2.2⟩
  by_contra hne
  obtain ⟨c, hc⟩ := h2.1 v (Finsupp.mem_support_iff.mpr hne)
  exact hv c hc

end lat

end Formalism.InvariantFactorPaths.KP.LL
end

section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section lat2
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem wv_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : wv D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wv, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_pos_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega

theorem ev_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [ev, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_succ_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega

theorem wU_ne_xi (c d : Fin r) : wU D c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wU, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact (Fin.castSucc_lt_last _).ne h.1

theorem yz_pol {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Pol p r LL :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).1

theorem yz_y {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Y p (r := r) LL J M :=
  (Submodule.mem_inf.1 hy).1

theorem yz_int {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ IntPol p (Fin N × Fin r) :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).2).2

theorem yz_mk {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (h1 : y ∈ Y p (r := r) LL J M) (h2 : y ∈ IntPol p (Fin N × Fin r)) :
    y ∈ YZ p (r := r) LL J M :=
  Submodule.mem_inf.2 ⟨h1, Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 h1).1, h2⟩⟩

omit [NeZero r] in
theorem biHom_span {r' : ℕ} {w e : Fin r' → BVar N r D.T.t} {a b : ℕ} {S : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])}
    (h : ∀ x ∈ S, BiHom w e a b x) : ∀ x ∈ Submodule.span ℤ_[p] S, BiHom w e a b x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hxS => exact h x hxS
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h' | h'
    · exact hx m h'
    · exact hy m h'
  | smul a x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

theorem biHom_tie (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wv D i) (ev D i) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)))
      ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1))) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wv D i c) = m1 (D.letterAt (D.T.pos i), c) := fun c => by
      rw [wv_chain (hB := hB), Finsupp.mapDomain_apply (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wv D i c) = 0 := fun c => hxi.1 _ (fun d => wv_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (ev D i c) = m1 (D.letterAt (D.T.pos i + 1), c) := fun c => by
      rw [ev_chain (hB := hB), Finsupp.mapDomain_apply (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (ev D i c) = 0 := fun c => hxi.1 _ (fun d => ev_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _

theorem biHom_plus (j : Fin D.T.t → ℕ) (jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wU D) (xiVar N r D.T.t) ((D.lettersAt j jp).deg D.uPos) (D.B - jp) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wU D c) = m1 (D.uPos, c) := fun c => by
      show Finsupp.mapDomain (chainEmb N r D.T.t) m1 (chainEmb N r D.T.t (D.uPos, c)) = _
      rw [Finsupp.mapDomain_apply (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wU D c) = 0 := fun c => hxi.1 _ (fun d => wU_ne_xi c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (xiVar N r D.T.t c) = 0 := fun c =>
      Finsupp.mapDomain_notin_range _ _ (xi_notin (D := D) c)
    simp only [e1, Finset.sum_const_zero, zero_add]
    exact hxi.2

end lat2

end Formalism.InvariantFactorPaths.KP.LL
end

section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

def PairStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ) (zv sv : σ), 1 ≤ r → (∀ c, w c ≠ zv ∧ e c ≠ zv) →
    ∀ (o n z L u : ℕ) (Λ : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])),
      (∀ l, ∀ x ∈ Λ l, ∀ m, min (o - l) (n - l) < m → (tieF w e ^ m) x = 0) →
      (∀ l m, m ≤ min o n → ∀ x ∈ Λ l,
        (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) x) ∈ Λ (l + m)) →
      r * L + Nat.log p (o + n + r + z) ≤ u →
      ∀ l ≤ min o n, ∀ x ∈ Λ l,
        ((p : ℚ_[p]) ^ u • (ehP w e zv sv ^ l * (X zv ^ z * x)) ∈ Submodule.span ℤ_[p]
          {v | ∃ l' ≤ min o n, ∃ x' ∈ Λ l', v = ehP w e zv sv ^ l' * tieP w e zv sv (o - l') (n - l') z x'}) ∧
        ((p : ℚ_[p]) ^ u • (ehP w e zv sv ^ l * tieP w e zv sv (o - l) (n - l) z x) ∈ Submodule.span ℤ_[p]
          {v | ∃ l' ≤ min o n, ∃ x' ∈ Λ l', v = ehP w e zv sv ^ l' * (X zv ^ z * x')})

section block
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

def HypJoin : Prop :=
  ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    Formalism.GM.tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y ∈
      Y p (r := r) (D.lettersAt (Function.update j i (j i + 1)) jp) D.T.J D.T.thr

def HypU : Prop :=
  ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (c : Fin r), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    pderiv (D.uPos, c) y ∈ Y p (r := r) (D.lettersAt j (jp + 1)) D.T.J D.T.thr

noncomputable def midGen (k : ℕ) (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop k) j jp x

noncomputable def Mid (k : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {v | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧ ∃ x ∈ Lat p D (r := r) j jp,
    v = midGen p D k j jp x}

noncomputable def MidP : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {v | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧ ∃ x ∈ Lat p D (r := r) j jp,
    v = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)}

end block

def LatPlus : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → HypU p (r := r) D →
    ∀ (j : Fin D.T.t → ℕ) (jp m L : ℕ), Nat.log p m ≤ L → ∀ x ∈ Lat p D (r := r) j jp,
      (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF (wU D) (xiVar N r D.T.t) ^ m) x) ∈
        Lat p D (r := r) j (jp + m)

def LatTie : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → HypJoin p (r := r) D →
    ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) (m L : ℕ), Nat.log p m ≤ L → ∀ x ∈ Lat p D (r := r) j jp,
      (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF (wv D i) (ev D i) ^ m) x) ∈
        Lat p D (r := r) (j + Pi.single i m) jp

def PLLin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ),
    (∃ T : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p],
      ∀ x, T x = PL p D L j jp x) ∧
    ∃ T : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p],
      ∀ x, T x = Pplus p D jp x

def CommPL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK →
    ∀ (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp m : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
      (∀ k : Fin D.T.t, k ∉ L →
        (tieF (wv D k) (ev D k) ^ m) (PL p D L j jp x) = PL p D L j jp ((tieF (wv D k) (ev D k) ^ m) x)) ∧
      (tieF (wU D) (xiVar N r D.T.t) ^ m) (PL p D L j jp x) =
        PL p D L j jp ((tieF (wU D) (xiVar N r D.T.t) ^ m) x)

def ParamPL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK →
    ∀ (L : List (Fin D.T.t)) (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
      (∀ i ∈ L, j i = j' i) → PL p D L j jp x = PL p D L j' jp' x

def MidTop : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), Mid p (r := r) D D.T.t = D.SSZ p (r := r)

def MidPEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), MidP p (r := r) D = D.PSZ p (r := r)

def JoinCondition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a u : ℕ), D.BlockOK → 1 ≤ r →
    (∀ x, D.LL.deg x ≤ 2 * a) → (∀ i, D.T.z i ≤ 2 * a) → HypJoin p (r := r) D →
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u → ∀ k < D.T.t,
      (∀ v ∈ Mid p (r := r) D (k + 1), (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k) ∧
      (∀ v ∈ Mid p (r := r) D k, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D (k + 1))

def PlusCondition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a u : ℕ), D.BlockOK → 1 ≤ r →
    (∀ x, D.LL.deg x ≤ 2 * a) → D.B ≤ 2 * a → D.zPlus ≤ 2 * a → HypU p (r := r) D →
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u →
      (∀ v ∈ Mid p (r := r) D 0, (p : ℚ_[p]) ^ u • v ∈ MidP p (r := r) D) ∧
      (∀ v ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D 0)

end Formalism.InvariantFactorPaths.KP.LL
end
