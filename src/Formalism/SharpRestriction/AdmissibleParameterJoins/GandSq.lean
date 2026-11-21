import Mathlib
import Formalism.SharpRestriction.GrowthBounds.KerTies

section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries

section AlgebraTools

variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]

def diagS (a : PowerSeries R) (i : ι) : MvPowerSeries ι R := PowerSeries.subst (X i : MvPowerSeries ι R) a

private theorem powerSeries_hasSubst_of_constantCoeff_eq_zero {τ : Type} {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) :
    PowerSeries.HasSubst f := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hf
  | (show IsNilpotent _; rw [hf]; exact IsNilpotent.zero)

private theorem coeff_diagS [DecidableEq ι] (a : PowerSeries R) (i : ι) (e : ι →₀ ℕ) :
    coeff e (diagS a i : MvPowerSeries ι R) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) a else 0 := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries ι R) := powerSeries_hasSubst_of_constantCoeff_eq_zero (constantCoeff_X i)
  unfold diagS
  rw [PowerSeries.coeff_subst hX]
  have hterm : ∀ d : ℕ, PowerSeries.coeff d a • coeff e ((X i : MvPowerSeries ι R) ^ d) =
      if e = Finsupp.single i d then PowerSeries.coeff d a else 0 := by
    intro d
    first
    | (rw [MvPowerSeries.coeff_X_pow, smul_eq_mul]; split_ifs <;> simp)
    | (rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul]; split_ifs <;> simp)
  simp_rw [hterm]
  rw [finsum_eq_single _ (e i)]
  intro d hd
  have hne : ¬ e = Finsupp.single i d := fun he => hd (by rw [he, Finsupp.single_eq_same])
  simp [hne]

private theorem coeff_diagS_eq_zero_of_apply_eq_zero {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0)
    (i : ι) (d : ι →₀ ℕ) (hd : d i = 0) : coeff d (diagS a i : MvPowerSeries ι R) = 0 := by
  classical
  rw [coeff_diagS]
  split_ifs
  · rw [hd, PowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
  · rfl

theorem cc_dg {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) (i : ι) :
    constantCoeff (diagS a i : MvPowerSeries ι R) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_diagS_eq_zero_of_apply_eq_zero ha i 0 (by simp)

theorem hs_dg {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) :
    HasSubst (diagS a : ι → MvPowerSeries ι R) where
  const_coeff s := by rw [cc_dg ha]; exact IsNilpotent.zero
  coeff_zero d := by
    classical
    refine (d.support.finite_toSet).subset ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    unfold diagS at hs
    rw [PowerSeries.coeff_subst_single] at hs
    by_contra hns
    have h0 : d s = 0 := by simpa using hns
    split_ifs at hs with h1
    · rw [h0] at hs
      exact hs (by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ha])
    · exact hs rfl

private theorem hasSubst_of_finite_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {c : σ → MvPowerSeries τ R}
    (hc : ∀ s, constantCoeff (c s) = 0) : HasSubst c := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hc

theorem subst_psubst {c : ι → MvPowerSeries κ R} (hc : HasSubst c) {f : MvPowerSeries ι R}
    (hf : constantCoeff f = 0) (a : PowerSeries R) :
    subst c (PowerSeries.subst f a) = PowerSeries.subst (subst c f) a := by
  have hf' : HasSubst (fun _ : Unit => f) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hf)
  first
  | exact MvPowerSeries.subst_comp_subst_apply hf' hc a
  | (rw [PowerSeries.subst, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hf' hc])

theorem dg_comp {a b : PowerSeries R} (hb : PowerSeries.constantCoeff b = 0) (i : ι) :
    subst (diagS b) (diagS a i : MvPowerSeries ι R) = diagS (PowerSeries.subst b a) i := by
  have hc : HasSubst (diagS b : ι → MvPowerSeries ι R) := hs_dg hb
  have hXi : constantCoeff (X i : MvPowerSeries ι R) = 0 := constantCoeff_X i
  have hb' : constantCoeff (b : MvPowerSeries Unit R) = 0 := hb
  have hu : HasSubst (fun _ : Unit => (X i : MvPowerSeries ι R)) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hXi)
  calc subst (diagS b) (diagS a i : MvPowerSeries ι R)
      = PowerSeries.subst (subst (diagS b) (X i : MvPowerSeries ι R)) a :=
        subst_psubst hc hXi a
    _ = PowerSeries.subst (diagS b i) a := by rw [MvPowerSeries.subst_X hc]
    _ = PowerSeries.subst (subst (fun _ : Unit => (X i : MvPowerSeries ι R)) b) a := rfl
    _ = subst (fun _ : Unit => (X i : MvPowerSeries ι R)) (PowerSeries.subst b a) :=
        (subst_psubst hu hb' a).symm
    _ = diagS (PowerSeries.subst b a) i := rfl

theorem map_dg (h : R →+* S) (a : PowerSeries R) (i : ι) :
    map h (diagS a i : MvPowerSeries ι R) = diagS (PowerSeries.map h a) i := by
  classical
  ext e
  rw [MvPowerSeries.coeff_map, coeff_diagS, coeff_diagS]
  split_ifs
  · rw [PowerSeries.coeff_map]
  · exact map_zero h


private theorem diagS_unit (a : PowerSeries R) :
    (diagS a () : MvPowerSeries Unit R) = (a : MvPowerSeries Unit R) := by
  refine MvPowerSeries.ext fun e => ?_
  have he : e = Finsupp.single () (e ()) := Finsupp.ext fun u => by
    cases u
    rw [Finsupp.single_eq_same]
  rw [coeff_diagS, if_pos he]
  conv_rhs => rw [he]
  rfl

private theorem constantCoeff_powerSeries_subst_eq_zero_admissible_parameter_joins {τ : Type} {f : MvPowerSeries τ R} (hf : constantCoeff f = 0)
    {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) :
    constantCoeff (PowerSeries.subst f a) = 0 := by
  obtain ⟨b, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
  first
  | rw [PowerSeries.subst_mul (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), PowerSeries.subst_X (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, hf, zero_mul]
  | rw [← PowerSeries.coe_substAlgHom (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, hf, zero_mul]

theorem coeff_pow_zero {f : MvPowerSeries ι R} (hf : constantCoeff f = 0) :
    ∀ (d : ℕ) (n : ι →₀ ℕ), n.degree < d → coeff n (f ^ d) = 0 := by
  classical
  intro d
  induction d with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero _)
  | succ d ih =>
    intro n hn
    rw [pow_succ, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    replace hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases h2 : p.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero]
    · have hdeg : p.1.degree + p.2.degree = n.degree := by
        rw [← hp]
        first
        | exact (Finsupp.degree_add p.1 p.2).symm
        | exact (map_add Finsupp.degree p.1 p.2).symm
        | simp [Finsupp.degree_add]
      have hpos : p.2.degree ≠ 0 := by
        intro h
        apply h2
        first
        | exact (Finsupp.degree_eq_zero_iff _).mp h
        | exact Finsupp.degree_eq_zero_iff.mp h
      rw [ih p.1 (by omega), zero_mul]

end AlgebraTools

section Exp

variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']

def Ex (f : MvPowerSeries ι K) : MvPowerSeries ι K := PowerSeries.subst f (PowerSeries.exp K)

theorem subst_Ex {c : ι → MvPowerSeries κ K} (hc : HasSubst c) {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) : subst c (Ex f) = Ex (subst c f) := by
  exact subst_psubst hc hf (PowerSeries.exp K)

private theorem coeff_Ex_eq_sum_inv_factorial_coeff_pow {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) (n : ι →₀ ℕ) :
    coeff n (Ex f) =
      ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K))⁻¹ * coeff n (f ^ k) := by
  unfold Ex
  rw [PowerSeries.coeff_subst (powerSeries_hasSubst_of_constantCoeff_eq_zero hf)]
  have key : ∀ k, k ∉ Finset.range (n.degree + 1) →
      PowerSeries.coeff k (PowerSeries.exp K) • coeff n (f ^ k) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [coeff_pow_zero hf k n (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n.degree + 1))
    (fun k hk => by
      by_contra h
      exact hk (key k h))]
  apply Finset.sum_congr rfl
  intro k _
  simp [PowerSeries.coeff_exp, smul_eq_mul]

theorem map_Ex (h : K →+* K') {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) :
    map h (Ex f) = Ex (map h f) := by
  ext n
  have hf' : constantCoeff (map h f) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hf, map_zero]
  rw [MvPowerSeries.coeff_map, coeff_Ex_eq_sum_inv_factorial_coeff_pow hf, coeff_Ex_eq_sum_inv_factorial_coeff_pow hf', map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, map_inv₀, map_natCast, ← map_pow (MvPowerSeries.map h) f k, MvPowerSeries.coeff_map]

theorem Ex_zero : Ex (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_Ex_eq_sum_inv_factorial_coeff_pow (f := (0 : MvPowerSeries ι K)) (by simp), Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

private theorem coeff_X_zero_add_X_one_pow (n : Fin 2 →₀ ℕ) (k : ℕ) :
    coeff n ((X 0 + X 1 : MvPowerSeries (Fin 2) K) ^ k) =
      if k = n 0 + n 1 then ((k.choose (n 0) : ℕ) : K) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      coeff n ((X 0 : MvPowerSeries (Fin 2) K) ^ m * X 1 ^ (k - m) *
        ((k.choose m : ℕ) : MvPowerSeries (Fin 2) K)) =
        if n = Finsupp.single 0 m + Finsupp.single 1 (k - m) then ((k.choose m : ℕ) : K) else 0 := by
    intro m _
    first
    | (rw [← nsmul_eq_mul', map_nsmul, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial, one_mul, MvPowerSeries.coeff_monomial, nsmul_eq_mul]
       split_ifs <;> simp)
    | (rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
        ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C,
        MvPowerSeries.coeff_monomial]
       split_ifs <;> simp)
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hk
  · rw [Finset.sum_eq_single (n 0)]
    · rw [if_pos]
      ext i
      fin_cases i <;> simp [hk]
    · intro m _ hm
      rw [if_neg]
      intro h
      apply hm
      have h0 := congrArg (fun e => e 0) h
      simp at h0
      omega
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro h
    apply hk
    have h0 := congrArg (fun e => e 0) h
    have h1 := congrArg (fun e => e 1) h
    simp at h0 h1
    rw [Finset.mem_range] at hm
    omega

theorem Ex_biv : Ex (X 0 + X 1 : MvPowerSeries (Fin 2) K) = Ex (X 0) * Ex (X 1) := by
  ext n
  have hs : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hL : coeff n (Ex (X 0 + X 1 : MvPowerSeries (Fin 2) K)) =
      PowerSeries.coeff (n 0 + n 1) (PowerSeries.exp K) * (((n 0 + n 1).choose (n 0) : ℕ) : K) := by
    unfold Ex
    rw [PowerSeries.coeff_subst (powerSeries_hasSubst_of_constantCoeff_eq_zero hs)]
    simp_rw [coeff_X_zero_add_X_one_pow]
    rw [finsum_eq_single _ (n 0 + n 1)]
    · simp
    · intro d hd
      simp [hd]
  have hR : coeff n (Ex (X 0 : MvPowerSeries (Fin 2) K) * Ex (X 1)) =
      PowerSeries.coeff (n 0) (PowerSeries.exp K) * PowerSeries.coeff (n 1) (PowerSeries.exp K) := by
    change coeff n (diagS (PowerSeries.exp K) 0 * diagS (PowerSeries.exp K) 1) = _
    rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (n 0), Finsupp.single 1 (n 1))]
    · rw [coeff_diagS, coeff_diagS]
      simp
    · intro p hp hne
      replace hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [coeff_diagS, coeff_diagS]
      by_cases h1 : p.1 = Finsupp.single 0 (p.1 0)
      · by_cases h2 : p.2 = Finsupp.single 1 (p.2 1)
        · exfalso
          apply hne
          have e0 := congrArg (fun e => e 0) hp
          have e1 := congrArg (fun e => e 1) hp
          rw [h2] at e0
          rw [h1] at e1
          simp at e0 e1
          exact Prod.ext (h1.trans (congrArg (Finsupp.single 0) e0))
            (h2.trans (congrArg (Finsupp.single 1) e1))
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h
      exfalso
      apply h
      refine Finset.HasAntidiagonal.mem_antidiagonal.mpr ?_
      ext i
      fin_cases i <;> simp
  rw [hL, hR]
  simp only [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast]
  rw [Nat.cast_add_choose]
  have hne : ((n 0 + n 1).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  first
  | (rw [div_mul_div_comm, one_mul, div_mul_cancel_left₀ hne]; simp)
  | (field_simp; done)
  | (field_simp; rw [mul_inv_cancel₀ hne, one_mul])
  | (field_simp; simp [hne])
  all_goals first | ring | exact mul_comm _ _

theorem Ex_add {f g : MvPowerSeries ι K} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    Ex (f + g) = Ex f * Ex g := by
  have hc : HasSubst (![f, g] : Fin 2 → MvPowerSeries ι K) :=
    hasSubst_of_finite_constantCoeff_eq_zero (by intro i; fin_cases i <;> simp [hf, hg])
  have h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have key := congrArg (subst (![f, g] : Fin 2 → MvPowerSeries ι K)) (Ex_biv (K := K))
  rw [subst_Ex hc h01, MvPowerSeries.subst_mul hc, subst_Ex hc h0, subst_Ex hc h1,
    MvPowerSeries.subst_add hc, MvPowerSeries.subst_X hc, MvPowerSeries.subst_X hc] at key
  simpa using key

theorem Ex_neg_mul {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) : Ex (-f) * Ex f = 1 := by
  have hn : constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  rw [← Ex_add hn hf]
  simp [Ex_zero]

theorem coeff_Ex {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) (n : ι →₀ ℕ) :
    coeff n (Ex f) = ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K))⁻¹ * coeff n (f ^ k) := by
  exact coeff_Ex_eq_sum_inv_factorial_coeff_pow hf n

end Exp

section Int

variable {ι κ : Type} {K : Type} [Field K]

theorem exists_lift (O : Subring K) (A : MvPowerSeries ι K) (h : ∀ n, coeff n A ∈ O) :
    ∃ A' : MvPowerSeries ι O, map O.subtype A' = A := by
  refine ⟨fun n => ⟨coeff n A, h n⟩, ?_⟩
  ext n
  first
  | rfl
  | (erw [MvPowerSeries.coeff_map]; rfl)

private theorem finsum_mem_subring (O : Subring K) {α : Type} (F : α → K) (hF : ∀ x, F x ∈ O) :
    ∑ᶠ x, F x ∈ O := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_sum F hfin]
    exact Subring.sum_mem O (fun x _ => hF x)
  · rw [finsum_of_infinite_support hfin]
    exact O.zero_mem

private theorem mem_range_map_subring_iff {σ : Type} (O : Subring K) (F : MvPowerSeries σ K) :
    F ∈ (MvPowerSeries.map (σ := σ) O.subtype).range ↔ ∀ n, coeff n F ∈ O := by
  constructor
  · intro hF n
    obtain ⟨F', rfl⟩ := RingHom.mem_range.mp hF
    rw [MvPowerSeries.coeff_map]
    exact (coeff n F').2
  · intro hF
    obtain ⟨F', hF'⟩ := exists_lift O F hF
    exact RingHom.mem_range.mpr ⟨F', hF'⟩

private theorem coeff_subst_mem_subring {σ τ : Type} (O : Subring K) (A : MvPowerSeries σ K)
    (hA : ∀ n, coeff n A ∈ O) (c : σ → MvPowerSeries τ K) (hc : HasSubst c)
    (hcO : ∀ i n, coeff n (c i) ∈ O) : ∀ n, coeff n (subst c A) ∈ O := by
  intro e
  rw [MvPowerSeries.coeff_subst hc]
  apply finsum_mem_subring
  intro d
  simp only [smul_eq_mul]
  refine O.mul_mem (hA d) ?_
  have hmem : (d.prod fun s k => c s ^ k) ∈ (MvPowerSeries.map (σ := τ) O.subtype).range := by
    simp only [Finsupp.prod]
    apply Subring.prod_mem
    intro s _
    exact Subring.pow_mem _ ((mem_range_map_subring_iff O (c s)).mpr (hcO s)) _
  exact (mem_range_map_subring_iff O _).mp hmem e

theorem int_dg (O : Subring K) (a : PowerSeries K) (ha : ∀ n, PowerSeries.coeff n a ∈ O) (i : ι) (n : ι →₀ ℕ) :
    coeff n (diagS a i : MvPowerSeries ι K) ∈ O := by
  classical
  rw [coeff_diagS]
  split_ifs
  · exact ha _
  · exact O.zero_mem


theorem int_subst_dg (O : Subring K) (A : MvPowerSeries ι K) (hA : ∀ n, coeff n A ∈ O) (a : PowerSeries K)
    (ha0 : PowerSeries.constantCoeff a = 0) (ha : ∀ n, PowerSeries.coeff n a ∈ O) :
    ∀ n, coeff n (subst (diagS a) A) ∈ O := by
  exact coeff_subst_mem_subring O A hA (diagS a) (hs_dg ha0)
    (fun i n => int_dg O a ha i n)

theorem descent (O : Subring K) (th lg ps : PowerSeries K) (hth0 : PowerSeries.constantCoeff th = 0)
    (hps0 : PowerSeries.constantCoeff ps = 0) (hpsO : ∀ n, PowerSeries.coeff n ps ∈ O)
    (hinv : PowerSeries.subst ps th = PowerSeries.X) (hlg0 : PowerSeries.constantCoeff lg = 0)
    (G : MvPowerSeries ι K) (h : ∀ n, coeff n (subst (diagS (PowerSeries.subst th lg)) G) ∈ O) :
    ∀ n, coeff n (subst (diagS lg) G) ∈ O := by
  have hthlg : constantCoeff (PowerSeries.subst th lg) = 0 := constantCoeff_powerSeries_subst_eq_zero_admissible_parameter_joins hth0 hlg0
  have hcomp : PowerSeries.subst ps (PowerSeries.subst th lg) = lg := by
    have hu : HasSubst (fun _ : Unit => ps) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hps0)
    have h1 : PowerSeries.subst ps (PowerSeries.subst th lg) =
        PowerSeries.subst (PowerSeries.subst ps th) lg :=
      subst_psubst hu hth0 lg
    rw [h1, hinv]
    exact diagS_unit lg
  have key : subst (diagS ps) (subst (diagS (PowerSeries.subst th lg)) G) =
      subst (diagS lg) G := by
    rw [MvPowerSeries.subst_comp_subst_apply (hs_dg hthlg) (hs_dg hps0)]
    congr 1
    funext i
    rw [dg_comp hps0 i, hcomp]
  rw [← key]
  exact int_subst_dg O _ h ps hps0 hpsO

end Int

end Formalism.MainNotions.J
end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric

section Core

variable (p : ℕ) [Fact p.Prime]

instance : CharZero (WW p) := by
  obtain ⟨q, hq⟩ := CharP.exists (WW p)
  rcases CharP.char_is_prime_or_zero (WW p) q with h | h
  · exfalso
    have h0 : ((q : ℕ) : WW p) = 0 := CharP.cast_eq_zero (WW p) q
    have h1 : ((q : ℕ) : kb p) = 0 := by
      have := congrArg (WittVector.constantCoeff (p := p) (R := kb p)) h0
      rw [map_natCast, map_zero] at this
      exact this
    have h2 : p ∣ q := (CharP.cast_eq_zero_iff (kb p) p q).mp h1
    have h3 : p = q := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) h).mp h2
    have h4 : ((p : ℕ) : WW p) = ((q : ℕ) : WW p) := congrArg (Nat.cast) h3
    exact WittVector.p_nonzero p (kb p) (h4.trans h0)
  · subst h
    exact CharP.charP_to_charZero (WW p)

instance : CharZero (K0 p) := charZero_of_injective_algebraMap (IsFractionRing.injective (WW p) (K0 p))

theorem cc_pmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a : PowerSeries A}
    (ha : PowerSeries.constantCoeff a = 0) : PowerSeries.constantCoeff (PowerSeries.map f a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, ha, map_zero]

theorem expS_eq_Ex {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : constantCoeff f = 0) : expS p f = Ex f := by
  ext n
  rw [coeff_Ex hf]
  rfl

instance : CharZero ℂ_[p] := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ℂ_[p]).injective

theorem expMv_eq_Ex {ι : Type} {f : MvPowerSeries ι ℂ_[p]} (hf : constantCoeff f = 0) : expMv f = Ex f := by
  ext n
  rw [coeff_Ex hf]
  show ∑ k ∈ Finset.range ((n.sum fun _ k => k) + 1),
      MvPowerSeries.coeff n (f ^ k) / (k.factorial : ℂ_[p]) = _
  refine Finset.sum_congr (by rfl) fun k _ => ?_
  exact div_eq_inv_mul (MvPowerSeries.coeff n (f ^ k)) (k.factorial : ℂ_[p])

theorem pmap_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) (a : PowerSeries A) :
    PowerSeries.map g (PowerSeries.map f a) = PowerSeries.map (g.comp f) a := by
  ext n
  simp [PowerSeries.coeff_map]

theorem mmap_map {ι A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B)
    (a : MvPowerSeries ι A) : map g (map f a) = map (g.comp f) a := by
  ext n
  simp [MvPowerSeries.coeff_map]

theorem cc_logF : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF]

def PhS (ι : Type) [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 p)) : MvPowerSeries (ι ⊕ ι) (K0 p) :=
  ∑ e : ι, sub2 p be (X (Sum.inl e)) (X (Sum.inr e))

theorem hs2 {τ R : Type} [CommRing R] {a b : MvPowerSeries τ R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    HasSubst (![a, b] : Fin 2 → MvPowerSeries τ R) :=  by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [ha, hb]
  | exact ⟨fun i => by fin_cases i <;> simp [ha, hb], fun d => Set.toFinite _⟩

variable {p}

theorem K1core {ι : Type} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (Oc : Subring Kc)
    (witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) x) ∈ Oc)
    (iC : Kc →+* ℂ_[p]) (iC_int : ∀ x : Kc, x ∈ Oc ↔ ‖iC x‖ ≤ 1)
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (th_unit : IsUnit (PowerSeries.coeff 1 th))
    (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE)
    (Ph : MvPowerSeries ι (K0 p)) (hPh : constantCoeff Ph = 0) (Th : MvPowerSeries ι Kc)
    (hInt : IntegralMv (subst (diagS lgE) (map iC Th) *
      expMv (subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) Ph)))) :
    ∃ U : MvPowerSeries ι Kc, Th = map (algebraMap (K0 p) Kc) (expS p (-Ph)) * U ∧ IntR Oc (inParamK p Kc U) := by
  classical
  set φ : WW p →+* Kc := (algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)) with hφ
  set th' : PowerSeries Kc := PowerSeries.map φ th with hth'
  set lg : PowerSeries Kc := PowerSeries.map (algebraMap (K0 p) Kc) (logF p) with hlg
  have hth'0 : PowerSeries.constantCoeff th' = 0 := cc_pmap φ th_zero
  have hlg0 : PowerSeries.constantCoeff lg = 0 := cc_pmap _ (cc_logF p)
  set ps : PowerSeries (WW p) := th.substInvOfIsUnit th_unit with hps
  have hps0 : PowerSeries.constantCoeff ps = 0 := PowerSeries.constantCoeff_substInvOfIsUnit th th_unit
  have hinv0 : PowerSeries.subst ps th = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right th th_zero th_unit
  set ps' : PowerSeries Kc := PowerSeries.map φ ps with hps'
  have hps'0 : PowerSeries.constantCoeff ps' = 0 := cc_pmap φ hps0
  have hps'O : ∀ n, PowerSeries.coeff n ps' ∈ Oc := by
    intro n
    rw [hps', PowerSeries.coeff_map]
    exact witt_mem_integers_Cp _
  have hinv : PowerSeries.subst ps' th' = PowerSeries.X := by
    have h1 := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hps0) (h := φ) th
    rw [hinv0] at h1
    exact h1.symm.trans (PowerSeries.map_X φ)
  have hlgK0 : PowerSeries.constantCoeff (PowerSeries.subst th' lg) = 0 := by
    have hs : HasSubst (fun _ : Unit => th') := by
      first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero' hth'0
      | exact ⟨fun _ => by rw [show MvPowerSeries.constantCoeff th' = 0 from hth'0]; exact IsNilpotent.zero,
          fun d => Set.toFinite _⟩
    exact MvPowerSeries.constantCoeff_subst_eq_zero hs (fun _ => hth'0) hlg0
  have hlgE : PowerSeries.map iC (PowerSeries.subst th' lg) = lgE := by
    have h1 := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hth'0) (h := iC) lg
    refine h1.trans ?_
    rw [← th_log]
    show PowerSeries.subst (PowerSeries.map iC (PowerSeries.map φ th))
      (PowerSeries.map iC (PowerSeries.map (algebraMap (K0 p) Kc) (logF p))) = _
    rw [pmap_map, pmap_map]
  have hlgE0 : PowerSeries.constantCoeff lgE = 0 := by
    rw [← hlgE]
    exact cc_pmap iC hlgK0
  have hc : constantCoeff (map (iC.comp (algebraMap (K0 p) Kc)) Ph) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hPh, map_zero]
  have hc' := MvPowerSeries.constantCoeff_subst_eq_zero (hs_dg hlgE0) (cc_dg hlgE0) hc
  have hE : subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) (expS p Ph)) =
      expMv (subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) Ph)) := by
    rw [expS_eq_Ex p hPh, map_Ex _ hPh, subst_Ex (hs_dg hlgE0) hc, expMv_eq_Ex p hc']
  refine ⟨map (algebraMap (K0 p) Kc) (expS p Ph) * Th, ?_, ?_⟩
  · have hn : constantCoeff (-Ph) = 0 := by rw [map_neg, hPh, neg_zero]
    rw [← mul_assoc, ← map_mul, expS_eq_Ex p hn, expS_eq_Ex p hPh, Ex_neg_mul hPh, map_one, one_mul]
  · have hInt' : IntegralMv (subst (diagS lgE) (map iC (map (algebraMap (K0 p) Kc) (expS p Ph) * Th))) := by
      rw [map_mul, mmap_map, MvPowerSeries.subst_mul (hs_dg hlgE0), hE, mul_comm]
      exact hInt
    have key : map iC (subst (diagS (PowerSeries.subst th' lg))
        (map (algebraMap (K0 p) Kc) (expS p Ph) * Th)) =
        subst (diagS lgE) (map iC (map (algebraMap (K0 p) Kc) (expS p Ph) * Th)) := by
      rw [MvPowerSeries.map_subst (hs_dg hlgK0)]
      congr 1
      funext i
      rw [map_dg, hlgE]
    intro n
    refine descent Oc th' lg ps' hth'0 hps'0 hps'O hinv hlg0 _ (fun m => ?_) n
    rw [iC_int]
    have hm := hInt' m
    rw [← key, MvPowerSeries.coeff_map] at hm
    exact hm

end Core

end Formalism.MainNotions.J
end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem cc_l : PowerSeries.constantCoeff g.l = 0 := by
  unfold G1.l
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.TaylorLogMetric.flog, PowerSeries.coeff_mk, if_pos rfl]

private theorem cc_subst_lemma {R : Type} [CommRing R] {υ : Type} {a : MvPowerSeries υ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst hs]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  rcases d with _ | d
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_smul]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow (Nat.succ_ne_zero d), smul_zero]

private theorem comp_lemma_2 {υ ρ : Type} {R : Type} [CommRing R] {a : MvPowerSeries υ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {c : υ → MvPowerSeries ρ R} (hc : HasSubst c)
    (f : PowerSeries R) : subst c (PowerSeries.subst a f) = PowerSeries.subst (subst c a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hc]

theorem cc_lg {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) : constantCoeff (g.lg a) = 0 :=
  cc_subst_lemma ha (cc_l g)

theorem cc_pt (hex : PowerSeries.constantCoeff g.ex = 0) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) :
    constantCoeff (g.pt a) = 0 :=
  cc_subst_lemma ha hex

theorem lg_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.lg a) = g.lg (subst c a) :=
  comp_lemma_2 ha hc g.l

theorem pt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.pt a) = g.pt (subst c a) :=
  comp_lemma_2 ha hc g.ex

theorem phAt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.phAt a) = g.phAt (subst c a) :=
  comp_lemma_2 ha hc g.ph

theorem add_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.add a b) = g.add (subst c a) (subst c b) := by
  have h0 : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add, cc_lg g ha, cc_lg g hb, add_zero]
  show subst c (g.pt (g.lg a + g.lg b)) = g.pt (g.lg (subst c a) + g.lg (subst c b))
  rw [pt_subst g hc h0, ← coe_substAlgHom hc, map_add, coe_substAlgHom, lg_subst g hc ha, lg_subst g hc hb]

theorem cc_add (hex : PowerSeries.constantCoeff g.ex = 0) {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : constantCoeff (g.add a b) = 0 :=
  cc_pt g hex (by rw [map_add, cc_lg g ha, cc_lg g hb, add_zero])

theorem be_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.be a b) = g.be (subst c a) (subst c b) := by
  have hab := cc_add g hex ha hb
  show subst c (g.phAt (g.add a b) - g.phAt a - g.phAt b) =
    g.phAt (g.add (subst c a) (subst c b)) - g.phAt (subst c a) - g.phAt (subst c b)
  rw [← coe_substAlgHom hc, map_sub, map_sub, coe_substAlgHom, phAt_subst g hc hab, phAt_subst g hc ha,
    phAt_subst g hc hb, add_subst g hex hc ha hb]

theorem dg_Cmul (ep : ℂ_[p]) (i : σ) :
    (diagS (PowerSeries.C ep * g.l) i : MvPowerSeries σ ℂ_[p]) = C ep * g.lg (X i) := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries σ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)
  unfold diagS G1.lg
  rw [← PowerSeries.smul_eq_C_mul, ← smul_eq_C_mul, ← PowerSeries.coe_substAlgHom hX, map_smul]

theorem cc_Cl (ep : ℂ_[p]) : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
  rw [map_mul, cc_l g, mul_zero]

end G1

section Lin

variable {Z E Kap : Type} {R : Type} [CommRing R]

def IsLin [Fintype Z] (f : MvPowerSeries Z R) : Prop :=
  f = ∑ z, C (coeff (Finsupp.single z 1) f) * X z

theorem isLin_sum [Fintype Z] {α : Type} (s : Finset α) (f : α → MvPowerSeries Z R) (h : ∀ a ∈ s, IsLin (f a)) :
    IsLin (∑ a ∈ s, f a) := by
  unfold IsLin at *
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl h

end Lin

end Formalism.MainNotions.J
end
end
