import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsOfEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePow

section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.TraceTower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow (T : Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ (p ^ k) = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, pow_succ', pow_mul, T.ζpow, ih]

theorem qq_pow (T : Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ (p ^ k) = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, pow_succ', pow_mul, T.qpow, ih]

theorem zeta_pow' (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : T.ζ n ^ (p ^ (n - m)) = T.ζ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using zeta_pow T m k

theorem qq_pow' (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : T.qq n ^ (p ^ (n - m)) = T.qq m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using qq_pow T m k

theorem qq_pow_top (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  have := qq_pow' T (Nat.zero_le n)
  simpa [T.q0] using this

theorem lift_hom {R A S M : Type} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [Field S]
    [Algebra R S] [Algebra.IsAlgebraic R S] [Field M] [IsAlgClosed M]
    (hA : Function.Injective (algebraMap R A)) (ι : A →ₐ[R] S) (f : A →+* M)
    (hι : Function.Injective ι) (hf : Function.Injective f) :
    ∃ τ : S →+* M, ∀ x, τ (ι x) = f x := by
  letI : Algebra A S := ι.toRingHom.toAlgebra
  letI : Algebra A M := f.toAlgebra
  haveI : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  haveI : Algebra.IsAlgebraic A S := Algebra.IsAlgebraic.extendScalars (R := R) hA
  haveI : Module.IsTorsionFree A S := Module.isTorsionFree_iff_algebraMap_injective.2 hι
  haveI : Module.IsTorsionFree A M := Module.isTorsionFree_iff_algebraMap_injective.2 hf
  let L : S →ₐ[A] M := IsAlgClosed.lift
  exact ⟨L.toRingHom, fun x => L.commutes x⟩

theorem ext_aut (hΩ : IsClo p Ω) {A : Type} [CommRing A] [IsDomain A] [Algebra (O0 p) A]
    [Algebra.IsIntegral (O0 p) A] (ι f : A →ₐ[O0 p] Ω) :
    ∃ σ : Gal p Ω, ∀ x : A, σ (ι x) = f x := by
  haveI := hΩ.clo
  haveI := hΩ.alg
  haveI : IsDomain (O0 p) := hΩ.inj.isDomain _
  have hinj : ∀ g : A →ₐ[O0 p] Ω, Function.Injective g := by
    intro g
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := O0 p) ?_
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hr
    exact hΩ.inj (by rw [hr, map_zero])
  have hA : Function.Injective (algebraMap (O0 p) A) := by
    intro x y hxy
    apply hΩ.inj
    rw [← ι.commutes, ← ι.commutes, hxy]
  obtain ⟨τ, hτ⟩ := lift_hom hA ι f.toRingHom (hinj ι) (hinj f)
  let τ' : Ω →ₐ[O0 p] Ω :=
    { τ with
      commutes' := fun r => by
        show τ _ = _
        rw [← ι.commutes, hτ, ι.commutes]
        exact f.commutes r }
  haveI : Module.IsTorsionFree (O0 p) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hΩ.inj
  exact ⟨AlgEquiv.ofBijective τ' (Algebra.IsAlgebraic.algHom_bijective τ'), hτ⟩

open Polynomial in

theorem exists_hom (T : Tower p Ω) (n : ℕ) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ f : On p n →ₐ[O0 p] Ω, f (xn p n) = T.ζ n ^ a ∧ f (yn p n) = T.ζ n ^ b * T.qq n := by
  classical
  have hp := (Fact.out : p.Prime)
  have hcop : a.Coprime (p ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 ha))
  have hprim : IsPrimitiveRoot (T.ζ n ^ a) (p ^ n) := (T.prim n).pow_of_coprime a hcop
  let φ : Polynomial (Polynomial (O0 p)) →ₐ[O0 p] Ω :=
    aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n)
  have hle : towerIdeal p n ≤ RingHom.ker φ := by
    refine Ideal.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (C (cyclotomic (p ^ n) (O0 p))) = 0
      rw [aevalTower_C, aeval_def, ← eval_map, map_cyclotomic]
      exact hprim.isRoot_cyclotomic (pow_pos hp.pos n)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (X ^ (p ^ n) - C (C (qO p))) = 0
      rw [map_sub, map_pow, aevalTower_X, aevalTower_C, aeval_C, mul_pow, qq_pow_top, ← pow_mul,
        mul_comm b, pow_mul, (T.prim n).pow_eq_one, one_pow, one_mul, sub_self]
  let f0 : On p n →ₐ[O0 p] Ω := Ideal.Quotient.liftₐ (towerIdeal p n) φ (fun x hx => (RingHom.mem_ker).1 (hle hx))
  have hf0x : f0 (xn p n) = T.ζ n ^ a := by
    show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (C X) = _
    rw [aevalTower_C, aeval_X]
  have hf0y : f0 (yn p n) = T.ζ n ^ b * T.qq n := by
    show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) X = _
    rw [aevalTower_X]
  exact ⟨f0, hf0x, hf0y⟩

theorem exists_aut (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ σ : Gal p Ω, σ (T.ζ n) = T.ζ n ^ a ∧ σ (T.qq n) = T.ζ n ^ b * T.qq n := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨ι, hx, hy⟩ := exists_hom T n 1 0 hp.not_dvd_one
  obtain ⟨f, hfx, hfy⟩ := exists_hom T n a b ha
  obtain ⟨_, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  obtain ⟨B, -⟩ := GlobalTheory.K5.OnFree.on_free p n
  haveI : Module.Finite (O0 p) (On p n) := Module.Finite.of_basis B
  haveI : Algebra.IsIntegral (O0 p) (On p n) := Algebra.IsIntegral.of_finite (O0 p) (On p n)
  obtain ⟨σ, key⟩ := ext_aut hΩ ι f
  have k1 := key (xn p n)
  have k2 := key (yn p n)
  rw [hx, hfx, pow_one] at k1
  rw [hy, hfy, pow_zero, one_mul] at k2
  exact ⟨σ, k1, k2⟩


end GlobalTheory.K5.TraceTower
end
end

section
noncomputable section

namespace GlobalTheory.K5.Rel

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def IsGen (T : Tower p Ω) (m s : ℕ) (τ γ : Gal p Ω) : Prop :=
  (∀ n, τ (T.ζ n) = T.ζ n) ∧ (∀ n, τ (T.qq n) = T.ζ n ^ (p ^ s) * T.qq n) ∧
  (∀ n, γ (T.ζ n) = T.ζ n ^ (1 + p ^ m)) ∧ ∀ n, γ (T.qq n) = T.qq n

theorem gal_zeta (T : Tower p Ω) (g : Gal p Ω) (n : ℕ) : ∃ e : ℕ, g (T.ζ n) = T.ζ n ^ e := by
  obtain ⟨χ, h⟩ := Basic.exists_isCyc T n
  exact ⟨_, h g⟩

theorem gal_qq (T : Tower p Ω) (g : Gal p Ω) (n : ℕ) : ∃ e : ℕ, g (T.qq n) = T.ζ n ^ e * T.qq n := by
  obtain ⟨a, h⟩ := Basic.exists_isKum_qq T n
  exact ⟨_, h g trivial⟩

theorem conj_mem_Gn (T : Tower p Ω) (n : ℕ) (g : Gal p Ω) {u : Gal p Ω} (hu : u ∈ Gn T n) :
    g⁻¹ * u * g ∈ Gn T n := by
  obtain ⟨e, he⟩ := gal_zeta T g n
  obtain ⟨f, hf⟩ := gal_qq T g n
  have h1 : u (g (T.ζ n)) = g (T.ζ n) := by rw [he, map_pow, (mem_Gn.1 hu).1]
  have h2 : u (g (T.qq n)) = g (T.qq n) := by
    rw [hf, map_mul, map_pow, (mem_Gn.1 hu).1, (mem_Gn.1 hu).2]
  refine mem_Gn.2 ⟨?_, ?_⟩
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1]; exact g.symm_apply_apply _
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h2]; exact g.symm_apply_apply _


theorem conj_mem_Hinf (T : Tower p Ω) (g : Gal p Ω) {u : Gal p Ω} (hu : u ∈ Hinf T) :
    g⁻¹ * u * g ∈ Hinf T :=
  Subgroup.mem_iInf.2 fun n => conj_mem_Gn T n g (Hinf_le T n hu)








variable {T : Tower p Ω} {m s : ℕ} {τ γ : Gal p Ω}

theorem IsGen.tau_pow_zeta (h : IsGen T m s τ γ) (b n : ℕ) : (τ ^ b) (T.ζ n) = T.ζ n := by
  induction b with
  | zero => rfl
  | succ b ih => rw [pow_succ, AlgEquiv.mul_apply, h.1, ih]

theorem IsGen.tau_pow_qq (h : IsGen T m s τ γ) (b n : ℕ) :
    (τ ^ b) (T.qq n) = T.ζ n ^ (p ^ s * b) * T.qq n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, AlgEquiv.mul_apply, h.2.1, map_mul, map_pow, h.tau_pow_zeta, ih]; ring



theorem exists_aut_all (hΩ : IsClo p Ω) (T : Tower p Ω) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ g : Gal p Ω, ∀ n, g (T.ζ n) = T.ζ n ^ a ∧ g (T.qq n) = T.ζ n ^ b * T.qq n := by
  classical
  by_contra hcon
  push_neg at hcon
  choose lv hlv using hcon
  obtain ⟨F, hF⟩ := gal_finite_subcover p Ω hΩ (fun g => {T.ζ (lv g), T.qq (lv g)})
  obtain ⟨σ, h1, h2⟩ := TraceTower.exists_aut hΩ T (F.sup lv + 1) (by omega) a b ha
  obtain ⟨g, hg, hS⟩ := hF σ
  have hle : lv g ≤ F.sup lv + 1 := (Finset.le_sup hg).trans (Nat.le_succ _)
  have e1 : σ (T.ζ (lv g)) = T.ζ (lv g) ^ a := by
    rw [← TraceTower.zeta_pow' T hle, map_pow, h1, ← pow_mul, ← pow_mul, mul_comm]
  have e2 : σ (T.qq (lv g)) = T.ζ (lv g) ^ b * T.qq (lv g) := by
    rw [← TraceTower.zeta_pow' T hle, ← TraceTower.qq_pow' T hle, map_pow, h2, mul_pow, ← pow_mul,
      ← pow_mul, mul_comm b]
  exact hlv g (by rw [← hS _ (by simp), e1]) (by rw [← hS _ (by simp), e2])

end GlobalTheory.K5.Rel
end
end

section
noncomputable section

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog GlobalTheory.K5.Rel

theorem exists_pow_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m n i : ℕ} (hm : 1 ≤ m)
    (hi : ¬ p ^ (n - m) ∣ i) :
    m < n ∧ ∃ K d u : ℕ, ¬ p ∣ d ∧ ¬ p ∣ u ∧ i * (1 + p ^ m) ^ K = i + u * d * p ^ (n - 1) ∧
      ∃ w, (1 + p ^ m) ^ K = 1 + p * w := by
  have hp : p.Prime := Fact.out
  have hi0 : i ≠ 0 := by rintro rfl; exact hi (dvd_zero _)
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 p hp.ne_one
  have hv : v < n - m := by
    by_contra h
    push_neg at h
    exact hi (Dvd.dvd.mul_right (pow_dvd_pow p h) _)
  refine ⟨by omega, ?_⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpm : 0 < p ^ m := pow_pos hp.pos m
  have hlt : 1 < 1 + p ^ m := by omega
  have hnd : ¬ p ∣ 1 + p ^ m := fun h =>
    hp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h)
  have hval := padicValNat.pow_sub_pow (p := p) hodd (x := 1 + p ^ m) (y := 1) hlt
    (by rw [Nat.add_sub_cancel_left]; exact dvd_pow_self p (by omega)) hnd
    (n := p ^ (n - v - 1 - m)) (pow_ne_zero _ hp.ne_zero)
  rw [one_pow, Nat.add_sub_cancel_left, padicValNat.prime_pow, padicValNat.prime_pow] at hval
  have hK1 : 1 < (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) :=
    Nat.one_lt_pow (pow_ne_zero _ hp.ne_zero) hlt
  obtain ⟨e, d, hd, hed⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.sub_ne_zero_of_lt hK1) p
    hp.ne_one
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
  rw [hed, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hd0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hd, add_zero] at hval
  have hK : (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) = 1 + p ^ e * d := by omega
  refine ⟨p ^ (n - v - 1 - m), d, u, hd, hu, ?_, p ^ (e - 1) * d, ?_⟩
  · rw [hK, mul_add, mul_one, show n - 1 = v + e by omega, pow_add]
    ring
  · rw [hK, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]

end GlobalTheory.K5.MonX

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog GlobalTheory.K5.Rel

end GlobalTheory.K5.MonX

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog GlobalTheory.K5.Rel

end GlobalTheory.K5.MonX
end
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.TateInv

theorem sub_one_mul_sum {R : Type*} [CommRing R] (ω : R) (n : ℕ) :
    (ω - 1) * ∑ s ∈ Finset.range n, (s : R) * ω ^ s = n * ω ^ n - ω * ∑ s ∈ Finset.range n, ω ^ s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem sub_one_mul_sum_eq {Ω : Type*} [Field Ω] (ω : Ω) (p : ℕ) (h1 : ω ≠ 1) (hp : ω ^ p = 1) :
    (ω - 1) * ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s = p := by
  rw [sub_one_mul_sum, hp, geom_sum_eq h1, hp, sub_self, zero_div, mul_zero, sub_zero, mul_one]

theorem pow_apply_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t i : ℕ) : (γ ^ t) (ζ ^ i) = ζ ^ (i * a ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hγ, ← pow_mul, pow_succ]
    congr 1; ring

theorem pow_apply_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t : ℕ) {x : Ω} (hx : x ∈ Subring.closure {ζ}) : (γ ^ t) x ∈ Subring.closure {ζ} := by
  have h : Subring.closure {ζ} ≤ (Subring.closure {ζ}).comap ((γ ^ t : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω) := by
    rw [Subring.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy, SetLike.mem_coe, Subring.mem_comap]
    have := pow_apply_pow γ ζ a hγ t 1
    simp only [pow_one, one_mul] at this
    show (γ ^ t) ζ ∈ _
    rw [this]
    exact Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  exact h hx

theorem mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m)) (i : ℕ)
    (hi : ¬ p ^ (L - m) ∣ i) :
    ∃ H ∈ Subring.closure {ζ}, (p : Ω) * ζ ^ i = γ H - H := by
  have hp : p.Prime := hpf.out
  obtain ⟨hmL, K, d, u, hd, hu, he, -⟩ := GlobalTheory.K5.MonX.exists_pow_eq hp2 hm1 hi
  have hpL : p ^ L = p ^ (L - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hpm : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  set ω := ζ ^ (u * d * p ^ (L - 1)) with hω
  have hω1 : ω ≠ 1 := by
    rw [hω, Ne, hζ.pow_eq_one_iff_dvd, hpL]
    intro h
    have h' : p ^ (L - 1) * p ∣ p ^ (L - 1) * (u * d) := by rwa [mul_comm (p ^ (L - 1)) (u * d)]
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h'
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact hu h
    · exact hd h
  have hωp : ω ^ p = 1 := by
    rw [hω, ← pow_mul, hζ.pow_eq_one_iff_dvd]
    exact ⟨u * d, by rw [hpL]; ring⟩
  have hγω : γ ω = ω := by
    rw [hω, map_pow, hγ, ← pow_mul]
    have e : (1 + p ^ m) * (u * d * p ^ (L - 1)) = u * d * p ^ (L - 1) + p ^ L * (u * d * p ^ (m - 1)) := by
      rw [hpL, hpm]; ring
    rw [e, pow_add, pow_mul ζ (p ^ L), hζ.pow_eq_one, one_pow, mul_one]
  have hγtω : ∀ t : ℕ, (γ ^ t) ω = ω := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hγω]
  set S : Ω := ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s with hS
  have hγtS : ∀ t : ℕ, (γ ^ t) S = S := by
    intro t
    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_mul, map_natCast, map_pow, hγtω]
  have hK : (γ ^ K) (ζ ^ i) = ω * ζ ^ i := by
    rw [pow_apply_pow γ ζ _ hγ, he, pow_add, hω, mul_comm]
  have hωmem : ω ∈ Subring.closure {ζ} := Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  have hSmem : S ∈ Subring.closure {ζ} :=
    Subring.sum_mem _ fun s _ => Subring.mul_mem _ (natCast_mem _ s) (Subring.pow_mem _ hωmem _)
  have hH0 : S * ζ ^ i ∈ Subring.closure {ζ} :=
    Subring.mul_mem _ hSmem (Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _)
  refine ⟨∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i),
    Subring.sum_mem _ fun t _ => pow_apply_mem γ ζ _ hγ t hH0, ?_⟩
  have hγH : γ (∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i)) = ∑ t ∈ Finset.range K, (γ ^ (t + 1)) (S * ζ ^ i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [pow_succ', AlgEquiv.mul_apply]
  rw [hγH, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (γ ^ t) (S * ζ ^ i)), pow_zero,
    AlgEquiv.one_apply, map_mul, hγtS, hK]
  have := sub_one_mul_sum_eq ω p hω1 hωp
  rw [← hS] at this
  linear_combination (-(ζ ^ i)) * this

open Classical in

theorem trace_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * (if p ^ (L - m) ∣ i then ζ ^ i else 0) := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := GlobalTheory.NTr.sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  split_ifs with hd
  · have h1 : (ζ ^ p ^ m) ^ i = 1 := by
      obtain ⟨j, hj⟩ := hd
      rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]

open Classical in

theorem key_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (ζ ^ i - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  rw [trace_mono p L m hm1 hm ζ hζ τ hτ i]
  split_ifs with hd
  · exact ⟨0, Subring.zero_mem _, ζ ^ i, by simp, rfl⟩
  · obtain ⟨H, hH, e⟩ := mono p hp2 L m hm1 ζ hζ γ hγ i hd
    exact ⟨H, hH, 0, by rw [sub_zero, e], rfl⟩

open Classical in

theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val)
    (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (y - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact key_mono p hp2 L m hm1 hm ζ hζ γ hγ τ hτ (Multiplicative.toAdd i)
  | zero => exact ⟨0, Subring.zero_mem _, 0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    obtain ⟨H2, h2, z2, e2, f2⟩ := hy
    exact ⟨H1 + H2, Subring.add_mem _ h1 h2, z1 + z2, by rw [map_add]; linear_combination e1 + e2,
      by simp only [map_add, Finset.sum_add_distrib, f1, f2]; ring⟩
  | neg x _ hx =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    exact ⟨-H1, Subring.neg_mem _ h1, -z1, by rw [map_neg]; linear_combination -e1,
      by simp only [map_neg, Finset.sum_neg_distrib, f1]; ring⟩

theorem tate_inv : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F F' : Ω, InZl ε p L F → IsNT ε p L m F F' →
  ∀ γ : Ω ≃ₐ[ℚ] Ω, γ (zt ε p L) = zt ε p L ^ (1 + p ^ m) → ∃ H : Ω, InZl ε p L H ∧ (p : Ω) ^ c * (F - F') = γ H - H := by
  intro p hpf hp2
  refine ⟨1, ?_⟩
  intro Ω _ _ _ ε L m hm1 hmL F F' hF hNT γ hγ
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := GlobalTheory.NTr.zt_prim ε p L hp.pos
  obtain ⟨D, hD, hDF⟩ := hF
  obtain ⟨τ, hτ, hT⟩ := hNT
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨H, hH, z, e1, e2⟩ := key p hp2 L m hm1 hmL (zt ε p L) hζ γ hγ τ hτ _ hDF
  have hz : z = D * F' := by
    apply mul_left_cancel₀ hpN
    rw [← e2]
    simp only [map_mul, map_natCast, ← Finset.mul_sum]
    rw [← hT]; ring
  refine ⟨H / D, ⟨D, hD, by rwa [mul_div_cancel₀ _ hD0]⟩, ?_⟩
  rw [map_div₀, map_natCast, pow_one, ← sub_div, ← e1, hz, eq_div_iff hD0]
  ring

end GlobalTheory.TateInv
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.LamEq

theorem pow_prime_step (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) (t : ℤ) :
    (p : ℤ) ^ (2 * n + 1) ∣ (1 + (p : ℤ) ^ n * t) ^ p - 1 - (p : ℤ) ^ (n + 1) * t := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  set P : ℤ := ((q + 2 : ℕ) : ℤ) with hP
  have hexp : (1 + P ^ n * t) ^ (q + 2) =
      ∑ i ∈ Finset.range (q + 1), (P ^ n * t) ^ (i + 2) * ((q + 2).choose (i + 2) : ℤ) + (q + 2 : ℕ) * (P ^ n * t) + 1 := by
    rw [add_comm (1 : ℤ), add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_one]
    push_cast; ring
  rw [hexp]
  have hPP : (q + 2 : ℕ) * (P ^ n * t) = P ^ (n + 1) * t := by rw [hP]; ring
  rw [hPP, show ∀ a b : ℤ, a + b + 1 - 1 - b = a from fun a b => by ring]
  apply Finset.dvd_sum
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hc : ((q + 2 : ℕ) : ℤ) ∣ ((q + 2).choose 2 : ℤ) := by
      exact_mod_cast hp.dvd_choose_self (by norm_num) (by omega)
    rw [← hP] at hc
    obtain ⟨c, hc⟩ := hc
    exact ⟨t ^ 2 * c, by rw [hc]; ring⟩
  · have h3 : 2 * n + 1 ≤ n * (i + 2) := by nlinarith
    refine Dvd.dvd.mul_right ?_ _
    rw [mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ h3) _

theorem pow_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (j n : ℕ), 1 ≤ n → ∀ t : ℤ,
      (p : ℤ) ^ (2 * n + j) ∣ (1 + (p : ℤ) ^ n * t) ^ (p ^ j) - 1 - (p : ℤ) ^ (n + j) * t := by
  intro j
  induction j with
  | zero => intro n _ t; simp
  | succ j ih =>
    intro n hn t
    obtain ⟨w, hw⟩ := pow_prime_step p hp hp2 n hn t
    have h1 : (1 + (p : ℤ) ^ n * t) ^ p = 1 + (p : ℤ) ^ (n + 1) * (t + (p : ℤ) ^ n * w) := by
      linear_combination hw + (0 : ℤ) * w
    obtain ⟨w', hw'⟩ := ih (n + 1) (by omega) (t + (p : ℤ) ^ n * w)
    rw [pow_succ', pow_mul, h1]
    refine ⟨(p : ℤ) * w' + w, ?_⟩
    linear_combination hw'
end GlobalTheory.LamEq

namespace GlobalTheory.LamEq

theorem aut_pow_apply {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (z : Ω) (c : ℕ) (hc : s z = z ^ c) :
    ∀ k : ℕ, (s ^ k) z = z ^ (c ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hc, map_pow, ih, ← pow_mul, pow_succ]

theorem lam_eq : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ s : Ω ≃ₐ[ℚ] Ω, s (zt ε p m) = zt ε p m →
  ∀ tt tt' : ZMod (p ^ n), IsLamG ε p n m s tt → (s ^ (p ^ (L - m))) (zt ε p (L + n)) = zt ε p n ^ tt'.val * zt ε p (L + n) → tt = tt' := by
  intro Ω _ _ _ ε p hpf hp2 L n m hm1 hmn hnL s _ tt tt' hlam hL
  have hp : p.Prime := hpf.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨e, rfl⟩ : ∃ e, L = n + e := ⟨L - n, by omega⟩
  set z := zt ε p (n + e + n) with hzdef
  have hz : IsPrimitiveRoot z (p ^ (n + e + n)) := IsNTr.isPrimitiveRoot_zt ε p _
  obtain ⟨c, -, hc⟩ := hz.eq_pow_of_pow_eq_one (ξ := s z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  have hs := aut_pow_apply s z c hc.symm
  have h2n : zt ε p (2 * n) = z ^ (p ^ e) := by
    rw [hzdef, ← IsNTr.zt_pow ε p (2 * n) e]; congr 2; omega
  have hn : zt ε p n = z ^ (p ^ (n + e)) := by
    rw [hzdef, ← IsNTr.zt_pow ε p n (n + e)]; congr 2; omega

  have E1 : z ^ (c ^ (p ^ (n - m)) * p ^ e) = z ^ (p ^ (n + e) * tt.val + p ^ e) := by
    have := hlam
    unfold IsLamG at this
    change (s ^ (p ^ (n - m))) (zt ε p (2 * n)) = zt ε p n ^ tt.val * zt ε p (2 * n) at this
    rw [h2n, hn, map_pow, hs, ← pow_mul, ← pow_mul, ← pow_add] at this
    exact this
  have E2 : z ^ (c ^ (p ^ (n + e - m))) = z ^ (p ^ (n + e) * tt'.val + 1) := by
    rw [← hs, hL, hn, ← pow_mul, pow_succ]
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, hz.pow_eq_one⟩
  have hmod : ∀ a b : ℕ, z ^ a = z ^ b ↔ a ≡ b [MOD p ^ (n + e + n)] := by
    intro a b; rw [hz.eq_orderOf]; exact hfin.pow_eq_pow_iff_modEq
  rw [hmod, Nat.modEq_iff_dvd] at E1 E2
  obtain ⟨w1, hw1⟩ := E1
  obtain ⟨w3, hw3⟩ := E2
  push_cast at hw1 hw3
  set P : ℤ := (p : ℤ) with hP
  have hP0 : P ≠ 0 := by rw [hP]; exact_mod_cast hp.ne_zero
  set a : ℤ := (c : ℤ) ^ (p ^ (n - m)) with ha
  set v : ℤ := ((tt.val : ℕ) : ℤ)
  set v' : ℤ := ((tt'.val : ℕ) : ℤ)
  have h1 : a = 1 + P ^ n * (v - P ^ n * w1) := by
    apply mul_left_cancel₀ (pow_ne_zero e hP0)
    linear_combination (-1 : ℤ) * hw1
  obtain ⟨w2, hw2⟩ := pow_prime_pow p hp hp2 e n (by omega) (v - P ^ n * w1)
  rw [← h1, ← hP] at hw2
  have hce : (c : ℤ) ^ (p ^ (n + e - m)) = a ^ (p ^ e) := by
    rw [ha, ← pow_mul, ← pow_add]; congr 2; omega
  rw [hce] at hw3
  have hd : v' - v = P ^ n * (w3 - w1 + w2) := by
    apply mul_left_cancel₀ (pow_ne_zero (n + e) hP0)
    linear_combination hw3 + hw2
  have hv : ((v : ℤ) : ZMod (p ^ n)) = ((v' : ℤ) : ZMod (p ^ n)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ⟨w3 - w1 + w2, by push_cast; rw [hd]⟩
  simpa [v, v', ZMod.natCast_zmod_val] using hv

end GlobalTheory.LamEq

example : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ s : Ω ≃ₐ[ℚ] Ω, s (zt ε p m) = zt ε p m →
  ∀ tt tt' : ZMod (p ^ n), IsLamG ε p n m s tt → (s ^ (p ^ (L - m))) (zt ε p (L + n)) = zt ε p n ^ tt'.val * zt ε p (L + n) → tt = tt' :=
  GlobalTheory.LamEq.lam_eq
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.CorShap

section Cg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ}

theorem nat_mem (k : ℕ) : (k : Ω) ∈ A := by simpa using A.toSubring.natCast_mem k

theorem int_mem (k : ℤ) : (k : Ω) ∈ A := by simpa using A.toSubring.intCast_mem k

theorem cg_refl (x : Ω) : CgA A l n x x := ⟨0, A.zero_mem, by simp⟩

theorem cg_symm {x y : Ω} (h : CgA A l n x y) : CgA A l n y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, neg_mem hz, by rw [mul_neg, ← e]; ring⟩

theorem cg_trans {x y w : Ω} (h1 : CgA A l n x y) (h2 : CgA A l n y w) : CgA A l n x w := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, add_mem ha hb, by rw [mul_add, ← e1, ← e2]; ring⟩

theorem cg_add {x y x' y' : Ω} (h1 : CgA A l n x y) (h2 : CgA A l n x' y') : CgA A l n (x + x') (y + y') := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, add_mem ha hb, by rw [mul_add, ← e1, ← e2]; ring⟩

theorem cg_sub {x y x' y' : Ω} (h1 : CgA A l n x y) (h2 : CgA A l n x' y') : CgA A l n (x - x') (y - y') := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a - b, sub_mem ha hb, by rw [mul_sub, ← e1, ← e2]; ring⟩

theorem cg_mul {x y : Ω} (c : Ω) (hc : c ∈ A) (h : CgA A l n x y) : CgA A l n (c * x) (c * y) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨c * a, mul_mem hc ha, by rw [← mul_sub, e]; ring⟩

theorem cg_congr {x y x' y' : Ω} (h : CgA A l n x y) (hx : x = x') (hy : y = y') : CgA A l n x' y' := hx ▸ hy ▸ h

theorem cg_sum {ι : Type*} (s : Finset ι) (f g : ι → Ω) (h : ∀ i ∈ s, CgA A l n (f i) (g i)) :
    CgA A l n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using cg_refl (A := A) (l := l) (n := n) (0 : Ω)
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact cg_add (h a (Finset.mem_cons_self a s)) (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

theorem cg_map {s : Ω ≃ₐ[ℚ] Ω} (hs : Stab A s) {x y : Ω} (h : CgA A l n x y) : CgA A l n (s x) (s y) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨s a, (hs a).2 ha, by rw [← map_sub, e, map_mul, map_pow, map_natCast]⟩

theorem cg_nat {a b : ℕ} (h : (a : ZMod (l ^ n)) = b) : CgA A l n (a : Ω) (b : Ω) := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  refine ⟨((a / l ^ n : ℕ) : Ω) - ((b / l ^ n : ℕ) : Ω), sub_mem (nat_mem _) (nat_mem _), ?_⟩
  have e1 : (a : Ω) = ((a % l ^ n : ℕ) : Ω) + (l : Ω) ^ n * ((a / l ^ n : ℕ) : Ω) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  have e2 : (b : Ω) = ((b % l ^ n : ℕ) : Ω) + (l : Ω) ^ n * ((b / l ^ n : ℕ) : Ω) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  rw [e1, e2, h]; ring

end Cg

theorem stab_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {s t : Ω ≃ₐ[ℚ] Ω} (hs : Stab A s)
    (ht : Stab A t) : Stab A (s * t) := fun x => by rw [AlgEquiv.mul_apply, hs, ht]

theorem stab_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {s : Ω ≃ₐ[ℚ] Ω} (hs : Stab A s) :
    Stab A s⁻¹ := fun x => by
  rw [← hs (s⁻¹ x), ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem stab_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {s : Ω ≃ₐ[ℚ] Ω} (hs : Stab A s) (k : ℕ) :
    Stab A (s ^ k) := by
  induction k with
  | zero => intro x; simp
  | succ k ih => rw [pow_succ]; exact stab_mul ih hs

theorem mem_of_inZl {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (hp : ((p : ℕ) : Ω) ∈ A.nonunits) (L : ℕ) (F : Ω) (hF : InZl ε p L F) : F ∈ A := by
  have hpp : p.Prime := Fact.out
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hζ := IsNTr.isPrimitiveRoot_zt ε p L
  have hN : 0 < p ^ L := pow_pos hpp.pos L
  have hz : zt ε p L ∈ A := by
    rcases A.mem_or_inv_mem (zt ε p L) with h | h
    · exact h
    · have e : zt ε p L = (zt ε p L)⁻¹ ^ (p ^ L - 1) := by
        rw [inv_pow]; apply eq_inv_of_mul_eq_one_left; rw [← pow_succ', Nat.sub_add_cancel hN, hζ.pow_eq_one]
      rw [e]; exact pow_mem h _
  obtain ⟨D, hD, hDF⟩ := hF
  have hcl : (D : Ω) * F ∈ A :=
    (Subring.closure_le (t := A.toSubring)).2 (Set.singleton_subset_iff.2 hz) hDF
  have hcop : IsCoprime (D : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hD).symm
  obtain ⟨u, v, huv⟩ := hcop
  have e : (u : Ω) * D + v * p = 1 := by exact_mod_cast congrArg (fun x : ℤ => (x : Ω)) huv
  have hv : A.valuation (D : Ω) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).2 (nat_mem D)) ?_
    by_contra hlt
    push_neg at hlt
    have hp1 : A.valuation (p : Ω) < 1 := A.mem_nonunits_iff.1 hp
    have hu1 : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (int_mem u)
    have hv1 : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (int_mem v)
    have h1 : A.valuation ((u : Ω) * D + v * p) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hu1) hlt
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hv1) hp1
    rw [e, map_one] at h1
    exact lt_irrefl _ h1
  have hD0 : (D : Ω) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hDi : (D : Ω)⁻¹ ∈ A := (A.valuation_le_one_iff _).1 (by rw [map_inv₀, hv, inv_one])
  have := mul_mem hDi hcl
  rwa [inv_mul_cancel_left₀ hD0] at this

section Lev

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem lc_exists (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (M : ℕ) :
    ∃ e : (Ω ≃ₐ[ℚ] Ω) → ZMod (p ^ M), ∀ g, g (zt ε p M) = zt ε p M ^ (e g).val := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hζ := IsNTr.isPrimitiveRoot_zt ε p M
  have : ∀ g : Ω ≃ₐ[ℚ] Ω, ∃ t : ZMod (p ^ M), g (zt ε p M) = zt ε p M ^ t.val := fun g => by
    obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one (ξ := g (zt ε p M)) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, by rw [ZMod.val_natCast_of_lt hi, he]⟩
  exact ⟨fun g => (this g).choose, fun g => (this g).choose_spec⟩

theorem lc_mul (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (M : ℕ) (e : (Ω ≃ₐ[ℚ] Ω) → ZMod (p ^ M))
    (he : ∀ g, g (zt ε p M) = zt ε p M ^ (e g).val) (s t : Ω ≃ₐ[ℚ] Ω) : e (s * t) = e s * e t := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hζ := IsNTr.isPrimitiveRoot_zt ε p M
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← he, AlgEquiv.mul_apply, he t, map_pow, he s, GlobalTheory.K4.TopW.pow_val_mul hζ, ← pow_mul, ← pow_mul, mul_comm]

theorem lc_one (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (M : ℕ) (hM : 1 ≤ M) (e : (Ω ≃ₐ[ℚ] Ω) → ZMod (p ^ M))
    (he : ∀ g, g (zt ε p M) = zt ε p M ^ (e g).val) : e 1 = 1 := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  haveI : Fact (1 < p ^ M) := ⟨Nat.one_lt_pow (by omega) hpp.one_lt⟩
  have hζ := IsNTr.isPrimitiveRoot_zt ε p M
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← he, AlgEquiv.one_apply, ZMod.val_one, pow_one]

theorem fix_iff (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ) (hmL : m ≤ L) (g : Ω ≃ₐ[ℚ] Ω) (t : ZMod (p ^ L))
    (hg : g (zt ε p L) = zt ε p L ^ t.val) : g (zt ε p m) = zt ε p m ↔ t.val ≡ 1 [MOD p ^ m] := by
  have hζm := IsNTr.isPrimitiveRoot_zt ε p m
  have hz : zt ε p L ^ p ^ (L - m) = zt ε p m := by
    have := IsNTr.zt_pow ε p m (L - m); rwa [Nat.add_sub_cancel' hmL] at this
  have e : g (zt ε p m) = zt ε p m ^ t.val := by
    rw [← hz, map_pow, hg, ← pow_mul, ← pow_mul, mul_comm]
  have hpos : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  have h1 : ∀ a, zt ε p m ^ a = zt ε p m ^ (a % p ^ m) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a (p ^ m), pow_add, pow_mul, hζm.pow_eq_one, one_pow, mul_one]
  rw [e]
  nth_rewrite 2 [← pow_one (zt ε p m)]
  rw [h1 t.val, h1 1]
  exact ⟨fun h => hζm.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h, fun h => by rw [show t.val % p ^ m = 1 % p ^ m from h]⟩

end Lev

theorem pows_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm : 1 ≤ m) (hmL : m ≤ L) (u : (ZMod (p ^ L))ˣ)
    (hu : (u : ZMod (p ^ L)) = 1 + (p : ZMod (p ^ L)) ^ m) :
    orderOf u = p ^ (L - m) ∧ (Finset.range (p ^ (L - m))).image (fun k => u ^ k) =
      Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]) := by
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hord : orderOf u = p ^ (L - m) := by
    rw [← orderOf_units, hu]
    have h := ZMod.orderOf_one_add_mul_prime_pow hpp m (by omega) (by nlinarith) 1
      (by exact_mod_cast hpp.not_dvd_one) (L - m)
    rw [Nat.sub_add_cancel hmL, Int.cast_one, mul_one] at h
    exact h
  refine ⟨hord, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hd : p ^ m ∣ p ^ L := pow_dvd_pow p hmL
    have h1 : (((u ^ k : (ZMod (p ^ L))ˣ) : ZMod (p ^ L)).val : ZMod (p ^ m)) = ((1 : ℕ) : ZMod (p ^ m)) := by
      rw [← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := hd), Units.val_pow_eq_pow_val, map_pow, hu, map_add, map_one,
        map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, add_zero, one_pow, Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  · rw [Finset.card_image_of_injOn, Finset.card_range, IsNTr.card_filter p L m hm hmL]
    intro a ha b hb hab
    have := (pow_inj_mod (x := u)).1 hab
    rwa [hord, Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at this

theorem sum_shift {M : Type*} [AddCommMonoid M] (N j : ℕ) (hj : j < N) (f : ℕ → M) :
    ∑ k ∈ Finset.range N, f ((k + N - j) % N) = ∑ k ∈ Finset.range N, f k := by
  have key1 : ∀ k < N, (k + N - j) % N = if j ≤ k then k - j else k + N - j := fun k hk => by
    split_ifs with h
    · rw [show k + N - j = (k - j) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have key2 : ∀ k < N, (k + j) % N = if k + j < N then k + j else k + j - N := fun k hk => by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · conv_lhs => rw [show k + j = (k + j - N) + N by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  apply Finset.sum_nbij' (fun k => (k + N - j) % N) (fun k => (k + j) % N)
  · intro k _; simpa using Nat.mod_lt _ (show 0 < N by omega)
  · intro k _; simpa using Nat.mod_lt _ (show 0 < N by omega)
  · intro k hk
    replace hk : k < N := by simpa using hk
    rw [key1 k hk]
    split_ifs with h
    · rw [key2 _ (by omega)]; split_ifs <;> omega
    · rw [key2 _ (by omega)]; split_ifs <;> omega
  · intro k hk
    replace hk : k < N := by simpa using hk
    rw [key2 k hk]
    split_ifs with h
    · rw [key1 _ (by omega)]; split_ifs <;> omega
    · rw [key1 _ (by omega)]; split_ifs <;> omega
  · intro k _; rfl

section Tt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def Tt (ε : Ω →+* ℂ) (p L n : ℕ) (g : Ω ≃ₐ[ℚ] Ω) (t : ZMod (p ^ n)) : Prop :=
  g (zt ε p (L + n)) = zt ε p n ^ t.val * zt ε p (L + n)

variable {ε : Ω →+* ℂ} {p : ℕ} [Fact p.Prime] {L n : ℕ}

theorem fix_le {a b : ℕ} (h : a ≤ b) {g : Ω ≃ₐ[ℚ] Ω} (hg : g (zt ε p b) = zt ε p b) : g (zt ε p a) = zt ε p a := by
  have hz := IsNTr.zt_pow ε p a (b - a)
  rw [Nat.add_sub_cancel' h] at hz
  rw [← hz, map_pow, hg]

omit [IsAlgClosure ℚ Ω] in
theorem fix_pow {x : Ω} {g : Ω ≃ₐ[ℚ] Ω} (hg : g x = x) (k : ℕ) : (g ^ k) x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hg, ih]

theorem tt_exists {g : Ω ≃ₐ[ℚ] Ω} (hg : g (zt ε p L) = zt ε p L) : ∃ t, Tt ε p L n g t := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hζ := IsNTr.isPrimitiveRoot_zt ε p (L + n)
  have h0 : zt ε p (L + n) ≠ 0 := hζ.ne_zero (pow_ne_zero _ hpp.ne_zero)
  have h1 : (g (zt ε p (L + n)) / zt ε p (L + n)) ^ p ^ n = 1 := by
    rw [div_pow, ← map_pow, IsNTr.zt_pow, hg,
      div_self ((IsNTr.isPrimitiveRoot_zt ε p L).ne_zero (pow_ne_zero _ hpp.ne_zero))]
  obtain ⟨i, hi, he⟩ := (IsNTr.isPrimitiveRoot_zt ε p n).eq_pow_of_pow_eq_one h1
  exact ⟨i, by rw [Tt, ZMod.val_natCast_of_lt hi, he, div_mul_cancel₀ _ h0]⟩

theorem tt_mul {g h : Ω ≃ₐ[ℚ] Ω} {t t' : ZMod (p ^ n)} (hg : g (zt ε p n) = zt ε p n) (h1 : Tt ε p L n g t)
    (h2 : Tt ε p L n h t') : Tt ε p L n (g * h) (t + t') := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold Tt at *
  rw [AlgEquiv.mul_apply, h2, map_mul, map_pow, hg, h1, GlobalTheory.K4.TopW.pow_val_add (IsNTr.isPrimitiveRoot_zt ε p n)]
  ring

theorem tt_pow {g : Ω ≃ₐ[ℚ] Ω} {t : ZMod (p ^ n)} (hg : g (zt ε p n) = zt ε p n) (h1 : Tt ε p L n g t) (k : ℕ) :
    Tt ε p L n (g ^ k) ((k : ZMod (p ^ n)) * t) := by
  induction k with
  | zero => simp [Tt]
  | succ k ih =>
    have := tt_mul (fix_pow hg k) ih h1
    rwa [pow_succ, Nat.cast_succ, add_mul, one_mul]

theorem tt_transfer (hL : 1 ≤ L) (hnL : n ≤ L) (g s : Ω ≃ₐ[ℚ] Ω) (N j : ℕ) (ta tb : ZMod (p ^ n))
    (ha : ((g ^ j)⁻¹ * s) (zt ε p L) = zt ε p L) (hb : (g ^ N) (zt ε p L) = zt ε p L)
    (hta : Tt ε p L n ((g ^ j)⁻¹ * s) ta) (htb : Tt ε p L n (g ^ N) tb) :
    (∀ k k', k' + j = k → Tt ε p L n ((g ^ k)⁻¹ * s * g ^ k') ta) ∧
    (∀ k k', k' + j = k + N → Tt ε p L n ((g ^ k)⁻¹ * s * g ^ k') (ta + tb)) ∧
    Tt ε p L n (s ^ N) (N * ta + j * tb) := by
  obtain ⟨e, he⟩ := lc_exists ε p (L + n)
  let E : (Ω ≃ₐ[ℚ] Ω) →* ZMod (p ^ (L + n)) :=
    { toFun := e, map_one' := lc_one ε p _ (by omega) e he, map_mul' := lc_mul ε p _ e he }
  have tr : ∀ (x y : Ω ≃ₐ[ℚ] Ω) t, E.toHomUnits x = E.toHomUnits y → Tt ε p L n y t → Tt ε p L n x t := by
    intro x y t hxy h
    have : e x = e y := congrArg Units.val hxy
    unfold Tt at *
    rw [← h, he x, he y, this]
  generalize E.toHomUnits = φ at tr
  have ha' := fix_le hnL ha
  refine ⟨fun k k' hk => tr _ _ _ ?_ hta, fun k k' hk => tr _ _ _ ?_ (tt_mul ha' hta htb),
    tr _ _ _ ?_ (tt_mul (fix_pow ha' N) (tt_pow ha' hta N) (tt_pow (fix_le hnL hb) htb j))⟩
  · subst hk
    simp only [map_mul, map_inv, map_pow, pow_add, mul_inv]
    generalize φ g ^ k' = x
    rw [mul_right_comm, mul_right_comm x⁻¹, inv_mul_cancel, one_mul]
  · simp only [map_mul, map_inv, map_pow]
    have h : φ g ^ k' * φ g ^ j = φ g ^ k * φ g ^ N := by rw [← pow_add, ← pow_add, hk]
    rw [mul_right_comm, mul_right_comm (φ g ^ j)⁻¹]
    congr 1
    rw [inv_mul_eq_iff_eq_mul, mul_left_comm, eq_inv_mul_iff_mul_eq, mul_comm, h]
  · simp only [map_mul, map_inv, map_pow, mul_pow, inv_pow, ← pow_mul]
    rw [mul_comm N j, mul_right_comm, inv_mul_cancel, one_mul]

end Tt

section Alg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ}

theorem abel_sum [NeZero (l ^ n)] (N j : ℕ) (hj : j ≤ N) (a : Ω) (ha : a ∈ A) (f : ℕ → Ω) (hf : ∀ k, f k ∈ A) (hN : f N = f 0)
    (ta tb : ZMod (l ^ n)) :
    CgA A l n (∑ k ∈ Finset.range N, (a + (f (k + 1) - f k)) * (((if k < j then ta + tb else ta).val : ℕ) : Ω))
      ((f j - f 0) * (tb.val : Ω) + a * ((((N : ZMod (l ^ n)) * ta + j * tb).val : ℕ) : Ω)) := by
  have h1 : CgA A l n (∑ k ∈ Finset.range N, (a + (f (k + 1) - f k)) * (((if k < j then ta + tb else ta).val : ℕ) : Ω))
      (∑ k ∈ Finset.range N, (a + (f (k + 1) - f k)) * ((ta.val : Ω) + if k < j then (tb.val : Ω) else 0)) := by
    refine cg_sum _ _ _ fun k _ => cg_mul _ (add_mem ha (sub_mem (hf _) (hf _))) ?_
    split_ifs with h
    · rw [← Nat.cast_add]; exact cg_nat (by simp)
    · rw [add_zero]; exact cg_refl _
  have h2 : ∑ k ∈ Finset.range N, (a + (f (k + 1) - f k)) * ((ta.val : Ω) + if k < j then (tb.val : Ω) else 0) =
      (f j - f 0) * (tb.val : Ω) + a * ((N * ta.val + j * tb.val : ℕ) : Ω) := by
    have hfil : (Finset.range N).filter (fun k => k < j) = Finset.range j := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
    rw [← Finset.sum_filter, hfil, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_range_sub, Finset.sum_range_sub, hN]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  rw [h2] at h1
  exact cg_trans h1 (cg_add (cg_refl _) (cg_mul _ ha (cg_nat (by simp))))

theorem shapiro {G : Type} [CommGroup G] (χ : (Ω ≃ₐ[ℚ] Ω) →* G) (z : (Ω ≃ₐ[ℚ] Ω) → G → Ω)
    (hz : ∀ s t, Stab A s → Stab A t → ∀ x, CgA A l n (z (s * t) x) (z s x + s (z t (x * (χ s)⁻¹))))
    (g s : Ω ≃ₐ[ℚ] Ω) (hg : Stab A g) (hs : Stab A s) (N j : ℕ) (hj : j < N) (ξ : Ω) (w : ℕ → Ω)
    (hx : ∀ k < N, χ g ^ k * (χ s)⁻¹ = χ g ^ ((k + N - j) % N))
    (h1 : ∀ k < N, CgA A l n (z ((g ^ k)⁻¹ * s * g ^ ((k + N - j) % N)) 1)
      (((g ^ k)⁻¹ * s * g ^ ((k + N - j) % N)) ξ - ξ + w k)) :
    CgA A l n (∑ k ∈ Finset.range N, z s (χ g ^ k))
      (s (∑ k ∈ Finset.range N, ((g ^ k) ξ - z (g ^ k) (χ g ^ k))) - (∑ k ∈ Finset.range N, ((g ^ k) ξ - z (g ^ k) (χ g ^ k))) +
        ∑ k ∈ Finset.range N, (g ^ k) (w k)) := by
  nth_rewrite 1 [← sum_shift N j hj (fun k => (g ^ k) ξ - z (g ^ k) (χ g ^ k))]
  rw [map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine cg_sum _ _ _ fun k hk => ?_
  replace hk := Finset.mem_range.1 hk
  have a1 := hz s _ hs (stab_pow hg ((k + N - j) % N)) (χ g ^ k)
  have a2 := hz _ _ (stab_pow hg k) (stab_mul (stab_mul (stab_inv (stab_pow hg k)) hs) (stab_pow hg ((k + N - j) % N))) (χ g ^ k)
  have a3 := cg_map (stab_pow hg k) (h1 k hk)
  have e : g ^ k * ((g ^ k)⁻¹ * s * g ^ ((k + N - j) % N)) = s * g ^ ((k + N - j) % N) := by group
  rw [map_add, map_sub, ← AlgEquiv.mul_apply (g ^ k) (_ * _), e, AlgEquiv.mul_apply] at a3
  rw [e, map_pow, mul_inv_cancel] at a2
  rw [hx k hk] at a1
  have a4 := cg_sub (cg_trans (cg_symm a1) (cg_trans a2 (cg_add (cg_refl _) a3)))
    (cg_refl (s (z (g ^ ((k + N - j) % N)) (χ g ^ ((k + N - j) % N)))))
  refine cg_congr a4 (by ring) ?_
  rw [map_sub]; ring

end Alg

section Inert

open ReciprocityTheory.Gal Pointwise

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem mem_ine_iff {A : ValuationSubring Ω} {s : Ω ≃ₐ[ℚ] Ω} :
    s ∈ Ine (F := ℚ) A ↔ Stab A s ∧ ∀ x ∈ A, A.valuation (s x - x) < 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨apply_mem_iff_of_mem_Dec h1, fun x hx => h2 x ((A.valuation_le_one_iff x).2 hx)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x hx => h2 x ((A.valuation_le_one_iff x).1 hx)⟩
    show s • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    exact stab_inv h1 x

theorem exists_ine_pow [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω)
    (hp : ((p : ℕ) : Ω) ∈ A.nonunits) (L : ℕ) (u : (ZMod (p ^ L))ˣ) :
    ∃ s ∈ Ine (F := ℚ) A, s (zt ε p L) = zt ε p L ^ (u : ZMod (p ^ L)).val := by
  obtain ⟨⟨s, hs⟩, h⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective p Ω A (A.mem_nonunits_iff.1 hp) L u
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  refine ⟨s, hs, ?_⟩
  rw [← h]
  exact cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω s) _
    (IsNTr.isPrimitiveRoot_zt ε p L).pow_eq_one

end Inert

theorem cores_law : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ χ : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ, (∀ s, s (zt ε p L) = zt ε p L ^ (χ s : ZMod (p ^ L)).val) →
  ∀ z : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ → ℚ → Ω, (∀ s x r, z s x r ∈ A) →
  (∀ s t, Stab A s → Stab A t → ∀ x r, CgA A p n (z (s * t) x r) (z s x r + s (z t (x * (χ s)⁻¹) r))) →
  ∀ ξ F : ℚ → Ω, (∀ r, ξ r ∈ A ∧ InZl ε p L (F r)) →
  (∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → χ s = 1 → ∀ tt : ZMod (p ^ n), s (zt ε p (L + n)) = zt ε p n ^ tt.val * zt ε p (L + n) →
    ∀ r, CgA A p n (z s 1 r) (s (ξ r) - ξ r + F r * (tt.val : Ω))) →
  ∀ F' : ℚ → Ω, (∀ r, IsNT ε p L m (F r) (F' r)) →
  ∃ ξ' : ℚ → Ω, (∀ r, ξ' r ∈ A) ∧ ∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → s (zt ε p m) = zt ε p m → ∀ tt : ZMod (p ^ n), IsLamG ε p n m s tt →
    ∀ r, CgA A p n ((p : Ω) ^ c * ∑ x ∈ Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), z s x r)
      (s (ξ' r) - ξ' r + (p : Ω) ^ c * (F' r * (tt.val : Ω))) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.TateInv.tate_inv p hp2
  refine ⟨c, ?_⟩
  intro Ω _ _ _ ε A hpA L n m hm hmn hnL χ₀ hχ₀ z hzA hcoc ξ F hξF hz1 F' hF'
  have hpp : p.Prime := Fact.out
  have hmL : m ≤ L := hmn.trans hnL
  haveI : NeZero (p ^ L) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  haveI : Fact (1 < p ^ L) := ⟨Nat.one_lt_pow (by omega) hpp.one_lt⟩
  have hζL := IsNTr.isPrimitiveRoot_zt ε p L
  let χ : (Ω ≃ₐ[ℚ] Ω) →* (ZMod (p ^ L))ˣ := MonoidHom.mk' χ₀ fun s t =>
    Units.ext (lc_mul ε p L (fun g => (χ₀ g : ZMod (p ^ L))) hχ₀ s t)
  have hχ : ∀ s, s (zt ε p L) = zt ε p L ^ (χ s : ZMod (p ^ L)).val := hχ₀
  have fixL : ∀ g, χ g = 1 → g (zt ε p L) = zt ε p L := fun g h => by
    rw [hχ, h, Units.val_one, ZMod.val_one, pow_one]
  have hcop : Nat.Coprime (1 + p ^ m) (p ^ L) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
    intro h
    exact hpp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h)
  obtain ⟨g, hgI, hg⟩ := exists_ine_pow ε p A hpA L (ZMod.unitOfCoprime (1 + p ^ m) hcop)
  have hgA : Stab A g := (mem_ine_iff.1 hgI).1
  have hχg : χ g = ZMod.unitOfCoprime (1 + p ^ m) hcop :=
    Units.ext (ZMod.val_injective _ (hζL.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [← hχ, hg])))
  have hgL : g (zt ε p L) = zt ε p L ^ (1 + p ^ m) := by
    rw [hg, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div (1 + p ^ m) (p ^ L), pow_add, pow_mul, hζL.pow_eq_one, one_pow, mul_one]
  obtain ⟨hord, himg⟩ := pows_eq p hp2 L m hm hmL (χ g) (by rw [hχg, ZMod.coe_unitOfCoprime]; push_cast; rfl)
  have hgm : g (zt ε p m) = zt ε p m := by
    have hz := IsNTr.zt_pow ε p m (L - m)
    rw [Nat.add_sub_cancel' hmL] at hz
    rw [← hz, map_pow, hgL, ← pow_mul, add_mul, one_mul, ← pow_add, Nat.add_sub_cancel' hmL, pow_add, hζL.pow_eq_one, mul_one]
  have hlam := fun s hs tt tt' => GlobalTheory.LamEq.lam_eq ε p hp2 L n m hm hmn hnL s hs tt tt'
  generalize hN : p ^ (L - m) = N at hord himg hlam
  have huN : χ g ^ N = 1 := by rw [← hord, pow_orderOf_eq_one]
  have hb : (g ^ N) (zt ε p L) = zt ε p L := fixL _ (by rw [map_pow, huN])
  obtain ⟨tb, htb⟩ := tt_exists (n := n) hb
  choose H hHZ hH using fun r => hc ε L m hm hmL (F r) (F' r) (hξF r).2 (hF' r) g hgL
  have hHA : ∀ r, H r ∈ A := fun r => mem_of_inZl ε p A hpA L _ (hHZ r)
  have hF'Z : ∀ r, InZl ε p m (F' r) := fun r => by
    obtain ⟨F'', -, h1, h2⟩ := GlobalTheory.NTr.normTrace_exists_unique ε p L m hm hmL (F r) (hξF r).2
    rw [h2 _ (hF' r)]; exact h1
  have hpc : (p : Ω) ^ c ∈ A := pow_mem (nat_mem p) c
  refine ⟨fun r => (p : Ω) ^ c * (∑ k ∈ Finset.range N, ((g ^ k) (ξ r) - z (g ^ k) (χ g ^ k) r)) + H r * (tb.val : Ω),
    fun r => add_mem (mul_mem hpc (sum_mem fun k _ => sub_mem ((stab_pow hgA k _).2 (hξF r).1) (hzA _ _ _)))
      (mul_mem (hHA r) (nat_mem _)), fun s hsA hsI hsm tt htt r => ?_⟩
  obtain ⟨j, hjN, hj⟩ : ∃ j < N, χ g ^ j = χ s := by
    have h : χ s ∈ (Finset.range N).image (fun k => χ g ^ k) := by
      rw [himg, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (fix_iff ε p L m hmL s _ (hχ s)).1 hsm⟩
    simpa using h
  have ha : ((g ^ j)⁻¹ * s) (zt ε p L) = zt ε p L := fixL _ (by rw [map_mul, map_inv, map_pow, hj, inv_mul_cancel])
  obtain ⟨ta, hta⟩ := tt_exists (n := n) ha
  obtain ⟨t1, t2, t3⟩ := tt_transfer (by omega) hnL g s N j ta tb ha hb hta htb
  have hkp : ∀ k < N, (k + N - j) % N + j = if k < j then k + N else k := fun k hk => by
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show k + N - j = (k - j) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  have hx : ∀ k < N, χ g ^ k * (χ s)⁻¹ = χ g ^ ((k + N - j) % N) := fun k hk => by
    rw [mul_inv_eq_iff_eq_mul, ← hj, ← pow_add, hkp k hk]
    split_ifs
    · rw [pow_add, huN, mul_one]
    · rfl
  have key := shapiro (A := A) (l := p) (n := n) χ (fun s x => z s x r) (fun s t hs ht x => hcoc s t hs ht x r) g s hgA hsA N j hjN (ξ r)
    (fun k => F r * (((if k < j then ta + tb else ta).val : ℕ) : Ω)) hx (fun k hk => by
      have hI := mem_ine_iff.1 (mul_mem (mul_mem (inv_mem (pow_mem hgI k)) (mem_ine_iff.2 ⟨hsA, hsI⟩))
        (pow_mem hgI ((k + N - j) % N)))
      refine hz1 _ hI.1 hI.2 ?_ _ ?_ r
      · show χ _ = 1
        rw [map_mul, map_mul, map_inv, map_pow, map_pow, ← hx k hk, mul_comm (χ g ^ k), mul_assoc, mul_inv_cancel_left,
          inv_mul_cancel]
      · have h := hkp k hk
        split_ifs at h ⊢
        · exact t2 _ _ h
        · exact t1 _ _ h)
  have hsum : ∑ x ∈ Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), z s x r =
      ∑ k ∈ Finset.range N, z s (χ g ^ k) r := by
    rw [← himg, Finset.sum_image]
    intro a ha b hb hab
    have := (pow_inj_mod (x := χ g)).1 hab
    rwa [hord, Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at this
  have hab := abel_sum (A := A) (l := p) (n := n) N j hjN.le ((p : Ω) ^ c * F' r)
    (mul_mem hpc (mem_of_inZl ε p A hpA m _ (hF'Z r))) (fun k => (g ^ k) (H r)) (fun k => (stab_pow hgA k _).2 (hHA r))
    (IsNTr.apply_eq_of_mem_adjoin (hHZ r).mem_adjoin (by rw [hb, pow_zero, AlgEquiv.one_apply])) ta tb
  have hjs : (g ^ j) (H r) = s (H r) :=
    IsNTr.apply_eq_of_mem_adjoin (hHZ r).mem_adjoin (by rw [hχ (g ^ j), hχ s, map_pow, hj])
  rw [← hlam s hsm tt _ htt t3, hjs, pow_zero, AlgEquiv.one_apply] at hab
  have hterm : (p : Ω) ^ c * ∑ k ∈ Finset.range N, (g ^ k) (F r * (((if k < j then ta + tb else ta).val : ℕ) : Ω)) =
      ∑ k ∈ Finset.range N, ((p : Ω) ^ c * F' r + ((g ^ (k + 1)) (H r) - (g ^ k) (H r))) *
        (((if k < j then ta + tb else ta).val : ℕ) : Ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := congrArg (g ^ k) (hH r)
    have h2 : (g ^ k) (F' r) = (1 : Ω ≃ₐ[ℚ] Ω) (F' r) :=
      IsNTr.apply_eq_of_mem_adjoin (hF'Z r).mem_adjoin (by rw [fix_pow hgm, AlgEquiv.one_apply])
    rw [map_mul, map_pow, map_natCast, map_sub, map_sub, h2, AlgEquiv.one_apply, ← AlgEquiv.mul_apply, ← pow_succ] at h1
    rw [map_mul, map_natCast, ← h1]; ring
  rw [hsum]
  have k2 := cg_mul _ hpc key
  rw [mul_add, hterm] at k2
  refine cg_congr (cg_trans k2 (cg_add (cg_refl _) hab)) rfl ?_
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.Glue.CorShap
end
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corestriction_cyclotomic_shapiro_normalisedTrace : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ χ : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ, (∀ s, s (zt ε p L) = zt ε p L ^ (χ s : ZMod (p ^ L)).val) →
  ∀ z : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ → ℚ → Ω, (∀ s x r, z s x r ∈ A) →
  (∀ s t, Stab A s → Stab A t → ∀ x r, CgA A p n (z (s * t) x r) (z s x r + s (z t (x * (χ s)⁻¹) r))) →
  ∀ ξ F : ℚ → Ω, (∀ r, ξ r ∈ A ∧ InZl ε p L (F r)) →
  (∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → χ s = 1 → ∀ tt : ZMod (p ^ n), s (zt ε p (L + n)) = zt ε p n ^ tt.val * zt ε p (L + n) →
    ∀ r, CgA A p n (z s 1 r) (s (ξ r) - ξ r + F r * (tt.val : Ω))) →
  ∀ F' : ℚ → Ω, (∀ r, IsNT ε p L m (F r) (F' r)) →
  ∃ ξ' : ℚ → Ω, (∀ r, ξ' r ∈ A) ∧ ∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → s (zt ε p m) = zt ε p m → ∀ tt : ZMod (p ^ n), IsLamG ε p n m s tt →
    ∀ r, CgA A p n ((p : Ω) ^ c * ∑ x ∈ Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), z s x r)
      (s (ξ' r) - ξ' r + (p : Ω) ^ c * (F' r * (tt.val : Ω))) := by
  first | (exact @GlobalTheory.Glue.CorShap.cores_law) | (exact GlobalTheory.Glue.CorShap.cores_law) | (intros; apply GlobalTheory.Glue.CorShap.cores_law  <;> assumption)
end
