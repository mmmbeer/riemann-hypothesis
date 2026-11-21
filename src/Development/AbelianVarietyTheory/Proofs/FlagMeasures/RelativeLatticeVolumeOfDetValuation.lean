import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardQuotPow

section
namespace GlobalTheory.CardQuotientPow

open Module Submodule

theorem card_quot_pow {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by
  have key : ∀ I : Ideal R, Nat.card (R ⧸ I) = I.toAddSubgroup.index := fun I => rfl
  induction k with
  | zero => rw [key]; simp
  | succ k ih =>
    rw [pow_succ (Nat.card (R ⧸ Ideal.span {p})) k, ← ih, key, key, key]
    have hle : (Ideal.span {p ^ (k+1)}).toAddSubgroup ≤ (Ideal.span {p ^ k}).toAddSubgroup := by
      intro x hx
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p (Nat.le_succ k)) hx
    rw [← AddSubgroup.relIndex_mul_index hle, mul_comm]
    congr 1
    let f : R →+ R := AddMonoidHom.mulLeft (p ^ k)
    have hr : f.range = (Ideal.span {p ^ k}).toAddSubgroup := by
      ext x
      simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton', f,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
    have hc : (Ideal.span {p ^ (k+1)}).toAddSubgroup.comap f = (Ideal.span {p}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, f,
        AddMonoidHom.coe_mulLeft]
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
    rw [← hr, ← AddSubgroup.index_comap, hc]

theorem main {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Module.Basis ι R M) {p : R}
    (hp : Irreducible p) (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m := by
  classical
  set N := LinearMap.range φ with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hφ
  have h : finrank R N = finrank R M := e.finrank_eq.symm
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let f : M →ₗ[R] M := N.subtype ∘ₗ (b'.equiv ab (Equiv.refl _) : M →ₗ[R] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, b'.equiv_apply, Equiv.refl_apply,
      Submodule.subtype_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hφf : Associated (LinearMap.det φ) (LinearMap.det f) := by
    have : φ = N.subtype ∘ₗ (e : M →ₗ[R] N) := by ext x; rfl
    rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  choose k hk using fun i =>
    IsDiscreteValuationRing.associated_pow_irreducible (smithNormalFormCoeffs_ne_zero b h i) hp
  refine ⟨∑ i, k i, ?_, ?_⟩
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine hφf.trans ?_
    rw [hdetf]
    exact Associated.prod _ _ _ fun i _ => hk i
  · rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← card_quot_pow hp, Ideal.span_singleton_eq_span_singleton.mpr (hk i)]

end GlobalTheory.CardQuotientPow
end

section
namespace GlobalTheory.QuotientCardinality

open ValuativeRel

theorem main : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ {a : ℤ} {m : ℕ} {u v : (↥(Valuation.integer (ValuativeRel.valuation F)))ˣ}, (↑ϖ : F) ^ a * (↑(↑u : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) * (↑(↑v : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) = (↑ϖ : F) ^ m → a = (↑m : ℤ) := by
  intro F _ _ _ _ ϖ hϖ a m u v h
  have hint := Valuation.integer.integers (ValuativeRel.valuation F)
  have hu : ValuativeRel.valuation F ((u : (ValuativeRel.valuation F).integer) : F) = 1 :=
    hint.one_of_isUnit u.isUnit
  have hv : ValuativeRel.valuation F ((v : (ValuativeRel.valuation F).integer) : F) = 1 :=
    hint.one_of_isUnit v.isUnit
  have hne : (ϖ : F) ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (Subtype.ext (by simpa using h0))
  have hpos : 0 < ValuativeRel.valuation F (ϖ : F) := by
    rw [pos_iff_ne_zero]
    exact (map_ne_zero (ValuativeRel.valuation F)).mpr hne
  have hne1 : ValuativeRel.valuation F (ϖ : F) ≠ 1 := by
    intro h1
    exact hϖ.not_isUnit ((hint.isUnit_iff_valuation_eq_one (x := ϖ)).mpr h1)
  have h2 := congrArg (ValuativeRel.valuation F) h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one, map_zpow₀, map_pow, ← zpow_natCast] at h2
  exact zpow_right_injective₀ hpos hne1 h2

end GlobalTheory.QuotientCardinality
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatDet

theorem card_quot_pow {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {p : R}
    (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  have hq := cardQuot_pow_of_prime (P := Ideal.span {p})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero) (i := k)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, Ideal.span_singleton_pow] at hq
  exact hq

open Module Submodule in

theorem card_coker {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Basis ι R M) {p : R} (hp : Irreducible p)
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m :=
  _root_.GlobalTheory.CardQuotientPow.main b hp φ hφ

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem resQ_ne_zero {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) : resQ ϖ ≠ 0 := by
  unfold resQ
  rw [← hϖ.maximalIdeal_eq]
  haveI : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

theorem relIndex_map {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {W : Type} [AddCommGroup W] [Module F W]
    {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (ψ : W →ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det ψ = (ϖ : F) ^ a * ((u : 𝒪[F]) : F)) (W0 : AddSubgroup W)
    (hW : ∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) (hψ : ∀ i j, b.repr (ψ (b j)) i ∈ 𝒪[F]) :
    ∃ m : ℕ, a = m ∧ (W0.map ψ.toAddMonoidHom).relIndex W0 = resQ ϖ ^ m :=
  _root_.UpperTheory.Reformulated.B.Yzb5.relIndex_map hϖ b ψ a u hd W0 hW hψ

theorem relVol_map : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {W : Type} [AddCommGroup W] [Module F W] {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (φ : W ≃ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ), LinearMap.det (φ : W →ₗ[F] W) = (ϖ : F) ^ a * ((u : 𝒪[F]) : F) → ∀ W0 : AddSubgroup W, (∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) → (W0.map φ.toAddEquiv.toAddMonoidHom).relIndex W0 ≠ 0 ∧ W0.relIndex (W0.map φ.toAddEquiv.toAddMonoidHom) ≠ 0 ∧ relVol W0 (W0.map φ.toAddEquiv.toAddMonoidHom) = (resQ ϖ : ℝ) ^ (-a) := by
  intro F _ _ _ _ ϖ hϖ W _ _ ι _ b φ a u hd W0 hW
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hq := resQ_ne_zero hϖ
  haveI := Module.Finite.of_basis b
  haveI := Module.Free.of_basis b
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[F])
    (fun ij : ι × ι => b.repr (φ (b ij.2)) ij.1)
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero c.2) hϖ
  set d := Module.finrank F W
  set t : F := (ϖ : F) ^ n with ht
  have htO : t ∈ 𝒪[F] := pow_mem ϖ.2 n
  have h1 : ∀ i j, b.repr ((t • (φ : W →ₗ[F] W)) (b j)) i ∈ 𝒪[F] := by
    intro i j
    obtain ⟨y, hy⟩ := hc (i, j)
    have e1 : t = ((v : 𝒪[F]) : F) * ((c : 𝒪[F]) : F) := by
      rw [ht, mul_comm]; exact_mod_cast congrArg (fun x : 𝒪[F] => (x : F)) hv.symm
    have e2 : b.repr ((t • (φ : W →ₗ[F] W)) (b j)) i = ((v : 𝒪[F]) : F) * (y : F) := by
      have hy' : (y : F) = ((c : 𝒪[F]) : F) * b.repr (φ (b j)) i := hy
      rw [hy', ← mul_assoc, ← e1]
      simp
    rw [e2]
    exact mul_mem (v : 𝒪[F]).2 y.2
  have h2 : ∀ i j, b.repr ((t • (LinearMap.id : W →ₗ[F] W)) (b j)) i ∈ 𝒪[F] := by
    intro i j
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs
    · simpa using htO
    · simp
  obtain ⟨m1, hm1, i1⟩ := relIndex_map hϖ b _ (n * d + a) u (by
    rw [LinearMap.det_smul, hd, zpow_add₀ h0, ht, ← pow_mul, ← zpow_natCast, mul_assoc]
    push_cast; rfl) W0 hW h1
  obtain ⟨m2, hm2, i2⟩ := relIndex_map hϖ b _ (n * d) 1 (by
    rw [LinearMap.det_smul, LinearMap.det_id, ht, ← pow_mul, ← zpow_natCast]
    push_cast; rfl) W0 hW h2
  set A := W0.map φ.toAddEquiv.toAddMonoidHom with hA
  set B := W0.map (t • (φ : W →ₗ[F] W)).toAddMonoidHom with hB
  have hBe : B = (W0.map (t • (LinearMap.id : W →ₗ[F] W)).toAddMonoidHom).map
      φ.toAddEquiv.toAddMonoidHom := by
    rw [hB, AddSubgroup.map_map]
    congr 1
    ext x
    simp
  have i3 : B.relIndex A = resQ ϖ ^ m2 := by
    rw [hBe, hA, AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective, i2]
  have hle : ∀ ψ : W →ₗ[F] W, (∀ i j, b.repr (ψ (b j)) i ∈ 𝒪[F]) →
      W0.map ψ.toAddMonoidHom ≤ W0 := by
    rintro ψ hψ _ ⟨x, hx, rfl⟩
    rw [hW]
    intro i
    have : b.repr (ψ.toAddMonoidHom x) i = ∑ j, b.repr x j * b.repr (ψ (b j)) i := by
      change b.repr (ψ x) i = _
      conv_lhs => rw [← b.sum_repr x, map_sum, map_sum, Finsupp.finset_sum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [this]
    exact sum_mem fun j _ => mul_mem ((hW x).1 hx j) (hψ i j)
  have hBW : B ≤ W0 := hle _ h1
  have hBA : B ≤ A := by
    rw [hBe, hA]; exact AddSubgroup.map_mono (hle _ h2)
  have t1 := AddSubgroup.relIndex_mul_relIndex B (A ⊓ W0) W0 (le_inf hBA hBW) inf_le_right
  have t2 := AddSubgroup.relIndex_mul_relIndex B (A ⊓ W0) A (le_inf hBA hBW) inf_le_left
  rw [AddSubgroup.inf_relIndex_right, i1] at t1
  rw [AddSubgroup.inf_relIndex_left, i3] at t2
  have n1 := mul_ne_zero_iff.1 (t1 ▸ pow_ne_zero m1 hq)
  have n2 := mul_ne_zero_iff.1 (t2 ▸ pow_ne_zero m2 hq)
  refine ⟨n1.2, n2.2, ?_⟩
  have hq' : (resQ ϖ : ℝ) ≠ 0 := by exact_mod_cast hq
  have c0 : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast n1.1
  have t1' : (B.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = (resQ ϖ : ℝ) ^ m1 := by exact_mod_cast t1
  have t2' : (B.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = (resQ ϖ : ℝ) ^ m2 := by exact_mod_cast t2
  have ea : -a = (m2 : ℤ) - m1 := by omega
  unfold relVol
  rw [ea, zpow_sub₀ hq', zpow_natCast, zpow_natCast, ← t1', ← t2', mul_div_mul_left _ _ c0]

end GlobalTheory.HL.LatDet
end
