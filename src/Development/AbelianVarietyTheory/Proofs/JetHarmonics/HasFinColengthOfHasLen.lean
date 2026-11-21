import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.LieMatrixCoordinates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotIsUnitNatCastOfIsLocalHom
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentPowerUnramifiedIff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_power_unramified_iff : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R) (P : Ideal R), P.IsMaximal → (p : R) ∈ P → (P.map w.toOw).IsMaximal → (∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) → (∃ a b : ℕ, 0 < b ∧ (differentIdeal ℤ R).map w.toOw ^ b = Ideal.span {(p : w.Ow) ^ a}) ∧ (w.IsUnramified ↔ (differentIdeal ℤ R).map w.toOw = ⊤) := by
  first | exact @GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff | exact GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff | (intros; apply GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff <;> assumption)
end

section
noncomputable section
open scoped TensorProduct
open Matrix

namespace GlobalTheory.CutMultiplicationUnits

section Lin

variable {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O] [Algebra k O]

abbrev cut (k : Type) {A : Type} [CommRing k] [CommRing A] [Algebra k A] (e : A) : Submodule k A :=
  LinearMap.range (LinearMap.mulLeft k e)

theorem mul_mem_cut {e : A} (y : A) {a : A} (ha : a ∈ cut k e) : y * a ∈ cut k e := by
  obtain ⟨c, rfl⟩ := ha
  exact ⟨y * c, by simp [mul_left_comm]⟩

theorem e_mul_of_mem {e : A} (he : e * e = e) {a : A} (ha : a ∈ cut k e) : e * a = a := by
  obtain ⟨c, rfl⟩ := ha
  simp [← mul_assoc, he]

def mulCut (e y : A) : cut k e →ₗ[k] cut k e :=
  (LinearMap.mulLeft k y).restrict (fun _ ha => mul_mem_cut y ha)

variable {n : ℕ} {e : A} (b : Module.Basis (Fin n) k (cut k e))

variable (T : Fin n → (A →ₐ[k] O))

end Lin

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

def extFun (l : R →ₗ[ℤ] ℤ) : Op p R →ₗ[ℤ_[p]] ℤ_[p] :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℤ_[p] ℤ_[p]).toLinearMap ∘ₗ l.baseChange ℤ_[p]

variable [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
  {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O]

end Local

section Compare

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

theorem sig_eq_bar [StarRing R] (x : Op p R) : AvDefs.sig p R x = bar p R x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def placeUEquiv : AvDefs.PlaceU p R ≃ Place p R where
  toFun w := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  invFun w := ⟨w.e, w.idem, w.ne_zero, w.primitive⟩
  left_inv _ := rfl
  right_inv _ := rfl

def placeEquiv [StarRing R] : AvDefs.Place p R ≃ SplitPlace p R where
  toFun w := ⟨⟨w.e, w.idem, w.ne_zero, w.prim⟩, fun h =>
    w.split ((sig_eq_bar w.e).trans (congrArg Place.e h).symm)⟩
  invFun w := ⟨w.e, w.idem, w.ne_zero, w.primitive, fun h =>
    w.ne_conj (Place.ext ((sig_eq_bar w.e).symm.trans h).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def embEquiv (w : Place p R) (O : Type) [CommRing O] [Algebra ℤ_[p] O] :
    AvDefs.Emb (O := O) w.e ≃ w.Emb O := Equiv.refl _

variable [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
  {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O]

end Compare

end GlobalTheory.CutMultiplicationUnits
end
end

section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open NumberField

namespace GlobalTheory.AvChartCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

def IsPrimeUnder (w : Place p R) (P : Ideal R) : Prop :=
  P.IsMaximal ∧ (p : R) ∈ P ∧ (P.map w.toOw).IsMaximal ∧
    ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤

namespace IsPrimeUnder

variable {w : Place p R} {P : Ideal R}

theorem p_mem (h : IsPrimeUnder w P) : (p : w.Ow) ∈ P.map w.toOw := by
  rw [← map_natCast w.toOw]; exact Ideal.mem_map_of_mem _ h.2.1

theorem map_eq_pow [IsDedekindDomain R] (h : IsPrimeUnder w P) {J : Ideal R} (hJ : J ≠ ⊥) :
    J.map w.toOw =
      P.map w.toOw ^ (UniqueFactorizationMonoid.normalizedFactors J).count P := by
  have := h.1
  obtain ⟨Q, hPQ, hQe⟩ := Ideal.eq_prime_pow_mul_coprime hJ P
  generalize Multiset.count P _ = e at hQe
  have hQ0 : Q ≠ ⊥ := by rintro rfl; exact hJ (by simpa using hQe)
  rw [hQe, Ideal.map_mul, Ideal.map_pow,
    GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime _ P h.1 h.2.2.2 Q hQ0 hPQ, Ideal.mul_top]

variable [IsDedekindDomain R] [CharZero R]

theorem span_p_eq (h : IsPrimeUnder w P) :
    Ideal.span {(p : w.Ow)} = P.map w.toOw ^
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P := by
  rw [← h.map_eq_pow (by simpa using (Fact.out : p.Prime).ne_zero), Ideal.map_span,
    Set.image_singleton, map_natCast]

theorem count_ne_zero (h : IsPrimeUnder w P) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P ≠ 0 := by
  intro h0
  have h1 := h.span_p_eq
  rw [h0, pow_zero, Ideal.one_eq_top] at h1
  exact h.2.2.1.ne_top (eq_top_iff.2 (h1 ▸ (Ideal.span_singleton_le_iff_mem _).2 h.p_mem))

variable [Module.Finite ℤ R]

theorem pow_inj (h : IsPrimeUnder w P) {i j : ℕ}
    (hij : P.map w.toOw ^ i = P.map w.toOw ^ j) : i = j := by
  have key : ∀ i j : ℕ, P.map w.toOw ^ i = P.map w.toOw ^ j → ¬ i < j := by
    intro i j hij hlt
    have h1 : Ideal.span {(p : w.Ow) ^ i} = Ideal.span {(p : w.Ow) ^ j} := by
      rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, h.span_p_eq, ← pow_mul,
        ← pow_mul, mul_comm _ i, mul_comm _ j, pow_mul, pow_mul, hij]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h2 : ∀ (n : ℕ) (x : w.Ow), (p : w.Ow) ^ n * x = 0 → x = 0 := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ih =>
        intro x hx
        exact GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree p R w x (ih _ (by linear_combination hx))
    have h3 := h2 i (1 - c * p ^ k * p) (by linear_combination -hc)
    apply h.2.2.1.ne_top
    rw [Ideal.eq_top_iff_one, sub_eq_zero.1 h3]
    exact Ideal.mul_mem_left _ _ h.p_mem
  exact le_antisymm (not_lt.1 (key j i hij.symm)) (not_lt.1 (key i j hij))

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in

theorem isDiffVal_iff (h : IsPrimeUnder w P) (vd : ℝ) :
    w.IsDiffVal_vp vd ↔ vd =
      ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ R)).count P : ℝ) /
        ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P : ℝ) := by
  have : CharZero (FractionRing R) := inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)) (FractionRing R) :=
    IsIntegralClosure.isLocalization _ (FractionRing ℤ) _ _
  have : FiniteDimensional (FractionRing ℤ) (FractionRing R) :=
    .of_isLocalization ℤ R (nonZeroDivisors ℤ)
  have hsep : Algebra.IsSeparable (FractionRing ℤ) (FractionRing R) := inferInstance
  have hD : differentIdeal ℤ R ≠ ⊥ := differentIdeal_ne_bot
  have h1 := h.span_p_eq
  have h2 := h.map_eq_pow hD
  have he := h.count_ne_zero
  generalize Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
    (Ideal.span {(p : R)})) = e at h1 he ⊢
  generalize Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
    (differentIdeal ℤ R)) = k at h2 ⊢
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
  constructor
  · rintro ⟨a, b, hb, hvd, hab⟩
    rw [← Ideal.span_singleton_pow, h1, h2, ← pow_mul, ← pow_mul] at hab
    have h3 : (k : ℝ) * b = e * a := by exact_mod_cast h.pow_inj hab
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [eq_div_iff he']
    apply mul_right_cancel₀ hb'
    rw [h3, ← hvd]; ring
  · rintro rfl
    refine ⟨k, e, Nat.pos_of_ne_zero he, div_mul_cancel₀ _ he', ?_⟩
    rw [← Ideal.span_singleton_pow, h1, h2, ← pow_mul, ← pow_mul, mul_comm]

end IsPrimeUnder

end GlobalTheory.AvChartCompare
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.PGsh.Up
open GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixCoordinates GlobalTheory.TorsionCompare NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AvChartCompare

section Charts

variable {R : Type} [CommRing R]

variable {G : Over (Sp R)} {d : ℕ}

end Charts

section Series

variable {O : Type} [CommRing O] {d : ℕ}

variable {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]

def HasFinColength (F : Fin d → PS O 2 d) {s : ℕ} (u : Fin s → Fin d → O) (x : NNReal) : Prop :=
  ∃ S : Set (PS O 1 d), S.Finite ∧ (∀ χ ∈ S, IsMultSeries F χ) ∧
    HasLen v O ((Fin s → O) ⧸
      Submodule.span O {l | ∃ χ ∈ S, l = fun i => linCoeff χ ⬝ᵥ u i}) x

variable {v}

theorem hasLen_le_of_surjective (hv : v.Integers O) {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (π : M →ₗ[O] N) (hπ : Function.Surjective π) {x y : NNReal}
    (hx : HasLen v O M x) (hy : HasLen v O N y) : x ≤ y := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, b, ⟨e'⟩, rfl⟩ := hy
  let f := e'.toLinearMap ∘ₗ π ∘ₗ e.symm.toLinearMap
  have hf : Function.Surjective f := e'.surjective.comp (hπ.comp e.symm.surjective)
  let q : Fin m → ((j : Fin n) → O ⧸ Ideal.span {b j}) :=
    fun i => f (Pi.single i (1 : O ⧸ Ideal.span {c i}))
  have hq : Submodule.span O (Set.range q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨z, rfl⟩ := hf z
    have hz : z = ∑ i, (Quotient.out (z i) : O) • Pi.single i (1 : O ⧸ Ideal.span {c i}) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, _root_.mul_one,
          Ideal.Quotient.algebraMap_eq]
        exact (Ideal.Quotient.mk_out (z k)).symm
      · intro b _ hb
        simp [Pi.single_eq_of_ne' hb]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hz, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • q i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, q, ← map_smul]
      have : c k • (Pi.single k (1 : O ⧸ Ideal.span {c k}) : (i : Fin m) → O ⧸ Ideal.span {c i}) =
          0 := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, Algebra.smul_def, _root_.mul_one,
            Ideal.Quotient.algebraMap_eq]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        · simp [Pi.single_eq_of_ne hj]
      rw [this, map_zero]
    · intro b _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ k) h
  have h := det_mem_span_prod n b m q hq (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at h
  simpa only [map_prod] using hv.le_of_dvd (Ideal.mem_span_singleton.1 h)

theorem HasFinColength.le (hv : v.Integers O) {F : Fin d → PS O 2 d} {s : ℕ}
    {u : Fin s → Fin d → O} {x y : NNReal} (hx : HasFinColength v F u x)
    (hy : HasLen v O ((Fin s → O) ⧸ dlogSpan F u) y) : x ≤ y := by
  obtain ⟨S, -, hS, hx⟩ := hx
  have hle : Submodule.span O {l | ∃ χ ∈ S, l = fun i => linCoeff χ ⬝ᵥ u i} ≤ dlogSpan F u :=
    Submodule.span_mono fun l ⟨χ, h, hl⟩ => ⟨χ, hS χ h, hl⟩
  exact hasLen_le_of_surjective hv (Submodule.factor hle) (Submodule.factor_surjective hle) hx hy

end Series

section Emb

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem exists_extend (τ : 𝓞 E →+* C) : ∃! σ : E →+* C, ∀ a : 𝓞 E, σ a = τ a := by
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    obtain ⟨n, hn⟩ := (Submodule.ne_bot_iff _).1
      (Ideal.IsIntegral.comap_ne_bot ℤ (I := RingHom.ker τ) h)
    have h1 : τ (algebraMap ℤ (𝓞 E) n) = 0 := hn.1
    simp [hn.2] at h1
  refine ⟨IsFractionRing.lift (K := E) hτ, fun a => IsFractionRing.lift_algebraMap hτ a,
    fun σ h => IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_⟩
  rw [IsFractionRing.lift_algebraMap]; exact h a

theorem exists_restrict (hv : v.Integers O) (σ : E →+* C) :
    ∃ τ : 𝓞 E →+* O, ∀ a : 𝓞 E, σ a = algebraMap O C (τ a) := by
  have h : ∀ a : 𝓞 E, ∃ z : O, algebraMap O C z = σ a := fun a => by
    have h1 : IsIntegral ℤ (σ a) := a.isIntegral_coe.map σ.toIntAlgHom
    exact hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h1.tower_top)
  choose f hf using h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun a => (hf a).symm⟩ <;> intros <;> apply hv.hom_inj <;> simp [hf]

def embEquiv (hv : v.Integers O) : (𝓞 E →+* O) ≃ (E →+* C) :=
  Equiv.ofBijective (fun τ => (exists_extend ((algebraMap O C).comp τ)).choose) (by
    constructor
    · intro τ τ' h
      ext a
      apply hv.hom_inj
      have h1 := (exists_extend ((algebraMap O C).comp τ)).choose_spec.1 a
      have h2 := (exists_extend ((algebraMap O C).comp τ')).choose_spec.1 a
      exact h1.symm.trans ((DFunLike.congr_fun h (a : E)).trans h2)
    · intro σ
      obtain ⟨τ, hτ⟩ := exists_restrict hv σ
      exact ⟨τ, ((exists_extend ((algebraMap O C).comp τ)).choose_spec.2 σ hτ).symm⟩)

end Emb

section Places

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]
  {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O]

def Under (w : AvDefs.Place p (𝓞 E)) (P : Ideal (𝓞 E)) : Prop :=
  IsPrimeUnder (GlobalTheory.CutMultiplicationUnits.placeEquiv w).toPlace P

variable {w : AvDefs.Place p (𝓞 E)} {P : Ideal (𝓞 E)}

end Places

abbrev Conclusion : Type 1 :=
  ∀ {T : Type} [CommRing T] {E : Type} [Field E] [NumberField E] {d : ℕ} (_F : FGLaw T d)
    {C : Type} [Field C] [CharZero C] (_v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (_io : T →+* O) (_w : Ideal (𝓞 E)) {rp : ℕ} (_rm : ℕ)
    (_u : (E →+* C) → Fin rp → Fin d → O), Prop

def bound_vp (p : ℕ) {E : Type} [Field E] [NumberField E] (w : Ideal (𝓞 E)) (r : ℝ) : ℝ :=
  (localDeg p w : ℝ) * r * (1 / ((p : ℝ) - 1) + vd_vp p w / 2)

open Classical in

def ColengthsBounded (p : ℕ) : Conclusion :=
  fun {_} _ {E} _ _ {_} F {C} _ _ v {_} _ _ io w {_} rm u =>
  ∀ a : (E →+* C) → ℝ, (∀ τ, Induces v τ w → HasColength_vp p v F io (u τ) (a τ)) →
    ∑ τ ∈ Finset.univ.filter (fun τ : E →+* C => Induces v τ w), a τ ≤ bound_vp p w rm

open Classical in

def FiniteColengthsBounded (p : ℕ) : Conclusion :=
  fun {_} _ {E} _ _ {_} F {C} _ _ v {_} _ _ io w {_} rm u =>
  ∃ xs : (E →+* C) → NNReal, (∀ τ, Induces v τ w → HasFinColength v (F.mapF io) (u τ) (xs τ)) ∧
    v (p : C) ^ bound_vp p w rm ≤
      ∏ τ ∈ Finset.univ.filter (fun τ : E →+* C => Induces v τ w), xs τ

end GlobalTheory.AvChartCompare
end
end
