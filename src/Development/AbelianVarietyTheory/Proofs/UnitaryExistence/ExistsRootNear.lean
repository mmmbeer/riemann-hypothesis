import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.AdLat.UnitRoot

section quad
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_one_or (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (f : E ≃ₐ[F] E) : f = 1 ∨ f = c := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hcard : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← h2]; exact AlgEquiv.card_le
  by_contra h
  push Not at h
  have : 2 < Fintype.card (E ≃ₐ[F] E) :=
    Fintype.two_lt_card_iff.2 ⟨f, 1, c, h.1, h.2, hc.symm⟩
  omega

theorem invol (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    c (c x) = x := by
  rcases eq_one_or c h2 hc (c * c) with h | h
  · exact congrArg (fun g : E ≃ₐ[F] E => g x) h
  · exact absurd (mul_left_cancel (a := c) (h.trans (mul_one c).symm)) hc

theorem fixed_integral (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E)
    (hx : IsIntegral ℤ x) (hfix : c x = x) :
    ∃ y ∈ (algebraMap (𝓞 F) F).range, algebraMap F E y = x := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := inferInstance
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) x).2 (fun f => by
    rcases eq_one_or c h2 hc f with rfl | rfl
    · rfl
    · exact hfix)
  exact ⟨y, ⟨⟨y, (isIntegral_algebraMap_iff (algebraMap F E).injective).1 hx⟩, rfl⟩, rfl⟩

end quad

section inst
variable (F : Type) [Field F] [NumberField F]

abbrev IntAd : Type := ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F

noncomputable def incl : IntAd F →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := ⟨fun v => a v, Filter.Eventually.of_forall fun v => (a v).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem incl_apply (a : IntAd F) (v) : incl F a v = a v := rfl

theorem incl_injective : Function.Injective (incl F) := fun a b h =>
  funext fun v => Subtype.ext (by rw [← incl_apply, ← incl_apply, h])

theorem exists_incl {a : FiniteAdeleRing (𝓞 F) F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    ∃ b, incl F b = a := ⟨fun v => ⟨a v, ha v⟩, rfl⟩

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

noncomputable def hatRing : Subring (RA F E) where
  toAddSubgroup := hat1 F (Set.range (algebraMap (𝓞 E) E))
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  mul_mem' hx hy := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩) hx hy

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
variable (F : Type) [Field F] [NumberField F] in
variable (E : Type) [Field E] [NumberField E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.UnitRoot.mem_hatRing (z : _root_.GlobalTheory.AdLat.RA F E) :
    z ∈ _root_.GlobalTheory.AdLat.UnitRoot.hatRing F E ↔
      z ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := Iff.rfl

variable {F E}

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
variable (F : Type) [Field F] [NumberField F] in
variable (E : Type) [Field E] [NumberField E] [Algebra F E] in
variable {F E} in
theorem _root_.GlobalTheory.AdLat.UnitRoot.conj_mem (c : E ≃ₐ[F] E) :
    ∀ x ∈ Set.range (algebraMap (𝓞 E) E), c x ∈ Set.range (algebraMap (𝓞 E) E) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨c (a : E), a.2.map c.toAlgHom.toRingHom.toIntAlgHom⟩, rfl⟩

theorem tmul_fixed (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {a : FiniteAdeleRing (𝓞 F) F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {x : E}
    (hx : x ∈ Set.range (algebraMap (𝓞 E) E)) (hfix : c x = x) :
    ∃ b, (a ⊗ₜ[F] x : RA F E) = incl F b ⊗ₜ[F] 1 := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, hy, hyx⟩ := fixed_integral c h2 hc _ (RingOfIntegers.isIntegral_coe x) hfix
  obtain ⟨b, hb⟩ := exists_incl F (a := algebraMap F _ y * a)
    (fun v => adele_mul_integral F ((mem_range_iff_adele_integral F y).1 hy v) (ha v))
  refine ⟨b, ?_⟩
  rw [hb, ← Algebra.smul_def, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hyx]

theorem sg_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] x) = a ⊗ₜ[F] c x := rfl

theorem sg_sg (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (z : RA F E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (sg (FiniteAdeleRing (𝓞 F) F) c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [sg_tmul, sg_tmul, invol c h2 hc]
  | add y z h1 h2 => rw [map_add, map_add, h1, h2]

theorem trace_mem (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {z : RA F E}
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ b, z + sg (FiniteAdeleRing (𝓞 F) F) c z = incl F b ⊗ₜ[F] 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    rw [sg_tmul, ← TensorProduct.tmul_add]
    refine tmul_fixed c h2 hc ha ?_ (by rw [map_add, invol c h2 hc, add_comm])
    obtain ⟨s, hs⟩ := conj_mem c x hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t + s, by rw [map_add, hs]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨a + b, by rw [map_add, map_add, TensorProduct.add_tmul, ← ha, ← hb]; ring⟩
  | neg y _ h1 =>
    obtain ⟨a, ha⟩ := h1
    exact ⟨-a, by rw [map_neg, map_neg, TensorProduct.neg_tmul, ← ha]; ring⟩

theorem norm_mem (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {z : RA F E}
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ b, z * sg (FiniteAdeleRing (𝓞 F) F) c z = incl F b ⊗ₜ[F] 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    rw [sg_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    refine tmul_fixed c h2 hc (fun v => adele_mul_integral F (ha v) (ha v)) ?_
      (by rw [map_mul, invol c h2 hc, mul_comm])
    obtain ⟨s, hs⟩ := conj_mem c x hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t * s, by rw [map_mul, hs]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz h1 h3 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h3
    obtain ⟨d, hd⟩ := trace_mem c h2 hc ((hatRing F E).mul_mem hy
      (galoisAut_mem_adelicCompletionOfElementSet F c (conj_mem c) hz))
    rw [map_mul, sg_sg c h2 hc] at hd
    exact ⟨a + b + d, by
      rw [map_add, map_add, map_add, TensorProduct.add_tmul, TensorProduct.add_tmul,
        ← ha, ← hb, ← hd]; ring⟩
  | neg y _ h1 =>
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by rw [map_neg, ← ha]; ring⟩

variable (F E) in

noncomputable def adIn : IntAd F →+* hatRing F E :=
  ((Algebra.TensorProduct.includeLeftRingHom :
    FiniteAdeleRing (𝓞 F) F →+* RA F E).comp (incl F)).codRestrict (hatRing F E)
    fun a => (mem_hatRing F E _).2 (tmul_mem_adelicCompletion_of_integral F (a := incl F a) (x := 1)
      (fun v => (a v).2) ⟨1, map_one _⟩)

variable (F E) in

noncomputable def intIn : 𝓞 E →+* hatRing F E :=
  ((Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E) :
    E →+* RA F E).comp (algebraMap (𝓞 E) E)).codRestrict _
    fun a => one_tmul_mem_adelicCompletionOfElementSet F ⟨a, rfl⟩

end inst

end GlobalTheory.AdLat.UnitRoot

namespace GlobalTheory.AdLat
open UnitRoot

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
private lemma mul_self_eq_one_of_quadratic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) : c * c = 1 := by
  by_contra h
  have hle := card_algHom_le_finrank (K := F) (M := E) (L := E)
  rw [h2] at hle
  let f : Fin 3 → (E →ₐ[F] E) :=
    ![AlgHom.id F E, (c : E →ₐ[F] E), ((c * c : E ≃ₐ[F] E) : E →ₐ[F] E)]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
    all_goals have hx := fun x => DFunLike.congr_fun hij x
    all_goals simp only [AlgHom.coe_id, id_eq, AlgEquiv.coe_algHom, AlgEquiv.mul_apply] at hx
    all_goals first
      | exact hc (AlgEquiv.ext fun x => (hx x).symm)
      | exact hc (AlgEquiv.ext fun x => hx x)
      | exact h (AlgEquiv.ext fun x => (hx x).symm)
      | exact h (AlgEquiv.ext fun x => hx x)
      | exact hc (AlgEquiv.ext fun x => c.injective (hx x).symm)
      | exact hc (AlgEquiv.ext fun x => c.injective (hx x))
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at this
  omega

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
private lemma sg_sg_of_quadratic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (z : _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
      (_root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c z) = z := by
  have hcc := mul_self_eq_one_of_quadratic c h2 hc
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [_root_.GlobalTheory.AdLat.sg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgEquiv.coe_algHom]
    rw [← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
private lemma exists_sum_mul_sub_conj_eq_one {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) :
    ∃ (n : ℕ) (r t s : Fin n → 𝓞 E), (∀ k, (s k : E) = c (t k : E)) ∧
      ∑ k, r k * (t k - s k) = 1 := by
  let S : Set (𝓞 E) := {d | ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ d = t - s}
  have htop : Ideal.span S = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨t, s, hs, hts⟩ := hP M hM
    exact hts (hle (Ideal.subset_span ⟨t, s, hs, rfl⟩))
  have h1 : (1 : 𝓞 E) ∈ Ideal.span S := htop ▸ Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 h1
  choose t s hs ht using fun k => (g k).2
  refine ⟨n, f, t, s, hs, ?_⟩
  rw [← hfg]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, ht k]

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
private lemma mem_bot_of_fixed_of_quadratic {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (x : E) (hx : c x = x) : x ∈ (⊥ : IntermediateField F E) := by
  by_contra hxb
  have htop : IntermediateField.adjoin F {x} = ⊤ := by
    have hd : Module.finrank F (IntermediateField.adjoin F {x}) ∣ 2 := by
      rw [← h2]; exact IntermediateField.finrank_dvd_of_le_right le_top |>.trans (by simp)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact absurd (IntermediateField.adjoin_simple_eq_bot_iff.1
        (IntermediateField.finrank_eq_one_iff.1 h1)) hxb
    · apply IntermediateField.eq_of_le_of_finrank_eq le_top
      rw [h1, IntermediateField.finrank_top', h2]
  apply hc
  have hx' : Algebra.adjoin F {x} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic x), htop]
    rfl
  have := AlgHom.ext_of_adjoin_eq_top (φ₁ := (c : E →ₐ[F] E)) (φ₂ := AlgHom.id F E) hx'
    (by simpa using hx)
  ext y
  exact DFunLike.congr_fun this y

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
private lemma exists_integer_of_fixed_integral {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (x : E) (hx : c x = x) (hint : x ∈ Set.range (algebraMap (𝓞 E) E)) :
    ∃ f : 𝓞 F, algebraMap F E f = x := by
  obtain ⟨f, rfl⟩ := IntermediateField.mem_bot.1 (mem_bot_of_fixed_of_quadratic c h2 hc x hx)
  obtain ⟨y, hy⟩ := hint
  refine ⟨⟨f, ?_⟩, rfl⟩
  have : IsIntegral ℤ (algebraMap F E f) := hy ▸ y.2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).1 this

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
private lemma exists_add_sg_eq_tmul_one_of_mem_closure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (P : FiniteAdeleRing (𝓞 F) F → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hneg : ∀ a, P a → P (-a)) (hsm : ∀ (f : 𝓞 F) a, P a → P (algebraMap F _ (f : F) * a))
    (z : _root_.GlobalTheory.AdLat.RA F E)
    (hz : z ∈ AddSubgroup.closure
      {z | ∃ a, P a ∧ ∃ x ∈ Set.range (algebraMap (𝓞 E) E), z = a ⊗ₜ[F] x}) :
    ∃ n, P n ∧ z + _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c z = n ⊗ₜ[F] (1 : E) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    have hcc := mul_self_eq_one_of_quadratic c h2 hc
    have hfix : c (x + c x) = x + c x := by
      rw [map_add, ← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply, add_comm]
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨w, hw⟩ := _root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨y, rfl⟩
    obtain ⟨f, hf⟩ := exists_integer_of_fixed_integral c h2 hc _ hfix ⟨y + w, by simp [hw]⟩
    refine ⟨algebraMap F _ (f : F) * a, hsm f a ha, ?_⟩
    rw [show _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
        (a ⊗ₜ[F] algebraMap (𝓞 E) E y) = a ⊗ₜ[F] c (algebraMap (𝓞 E) E y) by
      simp [_root_.GlobalTheory.AdLat.sg], ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
  | zero => exact ⟨0, h0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, e⟩ := hx
    obtain ⟨m, hm, e'⟩ := hy
    exact ⟨n + m, hadd _ _ hn hm, by rw [map_add, TensorProduct.add_tmul, ← e, ← e']; abel⟩
  | neg x _ hx =>
    obtain ⟨n, hn, e⟩ := hx
    exact ⟨-n, hneg _ hn, by rw [map_neg, TensorProduct.neg_tmul, ← e]; abel⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
private lemma exists_norm_sum_tmul_eq_tmul_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (P : FiniteAdeleRing (𝓞 F) F → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hneg : ∀ a, P a → P (-a)) (hsm : ∀ (f : 𝓞 F) a, P a → P (algebraMap F _ (f : F) * a))
    (hmul : ∀ a b, P a → P b → P (a * b)) {ι : Type} (s : Finset ι)
    (a : ι → FiniteAdeleRing (𝓞 F) F) (w : ι → 𝓞 E) (ha : ∀ k, P (a k)) :
    ∃ n, P n ∧ (∑ k ∈ s, a k ⊗ₜ[F] (w k : E)) *
      _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (∑ k ∈ s, a k ⊗ₜ[F] (w k : E)) =
        n ⊗ₜ[F] (1 : E) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, h0, by simp⟩
  | insert k s hk ih =>
    obtain ⟨n, hn, e⟩ := ih
    have hσ : ∀ b (x : E), _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
        (b ⊗ₜ[F] x) = b ⊗ₜ[F] c x := fun b x => by
      simp [_root_.GlobalTheory.AdLat.sg]
    obtain ⟨cw, hcw⟩ := _root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨w k, rfl⟩
    have hfix : c ((w k : E) * c (w k : E)) = (w k : E) * c (w k : E) := by
      rw [map_mul, ← AlgEquiv.mul_apply, mul_self_eq_one_of_quadratic c h2 hc, AlgEquiv.one_apply, mul_comm]
    obtain ⟨f, hf⟩ := exists_integer_of_fixed_integral c h2 hc _ hfix ⟨w k * cw, by simp [hcw]⟩
    have hmem : (∑ k ∈ s, a k ⊗ₜ[F] (w k : E)) *
        _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a k ⊗ₜ[F] (w k : E)) ∈ AddSubgroup.closure
        {z | ∃ a, P a ∧ ∃ x ∈ Set.range (algebraMap (𝓞 E) E), z = a ⊗ₜ[F] x} := by
      rw [hσ, ← hcw, Finset.sum_mul]
      refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ?_
      exact ⟨a j * a k, hmul _ _ (ha j) (ha k), _, ⟨w j * cw, rfl⟩, by
        rw [Algebra.TensorProduct.tmul_mul_tmul, map_mul]⟩
    obtain ⟨m, hm, e'⟩ := exists_add_sg_eq_tmul_one_of_mem_closure c h2 hc P h0 hadd hneg hsm _ hmem
    refine ⟨n + m + algebraMap F _ (f : F) * (a k * a k),
      hadd _ _ (hadd _ _ hn hm) (hsm f _ (hmul _ _ (ha k) (ha k))), ?_⟩
    have hN : (a k ⊗ₜ[F] (w k : E)) * (a k ⊗ₜ[F] c (w k : E)) =
        (algebraMap F _ (f : F) * (a k * a k)) ⊗ₜ[F] (1 : E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    rw [Finset.sum_insert hk, map_add, TensorProduct.add_tmul, TensorProduct.add_tmul, ← e, ← e',
      map_mul, sg_sg_of_quadratic c h2 hc, hσ]
    linear_combination hN

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in

theorem _root_.GlobalTheory.AdLat.exists_integral_unit_root : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → ∀ u ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), u * _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), (∃ y ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), x * y = 1) ∧ x = u * _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c x := by
  intro F E _ _ _ _ _ c h2 hc hP u hu hnorm
  classical
  have hσ : ∀ b (x : E), _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (b ⊗ₜ[F] x) =
      b ⊗ₜ[F] c x := fun b x => by simp [_root_.GlobalTheory.AdLat.sg]
  set σ := _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c with hσdef
  have hcc := mul_self_eq_one_of_quadratic c h2 hc
  have hσσ : ∀ z, σ (σ z) = z := sg_sg_of_quadratic c h2 hc
  obtain ⟨n, r, t, s, hs, hrts⟩ := exists_sum_mul_sub_conj_eq_one c hP
  let X : Option (Fin n) → 𝓞 E := fun i => i.elim 1 t
  let CX : Option (Fin n) → 𝓞 E := fun i => i.elim 1 s
  let Y : Option (Fin n) → 𝓞 E := fun i => i.elim (-∑ k, r k * s k) r
  have hCX : ∀ i, (CX i : E) = c (X i : E) := by rintro (_ | k) <;> simp [X, CX, hs]
  have hXY : ∑ i, Y i * X i = 1 := by
    rw [Fintype.sum_option, ← hrts]
    simp only [X, Y, Option.elim_none, Option.elim_some, mul_one, mul_sub, Finset.sum_sub_distrib]
    ring
  have hCXY : ∑ i, Y i * CX i = 0 := by
    rw [Fintype.sum_option]
    simp only [CX, Y, Option.elim_none, Option.elim_some, mul_one]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun k _ => by ring
  let ρ : 𝓞 E →+* _root_.GlobalTheory.AdLat.RA F E :=
    (Algebra.TensorProduct.includeRight : E →ₐ[F] _root_.GlobalTheory.AdLat.RA F E).toRingHom.comp
      (algebraMap (𝓞 E) E)
  have hρ : ∀ x, ρ x = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) := fun x => rfl
  have hσX : ∀ i, σ (ρ (X i)) = ρ (CX i) := fun i => by rw [hρ, hσ, hρ, hCX]
  have hσCX : ∀ i, σ (ρ (CX i)) = ρ (X i) := fun i => by
    rw [hρ, hσ, hρ, hCX, ← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]
  let m : Option (Fin n) → _root_.GlobalTheory.AdLat.RA F E := fun i => ρ (X i) + u * ρ (CX i)
  have hum : ∀ i, u * σ (m i) = m i := fun i => by
    simp only [m, map_add, map_mul, hσX, hσCX]
    linear_combination ρ (X i) * hnorm
  let H := _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))
  have hρmem : ∀ x, ρ x ∈ H := fun x => _root_.GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  have hmul : ∀ a b, a ∈ H → b ∈ H → a * b ∈ H := fun a b ha hb =>
    _root_.GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩) ha hb
  have hσmem : ∀ z ∈ H, σ z ∈ H := fun z hz =>
    _root_.GlobalTheory.AdLat.galoisAut_mem_adelicCompletionOfElementSet F c (_root_.GlobalTheory.AdLat.UnitRoot.conj_mem c) hz
  have hmmem : ∀ i, m i ∈ H := fun i => add_mem (hρmem _) (hmul _ _ hu (hρmem _))
  let Pint : FiniteAdeleRing (𝓞 F) F → Prop := fun a => ∀ v, a v ∈ v.adicCompletionIntegers F
  have hsmI : ∀ (f : 𝓞 F) a, Pint a → Pint (algebraMap F _ (f : F) * a) := fun f a ha v =>
    _root_.GlobalTheory.AdLat.adele_mul_integral F
      ((_root_.GlobalTheory.AdLat.mem_range_iff_adele_integral F (f : F)).1 ⟨f, rfl⟩ v) (ha v)
  have h0I : Pint 0 := fun v => zero_mem _
  have haddI : ∀ a b, Pint a → Pint b → Pint (a + b) := fun a b ha hb v =>
    _root_.GlobalTheory.AdLat.adele_add_integral F (ha v) (hb v)
  have hnegI : ∀ a, Pint a → Pint (-a) := fun a ha v => neg_mem (ha v)
  have hmulI : ∀ a b, Pint a → Pint b → Pint (a * b) := fun a b ha hb v =>
    _root_.GlobalTheory.AdLat.adele_mul_integral F (ha v) (hb v)
  have hp : ∀ i j, ∃ q, Pint q ∧ m i * σ (m j) = q ⊗ₜ[F] (1 : E) := by
    intro i j
    obtain ⟨q, hq, e⟩ := exists_add_sg_eq_tmul_one_of_mem_closure c h2 hc Pint h0I haddI hnegI hsmI (ρ (X i) * σ (m j))
      (hmul _ _ (hρmem _) (hσmem _ (hmmem j)))
    refine ⟨q, hq, ?_⟩
    rw [← e, map_mul, hσσ, hσX]
    have := hum j
    simp only [m] at this ⊢
    linear_combination ρ (CX i) * this
  choose p hpint hpe using hp
  let Pv : HeightOneSpectrum (𝓞 F) → FiniteAdeleRing (𝓞 F) F → Prop := fun v a =>
    Pint a ∧ Valued.v (a v) < 1
  have hkey : ∀ v, ∃ ij : Option (Fin n) × Option (Fin n), ¬ Valued.v (p ij.1 ij.2 v) < 1 := by
    intro v
    by_contra hcon
    push_neg at hcon
    choose cy hcy using fun j => _root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨Y j, rfl⟩
    have h1 : ∑ i, ρ (Y i) * m i = 1 := by
      simp only [m, mul_add, Finset.sum_add_distrib, mul_left_comm _ u, ← Finset.mul_sum,
        ← map_mul, ← map_sum, hXY, hCXY, map_one, map_zero, mul_zero, add_zero]
    have h1' : ∑ j, ρ (cy j) * σ (m j) = 1 := by
      have := congrArg σ h1
      rw [map_sum, map_one] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hρ (Y j), hσ, ← hcy]
      rfl
    have hZ : ∑ ij : Option (Fin n) × Option (Fin n),
        p ij.1 ij.2 ⊗ₜ[F] ((Y ij.1 * cy ij.2 : 𝓞 E) : E) = 1 := by
      rw [← mul_one (1 : _root_.GlobalTheory.AdLat.RA F E)]
      nth_rewrite 1 [← h1]
      rw [← h1', Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [show ρ (Y ij.1) * m ij.1 * (ρ (cy ij.2) * σ (m ij.2)) =
          ρ (Y ij.1 * cy ij.2) * (m ij.1 * σ (m ij.2)) by rw [map_mul]; ring, hpe, hρ,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have h0v : Pv v 0 := ⟨h0I, by
      show Valued.v (0 : v.adicCompletion F) < 1
      rw [map_zero]; exact zero_lt_one⟩
    have haddv : ∀ a b, Pv v a → Pv v b → Pv v (a + b) := fun a b ha hb =>
      ⟨haddI a b ha.1 hb.1, by
        show Valued.v (a v + b v) < 1
        exact Valuation.map_add_lt _ ha.2 hb.2⟩
    have hnegv : ∀ a, Pv v a → Pv v (-a) := fun a ha =>
      ⟨hnegI a ha.1, by
        show Valued.v (-(a v)) < 1
        rw [Valuation.map_neg]; exact ha.2⟩
    have hmulv : ∀ a b, Pint a → Pv v b → Pv v (a * b) := fun a b ha hb =>
      ⟨hmulI a b ha hb.1, by
        show Valued.v (a v * b v) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (ha v))) hb.2⟩
    have hPv : ∀ ij : Option (Fin n) × Option (Fin n), Pv v (p ij.1 ij.2) :=
      fun ij => ⟨hpint ij.1 ij.2, hcon ij⟩
    clear_value m ρ H X CX Y
    obtain ⟨N, hN, eN⟩ := exists_norm_sum_tmul_eq_tmul_one c h2 hc (Pv v) h0v haddv hnegv
      (fun f a ha => by
        have := hmulv _ a (hsmI f 1 (_root_.GlobalTheory.AdLat.adele_one_integral F)) ha
        rwa [mul_one] at this)
      (fun a b ha hb => hmulv a b ha.1 hb) Finset.univ
      (fun ij : Option (Fin n) × Option (Fin n) => p ij.1 ij.2)
      (fun ij : Option (Fin n) × Option (Fin n) => Y ij.1 * cy ij.2) hPv
    beta_reduce at eN
    rw [hZ, map_one, mul_one, Algebra.TensorProduct.one_def] at eN
    have hN1 : N = 1 := (Algebra.TensorProduct.includeLeft_injective (R := F)
      (S := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E) (algebraMap F E).injective eN).symm
    have := hN.2
    rw [hN1] at this
    exact absurd this (by
      show ¬ Valued.v (1 : v.adicCompletion F) < 1
      rw [map_one]; exact lt_irrefl 1)
  choose ij hij using hkey
  have hval1 : ∀ v, Valued.v (p (ij v).1 (ij v).2 v) = 1 := fun v =>
    le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hpint _ _ v)) (not_lt.1 (hij v))
  have hne : ∀ v, p (ij v).1 (ij v).2 v ≠ 0 := fun v h => by
    have := hval1 v; rw [h, map_zero] at this; exact zero_ne_one this
  have hE0 : ∀ (q : Option (Fin n) × Option (Fin n)) (v : HeightOneSpectrum (𝓞 F)),
      (if ij v = q then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro q v; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hD0 : ∀ v : HeightOneSpectrum (𝓞 F),
      (p (ij v).1 (ij v).2 v)⁻¹ ∈ v.adicCompletionIntegers F := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval1, inv_one]
  let e : Option (Fin n) × Option (Fin n) → FiniteAdeleRing (𝓞 F) F := fun q =>
    ⟨fun v => if ij v = q then 1 else 0, Filter.Eventually.of_forall fun v => hE0 q v⟩
  let d : FiniteAdeleRing (𝓞 F) F :=
    ⟨fun v => (p (ij v).1 (ij v).2 v)⁻¹, Filter.Eventually.of_forall hD0⟩
  have heI : ∀ q, Pint (e q) := fun q v => hE0 q v
  have hdI : Pint d := hD0
  let ev : ∀ v : HeightOneSpectrum (𝓞 F), FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F := fun v =>
    { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  have hsum1 : d * ∑ q : Option (Fin n) × Option (Fin n), ∑ q' : Option (Fin n) × Option (Fin n),
      e q * e q' * p q.1 q'.2 = 1 := by
    apply FiniteAdeleRing.ext F
    intro v
    have := map_sum (ev v) (fun q => ∑ q' : Option (Fin n) × Option (Fin n), e q * e q' * p q.1 q'.2)
      Finset.univ
    show d v * (ev v) _ = 1
    rw [this]
    have hevv : ∀ a : FiniteAdeleRing (𝓞 F) F, ev v a = a v := fun _ => rfl
    have hev : ∀ q, e q v = if ij v = q then 1 else 0 := fun _ => rfl
    have hdv : d v = (p (ij v).1 (ij v).2 v)⁻¹ := rfl
    simp only [map_sum, map_mul]
    simp only [hevv, hev, hdv, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact inv_mul_cancel₀ (hne v)
  refine ⟨∑ q, (e q ⊗ₜ[F] (1 : E)) * m q.1, ?_, ⟨(d ⊗ₜ[F] (1 : E)) *
    ∑ q, (e q ⊗ₜ[F] (1 : E)) * σ (m q.2), ?_, ?_⟩, ?_⟩
  · exact AddSubgroup.sum_mem _ fun q _ => hmul _ _
      (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F (heI q) ⟨1, map_one _⟩) (hmmem _)
  · exact hmul _ _ (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F hdI ⟨1, map_one _⟩)
      (AddSubgroup.sum_mem _ fun q _ => hmul _ _
        (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F (heI q) ⟨1, map_one _⟩) (hσmem _ (hmmem _)))
  · rw [mul_left_comm, Finset.sum_mul_sum]
    have hterm : ∀ q q' : Option (Fin n) × Option (Fin n),
        (e q ⊗ₜ[F] (1 : E)) * m q.1 * ((e q' ⊗ₜ[F] (1 : E)) * σ (m q'.2)) =
          (e q * e q' * p q.1 q'.2) ⊗ₜ[F] (1 : E) := fun q q' => by
      rw [show (e q ⊗ₜ[F] (1 : E)) * m q.1 * ((e q' ⊗ₜ[F] (1 : E)) * σ (m q'.2)) =
        (e q ⊗ₜ[F] (1 : E)) * (e q' ⊗ₜ[F] (1 : E)) * (m q.1 * σ (m q'.2)) by ring, hpe,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
    simp only [hterm, ← TensorProduct.sum_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsum1]
    rfl
  · rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, hσ, map_one, mul_left_comm, hum]

end GlobalTheory.AdLat
end

section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unit_root_norm_one_adele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → ∀ u ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (∃ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), x * y = 1) ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  first | exact @GlobalTheory.AdLat.exists_integral_unit_root | exact GlobalTheory.AdLat.exists_integral_unit_root | (intros; apply GlobalTheory.AdLat.exists_integral_unit_root <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); (∀ N : ℕ, 0 < N → IsOpen {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y}) ∧ ∀ W ∈ 𝓝 (0 : RA F E), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), N • y ∈ W := by
  first | exact @GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat | exact GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat | (intros; apply GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] , letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ e : (AdeleRing (𝓞 F) F ⊗[F] E) ≃+* (InfiniteAdeleRing F ⊗[F] E) × (FiniteAdeleRing (𝓞 F) F ⊗[F] E), (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z ∧ (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z) ∧ Continuous e ∧ Continuous e.symm := by
  first | exact @GlobalTheory.AdSplit.exists_adele_equiv | exact GlobalTheory.AdSplit.exists_adele_equiv | (intros; apply GlobalTheory.AdSplit.exists_adele_equiv <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

noncomputable section

namespace GlobalTheory.AdLat.RootNear

theorem inv_near {A R ι : Type} [CommRing A] [CommRing R] [Algebra A R] [TopologicalSpace A]
    [IsTopologicalRing A] [TopologicalSpace R] [IsModuleTopology A R] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A R) (i : A → A) (hi : ContinuousAt i 1) (hi1 : i 1 = 1)
    (hii : ∀ᶠ a in 𝓝 (1 : A), a * i a = 1) :
    ∀ V ∈ 𝓝 (1 : R), ∀ᶠ x in 𝓝 (1 : R), ∃ y ∈ V, x * y = 1 := by
  intro V hV
  have : ContinuousAdd R := IsModuleTopology.toContinuousAdd A R
  have hM : Continuous (fun x : R => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hb : Continuous (b.equivFun.symm) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  let d : R → A := fun x => (Algebra.leftMulMatrix b x).det
  let adj : R → R := fun x => b.equivFun.symm ((Algebra.leftMulMatrix b x).adjugate *ᵥ b.equivFun 1)
  have hd : Continuous d := hM.matrix_det
  have hadj : Continuous adj := hb.comp (hM.matrix_adjugate.matrix_mulVec continuous_const)
  have hd1 : d 1 = 1 := by simp [d]
  have hadj1 : adj 1 = 1 := by simp [adj]
  have key : ∀ x, x * adj x = d x • (1 : R) := by
    intro x
    apply b.equivFun.injective
    have h1 : ∀ y : R, b.equivFun (x * y) = Algebra.leftMulMatrix b x *ᵥ b.equivFun y := by
      intro y
      have := Algebra.leftMulMatrix_mulVec_repr b x y
      simpa using this.symm
    rw [h1, map_smul]
    simp only [adj, d, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdt : Filter.Tendsto d (𝓝 1) (𝓝 1) := by
    have := hd.tendsto 1
    rwa [hd1] at this
  have hy : Filter.Tendsto (fun x => i (d x) • adj x) (𝓝 1) (𝓝 1) := by
    have h1 : Filter.Tendsto (fun x => i (d x)) (𝓝 1) (𝓝 1) := by
      have := hi.tendsto
      rw [hi1] at this
      exact this.comp hdt
    have h2 := h1.smul (hadj.tendsto 1)
    simpa [hadj1] using h2
  filter_upwards [hy hV, hdt hii] with x h1 h2
  refine ⟨_, h1, ?_⟩
  rw [mul_smul_comm, key, smul_smul, mul_comm, h2, one_smul]

theorem unit_of_integral {A O : Type} [CommRing A] [CommRing O] (φ : A →+* O) (hφ : φ.IsIntegral) (j : A)
    (hj : ∀ a, IsUnit (1 + j * a)) (z : O) : IsUnit (1 + φ j * z) := by
  by_contra h
  obtain ⟨M, hM, hx⟩ := exists_max_ideal_of_mem_nonunits h
  have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφ M
  have hjm : j ∈ M.comap φ := by
    have : j ∈ Ideal.jacobson (⊥ : Ideal A) := by
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [add_comm]; exact hj y
    exact Ideal.mem_sInf.1 this ⟨bot_le, hm⟩
  apply hM.ne_top
  rw [Ideal.eq_top_iff_one]
  have := M.sub_mem hx (M.mul_mem_right z (Ideal.mem_comap.1 hjm))
  simpa using this

theorem exists_idem {ι : Type} (O : ι → Type) [∀ v, CommRing (O v)] [∀ v, IsLocalRing (O v)] (n : ℕ) :
    ∃ e f : ∀ v, O v, e * e = e ∧ 1 - e = n * f ∧ ∀ a, IsUnit (1 + e * n * a) := by
  classical
  refine ⟨fun v => if IsUnit (n : O v) then 0 else 1,
    fun v => if IsUnit (n : O v) then Ring.inverse (n : O v) else 0, ?_, ?_, ?_⟩
  · funext v
    by_cases h : IsUnit (n : O v) <;> simp [h]
  · funext v
    by_cases h : IsUnit (n : O v) <;> simp [h, Ring.mul_inverse_cancel]
  · intro a
    rw [Pi.isUnit_iff]
    intro v
    by_cases h : IsUnit (n : O v)
    · simp [h]
    · have h2 : -((n : O v) * a v) ∈ nonunits (O v) := by
        intro h3
        exact h (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h3))
      simpa [h] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h2

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def incl : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := (⟨fun v => (a v : v.adicCompletion F), Filter.Eventually.of_forall fun v => (a v).2⟩ :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => v.adicCompletionIntegers F) Filter.cofinite)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [NumberField E] in
theorem tmul_mem (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (x : 𝓞 E) :
    a ⊗ₜ[F] (algebraMap (𝓞 E) E x) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
  AddSubgroup.subset_closure ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩

omit [NumberField E] in
theorem mul_mem_hat {a b : RA F E} (ha : a ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hb : b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) : a * b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  induction ha, hb using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    obtain ⟨b, hb, _, ⟨t, rfl⟩, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
    exact tmul_mem F E (a * b) (fun v => (v.adicCompletionIntegers F).mul_mem _ _ (ha v) (hb v)) (s * t)
  | zero_left x hx => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | zero_right x hx => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
  | neg_left x y _ _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
  | neg_right x y _ _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h

def intHat : Subring (RA F E) where
  carrier := hat1 F (Set.range (algebraMap (𝓞 E) E))
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  neg_mem' := AddSubgroup.neg_mem _
  one_mem' := by
    have := tmul_mem F E 1 (fun v => one_mem _) 1
    rw [map_one] at this
    exact this
  mul_mem' := mul_mem_hat F E

def inclHat : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* intHat F E :=
  ((Algebra.TensorProduct.includeLeftRingHom : FiniteAdeleRing (𝓞 F) F →+* RA F E).comp (incl F)).codRestrict
    (intHat F E) (fun a => by
      have := tmul_mem F E (incl F a) (fun v => (a v).2) 1
      rw [map_one] at this
      exact this)

def ratHat : 𝓞 E →+* intHat F E :=
  ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict
    (intHat F E) (fun x => tmul_mem F E 1 (fun v => one_mem _) x)

theorem inclHat_integral : (inclHat F E).IsIntegral := by
  letI := (inclHat F E).toAlgebra
  rintro ⟨z, hz⟩
  change IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (⟨z, hz⟩ : intHat F E)
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    have h1 : IsIntegral ℤ (ratHat F E s) :=
      (RingOfIntegers.isIntegral s).map (ratHat F E).toIntAlgHom
    have h2 : IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (ratHat F E s) :=
      h1.tower_top
    have h3 := (isIntegral_algebraMap (A := intHat F E)
      (x := (fun v => ⟨a v, ha v⟩ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F))).mul h2
    refine Eq.mpr (congrArg (IsIntegral _) (Subtype.ext ?_)) h3
    change _ = (a ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E s))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | zero => exact isIntegral_zero
  | add x y _ _ h1 h2 => exact h1.add h2
  | neg x _ h => exact h.neg

omit [NumberField E] in
theorem half_root {A : Type} [CommRing A] [Algebra F A] (c : E ≃ₐ[F] E) (u x : A ⊗[F] E)
    (hu : u * sg A c u = 1) (hx : 2 * x = 1 + u) : x = u * sg A c x := by
  have h2 : IsUnit (2 : A ⊗[F] E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (A ⊗[F] E))
    rwa [map_ofNat] at this
  apply h2.mul_left_cancel
  have := congrArg (sg A c) hx
  rw [map_mul, map_ofNat, map_add, map_one] at this
  linear_combination hx - u * this - hu

theorem finite_root (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (u z : RA F E) (hz : z ∈ intHat F E) (huz : u - 1 = (2 * n) • z)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x y : RA F E, x * y = 1 ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧
      (∃ p ∈ intHat F E, x = 1 + n • p) ∧ ∃ p ∈ intHat F E, y = 1 + n • p := by
  have hu1 : u = 1 + 2 * n * z := by
    rw [nsmul_eq_mul] at huz
    push_cast at huz
    linear_combination huz
  have huO : u ∈ intHat F E := by
    rw [hu1]
    exact add_mem (one_mem _) (mul_mem (mul_mem (ofNat_mem _ 2) (natCast_mem _ n)) hz)
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun ⟨z, hz⟩).exists_right_inv
  have hr₀ : (1 + n * z) = u * sg (FiniteAdeleRing (𝓞 F) F) c (1 + n * z) :=
    half_root F E c u _ hu (by rw [hu1]; ring)
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * z) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  have hxy : (e' * (1 + n * z) + (1 - e') * x₁) * (e' * y' + (1 - e') * y₁) = 1 := by
    linear_combination e' * hy₀' + (1 - e') * hxy₁ +
      (y' - (1 + n * z) * y₁ - x₁ * y' + x₁ * y₁) * hee'
  have hp : e' * z + f' * (x₁ - 1) ∈ intHat F E :=
    add_mem (mul_mem heO hz) (mul_mem hfO (sub_mem hx₁' (one_mem _)))
  have hx : e' * (1 + n * z) + (1 - e') * x₁ = 1 + n * (e' * z + f' * (x₁ - 1)) := by
    linear_combination (x₁ - 1) * hef'
  refine ⟨_, _, hxy, ?_, ⟨_, hp, by rw [nsmul_eq_mul]; exact hx⟩,
    -((e' * y' + (1 - e') * y₁) * (e' * z + f' * (x₁ - 1))), ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, map_sub, map_one, hse]
    linear_combination e' * hr₀ + (1 - e') * hr₁
  · exact neg_mem (mul_mem (add_mem (mul_mem heO hy₀O) (mul_mem (sub_mem (one_mem _) heO) hy₁')) hp)
  · rw [nsmul_eq_mul]
    rw [hx] at hxy
    linear_combination hxy

theorem finite_near (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) :
    letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
    ∀ V ∈ 𝓝 (1 : RA F E), ∀ᶠ u in 𝓝 (1 : RA F E), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
  have : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E) := ⟨rfl⟩
  have : ContinuousAdd (RA F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  intro V hV
  let L : Submodule (𝓞 E) (Fin 1 → E) :=
    Submodule.pi Set.univ (fun _ => LinearMap.range (Algebra.linearMap (𝓞 E) E))
  have hL : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : (fun _ => (1 : E)) ∈ L := fun i _ => ⟨1, map_one (algebraMap (𝓞 E) E)⟩
    have h3 := Submodule.smul_mem _ (v 0) (Submodule.subset_span (R := E) h1)
    convert h3 using 1
    funext i
    rw [Subsingleton.elim i 0]
    simp
  obtain ⟨hopen, hbas⟩ := GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet F E 1 L hL
  have hV0 : {y : RA F E | 1 + y ∈ V} ∈ 𝓝 (0 : RA F E) := by
    have : Continuous (fun y : RA F E => 1 + y) := continuous_const_add 1
    have h := this.tendsto 0
    rw [add_zero] at h
    exact h hV
  obtain ⟨n, hn, hnV⟩ := hbas _ hV0
  have hhat : ∀ y ∈ hat F (L : Set (Fin 1 → E)), y 0 ∈ intHat F E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hx
      obtain ⟨s, hs⟩ := hw 0 (Set.mem_univ _)
      have := tmul_mem F E a ha s
      change a ⊗ₜ[F] (w 0) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))
      rw [← hs]
      exact this
    | zero => exact zero_mem _
    | add x y _ _ h1 h2 => exact add_mem h1 h2
    | neg x _ h => exact neg_mem h
  have hcont : Continuous (fun (u : RA F E) (_ : Fin 1) => u + (-1)) :=
    continuous_pi fun _ => continuous_id.add continuous_const
  have hN := ((hopen (2 * n) (by omega)).preimage hcont).mem_nhds (x := 1)
    ⟨0, zero_mem _, by funext i; simp⟩
  filter_upwards [hN] with u hu hn1
  obtain ⟨z, hz, hz2⟩ := hu
  have hz3 : u - 1 = (2 * n) • z 0 := by
    rw [sub_eq_add_neg]
    exact congrFun hz2 0
  obtain ⟨x, y, hxy, hx, ⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩ := finite_root F E c h2 hc hP n u (z 0) (hhat z hz) hz3 hn1
  exact ⟨_, hnV p hp, _, hnV q hq, hxy, hx⟩

theorem infinite_near (c : E ≃ₐ[F] E) :
    letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
      moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
    ∀ V ∈ 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E), ∀ᶠ u in 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E),
      u * sg (InfiniteAdeleRing F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (InfiniteAdeleRing F) c x := by
  classical
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  have : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) :=
    IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
  intro V hV
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hev : ∀ v : InfinitePlace F, Continuous (fun a : InfiniteAdeleRing F => a v) :=
    fun v => continuous_apply v
  have hinv := inv_near (Algebra.TensorProduct.basis (InfiniteAdeleRing F) (Module.finBasis F E))
    (fun a v => (a v)⁻¹)
    (continuousAt_pi.2 fun v => ((hev v).continuousAt (x := 1)).inv₀ (one_ne_zero))
    (funext fun v => inv_one)
    (by
      have : ∀ v : InfinitePlace F, ∀ᶠ a in 𝓝 (1 : InfiniteAdeleRing F), a v ≠ 0 :=
        fun v => ((hev v).continuousAt (x := 1)).eventually_ne one_ne_zero
      filter_upwards [Filter.eventually_all.2 this] with a ha
      exact funext fun v => mul_inv_cancel₀ (ha v)) V hV
  let h : InfiniteAdeleRing F := algebraMap F _ 2⁻¹
  have hh : ∀ w : InfiniteAdeleRing F ⊗[F] E, 2 * (h • w) = w := by
    intro w
    rw [algebraMap_smul, ← map_ofNat (algebraMap F (InfiniteAdeleRing F ⊗[F] E)) 2, ← Algebra.smul_def,
      smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]
  have hcont : Continuous (fun u : InfiniteAdeleRing F ⊗[F] E => h • (1 + u)) :=
    (continuous_const.add continuous_id).const_smul h
  have ht := hcont.tendsto 1
  have h11 : h • ((1 : InfiniteAdeleRing F ⊗[F] E) + 1) = 1 := by
    rw [smul_add, ← two_mul, hh]
  rw [h11] at ht
  filter_upwards [ht hV, ht hinv] with u h1 h3 hu
  obtain ⟨y, hy, hxy⟩ := h3
  exact ⟨_, h1, y, hy, hxy, half_root F E c u _ hu (hh _)⟩

theorem units_nhds {M : Type} [Monoid M] [TopologicalSpace M] (W : Set Mˣ) (hW : W ∈ 𝓝 (1 : Mˣ)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ x : Mˣ, (x : M) ∈ V → ((x⁻¹ : Mˣ) : M) ∈ V → x ∈ W := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨T, hT, hTW⟩ := hW
  rw [map_one] at hT
  obtain ⟨V₁, h₁, V₂, h₂, hsub⟩ := mem_nhds_prod_iff.1 hT
  have h₃ : MulOpposite.op ⁻¹' V₂ ∈ 𝓝 (1 : M) := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds h₂
  exact ⟨_, Filter.inter_mem h₁ h₃, fun x hx hy => hTW (hsub ⟨hx.1, hy.2⟩)⟩

omit [NumberField F] [NumberField E] in
theorem map_sg {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (c : E ≃ₐ[F] E)
    (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.TensorProduct.map p (AlgHom.id F E) (sg A c z) =
      sg B c (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sg]
  | add x y h1 h2 => simp only [map_add, h1, h2]

theorem exists_root_near : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∀ W ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∃ N ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∀ u ∈ N, (u : AdeleRing (𝓞 F) F ⊗[F] E) * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ W, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c x := by
  intro F E _ _ _ _ _ c h2 hc hP
  letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)
  letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  intro W hW
  obtain ⟨V, hV, hVW⟩ := units_nhds W hW
  obtain ⟨e, he, hec, hes⟩ := GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite F E
  have hs1 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).1 = sg _ c (e z).1 := fun z => by
    rw [(he _).1, (he _).1]
    exact map_sg F E c _ z
  have hs2 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).2 = sg _ c (e z).2 := fun z => by
    rw [(he _).2, (he _).2]
    exact map_sg F E c _ z
  have hV' : e.symm ⁻¹' V ∈ 𝓝 (1 : (InfiniteAdeleRing F ⊗[F] E) × RA F E) :=
    hes.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V₁, h₁, V₂, h₂, hsub⟩ := mem_nhds_prod_iff.1 hV'
  have ht : Filter.Tendsto (fun u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ => e u) (𝓝 1) (𝓝 1) := by
    have := (hec.comp Units.continuous_val).tendsto 1
    simpa [Function.comp_def] using this
  have ht1 := (continuous_fst.tendsto _).comp ht
  have ht2 := (continuous_snd.tendsto _).comp ht
  refine ⟨_, Filter.inter_mem (ht1 (infinite_near F E c V₁ h₁)) (ht2 (finite_near F E c h2 hc hP V₂ h₂)), ?_⟩
  rintro u ⟨hu1, hu2⟩ hu
  have heu := congrArg e hu
  rw [map_mul, map_one] at heu
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁, hr₁⟩ := hu1 (by
    have := congrArg Prod.fst heu
    rw [Prod.fst_mul, hs1] at this
    exact this)
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂, hr₂⟩ := hu2 (by
    have := congrArg Prod.snd heu
    rw [Prod.snd_mul, hs2] at this
    exact this)
  have hxy : e.symm (x₁, x₂) * e.symm (y₁, y₂) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, hxy₁, hxy₂]
    exact map_one _
  refine ⟨⟨e.symm (x₁, x₂), e.symm (y₁, y₂), hxy, by rw [mul_comm]; exact hxy⟩,
    hVW _ (hsub (⟨hx₁, hx₂⟩ : (x₁, x₂) ∈ V₁ ×ˢ V₂)) (hsub (⟨hy₁, hy₂⟩ : (y₁, y₂) ∈ V₁ ×ˢ V₂)), ?_⟩
  apply e.injective
  change e (e.symm (x₁, x₂)) = e (u * sg (AdeleRing (𝓞 F) F) c (e.symm (x₁, x₂)))
  rw [map_mul]
  apply Prod.ext
  · rw [Prod.fst_mul, hs1, e.apply_symm_apply]
    exact hr₁
  · rw [Prod.snd_mul, hs2, e.apply_symm_apply]
    exact hr₂

end GlobalTheory.AdLat.RootNear
end
end
