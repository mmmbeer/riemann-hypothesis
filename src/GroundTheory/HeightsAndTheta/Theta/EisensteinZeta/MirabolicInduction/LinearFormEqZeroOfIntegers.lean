import Mathlib
import GroundTheory.HeightsAndTheta.Theta.UnitaryReduction.UnipotentRadicalPlaces
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

namespace DualHomPf

open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate

section NumberFieldFacts

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

open Classical

private theorem embedding_ne_conjugate (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hr : InfinitePlace.IsReal w := InfinitePlace.isReal_iff.mpr
    (ComplexEmbedding.isReal_iff.mpr h.symm)
  exact (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) hr

end NumberFieldFacts

section DualLattice

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem mem_two_invDiff_iff (t : E) :
    t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E ↔
      ∀ c : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((c : E) * t) = 2 * n := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩ c
    rw [invDiff, FractionalIdeal.mem_dual h1] at hy
    obtain ⟨n, hn⟩ := hy (c : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨c, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    have : (c : E) * (2 * y) = (2 : ℚ) • (y * c) := by
      rw [Algebra.smul_def, map_ofNat]; ring
    rw [this, LinearMap.map_smul, ← hn]
    simp
  · intro h
    refine ⟨(2 : E)⁻¹ * t, ?_, by field_simp⟩
    rw [invDiff, FractionalIdeal.mem_dual h1]
    intro a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := h c
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    have : (2 : E)⁻¹ * t * algebraMap (𝓞 E) E c = (2⁻¹ : ℚ) • ((c : E) * t) := by
      rw [Algebra.smul_def]; simp only [map_inv₀, map_ofNat]; ring
    rw [this, LinearMap.map_smul, hn]
    simp

end DualLattice

section DualBasis

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_extend_of_submodule (A : Submodule (𝓞 E) V) (s : A →ₗ[𝓞 E] 𝓞 E) :
    ∃ σ : V →ₗ[E] E, ∀ x : A, σ (x : V) = ((s x : 𝓞 E) : E) := by
  classical
  obtain ⟨bs, hbA, _hspan, hli⟩ := exists_linearIndependent E (A : Set V)
  let bb := Basis.span hli
  let σ₀ := bb.constr E (fun i : bs => ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E))
  obtain ⟨σ, hσ⟩ := LinearMap.exists_extend σ₀
  have hrange : Set.range ((↑) : bs → V) = bs := Subtype.range_coe
  have hσb : ∀ i : bs, σ (i : V) = ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E) := by
    intro i
    have hi : (i : V) ∈ Submodule.span E (Set.range ((↑) : bs → V)) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 : σ (i : V) = σ₀ ⟨i, hi⟩ := by
      rw [← hσ]; rfl
    have h2 : (⟨i, hi⟩ : Submodule.span E (Set.range ((↑) : bs → V))) = bb i := by
      ext; rw [Basis.span_apply]
    rw [h1, h2, Basis.constr_basis]

  have hP : ∀ y ∈ Submodule.span (𝓞 E) (bs : Set V), ∀ hy : y ∈ A,
      σ y = ((s ⟨y, hy⟩ : 𝓞 E) : E) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => intro hxA; exact hσb ⟨x, hx⟩
    | zero => intro h0; simp [show (⟨0, h0⟩ : A) = 0 from rfl]
    | add x y hx hy ihx ihy =>
      intro hxyA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have hyA : y ∈ A := Submodule.span_le.mpr hbA hy
      rw [map_add, ihx hxA, ihy hyA, show (⟨x + y, hxyA⟩ : A) = ⟨x, hxA⟩ + ⟨y, hyA⟩ from rfl,
        map_add]
      push_cast; rfl
    | smul c x hx ihx =>
      intro hcxA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have e1 : σ (c • x) = (c : E) * σ x := by
        rw [← algebraMap_smul E c x, LinearMap.map_smul, smul_eq_mul,
          RingOfIntegers.coe_eq_algebraMap]
      have e2 : s ⟨c • x, hcxA⟩ = c * s ⟨x, hxA⟩ := by
        rw [show (⟨c • x, hcxA⟩ : A) = c • ⟨x, hxA⟩ from rfl, LinearMap.map_smul, smul_eq_mul]
      rw [e1, e2, ihx hxA]
      simp
  refine ⟨σ, fun x => ?_⟩
  have hx : (x : V) ∈ Submodule.span E (bs : Set V) := by
    rw [_hspan]; exact Submodule.subset_span x.2
  obtain ⟨m, c, v, hv, hxv⟩ : ∃ (m : ℕ) (c : Fin m → E) (v : Fin m → V), (∀ i, v i ∈ bs) ∧
      (x : V) = ∑ i, c i • v i := by
    obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').mp hx
    exact ⟨m, c, fun i => (g i : V), fun i => (g i).2, hg.symm⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ c
  choose o ho using fun i => hd i (Finset.mem_univ i)
  have hdx : ((d : 𝓞 E) : E) • (x : V) = ∑ i, o i • v i := by
    rw [hxv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (o i) (v i), ho i, Algebra.smul_def, mul_smul,
      RingOfIntegers.coe_eq_algebraMap]
  have hyP : ∑ i, o i • v i ∈ Submodule.span (𝓞 E) (bs : Set V) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hv i))
  have hyA : ∑ i, o i • v i ∈ A := Submodule.span_le.mpr hbA hyP
  have key := hP _ hyP hyA
  have hyeq : (⟨∑ i, o i • v i, hyA⟩ : A) = (d : 𝓞 E) • x := by
    apply Subtype.ext
    change (∑ i, o i • v i) = (d : 𝓞 E) • (x : V)
    rw [← hdx, ← algebraMap_smul E (d : 𝓞 E) (x : V), RingOfIntegers.coe_eq_algebraMap]
  rw [hyeq, map_smul, smul_eq_mul, ← hdx, map_smul, smul_eq_mul] at key
  have hd0 : ((d : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero d (by exact_mod_cast h)
  push_cast at key
  exact mul_left_cancel₀ hd0 key

end DualBasis

section DualBasis2

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_dualBasis (A : Submodule (𝓞 E) V) (hA : A.FG) :
    ∃ (n : ℕ) (a : Fin n → V) (σ : Fin n → (V →ₗ[E] E)),
      (∀ i, a i ∈ A) ∧ (∀ i, ∀ x ∈ A, σ i x ∈ Set.range (algebraMap (𝓞 E) E)) ∧
      ∀ x ∈ espan A, x = ∑ i, σ i x • a i := by
  classical
  have : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.mpr hA
  have : Module.Flat (𝓞 E) A := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have h1 : ((a : 𝓞 E) : E) • (x : V) = 0 := by
      rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
      exact congrArg Subtype.val ha
    have ha0 : ((a : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero a (by exact_mod_cast h)
    rw [Submodule.mem_bot]
    exact Subtype.ext ((smul_eq_zero.mp h1).resolve_left ha0)
  have : Module.FinitePresentation (𝓞 E) A := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) A := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) A
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose σ hσ using fun i : Fin n => exists_extend_of_submodule A ((LinearMap.proj i).comp h)
  have hxA : ∀ x : A, (x : V) = ∑ i, σ i x • (f (Pi.single i 1) : V) := by
    intro x
    have h1 : x = f (h x) := (LinearMap.congr_fun hh x).symm
    have h2 : h x = ∑ i, h x i • (Pi.single i 1 : Fin n → 𝓞 E) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1, h2]
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.coe_smul, hσ i x, ← algebraMap_smul E (h x i),
      RingOfIntegers.coe_eq_algebraMap]
    rfl
  refine ⟨n, fun i => (f (Pi.single i 1) : V), σ, fun i => (f (Pi.single i 1)).2, ?_, ?_⟩
  · intro i x hx
    exact ⟨h ⟨x, hx⟩ i, by rw [hσ i ⟨x, hx⟩, RingOfIntegers.coe_eq_algebraMap]; rfl⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hxA ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz =>
      conv_lhs => rw [hy, hz]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]
    | smul c y _ hy =>
      conv_lhs => rw [hy]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]

end DualBasis2

section Fibres

variable {E : Type} [Field E] [NumberField E]

variable (S : MetSpace E) (τ : InfinitePlace E)

theorem pt_smul' (e : E) (x : S.V) : S.pt τ (e • x) = τ.embedding e • S.pt τ x := by
  change (1 : CAt τ.embedding) ⊗ₜ[E] (e • x) = τ.embedding e • ((1 : CAt τ.embedding) ⊗ₜ[E] x)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', CAt.smul_def, CAt.complex_smul_def]

theorem pt_sum_smul' {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → S.V) :
    S.pt τ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, τ.embedding (c i) • S.pt τ (v i) := by
  change (1 : CAt τ.embedding) ⊗ₜ[E] (∑ i ∈ s, c i • v i) = _
  rw [TensorProduct.tmul_sum]
  exact Finset.sum_congr rfl fun i _ => pt_smul' S τ (c i) (v i)

theorem tmul_eq_smul_pt (z : CAt τ.embedding) (v : S.V) :
    (z ⊗ₜ[E] v : S.FibSp τ) = (CAt.ofComplex τ.embedding).symm z • S.pt τ v := by
  change z ⊗ₜ[E] v = (CAt.ofComplex τ.embedding).symm z • ((1 : CAt τ.embedding) ⊗ₜ[E] v)
  rw [TensorProduct.smul_tmul', CAt.complex_smul_def, AlgEquiv.apply_symm_apply, mul_one]

theorem fibSub_eq_span (W : Submodule E S.V) :
    S.fibSub W τ = Submodule.span ℂ (S.pt τ '' (W : Set S.V)) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z w =>
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      have hmem : S.pt τ (w : S.V) ∈ Submodule.span ℂ (S.pt τ '' (W : Set S.V)) :=
        Submodule.subset_span ⟨w, w.2, rfl⟩
      have h2 := (Submodule.span ℂ (S.pt τ '' (W : Set S.V))).smul_mem
        ((CAt.ofComplex τ.embedding).symm z) hmem
      rw [← tmul_eq_smul_pt] at h2
      exact h2
    | add y y' hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(1 : CAt τ.embedding) ⊗ₜ[E] (⟨w, hw⟩ : W), by
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]; rfl⟩

theorem fibMap_pt' (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (v : S.V) :
    S.fibMap T φ τ (S.pt τ v) = T.pt τ (φ v) := rfl

def fibFun (σ : S.V →ₗ[E] E) : S.FibSp τ →ₗ[ℂ] ℂ :=
  (S.dualFunctional τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) : S.FibSp τ →L[ℂ] ℂ)

theorem fibFun_pt (σ : S.V →ₗ[E] E) (v : S.V) :
    fibFun S τ σ (S.pt τ v) = τ.embedding (σ v) := by
  change (CAt.ofComplex τ.embedding).symm
    (S.dualCoord τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) ((1 : CAt τ.embedding) ⊗ₜ[E] v)) = _
  rw [dualCoord_tmul_tmul, one_mul, mul_one, CAt.algebraMap_apply, AlgEquiv.symm_apply_apply]

theorem dualBasis_at (A : Submodule (𝓞 E) S.V) {n : ℕ} (a : Fin n → S.V) (σ : Fin n → (S.V →ₗ[E] E))
    (hid : ∀ x ∈ espan A, x = ∑ i, σ i x • a i) {x : S.FibSp τ}
    (hx : x ∈ S.fibSub (espan A) τ) :
    x = ∑ i, fibFun S τ (σ i) x • S.pt τ (a i) := by
  rw [fibSub_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    conv_lhs => rw [hid w hw, pt_sum_smul']
    exact Finset.sum_congr rfl fun i _ => by rw [fibFun_pt]
  | zero => simp
  | add y z _ _ hy hz =>
    conv_lhs => rw [hy, hz]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]
  | smul c y _ hy =>
    conv_lhs => rw [hy]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]

end Fibres

section Adjoints

variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]

theorem trace_adjoint' (T : H₁ →ₗ[ℂ] H₁) :
    LinearMap.trace ℂ H₁ (LinearMap.adjoint T) = conj (LinearMap.trace ℂ H₁ T) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H₁),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H₁), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.adjoint_inner_right, inner_conj_symm]

theorem re_trace_comp_adjoint (X Y : H₁ →ₗ[ℂ] H₂) :
    (LinearMap.trace ℂ H₂ (X ∘ₗ LinearMap.adjoint Y)).re =
      (LinearMap.trace ℂ H₂ (Y ∘ₗ LinearMap.adjoint X)).re := by
  have e1 : LinearMap.trace ℂ H₂ (X ∘ₗ LinearMap.adjoint Y) =
      LinearMap.trace ℂ H₁ (LinearMap.adjoint Y ∘ₗ X) := by
    rw [LinearMap.trace_comp_comm']
  have e2 : LinearMap.trace ℂ H₂ (Y ∘ₗ LinearMap.adjoint X) =
      LinearMap.trace ℂ H₁ (LinearMap.adjoint X ∘ₗ Y) := by
    rw [LinearMap.trace_comp_comm']
  have e3 : LinearMap.adjoint (LinearMap.adjoint Y ∘ₗ X) = LinearMap.adjoint X ∘ₗ Y := by
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  rw [e1, e2, ← e3, trace_adjoint', Complex.conj_re]

theorem adjoint_maps (X : H₁ →ₗ[ℂ] H₂) (K₁ : Submodule ℂ H₁) (K₂ : Submodule ℂ H₂)
    (h1 : ∀ y ∈ K₁ᗮ, X y = 0) (h2 : ∀ y, X y ∈ K₂) :
    (∀ y ∈ K₂ᗮ, LinearMap.adjoint X y = 0) ∧ ∀ y, LinearMap.adjoint X y ∈ K₁ := by
  constructor
  · intro y hy
    refine ext_inner_left ℂ fun u => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact Submodule.inner_right_of_mem_orthogonal (h2 u) hy
  · intro y
    rw [← Submodule.orthogonal_orthogonal K₁, Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.adjoint_inner_right, h1 u hu, inner_zero_left]

end Adjoints

section IdealMaps

variable {E : Type} [Field E] [NumberField E]
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']

theorem map_smulIdeal_mem (aa : FractionalIdeal (𝓞 E)⁰ E) (A : Submodule (𝓞 E) V)
    (B : Submodule (𝓞 E) V') (U : V →ₗ[E] V') (hU : ∀ a ∈ A, U a ∈ B) {x : V}
    (hx : x ∈ smulIdeal aa A) : U x ∈ smulIdeal aa B := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, rfl⟩ := hy
    rw [LinearMap.map_smul]
    exact Submodule.subset_span ⟨c, hc, U a, hU a ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hy

end IdealMaps

section FibMaps

variable {E : Type} [Field E] [NumberField E]

theorem fibMap_fibSub (S T : MetSpace E) (τ : InfinitePlace E) (φ : S.V →ₗ[E] T.V)
    (W : Submodule E S.V) (W' : Submodule E T.V) (hφ : ∀ w ∈ W, φ w ∈ W') {y : S.FibSp τ}
    (hy : y ∈ S.fibSub W τ) : S.fibMap T φ τ y ∈ T.fibSub W' τ := by
  rw [fibSub_eq_span] at hy ⊢
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [fibMap_pt']; exact Submodule.subset_span ⟨φ v, hφ v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem pt_mem_fibSub (S : MetSpace E) (τ : InfinitePlace E) (W : Submodule E S.V) {w : S.V}
    (hw : w ∈ W) : S.pt τ w ∈ S.fibSub W τ := by
  rw [fibSub_eq_span]; exact Submodule.subset_span ⟨w, hw, rfl⟩

end FibMaps

end DualHomPf

open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace DualHomPf
open scoped InnerProductSpace nonZeroDivisors

end UnitaryReduction

end GroundTheory.Heights₂.Theta
