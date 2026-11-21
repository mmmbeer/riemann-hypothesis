import Mathlib
import GroundTheory.AutomorphicForms.QuotientKernel
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
import GroundTheory.AutomorphicForms.TraceClass
import GroundTheory.AutomorphicForms.TraceFormulaWeil

section
open MeasureTheory

namespace GroundTheory.Automorphic

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isCompactOperator_integrated (f : CompactlySupportedContinuousMap G ℂ) :
    IsCompactOperator ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) :=
  isCompactOperator_integrated_rightRegularRep Γ μ f


end RightCosetSpace

end GroundTheory.Automorphic
end

section
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct

namespace GroundTheory.Automorphic

noncomputable section

section Intermediate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem two_mul_traceNorm_comp_le_of_hilbertSchmidt (A : K →L[ℂ] H) (B : H →L[ℂ] K) :
    2 * traceNorm (A.comp B) ≤ hsNormSq A + hsNormSq B := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (A.comp B)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc 2 * traceNorm (A.comp B) ≤ 2 * ∑' i, ‖⟪V (b i), A (B (b i))⟫_ℂ‖ₑ := by
        gcongr; exact traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖((A†).comp V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← adjoint_inner_left, ← comp_apply (A†) V]
        calc 2 * ‖⟪((A†).comp V) (b i), B (b i)⟫_ℂ‖ₑ
            ≤ 2 * (‖((A†).comp V) (b i)‖ₑ * ‖B (b i)‖ₑ) := by gcongr; exact enorm_inner_le _ _
          _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
    _ = hsNormSq ((A†).comp V) + hsNormSq B := by
        rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
    _ ≤ ‖V‖ₑ ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr; exact hsNormSq_comp_right_le _ _
    _ ≤ 1 ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr
    _ = hsNormSq A + hsNormSq B := by rw [one_pow, one_mul, hsNormSq_adjoint]

theorem isTraceClass_comp_of_isHilbertSchmidt {A : K →L[ℂ] H} {B : H →L[ℂ] K}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) : IsTraceClass (A.comp B) := by
  have h := (two_mul_traceNorm_comp_le_of_hilbertSchmidt A B).trans_lt
    (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  rw [IsTraceClass]
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.mul_top two_ne_zero] at h
  exact lt_irrefl _ h

theorem isTraceClass_and_trace_eq_of_conj (e : H ≃ₗᵢ[ℂ] K) {T : H →L[ℂ] H} {S : K →L[ℂ] K}
    (hT : IsTraceClass T) (hS : ∀ v, S (e v) = e (T v)) : IsTraceClass S ∧ trace S = trace T := by
  have hS' : S = ((e : H →L[ℂ] K).comp T).comp (e.symm : K →L[ℂ] H) := by
    ext w
    obtain ⟨v, rfl⟩ := e.surjective w
    simp [hS]
  have hSc : IsTraceClass S := by
    obtain ⟨A, B, hA, hB, hAB⟩ := hT.exists_comp
    rw [hS', hAB, ← comp_assoc, comp_assoc]
    exact isTraceClass_comp_of_isHilbertSchmidt (hA.comp_left _) (hB.comp_right _)
  refine ⟨hSc, ?_⟩
  let b := stdHilbertBasis ℂ H
  let b' : HilbertBasis _ ℂ K := HilbertBasis.ofRepr (e.symm.trans b.repr)
  have hb' : ∀ i, b' i = e (b i) := fun i => rfl
  have h1 := hSc.hasSum_trace b'
  have h2 := hT.hasSum_trace b
  refine h1.unique (h2.congr_fun fun i => ?_)
  rw [hb', hS, LinearIsometryEquiv.inner_map_map]

end Intermediate

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

section Equiv

variable {μ : Measure G} {σ : UnitaryRep G K} {τ : UnitaryRep G L}

theorem Equiv.isTraceClass_integrated_and_trace_eq (e : σ.Equiv τ) (f : G →₁[μ] ℂ)
    (h : IsTraceClass (σ.integrated μ f)) :
    IsTraceClass (τ.integrated μ f) ∧ trace (τ.integrated μ f) = trace (σ.integrated μ f) := by
  refine isTraceClass_and_trace_eq_of_conj e.toLinearIsometryEquiv h fun v => ?_
  have := comp_integrated_of_mem_intertwiners σ μ e.mem_intertwiners f
  exact (congrArg (fun T : K →L[ℂ] L => T v) this).symm

theorem Equiv.trace_integrated (e : σ.Equiv τ) (f : G →₁[μ] ℂ)
    (h : IsTraceClass (σ.integrated μ f)) :
    trace (τ.integrated μ f) = trace (σ.integrated μ f) :=
  (e.isTraceClass_integrated_and_trace_eq f h).2

end Equiv

section Decomposition

variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))

theorem integrated_restrict_apply (j : J) (v : V j) :
    (((π.restrict (V j) (hinv j)).integrated μ f v : V j) : H) = π.integrated μ f (v : H) := by
  have := comp_integrated_of_mem_intertwiners (π.restrict (V j) (hinv j)) μ
    (subtypeL_mem_intertwiners π (V j) (hinv j)) f
  exact congrArg (fun T : V j →L[ℂ] H => T v) this

variable {π μ f}

theorem isTraceClass_integrated_restrict (hT : IsTraceClass (π.integrated μ f)) (j : J) :
    IsTraceClass ((π.restrict (V j) (hinv j)).integrated μ f) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := hT.exists_comp
  set ι : V j →L[ℂ] H := (V j).subtypeL
  have hιι : ∀ x : V j, (ι†) (ι x) = x := fun x =>
    ext_inner_left ℂ fun w => by
      rw [adjoint_inner_right]
      rfl
  have heq : (π.restrict (V j) (hinv j)).integrated μ f = ((ι†).comp A).comp (B.comp ι) := by
    ext1 x
    simp only [comp_apply]
    rw [← hιι ((π.restrict (V j) (hinv j)).integrated μ f x)]
    congr 1
    change (((π.restrict (V j) (hinv j)).integrated μ f x : V j) : H) = _
    rw [integrated_restrict_apply, hAB]
    rfl
  rw [heq]
  exact isTraceClass_comp_of_isHilbertSchmidt (hA.comp_left _) (hB.comp_right _)

variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)

def collectedHilbertBasis : HilbertBasis (Σ j, (exists_hilbertBasis ℂ (V j)).choose) ℂ H :=
  HilbertBasis.mk (v := fun a => (V a.1).subtypeₗᵢ (stdHilbertBasis ℂ (V a.1) a.2))
    (hsum.OrthogonalFamily.orthonormal_sigma_orthonormal fun j =>
      (stdHilbertBasis ℂ (V j)).orthonormal) (by
    refine le_trans (top_le_topologicalClosure_iSup hsum) (Submodule.topologicalClosure_minimal _
      (iSup_le fun j => ?_) (Submodule.isClosed_topologicalClosure _))
    intro v hv
    have hd := (stdHilbertBasis ℂ (V j)).dense_span
    have hmem : (⟨v, hv⟩ : V j) ∈
        (Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j)))).topologicalClosure := by
      rw [hd]; trivial
    have h1 := Submodule.topologicalClosure_map (V j).subtypeL
      (Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j))))
    have h2 : v ∈ ((Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j)))).map
        ((V j).subtypeL : V j →ₗ[ℂ] H)).topologicalClosure :=
      h1 ⟨⟨v, hv⟩, hmem, rfl⟩
    refine Submodule.topologicalClosure_mono ?_ h2
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨j, i⟩, rfl⟩)

theorem collectedHilbertBasis_apply (a : Σ j, (exists_hilbertBasis ℂ (V j)).choose) :
    collectedHilbertBasis hsum a = ((stdHilbertBasis ℂ (V a.1) a.2 : V a.1) : H) := by
  rw [collectedHilbertBasis, HilbertBasis.coe_mk]
  rfl

include hsum in

theorem hasSum_trace_integrated_restrict (hT : IsTraceClass (π.integrated μ f)) :
    HasSum (fun j => trace ((π.restrict (V j) (hinv j)).integrated μ f))
      (trace (π.integrated μ f)) := by
  have h1 := hT.hasSum_trace (collectedHilbertBasis hsum)
  refine h1.sigma fun j => ?_
  refine ((isTraceClass_integrated_restrict hinv hT j).hasSum_trace
    (stdHilbertBasis ℂ (V j))).congr_fun fun i => ?_
  rw [collectedHilbertBasis_apply, ← integrated_restrict_apply π μ f hinv j]
  rfl

variable (π) in

def restrictSetoid : Setoid J where
  r j k := (π.restrict (V j) (hinv j)).IsEquivalent (π.restrict (V k) (hinv k))
  iseqv := ⟨fun _ => IsEquivalent.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

variable (π) in

def multiplicity (c : Quotient (restrictSetoid π hinv)) : ℕ :=
  Nat.card {j : J // (Quotient.mk (restrictSetoid π hinv) j) = c}

include hsum in

theorem hasSum_multiplicity_mul_trace (hT : IsTraceClass (π.integrated μ f))
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite) :
    HasSum (fun c : Quotient (restrictSetoid π hinv) => (multiplicity π hinv c : ℂ) *
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f))
      (trace (π.integrated μ f)) := by
  set S := restrictSetoid π hinv
  have h0 := hasSum_trace_integrated_restrict hinv hsum hT
  let e := Equiv.sigmaFiberEquiv (Quotient.mk S)
  have h1 : HasSum (fun a : Σ c : Quotient S, {j : J // Quotient.mk S j = c} =>
      trace ((π.restrict (V (e a)) (hinv (e a))).integrated μ f)) (trace (π.integrated μ f)) :=
    (e.hasSum_iff).2 h0
  refine h1.sigma fun c => ?_
  have hfc : Set.Finite {j : J | Quotient.mk S j = c} := by
    refine (hfin c.out).subset fun j hj => ?_
    have : Quotient.mk S j = Quotient.mk S c.out := by rw [show Quotient.mk S j = c from hj]; exact c.out_eq.symm
    exact Quotient.exact this
  have : Finite {j : J // Quotient.mk S j = c} := hfc.to_subtype
  have : Fintype {j : J // Quotient.mk S j = c} := Fintype.ofFinite _
  have hconst : ∀ a : {j : J // Quotient.mk S j = c},
      trace ((π.restrict (V (e ⟨c, a⟩)) (hinv (e ⟨c, a⟩))).integrated μ f) =
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f) := by
    intro a
    have hja : Quotient.mk S a.1 = Quotient.mk S c.out := by rw [a.2]; exact c.out_eq.symm
    obtain ⟨eq⟩ := (Quotient.exact hja : S a.1 c.out)
    exact (eq.trace_integrated f (isTraceClass_integrated_restrict hinv hT a.1)).symm
  have h2 := hasSum_fintype (fun a : {j : J // Quotient.mk S j = c} =>
    trace ((π.restrict (V (e ⟨c, a⟩)) (hinv (e ⟨c, a⟩))).integrated μ f))
  convert h2 using 1
  rw [Finset.sum_congr rfl fun a _ => hconst a, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    multiplicity, Nat.card_eq_fintype_card]

end Decomposition

end UnitaryRep

end

end GroundTheory.Automorphic
end

section
open ContinuousLinearMap
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))

theorem orthogonalProjection_mem_intertwiners (j : J) :
    ((V j).orthogonalProjectionOnto : H →L[ℂ] V j) ∈ π.intertwiners (π.restrict (V j) (hinv j)) := by
  rw [mem_intertwiners]
  intro g v
  apply Subtype.ext
  have h := ((isInvariant_iff_commute_starProjection (V j)).1 (hinv j) g).eq
  have h2 : (π g) ((V j).starProjection v) = (V j).starProjection (π g v) :=
    congrArg (fun T : H →L[ℂ] H => T v) h
  rw [coe_restrict_apply, ← Submodule.starProjection_apply, ← Submodule.starProjection_apply]
  exact h2.symm

variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)

include hsum in

theorem orthogonalProjection_coe_eq_zero {i j : J} (hij : i ≠ j) (v : V j) :
    (V i).orthogonalProjectionOnto (v : H) = 0 := by
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  exact hsum.OrthogonalFamily hij ⟨u, hu⟩ v

include hsum in

theorem eq_zero_of_forall_orthogonalProjection {x : H}
    (hx : ∀ j, (V j).orthogonalProjectionOnto x = 0) : x = 0 := by
  have hle : (⨆ j, V j) ≤ (ℂ ∙ x)ᗮ := by
    refine iSup_le fun j u hu => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := (Submodule.orthogonalProjectionOnto_eq_zero_iff).1 (hx j)
    rw [Submodule.mem_orthogonal] at this
    rw [← inner_conj_symm, this u hu, map_zero]
  have hcl : (⨆ j, V j).topologicalClosure ≤ (ℂ ∙ x)ᗮ :=
    Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
  have hmem : x ∈ (ℂ ∙ x)ᗮ := hcl (top_le_topologicalClosure_iSup hsum Submodule.mem_top)
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  exact inner_self_eq_zero.1 hmem

variable (hirr : ∀ j, (π.restrict (V j) (hinv j)).IsIrreducible)

section Class

variable {σ : UnitaryRep G K}

abbrev EquivSummands (σ : UnitaryRep G K) : Type _ :=
  {j : J // (π.restrict (V j) (hinv j)).IsEquivalent σ}

def summandEquivL (w : EquivSummands hinv σ) : K →L[ℂ] V w.1 :=
  ((w.2.some.symm.toLinearIsometryEquiv : K ≃ₗᵢ[ℂ] V w.1) : K →L[ℂ] V w.1)

theorem summandEquivL_mem (w : EquivSummands hinv σ) :
    summandEquivL hinv w ∈ σ.intertwiners (π.restrict (V w.1) (hinv w.1)) :=
  Equiv.mem_intertwiners _

theorem summandEquivL_ne_zero (hσ : σ.IsIrreducible) (w : EquivSummands hinv σ) :
    summandEquivL hinv w ≠ 0 := by
  have := hσ.1
  obtain ⟨k, hk⟩ := exists_ne (0 : K)
  intro h
  have h1 := congrArg (fun T : K →L[ℂ] V w.1 => T k) h
  simp only [zero_apply] at h1
  apply hk
  have h2 : ‖summandEquivL hinv w k‖ = ‖k‖ := LinearIsometryEquiv.norm_map _ k
  rw [h1, norm_zero] at h2
  exact norm_eq_zero.1 h2.symm

def sumEquivL [Fintype (EquivSummands hinv σ)] (c : EquivSummands hinv σ → ℂ) : K →L[ℂ] H :=
  ∑ w, c w • ((V w.1).subtypeL ∘L summandEquivL hinv w)

theorem sumEquivL_mem [Fintype (EquivSummands hinv σ)] (c : EquivSummands hinv σ → ℂ) :
    sumEquivL hinv c ∈ σ.intertwiners π :=
  Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _
    (comp_mem_intertwiners (subtypeL_mem_intertwiners π (V w.1) (hinv w.1))
      (summandEquivL_mem hinv w))

open Classical in
include hsum in
theorem orthogonalProjection_comp_sumEquivL [Fintype (EquivSummands hinv σ)]
    (c : EquivSummands hinv σ → ℂ) (j : J) (k : K) :
    (V j).orthogonalProjectionOnto (sumEquivL hinv c k) =
      if h : (π.restrict (V j) (hinv j)).IsEquivalent σ then
        c ⟨j, h⟩ • summandEquivL hinv ⟨j, h⟩ k else 0 := by
  classical
  simp only [sumEquivL, sum_apply, smul_apply, comp_apply, map_sum, map_smul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp [Submodule.subtypeL_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    · intro w _ hw
      have hwj : j ≠ w.1 := fun e => hw (Subtype.ext e.symm)
      rw [Submodule.subtypeL_apply, orthogonalProjection_coe_eq_zero hsum hwj, smul_zero]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun w _ => ?_
    have hwj : j ≠ w.1 := fun e => h (e ▸ w.2)
    rw [Submodule.subtypeL_apply, orthogonalProjection_coe_eq_zero hsum hwj, smul_zero]

include hsum hirr in

theorem finrank_intertwiners_eq_card (hσ : σ.IsIrreducible)
    (hW : {j | (π.restrict (V j) (hinv j)).IsEquivalent σ}.Finite) :
    FiniteDimensional ℂ (σ.intertwiners π) ∧
      Module.finrank ℂ (σ.intertwiners π) = Nat.card (EquivSummands hinv σ) := by
  classical
  have : Finite (EquivSummands hinv σ) := hW.to_subtype
  let _ : Fintype (EquivSummands hinv σ) := Fintype.ofFinite _
  let Ψ : (EquivSummands hinv σ → ℂ) →ₗ[ℂ] σ.intertwiners π :=
    { toFun := fun c => ⟨sumEquivL hinv c, sumEquivL_mem hinv c⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp [sumEquivL, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a b => by
        apply Subtype.ext
        simp [sumEquivL, smul_smul, Finset.smul_sum] }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext w
    have h1 : ∀ k, (V w.1).orthogonalProjectionOnto (sumEquivL hinv c k) = 0 := by
      intro k
      have := congrArg (fun T : σ.intertwiners π => (T : K →L[ℂ] H) k) hc
      change sumEquivL hinv c k = 0 at this
      rw [this, map_zero]
    have h2 : c w • summandEquivL hinv w = 0 := by
      ext1 k
      have := h1 k
      rw [orthogonalProjection_comp_sumEquivL hinv hsum, dif_pos w.2] at this
      simpa using this
    have := hσ.1
    obtain ⟨k, hk⟩ := exists_ne (0 : K)
    have h3 := congrArg (fun S : K →L[ℂ] V w.1 => S k) h2
    simp only [smul_apply, zero_apply] at h3
    rcases smul_eq_zero.1 h3 with h | h
    · exact h
    · exfalso
      have h4 : ‖summandEquivL hinv w k‖ = ‖k‖ := LinearIsometryEquiv.norm_map _ k
      rw [h, norm_zero] at h4
      exact hk (norm_eq_zero.1 h4.symm)
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨T, hT⟩
    have hPT : ∀ w : EquivSummands hinv σ, ∃ c : ℂ,
        (V w.1).orthogonalProjectionOnto ∘L T = c • summandEquivL hinv w := fun w =>
      hσ.exists_eq_smul_of_mem_intertwiners (hirr w.1) (summandEquivL_mem hinv w)
        (comp_mem_intertwiners (orthogonalProjection_mem_intertwiners hinv w.1) hT)
        (summandEquivL_ne_zero hinv hσ w)
    choose c hc using hPT
    refine ⟨c, Subtype.ext ?_⟩
    change sumEquivL hinv c = T
    ext1 k
    refine (sub_eq_zero.1 (eq_zero_of_forall_orthogonalProjection hsum fun j => ?_)).symm
    rw [map_sub, orthogonalProjection_comp_sumEquivL hinv hsum]
    split_ifs with h
    · have := congrArg (fun S : K →L[ℂ] V j => S k) (hc ⟨j, h⟩)
      simp only [comp_apply, smul_apply] at this
      rw [this, sub_self]
    · have h0 : (V j).orthogonalProjectionOnto ∘L T = 0 :=
        hσ.eq_zero_of_not_isEquivalent (hirr j) (fun e => h e.symm)
          (comp_mem_intertwiners (orthogonalProjection_mem_intertwiners hinv j) hT)
      have := congrArg (fun S : K →L[ℂ] V j => S k) h0
      simp only [comp_apply, zero_apply] at this
      rw [this, sub_zero]
  let e := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.finiteDimensional e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Class

include hsum hirr in

theorem multiplicity_eq_finrank
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite)
    (c : Quotient (restrictSetoid π hinv)) {σ : UnitaryRep G K}
    (hσ : (π.restrict (V c.out) (hinv c.out)).IsEquivalent σ) :
    FiniteDimensional ℂ (σ.intertwiners π) ∧
      multiplicity π hinv c = Module.finrank ℂ (σ.intertwiners π) := by
  have hσirr : σ.IsIrreducible := hσ.isIrreducible_iff.1 (hirr c.out)
  have hiff : ∀ j, (π.restrict (V j) (hinv j)).IsEquivalent σ ↔
      Quotient.mk (restrictSetoid π hinv) j = c := by
    intro j
    rw [← Quotient.out_eq c, Quotient.eq]
    exact ⟨fun h => h.trans hσ.symm, fun h => h.trans hσ⟩
  have hW : {j | (π.restrict (V j) (hinv j)).IsEquivalent σ}.Finite :=
    (hfin c.out).subset fun j hj => hj.trans hσ.symm
  obtain ⟨hfd, hrank⟩ := finrank_intertwiners_eq_card hinv hsum hirr hσirr hW
  refine ⟨hfd, ?_⟩
  rw [hrank, multiplicity]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun j => (hiff j).symm)

end UnitaryRep

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem hasSum_orbitalIntegral_of_rep (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)))
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c) :
    HasSum (fun c : ConjClasses Γ =>
        ∫ x, conjOrbitFun (centralizerIn Γ ((r c : Γ) : G)) (centralizerIn_le_centralizer Γ _) f x
          ∂quotientMeasure (centralizerIn Γ ((r c : Γ) : G)) μ)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) := by
  have h := hasSum_integral_conj Γ μ f hf
  rw [← (Equiv.sigmaFiberEquiv (ConjClasses.mk : Γ → ConjClasses Γ)).hasSum_iff] at h
  refine h.sigma fun c => ?_
  let e : {γ' : Γ // IsConj (r c) γ'} ≃ {γ' : Γ // ConjClasses.mk γ' = c} :=
    Equiv.subtypeEquivRight fun γ' => by
      have hc := hr c
      constructor
      · intro h'
        rw [← hc]
        exact ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_comm.1 h')
      · intro h'
        rw [← hc] at h'
        exact isConj_comm.1 (ConjClasses.mk_eq_mk_iff_isConj.1 h')
  have h2 := hasSum_integral_conj_isConj Γ μ f (r c)
  rw [← e.symm.hasSum_iff] at h2
  convert h2 using 1
  all_goals rfl

omit [μ.IsMulRightInvariant] in

theorem integrable_conjOrbitFun_centralizerIn (f : CompactlySupportedContinuousMap G ℂ) (γ : Γ) :
    Integrable (conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f)
      (quotientMeasure (centralizerIn Γ γ) μ) := by
  classical
  have hδ : ∀ i : {γ' : Γ // IsConj γ γ'}, ∃ d : Γ, d⁻¹ * γ * d = i.1 := fun i => by
    obtain ⟨c, hc⟩ := isConj_iff.1 i.2
    exact ⟨c⁻¹, by rw [inv_inv]; exact hc⟩
  choose δ hδ using hδ
  have hD := (measure_fundamentalDomain_lt_top Γ μ).ne
  have hEμ : ∀ i : {γ' : Γ // IsConj γ γ'},
      μ (((δ i : Γ) : G) • fundamentalDomain Γ) ≠ ∞ := fun i => by
    rw [measure_smul]; exact hD
  have hconj : ∀ (i : {γ' : Γ // IsConj γ γ'}) (x : G),
      ((δ i : G) * x)⁻¹ * γ * ((δ i : G) * x) = x⁻¹ * (i.1 : G) * x := by
    intro i x
    have := congrArg Subtype.val (hδ i)
    push_cast at this
    rw [← this]
    group
  have hnorm : ∀ i : {γ' : Γ // IsConj γ γ'},
      ∫ x in ((δ i : Γ) : G) • fundamentalDomain Γ, ‖f (x⁻¹ * (γ : G) * x)‖ ∂μ =
        ∫ x in fundamentalDomain Γ, ‖f (x⁻¹ * (i.1 : G) * x)‖ ∂μ := by
    intro i
    rw [setIntegral_smul_set μ]
    simp_rw [hconj]
  have hint : IntegrableOn (fun x => f (x⁻¹ * (γ : G) * x))
      (⋃ i, ((δ i : Γ) : G) • fundamentalDomain Γ) μ := by
    refine integrableOn_iUnion_of_summable_integral_norm
      (fun i => integrableOn_conj μ f _ (hEμ i)) ?_
    simp_rw [hnorm]
    exact (summable_integral_norm_conj Γ μ f).comp_injective Subtype.val_injective
  have hmeas : Measurable (conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f) :=
    measurable_from_quotient.2 (f.continuous.comp (by fun_prop)).measurable
  rw [← map_restrict_eq_quotientMeasure μ (isFundamentalDomain_iUnion_smul Γ μ γ hδ),
    integrable_map_measure hmeas.aestronglyMeasurable (measurable_mk _).aemeasurable]
  exact hint

omit [μ.IsMulRightInvariant] in

theorem integrable_conjOrbitFun_of_isWeilMeasure (f : CompactlySupportedContinuousMap G ℂ)
    (γ : Γ) (ν : Measure (Subgroup.centralizer {(γ : G)})) [ν.IsHaarMeasure]
    {ρ : Measure (RightCosetSpace (Subgroup.centralizer {(γ : G)}))}
    (hρ : IsWeilMeasure (Subgroup.centralizer {(γ : G)}) μ ν ρ) :
    Integrable (conjOrbitFun (Subgroup.centralizer {(γ : G)}) le_rfl f) ρ := by
  obtain ⟨h0, htop⟩ := quotientMeasure_centralizerLattice_univ_ne_zero_ne_top Γ γ ν
  have hmeas : Measurable (conjOrbitFun (Subgroup.centralizer {(γ : G)}) le_rfl f) :=
    measurable_from_quotient.2 (f.continuous.comp (by fun_prop)).measurable
  have hcomp : conjOrbitFun (Subgroup.centralizer {(γ : G)}) le_rfl f ∘
      mapOfLe (centralizerIn_le_centralizer Γ γ) =
        conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f := by
    funext y
    obtain ⟨x, rfl⟩ := mk_surjective _ y
    rfl
  have h1 : Integrable (conjOrbitFun (Subgroup.centralizer {(γ : G)}) le_rfl f)
      (quotientMeasure (centralizerLattice Γ (γ : G)) ν univ • ρ) := by
    rw [smul_eq_map_of_isWeilMeasure Γ μ (γ : G) ν hρ,
      integrable_map_measure hmeas.aestronglyMeasurable (measurable_mapOfLe _).aemeasurable, hcomp]
    exact integrable_conjOrbitFun_centralizerIn Γ μ f γ
  have h2 := h1.smul_measure (ENNReal.inv_ne_top.2 h0)
  rwa [smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul] at h2

theorem traceFormula (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)))
    {s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))}
    [∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))]
    (hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V)
    (hsum : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
      fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ)
    (hirr : ∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible)
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c)
    (ν : ∀ c : ConjClasses Γ, Measure (Subgroup.centralizer {((r c : Γ) : G)}))
    (hν : ∀ c, (ν c).IsHaarMeasure)
    (ρ : ∀ c : ConjClasses Γ, Measure (RightCosetSpace (Subgroup.centralizer {((r c : Γ) : G)})))
    (hρ : ∀ c, IsWeilMeasure (Subgroup.centralizer {((r c : Γ) : G)}) μ (ν c) (ρ c)) :
    HasSum (fun π : Quotient (UnitaryRep.restrictSetoid (rightRegularRep Γ μ) hinv) =>
        (UnitaryRep.multiplicity (rightRegularRep Γ μ) hinv π : ℂ) *
          trace (((rightRegularRep Γ μ).restrict π.out (hinv π.out)).integrated μ
            (UnitaryRep.ccToL1 μ f)))
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    HasSum (fun c : ConjClasses Γ =>
        (quotientMeasure (centralizerLattice Γ ((r c : Γ) : G)) (ν c) univ).toReal •
          ∫ y, conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f y ∂ρ c)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    ∀ c, Integrable (conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f) (ρ c) := by
  refine ⟨UnitaryRep.hasSum_multiplicity_mul_trace hinv hsum hf (fun V => UnitaryRep.finite_setOf_isEquivalent (isCompactOperator_integrated Γ μ) hinv
      hsum.OrthogonalFamily (hirr V)), ?_, fun c => ?_⟩
  · convert hasSum_orbitalIntegral_of_rep Γ μ f hf r hr using 1
    funext c
    have := hν c
    exact (integral_conjOrbitFun_eq_smul Γ μ _ (ν c) (hρ c) f).symm
  · have := hν c
    exact integrable_conjOrbitFun_of_isWeilMeasure Γ μ f (r c) (ν c) (hρ c)






end RightCosetSpace

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

theorem ccToL1_add (f g : CompactlySupportedContinuousMap G ℂ) :
    ccToL1 μ (f + g) = ccToL1 μ f + ccToL1 μ g := by
  unfold ccToL1
  rw [← MemLp.toLp_add]
  rfl



end UnitaryRep

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]



end RightCosetSpace

end

end GroundTheory.Automorphic
end
