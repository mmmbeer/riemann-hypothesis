import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.HformSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll

section
noncomputable section

namespace PI.DegenerateSiegelWeil.FibUniq

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib1 fib2 : X → Measure V}

theorem integral_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (φ : V → ℝ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (b : X) :
    ∫ v, φ v ∂(fib1 b) = ∫ v, φ v ∂(fib2 b) := by
  have c1 := (h1.2.2 φ hφc hφs hφU).2
  have c2 := (h2.2.2 φ hφc hφs hφU).2
  have h0 : ∀ S, IsCompact S → S ⊆ univ →
      ∫ b in S, (∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) ∂ν = 0 := by
    intro S hS _
    rw [integral_sub ((c1.mono (subset_univ S)).integrableOn_compact hS)
      ((c2.mono (subset_univ S)).integrableOn_compact hS),
      ← PI.VolStabSW.DensGen.fib_set h1 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S),
      ← PI.VolStabSW.DensGen.fib_set h2 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S), sub_self]
  exact sub_eq_zero.1 (PI.VolStabSW.DensGen.eq_zero_of_setIntegral (ν := ν)
    (fun b => ∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) univ b univ_mem (c1.sub c2) h0)

theorem fin_cpt {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hgK, hgc, hgU, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hi := (h.2.2 g g.continuous hgc hgU).1 b (mem_univ b)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂fib b := (lintegral_indicator_one hKm).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂fib b := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [hv, hgK hv]
        · simp [hv]
    _ < ⊤ := hi.lintegral_lt_top

theorem open_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (O : Set V) (hO : IsOpen O)
    (hOU : O ⊆ U) (b : X) : fib1 b O = fib2 b O := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := PI.VolStabSW.DiscreteGroups.approx O hO
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have key : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib →
      fib b O = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b)) := by
    intro fib hf
    calc fib b O = ∫⁻ v, O.indicator 1 v ∂(fib b) :=
          (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂(fib b) := lintegral_congr fun v => (hlim v).symm
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := lintegral_iSup hmeas hmon
      _ = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b)) := by
          congr 1
          funext k
          exact (ofReal_integral_eq_lintegral_ofReal
            ((hf.2.2 _ (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU)).1 b (mem_univ b))
            (ae_of_all _ fun v => (h01 k v).1)).symm
  rw [key fib1 h1, key fib2 h2]
  congr 1
  funext k
  rw [integral_eq h1 h2 hf' hff' hι (φ k) (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU) b]

theorem fib_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hU : IsOpen U) : fib1 = fib2 := by
  funext b
  obtain ⟨W, hW, hWU⟩ := PI.VolStabSW.DiscreteGroups.cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hnull : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → fib b Uᶜ = 0 :=
    fun fib hf => measure_mono_null (compl_subset_compl.2 inter_subset_right) (hf.1 b)
  have hfin : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → ∀ n, fib b (W n) ≠ ⊤ :=
    fun fib hf n => (lt_of_le_of_lt (measure_mono subset_closure)
      (fin_cpt hf hU b _ (hW n).2.1 (hW n).2.2)).ne
  let s : Option ℕ → Set V := fun o => o.elim Uᶜ W
  have hs : ⋃ o, s o = univ := by
    rw [iUnion_option]
    simp only [s, Option.elim_none, Option.elim_some]
    rw [hWU, compl_union_self]
  refine (Measure.ext_iff_of_iUnion_eq_univ hs).2 fun o => ?_
  cases o with
  | none =>
    simp only [s, Option.elim_none]
    rw [Measure.restrict_eq_zero.2 (hnull fib1 h1), Measure.restrict_eq_zero.2 (hnull fib2 h2)]
  | some n =>
    simp only [s, Option.elim_some]
    have : IsFiniteMeasure ((fib1 b).restrict (W n)) :=
      isFiniteMeasure_restrict.2 (hfin fib1 h1 n)
    refine ext_of_generate_finite {t : Set V | IsOpen t} (BorelSpace.measurable_eq.trans rfl)
      isPiSystem_isOpen (fun t ht => ?_) ?_
    · rw [Measure.restrict_apply ht.measurableSet, Measure.restrict_apply ht.measurableSet]
      exact open_eq h1 h2 hf' hff' hι _ (ht.inter (hW n).1) (inter_subset_right.trans (hWsub n)) b
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact open_eq h1 h2 hf' hff' hι _ (hW n).1 (hWsub n) b

end Gen

section Tens

open scoped TensorProduct
open PI.VolStabSW PI.VolStabSW.TensAllW

end Tens

end PI.DegenerateSiegelWeil.FibUniq

namespace PI.DegenerateSiegelWeil

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.TensAllW

end PI.DegenerateSiegelWeil
end
end

section
noncomputable section

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal NNReal

section Reindex

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem isFibreFamily_reindex (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞}
    (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) :
    IsFibreFamily ((cμ * cν) • μ) f ι U ν univ
      (fun b => (fib (h.symm b)).map e.toMeasurableEquiv) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  have hme : ⇑e.toMeasurableEquiv = ⇑e := rfl
  have hμ' : μ.map e.toMeasurableEquiv = cμ • μ := hμ
  have hν' : ν.map h.symm.toMeasurableEquiv = cν • ν := hν
  have hpre : ∀ b, e ⁻¹' (f ⁻¹' {ι b} ∩ U) = f ⁻¹' {ι (h.symm b)} ∩ U := by
    intro b
    ext v
    have hUv : e v ∈ U ↔ v ∈ U := by
      conv_rhs => rw [← hU]
      exact Iff.rfl
    simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, hff', heh, hι.eq_iff, hUv]
    rw [h.eq_symm_apply]
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · rw [MeasurableEquiv.map_apply, preimage_compl, hme, hpre]
    exact h1 (h.symm b)
  · rw [Measure.restrict_smul, lintegral_smul_measure]
    have hφe : Measurable (φ ∘ e) := hφ.comp e.continuous.measurable
    have key1 : ∫⁻ v in U, (φ ∘ e) v ∂μ = cμ * ∫⁻ v in U, φ v ∂μ := by
      have h0 : ∫⁻ v in U, φ v ∂(μ.map e.toMeasurableEquiv) = ∫⁻ v in U, (φ ∘ e) v ∂μ := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hme, hU]
        rfl
      rw [← h0, hμ', Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    have key2 : ∫⁻ b, ∫⁻ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv ∂ν =
        cν * ∫⁻ b, ∫⁻ v, (φ ∘ e) v ∂fib b ∂ν := by
      simp only [lintegral_map_equiv]
      rw [← smul_eq_mul, ← lintegral_smul_measure, ← hν', lintegral_map_equiv]
      rfl
    rw [key2, ← h2 _ hφe, key1, smul_eq_mul]
    ring
  · have hφe_c : Continuous (φ ∘ e) := hφc.comp e.continuous
    have hφe_s : HasCompactSupport (φ ∘ e) := hφs.comp_homeomorph e
    have hsub : tsupport (φ ∘ e) ⊆ e ⁻¹' tsupport φ :=
      closure_minimal (fun v hv => subset_tsupport φ hv) ((isClosed_tsupport φ).preimage e.continuous)
    have hφe_U : tsupport (φ ∘ e) ⊆ U := by
      intro v hv
      rw [← hU]
      exact hφU (hsub hv)
    obtain ⟨hi, hcont⟩ := h3 _ hφe_c hφe_s hφe_U
    refine ⟨fun b _ => ?_, ?_⟩
    · rw [integrable_map_equiv]
      exact hi _ (mem_univ _)
    · have hfun : (fun b => ∫ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv) =
          (fun b' => ∫ v, (φ ∘ e) v ∂fib b') ∘ h.symm := by
        funext b
        simp only [Function.comp_apply, integral_map_equiv]
        rfl
      rw [hfun]
      exact ((continuousOn_univ.1 hcont).comp h.symm.continuous).continuousOn

theorem isFibreFamily_smul {B : Set X} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hfib : IsFibreFamily μ f ι U ν B fib) :
    IsFibreFamily (c • μ) f ι U ν B (fun b => c • fib b) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · simp [h1 b]
  · rw [Measure.restrict_smul, lintegral_smul_measure, h2 φ hφ, smul_eq_mul, ← lintegral_const_mul' _ _ hc]
    simp only [lintegral_smul_measure, smul_eq_mul]
  · obtain ⟨hi, hcont⟩ := h3 φ hφc hφs hφU
    refine ⟨fun b hb => (hi b hb).smul_measure hc, ?_⟩
    simp only [integral_smul_measure, smul_eq_mul]
    exact continuousOn_const.mul hcont

end Reindex

section Uniq

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem fib_reindex_eq (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) :
    (fib (h.symm b)).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hc : cμ * cν ≠ ⊤ := ENNReal.mul_ne_top hcμ hcν
  haveI : IsFiniteMeasureOnCompacts ((cμ * cν) • μ) := IsFiniteMeasureOnCompacts.smul μ hc
  have := PI.DegenerateSiegelWeil.FibUniq.fib_eq (isFibreFamily_reindex e h hff' hι heh hU hμ hν hfib)
    (isFibreFamily_smul hc hfib) hf' hff' hι hUo
  exact congrFun this b

theorem fib_map_fixed (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) (hb : h b = b) :
    (fib b).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hb' : h.symm b = b := h.symm_apply_eq.2 hb.symm
  have := fib_reindex_eq e h hf' hff' hι hUo heh hU hcμ hcν hμ hν hfib b
  rwa [hb'] at this

end Uniq

end PI.DegenerateSiegelWeil.Scale
end
end

section
noncomputable section

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW
open scoped ENNReal NNReal TensorProduct Matrix

section Alg

variable {K : Type} [CommRing K] {n M : ℕ}

def mulTup (D : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) : Fin n → Fin M → K :=
  fun j i => ∑ k, D k j * X k i

theorem mulTup_mul (D₁ D₂ : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) :
    mulTup D₁ (mulTup D₂ X) = mulTup (D₂ * D₁) X := by
  funext j i
  simp only [mulTup, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mulTup_one (X : Fin n → Fin M → K) : mulTup (1 : Matrix (Fin n) (Fin n) K) X = X := by
  funext j i
  simp [mulTup, Matrix.one_apply]

theorem mulTup_add (D : Matrix (Fin n) (Fin n) K) (X Y : Fin n → Fin M → K) :
    mulTup D (X + Y) = mulTup D X + mulTup D Y := by
  funext j i
  simp [mulTup, mul_add, Finset.sum_add_distrib]

theorem mulTup_apply_eq_sum (D : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) (j : Fin n) :
    mulTup D X j = ∑ k, D k j • X k := by
  funext i
  simp [mulTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem linIndep_mulTup (D : (Matrix (Fin n) (Fin n) K)ˣ) {X : Fin n → Fin M → K}
    (hX : LinearIndependent K X) : LinearIndependent K (mulTup (D : Matrix (Fin n) (Fin n) K) X) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro c hc
  have key : ∑ j, c j • mulTup (D : Matrix (Fin n) (Fin n) K) X j =
      ∑ k, Matrix.mulVec (D : Matrix (Fin n) (Fin n) K) c k • X k := by
    simp only [mulTup_apply_eq_sum, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have h0 : Matrix.mulVec (D : Matrix (Fin n) (Fin n) K) c = 0 := funext (hX _ (key ▸ hc))
  have hc0 : c = 0 := by
    have h1 := congrArg (Matrix.mulVec ((D⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)) h0
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  intro j
  rw [hc0]
  rfl

theorem preimage_linIndep (D : (Matrix (Fin n) (Fin n) K)ˣ) :
    mulTup (M := M) (D : Matrix (Fin n) (Fin n) K) ⁻¹' {X | LinearIndependent K X} =
      {X | LinearIndependent K X} := by
  ext X
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro h
    have h1 := linIndep_mulTup D⁻¹ h
    rwa [mulTup_mul, Units.mul_inv, mulTup_one] at h1
  · exact linIndep_mulTup D

end Alg

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n M : ℕ}

def conjT (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (D.map (sigR R σ))ᵀ

theorem conjT_mul (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    conjT R σ (A * B) = conjT R σ B * conjT R σ A := by
  unfold conjT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_one : conjT R σ (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
  simp [conjT]

theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem conjT_conjT (hσ : ∀ x, σ (σ x) = x) (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    conjT R σ (conjT R σ A) = A := by
  ext i j
  simp [conjT, sigR_sigR R σ hσ]

theorem mem_herm_iff (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    S ∈ HermR R σ n ↔ conjT R σ S = S := by
  constructor
  · intro h
    have h' : ∀ a b, sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = S a b := h
    ext a b
    exact h' a b
  · intro h
    have h' : ∀ a b, sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = S a b := by
      intro a b
      have := congrFun (congrFun h a) b
      simpa [conjT] using this
    exact h'

def hermMap (hσ : ∀ x, σ (σ x) = x) (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (S : HermR R σ n) :
    HermR R σ n :=
  ⟨conjT R σ D * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * D, by
    rw [mem_herm_iff, conjT_mul, conjT_mul, conjT_conjT R σ hσ, (mem_herm_iff R σ _).1 S.2,
      Matrix.mul_assoc]⟩

theorem hermMap_coe (hσ : ∀ x, σ (σ x) = x) (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (S : HermR R σ n) :
    (hermMap R σ hσ D S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = conjT R σ D * S * D := rfl

theorem hermMap_mul (hσ : ∀ x, σ (σ x) = x) (D₁ D₂ : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (S : HermR R σ n) : hermMap R σ hσ D₁ (hermMap R σ hσ D₂ S) = hermMap R σ hσ (D₂ * D₁) S := by
  apply Subtype.ext
  simp only [hermMap_coe, conjT_mul, Matrix.mul_assoc]

theorem hermMap_one (hσ : ∀ x, σ (σ x) = x) (S : HermR R σ n) : hermMap R σ hσ 1 S = S := by
  apply Subtype.ext
  simp [hermMap_coe, conjT_one]

def tupS (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin M) (R ⊗[F] E) :=
  Matrix.of fun a i => sigR R σ (X a i)

end Herm

def GramMulTup : Prop := ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
  [Algebra F R] (σ : E →ₐ[F] E) (n M : ℕ) (J : Matrix (Fin M) (Fin M) E)
  (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E),
  gramR R σ J (mulTup D X) = conjT R σ D * gramR R σ J X * D

theorem gramH_mulTup_of (hG : GramMulTup) {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    PI.VolStabSW.gramH R σ hσ J hJ (mulTup D X) =
      hermMap R σ hσ D (PI.VolStabSW.gramH R σ hσ J hJ X) := by
  apply Subtype.ext
  rw [hermMap_coe]
  exact hG F E R σ n M J D X

end PI.DegenerateSiegelWeil.Scale
end
end

section
noncomputable section

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW PI.VolStabSW.TensAllW
open scoped ENNReal NNReal TensorProduct Matrix

section Equiv

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n M : ℕ}

theorem continuous_mulTup (D : Matrix (Fin n) (Fin n) K) : Continuous (mulTup (M := M) D) := by
  first
  | (unfold mulTup; fun_prop)
  | (simp only [mulTup]; fun_prop)
  | (unfold mulTup; continuity)
  | fun_prop

def tupEquiv (D : (Matrix (Fin n) (Fin n) K)ˣ) :
    (Fin n → Fin M → K) ≃ₜ+ (Fin n → Fin M → K) where
  toFun := mulTup (D : Matrix (Fin n) (Fin n) K)
  invFun := mulTup (↑D⁻¹ : Matrix (Fin n) (Fin n) K)
  left_inv X := by rw [mulTup_mul, D.mul_inv, mulTup_one]
  right_inv X := by rw [mulTup_mul, D.inv_mul, mulTup_one]
  map_add' := mulTup_add _
  continuous_toFun := continuous_mulTup _
  continuous_invFun := continuous_mulTup _

end Equiv

section HermEquiv

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}

theorem continuous_hermMap [IsTopologicalRing (R ⊗[F] E)] (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous (hermMap R σ hσ D) := by
  first
  | (unfold hermMap; fun_prop)
  | (simp only [hermMap]; fun_prop)
  | (unfold hermMap; exact Continuous.subtype_mk (by fun_prop) _)
  | (unfold hermMap; continuity)

def hermEquiv [IsTopologicalRing (R ⊗[F] E)] (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) :
    HermR R σ n ≃ₜ+ HermR R σ n where
  toFun := hermMap R σ hσ D
  invFun := hermMap R σ hσ ↑D⁻¹
  left_inv S := by rw [hermMap_mul, D.mul_inv, hermMap_one]
  right_inv S := by rw [hermMap_mul, D.inv_mul, hermMap_one]
  map_add' S T := Subtype.ext (by simp [hermMap_coe, Matrix.mul_add, Matrix.add_mul])
  continuous_toFun := continuous_hermMap R σ hσ _
  continuous_invFun := continuous_hermMap R σ hσ _

end HermEquiv

section Haar

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

theorem map_eq_smul (μ : Measure G) [μ.IsAddHaarMeasure] (e : G ≃ₜ+ G) :
    μ.map e = (((addEquivAddHaarChar e)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := by
  have h := MeasureTheory.addEquivAddHaarChar_smul_map μ e
  have hc : (addEquivAddHaarChar e : ℝ≥0) ≠ 0 := (MeasureTheory.addEquivAddHaarChar_pos e).ne'
  conv_rhs => rw [← h]
  rw [ENNReal.smul_def (addEquivAddHaarChar e), smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ hc,
    ENNReal.coe_one, one_smul]

end Haar

section Cov

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (hJ : ∀ i j, σ (J j i) = J i j) {n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R] [SecondCountableTopology (HermR R σ n)]

def cTup (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) : ℝ≥0 :=
  (addEquivAddHaarChar (tupEquiv (M := M) D))⁻¹

def cHerm (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) : ℝ≥0 :=
  addEquivAddHaarChar (hermEquiv R σ hσ (n := n) D)

include hJ in

theorem fib_map_mulTup (hG : GramMulTup) (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) (S₀ : HermR R σ n)
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀) :
    (fib S₀).map (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ((cTup (M := M) R D : ℝ≥0∞) *
        (cHerm σ hσ R D : ℝ≥0∞)) • fib S₀ := by
  let e := tupEquiv (M := M) D
  let h := hermEquiv R σ hσ D
  have hμ : μ.map e.toHomeomorph = (cTup (M := M) R D : ℝ≥0∞) • μ :=
    map_eq_smul μ e
  have hν : ν.map h.toHomeomorph.symm = (cHerm σ hσ R D : ℝ≥0∞) • ν := by
    have := map_eq_smul ν h.symm
    rw [addEquivAddHaarChar_symm, inv_inv] at this
    exact this
  have := fib_map_fixed e.toHomeomorph h.toHomeomorph (f' := gramH R σ hσ J hJ)
    (continuous_gramH R σ hσ J hJ) (fun _ => rfl) Subtype.val_injective
    (isOpen_linIndep (Module.finBasis F E) R hU hL)
    (fun X => gramH_mulTup_of hG R σ hσ J hJ _ X) (preimage_linIndep D) ENNReal.coe_ne_top
    ENNReal.coe_ne_top hμ hν hfib S₀ hS₀
  exact this

include hJ in

theorem fib_image_mulTup (hG : GramMulTup) (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) (S₀ : HermR R σ n)
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀)
    (A : Set (Fin n → Fin M → R ⊗[F] E)) :
    ((cTup (M := M) R D : ℝ≥0∞) * (cHerm σ hσ R D : ℝ≥0∞)) *
      fib S₀ (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) '' A) = fib S₀ A := by
  have hmap := fib_map_mulTup (hJ := hJ) (hG := hG) (hU := hU) (hL := hL) (hfib := hfib) (hS₀ := hS₀)
  have inj : Function.Injective (tupEquiv (M := M) D) := (tupEquiv (M := M) D).injective
  have e1 := MeasurableEquiv.map_apply (μ := fib S₀)
    ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv) ((tupEquiv (M := M) D) '' A)
  have e2 : ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv : _ → _) ⁻¹'
      ((tupEquiv (M := M) D) '' A) = A := Set.preimage_image_eq A inj
  rw [e2] at e1
  have e3 : ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv : _ → _) =
      mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl
  have e4 : ((tupEquiv (M := M) D) : _ → _) = mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl
  rw [e3, e4, hmap, Measure.smul_apply, smul_eq_mul] at e1
  exact e1

end Cov

end PI.DegenerateSiegelWeil.Scale
end
end
