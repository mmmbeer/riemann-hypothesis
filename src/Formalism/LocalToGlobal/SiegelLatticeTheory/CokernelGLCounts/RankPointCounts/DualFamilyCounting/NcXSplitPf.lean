import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXFinVolSk
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProdG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.AdmCpt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmDecomp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXLocSB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXSplS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.HformSmulLeft

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.BoxVolSk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def GramMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
    MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | gramR (Af F) σ J x ≠ T.map (inclR (Af F))} ∧
    (∀ y : Fin a → Fin n → AF F ⊗[F] E, gramR (AF F) σ J y = T.map (inclR (AF F)) →
      gramR (Af F) σ J (projFin y) = T.map (inclR (Af F))) ∧
    (∀ x : Fin a → Fin n → Af F ⊗[F] E, gramR (Af F) σ J x = T.map (inclR (Af F)) →
      ∀ v, gramR (Fv F v) σ J (projV v x) = T.map (inclR (Fv F v)))

def PosTest : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ)
    (μ : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
    (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (t : HermR (Ainf F) σ a),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    fib t ≠ 0 →
    ∃ Φ : (Fin a → Fin n → Ainf F ⊗[F] E) → ℝ, Continuous Φ ∧ HasCompactSupport Φ ∧ (∀ x, 0 ≤ Φ x) ∧
      Integrable Φ (fib t) ∧ 0 < ∫ x, Φ x ∂(fib t)

def BoxMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n a : ℕ) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)),
    (∀ v, MeasurableSet (C v)) → MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}

theorem BoxVolSk_tprod_ofReal {ι : Type} (r : ι → ℝ) (hm : Multipliable (fun i => (r i : ℂ))) :
    ∏' i, (r i : ℂ) = ((∏' i, r i : ℝ) : ℂ) := by
  obtain ⟨L, hL⟩ := hm
  have hclosed : IsClosed (Set.range ((↑) : ℝ → ℂ)) := Complex.isometry_ofReal.isClosedEmbedding.isClosed_range
  have hmem : L ∈ Set.range ((↑) : ℝ → ℂ) :=
    hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall fun s => ⟨∏ i ∈ s, r i, by rw [Complex.ofReal_prod]⟩)
  obtain ⟨l, rfl⟩ := hmem
  have hr : HasProd r l :=
    (Complex.isometry_ofReal.isEmbedding.isInducing.hasProd_iff (g := Complex.ofRealHom) (f := r) (a := l)).mp hL
  rw [hL.tprod_eq, hr.tprod_eq]

end Formalism.L2.SG.Pf.NcX.BoxVolSk
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.BoxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open Formalism.L2.SG.Pf.NcX.BoxVolSk
open scoped TensorProduct

theorem box_measurable_holds : BoxMeas := by
  intro F E _ _ _ _ _ n a C hC
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  have e : {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} = ⋂ v, projV v ⁻¹' C v := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter fun v =>
    (PI.VolStabW.TopoMeas.continuous_projV b v).measurable (hC v)

theorem gram_measurable_holds : GramMeas := by
  intro F E _ _ _ _ _ σ n J a T
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨?_, fun y hy => ?_, fun x hx v => ?_⟩
  · have : T2Space (Af F ⊗[F] E) := PI.VolStabW.RestrProdG.t2_tensor_product (Af F)
    have : T2Space (Matrix (Fin a) (Fin a) (Af F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Af F ⊗[F] E))
    exact (isClosed_singleton.preimage
      (PI.VolStabW.continuous_gramR (Af F) σ J)).isOpen_compl.measurableSet
  · funext i j
    have h := congrArg (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
      (congrFun (congrFun hy i) j)
    rw [PI.VolStabW.RestrProdG.map_gramR, Matrix.map_apply,
      PI.VolStabW.RestrProdG.map_inclR] at h
    rw [Matrix.map_apply]
    exact h
  · funext i j
    have h := congrArg (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))
      (congrFun (congrFun hx i) j)
    rw [PI.VolStabW.RestrProdG.map_gramR, Matrix.map_apply,
      PI.VolStabW.RestrProdG.map_inclR] at h
    rw [Matrix.map_apply]
    exact h

theorem positivity_test_holds : PosTest := by
  intro F E _ _ _ _ _ σ n J a μ ν fib t hfib hne
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  set V := Fin a → Fin n → Ainf F ⊗[F] E
  set U : Set V := {X | LinearIndependent (Ainf F ⊗[F] E) X} with hUdef
  have hUo : IsOpen U := PI.VolStabW.TensAllW.isOpen_linIndep b (Ainf F)
    (PI.VolStabW.isOpen_units_Ainf F) (PI.VolStabW.lip_ainf F)
  have : LocallyCompactSpace (Ainf F ⊗[F] E) := PI.AdicCompletionValuation.locallyCompactSpace_tens (Ainf F)
  have : T2Space (Ainf F ⊗[F] E) := PI.VolStabW.RestrProdG.t2_tensor_product (Ainf F)
  have : SecondCountableTopology (Ainf F ⊗[F] E) := PI.VolStabW.secondCountable_tens (Ainf F)

  have hcU : fib t Uᶜ = 0 := measure_mono_null
    (Set.compl_subset_compl.2 Set.inter_subset_right) (hfib.1 t)
  have hUpos : 0 < fib t U := by
    rcases eq_or_ne (fib t U) 0 with h | h
    · exfalso; apply hne
      rw [← Measure.measure_univ_eq_zero]
      have := measure_union_null h hcU
      rwa [Set.union_compl_self] at this
    · exact pos_iff_ne_zero.2 h

  have : LocallyCompactSpace U := hUo.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hUeq : U = ⋃ m, Subtype.val '' compactCovering U m := by
    ext x; constructor
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ((iUnion_compactCovering U).symm ▸ Set.mem_univ (⟨x, hx⟩ : U))
      exact Set.mem_iUnion.2 ⟨m, ⟨⟨x, hx⟩, hm, rfl⟩⟩
    · intro hx
      obtain ⟨m, y, _, rfl⟩ := Set.mem_iUnion.1 hx
      exact y.2
  obtain ⟨m, hm⟩ : ∃ m, 0 < fib t (Subtype.val '' compactCovering U m) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have : fib t U = 0 := by
      rw [hUeq]
      exact measure_iUnion_null fun m => nonpos_iff_eq_zero.1 (hcon m)
    exact hUpos.ne' this
  set K : Set V := Subtype.val '' compactCovering U m
  have hK : IsCompact K := (isCompact_compactCovering U m).image continuous_subtype_val
  have hKU : K ⊆ U := by rintro _ ⟨y, _, rfl⟩; exact y.2
  obtain ⟨f, hf1, hfc, hfU, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hUo hKU
  have hint : Integrable f (fib t) :=
    ((hfib.2.2 f f.continuous hfc hfU).1 t (Set.mem_univ _))
  refine ⟨f, f.continuous, hfc, fun x => (hf01 x).1, hint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun x => (hf01 x).1) hint]
  refine lt_of_lt_of_le hm (measure_mono fun x hx => ?_)
  rw [Function.mem_support, hf1 hx]
  exact one_ne_zero

end Formalism.L2.SG.Pf.NcX.BoxSteps
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.BoxVolPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open Formalism.L2.SG.Pf.NcX.BoxVolSk Formalism.L2.SG.Pf.NcX.BoxSteps Formalism.L2.SG.Pf.NcX.FinVolSk
open scoped TensorProduct

theorem finprod_box {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n a d : ℕ} (b : Module.Basis (Fin d) F E)
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E))
    (hCa : ∀ᶠ v in Filter.cofinite, C v = latV b v) (x : Fin a → Fin n → Af F ⊗[F] E) :
    (∏ᶠ v, (C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v x)) =
      ({x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}.indicator 1 x : ℂ) := by
  classical
  by_cases hx : ∀ v, projV v x ∈ C v
  · have hr : ({x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}.indicator 1 x : ℂ) = 1 := by
      simp [Set.indicator_apply, hx]
    rw [hr]
    exact finprod_eq_one_of_forall_eq_one fun v => by simp [Set.indicator_apply, hx v]
  · have hr : ({x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}.indicator 1 x : ℂ) = 0 := by
      simp only [Set.indicator_apply, Set.mem_setOf_eq, if_neg hx]
    rw [hr]
    push_neg at hx
    obtain ⟨v0, hv0⟩ := hx
    refine finprod_eq_zero _ v0 (by simp [Set.indicator_apply, hv0]) ?_
    have hev : ∀ᶠ v in Filter.cofinite, projV v x ∈ C v := by
      filter_upwards [hCa, PI.VolStabW.AdmissibleCompactSupport.eventually_mem_latV b x] with v h1 h2
      rw [h1]
      exact h2
    refine (Filter.eventually_cofinite.mp hev).subset ?_
    intro v hv hc
    apply hv
    simp [Set.indicator_apply, hc]

theorem box_volume_holds : BoxVol := by
  intro F E _ _ _ _ _ σ n J ψ a X0 hT νX hStd hdet ha hn hSWa hSWc hOm μinf νinf fibInf hμ hν hfib hne
    ωf hdec
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set TI := hermOf (Ainf F) σ (gramE σ J X0) hT with hTI
  obtain ⟨Φi, hΦc, hΦs, hΦ0, hΦint, hΦpos⟩ := positivity_test_holds F E σ n J a μinf νinf fibInf TI hfib hne
  set c : ENNReal := ∫⁻ z, ENNReal.ofReal (Φi z) ∂(fibInf TI) with hcdef
  have hc : c = ENNReal.ofReal (∫ z, Φi z ∂(fibInf TI)) :=
    (ofReal_integral_eq_lintegral_ofReal hΦint (Filter.Eventually.of_forall hΦ0)).symm
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 hΦpos).ne'
  have hcT : c ≠ ⊤ := by rw [hc]; exact ENNReal.ofReal_ne_top
  obtain ⟨hGm, hGf, hGv⟩ := gram_measurable_holds F E σ n J a (gramE σ J X0)
  have hae : ∀ᵐ y ∂νX, gramR (AF F) σ J y = (gramE σ J X0).map (inclR (AF F)) := by
    rw [Filter.Eventually, mem_ae_iff]
    simpa [Set.compl_ofPred] using hOm.1
  refine ⟨?_, ?_⟩
  · set S := {x : Fin a → Fin n → Af F ⊗[F] E | gramR (Af F) σ J x ≠ (gramE σ J X0).map (inclR (Af F))}
      with hSdef
    have h1 := hdec (fun z => ENNReal.ofReal (Φi z)) S hGm
    have hL : ∫⁻ y, ENNReal.ofReal (Φi (projInf y)) * S.indicator 1 (projFin y) ∂νX = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
      filter_upwards [hae] with y hy
      have : projFin y ∉ S := fun h => h (hGf y hy)
      simp [Set.indicator_of_notMem this]
    rw [hL] at h1
    have hS0 : ωf S = 0 := by
      rcases (mul_eq_zero.1 h1.symm) with h | h
      · exact h
      · exact absurd h hc0
    refine measure_mono_null (fun x hx => ?_) hS0
    intro hxT
    exact hx (hGv x hxT)
  · intro d b C hSB hCm hCa
    set B := {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} with hBdef
    have hBm : MeasurableSet B := box_measurable_holds F E n a C hCm
    have h2 := hdec (fun z => ENNReal.ofReal (Φi z)) B hBm

    have hA1 := hOm.2.2 μinf hμ
    have hA2 := hA1.2 νinf hν
    have hdX : ∀ v, SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
      intro v
      obtain ⟨μv, hμv⟩ := hA2.1
      have hex : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ := ⟨μv v, hμv v⟩
      simp only [dX, dif_pos hex]
      exact hex.choose_spec
    have hA3 := hA2.2 (fun v => dX σ J ψ v a) hdX
    have hdT : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
      intro v
      obtain ⟨νv, hνv⟩ := hA3.1
      have hex : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν := ⟨νv v, hνv v⟩
      simp only [dT, dif_pos hex]
      exact hex.choose_spec
    have hA4 := hA3.2 (fun v => dT σ ψ v a) hdT
    have hA5 := hA4.2 fibInf hfib
    have hOmF : ∀ v, IsOm σ J ψ v a (omFam σ J ψ v a) := by
      intro v
      obtain ⟨fibV, hfibV⟩ := hA5.1
      have hex : ∃ fib, IsOm σ J ψ v a fib := ⟨fibV v, hfibV v⟩
      simp only [omFam, dif_pos hex]
      exact hex.choose_spec
    have hQ := hA5.2 (fun v => omFam σ J ψ v a) hOmF

    let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ :=
      fun v => (C v).indicator 1
    let Φf : (Fin a → Fin n → Af F ⊗[F] E) → ℂ := fun x => ∏ᶠ v, Φv v (projV v x)
    let Φinf : (Fin a → Fin n → Ainf F ⊗[F] E) → ℂ := fun z => (Φi z : ℂ)
    let Φ : (Fin a → Fin n → AF F ⊗[F] E) → ℂ := fun y => Φinf (projInf y) * Φf (projFin y)
    have hpure : IsPureFin b Φf Φv :=
      ⟨hSB, hCa.mono fun v h => by simp only [Φv, h], fun X => rfl⟩
    obtain ⟨hInt, hMult, hEq⟩ := hQ d b Φ Φinf Φf Φv (Complex.continuous_ofReal.comp hΦc)
      (hΦs.comp_left Complex.ofReal_zero) hpure (fun X => rfl)

    let g : (Fin a → Fin n → AF F ⊗[F] E) → ℝ := fun y => Φi (projInf y) * B.indicator 1 (projFin y)
    have hΦg : ∀ y, Φ y = (g y : ℂ) := by
      intro y
      simp only [Φ, Φinf, Φf, Φv, g]
      rw [finprod_box b C hCa (projFin y), ← hBdef]
      by_cases hy : projFin y ∈ B
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    have hg0 : ∀ y, 0 ≤ g y := fun y => mul_nonneg (hΦ0 _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hgInt : Integrable g νX := by
      have : Integrable (fun y => (g y : ℂ)) νX := hInt.congr (Filter.Eventually.of_forall hΦg)
      exact this.re
    have hlin : ∫⁻ y, ENNReal.ofReal (g y) ∂νX =
        ∫⁻ y, ENNReal.ofReal (Φi (projInf y)) * B.indicator 1 (projFin y) ∂νX := by
      refine lintegral_congr fun y => ?_
      by_cases hy : projFin y ∈ B
      · simp [g, Set.indicator_of_mem hy]
      · simp [g, Set.indicator_of_notMem hy]
    have hLHS : ∫ y, Φ y ∂νX = ((ωf B * c).toReal : ℂ) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hΦg), integral_complex_ofReal,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgInt.aestronglyMeasurable,
        hlin, h2]
    have hfinB : ωf B * c ≠ ⊤ := by
      rw [← h2, ← hlin]; exact (hgInt.lintegral_lt_top).ne
    have hωT : ωf B ≠ ⊤ := by
      intro h; apply hfinB; rw [h]; exact ENNReal.top_mul hc0

    have hloc : ∀ v, (∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
        (((omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))))
          (C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))})).toReal : ℂ) := by
      intro v
      have hom : omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))) =
          omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT) := by
        simp only [omAt, dif_pos (map_mem_HermR (Fv F v) σ (gramE σ J X0) hT)]
        rfl
      have hnull : omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT)
          {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hOmF v).1 _)
      rw [hom, measure_inter_conull hnull]
      have e : Φv v = fun X => (((C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℝ) X : ℝ) : ℂ) := by
        funext X
        by_cases hX : X ∈ C v
        · simp [Φv, Set.indicator_of_mem hX]
        · simp [Φv, Set.indicator_of_notMem hX]
      rw [e, integral_complex_ofReal, integral_indicator_one (hCm v), Measure.real]
    let r : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
      ((omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))))
        (C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))})).toReal
    have hMult' : Multipliable (fun v => (r v : ℂ)) := by
      have : (fun v => ∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
        fun v => (r v : ℂ) := funext hloc
      rw [← this]; exact hMult
    have hRHS : (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) *
        ∏' v, ∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
        (((∫ z, Φi z ∂(fibInf TI)) * ∏' v, r v : ℝ) : ℂ) := by
      rw [tprod_congr hloc, BoxVolSk_tprod_ofReal r hMult']
      simp only [Φinf]
      rw [integral_complex_ofReal, Complex.ofReal_mul]
    rw [hLHS, hRHS, Complex.ofReal_inj, ENNReal.toReal_mul] at hEq
    have hcR : c.toReal = ∫ z, Φi z ∂(fibInf TI) := by
      rw [hc, ENNReal.toReal_ofReal (integral_nonneg hΦ0)]
    rw [hcR, mul_comm] at hEq
    have hB : (ωf B).toReal = ∏' v, r v := mul_left_cancel₀ hΦpos.ne' hEq
    rw [← hB, ENNReal.ofReal_toReal hωT]

end Formalism.L2.SG.Pf.NcX.BoxVolPf
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.LT.GLP

variable {K : Type*} [Field K]

theorem surj_equiv {C W : Type*} [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup W] [Module K W] (L1 L2 : C →ₗ[K] W) (h1 : Function.Surjective L1)
    (h2 : Function.Surjective L2) : ∃ δ : C ≃ₗ[K] C, ∀ c, L1 (δ c) = L2 c := by
  obtain ⟨D1, hD1⟩ := Submodule.exists_isCompl (LinearMap.ker L1)
  obtain ⟨D2, hD2⟩ := Submodule.exists_isCompl (LinearMap.ker L2)
  let e1 : D1 ≃ₗ[K] W := (Submodule.quotientEquivOfIsCompl _ _ hD1).symm.trans (L1.quotKerEquivOfSurjective h1)
  let e2 : D2 ≃ₗ[K] W := (Submodule.quotientEquivOfIsCompl _ _ hD2).symm.trans (L2.quotKerEquivOfSurjective h2)
  have he1 : ∀ d : D1, e1 d = L1 d := fun d => by
    simp [e1, Submodule.quotientEquivOfIsCompl_symm_apply]
  have he2 : ∀ d : D2, e2 d = L2 d := fun d => by
    simp [e2, Submodule.quotientEquivOfIsCompl_symm_apply]
  have : FiniteDimensional K W := Module.Finite.of_surjective L1 h1
  have hk : Module.finrank K (LinearMap.ker L2) = Module.finrank K (LinearMap.ker L1) := by
    have a1 := LinearMap.finrank_range_add_finrank_ker L1
    have a2 := LinearMap.finrank_range_add_finrank_ker L2
    rw [LinearMap.range_eq_top.2 h1, finrank_top] at a1
    rw [LinearMap.range_eq_top.2 h2, finrank_top] at a2
    omega
  let k : LinearMap.ker L2 ≃ₗ[K] LinearMap.ker L1 := LinearEquiv.ofFinrankEq _ _ hk
  let δ : C ≃ₗ[K] C := (Submodule.prodEquivOfIsCompl _ _ hD2).symm.trans
    ((k.prodCongr (e2.trans e1.symm)).trans (Submodule.prodEquivOfIsCompl _ _ hD1))
  refine ⟨δ, fun c => ?_⟩
  set p := (Submodule.prodEquivOfIsCompl _ _ hD2).symm c with hp
  have hc : c = (p.1 : C) + (p.2 : C) := by
    rw [← Submodule.coe_prodEquivOfIsCompl' _ _ hD2, hp, LinearEquiv.apply_symm_apply]
  have hδ : δ c = ((k p.1 : LinearMap.ker L1) : C) + ((e1.symm (e2 p.2) : D1) : C) := by
    simp only [δ, LinearEquiv.trans_apply, ← hp]
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [hδ, map_add, LinearMap.mem_ker.1 (k p.1).2, zero_add, ← he1, LinearEquiv.apply_symm_apply, he2]
  conv_rhs => rw [hc]
  rw [map_add, LinearMap.mem_ker.1 p.1.2, zero_add]

theorem pi_surj {V : Type*} [AddCommGroup V] [Module K V] {a : ℕ} (ψ : Fin a → Module.Dual K V)
    (hψ : LinearIndependent K ψ) : Function.Surjective (LinearMap.pi ψ) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have hsum : ∑ i, f (Pi.single i 1) • ψ i = 0 := by
    ext v
    have hv : f (LinearMap.pi ψ v) = 0 := hfk ⟨v, rfl⟩
    have hdec : LinearMap.pi ψ v = ∑ i, ψ i v • (Pi.single i 1 : Fin a → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdec, map_sum] at hv
    simpa [smul_eq_mul, mul_comm] using hv
  have hc := Fintype.linearIndependent_iff.1 hψ _ hsum
  apply LinearMap.pi_ext'
  intro i
  ext
  simp [hc i]

theorem trans_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (hx : LinearIndependent K x) (hy : LinearIndependent K y) :
    ∃ A : V ≃ₗ[K] V, ∀ j, A (x j) = y j := by
  set U := Submodule.span K (Set.range x)
  set U' := Submodule.span K (Set.range y)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl U'
  let bx := Module.Basis.span hx
  let by' := Module.Basis.span hy
  have hU : Module.finrank K U = a := by rw [Module.finrank_eq_card_basis bx, Fintype.card_fin]
  have hU' : Module.finrank K U' = a := by rw [Module.finrank_eq_card_basis by', Fintype.card_fin]
  have h1 := Submodule.finrank_add_eq_of_isCompl hC
  have h2 := Submodule.finrank_add_eq_of_isCompl hC'
  let eC : C ≃ₗ[K] C' := LinearEquiv.ofFinrankEq _ _ (by omega)
  let eU : U ≃ₗ[K] U' := bx.equiv by' (Equiv.refl _)
  refine ⟨(Submodule.prodEquivOfIsCompl _ _ hC).symm.trans
    ((eU.prodCongr eC).trans (Submodule.prodEquivOfIsCompl _ _ hC')), fun j => ?_⟩
  have hxj : x j ∈ U := Submodule.subset_span ⟨j, rfl⟩
  simp only [LinearEquiv.trans_apply]
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC ⟨x j, hxj⟩]
  rw [Submodule.coe_prodEquivOfIsCompl']
  have : eU ⟨x j, hxj⟩ = ⟨y j, Submodule.subset_span ⟨j, rfl⟩⟩ := by
    have hb : (⟨x j, hxj⟩ : U) = bx j := by ext; simp [bx, Module.Basis.span_apply]
    rw [hb]
    simp only [eU, Module.Basis.equiv_apply, Equiv.refl_apply]
    exact Module.Basis.span_apply hy j
  simp [LinearEquiv.prodCongr_apply, this]

theorem fix_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (φ ψ : Fin a → Module.Dual K V)
    (hφ : LinearIndependent K φ) (hψ : LinearIndependent K ψ) (h : ∀ i j, φ i (x j) = ψ i (x j)) :
    ∃ B : V ≃ₗ[K] V, (∀ j, B (x j) = x j) ∧ ∀ i v, ψ i (B v) = φ i v := by
  set U := Submodule.span K (Set.range x)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  set Φ := LinearMap.pi φ
  set Ψ := LinearMap.pi ψ
  have hUeq : Φ ∘ₗ U.subtype = Ψ ∘ₗ U.subtype := by
    apply (Module.Basis.span hx).ext
    intro j
    ext i
    simp [Φ, Ψ, Module.Basis.span_apply, h i j]
  have hUv : ∀ u : U, Φ u = Ψ u := fun u => LinearMap.congr_fun hUeq u
  have hsplit : ∀ v : V, ∃ u ∈ U, ∃ c ∈ C, u + c = v := fun v =>
    Submodule.mem_sup.1 (by rw [hC.sup_eq_top]; exact Submodule.mem_top)
  set R := LinearMap.range (Ψ ∘ₗ U.subtype)
  have hsurj : ∀ Θ : V →ₗ[K] (Fin a → K), Function.Surjective Θ → (∀ u : U, Θ u = Ψ u) →
      Function.Surjective (R.mkQ ∘ₗ Θ ∘ₗ C.subtype) := by
    intro Θ hΘ hΘU w
    obtain ⟨w', rfl⟩ := R.mkQ_surjective w
    obtain ⟨v, rfl⟩ := hΘ w'
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    refine ⟨⟨c, hc⟩, ?_⟩
    have h0 : R.mkQ (Θ u) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨u, hu⟩, (hΘU ⟨u, hu⟩).symm⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_add, h0, zero_add]
  obtain ⟨δ, hδ⟩ := surj_equiv (R.mkQ ∘ₗ Ψ ∘ₗ C.subtype) (R.mkQ ∘ₗ Φ ∘ₗ C.subtype)
    (hsurj Ψ (pi_surj ψ hψ) fun _ => rfl) (hsurj Φ (pi_surj φ hφ) hUv)
  set D : C →ₗ[K] (Fin a → K) := Φ ∘ₗ C.subtype - Ψ ∘ₗ C.subtype ∘ₗ δ.toLinearMap
  have hD : ∀ c, D c ∈ R := by
    intro c
    have e := hδ c
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at e
    exact (Submodule.Quotient.eq R).1 e.symm
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (Ψ ∘ₗ U.subtype).rangeRestrict
    (LinearMap.range_rangeRestrict _)
  set β : C →ₗ[K] U := s ∘ₗ D.codRestrict R hD
  have hβ : ∀ c, Ψ (β c : V) = D c := by
    intro c
    have e := congrArg Subtype.val (LinearMap.congr_fun hs (D.codRestrict R hD c))
    simpa [β] using e
  set P := (Submodule.prodEquivOfIsCompl _ _ hC).symm
  have hP : ∀ (u : U) (c : C), P ((u : V) + c) = (u, c) := by
    intro u c
    have e : (u : V) + c = Submodule.prodEquivOfIsCompl _ _ hC (u, c) :=
      (Submodule.coe_prodEquivOfIsCompl' _ _ hC (u, c)).symm
    rw [e]
    exact LinearEquiv.symm_apply_apply _ _
  set B0 : V →ₗ[K] V := (U.subtype ∘ₗ LinearMap.fst K U C + U.subtype ∘ₗ β ∘ₗ LinearMap.snd K U C +
    C.subtype ∘ₗ δ.toLinearMap ∘ₗ LinearMap.snd K U C) ∘ₗ P.toLinearMap
  have hB0 : ∀ (u : U) (c : C), B0 ((u : V) + c) = (u : V) + (β c : V) + (δ c : V) := by
    intro u c
    simp [B0, hP u c]
  have hinj : Function.Injective B0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    have e := hB0 ⟨u, hu⟩ ⟨c, hc⟩
    rw [hv] at e
    have hδU : (δ ⟨c, hc⟩ : V) ∈ U := by
      have : (δ ⟨c, hc⟩ : V) = -(u + (β ⟨c, hc⟩ : V)) := eq_neg_of_add_eq_zero_right e.symm
      rw [this]
      exact U.neg_mem (U.add_mem hu (β _).2)
    have h1 : (δ ⟨c, hc⟩ : V) = 0 := Submodule.disjoint_def.1 hC.disjoint _ hδU (δ _).2
    have h2 : (⟨c, hc⟩ : C) = 0 := δ.injective (by rw [map_zero]; exact Subtype.ext h1)
    have hc0 : c = 0 := congrArg Subtype.val h2
    subst hc0
    have hβ0 : (β ⟨0, hc⟩ : V) = 0 := by
      rw [show (⟨0, hc⟩ : C) = 0 from rfl, map_zero]; rfl
    rw [h1, hβ0, add_zero, add_zero] at e
    rw [add_zero]
    exact e.symm
  refine ⟨LinearEquiv.ofInjectiveEndo B0 hinj, fun j => ?_, fun i v => ?_⟩
  · have hxj : x j ∈ U := Submodule.subset_span ⟨j, rfl⟩
    have e := hB0 ⟨x j, hxj⟩ 0
    simp only [map_zero, Submodule.coe_zero, add_zero] at e
    exact e
  · obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    have hv : Ψ (B0 (u + c)) = Φ (u + c) := by
      rw [show u + c = ((⟨u, hu⟩ : U) : V) + ((⟨c, hc⟩ : C) : V) from rfl, hB0]
      simp only [map_add, hβ, hUv ⟨u, hu⟩, D, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, LinearEquiv.coe_coe]
      abel
    exact congrFun hv i

theorem glPair {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (ξ η : Fin a → Module.Dual K V) (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hξ : LinearIndependent K ξ) (hη : LinearIndependent K η)
    (h : ∀ i j, ξ i (x j) = η i (y j)) :
    ∃ A : V ≃ₗ[K] V, (∀ j, A (x j) = y j) ∧ ∀ i v, η i (A v) = ξ i v := by
  obtain ⟨A0, hA0⟩ := trans_tuple x y hx hy
  set η' : Fin a → Module.Dual K V := fun i => η i ∘ₗ A0.toLinearMap
  have hη' : LinearIndependent K η' := by
    rw [Fintype.linearIndependent_iff] at hη ⊢
    intro c hc i
    apply hη c _ i
    ext v
    have e := LinearMap.congr_fun hc (A0.symm v)
    simpa [η'] using e
  obtain ⟨B, hBx, hB⟩ := fix_tuple x hx ξ η' hξ hη' (fun i j => by simp [η', hA0, h])
  refine ⟨B.trans A0, fun j => by simp [hBx, hA0], fun i v => ?_⟩
  simpa [η'] using hB i v

end Formalism.L2.SG.Pf.NcX.LT.GLP
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcX.LT

namespace WSp

section Lin

variable {K : Type*} [Field K] {n : ℕ}

def dl (u : Fin n → K) : Module.Dual K (Fin n → K) where
  toFun w := u ⬝ᵥ w
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

theorem dl_apply (u w : Fin n → K) : dl u w = u ⬝ᵥ w := rfl

theorem eq_of_dot (u u' : Fin n → K) (h : ∀ w, u ⬝ᵥ w = u' ⬝ᵥ w) : u = u' := by
  funext i
  simpa [dotProduct_single] using h (Pi.single i 1)

end Lin

section Split

variable {K S : Type*} [Field K] [CommRing S] (π π' : S →+* K)

theorem indep_coord {n m : ℕ} (hinj : ∀ s t, π s = π t → π' s = π' t → s = t)
    (hsur : ∀ p : K, ∃ s, π s = p ∧ π' s = 0) (X : Fin m → Fin n → S) (hX : LinearIndependent S X) :
    LinearIndependent K (fun j i => π (X j i)) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro c hc j
  choose s hs1 hs2 using hsur
  have hsum : ∑ k, s (c k) • X k = 0 := by
    funext i
    apply hinj
    · have h1 := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
      simp only [map_sum, map_mul, hs1, map_zero]
      exact h1
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_sum, map_mul, hs2,
        zero_mul, Finset.sum_const_zero, map_zero]
  rw [← hs1 (c j), hX _ hsum j, map_zero]

theorem mat_ext {n : ℕ} (hinj : ∀ s t, π s = π t → π' s = π' t → s = t) (M N : Matrix (Fin n) (Fin n) S)
    (h1 : M.map π = N.map π) (h2 : M.map π' = N.map π') : M = N := by
  ext i j
  exact hinj _ _ (congrArg (fun A => A i j) h1) (congrArg (fun A => A i j) h2)

theorem map_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (x : Fin n → S) (i : Fin n) :
    π ((M *ᵥ x) i) = (M.map π *ᵥ fun j => π (x j)) i := by
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end Split

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem witt_split (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (v : HeightOneSpectrum (𝓞 F)) (π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v)
    (hσ1 : ∀ s, π₁ (sigR (Fv F v) σ s) = π₂ s) (hσ2 : ∀ s, π₂ (sigR (Fv F v) σ s) = π₁ s)
    (hinj : ∀ s t, π₁ s = π₁ t → π₂ s = π₂ t → s = t)
    (hsur : ∀ p q : Fv F v, ∃ s, π₁ s = p ∧ π₂ s = q) {m : ℕ} (X Y : TupV (E := E) v n m)
    (hX : LinearIndependent (Fv F v ⊗[F] E) X) (hY : LinearIndependent (Fv F v ⊗[F] E) Y)
    (hG : gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y) : ∃ g : HA (Fv F v) σ J, g • X = Y := by
  classical
  set J1 : Matrix (Fin n) (Fin n) (Fv F v) := (JR (F := F) (Fv F v) J).map π₁ with hJ1
  have hJ2 : (JR (F := F) (Fv F v) J).map π₂ = J1ᵀ := by
    ext i j
    simp only [Matrix.map_apply, transpose_apply, hJ1, JR]
    rw [← hσ1, (fun x => by simp [sigR, inclR] : ∀ x : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) =
      inclR (F := F) (Fv F v) (σ x)), hJ.1 j i]
  have hdetJ : IsUnit J1.det := by
    have e1 : J1.det = π₁ (JR (F := F) (Fv F v) J).det := (RingHom.map_det π₁ _).symm
    have e2 : (JR (F := F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det := (RingHom.map_det (inclR (F := F) (Fv F v)) J).symm
    rw [e1, e2]
    exact ((Ne.isUnit hJ.2).map (inclR (F := F) (Fv F v))).map π₁

  have hform : ∀ x y : Fin n → (Fv F v) ⊗[F] E,
      π₁ (hR (Fv F v) σ J x y) = (fun i => π₂ (x i)) ⬝ᵥ (J1 *ᵥ fun i => π₁ (y i)) := by
    intro x y
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, hσ1, dotProduct, mulVec, Finset.mul_sum, hJ1,
      Matrix.map_apply, mul_assoc]
  set x1 : Fin m → Fin n → (Fv F v) := fun j i => π₁ (X j i)
  set y1 : Fin m → Fin n → (Fv F v) := fun j i => π₁ (Y j i)
  set x2 : Fin m → Fin n → (Fv F v) := fun j i => π₂ (X j i)
  set y2 : Fin m → Fin n → (Fv F v) := fun j i => π₂ (Y j i)
  have hsur1 : ∀ p : (Fv F v), ∃ s, π₁ s = p ∧ π₂ s = 0 := fun p => hsur p 0
  have hsur2 : ∀ p : (Fv F v), ∃ s, π₂ s = p ∧ π₁ s = 0 := fun p => (hsur 0 p).imp fun _ h => ⟨h.2, h.1⟩
  have hinj' : ∀ s t, π₂ s = π₂ t → π₁ s = π₁ t → s = t := fun s t h2 h1 => hinj s t h1 h2
  have hx1 : LinearIndependent (Fv F v) x1 := indep_coord π₁ π₂ hinj hsur1 X hX
  have hy1 : LinearIndependent (Fv F v) y1 := indep_coord π₁ π₂ hinj hsur1 Y hY
  have hx2 : LinearIndependent (Fv F v) x2 := indep_coord π₂ π₁ hinj' hsur2 X hX
  have hy2 : LinearIndependent (Fv F v) y2 := indep_coord π₂ π₁ hinj' hsur2 Y hY

  have hvecinj : ∀ u : Fin n → (Fv F v), u ᵥ* J1 = 0 → u = 0 := by
    intro u hu
    have : u = (u ᵥ* J1) ᵥ* J1⁻¹ := by rw [vecMul_vecMul, mul_nonsing_inv _ hdetJ, vecMul_one]
    rw [this, hu, zero_vecMul]
  have hforms : ∀ z : Fin m → Fin n → (Fv F v), LinearIndependent (Fv F v) z →
      LinearIndependent (Fv F v) (fun j => dl (z j ᵥ* J1)) := by
    intro z hz
    rw [Fintype.linearIndependent_iff] at hz ⊢
    intro c hc
    apply hz c
    apply hvecinj
    apply eq_of_dot
    intro w
    have e := LinearMap.congr_fun hc w
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, dl_apply, smul_eq_mul,
      LinearMap.zero_apply] at e
    have key : ∀ u, (u ᵥ* J1) ⬝ᵥ w = dl (J1 *ᵥ w) u := fun u => by
      rw [dl_apply, ← dotProduct_mulVec, dotProduct_comm]
    rw [key, zero_dotProduct, map_sum]
    refine (Finset.sum_congr rfl fun x _ => ?_).trans e
    rw [map_smul, ← key, smul_eq_mul]
  have hpair : ∀ i j, dl (x2 i ᵥ* J1) (x1 j) = dl (y2 i ᵥ* J1) (y1 j) := by
    intro i j
    rw [dl_apply, dl_apply, ← dotProduct_mulVec, ← dotProduct_mulVec]
    have e := congrFun (congrFun hG i) j
    simp only [gramR] at e
    have e1 := hform (X i) (X j)
    have e2 := hform (Y i) (Y j)
    rw [e] at e1
    exact e1.symm.trans e2
  obtain ⟨A, hAx, hAη⟩ := GLP.glPair x1 y1 (fun j => dl (x2 j ᵥ* J1)) (fun j => dl (y2 j ᵥ* J1)) hx1 hy1
    (hforms x2 hx2) (hforms y2 hy2) hpair
  set Am := LinearMap.toMatrix' (A : (Fin n → (Fv F v)) →ₗ[(Fv F v)] (Fin n → (Fv F v)))
  set Ai := LinearMap.toMatrix' (A.symm : (Fin n → (Fv F v)) →ₗ[(Fv F v)] (Fin n → (Fv F v)))
  have hAm : ∀ w, Am *ᵥ w = A w := fun w => LinearMap.toMatrix'_mulVec _ w
  have hAAi : Am * Ai = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext w
    simp
  have hAiA : Ai * Am = 1 := mul_eq_one_comm.mp hAAi
  have hJJ : J1 * J1⁻¹ = 1 := mul_nonsing_inv _ hdetJ
  have hJJ' : J1⁻¹ * J1 = 1 := nonsing_inv_mul _ hdetJ
  set B : Matrix (Fin n) (Fin n) (Fv F v) := (J1 * Ai * J1⁻¹)ᵀ
  set Bi : Matrix (Fin n) (Fin n) (Fv F v) := (J1 * Am * J1⁻¹)ᵀ
  have hBBi : B * Bi = 1 := by
    rw [← transpose_mul, ← transpose_one]
    congr 1
    calc J1 * Am * J1⁻¹ * (J1 * Ai * J1⁻¹) = J1 * Am * (J1⁻¹ * J1) * Ai * J1⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJJ', Matrix.mul_one, Matrix.mul_assoc J1, hAAi, Matrix.mul_one, hJJ]
  have hBiB : Bi * B = 1 := mul_eq_one_comm.mp hBBi
  have hU1 : Bᵀ * J1 * Am = J1 := by
    calc Bᵀ * J1 * Am = J1 * Ai * (J1⁻¹ * J1) * Am := by simp only [B, transpose_transpose, Matrix.mul_assoc]
      _ = J1 := by rw [hJJ', Matrix.mul_one, Matrix.mul_assoc, hAiA, Matrix.mul_one]
  have hU2 : Amᵀ * J1ᵀ * B = J1ᵀ := by
    have : Amᵀ * J1ᵀ * B = (Bᵀ * J1 * Am)ᵀ := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [this, hU1]

  choose mk hmk using hsur
  set gm : Matrix (Fin n) (Fin n) ((Fv F v) ⊗[F] E) := Matrix.of fun i j => mk (Am i j) (B i j)
  set gi : Matrix (Fin n) (Fin n) ((Fv F v) ⊗[F] E) := Matrix.of fun i j => mk (Ai i j) (Bi i j)
  have hg1 : gm.map π₁ = Am := by ext i j; simp [gm, (hmk _ _).1]
  have hg2 : gm.map π₂ = B := by ext i j; simp [gm, (hmk _ _).2]
  have hgi1 : gi.map π₁ = Ai := by ext i j; simp [gi, (hmk _ _).1]
  have hgi2 : gi.map π₂ = Bi := by ext i j; simp [gi, (hmk _ _).2]
  have hone1 : (1 : Matrix (Fin n) (Fin n) ((Fv F v) ⊗[F] E)).map π₁ = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hone2 : (1 : Matrix (Fin n) (Fin n) ((Fv F v) ⊗[F] E)).map π₂ = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hm1 : gm * gi = 1 := mat_ext π₁ π₂ hinj _ _ (by rw [Matrix.map_mul, hg1, hgi1, hAAi, hone1])
    (by rw [Matrix.map_mul, hg2, hgi2, hBBi, hone2])
  have hm2 : gi * gm = 1 := mat_ext π₁ π₂ hinj _ _ (by rw [Matrix.map_mul, hg1, hgi1, hAiA, hone1])
    (by rw [Matrix.map_mul, hg2, hgi2, hBiB, hone2])
  set u : GL (Fin n) ((Fv F v) ⊗[F] E) := ⟨gm, gi, hm1, hm2⟩
  have hcT1 : (Formalism.UG.cT (sigR (Fv F v) σ) gm).map π₁ = Bᵀ := by
    ext i j; simp [Formalism.UG.cT, hσ1, ← hg2]
  have hcT2 : (Formalism.UG.cT (sigR (Fv F v) σ) gm).map π₂ = Amᵀ := by
    ext i j; simp [Formalism.UG.cT, hσ2, ← hg1]
  have hu : u ∈ HR (Fv F v) σ J := by
    show Formalism.UG.cT (sigR (Fv F v) σ) gm * JR (F := F) (Fv F v) J * gm = JR (F := F) (Fv F v) J
    apply mat_ext π₁ π₂ hinj
    · rw [Matrix.map_mul, Matrix.map_mul, hcT1, hg1, ← hJ1, hU1]
    · rw [Matrix.map_mul, Matrix.map_mul, hcT2, hg2, hJ2, hU2]
  refine ⟨⟨u, hu⟩, ?_⟩
  have hmul : ∀ w : Fin n → (Fv F v) ⊗[F] E, (⟨u, hu⟩ : HA (Fv F v) σ J) • (fun _ : Fin 1 => w) = fun _ => gm *ᵥ w :=
    fun _ => rfl

  have hB2 : ∀ j, B *ᵥ x2 j = y2 j := by
    intro j
    have hdot : y2 j ᵥ* J1 ᵥ* Am = x2 j ᵥ* J1 := by
      apply eq_of_dot
      intro w
      have e := hAη j w
      simp only [dl_apply, ← hAm] at e
      rw [← dotProduct_mulVec, e]
    calc B *ᵥ x2 j = x2 j ᵥ* J1 ᵥ* Ai ᵥ* J1⁻¹ := by
          simp only [B, mulVec_transpose, vecMul_vecMul]
      _ = y2 j ᵥ* J1 ᵥ* Am ᵥ* Ai ᵥ* J1⁻¹ := by rw [hdot]
      _ = y2 j := by
          simp only [vecMul_vecMul, Matrix.mul_assoc, hAAi, Matrix.mul_one, hJJ, vecMul_one]
  funext j
  show gm *ᵥ X j = Y j
  funext i
  apply hinj
  · rw [map_mulVec, hg1]
    show (Am *ᵥ x1 j) i = y1 j i
    rw [hAm, hAx]
  · rw [map_mulVec, hg2]
    show (B *ᵥ x2 j) i = y2 j i
    rw [hB2]

end Main

end WSp

end Formalism.L2.SG.Pf.NcX.LT
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Polynomial
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcX.LT

namespace LtSplSPf

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sq_of_cm (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem exists_moved_of_cm (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  obtain ⟨-, hC, -, hτ⟩ := h
  by_contra hno
  push Not at hno
  let τ : E →+* ℂ := Classical.arbitrary _
  have hR : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact ((hτ τ x).symm.trans (congrArg τ (hno x)) : _)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (hC.isComplex (InfinitePlace.mk τ)))
    (InfinitePlace.isReal_mk_iff.2 hR)

end CM

section Quad

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E]

theorem exists_alpha (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hmov : ∃ y, σ y ≠ y) :
    ∃ α : E, α ≠ 0 ∧ σ α = -α := by
  obtain ⟨y, hy⟩ := hmov
  refine ⟨y - σ y, sub_ne_zero.2 (Ne.symm hy), ?_⟩
  rw [map_sub, hσ]
  ring

theorem rep_of (σ : E →ₐ[F] E) (hfin : Module.finrank F E = 2) {α : E} (hα0 : α ≠ 0)
    (hσα : σ α = -α) : ∀ e : E, ∃ a b : F, e = algebraMap F E a + b • α := by
  have hli : LinearIndependent F ![(1 : E), α] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [← Algebra.algebraMap_eq_smul_one, Algebra.smul_def] at hst
    have h1 := congrArg σ hst
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσα, map_zero] at h1
    have h2 : (2 : E) * (algebraMap F E t * α) = 0 := by linear_combination hst - h1
    have ht : algebraMap F E t = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left two_ne_zero)).resolve_right hα0
    have ht' : t = 0 := (algebraMap F E).injective (ht.trans (map_zero _).symm)
    subst ht'
    rw [map_zero, zero_mul, add_zero] at hst
    exact ⟨(algebraMap F E).injective (hst.trans (map_zero _).symm), rfl⟩
  intro e
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hfin])
  have hb := B.sum_repr e
  rw [Fin.sum_univ_two] at hb
  simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hb
  refine ⟨B.repr e 0, B.repr e 1, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  exact hb.symm

theorem exists_d (σ : E →ₐ[F] E) {α : E} (hrep : ∀ e : E, ∃ a b : F, e = algebraMap F E a + b • α)
    (hσα : σ α = -α) : ∃ d : F, algebraMap F E d = α * α := by
  obtain ⟨a, b, hab⟩ := hrep (α * α)
  rw [Algebra.smul_def] at hab
  have h1 := congrArg σ hab
  rw [map_mul, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσα, neg_mul_neg] at h1
  have h2 : (2 : E) * (algebraMap F E b * α) = 0 := by linear_combination h1 - hab
  have hb : algebraMap F E b * α = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  exact ⟨a, by rw [hab, hb, add_zero]⟩

end Quad

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] {K : Type} [Field K] [Algebra F K]

def ev (φ : E →ₐ[F] K) : K ⊗[F] E →+* K :=
  (Algebra.TensorProduct.lift (AlgHom.id K K) φ (fun _ _ => Commute.all _ _)).toRingHom

theorem ev_rep (φ : E →ₐ[F] K) (α : E) (a b : K) :
    ev φ (algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] α)) =
      a + b * φ α := by
  simp [ev, Algebra.TensorProduct.algebraMap_apply]

theorem ev_alg (φ : E →ₐ[F] K) (c : K) : ev φ (algebraMap K (K ⊗[F] E) c) = c := by
  simp [ev, Algebra.TensorProduct.algebraMap_apply]

theorem tens_rep {α : E} (hrep : ∀ e : E, ∃ a b : F, e = algebraMap F E a + b • α)
    (s : K ⊗[F] E) : ∃ a b : K,
      s = algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] α) := by
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r e =>
    obtain ⟨a, b, rfl⟩ := hrep e
    refine ⟨r * algebraMap F K a, r * algebraMap F K b, ?_⟩
    have key : r ⊗ₜ[F] (algebraMap F E a + b • α) =
        (r * algebraMap F K a) ⊗ₜ[F] (1 : E) + (r * algebraMap F K b) ⊗ₜ[F] α := by
      rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one (A := E) a,
        ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def,
        mul_comm (algebraMap F K a), mul_comm (algebraMap F K b)]
    rw [key]
    simp [Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by simp only [map_add]; ring⟩

theorem sigR_rep (σ : E →ₐ[F] E) {α : E} (hσα : σ α = -α) (a b : K) :
    sigR K σ (algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] α)) =
      algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) (-b) * ((1 : K) ⊗ₜ[F] α) := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply, hσα, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

theorem u_mul_u {α : E} {d : F} (hd : algebraMap F E d = α * α) :
    ((1 : K) ⊗ₜ[F] α) * ((1 : K) ⊗ₜ[F] α) = algebraMap K (K ⊗[F] E) (algebraMap F K d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := E) d,
    Algebra.algebraMap_eq_smul_one (A := K) d, ← TensorProduct.smul_tmul]

end Tens

theorem main_gen {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] [CharZero E]
    (K : Type) [Field K] [Algebra F K] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (hmov : ∃ y, σ y ≠ y) (hfin : Module.finrank F E = 2) (hnf : ¬ IsField (K ⊗[F] E)) :
    ∃ π₁ π₂ : K ⊗[F] E →+* K,
      (∀ s, π₁ (sigR K σ s) = π₂ s) ∧ (∀ s, π₂ (sigR K σ s) = π₁ s) ∧
      (∀ c : K, π₁ (algebraMap K (K ⊗[F] E) c) = c ∧ π₂ (algebraMap K (K ⊗[F] E) c) = c) ∧
      (∀ s t, π₁ s = π₁ t → π₂ s = π₂ t → s = t) ∧ (∀ p q : K, ∃ s, π₁ s = p ∧ π₂ s = q) := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
  have h2K : (2 : K) ≠ 0 := by
    have := (algebraMap F K).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at this
  obtain ⟨α, hα0, hσα⟩ := exists_alpha σ hσ hmov
  have hrep := rep_of σ hfin hα0 hσα
  obtain ⟨d, hd⟩ := exists_d σ hrep hσα
  have huu := u_mul_u (K := K) hd
  have hrepS := tens_rep (K := K) hrep
  by_cases hsq : ∃ c : K, c * c = algebraMap F K d
  swap
  · exfalso
    apply hnf
    push Not at hsq
    have : Nontrivial (K ⊗[F] E) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F K E
        (algebraMap F K).injective (algebraMap F E).injective
    refine ⟨exists_pair_ne _, mul_comm, ?_⟩
    intro s hs
    obtain ⟨a, b, rfl⟩ := hrepS s
    have hN : a * a - b * b * algebraMap F K d ≠ 0 := by
      intro h0
      by_cases hb : b = 0
      · subst hb
        apply hs
        have ha : a = 0 := by simpa using h0
        simp [ha]
      · apply hsq (a / b)
        rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hb hb)]
        linear_combination h0
    refine ⟨(algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) (-b) * ((1 : K) ⊗ₜ[F] α)) *
      algebraMap K (K ⊗[F] E) (a * a - b * b * algebraMap F K d)⁻¹, ?_⟩
    have hprod : (algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] α)) *
        (algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) (-b) * ((1 : K) ⊗ₜ[F] α)) =
        algebraMap K (K ⊗[F] E) (a * a - b * b * algebraMap F K d) := by
      simp only [map_sub, map_mul, map_neg, ← huu]
      ring
    rw [← mul_assoc, hprod, ← map_mul, mul_inv_cancel₀ hN, map_one]
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : algebraMap F K d = 0 := by rw [← hc, mul_zero]
    have hd0 : d = 0 := (algebraMap F K).injective (h0.trans (map_zero _).symm)
    rw [hd0, map_zero] at hd
    exact hα0 (mul_self_eq_zero.1 hd.symm)
  have hα_nr : α ∉ (algebraMap F E).range := by
    intro h
    obtain ⟨f, hf⟩ := RingHom.mem_range.1 h
    have h1 : σ α = α := by rw [← hf, AlgHom.commutes]
    rw [hσα] at h1
    have h2 : (2 : E) * α = 0 := by linear_combination -h1
    exact hα0 ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hmin : minpoly F α = X ^ 2 - C d := by
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (monic_X_pow_sub_C d two_ne_zero) (minpoly.dvd F α ?_) ?_).symm
    · simp [hd, sq]
    · rw [natDegree_X_pow_sub_C]
      have h0 := minpoly.natDegree_pos hint
      have h1 : (minpoly F α).natDegree ≠ 1 := fun h => hα_nr (minpoly.natDegree_eq_one_iff.1 h)
      omega
  have hadj : Algebra.adjoin F {α} = ⊤ := by
    refine eq_top_iff.2 fun e _ => ?_
    obtain ⟨a, b, rfl⟩ := hrep e
    exact add_mem (Subalgebra.algebraMap_mem _ a)
      (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton α)) b)
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = α := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hroot : ∀ y : K, y * y = algebraMap F K d → aeval y (minpoly F pb.gen) = 0 := by
    intro y hy
    rw [hgen, hmin]
    simp [sq, hy]
  let φ₁ : E →ₐ[F] K := pb.lift c (hroot c hc)
  let φ₂ : E →ₐ[F] K := pb.lift (-c) (hroot (-c) (by rw [neg_mul_neg]; exact hc))
  have hφ₁ : φ₁ α = c := by rw [← hgen]; exact pb.lift_gen _ _
  have hφ₂ : φ₂ α = -c := by rw [← hgen]; exact pb.lift_gen _ _
  refine ⟨ev φ₁, ev φ₂, ?_, ?_, fun c' => ⟨ev_alg φ₁ c', ev_alg φ₂ c'⟩, ?_, ?_⟩
  · intro s
    obtain ⟨a, b, rfl⟩ := hrepS s
    rw [sigR_rep σ hσα, ev_rep, ev_rep, hφ₁, hφ₂]
    ring
  · intro s
    obtain ⟨a, b, rfl⟩ := hrepS s
    rw [sigR_rep σ hσα, ev_rep, ev_rep, hφ₁, hφ₂]
    ring
  · intro s t h1 h2
    obtain ⟨a, b, rfl⟩ := hrepS s
    obtain ⟨a', b', rfl⟩ := hrepS t
    rw [ev_rep, ev_rep, hφ₁] at h1
    rw [ev_rep, ev_rep, hφ₂] at h2
    have ha : a = a' := by
      have h3 : (2 : K) * (a - a') = 0 := by linear_combination h1 + h2
      have h4 := (mul_eq_zero.1 h3).resolve_left h2K
      linear_combination h4
    have hb : b = b' := by
      have h3 : ((2 : K) * c) * (b - b') = 0 := by linear_combination h1 - h2
      have h4 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero h2K hc0)
      linear_combination h4
    rw [ha, hb]
  · intro p q
    refine ⟨algebraMap K (K ⊗[F] E) ((p + q) / 2) +
      algebraMap K (K ⊗[F] E) ((p - q) / (2 * c)) * ((1 : K) ⊗ₜ[F] α), ?_, ?_⟩
    · rw [ev_rep, hφ₁]
      field_simp
      ring
    · rw [ev_rep, hφ₂]
      field_simp
      ring

end LtSplSPf

theorem splitStr : SplitStr := by
  intro F E _ _ _ _ _ σ v hCM hnf
  exact LtSplSPf.main_gen (Fv F v) σ (LtSplSPf.sigma_sq_of_cm σ hCM)
    (LtSplSPf.exists_moved_of_cm σ hCM) hCM.2.2.1 hnf

end Formalism.L2.SG.Pf.NcX.LT
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.WittLocPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

theorem local_witt_theorem : Formalism.L2.SG.Pf.NcX.LocSBPf.WittLocT := by
  intro F E _ _ _ _ _ σ n J a X0 hCM hJ hdet v X hX
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set Y := ratTup (F := F) (Fv F v) X0 with hYdef
  have hYG : gramR (Fv F v) σ J Y = (gramE σ J X0).map (inclR (F := F) (Fv F v)) :=
    PI.VolStabW.LocPosW.gramR_ratTup (Fv F v) σ J X0
  have hunit : IsUnit ((gramE σ J X0).map (inclR (F := F) (Fv F v))).det := by
    have e : ((gramE σ J X0).map (inclR (F := F) (Fv F v))).det = inclR (F := F) (Fv F v) (gramE σ J X0).det :=
      (RingHom.map_det (inclR (F := F) (Fv F v)) (gramE σ J X0)).symm
    rw [e]
    exact (Ne.isUnit hdet).map (inclR (F := F) (Fv F v))
  have hYind : LinearIndependent (Fv F v ⊗[F] E) Y :=
    PI.VolStabW.linIndep_of_isUnit_det (Fv F v) σ J Y (hYG ▸ hunit)
  have hXind : LinearIndependent (Fv F v ⊗[F] E) X :=
    PI.VolStabW.linIndep_of_isUnit_det (Fv F v) σ J X (hX ▸ hunit)
  by_cases hK : IsField (Fv F v ⊗[F] E)
  · letI : Field (Fv F v ⊗[F] E) := hK.toField
    have hσ : ∀ x, σ (σ x) = x := PI.VolStabW.sigma_invol_cm σ hCM
    have hinv : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r t => simp [sigR, hσ]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    letI : StarRing (Fv F v ⊗[F] E) := PI.VolStabW.starOfInv (sigR (Fv F v) σ) hinv
    haveI : CharZero (Fv F v ⊗[F] E) :=
      charZero_of_injective_algebraMap (algebraMap F (Fv F v ⊗[F] E)).injective
    have hs : starRingEnd (Fv F v ⊗[F] E) = sigR (Fv F v) σ := RingHom.ext fun _ => rfl
    have hJ' : ∀ i j, starRingEnd (Fv F v ⊗[F] E) (JR (F := F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by
      intro i j
      rw [hs]
      simp only [JR, Matrix.map_apply]
      rw [(fun x => by simp [sigR, inclR] : ∀ x : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) =
        inclR (F := F) (Fv F v) (σ x)), hJ.1 i j]
    have hdetJ : (JR (F := F) (Fv F v) J).det ≠ 0 := by
      have e : (JR (F := F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det := by
        rw [RingHom.map_det]
        rfl
      rw [e]
      intro h
      apply hJ.2
      exact (inclR (F := F) (Fv F v)).injective (h.trans (map_zero _).symm)
    have hGg : ∀ i j, Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (X i) (X j) =
        Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (Y i) (Y j) := by
      intro i j
      rw [hs]
      exact congrFun (congrFun (hX.trans hYG.symm) i) j
    obtain ⟨g, hg, hgX⟩ := PI.VolStabW.witt_tuple (JR (F := F) (Fv F v) J) hJ' hdetJ Y X hYind hXind hGg
    rw [hs] at hg
    exact ⟨⟨g, hg⟩, funext fun i => hgX i⟩
  · obtain ⟨π₁, π₂, h1, h2, -, h4, h5⟩ := Formalism.L2.SG.Pf.NcX.LT.splitStr σ v hCM hK
    exact Formalism.L2.SG.Pf.NcX.LT.WSp.witt_split σ J hJ v π₁ π₂ h1 h2 h4 h5 Y X hYind hXind (hYG.trans hX.symm)

end Formalism.L2.SG.Pf.NcX.WittLocPf
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.SplitPf

open Formalism.L2.SG.Pf.NcX

theorem omega_finite_volume_of_witt (hW : LocSBPf.WittLocT) (hI : LocSBPf.IntWittAE) : SplitSk.OmFinVol :=
  FinVolSk.omFinVol_of KfOrbPf.finite_orbit_holds (LocSBPf.locSB_of hW hI) BoxVolPf.box_volume_holds

theorem omega_splitting_of_witt (hW : LocSBPf.WittLocT) (hI : LocSBPf.IntWittAE) : Formalism.L2.SG.Pf.NcSplit.SplitOm :=
  SplitSk.splitOm_of AdTupPf.admissible_tuple_holds OmDecompPf.omega_decomposition_holds (omega_finite_volume_of_witt hW hI)

theorem splitOm_of_intWitt (hI : LocSBPf.IntWittAE) : Formalism.L2.SG.Pf.NcSplit.SplitOm :=
  omega_splitting_of_witt WittLocPf.local_witt_theorem hI

end Formalism.L2.SG.Pf.NcX.SplitPf
end
end
