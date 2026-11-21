import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentPreservesFlag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfCommuteOfSeparable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.KillingFormDiffCartanInvolution

section
open MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def HaarQK : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (Q K : Subgroup G) (_ : IsClosed (Q : Set G)) (_ : IsCompact (K : Set G))
  (_ : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
  (νQ : Measure Q) [νQ.IsHaarMeasure] (κ : Measure K) [κ.IsHaarMeasure],
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    μ = c • (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G))

private theorem cancel_lemma_0 {a b s : ℝ≥0∞} (h0 : s ≠ 0) (ht : s ≠ ⊤) (h : s * a = s * b) : a = b := by
  calc a = s⁻¹ * (s * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ = s⁻¹ * (s * b) := by rw [h]
    _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

private theorem mapMulRight_lemma {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H]
    (ν : Measure H) [ν.IsMulLeftInvariant] (a : H) : (ν.map (· * a)).IsMulLeftInvariant := by
  constructor
  intro b
  rw [Measure.map_map (measurable_const_mul b) (measurable_mul_const a)]
  rw [show ((b * ·) ∘ (· * a)) = ((· * a) ∘ (b * ·)) from funext fun x => (mul_assoc b x a).symm]
  rw [← Measure.map_map (measurable_mul_const a) (measurable_const_mul b), MeasureTheory.map_mul_left_eq_self]

private theorem cptRight_lemma_2 {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (κ : Measure H) [κ.IsHaarMeasure] : κ.IsMulRightInvariant := by
  constructor
  intro a
  haveI := mapMulRight_lemma κ a
  have h := Measure.isMulLeftInvariant_eq_smul (κ.map (· * a)) κ
  have hu := congrArg (fun ν : Measure H => ν Set.univ) h
  simp only [Measure.map_apply (measurable_mul_const a) MeasurableSet.univ, Set.preimage_univ,
    Measure.nnreal_smul_coe_apply] at hu
  have h0 : κ Set.univ ≠ 0 := (isOpen_univ.measure_pos κ Set.univ_nonempty).ne'
  have ht : κ Set.univ ≠ ⊤ := measure_ne_top κ _
  have hc : ((κ.map (· * a)).haarScalarFactor κ : ℝ≥0∞) = 1 :=
    cancel_lemma_0 h0 ht (by rw [mul_one, mul_comm]; exact hu.symm)
  rw [h, show (κ.map (· * a)).haarScalarFactor κ = 1 from ENNReal.coe_eq_one.1 hc, one_smul]

theorem haarQK : HaarQK := by
  unfold HaarQK
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hQK νQ _ κ _
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : κ.IsMulRightInvariant := cptRight_lemma_2 κ
  have hνR : ∀ q0 : Q, ∃ c : NNReal, νQ.map (· * q0) = c • νQ := by
    intro q0
    haveI := mapMulRight_lemma νQ q0
    haveI : IsFiniteMeasureOnCompacts (νQ.map (· * q0)) := ⟨fun C hC => by
      rw [Measure.map_apply (measurable_mul_const q0) hC.measurableSet]
      exact ((Homeomorph.mulRight q0).isCompact_preimage.2 hC).measure_lt_top⟩
    exact ⟨_, Measure.isMulLeftInvariant_eq_smul (νQ.map (· * q0)) νQ⟩
  have hT : ∀ g : G, ∃ c : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) =
        c * ∫⁻ h : Q × K, f ((h.1 : G) * (h.2 : G)) ∂(νQ.prod κ) := by
    intro g
    obtain ⟨q0, hq0, k0, hk0, rfl⟩ := hQK g
    obtain ⟨c, hc⟩ := hνR ⟨q0, hq0⟩
    refine ⟨(c : ℝ≥0∞), fun f hf => ?_⟩
    have hF : Measurable (fun p : Q × K => f ((p.1 : G) * (p.2 : G))) := by fun_prop
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ hF.aemeasurable]
    have h1 : ∀ q : Q, ∫⁻ k : K, f ((q : G) * (q0 * k0) * (k : G)) ∂κ =
        ∫⁻ k : K, f (((q * ⟨q0, hq0⟩ : Q) : G) * (k : G)) ∂κ := by
      intro q
      rw [← lintegral_mul_left_eq_self (fun k : K => f (((q * ⟨q0, hq0⟩ : Q) : G) * (k : G))) ⟨k0, hk0⟩]
      congr 1
      funext k
      simp [mul_assoc]
    calc ∫⁻ q : Q, ∫⁻ k : K, f ((q : G) * (q0 * k0) * (k : G)) ∂κ ∂νQ
        = ∫⁻ q : Q, (fun q' : Q => ∫⁻ k : K, f ((q' : G) * (k : G)) ∂κ) (q * ⟨q0, hq0⟩) ∂νQ :=
          lintegral_congr fun q => h1 q
      _ = ∫⁻ q : Q, (fun q' : Q => ∫⁻ k : K, f ((q' : G) * (k : G)) ∂κ) q ∂(νQ.map (· * ⟨q0, hq0⟩)) :=
          (lintegral_map hF.lintegral_prod_right' (measurable_mul_const _)).symm
      _ = (c : ℝ≥0∞) * ∫⁻ q : Q, ∫⁻ k : K, f ((q : G) * (k : G)) ∂κ ∂νQ := by
          rw [hc, lintegral_smul_measure]
          rfl

  have hswap : ∀ f φ : G → ℝ≥0∞, Measurable f → Measurable φ →
      ∫⁻ g, φ g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ =
        ∫⁻ g, f g * ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) ∂μ := by
    intro f φ hf hφ
    have e1 : ∀ g, φ g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, φ g * f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) := fun g =>
      (lintegral_const_mul _ (by fun_prop)).symm
    have e2 : ∀ g, f g * ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, f g * φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) := fun g =>
      (lintegral_const_mul _ (by fun_prop)).symm
    rw [lintegral_congr e1, lintegral_congr e2]
    have m1 : Measurable (fun p : G × (Q × K) => φ p.1 * f ((p.2.1 : G) * p.1 * (p.2.2 : G))) := by fun_prop
    have m2 : Measurable (fun p : G × (Q × K) => f p.1 * φ ((p.2.1 : G)⁻¹ * p.1 * (p.2.2 : G)⁻¹)) := by fun_prop
    rw [lintegral_lintegral_swap m1.aemeasurable]
    conv_rhs => rw [lintegral_lintegral_swap m2.aemeasurable]
    refine lintegral_congr fun h => ?_
    have inv : ∀ F : G → ℝ≥0∞, ∫⁻ g, F ((h.1 : G) * g * (h.2 : G)) ∂μ = ∫⁻ g, F g ∂μ := by
      intro F
      rw [lintegral_mul_left_eq_self (fun x => F (x * (h.2 : G))) (h.1 : G),
        lintegral_mul_right_eq_self F (h.2 : G)]
    rw [← inv (fun g => f g * φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹))]
    refine lintegral_congr fun g => ?_
    rw [mul_comm]
    simp [mul_assoc]
  have hS : ∀ φ : G → ℝ≥0∞, Measurable φ → ∀ g : G,
      ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) := by
    intro φ hφ g
    obtain ⟨q0, hq0, k0, hk0, rfl⟩ := hQK g
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
    have hin : ∀ x : G, ∫⁻ k : K, φ (x * k0 * (k : G)⁻¹) ∂κ = ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ := by
      intro x
      rw [← lintegral_mul_right_eq_self (fun k : K => φ (x * k0 * (k : G)⁻¹)) ⟨k0, hk0⟩]
      refine lintegral_congr fun k => ?_
      simp [mul_assoc]
    have hΨ : Measurable (fun p : G × K => φ (p.1 * (p.2 : G)⁻¹)) := by fun_prop
    calc ∫⁻ q : Q, ∫⁻ k : K, φ ((q : G)⁻¹ * (q0 * k0) * (k : G)⁻¹) ∂κ ∂νQ
        = ∫⁻ q : Q, (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ) ((q : G)⁻¹ * q0) ∂νQ := by
          refine lintegral_congr fun q => ?_
          show _ = ∫⁻ k : K, φ ((q : G)⁻¹ * q0 * (k : G)⁻¹) ∂κ
          rw [← hin ((q : G)⁻¹ * q0)]
          simp only [mul_assoc]
      _ = ∫⁻ q : Q, (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ)
            (((⟨q0, hq0⟩ * q : Q) : G)⁻¹ * q0) ∂νQ :=
          (lintegral_mul_left_eq_self
            (fun q : Q => (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ) ((q : G)⁻¹ * q0)) ⟨q0, hq0⟩).symm
      _ = ∫⁻ q : Q, ∫⁻ k : K, φ ((q : G)⁻¹ * (k : G)⁻¹) ∂κ ∂νQ := by
          refine lintegral_congr fun q => ?_
          simp [mul_assoc]

  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have h1C : (1 : G) ∈ interior C := mem_interior_iff_mem_nhds.2 hC1
  obtain ⟨f0, hf0⟩ : ∃ f0 : G → ℝ≥0∞, f0 = C.indicator 1 := ⟨_, rfl⟩
  have hf0m : Measurable f0 := hf0 ▸ measurable_one.indicator hCm
  have hΦm : Measurable (fun p : Q × K => (p.1 : G) * (p.2 : G)) := by fun_prop
  have hΦc : Continuous (fun p : Q × K => (p.1 : G) * (p.2 : G)) := by fun_prop
  have hΨm : Measurable (fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) := by fun_prop
  have hΨc : Continuous (fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) := by fun_prop
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Measure G, ρ = (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G)) := ⟨_, rfl⟩
  have hPρ : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ h : Q × K, f ((h.1 : G) * (h.2 : G)) ∂(νQ.prod κ) = ∫⁻ g, f g ∂ρ := fun f hf => by
    rw [hρ, lintegral_map hf hΦm]
  have hρC : ρ C = (νQ.prod κ) ((fun p : Q × K => (p.1 : G) * (p.2 : G)) ⁻¹' C) := by
    rw [hρ, Measure.map_apply hΦm hCm]
  have hρCt : ρ C ≠ ⊤ := by
    rw [hρC]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (t := (Subtype.val ⁻¹' ((fun x : G × G => x.1 * x.2) '' (C ×ˢ (K : Set G))) : Set Q) ×ˢ
      (Set.univ : Set K)) ?_) ((hQ.isClosedEmbedding_subtypeVal.isCompact_preimage ((hCc.prod hK).image continuous_mul)).prod
        isCompact_univ).measure_lt_top)
    intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    exact ⟨((p.1 : G) * (p.2 : G), ((p.2 : K) : G)⁻¹), ⟨hp, K.inv_mem p.2.2⟩, by simp⟩
  have hρC0 : ρ C ≠ 0 := by
    rw [hρC]
    exact ((isOpen_interior.preimage hΦc).measure_pos _ ⟨(1, 1), by simpa using h1C⟩).trans_le
      (measure_mono (Set.preimage_mono interior_subset)) |>.ne'
  have hμCt : μ C ≠ ⊤ := hCc.measure_lt_top.ne
  have hμC0 : μ C ≠ 0 :=
    ((isOpen_interior.measure_pos μ ⟨1, h1C⟩).trans_le (measure_mono interior_subset)).ne'
  have hs : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
      (νQ.prod κ) ((fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) ⁻¹' C) := by
    rw [lintegral_map (f := f0) hf0m hΨm |>.symm, hf0, lintegral_indicator_one hCm, Measure.map_apply hΨm hCm]
  have hst : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) ≠ ⊤ := by
    rw [hs]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (t := (Subtype.val ⁻¹' ((fun x : G × G => x.1 * x.2⁻¹) '' ((K : Set G) ×ˢ C)) : Set Q) ×ˢ
      (Set.univ : Set K)) ?_) ((hQ.isClosedEmbedding_subtypeVal.isCompact_preimage ((hK.prod hCc).image (by fun_prop))).prod
        isCompact_univ).measure_lt_top)
    intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    exact ⟨(((p.2 : K) : G)⁻¹, (p.1 : G)⁻¹ * (p.2 : G)⁻¹), ⟨K.inv_mem p.2.2, hp⟩, by group⟩
  have hs0 : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) ≠ 0 := by
    rw [hs]
    exact ((isOpen_interior.preimage hΨc).measure_pos _ ⟨(1, 1), by simpa using h1C⟩).trans_le
      (measure_mono (Set.preimage_mono interior_subset)) |>.ne'

  have hμf0 : ∫⁻ g, f0 g ∂μ = μ C := by rw [hf0, lintegral_indicator_one hCm]
  have hρf0 : ∫⁻ g, f0 g ∂ρ = ρ C := by rw [hf0, lintegral_indicator_one hCm]
  choose c hc using hT
  have hTm : Measurable (fun g : G => ∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) :=
    (by fun_prop : Measurable (fun p : G × (Q × K) => f0 ((p.2.1 : G) * p.1 * (p.2.2 : G)))).lintegral_prod_right'
  have key : ∀ f : G → ℝ≥0∞, Measurable f → (∫⁻ g, f g ∂μ) * ρ C = μ C * ∫⁻ g, f g ∂ρ := by
    intro f hf
    set s0 := ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) with hs0def
    have A := hswap f f0 hf hf0m
    have B := hswap f0 f0 hf0m hf0m
    simp only [hS f0 hf0m] at A B
    rw [lintegral_mul_const _ hf] at A
    rw [lintegral_mul_const _ hf0m, hμf0] at B
    have e : ∀ g, f0 g * (∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ρ C =
        f0 g * (∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ∫⁻ x, f x ∂ρ := by
      intro g
      rw [hc g f hf, hc g f0 hf0m, hPρ f hf, hPρ f0 hf0m, hρf0]
      ring
    have hmain : s0 * ((∫⁻ g, f g ∂μ) * ρ C) = s0 * (μ C * ∫⁻ g, f g ∂ρ) := by
      calc s0 * ((∫⁻ g, f g ∂μ) * ρ C) = (∫⁻ g, f g ∂μ) * s0 * ρ C := by ring
        _ = (∫⁻ g, f0 g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ) * ρ C := by
            rw [A]
        _ = ∫⁻ g, f0 g * (∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ρ C ∂μ :=
            (lintegral_mul_const' _ _ hρCt).symm
        _ = ∫⁻ g, f0 g * (∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) *
              ∫⁻ x, f x ∂ρ ∂μ := lintegral_congr e
        _ = (∫⁻ g, f0 g * ∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ) *
              ∫⁻ x, f x ∂ρ := lintegral_mul_const _ (hf0m.mul hTm)
        _ = s0 * (μ C * ∫⁻ g, f g ∂ρ) := by rw [B]; ring
    exact cancel_lemma_0 hs0 hst hmain
  refine ⟨μ C * (ρ C)⁻¹, mul_ne_zero hμC0 (ENNReal.inv_ne_zero.2 hρCt),
    ENNReal.mul_ne_top hμCt (ENNReal.inv_ne_top.2 hρC0), ?_⟩
  rw [← hρ]
  ext B hB
  have hk := key (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, lintegral_indicator_one hB] at hk
  rw [Measure.smul_apply, smul_eq_mul]
  calc μ B = μ B * ρ C * (ρ C)⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hρC0 hρCt, mul_one]
    _ = μ C * ρ B * (ρ C)⁻¹ := by rw [hk]
    _ = μ C * (ρ C)⁻¹ * ρ B := by ring

end GlobalTheory.CompanionTheory.QuotVan
end

section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def HaarNM : Prop := ∀ {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [LocallyCompactSpace Q] [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  (νQ : Measure Q) [νQ.IsHaarMeasure] (N M : Subgroup Q) [N.Normal]
  (_ : IsClosed (N : Set Q)) (_ : IsClosed (M : Set Q))
  (_ : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m) (_ : N ⊓ M = ⊥)
  (νN : Measure N) [νN.IsHaarMeasure] (νM : Measure M) [νM.IsHaarMeasure],
  ∃ δ : M → ℝ≥0∞, Measurable δ ∧ (∀ m, δ m ≠ ∞) ∧
    νQ = ((νN.prod νM).withDensity fun p => δ p.2).map (fun p : N × M => (p.1 : Q) * (p.2 : Q))

theorem map_withDensity_eq_of_scale {X : Type*} [MeasurableSpace X] (ρ : Measure X) (S : X → X)
    (hS : Measurable S) (f : X → ℝ≥0∞) (hf : Measurable f) (a : ℝ≥0∞) (ha0 : a ≠ 0) (hat : a ≠ ∞)
    (hρ : ρ.map S = a • ρ) (hfS : ∀ x, f (S x) = a * f x) :
    (ρ.withDensity f).map S = ρ.withDensity f := by
  ext A hA
  rw [map_apply hS hA, withDensity_apply _ (hS hA), withDensity_apply _ hA]
  have key : ∫⁻ x, (A.indicator f) x ∂(ρ.map S) = a * ∫⁻ x, A.indicator f x ∂ρ := by
    rw [hρ, lintegral_smul_measure]; rfl
  rw [lintegral_map (hf.indicator hA) hS] at key
  have h2 : (fun x => A.indicator f (S x)) = fun x => a * (S ⁻¹' A).indicator f x := by
    funext x
    by_cases hx : S x ∈ A
    · have hx' : x ∈ S ⁻¹' A := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', hfS]
    · have hx' : x ∉ S ⁻¹' A := hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]
  rw [h2, lintegral_const_mul _ (hf.indicator (hS hA)), lintegral_indicator (hS hA),
    lintegral_indicator hA] at key
  exact (ENNReal.mul_right_inj ha0 hat).1 key

section
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

noncomputable def conjCE (N : Subgroup Q) [N.Normal] (g : Q) : N ≃ₜ* N where
  toMulEquiv := MulAut.conjNormal g
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun u : N => g * (u : Q) * g⁻¹ := by fun_prop
    exact this
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun u : N => g⁻¹ * (u : Q) * g⁻¹⁻¹ := by fun_prop
    exact this

theorem conjCE_coe (N : Subgroup Q) [N.Normal] (g : Q) (u : N) :
    ((conjCE N g u : N) : Q) = g * u * g⁻¹ := rfl

theorem conjCE_mul (N : Subgroup Q) [N.Normal] (g h : Q) :
    conjCE N (g * h) = (conjCE N h).trans (conjCE N g) := by
  ext u
  simp [conjCE_coe, mul_assoc]

variable [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q] [T2Space Q]
variable (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [SecondCountableTopology N]
  [SecondCountableTopology M]

noncomputable def modInv (m : M) : ℝ≥0∞ :=
  ((mulEquivHaarChar (conjCE N (m : Q)) : ℝ≥0) : ℝ≥0∞)⁻¹

theorem modInv_ne_top (m : M) : modInv N M m ≠ ∞ := by
  have h := (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'
  simp [modInv, h]

theorem modInv_ne_zero (m : M) : modInv N M m ≠ 0 := by
  simp [modInv]

theorem modInv_mul (m m' : M) : modInv N M (m * m') = modInv N M m * modInv N M m' := by
  have h1 := (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'
  have h2 := (mulEquivHaarChar_pos (conjCE N (m' : Q))).ne'
  simp only [modInv, Subgroup.coe_mul, conjCE_mul, mulEquivHaarChar_trans, ENNReal.coe_mul]
  rw [ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), mul_comm]

theorem map_conj (ν : Measure N) [ν.IsHaarMeasure] (m : M) :
    ν.map (conjCE N (m : Q)) = modInv N M m • ν := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : N)
  haveI : ν.Regular := regular_of_isMulLeftInvariant hK ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩
    hK.measure_lt_top.ne
  have h := mulEquivHaarChar_smul_map ν (conjCE N (m : Q))
  have hc : ((mulEquivHaarChar (conjCE N (m : Q)) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'
  rw [ENNReal.smul_def] at h
  conv_rhs => rw [← h]
  rw [smul_smul, modInv, ENNReal.inv_mul_cancel hc ENNReal.coe_ne_top, one_smul]

theorem measurable_modInv : Measurable (modInv N M) := by
  let ν : Measure N := haar
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : N)
  have hs : IsOpen (interior K) := isOpen_interior
  have hs0 : ν (interior K) ≠ 0 := (hs.measure_pos ν ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hst : ν (interior K) ≠ ∞ :=
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne
  let F : M × N → N := fun p => conjCE N (p.1 : Q) p.2
  have hF : Continuous F := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun p : M × N => (p.1 : Q) * (p.2 : Q) * (p.1 : Q)⁻¹ := by fun_prop
    exact this
  have hB : MeasurableSet (F ⁻¹' interior K) := (hs.preimage hF).measurableSet
  have hm := measurable_measure_prodMk_left (ν := ν) hB
  have he : modInv N M = fun m => ν (Prod.mk m ⁻¹' (F ⁻¹' interior K)) / ν (interior K) := by
    funext m
    have h := congrArg (fun μ : Measure N => μ (interior K)) (map_conj N M ν m)
    simp only [Measure.smul_apply, smul_eq_mul] at h
    rw [map_apply (map_continuous _).measurable hs.measurableSet] at h
    have h3 : Prod.mk m ⁻¹' (F ⁻¹' interior K) = conjCE N (m : Q) ⁻¹' interior K := rfl
    rw [h3, h, ENNReal.mul_div_cancel_right hs0 hst]
  rw [he]
  exact hm.div_const _

theorem map_translate (νN : Measure N) [νN.IsHaarMeasure] (νM : Measure M) [νM.IsHaarMeasure]
    [LocallyCompactSpace M] (u : N) (m : M) :
    ((νN.prod νM).withDensity fun p => modInv N M p.2).map
        (fun p : N × M => (u * conjCE N (m : Q) p.1, m * p.2)) =
      (νN.prod νM).withDensity fun p => modInv N M p.2 := by
  have hS1 : Measurable fun x : N => u * conjCE N (m : Q) x :=
    (continuous_const.mul (map_continuous _)).measurable
  have hS2 : Measurable fun x : M => m * x := (continuous_const.mul continuous_id).measurable
  refine map_withDensity_eq_of_scale _ _ (hS1.prodMap hS2) _
    ((measurable_modInv N M).comp measurable_snd) (modInv N M m) (modInv_ne_zero N M m)
    (modInv_ne_top N M m) ?_ ?_
  · have h1 : νN.map (fun x : N => u * conjCE N (m : Q) x) = modInv N M m • νN := by
      have h0 : (fun x : N => u * conjCE N (m : Q) x) = (fun x => u * x) ∘ conjCE N (m : Q) := rfl
      rw [h0, ← map_map (measurable_const_mul u) (map_continuous _).measurable, map_conj,
        Measure.map_smul, map_mul_left_eq_self]
    have h2 : νM.map (fun x : M => m * x) = νM := map_mul_left_eq_self νM m
    have h3 := map_prod_map νN νM hS1 hS2
    rw [h1, h2] at h3
    show map (Prod.map _ _) _ = _
    rw [← h3, prod_smul_left]
  · intro x
    exact modInv_mul N M m x.2

end

theorem mulMap_injective {Q : Type} [Group Q] (N M : Subgroup Q) (hinf : N ⊓ M = ⊥) :
    Function.Injective (fun p : N × M => (p.1 : Q) * (p.2 : Q)) := by
  rintro ⟨u, m⟩ ⟨u', m'⟩ h
  have h' : (u : Q) * m = u' * m' := h
  have h1 : (u' : Q)⁻¹ * u = m' * (m : Q)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h'
  have h2 : (u' : Q)⁻¹ * u ∈ N ⊓ M :=
    ⟨N.mul_mem (N.inv_mem u'.2) u.2, by rw [h1]; exact M.mul_mem m'.2 (M.inv_mem m.2)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  have hu : (u : Q) = u' := (inv_mul_eq_one.1 h2).symm
  have hm : (m : Q) = m' := by
    rw [hu] at h'
    exact mul_left_cancel h'
  exact Prod.ext (Subtype.ext hu) (Subtype.ext hm)

theorem haarNM : HaarNM := by
  intro Q _ _ _ _ _ _ _ _ νQ _ N M _ hNc hMc hdec hinf νN _ νM _
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hMc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology M := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : PolishSpace N := PI.VolStabS.TopoPolish.polish_of_lcsc N
  haveI : PolishSpace M := PI.VolStabS.TopoPolish.polish_of_lcsc M
  let φ : N × M → Q := fun p => (p.1 : Q) * (p.2 : Q)
  have φc : Continuous φ := by fun_prop
  have φemb : MeasurableEmbedding φ := φc.measurableEmbedding (mulMap_injective N M hinf)
  let f : N × M → ℝ≥0∞ := fun p => modInv N M p.2
  have hf : Measurable f := (measurable_modInv N M).comp measurable_snd
  let ρ : Measure (N × M) := (νN.prod νM).withDensity f
  let ν' : Measure Q := ρ.map φ
  haveI : SigmaFinite ρ := SigmaFinite.withDensity_of_ne_top
    (Filter.Eventually.of_forall fun p => modInv_ne_top N M p.2)
  haveI : SigmaFinite ν' := φemb.sigmaFinite_map
  haveI : ν'.IsMulLeftInvariant := ⟨fun q => by
    obtain ⟨u, hu, m, hm, rfl⟩ := hdec q
    have hS1 : Measurable fun x : N => (⟨u, hu⟩ : N) * conjCE N m x :=
      (continuous_const.mul (map_continuous _)).measurable
    have hS2 : Measurable fun x : M => (⟨m, hm⟩ : M) * x :=
      (continuous_const.mul continuous_id).measurable
    have hS : Measurable fun p : N × M => ((⟨u, hu⟩ : N) * conjCE N m p.1, (⟨m, hm⟩ : M) * p.2) :=
      hS1.prodMap hS2
    have hcomm : (fun x => u * m * x) ∘ φ =
        φ ∘ fun p : N × M => ((⟨u, hu⟩ : N) * conjCE N m p.1, (⟨m, hm⟩ : M) * p.2) := by
      funext p
      show (u * m) * ((p.1 : Q) * p.2) = (u * ((m * p.1) * m⁻¹)) * (m * p.2)
      group
    show map (fun x => u * m * x) (map φ ρ) = map φ ρ
    rw [map_map (measurable_const_mul _) φemb.measurable, hcomm, ← map_map φemb.measurable hS]
    exact congrArg (map φ) (map_translate N M νN νM ⟨u, hu⟩ ⟨m, hm⟩)⟩
  have hν0 : ν' Set.univ ≠ 0 := by
    intro h0
    rw [φemb.map_apply, Set.preimage_univ] at h0
    have hac : (νN.prod νM) ≪ ρ := withDensity_absolutelyContinuous' hf.aemeasurable
      (Filter.Eventually.of_forall fun p => modInv_ne_zero N M p.2)
    exact (isOpen_univ.measure_pos (νN.prod νM) Set.univ_nonempty).ne' (hac h0)
  obtain ⟨n, hn⟩ : ∃ n, ν' (spanningSets (ν' + νQ) n) ≠ 0 := by
    by_contra! h
    exact hν0 (by rw [← iUnion_spanningSets (ν' + νQ)]; exact measure_iUnion_null h)
  have hfin := measure_spanningSets_lt_top (ν' + νQ) n
  rw [Measure.add_apply] at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have key := measure_eq_div_smul νQ ν' hn h1.ne
  have hc : νQ (spanningSets (ν' + νQ) n) / ν' (spanningSets (ν' + νQ) n) ≠ ∞ :=
    ENNReal.div_ne_top h2.ne hn
  generalize νQ (spanningSets (ν' + νQ) n) / ν' (spanningSets (ν' + νQ) n) = c at key hc
  refine ⟨fun m => c * modInv N M m, (measurable_modInv N M).const_mul c,
    fun m => ENNReal.mul_ne_top hc (modInv_ne_top N M m), key.trans ?_⟩
  have h3 : (fun p : N × M => c * modInv N M p.2) = c • f := rfl
  rw [h3, withDensity_smul c hf, Measure.map_smul]

end GlobalTheory.CompanionTheory.QuotVan
end

section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def AbsVanish : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (Q K : Subgroup G) (_ : IsClosed (Q : Set G)) (_ : IsCompact (K : Set G))
  (_ : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
  (N M : Subgroup Q) [N.Normal] (_ : IsClosed (N : Set Q)) (_ : IsClosed (M : Set Q))
  (_ : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m) (_ : N ⊓ M = ⊥)
  (νN : Measure N) [νN.IsHaarMeasure]
  (T : Subgroup G) (_ : ∀ t ∈ T, ∃ h : t ∈ Q, (⟨t, h⟩ : Q) ∈ M)
  (μT : Measure T) [SFinite μT] [μT.IsInvInvariant]
  (F : G → ℂ), Measurable F → (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) →
    (∀ x, ∫ u : N, F (((u : Q) : G) * x) ∂νN = 0) → quotIntegral μ T μT F = 0

theorem integral_mul_weight_eq_zero {Q : Type} [Group Q] [MeasurableSpace Q]
    (N M : Subgroup Q) (νN : Measure N) [SFinite νN] (νM : Measure M) [SFinite νM]
    (δ : M → ℝ≥0∞) (hδ : Measurable δ) (hδt : ∀ m, δ m ≠ ∞)
    (hφ : MeasurableEmbedding (fun p : N × M => (p.1 : Q) * (p.2 : Q)))
    (f w : Q → ℂ) (w' : M → ℂ) (hw : ∀ (u : N) (m : M), w ((u : Q) * (m : Q)) = w' m)
    (hf0 : ∀ m : M, ∫ u : N, f ((u : Q) * (m : Q)) ∂νN = 0) :
    ∫ q, f q * w q ∂(((νN.prod νM).withDensity fun p => δ p.2).map
      (fun p : N × M => (p.1 : Q) * (p.2 : Q))) = 0 := by
  rw [hφ.integral_map,
    integral_withDensity_eq_integral_toReal_smul (f := fun p : N × M => δ p.2) (hδ.comp measurable_snd)
      (Filter.Eventually.of_forall fun p => lt_top_iff_ne_top.2 (hδt p.2))]
  by_cases hI : Integrable (fun p : N × M => (δ p.2).toReal • (f ((p.1 : Q) * (p.2 : Q)) *
      w ((p.1 : Q) * (p.2 : Q)))) (νN.prod νM)
  · rw [integral_prod_symm _ hI]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun m => ?_)
    simp only [hw, Pi.zero_apply]
    rw [integral_smul, integral_mul_const, hf0 m]
    simp
  · exact integral_undef hI

theorem integral_eq_smul_integral_avg {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) (Q K : Subgroup G) (νQ : Measure Q) [SFinite νQ] (κ : Measure K) [SFinite κ]
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hμ : μ = c • (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G)))
    (F : G → ℂ) (hF : Measurable F) (hFK : ∀ k ∈ K, ∀ x, F (x * k) = F x)
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hfin : ∀ᵐ g ∂μ, ρ g < ∞)
    (hint : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ) :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ =
      c.toReal • ∫ q : Q, F q * (((∫⁻ k : K, ρ ((q : G) * (k : G)) ∂κ).toReal : ℝ) : ℂ) ∂νQ := by
  have hm : Measurable (fun p : Q × K => (p.1 : G) * (p.2 : G)) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hg : Measurable (fun g => F g * ((ρ g).toReal : ℂ)) :=
    hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)
  subst hμ
  have hint' := (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).1
    ((integrable_smul_measure hc0 hct).1 hint)
  have hfin' : ∀ᵐ p ∂(νQ.prod κ), ρ ((p.1 : G) * (p.2 : G)) < ∞ :=
    ae_of_ae_map hm.aemeasurable ((Measure.absolutelyContinuous_smul hc0).ae_le hfin)
  have hint'' : Integrable (fun p : Q × K => F ((p.1 : G) * (p.2 : G)) *
      ((ρ ((p.1 : G) * (p.2 : G))).toReal : ℂ)) (νQ.prod κ) := hint'
  rw [integral_smul_measure, integral_map hm.aemeasurable hg.aestronglyMeasurable,
    integral_prod _ hint'']
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hfin'] with q hq
  have hmk : Measurable fun k : K => ρ ((q : G) * (k : G)) :=
    hρ.comp (measurable_subtype_coe.const_mul _)
  have e1 : ∀ k : K, F ((q : G) * (k : G)) = F q := fun k => hFK k k.2 _
  simp only [e1]
  rw [integral_const_mul, integral_complex_ofReal, integral_toReal hmk.aemeasurable hq]

section Normalisers

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def onQ (Q T : Subgroup G) (h : T ≤ Q) (t : T) : T.subgroupOf Q :=
  ⟨⟨t, h t.2⟩, Subgroup.mem_subgroupOf.2 t.2⟩

theorem measurable_onQ (Q T : Subgroup G) (h : T ≤ Q) : Measurable (onQ Q T h) :=
  (measurable_subtype_coe.subtype_mk).subtype_mk

theorem isInvInvariant_map_onQ (Q T : Subgroup G) (h : T ≤ Q) (μT : Measure T) [μT.IsInvInvariant] :
    (μT.map (onQ Q T h)).IsInvInvariant := by
  have hi : MeasurableInv T := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hi' : MeasurableInv (T.subgroupOf Q) := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  show Measure.map Inv.inv (μT.map (onQ Q T h)) = μT.map (onQ Q T h)
  rw [Measure.map_map measurable_inv (measurable_onQ Q T h)]
  have e : (Inv.inv ∘ onQ Q T h) = onQ Q T h ∘ Inv.inv := rfl
  rw [e, ← Measure.map_map (measurable_onQ Q T h) measurable_inv]
  exact congrArg (Measure.map (onQ Q T h)) (Measure.inv_eq_self μT)

theorem normaliser_onQ {Q T : Subgroup G} (hTQ : T ≤ Q) {μT : Measure T} {σ : Q → ℝ≥0∞}
    (hσ : Measurable σ) (h : ∀ q : Q, ∫⁻ t : T, σ (⟨t, hTQ t.2⟩ * q) ∂μT = 1) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ)) σ := by
  refine ⟨hσ, fun q => ?_⟩
  have hm : Measurable fun x : T.subgroupOf Q => σ ((x : Q) * q) :=
    hσ.comp (measurable_subtype_coe.mul_const q)
  rw [lintegral_map hm (measurable_onQ Q T hTQ)]
  exact h q

theorem normaliser_avg {Q K T : Subgroup G} (hTQ : T ≤ Q) (κ : Measure K) [SFinite κ]
    (hκ : κ Set.univ = 1) {μT : Measure T} [SFinite μT] {ρ : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser T μT ρ) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ))
      (fun q => ∫⁻ k : K, ρ ((q : G) * (k : G)) ∂κ) := by
  have hm : Measurable fun p : Q × K => ρ ((p.1 : G) * (p.2 : G)) :=
    hρ.1.comp ((measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd))
  refine normaliser_onQ hTQ hm.lintegral_prod_right' fun q => ?_
  rw [lintegral_lintegral_swap]
  · have key : ∀ k : K, ∫⁻ t : T, ρ (((⟨t, hTQ t.2⟩ * q : Q) : G) * (k : G)) ∂μT = 1 := fun k => by
      have := hρ.2 ((q : G) * (k : G))
      simpa [mul_assoc] using this
    simp only [key, lintegral_one, hκ]
  · have : Measurable fun p : T × K => ρ (((p.1 : G) * (q : G)) * (p.2 : G)) :=
      hρ.1.comp (((measurable_subtype_coe.comp measurable_fst).mul_const _).mul
        (measurable_subtype_coe.comp measurable_snd))
    exact this.aemeasurable

theorem normaliser_proj {Q T : Subgroup G} (hTQ : T ≤ Q) (N M : Subgroup Q) [hN : N.Normal]
    (hTM : ∀ t : T, (⟨t, hTQ t.2⟩ : Q) ∈ M) (hdec : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m)
    (pr : Q → M) (hprm : Measurable pr) (hpr : ∀ (u : N) (m : M), pr ((u : Q) * (m : Q)) = m)
    {μT : Measure T} {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser T μT ρ) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ)) (fun q => ρ ((pr q : Q) : G)) := by
  refine normaliser_onQ hTQ
    (hρ.1.comp (measurable_subtype_coe.comp (measurable_subtype_coe.comp hprm))) fun q => ?_
  obtain ⟨u, hu, m, hm, rfl⟩ := hdec q
  have key : ∀ t : T, ((pr ((⟨t, hTQ t.2⟩ : Q) * (u * m)) : Q) : G) = (t : G) * ((m : Q) : G) := by
    intro t
    have e : (⟨t, hTQ t.2⟩ : Q) * (u * m) =
        ((⟨(⟨t, hTQ t.2⟩ : Q) * u * (⟨t, hTQ t.2⟩ : Q)⁻¹, hN.conj_mem u hu _⟩ : N) : Q) *
          ((⟨(⟨t, hTQ t.2⟩ : Q) * m, M.mul_mem (hTM t) hm⟩ : M) : Q) := by
      simp only
      group
    rw [e, hpr]
    rfl
  simp only [key]
  exact hρ.2 _

end Normalisers

theorem absVanish_of (hQK : HaarQK) (hNM : HaarNM) : AbsVanish := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec N M _ hN hM hnm hinf νN _ T hT μT _ _ F hF hFT hFK hF0
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T μT ρ
  swap
  · simp [quotIntegral, hex]
  rw [quotIntegral, dif_pos hex]
  have hρ := hex.choose_spec
  generalize hex.choose = ρ at hρ
  have hTQ : T ≤ Q := fun t ht => by
    obtain ⟨h, _⟩ := hT t ht
    exact h
  have hTM : ∀ t : T, (⟨t, hTQ t.2⟩ : Q) ∈ M := fun t => by
    obtain ⟨h, h'⟩ := hT t t.2
    exact h'
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology Q := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology M := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : PolishSpace N := PI.VolStabS.TopoPolish.polish_of_lcsc N
  haveI : PolishSpace M := PI.VolStabS.TopoPolish.polish_of_lcsc M
  obtain ⟨νQ, _⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨νM, _⟩ : ∃ ν : Measure M, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨κ, _, hκ⟩ : ∃ κ : Measure K, κ.IsHaarMeasure ∧ κ Set.univ = 1 :=
    ⟨Measure.haarMeasure ⊤, inferInstance, Measure.haarMeasure_self⟩
  obtain ⟨c, hc0, hct, hμ⟩ := hQK μ Q K hQ hK hdec νQ κ
  obtain ⟨δ, hδ, hδt, hνQ⟩ := hNM νQ N M hN hM hnm hinf νN νM
  have φc : Continuous fun p : N × M => (p.1 : Q) * (p.2 : Q) := by fun_prop
  have φemb : MeasurableEmbedding fun p : N × M => (p.1 : Q) * (p.2 : Q) :=
    φc.measurableEmbedding (mulMap_injective N M hinf)
  let pr : Q → M := Function.extend (fun p : N × M => (p.1 : Q) * (p.2 : Q)) Prod.snd (fun _ => 1)
  have hprm : Measurable pr := φemb.measurable_extend measurable_snd measurable_const
  have hpr : ∀ (u : N) (m : M), pr ((u : Q) * (m : Q)) = m := fun u m =>
    (mulMap_injective N M hinf).extend_apply Prod.snd _ (u, m)
  have hfin := GlobalTheory.CompanionTheory.QuotNorm.ae_lt_top_of_normaliser (μG := μ) hρ
  by_cases hint : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ
  swap
  · exact integral_undef hint
  rw [integral_eq_smul_integral_avg μ Q K νQ κ c hc0 hct hμ F hF hFK ρ hρ.1 hfin hint]
  haveI := isInvInvariant_map_onQ Q T hTQ μT
  have hρ₁ := normaliser_avg (Q := Q) hTQ κ hκ hρ
  have hρ₂ := normaliser_proj hTQ N M hTM hnm pr hprm hpr hρ
  have e := GlobalTheory.CompanionTheory.QuotNorm.integral_normaliser_eq_of (μG := νQ) (F := fun q : Q => F q)
    (hF.comp measurable_subtype_coe)
    (fun h hh g => hFT h (Subgroup.mem_subgroupOf.1 hh) g) hρ₁ hρ₂
  have z : ∫ q : Q, F q * ((ρ ((pr q : Q) : G)).toReal : ℂ) ∂νQ = 0 := by
    rw [hνQ]
    exact integral_mul_weight_eq_zero N M νN νM δ hδ hδt φemb _ _
      (fun m => ((ρ ((m : Q) : G)).toReal : ℂ)) (fun u m => by simp only [hpr])
      (fun m => hF0 _)
  rw [e, z, smul_zero]

theorem absVanish : AbsVanish := absVanish_of haarQK haarNM

end GlobalTheory.CompanionTheory.QuotVan

end
end

section
noncomputable section

open Matrix Module PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.IwaDecomp

section Isometry

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

def isoOfFinrank (h : finrank ℂ F = finrank ℂ G) : F ≃ₗᵢ[ℂ] G :=
  (stdOrthonormalBasis ℂ F).equiv (stdOrthonormalBasis ℂ G) (finCongr h)

theorem exists_extend (h : finrank ℂ F = finrank ℂ G) (S : Submodule ℂ F) (φ : S →ₗᵢ[ℂ] G) :
    ∃ ψ : F →ₗᵢ[ℂ] G, ∀ s : S, ψ s = φ s := by
  let e := isoOfFinrank h
  let L : S →ₗᵢ[ℂ] F := e.symm.toLinearIsometry.comp φ
  refine ⟨e.toLinearIsometry.comp L.extend, fun s => ?_⟩
  simp [L, LinearIsometry.extend_apply]

theorem finrank_map_isometry (K : E →ₗᵢ[ℂ] E) (A : Submodule ℂ E) :
    finrank ℂ (A.map K.toLinearMap) = finrank ℂ A :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective K.toLinearMap K.injective A)).symm

theorem exists_isometry_flag {A₁ A₂ B₁ B₂ : Submodule ℂ E} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, A₁.map K.toLinearMap = B₁ ∧ A₂.map K.toLinearMap = B₂ := by
  let φ : A₁ ≃ₗᵢ[ℂ] B₁ := isoOfFinrank h₁
  let S : Submodule ℂ A₂ := A₁.comap A₂.subtype
  let ι : S →ₗᵢ[ℂ] A₁ :=
    ⟨LinearMap.codRestrict A₁ (A₂.subtype ∘ₗ S.subtype) (fun x => x.2), fun x => rfl⟩
  let j : B₁ →ₗᵢ[ℂ] B₂ := ⟨Submodule.inclusion hB, fun x => rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_extend h₂ S (j.comp (φ.toLinearIsometry.comp ι))
  let L : A₂ →ₗᵢ[ℂ] E := B₂.subtypeₗᵢ.comp ψ
  have hK : ∀ a : A₂, L.extend a = ψ a := fun a => by
    simpa [L] using LinearIsometry.extend_apply L a
  refine ⟨L.extend, ?_, ?_⟩
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₁)
    rintro _ ⟨a, ha, rfl⟩
    have h := hK ⟨a, hA ha⟩
    have h2 := hψ ⟨⟨a, hA ha⟩, ha⟩
    change L.extend a ∈ B₁
    rw [show L.extend a = ((ψ ⟨a, hA ha⟩ : B₂) : E) from h, show ψ ⟨a, hA ha⟩ = _ from h2]
    exact (φ (ι ⟨⟨a, hA ha⟩, ha⟩)).2
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₂)
    rintro _ ⟨a, ha, rfl⟩
    change L.extend a ∈ B₂
    rw [show L.extend a = ((ψ ⟨a, ha⟩ : B₂) : E) from hK ⟨a, ha⟩]
    exact (ψ ⟨a, ha⟩).2

theorem exists_isometry_flag_of_equiv {V : Type*} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] E)
    {A₁ A₂ B₁ B₂ : Submodule ℂ V} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, (A₁.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₁.map (e : V →ₗ[ℂ] E) ∧
      (A₂.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₂.map (e : V →ₗ[ℂ] E) := by
  have hT : ∀ W : Submodule ℂ V, finrank ℂ (W.map (e : V →ₗ[ℂ] E)) = finrank ℂ W :=
    fun W => LinearEquiv.finrank_map_eq e W
  exact exists_isometry_flag (Submodule.map_mono hA) (Submodule.map_mono hB)
    (by rw [hT, hT, h₁]) (by rw [hT, hT, h₂])

end Isometry

variable {n : ℕ}

theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  simp [img]

theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img (a * b) W = img a (img b W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem img_mono (a : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') : img a W ≤ img a W' :=
  Submodule.map_mono h

def linEquiv (g : GL (Fin n) ℂ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.toLin'OfInv (M := (g⁻¹ : GL (Fin n) ℂ).val) (M' := g.val) (by simp) (by simp)

theorem img_eq_map_linEquiv (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img g W = W.map (linEquiv g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  rfl

theorem finrank_img (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : finrank ℂ (img g W) = finrank ℂ W := by
  rw [img_eq_map_linEquiv]
  exact LinearEquiv.finrank_map_eq (linEquiv g) W

theorem thetaR_eq_self_iff (k : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n k = k ↔ k.val.conjTranspose = (k⁻¹ : GL (Fin n) ℂ).val := by
  have h : (thetaR (starRingEnd ℂ) n k).val = (k⁻¹ : GL (Fin n) ℂ).val.conjTranspose := by
    rw [thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]
  constructor
  · intro e
    have h' := congrArg Units.val e
    rw [h] at h'
    rw [← h', Matrix.conjTranspose_conjTranspose]
  · intro e
    refine Units.ext ?_
    rw [h, ← e, Matrix.conjTranspose_conjTranspose]

abbrev eu (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm

theorem unitary_of_isometry (K : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧
      ∀ W : Submodule ℂ (Fin n → ℂ), (img k W).map (eu n : (Fin n → ℂ) →ₗ[ℂ] _) =
        (W.map (eu n : (Fin n → ℂ) →ₗ[ℂ] _)).map K.toLinearMap := by
  let f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    ((eu n).symm : _ →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ K.toLinearMap ∘ₗ (eu n : (Fin n → ℂ) →ₗ[ℂ] _)
  let M : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' f
  have hM : Matrix.toLin' M = f := Matrix.toLin'_toMatrix' f
  have key : ∀ x y : Fin n → ℂ, f y ⬝ᵥ star (f x) = y ⬝ᵥ star x := fun x y => by
    have := K.inner_map_map (eu n x) (eu n y)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    exact this
  have hc : ∀ i l, M l i = f (Pi.single i 1) l := fun i l => by
    rw [← hM, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  have h1 : M.conjTranspose * M = 1 := by
    ext i j
    have h := key (Pi.single i 1) (Pi.single j 1)
    have e : (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ star (Pi.single i 1 : Fin n → ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      rw [single_one_dotProduct]
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [← e, ← h]
    simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, hc, Pi.star_apply, mul_comm]
  have h2 : M * M.conjTranspose = 1 := mul_eq_one_comm.1 h1
  let k : GL (Fin n) ℂ := ⟨M, M.conjTranspose, h2, h1⟩
  refine ⟨k, (thetaR_eq_self_iff k).2 rfl, fun W => ?_⟩
  have : (k.val : Matrix (Fin n) (Fin n) ℂ) = M := rfl
  change Submodule.map _ (Submodule.map (Matrix.toLin' M) W) = _
  rw [hM, ← Submodule.map_comp, ← Submodule.map_comp]
  refine congrArg (fun t => Submodule.map t W) (LinearMap.ext fun x => ?_)
  simp [f]

theorem img_mul_inv_eq {g k : GL (Fin n) ℂ} {W : Submodule ℂ (Fin n → ℂ)} (h : img k (img g⁻¹ W) = W) :
    img (g * k⁻¹) W = W := by
  conv_lhs => rw [← h]
  rw [← img_mul, ← img_mul, show g * k⁻¹ * k * g⁻¹ = 1 by group, img_one]

theorem exists_flag_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧ img k (img g⁻¹ W₁) = W₁ ∧ img k (img g⁻¹ W₂) = W₂ := by
  obtain ⟨K, hK₁, hK₂⟩ := exists_isometry_flag_of_equiv (eu n) (img_mono g⁻¹ h) h
    (finrank_img g⁻¹ W₁) (finrank_img g⁻¹ W₂)
  obtain ⟨k, hk, hkK⟩ := unitary_of_isometry K
  have hinj : Function.Injective (eu n : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := (eu n).injective
  have inj := Submodule.map_injective_of_injective hinj
  exact ⟨k, hk, inj ((hkK _).trans hK₁), inj ((hkK _).trans hK₂)⟩

theorem exists_eq_mul_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ q k : GL (Fin n) ℂ, g = q * k ∧ thetaR (starRingEnd ℂ) n k = k ∧ img q W₁ = W₁ ∧ img q W₂ = W₂ := by
  obtain ⟨k, hk, h₁, h₂⟩ := exists_flag_unitary W₁ W₂ h g
  exact ⟨g * k⁻¹, k, by group, hk, img_mul_inv_eq h₁, img_mul_inv_eq h₂⟩

theorem iwaFlag : PositivityTheory.Rg.BcB.D4.IwaFlag := fun _ W₁ W₂ h g => by
  obtain ⟨q, k, e, hk, h₁, h₂⟩ := exists_eq_mul_unitary W₁ W₂ h g
  exact ⟨q, ⟨h₁, h₂⟩, k, hk, e⟩

end GlobalTheory.CompanionTheory.IwaDecomp
end
end

section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.QuotVan

variable {n : ℕ}

local notation "θc" => thetaR (starRingEnd ℂ) n

theorem isMulRightInvariant_of_center {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (hG : ∀ Δ : G →* ℝ≥0, (∀ g, (∀ h, g * h = h * g) → Δ g = 1) → ∀ g, Δ g = 1)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : Measure.modularCharacter g = 1 := by
    refine hG Measure.modularCharacter (fun z hz => ?_) g
    have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
    rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      Measure.IsMulLeftInvariant.map_mul_left_eq_self] at h1
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
    have h2 := congrArg (fun m : Measure G => m C) h1
    have hne : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
    have hnt : μ C ≠ ⊤ := hC.measure_lt_top.ne
    simp only [Measure.coe_nnreal_smul_apply] at h2
    have h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
    exact_mod_cast h3
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from h, one_smul]

theorem isMulRightInvariant_GL (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (μ : Measure (GL (Fin n) ℂ)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  haveI := GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n
  haveI := GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n
  exact isMulRightInvariant_of_center (fun Δ hc g => GlobalTheory.SplitFlip.hom_eq_one_of_center Δ hc g) μ

def uK (n : ℕ) : Subgroup (GL (Fin n) ℂ) := MonoidHom.eqLocus (thetaR (starRingEnd ℂ) n) (MonoidHom.id _)

theorem isCompact_uK (n : ℕ) : IsCompact (uK n : Set (GL (Fin n) ℂ)) := by
  have h := GlobalTheory.Tw.isCompact_unitary_GL n
  convert h using 1
  ext k
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, Matrix.mem_unitaryGroup_iff]
  change thetaR (starRingEnd ℂ) n k = k ↔ k.val * star k.val = 1
  constructor
  · intro hk
    have h1 := GlobalTheory.CompanionTheory.NilChangeVar.theta_val k
    rw [hk] at h1
    have h2 : star k.val = (k⁻¹ : GL (Fin n) ℂ).val := by
      rw [Matrix.star_eq_conjTranspose]
      conv_lhs => rw [h1]
      rw [Matrix.conjTranspose_conjTranspose]
    rw [h2]
    exact Units.mul_inv k
  · intro hk
    refine Units.ext ?_
    rw [GlobalTheory.CompanionTheory.NilChangeVar.theta_val]
    have : (k⁻¹ : GL (Fin n) ℂ).val = star k.val := Units.inv_eq_of_mul_eq_one_right hk
    rw [this, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem commute_of_commute_separable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f a b : Module.End ℂ V) (hs : (LinearMap.charpoly f).Separable) (ha : Commute f a) (hb : Commute f b) :
    a * b = b * a := by
  have hlocus : (⊤ : Submodule ℂ V) ≤ LinearMap.eqLocus (a * b) (b * a) := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    refine iSup_le fun μ x hx => ?_
    have hdim : Module.finrank ℂ (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
    obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hdim
    have key : ∀ c : Module.End ℂ V, Commute f c → ∃ α : ℂ, ∀ y ∈ f.maxGenEigenspace μ, c y = α • y := by
      intro c hc
      obtain ⟨α, hα⟩ := hv ⟨c v, Module.End.mapsTo_maxGenEigenspace_of_comm hc μ v.2⟩
      refine ⟨α, fun y hy => ?_⟩
      obtain ⟨β, hβ⟩ := hv ⟨y, hy⟩
      have hβ' : β • (v : V) = y := congrArg Subtype.val hβ
      have hα' : α • (v : V) = c v := congrArg Subtype.val hα
      rw [← hβ', map_smul, ← hα', smul_comm]
    obtain ⟨α, hα⟩ := key a ha
    obtain ⟨β, hβ⟩ := key b hb
    change (a * b) x = (b * a) x
    rw [Module.End.mul_apply, Module.End.mul_apply, hβ x hx, hα x hx, map_smul, map_smul, hα x hx, hβ x hx, smul_comm]
  exact LinearMap.ext fun x => hlocus (Submodule.mem_top (x := x))

theorem twCent_comm {d : GL (Fin n) ℂ} (hd : (d * θc d).val.charpoly.Separable)
    {a b : GL (Fin n) ℂ} (ha : a ∈ twCent θc d) (hb : b ∈ twCent θc d) : a * b = b * a := by
  have hs : (LinearMap.charpoly (Matrix.toLin' (d * θc d).val)).Separable := by
    rwa [Matrix.charpoly_toLin']
  have cm : ∀ t ∈ twCent θc d, Commute (Matrix.toLin' (d * θc d).val) (Matrix.toLin' t.val) := by
    intro t ht
    have h := GlobalTheory.CompanionTheory.FlagCent.commute_norm (starRingEnd ℂ) (fun x => by simp) ht
    change Matrix.toLin' _ * Matrix.toLin' _ = Matrix.toLin' _ * Matrix.toLin' _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      ← Units.val_mul, ← Units.val_mul, h]
  have := commute_of_commute_separable _ _ _ hs (cm a ha) (cm b hb)
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul] at this
  exact Units.ext (by simpa using Matrix.toLin'.injective this)

end GlobalTheory.CompanionTheory.QuotVan
end

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotVan

section Ring

variable {R : Type*} [Ring R]

def lev (p₁ p₂ p₃ a : R) : R := p₁ * a * p₁ + p₂ * a * p₂ + p₃ * a * p₃

theorem lev_mul {p₁ p₂ p₃ a b : R} (hs : p₁ + p₂ + p₃ = 1)
    (o12 : p₁ * p₂ = 0) (o13 : p₁ * p₃ = 0) (o21 : p₂ * p₁ = 0) (o23 : p₂ * p₃ = 0)
    (o31 : p₃ * p₁ = 0) (o32 : p₃ * p₂ = 0) (ab : a * b = 1)
    (a21 : p₂ * a * p₁ = 0) (a31 : p₃ * a * p₁ = 0) (a32 : p₃ * a * p₂ = 0)
    (b21 : p₂ * b * p₁ = 0) (b32 : p₃ * b * p₂ = 0) (b31 : p₃ * b * p₁ = 0) :
    lev p₁ p₂ p₃ a * lev p₁ p₂ p₃ b = 1 := by
  have i1 : p₁ * p₁ = p₁ := by
    have := congrArg (fun x => p₁ * x) hs
    simpa [mul_add, o12, o13] using this
  have i2 : p₂ * p₂ = p₂ := by
    have := congrArg (fun x => p₂ * x) hs
    simpa [mul_add, o21, o23] using this
  have i3 : p₃ * p₃ = p₃ := by
    have := congrArg (fun x => p₃ * x) hs
    simpa [mul_add, o31, o32] using this
  have e : lev p₁ p₂ p₃ a * lev p₁ p₂ p₃ b =
      p₁ * a * p₁ * b * p₁ + p₂ * a * p₂ * b * p₂ + p₃ * a * p₃ * b * p₃ := by
    simp only [lev, add_mul, mul_add, mul_assoc]
    simp only [← mul_assoc (p₁) (p₁), ← mul_assoc p₁ p₂, ← mul_assoc p₁ p₃, ← mul_assoc p₂ p₁,
      ← mul_assoc p₂ p₂, ← mul_assoc p₂ p₃, ← mul_assoc p₃ p₁, ← mul_assoc p₃ p₂, ← mul_assoc p₃ p₃,
      i1, i2, i3, o12, o13, o21, o23, o31, o32, zero_mul, mul_zero, add_zero, zero_add]
  have key : ∀ p : R, p * p = p → p * a * p₁ * b * p + p * a * p₂ * b * p + p * a * p₃ * b * p = p := by
    intro p hp
    calc p * a * p₁ * b * p + p * a * p₂ * b * p + p * a * p₃ * b * p
        = p * a * (p₁ + p₂ + p₃) * b * p := by noncomm_ring
      _ = p * (a * b) * p := by rw [hs]; simp [mul_assoc]
      _ = p := by rw [ab, mul_one, hp]
  have k1 := key p₁ i1
  have k2 := key p₂ i2
  have k3 := key p₃ i3
  have t1 : p₁ * a * p₂ * b * p₁ = 0 := by simp only [mul_assoc] at b21 ⊢; simp [b21]
  have t2 : p₁ * a * p₃ * b * p₁ = 0 := by simp only [mul_assoc] at b31 ⊢; simp [b31]
  have t3 : p₂ * a * p₁ * b * p₂ = 0 := by rw [a21]; simp
  have t4 : p₂ * a * p₃ * b * p₂ = 0 := by simp only [mul_assoc] at b32 ⊢; simp [b32]
  have t5 : p₃ * a * p₁ * b * p₃ = 0 := by rw [a31]; simp
  have t6 : p₃ * a * p₂ * b * p₃ = 0 := by rw [a32]; simp
  rw [t1, t2, add_zero, add_zero] at k1
  rw [t3, t4, zero_add, add_zero] at k2
  rw [t5, t6, zero_add, zero_add] at k3
  rw [e, k1, k2, k3, hs]

theorem eq_lev_add {p₁ p₂ p₃ a : R} (hs : p₁ + p₂ + p₃ = 1)
    (a21 : p₂ * a * p₁ = 0) (a31 : p₃ * a * p₁ = 0) (a32 : p₃ * a * p₂ = 0) :
    a - lev p₁ p₂ p₃ a = p₁ * a * p₂ + p₁ * a * p₃ + p₂ * a * p₃ := by
  have h : a = (p₁ + p₂ + p₃) * a * (p₁ + p₂ + p₃) := by rw [hs]; simp
  have h2 : (p₁ + p₂ + p₃) * a * (p₁ + p₂ + p₃) = p₁ * a * p₁ + p₁ * a * p₂ + p₁ * a * p₃ +
      (p₂ * a * p₁ + p₂ * a * p₂ + p₂ * a * p₃) + (p₃ * a * p₁ + p₃ * a * p₂ + p₃ * a * p₃) := by
    noncomm_ring
  rw [a21, a31, a32] at h2
  have h3 := h.trans h2
  simp only [lev]
  nth_rewrite 1 [h3]
  abel

end Ring

end GlobalTheory.CompanionTheory.QuotVan
end

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotVan

section Levi

variable {n : ℕ}

local notation "Mx" => Matrix (Fin n) (Fin n) ℂ
local notation "Sb" => Submodule ℂ (Fin n → ℂ)

open GlobalTheory.CompanionTheory.FlagCent (mem_img_iff)

theorem mulVec_inv_mulVec (g : GL (Fin n) ℂ) (y : Fin n → ℂ) :
    g.val *ᵥ ((g⁻¹ : GL (Fin n) ℂ).val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp

theorem img_eq_of_mapsTo (g : GL (Fin n) ℂ) (W : Sb) (h₁ : ∀ y ∈ W, g.val *ᵥ y ∈ W)
    (h₂ : ∀ y ∈ W, (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ W) : img g W = W := by
  ext y
  rw [mem_img_iff]
  refine ⟨fun h => ?_, h₂ y⟩
  have := h₁ _ h
  rwa [mulVec_inv_mulVec] at this

theorem mulVec_mem_of_img (g : GL (Fin n) ℂ) {W : Sb} (h : img g W = W) {y : Fin n → ℂ} (hy : y ∈ W) :
    g.val *ᵥ y ∈ W := by
  rw [← h]
  exact ⟨y, hy, by rw [Matrix.toLin'_apply]⟩

theorem inv_mulVec_mem_of_img (g : GL (Fin n) ℂ) {W : Sb} (h : img g W = W) {y : Fin n → ℂ} (hy : y ∈ W) :
    (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ W := by
  rw [← h] at hy
  exact (mem_img_iff g _ y).1 hy

theorem exists_stable_compl (γ : Mx) (hs : γ.charpoly.Separable) (W : Sb)
    (hW : ∀ x ∈ W, γ *ᵥ x ∈ W) : ∃ C : Sb, IsCompl W C ∧ ∀ x ∈ C, γ *ᵥ x ∈ C := by
  have hss : Module.End.IsSemisimple (Matrix.toLin' γ : Module.End ℂ (Fin n → ℂ)) := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := LinearMap.charpoly (Matrix.toLin' γ)) ?_ (LinearMap.aeval_self_charpoly _)
    rw [Matrix.charpoly_toLin']
    exact hs.squarefree
  obtain ⟨C, hC, hc⟩ := Module.End.isSemisimple_iff.1 hss W
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (Matrix.toLin' γ)).2 fun x hx => by
      simpa [Matrix.toLin'_apply] using hW x hx)
  refine ⟨C, hc, fun x hx => ?_⟩
  have := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (Matrix.toLin' γ)).1 hC x hx
  simpa [Matrix.toLin'_apply] using this

theorem exists_levi_spaces (γ : GL (Fin n) ℂ) (hs : γ.val.charpoly.Separable) {W₁ W₂ : Sb} (hle : W₁ ≤ W₂)
    (h₁ : img γ W₁ = W₁) (h₂ : img γ W₂ = W₂) :
    ∃ V₂ V₃ : Sb, W₁ ⊔ V₂ = W₂ ∧ W₁ ⊓ V₂ = ⊥ ∧ W₂ ⊔ V₃ = ⊤ ∧ W₂ ⊓ V₃ = ⊥ ∧
      img γ V₂ = V₂ ∧ img γ V₃ = V₃ := by
  obtain ⟨A, hA, hAs⟩ := exists_stable_compl γ.val hs W₁ fun x hx => mulVec_mem_of_img γ h₁ hx
  obtain ⟨V₃, hV, hVs⟩ := exists_stable_compl γ.val hs W₂ fun x hx => mulVec_mem_of_img γ h₂ hx
  have st : ∀ C : Sb, (∀ x ∈ C, γ.val *ᵥ x ∈ C) → img γ C = C := fun C hC => by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (GlobalTheory.CompanionTheory.IwaDecomp.finrank_img γ C)
    rintro _ ⟨x, hx, rfl⟩
    simpa [Matrix.toLin'_apply] using hC x hx
  refine ⟨A ⊓ W₂, V₃, ?_, ?_, hV.sup_eq_top, hV.inf_eq_bot, st _ fun x hx => ?_, st _ hVs⟩
  · rw [← sup_inf_assoc_of_le A hle, hA.sup_eq_top, top_inf_eq]
  · rw [← inf_assoc, hA.inf_eq_bot, bot_inf_eq]
  · exact ⟨hAs x hx.1, mulVec_mem_of_img γ h₂ hx.2⟩

theorem exists_sum_along_flag {W₁ W₂ V₂ V₃ : Sb} (c₁ : W₁ ⊔ V₂ = W₂) (c₂ : W₂ ⊔ V₃ = ⊤) (y : Fin n → ℂ) :
    ∃ a ∈ W₁, ∃ b ∈ V₂, ∃ c ∈ V₃, y = a + b + c := by
  have hy : y ∈ W₂ ⊔ V₃ := by rw [c₂]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
  rw [← c₁] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

theorem exists_proj {W₁ W₂ V₂ V₃ : Sb} (c₁ : W₁ ⊔ V₂ = W₂) (d₁ : W₁ ⊓ V₂ = ⊥) (c₂ : W₂ ⊔ V₃ = ⊤)
    (d₂ : W₂ ⊓ V₃ = ⊥) : ∃ P₁ P₂ P₃ : Mx, P₁ + P₂ + P₃ = 1 ∧ (∀ y, P₁ *ᵥ y ∈ W₁) ∧ (∀ y, P₂ *ᵥ y ∈ V₂) ∧
      (∀ y, P₃ *ᵥ y ∈ V₃) ∧ (∀ y ∈ W₂, P₃ *ᵥ y = 0) ∧ (∀ y ∈ W₁, P₂ *ᵥ y = 0) ∧
      (∀ y ∈ V₂, P₁ *ᵥ y = 0) ∧ (∀ y ∈ V₃, P₁ *ᵥ y = 0) ∧ ∀ y ∈ V₃, P₂ *ᵥ y = 0 := by
  have hle₁ : W₁ ≤ W₂ := c₁ ▸ le_sup_left
  have hle₂ : V₂ ≤ W₂ := c₁ ▸ le_sup_right
  have h3 : IsCompl V₃ W₂ := ⟨disjoint_iff.2 (by rw [inf_comm]; exact d₂),
    codisjoint_iff.2 (by rw [sup_comm]; exact c₂)⟩
  have h1 : IsCompl W₁ (V₂ ⊔ V₃) := by
    refine ⟨Submodule.disjoint_def.2 fun y hy hy' => ?_, codisjoint_iff.2 ?_⟩
    · obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 hy'
      have hcW : c ∈ W₂ := by
        have := W₂.sub_mem (hle₁ hy) (hle₂ hb)
        simpa using this
      have hc0 : c = 0 := by
        have : c ∈ W₂ ⊓ V₃ := ⟨hcW, hc⟩
        rw [d₂] at this
        simpa using this
      subst hc0
      have : b + 0 ∈ W₁ ⊓ V₂ := ⟨hy, by simpa using hb⟩
      rw [d₁] at this
      simpa using this
    · rw [← sup_assoc, c₁, c₂]
  let E₁ := W₁.projection (V₂ ⊔ V₃) h1
  let E₃ := V₃.projection W₂ h3
  have e1 : ∀ a ∈ W₁, E₁ a = a := fun a ha => Submodule.projection_apply_left h1 ⟨a, ha⟩
  have e1' : ∀ b ∈ V₂ ⊔ V₃, E₁ b = 0 := fun b hb => Submodule.projection_apply_of_mem_right h1 hb
  have e3 : ∀ c ∈ V₃, E₃ c = c := fun c hc => Submodule.projection_apply_left h3 ⟨c, hc⟩
  have e3' : ∀ b ∈ W₂, E₃ b = 0 := fun b hb => Submodule.projection_apply_of_mem_right h3 hb
  have m1 : ∀ y, LinearMap.toMatrix' E₁ *ᵥ y = E₁ y := fun y => LinearMap.toMatrix'_mulVec E₁ y
  have m3 : ∀ y, LinearMap.toMatrix' E₃ *ᵥ y = E₃ y := fun y => LinearMap.toMatrix'_mulVec E₃ y
  have m2 : ∀ y, (1 - LinearMap.toMatrix' E₁ - LinearMap.toMatrix' E₃ : Mx) *ᵥ y = y - E₁ y - E₃ y := fun y => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, m1, m3]
  refine ⟨LinearMap.toMatrix' E₁, 1 - LinearMap.toMatrix' E₁ - LinearMap.toMatrix' E₃, LinearMap.toMatrix' E₃,
    by abel, fun y => ?_, fun y => ?_, fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, fun y hy => ?_⟩
  · rw [m1]; exact Submodule.projection_apply_mem h1 y
  · rw [m2]
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_sum_along_flag c₁ c₂ y
    have f1 : E₁ (a + b + c) = a := by
      rw [map_add, map_add, e1 a ha, e1' b (Submodule.mem_sup_left hb),
        e1' c (Submodule.mem_sup_right hc), add_zero, add_zero]
    have f3 : E₃ (a + b + c) = c := by
      rw [map_add, map_add, e3' a (hle₁ ha), e3' b (hle₂ hb), e3 c hc, zero_add, zero_add]
    rw [f1, f3, show a + b + c - a - c = b by abel]
    exact hb
  · rw [m3]; exact Submodule.projection_apply_mem h3 y
  · rw [m3]; exact e3' y hy
  · rw [m2, e1 y hy, e3' y (hle₁ hy)]; simp
  · rw [m1]; exact e1' y (Submodule.mem_sup_left hy)
  · rw [m1]; exact e1' y (Submodule.mem_sup_right hy)
  · rw [m2, e1' y (Submodule.mem_sup_right hy), e3 y hy]; simp

end Levi

end GlobalTheory.CompanionTheory.QuotVan
end

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotVan

section Decomp

variable {n : ℕ}

local notation "Mx" => Matrix (Fin n) (Fin n) ℂ
local notation "Sb" => Submodule ℂ (Fin n → ℂ)

open GlobalTheory.CompanionTheory.NilChangeVar (eq_zero_of_mulVec)

theorem levi_decomp {W₁ W₂ V₂ V₃ : Sb} (c₁ : W₁ ⊔ V₂ = W₂) (d₁ : W₁ ⊓ V₂ = ⊥) (c₂ : W₂ ⊔ V₃ = ⊤)
    (d₂ : W₂ ⊓ V₃ = ⊥) (q : GL (Fin n) ℂ) (hq₁ : img q W₁ = W₁) (hq₂ : img q W₂ = W₂) :
    ∃ u m : GL (Fin n) ℂ, q = u * m ∧ u.val - 1 ∈ nilrad W₁ W₂ ∧ img m W₁ = W₁ ∧ img m W₂ = W₂ ∧
      img m V₂ = V₂ ∧ img m V₃ = V₃ := by
  obtain ⟨P₁, P₂, P₃, hs, r₁, r₂, r₃, k₃, k₂, k₁₂, k₁₃, k₂₃⟩ := exists_proj c₁ d₁ c₂ d₂
  have hle₁ : W₁ ≤ W₂ := c₁ ▸ le_sup_left
  have hle₂ : V₂ ≤ W₂ := c₁ ▸ le_sup_right
  have mv : ∀ (A B : Mx) y, (A * B) *ᵥ y = A *ᵥ (B *ᵥ y) := fun A B y => (Matrix.mulVec_mulVec _ _ _).symm
  have o12 : P₁ * P₂ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₁₂ _ (r₂ y)
  have o13 : P₁ * P₃ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₁₃ _ (r₃ y)
  have o21 : P₂ * P₁ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₂ _ (r₁ y)
  have o23 : P₂ * P₃ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₂₃ _ (r₃ y)
  have o31 : P₃ * P₁ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₃ _ (hle₁ (r₁ y))
  have o32 : P₃ * P₂ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₃ _ (hle₂ (r₂ y))
  have tri : ∀ A : Mx, (∀ y ∈ W₁, A *ᵥ y ∈ W₁) → (∀ y ∈ W₂, A *ᵥ y ∈ W₂) →
      P₂ * A * P₁ = 0 ∧ P₃ * A * P₁ = 0 ∧ P₃ * A * P₂ = 0 := fun A h₁ h₂ =>
    ⟨eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₂ _ (h₁ _ (r₁ y)),
     eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₃ _ (hle₁ (h₁ _ (r₁ y))),
     eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₃ _ (h₂ _ (hle₂ (r₂ y)))⟩
  obtain ⟨a21, a31, a32⟩ := tri q.val (fun y hy => mulVec_mem_of_img q hq₁ hy)
    (fun y hy => mulVec_mem_of_img q hq₂ hy)
  obtain ⟨b21, b31, b32⟩ := tri (q⁻¹ : GL (Fin n) ℂ).val (fun y hy => inv_mulVec_mem_of_img q hq₁ hy)
    (fun y hy => inv_mulVec_mem_of_img q hq₂ hy)
  let L : Mx → Mx := lev P₁ P₂ P₃
  have Lv : ∀ A y, L A *ᵥ y = P₁ *ᵥ (A *ᵥ (P₁ *ᵥ y)) + P₂ *ᵥ (A *ᵥ (P₂ *ᵥ y)) + P₃ *ᵥ (A *ᵥ (P₃ *ᵥ y)) := fun A y => by
    simp only [L, lev, Matrix.add_mulVec, mv]
  have L1 : ∀ A, ∀ y ∈ W₁, L A *ᵥ y ∈ W₁ := fun A y hy => by
    rw [Lv, k₂ y hy, k₃ y (hle₁ hy)]
    simp only [Matrix.mulVec_zero, add_zero]
    exact r₁ _
  have L2 : ∀ A, ∀ y ∈ W₂, L A *ᵥ y ∈ W₂ := fun A y hy => by
    rw [Lv, k₃ y hy]
    simp only [Matrix.mulVec_zero, add_zero]
    exact W₂.add_mem (hle₁ (r₁ _)) (hle₂ (r₂ _))
  have LV2 : ∀ A, ∀ y ∈ V₂, L A *ᵥ y ∈ V₂ := fun A y hy => by
    rw [Lv, k₁₂ y hy, k₃ y (hle₂ hy)]
    simp only [Matrix.mulVec_zero, add_zero, zero_add]
    exact r₂ _
  have LV3 : ∀ A, ∀ y ∈ V₃, L A *ᵥ y ∈ V₃ := fun A y hy => by
    rw [Lv, k₁₃ y hy, k₂₃ y hy]
    simp only [Matrix.mulVec_zero, zero_add]
    exact r₃ _
  have hmm' : L q.val * L (q⁻¹ : GL (Fin n) ℂ).val = 1 :=
    lev_mul hs o12 o13 o21 o23 o31 o32 (Units.mul_inv q) a21 a31 a32 b21 b32 b31
  have hm'm : L (q⁻¹ : GL (Fin n) ℂ).val * L q.val = 1 :=
    lev_mul hs o12 o13 o21 o23 o31 o32 (Units.inv_mul q) b21 b31 b32 a21 a32 a31
  let m : GL (Fin n) ℂ := ⟨L q.val, L (q⁻¹ : GL (Fin n) ℂ).val, hmm', hm'm⟩
  have hmv : m.val = L q.val := rfl
  have hmi : (m⁻¹ : GL (Fin n) ℂ).val = L (q⁻¹ : GL (Fin n) ℂ).val := rfl
  refine ⟨q * m⁻¹, m, by group, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (q * m⁻¹).val - 1 = (q.val - L q.val) * L (q⁻¹ : GL (Fin n) ℂ).val := by
      rw [Units.val_mul, hmi, sub_mul, hmm']
    have hD : q.val - L q.val = P₁ * q.val * P₂ + P₁ * q.val * P₃ + P₂ * q.val * P₃ :=
      eq_lev_add hs a21 a31 a32
    have Dv : ∀ y, (q.val - L q.val) *ᵥ y = P₁ *ᵥ (q.val *ᵥ (P₂ *ᵥ y)) + P₁ *ᵥ (q.val *ᵥ (P₃ *ᵥ y)) +
        P₂ *ᵥ (q.val *ᵥ (P₃ *ᵥ y)) := fun y => by
      rw [hD]; simp only [Matrix.add_mulVec, mv]
    rw [e]
    refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
    · rw [mv, Dv]
      exact W₂.add_mem (W₂.add_mem (hle₁ (r₁ _)) (hle₁ (r₁ _))) (hle₂ (r₂ _))
    · rw [mv, Dv, k₃ _ (L2 _ y hy)]
      simp only [Matrix.mulVec_zero, add_zero]
      exact r₁ _
    · rw [mv, Dv, k₃ _ (hle₁ (L1 _ y hy)), k₂ _ (L1 _ y hy)]
      simp
  · exact img_eq_of_mapsTo m W₁ (L1 _) (L1 _)
  · exact img_eq_of_mapsTo m W₂ (L2 _) (L2 _)
  · exact img_eq_of_mapsTo m V₂ (LV2 _) (LV2 _)
  · exact img_eq_of_mapsTo m V₃ (LV3 _) (LV3 _)

theorem levi_inf {W₁ W₂ V₂ V₃ : Sb} (c₁ : W₁ ⊔ V₂ = W₂) (d₁ : W₁ ⊓ V₂ = ⊥) (c₂ : W₂ ⊔ V₃ = ⊤)
    (d₂ : W₂ ⊓ V₃ = ⊥) (g : GL (Fin n) ℂ) (hX : g.val - 1 ∈ nilrad W₁ W₂) (h₂ : img g V₂ = V₂)
    (h₃ : img g V₃ = V₃) : g = 1 := by
  have hle₂ : V₂ ≤ W₂ := c₁ ▸ le_sup_right
  have e : ∀ y, (g.val - 1) *ᵥ y = g.val *ᵥ y - y := fun y => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hz : g.val - 1 = 0 := eq_zero_of_mulVec fun y => by
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_sum_along_flag c₁ c₂ y
    have f1 : (g.val - 1) *ᵥ a = 0 := hX.2.2 a ha
    have f2 : (g.val - 1) *ᵥ b = 0 := by
      have m1 : (g.val - 1) *ᵥ b ∈ W₁ ⊓ V₂ := ⟨hX.2.1 b (hle₂ hb), by
        rw [e]; exact V₂.sub_mem (mulVec_mem_of_img g h₂ hb) hb⟩
      rw [d₁] at m1
      simpa using m1
    have f3 : (g.val - 1) *ᵥ c = 0 := by
      have m1 : (g.val - 1) *ᵥ c ∈ W₂ ⊓ V₃ := ⟨hX.1 c, by
        rw [e]; exact V₃.sub_mem (mulVec_mem_of_img g h₃ hc) hc⟩
      rw [d₂] at m1
      simpa using m1
    rw [Matrix.mulVec_add, Matrix.mulVec_add, f1, f2, f3]
    simp
  exact Units.ext (by simpa [sub_eq_zero] using hz)

end Decomp

end GlobalTheory.CompanionTheory.QuotVan
end
end
