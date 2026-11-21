import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.ColumnAdditionFixesTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.IsTopRingTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.RightKDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IsClosedCongruenceSubgroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.HermitianFormStandardFrameVanishes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.TransitiveOverLocalRings
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.MemSecondProjectionIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SaturatedSplitLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SatSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.UnitaryLocalMassIdentity
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.MeasurableConjugateCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.NonDeg

section
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct

def OmHyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E))
    (T T' : F) (κ : HA (Fv F v) σ J) (μG : Measure (HA (Fv F v) σ J))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (μS0' : Measure (S0 (Fv F v) σ J P')) : Prop :=
  StdHyp σ J ψ ∧ P.IsStd σ J T ∧ P'.IsStd σ J T' ∧ IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧
    g.Prime ∧ (g : 𝓞 F) ∈ v.asIdeal ∧ Ideal.absNorm v.asIdeal = g ∧ etaV (E := E) v = 1 ∧
    κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ∧
    (∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (κ • ratTup (Fv F v) (F0 P')) a - locF v (ratTup (Fv F v) (F0 P)) a =
        sc (E := E) v (g : Fv F v) • y) ∧
    μG.IsHaarMeasure ∧
    μS0.IsHaarMeasure ∧ IsCompatLoc σ J v (F0 P) μG μS0 (omAt σ J ψ v (TFl σ J v P)) ∧
    μS0'.IsHaarMeasure ∧ IsCompatLoc σ J v (F0 P') μG μS0' (omAt σ J ψ v (TFl σ J v P')) ∧
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) ∧ IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P'))) ∧
    LocMassOrdW.IsLatLoc v Λ ∧ (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 ∧ (μS0' (stabilizerCompact σ J v Λ P')).toReal ≠ 0

def OmMeas : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E))
    (T T' : F) (κ : HA (Fv F v) σ J) (μG : Measure (HA (Fv F v) σ J))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (μS0' : Measure (S0 (Fv F v) σ J P')),
    OmHyp σ J ψ v g P P' Λ T T' κ μG μS0 μS0' →
    MeasurableSet (OmTyp v Λ g r) ∧ MeasurableSet (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ∧
      MeasurableSet (K1 σ J v Λ g P) ∧
      MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) (F0 P)) ''
        Formalism.L2.SG.TypedSets.Kv σ J Λ v) ∧
      ∀ k : HA (Fv F v) σ J, MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) (F0 P')) ''
        {c | k⁻¹ * c * κ⁻¹ ∈ K1 σ J v Λ g P})

theorem weil_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) {a : ℕ}
    (X0 : Fin a → Fin n → E) (μG : Measure (HA (Fv F v) σ J))
    (μ' : Measure (stabT (Fv F v) σ J X0)) (ν : Measure (TupV (E := E) v n a))
    (hc : IsCompatLoc σ J v X0 μG μ' ν) (C : Set (HA (Fv F v) σ J)) (hCm : MeasurableSet C)
    (D : Set (stabT (Fv F v) σ J X0)) (hDm : MeasurableSet D)
    (hCD : ∀ c ∈ C, ∀ h : stabT (Fv F v) σ J X0, c * (h : HA (Fv F v) σ J) ∈ C ↔ h ∈ D)
    (hAm : MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) X0) '' C)) :
    ν ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) X0) '' C) * μ' D = μG C := by
  classical
  set X0r := ratTup (F := F) (Fv F v) X0 with hX0r
  set A := (fun c : HA (Fv F v) σ J => c • X0r) '' C with hAdef
  let s : TupV (E := E) v n a → HA (Fv F v) σ J := fun Y =>
    if hY : Y ∈ A then hY.choose else if h' : ∃ g : HA (Fv F v) σ J, g • X0r = Y then h'.choose else 1
  have hs : ∀ Y, (∃ g : HA (Fv F v) σ J, g • X0r = Y) → s Y • X0r = Y := by
    intro Y hY
    by_cases hA : Y ∈ A
    · simp only [s, dif_pos hA]; exact hA.choose_spec.2
    · simp only [s, dif_neg hA, dif_pos hY]; exact hY.choose_spec
  have hf : Measurable (C.indicator (1 : HA (Fv F v) σ J → ENNReal)) := measurable_one.indicator hCm
  have key := hc.2 _ hf s hs
  have hL : ∫⁻ g, C.indicator (1 : HA (Fv F v) σ J → ENNReal) g ∂μG = μG C := lintegral_indicator_one hCm
  have hpt : ∀ Y, (∃ g : HA (Fv F v) σ J, g • X0r = Y) →
      ∫⁻ h', C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) ∂μ' =
        A.indicator (fun _ => μ' D) Y := by
    intro Y hY
    by_cases hA : Y ∈ A
    · rw [Set.indicator_of_mem hA]
      have hk : hA.choose ∈ C := hA.choose_spec.1
      have hsY : s Y = hA.choose := by simp only [s, dif_pos hA]
      rw [← lintegral_indicator_one hDm]
      congr 1
      funext h'
      rw [hsY]
      by_cases hh : h' ∈ D
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hCD _ hk h').2 hh)]; rfl
      · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (fun hm => hh ((hCD _ hk h').1 hm))]
    · rw [Set.indicator_of_notMem hA]
      have hz : ∀ h' : stabT (Fv F v) σ J X0,
          C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) = 0 := by
        intro h'
        rw [Set.indicator_of_notMem]
        intro hmem
        apply hA
        refine ⟨s Y * (h' : HA (Fv F v) σ J), hmem, ?_⟩
        have hst : (h' : HA (Fv F v) σ J) • X0r = X0r := h'.2
        show (s Y * (h' : HA (Fv F v) σ J)) • X0r = Y
        rw [mul_smul, hst, hs Y hY]
      simp [hz]
  have hae : ∀ᵐ Y ∂ν, ∃ g : HA (Fv F v) σ J, g • X0r = Y := ae_iff.mpr hc.1
  have hR' : ∫⁻ Y, ∫⁻ h', C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) ∂μ' ∂ν =
      ∫⁻ Y, A.indicator (fun _ => μ' D) Y ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hae] with Y hY
    exact hpt Y hY
  rw [hL, hR', lintegral_indicator_const hAm] at key
  rw [key, mul_comm]

theorem stepOm_ofK (hW : StepW) (hM : OmMeas) (hRK : RightK) (hO : LocMassOrdW.OmSF) :
    StepOm := by
  intro F E _ _ _ _ _ σ n J ψ v r g P P' Λ T T' κ μG μS0 μS0' hStd hP hP' hSD hUn hg hgv hN hEta hκ
    hκc hμG hμS0 hC hμS0' hC' hPr hPr' hL ha ha'
  have hH : OmHyp σ J ψ v g P P' Λ T T' κ μG μS0 μS0' :=
    ⟨hStd, hP, hP', hSD, hUn, hg, hgv, hN, hEta, hκ, hκc, hμG, hμS0, hC, hμS0', hC', hPr, hPr', hL, ha, ha'⟩
  obtain ⟨hOmm, hKm, hK1m, hAm, hBm⟩ := hM σ J ψ v g P P' Λ T T' κ μG μS0 μS0' hH
  have := hO σ J ψ v hStd (TFl σ J v P')
  set K := Formalism.L2.SG.TypedSets.Kv σ J Λ v with hKdef
  set K1s := K1 σ J v Λ g P with hK1def
  set X0r := ratTup (F := F) (Fv F v) (F0 P) with hX0r
  set X0r' := ratTup (F := F) (Fv F v) (F0 P') with hX0r'
  set ν := omAt σ J ψ v (TFl σ J v P) with hν
  set ν' := omAt σ J ψ v (TFl σ J v P') with hν'
  set a := μS0 (stabilizerCompact σ J v Λ P) with hadef
  set a' := μS0' (stabilizerCompact σ J v Λ P') with ha'def
  have hcg : CongL (Λ := Λ) g X0r (κ • X0r') := hκc
  have hS0Km : MeasurableSet (stabilizerCompact σ J v Λ P) := measurable_subtype_coe hKm
  have hS0Km' : MeasurableSet (stabilizerCompact σ J v Λ P') := measurable_subtype_coe hKm

  have hWK : ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * a = μG K := by
    refine weil_gen σ J v (F0 P) μG μS0 ν hC K hKm (stabilizerCompact σ J v Λ P) hS0Km ?_ hAm
    intro c hc h
    show c * (h : HA (Fv F v) σ J) ∈ K ↔ (h : HA (Fv F v) σ J) ∈ K
    constructor
    · intro hm
      have := kv_mul' (kv_inv' hc) hm
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · exact kv_mul' hc

  have hWC : ∀ k : HA (Fv F v) σ J,
      ν' ((fun c : HA (Fv F v) σ J => c • X0r') '' {c | k⁻¹ * c * κ⁻¹ ∈ K1s}) * a' = μG K1s := by
    intro k
    have hCm : MeasurableSet {c : HA (Fv F v) σ J | k⁻¹ * c * κ⁻¹ ∈ K1s} :=
      hK1m.preimage ((measurable_const_mul k⁻¹).mul_const κ⁻¹)
    refine (weil_gen σ J v (F0 P') μG μS0' ν' hC' _ hCm (stabilizerCompact σ J v Λ P') hS0Km' ?_ (hBm k)).trans ?_
    swap
    · show μG ((fun c => k⁻¹ * c) ⁻¹' ((fun c => c * κ⁻¹) ⁻¹' K1s)) = μG K1s
      rw [measure_preimage_mul]
      exact hRK σ J ψ v Λ μG hStd hSD hUn hEta hL hμG κ⁻¹ (kv_inv' hκ) K1s hK1m
    · intro c hc h
      show k⁻¹ * (c * (h : HA (Fv F v) σ J)) * κ⁻¹ ∈ K1s ↔ (h : HA (Fv F v) σ J) ∈ K
      rw [show k⁻¹ * (c * (h : HA (Fv F v) σ J)) * κ⁻¹ =
          (k⁻¹ * c * κ⁻¹) * (κ * (h : HA (Fv F v) σ J) * κ⁻¹) by group, congruence_mul_mem_iff hc]
      exact conj_mem_congruence_iff hκ hcg h.2
  have ha0' : a' ≠ 0 ∧ a' ≠ ⊤ := ⟨fun h => ha' (by rw [h]; rfl), fun h => ha' (by rw [h]; rfl)⟩
  have hWC' : ∀ k : HA (Fv F v) σ J,
      ν' ((fun c : HA (Fv F v) σ J => c • X0r') '' {c | k⁻¹ * c * κ⁻¹ ∈ K1s}) = μG K1s / a' := by
    intro k
    rw [ENNReal.eq_div_iff ha0'.1 ha0'.2, mul_comm]
    exact hWC k

  have hae' : ∀ᵐ Y ∂ν', ∃ g2 : HA (Fv F v) σ J, g2 • X0r' = Y := ae_iff.mpr hC'.1
  have hae : ∀ᵐ Y ∂ν, ∃ g1 : HA (Fv F v) σ J, g1 • X0r = Y := ae_iff.mpr hC.1
  have hslice : ∀ x, (∃ g1 : HA (Fv F v) σ J, g1 • X0r = x) →
      ν' (Prod.mk x ⁻¹' OmTyp v Λ g r) =
        ((fun c : HA (Fv F v) σ J => c • X0r) '' K).indicator (fun _ => μG K1s / a') x := by
    intro x ⟨g1, hg1⟩
    by_cases hx : x ∈ (fun c : HA (Fv F v) σ J => c • X0r) '' K
    · rw [Set.indicator_of_mem hx]
      obtain ⟨k, hk, hkx⟩ := hx
      rw [← hWC' k]
      apply measure_congr
      rw [Filter.eventuallyEq_set]
      filter_upwards [hae'] with x' hx'
      obtain ⟨g2, hg2⟩ := hx'
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨_, hp2, hcong⟩
        rw [← hg2] at hp2
        obtain ⟨k', hk', hk'x⟩ := hW σ J ψ v P' Λ T' hStd hP' hSD hUn hEta hPr' hL g2 hp2
        refine ⟨k', ⟨kv_mul' (kv_mul' (kv_inv' hk) hk') (kv_inv' hκ), ?_⟩, hk'x.trans hg2⟩
        have hc1 : CongL (Λ := Λ) g x x' := hcong
        have h1 := congL_smul (kv_inv' hk) hc1
        rw [← hkx, inv_smul_smul] at h1
        have h2 := congL_smul (kv_mul' (kv_mul' (kv_inv' hk) hk') (kv_inv' hκ)) hcg
        rw [show (k⁻¹ * k' * κ⁻¹) • κ • X0r' = k⁻¹ • x' by
          rw [← mul_smul, show k⁻¹ * k' * κ⁻¹ * κ = k⁻¹ * k' by group, mul_smul, hk'x, hg2]] at h2
        exact congL_trans h1 (congL_symm h2)
      · rintro ⟨c, homogComponent_comm_first_action, rfl⟩
        have hk1 := (mem_congruence_subgroup_iff).1 homogComponent_comm_first_action
        have hcK : c ∈ K := by
          have := kv_mul' (kv_mul' hk hk1.1) hκ
          rwa [show k * (k⁻¹ * c * κ⁻¹) * κ = c by group] at this
        refine ⟨?_, ?_, ?_⟩
        · rw [← hkx, locF_smul]; exact prim_smul hk hPr
        · rw [locF_smul]; exact prim_smul hcK hPr'
        · show CongL (Λ := Λ) g x (c • X0r')
          rw [← hkx, show c = k * ((k⁻¹ * c * κ⁻¹) * κ) by group, mul_smul]
          apply congL_smul hk
          rw [mul_smul]
          exact congL_trans hk1.2 (congL_smul hk1.1 hcg)
    · rw [Set.indicator_of_notMem hx]
      convert measure_empty (μ := ν')
      ext x'
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp1, _, _⟩
      rw [← hg1] at hp1
      obtain ⟨k, hk, hkx⟩ := hW σ J ψ v P Λ T hStd hP hSD hUn hEta hPr hL g1 hp1
      exact hx ⟨k, hk, hkx.trans hg1⟩
  have hprod : (ν.prod ν') (OmTyp v Λ g r) =
      μG K1s / a' * ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) := by
    rw [Measure.prod_apply hOmm, ← lintegral_indicator_const hAm]
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    exact hslice x hx
  unfold Mv
  rw [hprod, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
  congr 1
  calc μG K1s / a' * ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * (a * a')
      = (ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * a) * (μG K1s / a' * a') := by ring
    _ = μG K * μG K1s := by rw [hWK, ENNReal.div_mul_cancel ha0'.1 ha0'.2]

end PI.LocMassTypW
end
end

section
noncomputable section

namespace PI.LocMassTypM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
open PI.LocMassTypW

theorem orbit_measure : OmMeas := by
  intro F E _ _ _ _ _ σ n J ψ v r g P P' Λ T T' κ μG μS0 μS0' hyp
  obtain ⟨-, -, -, hSD, -, hg, hgv, -⟩ := hyp
  have hKv : IsClosed (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdKv.isClosed_Kv σ J v Λ hSD
  have hK1 : IsClosed (K1 σ J v Λ g P) := isClosed_congruence_subgroup σ J v Λ hSD hg P

  have hK1' : ∀ k : HA (Fv F v) σ J, IsClosed {c | k⁻¹ * c * κ⁻¹ ∈ K1 σ J v Λ g P} := fun k =>
    hK1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  exact ⟨measurableSet_omTyp v Λ σ J hSD hg hgv r, LocMassOrdKv.kv_measurableSet σ J v Λ hSD,
    hK1.measurableSet, measurableSet_image_closed σ J v hKv _,
    fun k => measurableSet_image_closed σ J v (hK1' k) _⟩

end PI.LocMassTypM
end
end

section
noncomputable section

namespace PI.LocMassTypL

open Matrix PI.LocMassTypW.WCoreP

theorem wCoreG (O : Type) [CommRing O] [IsLocalRing O] {n m : ℕ} (t : O)
    (ht : t ∈ IsLocalRing.maximalIdeal O) (A0 A B0 B A' B' : Matrix (Fin n) (Fin m) O)
    (L0 M : Matrix (Fin m) (Fin n) O) (hL0 : L0 * A0 = 1) (hM : M * B = 1)
    (hC : A0ᵀ * B0 = Aᵀ * B) (hA : A = A0 + t • A') (hB : B = B0 + t • B') :
    ∃ k K' : Matrix (Fin n) (Fin n) O, IsUnit k ∧ k * A0 = A ∧ kᵀ * B = B0 ∧ k = 1 + t • K' := by
  classical
  set K' : Matrix (Fin n) (Fin n) O := A' * L0 - Mᵀ * B'ᵀ * (1 - A0 * L0) with hK'

  have h1 : (1 - A0 * L0) * A0 = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hL0, Matrix.mul_one, sub_self]

  have hkey : t • (A0ᵀ * B' + A'ᵀ * B) = 0 := by
    have e : Aᵀ * B = A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B) := by
      calc Aᵀ * B = A0ᵀ * B + t • (A'ᵀ * B) := by
            rw [hA, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul]
        _ = A0ᵀ * B0 + t • (A0ᵀ * B') + t • (A'ᵀ * B) := by
            nth_rewrite 1 [hB]; rw [Matrix.mul_add, Matrix.mul_smul]
        _ = A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B) := by rw [smul_add, add_assoc]
    rw [e] at hC
    calc t • (A0ᵀ * B' + A'ᵀ * B) = (A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B)) - A0ᵀ * B0 := by abel
      _ = 0 := by rw [← hC, sub_self]
  have hBM : Bᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]
  have key' : t • (Bᵀ * A') + t • (B'ᵀ * A0) = 0 := by
    have := congrArg Matrix.transpose hkey
    simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_zero, smul_add] at this
    rw [add_comm]; exact this
  have hB0 : B0ᵀ = Bᵀ - t • B'ᵀ := by
    rw [hB, Matrix.transpose_add, Matrix.transpose_smul, add_sub_cancel_right]
  have hk : Bᵀ * (1 + t • K') = B0ᵀ := by
    have e : Bᵀ * (1 + t • K') = Bᵀ - t • B'ᵀ + (t • (Bᵀ * A') + t • (B'ᵀ * A0)) * L0 := by
      simp only [hK', Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_sub,
        ← Matrix.mul_assoc, hBM, Matrix.one_mul, Matrix.add_mul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, key', Matrix.zero_mul, add_zero, hB0]
  refine ⟨1 + t • K', K', ?_, ?_, ?_, rfl⟩
  ·
    rw [Matrix.isUnit_iff_isUnit_det]
    have ht0 : IsLocalRing.residue O t = 0 := (IsLocalRing.residue_eq_zero_iff t).2 ht
    have hmap : (IsLocalRing.residue O).mapMatrix (1 + t • K') = 1 := by
      ext i j
      simp [Matrix.one_apply, apply_ite, ht0]
    have hdet : IsLocalRing.residue O (1 + t • K').det = 1 := by
      rw [RingHom.map_det, hmap, Matrix.det_one]
    by_contra hnu
    have hm : (1 + t • K').det ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [(IsLocalRing.residue_eq_zero_iff _).2 hm] at hdet
    exact zero_ne_one hdet
  · rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hK', Matrix.sub_mul, Matrix.mul_assoc A',
      hL0, Matrix.mul_one, Matrix.mul_assoc (Mᵀ * B'ᵀ), h1, Matrix.mul_zero, sub_zero, hA]
  · rw [← Matrix.transpose_transpose B, ← Matrix.transpose_mul, hk,
      Matrix.transpose_transpose]

end PI.LocMassTypL
end
end

section
noncomputable section

namespace PI.LocMassTypL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
  PI.LocMassTypW
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem natCast_mem_max (v : HeightOneSpectrum (𝓞 F)) {g : ℕ} (hgv : (g : 𝓞 F) ∈ v.asIdeal) :
    (g : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  have hlt := PI.LocMassTypM.v_natCast_lt_one v hgv
  have hw1 : Valued.v (w : Fv F v) ≤ 1 := w.2
  have e : (w : Fv F v) * (g : Fv F v) = 1 := by
    have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) hw
    simpa using this
  have : Valued.v ((w : Fv F v) * (g : Fv F v)) < 1 :=
    lt_of_le_of_lt (by rw [map_mul]; exact mul_le_of_le_one_left' hw1) hlt
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem congruence_lift_of_basis {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
    {r : ℕ} {P : Frame E n r} {Λ : Set (Fin n → E)} (D : SD σ v) (Q : GL (Fin n) (Fv F v ⊗[F] E))
    (hQΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔
      ∃ x : Fin n → Fv F v ⊗[F] E, (∀ i, x i ∈ OEv (E := E) v) ∧
        y = (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
    (hQh : ∀ x y : Fin n → Fv F v ⊗[F] E,
      hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
        ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, sigR (Fv F v) σ (x i) * y i)
    (hSat : SatSplit)
    (hPr : IsPrim v Λ (locF v (ratTup (F := F) (Fv F v) (F0 P)))) {g : ℕ}
    (hgv : (g : 𝓞 F) ∈ v.asIdeal) (k : HA (Fv F v) σ J) (hk : k ∈ K1 σ J v Λ g P) :
    k ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v := by
  classical
  have hkK := hk.1
  set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm
  set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi
  have hQQi : Qm * Qi = 1 := Q.mul_inv
  have hQiQ : Qi * Qm = 1 := Q.inv_mul
  have memΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔ IntV v (Qi *ᵥ y) := by
    intro y
    rw [hQΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [mulVec_mulVec, hQiQ, one_mulVec]
    · intro hy
      exact ⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩
  set X0r := ratTup (F := F) (Fv F v) (F0 P) with hX0r
  set Y0 := locF v X0r with hY0
  have hYdef : locF v (k • X0r) = k • Y0 := locF_smul σ J v k X0r

  have hPrk : IsPrim v Λ (k • Y0) := by
    refine ⟨fun a => kv_lat hkK (hPr.1 a), fun c hc => hPr.2 c ?_⟩
    have e : ∑ a, c a • (k • Y0) a = lin (Fv F v) σ J k (∑ a, c a • Y0 a) := by
      rw [map_sum]; simp only [map_smul, smul_tup]
    rw [e] at hc
    have := kv_lat (kv_inv hkK) hc
    rwa [lin_inv_lin] at this

  have hunit : ∀ x y, hR (Fv F v) σ J ((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) _) *ᵥ x)
      ((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) _) *ᵥ y) = hR (Fv F v) σ J x y := by
    intro x y
    have hmem := (show HR (Fv F v) σ J from k).2
    show Formalism.UG.hform _ _ _ _ = Formalism.UG.hform _ _ _ _
    rw [hform_mulVec]
    congr 1
  have primT : ∀ W : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, IsPrim v Λ W →
      ∀ c : Fin (r + 1) → Fv F v ⊗[F] E, IntV v (∑ a, c a • (Qi *ᵥ W a)) → ∀ a, c a ∈ OEv (E := E) v := by
    intro W hW c hc
    apply hW.2 c
    rw [memΛ]
    have : Qi *ᵥ (∑ a, c a • W a) = ∑ a, c a • (Qi *ᵥ W a) := by
      show Matrix.mulVecLin Qi (∑ a, c a • W a) = _
      rw [map_sum]
      simp only [map_smul, Matrix.mulVecLin_apply]
    rwa [this]
  set Z0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Y0 a with hZ0def
  set Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ (k • Y0) a with hZdef
  have hZ0 : ∀ a, IntV v (Z0 a) := fun a => (memΛ _).1 (hPr.1 a)
  have hZ : ∀ a, IntV v (Z a) := fun a => (memΛ _).1 (hPrk.1 a)
  have pZ0 := primT Y0 hPr
  have pZ := primT (k • Y0) hPrk

  have hcong : ∀ a, ∃ y ∈ latLoc (E := E) v Λ, (k • Y0) a = Y0 a + sc (E := E) v (g : Fv F v) • y := by
    intro a
    obtain ⟨y, hy, hye⟩ := hk.2 a
    refine ⟨y, hy, ?_⟩
    rw [← hYdef, ← hye]; abel
  choose yv hyv hyve using hcong
  set Wv : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ yv a with hWv
  have hW : ∀ a, IntV v (Wv a) := fun a => (memΛ _).1 (hyv a)
  have hZW : ∀ a, Z a = Z0 a + sc (E := E) v (g : Fv F v) • Wv a := by
    intro a
    simp only [hZdef, hZ0def, hWv]
    rw [hyve a, mulVec_add, mulVec_smul]

  let A0 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Z0 a i), ((D.hO _).1 (hZ0 a i)).1⟩
  let B0 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Z0 a i), ((D.hO _).1 (hZ0 a i)).2⟩
  let A1 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Z a i), ((D.hO _).1 (hZ a i)).1⟩
  let B1 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Z a i), ((D.hO _).1 (hZ a i)).2⟩
  let A' : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Wv a i), ((D.hO _).1 (hW a i)).1⟩
  let B' : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Wv a i), ((D.hO _).1 (hW a i)).2⟩
  obtain ⟨L0, hL0⟩ := hSat v n (r + 1) A0 (fun t ht => D.sat₁ Z0 pZ0 t ht)
  obtain ⟨M1, hM1⟩ := hSat v n (r + 1) B1 (fun t ht => D.sat₂ Z pZ t ht)
  have hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b) := by
    intro a b
    have e1 : stdH σ (Z a) (Z b) = hR (Fv F v) σ J ((k • Y0) a) ((k • Y0) b) := by
      rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
    have e2 : stdH σ (Z0 a) (Z0 b) = hR (Fv F v) σ J (Y0 a) (Y0 b) := by
      rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
    rw [e1, e2]
    exact hunit (Y0 a) (Y0 b)
  have hgram : A0ᵀ * B0 = A1ᵀ * B1 := by
    refine Matrix.ext fun a b => Subtype.ext ?_
    have := congrArg D.π₂ (hstd a b)
    rw [D.snd_proj_standard_hermitian_form, D.snd_proj_standard_hermitian_form] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    push_cast
    simp only [dotProduct] at this
    exact this.symm
  have hgc : ((g : v.adicCompletionIntegers F) : Fv F v) = (g : Fv F v) := by push_cast; rfl
  have hA1 : A1 = A0 + (g : v.adicCompletionIntegers F) • A' := by
    refine Matrix.ext fun i a => Subtype.ext ?_
    simp only [A1, A0, A', Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    rw [hZW a, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, (D.hsc _).1]
  have hB1 : B1 = B0 + (g : v.adicCompletionIntegers F) • B' := by
    refine Matrix.ext fun i a => Subtype.ext ?_
    simp only [B1, B0, B', Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    rw [hZW a, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, (D.hsc _).2]
  obtain ⟨k1, K', hk1u, hk1A, hk1B, hk1e⟩ := wCoreG (v.adicCompletionIntegers F)
    (g : v.adicCompletionIntegers F) (natCast_mem_max v hgv) A0 A1 B0 B1 A' B' L0 M1 hL0 hM1
    hgram hA1 hB1
  have hdet : IsUnit k1.det := (Matrix.isUnit_iff_isUnit_det k1).1 hk1u
  have hki : k1 * k1⁻¹ = 1 := Matrix.mul_nonsing_inv k1 hdet
  have hik : k1⁻¹ * k1 = 1 := Matrix.nonsing_inv_mul k1 hdet
  set f := (v.adicCompletionIntegers F).subtype with hf
  have mo : ∀ {M N : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)}, M * N = 1 →
      M.map f * N.map f = 1 := by
    intro M N hMN
    rw [← Matrix.map_mul, hMN, Matrix.map_one f (map_zero f) (map_one f)]
  have e1 : (k1⁻¹)ᵀᵀ * k1 = 1 := by rw [transpose_transpose, hik]
  have e2 : k1ᵀ * (k1⁻¹)ᵀ = 1 := by rw [← transpose_mul, hik, transpose_one]
  have e3 : (k1⁻¹)ᵀ * k1ᵀ = 1 := by rw [← transpose_mul, hki, transpose_one]
  have tm : ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F), (M.map f)ᵀ = Mᵀ.map f :=
    fun M => (Matrix.transpose_map).symm
  set kstd := D.kS (k1.map f) ((k1⁻¹)ᵀ.map f) with hkstd
  set kstd' := D.kS (k1⁻¹.map f) (k1ᵀ.map f) with hkstd'
  have hkk : kstd * kstd' = 1 := by
    rw [hkstd, hkstd', SD.kS_mul, mo hki, mo e3, SD.kS_one]
  have hk'k : kstd' * kstd = 1 := mul_eq_one_comm.mp hkk
  have hkU : ∀ x y, stdH σ (kstd *ᵥ x) (kstd *ᵥ y) = stdH σ x y := by
    intro x y
    refine D.stdH_kS _ _ ?_ ?_ x y
    · rw [tm, mo e1]
    · rw [tm, mo e2]
  have hkI : ∀ x, IntV v (kstd *ᵥ x) ↔ IntV v x := by
    intro x
    constructor
    · intro hx
      have := D.intV_kS (k1⁻¹) k1ᵀ hx
      rwa [← hkstd', mulVec_mulVec, hk'k, one_mulVec] at this
    · intro hx
      exact D.intV_kS k1 (k1⁻¹)ᵀ hx
  have hkZ : ∀ a, kstd *ᵥ Z0 a = Z a := by
    intro a
    apply D.extV
    · intro i
      rw [hkstd, SD.fst_proj_split_matrix_mulVec]
      have := congrArg (fun M => f (M i a)) hk1A
      simp only [Matrix.mul_apply, map_sum, map_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply]
      exact this
    · intro i
      have hB : (k1⁻¹)ᵀ * B0 = B1 := by
        rw [← hk1B, ← Matrix.mul_assoc, e3, Matrix.one_mul]
      rw [hkstd, SD.snd_proj_split_matrix_mulVec]
      have := congrArg (fun M => f (M i a)) hB
      simp only [Matrix.mul_apply, map_sum, map_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply]
      exact this

  set K'' : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := -(k1⁻¹ * K')ᵀ with hK''
  have hk1i : (k1⁻¹)ᵀ = 1 + (g : v.adicCompletionIntegers F) • K'' := by
    have h0 : k1⁻¹ = 1 - (g : v.adicCompletionIntegers F) • (k1⁻¹ * K') := by
      have : k1⁻¹ * k1 = k1⁻¹ + (g : v.adicCompletionIntegers F) • (k1⁻¹ * K') := by
        rw [hk1e, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      rw [hik] at this
      rw [this]; abel
    rw [h0, hK'', Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, smul_neg]
    abel
  set U := D.kS (K'.map f) (K''.map f) with hU
  have hkmod : ∀ x, kstd *ᵥ x - x = sc (E := E) v (g : Fv F v) • (U *ᵥ x) := by
    intro x
    apply D.extV
    · intro i
      rw [Pi.sub_apply, map_sub, hkstd, SD.fst_proj_split_matrix_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, (D.hsc _).1,
        hU, SD.fst_proj_split_matrix_mulVec, hk1e, Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), add_mulVec,
        one_mulVec, Pi.add_apply, add_sub_cancel_left]
      simp only [mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum, hf, Subring.coe_subtype]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_natCast]; ring
    · intro i
      rw [Pi.sub_apply, map_sub, hkstd, SD.snd_proj_split_matrix_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, (D.hsc _).2,
        hU, SD.snd_proj_split_matrix_mulVec, hk1i, Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), add_mulVec,
        one_mulVec, Pi.add_apply, add_sub_cancel_left]
      simp only [mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum, hf, Subring.coe_subtype]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_natCast]; ring

  set kM := Qm * kstd * Qi with hkM
  set kMi := Qm * kstd' * Qi with hkMi
  have hkMM : kM * kMi = 1 := by
    rw [hkM, hkMi]
    calc Qm * kstd * Qi * (Qm * kstd' * Qi) = Qm * (kstd * (Qi * Qm) * kstd') * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQiQ, Matrix.mul_one, hkk, Matrix.mul_one, hQQi]
  have hkMM' : kMi * kM = 1 := mul_eq_one_comm.mp hkMM
  let kG : GL (Fin n) (Fv F v ⊗[F] E) := ⟨kM, kMi, hkMM, hkMM'⟩
  have hkx : ∀ x, kM *ᵥ x = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ x)) := by
    intro x; rw [hkM, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hmem : kG ∈ HR (Fv F v) σ J := by
    show Formalism.UG.cT (sigR (Fv F v) σ) kM * JR (Fv F v) J * kM = JR (Fv F v) J
    apply hform_ext (sigR (Fv F v) σ)
    intro x y
    rw [← hform_mulVec]
    show hR (Fv F v) σ J (kM *ᵥ x) (kM *ᵥ y) = hR (Fv F v) σ J x y
    rw [hkx, hkx, hQh, ← stdH, hkU, stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec,
      one_mulVec]
  let kH : HA (Fv F v) σ J := (⟨kG, hmem⟩ : HR (Fv F v) σ J)
  have hkHK : kH ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
    intro y
    show y ∈ latLoc (E := E) v Λ ↔ kM *ᵥ y ∈ latLoc (E := E) v Λ
    rw [memΛ, memΛ, hkx, mulVec_mulVec, hQiQ, one_mulVec, hkI]
  have hkHX : kH • X0r = k • X0r := by
    apply locF_injective v
    rw [locF_smul σ J v kH X0r, hYdef]
    funext a
    show kM *ᵥ Y0 a = (k • Y0) a
    rw [hkx]
    have := hkZ a
    simp only [hZ0def, hZdef] at this
    rw [this, mulVec_mulVec, hQQi, one_mulVec]
  have hkHg : kH ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v := by
    refine (kgv_iff kH).2 ⟨hkHK, fun w hw => ?_⟩
    refine ⟨Qm *ᵥ (U *ᵥ (Qi *ᵥ w)), ?_, ?_⟩
    · rw [memΛ, mulVec_mulVec, hQiQ, one_mulVec]
      exact D.intV_kS K' K'' ((memΛ w).1 hw)
    · show kM *ᵥ w - w = _
      have e : Qm *ᵥ (kstd *ᵥ (Qi *ᵥ w)) - w = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ w) - Qi *ᵥ w) := by
        rw [mulVec_sub, show Qm *ᵥ (Qi *ᵥ w) = w by rw [mulVec_mulVec, hQQi, one_mulVec]]
      rw [hkx, e, hkmod, mulVec_smul]

  set s := kH⁻¹ * k with hs
  have hsK : s ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := kv_mul (kv_inv hkHK) hkK
  have hsX : s • X0r = X0r := by
    rw [hs, mul_smul, ← hkHX, inv_smul_smul]
  have hsS : s ∈ (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J)) := by
    intro b
    show lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) - ratV (F := F) (Fv F v) (F0 P b) ∈ _
    have := congrFun hsX b
    rw [smul_tup] at this
    rw [show ratV (F := F) (Fv F v) (F0 P b) = X0r b from rfl, this, sub_self]
    exact Submodule.zero_mem _
  exact ⟨hkK, s, s⁻¹ * kH * s, hsS, hsK, kgv_conj hsK hkHg, by rw [hs]; group⟩

end Core

theorem congruence_lift_of_split (hS : SplitR) : CongruenceSubgroupLift := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp k hk
  obtain ⟨hStd, -, hSD, hUn, -, hgv, -, hEta, hPr, hLat, -⟩ := hyp
  obtain ⟨D⟩ := exists_SD hS σ J ψ v hStd hUn hEta
  obtain ⟨Q, hQΛ, hQh⟩ := latStd_SD D hStd.2.1 hSD hLat
  exact congruence_lift_of_basis D Q hQΛ hQh saturated_split_lattice hPr hgv k hk

end PI.LocMassTypL
end
end

section
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

theorem congruence_subgroup_measurable : CongruenceSubgroupMeasurable := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp
  obtain ⟨-, -, hSD, -, hg, -⟩ := hyp
  exact (PI.LocMassTypM.isClosed_congruence_subgroup σ J v Λ hSD hg P).measurableSet

theorem isOpen_uog {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (r g : ℕ) : IsOpen (UOg (E := E) v g r) := by
  rw [PI.LocMassTypU.uog_eq v g r]
  exact PI.LocMassTypU.isOpen_boxS _

theorem unipotent_orbit_measurable : MeasUOg := by
  intro F E _ _ _ _ _ v r g _
  haveI := PI.LocMassTypM.sc_tensV (E := E) v
  haveI := PI.LocMassTypM.borel_tensV (E := E) v
  exact (isOpen_uog (E := E) v r g).measurableSet

theorem unipotent_orbit_count : CountUOg := by
  intro F E _ _ _ _ _ v r g _
  haveI := PI.LocMassTypM.sc_tensV (E := E) v
  haveI : SecondCountableTopology (UIdx r → Fv F v ⊗[F] E) := inferInstance
  have hB : IsOpen (UOgS (E := E) v g r : Set (UIdx r → Fv F v ⊗[F] E)) := isOpen_uog v r g
  rw [← Set.countable_univ_iff]
  have hd : (Set.univ : Set ((UIdx r → Fv F v ⊗[F] E) ⧸ UOgS (E := E) v g r)).PairwiseDisjoint
      (fun q => (QuotientAddGroup.mk : (UIdx r → Fv F v ⊗[F] E) → _ ⧸ UOgS (E := E) v g r) ⁻¹' {q}) :=
    Set.pairwiseDisjoint_fiber _ _
  refine hd.countable_of_isOpen (fun q _ => ?_) (fun q _ => ?_)
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    have e : (QuotientAddGroup.mk : (UIdx r → Fv F v ⊗[F] E) → _ ⧸ UOgS (E := E) v g r) ⁻¹'
        {(QuotientAddGroup.mk x : _ ⧸ UOgS (E := E) v g r)} =
        (fun w => -x + w) ⁻¹' (UOgS (E := E) v g r : Set (UIdx r → Fv F v ⊗[F] E)) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientAddGroup.eq]
    rw [e]
    exact hB.preimage (continuous_const.add continuous_id)
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨x, rfl⟩

theorem index_formula_of_lift (hL : CongruenceSubgroupLift) (hU : KUnip1) : StepIdx :=
  stepIdx_of hL hU congruence_subgroup_measurable unipotent_orbit_measurable unipotent_orbit_count

end PI.LocMassTypW
end
end

section
namespace PI.LocMassTypL

open PI.LocMassTypW

theorem index_formula_of_split (hS : SplitR) (hU : KUnip1) : StepIdx :=
  index_formula_of_lift (congruence_lift_of_split hS) hU

end PI.LocMassTypL
end

section
noncomputable section

namespace PI.LocMassTypL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
  PI.LocMassTypW
open scoped TensorProduct

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n : ℕ}

theorem ratV_add (x y : Fin n → E) : ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i; simp [ratV, map_add]

theorem ratV_zero : ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i; simp [ratV]

theorem ratV_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → E) :
    ratV (F := F) R (∑ i ∈ s, x i) = ∑ i ∈ s, ratV (F := F) R (x i) := by
  funext j; simp [ratV, map_sum, Finset.sum_apply]

theorem ratV_zsmul (m : ℤ) (x : Fin n → E) : ratV (F := F) R (m • x) = m • ratV (F := F) R x := by
  funext i; simp [ratV, map_zsmul]

theorem ratV_smul (a : E) (x : Fin n → E) :
    ratV (F := F) R (a • x) = inclR (F := F) R a • ratV (F := F) R x := by
  funext i; simp [ratV, map_mul]

end Rat

theorem local_lattice_of_global : LatOfGlob := by
  intro F E _ _ _ _ _ v n Λ hL
  obtain ⟨L, hL, hLΛ⟩ := hL
  classical
  obtain ⟨S, hS⟩ := hL.fg
  let b := NumberField.RingOfIntegers.basis E
  set T : Set (Fin n → E) := Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × S =>
    (b p.1 : 𝓞 E) • (p.2 : Fin n → E)) with hT
  have hTfin : T.Finite := Set.finite_range _
  have hTL : T ⊆ (L : Set (Fin n → E)) := by
    rintro _ ⟨⟨j, s⟩, rfl⟩
    exact L.smul_mem _ (hS ▸ Submodule.subset_span (Finset.mem_coe.2 s.2))
  have key : ∀ x ∈ L, ratV (F := F) (Fv F v) x ∈
      Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by
    intro x hx
    rw [← hS] at hx
    obtain ⟨f, -, rfl⟩ := (Submodule.mem_span_finset).1 hx
    rw [ratV_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    rw [← b.sum_repr (f s), Finset.sum_smul, ratV_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_assoc, ratV_zsmul]
    have hmem : ratV (F := F) (Fv F v) ((b j : 𝓞 E) • s) ∈ ratV (F := F) (Fv F v) '' T :=
      ⟨_, ⟨(j, ⟨s, hs⟩), rfl⟩, rfl⟩
    exact zsmul_mem (Submodule.subset_span hmem) _
  have heq : latLoc (E := E) v Λ =
      Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by
    apply le_antisymm
    · rw [latLoc, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [← hLΛ] at hx
      exact key x hx
    · rw [latLoc]
      exact Submodule.span_mono (Set.image_mono (by rw [← hLΛ]; exact hTL))
  refine ⟨?_, ?_⟩
  · rw [heq]; exact Submodule.fg_span (hTfin.image _)
  · have hspan : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)),
        ratV (F := F) (Fv F v) x ∈ Submodule.span (Fv F v ⊗[F] E)
          (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        apply Submodule.subset_span
        show ratV (F := F) (Fv F v) y ∈ latLoc (E := E) v Λ
        exact Submodule.subset_span ⟨y, hLΛ ▸ hy, rfl⟩
      | zero => rw [ratV_zero]; exact Submodule.zero_mem _
      | add y z _ _ h1 h2 => rw [ratV_add]; exact Submodule.add_mem _ h1 h2
      | smul a y _ h => rw [ratV_smul]; exact Submodule.smul_mem _ _ h
    rw [eq_top_iff]
    intro y _
    rw [pi_eq_sum_univ y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have := hspan (fun j => if i = j then (1 : E) else 0) (by rw [hL.span_eq_top]; trivial)
    convert this using 1
    funext j
    by_cases hij : i = j <;> simp [ratV, hij]

end PI.LocMassTypL
end
end

section
noncomputable section

namespace PI.LocMassTypS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct
open PI.LocMassTypW

section Gen

variable {K A : Type} [Field K] [CommRing A] [Algebra K A] {e : A}

theorem idem_mul_compl (he : e * e = e) : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he, sub_self]

theorem compl_idem (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  rw [sub_mul, one_mul, idem_mul_compl he, sub_zero]

theorem linInd (he : e * e = e) (h0 : e ≠ 0) (h1 : e ≠ 1) : LinearIndependent K ![e, 1 - e] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1' : (1 - e) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have hs : s • e = 0 := by
    have := congrArg (· * e) hst
    simp only [add_mul, smul_mul_assoc, he, mul_comm (1 - e) e, idem_mul_compl he, smul_zero,
      add_zero, zero_mul] at this
    exact this
  have ht : t • (1 - e) = 0 := by
    have := congrArg (· * (1 - e)) hst
    simp only [add_mul, smul_mul_assoc, idem_mul_compl he, compl_idem he, smul_zero,
      zero_add, zero_mul] at this
    exact this
  exact ⟨(smul_eq_zero.1 hs).resolve_right h0, (smul_eq_zero.1 ht).resolve_right h1'⟩

variable [FiniteDimensional K A] (h2 : Module.finrank K A = 2) (he : e * e = e) (h0 : e ≠ 0)
  (h1 : e ≠ 1)

def B : Module.Basis (Fin 2) K A :=
  basisOfLinearIndependentOfCardEqFinrank (linInd he h0 h1) (by simp [h2])

theorem B_apply (i : Fin 2) : B h2 he h0 h1 i = ![e, 1 - e] i := by
  simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]

def c1 (x : A) : K := (B h2 he h0 h1).repr x 0

def c2 (x : A) : K := (B h2 he h0 h1).repr x 1

theorem decomp (x : A) : x = c1 h2 he h0 h1 x • e + c2 h2 he h0 h1 x • (1 - e) := by
  have := (B h2 he h0 h1).sum_repr x
  rw [Fin.sum_univ_two, B_apply, B_apply] at this
  simpa [c1, c2] using this.symm

theorem mul_e (x : A) : x * e = c1 h2 he h0 h1 x • e := by
  conv_lhs => rw [decomp h2 he h0 h1 x]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, he, mul_comm (1 - e) e, idem_mul_compl he,
    smul_zero, add_zero]

theorem mul_ce (x : A) : x * (1 - e) = c2 h2 he h0 h1 x • (1 - e) := by
  conv_lhs => rw [decomp h2 he h0 h1 x]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, idem_mul_compl he, compl_idem he, smul_zero,
    zero_add]

include h0 in
theorem uniq1 {c d : K} (h : c • e = d • e) : c = d := smul_left_injective K h0 h

include h1 in
theorem uniq2 {c d : K} (h : c • (1 - e) = d • (1 - e)) : c = d :=
  smul_left_injective K (sub_ne_zero.2 (Ne.symm h1)) h

def p1 : A →+* K where
  toFun := c1 h2 he h0 h1
  map_one' := uniq1 h0 (by rw [← mul_e h2 he h0 h1, one_mul, one_smul])
  map_mul' x y := uniq1 h0 (by
    rw [← mul_e h2 he h0 h1, mul_assoc, mul_e h2 he h0 h1 y, mul_smul_comm, mul_e h2 he h0 h1 x,
      smul_smul, mul_comm])
  map_zero' := uniq1 h0 (by rw [← mul_e h2 he h0 h1, zero_mul, zero_smul])
  map_add' x y := uniq1 h0 (by
    rw [← mul_e h2 he h0 h1, add_mul, mul_e h2 he h0 h1 x, mul_e h2 he h0 h1 y, add_smul])

def p2 : A →+* K where
  toFun := c2 h2 he h0 h1
  map_one' := uniq2 h1 (by rw [← mul_ce h2 he h0 h1, one_mul, one_smul])
  map_mul' x y := uniq2 h1 (by
    rw [← mul_ce h2 he h0 h1, mul_assoc, mul_ce h2 he h0 h1 y, mul_smul_comm, mul_ce h2 he h0 h1 x,
      smul_smul, mul_comm])
  map_zero' := uniq2 h1 (by rw [← mul_ce h2 he h0 h1, zero_mul, zero_smul])
  map_add' x y := uniq2 h1 (by
    rw [← mul_ce h2 he h0 h1, add_mul, mul_ce h2 he h0 h1 x, mul_ce h2 he h0 h1 y, add_smul])

theorem idem_cases {a : K} (h : a * a = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 this with h' | h'
  · exact Or.inl h'
  · exact Or.inr (sub_eq_zero.1 h')

end Gen

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

attribute [local instance] LocMassOrdSF.finDim_FE

theorem finrank_tens (h : Module.finrank F E = 2) :
    Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))]
  simp [h]

theorem finDim_tens : FiniteDimensional (Fv F v) (Fv F v ⊗[F] E) :=
  Module.Finite.of_basis (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))

theorem sigR_sc (c : Fv F v) : sigR (Fv F v) σ (sc (E := E) v c) = sc (E := E) v c := by
  simp [sigR, sc]

theorem sigR_inclR (y : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) y) = inclR (F := F) (Fv F v) (σ y) := by
  simp [sigR, inclR]

theorem sigR_smul (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  rw [← PI.LocMassTypU.sc_mul_eq_smul, map_mul, sigR_sc, PI.LocMassTypU.sc_mul_eq_smul]

theorem sigR_sigR (hσ : ∀ y, σ (σ y) = y) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c y => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem inclR_injective : Function.Injective (inclR (F := F) (Fv F v) : E → Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F (Fv F v)).injective

theorem sigma_invol (hCM : IsCMExt F E σ) (y : E) : σ (σ y) = y := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hCM.2.2.2 τ (σ y), hCM.2.2.2 τ y, star_star]

theorem sigma_ne_id (hCM : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have hR : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hCM.2.2.2 τ x
    rw [hcon x] at this
    exact this.symm
  have hc := hCM.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) ⟨τ, hR, rfl⟩

theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have := PI.LocMassTypU.inclR_mem (E := E) v 1
  simpa using this

theorem oev_mul {a b : Fv F v ⊗[F] E} (ha : a ∈ OEv (E := E) v) (hb : b ∈ OEv (E := E) v) :
    a * b ∈ OEv (E := E) v := by
  change a ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at ha
  change b ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hb
  change a * b ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)
  induction ha using Submodule.span_induction with
  | mem a' ha' =>
    obtain ⟨α, -, rfl⟩ := ha'
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨β, -, rfl⟩ := hb'
      exact Submodule.subset_span ⟨α * β, trivial, by simp [map_mul]⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

def OEvR : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oev_mul v
  one_mem' := oev_one v
  add_mem' := PI.LocMassTypU.oev_add v
  zero_mem' := PI.LocMassTypU.oev_zero v
  neg_mem' := PI.LocMassTypU.oev_neg v

def cm : E ⊗[F] Fv F v ≃ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.comm F E (Fv F v)

theorem oev_iff_tensInt (x : Fv F v ⊗[F] E) :
    x ∈ OEv (E := E) v ↔ (cm v).symm x ∈
      PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
        (v.adicCompletionIntegers F).toSubring := by
  set T := PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
    (v.adicCompletionIntegers F).toSubring with hT
  have hsc : ∀ c ∈ v.adicCompletionIntegers F, (cm v).symm (sc (E := E) v c) ∈ T := by
    intro c hc
    have e : (cm v).symm (sc (E := E) v c) = (1 : E) ⊗ₜ[F] c := by
      simp [cm, sc]
    rw [e]
    exact Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)
  constructor
  · intro hx
    change x ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      have e : (cm v).symm (inclR (F := F) (Fv F v) (a : E)) = (a : E) ⊗ₜ[F] (1 : Fv F v) := by
        simp [cm, inclR]
      rw [e]
      exact Subring.subset_closure (Or.inl ⟨⟨(a : E), ⟨a, rfl⟩⟩, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact T.add_mem hy hz
    | smul c y _ hy =>
      have e : c • y = sc (E := E) v (c : Fv F v) * y := by
        rw [PI.LocMassTypU.sc_mul_eq_smul]
        rfl
      rw [e, map_mul]
      exact T.mul_mem (hsc _ c.2) hy
  · intro hx
    have hle : T ≤ (OEvR v).comap (cm v).toAlgHom.toRingHom := by
      rw [hT]
      unfold PI.SplitIntLoc.tensInt
      rw [Subring.closure_le]
      rintro _ (⟨⟨a, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
      · show (cm v) ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : Fv F v)) ∈ OEv (E := E) v
        have e : (cm v) ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : Fv F v)) =
            inclR (F := F) (Fv F v) (b : E) := by
          simp [cm, inclR]
        rw [e]
        exact PI.LocMassTypU.inclR_mem v b
      · show (cm v) ((1 : E) ⊗ₜ[F] c) ∈ OEv (E := E) v
        have e : (cm v) ((1 : E) ⊗ₜ[F] c) = c • (1 : Fv F v ⊗[F] E) := by
          rw [← PI.LocMassTypU.sc_mul_eq_smul, mul_one]
          simp [cm, sc]
        rw [e]
        exact PI.LocMassTypU.oev_smul v hc (oev_one v)
    have h : x ∈ OEvR v := by simpa using hle hx
    exact h

end Split

end PI.LocMassTypS
end
end

section
noncomputable section

namespace PI.LocMassTypS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct
open PI.LocMassTypW

theorem split_reduction : SplitR := by
  intro F E _ _ _ _ _ σ n J ψ v hStd _ hEta
  have hCM := hStd.1
  have h2 := finrank_tens (E := E) v hCM.2.2.1
  have := finDim_tens (E := E) v
  obtain ⟨e, he, h0, h1⟩ : ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
    unfold etaV at hEta
    split_ifs at hEta with h
    · exact h
    all_goals norm_num at hEta
  set π₁ := p1 h2 he h0 h1 with hπ₁
  set π₂ := p2 h2 he h0 h1 with hπ₂
  have hm1 : ∀ x, x * e = π₁ x • e := mul_e h2 he h0 h1
  have hm2 : ∀ x, x * (1 - e) = π₂ x • (1 - e) := mul_ce h2 he h0 h1
  have hdec : ∀ x, x = π₁ x • e + π₂ x • (1 - e) := decomp h2 he h0 h1
  have hσσ := sigma_invol σ hCM
  set f := sigR (Fv F v) σ e with hf
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hfe : f = 1 - e := by
    have c1 := idem_cases (show π₁ f * π₁ f = π₁ f by rw [← map_mul, hff])
    have c2 := idem_cases (show π₂ f * π₂ f = π₂ f by rw [← map_mul, hff])
    have hfd := hdec f
    rcases c1 with a | a <;> rcases c2 with b | b <;> rw [a, b] at hfd
    · exfalso
      apply h0
      rw [← sigR_sigR σ v hσσ e, ← hf, hfd]
      simp
    · simpa using hfd
    · exfalso
      obtain ⟨y, hy⟩ := sigma_ne_id σ hCM
      have hfe : f = e := by simpa using hfd
      have hid : ∀ x, sigR (Fv F v) σ x = x := by
        intro x
        conv_lhs => rw [hdec x]
        rw [map_add, sigR_smul, sigR_smul, map_sub, map_one, ← hf, hfe]
        exact (hdec x).symm
      apply hy
      apply inclR_injective (E := E) v
      rw [← sigR_inclR, hid]
    · exfalso
      apply h1
      rw [← sigR_sigR σ v hσσ e, ← hf, hfd]
      simp
  have hσe : sigR (Fv F v) σ e = 1 - e := hfe
  have hσ1 : sigR (Fv F v) σ (1 - e) = e := by
    rw [map_sub, map_one, hσe, sub_sub_cancel]
  have hp2σ : ∀ x, π₂ (sigR (Fv F v) σ x) = π₁ x := by
    intro x
    apply uniq2 h1 (K := Fv F v)
    calc π₂ (sigR (Fv F v) σ x) • (1 - e) = sigR (Fv F v) σ x * (1 - e) := (hm2 _).symm
      _ = sigR (Fv F v) σ x * sigR (Fv F v) σ e := by rw [hσe]
      _ = sigR (Fv F v) σ (x * e) := (map_mul _ _ _).symm
      _ = sigR (Fv F v) σ (π₁ x • e) := by rw [hm1]
      _ = π₁ x • sigR (Fv F v) σ e := sigR_smul σ v _ _
      _ = π₁ x • (1 - e) := by rw [hσe]
  have hp1σ : ∀ x, π₁ (sigR (Fv F v) σ x) = π₂ x := by
    intro x
    apply uniq1 h0 (K := Fv F v)
    calc π₁ (sigR (Fv F v) σ x) • e = sigR (Fv F v) σ x * e := (hm1 _).symm
      _ = sigR (Fv F v) σ x * sigR (Fv F v) σ (1 - e) := by rw [hσ1]
      _ = sigR (Fv F v) σ (x * (1 - e)) := (map_mul _ _ _).symm
      _ = sigR (Fv F v) σ (π₂ x • (1 - e)) := by rw [hm2]
      _ = π₂ x • sigR (Fv F v) σ (1 - e) := sigR_smul σ v _ _
      _ = π₂ x • e := by rw [hσ1]
  have hsc : ∀ c : Fv F v, π₁ (sc (E := E) v c) = c ∧ π₂ (sc (E := E) v c) = c := by
    intro c
    refine ⟨uniq1 h0 (K := Fv F v) ?_, uniq2 h1 (K := Fv F v) ?_⟩
    · rw [← hm1, PI.LocMassTypU.sc_mul_eq_smul]
    · rw [← hm2, PI.LocMassTypU.sc_mul_eq_smul]
  have he1 : π₁ e = 1 := uniq1 h0 (K := Fv F v) (by rw [← hm1, he, one_smul])
  have he2 : π₂ e = 0 := uniq2 h1 (K := Fv F v) (by rw [← hm2, idem_mul_compl he, zero_smul])
  have hce1 : π₁ (1 - e) = 0 := by rw [map_sub, map_one, he1, sub_self]
  have hce2 : π₂ (1 - e) = 1 := by rw [map_sub, map_one, he2, sub_zero]

  let φ : (Fv F v ⊗[F] E) →+* Fv F v × Fv F v := RingHom.prod π₁ π₂
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1' : π₁ x = π₁ y := congrArg Prod.fst hxy
      have h2' : π₂ x = π₂ y := congrArg Prod.snd hxy
      rw [hdec x, hdec y, h1', h2']
    · rintro ⟨a, b⟩
      refine ⟨sc (E := E) v a * e + sc (E := E) v b * (1 - e), ?_⟩
      show (π₁ _, π₂ _) = (a, b)
      rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul, (hsc a).1, (hsc b).1, (hsc a).2,
        (hsc b).2, he1, he2, hce1, hce2]
      simp
  let spl : E ⊗[F] Fv F v ≃+* Fv F v × Fv F v :=
    (cm (E := E) v).toRingEquiv.trans (RingEquiv.ofBijective φ hbij)
  have hspl_apply : ∀ y, spl y = (π₁ (cm (E := E) v y), π₂ (cm (E := E) v y)) := fun _ => rfl
  have hspl : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a
    rw [hspl_apply]
    have e1 : cm (E := E) v ((1 : E) ⊗ₜ[F] a) = sc (E := E) v a := by
      simp [cm, sc]
    rw [e1, (hsc a).1, (hsc a).2]
  have hOE : ∀ x, x ∈ OEv (E := E) v ↔
      π₁ x ∈ v.adicCompletionIntegers F ∧ π₂ x ∈ v.adicCompletionIntegers F := by
    intro x
    rw [oev_iff_tensInt, split_integral_local F E v spl hspl, hspl_apply]
    simp
  refine ⟨e, π₁, π₂, he, hσe, fun x => ?_, fun x => ?_, he1, he2, hsc, hp2σ, hp1σ, hOE⟩
  · rw [PI.LocMassTypU.sc_mul_eq_smul]
    exact hm1 x
  · rw [PI.LocMassTypU.sc_mul_eq_smul]
    exact hm2 x

end PI.LocMassTypS
end
end

section
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct

def StepCT : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E)) (T : F)
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)),
    LocMassOrdW.FrameHyp σ J ψ v P Λ μG μS μS0 1 → P.IsStd σ J T → etaV (E := E) v = 1 →
    LocMassOrdW.IsLatLoc v Λ → g.Prime → (g : 𝓞 F) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g →
    (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 →
    μS (KSv σ J v P Λ) = μS0 (stabilizerCompact σ J v Λ P) * sdE (E := E) ψ v (UIdx r) (UO v r)

theorem stepCT_of (hKU : KUnip1) : StepCT := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μG μS μS0 Fr hP hEta hL hg hgv hN ha
  have hPr : IsPrim v Λ (locF v (ratTup (F := F) (Fv F v) (F0 P))) := by
    have := Fr.2.2.2.2.2.2.2.2.2
    rwa [one_smul] at this
  have key := LocMassOrdSC.stepC_at σ J ψ v P Λ μG μS μS0 1 Fr
    (LocMassOrdSC.measConj σ J v Λ Fr.2.2.1 1) (LocMassOrdSC.measurable_unipotent_orbit v r)
    (unipSplitF PI.LocMassTypS.split_reduction (PI.LocMassTypL.latStd_of PI.LocMassTypS.split_reduction)
      σ J ψ v P Λ T Fr.1 hP Fr.2.2.1 Fr.2.2.2.1 hEta hL hPr)
    (fun x hx => by
      obtain ⟨s, hs, hsx⟩ := hKU σ J ψ v g P Λ T μS0
        ⟨Fr.1, hP, Fr.2.2.1, Fr.2.2.2.1, hg, hgv, hN, hEta, hPr, hL, Fr.2.2.2.2.2.2.1, ha⟩ x hx
      exact ⟨s, hsx, by simpa using hs⟩)
  rwa [KSv_eq, stabilizer_compact_eq] at key

theorem local_mass_type_formula (hOm : StepOm) (hC : StepCT) (hIdx : StepIdx) (hG : LatOfGlob)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) :
    Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ := by
  intro hStd T T' hP hP' hSD hUn hGL hg hgv hN hEta hκ μG hμG μS hμS hTie μS' hμS' hTie' hPr hPr'
  have hL := hG v Λ hGL
  obtain ⟨κ, hκK, hκc⟩ := hκ
  obtain ⟨μS0, hμS0, hCm, hPU⟩ := hTie
  obtain ⟨μS0', hμS0', hCm', hPU'⟩ := hTie'
  have Fr : LocMassOrdW.FrameHyp σ J ψ v P Λ μG μS μS0 1 :=
    ⟨hStd, ⟨T, hP⟩, hSD, hUn, hμG, hμS, hμS0, hCm, hPU, by rw [one_smul]; exact hPr⟩
  have Fr' : LocMassOrdW.FrameHyp σ J ψ v P' Λ μG μS' μS0' 1 :=
    ⟨hStd, ⟨T', hP'⟩, hSD, hUn, hμG, hμS', hμS0', hCm', hPU', by rw [one_smul]; exact hPr'⟩
  have ha : (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 := by
    rw [← stabilizer_compact_eq]; exact LocMassOrdND.nondegenerate_lattice σ J ψ v P Λ μG μS μS0 1 Fr hL
  have ha' : (μS0' (stabilizerCompact σ J v Λ P')).toReal ≠ 0 := by
    rw [← stabilizer_compact_eq]; exact LocMassOrdND.nondegenerate_lattice σ J ψ v P' Λ μG μS' μS0' 1 Fr' hL
  have h1 := hC σ J ψ v g P Λ T μG μS μS0 Fr hP hEta hL hg hgv hN ha
  have h2 := hC σ J ψ v g P' Λ T' μG μS' μS0' Fr' hP' hEta hL hg hgv hN ha'
  have h1r := congrArg ENNReal.toReal h1
  have h2r := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_mul] at h1r h2r
  have hu := PI.LocMassTypU.unitary_local_mass_identity σ J ψ v (r := r) g hStd hg hgv
  rw [hu, h1r, h2r]
  have hM := hOm σ J ψ v g P P' Λ T T' κ μG μS0 μS0' hStd hP hP' hSD hUn hg hgv hN hEta hκK hκc
    hμG hμS0 hCm hμS0' hCm' hPr hPr' hL ha ha'
  have hi := hIdx σ J ψ v g P Λ T μG μS0 hStd hP hSD hUn hg hgv hN hEta hPr hμG hL hμS0 ha
  exact arith _ _ _ _ _ _ _ _ _ _ hM rfl rfl hi ha ha' (PI.LocMassTypU.positivity_of_local_mass σ J ψ v g hStd hg hgv)

theorem local_mass_type_of_parts (hRK : RightK) (hKU : KUnip1)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) :
    Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ :=
  local_mass_type_formula
    (stepOm_ofK (stepW_of PI.LocMassTypS.split_reduction (PI.LocMassTypL.latStd_of PI.LocMassTypS.split_reduction)
      saturated_split_lattice transitiveOverLocalRings) PI.LocMassTypM.orbit_measure hRK LocMassOrdSF.orbit_measure_sFinite)
    (stepCT_of hKU) (PI.LocMassTypL.index_formula_of_split PI.LocMassTypS.split_reduction hKU)
    PI.LocMassTypL.local_lattice_of_global σ J ψ v g P P' Λ

end PI.LocMassTypW
end
end
