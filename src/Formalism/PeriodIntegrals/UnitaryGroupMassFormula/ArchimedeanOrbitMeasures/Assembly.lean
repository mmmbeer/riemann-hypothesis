import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AprimeInfOfLeaves
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AinfValueOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTestC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfFibres
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfAction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInvT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UniInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsOrthonormalPerp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamDer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BridgeC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceJacAllHolds

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem exInf_holds : ExInf := by
  intro D X hb FdN FdN' u u' ψ _hX hM _hS
  obtain ⟨⟨_hT1, _νH, hOm, _⟩, _⟩ := hM.1 u'
  obtain ⟨_, h1⟩ := hOm
  refine ⟨h1.1, fun μ hμ => ⟨(h1.2 μ hμ).1, fun ν hν => ?_⟩⟩
  have h2 := (h1.2 μ hμ).2 ν hν
  obtain ⟨μv, hμv⟩ := h2.1
  have h3 := h2.2 μv hμv
  obtain ⟨νv, hνv⟩ := h3.1
  exact ((h3.2 νv hνv).1)

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem weilInf_of (hH : HtotInf) : WeilInf := by
  intro D X hb FdN FdN' u u' hX f hf s hs
  obtain ⟨e1, e2, e3⟩ := hH X hb FdN FdN' u u' hX
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  haveI : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have hL : Measure.IsMulLeftInvariant ((X.measW u').μHinf : Measure (MulAction.stabilizer
      (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u'))))) :=
    (X.measW_norm u').2.1.toIsMulLeftInvariant
  have h0 : (X.measW u').μHinf Set.univ ≠ 0 := by rw [e1]; exact e2.ne'
  have hfin : (X.measW u').μHinf Set.univ ≠ ⊤ := by rw [e1]; exact e3.ne
  exact PI.AprimeInfA.unfold_stab (G := HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')))
    (PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _)
    X.measG.μGinf (X.measW u').μHinf hL h0 hfin f hf s hs

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

theorem pushInf_of_pushLFin_of_orbUniq_of_constTest (hL : PushLFin) (hU : OrbUniq) (hC : ConstTest) : PushInf :=
  pushInf_of invPush_holds invFib_holds (lfPush_of detNZ_holds hL) lfFib_holds hU hC


end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

theorem properOrb_of_compact (hH : MassDataMassesW.HinfCompact) : ProperOrb :=
  properOrb_of_one (properOne_of wittInf_holds hH) invNbhd_holds

theorem pushCont_of_compact (hH : MassDataMassesW.HinfCompact) : PushCont :=
  pushCont_of frame_independent_at_infinity (properOrb_of_compact hH)

theorem pushLFin_of_compact (hH : MassDataMassesW.HinfCompact) : PushLFin :=
  pushLFin_of_proper (properOrb_of_compact hH)

theorem constTest_of_polar_compact (hP : PolarLoc) (hH : MassDataMassesW.HinfCompact) : ConstTest :=
  constTest_of_polar hP (pushCont_of_compact hH)

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

theorem fibOrbAt_of (hU : UnitsOpenTens) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) : FibOrbAt := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hCh
  obtain ⟨Ω₁, hΩ₁, hn, hu⟩ := nearFacts_of hU X u' ψ hT μinf νinf fibInf hP Ω a hCh
  exact ⟨Ω₁, hΩ₁, hn, fun T hT1 => fib_near rmulFacts_holds hF hC X u' ψ hT μinf νinf fibInf hP T (a T)
    (hu T hT1).1 (hCh.2.2.2 T (hΩ₁ hT1)) (hu T hT1).2⟩

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem lfFib_at {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) : LFI X (fibInf T) := by
  intro K hK hKU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, -, hkcl, hKk, hkU⟩ := exists_compact_closed_between hK (isOpen_IndI X) hKU
  obtain ⟨f, hf1, hf0, hfc, -⟩ := exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr hKk)
  have hts : tsupport f ⊆ IndI X := by
    refine (closure_minimal ?_ hkcl).trans hkU
    intro y hy
    by_contra h
    exact hy (hf0 (fun h' => h (interior_subset h')))
  have hI := ((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 T (Set.mem_univ _)
  calc fibInf T K ≤ fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} :=
        measure_mono fun y hy => by
          simp only [Set.mem_ofPred_eq]
          rw [hf1 hy]
          simp
    _ = 1 * fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf T) :=
        mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1
    _ < ⊤ := hI.lintegral_lt_top

theorem fibAllT_holds : FibAllT := by
  intro D X u' ψ hT μinf νinf fibInf hP T
  refine ⟨fun g => ?_, lfFib_at X u' ψ hT μinf νinf fibInf hP T⟩
  have hfib := hP.2.2.2.2.2.2
  have h := fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1
    (fibTrans X μinf νinf fibInf hfib g (sdInvG_of sdTestI_holds X u' ψ hT μinf νinf fibInf hP g)) hfib
  exact congrFun h T

end PI.AprimeInfW
end
end

section
namespace PI.AprimeInfW

theorem unitsOpenTens : UnitsOpenTens := fun X => isOpen_units_tens X

theorem fibOrbAt_of_compact (hC : MassDataMassesW.HinfCompact) : FibOrbAt :=
  fibOrbAt_of unitsOpenTens fibAllT_holds hC

end PI.AprimeInfW
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def JacOneCFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem jacOneCFor_of {Pr : ChartPred} (hK : KPos) (hR : LocRatioFor Pr) : JacOneCFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨V, W, hVW, hsh, hlim⟩ := hR X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  set L : ℕ → ENNReal := fun n => μinf (BoxT X u' a (V n) (W n)) with hL
  set B : ℕ → ENNReal := fun n => νinf (W n) with hB
  set M : ℕ → ENNReal := fun n => X.measG.μGinf (TubeG X u' (V n)) with hM
  set A : ℕ → ENNReal := fun n => ∫⁻ T in W n, c T ∂νinf with hA

  have key : ∀ n, L n = A n * M n := by
    intro n
    obtain ⟨hWm, hWs, -, -, hU, hBm, hBI, -, hTm, -, hMt⟩ := hVW n
    have h := hid ((BoxT X u' a (V n) (W n)).indicator 1) (measurable_one.indicator hBm) (W n)
      hWs hWm
    have hsub : BoxT X u' a (V n) (W n) ⊆
        gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' (W n)) ∩ IndI X := by
      intro y hy
      refine ⟨?_, hBI hy⟩
      obtain ⟨T, hTW, g, -, rfl⟩ := hy
      refine ⟨T, hTW, ?_⟩
      rw [gramR_smul, hC.2.2.2 T (hΩ₂ (hWs hTW))]
    rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm, Set.inter_eq_left.2 hsub] at h
    have hin : ∀ T ∈ W n, ∫⁻ g, (BoxT X u' a (V n) (W n)).indicator 1 (g • rmulT X (a T) (Y0 X u'))
        ∂X.measG.μGinf = M n := by
      intro T hTW
      have hs := pre_box X u' hT hC (V n) (hWs.trans hΩ₂) hU T hTW
      have e : (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
          (BoxT X u' a (V n) (W n)).indicator (1 : TupI X → ENNReal) (g • rmulT X (a T) (Y0 X u'))) =
          (TubeG X u' (V n)).indicator 1 := by
        funext g
        by_cases hg : g ∈ TubeG X u' (V n)
        · have h4 : g • rmulT X (a T) (Y0 X u') ∈ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_mem hg, Set.indicator_of_mem h4]; rfl
        · have h4 : g • rmulT X (a T) (Y0 X u') ∉ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem h4]
      rw [e, lintegral_indicator_one hTm]
    rw [setLIntegral_congr_fun hWm (fun T hT' => by rw [hin T hT'])] at h
    rw [lintegral_mul_const' _ _ hMt.ne] at h
    exact h
  have hAt : ∀ n, A n ≠ ⊤ := by
    intro n hA'
    obtain ⟨-, -, -, -, -, -, -, hLt, -, hM0, -⟩ := hVW n
    have : L n = ⊤ := by rw [key n, hA', ENNReal.top_mul hM0.ne']
    exact absurd this hLt.ne
  have e1 : ∀ n, (L n).toReal / ((B n).toReal * (M n).toReal) = (A n).toReal / (B n).toReal := by
    intro n
    obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt⟩ := hVW n
    have hMr : 0 < (M n).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
    rw [key n, ENNReal.toReal_mul]
    field_simp
  have hlim' : Tendsto (fun n => (L n).toReal / ((B n).toReal * (M n).toReal)) atTop (𝓝 (KVal X u')⁻¹) := hlim

  have hge : ∀ b : ENNReal, b < c (TI X u' hT) → b.toReal ≤ (KVal X u')⁻¹ := by
    intro b hb
    have hU : c ⁻¹' Set.Ioi b ∈ 𝓝 (TI X u' hT) := hcc (Ioi_mem_nhds hb)
    refine ge_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hlow : b * B n ≤ A n :=
      calc b * B n = ∫⁻ _ in W n, b ∂νinf := (setLIntegral_const _ _).symm
        _ ≤ A n := lintegral_mono_ae ((ae_restrict_iff' hWm).2 (Eventually.of_forall fun T hT' =>
            (hn hT').le))
    rw [e1 n, le_div_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (hAt n) hlow

  have hle : ∀ b : ENNReal, c (TI X u' hT) < b → b ≠ ⊤ → (KVal X u')⁻¹ ≤ b.toReal := by
    intro b hb hbt
    have hU : c ⁻¹' Set.Iio b ∈ 𝓝 (TI X u' hT) := hcc (Iio_mem_nhds hb)
    refine le_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hup : A n ≤ b * B n :=
      calc A n ≤ ∫⁻ _ in W n, b ∂νinf := lintegral_mono_ae ((ae_restrict_iff' hWm).2
            (Eventually.of_forall fun T hT' => (hn hT').le))
        _ = b * B n := setLIntegral_const _ _
    rw [e1 n, div_le_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hbt hBt.ne) hup

  have hfin : c (TI X u' hT) ≠ ⊤ := by
    intro htop
    have h1 := hge (ENNReal.ofReal ((KVal X u')⁻¹ + 1)) (by rw [htop]; exact ENNReal.ofReal_lt_top)
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    linarith
  set c₀ : ℝ := (c (TI X u' hT)).toReal with hc₀
  have hle' : c₀ ≤ (KVal X u')⁻¹ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hcε : c₀ - ε ≤ 0
    · have : 0 < (KVal X u')⁻¹ := inv_pos.2 hK0
      linarith
    · push_neg at hcε
      have hb : ENNReal.ofReal (c₀ - ε) < c (TI X u' hT) := by
        rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      have := hge _ hb
      rw [ENNReal.toReal_ofReal hcε.le] at this
      linarith
  have hge' : (KVal X u')⁻¹ ≤ c₀ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hc0 : 0 ≤ c₀ := ENNReal.toReal_nonneg
    have hb : c (TI X u' hT) < ENNReal.ofReal (c₀ + ε) := by
      rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := hle _ hb ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hceq : c₀ = (KVal X u')⁻¹ := le_antisymm hle' hge'
  rw [← ENNReal.ofReal_toReal hfin, ← hc₀, hceq, ENNReal.ofReal_inv_of_pos hK0]

theorem jacOneC_of_charts (hK : KPos) (hU : UnimodInf) (hW : WittNear) (hG : GoodChartEx) : JacOneC := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨Ω', a₂, hC₂, hgood⟩ := hG X u' ψ hT μinf νinf fibInf hP
  have hev : ∀ᶠ T in 𝓝 (TI X u' hT), ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u') := by
    obtain ⟨ι, _, κ, -, η, _, eT, eH, cμ, cν, Ψ', U, -, -, -, -, -, -, -, -, hev0, -⟩ := hgood
    filter_upwards [hev0, hC.1, hC₂.1] with T h1 h2 h3
    exact hW X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T ⟨h2, h3⟩ h1.1
  set Ω₃ := Ω₂ ∩ Ω' ∩ {T | ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')} with hΩ₃
  have hΩ₃n : Ω₃ ∈ 𝓝 (TI X u' hT) := inter_mem (inter_mem hΩ₂n hC₂.1) hev
  have hid₂ : PolId X u' μinf νinf a₂ Ω₃ c := by
    intro φ hφ S hS hSm
    rw [hid φ hφ S (hS.trans (Set.inter_subset_left.trans Set.inter_subset_left)) hSm]
    refine setLIntegral_congr_fun hSm (fun T hT' => ?_)
    obtain ⟨h, eh⟩ := (hS hT').2
    rw [eh]
    congr 1
    have e : ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
        φ (g • h • rmulT X (a₂ T) (Y0 X u')) = (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) (g * h) := by
      intro g; simp only [mul_smul]
    simp_rw [e]
    exact hU X u' ψ hT μinf νinf fibInf hP (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) h
  exact jacOneCFor_of hK (locRatioFor_of hK splitAsym_good) X u' ψ hT μinf νinf fibInf hP Ω' a₂ hC₂ hgood Ω₃
    (Set.inter_subset_left.trans Set.inter_subset_right) hΩ₃n c hcc hid₂

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittNear_holds : WittNear := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTm hU
  obtain ⟨-, hmul, hsm, hgr, hcT, hc1, -, -⟩ := rmulFacts_holds X
  obtain ⟨u, hu⟩ := hU
  set w : TupI X := rmulT X (↑u⁻¹ : MfI X) (rmulT X (a T) (Y0 X u')) with hw
  have hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC.2.2.2 T hTm.1
  have hgT₂ : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a₂ T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC₂.2.2.2 T hTm.2
  have hY0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    gramR_ratTup (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
  have hinv1 : cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X) = 1 := by
    rw [← hcT, Units.mul_inv, hc1]
  have hgw : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J w =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) := by
    rw [hw, hgr, hgT, ← hgT₂, ← hu, hgr, hY0]
    rw [show cTI X (↑u⁻¹ : MfI X) * (cTI X (↑u : MfI X) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) * (↑u : MfI X)) *
        (↑u⁻¹ : MfI X) = (cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X)) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) *
        ((↑u : MfI X) * (↑u⁻¹ : MfI X)) by simp only [Matrix.mul_assoc],
      hinv1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ b : X.B.I.E, X.B.I.cm.sig b = b ↔ b ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun b => X.B.I.cm.fixed b
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hUC : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hUC w hgw
  refine ⟨g, ?_⟩
  have hback : rmulT X (↑u : MfI X) w = rmulT X (a T) (Y0 X u') := by
    rw [hw, hmul, Units.inv_mul, rmulT_one]
  rw [← hback, ← hu, hsm]
  congr 1
  exact hg.symm

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW.MuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

section Tr

variable {D : D7} (X : HidaSetting D)

theorem emb_real (v : InfinitePlace X.B.I.F) (a : X.B.I.F) : conj (v.embedding a) = v.embedding a := by
  have hv : v.IsReal := totReal_of X v
  have h := NumberField.ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hv)
  have := RingHom.congr_fun h a
  simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this

theorem phi_star (v : InfinitePlace X.B.I.F) (e : X.B.I.E) : X.B.I.φ v (star e) = conj (X.B.I.φ v e) :=
  X.B.I.cm.cmUnram.2.1 _ e

theorem phi_notReal (v : InfinitePlace X.B.I.F) : ¬ ∀ e : X.B.I.E, conj (X.B.I.φ v e) = X.B.I.φ v e := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal (X.B.I.φ v) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext e
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq, h e]
  have hc := X.B.I.cm.cmUnram.1.isComplex (InfinitePlace.mk (X.B.I.φ v))
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem emb_trace (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    v.embedding (Algebra.trace X.B.I.F X.B.I.E e) = X.B.I.φ v e + conj (X.B.I.φ v e) := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  let φA : X.B.I.E →ₐ[X.B.I.F] ℂ := { X.B.I.φ v with commutes' := X.B.I.φ_over v }
  let ψA : X.B.I.E →ₐ[X.B.I.F] ℂ :=
    { (starRingEnd ℂ).comp (X.B.I.φ v) with
      commutes' := fun a => by
        show conj (X.B.I.φ v (algebraMap X.B.I.F X.B.I.E a)) = v.embedding a
        rw [X.B.I.φ_over, emb_real] }
  have hne : φA ≠ ψA := by
    intro h
    apply phi_notReal X v
    intro e
    have := congrArg (fun f : X.B.I.E →ₐ[X.B.I.F] ℂ => f e) h
    exact this.symm
  have hcard : Fintype.card (X.B.I.E →ₐ[X.B.I.F] ℂ) = 2 := by
    rw [AlgHom.card X.B.I.F X.B.I.E ℂ, X.B.I.cm.deg2]
  have huniv : (Finset.univ : Finset (X.B.I.E →ₐ[X.B.I.F] ℂ)) = {φA, ψA} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have h := trace_eq_sum_embeddings (K := X.B.I.F) (L := X.B.I.E) ℂ (x := e)
  rw [huniv, Finset.sum_pair hne] at h
  exact h

theorem evInf_conj (v : InfinitePlace X.B.I.F) (a : Ainf X.B.I.F) :
    conj (PI.AprimeInfU.evInf X v a) = PI.AprimeInfU.evInf X v a := by
  have hv : v.IsReal := totReal_of X v
  show conj (InfinitePlace.Completion.extensionEmbedding v (a v)) =
    InfinitePlace.Completion.extensionEmbedding v (a v)
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem evInf_alg (v : InfinitePlace X.B.I.F) (a : X.B.I.F) :
    PI.AprimeInfU.evInf X v (algebraMap X.B.I.F (Ainf X.B.I.F) a) = v.embedding a :=
  evV_algebraMap X.B.I v a

theorem trace_one_tmul (e : X.B.I.E) :
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) =
      algebraMap X.B.I.F (Ainf X.B.I.F) (Algebra.trace X.B.I.F X.B.I.E e) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem evInf_trace (v : InfinitePlace X.B.I.F) (z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.evInf X v (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) z) =
      PI.AprimeInfU.thetaInf X v z + conj (PI.AprimeInfU.thetaInf X v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : a ⊗ₜ[X.B.I.F] e = a • ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, trace_one_tmul, smul_eq_mul, map_mul, evInf_alg, emb_trace, ← h1, thetaInf_tmul, map_mul,
      evInf_conj]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]; ring

theorem theta_sigR (v : InfinitePlace X.B.I.F) (t : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (sigR (Ainf X.B.I.F) X.B.I.cm.sig t) = conj (PI.AprimeInfU.thetaInf X v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : sigR (Ainf X.B.I.F) X.B.I.cm.sig (a ⊗ₜ[X.B.I.F] e) = a ⊗ₜ[X.B.I.F] (star e) := rfl
    rw [h, thetaInf_tmul, thetaInf_tmul, map_mul, evInf_conj, phi_star]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem theta_hR (v : InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (hR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y) =
      ∑ i, ∑ j, conj (PI.AprimeInfU.thetaInf X v (x i)) * X.B.I.φ v (X.B.I.J i j) *
        PI.AprimeInfU.thetaInf X v (y j) := by
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, theta_sigR, JR, Matrix.map_apply, thetaInf_inclR]

end Tr

section Form

theorem form_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ) :
    ∑ i, ∑ j, conj (p i) * M i j * q j = star p ⬝ᵥ (M *ᵥ q) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_P {n : ℕ} (P A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ) :
    ∑ i, ∑ j, conj ((P *ᵥ p) i) * A i j * (P *ᵥ q) j = ∑ i, ∑ j, conj (p i) * (Pᴴ * A * P) i j * q j := by
  rw [form_dot, form_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem form_Jm {n : ℕ} (ε : Fin n → Bool) (p q : Fin n → ℂ) :
    (∑ i, ∑ j, conj (p i) * Formalism.REAL.Jm ε i j * q j).re =
      ∑ i, (if ε i then 1 else -1 : ℝ) * ((p i).re * (q i).re + (p i).im * (q i).im) := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

end Form

section Beta

variable {D : D7} (X : HidaSetting D)

theorem theta_col (v : InfinitePlace X.B.I.F) (Y : TupI X) (b : Fin (D.R.rS + 1 + D.R.rS)) :
    (fun j => PI.AprimeInfU.thetaInf X v (Y b j)) = X.B.I.P v *ᵥ fun i => betaV X v Y i b := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have : (fun i => betaV X v Y i b) = (X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y b j) := by
    funext i
    simp [betaV]
  rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]

theorem re_evInf_BR (v : InfinitePlace X.B.I.F) (Y Z : TupI X) :
    (PI.AprimeInfU.evInf X v (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y Z)).re =
      ∑ b, ∑ i, 2 * ((if X.B.I.ε v i then 1 else -1 : ℝ) *
        ((betaV X v Y i b).re * (betaV X v Z i b).re + (betaV X v Y i b).im * (betaV X v Z i b).im)) := by
  simp only [BR, map_sum, Complex.re_sum, evInf_trace, Complex.add_re, Complex.conj_re]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [theta_hR]
  have e1 := theta_col X v Y b
  have e2 := theta_col X v Z b
  have hY : ∀ i, PI.AprimeInfU.thetaInf X v (Y b i) = (X.B.I.P v *ᵥ fun i => betaV X v Y i b) i :=
    fun i => congrFun e1 i
  have hZ : ∀ i, PI.AprimeInfU.thetaInf X v (Z b i) = (X.B.I.P v *ᵥ fun i => betaV X v Z i b) i :=
    fun i => congrFun e2 i
  simp only [hY, hZ]
  have hJ : ∀ i j, X.B.I.φ v (X.B.I.J i j) = (X.B.I.J.map (X.B.I.φ v)) i j := fun _ _ => rfl
  simp only [hJ]
  rw [form_P, X.B.I.P_spec v, form_Jm, ← two_mul, Finset.mul_sum]

theorem betaI_bridge (x y : EuclideanSpace ℝ (KapI X)) :
    betaI X x y = ∑ v, ∑ b, ∑ i, 2 * ((if X.B.I.ε v i then 1 else -1 : ℝ) *
        ((betaV X v ((tupCoord X).symm x) i b).re * (betaV X v ((tupCoord X).symm y) i b).re +
          (betaV X v ((tupCoord X).symm x) i b).im * (betaV X v ((tupCoord X).symm y) i b).im)) := by
  simp only [betaI]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact re_evInf_BR X v _ _

end Beta

end PI.AprimeInfW.MuB
end
end

section
noncomputable section

namespace PI.AprimeInfW.MuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

open Classical

variable {D : D7} (X : HidaSetting D)

abbrev BrI : Type := InfinitePlace X.B.I.F × Fin X.B.I.n × Fin (D.R.rS + 1 + D.R.rS) × Bool

theorem reimV_apply {V : Type} {n m : ℕ} (M : V → Matrix (Fin n) (Fin m) ℂ) (p : V × Fin n × Fin m × Bool) :
    reimV M p = if p.2.2.2 then (M p.1 p.2.1 p.2.2.1).re else (M p.1 p.2.1 p.2.2.1).im := rfl

theorem reimV_addB {V : Type} {n m : ℕ} (A B : V → Matrix (Fin n) (Fin m) ℂ) :
    reimV (A + B) = reimV A + reimV B := by
  ext p
  by_cases h : p.2.2.2 <;> simp [reimV, h]

def bAdd : EuclideanSpace ℝ (KapI X) →+ EuclideanSpace ℝ (BrI X) :=
  AddMonoidHom.mk' (fun x => reimV (fun v => betaV X v ((tupCoord X).symm x))) fun x y => by
    rw [← reimV_addB]
    congr 1
    funext v
    rw [tupCoord_symm_add, betaV_add]
    rfl

theorem continuous_betaV (v : InfinitePlace X.B.I.F) (i : Fin X.B.I.n) (b : Fin (D.R.rS + 1 + D.R.rS)) :
    Continuous fun Y : TupI X => betaV X v Y i b := by
  simp only [betaV, Matrix.of_apply, Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul
    ((continuous_thetaInf X v).comp ((continuous_apply j).comp (continuous_apply b)))

theorem continuous_bAdd : Continuous (bAdd X) := by
  show Continuous fun x => reimV (fun v => betaV X v ((tupCoord X).symm x))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  rcases p with ⟨v, i, b, s⟩
  cases s
  · exact Complex.continuous_im.comp ((continuous_betaV X v i b).comp (tupCoord X).symm.continuous)
  · exact Complex.continuous_re.comp ((continuous_betaV X v i b).comp (tupCoord X).symm.continuous)

def bL : EuclideanSpace ℝ (KapI X) →L[ℝ] EuclideanSpace ℝ (BrI X) :=
  (bAdd X).toRealLinearMap (continuous_bAdd X)

theorem bL_apply (x : EuclideanSpace ℝ (KapI X)) : bL X x = reimV (fun v => betaV X v ((tupCoord X).symm x)) :=
  rfl

def qD (p : BrI X) : ℝ := 2 * (if X.B.I.ε p.1 p.2.1 then 1 else -1)

theorem betaI_q (x y : EuclideanSpace ℝ (KapI X)) : betaI X x y = ∑ p : BrI X, qD X p * bL X x p * bL X y p := by
  rw [betaI_bridge]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, bL_apply, reimV_apply, qD, if_true, Bool.false_eq_true,
    if_false]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem card_cbi : Fintype.card
    (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [← Module.finrank_eq_card_chooseBasisIndex, Module.finrank_baseChange, X.B.I.cm.deg2]

theorem card_BrI : Fintype.card (BrI X) = Fintype.card (KapI X) := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, card_cbi]
  ring

def eI : BrI X ≃ KapI X := Fintype.equivOfCardEq (card_BrI X)

def U : EuclideanSpace ℝ (BrI X) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (KapI X) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (eI X)

def fK : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  (U X).toLinearEquiv.toLinearMap ∘ₗ (bL X).toLinearMap

theorem fK_apply (x : EuclideanSpace ℝ (KapI X)) (k : KapI X) : fK X x k = bL X x ((eI X).symm k) := by
  simp [fK, U, Equiv.piCongrLeft'_apply]

open Classical in

def Bq : Matrix (KapI X) (KapI X) ℝ := fun k l => bL X (EuclideanSpace.single l 1) ((eI X).symm k)

open Classical in
theorem toMatrix_fK : LinearMap.toMatrix (EuclideanSpace.basisFun (KapI X) ℝ).toBasis
    (EuclideanSpace.basisFun (KapI X) ℝ).toBasis (fK X) = Bq X := by
  ext k l
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, fK_apply]
  rfl

theorem det_fK : LinearMap.det (fK X) = (Bq X).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (KapI X) ℝ).toBasis, toMatrix_fK]

open Classical in
theorem matI_eq : matI X = (Bq X)ᵀ * Matrix.diagonal (fun k => qD X ((eI X).symm k)) * Bq X := by
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  show betaI X _ _ = _
  rw [betaI_q, ← (eI X).symm.sum_comp]
  refine Finset.sum_congr rfl fun k' _ => ?_
  simp only [Bq]
  ring

theorem det_matI : (matI X).det = (Bq X).det ^ 2 * ∏ p : BrI X, qD X p := by
  rw [matI_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    (eI X).symm.prod_comp (fun p => qD X p)]
  ring

theorem abs_prod_qD : |∏ p : BrI X, qD X p| =
    ((2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F))) ^ 2 := by
  rw [Finset.abs_prod]
  have h : ∀ p : BrI X, |qD X p| = 2 := by
    intro p
    unfold qD
    split_ifs <;> norm_num
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul]
  congr 1
  ring

theorem sqrt_matI (hd : (matI X).det ≠ 0) :
    (Bq X).det ≠ 0 ∧ Real.sqrt |(matI X).det| =
      |(Bq X).det| * 2 ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F)) := by
  have hdm := det_matI X
  refine ⟨fun h0 => hd (by rw [hdm, h0]; ring), ?_⟩
  rw [hdm, abs_mul, abs_prod_qD, abs_pow, sq_abs]
  have hnn : 0 ≤ |(Bq X).det| * (2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F)) :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num) _)
  rw [← Real.sqrt_sq hnn, mul_pow, sq_abs]

end PI.AprimeInfW.MuB

namespace PI.AprimeInfW

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets
open Classical

theorem muBridge_holds : MuBridge := by
  intro D X u' ψ hT μinf νinf fibInf hP
  have hd : (matI X).det ≠ 0 := matNDH_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨hB0, hsq⟩ := MuB.sqrt_matI X hd
  have hfd : LinearMap.det (MuB.fK X) ≠ 0 := by rw [MuB.det_fK]; exact hB0
  have hfun : (fun Y => reimV (fun v => betaV X v Y)) = (MuB.U X).symm ∘ (MuB.fK X) ∘ (tupCoord X) := by
    funext Y
    simp [MuB.fK, MuB.bL_apply]
  have hUm : Measurable (MuB.U X).symm := (MuB.U X).symm.continuous.measurable
  have hfKm : Measurable (MuB.fK X) := (LinearMap.continuous_of_finiteDimensional (MuB.fK X)).measurable
  have htm : Measurable (tupCoord X) := (tupCoord X).continuous.measurable
  have e1 : μinf.map ((MuB.U X).symm ∘ (MuB.fK X) ∘ (tupCoord X)) =
      ((μinf.map (tupCoord X)).map (MuB.fK X)).map (MuB.U X).symm := by
    rw [Measure.map_map hUm hfKm, Measure.map_map (hUm.comp hfKm) htm]
    rfl
  rw [hfun, e1, densMu_holds X u' ψ hT μinf νinf fibInf hP, Measure.map_smul,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hfd, Measure.map_smul, Measure.map_smul,
    ((MuB.U X).symm.measurePreserving).map_eq, smul_smul, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hsq,
    MuB.det_fK]
  congr 2
  have ha : |(MuB.Bq X).det| ≠ 0 := abs_ne_zero.2 hB0
  rw [abs_inv]
  field_simp

theorem betaIso_holds : BetaIso := by
  intro D X
  have hinj : Function.Injective (MuB.fK X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hb : MuB.bL X x = 0 := by
      have := congrArg (MuB.U X).symm hx
      simpa [MuB.fK] using this
    have hβ : ∀ v, betaV X v ((tupCoord X).symm x) = betaV X v 0 := by
      intro v
      have h0 : betaV X v 0 = 0 := by
        have := betaV_add X v 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      rw [h0]
      ext i b
      have hre := congrArg (fun z : EuclideanSpace ℝ (MuB.BrI X) => z (v, i, b, true)) hb
      have him := congrArg (fun z : EuclideanSpace ℝ (MuB.BrI X) => z (v, i, b, false)) hb
      simp only [MuB.bL_apply, MuB.reimV_apply, if_true, Bool.false_eq_true, if_false] at hre him
      exact Complex.ext (by simpa using hre) (by simpa using him)
    have h1 := betaV_inj X _ _ hβ
    have h2 : tupCoord X 0 = 0 := by
      have := tupCoord_add X 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [← (tupCoord X).apply_symm_apply x, h1, h2]
  have hsurj : Function.Surjective (MuB.fK X) := LinearMap.injective_iff_surjective.1 hinj
  let eF := LinearEquiv.ofBijective (MuB.fK X) ⟨hinj, hsurj⟩
  refine ⟨(eF.trans (MuB.U X).symm.toLinearEquiv).toContinuousLinearEquiv, fun Y => ?_⟩
  show (MuB.U X).symm (MuB.fK X (tupCoord X Y)) = _
  simp [MuB.fK, MuB.bL_apply]

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem hasFDerivAt_conj_exp {ι : Type} [Fintype ι] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ∃ D : EuclideanSpace ℝ ι →L[ℝ] (Fin n → ℂ),
      HasFDerivAt (fun y => (A * NormedSpace.exp (L y) * B) *ᵥ w) D 0 ∧ ∀ y, D y = (A * L y * B) *ᵥ w := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : EuclideanSpace ℝ ι →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap L
  let h : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun M => (A * M * B) *ᵥ w
      map_add' := fun M N => by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun r M => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, mul_assoc] }
  let hc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap h
  have hexp : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (Lc 0) := by
    rw [map_zero]; exact hasFDerivAt_exp_zero
  have h1 := hc.hasFDerivAt.comp (0 : EuclideanSpace ℝ ι) (hexp.comp (0 : EuclideanSpace ℝ ι) Lc.hasFDerivAt)
  refine ⟨hc.comp ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).comp Lc), h1, fun y => rfl⟩

theorem dKForm_holds : DKForm := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL x v
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let Φ : TupI X →+ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    { toFun := fun Y v b i => PI.AprimeInfU.thetaInf X v (Y b i)
      map_zero' := by funext v b i; exact map_zero _
      map_add' := by intro Y Z; funext v b i; exact map_add _ _ _ }
  have hsa : ∀ z z', (tupCoord X).symm (z + z') = (tupCoord X).symm z + (tupCoord X).symm z' := by
    intro z z'; apply (tupCoord X).injective; rw [tupCoord_add]; simp
  let T0 : EuclideanSpace ℝ (KapI X) →+ TupI X :=
    { toFun := (tupCoord X).symm
      map_zero' := by
        have h := hsa 0 0
        rw [add_zero] at h
        simpa using h
      map_add' := hsa }
  let Ψ0 := Φ.comp T0
  have hc0 : Continuous Ψ0 := by
    refine continuous_pi fun v => continuous_pi fun b => continuous_pi fun i => ?_
    exact (continuous_thetaInf X v).comp ((continuous_apply i).comp ((continuous_apply b).comp
      (tupCoord X).symm.continuous))
  let Ψ := Ψ0.toRealLinearMap hc0
  have hΨ : ∀ z v b i, Ψ z v b i = PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) := fun _ _ _ _ => rfl
  have hinj : Function.Injective Ψ := by
    intro z z' h
    apply (tupCoord X).symm.injective
    funext b i
    have key : ∀ v, PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) =
        PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z' b i) := by
      intro v
      rw [← hΨ, ← hΨ, h]
    exact sub_eq_zero.1 (thetaInf_inj X _ fun v => by rw [map_sub, key v, sub_self])
  have hcbi : Fintype.card (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex,
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Ainf X.B.I.F)
        (Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2)), Fintype.card_fin]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (KapI X)) =
      Module.finrank ℝ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) := by
    simp only [finrank_euclideanSpace, Fintype.card_prod, hcbi, Module.finrank_pi_fintype,
      Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    ring
  let Ψe := LinearMap.linearEquivOfInjective (Ψ : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] _) hinj hdim
  have hΨe : ∀ Z : TupI X, tupCoord X Z = Ψe.symm (Φ Z) := by
    intro Z
    apply Ψe.injective
    rw [LinearEquiv.apply_symm_apply, LinearMap.linearEquivOfInjective_apply]
    show Φ (T0 (tupCoord X Z)) = Φ Z
    simp [T0]
  have hG : ∀ x v b, (fun i => Φ (kap0 X hb c L x • Y0 X u') v b i) =
      ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (L x v) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro x v b
    funext i
    show PI.AprimeInfU.thetaInf X v ((X.toInf hb (c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) • Y0 X u') b i) = _
    rw [theta_act]
    have hu : uMat ((c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) v) =
        uMat (c v) * NormedSpace.exp (L x v) * uMat (c v)⁻¹ := by
      have e := expU_val (X.B.I.ε v) (L x v) (hL.1 x v).1
      simp only [uMat, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at e ⊢
      rw [e]
    rw [hu]
    simp only [Matrix.mul_assoc]

  have hD : ∀ v b, ∃ Dvb : EuclideanSpace ℝ ι →L[ℝ] (Fin X.B.I.n → ℂ),
      HasFDerivAt (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) Dvb 0 ∧
        ∀ y, Dvb y = ((X.B.I.P v * uMat (c v)) * L y v * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro v b
    obtain ⟨Dvb, h1, h2⟩ := hasFDerivAt_conj_exp ((LinearMap.proj v : (InfinitePlace X.B.I.F →
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) (X.B.I.P v * uMat (c v)) (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)
      (fun j => X.B.I.φ v (tupH (frameOf X u') b j))
    refine ⟨Dvb, ?_, fun y => h2 y⟩
    have e : (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) = fun x =>
        ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (((LinearMap.proj v : (InfinitePlace X.B.I.F →
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) x) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext x
      exact hG x v b
    rw [e]
    exact h1
  choose Dv hDv1 hDv2 using hD
  let DD : EuclideanSpace ℝ ι →L[ℝ] (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    ContinuousLinearMap.pi fun v => ContinuousLinearMap.pi fun b => Dv v b
  have hGd : HasFDerivAt (fun x => Φ (kap0 X hb c L x • Y0 X u')) DD 0 :=
    hasFDerivAt_pi.2 fun v => hasFDerivAt_pi.2 fun b => hDv1 v b
  have hK : KapOrb X u' (kap0 X hb c L) = fun x => Ψe.symm (Φ (kap0 X hb c L x • Y0 X u')) := by
    funext x
    exact hΨe _
  have hKd : HasFDerivAt (KapOrb X u' (kap0 X hb c L))
      (Ψe.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp DD) 0 := by
    rw [hK]
    exact Ψe.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp (0 : EuclideanSpace ℝ ι) hGd
  rw [hKd.fderiv]
  have hΦ : Φ ((tupCoord X).symm (Ψe.symm (DD x))) = DD x := by
    have h1 : Ψe (Ψe.symm (DD x)) = DD x := Ψe.apply_symm_apply (DD x)
    rw [LinearMap.linearEquivOfInjective_apply] at h1
    exact h1
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  ext i b
  have e1 : (fun j => PI.AprimeInfU.thetaInf X v ((tupCoord X).symm (Ψe.symm (DD x)) b j)) = DD x v b :=
    funext fun j => congrFun (congrFun (congrFun hΦ v) b) j
  have hY0 : (fun j => PI.AprimeInfU.thetaInf X v (Y0 X u' b j)) = fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    funext j
    rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]
  show ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v ((tupCoord X).symm (Ψe.symm (DD x)) b j)) i =
    (uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b
  rw [e1, show DD x v b = Dv v b x from rfl, hDv2]
  have eR : (uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b =
      ((uMat (c v) * L x v * uMat (c v)⁻¹) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j))) i := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    show ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y0 X u' b j)) k = _
    rw [hY0]
    rfl
  have hM : (X.B.I.P v)⁻¹ * (X.B.I.P v * uMat (c v) * L x v * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) =
      uMat (c v) * L x v * uMat (c v)⁻¹ * (X.B.I.P v)⁻¹ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul, Matrix.mul_assoc (uMat (c v) * L x v)]
  rw [eR, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem rowsZ_holds : RowsZ := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S hc v i0 hi0 b
  classical
  let d : Fin X.B.I.n → ℂ := fun j => if j = i0 then -1 else 1
  have hdd : ∀ j, d j * d j = 1 := by intro j; simp only [d]; split_ifs <;> norm_num
  let Dm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ := Matrix.diagonal d
  have hDD : Dm * Dm = 1 := by
    show Matrix.diagonal d * Matrix.diagonal d = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact hdd j
  let Du : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ := ⟨Dm, Dm, hDD, hDD⟩
  have hDmem : Du ∈ Formalism.REAL.UJ (X.B.I.ε v) := by
    show Dmᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Dm = Formalism.REAL.Jm (X.B.I.ε v)
    simp only [Dm, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp only [d, Pi.star_apply]
    split_ifs <;> simp
  let g : X.B.I.Ginf := Pi.mulSingle v ⟨Du, hDmem⟩
  have hstd : ∀ w, InStd (S w) (g w) := by
    intro w i hi j
    by_cases hw : w = v
    · subst hw
      have hgi : g w = ⟨Du, hDmem⟩ := Pi.mulSingle_eq_same _ _
      rw [hgi]
      show Dm j i = _
      have hne : i ≠ i0 := fun e => hi (e ▸ hi0)
      simp only [Dm, Matrix.diagonal_apply, d]
      by_cases hji : j = i
      · subst hji; simp [hne]
      · simp [hji]
    · have hgi : g w = 1 := Pi.mulSingle_eq_of_ne hw _
      rw [hgi]
      simp [Matrix.one_apply]
  have hmem := (hc.2 g).2 hstd
  have hfix := (stabInfV_holds X u' hb (c * g * c⁻¹)).1 hmem v b
  have hgv : g v = ⟨Du, hDmem⟩ := Pi.mulSingle_eq_same _ _
  have hm : uMat ((c * g * c⁻¹) v) = uMat (c v) * Dm * uMat (c v)⁻¹ := by
    simp only [uMat, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hgv]
    rfl
  have hci : uMat (c v)⁻¹ * uMat (c v) = 1 := by simp [uMat]
  rw [hm] at hfix
  set x := uMat (c v)⁻¹ *ᵥ wV X u' v b with hxdef
  have hx : Dm *ᵥ x = x := by
    have h' := congrArg (fun y => uMat (c v)⁻¹ *ᵥ y) hfix
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hci, Matrix.one_mul] at h'
    rw [hxdef, Matrix.mulVec_mulVec]
    exact h'
  have hx0 : x i0 = 0 := by
    have h1 := congrFun hx i0
    simp only [Dm, Matrix.mulVec_diagonal, d, ↓reduceIte] at h1
    calc x i0 = ((-1) * x i0 - x i0) * (-1 / 2) := by ring
      _ = 0 := by rw [h1, sub_self, zero_mul]
  rw [beta_frame_coordinates]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact hx0

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gramH {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) D.host.E :=
  Matrix.of fun i j => (VS D).hT (wF X u' i) (wF X u' j)

theorem gram_sq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) :
    gramH X u' * gramH X u' =
    Matrix.diagonal (Fin.append (Fin.snoc (fun _ : Fin D.R.rS => (1 : D.host.E))
      ((((D.mem u').A.T : ℕ) : D.host.E) * (((D.mem u').A.T : ℕ) : D.host.E))) (fun _ : Fin D.R.rS => 1)) := by
  have h1 : ∀ b : Fin D.R.rS, Fin.last D.R.rS ≠ b.castSucc := fun b h => (Fin.castSucc_lt_last b).ne' h
  have h1' : ∀ b : Fin D.R.rS, b.castSucc ≠ Fin.last D.R.rS := fun b h => (Fin.castSucc_lt_last b).ne h
  have h2 : ∀ (x : Fin (D.R.rS + 1)) (y : Fin D.R.rS), Fin.castAdd D.R.rS x ≠ Fin.natAdd (D.R.rS + 1) y := by
    intro x y h
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    omega
  have h2' : ∀ (x : Fin (D.R.rS + 1)) (y : Fin D.R.rS), Fin.natAdd (D.R.rS + 1) y ≠ Fin.castAdd D.R.rS x :=
    fun x y h => h2 x y h.symm
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_castSucc]
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i <;> refine Fin.addCases (fun j1 => ?_) (fun j2 => ?_) j
  · refine Fin.lastCases ?_ (fun a => ?_) i1 <;> refine Fin.lastCases ?_ (fun b => ?_) j1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · refine Fin.lastCases ?_ (fun a => ?_) i1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · refine Fin.lastCases ?_ (fun b => ?_) j1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
      hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]

theorem detT_holds : DetT := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  have hGH : gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) = (gramH X u').map X.ιE.symm := by
    ext i j
    rw [gram_eq]
    rfl
  have hdet : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det = X.ιE.symm (gramH X u').det := by
    rw [hGH]
    exact (RingHom.map_det (X.ιE.symm : D.host.E →+* X.B.I.E) _).symm
  have hsq : (gramH X u').det ^ 2 = (((D.mem u').A.T : ℕ) : D.host.E) ^ 2 := by
    have h := congrArg Matrix.det (gram_sq X u')
    rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_add, Fin.prod_univ_castSucc] at h
    simp only [Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const_one,
      one_mul, mul_one] at h
    rw [sq, sq]
    exact h
  have hz : (X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det) ^ 2 =
      ((((D.mem u').A.T : ℕ) : ℂ)) ^ 2 := by
    rw [hdet, ← map_pow, ← map_pow, hsq, map_pow, map_pow, map_natCast, map_natCast]
  have hn : ‖X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det‖ ^ 2 = (Tw u') ^ 2 := by
    rw [← norm_pow, hz, norm_pow, Complex.norm_natCast]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (by unfold Tw; positivity)).1 hn

end PI.AprimeInfW
end
end

section
namespace PI.AprimeInfAsm

open PI.AprimeInfW

theorem aprimeInf_of_good (hC : MassDataMassesW.HinfCompact) (hG : GoodChartEx) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  have hJ : JacOneC := jacOneC_of_charts kPos_holds unimodInf_holds wittNear_holds hG
  aprimeInf_of_leaves exInf_holds
    (pushInf_of_pushLFin_of_orbUniq_of_constTest (pushLFin_of_compact hC) (orbUniq_of_compact hC)
      (constTest_of_polar_compact
        (polar_local_of_fibres kPos_holds gramMeas_holds (fibOrbAt_of_compact hC) (pushCont_of_compact hC) hJ) hC))
    (weilInf_of (htotInf_of (hinfFin_of hC))) hC

theorem aprimeInf_of_std (hC : MassDataMassesW.HinfCompact) (hG : GrpStd) (hT : TupStd) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_good hC (goodChartEx_of_witt linIndW_holds perpPosV wittLin_holds hG hT)

theorem lamDet_of_open (hN : NuBridge) (hP : PlaceJacAll) : LamDet :=
  lamDet_of betaIso_holds muBridge_holds hN dKForm_holds rowsZ_holds detT_holds hP

theorem aprimeInf_of_grp (hC : MassDataMassesW.HinfCompact) (hG : GrpStd) (hN : NuBridge) (hP : PlaceJacAll) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_std hC hG (tupStd_of_sm kapSm_holds (lamDet_of_open hN hP))

end PI.AprimeInfAsm
end
