import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.VolStabFromSWW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExFDStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoClose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.EqZeroOfMemNbhdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.SWeqOm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensFibInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnfoldFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.PullLocSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FinTheta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExOmTOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.NuNeSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.InvInvSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.MeasOrbSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensInfAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.SdUniq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RealCharacter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.SdDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProdG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FiniteOnCompacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RPGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RpAbsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DetAdm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.AdmCpt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensVolDone
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensIdxF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensCnt

section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem volStabFromSW_of (h1 : ExChar) (h2 : ExOmT) (h3 : ExStab) (h4 : ExFDStab)
    (h5 : SWeqOm) (h6 : Unfold) (h7 : PosTest) : PI.VolStabW.VolStabFromSWW := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc hJ' a ha1 ha2 X0 hT hdet
  refine ⟨h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet, fun ψ hψ => ?_⟩
  refine ⟨ha.1, fun μ hμ => ?_⟩
  refine ⟨h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ, fun νX hν => ?_⟩
  refine ⟨h3 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν, fun μ' hμ' => ?_⟩
  obtain ⟨hμ'H, hμ'C⟩ := hμ'
  refine ⟨(ha.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩
  refine ⟨h4 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' hμ'H, fun 𝓕' h𝓕' => ?_⟩
  obtain ⟨φ, hφ0, hadm, hI⟩ := h7 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  have e1 := h5 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν _ hadm
  unfold meanC at e1
  have hθ : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ))
      {X | gramE σ J X = gramE σ J X0} h ∂μ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at e1
    exact hI e1.symm
  obtain ⟨hfin, e2⟩ :=
    h6 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C 𝓕' h𝓕'
      φ hφ0 hadm hθ
  rw [e2, smul_smul] at e1
  have hc1 : (μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal = 1 := by
    have e3 : ((((μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal : ℝ)) : ℂ) * ∫ X, (φ X : ℂ) ∂νX =
        1 * ∫ X, (φ X : ℂ) ∂νX := by
      rw [one_mul, ← Complex.real_smul]
      exact e1
    exact_mod_cast mul_right_cancel₀ hI e3
  have h0 : (μ 𝓕).toReal ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_mul] at hc1
    exact zero_ne_one hc1
  have e4 : (μ 𝓕).toReal = (μ' 𝓕').toReal := (inv_mul_eq_one₀ h0).1 hc1
  exact (ENNReal.toReal_eq_toReal_iff' hfin ((ha.2 μ hμ).2 𝓕 h𝓕).ne).1 e4.symm

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem exChar_holds : ExChar := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha hc a _ha1 ha2 _X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have h0 : 2 * 0 < M := by omega
  have hrd : RapidDecay b (fun _ : Fin 0 → Fin M → Ainf F ⊗[F] E => (1 : ℂ)) :=
    fun N => ⟨1, fun X => by simp [sizeTup]⟩
  have hpf : IsPureFin b (fun _ : Fin 0 → Fin M → Af F ⊗[F] E => (1 : ℂ))
      (fun v (_ : Fin 0 → Fin M → Fv F v ⊗[F] E) => (1 : ℂ)) := by
    refine ⟨fun v => ⟨IsLocallyConstant.const 1, ?_⟩, Filter.Eventually.of_forall fun v => ?_,
      fun X => by simp⟩
    · exact (Set.subsingleton_of_subsingleton).isCompact
    · funext X
      simp [latV, Set.indicator]
  have hS := hc 0 h0 (0 : Matrix (Fin 0) (Fin 0) E) (fun i => Fin.elim0 i) (by simp)
    (Module.finrank F E) b (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    continuous_const hrd hpf (fun _ => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  exact ((hS.2 μ hμ).2 𝓕 h𝓕).1

end PI.VolStabW
end
end

section
namespace PI.VolStabW

theorem discHF_holds : DiscHF :=
  discHF_of_discHA (PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds)

theorem exFDStab_holds : ExFDStab := exFDStab_of scha_holds discHF_holds

end PI.VolStabW
end

section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem integrable_of_isOmT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {ψ : AddChar (AF F) ℂ}
    {a : ℕ} {T : Matrix (Fin a) (Fin a) E} {hT : ∀ i j, σ (T j i) = T i j}
    {νX : Measure (Fin a → Fin M → AF F ⊗[F] E)} (hν : IsOmT F E σ M J ψ T hT νX)
    {Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : IsAdm F E Φ) : Integrable Φ νX := by
  obtain ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpf, hprod⟩ := hΦ
  obtain ⟨μinf, h1⟩ := hν.2.1
  have k1 := hν.2.2 μinf h1
  obtain ⟨νinf, h2⟩ := k1.1
  have k2 := k1.2 νinf h2
  obtain ⟨μv, h3⟩ := k2.1
  have k3 := k2.2 μv h3
  obtain ⟨νv, h4⟩ := k3.1
  have k4 := k3.2 νv h4
  obtain ⟨fibInf, h5⟩ := k4.1
  have k5 := k4.2 fibInf h5
  obtain ⟨fibV, h6⟩ := k5.1
  exact (k5.2 fibV h6 d b Φ Φinf Φf Φv hc hcs hpf hprod).1

theorem posTest_of (hN : TestNear) : PosTest := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ _hψ μ hμ νX hν μ' _hμ' hC
  obtain ⟨φ, hφ0, hadm, U, hUo, hUne, hUpos⟩ := hN F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨φ, hφ0, hadm, fun hI0 => ?_⟩
  have hint : Integrable (fun X => (φ X : ℂ)) νX := integrable_of_isOmT hν hadm
  have hintR : Integrable φ νX := by simpa using hint.re
  have hI : ∫ X, φ X ∂νX = 0 := by
    rw [integral_complex_ofReal] at hI0
    exact_mod_cast hI0
  have hae : φ =ᵐ[νX] 0 := (integral_eq_zero_iff_of_nonneg (fun X => hφ0 X) hintR).1 hI
  obtain ⟨hnull, hform⟩ := hC
  classical
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y) →
      s y • ratTup (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hf : Measurable (U.indicator (1 : HA (AF F) σ J → ENNReal)) :=
    measurable_one.indicator hUo.measurableSet
  have e := hform _ hf s hs
  have hL : ∫⁻ g, U.indicator (1 : HA (AF F) σ J → ENNReal) g ∂μ = μ U :=
    lintegral_indicator_one hUo.measurableSet
  have : μ.IsHaarMeasure := hμ
  have hpos : 0 < μ U := hUo.measure_pos μ hUne
  have hR : ∫⁻ y, ∫⁻ h', U.indicator (1 : HA (AF F) σ J → ENNReal)
      (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae, ae_iff.2 hnull] with y hy0 hyo
    simp only [Pi.zero_apply] at hy0
    have hz : ∀ h' : stabT (AF F) σ J X0,
        U.indicator (1 : HA (AF F) σ J → ENNReal) (s y * (h' : HA (AF F) σ J)) = 0 := by
      intro h'
      refine Set.indicator_apply_eq_zero.2 fun hm => ?_
      exfalso
      have hh : (h' : HA (AF F) σ J) • ratTup (AF F) X0 = ratTup (AF F) X0 := h'.2
      have h0 := hUpos _ hm
      rw [mul_smul, hh, hs y hyo, hy0] at h0
      exact lt_irrefl _ h0
    simp only [hz, lintegral_zero]
  rw [hL, hR] at e
  exact hpos.ne' e

theorem posTest_holds : PosTest := posTest_of testNear_holds

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW.TopoFibInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open scoped TensorProduct

section Abstract

variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X]

theorem isFibreFamily_map (e : V ≃ₜ V) {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν B fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hf : ∀ x, f (e x) = f x) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν B (fun b => (fib b).map e.toMeasurableEquiv) := by
  set em := e.toMeasurableEquiv with hem
  have hU' : em ⁻¹' U = U := hU
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [MeasurableEquiv.map_apply]
    have : em ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι b} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f (e x) = ι b ∧ e x ∈ U) ↔ ¬ (f x = ι b ∧ x ∈ U)
      rw [hf x, hx]
    rw [this]
    exact hfib.1 b
  · have key : ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x, φ (em x) ∂(μ.restrict (em ⁻¹' U)) := by rw [hU']
        _ = ∫⁻ x, φ x ∂((μ.restrict (em ⁻¹' U)).map em) := (lintegral_map_equiv _ _).symm
        _ = ∫⁻ x, φ x ∂((μ.map em).restrict U) := by rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x in U, φ x ∂μ := by rw [hμ]
    rw [← key, hfib.2.1 (fun x => φ (em x)) (hφ.comp em.measurable)]
    refine lintegral_congr fun b => ?_
    exact (lintegral_map_equiv _ _).symm
  · have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e) (hc.comp e.continuous) (hcs.comp_homeomorph e) hts'
    refine ⟨fun b hb => (integrable_map_equiv em φ).2 (h1 b hb), ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂((fib b).map em)) = fun b => ∫ x, (φ ∘ e) x ∂(fib b) :=
      funext fun b => integral_map_equiv _ _
    rw [e2]
    exact h2

end Abstract

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gramR_smul (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (h • X) = gramR R σ J X := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR R J *
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) = JR R J := h.2
  funext x y
  change hR R σ J (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR R σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl

theorem linIndep_mulVec {A : Type} [CommRing A] (G : GL (Fin M) A) (X : Fin a → Fin M → A) :
    LinearIndependent A (fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) ↔ LinearIndependent A X := by
  have inj : ∀ H : GL (Fin M) A, LinearMap.ker (mulVecLin (H : Matrix (Fin M) (Fin M) A)) = ⊥ :=
    fun H => by
      refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
      have := congrArg (fun z => ((H⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) *ᵥ z) hxy
      simpa [mulVecLin_apply, mulVec_mulVec] using this
  constructor
  · intro hl
    have h2 := hl.map' (mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) (inj G⁻¹)
    have e : (⇑(mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) ∘
        fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) = X := by
      funext x
      simp [mulVec_mulVec]
    rw [e] at h2
    exact h2
  · intro hl
    exact hl.map' (mulVecLin (G : Matrix (Fin M) (Fin M) A)) (inj G)

theorem linIndep_smul (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) (h • X) ↔ LinearIndependent (R ⊗[F] E) X :=
  linIndep_mulVec (HA.mat R σ J h) X

end Loc

end PI.VolStabW.TopoFibInv

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def MuInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ h : HA (Ainf F) σ J, μinf.map (fun X => h • X) = μinf

def MuInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ h : HA (Fv F v) σ J, μv.map (fun X => h • X) = μv

theorem fibInvInf_of (hP : FibPin) (hM : MuInvInf) : FibInvInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfi h Φinf
    hcΦ hcs
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Ainf F) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfi
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h)
    (fun x => TopoFibInv.gramR_smul (Ainf F) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Ainf F) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 μinf hμ νinf hν _ _ hfam hfi Φinf
    hcΦ hcs
  rw [integral_map_equiv] at this
  exact this

theorem fibInvV_of (hP : FibPin) (hM : MuInvV) : FibInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfv h Φv hSB
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Fv F v) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfv
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h)
    (fun x => TopoFibInv.gramR_smul (Fv F v) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Fv F v) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2 v μv hμ νv hν _ _ hfam hfv Φv hSB
  rw [integral_map_equiv] at this
  exact this

theorem nuInv_of_steps (hD : DetAdm) (hC : CompG) (hP : FibPin) (hMI : MuInvInf) (hMV : MuInvV) :
    NuInv :=
  nuInv_of_loc gramPres_holds (pullLoc_of hC (fibInvInf_of hP hMI) (fibInvV_of hP hMV)) hD

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW.TopoMuInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem smul_apply (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (x : Fin n) :
    (h • X) x = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ X x := rfl

theorem BR_smul (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) (h • Y) = BR R σ J X Y := by
  simp only [BR, smul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨g, hg⟩ := h
  simp only [HA.mat, HR, hR, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_setOf_eq] at hg ⊢
  simp only [Formalism.UG.UJ, Formalism.UG.hform, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_setOf_eq] at hg ⊢
  congr 1
  conv_rhs => rw [← hg]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Matrix.transpose_apply, Matrix.map_apply]
  ring

theorem BR_smul_left (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) Y = BR R σ J X (h⁻¹ • Y) := by
  rw [← BR_smul R σ J h X (h⁻¹ • Y), smul_inv_smul]

theorem smul_neg' (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    h • (-X) = -(h • X) := by
  funext x
  simp only [smul_apply, Pi.neg_apply, Matrix.mulVec_neg]

def smulAddEquiv (h : HA R σ J) (n : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  map_add' X Y := by
    funext x
    change ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (X x + Y x) = _
    rw [mulVec_add]
    rfl

theorem selfDual_map (ψR : R → ℂ) {n : ℕ} (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : SdW F E σ M J R ψR n μ) (h : HA R σ J) :
    SdW F E σ M J R ψR n (μ.map (fun X => h • X)) := by
  let e := PI.VolStabW.smulHomeo R σ (a := n) J h
  let em := e.toMeasurableEquiv
  have hmap : μ.map (fun X => h • X) = μ.map em := rfl
  have : μ.IsAddHaarMeasure := hμ.1
  refine ⟨?_, fun Φ hc hcs hI z => ?_⟩
  · exact (smulAddEquiv R σ J h n).isAddHaarMeasure_map μ e.continuous e.symm.continuous
  rw [hmap] at hI ⊢
  let Fh : (Fin n → Fin M → R ⊗[F] E) → ℂ := fun w =>
    ∫ x, Φ (h • x) * ψR (BR R σ J x w) ∂μ
  have hin : ∀ y, ∫ x, Φ x * ψR (BR R σ J x y) ∂(μ.map em) = Fh (h⁻¹ • y) := fun y => by
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ (h • x) * ψR (BR R σ J (h • x) y) = Φ (h • x) * ψR (BR R σ J x (h⁻¹ • y))
    rw [BR_smul_left]
  have hI' : Integrable Fh μ := by
    rw [integrable_map_equiv] at hI
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    show ∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em) = Fh y
    rw [hin, inv_smul_smul]
  have key := hμ.2 (fun x => Φ (h • x)) (hc.comp e.continuous) (hcs.comp_homeomorph e) hI'
    (h⁻¹ • z)
  rw [integral_map_equiv]
  have e3 : (fun y => (∫ x, Φ x * ψR (BR R σ J x (em y)) ∂(μ.map em)) *
      ψR (BR R σ J (em y) z)) = fun y => Fh y * ψR (BR R σ J y (h⁻¹ • z)) := by
    funext y
    show (∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em)) * ψR (BR R σ J (h • y) z) = _
    rw [hin, inv_smul_smul, BR_smul_left]
  rw [e3]
  refine key.trans ?_
  show Φ (h • -(h⁻¹ • z)) = Φ (-z)
  rw [smul_neg', smul_inv_smul]

end PI.VolStabW.TopoMuInv

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem muInvInf_of (hU : SdUniq) : MuInvInf := by
  unfold MuInvInf
  unfold SdUniq at hU
  unfold InCtx at hU ⊢
  intro F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 ψ hψ μ hμ h
  exact ((@hU F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) ψ hψ).1 _ _
    (TopoMuInv.selfDual_map (Ainf F) _ _ (psiInf F ψ) μ hμ h) hμ

theorem muInvV_of (hU : SdUniq) : MuInvV := by
  unfold MuInvV
  unfold SdUniq at hU
  unfold InCtx at hU ⊢
  intro F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 ψ hψ v μ hμ h
  exact ((((@hU F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) ψ hψ).2.2 v).1 _ _
    (TopoMuInv.selfDual_map (Fv F v) _ _ (psiV F ψ v) μ hμ h) hμ)

theorem nuInv_of_pin (hD : DetAdm) (hC : CompG) (hP : FibPin) (hU : SdUniq) : NuInv :=
  nuInv_of_steps hD hC hP (muInvInf_of hU) (muInvV_of hU)

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

namespace CompGAux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabW.FiniteThetaCoordinates
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ x) =
      sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_mem_HR (φ : R →ₐ[F] S) {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom g ∈ HR S σ J := by
  set ψ : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hg' : Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := hg
  have hcT : (Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))).map ψ =
      Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, ψ, tmap_sigR]
  have hJ : (JR R J).map ψ = JR S J := by
    ext i j
    simp [JR, Matrix.map_apply, ψ, tmap_inclR]
  show Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) * JR S J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ = JR S J
  rw [← hcT, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

def haMap (φ : R →ₐ[F] S) : HA R σ J →* HA S σ J :=
  MonoidHom.codRestrict
    ((Formalism.UG.bc (n := Fin M) (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom).comp
      (HR R σ J).subtype) (HR S σ J) (fun h => map_mem_HR σ J φ h.2)

theorem mat_haMap_apply (φ : R →ₐ[F] S) (h : HA R σ J) (i j : Fin M) :
    ((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j =
      Algebra.TensorProduct.map φ (AlgHom.id F E)
        (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j) := rfl

theorem map_smul_tup (φ : R →ₐ[F] S) {n : ℕ} (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) ((h • X) x i)) =
      haMap σ J φ h • (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x i)) := by
  funext x i
  show Algebra.TensorProduct.map φ (AlgHom.id F E)
      ((((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X x)) i) =
    (((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec
      (fun j => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x j))) i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, mat_haMap_apply]

theorem tmap_comp {T : Type} [CommRing T] [Algebra F T] (f : R →ₐ[F] S) (g : S →ₐ[F] T)
    (y : R ⊗[F] E) :
    Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (g.comp f) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem crd_mulVec_mem (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (y : Fin M → Fv F v ⊗[F] E)
    (hm : ∀ i j p, crd b (Fv F v) (m i j) p ∈ v.adicCompletionIntegers F)
    (hy : ∀ j q, crd b (Fv F v) (y j) q ∈ v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (i : Fin M) (k : Fin d) : crd b (Fv F v) ((m.mulVec y) i) k ∈ v.adicCompletionIntegers F := by
  rw [crd_mulVec]
  exact sum_mem fun j _ => sum_mem fun p _ => sum_mem fun q _ =>
    mul_mem (mul_mem (hm i j p) (hy j q)) (hc p q k)

theorem smul_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d a : ℕ} (b : Module.Basis (Fin d) F E)
    (h : HA (Fv F v) σ J)
    (hm : ∀ i j p, crd b (Fv F v)
      (((HA.mat (Fv F v) σ J h : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p ∈
        v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (Y : Fin a → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV b v) : h • Y ∈ latV b v := by
  simp only [latV, Set.mem_ofPred_eq] at hY ⊢
  intro x i k
  exact crd_mulVec_mem v b _ (Y x) hm (fun j q => hY x j q) hc i k

theorem eventually_int (g : HA (AF F) σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ i j p, piV F v (crd b (AF F)
      (((HA.mat (AF F) σ J g : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
        v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j p
  exact (eventually_piV_le_one F _).mono fun v hv => (norm_le_one_iff_mem F v _).1 hv

theorem eventually_struct {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ p q k,
      algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro p q k
  refine (eventually_piV_le_one F (algebraMap F (AF F) (b.repr (b p * b q) k))).mono fun v hv => ?_
  rw [AlgHom.commutes] at hv
  exact (norm_le_one_iff_mem F v _).1 hv

theorem compG_gen (a : ℕ) (g : HA (AF F) σ J) :
    ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v := by
  refine ⟨haMap σ J (fstA F) g, fun v => haMap σ J (piV F v) g, ?_, ?_, ?_⟩
  · intro X
    exact map_smul_tup σ J (fstA F) g X
  · intro v X
    have e : ∀ Z : Fin a → Fin M → AF F ⊗[F] E, projV v (projFin Z) =
        fun x i => Algebra.TensorProduct.map (piV F v) (AlgHom.id F E) (Z x i) := by
      intro Z
      funext x i
      exact tmap_comp (sndA F) (evalV F v) (Z x i)
    rw [e, e, map_smul_tup]
  · intro d b
    filter_upwards [eventually_int σ J g b, eventually_int σ J g⁻¹ b, eventually_struct b]
      with v h1 h2 h3
    have hm : ∀ g' : HA (AF F) σ J, (∀ i j p, piV F v (crd b (AF F)
        (((HA.mat (AF F) σ J g' : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
          v.adicCompletionIntegers F) → ∀ i j p, crd b (Fv F v)
        (((HA.mat (Fv F v) σ J (haMap σ J (piV F v) g') : GL (Fin M) _) :
          Matrix (Fin M) (Fin M) _) i j) p ∈ v.adicCompletionIntegers F := by
      intro g' hg' i j p
      rw [mat_haMap_apply, crd_map]
      exact hg' i j p
    intro Y
    constructor
    · intro hY
      have := smul_mem_latV σ J v b (haMap σ J (piV F v) g⁻¹) (hm g⁻¹ h2) h3 _ hY
      rwa [map_inv, inv_smul_smul] at this
    · intro hY
      exact smul_mem_latV σ J v b (haMap σ J (piV F v) g) (hm g h1) h3 Y hY

end Loc

end CompGAux

theorem compG_holds : CompG := by
  intro F E _ _ _ _ _ σ _hCM M J _hJ _ha _hc a _ha1 _ha2 _X0 _hT _hdet g
  exact CompGAux.compG_gen σ J a g

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors

namespace LocalCountingSum

variable (K : Type) [Field K] [NumberField K]

def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

theorem sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  classical
  simp only [cnt, ← Nat.cast_sum]
  congr 1
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp only [sum_cnt, Real.rpow_one]
  have ht := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, Nat.cast_le] at ht
  refine isBigO_of_div_tendsto_nhds
    (f := fun n : ℕ ↦ (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ))
    (g := fun n : ℕ ↦ (n : ℝ)) ?_ _ ht
  filter_upwards [eventually_ne_atTop 0] with n hn h
  exact absurd h (by exact_mod_cast hn)

theorem cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have hL := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := 2) (sum_cnt_bigO K)
    (fun n ↦ by unfold cnt; positivity) zero_le_one (by norm_num)
  refine hL.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold cnt; positivity)]
    norm_num

end LocalCountingSum

theorem qV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem qvSum_holds : QvSum := by
  intro F _ _
  classical
  have hc := LocalCountingSum.cnt_summable F
  refine summable_of_sum_le (c := ∑' n, LocalCountingSum.cnt F n / (n : ℝ) ^ 2)
    (fun v ↦ by simp only [Pi.zero_apply]; positivity) fun S ↦ ?_
  let N : HeightOneSpectrum (𝓞 F) → ℕ := fun v ↦ Ideal.absNorm v.asIdeal
  have e1 : ∑ v ∈ S, (qV v)⁻¹ ^ 2 = ∑ v ∈ S, ((N v : ℝ))⁻¹ ^ 2 :=
    Finset.sum_congr rfl fun v _ ↦ by rw [qV_eq]
  rw [e1, Finset.sum_comp (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 2) N]
  have hcard : ∀ n, ((S.filter fun v ↦ N v = n).card : ℝ) ≤ LocalCountingSum.cnt F n := by
    intro n
    unfold LocalCountingSum.cnt
    have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    have hinj : Function.Injective
        (fun v : (S.filter fun v ↦ N v = n) ↦
          (⟨v.1.asIdeal, (Finset.mem_filter.mp v.2).2⟩ :
            {I : Ideal (𝓞 F) // Ideal.absNorm I = n})) := by
      intro x y h
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      exact congrArg Subtype.val h
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
    exact_mod_cast this
  calc ∑ n ∈ S.image N, (S.filter fun v ↦ N v = n).card • ((n : ℝ))⁻¹ ^ 2
      ≤ ∑ n ∈ S.image N, LocalCountingSum.cnt F n / (n : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun n _ ↦ ?_
        rw [nsmul_eq_mul, div_eq_mul_inv, inv_pow]
        exact mul_le_mul_of_nonneg_right (hcard n) (by positivity)
    _ ≤ ∑' n, LocalCountingSum.cnt F n / (n : ℝ) ^ 2 :=
        hc.sum_le_tsum _ fun n _ ↦ by unfold LocalCountingSum.cnt; positivity

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

namespace SdTestInfW

open MeasureTheory Complex Filter Topology

theorem char_real (f : ℝ → ℂ) (hc : Continuous f) (hadd : ∀ s t, f (s + t) = f s * f t)
    (hn : ∀ s, ‖f s‖ = 1) : ∃ b : ℝ, ∀ s : ℝ, f s = exp (↑(b * s) * I) :=
  _root_.UpperTheory.Reformulated.B.UnitaryCharacterOfReals.char_real f hc hadd hn

theorem freq_unique {u v : ℝ} (h : ∀ s : ℝ, exp (↑(u * s) * I) = exp (↑(v * s) * I)) : u = v := by
  by_contra huv
  have hne : u - v ≠ 0 := sub_ne_zero.2 huv
  have h1 := h (Real.pi / (u - v))
  have h2 : exp (↑((u - v) * (Real.pi / (u - v))) * I) = 1 := by
    have : (↑((u - v) * (Real.pi / (u - v))) : ℂ) * I =
        ↑(u * (Real.pi / (u - v))) * I - ↑(v * (Real.pi / (u - v))) * I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  rw [mul_div_cancel₀ _ hne, Complex.exp_pi_mul_I] at h2
  norm_num at h2

section Bichar

open scoped RealInnerProductSpace

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

structure IsBichar (χ : W → W → ℂ) : Prop where
  addL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y
  addR : ∀ x y y', χ x (y + y') = χ x y * χ x y'
  norm1 : ∀ x y, ‖χ x y‖ = 1
  contL : ∀ y, Continuous fun x => χ x y
  contR : ∀ x, Continuous (χ x)

theorem IsBichar.zero_left {χ : W → W → ℂ} (h : IsBichar χ) (y : W) : χ 0 y = 1 := by
  have hne : χ 0 y ≠ 0 := fun h0 => by have := h.norm1 0 y; rw [h0, norm_zero] at this; exact zero_ne_one this
  have e := h.addL 0 0 y
  rw [add_zero] at e
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact e.symm)

theorem IsBichar.freq {χ : W → W → ℂ} (h : IsBichar χ) (v y : W) :
    ∃ β : ℝ, ∀ s : ℝ, χ (s • v) y = exp (↑(β * s) * I) :=
  char_real (fun s => χ (s • v) y) ((h.contL y).comp (continuous_id.smul continuous_const))
    (fun s t => by simp only [add_smul]; exact h.addL _ _ y) (fun s => h.norm1 _ y)

theorem arg_exp_small {θ : ℝ} (h : θ ∈ Set.Ioo (-Real.pi) Real.pi) : arg (exp (↑θ * I)) = θ := by
  rw [arg_exp_mul_I, toIocMod_eq_self]
  exact ⟨h.1, by linarith [h.2, Real.pi_pos]⟩

theorem measurable_freq {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) : Measurable β := by
  let g : ℕ → W → ℝ := fun m y => ((m : ℝ) + 1) * arg (χ ((1 / ((m : ℝ) + 1)) • v) y)
  have hg : ∀ m, Measurable (g m) := fun m =>
    measurable_const.mul (measurable_arg.comp (h.contR _).measurable)
  refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun y => ?_)
  have ht : Tendsto (fun m : ℕ => β y * (1 / ((m : ℝ) + 1))) atTop (𝓝 (β y * 0)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (β y)
  rw [mul_zero] at ht
  have hev := ht (Ioo_mem_nhds (neg_lt_zero.2 Real.pi_pos) Real.pi_pos)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with m hm
  simp only [g]
  rw [hβ y, arg_exp_small hm]
  field_simp

theorem freq_add {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) (y y' : W) :
    β (y + y') = β y + β y' := by
  refine freq_unique fun s => ?_
  rw [← hβ, h.addR, hβ, hβ, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem bichar_eq {χ : W → W → ℂ} (h : IsBichar χ) :
    ∃ L : W →L[ℝ] W, ∀ x y, χ x y = (Real.fourierChar ⟪x, L y⟫ : ℂ) := by
  classical
  choose β hβ using fun v y => h.freq v y
  let b := stdOrthonormalBasis ℝ W
  have hm : ∀ j, Measurable (fun y => β (b j) y) := fun j =>
    measurable_freq h (b j) _ (fun y => hβ (b j) y)
  have ha : ∀ j y y', β (b j) (y + y') = β (b j) y + β (b j) y' := fun j =>
    freq_add h (b j) (fun y => β (b j) y) (fun y => hβ (b j) y)
  let Lf : W → W := fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
  let Lm : W →+ W := AddMonoidHom.mk' Lf fun y y' => by
    simp only [Lf, ha, add_div, add_smul, Finset.sum_add_distrib]
  have hLm : Measurable Lm := by
    show Measurable fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
    exact Finset.measurable_sum Finset.univ fun j _ => ((hm j).div_const _).smul_const (b j)
  have hLc : Continuous Lm := Measure.AddMonoidHom.continuous_of_measurable Lm hLm
  refine ⟨Lm.toRealLinearMap hLc, fun x y => ?_⟩
  have hprod : ∀ s : Finset (Fin (Module.finrank ℝ W)),
      χ (∑ j ∈ s, ⟪b j, x⟫ • b j) y = ∏ j ∈ s, χ (⟪b j, x⟫ • b j) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h.zero_left]
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, h.addL, ih]
  have e1 : χ x y = χ (∑ j, ⟪b j, x⟫ • b j) y := by rw [b.sum_repr' x]
  rw [e1, hprod]
  have e2 : ∀ j, χ (⟪b j, x⟫ • b j) y = exp (↑(β (b j) y * ⟪b j, x⟫) * I) := fun j => hβ _ _ _
  simp only [e2]
  rw [← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  have hLy : ⟪x, (Lm.toRealLinearMap hLc) y⟫ = ∑ j, β (b j) y / (2 * Real.pi) * ⟪b j, x⟫ := by
    show ⟪x, Lf y⟫ = _
    simp only [Lf, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
  rw [hLy]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

end Bichar

section Tests

open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem testEx_kernel (μ : Measure W) [μ.IsAddHaarMeasure] (χ : W → W → ℂ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hc : ∀ y, Continuous fun x => χ x y)
    (t : W) (ht0 : t ≠ 0) (ht : ∀ y, χ t y = 1) : SdUniqW.TestEx μ χ := by
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  let f : ContDiffBump (0 : W) := ⟨‖t‖ / 4, ‖t‖ / 2, by positivity, by linarith⟩
  let φ : W → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hφc : Continuous φ := Complex.continuous_ofReal.comp f.continuous
  have hφs : HasCompactSupport φ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  let Φ : W → ℂ := fun x => φ (x + t) - φ x
  have hΦc : Continuous Φ := (hφc.comp (continuous_id.add continuous_const)).sub hφc
  have hΦs : HasCompactSupport Φ := by
    have h1 : HasCompactSupport fun x => φ (x + t) := hφs.comp_homeomorph (Homeomorph.addRight t)
    exact h1.sub hφs
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = 0 := by
    intro y
    let g : W → ℂ := fun x => φ x * χ x y
    have hg : Integrable g μ := (hφc.mul (hc y)).integrable_of_hasCompactSupport hφs.mul_right
    have e : (fun x => Φ x * χ x y) = fun x => g (x + t) - g x := by
      funext x; simp only [Φ, g, hadd, ht, mul_one, sub_mul]
    rw [e, integral_sub (hg.comp_add_right t) hg, integral_add_right_eq_self, sub_self]
  refine ⟨Φ, hΦc, hΦs, ?_, 0, ?_⟩
  · have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = fun _ => 0 := funext hT
    rw [e]; exact integrable_zero _ _ _
  · simp only [Φ, φ, neg_zero, zero_add]
    rw [f.zero_of_le_dist (by rw [dist_zero_right]; show ‖t‖ / 2 ≤ ‖t‖; linarith),
      f.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))]
    norm_num

theorem testEx_fourier (μ : Measure W) [μ.IsAddHaarMeasure] (A : W ≃L[ℝ] W) :
    SdUniqW.TestEx μ (fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ)) := by
  let f : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : W → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hφd : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hφs : HasCompactSupport φ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  let S : 𝓢(W, ℂ) := hφs.toSchwartzMap hφd
  let B : W ≃L[ℝ] W := A.trans (ContinuousLinearEquiv.neg ℝ)
  set c : NNReal := μ.addHaarScalarFactor volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  have hT : ∀ y, ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ =
      ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y) := by
    intro y
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    congr 1
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [B, S, φ, inner_neg_right, Circle.smul_def, mul_comm]
  have hB : (Measure.map B μ).IsAddHaarMeasure := B.isAddHaarMeasure_map μ
  have hI : Integrable (fun y => (𝓕 S : 𝓢(W, ℂ)) (B y)) μ := by
    have h1 : Integrable (𝓕 S : 𝓢(W, ℂ)) (Measure.map B μ) := (𝓕 S).integrable
    exact (integrable_map_measure h1.aestronglyMeasurable B.continuous.measurable.aemeasurable).1 h1
  refine ⟨φ, hφd.continuous, hφs, ?_, 0, ?_⟩
  · have e : (fun y => ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ) =
        fun y => ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y) := funext hT
    rw [e]; exact hI.const_mul _
  · simp only [φ, neg_zero]
    rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    norm_num

theorem testEx_bichar (μ : Measure W) [μ.IsAddHaarMeasure] {χ : W → W → ℂ} (h : IsBichar χ) :
    SdUniqW.TestEx μ χ := by
  obtain ⟨L, hL⟩ := bichar_eq h
  by_cases hs : Function.Surjective L
  · have hi : Function.Injective L :=
      (LinearMap.injective_iff_surjective (f := (L : W →ₗ[ℝ] W))).2 hs
    let A : W ≃L[ℝ] W :=
      (LinearEquiv.ofBijective (L : W →ₗ[ℝ] W) ⟨hi, hs⟩).toContinuousLinearEquiv
    have e : χ = fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ) :=
      funext₂ fun x y => by rw [hL x y]; rfl
    rw [e]; exact testEx_fourier μ A
  · have hK : (LinearMap.range (L : W →ₗ[ℝ] W))ᗮ ≠ ⊥ := by
      rw [Ne, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]; exact hs
    obtain ⟨t, htK, ht0⟩ := (Submodule.ne_bot_iff _).1 hK
    refine testEx_kernel μ χ h.addL h.contL t ht0 fun y => ?_
    have h0 : ⟪t, L y⟫ = 0 :=
      (Submodule.mem_orthogonal' _ t).1 htK _ (LinearMap.mem_range_self (L : W →ₗ[ℝ] W) y)
    rw [hL, h0, AddChar.map_zero_eq_one, Circle.coe_one]

theorem testEx_of_homeo {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    (e : V ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : SdUniqW.TestEx μ χ := by
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  have hs : ∀ u v : W, e.symm (u + v) = e.symm u + e.symm v := fun u v => ea.symm.map_add u v
  let ce : V ≃ₜ+ W :=
    { ea with continuous_toFun := e.continuous, continuous_invFun := e.symm.continuous }
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  let μ' : Measure W := Measure.map em μ
  have : μ'.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ ce
  let χ' : W → W → ℂ := fun x y => χ (e.symm x) (e.symm y)
  have hb : IsBichar χ' :=
    { addL := fun x x' y => by simp only [χ', hs, hL]
      addR := fun x y y' => by simp only [χ', hs, hR]
      norm1 := fun x y => hn _ _
      contL := fun y => (hcL _).comp e.symm.continuous
      contR := fun x => (hcR _).comp e.symm.continuous }
  obtain ⟨φ, hφc, hφs, hI, z, hz⟩ := testEx_bichar μ' hb
  have hT : ∀ y, ∫ x, φ (e x) * χ x y ∂μ = ∫ x, φ x * χ' x (e y) ∂μ' := by
    intro y
    rw [integral_map_equiv em]
    simp [χ', em]
  refine ⟨fun x => φ (e x), hφc.comp e.continuous, hφs.comp_homeomorph e, ?_, e.symm z, ?_⟩
  · show Integrable (fun y => ∫ x, φ (e x) * χ x y ∂μ) μ
    have e1 : (fun y => ∫ x, φ (e x) * χ x y ∂μ) = (fun y => ∫ x, φ x * χ' x y ∂μ') ∘ em :=
      funext hT
    rw [e1]
    exact (integrable_map_equiv em _).1 hI
  · show φ (e (-e.symm z)) ≠ 0
    have h1 : e (-e.symm z) = -z := by
      have := ea.map_neg (e.symm z)
      change e (-e.symm z) = -e (e.symm z) at this
      rw [this, e.apply_symm_apply]
    rw [h1]; exact hz

end Tests

section Adelic

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem BR_add_right' (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → R ⊗[F] E) : BR R σ J X (Y + Y') = BR R σ J X Y + BR R σ J X Y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem pairHerm_add_right' (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n S (T + U) = pairHerm R σ n S T + pairHerm R σ n S U := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib,
    map_add]

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_BR_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → R ⊗[F] E) : Continuous fun X => BR R σ J X Y := by
  have h : ∀ a : Fin n, Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
      Algebra.trace R (R ⊗[F] E) (hR R σ J (X a) (Y a)) := by
    intro a
    have h0 : Continuous fun X : Fin n → Fin M → R ⊗[F] E => (X a, Y a) :=
      (continuous_apply a).prodMk (continuous_const (y := Y a))
    have hc := continuous_hR R σ J
    have h1 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc h0
    have h2 : Continuous fun z : R ⊗[F] E => Algebra.trace R (R ⊗[F] E) z := continuous_trace_tens R
    exact h2.comp h1
  exact continuous_finsetSum Finset.univ fun a _ => h a

theorem continuous_pairHerm_left (σ : E →ₐ[F] E) (n : ℕ) (T : HermR R σ n) :
    Continuous fun S : HermR R σ n => pairHerm R σ n S T := by
  show Continuous fun S : HermR R σ n => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (∑ a, ∑ b, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)
  refine continuous_const.mul ((continuous_trace_tens R).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (Continuous.matrix_elem continuous_subtype_val a b).mul continuous_const

end Top

theorem continuous_psiInf' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) : Continuous (psiInf F ψ) := by
  have : Continuous fun x : Ainf F => ((x, (0 : Af F)) : Ainf F × Af F) :=
    continuous_id.prodMk continuous_const
  exact hψ.comp this

theorem testEx_coord {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    {n : ℕ} (e : V ≃ₜ (Fin n → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : TestEx μ χ := by
  let L := (EuclideanSpace.equiv (Fin n) ℝ).symm
  refine testEx_of_homeo μ χ (e.trans L.toHomeomorph) (fun x y => ?_) hL hR hn hcL hcR
  show L (e (x + y)) = L (e x) + L (e y)
  rw [he, map_add]

end Adelic

end SdTestInfW

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW SdTestInfW

theorem sdTestInf_holds : SdTestInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨n, m, eV, eH, hV, hH⟩ := tensR_holds F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet
  have : SecondCountableTopology (HermR (Ainf F) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  have hpc := continuous_psiInf' ψ hψ.1
  have hpn : ∀ r, ‖psiInf F ψ r‖ = 1 := fun r => hψ.2.1 _
  refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
  · have := hμ.1
    exact testEx_coord μ _ eV hV (fun X X' Y => by rw [BR_add, psiInf_add])
      (fun X Y Y' => by rw [BR_add_right', psiInf_add]) (fun X Y => hpn _)
      (fun Y => hpc.comp (continuous_BR_left (Ainf F) σ J Y))
      (fun X => hpc.comp (continuous_BR_right (Ainf F) σ J X))
  · have := hν.1
    exact testEx_coord ν _ eH hH (fun S S' T => by rw [pairHerm_add, psiInf_add])
      (fun S T T' => by rw [pairHerm_add_right', psiInf_add]) (fun S T => hpn _)
      (fun T => hpc.comp (continuous_pairHerm_left (Ainf F) σ a T))
      (fun S => hpc.comp (continuous_pairHerm_right (Ainf F) σ a S))

end PI.VolStabW
end
end

section
namespace PI.VolStabW

theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabW
end

section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set LocPosW
open scoped TensorProduct ENNReal

theorem locPos_holds : LocPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).2 v
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let b := Module.finBasis F E
  set X1 := ratTup (F := F) (Fv F v) X0 with hX1
  set T := hermOf (Fv F v) σ (gramE σ J X0) hT with hTdef
  have hgT : gramH (Fv F v) σ hσ J hJ.1 X1 = T := Subtype.ext (gramR_ratTup (Fv F v) σ J X0)
  have hX1U : LinearIndependent (Fv F v ⊗[F] E) X1 :=
    linIndep_of_isUnit_det (Fv F v) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Fv F v) σ _ hT hdet)
  obtain ⟨N, hN, hd⟩ := gramFilt_of (dxOpen_of secGram_holds) F E σ hσ M J hJ.1 hJ.2 a ha1 (by omega) v
    _ b X1 hX1U
  obtain ⟨Λ0, hB, hΛ0o, hΛ0c, hsub⟩ := isCOBasis_latSub b v a M N hN
  obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ :=
    hd X1 (by rw [sub_self]; exact mem_of_mem_nhds hN) Λ0 hB hsub
  let Nb : Set (HermR (Fv F v) σ a) :=
    {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det}
  have hNb : Nb ∈ 𝓝 T :=
    (isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a).mem_nhds
      (isUnit_det_hermOf (Fv F v) σ _ hT hdet)
  have hval := fibCos μv νv (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ hσ J hJ.1) (continuous_gramH (Fv F v) σ hσ J hJ.1) (fun _ => rfl)
    _ Set.univ fibV hfib T Filter.univ_mem Nb hNb
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) Λ H hΛo hΛc hΛa hHo hHc hHb D hD X1
    hyp (by rw [hgT, sub_self]; exact zero_mem _)
  have hΛ0pos : μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ≠ 0 :=
    ((hΛo 0).measure_pos μv ⟨0, zero_mem _⟩).ne'
  have hΛ0fin : μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ≠ ⊤ :=
    ((hΛc 0).measure_lt_top).ne
  have hH0pos : νv (H 0 : Set (HermR (Fv F v) σ a)) ≠ 0 :=
    ((hHo 0).measure_pos νv ⟨0, zero_mem _⟩).ne'
  have hH0fin : νv (H 0 : Set (HermR (Fv F v) σ a)) ≠ ⊤ := ((hHc 0).measure_lt_top).ne
  have hQo : IsOpen {x | x - X1 ∈ Λ 0} := (hΛo 0).preimage (continuous_id.sub continuous_const)
  have hQcl : IsClosed {x | x - X1 ∈ Λ 0} :=
    (AddSubgroup.isClosed_of_isOpen _ (hΛo 0)).preimage (continuous_id.sub continuous_const)
  have hQc : IsCompact {x | x - X1 ∈ Λ 0} := by
    have e : {x | x - X1 ∈ Λ 0} = (fun w => w + X1) '' (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - X1, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [e]
    exact (hΛc 0).image (continuous_id.add continuous_const)
  refine ⟨{x | x - X1 ∈ Λ 0}.indicator 1, ⟨(LocallyConstant.indicator
    (LocallyConstant.const _ (1 : ℂ)) ⟨hQcl, hQo⟩).isLocallyConstant,
    HasCompactSupport.intro' hQc hQcl fun Y hY => Set.indicator_of_notMem hY _⟩, ?_⟩
  rw [hval]
  have hr : 0 < (μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) /
      νv (H 0 : Set (HermR (Fv F v) σ a))).toReal :=
    ENNReal.toReal_pos (ENNReal.div_pos_iff.2 ⟨hΛ0pos, hH0fin⟩).ne'
      (ENNReal.div_ne_top hΛ0fin hH0pos)
  exact_mod_cast hr.ne'

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology Set Filter
open scoped ENNReal

def SubmLB : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) → ∀ W : Set (Fin n → ℝ), IsOpen W → x0 ∈ W →
      ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (f x0), ∀ S ⊆ N, MeasurableSet S →
        c * ν S ≤ μ (f ⁻¹' S ∩ W)

theorem submLB_holds : SubmLB := by
  intro n m μ ν hμ hν f hf x0 hx0 W hW hxW
  let A := fderiv ℝ f x0
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hx0)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  let Θ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => T.symm (f x, (T x).2)
  have hΘc : ContDiff ℝ 1 Θ :=
    T.symm.contDiff.comp (hf.prodMk (contDiff_snd.comp T.contDiff))
  have hfA : ∀ x, A (Θ x) = f x := by
    intro x
    rw [← hT1]; simp [Θ]
  have hd : ∀ x, HasFDerivAt Θ (fderiv ℝ Θ x) x :=
    fun x => ((hΘc.differentiable one_ne_zero) x).hasFDerivAt
  have hid : fderiv ℝ Θ x0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    let P := (ContinuousLinearMap.snd ℝ (Fin m → ℝ) A.ker).comp T.toContinuousLinearMap
    have hP : HasFDerivAt (fun x => (T x).2) P x0 := P.hasFDerivAt
    have h1 : HasFDerivAt (fun x => (f x, (T x).2)) ((fderiv ℝ f x0).prod P) x0 :=
      ((hf.differentiable one_ne_zero) x0).hasFDerivAt.prodMk hP
    have h2 := T.symm.toContinuousLinearMap.hasFDerivAt.comp x0 h1
    rw [show fderiv ℝ Θ x0 = T.symm.toContinuousLinearMap.comp ((fderiv ℝ f x0).prod P) from
      h2.fderiv]
    ext1 y
    change T.symm ((fderiv ℝ f x0) y, (T y).2) = y
    have : ((fderiv ℝ f x0) y, (T y).2) = T y := Prod.ext (hT1 y).symm rfl
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  have hs : HasStrictFDerivAt Θ
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0 := by
    have := hΘc.contDiffAt.hasStrictFDerivAt (x := x0) one_ne_zero
    rw [hid] at this
    exact this
  let PH := hs.toOpenPartialHomeomorph Θ

  have hO : IsOpen (PH.source ∩ W) := PH.open_source.inter hW
  have hxO : x0 ∈ PH.source ∩ W := ⟨hs.mem_toOpenPartialHomeomorph_source, hxW⟩
  obtain ⟨K0, hK0c, hxK0, hK0O⟩ := exists_compact_subset hO hxO

  have hDc : Continuous fun x => (fderiv ℝ Θ x).det :=
    ContinuousLinearMap.continuous_det.comp (hΘc.continuous_fderiv one_ne_zero)
  obtain ⟨Dm, hDm⟩ := hK0c.exists_bound_of_continuousOn hDc.continuousOn
  set D' : ℝ≥0∞ := ENNReal.ofReal (max Dm 1) with hD'
  have hD'0 : D' ≠ 0 := by
    rw [hD', Ne, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD'top : D' ≠ ⊤ := ENNReal.ofReal_ne_top

  let V0 := PH '' interior K0
  have hV0o : IsOpen V0 := PH.isOpen_image_of_subset_source isOpen_interior
    (interior_subset.trans (hK0O.trans inter_subset_left))
  have hΘx0 : Θ x0 ∈ V0 := ⟨x0, hxK0, rfl⟩

  have hTV : T '' V0 ∈ 𝓝 (T (Θ x0)) :=
    (T.toHomeomorph.isOpenMap _ hV0o).mem_nhds ⟨_, hΘx0, rfl⟩
  rw [nhds_prod_eq] at hTV
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.1 hTV
  let lam : Measure A.ker := Measure.addHaar
  set Bk := interior v with hBk
  have hBk0 : lam Bk ≠ 0 :=
    (isOpen_interior.measure_pos lam ⟨_, mem_interior_iff_mem_nhds.2 hv⟩).ne'
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c0, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsm
    have := (isOpen_univ.measure_pos (μ.map T) univ_nonempty).ne'
    rw [hsm] at this
    exact this rfl
  refine ⟨min (D'⁻¹ * c0 * lam Bk) 1,
    lt_min (pos_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.2 hD'top) hc0) hBk0))
      one_pos,
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _), u, ?_, fun S hSu hSm => ?_⟩
  · have e : (T (Θ x0)).1 = f x0 := by rw [hT1, hfA]
    rw [← e]
    exact hu
  · let s := K0 ∩ Θ ⁻¹' (A ⁻¹' S)
    have hsm' : MeasurableSet s := hK0c.isClosed.measurableSet.inter
      ((A.continuous.comp hΘc.continuous).measurable hSm)
    have hs_sub : s ⊆ f ⁻¹' S ∩ W := fun x hx =>
      ⟨by show f x ∈ S; rw [← hfA]; exact hx.2, (hK0O hx.1).2⟩
    have hsrc : s ⊆ PH.source := fun x hx => (hK0O hx.1).1
    have hcv := lintegral_abs_det_fderiv_eq_addHaar_image μ hsm'
      (fun x _ => (hd x).hasFDerivWithinAt) (PH.injOn.mono hsrc)
    have hbound : μ (Θ '' s) ≤ D' * μ s := by
      rw [← hcv, ← setLIntegral_const]
      refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
      have h := hDm x hx.1
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    have hsub2 : T ⁻¹' (S ×ˢ Bk) ⊆ Θ '' s := by
      intro z hz
      obtain ⟨z', hz'V, hTz⟩ := huv ⟨hSu hz.1, interior_subset hz.2⟩
      have hzz : z' = z := T.injective hTz
      subst hzz
      obtain ⟨x, hxK, rfl⟩ := hz'V
      refine ⟨x, ⟨interior_subset hxK, ?_⟩, rfl⟩
      show A (Θ x) ∈ S
      rw [← hT1]
      exact hz.1
    have hmeasT : μ (T ⁻¹' (S ×ˢ Bk)) = c0 * (ν S * lam Bk) := by
      rw [← Measure.map_apply T.continuous.measurable (hSm.prod isOpen_interior.measurableSet),
        hsm, Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    calc min (D'⁻¹ * c0 * lam Bk) 1 * ν S ≤ D'⁻¹ * c0 * lam Bk * ν S :=
          mul_le_mul_left (min_le_left _ _) _
      _ = D'⁻¹ * μ (T ⁻¹' (S ×ˢ Bk)) := by rw [hmeasT]; ring
      _ ≤ D'⁻¹ * μ (Θ '' s) := mul_le_mul_right (measure_mono hsub2) _
      _ ≤ D'⁻¹ * (D' * μ s) := mul_le_mul_right hbound _
      _ = μ s := by rw [← mul_assoc, ENNReal.inv_mul_cancel hD'0 hD'top, one_mul]
      _ ≤ μ (f ⁻¹' S ∩ W) := measure_mono hs_sub

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set LocPosW
open scoped TensorProduct ENNReal

theorem lbInf_of (hC : CoordInf) (hS : SubmLB) : LBInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ hν W hWo hXW
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩ :=
    hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ a) := ⟨rfl⟩
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μinf.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (νinf.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  set X1 := ratTup (F := F) (Ainf F) X0 with hX1
  set T := hermOf (Ainf F) σ (gramE σ J X0) hT with hTdef
  have hX1U : LinearIndependent (Ainf F ⊗[F] E) X1 :=
    linIndep_of_isUnit_det (Ainf F) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  have hW' : IsOpen (eV.symm ⁻¹' W) := hWo.preimage eV.symm.continuous
  have hx0W : eV X1 ∈ eV.symm ⁻¹' W := by
    show eV.symm (eV X1) ∈ W
    rw [Homeomorph.symm_apply_apply]
    exact hXW
  obtain ⟨c, hc0, hct, N', hN', hlb'⟩ :=
    hS n m _ _ hμ' hν' f' hf' (eV X1) (hsurj X1 hX1U) _ hW' hx0W
  have hfx0 : f' (eV X1) = eH T := by
    have h1 : eH.symm (f' (eV X1)) = T := Subtype.ext ((hG X1).trans (gramR_ratTup (Ainf F) σ J X0))
    rw [← h1, Homeomorph.apply_symm_apply]
  have hN : eH ⁻¹' N' ∈ 𝓝 T := eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')
  refine ⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩
  have hS'm : MeasurableSet (eH.symm ⁻¹' S) := eH.symm.continuous.measurable hSm
  have hS'N : eH.symm ⁻¹' S ⊆ N' := fun z hz => by
    have := hSN hz
    rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
  have h := hlb' _ hS'N hS'm
  rw [show (νinf.map eH) = νinf.map eH.toMeasurableEquiv from rfl,
    show (μinf.map eV) = μinf.map eV.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply, MeasurableEquiv.map_apply] at h
  have e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S := by
    ext z
    simp
  have e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) =
      (gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W := by
    ext X
    simp only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.symm_apply_apply, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, h1, hG X⟩, h2⟩
    · rintro ⟨⟨s, hs, hsX⟩, h2⟩
      refine ⟨?_, h2⟩
      have : s = eH.symm (f' (eV X)) := Subtype.ext (hsX.trans (hG X).symm)
      rw [← this]
      exact hs
  rw [e1, e2] at h
  exact h

theorem lbInf_holds : LBInf :=
  lbInf_of (coordInf_of quadCoord_holds tensR_holds (freeSurj_of semisimpleTens_holds))
    submLB_holds

theorem archPos_holds : ArchPos := archPos_of_lb lbInf_holds

end PI.VolStabW
end
end

section
namespace PI.VolStabW.Assembly

open PI.VolStabW

theorem fibPin_closed : FibPin :=
  fibPin_of densFibInf_holds densFibV_holds latSB_holds

theorem sWeqOm_closed : SWeqOm :=
  sWeqOm_of densFibInf_holds densFibV_holds

theorem sdUniq_closed : SdUniq :=
  sdUniq_of_inf sdTestInf_holds

theorem exOmT_holds : ExOmT :=
  exOmT_of_open (fibInfEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densInf_holds)
    (fibVEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densV_holds) sdUniq_closed restrProd_holds

theorem nuInv_holds : NuInv :=
  nuInv_of_pin detAdm_holds compG_holds fibPin_closed sdUniq_closed

theorem volStabFromSW_of_nuNe (hN : NuNeZero) : PI.VolStabW.VolStabFromSWW :=
  volStabFromSW_of exChar_holds exOmT_holds (exStab_of_nu nuInv_holds nuFin_holds hN)
    exFDStab_holds sWeqOm_closed unfold_holds posTest_holds

theorem volStabFromSW_of_open_dens (hDA : DensAA) : PI.VolStabW.VolStabFromSWW :=
  volStabFromSW_of_nuNe (nuNeZero_of_dens archPos_holds locPos_holds hDA qvSum_holds)

theorem volStabFromSW_of_open_aa (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabW.VolStabFromSWW :=
  volStabFromSW_of_open_dens (densAA_of_open hV hH hI hC)

theorem volStabFromSW_of_open_vic (hV : VolAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabW.VolStabFromSWW :=
  volStabFromSW_of_open_aa hV hensAA_holds hI hC

theorem volStabFromSW_of_open_ic (hI : IdxH) (hC : CntAA) : PI.VolStabW.VolStabFromSWW :=
  volStabFromSW_of_open_vic volAA_holds hI hC

theorem volStabFromSW_of_cntAA (hC : CntAA) : PI.VolStabW.VolStabFromSWW :=
  volStabFromSW_of_open_ic idxH_holds hC

theorem volStabFromSW_holds : PI.VolStabW.VolStabFromSWW :=
  volStabFromSW_of_cntAA cntAA_holds

end PI.VolStabW.Assembly
end
