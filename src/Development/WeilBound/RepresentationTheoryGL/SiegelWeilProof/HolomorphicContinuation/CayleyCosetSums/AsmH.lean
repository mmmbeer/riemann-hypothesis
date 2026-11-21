import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RightConn
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseD
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolParam
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarId
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContDiffMatrixMul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Nonzero
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MatInv

section
noncomputable section

open Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

theorem iteratedDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) (k : ℕ) :
    iteratedDeriv k f s = iteratedDeriv k g s := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedDerivWithin_eq (by simpa using h) h.eq_of_nhds

theorem leib {U : Set ℂ} (hU : IsOpen U) : ∀ (j : ℕ) (h₁ h₂ : ℂ → ℂ), DifferentiableOn ℂ h₁ U → DifferentiableOn ℂ h₂ U →
    ∀ s ∈ U, iteratedDeriv j (fun z => h₁ z * h₂ z) s =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i h₁ s * iteratedDeriv (j - i) h₂ s := by
  intro j
  induction j with
  | zero => intro h₁ h₂ _ _ s _; simp
  | succ j ih =>
    intro h₁ h₂ hd₁ hd₂ s hs
    have hd₁' : DifferentiableOn ℂ (deriv h₁) U := hd₁.deriv hU
    have hd₂' : DifferentiableOn ℂ (deriv h₂) U := hd₂.deriv hU
    have hev : deriv (fun z => h₁ z * h₂ z) =ᶠ[𝓝 s] fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact deriv_mul ((hd₁.differentiableAt (hU.mem_nhds hz))) ((hd₂.differentiableAt (hU.mem_nhds hz)))
    rw [iteratedDeriv_succ', iteratedDeriv_eq_of_eventuallyEq hev]
    have hc₁ : ContDiffAt ℂ j (fun z => deriv h₁ z * h₂ z) s :=
      ((hd₁'.mul hd₂).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hc₂ : ContDiffAt ℂ j (fun z => h₁ z * deriv h₂ z) s :=
      ((hd₁.mul hd₂').contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hsplit : (fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z) =
        (fun z => deriv h₁ z * h₂ z) + (fun z => h₁ z * deriv h₂ z) := rfl
    rw [hsplit, iteratedDeriv_add hc₁ hc₂, ih _ _ hd₁' hd₂ s hs, ih _ _ hd₁ hd₂' s hs]
    have key := Finset.sum_choose_succ_mul (R := ℂ) (fun a b => iteratedDeriv a h₁ s * iteratedDeriv b h₂ s) j
    simp only [mul_assoc] at key ⊢
    rw [key, add_comm]
    congr 1
    all_goals
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      (try rw [← iteratedDeriv_succ']); (try rw [show j + 1 - i = j - i + 1 by omega])

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ExpLie : Prop := ∀ (n : ℕ) (x Z : M2 n) (t : ℝ), InG x →
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) ∧
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))

theorem lift_mR' (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  unfold lift
  rw [dif_pos h]
  congr 1
  ext : 2
  rfl

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x :=
  (Matrix.isUnit_iff_isUnit_det x).2 (PositivityTheory.Rg.Sw.Glob.DenseP.isUnit_det_of_inG hx)

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(isUnit_of_inG hx).unit, hx⟩

theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

theorem rC_const_mul (Z : M2 n) (a : ℂ) (F : M2 n → ℂ) (x : M2 n) :
    rC Z (fun x => a * F x) x = a * rC Z F x := by
  unfold rC
  rw [deriv_const_mul_field', deriv_const_mul_field']
  ring

theorem rC_zero (Z : M2 n) (x : M2 n) : rC Z (fun _ => (0 : ℂ)) x = 0 := by
  unfold rC
  simp

def Van (j : ℕ) (h : ℂ → ℂ) (s : ℂ) : Prop := ∀ k ≤ j, iteratedDeriv k h s = 0

theorem van_mul {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : Van j h s) : Van j (fun z => q z * h z) s := by
  intro k hk
  rw [leib hU k q h hq hh s hs]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hv (k - i) (by omega)]
  simp

theorem van_sum {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {ι : Type} (S : Finset ι) (h : ι → ℂ → ℂ)
    (hd : ∀ l, DifferentiableOn ℂ (h l) U) {j : ℕ} (hv : ∀ l, Van j (h l) s) : Van j (fun z => ∑ l ∈ S, h l z) s := by
  classical
  induction S using Finset.induction_on with
  | empty => intro k _; simp
  | insert a S ha ih =>
    intro k hk
    have e : (fun z => ∑ l ∈ insert a S, h l z) = (fun z => h a z) + (fun z => ∑ l ∈ S, h l z) := by
      funext z; simp [Finset.sum_insert ha]
    have hds : DifferentiableOn ℂ (fun z => ∑ l ∈ S, h l z) U := by
      exact DifferentiableOn.fun_sum (fun l _ => hd l)
    rw [e, iteratedDeriv_add (((hd a).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top)
      ((hds.contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top), hv a k hk, ih k hk, add_zero]

theorem iter_mul_low {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : ∀ i < j, iteratedDeriv i h s = 0) :
    iteratedDeriv j (fun z => q z * h z) s = q s * iteratedDeriv j h s ∧
      ∀ i < j, iteratedDeriv i (fun z => q z * h z) s = 0 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [leib hU j q h hq hh s hs, Finset.sum_eq_single 0]
    · simp
    · intro b hbm hb
      have := Finset.mem_range.1 hbm
      rw [hv (j - b) (by omega)]
      simp
    · intro h0; exact absurd (Finset.mem_range.2 (Nat.succ_pos j)) h0
  · rw [leib hU i q h hq hh s hs]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : b < i + 1 := Finset.mem_range.1 hb
    rw [hv (i - b) (by omega)]
    simp

theorem asmH_of (hF : FarId) (hS : SmoothX) (hT : TopHol) (hR : RcCongr) (hE : ExpLie) : AsmH := by
  intro hLT hSec hCR
  intro m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hsplit U d Ê t hU hRU hs0 hhol hcont hfar j hlow hsing g
  have hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t := ⟨hι, hsplit, hU, hRU, hs0, hhol, hcont, hfar⟩
  haveI : CompactSpace (KR n) := kRCpt n
  letI : MeasurableSpace (KR n) := borel _
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  let μ : Measure (KR n) := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : IsProbabilityMeasure μ := ⟨by simpa [μ] using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KR n)))⟩

  obtain ⟨Φs, Ω, c, hΩo, hΩG, hcd, hc0, hΦG, -, hΦj, hΦd, hΦrC⟩ := hS m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD g
  set φ : GR n → ℂ := fun y => iteratedDeriv j (Ê · (g * ι y)) s₀ with hφ
  set Ψ : ℕ → M2 n → ℂ := fun r x => iteratedDeriv r (Φs · x) s₀ with hΨ

  have hΨG : ∀ (y : GR n), Ψ j (mR y) = c s₀ * φ y ∧ ∀ i < j, Ψ i (mR y) = 0 := by
    intro y
    have hev : (Φs · (mR y)) =ᶠ[𝓝 s₀] fun z => c z * Ê z (g * ι y) := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hΦG z hz y
    have hlow' : ∀ i < j, iteratedDeriv i (Ê · (g * ι y)) s₀ = 0 := fun i hi => hlow i hi (g * ι y)
    obtain ⟨h1, h2⟩ := iter_mul_low hU hs0 hcd (hhol (g * ι y)) hlow'
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev j, h1]
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev i, h2 i hi]
  have hΨ0 : ∀ i < j, ∀ x', InG x' → Ψ i x' = 0 := by
    intro i hi x' hx'
    have := (hΨG (toGR x' hx')).2 i hi
    rwa [mR_toGR] at this

  have hιKc : Continuous (ιK n) := by
    unfold ιK
    exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hιKiff : ∀ x, InK x ↔ ∃ k, ιK n k = x := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨toGR x hx.1, hx⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2

  obtain ⟨N₀, ρ₀, ψ₀, a₀, b₀, D₀, M₀, hρ₀, hψ₀, hab₀, hDd₀, -, hMd₀, hid₀⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff 0
  obtain ⟨-, hK⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ 0 N₀ ρ₀ ψ₀ a₀ b₀ D₀ M₀ hρ₀ hψ₀ hab₀ hDd₀ hMd₀ hid₀
  refine hCR n m e φ (fun x => (c s₀)⁻¹ * Ψ j x) Ω hΩo hΩG (contDiffOn_const.mul (hΦj j)) ?_ ?_ ?_
  · intro y
    simp only [(hΨG y).1]
    field_simp
  · intro y k hk
    have hev : (Ê · (g * ι (y * k))) =ᶠ[𝓝 s₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hK z hz g y k hk
    simp only [hφ]
    rw [iteratedDeriv_eq_of_eventuallyEq hev j, iteratedDeriv_mul_const_field]
  · intro y Q
    rw [rC_const_mul]
    suffices h : rC (lowQ Q) (Ψ j) (mR y) = 0 by rw [h, mul_zero]
    obtain ⟨N, ρ, ψ, a, b, D, M, hρ, hψ, hab, hDd, hD0, hMd, hid⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff Q
    obtain ⟨⟨t', hfarId⟩, -⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ Q N ρ ψ a b D M hρ hψ hab hDd hMd hid
    set L : ℂ → ℂ := fun z => rC (lowQ Q) (Φs z) (mR y) with hL
    set T : Fin N → ℂ → ℂ := fun l z => tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y) with hTdef
    set R : ℂ → ℂ := fun z => c z * ∑ l, M l (z - s₀) * T l z with hRdef
    have hTH : ∀ l, DifferentiableOn ℂ (T l) U ∧ ∀ r : ℕ, iteratedDeriv r (T l) s₀ =
        tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y) := fun l =>
      hT m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD μ (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1 (hab l).1 (hab l).2 g y
    have hDs : Differentiable ℂ fun z => D (z - s₀) := hDd.comp (differentiable_id.sub_const s₀)
    have hMs : ∀ l, Differentiable ℂ fun z => M l (z - s₀) := fun l => (hMd l).comp (differentiable_id.sub_const s₀)
    have hLd : DifferentiableOn ℂ L U := (hΦrC Q y).1
    have hsumd : DifferentiableOn ℂ (fun z => ∑ l, M l (z - s₀) * T l z) U :=
      DifferentiableOn.fun_sum fun l _ => (hMs l).differentiableOn.mul (hTH l).1
    have hRd : DifferentiableOn ℂ R U := hcd.mul hsumd

    have hEq : EqOn (fun z => D (z - s₀) * L z) R U := by
      obtain ⟨σ, hσ⟩ := hRU.1
      set z₁ : ℂ := ((max t' σ + 1 : ℝ) : ℂ) with hz₁
      have hz₁U : z₁ ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (by rw [hz₁, Complex.ofReal_re]; linarith [le_max_right t' σ]))
      refine (hDs.differentiableOn.mul hLd).analyticOnNhd hU |>.eqOn_of_preconnected_of_eventuallyEq
        (hRd.analyticOnNhd hU) (rightConn U hU hRU) hz₁U ?_
      have hopen : IsOpen {z : ℂ | max t' σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (show max t' σ < z₁.re by rw [hz₁, Complex.ofReal_re]; linarith)] with z hz
      have hzt : t' < z.re := lt_of_le_of_lt (le_max_left _ _) hz
      have hzU : z ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (lt_of_le_of_lt (le_max_right _ _) hz))
      have hcong : L z = rC (lowQ Q) (fun x => c z * resG ι (Ê z) g x) (mR y) := by
        refine hR n (Φs z) _ (lowQ Q) (mR y) y.2 (fun x' hx' => ?_) (fun s => (hE n (mR y) (lowQ Q) s y.2).1)
          (fun s => (hE n (mR y) (lowQ Q) s y.2).2)
        have e1 := hΦG z hzU (toGR x' hx')
        rw [mR_toGR] at e1
        have e2 := lift_mR' (fun y => Ê z (g * ι y)) (toGR x' hx')
        rw [mR_toGR] at e2
        simp only [resG]
        rw [e1, e2]
      show D (z - s₀) * L z = c z * ∑ l, M l (z - s₀) * T l z
      rw [hcong, rC_const_mul, mul_left_comm, hfarId z hzt g y]
    have hev : (fun z => D (z - s₀) * L z) =ᶠ[𝓝 s₀] R := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hEq hz
    have hLlow : ∀ i < j, iteratedDeriv i L s₀ = 0 := by
      intro i hi
      rw [(hΦrC Q y).2 i, hR n _ (fun _ => 0) (lowQ Q) (mR y) y.2 (fun x' hx' => hΨ0 i hi x' hx')
        (fun s => (hE n (mR y) (lowQ Q) s y.2).1) (fun s => (hE n (mR y) (lowQ Q) s y.2).2), rC_zero]
    obtain ⟨hL1, -⟩ := iter_mul_low hU hs0 hDs.differentiableOn hLd hLlow
    have hnb : ∀ t, InG (nU (herm t) : M2 n) := fun t => PositivityTheory.Rg.Sw.LVs.HolB.inG_upper (PositivityTheory.Rg.Sw.AbsSt.LocOpA.herm_isHermitian t).eq
    have hRv : Van j R s₀ := by
      apply van_mul hU hs0 hcd hsumd
      apply van_sum hU hs0 Finset.univ (fun l z => M l (z - s₀) * T l z)
        (fun l => (hMs l).differentiableOn.mul (hTH l).1)
      intro l
      apply van_mul hU hs0 (hMs l).differentiableOn (hTH l).1
      intro k hk
      rw [(hTH l).2 k]
      rcases lt_or_eq_of_le hk with hk' | hkj
      · have hz0 : resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g = fun _ => 0 := by
          funext x
          unfold resG lift
          split_ifs <;> simp [hlow k hk']
        rw [hz0]
        simp [tOp]
      · subst hkj
        have hin : ∀ k' : KR n, (∫ t : Fin n → Fin n → ℝ, resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
            (mR y * ιK n k' * a l * nU (herm t) * b l) * ψ l t) = 0 := by
          intro k'
          let nb : (Fin n → Fin n → ℝ) → GR n := fun t => toGR (nU (herm t)) (hnb t)
          have key := hsing (ψ l) (hψ l) nb (fun t => rfl) g (y * (k' : GR n) * toGR (a l) (hab l).1)
            (toGR (b l) (hab l).2)
          refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans key
          show resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
              (mR (y * (k' : GR n) * toGR (a l) (hab l).1 * nb t * toGR (b l) (hab l).2)) * ψ l t = _
          simp only [resG]
          rw [lift_mR']
        unfold tOp
        simp_rw [hin, mul_zero, integral_zero]
    have hRj := hRv j le_rfl
    have h0 : D 0 * iteratedDeriv j L s₀ = 0 := by
      have h1 := iteratedDeriv_eq_of_eventuallyEq hev j
      rw [hL1, hRj, sub_self] at h1
      exact h1
    have hLj : iteratedDeriv j L s₀ = 0 := (mul_eq_zero.1 h0).resolve_left hD0
    rw [(hΦrC Q y).2 j] at hLj
    exact hLj

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lift_mR (φ : GR n → ℂ) (w : GR n) : lift φ (mR w) = φ w := by
  have h : IsUnit (mR w) ∧ InG (mR w) := ⟨⟨w.1, rfl⟩, w.2⟩
  unfold lift
  rw [dif_pos h]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp [mR]

theorem ιK_apply (k : KR n) : ιK n k = mR (k : GR n) := rfl

theorem mR_mul' (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem tOp_resG {G : Type} [Group G] (ι : GR n →* G) [MeasurableSpace (KR n)] (μ : Measure (KR n)) (ρ : KR n → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b : M2 n} (ha : InG a) (hb : InG b) (F : G → ℂ) (g : G) (y : GR n) :
    tOp μ (ιK n) ρ ψ a b (resG ι F g) (mR y) =
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F ((g * ι y) * ι ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t *
        LocOpA.mkG b hb)) * ψ t) ∂μ := by
  unfold tOp resG
  congr 1
  funext k
  congr 1
  congr 1
  funext t
  congr 1
  have e1 : mR y * ιK n k * a * nU (herm t) * b =
      mR (y * ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t * LocOpA.mkG b hb)) := by
    simp only [mR_mul', ιK_apply, LocOpA.mR_mkG, LocOpA.nbEl, Matrix.mul_assoc]
  rw [e1, lift_mR, map_mul]
  simp only [mul_assoc]

theorem hol_int {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ι : GR n →* G} (hιc : Continuous ι)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n)) [IsFiniteMeasure μ]
    {a b : GR n} {ρ : KR n → ℂ} (hρ : Continuous ρ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {U : Set ℂ} (hU : IsOpen U) (E : ℂ → G → ℂ)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ)) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (g : G) :
    DifferentiableOn ℂ (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ,
      E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) U ∧
    ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ,
      E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) z =
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, iteratedDeriv r (fun w => E w (g * ι ((k : GR n) * a * LocOpA.nbEl t * b))) z *
        ψ t) ∂μ := by
  set C := tsupport ψ
  have hC : IsCompact C := hψs
  haveI : IsFiniteMeasure (volume.restrict C) := ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hCc : (volume.restrict C) Cᶜ = 0 := by
    rw [Measure.restrict_apply (isClosed_tsupport ψ).isOpen_compl.measurableSet, Set.compl_inter_self, measure_empty]
  have hnb := LocOpA.continuous_nbEl (n := n)
  have hj : ContinuousOn (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ =>
      E y.2 (g * ι ((y.1.1 : GR n) * a * LocOpA.nbEl y.1.2 * b)) * ψ y.1.2) (univ ×ˢ U) := by
    refine ContinuousOn.mul ?_ (hψc.comp (continuous_snd.comp continuous_fst)).continuousOn
    refine hEc.comp (Continuous.continuousOn (continuous_snd.prodMk ((Vac.continuous_arg hιc hnb g).comp continuous_fst))) ?_
    intro y hy
    exact ⟨hy.2, trivial⟩
  have e1 : ∀ (k : KR n) (h : ℂ → G → ℂ) (z : ℂ), (∫ x in C, h z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) =
      ∫ x, h z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x := fun k h z =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hinner : ∀ k : KR n, ContinuousOn (fun y : (Fin n → Fin n → ℝ) × ℂ =>
      E y.2 (g * ι ((k : GR n) * a * LocOpA.nbEl y.1 * b)) * ψ y.1) (C ×ˢ U) := by
    intro k
    refine hj.comp (Continuous.continuousOn ((Continuous.prodMk_right k).prodMap continuous_id)) ?_
    intro y hy; exact ⟨trivial, hy.2⟩
  have hind : ∀ k : KR n, ∀ x ∈ C, DifferentiableOn ℂ (fun z => E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) U :=
    fun k x _ => (hEh _).mul_const _
  have hin : ∀ k : KR n, DifferentiableOn ℂ (fun z => ∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) U :=
    fun k => (holParam (Fin n → Fin n → ℝ) (volume.restrict C) C hC hCc U _ hU (hinner k) (hind k)).1
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hcont : Continuous (fun y : KR n × U => ∫ x in C, E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) := by
    refine continuous_parametric_integral_of_continuous
      (f := fun (y : KR n × U) x => E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ?_ hC
    have : Continuous (fun w : (KR n × U) × (Fin n → Fin n → ℝ) =>
        (((w.1.1, w.2), (w.1.2 : ℂ)) : (KR n × (Fin n → Fin n → ℝ)) × ℂ)) :=
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    exact hj.comp_continuous this fun w => ⟨trivial, w.1.2.2⟩
  have hcon : ContinuousOn (fun y : KR n × ℂ => ρ y.1 *
      ∫ x in C, E y.2 (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) (univ ×ˢ U) := by
    refine (hρ.comp continuous_fst).continuousOn.mul ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have : (univ ×ˢ U).domRestrict (fun y : KR n × ℂ => ∫ x in C, E y.2 (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) =
        (fun y : KR n × U => ∫ x in C, E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ∘
          (fun w : (univ ×ˢ U : Set (KR n × ℂ)) => ((w.1.1, ⟨w.1.2, w.2.2⟩) : KR n × U)) := by
      funext w; rfl
    rw [this]
    exact hcont.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have hP := holParam (KR n) μ univ isCompact_univ (by simp) U
    (fun k z => ρ k * ∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) hU hcon
    (fun k _ => (hin k).const_mul _)
  have e2 : (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) =
      fun z => ∫ k, ρ k * (∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ∂μ := by
    funext z
    congr 1
    funext k
    rw [e1 k E z]
  rw [e2]
  refine ⟨hP.1, fun z hz r => ?_⟩
  rw [hP.2 z hz r]
  congr 1
  funext k
  rw [iteratedDeriv_const_mul_field]
  congr 1
  rw [(holParam (Fin n → Fin n → ℝ) (volume.restrict C) C hC hCc U _ hU (hinner k) (hind k)).2 z hz r]
  simp_rw [iteratedDeriv_mul_const_field]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem topHol : TopHol := by
  intro m n e _ _ G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD _ _ μ _ _ ρ ψ a b hρ hψc hψs ha hb g y
  haveI : CompactSpace (KR n) := kRCpt n
  have hfun : ∀ F : ℂ → G → ℂ, (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (F z) g) (mR y)) = fun z =>
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F z ((g * ι y) * ι ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t *
        LocOpA.mkG b hb)) * ψ t) ∂μ := fun F => funext fun z => tOp_resG ι μ ρ ψ ha hb (F z) g y
  have H := hol_int hD.ιc μ (a := LocOpA.mkG a ha) (b := LocOpA.mkG b hb) hρ hψc hψs hD.hU Ê hD.cont hD.hol (g * ι y)
  refine ⟨?_, fun r => ?_⟩
  · rw [hfun Ê]
    exact H.1
  · rw [hfun Ê, H.2 s₀ hD.hs r, tOp_resG ι μ ρ ψ ha hb _ g y]

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg, Matrix.mul_one]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem JJ_inv : (JJ n)⁻¹ = -JJ n := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg, JJ_mul_self, neg_neg]

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  unfold JJ
  rw [fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  simp

theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  unfold sig
  rw [JJ_inv]
  simp [Matrix.neg_mul]

theorem sig_conjTranspose (X : M2 n) : (sig X)ᴴ = JJ n * X * JJ n := by
  rw [sig_eq]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

theorem lie_half1 (Z : M2 n) (t : ℝ) :
    ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))ᴴ * JJ n + JJ n * ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))) = 0 := by
  have h := JJ_mul_self (n := n)
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, sig_conjTranspose, Complex.star_def,
    Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  rw [sig_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h]
  rw [← Matrix.mul_assoc (JJ n) (JJ n), h]
  simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  module

theorem lie_half2 (Z : M2 n) (t : ℝ) :
    ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))ᴴ * JJ n +
      JJ n * ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))) = 0 := by
  have h := JJ_mul_self (n := n)
  have hI : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]
    simp [Complex.conj_ofNat]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, sig_conjTranspose, hI, Complex.star_def,
    Complex.conj_ofReal]
  rw [sig_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h]
  rw [← Matrix.mul_assoc (JJ n) (JJ n), h]
  simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  module

theorem inG_exp_of_lie {X : M2 n} (hX : Xᴴ * JJ n + JJ n * X = 0) : InG (NormedSpace.exp X) := by
  unfold InG
  have hJu : IsUnit (JJ n) := by
    refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    have := congrArg Matrix.det (JJ_mul_self (n := n))
    rw [Matrix.det_mul, Matrix.det_neg] at this
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at this
    simp at this
  have hXh : Xᴴ = JJ n * (-X) * (JJ n)⁻¹ := by
    have h1 : Xᴴ * JJ n = -(JJ n * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᴴ = Xᴴ * JJ n * (JJ n)⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hJu), Matrix.mul_one]
      _ = JJ n * (-X) * (JJ n)⁻¹ := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  rw [← Matrix.exp_conjTranspose, hXh, Matrix.exp_conj _ _ hJu, Matrix.exp_neg]
  have hE : IsUnit (NormedSpace.exp X) := Matrix.isUnit_exp X
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (JJ n)⁻¹ (JJ n),
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hJu), Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hE), Matrix.mul_one]

theorem expLie (x Z : M2 n) (t : ℝ) (hx : InG x) :
    InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) ∧
      InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))) := by
  have hmul : ∀ {a b : M2 n}, InG a → InG b → InG (a * b) := fun {a b} ha hb => by
    unfold InG at *
    calc (a * b)ᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [ha, hb]
  exact ⟨hmul hx (inG_exp_of_lie (lie_half1 Z t)), hmul hx (inG_exp_of_lie (lie_half2 Z t))⟩

theorem rcCongr : RcCongr := by
  intro n F F' Z x _ h h1 h2
  unfold rC
  have e1 : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) =
      fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) := funext fun t => h _ (h1 t)
  have e2 : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) =
      fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))) := funext fun t => h _ (h2 t)
  rw [e1, e2]

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_restrict_of_zero (ν : Measure (GR n)) {C : Set (GR n)} (_hCm : MeasurableSet C) {F : GR n → ℂ}
    (hF : ∀ u ∉ C, F u = 0) : ∫ u, F u ∂ν = ∫ u, F u ∂(ν.restrict C) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

theorem holInt (ν : Measure (GR n)) [ν.IsHaarMeasure] {C : Set (GR n)} (hC : IsCompact C) {U : Set ℂ} (hU : IsOpen U)
    (F : GR n → ℂ → ℂ) (hF0 : ∀ u ∉ C, ∀ z, F u z = 0)
    (hcont : ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ u ∈ C, DifferentiableOn ℂ (F u) U) :
    DifferentiableOn ℂ (fun z => ∫ u, F u z ∂ν) U ∧
      ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ u, F u z ∂ν) z = ∫ u, iteratedDeriv r (F u) z ∂ν := by
  classical
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  haveI : IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hdF : ∀ u, DifferentiableOn ℂ (F u) U := by
    intro u
    by_cases hu : u ∈ C
    · exact hd u hu
    · have h0 : F u = fun _ => 0 := funext (hF0 u hu)
      rw [h0]
      exact differentiableOn_const 0
  have key : ∀ z ∈ U, ∃ R : ℝ≥0, 0 < R ∧ Metric.closedBall z (R : ℝ) ⊆ U := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
    refine ⟨(ε / 2).toNNReal, Real.toNNReal_pos.mpr (half_pos hε), ?_⟩
    rw [Real.coe_toNNReal _ (half_pos hε).le]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hint : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ a : ℝ → ℂ, Continuous a →
      Integrable (fun p : ℝ × GR n => a p.1 • F p.2 (circleMap z R p.1))
        ((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod (ν.restrict C)) := by
    intro z R hzR a ha
    rw [Measure.prod_restrict]
    have hc2 : ContinuousOn (fun p : ℝ × GR n => a p.1 • F p.2 (circleMap z R p.1))
        (Set.Icc 0 (2 * Real.pi) ×ˢ C) := by
      apply ContinuousOn.smul (ha.comp continuous_fst).continuousOn
      have h1 : ContinuousOn (fun p : ℝ × GR n => (p.2, circleMap z R p.1)) (Set.Icc 0 (2 * Real.pi) ×ˢ C) :=
        (continuous_snd.prodMk ((continuous_circleMap z R).comp continuous_fst)).continuousOn
      refine hcont.comp h1 ?_
      rintro ⟨θ, u⟩ ⟨_, hu⟩
      exact ⟨hu, hzR (circleMap_mem_closedBall z R.coe_nonneg θ)⟩
    exact (hc2.integrableOn_compact (isCompact_Icc.prod hC)).mono_set
      (Set.prod_mono (Set.uIoc_subset_uIcc.trans (Set.uIcc_of_le (by positivity)).subset) subset_rfl)
  have hfub : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ a : ℝ → ℂ, Continuous a →
      (∫ θ in (0 : ℝ)..2 * Real.pi, a θ • ∫ u, F u (circleMap z R θ) ∂ν)
        = ∫ u, (∫ θ in (0 : ℝ)..2 * Real.pi, a θ • F u (circleMap z R θ)) ∂ν := by
    intro z R hzR a ha
    have e1 : ∀ θ, a θ • ∫ u, F u (circleMap z R θ) ∂ν
        = ∫ u, a θ • F u (circleMap z R θ) ∂(ν.restrict C) := by
      intro θ
      rw [integral_restrict_of_zero ν hCm (fun u hu => hF0 u hu (circleMap z R θ)), integral_smul]
    simp_rw [e1]
    rw [intervalIntegral_integral_swap (hint z R hzR a ha)]
    exact (integral_restrict_of_zero ν hCm (fun u hu => by simp [hF0 u hu])).symm
  have hcirc : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ k : ℂ → ℂ,
      Continuous (fun θ => k (circleMap z R θ)) →
      (∮ ζ in C(z, R), k ζ • ∫ u, F u ζ ∂ν) = ∫ u, (∮ ζ in C(z, R), k ζ • F u ζ) ∂ν := by
    intro z R hzR k hk
    simp only [circleIntegral, deriv_circleMap, smul_smul]
    exact hfub z R hzR (fun θ => circleMap 0 R θ * Complex.I * k (circleMap z R θ))
      (((continuous_circleMap 0 R).mul continuous_const).mul hk)
  have hps : ∀ z ∈ U, ∃ R : ℝ≥0, 0 < R ∧ Metric.closedBall z (R : ℝ) ⊆ U ∧
      HasFPowerSeriesOnBall (fun w => ∫ u, F u w ∂ν) (cauchyPowerSeries (fun w => ∫ u, F u w ∂ν) z R) z R := by
    intro z hz
    obtain ⟨R, hR, hzR⟩ := key z hz
    refine ⟨R, hR, hzR, ?_⟩
    have hci : CircleIntegrable (fun w => ∫ u, F u w ∂ν) z R := by
      have h := (hint z R hzR (fun _ => 1) continuous_const).integral_prod_left
      rw [CircleIntegrable, intervalIntegrable_iff]
      refine h.congr (Eventually.of_forall fun θ => ?_)
      simp only [one_smul]
      exact (integral_restrict_of_zero ν hCm (fun u hu => hF0 u hu _)).symm
    refine (hasFPowerSeriesOn_cauchy_integral hci hR).congr ?_
    intro w hw
    rw [Metric.emetric_ball_nnreal] at hw
    have hk : Continuous (fun θ => (circleMap z R θ - w)⁻¹) :=
      ((continuous_circleMap z R).sub continuous_const).inv₀
        (fun θ => sub_ne_zero.mpr (circleMap_ne_mem_ball hw θ))
    show (2 * ↑Real.pi * Complex.I)⁻¹ • (∮ ζ in C(z, R), (ζ - w)⁻¹ • ∫ u, F u ζ ∂ν) = ∫ u, F u w ∂ν
    rw [hcirc z R hzR (fun ζ => (ζ - w)⁻¹) hk, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw ((hdF u).continuousOn.mono hzR)
      (fun x hx => (hdF u).differentiableAt (hU.mem_nhds (hzR (Metric.ball_subset_closedBall hx.1))))
  constructor
  · intro z hz
    obtain ⟨R, -, -, h⟩ := hps z hz
    exact h.analyticAt.differentiableAt.differentiableWithinAt
  · intro z hz r
    obtain ⟨R, hR, hzR, h⟩ := hps z hz
    have hFu : ∀ u, iteratedDeriv r (F u) z = r.factorial • cauchyPowerSeries (F u) z R r (fun _ => 1) := by
      intro u
      rw [iteratedDeriv_eq_iteratedFDeriv, ← (((hdF u).mono hzR).hasFPowerSeriesOnBall hR).factorial_smul]
    have hne : ∀ θ, circleMap z R θ - z ≠ 0 := fun θ =>
      sub_ne_zero.mpr (fun h' => hR.ne' (by exact_mod_cast circleMap_eq_center_iff.mp h'))
    have hG : cauchyPowerSeries (fun w => ∫ u, F u w ∂ν) z R r (fun _ => 1)
        = ∫ u, cauchyPowerSeries (F u) z R r (fun _ => 1) ∂ν := by
      simp only [cauchyPowerSeries_apply, smul_smul]
      rw [hcirc z R hzR (fun ζ => (1 / (ζ - z)) ^ r * (ζ - z)⁻¹)
        (((continuous_const.div ((continuous_circleMap z R).sub continuous_const) hne).pow r).mul
          (((continuous_circleMap z R).sub continuous_const).inv₀ hne)), integral_smul]
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h.factorial_smul, integral_congr_ae (Eventually.of_forall hFu), hG]
    simp only [nsmul_eq_mul]
    rw [integral_const_mul]

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hLoc_nonneg' (g : GR n) : 0 ≤ hLoc g := by unfold hLoc; positivity

theorem hLoc_pos' (g : GR n) : 0 < hLoc g := Vac.hLoc_pos detU1 g

theorem hLoc_slit (g : GR n) : ((hLoc g : ℝ) : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.2 (hLoc_pos' g)

theorem continuous_phi (m : ℕ) (e : ℤ) (w : ℂ) : Continuous (phi (n := n) m e w) := by
  unfold phi
  refine (Vac.continuous_weight_factor detU1 m 0 e).mul ?_
  exact (Complex.continuous_ofReal.comp (Vac.continuous_hLoc detU1)).cpow continuous_const fun g => hLoc_slit g

theorem continuous_phi₂ (m : ℕ) (e : ℤ) :
    Continuous fun p : GR n × ℂ => phi m e p.2 p.1 := by
  unfold phi
  refine ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_fst).mul ?_
  exact (Complex.continuous_ofReal.comp ((Vac.continuous_hLoc detU1).comp continuous_fst)).cpow continuous_snd
    fun p => hLoc_slit p.1

theorem differentiable_phi (m : ℕ) (e : ℤ) (u : GR n) : Differentiable ℂ fun w => phi m e w u := by
  unfold phi
  have h0 : ((hLoc u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hLoc_pos' u).ne'
  exact (differentiable_const _).mul (differentiable_id.const_cpow (Or.inl h0))

section

variable {m : ℕ} {e : ℤ} (ν : Measure (GR n)) (μK : Measure (KR n)) {β : M2 n → ℝ}

theorem twC (hβs : HasCompactSupport β) : IsCompact ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) :=
  isCompact_preimage_mR (tw_support m e μK hβs)

theorem tw_zero_off {u : GR n} (hu : u ∉ (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) : tw m e μK β (mR u) = 0 :=
  image_eq_zero_of_notMem_tsupport hu

theorem continuous_twR [IsFiniteMeasure μK] (hβc : Continuous β) : Continuous fun u : GR n => tw m e μK β (mR u) := by
  have hF : Continuous fun k : KR n => (F0 m 0 e (k : GR n))⁻¹ :=
    ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_subtype_val).inv₀
      (fun k => Vac.spherical_section_ne_zero detU1 m 0 e _)
  have hc : Continuous (Function.uncurry fun (X : M2 n) (k : KR n) =>
      (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * X) : ℂ)) := by
    refine (hF.comp continuous_snd).mul (Complex.continuous_ofReal.comp (hβc.comp ?_))
    exact ((continuous_mR.comp (continuous_subtype_val.comp continuous_snd)).matrix_conjTranspose).matrix_mul
      continuous_fst
  have h := continuous_parametric_integral_of_continuous (μ := μK) hc isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h.comp continuous_mR

theorem integral_restrict_C (F : GR n → ℂ) (hF : ∀ u, u ∉ (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β) → F u = 0) :
    ∫ u, F u ∂ν = ∫ u, F u ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

theorem cw_differentiable [ν.IsHaarMeasure] [μK.IsHaarMeasure] (hβc : Continuous β) (hβs : HasCompactSupport β) :
    Differentiable ℂ fun w => cw m e ν μK β w := by
  have hC := twC (m := m) (e := e) μK hβs
  haveI : IsFiniteMeasure (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
    isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have key := holParam (GR n) (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)))
    ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) hC
    (by rw [Measure.restrict_apply' hC.isClosed.measurableSet]; simp) univ
    (fun u w => phi m e w u * tw m e μK β (mR u)) isOpen_univ
    (by
      refine Continuous.continuousOn ?_
      exact ((continuous_phi₂ m e).comp (continuous_fst.prodMk continuous_snd)).mul
        (hcont.comp continuous_fst))
    (fun u _ => ((differentiable_phi m e u).mul_const _).differentiableOn)
  have heq : (fun w => cw m e ν μK β w) =
      fun w => ∫ u, phi m e w u * tw m e μK β (mR u) ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) := by
    funext w
    exact integral_restrict_C ν μK _ (fun u hu => by rw [tw_zero_off μK hu, mul_zero])
  rw [heq]
  exact differentiableOn_univ.mp key.1

end

section Glob

variable {m : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ}
  {U : Set ℂ} {d : Polynomial ℂ} {Ê : ℂ → G → ℂ} {t : ℝ}

theorem lhs_diff (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β)
    (g : G) (y : GR n) : DifferentiableOn ℂ (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) U := by
  have hC := twC (m := m) (e := e) μK hβs
  haveI : IsFiniteMeasure (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
    isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have hmap : Continuous fun q : GR n × ℂ => (q.2, g * ι (y * q.1)) :=
    continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp (continuous_const.mul continuous_fst)))
  have key := holParam (GR n) (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)))
    ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) hC
    (by rw [Measure.restrict_apply' hC.isClosed.measurableSet]; simp) U
    (fun u z => Ê z (g * ι (y * u)) * tw m e μK β (mR u)) hD.hU
    (by
      refine ContinuousOn.mul ?_ (hcont.comp continuous_fst).continuousOn
      refine hD.cont.comp hmap.continuousOn ?_
      intro q hq
      exact ⟨hq.2, mem_univ _⟩)
    (fun u _ => (hD.hol (g * ι (y * u))).mul_const _)
  have heq : (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) =
      fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u)
        ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) := by
    funext z
    exact integral_restrict_C ν μK _ (fun u hu => by rw [tw_zero_off μK hu, mul_zero])
  rw [heq]
  exact key.1

theorem term_rep (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (w : ℂ) (g : G) (q : GlobalTheory.Eis.Cosets Pp Γ) :
    ∃ (c : ℂ) (y₀ : GR n), ∀ v : GR n,
      GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ w * f x) (g * ι v) q = c * phi m e w (y₀ * v) := by
  obtain ⟨x₀, y₀, S, r, hr, hxy, hp⟩ := hD.split (((q.out : Γ) : G) * g)
  refine ⟨(r : ℂ) ^ w * S, y₀, fun v => ?_⟩
  have e1 : ((q.out : Γ) : G) * (g * ι v) = x₀ * ι (y₀ * v) := by rw [← mul_assoc, hxy, map_mul, mul_assoc]
  show ((Ht (((q.out : Γ) : G) * (g * ι v)) : ℝ) : ℂ) ^ w * f (((q.out : Γ) : G) * (g * ι v)) = _
  rw [e1, (hp (y₀ * v)).1, (hp (y₀ * v)).2, phi, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_nonneg' _)]
  ring

theorem conv_far (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β)
    (z : ℂ) (hz : t < z.re) (g : G) (y : GR n) :
    ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
  obtain ⟨hfar, hE⟩ := hD.far z hz
  set Φ : G → ℂ := fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x with hΦ
  set C := (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β) with hCdef
  have hC : IsCompact C := twC μK hβs
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  haveI : IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have hι : Continuous fun u : GR n => g * ι (y * u) :=
    continuous_const.mul (hD.ιc.comp (continuous_const.mul continuous_id))
  obtain ⟨b, hb, hbd⟩ := hfar (insert (g * ι y) ((fun u => g * ι (y * u)) '' C)) ((hC.image hι).insert _)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  haveI : Countable (Function.support b) := hb.countable_support.to_subtype
  have hmemC : ∀ u ∈ C, g * ι (y * u) ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C) :=
    fun u hu => mem_insert_of_mem _ ⟨u, hu, rfl⟩
  have hzero : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C), ∀ q,
      q ∉ Function.support b → GlobalTheory.Eis.term Pp Γ Φ h q = 0 := by
    intro h hh q hq
    have h1 := hbd h hh q
    rw [Function.notMem_support.mp hq] at h1
    exact norm_le_zero_iff.mp h1
  have hsum_eq : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C),
      GlobalTheory.Eis.cosetSum Pp Γ Φ h = ∑' q : Function.support b, GlobalTheory.Eis.term Pp Γ Φ h q := by
    intro h hh
    unfold GlobalTheory.Eis.cosetSum
    exact (tsum_subtype_eq_of_support_subset
      (fun q hq => by_contra fun hq' => hq (hzero h hh q hq'))).symm
  have hsumm : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C),
      Summable fun q : Function.support b => GlobalTheory.Eis.term Pp Γ Φ h q :=
    fun h hh => Summable.of_norm_bounded (hb.subtype _) (fun q => hbd h hh q)
  have hvan : ∀ F : GR n → ℂ, ∀ u, u ∉ C → F u * tw m e μK β (mR u) = 0 :=
    fun F u hu => by rw [tw_zero_off μK hu, mul_zero]
  have hrep : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, ∃ (c : ℂ) (y₀ : GR n), ∀ v : GR n,
      GlobalTheory.Eis.term Pp Γ Φ (g * ι v) q = c * phi m e (z - s₀) (y₀ * v) := by
    intro q
    obtain ⟨c, y₀, hc⟩ := term_rep hD (z - s₀) g q
    exact ⟨c, y₀, fun v => by rw [hΦ]; exact hc v⟩
  have hterm : ∀ q : GlobalTheory.Eis.Cosets Pp Γ,
      ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂ν =
        cw m e ν μK β (z - s₀) * GlobalTheory.Eis.term Pp Γ Φ (g * ι y) q := by
    intro q
    obtain ⟨c, y₀, hc⟩ := hrep q
    simp only [hc, mul_assoc c]
    rw [integral_const_mul]
    simp only [← mul_assoc y₀ y]
    rw [conv_phi]
    ring
  have hmeas : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, AEStronglyMeasurable
      (fun u => GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u)) (ν.restrict C) := by
    intro q
    obtain ⟨c, y₀, hc⟩ := hrep q
    have hcq : Continuous fun u : GR n =>
        c * phi m e (z - s₀) (y₀ * (y * u)) * tw m e μK β (mR u) :=
      (continuous_const.mul ((continuous_phi m e (z - s₀)).comp
        (continuous_const.mul (continuous_const.mul continuous_id)))).mul hcont
    simp only [hc]
    exact hcq.aestronglyMeasurable
  have hHas : HasSum
      (fun q : Function.support b =>
        ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂(ν.restrict C))
      (∫ u, (∑' q : Function.support b, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q) *
        tw m e μK β (mR u) ∂(ν.restrict C)) := by
    refine hasSum_integral_of_dominated_convergence (fun q _ => b q * M) (fun q => hmeas q) ?_ ?_ ?_ ?_
    · intro q
      filter_upwards [ae_restrict_mem hCm] with u hu
      rw [norm_mul]
      have h1 := hbd _ (hmemC u hu) q
      exact mul_le_mul h1 (hM u hu) (norm_nonneg _) ((norm_nonneg _).trans h1)
    · exact Eventually.of_forall fun _ => (hb.subtype _).mul_right M
    · exact integrable_const _
    · filter_upwards [ae_restrict_mem hCm] with u hu
      exact (hsumm _ (hmemC u hu)).hasSum.mul_right _
  calc ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν
      = ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂(ν.restrict C) :=
        integral_restrict_C ν μK _ (hvan _)
    _ = ∫ u, Polynomial.eval z d * ((∑' q : Function.support b,
          GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q) * tw m e μK β (mR u)) ∂(ν.restrict C) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem hCm] with u hu
        rw [hE, hsum_eq _ (hmemC u hu)]
        ring
    _ = Polynomial.eval z d * ∑' q : Function.support b,
          ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂(ν.restrict C) := by
        rw [integral_const_mul, hHas.tsum_eq]
    _ = Polynomial.eval z d * ∑' q : Function.support b,
          cw m e ν μK β (z - s₀) * GlobalTheory.Eis.term Pp Γ Φ (g * ι y) q := by
        congr 1
        refine tsum_congr fun q => ?_
        rw [← integral_restrict_C ν μK _ (hvan _), hterm]
    _ = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
        rw [tsum_mul_left, hE, hsum_eq _ (mem_insert _ _)]
        ring

theorem conv_U (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β) :
    ∀ z ∈ U, ∀ (g : G) (y : GR n),
      ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
  intro z hz g y
  obtain ⟨σ, hσ⟩ := hD.hR.1
  have hz0U : (((max σ t + 1 : ℝ)) : ℂ) ∈ U := by
    apply hσ
    simp only [GlobalTheory.Cont.rightOf, mem_setOf_eq, Complex.ofReal_re]
    linarith [le_max_left σ t]
  have hL : AnalyticOnNhd ℂ (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) U :=
    (lhs_diff hD ν μK hβc hβs g y).analyticOnNhd hD.hU
  have hdc : Differentiable ℂ fun z : ℂ => cw m e ν μK β (z - s₀) :=
    (cw_differentiable ν μK hβc hβs).comp (differentiable_id.sub_const s₀)
  have hR : AnalyticOnNhd ℂ (fun z => cw m e ν μK β (z - s₀) * Ê z (g * ι y)) U :=
    (hdc.differentiableOn.mul (hD.hol _)).analyticOnNhd hD.hU
  have hev : (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) =ᶠ[𝓝 (((max σ t + 1 : ℝ)) : ℂ)]
      (fun z => cw m e ν μK β (z - s₀) * Ê z (g * ι y)) := by
    have hopen : IsOpen {w : ℂ | t < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (((max σ t + 1 : ℝ)) : ℂ) ∈ {w : ℂ | t < w.re} := by
      simp only [mem_setOf_eq, Complex.ofReal_re]
      linarith [le_max_right σ t]
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact conv_far hD ν μK hβc hβs w hw g y
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR hD.hR.isPreconnected hz0U hev hz

end Glob

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.MI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Z1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def Z2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

theorem curve_zero (x Y : M2 n) : x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = x := by
  simp

theorem rC_eq (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) :
    rC Z F x = deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z1 Z))) 0 +
      Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z2 Z))) 0 := rfl

theorem deriv_curve_of_hasFDerivAt {F : M2 n → ℂ} {D : M2 n →L[ℝ] ℂ} {x : M2 n} (hF : HasFDerivAt F D x) (Y : M2 n) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 = D (x * Y) := by
  exact (hF.comp_hasDerivAt_of_eq 0 (hasDerivAt_curve x Y) (curve_zero x Y).symm).deriv

theorem rC_of_diff {F : M2 n → ℂ} {x : M2 n} (hF : DifferentiableAt ℝ F x) (Z : M2 n) :
    rC Z F x = fderiv ℝ F x (x * Z1 Z) + Complex.I * fderiv ℝ F x (x * Z2 Z) := by
  rw [rC_eq, deriv_curve_of_hasFDerivAt hF.hasFDerivAt, deriv_curve_of_hasFDerivAt hF.hasFDerivAt]

theorem rC_congr {F F' : M2 n → ℂ} {O : Set (M2 n)} (hO : IsOpen O) {x : M2 n} (hx : x ∈ O) (h : EqOn F F' O)
    (Z : M2 n) : rC Z F x = rC Z F' x := by
  have key : ∀ Y : M2 n, deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      deriv (fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • Y))) 0 := by
    intro Y
    apply Filter.EventuallyEq.deriv_eq
    have hc := (hasDerivAt_curve x Y).continuousAt
    have hO' : O ∈ 𝓝 (x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) := by
      rw [curve_zero]
      exact hO.mem_nhds hx
    filter_upwards [hc.preimage_mem_nhds hO'] with t ht
    exact h ht
  rw [rC_eq, rC_eq, key, key]

end PositivityTheory.Rg.Sw.HSt.MI
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure]
  {β : M2 n → ℝ} (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)

def Psi (β : M2 n → ℝ) (h : GR n → ℂ) (x : M2 n) : ℂ := ∫ u, h u • kk m e μK β (x, mR u) ∂ν

def Lk (β : M2 n → ℝ) (Z x₀ : M2 n) (u : GR n) : ℂ :=
  fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ (x₀ * Z1 Z) +
    Complex.I * fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ (x₀ * Z2 Z)

include hβ hβs in
theorem good (h : GR n → ℂ) (hh : Continuous h) :
    PCD.Good (Inv n) (fun x u => h u • kk m e μK β (x, mR u)) :=
  PCD.good_of_joint isOpen_Inv _ (kk_contDiffOn m e μK hβ) (fun u : GR n => mR u) continuous_mR h hh
    (kk_supp m e μK hβs)

include hβ hβs in
theorem psi_contDiffOn (h : GR n → ℂ) (hh : Continuous h) : ContDiffOn ℝ ∞ (Psi m e ν μK β h) (Inv n) :=
  PCD.contDiffOn_integral isOpen_Inv ν (good m e μK hβ hβs h hh)

include hβ in
theorem kk_diff {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) (u : GR n) :
    DifferentiableAt ℝ (fun x' => kk m e μK β (x', mR u)) x₀ := by
  have hsl : ContDiffOn ℝ ∞ (fun x' => kk m e μK β (x', mR u)) (Inv n) :=
    (kk_contDiffOn m e μK hβ).comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  exact (hsl.differentiableOn (by simp) x₀ hx₀).differentiableAt (isOpen_Inv.mem_nhds hx₀)

include hβ hβs in
theorem rC_psi (h : GR n → ℂ) (hh : Continuous h) (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) :
    rC Z (Psi m e ν μK β h) x₀ = ∫ u, h u * Lk m e μK β Z x₀ u ∂ν := by
  have hG := good m e μK hβ hβs h hh
  have hF := hG.hasFDerivAt isOpen_Inv ν hx₀
  have hI := (hG.dK isOpen_Inv).integrable ν hx₀
  have hfd : ∀ u, fderiv ℝ (fun x => h u • kk m e μK β (x, mR u)) x₀ =
      h u • fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ := fun u =>
    fderiv_const_smul (kk_diff m e μK hβ hx₀ u) (h u)
  rw [show Psi m e ν μK β h = fun x => ∫ u, h u • kk m e μK β (x, mR u) ∂ν from rfl]
  rw [rC_of_diff hF.differentiableAt]
  erw [hF.fderiv, ContinuousLinearMap.integral_apply hI, ContinuousLinearMap.integral_apply hI]
  have i1 := hI.apply_continuousLinearMap (x₀ * Z1 Z)
  have i2 := hI.apply_continuousLinearMap (x₀ * Z2 Z)
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  erw [hfd u]
  change h u • (fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀) (x₀ * Z1 Z) +
    Complex.I * (h u • (fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀) (x₀ * Z2 Z)) = _
  simp only [Lk, smul_eq_mul]
  ring

include hβ in
theorem slice_fderiv {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) (v : M2 n) :
    fderiv ℝ (fun x' => kk m e μK β (x', v)) x₀ = (fderiv ℝ (kk m e μK β) (x₀, v)).comp (ContinuousLinearMap.inl ℝ (M2 n) (M2 n)) := by
  have hS : IsOpen (Inv n ×ˢ (univ : Set (M2 n))) := isOpen_Inv.prod isOpen_univ
  have hd : DifferentiableAt ℝ (kk m e μK β) (x₀, v) :=
    ((kk_contDiffOn m e μK hβ).differentiableOn (by simp) _ ⟨hx₀, mem_univ _⟩).differentiableAt
      (hS.mem_nhds ⟨hx₀, mem_univ _⟩)
  have hi : HasFDerivAt (fun x' : M2 n => (x', v)) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n)) x₀ :=
    (hasFDerivAt_id x₀).prodMk (hasFDerivAt_const v x₀)
  exact (hd.hasFDerivAt.comp x₀ hi).fderiv

include hβ in
theorem Lk_cont (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) : Continuous (Lk m e μK β Z x₀) := by
  have hS : IsOpen (Inv n ×ˢ (univ : Set (M2 n))) := isOpen_Inv.prod isOpen_univ
  have hc : ContinuousOn (fun p => fderiv ℝ (kk m e μK β) p) (Inv n ×ˢ univ) :=
    (kk_contDiffOn m e μK hβ).continuousOn_fderiv_of_isOpen hS (by simp)
  have hc' : Continuous fun u : GR n => fderiv ℝ (kk m e μK β) (x₀, mR u) :=
    hc.comp_continuous (continuous_const.prodMk continuous_mR) fun u => ⟨hx₀, mem_univ _⟩
  have e1 : Lk m e μK β Z x₀ = fun u => fderiv ℝ (kk m e μK β) (x₀, mR u) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n) (x₀ * Z1 Z)) +
      Complex.I * fderiv ℝ (kk m e μK β) (x₀, mR u) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n) (x₀ * Z2 Z)) := by
    funext u
    simp only [Lk, slice_fderiv m e μK hβ hx₀, ContinuousLinearMap.comp_apply]
  rw [e1]
  exact (hc'.clm_apply continuous_const).add (continuous_const.mul (hc'.clm_apply continuous_const))

omit [μK.IsHaarMeasure] in
include hβs in
theorem Lk_zero (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) :
    ∃ C : Set (GR n), IsCompact C ∧ ∀ u ∉ C, Lk m e μK β Z x₀ u = 0 := by
  obtain ⟨W, hW, C, hC, hz⟩ := kk_supp m e μK hβs x₀ hx₀
  refine ⟨C, hC, fun u hu => ?_⟩
  have h0 : (fun x' => kk m e μK β (x', mR u)) =ᶠ[𝓝 x₀] fun _ => 0 := by
    filter_upwards [hW] with x' hx' using hz x' hx' u hu
  simp [Lk, h0.fderiv_eq]

end

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {n m : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ}
  {U : Set ℂ} {d : Polynomial ℂ} {Ê : ℂ → G → ℂ} {t : ℝ}

private theorem taylor_cont_lemma {X : Type} [TopologicalSpace X] {U : Set ℂ} (hU : IsOpen U)
    (Φ : X → ℂ → ℂ) (hc : ContinuousOn (fun p : X × ℂ => Φ p.1 p.2) (univ ×ˢ U))
    (hd : ∀ x, DifferentiableOn ℂ (Φ x) U) :
    ContinuousOn (fun p : X × ℂ => deriv (Φ p.1) p.2) (univ ×ˢ U) := by
  rintro ⟨x₀, z₀⟩ ⟨-, hz₀⟩
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have rpos : 0 < ε / 2 := by positivity
  have hsub : Metric.closedBall z₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hε
  set S : Set (X × ℂ) := (univ : Set X) ×ˢ Metric.ball z₀ (ε / 2) with hSdef
  set K : X × ℂ → ℂ := fun p =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(z₀, ε / 2), ((w - p.2) ^ 2)⁻¹ • Φ p.1 w with hKdef
  have heq : ∀ p ∈ S, deriv (Φ p.1) p.2 = K p := fun p hp =>
    (Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hsub (hd p.1)
      hp.2).symm
  have hS : IsOpen S := isOpen_univ.prod Metric.isOpen_ball
  have hmem : (x₀, z₀) ∈ S := ⟨trivial, Metric.mem_ball_self rpos⟩
  have hK : ContinuousOn K S := by
    rw [continuousOn_iff_continuous_restrict]
    have hsph : ∀ θ : ℝ, circleMap z₀ (ε / 2) θ ∈ U := fun θ =>
      hsub (Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ rpos.le θ))
    have h3 : Continuous (fun q : S × ℝ => Φ q.1.1.1 (circleMap z₀ (ε / 2) q.2)) := by
      have := hc.comp_continuous (f := fun q : S × ℝ => (q.1.1.1, circleMap z₀ (ε / 2) q.2))
        (by fun_prop) (fun q => ⟨trivial, hsph q.2⟩)
      exact this
    have h2 : Continuous (fun q : S × ℝ => ((circleMap z₀ (ε / 2) q.2 - q.1.1.2) ^ 2)⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) ?_
      intro q h
      have hq : q.1.1.2 ∈ Metric.ball z₀ (ε / 2) := q.1.2.2
      have h0 : circleMap z₀ (ε / 2) q.2 = q.1.1.2 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
      have hs := circleMap_mem_sphere z₀ rpos.le q.2
      rw [h0] at hs
      rw [Metric.mem_sphere] at hs
      rw [Metric.mem_ball] at hq
      linarith
    have h1 : Continuous (fun q : S × ℝ => deriv (circleMap z₀ (ε / 2)) q.2) := by
      simp only [deriv_circleMap]
      fun_prop
    have hI := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun (q : S) (θ : ℝ) => deriv (circleMap z₀ (ε / 2)) θ •
        ((circleMap z₀ (ε / 2) θ - q.1.2) ^ 2)⁻¹ • Φ q.1.1 (circleMap z₀ (ε / 2) θ))
      (h1.smul (h2.smul h3)) 0 (2 * Real.pi)
    have hI2 := (continuous_const (y := (2 * Real.pi * Complex.I : ℂ)⁻¹)).mul hI
    convert hI2 using 1
    funext q
    simp only [Set.restrict_apply, hKdef, circleIntegral, smul_eq_mul, Pi.mul_apply]
  have hat : ContinuousAt (fun p : X × ℂ => deriv (Φ p.1) p.2) (x₀, z₀) := by
    refine (hK.continuousAt (hS.mem_nhds hmem)).congr ?_
    filter_upwards [hS.mem_nhds hmem] with p hp using (heq p hp).symm
  exact hat.continuousWithinAt

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] in
theorem taylor_cont (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) : ∀ r : ℕ,
    ContinuousOn (fun y : G × ℂ => iteratedDeriv r (Ê · y.1) y.2) (univ ×ˢ U) ∧
      ∀ x, DifferentiableOn ℂ (iteratedDeriv r (Ê · x)) U := by
  intro r
  induction r with
  | zero =>
    simp only [iteratedDeriv_zero]
    refine ⟨?_, fun x => hD.hol x⟩
    exact hD.cont.comp (continuous_swap.continuousOn) (fun y hy => ⟨hy.2, trivial⟩)
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    exact ⟨taylor_cont_lemma hD.hU _ ih.1 ih.2, fun x => (ih.2 x).deriv hD.hU⟩

end

theorem gset_inv {n : ℕ} {x : M2 n} (hx : InG x) : x ∈ Inv n := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hJ : JJ n * JJ n = -1 := by
    simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  have hl : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have e : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x) := by simp only [Matrix.mul_assoc]
    rw [neg_mul, e, hx', hJ, neg_neg]
  exact Matrix.det_ne_zero_of_left_inverse hl

theorem mR_inv {n : ℕ} (y : GR n) : (mR y)⁻¹ = mR y⁻¹ := by
  simp [mR, Matrix.coe_units_inv]

theorem smoothX : SmoothX := by
  intro m n e _ _ G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD g
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (GR n), ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨μK, hμK⟩ : ∃ μ : Measure (KR n), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨β, hβs, hβc, hβ0⟩ := exists_bump m e ν μK
  have hmR : Continuous (fun u : GR n => mR u) := Units.continuous_val.comp continuous_subtype_val
  have hcont : ∀ z ∈ U, Continuous (fun u : GR n => Ê z (g * ι u)) := by
    intro z hz
    have := hD.cont.comp_continuous (f := fun u : GR n => (z, g * ι u))
      (continuous_const.prodMk (continuous_const.mul hD.ιc)) (fun u => ⟨hz, trivial⟩)
    exact this
  have hcont' : ∀ r : ℕ, Continuous (fun u : GR n => iteratedDeriv r (Ê · (g * ι u)) s₀) := by
    intro r
    have := (taylor_cont hD r).1.comp_continuous (f := fun u : GR n => (g * ι u, s₀))
      ((continuous_const.mul hD.ιc).prodMk continuous_const) (fun u => ⟨trivial, hD.hs⟩)
    exact this
  have hmc : ∀ (a : ℂ → ℂ) (c z : ℂ) (r : ℕ),
      iteratedDeriv r (fun w => a w * c) z = iteratedDeriv r a z * c := by
    intro a c z r
    have hfun : (fun w => a w * c) = (fun w => c * a w) := funext fun w => mul_comm _ _
    rw [hfun, iteratedDeriv_const_mul_field, mul_comm]
  have hloc : ∀ (f₁ f₂ : ℂ → ℂ) (r : ℕ), (∀ z ∈ U, f₁ z = f₂ z) →
      iteratedDeriv r f₁ s₀ = iteratedDeriv r f₂ s₀ := by
    intro f₁ f₂ r hf
    have hev : f₁ =ᶠ[𝓝[univ] s₀] f₂ := by
      rw [nhdsWithin_univ]
      exact Filter.eventually_of_mem (hD.hU.mem_nhds hD.hs) hf
    have := Filter.EventuallyEq.iteratedDerivWithin_eq (n := r) hev (hf s₀ hD.hs)
    simpa only [iteratedDerivWithin_univ] using this
  have key : ∀ x ∈ MI.Inv n,
      DifferentiableOn ℂ (fun z => Psi m e ν μK β (fun u => Ê z (g * ι u)) x) U ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => Psi m e ν μK β (fun u => Ê z (g * ι u)) x) s₀ =
        Psi m e ν μK β (fun u => iteratedDeriv r (Ê · (g * ι u)) s₀) x := by
    intro x hx
    obtain ⟨W, hW, C, hC, hCz⟩ := kk_supp m e μK hβc x hx
    have hk0 : Continuous (fun u : GR n => x⁻¹ * mR u) := continuous_const.mul hmR
    have hk : Continuous (fun u : GR n => kk m e μK β (x, mR u)) :=
      (tw_contDiff m e μK hβs).continuous.comp hk0
    have hI := holInt ν hC hD.hU (fun u z => Ê z (g * ι u) • kk m e μK β (x, mR u))
      (fun u hu z => by simp [hCz x (mem_of_mem_nhds hW) u hu])
      (by
        have h1 : ContinuousOn (fun p : GR n × ℂ => Ê p.2 (g * ι p.1)) (C ×ˢ U) :=
          hD.cont.comp ((continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp continuous_fst))).continuousOn)
            (fun p hp => ⟨hp.2, trivial⟩)
        exact h1.smul (hk.comp continuous_fst).continuousOn)
      (fun u _ => (hD.hol (g * ι u)).smul_const _)
    refine ⟨hI.1, fun r => ?_⟩
    simp only [Psi]
    rw [hI.2 s₀ hD.hs r]
    simp only [smul_eq_mul]
    congr 1
    funext u
    exact hmc _ _ _ _
  refine ⟨fun z x => Psi m e ν μK β (fun u => Ê z (g * ι u)) x, MI.Inv n,
    fun z => cw m e ν μK β (z - s₀), MI.isOpen_Inv, fun x hx => gset_inv hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((cw_differentiable ν μK hβs.continuous hβc).comp (differentiable_id.sub_const s₀)).differentiableOn
  · simpa using hβ0
  · intro z hz y
    simp only [Psi, kk, smul_eq_mul]
    rw [← integral_mul_left_eq_self _ y]
    have := conv_U hD ν μK hβs.continuous hβc z hz g y
    rw [← this]
    congr 1
    funext u
    rw [mR_inv, ← mR_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro z hz
    exact psi_contDiffOn m e ν μK hβs hβc _ (hcont z hz)
  · intro r
    exact (psi_contDiffOn m e ν μK hβs hβc _ (hcont' r)).congr (fun x hx => (key x hx).2 r)
  · intro x hx
    exact (key x hx).1
  · intro Q y
    have hx₀ : mR y ∈ MI.Inv n := gset_inv y.2
    obtain ⟨C, hC, hCz⟩ := Lk_zero m e μK hβc (lowQ Q) hx₀
    have hL := Lk_cont m e μK hβs (lowQ Q) hx₀
    have hI := holInt ν hC hD.hU (fun u z => Ê z (g * ι u) * Lk m e μK β (lowQ Q) (mR y) u)
      (fun u hu z => by simp [hCz u hu])
      (by
        have h1 : ContinuousOn (fun p : GR n × ℂ => Ê p.2 (g * ι p.1)) (C ×ˢ U) :=
          hD.cont.comp ((continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp continuous_fst))).continuousOn)
            (fun p hp => ⟨hp.2, trivial⟩)
        exact h1.mul (hL.comp continuous_fst).continuousOn)
      (fun u _ => (hD.hol (g * ι u)).mul_const _)
    have hrc : ∀ z ∈ U, rC (lowQ Q) (Psi m e ν μK β (fun u => Ê z (g * ι u))) (mR y) =
        ∫ u, Ê z (g * ι u) * Lk m e μK β (lowQ Q) (mR y) u ∂ν := by
      intro z hz
      exact rC_psi m e ν μK hβs hβc (fun u => Ê z (g * ι u)) (hcont z hz) (lowQ Q) hx₀
    refine ⟨hI.1.congr hrc, fun r => ?_⟩
    rw [hloc _ _ r hrc, hI.2 s₀ hD.hs r]
    rw [MI.rC_congr MI.isOpen_Inv hx₀ (fun x hx => (key x hx).2 r) (lowQ Q),
      rC_psi m e ν μK hβs hβc _ (hcont' r) (lowQ Q) hx₀]
    congr 1
    funext u
    exact hmc _ _ _ _

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section
namespace PositivityTheory.Rg.Sw.HSt

theorem asmH : AsmH :=
  asmH_of farId Conv.smoothX topHol rcCongr (fun _ x Z t hx => expLie x Z t hx)

end PositivityTheory.Rg.Sw.HSt
end
