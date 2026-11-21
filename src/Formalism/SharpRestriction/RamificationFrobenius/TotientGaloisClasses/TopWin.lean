import Formalism.SharpRestriction.FamCore
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Formalism.ZetaNonvanishing.ZetaLandau
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window

section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism.HC.Landau

open Formalism ArithmeticFunction

theorem logDerivResidue' : LogDerivResidue := by
  intro f ρ hf ⟨z, hz⟩
  have hfa : ∀ w, AnalyticAt ℂ f w := fun w => hf.analyticAt w
  have hne : analyticOrderAt f ρ ≠ ⊤ := by
    rw [Ne, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ hfa]
    intro h
    exact hz (by simp [h])
  set m := analyticOrderNatAt f ρ with hm
  obtain ⟨g, hga, hgρ, hfg⟩ := ((hfa ρ).analyticOrderNatAt_eq_iff hne (n := m)).mp rfl
  have hfg' : f =ᶠ[𝓝 ρ] fun s => (s - ρ) ^ m * g s := by
    filter_upwards [hfg] with s hs
    simpa using hs
  have hderiv : deriv f =ᶠ[𝓝 ρ] deriv (fun s => (s - ρ) ^ m * g s) := hfg'.deriv
  have hgan : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ g s := hga.eventually_analyticAt
  have hgne : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hga.continuousAt.eventually_ne hgρ
  have key : (fun s => (m : ℂ) + (s - ρ) * (deriv g s / g s)) =ᶠ[𝓝[≠] ρ]
      fun s => (s - ρ) * (deriv f s / f s) := by
    have h1 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ ρ := self_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds hfg', nhdsWithin_le_nhds hderiv,
      nhdsWithin_le_nhds hgan, nhdsWithin_le_nhds hgne, h1] with s hfs hds hgs hgs0 hsρ
    have hsub : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
    have hd : deriv (fun s => (s - ρ) ^ m * g s) s =
        (m : ℂ) * (s - ρ) ^ (m - 1) * g s + (s - ρ) ^ m * deriv g s := by
      have h2 : HasDerivAt (fun s => (s - ρ) ^ m) ((m : ℂ) * (s - ρ) ^ (m - 1)) s := by
        simpa using ((hasDerivAt_id s).sub_const ρ).fun_pow m
      exact (h2.mul hgs.differentiableAt.hasDerivAt).deriv
    rw [hds, hfs, hd]
    have hpow : (s - ρ) * (s - ρ) ^ (m - 1) * (m : ℂ) = (m : ℂ) * (s - ρ) ^ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · simp [h0]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [hk]; simp [pow_succ]; ring
    have hpm : (s - ρ) ^ m ≠ 0 := pow_ne_zero _ hsub
    field_simp
    linear_combination (-(g s)) * hpow
  refine Tendsto.congr' key ?_
  have hdg : ContinuousAt (deriv g) ρ := hga.deriv.continuousAt
  have hlim : Tendsto (fun s => (m : ℂ) + (s - ρ) * (deriv g s / g s)) (𝓝 ρ)
      (𝓝 ((m : ℂ) + (ρ - ρ) * (deriv g ρ / g ρ))) := by
    refine tendsto_const_nhds.add ?_
    exact ((continuous_id.sub continuous_const).continuousAt.tendsto).mul
      (hdg.tendsto.div hga.continuousAt.tendsto hgρ)
  simpa using hlim.mono_left nhdsWithin_le_nhds

lemma natOrder_ne_zero' {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z y : ℂ} (hy : f y ≠ 0)
    (hz : f z = 0) : analyticOrderNatAt f z ≠ 0 := by
  have han : AnalyticOnNhd ℂ f univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have h0 : analyticOrderAt f z ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨han z trivial, hz⟩
  have htop : analyticOrderAt f z ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ y) (mem_univ z)
      (by rw [analyticOrderAt_eq_zero.mpr (Or.inr hy)]; simp)
  simp only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
  exact ⟨h0, htop⟩

lemma integral_real' (H : ℝ → ℝ) (σ : ℝ) :
    ∫ x in Ioi (1:ℝ), ((H x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ x in Ioi (1:ℝ), H x * x ^ (-σ - 1) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 ≤ x := by linarith [mem_Ioi.mp hx]
  simp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0]
  push_cast
  ring_nf

def AP (P : ℂ → ℂ) (a b : ℂ) (s : ℂ) : ℂ := deriv P s - (a + b * s) * P s

def PhiP (P : ℂ → ℂ) (a b : ℂ) (C θ : ℝ) (s : ℂ) : ℂ := dslope (AP P a b) 1 s / (s * P s) + C / (s - θ)

lemma differentiable_AP {P : ℂ → ℂ} (hP : Differentiable ℂ P) (a b : ℂ) : Differentiable ℂ (AP P a b) := by
  have hP' := differentiable_deriv_of hP
  unfold AP
  fun_prop

lemma PhiP_eq {P : ℂ → ℂ} {a b : ℂ} {C θ : ℝ} (hA : AP P a b 1 = 0) {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hZ : P s ≠ 0) :
    PhiP P a b C θ s = (deriv P s / P s - (a + b * s)) / (s * (s - 1)) + C / (s - θ) := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold PhiP
  rw [dslope_of_ne _ hs1, slope_def_field, hA, sub_zero]
  unfold AP
  field_simp

lemma PhiP_analyticAt {P : ℂ → ℂ} (hP : Differentiable ℂ P) (a b : ℂ) (C θ : ℝ) {s : ℂ} (hs0 : s ≠ 0)
    (hE : P s ≠ 0) (hsθ : s ≠ θ) : AnalyticAt ℂ (PhiP P a b C θ) s := by
  set V : Set ℂ := {z | z ≠ 0 ∧ P z ≠ 0 ∧ z ≠ θ} with hV
  have hVo : IsOpen V :=
    isOpen_ne.inter ((isOpen_ne_fun hP.continuous continuous_const).inter isOpen_ne)
  have hdsl : DifferentiableOn ℂ (dslope (AP P a b) 1) univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr (differentiable_AP hP a b).differentiableOn
  have hd : DifferentiableOn ℂ (PhiP P a b C θ) V := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (dslope (AP P a b) 1) z :=
      (hdsl z (mem_univ z)).differentiableAt Filter.univ_mem
    have h2 : DifferentiableAt ℂ P z := hP z
    unfold PhiP
    apply DifferentiableAt.add
    · exact h1.div (differentiableAt_id.mul h2) (mul_ne_zero hz.1 hz.2.1)
    · exact (differentiableAt_const _).div (differentiableAt_id.sub_const _)
        (sub_ne_zero.mpr hz.2.2)
  exact hd.analyticAt (hVo.mem_nhds ⟨hs0, hE, hsθ⟩)

theorem landau_entire (P : ℂ → ℂ) (hP : Differentiable ℂ P) (hP1 : ∀ s : ℂ, 1 ≤ s.re → P s ≠ 0) (a b : ℂ)
    (hA : AP P a b 1 = 0) (H : ℝ → ℝ) (hm : Measurable H) (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hI : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (C θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hM : ∀ s : ℂ, 1 < s.re → ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) =
      (deriv P s / P s - (a + b * s)) / (s * (s - 1)) + C / (s - θ)) :
    ∀ s : ℂ, θ < s.re → P s ≠ 0 := by
  have hP10 : P 1 ≠ 0 := hP1 1 (by simp)
  have lan : ∀ α : ℝ, θ ≤ α → α < 1 → (∀ σ : ℝ, α < σ → σ < 1 → P σ ≠ 0) →
      ∀ σ : ℝ, α < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) ∧
        PhiP P a b C θ σ = ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1) := by
    intro α ha ha1 hL
    refine landauEq H α 1 ha1 hm.aestronglyMeasurable (fun x hx => hH x hx.le) hI (PhiP P a b C θ) ?_ ?_ ?_
    · intro s hs
      exact PhiP_analyticAt hP a b C θ (ne_zero_of_lt_re zero_le_one hs) (hP1 s hs.le) (ne_ofReal_of_lt_re (by linarith))
    · intro σ h1' h2'
      have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
      have hσθ : (σ : ℂ) ≠ θ := ofReal_ne_ofReal_of_lt (by linarith)
      refine PhiP_analyticAt hP a b C θ hσ0 ?_ hσθ
      rcases h2'.lt_or_eq with h2' | h2'
      · exact hL σ h1' h2'
      · subst h2'
        simpa using hP10
    · intro s hs
      rw [hM s hs, PhiP_eq hA (ne_one_of_one_lt_re hs) (ne_zero_of_lt_re zero_le_one hs) (hP1 s hs.le)]

  have hreal : ∀ σ : ℝ, θ < σ → σ < 1 → P σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨β0, hβ0, hβ1, hz0⟩ := hcon
    set Pr : ℝ → ℂ := fun σ => P σ with hPr
    have hPc : Continuous Pr := hP.continuous.comp Complex.continuous_ofReal
    set Z : Set ℝ := Icc β0 1 ∩ Pr ⁻¹' {0} with hZ
    have hZc : IsCompact Z := isCompact_Icc.inter_right (isClosed_singleton.preimage hPc)
    have hZne : Z.Nonempty := ⟨β0, ⟨le_rfl, hβ1.le⟩, hz0⟩
    have hbdd : BddAbove Z := hZc.bddAbove
    have hβZ : sSup Z ∈ Z := hZc.sSup_mem hZne
    set β := sSup Z with hβdef
    obtain ⟨⟨hβ0le, hβle1⟩, hβP⟩ := hβZ
    have hβPz : P β = 0 := hβP
    have hβ1' : β < 1 := by
      rcases hβle1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [h] at hβPz
        exact hP10 (by simpa using hβPz)
    have hnz : ∀ σ : ℝ, β < σ → σ < 1 → P σ ≠ 0 := by
      intro σ h1 h2 hz
      have := le_csSup hbdd (show σ ∈ Z from ⟨⟨by linarith, h2.le⟩, hz⟩)
      linarith
    have hβθ : θ < β := by linarith
    have hβ0' : 0 < β := by linarith
    have hLan := lan β hβθ.le hβ1' hnz
    set z : ℂ := (β : ℂ) with hb
    have hbθ : z - (θ : ℂ) ≠ 0 := sub_ne_zero.mpr (ofReal_ne_ofReal_of_lt hβθ)
    have hb0 : z ≠ 0 := by rw [hb]; exact_mod_cast hβ0'.ne'
    have hb1 : z - 1 ≠ 0 := sub_ne_zero.mpr (ofReal_ne_one_of_lt hβ1')
    set m : ℕ := analyticOrderNatAt P z with hmdef
    have hlL : Tendsto (fun s => (s - z) * (deriv P s / P s)) (𝓝[≠] z) (𝓝 (m : ℂ)) :=
      logDerivResidue' P z hP ⟨1, hP10⟩
    have hlin : Tendsto (fun s => (s - z) * (a + b * s)) (𝓝[≠] z) (𝓝 0) := by
      have hc : Continuous (fun s => (s - z) * (a + b * s)) := by fun_prop
      have := (hc.tendsto z).mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
      simpa using this
    have hden : Tendsto (fun s : ℂ => s * (s - 1)) (𝓝[≠] z) (𝓝 (z * (z - 1))) :=
      ((continuous_id.mul (continuous_id.sub continuous_const)).tendsto z).mono_left
        (nhdsWithin_le_nhds (s := {z}ᶜ))
    have hCt : Tendsto (fun s : ℂ => (C : ℂ) * (s - z) / (s - θ)) (𝓝[≠] z) (𝓝 0) := by
      have hca : ContinuousAt (fun s : ℂ => (C : ℂ) * (s - z) / (s - θ)) z :=
        (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div
          (continuousAt_id.sub continuousAt_const) hbθ
      have := hca.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
      simpa using this
    have hg := ((hlL.sub hlin).div hden (mul_ne_zero hb0 hb1)).add hCt
    have hpath : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] β) (𝓝[≠] z) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto β).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun σ hσ =>
          ofReal_ne_ofReal_of_lt (mem_Ioi.mp hσ))
    have hre := (Complex.continuous_re.tendsto _).comp (hg.comp hpath)
    have hev : ∀ᶠ σ in 𝓝[>] β, 0 ≤ (((fun s : ℂ => ((s - z) * (deriv P s / P s) - (s - z) * (a + b * s))
        / (s * (s - 1)) + (C : ℂ) * (s - z) / (s - θ)) ∘ (fun σ : ℝ => (σ : ℂ))) σ).re := by
      filter_upwards [Ioo_mem_nhdsGT hβ1'] with σ hσ
      obtain ⟨h1, h2⟩ := hσ
      have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
      have hσ1 : (σ : ℂ) ≠ 1 := ofReal_ne_one_of_lt h2
      have hPe := PhiP_eq (C := C) (θ := θ) hA hσ1 hσ0 (hnz σ h1 h2)
      have hPi := (hLan σ h1).2
      rw [integral_real'] at hPi
      have hgσ : (((σ : ℂ) - z) * (deriv P σ / P σ) - ((σ : ℂ) - z) * (a + b * σ))
          / ((σ : ℂ) * ((σ : ℂ) - 1)) + (C : ℂ) * ((σ : ℂ) - z) / ((σ : ℂ) - θ)
          = (((σ - β : ℝ) : ℂ)) * PhiP P a b C θ σ := by
        rw [hPe, hb]
        push_cast
        ring
      simp only [Function.comp_apply]
      rw [hgσ, hPi, ← Complex.ofReal_mul, Complex.ofReal_re]
      refine mul_nonneg (by linarith) (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
      exact mul_nonneg (hH x (le_of_lt (mem_Ioi.mp hx)))
        (Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)
    have hge := ge_of_tendsto hre hev
    have hval : ((m : ℂ) - 0) / (z * (z - 1)) + 0 = ((((m : ℝ)) / (β * (β - 1)) : ℝ) : ℂ) := by
      rw [hb]
      push_cast
      ring
    rw [hval, Complex.ofReal_re] at hge
    have hm1 : m ≠ 0 := natOrder_ne_zero' hP hP10 hβPz
    have hnum : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm1
    have hden' : β * (β - 1) < 0 := mul_neg_of_pos_of_neg hβ0' (by linarith)
    have := div_neg_of_pos_of_neg hnum hden'
    linarith
  have hInt := fun σ hσ => (lan θ le_rfl hθ1 hreal σ hσ).1
  set I : ℂ → ℂ := fun s => ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) with hIdef
  set U : Set ℂ := {s | θ < s.re} with hU_def
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hId : DifferentiableOn ℂ I U := by
    intro s hs
    have hD := mellinDeriv (fun x => ((H x : ℝ) : ℂ)) θ
      (Complex.measurable_ofReal.comp hm).aestronglyMeasurable
      (fun σ hσ => (hInt σ hσ).congr_fun (fun x hx => by
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hH x (le_of_lt (mem_Ioi.mp hx)))])
        measurableSet_Ioi) s hs
    exact hD.differentiableAt.differentiableWithinAt
  have hAd := differentiable_AP hP a b
  have hf1 : DifferentiableOn ℂ (fun s => s * (s - 1) * P s * (I s - C / (s - θ))) U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    have hEs := hP s
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hsθ)
  have hEq : EqOn (fun s => s * (s - 1) * P s * (I s - C / (s - θ))) (AP P a b) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hf1.analyticOnNhd hUopen) (hAd.differentiableOn.analyticOnNhd hUopen)
      (convex_halfSpace_re_gt θ).isPreconnected (z₀ := 2)
      (show θ < (2:ℂ).re by simp; linarith) ?_
    have h2mem : (2:ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2mem] with z hz
    have hz' : 1 < z.re := hz
    have hZ := hP1 z hz'.le
    have hs1' : z - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hz')
    have hs0 : z ≠ 0 := ne_zero_of_lt_re zero_le_one hz'
    have hsθ : z - θ ≠ 0 := sub_ne_zero_of_lt_re (a := θ) (by linarith)
    have e : I z = _ := hM z hz'
    rw [e]
    unfold AP
    field_simp
    ring
  set q : ℂ → ℂ := fun s => (a + b * s) + s * (s - 1) * (I s - C / (s - θ)) with hq_def
  have hqd : DifferentiableOn ℂ q U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    apply DifferentiableAt.differentiableWithinAt
    simp only [hq_def]
    fun_prop (disch := exact hsθ)
  have hid : ∀ s ∈ U, deriv P s = q s * P s := by
    intro s hs
    have he := hEq hs
    simp only at he
    unfold AP at he
    simp only [hq_def]
    linear_combination -he
  intro s hs
  exact logDerivZeroFree P q U hUopen hP ⟨1, hP10⟩ hqd hid s hs

section Family

open DirichletCharacter

variable {N : ℕ} [NeZero N]


lemma lseries_re (ξ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((Λ n * (ξ n).re : ℝ) : ℂ)) s =
      -(deriv (LFunction ξ) s / LFunction ξ s + deriv (LFunction ξ⁻¹) s / LFunction ξ⁻¹ s) / 2 := by
  have hcoef : (fun n : ℕ => ((Λ n * (ξ n).re : ℝ) : ℂ)) =
      (1 / 2 : ℂ) • ((fun n : ℕ => ξ n * ((Λ n : ℝ) : ℂ)) + fun n : ℕ => ξ⁻¹ n * ((Λ n : ℝ) : ℂ)) := by
    funext n
    have hc : ξ⁻¹ (n : ZMod N) = starRingEnd ℂ (ξ n) := by
      rw [← MulChar.star_apply']; rfl
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hc]
    push_cast
    rw [Complex.re_eq_add_conj]
    ring
  have s1 : LSeriesSummable (fun n : ℕ => ξ n * ((Λ n : ℝ) : ℂ)) s := LSeriesSummable_twist_vonMangoldt ξ hs
  have s2 : LSeriesSummable (fun n : ℕ => ξ⁻¹ n * ((Λ n : ℝ) : ℂ)) s := LSeriesSummable_twist_vonMangoldt ξ⁻¹ hs
  have e1 : LSeries (fun n : ℕ => ξ n * ((Λ n : ℝ) : ℂ)) s = _ := LSeries_twist_vonMangoldt_eq ξ hs
  have e2 : LSeries (fun n : ℕ => ξ⁻¹ n * ((Λ n : ℝ) : ℂ)) s = _ := LSeries_twist_vonMangoldt_eq ξ⁻¹ hs
  rw [hcoef, LSeries_smul, LSeries_add s1 s2, e1, e2, LFunction_eq_LSeries ξ hs, LFunction_eq_LSeries ξ⁻¹ hs,
    deriv_LFunction_eq_deriv_LSeries ξ hs, deriv_LFunction_eq_deriv_LSeries ξ⁻¹ hs]
  ring

lemma mellin_Gchi' (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Gchi χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1:ℝ), (Gchi χ x : ℂ) * (x : ℂ) ^ (-s - 1) =
      LSeries (fun n => ((Λ n * (χ n).re : ℝ) : ℂ)) s / (s * (s - 1))
        + (((deriv (LFunction χ) 1 / LFunction χ 1).re : ℝ) : ℂ) * (1 / (s - 1)) := by
  have h5 := mellinElem
  have hS := mellinSgen _ 1 (twist_bound χ)
  have i1 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n * (χ n).re) x : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi 1) := cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  set c : ℝ := (deriv (LFunction χ) 1 / LFunction χ 1).re
  have hfun : (fun x : ℝ => (Gchi χ x : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      (Sa (fun n => Λ n * (χ n).re) x : ℂ) * (x : ℂ) ^ (-s - 1)
        + (c : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [Gchi, Schi_eq_Sa, Real.rpow_one, c]
    push_cast
    ring
  have j3 := Integrable.const_mul i3 (c : ℂ)
  refine ⟨by rw [hfun]; exact i1.add j3, ?_⟩
  rw [hfun, integral_add i1 j3, integral_const_mul, hS.2.2 s hs, h5.2.2.1 1 s (by simpa using hs)]
  push_cast
  ring

lemma lseries_real_im (a : ℕ → ℝ) (σ : ℝ) : (LSeries (fun n => (a n : ℂ)) σ).im = 0 := by
  have : LSeries (fun n => (a n : ℂ)) σ = ((∑' n : ℕ, (if n = 0 then 0 else a n / (n : ℝ) ^ σ) : ℝ) : ℂ) := by
    rw [ofReal_tsum]
    unfold LSeries
    refine tsum_congr fun n => ?_
    rw [LSeries.term_def]
    split_ifs
    · simp
    · rw [ofReal_div, ofReal_cpow (Nat.cast_nonneg n)]; simp
  rw [this, ofReal_im]

lemma Gchi_bdd (χ : DirichletCharacter ℂ N) (X : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → x ≤ X → |Gchi χ x| ≤ B := by
  refine ⟨|X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n| + |(deriv (LFunction χ) 1 / LFunction χ 1).re| * |X|, by positivity,
    fun x h1 hX => ?_⟩
  have hb := (Sz_bound h1 hX).2
  have hS : |Schi χ x| ≤ Sz x := by
    unfold Schi Sz
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn' := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
    have hny : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith))
    have h0 : 0 ≤ x / n - 1 := by rw [sub_nonneg, le_div_iff₀ hn0]; linarith
    rw [abs_mul, abs_of_nonneg h0]
    have := twist_bound χ n
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_right this h0
  unfold Gchi
  refine (abs_add_le _ _).trans (add_le_add (hS.trans (hb.trans (le_abs_self _))) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg (by linarith)]; exact hX.trans (le_abs_self _)) (abs_nonneg _)

set_option maxHeartbeats 1000000 in

theorem landau_family {ι : Type} (c : ι → PChar) (τ : ι → ι) (hτ : ∀ i, τ (τ i) = i) (hτc : ∀ i, c (τ i) = (c i).inv)
    (S : Finset ι) (h1 : ∀ ξ ∈ S, (c ξ).χ ≠ 1) (hinv : ∀ ξ ∈ S, τ ξ ∈ S) (R : ℕ) (hR : R ≠ 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (C0 y0 : ℝ) (hb : ∀ y ≥ y0, R * Gz y + ∑ ξ ∈ S, Gchi (c ξ).χ y ≤ C0 * y ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 ∧ ∀ ξ ∈ S, LFunction (c ξ).χ s ≠ 0 := by
  classical
  have h3 := mellinSgen
  have h5 := mellinElem
  have hLd : ∀ ξ ∈ S, Differentiable ℂ (LFunction (c ξ).χ) := fun ξ h => differentiable_LFunction (h1 ξ h)
  have hL1 : ∀ s : ℂ, 1 ≤ s.re → ∀ ξ ∈ S, LFunction (c ξ).χ s ≠ 0 :=
    fun s hs ξ h => LFunction_ne_zero_of_one_le_re (c ξ).χ (Or.inl (h1 ξ h)) hs
  set P : ℂ → ℂ := fun s => riemannZeta₁ s ^ R * ∏ ξ ∈ S, LFunction (c ξ).χ s with hPdef
  have hZd : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hPr : Differentiable ℂ fun s => ∏ ξ ∈ S, LFunction (c ξ).χ s :=
    fun s => DifferentiableAt.fun_finsetProd fun ξ h => hLd ξ h s
  have hP : Differentiable ℂ P := (hZd.pow R).mul hPr
  have hP1 : ∀ s : ℂ, 1 ≤ s.re → P s ≠ 0 := fun s hs =>
    mul_ne_zero (pow_ne_zero _ (riemannZetaOne_ne_zero_of_one_le_re hs)) (Finset.prod_ne_zero_iff.2 (hL1 s hs))
  set g : ℂ → ℂ := fun s => ∑ ξ ∈ S, deriv (LFunction (c ξ).χ) s / LFunction (c ξ).χ s with hg
  have hlog : ∀ s : ℂ, 1 ≤ s.re → deriv P s / P s = R * (deriv riemannZeta₁ s / riemannZeta₁ s) + g s := by
    intro s hs
    have e := logDeriv_mul (f := fun s => riemannZeta₁ s ^ R) (g := fun s => ∏ ξ ∈ S, LFunction (c ξ).χ s) s
      (pow_ne_zero _ (riemannZetaOne_ne_zero_of_one_le_re hs)) (Finset.prod_ne_zero_iff.2 (hL1 s hs)) ((hZd.pow R) s) (hPr s)
    rw [logDeriv_fun_pow (hZd s), logDeriv_prod (hL1 s hs) (fun ξ h => hLd ξ h s)] at e
    simpa [logDeriv_apply] using e
  have hsumL : ∀ s : ℂ, 1 < s.re → ∑ ξ ∈ S, LSeries (fun n => ((Λ n * ((c ξ).χ n).re : ℝ) : ℂ)) s = -g s := by
    intro s hs
    have hi : ∑ ξ ∈ S, deriv (LFunction (c ξ).χ⁻¹) s / LFunction (c ξ).χ⁻¹ s = g s :=
      Finset.sum_bij' (fun ξ _ => τ ξ) (fun ξ _ => τ ξ) (fun ξ h => hinv ξ h) (fun ξ h => hinv ξ h)
        (fun ξ _ => hτ ξ) (fun ξ _ => hτ ξ)
        (fun ξ _ => congrArg (fun ψ : PChar => deriv (LFunction ψ.χ) s / LFunction ψ.χ s) (hτc ξ).symm)
    rw [Finset.sum_congr rfl fun ξ _ => lseries_re (c ξ).χ hs, ← Finset.sum_div, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, hi]
    simp only [hg]
    ring
  have him : (g 1).im = 0 := by
    have hc : ContinuousAt g 1 := by
      refine tendsto_finsetSum _ fun ξ h => ?_
      exact ((differentiable_deriv_of (hLd ξ h)).continuous.tendsto 1).div ((hLd ξ h).continuous.tendsto 1)
        (hL1 1 (by simp) ξ h)
    have hp : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 1) := by
      have := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
      simpa using this
    have ht := (Complex.continuous_im.tendsto _).comp (hc.tendsto.comp hp)
    have hz : ∀ᶠ σ : ℝ in 𝓝[>] 1, (im ∘ g ∘ fun σ : ℝ => (σ : ℂ)) σ = 0 := by
      refine eventually_nhdsWithin_of_forall fun σ hσ => ?_
      have e := congrArg Complex.im (hsumL σ (by simpa using hσ))
      rw [im_sum, Finset.sum_eq_zero fun ξ _ => lseries_real_im _ σ, neg_im] at e
      simp only [Function.comp_apply]
      linarith
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm))
  have hre : ∑ ξ ∈ S, (((deriv (LFunction (c ξ).χ) 1 / LFunction (c ξ).χ 1).re : ℝ) : ℂ) = g 1 := by
    rw [← ofReal_sum, ← re_sum]
    apply Complex.ext
    · simp [hg]
    · rw [him, ofReal_im]

  obtain ⟨B, hB0, hB⟩ := Gz_bdd (le_max_right y0 1)
  choose B' hB'0 hB' using fun ξ : ι => Gchi_bdd (c ξ).χ (max y0 1)
  set C : ℝ := max C0 (R * B + ∑ ξ ∈ S, B' ξ) with hC
  set H : ℝ → ℝ := fun x => C * x ^ θ - (R * Gz x + ∑ ξ ∈ S, Gchi (c ξ).χ x) with hHdef
  have hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x := by
    intro x hx
    have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ0.le
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hB2 : 0 ≤ R * B + ∑ ξ ∈ S, B' ξ := add_nonneg (mul_nonneg hR0 hB0) (Finset.sum_nonneg fun ξ _ => hB'0 ξ)
    have c1 : C0 ≤ C := le_max_left _ _
    have c2 : R * B + ∑ ξ ∈ S, B' ξ ≤ C := le_max_right _ _
    simp only [hHdef]
    rcases le_or_gt x (max y0 1) with hxX | hxX
    · have a1 : R * Gz x ≤ R * B := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hB x hx hxX)) hR0
      have a2 : ∑ ξ ∈ S, Gchi (c ξ).χ x ≤ ∑ ξ ∈ S, B' ξ :=
        Finset.sum_le_sum fun ξ _ => (le_abs_self _).trans (hB' ξ x hx hxX)
      exact sub_nonneg.2 ((add_le_add a1 a2).trans (c2.trans (le_mul_of_one_le_right (hB2.trans c2) hxθ)))
    · have a1 := hb x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hxX))
      have a2 : C0 * x ^ θ ≤ C * x ^ θ := mul_le_mul_of_nonneg_right c1 (zero_le_one.trans hxθ)
      exact sub_nonneg.2 (a1.trans a2)
  have hm : Measurable H := by
    have a1 := measurable_Gz h3
    have a2 : Measurable fun x => ∑ ξ ∈ S, Gchi (c ξ).χ x := Finset.measurable_fun_sum _ fun ξ _ => measurable_Gchi h3 (c ξ).χ
    exact (measurable_const.mul (measurable_id.pow_const _)).sub ((measurable_const.mul a1).add a2)
  have hI : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    have hfun : (fun x : ℝ => H x * x ^ (-σ - 1)) = fun x =>
        C * (x ^ θ * x ^ (-σ - 1)) - (R * (Gz x * x ^ (-σ - 1)) + ∑ ξ ∈ S, Gchi (c ξ).χ x * x ^ (-σ - 1)) := by
      funext x
      simp only [hHdef]
      rw [← Finset.sum_mul]
      ring
    rw [hfun]
    exact Integrable.sub (Integrable.const_mul (h5.1 θ σ (by linarith)) _)
      (Integrable.add (Integrable.const_mul (rint_Gz h3 h5 hσ) _)
        (integrable_finsetSum _ fun ξ _ => rint_Gchi h3 h5 (c ξ).χ hσ))
  have hA : AP P (-R) (R * (1 + (Real.eulerMascheroniConstant : ℂ)) + g 1) 1 = 0 := by
    have e := hlog 1 (by simp)
    have hp := hP1 1 (by simp)
    rw [deriv_riemannZeta₁_one, riemannZeta₁_one, div_eq_iff hp] at e
    unfold AP
    rw [e]
    ring
  have key := landau_entire P hP hP1 _ _ hA H hm hH hI C θ hθ0 hθ1 (by
    intro s hs
    have iz := (mellin_Gz h3 h5 hs).1
    have i4 : IntegrableOn (fun x : ℝ => ((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
      cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
    have iS : Integrable (fun x : ℝ => ∑ ξ ∈ S, (Gchi (c ξ).χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi 1)) :=
      integrable_finsetSum _ fun ξ _ => (mellin_Gchi' (c ξ).χ hs).1
    have hfun : (fun x : ℝ => ((H x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
        (C : ℂ) * (((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) -
          ((R : ℂ) * ((Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) + ∑ ξ ∈ S, (Gchi (c ξ).χ x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      funext x
      simp only [hHdef]
      rw [← Finset.sum_mul]
      push_cast
      ring
    have j1 := Integrable.const_mul iz (R : ℂ)
    have j2 : Integrable (fun x : ℝ => (R : ℂ) * ((Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) +
        ∑ ξ ∈ S, (Gchi (c ξ).χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi 1)) := j1.add iS
    rw [hfun, integral_sub (Integrable.const_mul i4 _) j2, integral_add j1 iS, integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun ξ _ => (mellin_Gchi' (c ξ).χ hs).1, Finset.sum_congr rfl fun ξ _ => (mellin_Gchi' (c ξ).χ hs).2,
      Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, hsumL s hs, hre, mellin_Gz_n h3 h5 hs,
      h5.2.2.1 θ s (by linarith), hlog s hs.le]
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hs)
    have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
    have hsθ : s - θ ≠ 0 := sub_ne_zero_of_lt_re (a := θ) (by linarith)
    unfold nZ linZ
    generalize deriv riemannZeta₁ s / riemannZeta₁ s = u
    field_simp
    ring)
  intro s hs
  have hne := key s hs
  have hZ1 : riemannZeta₁ s ≠ 0 := fun h => hne (by simp [hPdef, h, hR])
  refine ⟨?_, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne)⟩
  by_cases h1 : s = 1
  · subst h1
    exact riemannZeta_ne_zero_of_one_le_re (by simp)
  · rw [riemannZetaOne_eq_mul_of_ne_one h1] at hZ1
    exact right_ne_zero_of_mul hZ1

end Family


theorem eq_one_of_chi {ψ : PChar} (h : ψ.χ = 1) : ψ = PChar.one := by
  obtain ⟨N, χ, hp⟩ := ψ
  have h' : χ = 1 := h
  subst h'
  have e : N = 1 := hp.symm.trans DirichletCharacter.conductor_one
  subst e
  rfl

theorem one_inv : PChar.one.inv = PChar.one := eq_one_of_chi (inv_one (G := DirichletCharacter ℂ 1))


end Formalism.HC.Landau

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.HC

def EAt (Λ : Level) (D : D7) (x eps C : ℝ) : Prop := EAtH Λ D.host.toHostRaw D.host.TT x eps C

def EFamC (Λ : Level) {eps : ℝ} (Fm : FamCore eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, EAt Λ (Fm.D x i) x eps C

section

variable {Fam : ℝ → Type 1} (core : ∀ {eps : ℝ}, Fam eps → FamCore eps)
  (Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop)

def ChebyshevInequalityForFamily (Λ : Level) : Prop :=
  ∀ (eD eL eps : ℝ), 0 < eps → ∀ Fm : Fam eps, EFamC Λ (core Fm) →
    (∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, Tied Fm eD eL K cHH eK CL x) →
    ∃ x1 : ℝ, ∀ x ≥ x1, Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

def ChebyshevInequalityEventual (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ Fm : Fam eps, EFamC Λ (core Fm) ∧
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, Tied Fm eD eL K cHH eK CL x

variable {core Tied}

end

end Formalism.HC

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.HC

theorem windows_iff {eps : ℝ} (Fm : FamCore eps) (la : ℝ) : Fm.Windows la ↔ HasWindows Fm.Win la := Iff.rfl

def WinAll {eps : ℝ} (Fm : FamCore eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win

theorem WinAll.windows {eps : ℝ} {Fm : FamCore eps} (h : WinAll Fm) (la : ℝ) : Fm.Windows la := by
  obtain ⟨x0, h⟩ := h
  exact hasWindows_of_large h la

section

variable {Fam : ℝ → Type 1} (core : ∀ {eps : ℝ}, Fam eps → FamCore eps)
  (Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop)

def ChebyshevInequalityOnFamilyWindows {eps : ℝ} (Fm : Fam eps) (eD eL : ℝ) : Prop :=
  ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ (core Fm).Win → Tied Fm eD eL K cHH eK CL x

def ChebyshevInequalityOnWindows (Λ : Level) : Prop :=
  ∀ (eD eL eps : ℝ), 0 < eps → ∀ Fm : Fam eps, EFamC Λ (core Fm) → ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL →
    ∃ x1 : ℝ, ∀ x ≥ x1, x ∈ (core Fm).Win → Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

def ChebyshevInequalityAtWindowScale (la : ℝ) (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ Fm : Fam eps, EFamC Λ (core Fm) ∧
    (core Fm).Windows la ∧ ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL

def TiedAll (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ Fm : Fam eps, EFamC Λ (core Fm) ∧
    WinAll (core Fm) ∧ ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL

variable {TransportedAlt : Type} (P : ∀ {eps : ℝ}, Fam eps → TransportedAlt → Prop) (HypV : ∀ {eps : ℝ}, FamCore eps → Prop)

def ExWin (la : ℝ) (Λ : Level) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∀ K : TransportedAlt, ∃ Fm : Fam eps, P Fm K ∧ EFamC Λ (core Fm) ∧
    (core Fm).Windows la ∧ HypV (core Fm)

def ChainWin (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ K : TransportedAlt, ∀ Fm : Fam eps, P Fm K → EFamC Λ (core Fm) →
    HypV (core Fm) → ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL

variable {core Tied P HypV}


theorem exists_small_eps (C : ℝ) {δ ε₁ : ℝ} (hδ : 0 < δ) (h1 : 0 < ε₁) : ∃ ε : ℝ, 0 < ε ∧ ε < ε₁ ∧ C * ε ≤ δ := by
  have hp : 0 < |C| + 1 := by positivity
  have h0 : 0 < min (ε₁ / 2) (δ / (|C| + 1)) := lt_min (by linarith) (div_pos hδ hp)
  refine ⟨_, h0, lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) h0.le
  have a2 : min (ε₁ / 2) (δ / (|C| + 1)) ≤ δ / (|C| + 1) := min_le_right _ _
  rw [le_div_iff₀ hp] at a2
  nlinarith

theorem level_of_tiedWin {Λ : Level} {la : ℝ} (h112 : ChebyshevInequalityOnWindows @core @Tied Λ) (hB : Λ.FormBAt la)
    (h : ChebyshevInequalityAtWindowScale @core @Tied la Λ) : Λ.ZeroFreeLevel := by
  obtain ⟨eD, eL, ε₁, h1, h⟩ := h
  intro ψ hψ s hs
  have hm1 : min (s.re - 1 / 2) (1 / 2) ≤ s.re - 1 / 2 := min_le_left _ _
  have hm2 : min (s.re - 1 / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hm0 : 0 < min (s.re - 1 / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  obtain ⟨ε, hε0, hεlt, hCe⟩ := exists_small_eps (eD + eL + 7) (half_pos hm0) h1
  obtain ⟨Fm, hE, hW, hT⟩ := h ε hε0 hεlt
  obtain ⟨x1, hx⟩ := h112 eD eL ε hε0 Fm hE hT
  refine hB (1 / 2 + min (s.re - 1 / 2) (1 / 2) / 2) (by linarith) (by linarith)
    (((windows_iff _ la).1 hW).mono (x0 := max x1 1) fun y hy hw => ?_) ψ hψ s (by linarith)
  exact (hx y (le_of_max_le_left hy) hw).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_right hy) (by linarith))

theorem zeroFreeOn_of_tiedWin {Q : PChar → Prop}
    (h : ∀ ψ, Q ψ → ∃ (Λ : Level) (la : ℝ), ψ ∈ Λ.KEPT ∧ 1 < la ∧ ChebyshevInequalityOnWindows @core @Tied Λ ∧ Λ.FormB ∧
      ChebyshevInequalityAtWindowScale @core @Tied la Λ) : ZeroFreeOn Q :=
  zeroFreeOn_of_levels fun ψ hψ => by
    obtain ⟨Λ, la, a, b, c, d, e⟩ := h ψ hψ
    exact ⟨Λ, a, level_of_tiedWin c (d la b) e⟩

theorem zeroFreeOn_of_tiedWin_cyc {Q : PChar → Prop} {la : ℝ} (hla : 1 < la)
    (h112 : ∀ ψ, Q ψ → ChebyshevInequalityOnWindows @core @Tied (Level.cyc ψ)) (hB : ∀ ψ, Q ψ → (Level.cyc ψ).FormB)
    (h : ∀ ψ, Q ψ → ChebyshevInequalityAtWindowScale @core @Tied la (Level.cyc ψ)) : ZeroFreeOn Q :=
  zeroFreeOn_of_tiedWin fun ψ hψ => ⟨_, la, Level.mem_cyc ψ, hla, h112 ψ hψ, hB ψ hψ, h ψ hψ⟩






end

end Formalism.HC

end
end
