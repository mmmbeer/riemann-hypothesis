import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N → IsLevelK V N Kf → ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  first | exact @GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds | exact GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds | (intros; apply GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntWtRead

open Formalism.L2.Pj

theorem wtAllZ_of_borChart {K : Type} [Field K] {ι : Type} [Fintype ι]
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}
    (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts} (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (y y' : pts S) (hy : FromTest pts mapR y)
    (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dif_pos hy, dif_pos hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have hu : ∀ i, Units.map (cB : B.R →* Localization.AtPrime m) (tB i)
      = Units.map ((locM K m : S →ₐ[K] Localization.AtPrime m) : S →* Localization.AtPrime m) (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map (cB : B.R →* Localization.AtPrime m) (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map ((locM K m : S →ₐ[K] Localization.AtPrime m) : S →* Localization.AtPrime m)
        (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp only [map_zpow, hu]

end GlobalTheory.IntWtRead

namespace GlobalTheory.IntWtRead

open Formalism.L2.Pj

set_option maxHeartbeats 800000 in

theorem cuspW_eq_zero_of_reading : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ (G : WTZ D.host.E) (x : Y.V G), (∀ k, ∀ z ∈ ((Y.U σ).X k).dom, rdU (Y.U σ) (x : Rul Y.d.Xo₂ Y.d.c₂) k z = 0) → x = 0 := by
  intro D T j Y e o hY σ hσ G x h0
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hU := hY.unf σ hσ
  obtain ⟨-, hB, hW, -, -, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hall : AllTest Y.d.Xo₂ Y.d.c₂ := GlobalTheory.T.framedPoint_reduced_from_testRing hS _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hx : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ _ G) :=
    GlobalTheory.AllWt.cuspW_le_secZ G x.2
  apply Subtype.ext
  funext p y
  show (x : Rul Y.d.Xo₂ Y.d.c₂) p y = 0
  refine eq_zero_of_cpts σ p _ fun ψ => ?_
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ _ _ _ Y.d.Xo₂ Y.d.c₂ p.R (CAt σ) ψ y
  obtain ⟨k, x', t, ht⟩ := hU.2.2.1 z
  have hft : FromTest (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) z :=
    ⟨p, ψ, y, hz⟩
  have hev : evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) z = ψ ((x : Rul Y.d.Xo₂ Y.d.c₂) p y) := by
    unfold evR evalAt
    rw [dif_pos hft]
    exact hW _ hx.1 (CAt σ) _ p _ ψ _ y z hft.choose_spec.choose_spec.choose_spec hz
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hw := wtAllZ_of_borChart hB (exZ _ G) hx.1 hx.2 (CAt σ) t _ z (hall _ _) (hall _ _) ht
  have h1 := h0 k x'.1 x'.2
  have h2 : toC (evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k x')) = 0 := by
    rw [← h1]
    classical
    show _ = (if h : x'.1 ∈ ((Y.U σ).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k ⟨x'.1, h⟩)) else 0)
    rw [dif_pos x'.2]
  have h3 : evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k x') = 0 := h2
  rw [← hev]
  unfold evR
  rw [hw]
  unfold evR at h3
  rw [h3, mul_zero]

end GlobalTheory.IntWtRead
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_restrictions_vanish : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ (G : WTZ D.host.E) (x : Y.V G), (∀ k, ∀ z ∈ ((Y.U σ).X k).dom, rdU (Y.U σ) (x : Rul Y.d.Xo₂ Y.d.c₂) k z = 0) → x = 0 := by
  atlas_forward_decl GlobalTheory.IntWtRead.cuspW_eq_zero_of_reading
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.PetDef

open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adelAut_of_gamma {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} (hχ : ∀ k la γ, γ ∈ (X k).Γ → (X k).χ la γ = 1) (hd : DictIsUnif V dict Kf th hr)
    (hm : MuUnit V dict mu) (hL : DictLoc V dict) (hmc : Continuous mu) : AdelAut V dict mu := by
  intro la P hP
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · obtain ⟨γ', hγ', he⟩ := hd.1 γ hγ g
    have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hd.2.2.2.1 g)
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hE, hχ _ _ _ hγ', one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
    have hsec : (X k).IsSec (la k) (P k) := (hP k).1.1
    have hPc : ContinuousOn (P k) (X k).dom := hsec.1.continuousOn
    have hc : ContinuousOn (fun g => mu g * P k (x g)) N :=
      hmc.continuousOn.mul (hPc.comp hx fun g hg => (hs g hg).1)
    have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      obtain ⟨hd', γ, hγ, he⟩ := hs g hg
      show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show mu g * P k (x g) = mu g * P k (lact γ (x g))
      rw [hsec.2.2 γ hγ (x g) hd', hχ _ _ _ hγ, one_mul]
    exact (hc.continuousAt hN).congr heq

end Gen

section Cover

variable {D : D7} {T : Core D} {j : ℕ}

theorem dictLoc_of_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ)
    (hσ : GoodEmb Y.d.c₂ σ) : ∃ th hr, DictIsUnif (D.sp.W j) (Y.dict σ) Y.Kf th hr ∧ DictLoc (D.sp.W j) (Y.dict σ) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  refine ⟨th, hr, hd, ?_⟩
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hK : Y.Kf ≤ GfC (D.sp.W j) := fun k hk => ((h.levelK k).1 hk).1
  exact GlobalTheory.DictLocTest.locClause_of_unif_places hd hK (GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)

theorem muUnit_one (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
  ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, h.unit σ hσ⟩

theorem adelAut_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelAut (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, hL⟩ := dictLoc_of_good Y h σ hσ
  exact adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd (muUnit_one Y h σ hσ) hL
    continuous_const

theorem aeDom_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AeDom Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, -⟩ := dictLoc_of_good Y h σ hσ
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  exact aeDom_of_aut Y.d.Xo₂ Y.d.c₂ (adelAut_good Y h σ hσ) (quotSupp_of _ hV hP) (muUnit_one Y h σ hσ) hd

end Cover

end GlobalTheory.PetDef
end
end
