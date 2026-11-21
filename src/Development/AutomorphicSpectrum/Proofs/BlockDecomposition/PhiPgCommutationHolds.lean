import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveIntertwinerSubrepEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureDataStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationInduced
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationInducedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesClosedCellStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesOpenCellStatement

section
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Glue

open GlobalTheory.CompanionTheory.TwistedAverage GlobalTheory.CompanionTheory.PRep.JacExact

section Eig

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [TopologicalSpace G] [IsTopologicalGroup G]

theorem eq_zero_of_mem_twKer_of_eig (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (χ : L →* ℂˣ) (hχ : IsOpen (χ.ker : Set L)) (e : V)
    (he : e ∈ twKer ρ L χ) (hev : ∀ l : L, ρ (l : G) e = ((χ l : ℂˣ) : ℂ) • e) : e = 0 := by
  classical
  obtain ⟨s, t, hst⟩ := exists_finite_support ρ L χ e he
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  obtain ⟨M, hMo, hMχ, -, hMt⟩ := exists_open_fixing ρ ρ hρ hρ L χ.ker hχ e t
  haveI : Finite (L ⧸ M) := Subgroup.quotient_finite_of_isOpen M hMo
  haveI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let C : Subgroup L := M.normalCore
  haveI : C.Normal := Subgroup.normalCore_normal M
  haveI : C.FiniteIndex := inferInstance
  haveI : Finite (L ⧸ C) := inferInstance
  letI := Fintype.ofFinite (L ⧸ C)
  have hCM : C ≤ M := Subgroup.normalCore_le M
  let τ : Representation ℂ L V := ρ.comp L.subtype
  have h0 : avg τ χ C e = 0 := by
    have hle : Submodule.span ℂ {y | ∃ n ∈ s, ∃ w ∈ t, y = ρ (n : G) w - ((χ n : ℂˣ) : ℂ) • w} ≤
        LinearMap.ker (avg τ χ C) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨n, -, w, hw, rfl⟩
      show avg τ χ C (τ n w - ((χ n : ℂˣ) : ℂ) • w) = 0
      rw [map_sub, avg_translate τ χ C (hCM.trans hMχ) w (fun m hm => hMt w hw m (hCM hm)) n, map_smul,
        sub_self]
    exact hle hst
  have h1 : avg τ χ C e = ((Fintype.card (L ⧸ C) : ℕ) : ℂ) • e := by
    have h2 : ∀ q : L ⧸ C, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) e = e := by
      intro q
      show (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • ρ ((Quotient.out q : L) : G) e = e
      rw [hev, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [avg_apply, Finset.sum_congr rfl fun q _ => h2 q]
    simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hc : ((Fintype.card (L ⧸ C) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [h0] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hc

theorem twKer_mono (ρ : Representation ℂ G V) {U L₁ L₂ : Subgroup G} (θ : U →* ℂˣ) (h₁ : L₁ ≤ U) (h₂ : L₂ ≤ U)
    (h : L₁ ≤ L₂) :
    twKer ρ L₁ (θ.comp (Subgroup.inclusion h₁)) ≤ twKer ρ L₂ (θ.comp (Subgroup.inclusion h₂)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨n, v, rfl⟩
  exact ⟨⟨n, h n.2⟩, v, rfl⟩

theorem twKer_le (ρ : Representation ℂ G V) {U L : Subgroup G} (θ : U →* ℂˣ) (h : L ≤ U) :
    twKer ρ L (θ.comp (Subgroup.inclusion h)) ≤ twKer ρ U θ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨n, v, rfl⟩
  exact ⟨⟨n, h n.2⟩, v, rfl⟩

theorem isOpen_ker_comp {U L : Subgroup G} (θ : U →* ℂˣ) (hθ : IsOpen (θ.ker : Set U)) (h : L ≤ U) :
    IsOpen ((θ.comp (Subgroup.inclusion h)).ker : Set L) := by
  have e : ((θ.comp (Subgroup.inclusion h)).ker : Set L) = Subgroup.inclusion h ⁻¹' (θ.ker : Set U) := by
    ext l
    simp [MonoidHom.mem_ker]
  rw [e]
  exact hθ.preimage (Continuous.subtype_mk continuous_subtype_val _)

end Eig

theorem exists_factor {Y V A : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup V] [Module ℂ V] [AddCommGroup A]
    [Module ℂ A] (j : V →ₗ[ℂ] A) (hj : Function.Injective j) (E : Y →ₗ[ℂ] A) (h : ∀ y, ∃ v, j v = E y) :
    ∃ Φ : Y →ₗ[ℂ] V, ∀ y, j (Φ y) = E y := by
  let E' : Y →ₗ[ℂ] LinearMap.range j := E.codRestrict _ fun y => by
    obtain ⟨v, hv⟩ := h y
    exact ⟨v, hv⟩
  refine ⟨(LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ E', fun y => ?_⟩
  have := (LinearEquiv.ofInjective j hj).apply_symm_apply (E' y)
  exact congrArg Subtype.val this

theorem extension_of_maps {M Y VC VO AC AO : Type} [Group M] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup VC] [Module ℂ VC]
    [AddCommGroup VO] [Module ℂ VO] [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (ρ : Representation ℂ M Y) (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (EC : Y →ₗ[ℂ] AC) (EO : Y →ₗ[ℂ] AO)
    (ECi : ∀ m y, EC (ρ m y) = aC m (EC y)) (EOi : ∀ m y, EO (ρ m y) = aO m (EO y))
    (hCmem : ∀ y, ∃ v, jC v = EC y) (hConto : ∀ v, ∃ y, EC y = jC v)
    (h1 : ∀ y, EC y = 0 → ∃ v, jO v = EO y) (h2 : ∀ y, EC y = 0 → EO y = 0 → y = 0)
    (h3 : ∀ v, ∃ y, EC y = 0 ∧ EO y = jO v) :
    ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  obtain ⟨ΦC, hΦC⟩ := exists_factor jC hjC EC hCmem
  let R : ρ.IntertwiningMap πC := ⟨ΦC, fun m => LinearMap.ext fun y => by
    apply hjC
    show jC (ΦC (ρ m y)) = jC (πC m (ΦC y))
    rw [hΦC, hjCe, hΦC, ECi]⟩
  have hRs : Function.Surjective R := fun v => by
    obtain ⟨y, hy⟩ := hConto v
    refine ⟨y, hjC ?_⟩
    show jC (ΦC y) = jC v
    rw [hΦC, hy]
  obtain ⟨S, hS, hq⟩ := GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv ρ πC R hRs
  have memS : ∀ y, y ∈ S.toSubmodule ↔ EC y = 0 := by
    intro y
    rw [hS, LinearMap.mem_ker]
    constructor
    · intro h
      have h' : ΦC y = 0 := h
      rw [← hΦC, h', map_zero]
    · intro h
      refine hjC ?_
      show jC (ΦC y) = jC 0
      rw [hΦC, h, map_zero]
  obtain ⟨Ψ, hΨ⟩ := exists_factor jO hjO (EO ∘ₗ S.toSubmodule.subtype)
    (fun y => h1 y.1 ((memS _).1 y.2))
  refine ⟨S, GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective ρ πO S Ψ ⟨?_, ?_⟩ ?_, hq⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, hy⟩ h0
    have hO : EO y = 0 := by
      have := hΨ ⟨y, hy⟩
      rw [h0, map_zero] at this
      exact this.symm
    exact Subtype.ext (h2 y ((memS _).1 hy) hO)
  · intro v
    obtain ⟨y, hy, he⟩ := h3 v
    refine ⟨⟨y, (memS _).2 hy⟩, hjO ?_⟩
    rw [hΨ]
    exact he
  · intro m v
    apply hjO
    rw [hΨ, hjOe, hΨ]
    exact EOi m v.1

section Glue

variable {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]

def evC (H : Subgroup G) (σ : Representation ℂ H Z) (x : G) : cIndSpace H σ →ₗ[ℂ] Z :=
  GlobalTheory.CompanionTheory.TwAvgInd.evalAt H σ x ∘ₗ (cIndSpace H σ).subtype

theorem exists_avg (H : Subgroup G) (σ : Representation ℂ H Z) {L : Subgroup G} (hL : IsCompact (L : Set G))
    (χ : L →* ℂˣ) (hχ : IsOpen (χ.ker : Set L)) (f : cIndSpace H σ) :
    ∃ f' : cIndSpace H σ, f - f' ∈ twKer (cInd H σ) L χ ∧
      (∀ x, f'.1.1.1 x ≠ 0 → ∃ l ∈ L, f.1.1.1 (x * l) ≠ 0) ∧
      ∀ l : L, cInd H σ (l : G) f' = ((χ l : ℂˣ) : ℂ) • f' := by
  obtain ⟨ι, _, r, c, h1, h2⟩ :=
    GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL χ hχ f
  refine ⟨_, h1, ?_, h2⟩
  intro x hx
  by_contra hcon
  push_neg at hcon
  apply hx
  have hz : ∀ i, evC H σ x (twOrbit (cInd H σ) L χ f (r i)) = 0 := by
    intro i
    have : evC H σ x (cInd H σ ((r i : L) : G) f) = 0 := hcon _ (r i).2
    simp only [twOrbit, map_smul, this, smul_zero]
  have : evC H σ x (c • ∑ i, twOrbit (cInd H σ) L χ f (r i)) = 0 := by
    rw [map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]
  exact this

def Good (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (f : cIndSpace H σ)
    (A : Set G) : Prop :=
  ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧
    ∀ (L' : Subgroup G) (hL' : L' ≤ U), IsCompact (L' : Set G) → L ≤ L' →
      ∀ g : cIndSpace H σ, f - g ∈ twKer (cInd H σ) L' (θ.comp (Subgroup.inclusion hL')) →
        (∀ l : L', cInd H σ (l : G) g = ((θ (Subgroup.inclusion hL' l) : ℂˣ) : ℂ) • g) →
        ∀ x ∈ A, g.1.1.1 x = 0

theorem good_nhds (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U)) (f : cIndSpace H σ) (p : G) (hp : AvgVanish H σ U θ f p) :
    ∃ t ∈ 𝓝 p, Good H σ U θ f t := by
  obtain ⟨L, hL, hLc, gp, h1, -, h3⟩ := hp
  have hK : IsOpen {k : G | cInd H σ k gp = gp} := GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ gp
  have hop : IsOpen ((fun x => p⁻¹ * x) ⁻¹' {k : G | cInd H σ k gp = gp}) :=
    hK.preimage (by fun_prop)
  refine ⟨_, hop.mem_nhds (by simp), L, hL, hLc, fun L' hL' hL'c hLL' g hg hge ω hω => ?_⟩
  by_contra hne
  obtain ⟨h', a1, a2, a3⟩ := exists_avg H σ hL'c (θ.comp (Subgroup.inclusion hL'))
    (isOpen_ker_comp θ hθ hL') gp
  have hgh : g - h' = 0 := by
    refine eq_zero_of_mem_twKer_of_eig (cInd H σ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL'c _
      (isOpen_ker_comp θ hθ hL') _ ?_ ?_
    · have e : g - h' = (f - gp) + (gp - h') - (f - g) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (twKer_mono _ θ hL hL' hLL' h1) a1) hg
    · intro l
      rw [map_sub, hge l, a3 l, smul_sub]
      rfl
  obtain rfl : g = h' := sub_eq_zero.1 hgh
  obtain ⟨l, hl, hne'⟩ := a2 ω hne
  apply hne'
  set k : G := p⁻¹ * ω with hk
  have hkK : cInd H σ k gp = gp := hω
  have hu : k * l * k⁻¹ ∈ U := hUn.conj_mem l (hL' hl) k
  have e1 : ω * l = p * (k * l * k⁻¹) * k := by
    rw [hk]; group
  have e2 : gp.1.1.1 (p * (k * l * k⁻¹) * k) = (cInd H σ k gp).1.1.1 (p * (k * l * k⁻¹)) := rfl
  rw [e1, e2, hkK]
  exact h3 _ hu

theorem glue (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (S : Set G) (hS : IsClosed S) (hHS : ∀ h ∈ H, ∀ x ∈ S, h * x ∈ S) (hSU : ∀ x ∈ S, ∀ u ∈ U, x * u ∈ S)
    (f : cIndSpace H σ) (hf : ∀ p ∈ S, AvgVanish H σ U θ f p) :
    ∃ g : cIndSpace H σ, f - g ∈ twKer (cInd H σ) U θ ∧ ∀ x ∈ S, g.1.1.1 x = 0 := by
  obtain ⟨Ω₀, hΩ₀, hsupp⟩ := f.2
  have hΩ : IsCompact (Ω₀ ∩ S) := hΩ₀.inter_right hS
  have hG : Good H σ U θ f (Ω₀ ∩ S) := by
    refine hΩ.induction_on (p := Good H σ U θ f) ?_ ?_ ?_ ?_
    · refine ⟨⊥, bot_le, ?_, fun _ _ _ _ _ _ _ x hx => hx.elim⟩
      rw [Subgroup.coe_bot]
      exact isCompact_singleton
    · rintro A B hAB ⟨L, hL, hLc, h⟩
      exact ⟨L, hL, hLc, fun L' hL' c hl g a b x hx => h L' hL' c hl g a b x (hAB hx)⟩
    · rintro A B ⟨L₁, h₁, c₁, a₁⟩ ⟨L₂, h₂, c₂, a₂⟩
      obtain ⟨L, hL, hLc, l₁, l₂⟩ := hdir L₁ L₂ h₁ h₂ c₁ c₂
      refine ⟨L, hL, hLc, fun L' hL' c hl g a b x hx => ?_⟩
      rcases hx with hx | hx
      · exact a₁ L' hL' c (l₁.trans hl) g a b x hx
      · exact a₂ L' hL' c (l₂.trans hl) g a b x hx
    · intro x hx
      obtain ⟨t, ht, hg⟩ := good_nhds H σ U hUn θ hθ f x (hf x hx.2)
      exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, hg⟩
  obtain ⟨L, hL, hLc, hgood⟩ := hG
  obtain ⟨g, h1, h2, h3⟩ := exists_avg H σ hLc (θ.comp (Subgroup.inclusion hL)) (isOpen_ker_comp θ hθ hL) f
  refine ⟨g, twKer_le _ θ hL h1, fun x hx => ?_⟩
  by_contra hne
  obtain ⟨l, hl, hfl⟩ := h2 x hne
  obtain ⟨h, hh, ω, hω, e⟩ := hsupp (x * l) hfl
  have hωS : ω ∈ S := by
    have : ω = h⁻¹ * (x * l) := by rw [e]; group
    rw [this]
    exact hHS _ (inv_mem hh) _ (hSU x hx l (hL hl))
  have hz : g.1.1.1 ω = 0 := hgood L hL hLc le_rfl g h1 h3 ω ⟨hω, hωS⟩
  have hxl : g.1.1.1 (x * l) = 0 := by
    have e4 : g.1.1.1 (((⟨h, hh⟩ : H) : G) * ω) = σ ⟨h, hh⟩ (g.1.1.1 ω) := g.1.1.2 ⟨h, hh⟩ ω
    rw [e]
    rw [show g.1.1.1 (h * ω) = _ from e4, hz, map_zero]
  have e5 : g.1.1.1 (x * l) = (cInd H σ ((⟨l, hl⟩ : L) : G) g).1.1.1 x := rfl
  rw [e5, h3 ⟨l, hl⟩] at hxl
  have e7 : ((θ.comp (Subgroup.inclusion hL) ⟨l, hl⟩ : ℂˣ) : ℂ) • g.1.1.1 x = 0 := hxl
  exact hne ((smul_eq_zero.1 e7).resolve_left (Units.ne_zero _))

end Glue

theorem extension {G M Z VC VO AC AO : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup VC] [Module ℂ VC] [AddCommGroup VO] [Module ℂ VO]
    [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (s : M →* G) (c : M →* ℂˣ) (ρ : Representation ℂ M (TwJacquet (cInd H σ) U θ))
    (hρ : ∀ (m : M) (f : cIndSpace H σ), ρ m (Submodule.Quotient.mk f) =
      ((c m : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd H σ (s m) f))
    (C : Set G) (hCc : IsClosed C) (hHC : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C) (hCU : ∀ x ∈ C, ∀ u ∈ U, x * u ∈ C)
    (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (eC : cIndSpace H σ →ₗ[ℂ] AC) (eO : cIndSpace H σ →ₗ[ℂ] AO)
    (hC1 : ∀ (u : U) f, eC (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eC f)
    (hO1 : ∀ (u : U) f, eO (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eO f)
    (hCs : ∀ m f, aC m (eC f) = ((c m : ℂˣ) : ℂ) • eC (cInd H σ (s m) f))
    (hOs : ∀ m f, aO m (eO f) = ((c m : ℂˣ) : ℂ) • eO (cInd H σ (s m) f))
    (hCmem : ∀ f, ∃ v, jC v = eC f)
    (hOmem : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → ∃ v, jO v = eO f)
    (hConto : ∀ v, ∃ f, eC f = jC v)
    (hOonto : ∀ v, ∃ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) ∧ eO f = jO v)
    (hCoff : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → eC f = 0)
    (hlocC : ∀ f, eC f = 0 → ∀ p ∈ C, AvgVanish H σ U θ f p)
    (hlocO : ∀ f, eO f = 0 → ∀ p, p ∉ C → AvgVanish H σ U θ f p) :
    ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  have kC : twKer (cInd H σ) U θ ≤ LinearMap.ker eC := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eC _ = 0
    rw [map_sub, hC1, map_smul, sub_self])
  have kO : twKer (cInd H σ) U θ ≤ LinearMap.ker eO := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eO _ = 0
    rw [map_sub, hO1, map_smul, sub_self])
  have ECmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eC kC (Submodule.Quotient.mk f) = eC f := fun f => rfl
  have EOmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eO kO (Submodule.Quotient.mk f) = eO f := fun f => rfl
  refine Glue.extension_of_maps ρ πC πO aC aO jC jO hjC hjO hjCe hjOe
    ((twKer (cInd H σ) U θ).liftQ eC kC) ((twKer (cInd H σ) U θ).liftQ eO kO) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, ECmk, ECmk, hCs]
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, EOmk, EOmk, hOs]
  · intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact hCmem f
  · intro v
    obtain ⟨f, hf⟩ := hConto v
    exact ⟨Submodule.Quotient.mk f, hf⟩
  · intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir C hCc hHC hCU f (hlocC f hy)
    have e : (Submodule.Quotient.mk f : TwJacquet (cInd H σ) U θ) = Submodule.Quotient.mk g :=
      (Submodule.Quotient.eq _).2 hg
    obtain ⟨v, hv'⟩ := hOmem g hv
    exact ⟨v, by rw [e, EOmk, hv']⟩
  · intro y hyC hyO
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir Set.univ isClosed_univ (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial) f (fun p _ => by
        by_cases hp : p ∈ C
        · exact hlocC f hyC p hp
        · exact hlocO f hyO p hp)
    have hg0 : g = 0 := Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => hv x trivial)))
    rw [hg0, sub_zero] at hg
    exact (Submodule.Quotient.mk_eq_zero _).2 hg
  · intro v
    obtain ⟨f, hf, he⟩ := hOonto v
    exact ⟨Submodule.Quotient.mk f, hCoff f hf, he⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Glue
end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_closed_open_sequence : ∀ {G M Z VC VO AC AO : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup VC] [Module ℂ VC] [AddCommGroup VO] [Module ℂ VO]
    [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (s : M →* G) (c : M →* ℂˣ) (ρ : Representation ℂ M (TwJacquet (cInd H σ) U θ))
    (hρ : ∀ (m : M) (f : cIndSpace H σ), ρ m (Submodule.Quotient.mk f) =
      ((c m : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd H σ (s m) f))
    (C : Set G) (hCc : IsClosed C) (hHC : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C) (hCU : ∀ x ∈ C, ∀ u ∈ U, x * u ∈ C)
    (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (eC : cIndSpace H σ →ₗ[ℂ] AC) (eO : cIndSpace H σ →ₗ[ℂ] AO)
    (hC1 : ∀ (u : U) f, eC (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eC f)
    (hO1 : ∀ (u : U) f, eO (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eO f)
    (hCs : ∀ m f, aC m (eC f) = ((c m : ℂˣ) : ℂ) • eC (cInd H σ (s m) f))
    (hOs : ∀ m f, aO m (eO f) = ((c m : ℂˣ) : ℂ) • eO (cInd H σ (s m) f))
    (hCmem : ∀ f, ∃ v, jC v = eC f)
    (hOmem : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → ∃ v, jO v = eO f)
    (hConto : ∀ v, ∃ f, eC f = jC v)
    (hOonto : ∀ v, ∃ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) ∧ eO f = jO v)
    (hCoff : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → eC f = 0)
    (hlocC : ∀ f, eC f = 0 → ∀ p ∈ C, AvgVanish H σ U θ f p)
    (hlocO : ∀ f, eO f = 0 → ∀ p, p ∉ C → AvgVanish H σ U θ f p),
  ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZPhiPG.Glue.extension
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.TwC
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_false_eq (I T : ℕ) (a : Fin I) :
    ePG I T ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd T a) := by
  apply Fin.ext
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem ePG_true_eq (I T : ℕ) (b : Fin T) :
    ePG I T ⟨true, b⟩ = Fin.castSucc (Fin.natAdd I b) := by
  apply Fin.ext
  simp [ePG]

theorem colMat_castSucc_last (n : ℕ) (v : Fin n → k) (r : Fin n) :
    colMat k n v (Fin.castSucc r) (Fin.last n) = v r := by
  simp [colMat]

theorem colMat_last_last (n : ℕ) (v : Fin n → k) : colMat k n v (Fin.last n) (Fin.last n) = 0 := by
  simp [colMat]

theorem colMat_of_ne (n : ℕ) (v : Fin n → k) (r : Fin (n + 1)) {c : Fin (n + 1)} (hc : c ≠ Fin.last n) :
    colMat k n v r c = 0 := by
  simp [colMat, hc]

def uG (I T : ℕ) (v : Fin (I + T) → k) : Mir k (I + T) :=
  ⟨unip k (I + T) (Multiplicative.ofAdd v), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem uG_add (I T : ℕ) (v w : Fin (I + T) → k) : uG I T (v + w) = uG I T v * uG I T w := by
  apply Subtype.ext
  show unip k (I + T) (Multiplicative.ofAdd (v + w)) = unip k _ _ * unip k _ _
  rw [ofAdd_add, map_mul]

theorem uG_comm (I T : ℕ) (v w : Fin (I + T) → k) : uG I T v * uG I T w = uG I T w * uG I T v := by
  rw [← uG_add, ← uG_add]
  exact congrArg _ (add_comm v w)

theorem uG_mem_H (I T : ℕ) (c : Fin I → k) : uG I T (Fin.append c (0 : Fin T → k)) ∈ HPG k I T := by
  show ((uG I T (Fin.append c (0 : Fin T → k)) : Mir k (I + T)) : GL (Fin (I + T + 1)) k) ∈ parab k (ePG I T)
  rw [mem_parab_iff]
  intro a b x y hab
  obtain ⟨rfl, rfl⟩ : a = true ∧ b = false := by
    cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd hab (by decide)
  show (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨true, x⟩) (ePG I T ⟨false, y⟩) +
    colMat k (I + T) (Fin.append c (0 : Fin T → k)) (ePG I T ⟨true, x⟩) (ePG I T ⟨false, y⟩) = 0
  rw [Matrix.one_apply_ne ((ePG I T).injective.ne (by simp)), zero_add]
  by_cases hy : y = Fin.last I
  · subst hy
    rw [ePG_false_last, ePG_true_eq, colMat_castSucc_last, Fin.append_right]
    rfl
  · exact colMat_of_ne _ _ _ fun e => hy ((ePG_false_eq_last_iff I T y).1 e)

theorem pgProj_snd (I T : ℕ) (c : Fin I → k) :
    (pgProj k I T ⟨uG I T (Fin.append c (0 : Fin T → k)), uG_mem_H I T c⟩).2 = 1 := by
  ext x y
  show (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨true, x⟩) (ePG I T ⟨true, y⟩) +
    colMat k (I + T) (Fin.append c (0 : Fin T → k)) (ePG I T ⟨true, x⟩) (ePG I T ⟨true, y⟩) = (1 : Matrix _ _ k) x y
  rw [colMat_of_ne _ _ _ (by rw [ePG_true_eq]; exact Fin.castSucc_ne_last _), add_zero]
  by_cases h : x = y
  · subst h; simp
  · rw [Matrix.one_apply_ne ((ePG I T).injective.ne (by simpa using h)), Matrix.one_apply_ne h]

theorem pgProj_fst (I T : ℕ) (c : Fin I → k) :
    (((pgProj k I T ⟨uG I T (Fin.append c (0 : Fin T → k)), uG_mem_H I T c⟩).1 : Mir k I) : GL (Fin (I + 1)) k) =
      unip k I (Multiplicative.ofAdd c) := by
  ext x y
  show (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨false, x⟩) (ePG I T ⟨false, y⟩) +
    colMat k (I + T) (Fin.append c (0 : Fin T → k)) (ePG I T ⟨false, x⟩) (ePG I T ⟨false, y⟩) =
    (1 : Matrix _ _ k) x y + colMat k I c x y
  induction y using Fin.lastCases with
  | last =>
    induction x using Fin.lastCases with
    | last => rw [ePG_false_last, colMat_last_last, colMat_last_last]; simp
    | cast a =>
      rw [ePG_false_last, ePG_false_eq, colMat_castSucc_last, colMat_castSucc_last, Fin.append_left,
        Matrix.one_apply_ne (Fin.castSucc_ne_last _), Matrix.one_apply_ne (Fin.castSucc_ne_last _)]
  | cast b =>
    rw [colMat_of_ne _ _ _ (by rw [ePG_false_eq]; exact Fin.castSucc_ne_last _),
      colMat_of_ne _ _ _ (Fin.castSucc_ne_last _)]
    by_cases h : x = Fin.castSucc b
    · subst h; simp
    · rw [Matrix.one_apply_ne ((ePG I T).injective.ne (by simpa using h)), Matrix.one_apply_ne h]

theorem append_split (I T : ℕ) (v : Fin (I + T) → k) :
    v = Fin.append (fun a => v (Fin.castAdd T a)) (0 : Fin T → k) +
      Fin.append (0 : Fin I → k) (fun b => v (Fin.natAdd I b)) := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · simp
  · simp

theorem dEmb_eq (i t : ℕ) (d : Fin (t + 1) → k) : dEmb k i t d = uG (i + 1) (t + 1) (Fin.append 0 d) := rfl

def mv {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) : Fin ((i + 1) + (t + 1)) → k :=
  ((m : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v

theorem sEmb_mul_uG (i t : ℕ) (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) :
    sEmb k _ m * uG (i + 1) (t + 1) v = uG (i + 1) (t + 1) (mv m v) * sEmb k _ m := by
  apply Subtype.ext
  exact glEmb_mul_unip' k ((i + 1) + t + 1) (m : GL (Fin ((i + 1) + t + 1)) k) (Multiplicative.ofAdd v)

theorem dEmb_add (i t : ℕ) (d e : Fin (t + 1) → k) : dEmb k i t (d + e) = dEmb k i t d * dEmb k i t e := by
  rw [dEmb_eq, dEmb_eq, dEmb_eq, ← uG_add]
  congr 1
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x <;> simp

def keyC {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) : Fin (i + 1) → k :=
  fun a => mv m v (Fin.castAdd (t + 1) a)

def keyD {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) : Fin (t + 1) → k :=
  fun b => mv m v (Fin.natAdd (i + 1) b)

theorem keyD_last {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) :
    keyD m v (Fin.last t) = v (Fin.last _) := by
  have e : Fin.natAdd (i + 1) (Fin.last t) = Fin.last ((i + 1) + t) := Fin.ext (by simp)
  show mv m v (Fin.natAdd (i + 1) (Fin.last t)) = _
  rw [e]
  exact mulVec_last_of_mem k _ m.2 v

theorem key {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) (d : Fin (t + 1) → k) :
    dEmb k i t d * sEmb k _ m * uG (i + 1) (t + 1) v =
      uG (i + 1) (t + 1) (Fin.append (keyC m v) (0 : Fin (t + 1) → k)) *
        (dEmb k i t (d + keyD m v) * sEmb k _ m) := by
  have hs := append_split (i + 1) (t + 1) (mv m v)
  rw [mul_assoc, sEmb_mul_uG, ← mul_assoc, ← mul_assoc, dEmb_add]
  conv_lhs => rw [hs, uG_add]
  rw [dEmb_eq, dEmb_eq]
  congr 1
  rw [← mul_assoc, ← mul_assoc, uG_comm]
  rfl

theorem det_unip (n : ℕ) (c : Fin n → k) :
    Matrix.GeneralLinearGroup.det (unip k n (Multiplicative.ofAdd c)) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  show (1 + colMat k n c).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun x _ => ?_
    induction x using Fin.lastCases with
    | last => simp [colMat]
    | cast a => simp [colMat, Fin.castSucc_ne_last]
  · intro x y hxy
    have hy : y ≠ Fin.last n := fun e => by
      subst e
      exact absurd (Fin.le_last x) (not_le.2 hxy)
    rw [Matrix.add_apply, colMat_of_ne _ _ _ hy, add_zero]
    exact Matrix.one_apply_ne fun h => by
      subst h
      exact lt_irrefl _ hxy

theorem dpowM_of_unip (n : ℕ) (s : ℝ) (g : Mir k n) (c : Fin n → k)
    (hg : (g : GL (Fin (n + 1)) k) = unip k n (Multiplicative.ofAdd c)) : dpowM n s g = 1 := by
  show absPow k (s : ℂ) (Matrix.GeneralLinearGroup.det (g : GL (Fin (n + 1)) k)) = 1
  rw [hg, det_unip, map_one]

section Fibre
variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

theorem qC_sigX (c : Fin (i + 1) → k) (z : τ.V ⊗[ℂ] σ.V) :
    qC τ σ (sigX τ σ ⟨uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)), uG_mem_H _ _ c⟩ z) = qC τ σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul a b =>
    set g := (pgProj k (i + 1) (t + 1) ⟨uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)), uG_mem_H _ _ c⟩) with hgdef
    have hg2 : g.2 = 1 := pgProj_snd _ _ c
    have hg1 : ((g.1 : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) = unip k (i + 1) (Multiplicative.ofAdd c) :=
      pgProj_fst _ _ c
    have hmem : g.1 ∈ MirUin k (i + 1) := by
      show ((g.1 : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) ∈ MirU k (i + 1)
      rw [hg1]
      exact ⟨_, rfl⟩
    have e2 : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ g.1 a = τ.ρ g.1 a := by
      show ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) g.1 : ℂˣ) : ℂ) • τ.ρ g.1 a = _
      rw [dpowM_of_unip _ _ _ c hg1, Units.val_one, one_smul]
    have e3 : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ g.2 b = b := by
      rw [hg2, map_one]
      rfl
    have e : sigX τ σ ⟨uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)), uG_mem_H _ _ c⟩ (a ⊗ₜ b) =
        (τ.ρ g.1 a) ⊗ₜ[ℂ] b :=
      (extTensor_tmul _ _ _ _ _).trans (congrArg₂ (fun (x : τ.V) (y : σ.V) => x ⊗ₜ[ℂ] y) e2 e3)
    rw [e]
    show LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ _ = LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ _
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨g.1, hmem⟩, a, ?_⟩)
    simp

end Fibre

section Integral

def chi {t : ℕ} (ψ : AddChar k Circle) (d : Fin (t + 1) → k) : ℂ :=
  (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)

theorem chi_add {t : ℕ} (ψ : AddChar k Circle) (d e : Fin (t + 1) → k) :
    chi ψ d = ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) * chi ψ (d + e) := by
  unfold chi
  rw [← Units.val_mul, Pi.add_apply, AddChar.map_add_eq_mul, map_mul, mul_inv, mul_left_comm, mul_inv_cancel, mul_one]

theorem chi_lc {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    IsLocallyConstant (chi ψ : (Fin (t + 1) → k) → ℂ) :=
  ((GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous
    (continuous_apply (Fin.last t))).comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))

variable {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem chi_smul_lc {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {F : (Fin (t + 1) → k) → W}
    (l : IsLocallyConstant F) : IsLocallyConstant (fun d => chi ψ d • F d) :=
  (chi_lc ψ hψ).comp₂ l (fun a b => a • b)

theorem chi_smul_cs {t : ℕ} (ψ : AddChar k Circle) {F : (Fin (t + 1) → k) → W}
    (c : HasCompactSupport F) : HasCompactSupport (fun d => chi ψ d • F d) :=
  c.mono fun d hd h => hd (by simp [h])

theorem T_smInt {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (T : W →ₗ[ℂ] W') {F : (Fin (t + 1) → k) → W}
    (l : IsLocallyConstant F) (c : HasCompactSupport F) :
    T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F d)) =
      @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • T (F d)) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by unfold muD; infer_instance
  rw [← GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T (chi_smul_lc ψ hψ l) (chi_smul_cs ψ c)]
  congr 1
  funext d
  simp

theorem smInt_shift {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {F : (Fin (t + 1) → k) → W}
    (l : IsLocallyConstant F) (c : HasCompactSupport F) (e : Fin (t + 1) → k) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F (d + e)) =
      ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) •
        @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F d) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by unfold muD; infer_instance
  set θ : ℂ := ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) with hθ
  let T : W →ₗ[ℂ] W := θ • LinearMap.id
  have lΦ := chi_smul_lc ψ hψ l
  have h2 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T lΦ (chi_smul_cs ψ c)
  have h1 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp_measurePreserving (muD k (t + 1)) (c := (· + e))
    (φ := T ∘ fun d => chi ψ d • F d) (MeasureTheory.measurePreserving_add_right _ e)
    (lΦ.comp (fun x => T x))
  have h3 : (fun d => chi ψ d • F (d + e)) = (T ∘ fun d => chi ψ d • F d) ∘ (· + e) := by
    funext d
    simp only [Function.comp, T, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [← chi_add]
  rw [h3, h1, h2]
  rfl

theorem shift_abs {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (T : W →ₗ[ℂ] W')
    {F F' : (Fin (t + 1) → k) → W} (l : IsLocallyConstant F) (c : HasCompactSupport F)
    (l' : IsLocallyConstant F') (c' : HasCompactSupport F') (e : Fin (t + 1) → k)
    (hpt : ∀ d, T (F' d) = T (F (d + e))) :
    T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F' d)) =
      ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) •
        T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F d)) := by
  have lq : IsLocallyConstant (fun d => T (F d)) := l.comp (fun x => T x)
  have cq : HasCompactSupport (fun d => T (F d)) := c.comp_left (g := fun x => T x) (map_zero _)
  rw [T_smInt ψ hψ T l' c', T_smInt ψ hψ T l c, ← smInt_shift ψ hψ lq cq e]
  congr 1
  funext d
  rw [hpt]

end Integral

section Main
variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

theorem evX_cInd (f : XS τ σ) (g p : Mir k ((i + 1) + t + 1)) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

theorem evX_mul (f : XS τ σ) (h : HPG k (i + 1) (t + 1)) (p : Mir k ((i + 1) + t + 1)) :
    evX f ((h : Mir k ((i + 1) + t + 1)) * p) = sigX τ σ h (evX f p) := f.1.1.2 h p

theorem qC_evX (f : XS τ σ) (g y : Mir k ((i + 1) + t + 1)) (c : Fin (i + 1) → k) (e : Fin (t + 1) → k)
    (hk : ∀ d, dEmb k i t d * y * g =
      uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)) * (dEmb k i t (d + e) * y)) (d : Fin (t + 1) → k) :
    qC τ σ (evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) (dEmb k i t d * y)) =
      qC τ σ (evX f (dEmb k i t (d + e) * y)) := by
  have h1 : evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) (dEmb k i t d * y) =
      evX f (uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)) * (dEmb k i t (d + e) * y)) :=
    (evX_cInd τ σ f g _).trans (congrArg _ (hk d))
  have h2 := evX_mul τ σ f ⟨uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)), uG_mem_H _ _ c⟩
    (dEmb k i t (d + e) * y)
  exact (congrArg (qC τ σ) (h1.trans h2)).trans (qC_sigX τ σ c _)

theorem qC_intC_abs (ψ : AddChar k Circle) (hψ : Continuous ψ) (f f' : XS τ σ) (y : Mir k ((i + 1) + t + 1))
    (e : Fin (t + 1) → k)
    (hpt : ∀ d, qC τ σ (evX f' (dEmb k i t d * y)) = qC τ σ (evX f (dEmb k i t (d + e) * y))) :
    qC τ σ (intC ψ f' y) = ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) • qC τ σ (intC ψ f y) :=
  shift_abs ψ hψ (qC τ σ) (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2
    (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f' y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f' y).2 e hpt

theorem qC_intC_tw (ψ : AddChar k Circle) (hψ : Continuous ψ) (f : XS τ σ) (y g : Mir k ((i + 1) + t + 1))
    (c : Fin (i + 1) → k) (e : Fin (t + 1) → k)
    (hk : ∀ d, dEmb k i t d * y * g =
      uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)) * (dEmb k i t (d + e) * y)) :
    qC τ σ (intC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y) =
      ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) • qC τ σ (intC ψ f y) :=
  qC_intC_abs τ σ ψ hψ f _ y e (qC_evX τ σ f g y c e hk)

end Main

theorem eC_tw_at {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ) (m : Mir k ((i + 1) + t))
    (v : Multiplicative (Fin ((i + 1) + t + 1) → k))
    (hv : unip k ((i + 1) + t + 1) v = ((u : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)) :
    eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) m =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eC ψ f m := by
  have hu : (u : Mir k ((i + 1) + t + 1)) = uG (i + 1) (t + 1) v.toAdd := Subtype.ext hv.symm
  have hθ : ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) =
      ((Circle.toUnits (ψ (keyD m v.toAdd (Fin.last t))) : ℂˣ) : ℂ) := by
    rw [mirChar_eq k ψ _ u v hv.symm, keyD_last]
    rfl
  have h := qC_intC_tw τ σ ψ hψ f (sEmb k _ m) (u : Mir k ((i + 1) + t + 1)) (keyC m v.toAdd) (keyD m v.toAdd)
    (fun d => by rw [hu]; exact key m v.toAdd d)
  show ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ _ (sEmb k _ m)) =
    ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m))
  rw [h, hθ, smul_comm]

theorem eC_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eC ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ u f
  have h : ∃ v, unip k ((i + 1) + t + 1) v = ((u : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) := u.2
  exact funext fun m => eC_tw_at ψ hψ τ σ u f m h.choose h.choose_spec

end GlobalTheory.CompanionTheory.BZPhiPG.TwC

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_evaluation_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eC ψ f := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZPhiPG.TwC.eC_tw
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.TwO

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def uM (n : ℕ) (w : Fin n → k) : Mir k n :=
  ⟨unip k n (Multiplicative.ofAdd w), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem uM_add (n : ℕ) (v w : Fin n → k) : uM k n (v + w) = uM k n v * uM k n w := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd (v + w)) = unip k n (Multiplicative.ofAdd v) * unip k n (Multiplicative.ofAdd w)
  rw [ofAdd_add, map_mul]

theorem levi_mul_uM (n : ℕ) (g : GL (Fin n) k) (v : Fin n → k) :
    levi k n g * uM k n v = uM k n ((g : Matrix (Fin n) (Fin n) k).mulVec v) * levi k n g := by
  apply Subtype.ext
  exact glEmb_mul_unip' k n g (Multiplicative.ofAdd v)

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem ePG_false_castSucc_val (i t : ℕ) (a : Fin i) :
    ((ePG i t ⟨false, Fin.castSucc a⟩ : Fin (i + t + 1)) : ℕ) = a := by
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem piPerm_last (i t : ℕ) : piPerm i t (Fin.last ((i + 1) + t)) = Fin.castAdd (t + 1) (Fin.last i) := by
  have h1 : (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)) (Fin.last ((i + 1) + t)) = Fin.last (i + (t + 1)) :=
    Fin.ext (by simp)
  have h2 : (ePG i (t + 1)).symm (Fin.last (i + (t + 1))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq, ePG_false_last]
  show eGP (i + 1) t ((ePG i (t + 1)).symm ((finCongr _) (Fin.last ((i + 1) + t)))) = _
  rw [h1, h2]
  apply Fin.ext
  simp [eGP, stdSum]

def cVec (i t : ℕ) (c : Fin (i + 1) → k) : Fin ((i + 1) + (t + 1)) → k := Fin.append c (0 : Fin (t + 1) → k)

theorem unip_entry (n : ℕ) (w : Fin n → k) (a b : Fin (n + 1)) :
    ((uM k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b + colMat k n w a b := rfl

theorem ePG_true_ne_last (i t : ℕ) (b : Fin t) : ePG i t ⟨true, b⟩ ≠ Fin.last (i + t) := by
  intro h
  have := congrArg Fin.val h
  rw [ePG_true_val] at this
  simp at this
  omega

theorem ePG_true_eq_natAdd (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
  apply Fin.ext
  rw [ePG_true_val]
  simp

theorem ePG_false_eq_castAdd (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a) := by
  apply Fin.ext
  rw [ePG_false_castSucc_val]
  simp

theorem uM_mem_HPG (i t : ℕ) (c : Fin (i + 1) → k) : uM k _ (cVec i t c) ∈ HPG k (i + 1) (t + 1) := by
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k) ∈ parab k (ePG (i + 1) (t + 1))
  rw [mem_parab_iff]
  rintro (_ | _) (_ | _) x y hab
  · exact absurd hab (by decide)
  · exact absurd hab (by decide)
  · rw [unip_entry]
    have hne : ePG (i + 1) (t + 1) ⟨true, x⟩ ≠ ePG (i + 1) (t + 1) ⟨false, y⟩ := by
      intro h
      simpa using (ePG (i + 1) (t + 1)).injective h
    rw [Matrix.one_apply_ne hne, zero_add]
    simp only [colMat]
    split_ifs with hl
    · rw [ePG_true_eq_natAdd, Fin.lastCases_castSucc, cVec, Fin.append_right]
      rfl
    · rfl
  · exact absurd hab (by decide)

theorem pgProj_fst (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩).1 = uM k (i + 1) c := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k).val (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) =
    (1 : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b + colMat k (i + 1) c a b
  rw [unip_entry]
  congr 1
  · by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
      intro h
      apply hab
      simpa using (ePG (i + 1) (t + 1)).injective h
  · simp only [colMat]
    by_cases hb : b = Fin.last (i + 1)
    · subst hb
      rw [if_pos (ePG_false_last _ _), if_pos rfl]
      induction a using Fin.lastCases with
      | last => rw [ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]
      | cast a =>
        rw [ePG_false_eq_castAdd, Fin.lastCases_castSucc, Fin.lastCases_castSucc, cVec, Fin.append_left]
    · rw [if_neg (fun h => hb ((ePG_false_eq_last_iff _ _ _).1 h)), if_neg hb]

theorem pgProj_snd (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩).2 = 1 := by
  apply Units.ext
  ext a b
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k).val (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) =
    (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b
  rw [unip_entry]
  have h0 : colMat k _ (cVec i t c) (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = 0 := by
    simp only [colMat]
    rw [if_neg (ePG_true_ne_last _ _ _)]
  rw [h0, add_zero]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
    intro h
    apply hab
    simpa using (ePG (i + 1) (t + 1)).injective h

theorem det_uM (n : ℕ) (s : ℝ) (w : Fin n → k) : dpowM n s (uM k n w) = 1 := by
  have h : Matrix.GeneralLinearGroup.det ((uM k n w : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    ext
    show Matrix.det (1 + colMat k n w) = 1
    have hT : (1 + colMat k n w).BlockTriangular id := by
      intro a b hab
      have hab' : b < a := hab
      have hb : b ≠ Fin.last n := fun h => by
        rw [h] at hab'
        exact absurd hab' (not_lt.2 (Fin.le_last a))
      simp [colMat, hb, Matrix.one_apply_ne hab'.ne']
    rw [Matrix.det_of_upperTriangular hT]
    refine Finset.prod_eq_one fun a _ => ?_
    induction a using Fin.lastCases with
    | last => simp [colMat]
    | cast a => simp [colMat, Fin.castSucc_ne_last]
  show detChar (Fin (n + 1)) (absPow k ((s : ℝ) : ℂ)) ((uM k n w : Mir k n) : GL (Fin (n + 1)) k) = 1
  simp [detChar, h]

theorem mk_twist {n : ℕ} (ψ : AddChar k Circle) (τ : MRep k (n + 1)) (w : Fin (n + 1) → k) (a : τ.V) :
    (twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)).mkQ (τ.ρ (uM k (n + 1) w) a) =
      ((Circle.toUnits (ψ (w (Fin.last n))) : ℂˣ) : ℂ) •
        (twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)).mkQ a := by
  have hm : uM k (n + 1) w ∈ MirUin k (n + 1) := ⟨_, rfl⟩
  have hc := mirChar_eq k ψ n ⟨uM k (n + 1) w, hm⟩ (Multiplicative.ofAdd w) rfl
  have hk : τ.ρ (uM k (n + 1) w) a - ((mirChar k ψ n ⟨uM k (n + 1) w, hm⟩ : ℂˣ) : ℂ) • a ∈
      twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n) :=
    Submodule.subset_span ⟨⟨uM k (n + 1) w, hm⟩, a, rfl⟩
  have h := (Submodule.Quotient.mk_eq_zero _).2 hk
  rw [Submodule.Quotient.mk_sub, sub_eq_zero, Submodule.Quotient.mk_smul, hc] at h
  exact h

theorem qO_sigX {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (c : Fin (i + 1) → k)
    (z : τ.V ⊗[ℂ] σ.V) :
    qO τ σ ψ (sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ z) =
      ((Circle.toUnits (ψ (c (Fin.last i))) : ℂˣ) : ℂ) • qO τ σ ψ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  | tmul a b =>
    have e : sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ (a ⊗ₜ b) = τ.ρ (uM k (i + 1) c) a ⊗ₜ b := by
      have h1 := extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩) a b
      rw [pgProj_fst, pgProj_snd, map_one] at h1
      refine h1.trans ?_
      have h2 : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (uM k (i + 1) c) a = τ.ρ (uM k (i + 1) c) a := by
        show twist τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) (uM k (i + 1) c) a = _
        simp [twist, det_uM]
      rw [h2]
      rfl
    rw [e]
    show (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (uM k (i + 1) c) a) ⊗ₜ[ℂ] b = _
    rw [mk_twist]
    exact (TensorProduct.smul_tmul' _ _ _).symm

theorem vec_split (i t : ℕ) (c : Fin (i + 1) → k) (d d' : Fin (t + 1) → k) :
    Fin.append (0 : Fin (i + 1) → k) d + Fin.append c d' =
      cVec i t c + Fin.append (0 : Fin (i + 1) → k) (d + d') := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x <;> simp [cVec]

theorem dEmb_eq (i t : ℕ) (d : Fin (t + 1) → k) :
    dEmb k i t d = uM k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := rfl

theorem mul_uM_eq (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k)
    (c : Fin (i + 1) → k) (d d' : Fin (t + 1) → k)
    (hw : ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v = Fin.append c d') :
    dEmb k i t d * (wEl k i t * sEmb k _ m₀) * uM k _ v =
      uM k ((i + 1) + (t + 1)) (cVec i t c) * (dEmb k i t (d + d') * (wEl k i t * sEmb k _ m₀)) := by
  have hy : wEl k i t * sEmb k _ m₀ = levi k _ (wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k)) :=
    (map_mul (levi k _) _ _).symm
  have h1 := levi_mul_uM _ (wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k)) v
  rw [hw] at h1
  rw [hy, mul_assoc, h1, dEmb_eq, dEmb_eq, ← mul_assoc, ← mul_assoc]
  congr 1
  have e1 := uM_add (k := k) ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) (Fin.append c d')
  have e2 := uM_add (k := k) ((i + 1) + (t + 1)) (cVec i t c) (Fin.append (0 : Fin (i + 1) → k) (d + d'))
  rw [vec_split] at e1
  exact e1.symm.trans e2

theorem w_coord (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) :
    ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v
      (Fin.castAdd (t + 1) (Fin.last i)) = v (Fin.last ((i + 1) + t)) := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  show (Equiv.Perm.permMatrix k (piPerm i t)⁻¹).mulVec _ _ = _
  rw [Matrix.permMatrix_mulVec, ← piPerm_last]
  have h : (piPerm i t)⁻¹ (piPerm i t (Fin.last ((i + 1) + t))) = Fin.last ((i + 1) + t) := by simp
  simp only [Function.comp, h]
  exact mulVec_last_of_mem k _ m₀.2 v

theorem evX_cInd {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (g p : Mir k ((i + 1) + (t + 1))) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

theorem evX_mul {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (h : HPG k (i + 1) (t + 1))
    (p : Mir k ((i + 1) + (t + 1))) :
    evX f ((h : Mir k ((i + 1) + (t + 1))) * p) = sigX τ σ h (evX f p) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 h p

theorem intO_translate {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) (T : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] τ.V ⊗[ℂ] σ.V) (d' : Fin (t + 1) → k)
    (F : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V) (hF : ∀ d, F d = T (evX f (dEmb k i t (d + d') * y))) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) F = T (intO f y) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by
    unfold muD
    infer_instance
  obtain ⟨hl, hc⟩ := GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y
  let φ : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V := fun d => evX f (dEmb k i t d * y)
  have hl' : IsLocallyConstant (φ ∘ (· + d')) := hl.comp_continuous (continuous_add_right d')
  have hc' : HasCompactSupport (φ ∘ (· + d')) := hc.comp_homeomorph (Homeomorph.addRight d')
  have e : F = T ∘ (φ ∘ (· + d')) := funext hF
  have h2 : GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1)) (φ ∘ (· + d')) = GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1)) φ :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp_measurePreserving (muD k (t + 1))
      (MeasureTheory.measurePreserving_add_right (muD k (t + 1)) d') hl
  rw [e, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T hl' hc', h2]
  rfl

theorem intO_cInd_uM_eq_sigX_intO {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) (c : Fin (i + 1) → k) (d' : Fin (t + 1) → k)
    (hw : ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v = Fin.append c d') :
    intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) (wEl k i t * sEmb k _ m₀) =
      sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ (intO f (wEl k i t * sEmb k _ m₀)) := by
  refine intO_translate f _ (sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩) d' _ fun d => ?_
  have e := mul_uM_eq i t m₀ v c d d' hw
  refine (congrArg (evX f) e).trans ?_
  exact evX_mul f ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ _

def wV (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) : Fin ((i + 1) + (t + 1)) → k :=
  ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v

theorem qO_intO_cInd {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) :
    qO τ σ ψ (intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) (wEl k i t * sEmb k _ m₀)) =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) •
        qO τ σ ψ (intO f (wEl k i t * sEmb k _ m₀)) := by
  have hsplit : wV i t m₀ v = Fin.append (fun j => wV i t m₀ v (Fin.castAdd (t + 1) j))
      (fun j => wV i t m₀ v (Fin.natAdd (i + 1) j)) :=
    (Fin.append_castAdd_natAdd).symm
  have hc : wV i t m₀ v (Fin.castAdd (t + 1) (Fin.last i)) = v (Fin.last ((i + 1) + t)) := w_coord i t m₀ v
  have h1 := intO_cInd_uM_eq_sigX_intO ψ τ σ f m₀ v _ _ hsplit
  have h2 := qO_sigX ψ τ σ (fun j => wV i t m₀ v (Fin.castAdd (t + 1) j)) (intO f (wEl k i t * sEmb k _ m₀))
  refine (congrArg (qO τ σ ψ) h1).trans (h2.trans ?_)
  exact congrArg (fun x => ((Circle.toUnits (ψ x) : ℂˣ) : ℂ) • qO τ σ ψ (intO f (wEl k i t * sEmb k _ m₀))) hc

theorem eO_cInd_uM {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (v : Fin ((i + 1) + t + 1) → k) (m : Mir k (i + (t + 1))) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) m =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) • eO ψ f m :=
  (congrArg (fun z => ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) • z)
    (qO_intO_cInd ψ τ σ f (castM k (by omega) m) v)).trans (smul_comm _ _ _)

theorem exists_unip {n : ℕ} (u : MirUin k n) : ∃ v : Multiplicative (Fin n → k),
    unip k n v = ((u : Mir k n) : GL (Fin (n + 1)) k) := u.2

theorem eO_of_eq {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (g : Mir k ((i + 1) + (t + 1))) (v : Fin ((i + 1) + t + 1) → k) (m : Mir k (i + (t + 1)))
    (hg : g = uM k ((i + 1) + (t + 1)) v) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) m =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) • eO ψ f m := by
  subst hg
  exact eO_cInd_uM ψ τ σ f v m

theorem eO_cInd_eq_mirChar_smul {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ) (m : Mir k (i + (t + 1))) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) m =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f m := by
  refine Exists.elim (exists_unip u) fun v hv => ?_
  have hu : (u : Mir k ((i + 1) + (t + 1))) = uM k ((i + 1) + (t + 1)) v.toAdd := Subtype.ext hv.symm
  have hθ := mirChar_eq k ψ ((i + 1) + t) u v hv.symm
  refine (eO_of_eq ψ τ σ f _ v.toAdd m hu).trans ?_
  exact congrArg (fun x : ℂˣ => (x : ℂ) • eO ψ f m) hθ.symm

theorem eO_cInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f := by
  intro k _ _ _ _ i t ψ _ τ σ _ _ u f
  funext m
  exact eO_cInd_eq_mirChar_smul ψ τ σ u f m

end GlobalTheory.CompanionTheory.BZPhiPG.TwO

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_evaluation_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd
end

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Off

variable {k : Type} [Field k]

theorem sEmb_row (n : ℕ) (m : Mir k n) (j : Fin (n + 1 + 1)) :
    (((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
      (Fin.castSucc (Fin.last n)) j = (1 : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hs : ((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmb k (n + 1) (m : GL (Fin (n + 1)) k) := rfl
  have hm : Matrix.vecMul (GlobalTheory.BZMir.eLast k n) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.eLast k n := m.2
  rw [GlobalTheory.BZMir.vecMul_eLast] at hm
  rw [hs]
  show GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (Fin.castSucc (Fin.last n)) j = _
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne]
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
    rw [hm]
    by_cases hj : j' = Fin.last n
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · rw [Matrix.one_apply_ne (fun e => hj (Fin.castSucc_injective _ e).symm)]
      simp [GlobalTheory.BZMir.eLast, Pi.single_apply, hj]

theorem dEmb_mul_sEmb_mem_Cl (i t : ℕ) (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) :
    dEmb k i t d * sEmb k _ m ∈ Cl k i t := by
  simp only [Cl, Set.mem_ofPred_eq]
  intro c
  rw [_root_.mul_inv_rev, ← map_inv, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  simp_rw [sEmb_row]
  rw [← Matrix.mul_apply, Matrix.one_mul]
  show ((1 : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) -
      GlobalTheory.BZMir.colMat k (i + 1 + (t + 1)) (Fin.append 0 d)) _ _ = 0
  rw [Matrix.sub_apply]
  have hRC : (Fin.last (i + 1 + t)).castSucc ≠ (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  have hCL : (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) ≠ Fin.last (i + 1 + (t + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  rw [Matrix.one_apply_ne hRC]
  simp [GlobalTheory.BZMir.colMat, hCL]

end GlobalTheory.CompanionTheory.BZPhiPG.Off

open GlobalTheory.CompanionTheory.BZPhiPG.Off in

theorem GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
    eC ψ f = 0 := by
  intro k _ _ _ _ i t ψ τ σ hτ hσ f hf
  funext m
  have hz : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * sEmb k (i + 1 + t) m) = 0 :=
    fun d => hf _ (dEmb_mul_sEmb_mem_Cl i t d m)
  have hint : intC ψ f (sEmb k (i + 1 + t) m) = 0 := by
    unfold intC
    simp only [hz, smul_zero]
    unfold GlobalTheory.CompanionTheory.Rodier.smInt
    apply finsum_eq_zero_of_forall_eq_zero
    intro w
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have hpre : ((fun _ => (0 : TensorProduct ℂ τ.V σ.V)) : (Fin (t + 1) → k) → TensorProduct ℂ τ.V σ.V) ⁻¹' {w} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h0 => hw h0.symm
      rw [hpre, MeasureTheory.measure_empty]
      simp
  simp only [eC, hint, map_zero, smul_zero, Pi.zero_apply]

end
end

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_evaluation_vanishing_on_open : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  eC ψ f = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish
end

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}

theorem mcast_spec {a b : ℕ} (h : a = b) (Y : MRep k a) :
    ∃ e : Y.V ≃ₗ[ℂ] (mcast h Y).V, ∀ x v, e (Y.ρ x v) = (mcast h Y).ρ (castM k h x) (e v) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem dpowM_castM {a b : ℕ} (h : a = b) (s : ℝ) (x : Mir k a) : dpowM b s (castM k h x) = dpowM a s x := by
  subst h
  rfl

theorem mExt_mcast {a b : ℕ} (h : a = b) {A B C : MRep k a} (H : MExt A B C) :
    MExt (mcast h A) (mcast h B) (mcast h C) := by
  subst h
  exact H

theorem phiN_mcast (ψ : AddChar k Circle) {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (X : MRep k (a + 1)) :
    phiN ψ (mcast h' X) = mcast h (phiN ψ X) := by
  subst h
  rfl

theorem mcast_mcast {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (X : MRep k a) :
    mcast h₂ (mcast h₁ X) = mcast h₃ X := by
  subst h₁
  subst h₂
  rfl

theorem evX_cInd {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (g p : Mir k ((i + 1) + t + 1)) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

theorem intC_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intC ψ f (y * g) := by
  simp only [intC, evX_cInd, mul_assoc]

theorem intO_translate {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intO f (y * g) := by
  simp only [intO, evX_cInd, mul_assoc]

abbrev XR (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t + 1) := prodPGn (i := i + 1) (t := t + 1) τ σ

theorem eC_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (x m : Mir k ((i + 1) + t)) :
    eC ψ f (x * m) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) x := by
  simp only [eC, map_mul, Units.val_mul, intC_translate, smul_smul, mul_comm]

theorem eO_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (x m : Mir k (i + (t + 1))) :
    eO ψ f (x * m) = ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) •
      eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) (castM k (by omega : i + (t + 1) = (i + 1) + t) m)) f) x := by
  simp only [eO, map_mul, Units.val_mul, intO_translate, smul_smul, mul_comm, mul_assoc]

def XR' (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t + 1) :=
  ⟨XS τ σ, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)⟩

def RC (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t) :=
  ⟨cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), cInd (MirabolicParabolic k (i + 1) t) (sigC τ σ)⟩

def RO (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k (i + (t + 1)) :=
  ⟨cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), cInd (HPG k i (t + 1)) (sigO τ σ ψ)⟩

set_option maxHeartbeats 1000000 in
theorem xr_eq (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : XR τ σ = XR' τ σ := rfl

set_option maxHeartbeats 1000000 in
theorem rc_eq (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : prodGPn (psiN τ) (gres σ) = RC τ σ := rfl

set_option maxHeartbeats 1000000 in
theorem ro_eq (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) :
    prodPGn (phiN ψ τ) σ = RO ψ τ σ := rfl

theorem rho_eq (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    (phiN ψ (n := (i + 1) + t) (XR' τ σ)).ρ m (Submodule.Quotient.mk f) =
      ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) :
          TwJacquet (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t))) := rfl

def jC (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) :
    (RC τ σ).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (psiN τ).V ⊗[ℂ] σ.V) :=
  (indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)).subtype ∘ₗ (smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).subtype ∘ₗ
    (cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)).subtype

def mirabolicRestriction (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hh : i + (t + 1) = (i + 1) + t) :
    (RO ψ τ σ).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) :=
  (LinearMap.funLeft ℂ _ (fun m => (castM k hh).symm m)) ∘ₗ
    (indSpace (HPG k i (t + 1)) (sigO τ σ ψ)).subtype ∘ₗ (smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).subtype ∘ₗ
      (cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).subtype

theorem jC_inj (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : Function.Injective (jC τ σ) :=
  fun _ _ hab => Subtype.ext (Subtype.ext (Subtype.ext hab))

theorem jO0_inj (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hh : i + (t + 1) = (i + 1) + t) :
    Function.Injective (mirabolicRestriction ψ τ σ hh) := fun a b hab => by
  refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
  funext m
  have h2 : (a : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (castM k hh m)) =
      (b : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (castM k hh m)) := congrFun hab (castM k hh m)
  rw [MulEquiv.symm_apply_apply] at h2
  exact h2

def eCl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) : XS τ σ →ₗ[ℂ] (Mir k ((i + 1) + t) → (psiN τ).V ⊗[ℂ] σ.V) where
  toFun f := eC ψ f
  map_add' f g := (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f g 0).1
  map_smul' c f := (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f f c).2.1

def eOl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) :
    XS τ σ →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) where
  toFun f m := eO ψ f ((castM k hh).symm m)
  map_add' f g := by
    funext m
    exact congrFun (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f g 0).2.2.1 _
  map_smul' c f := by
    funext m
    exact congrFun (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f f c).2.2.2 _

theorem eOl_apply (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) (f : XS τ σ) (m : Mir k ((i + 1) + t)) :
    eOl ψ hψ τ σ hτ hσ hh f m = eO ψ f ((castM k hh).symm m) := rfl

theorem aO_eOl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    rightReg ℂ _ _ m (eOl ψ hψ τ σ hτ hσ hh f) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eOl ψ hψ τ σ hτ hσ hh (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) := by
  funext x
  show eO ψ f ((castM k hh).symm (x * m)) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) ((castM k hh).symm x)
  have e1 := map_mul (castM k hh).symm x m
  have e2 := eO_translate ψ f ((castM k hh).symm x) ((castM k hh).symm m)
  have e3 : castM k hh ((castM k hh).symm m) = m := MulEquiv.apply_symm_apply _ _
  have e4 : dpowM (i + (t + 1)) (-1 / 2) ((castM k hh).symm m) = dpowM ((i + 1) + t) (-1 / 2) m := by
    have := dpowM_castM (k := k) hh (-1 / 2) ((castM k hh).symm m)
    rw [e3] at this
    exact this.symm
  have e6 := congrArg (fun g => eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) g) f)
    ((castM k hh).symm x)) e3
  have e7 : ((dpowM (i + (t + 1)) (-1 / 2) ((castM k hh).symm m) : ℂˣ) : ℂ) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) :=
    congrArg _ e4
  exact (congrArg (eO ψ f) e1).trans (e2.trans (congrArg₂ (· • ·) e7 e6))

theorem aC_eCl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    rightReg ℂ _ _ m (eCl ψ hψ τ σ hτ hσ f) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eCl ψ hψ τ σ hτ hσ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) := by
  funext x
  exact eC_translate ψ f x m

set_option maxHeartbeats 1000000 in
theorem phiPG_core (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) :
    MExt (mcast (by omega : i + (t + 1) = (i + 1) + t) (RO ψ τ σ)) (phiN ψ (n := (i + 1) + t) (XR' τ σ)) (RC τ σ) := by
  have hh : i + (t + 1) = (i + 1) + t := by omega
  obtain ⟨hUn, hθ, hCc, hHC, hCU, hdir⟩ := GlobalTheory.T.mirabolic_cell_structure_data k ψ hψ i t
  obtain ⟨e, he⟩ := mcast_spec hh (RO ψ τ σ)
  let jOl : (mcast hh (RO ψ τ σ)).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) :=
    mirabolicRestriction ψ τ σ hh ∘ₗ e.symm.toLinearMap
  have hjOl : Function.Injective jOl := (jO0_inj ψ τ σ hh).comp e.symm.injective
  have hes : ∀ (m : Mir k ((i + 1) + t)) v, e.symm ((mcast hh (RO ψ τ σ)).ρ m v) =
      (RO ψ τ σ).ρ ((castM k hh).symm m) (e.symm v) := by
    intro m v
    rw [LinearEquiv.symm_apply_eq, he, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hjOe : ∀ m v, jOl ((mcast hh (RO ψ τ σ)).ρ m v) = rightReg ℂ _ _ m (jOl v) := by
    intro m v
    show mirabolicRestriction ψ τ σ hh (e.symm _) = _
    rw [hes]
    funext x
    show (e.symm v : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm x * (castM k hh).symm m) =
      (e.symm v : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (x * m))
    rw [map_mul]
  exact GlobalTheory.T.twisted_jacquet_closed_open_sequence (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) hUn (mirChar k ψ ((i + 1) + t)) hθ hdir
    (sEmb k ((i + 1) + t)) (dpowM ((i + 1) + t) (-1 / 2)) (phiN ψ (n := (i + 1) + t) (XR' τ σ)).ρ (fun m f => rho_eq ψ τ σ m f)
    (Cl k i t) hCc hHC hCU
    (RC τ σ).ρ (mcast hh (RO ψ τ σ)).ρ
    (rightReg ℂ _ _) (rightReg ℂ _ _) (jC τ σ) jOl (jC_inj τ σ) hjOl (fun m v => rfl) hjOe
    (eCl ψ hψ τ σ hτ hσ) (eOl ψ hψ τ σ hτ hσ hh)
    (fun u f => GlobalTheory.T.closed_evaluation_equivariant k i t ψ hψ τ σ hτ hσ u f)
    (fun u f => by
      funext m
      exact congrFun (GlobalTheory.T.open_evaluation_equivariant k i t ψ hψ τ σ hτ hσ u f) _)
    (fun m f => aC_eCl ψ hψ τ σ hτ hσ m f)
    (fun m f => aO_eOl ψ hψ τ σ hτ hσ hh m f)
    (fun f => by
      obtain ⟨y, hy⟩ := GlobalTheory.T.closed_evaluation_induced k i t ψ hψ τ σ hτ hσ f
      exact ⟨y, hy⟩)
    (fun f hf => by
      obtain ⟨y, hy⟩ := GlobalTheory.T.open_evaluation_induced k i t ψ hψ τ σ hτ hσ f hf
      refine ⟨e y, ?_⟩
      funext m
      have e1 : e.symm (e y) = y := e.symm_apply_apply y
      exact (congrArg (fun z => mirabolicRestriction ψ τ σ hh z m) e1).trans (congrFun hy _))
    (fun v => GlobalTheory.T.closed_evaluation_surjective k i t ψ hψ τ σ hτ hσ v)
    (fun v => by
      obtain ⟨f, hf, hy⟩ := GlobalTheory.T.open_evaluation_surjective k i t ψ hψ τ σ hτ hσ (e.symm v)
      refine ⟨f, hf, ?_⟩
      funext m
      exact congrFun hy _)
    (fun f hf => GlobalTheory.T.closed_evaluation_vanishing_on_open k i t ψ τ σ hτ hσ f hf)
    (fun f h0 p hp => GlobalTheory.T.average_vanishes_closed_cell k i t ψ hψ τ σ hτ hσ f h0 p hp)
    (fun f h0 p hp => GlobalTheory.T.average_vanishes_open_cell k i t ψ hψ τ σ hτ hσ f (by
      funext m
      have := congrFun h0 (castM k hh m)
      rw [eOl_apply, MulEquiv.symm_apply_apply] at this
      exact this) p hp)

theorem phiPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG k := by
  intro k _ _ _ _ ψ hψ _ i t τ σ hτ hσ
  have h0 : (i + 1) + t = i + t + 1 := by omega
  have H := mExt_mcast h0 (phiPG_core ψ hψ i t τ σ hτ hσ)
  rw [mcast_mcast _ _ (by omega : i + (t + 1) = i + t + 1), ← ro_eq, ← xr_eq, ← rc_eq] at H
  rw [phiN_mcast ψ h0 (by omega)]
  exact H

end GlobalTheory.CompanionTheory.BZPhiPG

end
end
