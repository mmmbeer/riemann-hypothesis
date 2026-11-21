import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

section
noncomputable section

namespace GlobalTheory.DefDoubling

open MeasureTheory Filter Topology Set GlobalTheory.Eis GlobalTheory.Cont GlobalTheory.Doubling GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal

section Unfold

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
  {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G}

theorem lintegral_tsum_eq (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x in 𝓕, ∑' γ : Γ, f (γ * x) ∂μ = ∫⁻ x, f x ∂μ := by
  rw [h.lintegral_eq_tsum'' f, lintegral_tsum (f := fun (γ : Γ) x => f (γ * x)) fun γ : Γ =>
    (hf.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict]
  rfl

theorem integral_tsum_eq (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℂ} (hf : Integrable f μ) :
    IntegrableOn (fun x => ∑' γ : Γ, f (γ * x)) 𝓕 μ ∧ ∫ x in 𝓕, ∑' γ : Γ, f (γ * x) ∂μ = ∫ x, f x ∂μ := by
  have hm : ∀ γ : Γ, AEStronglyMeasurable (fun x => f (γ * x)) (μ.restrict 𝓕) := fun γ =>
    (hf.1.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict
  have hl : ∑' γ : Γ, ∫⁻ x in 𝓕, ‖f (γ * x)‖ₑ ∂μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    rw [← lintegral_tsum fun γ => (hm γ).enorm, lintegral_tsum_eq h hf.1.enorm]
  refine ⟨⟨AEStronglyMeasurable.tsum hm, ?_⟩, ?_⟩
  · refine lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun γ => (hm γ).enorm, hl]
    exact hf.2
  · rw [integral_tsum hm (hl ▸ hf.2.ne), h.integral_eq_tsum'' f hf]
    rfl

end Unfold

section Dbl

variable {G G₂ : Type} [Group G] [Group G₂] (i : G × G →* G₂) {P Γ₂ : Subgroup G₂} {Γ : Subgroup G} {r : Γ → Γ₂}

theorem cosetSum_io {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) (hri : ∀ δ, (r δ : G₂) = i (1, δ))
    (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ)) (h x : G) :
    cosetSum P Γ₂ Φ (i (h, x)) = ∑' δ : Γ, Φ (i (h, δ * x)) ∧
      (CosetConv P Γ₂ Φ (i (h, x)) ↔ Summable fun δ : Γ => ‖Φ (i (h, δ * x))‖) := by
  have e : ∀ δ : Γ, (r δ : G₂) * i (h, x) = i (h, δ * x) := fun δ => by
    rw [hri, ← map_mul, Prod.mk_mul_mk, one_mul]
  refine ⟨(cosetSum_eq_tsum hΦ hr _).trans (tsum_congr fun δ => by rw [e]), ?_⟩
  rw [cosetConv_iff hΦ hr]
  exact summable_congr fun δ => by rw [e]

variable [MeasurableSpace G] [MeasurableMul G] [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G}

theorem unfold_core (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ)
    (hri : ∀ δ, (r δ : G₂) = i (1, δ)) (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ))
    {c : G → ℂ} (hlaw : ∀ h y, Φ (i (h, h) * y) = c h * Φ y) {w : G → ℂ} (hw : ∀ x y, w (x * y) = w x * w y)
    (hwΓ : ∀ γ ∈ Γ, w γ = 1) (hw1 : ∀ x, ‖w x‖ = 1) (hwm : AEStronglyMeasurable w μ)
    (hm : ∀ h, AEStronglyMeasurable (fun x => Φ (i (h, x))) μ) (h : G)
    (hfin : ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun g => Φ (i (1, g)) * w g) μ ∧ IntegrableOn (fun x => cosetSum P Γ₂ Φ (i (h, x)) * w x) 𝓕 μ ∧
      ∫ x in 𝓕, cosetSum P Γ₂ Φ (i (h, x)) * w x ∂μ = c h * w h * ∫ g, Φ (i (1, g)) * w g ∂μ := by
  set F : G → ℂ := fun x => Φ (i (h, x)) * w x with hF
  have hFm : AEStronglyMeasurable F μ := (hm h).mul hwm
  have hFn : ∀ x, ‖F x‖ₑ = ‖Φ (i (h, x))‖ₑ := fun x => by
    rw [hF, enorm_mul, ← ofReal_norm_eq_enorm (w x), hw1, ENNReal.ofReal_one, mul_one]
  have hFi : Integrable F μ := by
    refine ⟨hFm, ?_⟩
    rw [HasFiniteIntegral, lintegral_congr (fun x => hFn x), ← lintegral_tsum_eq h𝓕 (hm h).enorm]
    exact lt_top_iff_ne_top.2 hfin
  have hδ : ∀ x, ∑' δ : Γ, F (δ * x) = cosetSum P Γ₂ Φ (i (h, x)) * w x := fun x => by
    rw [(cosetSum_io i hΦ hri hr h x).1, ← tsum_mul_right]
    exact tsum_congr fun δ => by
      show Φ _ * w (δ * x) = _
      rw [hw, hwΓ _ δ.2, one_mul]
  have hsh : ∀ x, F (h * x) = c h * w h * (Φ (i (1, x)) * w x) := fun x => by
    have : i (h, h * x) = i (h, h) * i (1, x) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rw [hF]; simp only [this, hlaw, hw]; ring
  have hsh' : ∀ x, Φ (i (1, x)) * w x = c h⁻¹ * w h⁻¹ * F (h * x) := fun x => by
    have : i (1, x) = i (h⁻¹, h⁻¹) * i (h, h * x) := by
      rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel_left]
    have hx : w x = w h⁻¹ * w (h * x) := by rw [← hw, inv_mul_cancel_left]
    rw [hF]; simp only [this, hlaw, hx]; ring
  have hFh : Integrable (fun x => F (h * x)) μ := hFi.comp_mul_left h
  obtain ⟨h1, h2⟩ := integral_tsum_eq h𝓕 hFi
  refine ⟨(hFh.const_mul (c h⁻¹ * w h⁻¹)).congr (Eventually.of_forall fun x => (hsh' x).symm), ?_, ?_⟩
  · exact Integrable.congr h1 (Eventually.of_forall hδ)
  · rw [← setIntegral_congr_fun₀ ?_ (fun x _ => hδ x), h2, ← integral_mul_left_eq_self F h]
    · simp only [hsh]; rw [integral_const_mul]
    · exact h𝓕.nullMeasurableSet

end Dbl

section Passage

variable {s₀ : ℂ}

theorem holValueAt_sum {ι : Type} (T : Finset ι) {f : ι → ℂ → ℂ} {z : ι → ℂ}
    (h : ∀ j ∈ T, HolValueAt (f j) s₀ (z j)) : HolValueAt (fun s => ∑ j ∈ T, f j s) s₀ (∑ j ∈ T, z j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem holValueAt_integral_of_expansion {X ι : Type} [MeasurableSpace X] {ν : Measure X} [Fintype ι]
    {Φ : ℂ → X → ℂ} {Ψ : X → ℂ} {c : ι → X → ℂ} {v : ι → ℂ → ℂ} {w : ι → ℂ} {σ : ℝ}
    (hc : ∀ j, Integrable (c j) ν) (hexp : ∀ s : ℂ, σ < s.re → ∀ x, Φ s x = ∑ j, c j x * v j s)
    (hv : ∀ j, HolValueAt (v j) s₀ (w j)) (hΨ : ∀ x, HolValueAt (fun s => Φ s x) s₀ (Ψ x)) :
    (∀ x, Ψ x = ∑ j, c j x * w j) ∧ Integrable Ψ ν ∧ HolValueAt (fun s => ∫ x, Φ s x ∂ν) s₀ (∫ x, Ψ x ∂ν) := by
  have hΨe : ∀ x, Ψ x = ∑ j, c j x * w j := fun x =>
    (hΨ x).unique ((holValueAt_sum Finset.univ fun j _ => (holValueAt_const (c j x) s₀).mul (hv j)).congr
      ⟨σ, fun s hs => (hexp s hs x).symm⟩)
  have hΨi : Integrable Ψ ν := by
    rw [funext hΨe]
    exact integrable_finset_sum _ fun j _ => (hc j).mul_const (w j)
  refine ⟨hΨe, hΨi, ?_⟩
  have e1 : ∫ x, Ψ x ∂ν = ∑ j, (∫ x, c j x ∂ν) * w j := by
    rw [funext hΨe, integral_finset_sum _ fun j _ => (hc j).mul_const (w j)]
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
  rw [e1]
  refine (holValueAt_sum Finset.univ fun j _ => (holValueAt_const (∫ x, c j x ∂ν) s₀).mul (hv j)).congr
    ⟨σ, fun s hs => ?_⟩
  simp only
  rw [integral_congr_ae (Eventually.of_forall (hexp s hs)),
    integral_finset_sum _ fun j _ => (hc j).mul_const (v j s)]
  exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm

end Passage

section Expansion

variable {G₂ : Type} [Group G₂] {P Γ₂ K : Subgroup G₂} {ι : Type} [Fintype ι] {kk : ι → G₂} {c : ι → G₂ → ℂ}

theorem flatSec_expansion {δ : P →* ℝ≥0} (hI : IsIwasawa δ K) {f : G₂ → ℂ} (hkk : ∀ j, kk j ∈ K)
    (hexp : ∀ g, ∀ k ∈ K, f (g * k) = ∑ j, c j k * f (g * kk j)) (s₀ s : ℂ) (g : G₂) {k : G₂} (hk : k ∈ K) :
    flatSec δ K f s₀ s (g * k) = ∑ j, c j k * flatSec δ K f s₀ s (g * kk j) := by
  simp only [flatSec, hI.iwAbs_right g hk, hI.iwAbs_right g (hkk _), hexp g k hk, Finset.sum_mul, mul_assoc]

theorem cosetSum_expansion {Φ : G₂ → ℂ} (hexp : ∀ g, ∀ k ∈ K, Φ (g * k) = ∑ j, c j k * Φ (g * kk j)) (y : G₂)
    (hconv : ∀ j, CosetConv P Γ₂ Φ (y * kk j)) {k : G₂} (hk : k ∈ K) :
    cosetSum P Γ₂ Φ (y * k) = ∑ j, c j k * cosetSum P Γ₂ Φ (y * kk j) := by
  have e : ∀ q, term P Γ₂ Φ (y * k) q = ∑ j, c j k * term P Γ₂ Φ (y * kk j) q := fun q => by
    simp only [term, ← mul_assoc]
    exact hexp _ k hk
  rw [cosetSum, tsum_congr e, Summable.tsum_finsetSum fun j _ => ((hconv j).of_norm).mul_left (c j k)]
  exact Finset.sum_congr rfl fun j _ => tsum_mul_left

theorem cosetSum_norm_expansion {Φ : G₂ → ℂ} (hexp : ∀ g, ∀ k ∈ K, Φ (g * k) = ∑ j, c j k * Φ (g * kk j))
    (y : G₂) {k : G₂} (hk : k ∈ K) :
    ∑' q, ‖term P Γ₂ Φ (y * k) q‖ₑ ≤ ∑ j, ‖c j k‖ₑ * ∑' q, ‖term P Γ₂ Φ (y * kk j) q‖ₑ := by
  have e : ∀ q, ‖term P Γ₂ Φ (y * k) q‖ₑ ≤ ∑ j, ‖c j k‖ₑ * ‖term P Γ₂ Φ (y * kk j) q‖ₑ := fun q => by
    simp only [term, ← mul_assoc]
    rw [hexp _ k hk]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (enorm_mul _ _).le)
  refine (ENNReal.tsum_le_tsum e).trans ?_
  rw [Summable.tsum_finsetSum fun j _ => ENNReal.summable]
  exact le_of_eq (Finset.sum_congr rfl fun j _ => ENNReal.tsum_mul_left)

end Expansion

section Cover

theorem measure_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {C : Set G}
    (hcov : ∀ x, ∃ γ : Γ, (γ : G) * x ∈ C) : μ 𝓕 ≤ μ C := by
  rw [h𝓕.measure_eq_tsum C]
  refine le_trans (measure_mono fun x hx => ?_) (measure_iUnion_le _)
  obtain ⟨γ, hγ⟩ := hcov x
  exact mem_iUnion.2 ⟨γ⁻¹, Set.mem_smul_set_iff_inv_smul_mem.2 (by simpa [Subgroup.smul_def] using hγ), hx⟩

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ K : Subgroup G} [Countable Γ]

theorem measure_lt_top_of_cover {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hKc : IsCompact (K : Set G)) (A : Finset G)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) : μ 𝓕 < ⊤ := by
  refine lt_of_le_of_lt (measure_le_of_cover h𝓕 (C := ⋃ a ∈ A, (a * ·) '' (K : Set G)) fun x => ?_)
    ((A.isCompact_biUnion fun a _ => hKc.image (continuous_mul_left a)).measure_lt_top)
  obtain ⟨a, ha, γ, hγ, k, hk, rfl⟩ := hcov x
  exact ⟨⟨γ⁻¹, inv_mem hγ⟩, mem_biUnion ha ⟨k, hk, by simp [mul_assoc]⟩⟩

open Classical in

theorem exists_coeff (hK : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (A : Finset G)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) {ι : Type} [Fintype ι] (c : ι → G → ℂ)
    (hc : ∀ j, Continuous (c j)) :
    ∃ C : G → ι → G → ℂ, (∀ a j, Measurable (C a j)) ∧ (∃ M : ℝ, ∀ a j x, ‖C a j x‖ ≤ M) ∧
      ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k ∧ ∀ a' j, C a' j x = if a' = a then c j k else 0 := by
  classical
  haveI : Nonempty (Γ × A) := by
    obtain ⟨a, ha, γ, hγ, -⟩ := hcov 1
    exact ⟨(⟨γ, hγ⟩, ⟨a, ha⟩)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Γ × A)
  set y : ℕ → G → G := fun n x => ((e n).2 : G)⁻¹ * ((e n).1 : G)⁻¹ * x with hy
  have hyc : ∀ n, Continuous (y n) := fun n => continuous_const.mul continuous_id
  have hex : ∀ x, ∃ n, y n x ∈ K := fun x => by
    obtain ⟨a, ha, γ, hγ, k, hk, rfl⟩ := hcov x
    obtain ⟨n, hn⟩ := he (⟨γ, hγ⟩, ⟨a, ha⟩)
    exact ⟨n, by simpa [hy, hn, mul_assoc] using hk⟩
  have hM : ∀ j, ∃ M, ∀ x ∈ K, ‖c j x‖ ≤ M := fun j => hKc.exists_bound_of_continuousOn (hc j).continuousOn
  choose M hM using hM
  refine ⟨fun a' j x => if a' = ((e (Nat.find (hex x))).2 : G) then c j (y (Nat.find (hex x)) x) else 0,
    fun a' j => ?_, ⟨∑ j, |M j|, fun a' j x => ?_⟩, fun x => ?_⟩
  · refine Measurable.find (f := fun n x => if a' = ((e n).2 : G) then c j (y n x) else 0)
      (p := fun n x => y n x ∈ K) (fun n => ?_) (fun n => (hK.preimage (hyc n)).measurableSet) hex
    by_cases h : a' = ((e n).2 : G)
    · simp only [h, ite_true]; exact ((hc j).comp (hyc n)).measurable
    · simpa [h] using measurable_const
  · dsimp only
    split_ifs
    · exact (hM j _ (Nat.find_spec (hex x))).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))
    · rw [norm_zero]; exact Finset.sum_nonneg fun j _ => abs_nonneg _
  · refine ⟨((e (Nat.find (hex x))).2 : G), (e (Nat.find (hex x))).2.2, ((e (Nat.find (hex x))).1 : G),
      (e (Nat.find (hex x))).1.2, y (Nat.find (hex x)) x, Nat.find_spec (hex x), by simp [hy, mul_assoc], fun a' j => rfl⟩

end Cover

end GlobalTheory.DefDoubling
end
end

section
namespace GlobalTheory.Doubling

theorem translate_eq_sum_of_isKFinite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} {f : G → ℂ} (hf : Continuous f) (hK : IsKFinite K f) :
    ∃ (m : ℕ) (kk : Fin m → G) (c : Fin m → G → ℂ), (∀ j, kk j ∈ K) ∧ (∀ j, Continuous (c j)) ∧
      ∀ g, ∀ k ∈ K, f (g * k) = ∑ j, c j k * f (g * kk j) := by
  classical
  set S : Set (G → ℂ) := {Ψ | ∃ k ∈ K, Ψ = fun g => f (g * k)} with hS
  haveI : Module.Finite ℂ (Submodule.span ℂ S) := hK
  obtain ⟨b, hbS, hspan, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ S
  choose kk hkk hb using hbS
  set V := Submodule.span ℂ (Set.range b) with hV
  let B := Module.Basis.span hli
  haveI : FiniteDimensional ℂ V := Module.Finite.of_basis B
  let ev : G → Module.Dual ℂ V := fun g => (LinearMap.proj g).comp V.subtype
  have hev : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      ext g
      exact hv (ev g) (Submodule.subset_span ⟨g, rfl⟩)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have ha : ∀ j, ∃ a : G →₀ ℂ, (a.sum fun g x => x • ev g) = B.coord j := fun j =>
    (Finsupp.mem_span_range_iff_exists_finsupp).1 (hev ▸ Submodule.mem_top)
  choose a ha using ha
  refine ⟨_, kk, fun j k => (a j).sum fun i x => x * f (i * k), hkk, fun j => ?_, fun g k hk => ?_⟩
  · simp only [Finsupp.sum]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (hf.comp (continuous_mul_left i))
  · have hw : (fun g => f (g * k)) ∈ V := by
      have h := Submodule.subset_span (R := ℂ) (s := S) ⟨k, hk, rfl⟩
      rw [← hspan] at h
      exact h
    set w : V := ⟨_, hw⟩ with hwdef
    have e := congrArg (fun v : V => (v : G → ℂ) g) (B.sum_repr w)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, B,
      Module.Basis.span_apply, hwdef] at e
    have hc : ∀ j, B.repr w j = (a j).sum fun i x => x * f (i * k) := fun j => by
      rw [← Module.Basis.coord_apply, ← ha j]
      simp [Finsupp.sum, LinearMap.sum_apply, ev, hwdef]
    rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j]
    exact congrArg (fun x => x * f (g * kk j)) (hc j)

end GlobalTheory.Doubling
end

section
noncomputable section

namespace GlobalTheory.DefDoubling

open MeasureTheory Filter Topology Set GlobalTheory.Eis GlobalTheory.Cont GlobalTheory.Doubling GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal

section Main

variable {G G₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  {i : G × G →* G₂} {P Γ₂ K₂ : Subgroup G₂} {Γ K : Subgroup G} [Countable Γ] {r : Γ → Γ₂}
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G} {A : Finset G}
  {ι : Type} [Fintype ι] {kk : ι → G₂} {cc : ι → G₂ → ℂ}

theorem tsum_enorm_term_mul_left {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) {γ : G₂} (hγ : γ ∈ Γ₂) (g : G₂) :
    ∑' q, ‖term P Γ₂ Φ (γ * g) q‖ₑ = ∑' q, ‖term P Γ₂ Φ g q‖ₑ :=
  (tsum_congr fun q => by rw [term_mul_left hΦ ⟨γ, hγ⟩ g q]).trans ((rmulEquiv P Γ₂ ⟨γ, hγ⟩).tsum_eq fun q => ‖term P Γ₂ Φ g q‖ₑ)

theorem unfold (hi : Continuous i) (hri : ∀ δ, (r δ : G₂) = i (1, δ))
    (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ)) (hK : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hKK : ∀ k ∈ K, i (1, k) ∈ K₂)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) (hΦc : Continuous Φ) (hcc : ∀ j, Continuous (cc j))
    (hexp : ∀ g, ∀ k ∈ K₂, Φ (g * k) = ∑ j, cc j k * Φ (g * kk j)) (hconv : ∀ g, CosetConv P Γ₂ Φ g)
    {c : G → ℂ} (hlaw : ∀ h y, Φ (i (h, h) * y) = c h * Φ y) {w : G → ℂ} (hwc : Continuous w)
    (hw : ∀ x y, w (x * y) = w x * w y) (hwΓ : ∀ γ ∈ Γ, w γ = 1) (hw1 : ∀ x, ‖w x‖ = 1) (h : G) :
    Integrable (fun g => Φ (i (1, g)) * w g) μ ∧ IntegrableOn (fun x => cosetSum P Γ₂ Φ (i (h, x)) * w x) 𝓕 μ ∧
      ∫ x in 𝓕, cosetSum P Γ₂ Φ (i (h, x)) * w x ∂μ = c h * w h * ∫ g, Φ (i (1, g)) * w g ∂μ := by
  have hm : ∀ h, AEStronglyMeasurable (fun x => Φ (i (h, x))) μ := fun h =>
    (hΦc.comp (hi.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  obtain ⟨C, -, ⟨M, hM⟩, hC⟩ := exists_coeff (Γ := Γ) hK hKc A hcov (fun j k => cc j (i (1, k)))
    fun j => (hcc j).comp (hi.comp (continuous_const.prodMk continuous_id))

  set S : G₂ → ℝ≥0∞ := fun g => ∑' q, ‖term P Γ₂ Φ g q‖ₑ with hS
  have hSfin : ∀ g, S g ≠ ⊤ := fun g => by
    have := ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg (term P Γ₂ Φ g q)) (hconv g)
    simp only [ofReal_norm] at this
    change ∑' q, ‖term P Γ₂ Φ g q‖ₑ ≠ ⊤
    rw [← this]
    exact ENNReal.ofReal_ne_top
  set B : ℝ≥0∞ := ∑ a ∈ A, ∑ j, ‖(M : ℂ)‖ₑ * S (i (h, a) * kk j) with hB
  have hδ : ∀ x, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ = S (i (h, x)) := fun x => by
    change _ = ∑' q, ‖term P Γ₂ Φ (i (h, x)) q‖ₑ
    rw [← (Equiv.ofBijective _ hr).tsum_eq]
    refine tsum_congr fun δ => ?_
    rw [Equiv.ofBijective_apply, term_mk hΦ, hri, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hbd : ∀ x, S (i (h, x)) ≤ B := fun x => by
    obtain ⟨a, ha, γ, hγ, k, hk, rfl, hCx⟩ := hC x
    have e : i (h, γ * a * k) = i (1, γ) * (i (h, a) * i (1, k)) := by
      simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one, mul_assoc]
    have hγ2 : i (1, γ) ∈ Γ₂ := hri ⟨γ, hγ⟩ ▸ (r ⟨γ, hγ⟩).2
    change ∑' q, ‖term P Γ₂ Φ _ q‖ₑ ≤ B
    rw [e, tsum_enorm_term_mul_left hΦ hγ2]
    refine (cosetSum_norm_expansion hexp _ (hKK k hk)).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ j, ‖(M : ℂ)‖ₑ * S (i (h, a) * kk j))
      (fun _ _ => zero_le) ha)
    refine Finset.sum_le_sum fun j _ => mul_le_mul_left ?_ _
    have := hM a j (γ * a * k)
    rw [hCx a j, if_pos rfl] at this
    rw [enorm_le_iff_norm_le, Complex.norm_real, Real.norm_eq_abs]
    exact this.trans (le_abs_self M)
  have hBfin : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun a _ => ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.mul_ne_top enorm_ne_top (hSfin _)
  have hfin : ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hBfin (measure_lt_top_of_cover h𝓕 hKc A hcov).ne) ?_
    calc ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≤ ∫⁻ _ in 𝓕, B ∂μ :=
          lintegral_mono fun x => (hδ x).trans_le (hbd x)
      _ = B * μ 𝓕 := setLIntegral_const 𝓕 B
  exact unfold_core i h𝓕 hΦ hri hr hlaw hw hwΓ hw1 hwc.aestronglyMeasurable hm h hfin

theorem holValueAt_integral (hi : Continuous i) (hΓ₂ : ∀ γ ∈ Γ, i (1, γ) ∈ Γ₂) (hK : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hKK : ∀ k ∈ K, i (1, k) ∈ K₂)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : ℂ → G₂ → ℂ} {σ : ℝ} (hΦ : ∀ s : ℂ, σ < s.re → LeftInv (P ⊓ Γ₂) (Φ s)) (hcc : ∀ j, Continuous (cc j))
    (hexp : ∀ s : ℂ, σ < s.re → ∀ g, ∀ k ∈ K₂, Φ s (g * k) = ∑ j, cc j k * Φ s (g * kk j))
    (hconv : ∀ s : ℂ, σ < s.re → ∀ g, CosetConv P Γ₂ (Φ s) g) {w : G → ℂ} (hwc : Continuous w)
    (hw1 : ∀ x, ‖w x‖ = 1) {s₀ : ℂ} {Ψ : G₂ → ℂ} (hΨ : ∀ g, HolValueAt (fun s => cosetSum P Γ₂ (Φ s) g) s₀ (Ψ g))
    (h : G) :
    IntegrableOn (fun x => Ψ (i (h, x)) * w x) 𝓕 μ ∧
      HolValueAt (fun s => ∫ x in 𝓕, cosetSum P Γ₂ (Φ s) (i (h, x)) * w x ∂μ) s₀ (∫ x in 𝓕, Ψ (i (h, x)) * w x ∂μ) := by
  classical
  obtain ⟨C, hCm, ⟨M, hM⟩, hC⟩ := exists_coeff (Γ := Γ) hK hKc A hcov (fun j k => cc j (i (1, k)))
    fun j => (hcc j).comp (hi.comp (continuous_const.prodMk continuous_id))
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (measure_lt_top_of_cover h𝓕 hKc A hcov).ne
  have hc : ∀ p : {a // a ∈ A} × ι, Integrable (fun x => C p.1 p.2 x * w x) (μ.restrict 𝓕) := fun p =>
    Integrable.of_bound ((hCm p.1 p.2).aestronglyMeasurable.mul hwc.aestronglyMeasurable) M
      (Eventually.of_forall fun x => by rw [norm_mul, hw1, mul_one]; exact hM _ _ x)
  have hexp' : ∀ s : ℂ, σ < s.re → ∀ x, cosetSum P Γ₂ (Φ s) (i (h, x)) * w x =
      ∑ p : {a // a ∈ A} × ι, C p.1 p.2 x * w x * cosetSum P Γ₂ (Φ s) (i (h, p.1) * kk p.2) := by
    intro s hs x
    obtain ⟨a, ha, γ, hγ, k, hk, hx, hCx⟩ := hC x
    have e : i (h, x) = i (1, γ) * (i (h, a) * i (1, k)) := by
      rw [hx]; simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one, mul_assoc]
    rw [e, leftInv_cosetSum (hΦ s hs) _ (hΓ₂ γ hγ),
      cosetSum_expansion (hexp s hs) _ (fun j => hconv s hs _) (hKK k hk), Fintype.sum_prod_type,
      Finset.sum_eq_single (⟨a, ha⟩ : {a // a ∈ A}) (fun b _ hb => by
        simp [hCx, show (b : G) ≠ a from fun e => hb (Subtype.ext e)]) (by simp), Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hCx, if_pos rfl]; ring
  have key := holValueAt_integral_of_expansion (ν := μ.restrict 𝓕) (X := G) (ι := {a // a ∈ A} × ι)
    (Φ := fun s x => cosetSum P Γ₂ (Φ s) (i (h, x)) * w x) (Ψ := fun x => Ψ (i (h, x)) * w x)
    (c := fun p x => C p.1 p.2 x * w x) (v := fun p s => cosetSum P Γ₂ (Φ s) (i (h, p.1) * kk p.2))
    (w := fun p => Ψ (i (h, p.1) * kk p.2)) (σ := σ) hc hexp' (fun p => hΨ _)
    (fun x => (hΨ _).mul (holValueAt_const _ _))
  exact ⟨key.2.1, key.2.2⟩

end Main

section Flat

variable {G G₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  {i : G × G →* G₂} {P Γ₂ K₂ : Subgroup G₂} {Γ K : Subgroup G} [Countable Γ] {r : Γ → Γ₂}
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G} {A : Finset G}
  {δ : P →* ℝ≥0} {χ : P →* Circle} {f : G₂ → ℂ} {ρ s₀ : ℂ}

end Flat

end GlobalTheory.DefDoubling
end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DefDoubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance isTopologicalRing_adeleE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

instance t2Space_adeles_E : T2Space (AE F E) :=
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension

instance borelSpace_adelicU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

theorem transpose_blkMat' {A m k ι : Type} [CommRing A] (e : m ⊕ k ≃ ι) (x : Matrix m m A) (y : Matrix k k A) :
    (blkMat e x y)ᵀ = blkMat e xᵀ yᵀ := by
  simp [blkMat, Matrix.fromBlocks_transpose, Matrix.transpose_submatrix]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem incM_dblGram : incM F (dblGram finSumFinEquiv J) = dblGram finSumFinEquiv (incM F J) := by
  rw [incM, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]; rfl

theorem blkGL_mem_UG {x y : GL (Fin n) (AE F E)} :
    blkGL finSumFinEquiv (x, y) ∈ UG (cA σ) (incM F (dblGram finSumFinEquiv J)) ↔
      x ∈ UG (cA σ) (incM F J) ∧ y ∈ UG (cA σ) (incM F J) := by
  rw [incM_dblGram]
  change (blkMat finSumFinEquiv x.1 y.1)ᵀ * blkMat finSumFinEquiv (incM F J) (-incM F J) *
      (blkMat finSumFinEquiv x.1 y.1).map (cA σ) = blkMat finSumFinEquiv (incM F J) (-incM F J) ↔
    (x.1ᵀ * incM F J * x.1.map (cA σ) = incM F J) ∧ (y.1ᵀ * incM F J * y.1.map (cA σ) = incM F J)
  rw [blkMat_map _ _ (map_zero _), transpose_blkMat', blkMat_mul, blkMat_mul, blkMat_inj, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj]

def ioA : UA σ J × UA σ J →* UA σ (dblGram finSumFinEquiv J) :=
  ((blkGL finSumFinEquiv).comp ((UG (cA σ) (incM F J)).subtype.prodMap (UG (cA σ) (incM F J)).subtype)).codRestrict _
    fun g => (blkGL_mem_UG σ J).2 ⟨g.1.2, g.2.2⟩

theorem countable_ratU : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  refine Function.Injective.countable (f := fun x : ratU σ J =>
    (Classical.choose (Subgroup.mem_subgroupOf.1 x.2) : GL (Fin n) E)) ?_
  intro x y h
  have hx := Classical.choose_spec (Subgroup.mem_subgroupOf.1 x.2)
  have hy := Classical.choose_spec (Subgroup.mem_subgroupOf.1 y.2)
  apply Subtype.ext; apply Subtype.ext
  rw [← hx, ← hy]
  exact congrArg _ h

theorem ioA_one_mem_ratU {γ : UA σ J} (hγ : γ ∈ ratU σ J) : ioA σ J (1, γ) ∈ ratU σ (dblGram finSumFinEquiv J) := by
  obtain ⟨B, hB⟩ := Subgroup.mem_subgroupOf.1 hγ
  refine Subgroup.mem_subgroupOf.2 ⟨blkGL finSumFinEquiv (1, B), Units.ext ?_⟩
  change (blkMat finSumFinEquiv (1 : Matrix (Fin n) (Fin n) E) B.1).map (inclR (F := F) (AF F)) =
    blkMat finSumFinEquiv (1 : Matrix (Fin n) (Fin n) (AE F E)) ((γ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
  rw [blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), ← hB]
  rfl

end GlobalTheory.DefDoubling
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot

noncomputable section

namespace GlobalTheory.DblBox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

def rIdx (n d : ℕ) : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ Fin (n + n) × Fin d :=
  (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))

@[simp] theorem rIdx_inl (p : Fin n × Fin d) : rIdx n d (.inl p) = (finSumFinEquiv (.inl p.1), p.2) := rfl

@[simp] theorem rIdx_inr (p : Fin n × Fin d) : rIdx n d (.inr p) = (finSumFinEquiv (.inr p.1), p.2) := rfl

def upB {A : Type} (u : Matrix (Fin (n + n)) (Fin d) A) : Matrix (Fin n) (Fin d) A := fun i => u (finSumFinEquiv (.inl i))

def loB {A : Type} (u : Matrix (Fin (n + n)) (Fin d) A) : Matrix (Fin n) (Fin d) A := fun i => u (finSumFinEquiv (.inr i))

def reix {R κ κ' : Type} (e : κ ≃ κ') : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.arrowCongr e (Equiv.refl R)).symm

theorem reix_apply {R κ κ' : Type} (e : κ ≃ κ') (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e) := rfl

theorem reix_symm {R κ κ' : Type} (e : κ ≃ κ') : (reix (R := R) e).symm = reix e.symm := rfl

def bx (φ₁ φ₂ : Fn F n d) : Fn F (n + n) d := reix (rIdx n d) (boxFun φ₁ φ₂)

def cj (φ : Fn F n d) : Fn F n d := fun x => starRingEnd ℂ (φ x)

def IsBoxCo {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d))
    (cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)) : Prop :=
  ∀ u, cb.e u = (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1 ∘ (rIdx n d).symm,
    Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2) ∘ (rIdx n d).symm)

section Reindex₂

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem reix_mem_schA (e : κ ≃ κ') {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective φ h
  convert this using 2 with y
  rw [reix_apply]
  congr 1
  funext k
  obtain ⟨k, rfl⟩ := e.symm.surjective k
  rw [e.symm.injective.extend_apply]
  simp

theorem reix_mem_schA_iff (e : κ ≃ κ') {φ : (κ → AF F) → ℂ} : reix e φ ∈ schA F κ' ↔ φ ∈ schA F κ :=
  ⟨fun h => by simpa [← reix_symm] using reix_mem_schA e.symm h, reix_mem_schA e⟩

open scoped Classical in
theorem comp_reix_mem_adm (e : κ ≃ κ') {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (h : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ (reix e).toLinearMap ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := h (fun z => g (Function.extend e.symm z 0))
    (GlobalTheory.RestrSchA.sb_comp_extend F e.symm.injective hg)
  refine ⟨T.comp (GlobalTheory.RestrSchA.restrS F e.symm.injective), fun f => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ← hT, LinearMap.comp_apply]
  congr 1
  funext y
  rw [← GlobalTheory.RestrSchA.pureA_extend F e.symm.injective]
  show pureA F f g (y ∘ e) = _
  congr 1
  funext k
  obtain ⟨k, rfl⟩ := e.symm.surjective k
  rw [e.symm.injective.extend_apply]
  simp

omit [Fintype κ] [Fintype κ'] in
theorem thetaSum_reix (e : κ ≃ κ') (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).symm.tsum_eq fun ξ => φ fun i => algebraMap F (AF F) (ξ i)

theorem schr_reix {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (e : κ ≃ κ') (a b : κ → R)
    (φ : (κ → R) → ℂ) : schr ψ (a ∘ e.symm, b ∘ e.symm) (reix e φ) = reix e (schr ψ (a, b) φ) := by
  funext x
  have h1 : x ⬝ᵥ (b ∘ e.symm) = (x ∘ e) ⬝ᵥ b := by
    simp only [dotProduct]; rw [← e.sum_comp]; simp
  have h2 : (a ∘ e.symm) ⬝ᵥ (b ∘ e.symm) = a ⬝ᵥ b := by
    simp only [dotProduct]; rw [← e.sum_comp]; simp
  simp only [schr, reix_apply, h1, h2]
  congr 2
  funext k
  simp

end Reindex₂

theorem bx_mem_schA {φ₁ φ₂ : Fn F n d} (h₁ : φ₁ ∈ schA F _) (h₂ : φ₂ ∈ schA F _) : bx φ₁ φ₂ ∈ schA F _ :=
  reix_mem_schA _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ φ₂ h₂)

theorem cj_mem_schA {φ : Fn F n d} (h : φ ∈ schA F _) : cj φ ∈ schA F _ := GlobalTheory.ConjSch.conj_mem_schA φ h

theorem thetaSum_bx {φ₁ φ₂ : Fn F n d} (h₁ : φ₁ ∈ schA F _) (h₂ : φ₂ ∈ schA F _) :
    thetaSum F (bx φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  rw [bx, thetaSum_reix, GlobalTheory.ThetaBox.thetaSum_boxFun F _ _ φ₁ h₁ φ₂ h₂]

theorem exists_boxCo {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (hJ : J₂ = dblGram finSumFinEquiv J)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d))
    (hd : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d), IsBoxCo co cb ∧
      ∀ x : Matrix (Fin (n + n)) (Fin d) E, ∃ y z : Fin (n + n) × Fin d → F,
        cb.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  let S : Matrix (Fin (n + n)) (Fin d) (AE F E) ≃ₗ[AF F]
      Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin d) (AE F E) :=
    (LinearEquiv.funCongrLeft (AF F) (Fin d → AE F E) finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)
  let G : (Fin (n + n) × Fin d → AF F) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    (LinearEquiv.funCongrLeft (AF F) (AF F) (rIdx n d)).trans (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)
  let T := (LinearEquiv.prodProdProdComm (AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F)
    (Fin n × Fin d → AF F)).trans ((LinearEquiv.refl (AF F) _).prodCongr
      ((LinearEquiv.refl (AF F) (Fin n × Fin d → AF F)).prodCongr (LinearEquiv.neg (AF F) (M := Fin n × Fin d → AF F))))
  let e := S.trans ((co.e.prodCongr co.e).trans (T.trans (G.symm.prodCongr G.symm)))
  have he : ∀ u, e u = (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1 ∘ (rIdx n d).symm,
      Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2) ∘ (rIdx n d).symm) := fun u => by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> obtain ⟨k | k, rfl⟩ := (rIdx n d).surjective k <;>
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    · exact congrArg (fun z => z.1 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.2 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.1 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.2 k) (G.apply_symm_apply _)
  have hdot : ∀ a b : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
      (a ∘ (rIdx n d).symm) ⬝ᵥ (b ∘ (rIdx n d).symm) = a ⬝ᵥ b := fun a b => by
    simp only [dotProduct]; rw [← (rIdx n d).sum_comp]; simp
  refine ⟨⟨e, fun u v => ?_⟩, he, fun x => ?_⟩
  · rw [hJ, GlobalTheory.DefDoubling.incM_dblGram, GlobalTheory.SWAniso.symp_dblGram, he, he, hdot, hdot,
      sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_neg]
    have h1 := co.form (upB u) (upB v)
    have h2 := co.form (loB u) (loB v)
    refine (congrArg₂ (· - ·) h1 h2).trans ?_
    ring
  · obtain ⟨y, z, h1⟩ := hd (upB x)
    obtain ⟨y', z', h2⟩ := hd (loB x)
    refine ⟨Sum.elim y y' ∘ (rIdx n d).symm, Sum.elim z (-z') ∘ (rIdx n d).symm, ?_⟩
    change e (incM F x) = _
    rw [he, show upB (incM F x) = incM F (upB x) from rfl, show loB (incM F x) = incM F (loB x) from rfl, h1, h2]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> obtain ⟨k | k, rfl⟩ := (rIdx n d).surjective k <;>
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, map_neg]

theorem IsBoxCo.rho_reix {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    {co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d)}
    {cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)} (h : IsBoxCo co cb)
    (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin (n + n)) (Fin d) (AE F E))
    (φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) :
    cb.rho ψ u (reix (rIdx n d) φ) = reix (rIdx n d) (schr ψ (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1,
      Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2)) φ) := by
  rw [Darboux.rho, h u, schr_reix]

end GlobalTheory.DblBox

end
end
