import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.Reduction
import BuildAid.ForwardExisting
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGL
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartLeftInvariantLaplacianOpPowEqIterate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySoluti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinitStatement
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroupStatement

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.HCF

theorem exists_siegel_band : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ Ω : Set (GA E a), IsCompact Ω ∧ Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) ∧ ∃ t c₁ c₂ : ℝ, 0 < t ∧ 0 < c₁ ∧ ∀ g ∈ band E a, ∃ γ : GL (Fin a) E, ∃ b ∈ Ω, ∃ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ c₁ ≤ ∏ i, r i ∧ ∏ i, r i ≤ c₂ ∧ ∃ k ∈ (maxCompact : Subgroup (GA E a)), ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k := by
  intro E _ _ a
  obtain ⟨W0, hW, hWB, t, ht, h⟩ := exists_siegelSet (K := E) a
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := exists_pos_bounds hW
    (f := fun b => (ideleModule E (AdelicGLn.det E a b) : ℝ))
    (continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a)))
    (fun b _ => (ideleModule E (AdelicGLn.det E a b)).2)
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  set X₁ : ℝ := min 1 B₂⁻¹ with hX₁def
  set X₂ : ℝ := max 1 (2 / B₁) with hX₂def
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  refine ⟨W0, hW, hWB, t, X₁, X₂, ht, hX₁, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := h g
  obtain ⟨b, hbW, _, ⟨r, hr, hrat, rfl⟩, k, hk, hgeq⟩ := hγ
  have hgmod : (ideleModule E (AdelicGLn.det E a g) : ℝ) = absDetA g := (adeleAbs_units _).symm
  have hmod := congrArg (fun x => (ideleModule E (AdelicGLn.det E a x) : ℝ)) hgeq
  rw [det_mul_mul, ideleModule_det_diagUnits_posIdele r hr,
    mem_normOneGL.1 (maxCompact_le_normOneGL hk), mul_one, map_mul, map_mul, Positive.val_mul,
    mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩), one_mul, hgmod] at hmod
  set X : ℝ := ∏ i, r i with hX
  have hXpos : 0 < X := Finset.prod_pos fun i _ => hr i
  have hb := hB b hbW
  obtain ⟨h1, h2⟩ := hg
  have hXd1 : X ^ d ≤ 2 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc X ^ d * B₁ ≤ X ^ d * (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
          mul_le_mul_of_nonneg_left hb.1 (pow_nonneg hXpos.le _)
      _ = absDetA g := by rw [mul_comm, hmod]
      _ ≤ 2 := h2
  have hXd2 : B₂⁻¹ ≤ X ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ = (ideleModule E (AdelicGLn.det E a b) : ℝ) * X ^ d := hmod
      _ ≤ B₂ * X ^ d := mul_le_mul_of_nonneg_right hb.2 (pow_nonneg hXpos.le _)
  have hratGL : ratGL E a γ = AdelicGLn.diagonal E a γ := rfl
  refine ⟨γ, b, hbW, r, hr, hrat, ?_, ?_, k, hk, by rw [hratGL]; exact hgeq⟩
  · rcases le_or_gt 1 X with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hXd2.trans (pow_le_of_le_one hXpos.le h.le hd0.ne'))
  · rcases le_or_gt X 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hXd1.trans (le_max_right _ _))
end GlobalTheory.HCF
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelSet_reduction_adelicDetNormBand : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ Ω : Set (GA E a), IsCompact Ω ∧ Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) ∧ ∃ t c₁ c₂ : ℝ, 0 < t ∧ 0 < c₁ ∧ ∀ g ∈ band E a, ∃ γ : GL (Fin a) E, ∃ b ∈ Ω, ∃ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ c₁ ≤ ∏ i, r i ∧ ∏ i, r i ≤ c₂ ∧ ∃ k ∈ (maxCompact : Subgroup (GA E a)), ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k := by
  atlas_forward_decl GlobalTheory.HCF.exists_siegel_band
end

section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section
open scoped Pointwise
namespace GlobalTheory.HCF.ModGrowth
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in
theorem norm_ringEquivComplex (w : InfinitePlace E) (hw : w.IsComplex) (x : w.Completion) :
    ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry.norm_map_of_map_zero
    (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)) x

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  norm_ringEquivComplex w (IsTotallyComplex.isComplex w) (x.1 w)

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans_eq
    (by simp [nsmul_eq_mul]))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  · exact (norm_le_pi_norm (toL B k) j).trans (norm_le_pi_norm (toL B) k)

theorem height_mul_le (y z : GL (Fin a) (Cinf E)) :
    GlobalTheory.CuspRep.height (y * z) ≤ (a + 1) * (GlobalTheory.CuspRep.height y * GlobalTheory.CuspRep.height z) := by
  have h1 := norm_toL_mul_le (E := E) y.val z.val
  have h2 := norm_toL_mul_le (E := E) (z⁻¹).val (y⁻¹).val
  unfold GlobalTheory.CuspRep.height
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have p1 := norm_nonneg (toL y.val)
  have p2 := norm_nonneg (toL (y⁻¹).val)
  have q1 := norm_nonneg (toL z.val)
  have q2 := norm_nonneg (toL (z⁻¹).val)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith [mul_nonneg p1 q1, mul_nonneg p2 q2, mul_nonneg p1 q2, mul_nonneg p2 q1, mul_nonneg ha (mul_nonneg p1 q1),
    mul_nonneg ha (mul_nonneg p2 q2), mul_nonneg ha p1, mul_nonneg ha p2, mul_nonneg ha q1, mul_nonneg ha q2,
    mul_nonneg ha (mul_nonneg p1 q2), mul_nonneg ha (mul_nonneg p2 q1)]

theorem continuous_height : Continuous (GlobalTheory.CuspRep.height : GL (Fin a) (Cinf E) → ℝ) := by
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp continuous_inv
  exact (continuous_const.add (continuous_norm.comp h1)).add (continuous_norm.comp h2)

theorem pFin_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    Matrix.GeneralLinearGroup.map (pFin E) (diagUnits a fun i => posIdele (K := E) (r i) (hr i)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E ((diagUnits a fun i => posIdele (K := E) (r i) (hr i) : GA E a) i j) = (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [coe_diagUnits, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by
      change ((posIdele (K := E) (r i) (hr i) : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 v = _
      rw [posIdele_finite]; rfl
  · exact map_zero _

theorem height_pInf_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a fun i => posIdele (K := E) (r i) (hr i)))
      ≤ 1 + ∑ i, (r i + (r i)⁻¹) := by
  set d : Fin a → GroundTheory.Global.IdeleGroup E := fun i => posIdele (K := E) (r i) (hr i) with hd
  have hn : ∀ i w, ‖pInf E (d i : Ad E) w‖ = r i := fun i w => by
    rw [norm_pInf_apply]; exact norm_posIdele_infinite (r i) (hr i) w
  have hn' : ∀ i w, ‖pInf E (((d i)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E) w‖ = (r i)⁻¹ := fun i w => by
    have e : pInf E (((d i)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E) w * pInf E (d i : Ad E) w = 1 := by
      rw [← Pi.mul_apply, ← map_mul, Units.inv_mul, map_one, Pi.one_apply]
    have := congrArg norm e
    rw [norm_mul, hn, norm_one] at this
    exact eq_inv_of_mul_eq_one_left this
  have key : ∀ (f : Fin a → GroundTheory.Global.IdeleGroup E) (s : Fin a → ℝ), (∀ i w, ‖pInf E (f i : Ad E) w‖ = s i) →
      (∀ i, 0 ≤ s i) → ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a f)).val‖ ≤ ∑ i, s i := by
    intro f s hf hs
    have h0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => hs i
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    change ‖pInf E ((diagUnits a f : GA E a) i j)‖ ≤ _
    rw [coe_diagUnits, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      refine (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
      rw [hf]
      exact Finset.single_le_sum (fun k _ => hs k) (Finset.mem_univ i)
    · rw [map_zero, norm_zero]; exact h0
  have h1 := key d r hn fun i => (hr i).le
  have h2 := key (fun i => (d i)⁻¹) (fun i => (r i)⁻¹) hn' fun i => (inv_pos.2 (hr i)).le
  have e : (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a d))⁻¹ =
      Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a fun i => (d i)⁻¹) := by
    rw [← map_inv, ← map_inv]; rfl
  unfold GlobalTheory.CuspRep.height
  rw [e, Finset.sum_add_distrib]
  linarith

theorem span_props {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ} {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    (∀ l ∈ L, finRep E a l φ = φ) ∧ ∀ g, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
      ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    refine ⟨hx.2.1, fun g => ?_⟩
    obtain ⟨C, M, h⟩ := hx.1.growth g
    refine ⟨|C|, M, abs_nonneg _, fun y => (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) ?_)⟩
    exact pow_nonneg (zero_le_one.trans (one_le_height y)) _
  | zero => exact ⟨fun l _ => map_zero _, fun g => ⟨0, 0, le_rfl, fun y => by simp⟩⟩
  | add x y _ _ hx hy =>
    refine ⟨fun l hl => by rw [map_add, hx.1 l hl, hy.1 l hl], fun g => ?_⟩
    obtain ⟨C1, M1, h1, e1⟩ := hx.2 g
    obtain ⟨C2, M2, h2, e2⟩ := hy.2 g
    refine ⟨C1 + C2, M1 + M2, add_nonneg h1 h2, fun z => ?_⟩
    have hz := one_le_height z
    have p1 : GlobalTheory.CuspRep.height z ^ M1 ≤ GlobalTheory.CuspRep.height z ^ (M1 + M2) := pow_le_pow_right₀ hz (by omega)
    have p2 : GlobalTheory.CuspRep.height z ^ M2 ≤ GlobalTheory.CuspRep.height z ^ (M1 + M2) := pow_le_pow_right₀ hz (by omega)
    calc ‖(x + y).1 (g * infGL E a z)‖ = ‖x.1 (g * infGL E a z) + y.1 (g * infGL E a z)‖ := rfl
      _ ≤ ‖x.1 (g * infGL E a z)‖ + ‖y.1 (g * infGL E a z)‖ := norm_add_le _ _
      _ ≤ C1 * GlobalTheory.CuspRep.height z ^ (M1 + M2) + C2 * GlobalTheory.CuspRep.height z ^ (M1 + M2) :=
        add_le_add ((e1 z).trans (mul_le_mul_of_nonneg_left p1 h1)) ((e2 z).trans (mul_le_mul_of_nonneg_left p2 h2))
      _ = (C1 + C2) * GlobalTheory.CuspRep.height z ^ (M1 + M2) := by ring
  | smul c x _ hx =>
    refine ⟨fun l hl => by rw [map_smul, hx.1 l hl], fun g => ?_⟩
    obtain ⟨C, M, h, e⟩ := hx.2 g
    refine ⟨‖c‖ * C, M, by positivity, fun z => ?_⟩
    change ‖c * x.1 (g * infGL E a z)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (e z) (norm_nonneg c)

theorem uniform_fin {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hinv : ∀ l ∈ L, finRep E a l φ = φ)
    (hg : ∀ g, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M)
    {S : Set (GL (Fin a) (Af E))} (hS : IsCompact S) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ s ∈ S, ∀ y, ‖φ.1 (finGL E a s * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : GL (Fin a) (Af E) => s • (L : Set (GL (Fin a) (Af E))))
    (fun s => hL.leftCoset s) (fun s _ => Set.mem_iUnion.2 ⟨s, Set.mem_smul_set.2 ⟨1, L.one_mem, mul_one s⟩⟩)
  choose C M hC hb using fun s : GL (Fin a) (Af E) => hg (finGL E a s)
  refine ⟨∑ s ∈ t, C s, ∑ s ∈ t, M s, Finset.sum_nonneg fun s _ => hC s, fun s' hs' y => ?_⟩
  obtain ⟨s, hst, hs⟩ := Set.mem_iUnion₂.1 (ht hs')
  obtain ⟨l, hl, rfl⟩ := Set.mem_smul_set.1 hs
  have e : φ.1 (finGL E a (s • l) * infGL E a y) = φ.1 (finGL E a s * infGL E a y) := by
    have h := congrArg (fun ψ : Sm E a => ψ.1 (finGL E a s * infGL E a y)) (hinv l hl)
    refine Eq.trans ?_ h
    change φ.1 (finGL E a (s * l) * infGL E a y) = φ.1 (finGL E a s * infGL E a y * finGL E a l)
    rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
  rw [e]
  have hy := one_le_height y
  refine (hb s y).trans (mul_le_mul (Finset.single_le_sum (fun s _ => hC s) hst)
    (pow_le_pow_right₀ hy (Finset.single_le_sum (fun s _ => Nat.zero_le (M s)) hst))
    (pow_nonneg (zero_le_one.trans hy) _) (Finset.sum_nonneg fun s _ => hC s))

end GlobalTheory.HCF.ModGrowth

namespace GlobalTheory.HCF.ModGrowth

theorem modGrowth_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ))
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
    ∀ Ω : Set (GA E a), IsCompact Ω → ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i),
    ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E),
    ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤
      C * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀ := by
  intro E _ _ _ a L hL W X N φ hφ Ω hΩ
  obtain ⟨hinv, hgr⟩ := span_props hφ
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h1 : ∀ g : GA E 0, g = 1 := fun g => Units.ext (Matrix.ext fun i => Fin.elim0 i)
    refine ⟨‖φ.1 1‖, 0, norm_nonneg _, fun b _ r hr k _ y => ?_⟩
    rw [h1 (b * _ * k * _)]
    simp
  have hS : IsCompact ((fun p : GA E a × GA E a => Matrix.GeneralLinearGroup.map (pFin E) (p.1 * p.2)) ''
      (Ω ×ˢ ((maxCompact : Subgroup (GA E a)) : Set (GA E a)))) :=
    (hΩ.prod isCompact_maxCompact).image ((ContAut.continuous_map_pFin E a).comp (continuous_fst.mul continuous_snd))
  obtain ⟨C1, M, hC1, hb1⟩ := uniform_fin hL hinv hgr hS
  have hf : Continuous fun g : GA E a => GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) g) :=
    continuous_height.comp (ContAut.continuous_map_pInf E a)
  obtain ⟨Mb, hMb⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Mk, hMk⟩ := (isCompact_maxCompact (K := E) (n := a)).exists_bound_of_continuousOn hf.continuousOn
  have hB : (0 : ℝ) ≤ (a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) := by positivity
  refine ⟨C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1)) ^ M, M, by positivity, fun b hb r hr k hk y => ?_⟩
  have hfin : Matrix.GeneralLinearGroup.map (pFin E) (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k *
      infGL E a y) = Matrix.GeneralLinearGroup.map (pFin E) (b * k) := by
    simp only [map_mul, pFin_diag, pFin_infGL, mul_one]
  have hinf : Matrix.GeneralLinearGroup.map (pInf E) (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k *
      infGL E a y) = Matrix.GeneralLinearGroup.map (pInf E) b *
        Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i))) *
        Matrix.GeneralLinearGroup.map (pInf E) k * y := by
    simp only [map_mul, pInf_infGL]
  have hx := infGL_mul_finGL (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)
  rw [infGL_comm, hfin, hinf] at hx
  rw [← hx]
  have hs : Matrix.GeneralLinearGroup.map (pFin E) (b * k) ∈ (fun p : GA E a × GA E a =>
      Matrix.GeneralLinearGroup.map (pFin E) (p.1 * p.2)) '' (Ω ×ˢ ((maxCompact : Subgroup (GA E a)) : Set (GA E a))) :=
    ⟨(b, k), ⟨hb, hk⟩, rfl⟩
  refine (hb1 _ hs _).trans ?_

  set A := Matrix.GeneralLinearGroup.map (pInf E) b
  set D := Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)))
  set K := Matrix.GeneralLinearGroup.map (pInf E) k
  set s := ∑ i, (r i + (r i)⁻¹)
  have hs1 : 1 ≤ s := by
    have h0 : ∀ i, 0 ≤ r i + (r i)⁻¹ := fun i => add_nonneg (hr i).le (inv_pos.2 (hr i)).le
    have h1 : 1 ≤ r ⟨0, ha⟩ + (r ⟨0, ha⟩)⁻¹ := by
      rcases le_total (r ⟨0, ha⟩) 1 with h | h
      · linarith [(one_le_inv₀ (hr ⟨0, ha⟩)).2 h, hr ⟨0, ha⟩]
      · linarith [inv_pos.2 (hr ⟨0, ha⟩)]
    exact h1.trans (Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ _))
  have hA : GlobalTheory.CuspRep.height A ≤ max Mb 1 :=
    ((Real.le_norm_self _).trans (hMb b hb)).trans (le_max_left _ _)
  have hK : GlobalTheory.CuspRep.height K ≤ max Mk 1 :=
    ((Real.le_norm_self _).trans (hMk k hk)).trans (le_max_left _ _)
  have hD : GlobalTheory.CuspRep.height D ≤ 2 * s := (height_pInf_diag r hr).trans (by linarith)
  have hA1 := one_le_height A
  have hD1 := one_le_height D
  have hK1 := one_le_height K
  have hy1 := one_le_height y
  have c0 : (0 : ℝ) ≤ a + 1 := by positivity
  have e3 := height_mul_le A D
  have e2 := height_mul_le (A * D) K
  have e1 := height_mul_le (A * D * K) y
  have hAD : GlobalTheory.CuspRep.height A * GlobalTheory.CuspRep.height D ≤ max Mb 1 * (2 * s) :=
    mul_le_mul hA hD (by linarith) (by positivity)
  have hADK : GlobalTheory.CuspRep.height (A * D * K) ≤ (a + 1) * ((a + 1) * (max Mb 1 * (2 * s)) * max Mk 1) :=
    e2.trans (mul_le_mul_of_nonneg_left (mul_le_mul (e3.trans (mul_le_mul_of_nonneg_left hAD c0)) hK (by linarith)
      (by positivity)) c0)
  have hz : GlobalTheory.CuspRep.height (A * D * K * y) ≤ (a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) * s * GlobalTheory.CuspRep.height y := by
    refine e1.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hADK (by linarith)) c0).trans_eq ?_)
    ring
  have hz0 : 0 ≤ GlobalTheory.CuspRep.height (A * D * K * y) := zero_le_one.trans (one_le_height _)
  calc C1 * GlobalTheory.CuspRep.height (A * D * K * y) ^ M
      ≤ C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) * s * GlobalTheory.CuspRep.height y) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz M) hC1
    _ = C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1)) ^ M * s ^ M * GlobalTheory.CuspRep.height y ^ M := by
        rw [mul_pow, mul_pow]; ring

end GlobalTheory.HCF.ModGrowth
end
end

section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ Ω : Set (GA E a), IsCompact Ω → ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀ := by
  first | exact @GlobalTheory.HCF.ModGrowth.modGrowth_span | exact GlobalTheory.HCF.ModGrowth.modGrowth_span | (intros; apply GlobalTheory.HCF.ModGrowth.modGrowth_span <;> assumption)
end

section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
open GlobalTheory.HCAlpha
open scoped ContDiff

namespace GlobalTheory.HCFiniteSm

theorem chart_sum' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (s : Finset ℕ) (c : ℕ → ℂ)
    (ψ : ℕ → Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    chart (∑ k ∈ s, c k • ψ k).1 g y = ∑ k ∈ s, c k * chart (ψ k).1 g y := by
  have hy' : IsUnit (Matrix.of y) := hy
  simp only [chart, dif_pos hy', Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.HCFiniteSm

end
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HCSmoothGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem isAddHaarMeasure_volume_Lie : (volume : Measure (Lie E a)).IsAddHaarMeasure := by
  haveI : SigmaFinite (volume : Measure (InfinitePlace E → ℂ)) := inferInstance
  haveI : (volume : Measure (Fin a → InfinitePlace E → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : SigmaFinite (volume : Measure (Fin a → InfinitePlace E → ℂ)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

def conjCL (k : Kinf E a) : Lie E a →L[ℝ] Lie E a := (lmul (toL k.1)).comp (rmul (toL (star k.1)))

theorem conjCL_apply (k : Kinf E a) (x : Lie E a) : conjCL k x = toL (k.1 * Matrix.of x * star k.1) := by
  show toL (k.1 * (Matrix.of x * star k.1)) = _
  rw [mul_assoc]

theorem conjCL_mul (k k' : Kinf E a) (x : Lie E a) : conjCL (k * k') x = conjCL k (conjCL k' x) := by
  rw [conjCL_apply, conjCL_apply, conjCL_apply]
  show toL _ = toL (k.1 * (k'.1 * Matrix.of x * star k'.1) * star k.1)
  simp [mul_assoc, star_mul]

theorem conjCL_one (x : Lie E a) : conjCL 1 x = x := by
  simp [conjCL_apply]

def conjCE (k : Kinf E a) : Lie E a ≃L[ℝ] Lie E a :=
  ContinuousLinearEquiv.equivOfInverse (conjCL k) (conjCL k⁻¹)
    (fun x => by rw [← conjCL_mul, inv_mul_cancel, conjCL_one])
    (fun x => by rw [← conjCL_mul, mul_inv_cancel, conjCL_one])

variable [IsTotallyComplex E]

def avgChart [MeasurableSpace (Kinf E a)] (ν : Measure (Kinf E a)) (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : ℂ :=
  ∫ k, chart φ g (conjCL k x) ∂ν

open Classical in

def extL : (GL (Fin a) (Cinf E) → ℂ) →ₗ[ℂ] (Lie E a → ℂ) where
  toFun F x := if h : IsUnit (Matrix.of x) then F h.unit else 0
  map_add' F G := by funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [h]
  map_smul' c F := by funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [h]

theorem exists_smooth_beta : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ β : Lie E a → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ invSet E a ∧ ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  intro E _ _ _ a L W hW X hX N
  have hν := isAddHaarMeasure_volume_Lie (E := E) (a := a)
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite E a L W hW X hX N
  obtain ⟨α, hα, h⟩ := GlobalTheory.T.exists_testFunction_reproducing_laplacianPoly_solutions E a volume hν p hp0
  refine ⟨α, hα.1, hα.2.1, hα.2.2, fun φ hφm x => ?_⟩
  have hφ := hp φ hφm
  have h1 := h (chart φ.1 x) (φ.2 x) (fun y hy => by
    rw [Polynomial.aeval_eq_sum_range] at hφ
    have e := congrArg (fun ψ : Sm E a => chart ψ.1 x y) hφ
    rw [LinearMap.sum_apply] at e
    simp only [LinearMap.smul_apply] at e
    rw [GlobalTheory.HCFiniteSm.chart_sum' _ _ (fun k => (GlobalTheory.HCAlpha.lapOp E a ^ k) φ) _ hy] at e
    have e0 : chart (0 : Sm E a).1 x y = 0 := by simp [chart]
    rw [e0] at e
    rw [← e, GlobalTheory.HCAlpha.polyF, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.HCAlpha.chart_lapOp_pow E a φ x k y hy])
  simp only [mul_comm (chart φ.1 x _)]
  rw [h1]
  have := chart_val φ.1 x 1
  simpa using this

end GlobalTheory.HCSmoothGL
end
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_function_reproducing_forms_gl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ β : Lie E a → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ invSet E a ∧ ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  atlas_forward_decl GlobalTheory.HCSmoothGL.exists_smooth_beta
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspTail

theorem norm_le_of_altSum_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (m : ℕ) (B : ℝ),
      (∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ GroundTheory.Automorphic.scaledUnipFD E a r M) →
        ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) * φ (unip (GroundTheory.Automorphic.altPoint y ε) * x)‖ ≤ B) →
      ‖φ x‖ ≤ B := by
  intro E _ _ _ a r hr hra φ hinv hcusp hφ M hM x m B hB
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  set D := GroundTheory.Automorphic.scaledUnipFD E a r M with hDdef
  set ν := GroundTheory.Automorphic.AutomorphicForm.unipMeasure E a r
  have hD : IsAddFundamentalDomain (ratN E a r) D ν :=
    GroundTheory.Automorphic.isAddFundamentalDomain_scaledUnipFD hM
  have hD1 : ν D = 1 := GroundTheory.Automorphic.unipMeasure_scaledUnipFD hM
  set H : (BlockIx a r → Ad E) → ℂ := fun s => φ (unip s * x) with hH
  have hunip : (unip : (BlockIx a r → Ad E) → GA E a) =
      (GroundTheory.Automorphic.AutomorphicForm.unipGL (n := a) (r := r) (R := Ad E)) :=
    funext fun X => Units.ext rfl
  have hcont : Continuous H := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    rw [hunip]
    exact GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL
  have hper : ∀ ξ ∈ ratN E a r, ∀ s, H (ξ + s) = H s := by
    rintro _ ⟨e, rfl⟩ s
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + s) * x) = φ (unip s * x)
    rw [unip_add, unip_algebraMap, mul_assoc, hinv]
  obtain ⟨C, hC, hDC⟩ :=
    GroundTheory.Automorphic.CuspidalSpectrum.exists_isCompact_superset_scaledUnipFD (K := E) (n := a) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) D ν :=
    fun t => ((hcont.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hmean : ∫ y in D, H y ∂ν = 0 :=
    hcusp r hr hra ν D inferInstance hD x
  have hB' : ∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ D) →
      ‖GroundTheory.Automorphic.altSum m H y 0‖ ≤ B := by
    intro y hy
    rw [GroundTheory.Automorphic.altSum_eq_sum]
    simpa [H, zero_add, zsmul_eq_mul] using hB y hy
  have h0 := GroundTheory.Automorphic.norm_le_of_forall_altSum_le hD hD1 m H hper hint hmean B hB'
  have hu0 : (unip (0 : BlockIx a r → Ad E) : GA E a) = 1 := by
    have h := unip_add (0 : BlockIx a r → Ad E) 0
    rw [add_zero] at h
    simpa using h
  have hH0 : H 0 = φ x := by simp only [H, hu0, one_mul]
  rwa [hH0] at h0

end GlobalTheory.CuspTail
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_norm_le_of_alternatingSum_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (m : ℕ) (B : ℝ),
      (∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ GroundTheory.Automorphic.scaledUnipFD E a r M) →
        ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) * φ (unip (GroundTheory.Automorphic.altPoint y ε) * x)‖ ≤ B) →
      ‖φ x‖ ≤ B := by
  atlas_forward_decl GlobalTheory.CuspTail.norm_le_of_altSum_scaledUnipFD
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

namespace GlobalTheory.HCF.ReproSpan

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem chart_zero' (g : GA E a) (x : Lie E a) : chart (0 : GA E a → ℂ) g x = 0 := by
  unfold chart; split_ifs <;> rfl

theorem chart_add' (φ ψ : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (φ + ψ) g x = chart φ g x + chart ψ g x := by
  unfold chart; split_ifs <;> simp

theorem chart_smul' (c : ℂ) (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (c • φ) g x = c * chart φ g x := by
  unfold chart; split_ifs <;> simp

theorem integrable_chart_mul (ψ : Sm E a) (g : GA E a) (β : Lie E a → ℂ) (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ invSet E a) :
    MeasureTheory.Integrable (fun x => chart ψ.1 g x * β x) := by
  have hcont : Continuous (fun x => chart ψ.1 g x * β x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ invSet E a
    · exact (contDiffAt_chart ψ.2 g hx).continuousAt.mul hβ.continuousAt
    · have hxt : x ∉ tsupport β := fun h => hx (hs h)
      have hev : (fun x => chart ψ.1 g x * β x) =ᶠ[𝓝 x] fun _ => 0 := by
        have h0 : β =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxt
        filter_upwards [h0] with y hy
        simp [hy]
      exact (continuousAt_congr hev).mpr continuousAt_const
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Fin a → Cinf E)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin a → Cinf E)) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Lie E a)) :=
    MeasureTheory.Measure.pi.isFiniteMeasureOnCompacts _
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.mul_left hc)

end GlobalTheory.HCF.ReproSpan

open GlobalTheory.HCF.ReproSpan in

theorem GlobalTheory.HCF.repro_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ),
    ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a →
    (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) →
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  intro E _ _ _ a L W X N β hβ hc hs hform φ hφ
  have hβc : Continuous β := hβ.continuous
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hform x hx
  | zero =>
    intro g
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply]
    simp [chart_zero']
  | add x y _ _ hx hy =>
    intro g
    have e : (fun z => chart (x + y).1 g z * β z) =
        fun z => chart x.1 g z * β z + chart y.1 g z * β z := by
      funext z
      rw [Submodule.coe_add, chart_add', add_mul]
    rw [e, MeasureTheory.integral_add (integrable_chart_mul x g β hβc hc hs)
      (integrable_chart_mul y g β hβc hc hs), hx g, hy g]
    rfl
  | smul c x _ hx =>
    intro g
    have e : (fun z => chart (c • x).1 g z * β z) = fun z => c * (chart x.1 g z * β z) := by
      funext z
      rw [Submodule.coe_smul, chart_smul', mul_assoc]
    rw [e, MeasureTheory.integral_const_mul, hx g]
    rfl
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reproducingIdentity_extends_harishChandraSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ),
    ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a →
    (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) →
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  atlas_forward_decl GlobalTheory.HCF.repro_span
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.AltConv

open GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

abbrev Mat (E : Type) [Field E] [NumberField E] (a : ℕ) : Type := Matrix (Fin a) (Fin a) (Cinf E)

def toLA : Mat E a ≃+ Lie E a := Matrix.ofAddEquiv.symm

theorem toLA_apply (M : Mat E a) : toLA M = toL M := rfl

theorem isAddHaar_row : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : Fin a => (volume : Measure (Cinf E)))

theorem isAddHaar_lie : (volume : Measure (Lie E a)).IsAddHaarMeasure := by
  haveI := isAddHaar_row (E := E) (a := a)
  exact Measure.pi.isAddHaarMeasure (fun _ : Fin a => (volume : Measure (Fin a → Cinf E)))

theorem det_eq_one_of_sq {W : Type} [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    {L : W →ₗ[ℝ] W} (hK : (L - 1) * (L - 1) = 0) : LinearMap.det L = 1 := by
  have hN : IsNilpotent (L - 1) := ⟨2, by rw [pow_two, hK]⟩
  have h := (hN.neg).charpoly_eq_X_pow_finrank
  have h2 := LinearMap.eval_charpoly (-(L - 1)) 1
  rw [h] at h2
  simpa using h2.symm

def mulL (P : Mat E a) : Lie E a →ₗ[ℝ] Lie E a where
  toFun w := toL (P * Matrix.of w)
  map_add' x y := by
    show toL (P * (Matrix.of x + Matrix.of y)) = _
    rw [Matrix.mul_add]; rfl
  map_smul' c x := by
    show toL (P * (c • Matrix.of x)) = _
    rw [Matrix.mul_smul]; rfl

theorem mulL_mul (P P' : Mat E a) : mulL P * mulL P' = mulL (P * P') := by
  refine LinearMap.ext fun w => ?_
  show toL (P * (P' * Matrix.of w)) = toL (P * P' * Matrix.of w)
  rw [Matrix.mul_assoc]

theorem mulL_zero : mulL (0 : Mat E a) = 0 := by
  refine LinearMap.ext fun w => ?_
  show toL ((0 : Mat E a) * Matrix.of w) = 0
  rw [Matrix.zero_mul]; rfl

theorem one_add_mulL_apply (P : Mat E a) (w : Lie E a) :
    (1 + mulL P) w = toL ((1 + P) * Matrix.of w) := by
  show w + toL (P * Matrix.of w) = _
  rw [Matrix.add_mul, Matrix.one_mul]; rfl

theorem one_sub_mulL_apply (P : Mat E a) (w : Lie E a) :
    (1 - mulL P) w = toL ((1 - P) * Matrix.of w) := by
  show w - toL (P * Matrix.of w) = _
  rw [Matrix.sub_mul, Matrix.one_mul]; rfl

def shear (P : Mat E a) (hP : P * P = 0) : Lie E a ≃ₗ[ℝ] Lie E a :=
  LinearEquiv.ofLinear (1 + mulL P) (1 - mulL P)
    (by
      show (1 + mulL P) * (1 - mulL P) = 1
      calc (1 + mulL P) * (1 - mulL P) = 1 - mulL P * mulL P := by noncomm_ring
        _ = 1 := by rw [mulL_mul, hP, mulL_zero, sub_zero])
    (by
      show (1 - mulL P) * (1 + mulL P) = 1
      calc (1 - mulL P) * (1 + mulL P) = 1 - mulL P * mulL P := by noncomm_ring
        _ = 1 := by rw [mulL_mul, hP, mulL_zero, sub_zero])

theorem shear_apply (P : Mat E a) (hP : P * P = 0) (w : Lie E a) :
    shear P hP w = toL ((1 + P) * Matrix.of w) := one_add_mulL_apply P w

theorem shear_symm_apply (P : Mat E a) (hP : P * P = 0) (w : Lie E a) :
    (shear P hP).symm w = toL ((1 - P) * Matrix.of w) := one_sub_mulL_apply P w

theorem measurePreserving_shear (P : Mat E a) (hP : P * P = 0) :
    MeasurePreserving (shear P hP).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv volume volume := by
  haveI := isAddHaar_lie (E := E) (a := a)
  refine ⟨(shear P hP).toContinuousLinearEquiv.continuous.measurable, ?_⟩
  have hdet : LinearMap.det (1 + mulL P : Lie E a →ₗ[ℝ] Lie E a) = 1 :=
    det_eq_one_of_sq (by rw [add_sub_cancel_left, mulL_mul, hP, mulL_zero])
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Lie E a)))
    (f := 1 + mulL P) (by rw [hdet]; norm_num)
  rw [hdet] at h
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

theorem altPoint_sq {m : ℕ} {Y : Fin m → Mat E a} (hY : ∀ i j, Y i * Y j = 0) (ε : Fin m → Bool) :
    altPoint Y ε * altPoint Y ε = 0 := by
  unfold altPoint
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs <;> simp [hY]

theorem toL_altPoint {m : ℕ} (Y : Fin m → Mat E a) (ε : Fin m → Bool) :
    toL (altPoint Y ε) = altPoint (fun i => toL (Y i)) ε := by
  unfold altPoint
  rw [← toLA_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [toLA_apply]

theorem norm_toL_altPoint_le {m : ℕ} {Y : Fin m → Mat E a} {R : ℝ} (hR : ∀ i, ‖toL (Y i)‖ ≤ R)
    (ε : Fin m → Bool) : ‖toL (altPoint Y ε)‖ ≤ m * R := by
  rw [toL_altPoint]
  unfold altPoint
  calc ‖∑ i, if ε i then toL (Y i) else 0‖ ≤ ∑ i : Fin m, ‖if ε i then toL (Y i) else 0‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, R := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · exact hR i
        · rw [norm_zero]; exact (norm_nonneg _).trans (hR i)
    _ = m * R := by simp

theorem add_altPoint_eq {m : ℕ} (Y : Fin m → Mat E a) (ε : Fin m → Bool) (v : Lie E a) :
    v + altPoint (fun i => toL (-(Y i * Matrix.of v))) ε = toL ((1 - altPoint Y ε) * Matrix.of v) := by
  have h1 : altPoint (fun i => -(Y i * Matrix.of v)) ε = -(altPoint Y ε * Matrix.of v) := by
    unfold altPoint
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [← toL_altPoint (fun i => -(Y i * Matrix.of v)), h1, Matrix.sub_mul, Matrix.one_mul, sub_eq_add_neg,
    ← toLA_apply, ← toLA_apply, map_add]
  rfl

theorem norm_toL_mul_le (Y X : Mat E a) : ‖toL (Y * X)‖ ≤ a * ‖toL Y‖ * ‖toL X‖ := by
  have h0 : 0 ≤ (a : ℝ) * ‖toL Y‖ * ‖toL X‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have hY : ∀ l, ‖Y i l‖ ≤ ‖toL Y‖ := fun l => (norm_le_pi_norm (toL Y i) l).trans (norm_le_pi_norm (toL Y) i)
  have hX : ∀ l, ‖X l j‖ ≤ ‖toL X‖ := fun l => (norm_le_pi_norm (toL X l) j).trans (norm_le_pi_norm (toL X) l)
  show ‖(Y * X) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ l, Y i l * X l j‖ ≤ ∑ l : Fin a, ‖Y i l‖ * ‖X l j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
    _ ≤ ∑ _l : Fin a, ‖toL Y‖ * ‖toL X‖ :=
        Finset.sum_le_sum fun l _ => mul_le_mul (hY l) (hX l) (norm_nonneg _) (norm_nonneg _)
    _ = a * ‖toL Y‖ * ‖toL X‖ := by simp [mul_assoc]

theorem continuous_of_lie : Continuous (fun y : Lie E a => (Matrix.of y : Mat E a)) := continuous_id

theorem continuous_toL : Continuous (fun M : Mat E a => toL M) := continuous_id

def sqBall (r : ℝ) : Set (Lie E a) := {y | ‖y‖ ≤ r ∧ Matrix.of y * Matrix.of y = 0}

theorem isCompact_sqBall (r : ℝ) : IsCompact (sqBall (E := E) (a := a) r) := by
  refine (isCompact_closedBall (0 : Lie E a) r).of_isClosed_subset ?_ fun y hy => ?_
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_eq (continuous_of_lie.matrix_mul continuous_of_lie) continuous_const)
  · rw [mem_closedBall_zero_iff]; exact hy.1

def act (p : Lie E a × Lie E a) : Lie E a := toL ((1 + Matrix.of p.1) * Matrix.of p.2)

theorem continuous_act : Continuous (act (E := E) (a := a)) :=
  continuous_toL.comp ((continuous_const.add (continuous_of_lie.comp continuous_fst)).matrix_mul
    (continuous_of_lie.comp continuous_snd))

theorem isUnit_one_add_of_sq {P : Mat E a} (hP : P * P = 0) : IsUnit (1 + P) := by
  refine ⟨⟨1 + P, 1 - P, ?_, ?_⟩, rfl⟩
  · calc (1 + P) * (1 - P) = 1 - P * P := by noncomm_ring
      _ = 1 := by rw [hP, sub_zero]
  · calc (1 - P) * (1 + P) = 1 - P * P := by noncomm_ring
      _ = 1 := by rw [hP, sub_zero]

theorem norm_sum_altSign_integral_le : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β →
    HasCompactSupport β → tsupport β ⊆ invSet E a → ∀ (m : ℕ) (R : ℝ), ∃ (c : ℝ) (Q : Set (Lie E a)),
    0 ≤ c ∧ IsCompact Q ∧ Q ⊆ invSet E a ∧ ∀ f : Lie E a → ℂ, ContinuousOn f (invSet E a) →
    ∀ F : ℝ, 0 ≤ F → (∀ w ∈ Q, ‖f w‖ ≤ F) →
    ∀ Y : Fin m → Matrix (Fin a) (Fin a) (Cinf E), (∀ i j, Y i * Y j = 0) → (∀ i, ‖toL (Y i)‖ ≤ R) →
    ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) *
        ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Y ε) * Matrix.of w)) * β w‖ ≤ c * F * ∏ i, ‖toL (Y i)‖ := by
  intro E _ _ a β hβ hβc hβu m R
  haveI := isAddHaar_lie (E := E) (a := a)
  obtain ⟨Bm, hBm⟩ := exists_norm_altSum_le (E := Lie E a) (F := ℂ) hβ hβc m
  set Q : Set (Lie E a) := act '' (sqBall (m * R) ×ˢ tsupport β) with hQdef
  have hQc : IsCompact Q := ((isCompact_sqBall _).prod hβc).image continuous_act
  have hQu : Q ⊆ invSet E a := by
    rintro _ ⟨⟨y, w⟩, ⟨hy, hw⟩, rfl⟩
    show IsUnit ((1 + Matrix.of y) * Matrix.of w)
    exact (isUnit_one_add_of_sq hy.2).mul (hβu hw)
  obtain ⟨Rq, hRq⟩ := hQc.exists_bound_of_continuousOn continuous_id.continuousOn
  set Bm' := max Bm 0 with hBm'
  set Rq' := max Rq 0 with hRq'
  have hBm0 : 0 ≤ Bm' := le_max_right _ _
  have hRq0 : 0 ≤ Rq' := le_max_right _ _
  refine ⟨Bm' * ((a : ℝ) * Rq') ^ m * volume.real Q, Q, by positivity, hQc, hQu, ?_⟩
  intro f hf F hF hFQ Y hY hR
  have hP : ∀ ε, altPoint Y ε * altPoint Y ε = 0 := altPoint_sq hY
  have hmemQ : ∀ ε v, toL ((1 - altPoint Y ε) * Matrix.of v) ∈ tsupport β → v ∈ Q := by
    intro ε v hv
    refine ⟨(toL (altPoint Y ε), toL ((1 - altPoint Y ε) * Matrix.of v)),
      ⟨⟨norm_toL_altPoint_le hR ε, hP ε⟩, hv⟩, ?_⟩
    show toL ((1 + altPoint Y ε) * ((1 - altPoint Y ε) * Matrix.of v)) = v
    have h1 : (1 + altPoint Y ε) * (1 - altPoint Y ε) = 1 := by
      calc (1 + altPoint Y ε) * (1 - altPoint Y ε) = 1 - altPoint Y ε * altPoint Y ε := by noncomm_ring
        _ = 1 := by rw [hP ε, sub_zero]
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rfl
  have hstep : ∀ ε, ∫ w, f (toL ((1 + altPoint Y ε) * Matrix.of w)) * β w =
      ∫ v, f v * β (toL ((1 - altPoint Y ε) * Matrix.of v)) := by
    intro ε
    have hmp := measurePreserving_shear (altPoint Y ε) (hP ε)
    rw [← hmp.integral_comp' (g := fun v => f v * β (toL ((1 - altPoint Y ε) * Matrix.of v)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have e1 : (shear _ (hP ε)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv w =
        shear _ (hP ε) w := rfl
    simp only [e1]
    rw [← shear_symm_apply _ (hP ε), LinearEquiv.symm_apply_apply, shear_apply]
  have hint : ∀ ε, Integrable (fun v => f v * β (toL ((1 - altPoint Y ε) * Matrix.of v))) := by
    intro ε
    have hg : Continuous fun v : Lie E a => toL ((1 - altPoint Y ε) * Matrix.of v) :=
      continuous_toL.comp (continuous_const.matrix_mul continuous_of_lie)
    have hsub : tsupport (fun v => f v * β (toL ((1 - altPoint Y ε) * Matrix.of v))) ⊆ Q :=
      (tsupport_mul_subset_right).trans
        ((tsupport_comp_subset_preimage β hg).trans fun v hv => hmemQ ε v hv)
    exact Continuous.integrable_of_hasCompactSupport
      ((hf.mul (hβ.continuous.comp hg).continuousOn).continuous_of_tsupport_subset isOpen_invSet
        (hsub.trans hQu))
      (hQc.of_isClosed_subset (isClosed_tsupport _) hsub)
  have hA : ∀ v, ∑ ε : Fin m → Bool, (altSign ε : ℂ) * (f v * β (toL ((1 - altPoint Y ε) * Matrix.of v))) =
      f v * altSum m β (fun i => toL (-(Y i * Matrix.of v))) v := by
    intro v
    rw [altSum_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [add_altPoint_eq, zsmul_eq_mul]
    ring
  simp_rw [hstep, ← integral_const_mul]
  rw [← integral_finsetSum _ (fun ε _ => (hint ε).const_mul _)]
  simp_rw [hA]
  have hpt : ∀ v, ‖f v * altSum m β (fun i => toL (-(Y i * Matrix.of v))) v‖ ≤
      Q.indicator (fun _ => F * (Bm' * (((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖))) v := by
    intro v
    by_cases hv : v ∈ Q
    · rw [Set.indicator_of_mem hv, norm_mul]
      refine mul_le_mul (hFQ v hv) ?_ (norm_nonneg _) hF
      refine (hBm _ _).trans ?_
      have hv' : ‖v‖ ≤ Rq' := (hRq v hv).trans (le_max_left _ _)
      have hprod : ∏ i, ‖toL (-(Y i * Matrix.of v))‖ ≤ ((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖ := by
        rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        have hn : ‖toL (-(Y i * Matrix.of v))‖ = ‖toL (Y i * Matrix.of v)‖ := by
          show ‖-(toL (Y i * Matrix.of v))‖ = _
          exact norm_neg _
        rw [hn]
        have hnv : ‖toL (Matrix.of v : Mat E a)‖ = ‖v‖ := rfl
        calc ‖toL (Y i * Matrix.of v)‖ ≤ a * ‖toL (Y i)‖ * ‖toL (Matrix.of v : Mat E a)‖ := norm_toL_mul_le _ _
          _ = a * ‖toL (Y i)‖ * ‖v‖ := by rw [hnv]
          _ ≤ a * ‖toL (Y i)‖ * Rq' :=
              mul_le_mul_of_nonneg_left hv' (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
          _ = a * Rq' * ‖toL (Y i)‖ := by ring
      calc Bm * ∏ i, ‖toL (-(Y i * Matrix.of v))‖ ≤ Bm' * ∏ i, ‖toL (-(Y i * Matrix.of v))‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
        _ ≤ Bm' * (((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖) := mul_le_mul_of_nonneg_left hprod hBm0
    · rw [Set.indicator_of_notMem hv]
      have hz : altSum m β (fun i => toL (-(Y i * Matrix.of v))) v = 0 := by
        rw [altSum_eq_sum]
        refine Finset.sum_eq_zero fun ε _ => ?_
        rw [add_altPoint_eq]
        by_cases hs : toL ((1 - altPoint Y ε) * Matrix.of v) ∈ tsupport β
        · exact absurd (hmemQ ε v hs) hv
        · rw [image_eq_zero_of_notMem_tsupport hs, smul_zero]
      rw [hz, mul_zero, norm_zero]
  calc ‖∫ v, f v * altSum m β (fun i => toL (-(Y i * Matrix.of v))) v‖
      ≤ ∫ v, Q.indicator (fun _ => F * (Bm' * (((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖))) v :=
        norm_integral_le_of_norm_le ((integrableOn_const hQc.measure_lt_top.ne).integrable_indicator
          hQc.measurableSet) (Filter.Eventually.of_forall hpt)
    _ = F * (Bm' * (((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖)) * volume.real Q := by
        rw [integral_indicator hQc.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
    _ = Bm' * ((a : ℝ) * Rq') ^ m * volume.real Q * F * ∏ i, ‖toL (Y i)‖ := by ring

end GlobalTheory.AltConv
end
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_signed_sum_integral_le : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β →
    HasCompactSupport β → tsupport β ⊆ invSet E a → ∀ (m : ℕ) (R : ℝ), ∃ (c : ℝ) (Q : Set (Lie E a)),
    0 ≤ c ∧ IsCompact Q ∧ Q ⊆ invSet E a ∧ ∀ f : Lie E a → ℂ, ContinuousOn f (invSet E a) →
    ∀ F : ℝ, 0 ≤ F → (∀ w ∈ Q, ‖f w‖ ≤ F) →
    ∀ Y : Fin m → Matrix (Fin a) (Fin a) (Cinf E), (∀ i j, Y i * Y j = 0) → (∀ i, ‖toL (Y i)‖ ≤ R) →
    ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) *
        ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Y ε) * Matrix.of w)) * β w‖ ≤ c * F * ∏ i, ‖toL (Y i)‖ := by
  atlas_forward_decl GlobalTheory.AltConv.norm_sum_altSign_integral_le
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.GLCuspNorm

open scoped Classical in

theorem norm_pInf_le (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : Ad E) :
    ‖pInf E x‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace E x.1‖ := by
  classical
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
  have h1 : ‖pInf E x w‖ = ‖x.1 w‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))) (x.1 w)
  rw [h1, ← GroundTheory.Automorphic.CuspidalSpectrum.normAtPlace_ringEquiv_mixedSpace, mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w _) (Finset.mem_univ w)

theorem norm_toL_map_pInf_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ c : ℝ, 0 ≤ c ∧
    ∀ M : Matrix (Fin a) (Fin a) (Ad E),
      ‖toL (M.map (pInf E))‖ ≤ c * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a M‖ := by
  intro E _ _ _ a
  refine ⟨1, zero_le_one, fun M => ?_⟩
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  refine (norm_pInf_le E (M i j)).trans ?_
  rw [← GroundTheory.Automorphic.CuspidalSpectrum.archMat_apply]
  exact GroundTheory.Automorphic.CuspidalSpectrum.norm_entry_le_norm_archMatrix _ i j

end GlobalTheory.GLCuspNorm
end
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_toL_map_pInf_le' : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ c : ℝ, 0 ≤ c ∧
    ∀ M : Matrix (Fin a) (Fin a) (Ad E),
      ‖toL (M.map (pInf E))‖ ≤ c * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a M‖ := by
  atlas_forward_decl GlobalTheory.GLCuspNorm.norm_toL_map_pInf_le
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

namespace GlobalTheory.HeightBound

theorem height_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Q : Set (Lie E a)),
    IsCompact Q → Q ⊆ invSet E a →
    ∃ H : ℝ, ∀ y : GL (Fin a) (Cinf E), toL y.val ∈ Q → GlobalTheory.CuspRep.height y ≤ H := by
  intro E _ _ _ a Q hQ hsub
  let f : Lie E a → Lie E a := fun w => toL ((Matrix.of w)⁻¹)
  have hdetc : Continuous (fun x : Lie E a => (Matrix.of x).det) := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    refine continuous_finset_sum _ fun σ _ => continuous_const.mul (continuous_finset_prod _ fun i _ => ?_)
    exact (continuous_apply i).comp (continuous_apply (σ i))
  have hadj : Continuous (fun x : Lie E a => (Matrix.of x).adjugate) :=
    Continuous.matrix_adjugate (continuous_id : Continuous fun x : Lie E a => x)
  have hf : ContinuousOn f (invSet E a) := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    have hdet : IsUnit (Matrix.of w).det := (Matrix.isUnit_iff_isUnit_det _).1 hw
    have h1 : ContinuousAt (fun x : Lie E a => Ring.inverse (Matrix.of x).det) w := by
      have := NormedRing.inverse_continuousAt hdet.unit
      rw [hdet.unit_spec] at this
      exact this.comp hdetc.continuousAt
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    simp only [f, toL, Matrix.inv_def, Matrix.smul_apply, Matrix.of_symm_apply, smul_eq_mul]
    exact h1.mul ((continuous_apply j).comp ((continuous_apply i).comp hadj)).continuousAt
  obtain ⟨C1, hC1⟩ := hQ.exists_bound_of_continuousOn (f := fun w : Lie E a => w) continuous_id.continuousOn
  obtain ⟨C2, hC2⟩ := hQ.exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨1 + C1 + C2, fun y hy => ?_⟩
  have h2 : f (toL y.val) = toL (y⁻¹).val := by
    simp only [f, toL, Equiv.apply_symm_apply, Matrix.coe_units_inv]
  have := hC2 _ hy
  rw [h2] at this
  unfold GlobalTheory.CuspRep.height
  linarith [hC1 _ hy]

end GlobalTheory.HeightBound
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bounded_of_toL_mem_isCompact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Q : Set (Lie E a)),
    IsCompact Q → Q ⊆ invSet E a →
    ∃ H : ℝ, ∀ y : GL (Fin a) (Cinf E), toL y.val ∈ Q → GlobalTheory.CuspRep.height y ≤ H := by
  atlas_forward_decl GlobalTheory.HeightBound.height_le_of_isCompact
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section
namespace GlobalTheory.HCF.Decay

theorem meanIter : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (m : ℕ) (B : ℝ),
      (∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ GroundTheory.Automorphic.scaledUnipFD E a r M) →
        ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) * φ (unip (GroundTheory.Automorphic.altPoint y ε) * x)‖ ≤ B) →
      ‖φ x‖ ≤ B := GlobalTheory.T.cuspidal_norm_le_of_alternatingSum_scaledUnipFD

theorem reproSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ),
    ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a →
    (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) →
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := GlobalTheory.T.reproducingIdentity_extends_harishChandraSpan

theorem diffInt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β →
    HasCompactSupport β → tsupport β ⊆ invSet E a → ∀ (m : ℕ) (R : ℝ), ∃ (c : ℝ) (Q : Set (Lie E a)),
    0 ≤ c ∧ IsCompact Q ∧ Q ⊆ invSet E a ∧ ∀ f : Lie E a → ℂ, ContinuousOn f (invSet E a) →
    ∀ F : ℝ, 0 ≤ F → (∀ w ∈ Q, ‖f w‖ ≤ F) →
    ∀ Y : Fin m → Matrix (Fin a) (Fin a) (Cinf E), (∀ i j, Y i * Y j = 0) → (∀ i, ‖toL (Y i)‖ ≤ R) →
    ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) *
        ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Y ε) * Matrix.of w)) * β w‖ ≤ c * F * ∏ i, ‖toL (Y i)‖ := GlobalTheory.T.norm_signed_sum_integral_le

theorem normTransfer : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ c : ℝ, 0 ≤ c ∧
    ∀ M : Matrix (Fin a) (Fin a) (Ad E),
      ‖toL (M.map (pInf E))‖ ≤ c * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a M‖ := GlobalTheory.T.norm_toL_map_pInf_le'

theorem heightBound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Q : Set (Lie E a)),
    IsCompact Q → Q ⊆ invSet E a →
    ∃ H : ℝ, ∀ y : GL (Fin a) (Cinf E), toL y.val ∈ Q → GlobalTheory.CuspRep.height y ≤ H := GlobalTheory.T.height_bounded_of_toL_mem_isCompact

section Span
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {L : Subgroup (GL (Fin a) (Af E))}
  {W : Submodule ℂ (Kinf E a → ℂ)} {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ}

theorem span_left {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.1.left
  | zero => intro γ g; rfl
  | add x y _ _ hx hy => intro γ g; simp [hx γ g, hy γ g]
  | smul c x _ hx => intro γ g; simp [hx γ g]

theorem span_fin {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ l ∈ L, finRep E a l φ = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.2.1
  | zero => intro l _; exact map_zero _
  | add x y _ _ hx hy => intro l hl; rw [map_add, hx l hl, hy l hl]
  | smul c x _ hx => intro l hl; rw [map_smul, hx l hl]

theorem span_right {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) {l : GL (Fin a) (Af E)} (hl : l ∈ L)
    (g : GA E a) : φ.1 (g * finGL E a l) = φ.1 g :=
  congrFun (congrArg Subtype.val (span_fin hφ l hl)) g

theorem span_cont (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) : Continuous φ.1 := by
  refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a φ ?_
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun l => k * l) '' (L : Set (GL (Fin a) (Af E))), ?_, ?_, ⟨1, L.one_mem, mul_one k⟩⟩
  · rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, span_fin hφ l hl]
    exact hk
  · exact (Homeomorph.mulLeft k).isOpenMap _ hL

end Span

section Conj
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem nilM_add' {R : Type} [CommRing R] {r : ℕ} (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp

theorem nilM_zero' {R : Type} [CommRing R] {r : ℕ} : nilM (0 : BlockIx a r → R) = 0 := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.zero_apply]; split_ifs <;> rfl

theorem map_unip' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {r : ℕ} (P : BlockIx a r → R) :
    Matrix.GeneralLinearGroup.map f (unip P) = unip (fun p => f (P p)) := by
  ext i j
  change f ((1 + nilM P : Matrix (Fin a) (Fin a) R) i j) = (1 + nilM (fun p => f (P p)) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

variable (E) in

def conjY {r : ℕ} (x : GA E a) : (BlockIx a r → Ad E) →+ Matrix (Fin a) (Fin a) (Cinf E) where
  toFun P := (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * nilM P * (x : Matrix (Fin a) (Fin a) (Ad E))).map (pInf E)
  map_zero' := by simp [nilM_zero']
  map_add' P Q := by
    simp only [nilM_add', Matrix.mul_add, Matrix.add_mul]
    exact Matrix.map_add _ (map_add (pInf E)) _ _

theorem conjY_apply {r : ℕ} (x : GA E a) (P : BlockIx a r → Ad E) :
    conjY E x P = (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * nilM P * (x : Matrix (Fin a) (Fin a) (Ad E))).map (pInf E) := rfl

theorem conjY_mul {r : ℕ} (x : GA E a) (P Q : BlockIx a r → Ad E) : conjY E x P * conjY E x Q = 0 := by
  rw [conjY_apply, conjY_apply, ← Matrix.map_mul]
  have : ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * nilM P * (x : Matrix (Fin a) (Fin a) (Ad E)) *
      (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * nilM Q * (x : Matrix (Fin a) (Fin a) (Ad E))) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x : Matrix (Fin a) (Fin a) (Ad E)), Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (nilM P), nilM_mul, Matrix.zero_mul, Matrix.mul_zero]
  rw [this]; simp

theorem conjY_truncInf {r : ℕ} (x : GA E a) (P : BlockIx a r → Ad E) :
    conjY E x (GroundTheory.Automorphic.CuspidalSpectrum.truncInf P) = conjY E x P := by
  rw [conjY_apply, conjY_apply, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp only [nilM, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · rfl
  · simp

theorem conj_unip_eq {r : ℕ} (x : GA E a) (P : BlockIx a r → Ad E) (hP : ∀ p, (P p).2 = 0) :
    x⁻¹ * unip P * x = infGL E a (Matrix.GeneralLinearGroup.map (pInf E) (x⁻¹ * unip P * x)) := by
  refine ga_ext (by simp) ?_
  rw [pFin_infGL, map_mul, map_mul, map_unip', map_inv]
  have : (fun p => pFin E (P p)) = 0 := funext hP
  rw [this, show unip (0 : BlockIx a r → Af E) = 1 from Units.ext (by change 1 + nilM 0 = 1; rw [nilM_zero', add_zero]),
    mul_one, inv_mul_cancel]

theorem val_map_conj_unip {r : ℕ} (x : GA E a) (P : BlockIx a r → Ad E) :
    ((Matrix.GeneralLinearGroup.map (pInf E) (x⁻¹ * unip P * x) : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      1 + conjY E x P := by
  rw [conjY_apply]
  change (((x⁻¹ * unip P * x : GA E a)) : Matrix (Fin a) (Fin a) (Ad E)).map (pInf E) = _
  rw [Units.val_mul, Units.val_mul]
  change ((((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 + nilM P)) * (x : Matrix (Fin a) (Fin a) (Ad E))).map (pInf E) = _
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul, Matrix.map_add _ (map_add (pInf E)),
    Matrix.map_one _ (map_zero (pInf E)) (map_one (pInf E))]

end Conj

theorem oneRoot (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ))
    (N : ℕ) (β : Lie E a → ℂ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) (hβu : tsupport β ⊆ invSet E a)
    (hrep : ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g)
    (φ : Sm E a) (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) (hcusp : IsCuspidal φ.1)
    (Ω : Set (GA E a)) (hΩ : IsCompact Ω) (hΩB : Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)))
    (t C₀ : ℝ) (N₀ : ℕ) (ht : 0 < t)
    (hgrow : ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)),
      ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤
        C₀ * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * GlobalTheory.CuspRep.height y ^ N₀)
    (m s : ℕ) (hs : 0 < s) (hsa : s < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      ∀ k ∈ (maxCompact : Subgroup (GA E a)),
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤
        C * (r ⟨s, hsa⟩ / r ⟨s - 1, by omega⟩) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := by
  classical
  obtain ⟨M, hM, hfin⟩ := GlobalTheory.T.exists_conj_finiteUnipotent_mem_openSubgroup E a s L hL Ω hΩ
  obtain ⟨C₁, hC₁⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_norm_archMat_conj_le hΩ hΩB ht hs hsa
    (GroundTheory.Automorphic.isCompact_scaledInfSet (K := E) M)
  obtain ⟨cT, hcT0, hcT⟩ := normTransfer E a
  set K₁ := cT * max C₁ 0 with hK₁
  have hK₁0 : 0 ≤ K₁ := mul_nonneg hcT0 (le_max_right _ _)
  obtain ⟨c, Q, hc0, hQ, hQinv, hdiff⟩ := diffInt E a β hβ hβc hβu m (K₁ * t⁻¹)
  obtain ⟨H, hH⟩ := heightBound E a Q hQ hQinv
  set H' := max H 1 with hH'
  set C₀' := max C₀ 0 with hC₀'
  have hH'0 : 0 ≤ H' := le_trans zero_le_one (le_max_right _ _)
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  refine ⟨c * C₀' * H' ^ N₀ * K₁ ^ m, by positivity, ?_⟩
  intro b hb r hr hsieg k hk
  set x := b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k with hx
  set Sr := ∑ i, (r i + (r i)⁻¹) with hSr
  have hSr0 : 0 ≤ Sr := Finset.sum_nonneg fun i _ => add_nonneg (hr i).le (inv_nonneg.2 (hr i).le)
  set gain := r ⟨s, hsa⟩ / r ⟨s - 1, by omega⟩ with hgaindef
  have hgain0 : 0 ≤ gain := div_nonneg (hr _).le (hr _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨s - 1, by omega⟩ ⟨s, hsa⟩ (by simp; omega)
    rw [hgaindef, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  set f := chart φ.1 x with hf
  have hfc : ContinuousOn f (invSet E a) := (φ.2 x).continuousOn
  set F := C₀' * Sr ^ N₀ * H' ^ N₀ with hF
  have hF0 : 0 ≤ F := by positivity
  have hfQ : ∀ w ∈ Q, ‖f w‖ ≤ F := by
    intro w hw
    obtain ⟨u, hu⟩ := hQinv hw
    have hw' : w = toL u.val := by rw [hu]; rfl
    rw [hw'] at hw ⊢
    rw [hf, chart_val]
    have h1 := hgrow b hb r hr k hk u
    have h2 : GlobalTheory.CuspRep.height u ^ N₀ ≤ H' ^ N₀ :=
      pow_le_pow_left₀ (le_trans zero_le_one (one_le_height u)) ((hH u hw).trans (le_max_left _ _)) _
    calc ‖φ.1 (x * infGL E a u)‖ ≤ C₀ * Sr ^ N₀ * GlobalTheory.CuspRep.height u ^ N₀ := h1
      _ ≤ C₀' * Sr ^ N₀ * GlobalTheory.CuspRep.height u ^ N₀ := by
          gcongr
          · exact pow_nonneg (le_trans zero_le_one (one_le_height u)) _
          · exact le_max_left _ _
      _ ≤ F := by rw [hF]; gcongr
  refine meanIter E a s hs hsa φ.1 (span_left hφ) hcusp (span_cont hL hφ) M hM x m _ ?_
  intro y hy
  set Yv : Fin m → Matrix (Fin a) (Fin a) (Cinf E) := fun i => conjY E x (y i) with hYv
  have hYY : ∀ i j, Yv i * Yv j = 0 := fun i j => conjY_mul x _ _
  have hYn : ∀ i, ‖toL (Yv i)‖ ≤ K₁ * gain := by
    intro i
    have h1 := hC₁ b hb r hr hsieg k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncInf (y i)) (fun p => rfl)
      (fun p => GroundTheory.Automorphic.infinite_mem_scaledInfSet hM (hy i) p)
    have h2 := hcT (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
      nilM (GroundTheory.Automorphic.CuspidalSpectrum.truncInf (y i)) * (x : Matrix (Fin a) (Fin a) (Ad E)))
    have e : Yv i = (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        nilM (GroundTheory.Automorphic.CuspidalSpectrum.truncInf (y i)) * (x : Matrix (Fin a) (Fin a) (Ad E))).map (pInf E) := by
      rw [hYv]; dsimp only; rw [← conjY_truncInf, conjY_apply]
    rw [e]
    refine h2.trans ?_
    calc cT * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
          nilM (GroundTheory.Automorphic.CuspidalSpectrum.truncInf (y i)) * (x : Matrix (Fin a) (Fin a) (Ad E)))‖
        ≤ cT * (C₁ * gain) := mul_le_mul_of_nonneg_left h1 hcT0
      _ ≤ cT * (max C₁ 0 * gain) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0) hcT0
      _ = K₁ * gain := by rw [hK₁]; ring
  have hYR : ∀ i, ‖toL (Yv i)‖ ≤ K₁ * t⁻¹ := fun i => (hYn i).trans (mul_le_mul_of_nonneg_left hgain hK₁0)
  have key : ∀ ε : Fin m → Bool, φ.1 (unip (GroundTheory.Automorphic.altPoint y ε) * x) =
      ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Yv ε) * Matrix.of w)) * β w := by
    intro ε
    set sε := GroundTheory.Automorphic.altPoint y ε with hsε
    have hsplit : unip sε * x = x * (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf sε) * x) *
        (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncFin sε) * x) := by
      conv_lhs => rw [← GroundTheory.Automorphic.CuspidalSpectrum.truncInf_add_truncFin sε, unip_add]
      group
    obtain ⟨l, hl, hle⟩ := hfin b hb r hr k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncFin sε) (fun p => rfl)
      (fun p => GroundTheory.Automorphic.exists_finite_altPoint_eq_natCast_mul hM y hy ε p)
    rw [hsplit, hle, span_right hφ hl, conj_unip_eq x _ (fun p => rfl)]
    rw [← reproSpan E a L W X N β hβ hβc hβu hrep φ hφ, chart_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hv := val_map_conj_unip x (GroundTheory.Automorphic.CuspidalSpectrum.truncInf sε)
    rw [conjY_truncInf, hsε, GroundTheory.Automorphic.CuspidalSpectrum.map_altPoint] at hv
    simp only [Function.comp_apply]
    congr 2
    change toL (((Matrix.GeneralLinearGroup.map (pInf E) _ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of w) = _
    rw [hv]
  have hsum : ∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) * φ.1 (unip (GroundTheory.Automorphic.altPoint y ε) * x) =
      ∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) *
        ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Yv ε) * Matrix.of w)) * β w :=
    Finset.sum_congr rfl fun ε _ => by rw [key ε]
  rw [hsum]
  refine (hdiff f hfc F hF0 hfQ Yv hYY hYR).trans ?_
  have hprod : ∏ i, ‖toL (Yv i)‖ ≤ (K₁ * gain) ^ m := by
    rw [← Fin.prod_const]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
  calc c * F * ∏ i, ‖toL (Yv i)‖ ≤ c * F * (K₁ * gain) ^ m := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = c * C₀' * H' ^ N₀ * K₁ ^ m * gain ^ m * Sr ^ N₀ := by rw [hF]; ring

theorem decay : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a → (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) → ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ Ω : Set (GA E a), IsCompact Ω → Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) → ∀ (t C₀ : ℝ) (N₀ : ℕ), 0 < t → (∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C₀ * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀) → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ i j : Fin a, (j : ℕ) = i + 1 → ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤ C * (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := by
  intro E _ _ _ a L hL W X N β hβ hβc hβu hrep φ hφ hcusp Ω hΩ hΩB t C₀ N₀ ht hgrow m
  have hex : ∀ (s : ℕ) (hs : 0 < s) (hsa : s < a), ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i),
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ k ∈ (maxCompact : Subgroup (GA E a)),
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤
        C * (r ⟨s, hsa⟩ / r ⟨s - 1, by omega⟩) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := fun s hs hsa =>
    oneRoot E a L hL W X N β hβ hβc hβu hrep φ hφ hcusp Ω hΩ hΩB t C₀ N₀ ht hgrow m s hs hsa
  choose Cf hCf0 hCf using hex
  refine ⟨∑ s : Fin a, if h : 0 < (s : ℕ) then Cf s h s.2 else 0,
    Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hCf0], ?_⟩
  intro b hb r hr hsieg k hk i j hij
  have hj0 : 0 < (j : ℕ) := by omega
  have h := hCf j hj0 j.2 b hb r hr hsieg k hk
  have e1 : (⟨(j : ℕ) - 1, by omega⟩ : Fin a) = i := Fin.ext (by simp; omega)
  rw [e1] at h
  have hle : Cf j hj0 j.2 ≤ ∑ s : Fin a, if h : 0 < (s : ℕ) then Cf s h s.2 else 0 := by
    have h1 := Finset.single_le_sum (f := fun s : Fin a => if h : 0 < (s : ℕ) then Cf s h s.2 else 0)
      (fun s _ => by split_ifs <;> simp [hCf0]) (Finset.mem_univ j)
    simpa [hj0] using h1
  refine h.trans ?_
  have hpos : 0 ≤ (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ :=
    mul_nonneg (pow_nonneg (div_nonneg (hr _).le (hr _).le) _)
      (pow_nonneg (Finset.sum_nonneg fun i _ => add_nonneg (hr i).le (inv_nonneg.2 (hr i).le)) _)
  calc Cf j hj0 j.2 * (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀
      = Cf j hj0 j.2 * ((r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀) := by ring
    _ ≤ (∑ s : Fin a, if h : 0 < (s : ℕ) then Cf s h s.2 else 0) * ((r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀) :=
        mul_le_mul_of_nonneg_right hle hpos
    _ = _ := by ring

end GlobalTheory.HCF.Decay
end
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_rapidDecay_one_simpleRoot : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a → (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) → ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ Ω : Set (GA E a), IsCompact Ω → Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) → ∀ (t C₀ : ℝ) (N₀ : ℕ), 0 < t → (∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C₀ * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀) → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ i j : Fin a, (j : ℕ) = i + 1 → ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤ C * (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := by
  atlas_forward_decl GlobalTheory.HCF.Decay.decay
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

namespace GlobalTheory.RatioIneq

theorem chain_bound (a : ℕ) (t ρ : ℝ) (ht : 0 < t) (hρ : 1 ≤ ρ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlo : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hhi : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ n : ℕ, ∀ i k : Fin a, (i : ℕ) + n = k →
      r i ≤ (max 1 t⁻¹ * ρ) ^ n * r k ∧ r k ≤ (max 1 t⁻¹ * ρ) ^ n * r i := by
  have hM1 : (1:ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hBρ : ρ ≤ max 1 t⁻¹ * ρ := le_mul_of_one_le_left (by linarith) hM1
  have hBt : t⁻¹ ≤ max 1 t⁻¹ * ρ :=
    (le_max_right 1 t⁻¹).trans (le_mul_of_one_le_right (by linarith) hρ)
  intro n
  induction n with
  | zero =>
    intro i k h
    have : i = k := Fin.ext (by simpa using h)
    subst this; simp
  | succ n ih =>
    intro i k h
    have hk' : (i : ℕ) + n < a := by have := k.isLt; omega
    obtain ⟨h1, h2⟩ := ih i ⟨i + n, hk'⟩ rfl
    have hkk : (k : ℕ) = ((⟨i + n, hk'⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have n1 : r ⟨i + n, hk'⟩ ≤ (max 1 t⁻¹ * ρ) * r k :=
      (hhi _ k hkk).trans (mul_le_mul_of_nonneg_right hBρ (hr k).le)
    have n2 : r k ≤ (max 1 t⁻¹ * ρ) * r ⟨i + n, hk'⟩ := by
      have hl := hlo _ k hkk
      have : r k ≤ t⁻¹ * r ⟨i + n, hk'⟩ := by
        calc r k = t⁻¹ * (t * r k) := by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
          _ ≤ t⁻¹ * r ⟨i + n, hk'⟩ := mul_le_mul_of_nonneg_left hl (inv_nonneg.2 ht.le)
      exact this.trans (mul_le_mul_of_nonneg_right hBt (hr _).le)
    have hB0 : 0 ≤ (max 1 t⁻¹ * ρ) := by linarith
    have hBn : 0 ≤ (max 1 t⁻¹ * ρ) ^ n := pow_nonneg hB0 n
    constructor
    · calc r i ≤ (max 1 t⁻¹ * ρ) ^ n * r ⟨i + n, hk'⟩ := h1
        _ ≤ (max 1 t⁻¹ * ρ) ^ n * ((max 1 t⁻¹ * ρ) * r k) := mul_le_mul_of_nonneg_left n1 hBn
        _ = (max 1 t⁻¹ * ρ) ^ (n+1) * r k := by ring
    · calc r k ≤ (max 1 t⁻¹ * ρ) * r ⟨i + n, hk'⟩ := n2
        _ ≤ (max 1 t⁻¹ * ρ) * ((max 1 t⁻¹ * ρ) ^ n * r i) := mul_le_mul_of_nonneg_left h2 hB0
        _ = (max 1 t⁻¹ * ρ) ^ (n+1) * r i := by ring

theorem pair_bound (a : ℕ) (t ρ : ℝ) (ht : 0 < t) (hρ : 1 ≤ ρ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlo : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hhi : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) (i k : Fin a) :
    r i ≤ (max 1 t⁻¹ * ρ) ^ a * r k := by
  have hB1 : 1 ≤ max 1 t⁻¹ * ρ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hρ
  have hi := i.isLt
  have hk := k.isLt
  rcases le_total (i : ℕ) k with h | h
  · obtain ⟨h1, -⟩ := chain_bound a t ρ ht hρ r hr hlo hhi (k - i) i k (by omega)
    exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (hr k).le)
  · obtain ⟨-, h2⟩ := chain_bound a t ρ ht hρ r hr hlo hhi (i - k) k i (by omega)
    exact h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (hr k).le)

theorem le_max_one_of_pow_le {x c : ℝ} {a : ℕ} (ha : a ≠ 0) (h : x ^ a ≤ c) : x ≤ max 1 c := by
  rcases le_total x 1 with h1 | h1
  · exact h1.trans (le_max_left _ _)
  · exact (le_self_pow₀ h1 ha).trans (h.trans (le_max_right _ _))

end GlobalTheory.RatioIneq

namespace GlobalTheory.RatioIneq

theorem sum_add_inv_le_of_ratio_bounds :
    ∀ (a : ℕ) (t c₁ c₂ : ℝ), 0 < t → 0 < c₁ → ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ r : Fin a → ℝ,
      (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      c₁ ≤ ∏ i, r i → ∏ i, r i ≤ c₂ → ∀ ρ : ℝ, 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∑ i, (r i + (r i)⁻¹) ≤ C * ρ ^ K := by
  intro a t c₁ c₂ ht hc₁
  refine ⟨a * (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹) ^ a, a, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ max 1 c₂ := (zero_le_one.trans (le_max_left _ _))
    have h2 : (0:ℝ) ≤ max 1 c₁⁻¹ := (zero_le_one.trans (le_max_left _ _))
    have h3 : (0:ℝ) ≤ max 1 t⁻¹ := (zero_le_one.trans (le_max_left _ _))
    positivity
  intro r hr hlo hP1 hP2 ρ hρ hhi
  have hB1 : 1 ≤ max 1 t⁻¹ * ρ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hρ
  have hBa : 0 < (max 1 t⁻¹ * ρ) ^ a := pow_pos (by linarith) a
  have pb := pair_bound a t ρ ht hρ r hr hlo hhi
  have hup : ∀ i, r i ≤ max 1 c₂ * (max 1 t⁻¹ * ρ) ^ a := by
    intro i
    have ha : a ≠ 0 := by have := i.isLt; omega
    have hx : ∀ k, r i / (max 1 t⁻¹ * ρ) ^ a ≤ r k := fun k => by
      rw [div_le_iff₀ hBa, mul_comm]; exact pb i k
    have hprod : (r i / (max 1 t⁻¹ * ρ) ^ a) ^ a ≤ ∏ k, r k := by
      have := Finset.prod_le_prod (s := Finset.univ)
        (f := fun _ : Fin a => r i / (max 1 t⁻¹ * ρ) ^ a) (g := r)
        (fun _ _ => (div_pos (hr i) hBa).le) (fun k _ => hx k)
      rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    have := le_max_one_of_pow_le ha (hprod.trans hP2)
    rwa [div_le_iff₀ hBa] at this
  have hdown : ∀ i, (r i)⁻¹ ≤ max 1 c₁⁻¹ * (max 1 t⁻¹ * ρ) ^ a := by
    intro i
    have ha : a ≠ 0 := by have := i.isLt; omega
    have hy : 0 < (max 1 t⁻¹ * ρ) ^ a * r i := mul_pos hBa (hr i)
    have hprod : ∏ k, r k ≤ ((max 1 t⁻¹ * ρ) ^ a * r i) ^ a := by
      have := Finset.prod_le_prod (s := Finset.univ) (f := r)
        (g := fun _ : Fin a => (max 1 t⁻¹ * ρ) ^ a * r i)
        (fun k _ => (hr k).le) (fun k _ => pb k i)
      simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
    have hc : ((max 1 t⁻¹ * ρ) ^ a * r i)⁻¹ ^ a ≤ c₁⁻¹ := by
      rw [inv_pow]; exact inv_anti₀ hc₁ (hP1.trans hprod)
    have := le_max_one_of_pow_le ha hc
    have heq : (r i)⁻¹ = (max 1 t⁻¹ * ρ) ^ a * ((max 1 t⁻¹ * ρ) ^ a * r i)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hBa.ne', one_mul]
    rw [heq, mul_comm (max 1 c₁⁻¹)]
    exact mul_le_mul_of_nonneg_left this hBa.le
  calc ∑ i, (r i + (r i)⁻¹)
      ≤ ∑ _i : Fin a, (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹ * ρ) ^ a :=
        Finset.sum_le_sum fun i _ => by rw [add_mul]; exact add_le_add (hup i) (hdown i)
    _ = a * (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹) ^ a * ρ ^ a := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_pow]; ring

end GlobalTheory.RatioIneq
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_add_inv_le_of_consecutiveRatio_bounds : ∀ (a : ℕ) (t c₁ c₂ : ℝ), 0 < t → 0 < c₁ → ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → c₁ ≤ ∏ i, r i → ∏ i, r i ≤ c₂ → ∀ ρ : ℝ, 1 ≤ ρ → (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) → ∑ i, (r i + (r i)⁻¹) ≤ C * ρ ^ K := by
  atlas_forward_decl GlobalTheory.RatioIneq.sum_add_inv_le_of_ratio_bounds
end

section
section
namespace GlobalTheory.HCF

open NumberField MeasureTheory GlobalTheory.CuspRep Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

theorem bounded_on_band_of_cuspidal : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∃ M : ℝ, ∀ g ∈ band E a, ‖φ.1 g‖ ≤ M := by
  intro E _ _ _ a L hL W hW X hX N φ hφ hcusp
  have hleft : ∀ ψ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g := by
    intro ψ hψ γ g
    induction hψ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy =>
      change x.1 (ratGL E a γ * g) + y.1 (ratGL E a γ * g) = x.1 g + y.1 g
      rw [hx, hy]
    | smul c x _ hx =>
      change c * x.1 (ratGL E a γ * g) = c * x.1 g
      rw [hx]
  obtain ⟨Ω, hΩc, hΩB, t, c₁, c₂, ht, hc₁, hred⟩ := GlobalTheory.T.exists_siegelSet_reduction_adelicDetNormBand E a
  obtain ⟨C₀, N₀, hC₀, hpoly⟩ := GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms E a L hL W X N φ hφ Ω hΩc
  obtain ⟨β, hβ, hβc, hβs, hrep⟩ := GlobalTheory.T.exists_test_function_reproducing_forms_gl E a L W hW X hX N
  obtain ⟨C', K, hC', hineq⟩ := GlobalTheory.T.sum_add_inv_le_of_consecutiveRatio_bounds a t c₁ c₂ ht hc₁
  obtain ⟨Cm, hCm, hdec⟩ := GlobalTheory.T.cuspidal_rapidDecay_one_simpleRoot E a L hL W X N β hβ hβc hβs hrep φ hφ hcusp Ω hΩc hΩB t C₀ N₀ ht hpoly (K * N₀)
  refine ⟨max (C₀ * C' ^ N₀ * height (1 : GL (Fin a) (Cinf E)) ^ N₀) (Cm * C' ^ N₀), fun g hg => ?_⟩
  obtain ⟨γ, b, hb, r, hr, hrat, hp1, hp2, k, hk, hg'⟩ := hred g hg
  rw [← hleft φ hφ γ g, hg']
  have hs0 : 0 ≤ ∑ i, (r i + (r i)⁻¹) := Finset.sum_nonneg fun i _ => by have := hr i; positivity
  by_cases hP : ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ 1 ≤ r i / r j
  · obtain ⟨i₀, j₀, hij₀, h1⟩ := hP
    obtain ⟨p, hpP, hpmax⟩ := ((Finset.univ : Finset (Fin a × Fin a)).filter
      (fun p => (p.2 : ℕ) = p.1 + 1)).exists_max_image (fun p => r p.1 / r p.2)
      ⟨(i₀, j₀), by simp [hij₀]⟩
    have hpP' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hpP).2
    have hρ1 : 1 ≤ r p.1 / r p.2 := le_trans h1 (hpmax (i₀, j₀) (by simp [hij₀]))
    have hρ0 : 0 < r p.1 / r p.2 := by linarith
    have hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ (r p.1 / r p.2) * r j := fun i j hij => by
      have := hpmax (i, j) (by simp [hij])
      rwa [div_le_iff₀ (hr j)] at this
    have hsle := hineq r hr hrat hp1 hp2 _ hρ1 hall
    have hd := hdec b hb r hr hrat k hk p.1 p.2 hpP'
    refine le_trans hd (le_trans ?_ (le_max_right _ _))
    have e : r p.2 / r p.1 = (r p.1 / r p.2)⁻¹ := by rw [inv_div]
    rw [e]
    calc Cm * (r p.1 / r p.2)⁻¹ ^ (K * N₀) * (∑ i, (r i + (r i)⁻¹)) ^ N₀
        ≤ Cm * (r p.1 / r p.2)⁻¹ ^ (K * N₀) * (C' * (r p.1 / r p.2) ^ K) ^ N₀ := by
          gcongr
      _ = Cm * C' ^ N₀ := by
          rw [mul_pow, ← pow_mul, inv_pow]
          field_simp
  · push_neg at hP
    have hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ 1 * r j := fun i j hij => by
      have := (hP i j hij).le
      rwa [div_le_iff₀ (hr j)] at this
    have hsle := hineq r hr hrat hp1 hp2 1 le_rfl hall
    rw [one_pow, mul_one] at hsle
    have hb' := hpoly b hb r hr k hk 1
    rw [map_one, mul_one] at hb'
    refine le_trans hb' (le_trans ?_ (le_max_left _ _))
    have hh : 0 ≤ height (1 : GL (Fin a) (Cinf E)) := le_trans zero_le_one (one_le_height _)
    gcongr

end GlobalTheory.HCF
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_harishChandraFiniteForm_bounded_detNormBand : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∃ M : ℝ, ∀ g ∈ band E a, ‖φ.1 g‖ ≤ M := by
  atlas_forward_decl GlobalTheory.HCF.bounded_on_band_of_cuspidal
end
