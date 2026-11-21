import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.TrMulComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PTestJ
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.VeryCuspZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnInvReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PGrowth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.PChart
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ActHcsSlice
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenformsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBounded
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PRepro
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf

section
noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.Rg.BcB.CG.SmoothIntegrals

variable {X M T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]

def pd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Q : X × M → V) (q : X × M) : X →L[ℝ] V :=
  fderiv ℝ (fun x => Q (x, q.2)) q.1

omit [FiniteDimensional ℝ X] in
theorem contDiffOn_pd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Q : X × M → V} {U : Set X} {W : Set M}
    (hU : IsOpen U) (hW : IsOpen W) (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) : ContDiffOn ℝ ∞ (pd Q) (U ×ˢ W) := by
  intro q hq
  have hQa : ContDiffAt ℝ ∞ Q q := hQ.contDiffAt ((hU.prod hW).mem_nhds hq)
  refine ContDiffAt.contDiffWithinAt ?_
  refine ContDiffAt.fderiv (f := fun (r : X × M) (x : X) => Q (x, r.2)) (g := fun r => r.1) ?_ contDiffAt_fst
    ENat.coe_top_add_one.le
  have e : Function.uncurry (fun (r : X × M) (x : X) => Q (x, r.2)) = Q ∘ fun z : (X × M) × X => (z.2, z.1.2) := rfl
  rw [e]
  exact ContDiffAt.comp _ hQa (contDiffAt_snd.prodMk (contDiffAt_snd.comp _ contDiffAt_fst))

variable {μ : Measure T} [IsFiniteMeasureOnCompacts μ] {U : Set X} {W : Set M} {p : T → M}

theorem hasFDerivAt_step (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Q : X × M → V}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) (hs : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0)
    {x₀ : X} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ y, Q (x, p y) ∂μ) (∫ y, pd Q (x₀, p y) ∂μ) x₀ := by
  obtain ⟨K, hK, hKe⟩ := hs x₀ hx₀
  have hUW := hU.prod hW
  obtain ⟨δ, hδ, hδK⟩ := Metric.eventually_nhds_iff_ball.1 hKe
  obtain ⟨ε₀, hε₀, hε₀U⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set ε := min (δ / 2) (ε₀ / 2) with hεdef
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos hε₀)
  have hcb : closedBall x₀ ε ⊆ U := fun x hx =>
    hε₀U (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε₀))))
  have hcbδ : closedBall x₀ ε ⊆ ball x₀ δ := fun x hx =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)))
  have hQc : ContinuousOn Q (U ×ˢ W) := hQ.continuousOn
  have hPc : ContinuousOn (pd Q) (U ×ˢ W) := (contDiffOn_pd hU hW hQ).continuousOn
  have hcpt : IsCompact (closedBall x₀ ε ×ˢ (p '' K)) := (isCompact_closedBall x₀ ε).prod (hK.image hp)
  have hsub : closedBall x₀ ε ×ˢ (p '' K) ⊆ U ×ˢ W := prod_mono hcb (by rintro _ ⟨y, -, rfl⟩; exact hpW y)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hPc.mono hsub)
  have hzero : ∀ x ∈ ball x₀ δ, ∀ y ∉ K, pd Q (x, p y) = 0 := by
    intro x hx y hy
    have h0 : (fun x' => Q (x', p y)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx] with x' hx' using hδK x' hx' y hy
    show fderiv ℝ (fun x' => Q (x', p y)) x = 0
    rw [h0.fderiv_eq]
    exact fderiv_const_apply _
  have hdiff : ∀ x ∈ U, ∀ y, HasFDerivAt (fun x' => Q (x', p y)) (pd Q (x, p y)) x := by
    intro x hx y
    have h1 : ContDiffAt ℝ ∞ Q (x, p y) := hQ.contDiffAt (hUW.mem_nhds ⟨hx, hpW y⟩)
    have h2 : DifferentiableAt ℝ (fun x' => Q (x', p y)) x :=
      (h1.differentiableAt (by simp)).comp x (differentiableAt_id.prodMk (differentiableAt_const _))
    exact h2.hasFDerivAt
  have hcont : ∀ x ∈ U, Continuous fun y => Q (x, p y) := fun x hx =>
    hQc.comp_continuous (continuous_const.prodMk hp) fun y => ⟨hx, hpW y⟩
  have hcont' : ∀ x ∈ U, Continuous fun y => pd Q (x, p y) := fun x hx =>
    hPc.comp_continuous (continuous_const.prodMk hp) fun y => ⟨hx, hpW y⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (F := fun x y => Q (x, p y))
    (F' := fun x y => pd Q (x, p y)) (s := ball x₀ ε) (bound := K.indicator fun _ => C)
    (ball_mem_nhds x₀ hε) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hU.mem_nhds hx₀] with x hx using (hcont x hx).aestronglyMeasurable
  · exact (hcont x₀ hx₀).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy => hδK x₀ (mem_ball_self hδ) y hy)
  · exact (hcont' x₀ hx₀).aestronglyMeasurable
  · refine ae_of_all _ fun y x hx => ?_
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      exact hC _ ⟨ball_subset_closedBall hx, mem_image_of_mem p hy⟩
    · rw [hzero x (hcbδ (ball_subset_closedBall hx)) y hy, indicator_of_notMem hy, norm_zero]
  · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  · exact ae_of_all _ fun y x hx => hdiff x (hcb (ball_subset_closedBall hx)) y

theorem contDiffOn_integral_nat (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : X × M → V),
      ContDiffOn ℝ ∞ Q (U ×ˢ W) → (∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0) →
      ContDiffOn ℝ n (fun x => ∫ y, Q (x, p y) ∂μ) U := by
  induction n with
  | zero =>
    intro V _ _ _ Q hQ hs
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro V _ _ _ Q hQ hs
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hs' : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, pd Q (x', p y) = 0 := by
      intro x hx
      obtain ⟨K, hK, hKe⟩ := hs x hx
      refine ⟨K, hK, ?_⟩
      filter_upwards [eventually_eventually_nhds.2 hKe] with x' hx' y hy
      have h0 : (fun x'' => Q (x'', p y)) =ᶠ[𝓝 x'] fun _ => 0 := hx'.mono fun x'' h => h y hy
      show fderiv ℝ (fun x'' => Q (x'', p y)) x' = 0
      rw [h0.fderiv_eq]
      exact fderiv_const_apply _
    exact (ih (X →L[ℝ] V) (pd Q) (contDiffOn_pd hU hW hQ) hs').congr fun x hx =>
      (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).fderiv

theorem contDiffOn_integral (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Q : X × M → V}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) (hs : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ y, Q (x, p y) ∂μ) U :=
  contDiffOn_infty.2 fun n => contDiffOn_integral_nat hU hW hp hpW n V Q hQ hs

end PositivityTheory.Rg.BcB.CG.SmoothIntegrals

end
end

section
noncomputable section

open NumberField MeasureTheory Filter Topology Metric Set
open GlobalTheory.CuspRep
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG.SmoothIntegrals

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

abbrev gI (v : InfinitePlace E) : GA E n →* G n := Matrix.GeneralLinearGroup.map (PositivityTheory.Rg.BcB.cV v)

theorem continuous_pInf₀ : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_gI (v : InfinitePlace E) : Continuous (gI (n := n) v : GA E n → G n) :=
  Continuous.units_map _ (continuous_id.matrix_map ((continuous_apply v).comp continuous_pInf₀))

theorem continuous_infGL₀ : Continuous (infGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem gI_infGL_val (v : InfinitePlace E) (u : GL (Fin n) (Cinf E)) :
    (gI v (infGL E n u)).val = fun i j => u.val i j v := by
  ext i j
  exact congrArg (fun y : GL (Fin n) (Cinf E) => y.val i j v) (pInf_infGL (E := E) (a := n) u)

omit [NumberField E] [IsTotallyComplex E] in
theorem isOpen_GLs₀ : IsOpen (GLs n) :=
  isOpen_ne.preimage (Continuous.matrix_det continuous_id)

omit [NumberField E] [IsTotallyComplex E] in
theorem val_mem_GLs₀ (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

omit [NumberField E] [IsTotallyComplex E] in

def xv (v : InfinitePlace E) (x : Lie E n) : Mat n := fun i j => x i j v

omit [IsTotallyComplex E] in
theorem contDiff_xv (v : InfinitePlace E) : ContDiff ℝ ∞ (xv (n := n) v) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ ℂ v).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i))

omit [NumberField E] [IsTotallyComplex E] in
theorem contDiffAt_matMul {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : X → Mat n} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) : ContDiffAt ℝ ∞ (fun y => f y * g y) x := by
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ =>
    (contDiffAt_pi.1 (contDiffAt_pi.1 hf i) k).mul (contDiffAt_pi.1 (contDiffAt_pi.1 hg k) j)

open Classical in
omit [NumberField E] [IsTotallyComplex E] in

def uOf (x : Lie E n) : GL (Fin n) (Cinf E) := if h : IsUnit (Matrix.of x) then h.unit else 1

omit [NumberField E] [IsTotallyComplex E] in
theorem uOf_val {x : Lie E n} (hx : x ∈ invSet E n) : (uOf x).val = Matrix.of x := by
  have h : IsUnit (Matrix.of x) := hx
  rw [uOf, dif_pos h]
  rfl

theorem chart_eq {φ : GA E n → ℂ} {g : GA E n} {x : Lie E n} (hx : x ∈ invSet E n) :
    chart φ g x = φ (g * infGL E n (uOf x)) := by
  have h : IsUnit (Matrix.of x) := hx
  rw [chart, dif_pos h, uOf, dif_pos h]

omit [IsTotallyComplex E] in
theorem continuousOn_uOf : ContinuousOn (uOf (E := E) (n := n)) (invSet E n) := by
  rw [continuousOn_iff_continuous_domRestrict]
  show Continuous fun x : invSet E n => uOf x.1
  have hv : Continuous fun x : invSet E n => (Matrix.of x.1 : Matrix (Fin n) (Fin n) (Cinf E)) :=
    continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have e : (Units.val ∘ fun x : invSet E n => uOf x.1) = fun x => Matrix.of x.1 :=
      funext fun x => uOf_val x.2
    rw [e]
    exact hv
  · have e : (fun x : invSet E n => ((uOf x.1)⁻¹ : GL (Fin n) (Cinf E)).val) =
        fun x => Ring.inverse (Matrix.of x.1).det • (Matrix.of x.1).adjugate := funext fun x => by
      rw [Matrix.coe_units_inv, uOf_val x.2, Matrix.inv_def]
    rw [e]
    refine Continuous.smul (M := Cinf E) ?_ (Continuous.matrix_adjugate hv)
    refine continuous_iff_continuousAt.2 fun x => ?_
    have hu : IsUnit (Matrix.of x.1).det := (Matrix.isUnit_iff_isUnit_det _).1 x.2
    exact ContinuousAt.comp (f := fun x : invSet E n => (Matrix.of x.1).det) (g := Ring.inverse)
      (NormedRing.inverse_continuousAt (R := Cinf E) hu.unit) (Continuous.matrix_det hv).continuousAt

theorem xv_eq {x : Lie E n} (hx : x ∈ invSet E n) (v : InfinitePlace E) :
    (gI v (infGL E n (uOf x))).val = xv v x := by
  rw [gI_infGL_val, uOf_val hx]
  rfl

theorem xv_mem {x : Lie E n} (hx : x ∈ invSet E n) (v : InfinitePlace E) : xv v x ∈ GLs n := by
  rw [← xv_eq hx v]
  exact val_mem_GLs₀ _

omit [NumberField E] [IsTotallyComplex E] in
theorem inv_mul_mem {A B : Mat n} (hA : A ∈ GLs n) (hB : B ∈ GLs n) : A⁻¹ * B ∈ GLs n := by
  show (A⁻¹ * B).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (inv_ne_zero hA) hB

def kerQ (κ : InfinitePlace E → Mat n → ℂ) (q : Lie E n × ((InfinitePlace E → Mat n) × ℂ)) : ℂ :=
  (∏ v, κ v ((xv v q.1)⁻¹ * q.2.1 v)) * q.2.2

def Wset (E : Type) [Field E] [NumberField E] (n : ℕ) : Set ((InfinitePlace E → Mat n) × ℂ) :=
  (Set.univ.pi fun _ => GLs n) ×ˢ Set.univ

omit [IsTotallyComplex E] in
theorem isOpen_Wset : IsOpen (Wset E n) :=
  (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_GLs₀).prod isOpen_univ

theorem contDiffOn_kerQ {κ : InfinitePlace E → Mat n → ℂ} (hκ : ∀ v, ContDiffOn ℝ ∞ (κ v) (GLs n)) :
    ContDiffOn ℝ ∞ (kerQ κ) (invSet E n ×ˢ Wset E n) := by
  rintro ⟨x, m, b⟩ ⟨hx, hm, -⟩
  refine ContDiffAt.contDiffWithinAt ?_
  refine (contDiffAt_prod fun v _ => ?_).mul (contDiff_snd.comp contDiff_snd).contDiffAt
  have hinv : ContDiffAt ℝ ∞ (fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => (xv v q.1)⁻¹) (x, m, b) :=
    ContDiffAt.comp (g := fun A : Mat n => A⁻¹) (f := fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => xv v q.1)
      (x, m, b) (GlobalTheory.CompanionTheory.WaveCp.Rep.Frame.contDiffOn_inv_real.contDiffAt (isOpen_GLs₀.mem_nhds (xv_mem hx v)))
      ((contDiff_xv v).comp contDiff_fst).contDiffAt
  have hmv : ContDiffAt ℝ ∞ (fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => q.2.1 v) (x, m, b) :=
    ((contDiff_apply ℝ (Mat n) v).comp (contDiff_fst.comp contDiff_snd)).contDiffAt
  exact ContDiffAt.comp (g := κ v)
    (f := fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => (xv v q.1)⁻¹ * q.2.1 v) (x, m, b)
    ((hκ v).contDiffAt (isOpen_GLs₀.mem_nhds (inv_mul_mem (xv_mem hx v) (hm v trivial))))
    (contDiffAt_matMul (f := fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => (xv v q.1)⁻¹)
      (g := fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => q.2.1 v) hinv hmv)

variable {T : Type} [TopologicalSpace T] [Group T] [IsTopologicalGroup T] [T2Space T] [MeasurableSpace T]
  [BorelSpace T]

theorem mem_Sm_conv (μ : Measure T) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (ι : GA E n →* T) (hι : Continuous ι) (ρ : T → GA E n) (hρ : Continuous ρ)
    (hρι : ∀ h w, ρ (ι h * w) = h * ρ w)
    (κ : InfinitePlace E → Mat n → ℂ) (hκ : ∀ v, ContDiffOn ℝ ∞ (κ v) (GLs n))
    (C : T → ℂ) (hC : Continuous C) (hCι : ∀ u w, C (ι (infGL E n u) * w) = C w)
    (F : T → ℂ) (hF : Continuous F) (Φ : T → ℂ) (hΦ : ∀ w, Φ w = (∏ v, κ v (gI v (ρ w)).val) * C w)
    (hΦc : HasCompactSupport Φ) (t₀ : T) :
    (fun x' => ∫ y, Φ y * F (t₀ * ι x' * y) ∂μ) ∈ Sm E n := by
  refine fun g => ?_
  let p : T → (InfinitePlace E → Mat n) × ℂ := fun y =>
    (fun v => (gI v (ρ ((t₀ * ι g)⁻¹ * y))).val, C ((t₀ * ι g)⁻¹ * y) * F y)
  have hp : Continuous p := by
    have hl : Continuous fun y : T => (t₀ * ι g)⁻¹ * y := continuous_const.mul continuous_id
    exact (continuous_pi fun v => Units.continuous_val.comp ((continuous_gI v).comp (hρ.comp hl))).prodMk
      ((hC.comp hl).mul hF)
  have hpW : ∀ y, p y ∈ Wset E n := fun y => ⟨fun v _ => val_mem_GLs₀ _, trivial⟩
  have key : ∀ x ∈ invSet E n, ∀ y,
      kerQ κ (x, p y) = Φ ((ι (infGL E n (uOf x)))⁻¹ * ((t₀ * ι g)⁻¹ * y)) * F y := by
    intro x hx y
    rw [hΦ, ← map_inv ι, ← map_inv (infGL E n), hρι, hCι, mul_assoc]
    show (∏ v, κ v ((xv v x)⁻¹ * (gI v (ρ ((t₀ * ι g)⁻¹ * y))).val)) * (C ((t₀ * ι g)⁻¹ * y) * F y) = _
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul, map_inv, map_inv, Units.val_mul, Matrix.coe_units_inv, xv_eq hx v]
  have hsupp : ∀ x ∈ invSet E n, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, kerQ κ (x', p y) = 0 := by
    intro x₀ hx₀
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_invSet x₀ hx₀
    have hS : closedBall x₀ (r / 2) ⊆ invSet E n := (closedBall_subset_ball (half_lt_self hr)).trans hrU
    let L : Lie E n × T → T := fun q => t₀ * ι g * ι (infGL E n (uOf q.1)) * q.2
    refine ⟨L '' (closedBall x₀ (r / 2) ×ˢ tsupport Φ),
      ((isCompact_closedBall x₀ (r / 2)).prod hΦc).image_of_continuousOn ?_, ?_⟩
    · have hu : ContinuousOn (fun q : Lie E n × T => ι (infGL E n (uOf q.1))) (closedBall x₀ (r / 2) ×ˢ tsupport Φ) :=
        (hι.comp continuous_infGL₀).comp_continuousOn
          (continuousOn_uOf.comp continuous_fst.continuousOn fun q hq => hS hq.1)
      exact (continuousOn_const.mul hu).mul continuous_snd.continuousOn
    · filter_upwards [closedBall_mem_nhds x₀ (half_pos hr)] with x' hx' y hy
      rw [key x' (hS hx') y]
      have hw : (ι (infGL E n (uOf x')))⁻¹ * ((t₀ * ι g)⁻¹ * y) ∉ tsupport Φ := by
        intro hw
        apply hy
        refine ⟨(x', _), ⟨hx', hw⟩, ?_⟩
        simp only [L, mul_assoc, mul_inv_rev, mul_inv_cancel_left]
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
  refine (contDiffOn_integral (μ := μ) isOpen_invSet isOpen_Wset hp hpW (contDiffOn_kerQ hκ) hsupp).congr ?_
  intro x hx
  rw [chart_eq hx]
  have h2 := integral_mul_left_eq_self (μ := μ)
    (fun y => Φ ((t₀ * ι (g * infGL E n (uOf x)))⁻¹ * y) * F y) (t₀ * ι (g * infGL E n (uOf x)))
  simp only [inv_mul_cancel_left] at h2
  rw [h2]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  beta_reduce
  rw [key x hx y]
  simp only [map_mul, mul_inv_rev, mul_assoc]

end PositivityTheory.Rg.BcB.CG.SmoothIntegrals

end
end

section
noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped ContDiff Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace SmoothIntegrals

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def entL (M : KMod n) (i j : Ix M) : (M.V →L[ℂ] M.V) →L[ℝ] ℂ :=
  ((innerSL ℂ (stdOrthonormalBasis ℂ M.V i)).comp
    (ContinuousLinearMap.apply ℂ M.V (stdOrthonormalBasis ℂ M.V j))).restrictScalars ℝ

theorem mult_contDiffOn [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) : ContDiffOn ℝ ∞ k (GLs n) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  exact (ContDiffOn.sum fun i _ => ((hks i).2.1).const_smul (c i)).congr fun y hy => hk y hy

theorem ent_contDiffOn [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) (i j : Ix M) :
    ContDiffOn ℝ ∞ (fun A => ent M (k A) i j) (GLs n) :=
  (entL M i j).contDiff.comp_contDiffOn (mult_contDiffOn h)

theorem continuous_entA [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (h : IsMults μ k val T) (I J : IxA M) :
    Continuous fun g : GA E n => entA k I J g :=
  continuous_finsetProd _ fun v _ => (entL (M v) (I v) (J v)).continuous.comp
    ((mult_contDiffOn (h v)).continuousOn.comp_continuous (Units.continuous_val.comp (continuous_gI v))
      fun _ => val_mem_GLs₀ _)

omit [IsCMField E] in
theorem continuous_gFin₀ : Continuous (gFin : GA E n → GL (Fin n) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_snd)

theorem continuous_hFin₀ {a b : ℕ} : Continuous (hFin : H E a b → Hf E a b) :=
  (continuous_gFin₀.comp continuous_fst).prodMk (continuous_gFin₀.comp continuous_snd)

theorem gFin_infGL₀ (u : GL (Fin n) (Cinf E)) : gFin (infGL E n u) = 1 := pFin_infGL u

end SmoothIntegrals

open SmoothIntegrals in

theorem smoothOf (hTT : TensTest) : SmoothOf := by
  intro E _ _ _ a b _ _ _ _ μa _ μb _ Ma Mb ι _ D ka kb va vb T ψ U f hka hkb hψ _ _ hR
  have : BorelSpace (H E a b) := ⟨rfl⟩
  have : D.μ.IsMulLeftInvariant := D.haar.1
  have : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  have : IsFiniteMeasureOnCompacts D.μ := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  obtain ⟨hfc, c, hc, hconv⟩ := hR
  have hTest := (hTT E a b μa μb Ma Mb ι ka kb va vb T ψ hka hkb hψ).1
  have hψc : ∀ x y, Continuous fun w : H E a b => ψ x y (hFin w) := fun x y => (hψ x y).1.comp continuous_hFin₀

  have hrep : ∀ i z, f i z = c⁻¹ * ∑ j, ∫ y, tens ka kb ψ i j y * f j (z * y) ∂D.μ := by
    intro i z
    have h1 := congrFun (congrFun hconv i) z
    have h2 : c * f i z = ∑ j, ∫ y, tens ka kb ψ i j y * f j (z * y) ∂D.μ := h1.symm
    rw [← h2, inv_mul_cancel_left₀ hc]
  refine ⟨fun i m₂ => ?_, fun i m₁ => ?_⟩
  · have hj : ∀ j, (fun x => ∫ y, tens ka kb ψ i j y * f j ((x, m₂) * y) ∂D.μ) ∈ Sm E a := by
      intro j
      have h := mem_Sm_conv D.μ (MonoidHom.inl (GA E a) (GA E b)) (continuous_id.prodMk continuous_const) Prod.fst
        continuous_fst (fun h w => by simp) (fun v A => ent (Ma v) (ka v A) (i.1.1 v) (j.1.1 v))
        (fun v => ent_contDiffOn (hka v) _ _) (fun w => entA kb i.1.2 j.1.2 w.2 * ψ i.2 j.2 (hFin w))
        (((continuous_entA hkb _ _).comp continuous_snd).mul (hψc _ _))
        (fun _ w => by simp [hFin, gFin_infGL₀]) (f j) (hfc j) (tens ka kb ψ i j) (fun w => mul_assoc _ _ _)
        (hTest i j).2 ((1 : GA E a), m₂)
      have e : ∀ x : GA E a, ((1 : GA E a), m₂) * MonoidHom.inl (GA E a) (GA E b) x = (x, m₂) := fun x =>
        Prod.ext (one_mul x) (mul_one m₂)
      simpa only [e] using h
    refine ⟨⟨c⁻¹ • ∑ j, fun x => ∫ y, tens ka kb ψ i j y * f j ((x, m₂) * y) ∂D.μ,
      (Sm E a).smul_mem c⁻¹ ((Sm E a).sum_mem fun j _ => hj j)⟩, ?_⟩
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (hrep i (x, m₂)).symm
  · have hj : ∀ j, (fun x => ∫ y, tens ka kb ψ i j y * f j ((m₁, x) * y) ∂D.μ) ∈ Sm E b := by
      intro j
      have h := mem_Sm_conv D.μ (MonoidHom.inr (GA E a) (GA E b)) (continuous_const.prodMk continuous_id) Prod.snd
        continuous_snd (fun h w => by simp) (fun v A => ent (Mb v) (kb v A) (i.1.2 v) (j.1.2 v))
        (fun v => ent_contDiffOn (hkb v) _ _) (fun w => entA ka i.1.1 j.1.1 w.1 * ψ i.2 j.2 (hFin w))
        (((continuous_entA hka _ _).comp continuous_fst).mul (hψc _ _))
        (fun _ w => by simp [hFin, gFin_infGL₀]) (f j) (hfc j) (tens ka kb ψ i j)
        (fun w => by
          show entA ka _ _ w.1 * entA kb _ _ w.2 * ψ _ _ (hFin w) = entA kb _ _ w.2 * (entA ka _ _ w.1 * ψ _ _ (hFin w))
          ring)
        (hTest i j).2 (m₁, (1 : GA E b))
      have e : ∀ x : GA E b, (m₁, (1 : GA E b)) * MonoidHom.inr (GA E a) (GA E b) x = (m₁, x) := fun x =>
        Prod.ext (mul_one m₁) (one_mul x)
      simpa only [e] using h
    refine ⟨⟨c⁻¹ • ∑ j, fun x => ∫ y, tens ka kb ψ i j y * f j ((m₁, x) * y) ∂D.μ,
      (Sm E b).smul_mem c⁻¹ ((Sm E b).sum_mem fun j _ => hj j)⟩, ?_⟩
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (hrep i (m₁, x)).symm

end PositivityTheory.Rg.BcB.CG

end
end

section
noncomputable section

open Polynomial Finset NumberField GlobalTheory.CuspRep
open PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.CG.InfiniteConvergence

namespace PositivityTheory.Rg.BcB.CG

namespace HeckeFubiniEvaluationDefect

theorem eval_sS (t : ℕ → ℂ) (m N : ℕ) : (sS t m N).eval (m : ℂ) = (-1) ^ N * t N := by
  rw [sS, sum_range_succ, eval_add, eval_finset_sum, sum_eq_zero]
  · simp
  · intro k hk
    have := mem_range.mp hk
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
    rw [zero_pow (by omega), mul_zero]

theorem eq_of_defect (m : ℕ) (t t' : ℕ → ℂ) (Q : ℂ[X]) (hQ : Q.natDegree = m + 1)
    (h : ∀ N, (defect t m N Q).natDegree ≤ m) (h' : ∀ N, (defect t' m N Q).natDegree ≤ m) (k : ℕ) : t k = t' k := by
  have hQ0 : Q ≠ 0 := by intro e; rw [e, natDegree_zero] at hQ; omega
  have hS : sS t m k = sS t' m k := by
    have e : defect t m k Q - defect t' m k Q = Q * (sS t' m k - sS t m k) := by
      simp only [defect_eq]; ring
    by_contra hne
    have hD : sS t' m k - sS t m k ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 : (Q * (sS t' m k - sS t m k)).natDegree ≤ m := by
      rw [← e]; exact (natDegree_sub_le _ _).trans (max_le (h k) (h' k))
    rw [natDegree_mul hQ0 hD, hQ] at h1
    omega
  have e := congrArg (fun p => p.eval (m : ℂ)) hS
  simp only [eval_sS] at e
  have hu : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hu e

theorem exists_enum (s : Multiset ℂ) : ∀ n, Multiset.card s = n → ∃ r : Fin n → ℂ, Multiset.map r univ.val = s := by
  induction s using Multiset.induction_on with
  | empty =>
    intro n hn
    simp only [Multiset.card_zero] at hn
    subst hn
    exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    intro n hn
    rw [Multiset.card_cons] at hn
    subst hn
    obtain ⟨r, hr⟩ := ih _ rfl
    refine ⟨Fin.cons a r, ?_⟩
    conv_rhs => rw [← hr]
    simp [Fin.univ_succ, Multiset.map_map, Function.comp_def]

theorem exists_gelf (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (M : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
    (hM : Formalism.REAL.GlRel M) (v : V) (hv : v ≠ 0) (t : ℕ → ℂ) (ht : ∀ k, Formalism.REAL.etr M k v = t k • v) :
    ∃ χ : Fin (m + 1) → ℂ, ∀ k, GlobalTheory.Dec.gelfVal χ k = t k := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp hc)
  set f : Module.Dual ℂ V := (f₀ v)⁻¹ • f₀ with hfd
  have hf : f v = 1 := by
    rw [hfd, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) M
  set Q := GlobalTheory.CapelliNewton.polyOf (m + 1) c f v with hQd
  have hQ : ∀ u : ℂ, Q.eval u = f (Formalism.REAL.qdet M u v) := fun u => by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_eval, hc]
  have hQc : Q.coeff (m + 1) = 1 := by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_coeff, hc1]
    exact hf
  have hQn : Q.natDegree = m + 1 :=
    le_antisymm (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _)
      (le_natDegree_of_ne_zero (by rw [hQc]; exact one_ne_zero))
  have hQm : Q.Monic := by
    rw [Monic, leadingCoeff, hQn, hQc]
  have hcard : Multiset.card Q.roots = m + 1 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hQn]
  have hprod : (Q.roots.map fun a => X - Polynomial.C a).prod = Q :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm (by rw [hcard, hQn])
  obtain ⟨r, hr⟩ := exists_enum Q.roots (m + 1) hcard
  refine ⟨fun s => (m : ℂ) / 2 - r s, fun k => ?_⟩
  have hcq : (∏ s, (X + Polynomial.C ((m : ℂ) / 2 - r s - (m : ℂ) / 2))) = Q := by
    conv_rhs => rw [← hprod, ← hr]
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun s _ => ?_
    simp only [Function.comp_apply, map_sub]
    ring
  have h1 : ∀ N, (defect (GlobalTheory.Dec.gelfVal fun s => (m : ℂ) / 2 - r s) m N Q).natDegree ≤ m := by
    intro N
    have := natDegree_defect_gelf m (fun s => (m : ℂ) / 2 - r s) N
    rwa [hcq] at this
  have h2 : ∀ N, (defect t m N Q).natDegree ≤ m := fun N =>
    natDegree_defect_op V m M hM v t ht f Q hQ N
  exact eq_of_defect m _ t Q hQn h1 h2 k

theorem one_mem_GLs' {a : ℕ} : (1 : Matrix (Fin a) (Fin a) ℂ) ∈ PositivityTheory.RgBcC.GLs a := by
  simp [PositivityTheory.RgBcC.GLs]

end HeckeFubiniEvaluationDefect

open HeckeFubiniEvaluationDefect in
theorem infEx : InfEx := by
  intro E _ _ _ n S v t ⟨φ, hφS, hφ0⟩ h
  have hs : ∀ s k, Formalism.REAL.etr (eopW v s) k φ = t s k • φ := by
    intro s k
    apply Subtype.ext
    funext g
    have h1 := h φ hφS g s k 1 one_mem_GLs'
    rw [gel_along v g s k φ one_mem_GLs', along_one, along_one] at h1
    rw [Submodule.coe_smul, Pi.smul_apply]
    exact h1
  rcases n with _ | m
  · refine ⟨fun _ => Fin.elim0, fun s k => ?_⟩
    have ht0 : t s k = 0 := by
      have e : t s k • φ = 0 := by rw [← hs s k]; simp [Formalism.REAL.etr]
      exact (smul_eq_zero.mp e).resolve_right hφ0
    rw [ht0]
    simp [GlobalTheory.Dec.gelfVal]
  · have hgl : ∀ s, Formalism.REAL.GlRel (eopW (E := E) (a := m + 1) v s) := by
      intro s
      unfold eopW
      split <;> exact glRel_Eop _
    choose χ hχ using fun s => exists_gelf (Sm E (m + 1)) m (eopW v s) (hgl s) φ hφ0 (t s) (hs s)
    exact ⟨χ, fun s k => hχ s k⟩

end PositivityTheory.Rg.BcB.CG

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH HeckeM heckeAct)
open scoped Classical

namespace PositivityTheory.Rg.BcB.CG

theorem finH_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

theorem finHecke : FinHecke := by
  intro E _ _ _ a b _ _ ν _ A κ _ _ ψ U hψ hUo hUc hψU

  set K : Set (Hf E a b) := ⋃ x, ⋃ y, tsupport (ψ x y) with hK
  have hKc : IsCompact K := isCompact_iUnion fun x => isCompact_iUnion fun y => (hψ x y).2

  let C : Hf E a b ⧸ U → Set (Hf E a b) := fun q => (fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))
  have hCmem : ∀ q h, h ∈ C q ↔ (QuotientGroup.mk h : Hf E a b ⧸ U) = q := by
    intro q h
    show q.out⁻¹ * h ∈ U ↔ _
    rw [← QuotientGroup.eq]
    simp only [Quotient.out_eq]
    exact eq_comm
  have hCo : ∀ q, IsOpen (C q) := fun q => hUo.preimage (continuous_const.mul continuous_id)
  have hCm : ∀ q, MeasurableSet (C q) := fun q => (hCo q).measurableSet
  have hCf : ∀ q, ν (C q) ≠ ⊤ := by
    intro q
    show ν ((fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))) ≠ ⊤
    rw [measure_preimage_mul]
    exact hUc.measure_lt_top.ne
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover C hCo (by
    intro h _
    exact Set.mem_iUnion.2 ⟨QuotientGroup.mk h, (hCmem _ h).2 rfl⟩)
  have hin : ∀ h, (∀ x y, ψ x y h ≠ 0 → (QuotientGroup.mk h : Hf E a b ⧸ U) ∈ t) := by
    intro h x y hne
    have hhK : h ∈ K := Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, subset_tsupport _ hne⟩⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 (ht hhK)
    obtain ⟨hqt, hq⟩ := Set.mem_iUnion.1 hq
    rwa [(hCmem q h).1 hq]
  refine ⟨fun i j => if i.1 = j.1 then ∑ q ∈ t, Finsupp.single q.out ((ν (C q)).toReal * ψ i.2 j.2 q.out) else 0,
    ?_, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · intro p q x y
    simp
  · intro f hf
    funext i X
    simp only [convF, heckeAct]
    rw [Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single i.1 (fun p _ hp => by
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [if_neg (Ne.symm hp)]
      simp) (by simp)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [if_true]
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by ring)]
    set Φ : Hf E a b → ℂ := fun h => ψ i.2 z h * f (i.1, z) (X * finH h) with hΦ
    have hΦU : ∀ h, ∀ u ∈ U, Φ (h * u) = Φ h := by
      intro h u hu
      simp only [hΦ]
      rw [finH_mul, ← mul_assoc, hf _ u hu, hψU _ _ u hu h]
    have hΦout : ∀ h, Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out = Φ h := by
      intro h
      have h1 : ((QuotientGroup.mk h : Hf E a b ⧸ U).out)⁻¹ * h ∈ U := (hCmem _ h).2 rfl
      calc Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out
          = Φ ((QuotientGroup.mk h : Hf E a b ⧸ U).out * ((QuotientGroup.mk h : Hf E a b ⧸ U).out⁻¹ * h)) :=
            (hΦU _ _ h1).symm
        _ = Φ h := by rw [mul_inv_cancel_left]
    have hpt : Φ = fun h => ∑ q ∈ t, (C q).indicator (fun _ => Φ q.out) h := by
      funext h
      rw [Finset.sum_eq_single (QuotientGroup.mk h : Hf E a b ⧸ U)]
      · rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
      · intro q _ hq
        rw [Set.indicator_of_notMem]
        intro hc
        exact hq ((hCmem q h).1 hc).symm
      · intro hmem
        rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
        by_contra hne
        apply hmem
        refine hin h i.2 z ?_
        intro h0
        apply hne
        simp only [hΦ, h0, zero_mul]
    rw [hpt, integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hCm q), Finsupp.sum_single_index (by simp)]
      simp only [hΦ, Complex.real_smul, Measure.real]
      ring
    · intro q _
      exact (integrable_indicator_iff (hCm q)).2 (integrableOn_const (hCf q))

end PositivityTheory.Rg.BcB.CG

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH)
open PositivityTheory.RgBcC.Bridge (along BridgeSt)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG.PAut

section Eig

variable {n : ℕ}

theorem rd_smul (c : ℂ) (X : Mat n) (F : Mat n → ℂ) : Rd X (c • F) = c • Rd X F := by
  funext g
  have e : fderiv ℝ (c • F) = c • fderiv ℝ F := fderiv_const_smul_field c
  simp only [Rd, e, Pi.smul_apply]
  rfl

theorem eu_smul (c : ℂ) (s : Bool) (i j : Fin n) (F : Mat n → ℂ) : Eu s i j (c • F) = c • Eu s i j F := by
  simp only [Eu, rd_smul]
  module

theorem epow_smul (c : ℂ) (s : Bool) (m : ℕ) (i j : Fin n) (F : Mat n → ℂ) :
    Epow s m i j (c • F) = c • Epow s m i j F := by
  induction m generalizing i j with
  | zero =>
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    simp only [Epow, ih, eu_smul, Finset.smul_sum]

theorem gel_smul' (c : ℂ) (s : Bool) (m : ℕ) (F : Mat n → ℂ) : gel s m (c • F) = c • gel s m F := by
  simp only [gel, epow_smul, Finset.smul_sum]

theorem isEig_smul {χ : Inf n} {F : Mat n → ℂ} (h : IsEig χ F) (c : ℂ) : IsEig χ (c • F) := by
  intro s m g hg
  rw [gel_smul', Pi.smul_apply, h s m g hg, Pi.smul_apply]
  exact smul_comm _ _ _

end Eig

section Tc

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem along_smul' (w : InfinitePlace E) (g : GA E a) (c : ℂ) (φ : GA E a → ℂ) :
    along w g (c • φ) = c • along w g φ := by
  funext x
  simp only [along, chart, Pi.smul_apply]
  split_ifs <;> simp

theorem zfin_of (φ : Sm E a) (c : (E →+* ℂ) → ℂ → ℂ) (hc : ∀ τ u, cap τ u φ = c τ u • φ) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' (Zalg E a : Set _))) := by
  have : FiniteDimensional ℂ (Submodule.span ℂ {φ}) := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton φ)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨s, hs⟩ := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
  show z φ ∈ _
  rw [hs φ hc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self φ)

theorem kfin_of (φ : Sm E a) (W : Submodule ℂ (Kinf E a → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ z, (fun k : Kinf E a => φ.1 (z * infGL E a (Unitary.toUnits k))) ∈ W) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := by
  let Λ : Module.Dual ℂ W →ₗ[ℂ] (GA E a → ℂ) :=
    { toFun := fun l z => l ⟨_, hW z⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (Sm E a).subtype ≤ LinearMap.range Λ := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨(LinearMap.proj k).comp W.subtype, ?_⟩
    funext z
    rfl
  have := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective (Sm E a).subtype Subtype.val_injective _).symm

theorem level_of (φ : Sm E a) (K : Subgroup (GL (Fin a) (Af E))) (hK : IsOpen (K : Set (GL (Fin a) (Af E))))
    (h : ∀ u ∈ K, ∀ z, φ.1 (z * finGL E a u) = φ.1 z) : IsOpen {k | finRep E a k φ = φ} := by
  have hu : ∀ u ∈ K, finRep E a u φ = φ := fun u hu => Subtype.ext (funext fun z => h u hu z)
  rw [isOpen_iff_forall_mem_open]
  intro k hk
  have hk' : finRep E a k φ = φ := hk
  refine ⟨(fun u => k * u) '' (K : Set (GL (Fin a) (Af E))), ?_, isOpenMap_mul_left k _ hK, ⟨1, K.one_mem, mul_one k⟩⟩
  rintro _ ⟨u, hu', rfl⟩
  change finRep E a (k * u) φ = φ
  rw [map_mul, Module.End.mul_apply, hu u hu', hk']

def infP (A : Matrix (Fin a) (Fin a) (Ad E)) : ℝ :=
  ∑ v, Real.posLog (⨆ p : Fin a × Fin a, ‖cV v (A p.1 p.2)‖ ^ 2)

def finP (A : Matrix (Fin a) (Fin a) (Ad E)) : ℝ :=
  ∑ᶠ w, Real.posLog (⨆ p : Fin a × Fin a, ‖cW w (A p.1 p.2)‖)

theorem logSizeM_eq (A : Matrix (Fin a) (Fin a) (Ad E)) : logSizeM A = infP A + finP A := rfl

theorem logSizeM_nonneg (A : Matrix (Fin a) (Fin a) (Ad E)) : 0 ≤ logSizeM A := by
  rw [logSizeM_eq]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem logSize_nonneg (x : GA E a) : 0 ≤ logSize x :=
  add_nonneg (logSizeM_nonneg _) (logSizeM_nonneg _)

theorem infinitePart_le (A : Matrix (Fin a) (Fin a) (Ad E)) (B : ℝ) (hB : 1 ≤ B) (h : ∀ v i j, ‖cV v (A i j)‖ ≤ B) :
    infP A ≤ Fintype.card (InfinitePlace E) * (2 * Real.log B) := by
  have key : ∀ v, Real.posLog (⨆ p : Fin a × Fin a, ‖cV v (A p.1 p.2)‖ ^ 2) ≤ 2 * Real.log B := by
    intro v
    have h0 : 0 ≤ ⨆ p : Fin a × Fin a, ‖cV v (A p.1 p.2)‖ ^ 2 := Real.iSup_nonneg fun p => sq_nonneg _
    have hle : (⨆ p : Fin a × Fin a, ‖cV v (A p.1 p.2)‖ ^ 2) ≤ B ^ 2 :=
      Real.iSup_le (fun p => pow_le_pow_left₀ (norm_nonneg _) (h v p.1 p.2) 2) (sq_nonneg _)
    have hB2 : 1 ≤ |B ^ 2| := by
      rw [abs_of_nonneg (sq_nonneg B)]
      nlinarith
    calc _ ≤ Real.posLog (B ^ 2) := Real.monotoneOn_posLog h0 (sq_nonneg B) hle
      _ = Real.log (B ^ 2) := Real.posLog_eq_log hB2
      _ = 2 * Real.log B := by rw [Real.log_pow]; norm_num
  calc infP A ≤ ∑ _v : InfinitePlace E, 2 * Real.log B := Finset.sum_le_sum fun v _ => key v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem cV_mul (v : InfinitePlace E) (A B : Matrix (Fin a) (Fin a) (Ad E)) (i j : Fin a) :
    cV v ((A * B) i j) = ∑ k, cV v (A i k) * cV v (B k j) := by
  rw [Matrix.mul_apply, map_sum]
  simp only [map_mul]

theorem cV_infGL (v : InfinitePlace E) (y : GL (Fin a) (Cinf E)) (k j : Fin a) :
    cV v ((infGL E a y).val k j) = y.val k j v := by
  have e := congrArg (fun h : GL (Fin a) (Cinf E) => h.val k j v) (pInf_infGL (E := E) y)
  exact e

theorem pFin_mul_infGL (g : GA E a) (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    pFin E ((g * infGL E a y).val i j) = pFin E (g.val i j) := by
  have e : GeneralLinearGroup.map (pFin E) (g * infGL E a y) = GeneralLinearGroup.map (pFin E) g := by
    rw [map_mul, pFin_infGL, mul_one]
  exact congrArg (fun h : GL (Fin a) (Af E) => h.val i j) e

theorem pFin_inv_mul_infGL (g : GA E a) (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    pFin E (((g * infGL E a y)⁻¹).val i j) = pFin E ((g⁻¹).val i j) := by
  have e : GeneralLinearGroup.map (pFin E) (g * infGL E a y)⁻¹ = GeneralLinearGroup.map (pFin E) g⁻¹ := by
    rw [map_inv, map_mul, pFin_infGL, mul_one, ← map_inv]
  exact congrArg (fun h : GL (Fin a) (Af E) => h.val i j) e

theorem finP_mul_infGL (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    finP (g * infGL E a y).val = finP g.val := by
  unfold finP
  refine finsum_congr fun w => ?_
  congr 2
  funext p
  simp only [cW, RingHom.comp_apply]
  rw [pFin_mul_infGL]

theorem finP_inv_mul_infGL (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    finP ((g * infGL E a y)⁻¹).val = finP (g⁻¹).val := by
  unfold finP
  refine finsum_congr fun w => ?_
  congr 2
  funext p
  simp only [cW, RingHom.comp_apply]
  rw [pFin_inv_mul_infGL]

theorem logSize_mul_infGL (g : GA E a) : ∃ D : ℝ, ∀ y : GL (Fin a) (Cinf E),
    logSize (g * infGL E a y) ≤ D + 4 * Fintype.card (InfinitePlace E) * Real.log (height y) := by
  let M : InfinitePlace E → Fin a → Fin a → ℝ := fun v i k => ‖cV v (g.val i k)‖ + ‖cV v ((g⁻¹).val i k)‖
  have hM0 : ∀ v i k, 0 ≤ M v i k := fun v i k => add_nonneg (norm_nonneg _) (norm_nonneg _)
  let T : ℝ := ∑ v, ∑ i, ∑ k, M v i k
  have hT0 : 0 ≤ T :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hM0 v i k
  have hrow0 : ∀ v, ∑ i, ∑ k, M v i k ≤ T := fun v =>
    Finset.single_le_sum (f := fun v => ∑ i, ∑ k, M v i k)
      (fun v _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hM0 v i k) (Finset.mem_univ v)
  have hrow : ∀ v i, ∑ k, M v i k ≤ T := fun v i =>
    (Finset.single_le_sum (f := fun i => ∑ k, M v i k) (fun i _ => Finset.sum_nonneg fun k _ => hM0 v i k)
      (Finset.mem_univ i)).trans (hrow0 v)
  have hcol : ∀ v j, ∑ k, M v k j ≤ T := fun v j =>
    (Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := fun j => M v k j) (fun j _ => hM0 v k j)
      (Finset.mem_univ j)).trans (hrow0 v)
  refine ⟨finP g.val + finP (g⁻¹).val + 4 * Fintype.card (InfinitePlace E) * Real.log (1 + T), fun y => ?_⟩
  have h1 : 1 ≤ height y := one_le_height y
  have hB : 1 ≤ (1 + T) * height y := one_le_mul_of_one_le_of_one_le (by linarith) h1
  have hlogB : Real.log ((1 + T) * height y) = Real.log (1 + T) + Real.log (height y) :=
    Real.log_mul (by linarith) (by linarith)
  have e1 : ∀ v i j, ‖cV v ((g * infGL E a y).val i j)‖ ≤ (1 + T) * height y := by
    intro v i j
    rw [Units.val_mul, cV_mul]
    calc ‖∑ k, cV v (g.val i k) * cV v ((infGL E a y).val k j)‖
        ≤ ∑ k, ‖cV v (g.val i k)‖ * ‖cV v ((infGL E a y).val k j)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
      _ ≤ ∑ k, M v i k * height y := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul (le_add_of_nonneg_right (norm_nonneg _)) ?_
            (norm_nonneg _) (hM0 v i k)
          rw [cV_infGL]
          exact (GlobalTheory.CompanionTheory.GrowthEntries.norm_entry_le_toL _ k j v).trans
            (GlobalTheory.CompanionTheory.GrowthEntries.norm_toL_le_height y)
      _ = (∑ k, M v i k) * height y := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + T) * height y := mul_le_mul_of_nonneg_right (by linarith [hrow v i]) (by linarith)
  have hinv : (g * infGL E a y)⁻¹ = infGL E a y⁻¹ * g⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
  have e2 : ∀ v i j, ‖cV v (((g * infGL E a y)⁻¹).val i j)‖ ≤ (1 + T) * height y := by
    intro v i j
    rw [hinv, Units.val_mul, cV_mul]
    calc ‖∑ k, cV v ((infGL E a y⁻¹).val i k) * cV v ((g⁻¹).val k j)‖
        ≤ ∑ k, ‖cV v ((infGL E a y⁻¹).val i k)‖ * ‖cV v ((g⁻¹).val k j)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
      _ ≤ ∑ k, height y * M v k j := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul ?_ (le_add_of_nonneg_left (norm_nonneg _))
            (norm_nonneg _) (by linarith)
          rw [cV_infGL]
          exact (GlobalTheory.CompanionTheory.GrowthEntries.norm_entry_le_toL _ i k v).trans
            (GlobalTheory.CompanionTheory.GrowthEntries.norm_toL_inv_le_height y)
      _ = height y * ∑ k, M v k j := (Finset.mul_sum _ _ _).symm
      _ ≤ (1 + T) * height y := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (by linarith [hcol v j]) (by linarith)
  have i1 := infinitePart_le _ _ hB e1
  have i2 := infinitePart_le _ _ hB e2
  have f1 := finP_mul_infGL g y
  have f2 := finP_inv_mul_infGL g y
  have hs : logSize (g * infGL E a y) = infP (g * infGL E a y).val + finP (g * infGL E a y).val +
      (infP ((g * infGL E a y)⁻¹).val + finP ((g * infGL E a y)⁻¹).val) := rfl
  rw [hs, f1, f2]
  rw [hlogB] at i1 i2
  nlinarith

theorem growth_of_bound (F : GA E a → ℂ) (C N L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (N * (logSize x + L))) (z : GA E a) :
    ∃ (C' : ℝ) (M : ℕ), ∀ y : GL (Fin a) (Cinf E), ‖F (z * infGL E a y)‖ ≤ C' * height y ^ M := by
  obtain ⟨D, hD⟩ := logSize_mul_infGL z
  set P : ℝ := 4 * Fintype.card (InfinitePlace E)
  refine ⟨max C 0 * Real.exp (max N 0 * (D + L)), ⌈max N 0 * P⌉₊, fun y => ?_⟩
  have h1 : 1 ≤ height y := one_le_height y
  have hs0 : 0 ≤ logSize (z * infGL E a y) + L := add_nonneg (logSize_nonneg _) hL
  have hs : logSize (z * infGL E a y) + L ≤ D + L + P * Real.log (height y) := by linarith [hD y]
  have he : Real.exp (max N 0 * (D + L + P * Real.log (height y))) =
      Real.exp (max N 0 * (D + L)) * height y ^ (max N 0 * P) := by
    rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
    congr 1
    ring
  have hr : height y ^ (max N 0 * P) ≤ height y ^ ⌈max N 0 * P⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
  calc ‖F (z * infGL E a y)‖ ≤ C * Real.exp (N * (logSize (z * infGL E a y) + L)) := hF _
    _ ≤ max C 0 * Real.exp (max N 0 * (D + L + P * Real.log (height y))) := by
        refine mul_le_mul (le_max_left _ _) ?_ (Real.exp_pos _).le (le_max_right _ _)
        refine Real.exp_le_exp.2 ?_
        calc N * (logSize (z * infGL E a y) + L) ≤ max N 0 * (logSize (z * infGL E a y) + L) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (le_max_right _ _)
    _ = max C 0 * (Real.exp (max N 0 * (D + L)) * height y ^ (max N 0 * P)) := by rw [he]
    _ ≤ max C 0 * (Real.exp (max N 0 * (D + L)) * height y ^ ⌈max N 0 * P⌉₊) := by
        gcongr
    _ = _ := by ring

end Tc

section Cm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem card_mOf (χ : InfinitePlace E → Inf a) (τ : E →+* ℂ) : Multiset.card (mOf χ τ) = a := by
  unfold mOf
  simp

theorem hasInf_single (hB : BridgeSt) (χ : InfinitePlace E → Inf a) (φ : Sm E a)
    (hφ : ∀ v g, IsEig (χ v) (along v g φ.1)) (τ : E →+* ℂ) :
    HasInfCharGL (Submodule.span ℂ {φ}) τ (mOf χ τ) := by
  classical
  have key := (hB E a (Submodule.span ℂ {φ}) (InfinitePlace.mk τ) (χ (InfinitePlace.mk τ))).1 (by
    intro ψ hψ g
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hψ
    have e : ((c • φ : Sm E a) : GA E a → ℂ) = c • (φ : GA E a → ℂ) := rfl
    rw [e, along_smul']
    exact isEig_smul (hφ _ g) c)
  by_cases h : τ = (InfinitePlace.mk τ).embedding
  · have e : mOf χ τ = Multiset.map (χ (InfinitePlace.mk τ) true) Finset.univ.val := by
      have hd : decide (τ = (InfinitePlace.mk τ).embedding) = true := decide_eq_true h
      unfold mOf
      rw [hd]
    rw [e]
    have k1 := key.1
    rwa [← h] at k1
  · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ :=
      (InfinitePlace.embedding_mk_eq τ).resolve_left fun e' => h e'.symm
    have h3 : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h2]
      exact star_star τ
    have e : mOf χ τ = Multiset.map (χ (InfinitePlace.mk τ) false) Finset.univ.val := by
      have hd : decide (τ = (InfinitePlace.mk τ).embedding) = false := decide_eq_false h
      unfold mOf
      rw [hd]
    rw [e]
    have k2 := key.2
    rwa [h3] at k2

theorem hasInf_span (S : Set (Sm E a)) (τ : E →+* ℂ) (m : Multiset ℂ) (hm : Multiset.card m = a)
    (h : ∀ φ ∈ S, HasInfCharGL (Submodule.span ℂ {φ}) τ m) : HasInfCharGL (Submodule.span ℂ S) τ m := by
  refine ⟨hm, fun u ψ hψ => ?_⟩
  induction hψ using Submodule.span_induction with
  | mem x hx => exact (h x hx).2 u x (Submodule.mem_span_singleton_self x)
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

theorem isAutForm_of (hB : BridgeSt) (φ : Sm E a) (K : Subgroup (GL (Fin a) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin a) (Af E)))) (W : Submodule ℂ (Kinf E a → ℂ)) [FiniteDimensional ℂ W]
    (χ : InfinitePlace E → Inf a) (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hk : ∀ u ∈ K, ∀ z, φ.1 (z * finGL E a u) = φ.1 z)
    (hw : ∀ z, (fun k : Kinf E a => φ.1 (z * infGL E a (Unitary.toUnits k))) ∈ W)
    (he : ∀ v g, IsEig (χ v) (along v g φ.1))
    (hg : ∀ z, ∃ (C : ℝ) (M : ℕ), ∀ y, ‖φ.1 (z * infGL E a y)‖ ≤ C * height y ^ M) : IsAutForm φ :=
  ⟨hl, level_of φ K hK hk, kfin_of φ W hw,
    zfin_of φ _ fun τ u => (hasInf_single hB χ φ he τ).2 u φ (Submodule.mem_span_singleton_self φ), hg⟩

theorem typeW₁ {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (z : GA E a) (m₂ : GA E b) :
    (fun k : Kinf E a => F (z * infGL E a (Unitary.toUnits k), m₂)) ∈ W₁ := by
  let ev : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun k : Kinf E a => (k, (1 : Kinf E b)))
  have hle : (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}).map
      ev ≤ W₁ := by
    rw [Submodule.map_span_le]
    rintro _ ⟨w₁, hw₁, w₂, -, rfl⟩
    have e : ev (fun k => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
      funext k
      simp [ev, LinearMap.funLeft_apply, mul_comm]
    rw [e]
    exact W₁.smul_mem _ hw₁
  have := hle (Submodule.mem_map_of_mem (f := ev) (hF.2 (z, m₂)))
  convert this using 1
  funext k
  simp [ev, LinearMap.funLeft_apply]

theorem typeW₂ {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (m₁ : GA E a) (z : GA E b) :
    (fun k : Kinf E b => F (m₁, z * infGL E b (Unitary.toUnits k))) ∈ W₂ := by
  let ev : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun k : Kinf E b => ((1 : Kinf E a), k))
  have hle : (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}).map
      ev ≤ W₂ := by
    rw [Submodule.map_span_le]
    rintro _ ⟨w₁, -, w₂, hw₂, rfl⟩
    have e : ev (fun k => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
      funext k
      simp [ev, LinearMap.funLeft_apply]
    rw [e]
    exact W₂.smul_mem _ hw₂
  have := hle (Submodule.mem_map_of_mem (f := ev) (hF.2 (m₁, z)))
  convert this using 1
  funext k
  simp [ev, LinearMap.funLeft_apply]

theorem slice₁_aut (hB : BridgeSt) {ι : Type} {f : ι → H E a b → ℂ}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {χa : InfinitePlace E → Inf a}
    {χb : InfinitePlace E → Inf b} {C N : ℝ} (hK₁ : IsOpen (K₁ : Set (GL (Fin a) (Af E))))
    (hW₁ : FiniteDimensional ℂ W₁) (hL : LeftInv f) (hT : ∀ i, TypeH K₁ K₂ W₁ W₂ (f i))
    (hG : ∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))) (hE : EigAll χa χb f)
    (φ : Sm E a) (i : ι) (m₂ : GA E b) (hφ : φ.1 = fun x => f i (x, m₂)) : IsAutForm φ := by
  refine isAutForm_of hB φ K₁ hK₁ W₁ χa ?_ ?_ ?_ ?_ ?_
  · intro γ g
    rw [hφ]
    have := hL i ⟨(ratGL E a γ, ratGL E b 1), ⟨(γ, 1), rfl⟩⟩ (g, m₂)
    simpa using this
  · intro u hu z
    rw [hφ]
    have := (hT i).1 u hu 1 (Subgroup.one_mem _) (z, m₂)
    simpa using this
  · intro z
    rw [hφ]
    exact typeW₁ (hT i) z m₂
  · intro v g
    rw [hφ]
    exact hE.1 i v g m₂
  · intro z
    refine growth_of_bound φ.1 C N (logSize m₂) (logSize_nonneg m₂) (fun x => ?_) z
    rw [hφ]
    exact hG i (x, m₂)

theorem slice₂_aut (hB : BridgeSt) {ι : Type} {f : ι → H E a b → ℂ}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {χa : InfinitePlace E → Inf a}
    {χb : InfinitePlace E → Inf b} {C N : ℝ} (hK₂ : IsOpen (K₂ : Set (GL (Fin b) (Af E))))
    (hW₂ : FiniteDimensional ℂ W₂) (hL : LeftInv f) (hT : ∀ i, TypeH K₁ K₂ W₁ W₂ (f i))
    (hG : ∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))) (hE : EigAll χa χb f)
    (φ : Sm E b) (i : ι) (m₁ : GA E a) (hφ : φ.1 = fun x => f i (m₁, x)) : IsAutForm φ := by
  refine isAutForm_of hB φ K₂ hK₂ W₂ χb ?_ ?_ ?_ ?_ ?_
  · intro γ g
    rw [hφ]
    have := hL i ⟨(ratGL E a 1, ratGL E b γ), ⟨(1, γ), rfl⟩⟩ (m₁, g)
    simpa using this
  · intro u hu z
    rw [hφ]
    have := (hT i).1 1 (Subgroup.one_mem _) u hu (m₁, z)
    simpa using this
  · intro z
    rw [hφ]
    exact typeW₂ (hT i) m₁ z
  · intro v g
    rw [hφ]
    exact hE.2 i v g m₁
  · intro z
    refine growth_of_bound φ.1 C N (logSize m₁) (logSize_nonneg m₁) (fun x => ?_) z
    rw [hφ, add_comm (logSize x)]
    exact hG i (m₁, x)

end Cm

theorem autOf (hB : BridgeSt) : AutOf := by
  intro E _ _ _ a b ι f K₁ K₂ W₁ W₂ χa χb C N hK₁ hK₂ hW₁ hW₂ hL hT hG hE
  refine ⟨?_, ?_, fun τ => ?_, fun τ => ?_⟩
  · rintro φ ⟨i, m₂, hφ⟩
    exact slice₁_aut hB hK₁ hW₁ hL hT hG hE φ i m₂ hφ
  · rintro φ ⟨i, m₁, hφ⟩
    exact slice₂_aut hB hK₂ hW₂ hL hT hG hE φ i m₁ hφ
  · refine hasInf_span _ τ _ (card_mOf χa τ) fun φ hφ => ?_
    obtain ⟨i, m₂, hφ⟩ := hφ
    exact hasInf_single hB χa φ (fun v g => by rw [hφ]; exact hE.1 i v g m₂) τ
  · refine hasInf_span _ τ _ (card_mOf χb τ) fun φ hφ => ?_
    obtain ⟨i, m₁, hφ⟩ := hφ
    exact hasInf_single hB χb φ (fun v g => by rw [hφ]; exact hE.2 i v g m₁) τ

end PositivityTheory.Rg.BcB.CG.PAut

end
end

section
noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG

theorem norm_cosh_le_exp (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  show ‖(Complex.exp z + Complex.exp (-z)) / 2‖ ≤ _
  have h1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))
  have h2 : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by
      have := Complex.abs_re_le_norm z
      simp only [Complex.neg_re]
      linarith [neg_abs_le z.re])
  rw [norm_div]
  have h2' : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2']
  have := norm_add_le (Complex.exp z) (Complex.exp (-z))
  linarith

theorem sqrt_sq' (c : ℂ) : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
  have h := Complex.cpow_nat_inv_pow c (n := 2) (by norm_num)
  rw [one_div]
  push_cast at h
  exact h

theorem norm_sqrt_le (c : ℂ) : ‖c ^ (1 / 2 : ℂ)‖ ≤ 1 + ‖c‖ := by
  have h : ‖c ^ (1 / 2 : ℂ)‖ ^ 2 = ‖c‖ := by rw [← norm_pow, sqrt_sq']
  nlinarith [sq_nonneg (‖c ^ (1 / 2 : ℂ)‖ - 1), norm_nonneg (c ^ (1 / 2 : ℂ))]

theorem continuous_cosh_sqrt (t : ℂ) : Continuous fun c : ℂ => Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  rw [Metric.continuous_iff]
  intro c₀ ε hε
  have hc : Continuous fun w : ℂ => Complex.cosh (t * w) :=
    Complex.continuous_cosh.comp (continuous_const.mul continuous_id)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hc (c₀ ^ (1 / 2 : ℂ)) ε hε
  refine ⟨δ ^ 2, by positivity, fun c hcc => ?_⟩
  have hprod : (c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)) * (c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)) = c - c₀ := by
    have h1 := sqrt_sq' c
    have h2 := sqrt_sq' c₀
    linear_combination h1 - h2
  have hlt : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ * ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ < δ * δ := by
    rw [← norm_mul, hprod, ← dist_eq_norm, ← sq]
    exact hcc
  by_cases h : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ
  · exact hδε _ (by rwa [dist_eq_norm])
  · have h' : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ := by
      push Not at h
      have he : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ = ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ := by
        rw [← norm_neg]
        ring_nf
      rw [he]
      by_contra h2
      push Not at h2
      have := mul_le_mul h h2 hδ.le (norm_nonneg _)
      linarith
    have := hδε (-c ^ (1 / 2 : ℂ)) (by rwa [dist_eq_norm])
    simpa only [mul_neg, Complex.cosh_neg] using this

theorem continuous_coshT {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : Continuous (coshT g) := by
  rw [continuous_iff_continuousAt]
  intro c₀
  have hgc : Continuous g := hg.1.continuous
  have hF : ∀ c : ℂ, Continuous fun t : ℝ => (g t : ℂ) * Complex.cosh (t * c ^ (1 / 2 : ℂ)) := fun c =>
    (Complex.continuous_ofReal.comp hgc).mul
      (Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const))
  have hbc : Continuous fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)) :=
    (Complex.continuous_ofReal.comp hgc).norm.mul
      (Real.continuous_exp.comp (continuous_abs.mul continuous_const))
  have hbs : HasCompactSupport fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_
    have hT : T < |t| := by
      rw [Set.mem_Icc, not_and_or] at ht
      rcases ht with ht | ht
      · push Not at ht
        have := neg_abs_le t
        linarith
      · push Not at ht
        exact lt_of_lt_of_le ht (le_abs_self t)
    simp [hg.2.2 t hT]
  unfold coshT
  refine continuousAt_of_dominated (bound := fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)))
    (Eventually.of_forall fun c => (hF c).aestronglyMeasurable) ?_ (hbc.integrable_of_hasCompactSupport hbs)
    (ae_of_all _ fun t => (continuous_const.mul (continuous_cosh_sqrt (t : ℂ))).continuousAt)
  filter_upwards [Metric.ball_mem_nhds c₀ one_pos] with c hc
  refine ae_of_all _ fun t => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_cosh_le_exp _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
  have h1 := norm_sqrt_le c
  have h2 : ‖c‖ ≤ ‖c₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' c c₀
    rw [Metric.mem_ball, dist_eq_norm] at hc
    linarith
  linarith

theorem valCont : ValCont := by
  intro n _ μ M k val T χ χ₀ hk hχ
  obtain ⟨m, c, w, g, ks, hg, -, hval⟩ := hk
  have hv : val = fun χ => ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ) := funext hval
  rw [hv]
  have hz : ∀ l : List (Bool × ℕ), Tendsto (fun j => zVal l (χ j)) atTop (𝓝 (zVal l χ₀)) := by
    intro l
    induction l with
    | nil => simp only [zVal, List.map_nil, List.prod_nil]; exact tendsto_const_nhds
    | cons p l ih =>
      simp only [zVal, List.map_cons, List.prod_cons] at ih ⊢
      exact (hχ p.1 p.2).mul ih
  have hcas : Tendsto (fun j => cas (χ j)) atTop (𝓝 (cas χ₀)) := by
    unfold cas
    exact ((hχ true 2).add (hχ false 2)).const_mul 2
  refine tendsto_finsetSum _ fun i _ => ?_
  exact (tendsto_const_nhds.mul (hz (w i))).mul (((continuous_coshT (hg i).1).tendsto _).comp hcas)

end PositivityTheory.Rg.BcB.CG

end
end

section
open PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG

theorem smoothOf_holds : SmoothOf := smoothOf tensTest

theorem actVal_of (h : MultAlg) : ActVal := actVal h compatFub tensTest

theorem pack_of_gel (hS : SizeBasic) (hB : Bridge.BridgeSt) (hG : GelOf) : Pack :=
  pack_of tensTest typeOf smoothOf_holds (growthOf hS) hG infEx (PAut.autOf hB)

end PositivityTheory.Rg.BcB.CG
end
