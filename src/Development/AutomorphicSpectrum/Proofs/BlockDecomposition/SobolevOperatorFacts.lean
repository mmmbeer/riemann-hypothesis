import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnFderivApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FderivZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobSecK

variable {n : ℕ}

theorem far_Rd {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Mat n) {f : Mat n → V} {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → f y = 0) : ∀ y ∈ GLs n, R < lg y → Rd X f y = 0 := by
  intro y hy hl
  simp only [Rd]
  rw [RCalc.ByParts.fderiv_eq_zero_far GlobalTheory.CompanionTheory.LengthGL.lgFacts hR hy hl]
  rfl

theorem cpt_Rd {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Mat n) {f : Mat n → V} (hc : Cpt f) :
    Cpt (Rd X f) :=
  hc.imp fun _ h => far_Rd X h

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_of_cpt {W : Type} [NormedAddCommGroup W] {h : Mat n → W} (hc : ContinuousOn h (GLs n))
    (hz : Cpt h) : Integrable (fun y : G n => h y.val) μ := by
  obtain ⟨R, hR⟩ := hz
  have hcont : Continuous fun y : G n => h y.val :=
    hc.comp_continuous Units.continuous_val fun y => RCalc.ByParts.val_mem_GLs y
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
    ((GlobalTheory.CompanionTheory.LengthGL.lgFacts n).2.2.2.2.1 R) fun y hy => ?_)
  exact hR _ (RCalc.ByParts.val_mem_GLs y) (not_le.1 hy)

end Int

section Space

variable (n) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def Sp : Submodule ℂ (Mat n → V) where
  carrier := {f | ContDiffOn ℝ ∞ f (GLs n) ∧ Cpt f ∧ ∀ y, y ∉ GLs n → f y = 0}
  add_mem' := by
    rintro f h ⟨f1, ⟨R, f2⟩, f3⟩ ⟨h1, ⟨R', h2⟩, h3⟩
    refine ⟨f1.add h1, ⟨max R R', fun y hy hl => ?_⟩, fun y hy => ?_⟩
    · simp [f2 y hy (lt_of_le_of_lt (le_max_left _ _) hl), h2 y hy (lt_of_le_of_lt (le_max_right _ _) hl)]
    · simp [f3 y hy, h3 y hy]
  zero_mem' := ⟨contDiffOn_const, ⟨0, fun _ _ _ => rfl⟩, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨f1, ⟨R, f2⟩, f3⟩
    refine ⟨f1.const_smul c, ⟨R, fun y hy hl => ?_⟩, fun y hy => ?_⟩
    · simp [f2 y hy hl]
    · simp [f3 y hy]

variable {n V}
variable [MeasurableSpace (G n)]

def Hs (μ : Measure (G n)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Type := Sp n V

variable (μ : Measure (G n))

instance : AddCommGroup (Hs μ V) := inferInstanceAs (AddCommGroup (Sp n V))
instance : Module ℂ (Hs μ V) := inferInstanceAs (Module ℂ (Sp n V))

variable {μ}

def Hs.fn (f : Hs μ V) : Mat n → V := Subtype.val (p := fun f => f ∈ Sp n V) f

theorem Hs.smooth (f : Hs μ V) : ContDiffOn ℝ ∞ f.fn (GLs n) := f.2.1
theorem Hs.cpt (f : Hs μ V) : Cpt f.fn := f.2.2.1
theorem Hs.off (f : Hs μ V) {y : Mat n} (hy : y ∉ GLs n) : f.fn y = 0 := f.2.2.2 y hy
@[simp] theorem Hs.add_fn (f h : Hs μ V) : (f + h).fn = f.fn + h.fn := rfl
@[simp] theorem Hs.smul_fn (c : ℂ) (f : Hs μ V) : (c • f).fn = c • f.fn := rfl
@[simp] theorem Hs.zero_fn : (0 : Hs μ V).fn = 0 := rfl

theorem Hs.ext_on {f h : Hs μ V} (e : Set.EqOn f.fn h.fn (GLs n)) : f = h := by
  apply Subtype.ext
  funext y
  by_cases hy : y ∈ GLs n
  · exact e hy
  · exact (f.off hy).trans (h.off hy).symm

def toH (μ : Measure (G n)) (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hc : Cpt f) : Hs μ V :=
  ⟨(GLs n).indicator f, hf.congr fun y hy => Set.indicator_of_mem hy f,
    hc.imp fun _ h y hy hl => (Set.indicator_of_mem hy f).trans (h y hy hl),
    fun _ hy => Set.indicator_of_notMem hy f⟩

theorem toH_fn {f : Mat n → V} {hf : ContDiffOn ℝ ∞ f (GLs n)} {hc : Cpt f} {y : Mat n} (hy : y ∈ GLs n) :
    (toH μ f hf hc).fn y = f y :=
  Set.indicator_of_mem hy f

end Space

section Inner

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

theorem Hs.continuous_val (f : Hs μ V) : Continuous fun y : G n => f.fn y.val :=
  f.smooth.continuousOn.comp_continuous Units.continuous_val fun y => RCalc.ByParts.val_mem_GLs y

theorem integrable_inner (f h : Hs μ V) : Integrable (fun y : G n => ⟪f.fn y.val, h.fn y.val⟫_ℂ) μ := by
  obtain ⟨R, hR⟩ := f.cpt
  refine integrable_of_cpt μ (h := fun y => ⟪f.fn y, h.fn y⟫_ℂ)
    (f.smooth.continuousOn.inner h.smooth.continuousOn) ⟨R, fun y hy hl => ?_⟩
  simp [hR y hy hl]

theorem ip_self (f : Hs μ V) : ip μ f.fn f.fn = ((∫ y : G n, ‖f.fn y.val‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp only [ip, inner_self_eq_norm_sq_to_K]
  rw [← integral_complex_ofReal]
  simp

instance core : InnerProductSpace.Core ℂ (Hs μ V) where
  inner f h := ip μ f.fn h.fn
  conj_inner_symm f h := by
    simp only [ip]
    rw [← integral_conj]
    simp
  re_inner_nonneg f := by
    show 0 ≤ RCLike.re (ip μ f.fn f.fn)
    rw [ip_self]
    simpa using integral_nonneg fun y : G n => by positivity
  add_left f g h := by
    simp only [ip, Hs.add_fn, Pi.add_apply, inner_add_left]
    exact integral_add (integrable_inner f h) (integrable_inner g h)
  smul_left f h c := by
    simp only [ip, Hs.smul_fn, Pi.smul_apply, inner_smul_left]
    exact integral_const_mul _ _
  definite f hf := by
    have h0 : ∫ y : G n, ‖f.fn y.val‖ ^ 2 ∂μ = 0 := by
      have : ip μ f.fn f.fn = 0 := hf
      rw [ip_self] at this
      exact_mod_cast this
    have hint : Integrable (fun y : G n => ‖f.fn y.val‖ ^ 2) μ := by
      obtain ⟨R, hR⟩ := f.cpt
      refine integrable_of_cpt μ (h := fun y => ‖f.fn y‖ ^ 2) (f.smooth.continuousOn.norm.pow 2) ⟨R, fun y hy hl => ?_⟩
      simp [hR y hy hl]
    have h1 := (integral_eq_zero_iff_of_nonneg (fun y : G n => by positivity) hint).1 h0
    have hc : Continuous fun y : G n => ‖f.fn y.val‖ ^ 2 := (f.continuous_val.norm).pow 2
    have h2 := (Continuous.ae_eq_iff_eq μ hc continuous_const (g := fun _ => (0 : ℝ))).1 h1
    refine Hs.ext_on fun y hy => ?_
    have h3 := congrFun h2 (RCalc.ByParts.toG hy)
    simpa using h3

instance : NormedAddCommGroup (Hs μ V) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
instance : InnerProductSpace ℂ (Hs μ V) := InnerProductSpace.ofCore core.toCore

end Inner

section Ops

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)]
variable (μ : Measure (G n))

def Xop (p : Ix n) : Module.End ℂ (Hs μ V) where
  toFun f := toH μ (Rd (bs p) f.fn) (RCalc.Rd_contDiffOn _ f.smooth) (cpt_Rd _ f.cpt)
  map_add' f h := Hs.ext_on fun y hy => by
    simp only [Hs.add_fn, Pi.add_apply, toH_fn hy]
    exact OmDec.Rd_add_right _ f.smooth h.smooth hy
  map_smul' c f := Hs.ext_on fun y hy => by
    simp only [Hs.smul_fn, Pi.smul_apply, toH_fn hy, RingHom.id_apply]
    exact OmDec.Rd_smul_right _ _ f.smooth hy

variable {μ}

variable (μ)

variable {μ} in
theorem smooth_alt (T : V →L[ℂ] V) (f : Hs μ V) : ContDiffOn ℝ ∞ (fun y => T (f.fn y)) (GLs n) :=
  (T.restrictScalars ℝ).contDiff.comp_contDiffOn f.smooth

variable {μ} in
theorem compact_support_apply_clm (T : V →L[ℂ] V) (f : Hs μ V) : Cpt (fun y => T (f.fn y)) :=
  f.cpt.imp fun _ h y hy hl => by show T (f.fn y) = 0; rw [h y hy hl, map_zero]

def Tm (T : V →L[ℂ] V) : Module.End ℂ (Hs μ V) where
  toFun f := toH μ (fun y => T (f.fn y)) (smooth_alt T f) (compact_support_apply_clm T f)
  map_add' f h := Hs.ext_on fun y hy => by
    simp only [Hs.add_fn, Pi.add_apply]
    rw [toH_fn hy, toH_fn hy, toH_fn hy]
    simp only [Hs.add_fn, Pi.add_apply, map_add]
  map_smul' c f := Hs.ext_on fun y hy => by
    simp only [Hs.smul_fn, Pi.smul_apply, RingHom.id_apply]
    rw [toH_fn hy, toH_fn hy]
    simp only [Hs.smul_fn, Pi.smul_apply, map_smul]

variable {μ}

end Ops

end GlobalTheory.CompanionTheory.SobSecK
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobSecK

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_congr (w : List (Ix n)) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) :
    Set.EqOn (Rw w f) (Rw w h) (GLs n) := by
  induction w with
  | nil => exact e
  | cons p w ih => exact RCalc.Rd_congr (bs p) ih

theorem Rw_smooth (w : List (Ix n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact RCalc.Rd_contDiffOn (bs p) ih

theorem Rw_append (w w' : List (Ix n)) (f : Mat n → V) : Rw w' (Rw w f) = Rw (w' ++ w) f := by
  induction w' with
  | nil => rfl
  | cons p w' ih =>
    show Rd (bs p) (Rw w' (Rw w f)) = Rd (bs p) (Rw (w' ++ w) f)
    rw [ih]

end Words

section HWords

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)] {μ : Measure (G n)}

end HWords

section Skew

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Skew

section Bracket

def cf (M : Mat n) (p : Ix n) : ℝ := if p.1 then (M p.2.1 p.2.2).re else (M p.2.1 p.2.2).im

theorem sum_cf (M : Mat n) : ∑ p : Ix n, cf M p • bs p = M := by
  rw [OmDec.sum_Ix]
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ext i j
  simp only [cf, bs, if_true, Bool.false_eq_true, if_false, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · simp only [h, and_self, if_true]
    obtain ⟨rfl, rfl⟩ := h
    simp [Complex.real_smul, Complex.re_add_im]
  · simp [h]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sum_cf (M : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd M f g = ∑ p : Ix n, ((cf M p : ℝ) : ℂ) • Rd (bs p) f g := by
  conv_lhs => rw [← sum_cf M]
  simp only [Rd, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_smul_comm, map_smul]
  exact (Complex.coe_smul _ _).symm

end Bracket

section HBracket

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)] {μ : Measure (G n)}

end HBracket

section Sections

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Sections

section Powers

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Powers

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Main

end GlobalTheory.CompanionTheory.SobSecK
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobOpsPf

open GlobalTheory.CompanionTheory.RCalc (Rd_congr Rd_add Rd_smul Rd_contDiffOn differentiableAt_of_smooth gel_contDiffOn Rd_gel gel_right
  gel_post fderiv_comp_clm fderiv_post mulR mapsTo_mulR)
open GlobalTheory.CompanionTheory.SobSecK (Rw_congr Rw_smooth Rw_append Rd_sum_cf)

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_add (w : List (Bool × Fin n × Fin n)) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) : Set.EqOn (Rw w (f + f')) (Rw w f + Rw w f') (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_add (bs p) (Rw_smooth w hf) (Rw_smooth w hf') hx)

theorem Rw_smul (w : List (Bool × Fin n × Fin n)) (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (c • f)) (c • Rw w f) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_smul c (bs p) (Rw_smooth w hf) hx)

theorem Om_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Om f) (GLs n) :=
  ((gel_contDiffOn true 2 hf).add (gel_contDiffOn false 2 hf)).const_smul (2 : ℂ)

theorem Rd_Om (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Om f) g = Om (Rd X f) g := by
  have h1 := gel_contDiffOn true 2 hf
  have h2 := gel_contDiffOn false 2 hf
  have h3 : ContDiffOn ℝ ∞ (gel true 2 f + gel false 2 f) (GLs n) := h1.add h2
  have e1 := Rd_smul (2 : ℂ) X h3 hg
  have e2 := Rd_add X h1 h2 hg
  simp only [Pi.smul_apply, Pi.add_apply] at e1 e2
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [e1, e2, Rd_gel X true 2 hf hg, Rd_gel X false 2 hf hg]

theorem Rw_Om (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (Om f)) (Om (Rw w f)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_Om (bs p) (Rw_smooth w hf) hx)

theorem Rd_translate (X : Mat n) {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => f (y * x)) g = Rd (x⁻¹ * X * x) f (g * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hd := differentiableAt_of_smooth hf (mapsTo_mulR hx hg)
  have e : g * x * (x⁻¹ * X * x) = g * X * x := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have := fderiv_comp_clm (mulR x) hd (g * X)
  simp only [Rd, e]
  exact this

theorem Rd_post (X : Mat n) (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd X (fun y => A (f y)) g = A (Rd X f g) :=
  fderiv_post A (differentiableAt_of_smooth hf hg) _

theorem post_smooth (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => A (f y)) (GLs n) :=
  (A.restrictScalars ℝ).contDiff.comp_contDiffOn hf

theorem Rw_post (w : List (Bool × Fin n × Fin n)) (A : V →L[ℂ] V) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (Rw w (fun y => A (f y))) (fun y => A (Rw w f y)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_post (bs p) A (Rw_smooth w hf) hx)

theorem Om_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om (fun y => A (f y)) g = A (Om f g) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_post A _ _ hf hg, map_smul, map_add]

theorem Om_translate {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Om (fun y => f (y * x)) g = Om f (g * x) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_right _ _ hx hf hg]

theorem translate_smooth {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => f (y * x)) (GLs n) :=
  hf.comp (mulR x).contDiff.contDiffOn (mapsTo_mulR hx)

end Words

section Sob

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem val_mem (y : G n) : y.val ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.ByParts.val_mem_GLs y

theorem sob_congr {f h : Mat n → V} (hf : Sob μ f) (e : Set.EqOn f h (GLs n)) : Sob μ h :=
  ⟨hf.1.congr fun _ hx => (e hx).symm, fun w =>
    MemLp.ae_eq (ae_of_all _ fun y => Rw_congr w e (val_mem y)) (hf.2 w)⟩

theorem sob_add {f h : Mat n → V} (hf : Sob μ f) (hh : Sob μ h) : Sob μ (f + h) :=
  ⟨hf.1.add hh.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_add w hf.1 hh.1 (val_mem y)).symm)
    ((hf.2 w).add (hh.2 w))⟩

theorem sob_smul (c : ℂ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (c • f) :=
  ⟨hf.1.const_smul c, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_smul w c hf.1 (val_mem y)).symm)
    ((hf.2 w).const_smul c)⟩

theorem sob_zero {f : Mat n → V} (hf : Sob μ f) : Sob μ (0 : Mat n → V) := by
  simpa using sob_smul (0 : ℂ) hf

theorem sob_sum {ι : Type} (s : Finset ι) {f₀ : Mat n → V} (h₀ : Sob μ f₀) {F : ι → Mat n → V}
    (hF : ∀ i, Sob μ (F i)) : Sob μ (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sob_zero h₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact sob_add (hF a) ih

theorem sob_Rw (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rw w f) :=
  ⟨Rw_smooth w hf.1, fun w' => by rw [Rw_append]; exact hf.2 _⟩

theorem sob_bs (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd (bs p) f) :=
  sob_Rw [p] hf

theorem sob_Rd (X : Mat n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd X f) := by
  refine sob_congr (f := ∑ p : Bool × Fin n × Fin n, ((GlobalTheory.CompanionTheory.SobSecK.cf X p : ℝ) : ℂ) • Rd (bs p) f)
    (sob_sum _ hf fun p => sob_smul _ (sob_bs p hf)) fun g _ => ?_
  rw [Rd_sum_cf X f g]
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem sob_Eu (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Eu s a b f) :=
  sob_smul _ (sob_add (sob_Rd _ hf) (sob_smul _ (sob_Rd _ hf)))

theorem sob_Epow (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : ∀ a b, Sob μ (Epow s m a b f) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simpa [Epow, hab] using sob_zero hf
  | succ m ih =>
    intro a b
    exact sob_sum _ hf fun c => sob_Eu s a c (ih c b)

theorem sob_gel (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (gel s m f) :=
  sob_sum _ hf fun a => sob_Epow s m hf a a

theorem sob_Om {f : Mat n → V} (hf : Sob μ f) : Sob μ (Om f) :=
  sob_smul _ (sob_add (sob_gel _ _ hf) (sob_gel _ _ hf))

theorem sob_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : Sob μ f) : Sob μ (fun y => A (f y)) :=
  ⟨post_smooth A hf.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_post w A hf.1 (val_mem y)).symm)
    (A.comp_memLp' (hf.2 w))⟩

variable [BorelSpace (G n)] [μ.IsHaarMeasure]

theorem memLp_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : MemLp (fun y : G n => F y.val) 2 μ) :
    MemLp (fun y : G n => F (y.val * h.val)) 2 μ := by
  haveI := (hU n μ).1
  exact hF.comp_measurePreserving (measurePreserving_mul_right μ h)

theorem translate_memLp (hU : Unimod) (h : G n) (w : List (Bool × Fin n × Fin n)) :
    ∀ F : Mat n → V, Sob μ F → MemLp (fun y : G n => Rw w (fun z => F (z * h.val)) y.val) 2 μ := by
  induction w using List.reverseRecOn with
  | nil => exact fun F hF => memLp_translate hU h (hF.2 [])
  | append_singleton w p ih =>
    intro F hF
    rw [← Rw_append [p] w]
    have e : Set.EqOn (Rw [p] fun z => F (z * h.val)) (fun z => Rd (h.val⁻¹ * bs p * h.val) F (z * h.val)) (GLs n) :=
      fun g hg => Rd_translate (bs p) (val_mem h) hF.1 hg
    exact MemLp.ae_eq (ae_of_all _ fun y => (Rw_congr w e (val_mem y)).symm) (ih _ (sob_Rd _ hF))

theorem sob_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : Sob μ F) : Sob μ (fun y => F (y * h.val)) :=
  ⟨translate_smooth (val_mem h) hF.1, fun w => translate_memLp hU h w F hF⟩

end Sob

theorem sobOps : SobOps := by
  intro n _ _ μ _ V _ _ _ hU _ f hf
  refine ⟨sob_Om hf, fun w => sob_Rw w hf, fun w g hg => Rw_Om w hf.1 hg, fun a f' hf' => ⟨sob_add (sob_smul a hf) hf', ?_⟩,
    fun h A => ⟨sob_post A (sob_translate hU h hf), fun g hg => ?_⟩⟩
  · intro g hg
    have hs : ContDiffOn ℝ ∞ (a • f) (GLs n) := hf.1.const_smul a
    have e1 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_add hs hf'.1 hg
    have e2 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_smul a hf.1 hg
    simp only [Pi.add_apply, Pi.smul_apply] at e1 e2
    rw [e1, e2]
  · rw [Om_post A (translate_smooth (val_mem h) hf.1) hg, Om_translate (val_mem h) hf.1 hg]

end GlobalTheory.CompanionTheory.SobOpsPf
end
end
