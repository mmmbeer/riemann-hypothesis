import Mathlib
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.IsHermitianForExH
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.InstSecondCountableTopologyFrameSp
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.FramePairAddRight
import GroundTheory.HeightsAndTheta.Theta.SchroedingerTranslates.WmSysEquivDet

section
set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace SwmCone

open MeasureTheory Topology Filter Matrix TensorProduct NumberField IsDedekindDomain
  GroundTheory.Automorphic GroundTheory.Heights₂.Theta.IsoFrames
open scoped ENNReal NNReal

attribute [local instance] IsoFrames.scTop

section Local

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

variable (K E R) in

def cTr {m l : Type*} (g : Matrix m l (R ⊗[K] E)) : Matrix l m (R ⊗[K] E) :=
  (g.map (conjBase K E R))ᵀ

def frameMul (X : FrameSp K E R ι n) (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    FrameSp K E R ι n :=
  show Matrix ι (Fin n) (R ⊗[K] E) from (show Matrix ι (Fin n) (R ⊗[K] E) from X) * g

def frameSMul (h : Matrix ι ι (R ⊗[K] E)) (X : FrameSp K E R ι n) : FrameSp K E R ι n :=
  show Matrix ι (Fin n) (R ⊗[K] E) from h * (show Matrix ι (Fin n) (R ⊗[K] E) from X)

variable (K E R ι) in

def gramFibre (Q : Matrix ι ι E) (T : HermSp K E R n) : Set (FrameSp K E R ι n) :=
  {X | IsoFrames.gram K E R Q (show Matrix ι (Fin n) (R ⊗[K] E) from X) = T.mat}

variable (R) in

def modE [IsTopologicalRing R] [LocallyCompactSpace R] (z : (R ⊗[K] E)ˣ) : ℝ≥0 :=
  distribHaarChar R (Units.map (Algebra.norm R : R ⊗[K] E →* R) z)

def IsGramDensity (Q : Matrix ι ι E) (dX : Measure (FrameSp K E R ι n))
    (dS : Measure (HermSp K E R n)) (φ : FrameSp K E R ι n → ℂ) (Om : Set (HermSp K E R n))
    (δ : HermSp K E R n → ℂ) : Prop :=
  IsOpen Om ∧ ContinuousOn δ Om ∧
    ∀ f : Matrix (Fin n) (Fin n) (R ⊗[K] E) → ℂ, Continuous f → HasCompactSupport f →
      tsupport (fun S : HermSp K E R n ↦ f S.mat) ⊆ Om →
      ∫ X, f (IsoFrames.gram K E R Q (show Matrix ι (Fin n) (R ⊗[K] E) from X)) * φ X ∂dX =
        ∫ S, f S.mat * δ S ∂dS

def IsFibreMeasure (Q : Matrix ι ι E) (dX : Measure (FrameSp K E R ι n))
    (dS : Measure (HermSp K E R n)) (T : HermSp K E R n) (μ : Measure (FrameSp K E R ι n)) :
    Prop :=
  IsFiniteMeasureOnCompacts μ ∧ μ (gramFibre K E R ι Q T)ᶜ = 0 ∧
    (∀ h : unitaryPoints K E Q R,
      μ.map (frameSMul ((h : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E))) = μ) ∧
    ∀ φ : FrameSp K E R ι n → ℂ, Continuous φ → HasCompactSupport φ →
      ∃ (Om : Set (HermSp K E R n)) (δ : HermSp K E R n → ℂ),
        T ∈ Om ∧ IsGramDensity Q dX dS φ Om δ ∧ δ T = ∫ X, φ X ∂μ

variable [IsTopologicalRing R] [LocallyCompactSpace R]

def ConeChart (Q : Matrix ι ι E) (dX : Measure (FrameSp K E R ι n))
    (dS : Measure (HermSp K E R n)) (T : HermSp K E R n) (B : Set (GL (Fin n) (R ⊗[K] E)))
    (μ : Measure (FrameSp K E R ι n)) : Prop :=
  ∃ (Om : Set (HermSp K E R n)) (e : B ≃ₜ Om), IsOpen Om ∧ T ∈ Om ∧
    (∀ g : B, (e g : HermSp K E R n).mat =
      cTr K E R ((g : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E)) * T.mat *
        ((g : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))) ∧
    (∃ e₂ : (gramFibre K E R ι Q T) × B ≃ₜ (gramPre Q Om : Set (FrameSp K E R ι n)),
      ∀ p, (e₂ p : FrameSp K E R ι n) = frameMul (p.1 : FrameSp K E R ι n)
        ((p.2 : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))) ∧
    ∀ φ : FrameSp K E R ι n → ℂ, Continuous φ → HasCompactSupport φ →
      ∃ δ : HermSp K E R n → ℂ, IsGramDensity Q dX dS φ Om δ ∧
        ∀ g : B, δ (e g) =
          (((modE R (Matrix.GeneralLinearGroup.det (g : GL (Fin n) (R ⊗[K] E))) : ℝ) ^
              ((Fintype.card ι : ℤ) - n) : ℝ) : ℂ) *
            ∫ X, φ (frameMul X ((g : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))) ∂μ

def GeneralTAt (Q : Matrix ι ι E) (dX : Measure (FrameSp K E R ι n))
    (dS : Measure (HermSp K E R n)) : Prop :=
  ∀ T : HermSp K E R n, IsUnit T.mat.det →
    (∃ μ, IsFibreMeasure Q dX dS T μ) ∧
    ∀ (g₀ : GL (Fin n) (R ⊗[K] E)) (T' : HermSp K E R n),
      T'.mat = cTr K E R (g₀ : Matrix (Fin n) (Fin n) (R ⊗[K] E)) * T.mat * g₀ →
      ∀ μ μ' : Measure (FrameSp K E R ι n), IsFibreMeasure Q dX dS T μ →
        IsFibreMeasure Q dX dS T' μ' →
        μ' = ((modE R (Matrix.GeneralLinearGroup.det g₀)) ^ ((Fintype.card ι : ℤ) - n) : ℝ≥0) •
          μ.map (fun X ↦ frameMul X (g₀ : Matrix (Fin n) (Fin n) (R ⊗[K] E)))

end Local

section Groups

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]

variable (E) in

def realConeGroup (w : InfinitePlace K) (hw : w.IsReal) (n : ℕ) :
    Set (GL (Fin n) (w.Completion ⊗[K] E)) :=
  {g | (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) (w.Completion ⊗[K] E)) i j = 0) ∧
    ∀ i, ∃ u : w.Completion, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw u ∧
      (g : Matrix (Fin n) (Fin n) (w.Completion ⊗[K] E)) i i = algebraMap _ _ u}

variable (E) in

def finiteConeGroup (v : HeightOneSpectrum (𝓞 K)) (k n : ℕ) :
    Set (GL (Fin n) (v.adicCompletion K ⊗[K] E)) :=
  {g | (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) (v.adicCompletion K ⊗[K] E)) i j = 0) ∧
    (∀ i, ∃ u : v.adicCompletion K, ‖u - 1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ k ∧
      (g : Matrix (Fin n) (Fin n) (v.adicCompletion K ⊗[K] E)) i i = algebraMap _ _ u) ∧
    ∀ i j, i < j →
      ‖Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] E)
          ((g : Matrix (Fin n) (Fin n) (v.adicCompletion K ⊗[K] E)) i j)‖ ≤
          ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ k ∧
        ‖Algebra.norm (v.adicCompletion K)
          ((g : Matrix (Fin n) (Fin n) (v.adicCompletion K ⊗[K] E)) i j)‖ ≤
          ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ (2 * k)}

end Groups

section Statements

def ConeReal.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E]
    [Algebra.IsQuadraticExtension K E] (w : InfinitePlace K) (hw : w.IsReal)
    (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (Q : Matrix ι ι E),
    GroundTheory.Automorphic.IsHermitianFor (GroundTheory.Automorphic.conjHom K E) Q → IsUnit Q.det →
    ∀ (dX : Measure (FrameSp K E w.Completion ι n)) [dX.IsAddHaarMeasure]
      (dS : Measure (HermSp K E w.Completion n)) [dS.IsAddHaarMeasure]
      (T : HermSp K E w.Completion n) (t : Fin n → w.Completion), (∀ i, t i ≠ 0) →
      T.mat = Matrix.diagonal (fun i ↦ algebraMap w.Completion (w.Completion ⊗[K] E) (t i)) →
      ∃ μ : Measure (FrameSp K E w.Completion ι n),
        IsFibreMeasure Q dX dS T μ ∧ ConeChart Q dX dS T (realConeGroup E w hw n) μ

def ConeFinite.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E]
    [Algebra.IsQuadraticExtension K E] (v : HeightOneSpectrum (𝓞 K))
    (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (Q : Matrix ι ι E),
    GroundTheory.Automorphic.IsHermitianFor (GroundTheory.Automorphic.conjHom K E) Q → IsUnit Q.det →
    ∀ (dX : Measure (FrameSp K E (v.adicCompletion K) ι n)) [dX.IsAddHaarMeasure]
      (dS : Measure (HermSp K E (v.adicCompletion K) n)) [dS.IsAddHaarMeasure]
      (T : HermSp K E (v.adicCompletion K) n) (t : Fin n → v.adicCompletion K), (∀ i, t i ≠ 0) →
      T.mat = Matrix.diagonal
        (fun i ↦ algebraMap (v.adicCompletion K) (v.adicCompletion K ⊗[K] E) (t i)) →
      ∃ μ : Measure (FrameSp K E (v.adicCompletion K) ι n),
        IsFibreMeasure Q dX dS T μ ∧
        ∀ k : ℕ, ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ k < ‖(2 : v.adicCompletion K)‖ →
          ConeChart Q dX dS T (finiteConeGroup E v k n) μ

def ConeGeneral.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E]
    [Algebra.IsQuadraticExtension K E] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (Q : Matrix ι ι E),
    GroundTheory.Automorphic.IsHermitianFor (GroundTheory.Automorphic.conjHom K E) Q → IsUnit Q.det →
    (∀ (w : InfinitePlace K), w.IsReal →
      ∀ (dX : Measure (FrameSp K E w.Completion ι n)) [dX.IsAddHaarMeasure]
        (dS : Measure (HermSp K E w.Completion n)) [dS.IsAddHaarMeasure],
        GeneralTAt Q dX dS) ∧
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (dX : Measure (FrameSp K E (v.adicCompletion K) ι n)) [dX.IsAddHaarMeasure]
      (dS : Measure (HermSp K E (v.adicCompletion K) n)) [dS.IsAddHaarMeasure],
      GeneralTAt Q dX dS

end Statements

section Ties

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]

variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R]

def hermOne (n : ℕ) : HermSp K E R n :=
  ⟨1, by
    show ((1 : Matrix (Fin n) (Fin n) (R ⊗[K] E)).map (conjBase K E R))ᵀ = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]⟩

end Ties

end SwmCone

end GroundTheory.Heights₂.Theta
end
end

section
namespace GroundTheory.Heights₂.Theta

namespace FibreMeasure

open MeasureTheory

section Shear

variable {G P : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [AddCommGroup P] [MeasurableSpace P] [MeasurableAdd₂ P] [MeasurableNeg P]

theorem measurePreserving_shear (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure P) [ν.IsAddLeftInvariant] [SFinite ν] {B : Set P} (hB : MeasurableSet B)
    (hB0 : ν B ≠ 0) (hBt : ν B ≠ ⊤) (ζ : P →+ G) (hζ : Measurable ζ) (t : G → P)
    (ht : Measurable t) (htζ : ∀ X d, t (X + ζ d) = t X) :
    MeasurePreserving (fun X ↦ X + ζ (t X)) μ μ := by
  have hf : Measurable (fun X ↦ X + ζ (t X)) := measurable_id.add (hζ.comp ht)
  refine ⟨hf, ?_⟩
  set ρ : P → ENNReal := B.indicator (fun _ ↦ (ν B)⁻¹) with hρdef
  have hρ : Measurable ρ := measurable_const.indicator hB
  have hρ1 : ∫⁻ d, ρ d ∂ν = 1 := by
    rw [hρdef, lintegral_indicator hB, setLIntegral_const, ENNReal.inv_mul_cancel hB0 hBt]
  have hρsh : ∀ c : P, ∫⁻ d, ρ (d - c) ∂ν = 1 := fun c ↦ by
    rw [← hρ1]
    simp_rw [sub_eq_add_neg]
    exact lintegral_add_right_eq_self ρ (-c)
  have key : ∀ g : G → ENNReal, Measurable g →
      ∫⁻ X, g (X + ζ (t X)) ∂μ = ∫⁻ X, g X ∂μ := by
    intro g hg
    have hm1 : Measurable (Function.uncurry fun (d : P) (X : G) ↦ ρ d * g (X + ζ (d + t X))) := by
      refine (hρ.comp measurable_fst).mul (hg.comp ?_)
      exact measurable_snd.add (hζ.comp (measurable_fst.add (ht.comp measurable_snd)))
    have hm2 : Measurable (Function.uncurry fun (X : G) (d : P) ↦ ρ (d - t X) * g (X + ζ d)) := by
      refine (hρ.comp (measurable_snd.sub (ht.comp measurable_fst))).mul (hg.comp ?_)
      exact measurable_fst.add (hζ.comp measurable_snd)
    have hm3 : Measurable (Function.uncurry fun (d : P) (X : G) ↦ ρ (d - t X) * g X) := by
      exact (hρ.comp (measurable_fst.sub (ht.comp measurable_snd))).mul (hg.comp measurable_snd)
    calc ∫⁻ X, g (X + ζ (t X)) ∂μ
        = ∫⁻ d, ρ d * ∫⁻ X, g (X + ζ (t X)) ∂μ ∂ν := by
          rw [lintegral_mul_const _ hρ, hρ1, one_mul]
      _ = ∫⁻ d, ∫⁻ X, ρ d * g (X + ζ (d + t X)) ∂μ ∂ν := by
          refine lintegral_congr fun d ↦ ?_
          have h1 : ∫⁻ X, g (X + ζ (d + t X)) ∂μ = ∫⁻ X, g (X + ζ (t X)) ∂μ := by
            rw [← lintegral_add_right_eq_self (μ := μ) (fun X ↦ g (X + ζ (t X))) (ζ d)]
            refine lintegral_congr fun X ↦ ?_
            simp only [htζ, map_add]
            congr 1
            abel
          rw [lintegral_const_mul (ρ d) (f := fun X ↦ g (X + ζ (d + t X)))
            (hg.comp (measurable_id.add (hζ.comp (measurable_const.add ht)))), h1]
      _ = ∫⁻ X, ∫⁻ d, ρ d * g (X + ζ (d + t X)) ∂ν ∂μ :=
          lintegral_lintegral_swap hm1.aemeasurable
      _ = ∫⁻ X, ∫⁻ d, ρ (d - t X) * g (X + ζ d) ∂ν ∂μ := by
          refine lintegral_congr fun X ↦ ?_
          rw [← lintegral_add_right_eq_self (μ := ν) (fun d ↦ ρ (d - t X) * g (X + ζ d)) (t X)]
          simp
      _ = ∫⁻ d, ∫⁻ X, ρ (d - t X) * g (X + ζ d) ∂μ ∂ν :=
          lintegral_lintegral_swap hm2.aemeasurable
      _ = ∫⁻ d, ∫⁻ X, ρ (d - t X) * g X ∂μ ∂ν := by
          refine lintegral_congr fun d ↦ ?_
          have := lintegral_add_right_eq_self (μ := μ) (fun X ↦ ρ (d - t X) * g X) (ζ d)
          simp only [htζ] at this
          exact this
      _ = ∫⁻ X, ∫⁻ d, ρ (d - t X) * g X ∂ν ∂μ :=
          lintegral_lintegral_swap hm3.aemeasurable
      _ = ∫⁻ X, g X ∂μ := by
          refine lintegral_congr fun X ↦ ?_
          rw [lintegral_mul_const (r := g X) (f := fun d ↦ ρ (d - t X))
            (hρ.comp (measurable_id.sub measurable_const)), hρsh, one_mul]
  ext A hA
  rw [Measure.map_apply hf hA, ← lintegral_indicator_one (hf hA), ← lintegral_indicator_one hA]
  exact key (A.indicator 1) (measurable_one.indicator hA)

end Shear

end FibreMeasure

end GroundTheory.Heights₂.Theta
end

section
set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace FibreMeasure

open MeasureTheory Topology Filter Set

section Chart

variable {G T : Type*}
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
  [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

structure IsTransChart (dX : Measure G) (Γ : G → T) (Ω : Set G) (σ : T → G → G) : Prop where
  isOpen : IsOpen Ω
  continuousOn : ContinuousOn (fun q : T × G ↦ σ q.1 q.2) (univ ×ˢ Ω)
  mapsTo : ∀ s X, X ∈ Ω → σ s X ∈ Ω
  zero : ∀ X ∈ Ω, σ 0 X = X
  add : ∀ s t X, X ∈ Ω → σ s (σ t X) = σ (s + t) X
  shift : ∀ s X, X ∈ Ω → Γ (σ s X) = Γ X + s
  pres : ∀ s, MeasurePreserving (σ s) (dX.restrict Ω) (dX.restrict Ω)

variable {dX : Measure G} {Γ : G → T} {Ω : Set G} {σ : T → G → G}

variable (Γ σ) in

def chartProj (X : G) : G := σ (-Γ X) X

variable (Γ Ω σ) in

noncomputable def chartProjM : G → G := by
  classical exact Ω.piecewise (chartProj Γ σ) id

namespace IsTransChart

variable (h : IsTransChart dX Γ Ω σ)
include h

theorem Γ_chartProj {X : G} (hX : X ∈ Ω) : Γ (chartProj Γ σ X) = 0 := by
  rw [chartProj, h.shift _ _ hX, add_neg_cancel]

theorem σ_Γ_chartProj {X : G} (hX : X ∈ Ω) : σ (Γ X) (chartProj Γ σ X) = X := by
  rw [chartProj, h.add _ _ _ hX, add_neg_cancel, h.zero _ hX]

theorem chartProj_σ (s : T) {X : G} (hX : X ∈ Ω) :
    chartProj Γ σ (σ s X) = chartProj Γ σ X := by
  rw [chartProj, chartProj, h.shift _ _ hX, h.add _ _ _ hX]
  congr 1
  abel

theorem chartProj_of_Γ_eq_zero {X : G} (hX : X ∈ Ω) (h0 : Γ X = 0) : chartProj Γ σ X = X := by
  rw [chartProj, h0, neg_zero, h.zero _ hX]

end IsTransChart

end Chart

end FibreMeasure

end GroundTheory.Heights₂.Theta
end

section
set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

namespace Chart

open MeasureTheory Topology Filter Set Matrix TensorProduct GroundTheory.Automorphic FibreMeasure

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {H : Matrix ι ι E}

attribute [local instance] scTop finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

local infixl:70 " ⬝ " => @HMul.hMul _ _ _ instHMulOfFintypeOfMulOfAddCommMonoid

def toM {κ : Type*} [Fintype κ] [DecidableEq κ] (X : FrameSp K E R κ p) : Matrix κ (Fin p) (R ⊗[K] E) := X

def ofM {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ (Fin p) (R ⊗[K] E)) : FrameSp K E R κ p := M

variable (R p) in

def gramH (hH : IsHermitianFor (conjHom K E) H) (X : FrameSp K E R ι p) : HermSp K E R p :=
  ⟨gram K E R H (toM X), cT_framePair hH _ _⟩

theorem continuous_toM {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Continuous (toM : FrameSp K E R κ p → Matrix κ (Fin p) (R ⊗[K] E)) := continuous_id

theorem continuous_ofM {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Continuous (ofM : Matrix κ (Fin p) (R ⊗[K] E) → FrameSp K E R κ p) := continuous_id

theorem continuous_framePair_left {q : ℕ} (Z : Matrix ι (Fin q) (R ⊗[K] E)) :
    Continuous (fun X : FrameSp K E R ι p ↦ framePair K E R H Z (toM X)) := by
  simp only [framePair_eq]
  exact continuous_const.matrix_mul continuous_toM

variable (R p H) in

def chartSet (Z : Matrix ι (Fin p) (R ⊗[K] E)) : Set (FrameSp K E R ι p) :=
  {X | IsUnit (framePair K E R H Z (toM X)).det}

variable (H) in

def chartShift (Z : Matrix ι (Fin p) (R ⊗[K] E)) (S : HermSp K E R p) :
    FrameSp K E R ι p → FrameSp K E R (Fin p) p := by
  classical exact (chartSet R p H Z).piecewise (fun X ↦ ofM (shiftT (H := H) Z (toM X) S.mat)) 0

variable (H) in

def chartAct (Z : Matrix ι (Fin p) (R ⊗[K] E)) (S : HermSp K E R p) (X : FrameSp K E R ι p) :
    FrameSp K E R ι p :=
  ofM (toM X + Z ⬝ toM (chartShift H Z S X))

variable {Z : Matrix ι (Fin p) (R ⊗[K] E)}

theorem chartShift_of_mem {S : HermSp K E R p} {X : FrameSp K E R ι p}
    (hX : X ∈ chartSet R p H Z) :
    toM (chartShift H Z S X) = shiftT (H := H) Z (toM X) S.mat := by
  classical
  simp only [chartShift, Set.piecewise, hX, if_true]
  rfl

theorem chartShift_of_notMem {S : HermSp K E R p} {X : FrameSp K E R ι p}
    (hX : X ∉ chartSet R p H Z) : chartShift H Z S X = 0 := by
  classical
  simp only [chartShift, Set.piecewise, hX, if_false]
  rfl

theorem toM_chartAct (S : HermSp K E R p) (X : FrameSp K E R ι p) :
    toM (chartAct H Z S X) = toM X + Z ⬝ toM (chartShift H Z S X) := rfl

theorem framePair_chartAct (hZ : gram K E R H Z = 0) (S : HermSp K E R p) (X : FrameSp K E R ι p) :
    framePair K E R H Z (toM (chartAct H Z S X)) = framePair K E R H Z (toM X) := by
  rw [toM_chartAct]
  exact framePair_add_iso hZ _ _

theorem mem_chartSet_chartAct (hZ : gram K E R H Z = 0) (S : HermSp K E R p)
    (X : FrameSp K E R ι p) : chartAct H Z S X ∈ chartSet R p H Z ↔ X ∈ chartSet R p H Z := by
  show IsUnit _ ↔ IsUnit _
  rw [framePair_chartAct hZ]

theorem continuousAt_mulM {X : Type*} [TopologicalSpace X] {m n l : Type*} [Fintype n]
    {f : X → Matrix m n (R ⊗[K] E)} {g : X → Matrix n l (R ⊗[K] E)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun y ↦ f y ⬝ g y) x :=
  ((continuous_fst.matrix_mul continuous_snd :
    Continuous fun q : Matrix m n (R ⊗[K] E) × Matrix n l (R ⊗[K] E) ↦ q.1 ⬝ q.2).continuousAt).comp
    (hf.prodMk hg)

variable (hRu : IsOpen {r : R | IsUnit r}) (hRi : ∀ r : R, IsUnit r → ContinuousAt Ring.inverse r)

include hRu in
theorem isOpen_chartSet : IsOpen (chartSet R p H Z) :=
  (isOpen_isUnit_det hRu).preimage (continuous_framePair_left Z)

theorem shiftT_add (X : Matrix ι (Fin p) (R ⊗[K] E)) (S T : Matrix (Fin p) (Fin p) (R ⊗[K] E)) :
    shiftT (H := H) Z X (S + T) = shiftT (H := H) Z X S + shiftT (H := H) Z X T := by
  rw [shiftT, shiftT, shiftT, smul_add, Matrix.mul_add]

theorem shiftT_zero (X : Matrix ι (Fin p) (R ⊗[K] E)) : shiftT (H := H) Z X 0 = 0 := by
  rw [shiftT, smul_zero, Matrix.mul_zero]

theorem shiftT_add_iso (hZ : gram K E R H Z = 0) (X : Matrix ι (Fin p) (R ⊗[K] E))
    (d : Matrix (Fin p) (Fin p) (R ⊗[K] E)) (S : Matrix (Fin p) (Fin p) (R ⊗[K] E)) :
    shiftT (H := H) Z (X + Z ⬝ d) S = shiftT (H := H) Z X S := by
  rw [shiftT, shiftT, framePair_add_iso hZ]

theorem chartShift_add_iso (hZ : gram K E R H Z = 0) (S : HermSp K E R p) (X : FrameSp K E R ι p)
    (d : FrameSp K E R (Fin p) p) :
    chartShift H Z S (ofM (toM X + Z ⬝ toM d)) = chartShift H Z S X := by
  have hmem : ofM (toM X + Z ⬝ toM d) ∈ chartSet R p H Z ↔ X ∈ chartSet R p H Z := by
    show IsUnit _ ↔ IsUnit _
    rw [show toM (ofM (toM X + Z ⬝ toM d) : FrameSp K E R ι p) = toM X + Z ⬝ toM d from rfl,
      framePair_add_iso hZ]
  by_cases hX : X ∈ chartSet R p H Z
  · have h1 := chartShift_of_mem (S := S) hX
    have h2 := chartShift_of_mem (S := S) (hmem.2 hX)
    rw [show toM (ofM (toM X + Z ⬝ toM d) : FrameSp K E R ι p) = toM X + Z ⬝ toM d from rfl,
      shiftT_add_iso hZ, ← h1] at h2
    exact h2
  · rw [chartShift_of_notMem hX, chartShift_of_notMem (fun h ↦ hX (hmem.1 h))]

include hRu hRi in
theorem continuousOn_shiftT (S : HermSp K E R p) :
    ContinuousOn (fun X : FrameSp K E R ι p ↦
      (ofM (shiftT (H := H) Z (toM X) S.mat) : FrameSp K E R (Fin p) p)) (chartSet R p H Z) := by
  intro X hX
  refine ContinuousAt.continuousWithinAt ?_
  have hu : IsUnit (cT K E R (framePair K E R H Z (toM X))).det := by
    rw [det_cT]
    exact hX.map _
  have hc : Continuous (fun X : FrameSp K E R ι p ↦ cT K E R (framePair K E R H Z (toM X))) :=
    ((continuous_framePair_left Z).matrix_map (continuous_conjBase R)).matrix_transpose
  have hinv : ContinuousAt (fun X : FrameSp K E R ι p ↦ (cT K E R (framePair K E R H Z (toM X)))⁻¹) X :=
    ContinuousAt.comp (g := Inv.inv) (continuousAt_matrix_inv_A hRu hRi _ hu) hc.continuousAt
  exact continuous_ofM.continuousAt.comp (continuousAt_mulM hinv continuousAt_const)

include hRu hRi in
theorem measurable_chartShift (S : HermSp K E R p) : Measurable (chartShift H Z S) := by
  classical
  exact ContinuousOn.measurable_piecewise (γ := FrameSp K E R (Fin p) p)
    (continuousOn_shiftT hRu hRi S) continuousOn_const (isOpen_chartSet hRu).measurableSet

include hRu hRi in

theorem isTransChart_chart [CharZero K] (hH : IsHermitianFor (conjHom K E) H)
    (hZ : gram K E R H Z = 0) (dX : Measure (FrameSp K E R ι p)) [dX.IsAddHaarMeasure] :
    IsTransChart dX (gramH R p hH) (chartSet R p H Z) (chartAct H Z) := by
  have hΩ : IsOpen (chartSet R p H Z) := isOpen_chartSet hRu
  refine ⟨hΩ, ?_, fun S X hX ↦ (mem_chartSet_chartAct hZ S X).2 hX, ?_, ?_, ?_, ?_⟩
  ·
    intro q hq
    refine ContinuousAt.continuousWithinAt ?_
    have hu : IsUnit (cT K E R (framePair K E R H Z (toM q.2))).det := by
      rw [det_cT]
      exact hq.2.map _
    have hc : Continuous (fun q : HermSp K E R p × FrameSp K E R ι p ↦
        cT K E R (framePair K E R H Z (toM q.2))) :=
      (((continuous_framePair_left Z).comp continuous_snd).matrix_map
        (continuous_conjBase R)).matrix_transpose
    have hinv : ContinuousAt (fun q : HermSp K E R p × FrameSp K E R ι p ↦
        (cT K E R (framePair K E R H Z (toM q.2)))⁻¹) q :=
      ContinuousAt.comp (g := Inv.inv) (continuousAt_matrix_inv_A hRu hRi _ hu) hc.continuousAt
    have hS : Continuous (fun q : HermSp K E R p × FrameSp K E R ι p ↦ (2 : K)⁻¹ • q.1.mat) :=
      (continuous_hermSpMat.comp continuous_fst).const_smul ((2 : K)⁻¹)
    have hf : ContinuousAt (fun q : HermSp K E R p × FrameSp K E R ι p ↦
        ofM (toM q.2 + Z ⬝ ((cT K E R (framePair K E R H Z (toM q.2)))⁻¹ ⬝
            ((2 : K)⁻¹ • q.1.mat))) : HermSp K E R p × FrameSp K E R ι p → FrameSp K E R ι p) q :=
      continuous_ofM.continuousAt.comp ((continuous_toM.comp continuous_snd).continuousAt.add
        (continuousAt_mulM continuousAt_const (continuousAt_mulM hinv hS.continuousAt)))
    refine hf.congr ?_
    filter_upwards [(isOpen_univ.prod hΩ).mem_nhds hq] with q' hq'
    show _ = ofM (toM q'.2 + Z ⬝ toM (chartShift H Z q'.1 q'.2))
    rw [chartShift_of_mem hq'.2]
    rfl
  ·
    intro X hX
    show ofM (toM X + Z ⬝ toM (chartShift H Z 0 X)) = X
    rw [chartShift_of_mem hX]
    show ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) 0) = X
    rw [shiftT_zero, Matrix.mul_zero, add_zero]
    rfl
  ·
    intro S T X hX
    have hX' := (mem_chartSet_chartAct hZ T X).2 hX
    show ofM (toM (chartAct H Z T X) + Z ⬝ toM (chartShift H Z S (chartAct H Z T X))) =
      ofM (toM X + Z ⬝ toM (chartShift H Z (S + T) X))
    rw [chartShift_of_mem hX', chartShift_of_mem hX, toM_chartAct, chartShift_of_mem hX,
      shiftT_add_iso hZ]
    show ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) T.mat + Z ⬝ shiftT (H := H) Z (toM X) S.mat) =
      ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) (S.mat + T.mat))
    rw [shiftT_add, Matrix.mul_add]
    congr 1
    abel
  ·
    intro S X hX
    apply Subtype.ext
    show gram K E R H (toM X + Z ⬝ toM (chartShift H Z S X)) = gram K E R H (toM X) + S.mat
    rw [chartShift_of_mem hX]
    exact gram_add_shiftT hH hZ hX S.2
  ·
    intro S
    obtain ⟨B, hBc, hB0⟩ := exists_compact_mem_nhds (0 : FrameSp K E R (Fin p) p)
    let ν : Measure (FrameSp K E R (Fin p) p) := Measure.addHaar
    let ζ : FrameSp K E R (Fin p) p →+ FrameSp K E R ι p :=
      { toFun := fun d ↦ ofM (Z ⬝ toM d)
        map_zero' := Matrix.mul_zero Z
        map_add' := fun d d' ↦ Matrix.mul_add Z _ _ }
    have hζ : Continuous ζ :=
      continuous_ofM.comp (continuous_const.matrix_mul continuous_toM)
    have hsh := measurePreserving_shear dX ν hBc.measurableSet
      (Measure.measure_pos_of_mem_nhds ν hB0).ne' hBc.measure_lt_top.ne ζ hζ.measurable
      (chartShift H Z S) (measurable_chartShift hRu hRi S) (fun X d ↦ chartShift_add_iso hZ S X d)
    have hpre : (fun X ↦ X + ζ (chartShift H Z S X)) ⁻¹' chartSet R p H Z = chartSet R p H Z := by
      ext X
      exact mem_chartSet_chartAct hZ S X
    have := hsh.restrict_preimage (isOpen_chartSet (H := H) (Z := Z) hRu).measurableSet
    rw [hpre] at this
    exact this

end

end Chart

end IsoFrames

end GroundTheory.Heights₂.Theta
end

section
set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace SwmCone

open MeasureTheory Topology Filter Matrix TensorProduct GroundTheory.Automorphic IsoFrames
open scoped ENNReal NNReal

attribute [local instance] IsoFrames.scTop finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

section Linear

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

instance instModuleFrameSpSwmCone : Module R (FrameSp K E R ι n) :=
  inferInstanceAs (Module R (ι → Fin n → R ⊗[K] E))

instance instIsModuleTopologyFrameSpSwmCone : IsModuleTopology R (FrameSp K E R ι n) :=
  inferInstanceAs (IsModuleTopology R (ι → Fin n → R ⊗[K] E))

instance instFiniteDimensionalFrameSpSwmCone : FiniteDimensional R (FrameSp K E R ι n) :=
  inferInstanceAs (Module.Finite R (ι → Fin n → R ⊗[K] E))

variable (K E R ι n) in

def frameMulLinA (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    (ι → Fin n → R ⊗[K] E) →ₗ[R ⊗[K] E] (ι → Fin n → R ⊗[K] E) :=
  LinearMap.pi fun i ↦ (Matrix.toLin' gᵀ).comp (LinearMap.proj i)

theorem frameMulLinA_apply (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (X : ι → Fin n → R ⊗[K] E) :
    frameMulLinA K E R ι n g X = (Matrix.of X * g : Matrix ι (Fin n) (R ⊗[K] E)) := by
  ext i j
  simp only [frameMulLinA, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Matrix.toLin'_apply]
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rfl


variable (K E R ι n) in

def frameMulLin (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    FrameSp K E R ι n →ₗ[R] FrameSp K E R ι n :=
  (frameMulLinA K E R ι n g).restrictScalars R

theorem frameMulLin_apply (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameMulLin K E R ι n g X = frameMul X g :=
  frameMulLinA_apply g X


end Linear

section Modulus

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]

theorem absF_mul (a b : F) :
    IndefiniteRowSideFullHecke.WmSys.absF (a * b) = IndefiniteRowSideFullHecke.WmSys.absF a * IndefiniteRowSideFullHecke.WmSys.absF b := by
  by_cases ha : a = 0
  · simp [IndefiniteRowSideFullHecke.WmSys.absF, ha]
  by_cases hb : b = 0
  · simp [IndefiniteRowSideFullHecke.WmSys.absF, hb]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [IndefiniteRowSideFullHecke.WmSys.absF, dif_neg ha, dif_neg hb, dif_neg hab]
  rw [show Units.mk0 (a * b) hab = Units.mk0 a ha * Units.mk0 b hb from Units.ext rfl, map_mul]



variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable [Algebra K F]





end Modulus

section FrameMul

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem frameMul_frameMul (X : FrameSp K E R ι n) (g h : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    frameMul (frameMul X g) h = frameMul X (g * h) :=
  Matrix.mul_assoc (X : Matrix ι (Fin n) (R ⊗[K] E)) g h

theorem frameMul_one (X : FrameSp K E R ι n) : frameMul X 1 = X :=
  Matrix.mul_one (X : Matrix ι (Fin n) (R ⊗[K] E))

variable (K E R ι n) in

def frameMulLinEquiv (g : GL (Fin n) (R ⊗[K] E)) : FrameSp K E R ι n ≃ₗ[R] FrameSp K E R ι n :=
  { frameMulLin K E R ι n (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) with
    invFun := frameMulLin K E R ι n ((g⁻¹ : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))
    left_inv := fun X ↦ by
      show frameMulLin K E R ι n _ (frameMulLin K E R ι n _ X) = X
      rw [frameMulLin_apply, frameMulLin_apply, frameMul_frameMul, Units.mul_inv, frameMul_one]
    right_inv := fun X ↦ by
      show frameMulLin K E R ι n _ (frameMulLin K E R ι n _ X) = X
      rw [frameMulLin_apply, frameMulLin_apply, frameMul_frameMul, Units.inv_mul, frameMul_one] }

variable (K E R ι n) in

def frameMulHom (g : GL (Fin n) (R ⊗[K] E)) : FrameSp K E R ι n ≃ₜ+ FrameSp K E R ι n :=
  { (frameMulLinEquiv K E R ι n g).toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (frameMulLinEquiv K E R ι n g).toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (frameMulLinEquiv K E R ι n g).symm.toLinearMap }

@[simp]
theorem frameMulHom_apply (g : GL (Fin n) (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameMulHom K E R ι n g X = frameMul X (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :=
  frameMulLin_apply _ X

variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]


end FrameMul

section FrameSMul

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def transposePi (S : Type*) [CommRing S] (m κ : Type*) :
    (m → κ → S) ≃ₗ[S] (κ → m → S) where
  toFun X j i := X i j
  invFun Y i j := Y j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def rowMulLinA {S : Type*} [CommRing S] (m : Type*) {κ : Type*} [Fintype m] [Fintype κ]
    [DecidableEq κ] (g : Matrix κ κ S) : (m → κ → S) →ₗ[S] (m → κ → S) :=
  LinearMap.pi fun i ↦ (Matrix.toLin' gᵀ).comp (LinearMap.proj i)

theorem rowMulLinA_apply {S : Type*} [CommRing S] {m κ : Type*} [Fintype m] [Fintype κ]
    [DecidableEq κ] (g : Matrix κ κ S) (X : m → κ → S) :
    rowMulLinA m g X = (Matrix.of X * g : Matrix m κ S) := by
  ext i j
  simp only [rowMulLinA, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Matrix.toLin'_apply]
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rfl


def colMulLinA {S : Type*} [CommRing S] {m : Type*} (κ : Type*) [Fintype m] [DecidableEq m]
    [Fintype κ] (h : Matrix m m S) : (m → κ → S) →ₗ[S] (m → κ → S) :=
  ((transposePi S m κ).symm.toLinearMap.comp (rowMulLinA κ hᵀ)).comp
    (transposePi S m κ).toLinearMap

theorem colMulLinA_apply {S : Type*} [CommRing S] {m κ : Type*} [Fintype m] [DecidableEq m]
    [Fintype κ] (h : Matrix m m S) (X : m → κ → S) :
    colMulLinA κ h X = (h * Matrix.of X : Matrix m κ S) := by
  ext i j
  simp only [colMulLinA, LinearMap.comp_apply, LinearEquiv.coe_coe, rowMulLinA_apply]
  show (Matrix.of (fun j i ↦ X i j) * hᵀ) j i = (h * Matrix.of X) i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _


variable (K E R ι n) in

def frameSMulLin (h : Matrix ι ι (R ⊗[K] E)) : FrameSp K E R ι n →ₗ[R] FrameSp K E R ι n :=
  (colMulLinA (Fin n) h).restrictScalars R

theorem frameSMulLin_apply (h : Matrix ι ι (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameSMulLin K E R ι n h X = frameSMul h X :=
  colMulLinA_apply h X


theorem frameSMul_frameSMul (h h' : Matrix ι ι (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameSMul h (frameSMul h' X) = frameSMul (h * h') X :=
  (Matrix.mul_assoc h h' (X : Matrix ι (Fin n) (R ⊗[K] E))).symm

theorem frameSMul_one (X : FrameSp K E R ι n) : frameSMul (1 : Matrix ι ι (R ⊗[K] E)) X = X :=
  Matrix.one_mul (X : Matrix ι (Fin n) (R ⊗[K] E))

variable (K E R ι n) in

def frameSMulLinEquiv (h : GL ι (R ⊗[K] E)) : FrameSp K E R ι n ≃ₗ[R] FrameSp K E R ι n :=
  { frameSMulLin K E R ι n (h : Matrix ι ι (R ⊗[K] E)) with
    invFun := frameSMulLin K E R ι n ((h⁻¹ : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E))
    left_inv := fun X ↦ by
      show frameSMulLin K E R ι n _ (frameSMulLin K E R ι n _ X) = X
      rw [frameSMulLin_apply, frameSMulLin_apply, frameSMul_frameSMul, Units.inv_mul, frameSMul_one]
    right_inv := fun X ↦ by
      show frameSMulLin K E R ι n _ (frameSMulLin K E R ι n _ X) = X
      rw [frameSMulLin_apply, frameSMulLin_apply, frameSMul_frameSMul, Units.mul_inv, frameSMul_one] }

variable (K E R ι n) in

def frameSMulHom (h : GL ι (R ⊗[K] E)) : FrameSp K E R ι n ≃ₜ+ FrameSp K E R ι n :=
  { (frameSMulLinEquiv K E R ι n h).toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (frameSMulLinEquiv K E R ι n h).toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (frameSMulLinEquiv K E R ι n h).symm.toLinearMap }

@[simp]
theorem frameSMulHom_apply (h : GL ι (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameSMulHom K E R ι n h X = frameSMul (h : Matrix ι ι (R ⊗[K] E)) X :=
  frameSMulLin_apply _ X

variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]


end FrameSMul

section Unitary

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

variable (K E R) in

def conjBaseAlgEquiv : (R ⊗[K] E) ≃ₐ[R] (R ⊗[K] E) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (conj K E)




variable [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]



end Unitary

section Gram

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem gram_mul_right (Q : Matrix ι ι E) (X : Matrix ι (Fin n) (R ⊗[K] E))
    (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    IsoFrames.gram K E R Q (X * g) = cTr K E R g * IsoFrames.gram K E R Q X * g := by
  rw [IsoFrames.gram, IsoFrames.gram, Chart.framePair_mul_left, Chart.framePair_mul_right,
    Matrix.mul_assoc]
  rfl




end Gram

section UnitaryHaar

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}


end UnitaryHaar

section Congr

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {n : ℕ}

theorem cTr_mul {l m k : Type*} [Fintype m] (M : Matrix l m (R ⊗[K] E)) (N : Matrix m k (R ⊗[K] E)) :
    cTr K E R (M * N) = cTr K E R N * cTr K E R M :=
  Chart.cT_mul M N

theorem cTr_cTr {l m : Type*} (M : Matrix l m (R ⊗[K] E)) : cTr K E R (cTr K E R M) = M :=
  Chart.cT_cT M

theorem cTr_one {m : Type*} [DecidableEq m] : cTr K E R (1 : Matrix m m (R ⊗[K] E)) = 1 :=
  Chart.cT_one

theorem HermSp.cTr_mat (S : HermSp K E R n) : cTr K E R S.mat = S.mat := S.2

theorem HermSp.ext' {S S' : HermSp K E R n} (h : S.mat = S'.mat) : S = S' := Subtype.ext h

theorem congr_mem (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) :
    cTr K E R g * S.mat * g ∈ hermSub K E R n := by
  show cTr K E R (cTr K E R g * S.mat * g) = cTr K E R g * S.mat * g
  rw [cTr_mul, cTr_mul, cTr_cTr, HermSp.cTr_mat, Matrix.mul_assoc]

def congrPt (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) : HermSp K E R n :=
  ⟨cTr K E R g * S.mat * g, congr_mem g S⟩

@[simp]
theorem congrPt_mat (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) :
    (congrPt g S).mat = cTr K E R g * S.mat * g := rfl

theorem congrPt_congrPt (g h : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) :
    congrPt g (congrPt h S) = congrPt (h * g) S := by
  refine HermSp.ext' ?_
  simp only [congrPt_mat, cTr_mul, Matrix.mul_assoc]

theorem congrPt_one (S : HermSp K E R n) : congrPt 1 S = S := by
  refine HermSp.ext' ?_
  simp only [congrPt_mat, cTr_one, Matrix.one_mul, Matrix.mul_one]

theorem congrPt_add (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S S' : HermSp K E R n) :
    congrPt g (S + S') = congrPt g S + congrPt g S' := by
  refine HermSp.ext' ?_
  show cTr K E R g * (S.mat + S'.mat) * g = cTr K E R g * S.mat * g + cTr K E R g * S'.mat * g
  rw [Matrix.mul_add, Matrix.add_mul]

theorem continuous_congrPt (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    Continuous (congrPt (K := K) (E := E) (R := R) g) :=
  have hc : Continuous (fun S : HermSp K E R n ↦ S.mat) := continuous_induced_dom
  continuous_induced_rng.2 ((continuous_const.matrix_mul hc).matrix_mul continuous_const)

variable (K E R n) in

def congrHom (g : GL (Fin n) (R ⊗[K] E)) : HermSp K E R n ≃ₜ+ HermSp K E R n where
  toFun := congrPt (g : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  invFun := congrPt ((g⁻¹ : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  left_inv S := by rw [congrPt_congrPt, Units.mul_inv, congrPt_one]
  right_inv S := by rw [congrPt_congrPt, Units.inv_mul, congrPt_one]
  map_add' := congrPt_add _
  continuous_toFun := continuous_congrPt _
  continuous_invFun := continuous_congrPt _

@[simp]
theorem congrHom_mat (g : GL (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) :
    (congrHom K E R n g S).mat = cTr K E R (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) * S.mat *
      (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) := rfl

variable (K E R n) in

def ctGL (g : GL (Fin n) (R ⊗[K] E)) : GL (Fin n) (R ⊗[K] E) where
  val := cTr K E R (g : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  inv := cTr K E R ((g⁻¹ : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  val_inv := by rw [← cTr_mul, Units.inv_mul, cTr_one]
  inv_val := by rw [← cTr_mul, Units.mul_inv, cTr_one]

def congrAll (g : GL (Fin n) (R ⊗[K] E)) :
    FrameSp K E R (Fin n) n ≃ₜ+ FrameSp K E R (Fin n) n :=
  (frameSMulHom K E R (Fin n) n (ctGL K E R n g)).trans (frameMulHom K E R (Fin n) n g)


variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]


end Congr

section Split

variable {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {n : ℕ}

theorem exists_conj_eq_neg_swm : ∃ δ : E, δ ≠ 0 ∧ conj K E δ = -δ := by
  have hx : ∃ x : E, x ∉ Set.range (algebraMap K E) := by
    by_contra h
    push Not at h
    have hbij : Function.Bijective (Algebra.linearMap K E) :=
      ⟨(algebraMap K E).injective, fun y ↦ h y⟩
    have h1 := (LinearEquiv.ofBijective (Algebra.linearMap K E) hbij).finrank_eq
    rw [Module.finrank_self, Algebra.IsQuadraticExtension.finrank_eq_two] at h1
    norm_num at h1
  obtain ⟨x, hx⟩ := hx
  refine ⟨x - conj K E x, ?_, ?_⟩
  · intro h0
    apply hx
    refine ⟨(2 : K)⁻¹ * Algebra.trace K E x, ?_⟩
    have h1 := add_conj (F := K) x
    have h2 : conj K E x = x := (sub_eq_zero.1 h0).symm
    rw [h2] at h1
    rw [map_mul, ← h1, ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap K E) 2, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero' K), map_one, one_mul]
  · rw [map_sub, conj_conj]
    ring

variable (K E R) in

def epsU : (R ⊗[K] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E).toMonoidHom
    (Units.mk0 (exists_conj_eq_neg_swm (K := K) (E := E)).choose
      (exists_conj_eq_neg_swm (K := K) (E := E)).choose_spec.1)

theorem conjBase_epsU : conjBase K E R (epsU K E R : R ⊗[K] E) = -(epsU K E R : R ⊗[K] E) := by
  show conjBase K E R ((1 : R) ⊗ₜ[K] (exists_conj_eq_neg_swm (K := K) (E := E)).choose) =
    -((1 : R) ⊗ₜ[K] (exists_conj_eq_neg_swm (K := K) (E := E)).choose)
  rw [conjBase_tmul, (exists_conj_eq_neg_swm (K := K) (E := E)).choose_spec.2, TensorProduct.tmul_neg]

theorem conjBase_epsU_inv :
    conjBase K E R ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ) = -((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ) := by
  have h1 := congrArg (conjBase K E R) (Units.inv_mul (epsU K E R))
  rw [map_mul, conjBase_epsU, map_one] at h1
  have h2 := Units.mul_inv (epsU K E R)
  linear_combination (-(conjBase K E R ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ))) * h2 -
    ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ) * h1

abbrev halfA (K E R : Type*) [Field K] [Field E] [Algebra K E] [CommRing R] [Algebra K R] :
    R ⊗[K] E := algebraMap K (R ⊗[K] E) (2 : K)⁻¹

theorem two_mul_halfA : (2 : R ⊗[K] E) * halfA K E R = 1 := by
  rw [halfA, ← map_ofNat (algebraMap K (R ⊗[K] E)) 2, ← map_mul,
    mul_inv_cancel₀ (two_ne_zero' K), map_one]

theorem conjBase_halfA : conjBase K E R (halfA K E R) = halfA K E R := by
  rw [halfA, Algebra.algebraMap_eq_smul_one, Chart.conjBase_smul, map_one]

theorem cTr_apply {l m : Type*} (M : Matrix l m (R ⊗[K] E)) (i : m) (j : l) :
    cTr K E R M i j = conjBase K E R (M j i) := rfl

theorem HermSp.mat_apply_swap (S : HermSp K E R n) (i j : Fin n) :
    conjBase K E R (S.mat j i) = S.mat i j := by
  have := congrFun (congrFun (HermSp.cTr_mat S) i) j
  rwa [cTr_apply] at this

def hPartM (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E) :=
  halfA K E R • (X + cTr K E R X)

def sPartM (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E) :=
  (halfA K E R * ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ)) • (X - cTr K E R X)

theorem hPartM_mem (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)) : hPartM X ∈ hermSub K E R n := by
  show cTr K E R (hPartM X) = hPartM X
  ext i j
  simp only [hPartM, cTr_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_mul, map_add,
    conjBase_halfA, Chart.conjBase_conjBase]
  ring

theorem sPartM_mem (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)) : sPartM X ∈ hermSub K E R n := by
  show cTr K E R (sPartM X) = sPartM X
  ext i j
  simp only [sPartM, cTr_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul, map_sub,
    conjBase_halfA, conjBase_epsU_inv, Chart.conjBase_conjBase]
  ring

variable (K E R n) in

def splitHom : (HermSp K E R n × HermSp K E R n) ≃ₜ+ FrameSp K E R (Fin n) n where
  toFun p := (p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  invFun X := (⟨hPartM (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)), hPartM_mem _⟩,
    ⟨sPartM (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)), sPartM_mem _⟩)
  left_inv p := by
    refine Prod.ext (HermSp.ext' ?_) (HermSp.ext' ?_)
    · ext i j
      show hPartM (p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat) i j = p.1.mat i j
      simp only [hPartM, cTr_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_add,
        map_mul, conjBase_epsU, HermSp.mat_apply_swap]
      linear_combination (p.1.mat i j) * (two_mul_halfA (K := K) (E := E) (R := R))
    · ext i j
      show sPartM (p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat) i j = p.2.mat i j
      simp only [sPartM, cTr_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
        smul_eq_mul, map_add, map_mul, conjBase_epsU, HermSp.mat_apply_swap]
      linear_combination (p.2.mat i j) * (two_mul_halfA (K := K) (E := E) (R := R)) +
        (2 * halfA K E R * p.2.mat i j) * Units.inv_mul (epsU K E R)
  right_inv X := by
    refine Matrix.ext fun i j ↦ ?_
    show (hPartM (Chart.toM X) + (epsU K E R : R ⊗[K] E) • sPartM (Chart.toM X)) i j =
      Chart.toM X i j
    simp only [hPartM, sPartM, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (Chart.toM X i j) * (two_mul_halfA (K := K) (E := E) (R := R)) +
      (halfA K E R * (Chart.toM X i j - cTr K E R (Chart.toM X) i j)) *
        Units.mul_inv (epsU K E R)
  map_add' p q := by
    show ((p.1 + q.1).mat + (epsU K E R : R ⊗[K] E) • (p.2 + q.2).mat : Matrix (Fin n) (Fin n) _) =
      (p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat) + (q.1.mat + (epsU K E R : R ⊗[K] E) • q.2.mat)
    rw [show (p.1 + q.1).mat = p.1.mat + q.1.mat from rfl,
      show (p.2 + q.2).mat = p.2.mat + q.2.mat from rfl, smul_add]
    abel
  continuous_toFun := by
    have hc : Continuous (fun S : HermSp K E R n ↦ S.mat) := continuous_induced_dom
    exact (hc.comp continuous_fst).add ((continuous_const_smul (epsU K E R : R ⊗[K] E)).comp
      (hc.comp continuous_snd))
  continuous_invFun := by
    have hct : Continuous (fun X : FrameSp K E R (Fin n) n ↦ cTr K E R (Chart.toM X)) :=
      (continuous_id.matrix_map (continuous_conjBase R)).matrix_transpose
    refine Continuous.prodMk ?_ ?_
    · refine continuous_induced_rng.2 ?_
      show Continuous fun X : FrameSp K E R (Fin n) n ↦
        halfA K E R • (Chart.toM X + cTr K E R (Chart.toM X))
      exact (continuous_const_smul _).comp
        ((show Continuous (fun X : FrameSp K E R (Fin n) n ↦ Chart.toM X) from continuous_id).add hct)
    · refine continuous_induced_rng.2 ?_
      show Continuous fun X : FrameSp K E R (Fin n) n ↦
        (halfA K E R * ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ)) •
          (Chart.toM X - cTr K E R (Chart.toM X))
      exact (continuous_const_smul _).comp
        ((show Continuous (fun X : FrameSp K E R (Fin n) n ↦ Chart.toM X) from continuous_id).sub hct)

theorem splitHom_apply (p : HermSp K E R n × HermSp K E R n) :
    Chart.toM (splitHom K E R n p) = p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat := rfl


variable (K E R n) in

def congrPair (g : GL (Fin n) (R ⊗[K] E)) :
    (HermSp K E R n × HermSp K E R n) ≃ₜ+ (HermSp K E R n × HermSp K E R n) where
  toFun p := (congrHom K E R n g p.1, congrHom K E R n g p.2)
  invFun p := ((congrHom K E R n g).symm p.1, (congrHom K E R n g).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp [map_add]
  continuous_toFun := (congrHom K E R n g).continuous.prodMap (congrHom K E R n g).continuous
  continuous_invFun :=
    (congrHom K E R n g).symm.continuous.prodMap (congrHom K E R n g).symm.continuous

variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]

open Measure in
theorem addEquivAddHaarChar_congrPair (g : GL (Fin n) (R ⊗[K] E)) :
    addEquivAddHaarChar (congrPair K E R n g) = addEquivAddHaarChar (congrHom K E R n g) ^ 2 := by
  set φ := congrHom K E R n g
  let μ : Measure (HermSp K E R n) := addHaar
  let P : Measure (HermSp K E R n × HermSp K E R n) := μ.prod μ
  obtain ⟨U, hUc, hU0⟩ : ∃ U : Set (HermSp K E R n), IsCompact U ∧ U ∈ 𝓝 (0 : HermSp K E R n) :=
    exists_compact_mem_nhds 0
  have hφU0 : φ ⁻¹' U ∈ 𝓝 (0 : HermSp K E R n) := by
    have hc : Tendsto (fun x ↦ φ x) (𝓝 0) (𝓝 (φ 0)) := φ.continuous.tendsto 0
    rw [map_zero] at hc
    exact hc hU0
  have hφUc : IsCompact (φ ⁻¹' U) := φ.toHomeomorph.isCompact_preimage.2 hUc
  have hpre : ⇑(congrPair K E R n g) ⁻¹' (U ×ˢ U) = (φ ⁻¹' U) ×ˢ (φ ⁻¹' U) := by
    ext p; rfl
  have hpos : μ (φ ⁻¹' U) ≠ 0 := (measure_pos_of_mem_nhds μ hφU0).ne'
  have hfin : μ (φ ⁻¹' U) ≠ ∞ := hφUc.measure_lt_top.ne
  have hs := addEquivAddHaarChar_smul_preimage μ (X := U) φ
  rw [ENNReal.smul_def, smul_eq_mul] at hs
  refine WmSysEquiv.addEquivAddHaarChar_eq_of_preimage P _ (S := U ×ˢ U) ?_ ?_ ?_
  · rw [hpre, Measure.prod_prod]
    exact mul_ne_zero hpos hpos
  · rw [hpre, Measure.prod_prod]
    exact ENNReal.mul_ne_top hfin hfin
  · rw [hpre, Measure.prod_prod, Measure.prod_prod, ← hs, ENNReal.coe_pow]
    ring


end Split

section Joint

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}




variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]



end Joint

section Places

open NumberField IsDedekindDomain


variable {K : Type*} [Field K] [NumberField K]


theorem not_discreteTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    ¬ DiscreteTopology (v.adicCompletion K) := by
  intro hd
  have hfin := (GroundTheory.Global.isCompact_adicCompletionIntegers v).finite_of_discrete
  have hinj : Function.Injective (fun k : ℕ ↦ (k : v.adicCompletion K)) := by
    intro a b hab
    have : algebraMap K (v.adicCompletion K) (a : K) = algebraMap K (v.adicCompletion K) (b : K) := by
      simpa [map_natCast] using hab
    exact_mod_cast (algebraMap K (v.adicCompletion K)).injective this
  exact Set.infinite_of_injective_forall_mem hinj
    (fun k ↦ natCast_mem (v.adicCompletionIntegers K) k) hfin


theorem secondCountableTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K) :=
  locField_secondCountable (not_discreteTopology_adicCompletion v)

end Places

end SwmCone

end GroundTheory.Heights₂.Theta
end
end
