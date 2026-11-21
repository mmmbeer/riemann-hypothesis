import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA

section
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct SchwartzMap LineDeriv
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Lie

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def schV (L : V →L[ℝ] V →L[ℝ] ℝ) (a b : V) (φ : V → ℂ) : V → ℂ :=
  fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((L x b + L a b / 2 : ℝ) : ℂ)) * φ (x + a)

variable [MeasurableSpace V]

def IsSchL (L : V →L[ℝ] V →L[ℝ] ℝ) (μ : Measure V) (ρ₀ : V → V → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ a b (h : Lp ℂ 2 μ), ρ₀ a b h =ᵐ[μ] schV L a b h

end Real

section Arch

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def trL (κ : Type) [Fintype κ] : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap (LinearMap.mk₂ ℝ
    (fun x y : κ → mixedEmbedding.mixedSpace F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by rw [← map_add, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_mul])
    (fun c x y => by rw [← map_smul, Finset.smul_sum]; simp only [Pi.smul_apply, smul_mul_assoc])
    (fun x y y' => by rw [← map_add, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, mul_add])
    (fun c x y => by rw [← map_smul, Finset.smul_sum]; simp only [Pi.smul_apply, mul_smul_comm]))

variable (F) in

abbrev Ix (n d : ℕ) : Type := InfinitePlace F × Fin n × Fin d

open Classical in

def HM (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) :
    Matrix (Ix F n d) (Ix F n d) ℂ :=
  fun p q => if p.1 = q.1 then 2 * Complex.I * (τ p.1).1 (JX q.2.1 p.2.1) * (τ p.1).1 (JW q.2.2 p.2.2) else 0

open Classical in

def mM (τ : ∀ w : InfinitePlace F, EmbOver E w) (n : ℕ) {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix (Ix F n d) (Ix F n d) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then piInf (τ p.1) (g p.2.2 q.2.2) else 0

end Arch

end GlobalTheory.CompanionTheory.Ar.RT.Lie

end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct SchwartzMap LineDeriv ContDiff Matrix Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT.Lie

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Lie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem conj_extensionEmbedding_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (y : w.Completion) :
    starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w y) =
      InfinitePlace.Completion.extensionEmbedding w y := by
  refine InfinitePlace.Completion.induction_on w y ?_ ?_
  · exact isClosed_eq
      (Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous)
      (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  · intro a
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have h := RingHom.congr_fun (InfinitePlace.isReal_iff.mp hw) ((WithAbs.equiv _) a)
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using h

theorem piInf_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (x : AE F E) :
    piInf τ (cA σ x) = (starRingEnd ℂ) (piInf τ x) := by
  obtain ⟨hF, -, -, hστ⟩ := h
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, GlobalTheory.AdelicU.compInf, GlobalTheory.AdelicU.infEmb]
    rw [hστ]
    have hc := conj_extensionEmbedding_of_isReal (hF.isReal w) ((evInf F w) a)
    erw [hc]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.AdelicU.infEmb, GlobalTheory.AdelicU.compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

end GlobalTheory.CompanionTheory.Ar.RT.Lie

end
end
