import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

noncomputable section

namespace GlobalTheory.Core.Rk.NSing

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont

section Abstract

end Abstract

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def pairM {n : ℕ} (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (∑ a, ∑ b, S a b * T b a)

def starM (σ : E →ₐ[F] E) {m n : ℕ} (g : Matrix (Fin m) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin m) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ

variable [TopologicalSpace R] (χ : R → ℂ) (σ : E →ₐ[F] E)

end Ring

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}

def hermInf (S : HermR (AF F) σ n) : HermR (Ainf F) σ n :=
  ⟨Matrix.of fun a c => Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (S.1 a c), fun a c => by
    rw [Matrix.of_apply, Matrix.of_apply, ← S.2 a c]
    generalize S.1 c a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]⟩

def hermV (v : HeightOneSpectrum (𝓞 F)) (S : HermR (AF F) σ n) : HermR (Fv F v) σ n :=
  ⟨Matrix.of fun a c => GlobalTheory.GaugeEx.prV v (S.1 a c), fun a c => by
    rw [Matrix.of_apply, Matrix.of_apply, ← S.2 a c]
    generalize S.1 c a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [sigR, GlobalTheory.GaugeEx.prV]
    | add x y hx hy => simp only [map_add, hx, hy]⟩

def latH (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (HermR (Fv F v) σ n) :=
  {S | ∀ a c, S.1 a c ∈ GlobalTheory.GaugeEx.intV b v}

def LocInv (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) (lam : HermR R σ n → ℝ) : Prop :=
  ∃ N ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)), ∀ m ∈ N, ∀ S S' : HermR R σ n,
    S'.1 = m * S.1 * starM R σ m → lam S' = lam S

def IsIdxHgt (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : HermR (Fv F v) σ n → ℝ) : Prop :=
  ∀ μ : Measure (Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ {y | ∀ i, y i ∈ GlobalTheory.GaugeEx.intV b v} = 1 →
    ∀ S, lam S = μ.real {y | (∀ i, y i ∈ GlobalTheory.GaugeEx.intV b v) ∧ ∀ i, (S.1 *ᵥ y) i ∈ GlobalTheory.GaugeEx.intV b v}

structure IsHgt (b : Module.Basis (Fin d) F E) (ν : Measure (HermR (AF F) σ n)) (lam : HermR (AF F) σ n → ℝ)
    (li : HermR (Ainf F) σ n → ℝ) (lv : ∀ v, HermR (Fv F v) σ n → ℝ) (x₀ : ℝ) : Prop where

  prod : ∀ S, lam S = li (hermInf σ S) * ∏ᶠ v, lv v (hermV σ v S)

  inf : Continuous li ∧ ∀ S, 0 < li S

  fin : ∀ v, Continuous (lv v) ∧ ∀ S, 0 < lv v S

  poly : ∃ (C : ℝ) (N : ℕ), ∀ S, li S ≤ C * (1 + sizeTup b S.1) ^ N ∧ (li S)⁻¹ ≤ C * (1 + sizeTup b S.1) ^ N

  inv : ∀ v, LocInv (Fv F v) σ (lv v)

  unr : ∀ᶠ v in cofinite, IsIdxHgt σ b v (lv v)

  int : ∀ x : ℝ, x₀ < x → Integrable (fun S => lam S ^ x) ν

structure IsBump (b : Module.Basis (Fin d) F E) (χ : Ainf F → ℂ) (ν : Measure (HermR (Ainf F) σ n))
    (β : HermR (Ainf F) σ n → ℝ) : Prop where

  cont : Continuous β

  nonneg : ∀ S, 0 ≤ β S

  cpt : HasCompactSupport β

  mass : ∫ S, β S ∂ν = 1

  dec : ∀ N : ℕ, Integrable (fun S : HermR (Ainf F) σ n =>
    ‖∫ T, (β T : ℂ) * conj (χ (pairM (Ainf F) S.1 T.1)) ∂ν‖ * (1 + sizeTup b S.1) ^ N) ν

end Adelic

section Residue

def IsResRing (K : Type) [CommRing K] (τ : K →+* K) (q : ℕ) (ε : ℂ) : Prop :=
  (∀ x, τ (τ x) = x) ∧ Nat.card K = q ^ 2 ∧ IsUnit (2 : K) ∧
    ((IsField K ∧ (∃ x, τ x ≠ x) ∧ ε = -1) ∨
      ∃ (k : Type) (_ : Field k) (e : K ≃+* k × k), (∀ x, e (τ x) = (e x).swap) ∧ ε = 1)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}

structure ResData (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (O : Subring (Fv F v ⊗[F] E)) (ϖ : Fv F v) (K : Type) [CommRing K] (τ : K →+* K) (red : O →+* K)
    (ψ₀ : AddChar K ℂ) : Prop where

  carrier : (O : Set (Fv F v ⊗[F] E)) = GlobalTheory.GaugeEx.intV b v

  stab : ∀ x : O, ∃ h : sigR (Fv F v) σ x.1 ∈ O, red ⟨_, h⟩ = τ (red x)

  unif : Valued.v ϖ = WithZero.exp (-1 : ℤ)

  two : Valued.v (2 : Fv F v) = 1

  base : ∀ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t ∈ O ↔ t ∈ v.adicCompletionIntegers F

  surj : Function.Surjective red

  ker : ∀ x : O, red x = 0 ↔ ∃ y ∈ O, x.1 = ϖ • y

  res : IsResRing K τ (Ideal.absNorm v.asIdeal) (GlobalTheory.LFun.etaU E v : ℂˣ)

  unram : GlobalTheory.LFun.etaFam E 1 v = {GlobalTheory.LFun.etaU E v ^ 1}

  cond : ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F

  perf : ∀ y : Fv F v ⊗[F] E, (∀ x ∈ O, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (y * x) ∈ v.adicCompletionIntegers F) ↔ y ∈ O

  chr : ∀ x : O, ψ₀ (red x) =
    psiV F ψ v (ϖ⁻¹ * (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x.1))

  nontriv : ∃ x, τ x = x ∧ ψ₀ x ≠ 1

end Residue

section Datum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.MixModel
open GlobalTheory.Core.Rk.SWLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def lamA (A : HSp D) (a : GL (Fin A.rank) (AE D)) (w g : GA D (dblSp A))
    (e : HermR (AF D.host.F) D.sp.cm.sig A.rank ≃+ skewA D A.rank) (S : HermR (AF D.host.F) D.sp.cm.sig A.rank) : ℝ :=
  hgt A a (w * (dblDec A).nC (e S) * g)

end Datum

end GlobalTheory.Core.Rk.NSing

end
