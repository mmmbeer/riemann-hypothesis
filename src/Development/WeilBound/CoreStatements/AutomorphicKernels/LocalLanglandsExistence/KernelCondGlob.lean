import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCond
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

section Defs

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

def KernelCondTw {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle) (Z : Set ℂˣ) : Prop :=
  ∀ (r : ℕ) (L : Fin r → Type) [∀ i, Field (L i)] [∀ i, NumberField (L i)] [∀ i, Algebra (L i) Ω]
    [∀ i, IsAlgClosure (L i) Ω] [∀ i, Algebra K (L i)] [∀ i, IsScalarTower K (L i) Ω]
    (v' : ∀ i, HeightOneSpectrum (𝓞 (L i))) (h' : ∀ i, IsPlaceOver A (v' i)), (∀ i, IsLocalExt (L i) h) →
    ∀ (ψ' : ∀ i, AddChar ((v' i).adicCompletion (L i)) Circle), (∀ i, Continuous (ψ' i)) →
    (∀ i (z : L i), ψ' i (algebraMap (L i) _ z) = ψ (algebraMap K _ (Algebra.trace K (L i) z))) →
    ∀ (a : ∀ i, Weil (h' i) →* ((v' i).adicCompletion (L i))ˣ) (ha : ∀ i, IsLocalArtin (h' i) (a i))
      (χ : ∀ i, ((v' i).adicCompletion (L i))ˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i)) (c : Fin r → ℤ)
      (x x₀ : Fin r → WD h),
      (∃ z ∈ Z, ∃ φ : ∀ i, ((v' i).adicCompletion (L i))ˣ →* ℂˣ, (∀ i, IsOfFinOrder (φ i)) ∧
        ∀ i (σ' : Weil (h' i)) (σ : Weil h), (∀ w : Ω, (σ : G K Ω) w = (σ' : G (L i) Ω) w) →
          χ i (a i σ') = φ i (a i σ') * GlobalTheory.WeilDeligne.unrChar h z σ) →
      (∀ i, Induces (WD.lpOfChar (h' i) ((χ i).comp (a i)) ((ha i).smooth (hχ i))) (x i)) →
      (∀ i, Induces (WD.lpOfChar (h' i) ((1 : ((v' i).adicCompletion (L i))ˣ →* ℂˣ).comp (a i))
        ((ha i).smooth (isSmoothChar_of_isUnram fun _ _ => rfl))) (x₀ i)) →
      (∀ σ, ∏ i, (x i).charPol σ ^ (c i).toNat * (x₀ i).charPol σ ^ (-c i).toNat =
        ∏ i, (x₀ i).charPol σ ^ (c i).toNat * (x i).charPol σ ^ (-c i).toNat) →
      ∀ (t : ℝ) (e e₀ : Fin r → ℂ), 0 < t → (∀ i, IsTateMeas (ψ' i) t (χ i) (e i)) →
        (∀ i, IsTateMeas (ψ' i) t 1 (e₀ i)) → ∏ i, (e i / e₀ i) ^ (c i) = 1

def KernelCondGlob {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle)
    (F' : IntermediateField K Ω) : Prop :=
  ∀ (r : ℕ) (L : Fin r → Type) [∀ i, Field (L i)] [∀ i, NumberField (L i)] [∀ i, Algebra (L i) Ω]
    [∀ i, IsAlgClosure (L i) Ω] [∀ i, Algebra K (L i)] [∀ i, IsScalarTower K (L i) Ω]
    (v' : ∀ i, HeightOneSpectrum (𝓞 (L i))) (h' : ∀ i, IsPlaceOver A (v' i)), (∀ i, IsLocalExt (L i) h) →
    (∀ i (y : L i), algebraMap (L i) Ω y ∈ F') →
    ∀ (ψ' : ∀ i, AddChar ((v' i).adicCompletion (L i)) Circle), (∀ i, Continuous (ψ' i)) →
    (∀ i (z : L i), ψ' i (algebraMap (L i) _ z) = ψ (algebraMap K _ (Algebra.trace K (L i) z))) →
    ∀ (a : ∀ i, Weil (h' i) →* ((v' i).adicCompletion (L i))ˣ) (ha : ∀ i, IsLocalArtin (h' i) (a i))
      (χ : ∀ i, ((v' i).adicCompletion (L i))ˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
      (hfin : ∀ i, IsOfFinOrder (χ i))
      (hker : ∀ i (σ' : Weil (h' i)), (∀ y ∈ F', ((σ' : Weil (h' i)) : G (L i) Ω) y = y) → χ i (a i σ') = 1)
      (c : Fin r → ℤ)
      (x x₀ : Fin r → WD h),
      (∀ i, Induces (WD.lpOfChar (h' i) ((χ i).comp (a i)) ((ha i).smooth (hχ i))) (x i)) →
      (∀ i, Induces (WD.lpOfChar (h' i) ((1 : ((v' i).adicCompletion (L i))ˣ →* ℂˣ).comp (a i))
        ((ha i).smooth (isSmoothChar_of_isUnram fun _ _ => rfl))) (x₀ i)) →
      (∀ σ, ∏ i, (x i).charPol σ ^ (c i).toNat * (x₀ i).charPol σ ^ (-c i).toNat =
        ∏ i, (x₀ i).charPol σ ^ (c i).toNat * (x i).charPol σ ^ (-c i).toNat) →
      ∀ (t : ℝ) (e e₀ : Fin r → ℂ), 0 < t → (∀ i, IsTateMeas (ψ' i) t (χ i) (e i)) →
        (∀ i, IsTateMeas (ψ' i) t 1 (e₀ i)) → ∏ i, (e i / e₀ i) ^ (c i) = 1

end Defs

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
