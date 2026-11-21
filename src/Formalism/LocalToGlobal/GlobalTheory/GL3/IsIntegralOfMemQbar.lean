import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Formalism.LocalToGlobal.GlobalTheory.GL3.ProvisionExtensionLink
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

def AlgCoef (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : Prop :=
  ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D G M

def ZeroAlg : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ N N' : ℕ, Even N → Even N' → AlgCoef D (B.thZero N N')

def TransAlg : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
      ∀ G : VC D N N' → ℂ, G ∈ Th D (tor0 D cc δ) L₁ L₁' → AlgCoef D G →
        ∀ x ∈ La D (tor0 D cc δ) L₂ L₂', AlgCoef D (U D (tor0 D cc δ) x G)

def LinkVecCoef : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ : IdE D → ℂ, IsChi D χ → TaylorCoeffsInNumberField D (B.eNat χ)

section Coef

variable {D : D7} {N N' : ℕ}


theorem taylor_lin {ι : Type*} [Fintype ι] (r : ι → ℂ) (F : ι → VC D N N' → ℂ)
    (hF : ∀ k (m : ℕ), ContDiff ℂ m (F k)) (α : Mono D N N') :
    taylor D (fun z => ∑ k, r k * F k z) α = ∑ k, r k * taylor D (F k) α := by
  unfold taylor
  have h1 : (fun z => ∑ k, r k * F k z) = fun z => ∑ k ∈ Finset.univ, r k • F k z := rfl
  rw [h1, iteratedFDeriv_sum (fun k _ => (hF k _).const_smul (r k)), Finset.sum_apply, _root_.sum_apply,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun x => r k • F k x) = r k • F k := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((hF k _).contDiffAt), _root_.smul_apply, smul_eq_mul, mul_div_assoc]








end Coef



end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

end
end
