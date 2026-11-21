import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt

noncomputable section

namespace Formalism.CohomologicalDescent.Down

section SLD

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD

end SLD

section SLD2

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD

end SLD2

section SF06

open CategoryTheory CategoryTheory.Limits
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

end SF06

section SF07

open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative

open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def BlockIdealAt : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (l : ℕ)
    (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (lam : ι → ℕ → ℕ)
    [Module A (NablaT O D.Nr lam)] [IsScalarTower O A (NablaT O D.Nr lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O D.Nr lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O D.Nr lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin D.Nr → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin D.Nr → ℕ),
    D.Params →
    TopInputs O A Γ jK l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
      (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e L hwt →
    (∀ τ ∈ D.T2, D.maxB τ = UN D.Nr (lam τ) (D.k + D.j τ)) →
    D.J l ≤ sInf {J : ℕ | TopIncl O Γ jK l D.Nr lam S J} →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (Cor.coefficientBoundTau D τ l) else (D.ex τ l : ℝ))

open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def BlockIdealBound5Derived : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), D.Params →
    (∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
      D.t + 2 * D.kap l < l →
      ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (A : Type) (_ : Ring A)
        (_ : Algebra O A) (G : Type) (_ : Group G) (Γ K : Subgroup G) (jK : K →* A) (lam : ι → ℕ → ℕ)
        (_ : Module A (NablaT O D.Nr lam)) (_ : IsScalarTower O A (NablaT O D.Nr lam)) (T : Type)
        (_ : CommRing T) (_ : Algebra O T) (_ : Module T (Forms O Γ jK (NablaT O D.Nr lam)))
        (_ : IsScalarTower O T (Forms O Γ jK (NablaT O D.Nr lam))) (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
        (e : ι → (Fin D.Nr → ℕ) → A) (Λ : Type) (L : Λ → Type) (_ : ∀ μ, AddCommGroup (L μ))
        (_ : ∀ μ, Module O (L μ)) (_ : ∀ μ, Module A (L μ)) (_ : ∀ μ, IsScalarTower O A (L μ))
        (_ : ∀ μ, Module T (Forms O Γ jK (L μ))) (hwt : Λ → ι → Fin D.Nr → ℕ),
        TopInputs O A Γ jK l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
          (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e L hwt ∧
        (∀ τ ∈ D.T2, D.maxB τ = UN D.Nr (lam τ) (D.k + D.j τ)) ∧
        D.J l ≤ sInf {J : ℕ | TopIncl O Γ jK l D.Nr lam S J}) →
    Cor.BlockIdealBound5 D

end SF07

section SF09

open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

def InclWReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    P.lJ < (l : ℝ) → X.WInputs l (kc P) W.j W.T2 (W.iW P l) →
    X.Incl l (W.JW P l) ∧ X.Jmin l ≤ W.JW P l

end SF09

end Formalism.CohomologicalDescent.Down
