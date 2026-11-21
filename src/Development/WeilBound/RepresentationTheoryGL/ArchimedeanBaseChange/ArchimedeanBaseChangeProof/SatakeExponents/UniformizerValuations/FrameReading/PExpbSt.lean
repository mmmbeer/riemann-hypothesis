import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.BS

def hkS {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (f : G → ℂ) (v : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v

def JacHk : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ u ∈ fixed π (iwahori k (Fin n)),
      (Submodule.Quotient.mk (hkS π (iwahori k (Fin n))
          (fun g => if ∃ a ∈ iwahori k (Fin n), ∃ b ∈ iwahori k (Fin n),
            g = a * diagT k (Fin n) (fun i => ϖ ^ x i) * b then (1 : ℂ) else 0) u) :
        Jacquet π (unipB k (Fin n))) =
      ((Nat.card 𝓀[k] : ℂ) ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i)) •
        jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u)

def JacEig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GLw n w) V), IsSmooth π →
    ∀ (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (ξ : Fin n → ℂˣ) (c : ℂ) (x : Fin n → ℤ),
    StrictAnti x → ∀ u ∈ fixed π (iwGL n w),
      hkS π (iwGL n w) (dcos n w (tdiag ϖ x)) u =
        (c * (qh w ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i) * pw ξ x)) • u →
      jacB π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) =
        (c * pw ξ x) • (Submodule.Quotient.mk u : Jacquet π (unipB (w.adicCompletion E) (Fin n)))

end PositivityTheory.Rg.BcB.F.Tail.BS

end
