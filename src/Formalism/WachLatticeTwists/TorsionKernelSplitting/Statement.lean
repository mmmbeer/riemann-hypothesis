import Formalism.WachLatticeTwists.CoprimeLiftBounds.WachTwistTheorem
import Formalism.WachLatticeTwists.Statement

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

def StatRowCost : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Cs : Type) [AddCommGroup Cs] [Module O Cs] (Fs Im : Submodule O Cs)
    (rr : Type) [Fintype rr] (ℓ e c J : ℕ),
    Module.Finite O Fs →
    (∀ x ∈ Fs, ((ℓ : O) ^ e) • x ∈ Im) →
    (∃ H : Submodule O (rr → KO O), (∀ x ∈ H, ((ℓ : O) ^ c) • x = 0) ∧
      Module.length O (Submodule.torsion O Fs) ≤ Module.length O H) →
    Module.finrank O Fs ≤ J →
    Module.length O (Fs ⧸ Im.comap Fs.subtype) ≤
      (J : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) +
        (Fintype.card rr : ℕ∞) * ((c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}))

def StatSplitFold : Prop :=
  ∀ (v : ℕ∞) (what₂ cols : Finset ℕ) (conj : ℕ → ℕ) (lenRow a x c h y₁ y₂ : ℕ → ℕ∞) (j J : ℕ → ℕ)
    (R : ℕ∞),
    v ≤ ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, (a w + (j w : ℕ∞) * x w + c w + h w) + R →
    what₂ = cols.image conj → (∀ w ∈ cols, j w ≤ J w) →
    (∀ w ∈ cols, lenRow (conj w) ≤ y₁ w + y₂ w) →
    v ≤ ∑ w ∈ cols, (a w + (J w : ℕ∞) * x w + c w + h w + y₁ w + y₂ w) + R

end Formalism.RepresentationBoundsCohomology.JS
