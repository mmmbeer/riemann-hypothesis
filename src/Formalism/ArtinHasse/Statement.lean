import Mathlib

noncomputable section

open PowerSeries

namespace Formalism.FT

abbrev hPS (R : Type*) [CommRing R] (n k : ℕ) : MvPowerSeries (Fin n) R :=
  ((MvPolynomial.hsymm (Fin n) R k : MvPolynomial (Fin n) R) : MvPowerSeries (Fin n) R)

def SymmSeriesHsymm : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (F : MvPowerSeries (Fin n) R),
    (∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F) →
    ∃! G : MvPowerSeries (Fin n) R, G.subst (fun j : Fin n => hPS R n (j.val + 1)) = F

end Formalism.FT
