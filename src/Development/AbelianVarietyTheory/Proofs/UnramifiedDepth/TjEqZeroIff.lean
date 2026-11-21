import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.TopLimitModules.LimJMemSmulTop

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve
open ReciprocityTheory.ChartRestriction.G.Pdiv.TL

namespace GlobalTheory.JetExpansion

variable {k : Type} [CommRing k] {κ : Type} [Finite κ]

def tj (m : ℕ) : MvPowerSeries κ k →ₐ[k] JetR k κ m :=
  (MvPowerSeries.truncTotalAlgHom κ k (m + 1)).restrictScalars k

theorem tj_eq_iff (m : ℕ) (f g : MvPowerSeries κ k) :
    tj m f = tj m g ↔ ∀ x : κ →₀ ℕ, x.degree < m + 1 → MvPowerSeries.coeff x f = MvPowerSeries.coeff x g :=
  limJ_tt_eq_iff m f g

theorem tj_ext {f g : MvPowerSeries κ k} (h : ∀ m, tj m f = tj m g) : f = g := by
  ext x
  exact (tj_eq_iff x.degree f g).1 (h _) x (Nat.lt_succ_self _)

theorem tj_eq_zero_iff (m : ℕ) (f : MvPowerSeries κ k) :
    tj m f = 0 ↔ f ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ (m + 1) := by
  rw [← GlobalTheory.germIdeal_eq_span, GlobalTheory.mem_germIdeal_pow_iff, ← map_zero (tj (k := k) (κ := κ) m), tj_eq_iff]
  simp only [map_zero]

theorem exists_tj (p : ∀ m, JetR k κ m) (hp : ∀ m, jetTruncR k κ m (p (m + 1)) = p m) :
    ∃ f : MvPowerSeries κ k, ∀ m, tj m f = p m := by
  choose P hP using fun m => Ideal.Quotient.mk_surjective (p m)
  have hck : ∀ (u : κ →₀ ℕ) m, u.degree ≤ m → (P m).coeff u = (P u.degree).coeff u := by
    intro u m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [← ih]
      have h1 : (Ideal.Quotient.mk _ (P m) : JetR k κ m) = Ideal.Quotient.mk _ (P (m + 1)) := by
        rw [hP, ← hp m, ← hP]
        rfl
      exact ((limJ_mk_eq_iff m _ _).1 h1 u (by omega)).symm
  refine ⟨fun u => (P u.degree).coeff u, fun m => ?_⟩
  rw [← hP m]
  refine (limJ_mk_eq_iff m (MvPowerSeries.truncTotal (m + 1) _) _).2 fun u hu => ?_
  exact (MvPowerSeries.coeff_truncTotal _ hu).trans (hck u m (by omega)).symm

end GlobalTheory.JetExpansion
