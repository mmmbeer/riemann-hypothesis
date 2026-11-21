import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication

def jetOfSeries {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ) (f : MvPowerSeries κ R) :
    JetR R κ m :=
  Ideal.Quotient.mk _ (MvPowerSeries.truncTotal (m + 1) f)

def IsOriginChart {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] {d : ℕ}
    (x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) (F : FGLaw R d) : Prop :=
  (∀ m, algOverHom (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧
  (∀ m, algOverHom (jetZeroR R (Fin d) m) ≫ x m = toUnit _ ≫ η[G]) ∧
  (∀ (κ : Type) (m : ℕ) (y : algOver R (JetR R κ m) ⟶ G),
    algOverHom (jetZeroR R κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m,
      (∀ j, jetZeroR R κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m) ∧
  (∀ m, ∃ ψ₀ ψ₁ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
    (∀ j, ψ₀ (zR m j) = zR m ((0 : Fin 2), j)) ∧ (∀ j, ψ₁ (zR m j) = zR m ((1 : Fin 2), j)) ∧
    (∀ j, ψ (zR m j) = jetOfSeries m (F.F j)) ∧
    lift (algOverHom ψ₀ ≫ x m) (algOverHom ψ₁ ≫ x m) ≫ μ[G] = algOverHom ψ ≫ x m)

def mulSeries {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ) : Pt R 1 d :=
  Nat.rec (motive := fun _ => Pt R 1 d) 0 (fun _ a => F.add a (pt R d 0)) n

theorem mulSeries_zero {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) : mulSeries F 0 = 0 := rfl

theorem mulSeries_succ {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ) :
    mulSeries F (n + 1) = F.add (mulSeries F n) (pt R d 0) := rfl

theorem mulSeries_one {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) :
    mulSeries F 1 = pt R d 0 := by
  funext i
  exact F.unit i

theorem constantCoeff_mulSeries {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ)
    (i : Fin d) : MvPowerSeries.constantCoeff (mulSeries F n i) = 0 := by
  induction n generalizing i with
  | zero => simp [mulSeries_zero]
  | succ n ih =>
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulSeries F n, pt R d 0] : Fin 2 → Pt R 1 d) q.1 q.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a
      · exact ih j
      · simp [pt]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h) h (F.const i)

def torsionIdeal {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d)
    (n : ℕ) : Ideal (PS O 1 d) :=
  Ideal.span (Set.range fun i : Fin d => MvPowerSeries.map f (mulSeries F n i))

abbrev TorsionRing {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d)
    (n : ℕ) : Type :=
  PS O 1 d ⧸ torsionIdeal f F n

example {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d) :
    torsionIdeal f F 1 = Ideal.span (Set.range (pt O d (0 : Fin 1))) := by
  unfold torsionIdeal
  rw [mulSeries_one]
  unfold pt
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
