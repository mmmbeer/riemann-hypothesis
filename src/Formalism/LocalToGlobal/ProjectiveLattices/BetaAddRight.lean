import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure DatAt (Y : Model Xo c β) {p : ℕ} {C : SCF p} (P : PointsOfFlagModel.PtC Y C) : Type 1 where
  R : Type
  [ring : CommRing R]
  [dom : IsDomain R]
  [loc : IsLocalRing R]
  [ch0 : CharZero R]
  noeth : IsNoetherianRing R
  normal : IsIntegrallyClosed R
  complete : IsAdicComplete (maximalIdeal R) R
  ι : Sp R ⟶ Y.X
  f : R →+* intO ↥C.S
  f_loc : ∀ a ∈ maximalIdeal R, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1
  fac : spMap f ≫ ι = P.yt
  t : SAB H (Sp R)
  m : SABMap t Y.t ι
  U : PELUnif (maximalIdeal R) t
  unitOn : ∀ y, PsiUnitOn U.D.toPre y (ι ⁻¹' abLocus Y.t.G)
  tors : U.TorsionIso

attribute [instance] DatAt.ring DatAt.dom DatAt.loc DatAt.ch0

namespace DatAt

variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

abbrev Ylat (A : DatAt Y P) : Type := A.U.D.toPre.X

def beta (A : DatAt Y P) (a b : A.Ylat) : ℝ :=
  betaAt A.U.D.toPre ((intO ↥C.S).subtype.comp A.f) p a b


theorem beta_symm (A : DatAt Y P) (a b : A.Ylat) : A.beta a b = A.beta b a :=
  betaAt_symm _ _ _ a b

end DatAt

end Formalism.L2.Pj
end
end

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def N3AtPoints (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C), Nonempty (DatAt Y P)

def BetaAdd (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P) (a a' b : A.Ylat),
    A.beta (a + a') b = A.beta a b + A.beta a' b

def BetaBal (Y : Model Xo c β) (p : ℕ) (cj : E → E) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P) (x x' : 𝓞 E), (x' : E) = cj (x : E) →
    ∀ a b : A.Ylat, A.beta (x • a) b = A.beta a (x' • b)

def BetaPosDef (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P),
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.Ylat),
      ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * A.beta (b i) (b k)

def YlRank (Y : Model Xo c β) (p : ℕ) (r j : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P), ∃ ρ : ℕ,
    Module.finrank ℤ A.Ylat = 2 * (Module.finrank ℚ E / 2) * ρ ∧ (1 ≤ j → j + 1 ≤ r → ρ ≤ j ∧ ρ + j ≤ r)

namespace DatAt

variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem beta_add_right (hA : BetaAdd Y p) (A : DatAt Y P) (a b b' : A.Ylat) :
    A.beta a (b + b') = A.beta a b + A.beta a b' := by
  rw [A.beta_symm, hA C P A, A.beta_symm b, A.beta_symm b']

def beLin (hA : BetaAdd Y p) (A : DatAt Y P) : A.Ylat →ₗ[ℤ] A.Ylat →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => A.beta a b)
      (fun b b' => A.beta_add_right hA a b b')).toIntLinearMap)
    (fun a a' => by
      ext b
      simp [hA C P A a a' b])).toIntLinearMap

theorem beLin_apply (hA : BetaAdd Y p) (A : DatAt Y P) (a b : A.Ylat) : A.beLin hA a b = A.beta a b := rfl

end DatAt

end Formalism.L2.Pj
end
end
