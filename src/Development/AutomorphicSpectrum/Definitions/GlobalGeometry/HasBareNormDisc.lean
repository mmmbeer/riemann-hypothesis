import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GeometricComponentEmbedding

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

abbrev FracBase {O : Type} [CommRing O] (β : O →+* c.F) : Prop :=
  Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a

def Reads (U : Set (Xo.XF c)) (τ : E →+* ℂ) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) : Prop :=
  ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c),
    under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U →
    ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) →
      (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) →
      ψ (s p z) = φ F y v w

def UnitRule (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (sig : GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.Rule Y) :
    Prop :=
  ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Y.X) v w,
    GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.IsFrame Y U τ j x v w → IsUnit (sig R x v w)

def IsBareFrame {V K : Type} [CommRing V] [Field K] [Algebra V K] {y : Sp K ⟶ Xo.XF c} {𝒢 : Over (Sp V)} [GrpObj 𝒢]
    (a₁ : OAct (𝓞 E) 𝒢) {A : Over (Sp K)} (φ₀ : A.left ⟶ Xo.univ.t.G.left) (φ₁ : A.left ⟶ 𝒢.left)
    (σ : 𝓞 E →+* K) {n : ℕ} (v : Vecs y n) : Prop :=
  ∃ (σV : 𝓞 E →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ 𝒢)), (algebraMap V K).comp σV = σ ∧
    IsEigFrame a₁ (𝟙 (Sp V)) σV vV ∧ ∀ a, ∃ u : Sp (DualNumber K) ⟶ A.left,
      u ≫ φ₀ = (v a).left ∧ u ≫ φ₁ = spMap (dualMap (algebraMap V K)) ≫ (vV a).left

def BareNormOver (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ)
    (V K : Type) [CommRing V] [Field K] [Algebra V K] (j : K →+* ℂ_[p]) : Prop :=
  ∀ (β : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (𝒢 : Over (Sp V)) [GrpObj 𝒢]
    (a₁ : OAct (𝓞 E) 𝒢) (A : Over (Sp K)) [GrpObj A] (a : OAct (𝓞 E) A) (φ₀ : A.left ⟶ Xo.univ.t.G.left)
    (φ₁ : A.left ⟶ 𝒢.left), Function.Injective (algebraMap V K) →
    (∀ z : K, ‖j z‖ ≤ 1 ↔ z ∈ (algebraMap V K).range) → j.comp β = κ → IsFramed U τ β y v w → IsSemiAbelian 𝒢 →
    IsGrpPullback A Xo.univ.t.G (under y) φ₀ → IsGrpPullback A 𝒢 (spMap (algebraMap V K)) φ₁ →
    (∀ b, (a.act b).left ≫ φ₀ = φ₀ ≫ (Xo.univ.t.act.act b).left) → (∀ b, (a.act b).left ≫ φ₁ = φ₁ ≫ (a₁.act b).left) →
    IsBareFrame a₁ φ₀ φ₁ (β.comp (tauIn c τ)) v →
    IsBareFrame a₁ φ₀ φ₁ (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w →
    Real.log ‖j (φ K y v w)‖ = t

def HasBareNormDisc (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p])
    (t : ℝ) : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] (j : K →+* ℂ_[p]),
    BareNormOver U τ φ p κ t V K j

example (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) :
    UnitRule Y U τ (fun _ _ _ _ _ => 1) := fun _ _ _ _ _ _ _ => isUnit_one

end GlobalTheory.CompanionTheory.Ar.Br
