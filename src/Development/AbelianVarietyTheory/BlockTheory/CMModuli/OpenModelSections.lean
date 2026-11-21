import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoefficientFieldBaseChange

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange

section Push

variable {X : Scheme.{0}} (G : Over X) (L : LB G.left)

structure IsPushGen (V : X.Opens) (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) : Prop where
  mem : θ ∈ secOn L (G.hom ⁻¹ᵁ V)
  basis : ∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! c : Γ(X, W), ∀ i,
    s i = resG G.left (inf_le_left : G.hom ⁻¹ᵁ W ⊓ L.U i ≤ G.hom ⁻¹ᵁ W) ((G.hom.app W).hom c) *
      resG G.left (inf_le_inf_right _ (fun _ hy => hW hy) : G.hom ⁻¹ᵁ W ⊓ L.U i ≤ G.hom ⁻¹ᵁ V ⊓ L.U i) (θ i)

def NonzeroOnFibre {V : X.Opens} (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) (x : X) : Prop :=
  ∃ i, ((Scheme.Hom.fiberι G.hom x).app (G.hom ⁻¹ᵁ V ⊓ L.U i)).hom (θ i) ≠ 0

structure PushInvertible : Prop where
  invertible : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ, IsPushGen G L V θ
  nonzero : ∀ (V : X.Opens) θ, IsPushGen G L V θ → ∀ x ∈ V, NonzeroOnFibre G L θ x


end Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Model {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀)
    {O : Type} [CommRing O] (φ : O →+* F₀) where

  X : Scheme.{0}

  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s

  j : baseChange str h ⟶ pullback s (spMap φ)
  j_over : j ≫ pullback.snd s (spMap φ) = baseChangeStr str h
  j_open : IsOpenImmersion j
  j_dense : Dense (Set.range j)

  t : SAB H X

  t₀ : SAB H (baseChange str h)

  toUniv : SABMap t₀ univ.t (baseChangeFst str h)

  toModel : SABMap t₀ t (j ≫ pullback.fst s (spMap φ))
  ab : ∀ y : ↥(pullback s (spMap φ)), pullback.fst s (spMap φ) y ∈ abLocus t.G ↔ y ∈ Set.range j

namespace Model

variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀} (m : Model univ h φ)

def incl : baseChange str h ⟶ m.X := m.j ≫ pullback.fst m.s (spMap φ)

theorem incl_over : m.incl ≫ m.s = baseChangeStr str h ≫ spMap φ := by
  rw [incl, Category.assoc, pullback.condition, ← Category.assoc, m.j_over]

def liftSec (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : baseChange str h ⟶ m.t₀.G.left :=
  m.toUniv.cart.1.lift σ.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w σ)

def secMap (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : baseChange str h ⟶ m.t.G.left :=
  m.liftSec σ ≫ m.toModel.φ


def Extends (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) (U : m.X.Opens) : Prop :=
  ∃ τ : Over.mk U.ι ⟶ m.t.G, (m.incl ∣_ U) ≫ τ.left = (m.incl ⁻¹ᵁ U).ι ≫ m.secMap σ

end Model

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) : Type 1 :=
  Model univ h (algebraMap (𝓞 F₀) F₀)

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) [NumberField F₀]
    (lam : IsDedekindDomain.HeightOneSpectrum (𝓞 F₀)) : Type 1 :=
  Model univ h (lam.valuation F₀).valuationSubring.subtype

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) (a : D.La) :
    Over.mk (baseChangeFst str h) ⟶ univ.t.G := toUnit _ ≫ univ.eta a

end GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
