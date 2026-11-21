import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM

namespace GlobalTheory.GenDeg

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {O : Type} [CommRing O] {β : O →+* i₀.c.F}

structure Link (Z : LocM.Mdl Y i₀) (T : Model (Xo i₀.l) i₀.c β) : Type 1 where

  τ : (Y Z.i).X ⟶ (Y i₀).X

  mu : SABMap (Y Z.i).t (Y i₀).t τ

  trans : IsTrans i₀ Z.i τ mu

  h : gen T ⟶ (Y i₀).X

  tg : SAB H (gen T)

  m₁ : SABMap tg T.t (genι T)

  m₂ : SABMap tg (Y i₀).t h

  jQ_h : T.jQ ≫ h = (Y i₀).j

  h_s : h ≫ (Y i₀).s = genStr T ≫ spMap (i₀.c.V W).subtype

variable {Z : LocM.Mdl Y i₀} {T : Model (Xo i₀.l) i₀.c β}

def Link.Match (L : Link Z T) {F : Type} [Field F] {e : F ≃+* i₀.c.F} (C : FlagCpt T e) {k : Type} [Field k]
    (w : Sp k ⟶ Z.X) (q : Sp k ⟶ C.Y.X) : Prop :=
  ∃ (x : Sp k ⟶ (Xo i₀.l).XF i₀.c) (u : Vecs Dw (Y Z.i).t k) (φ : i₀.c.F →+* k) (g : EigFrame T φ ((q ≫ C.π) ≫ genι T)),
    w ≫ Z.π ≫ L.τ = x ≫ (Y i₀).j ∧ q ≫ C.π = x ≫ T.jQ ∧ x ≫ pullback.snd _ _ = spMap φ ∧ Z.FlagAt w u ∧ C.Carries q g ∧
    ∀ σ j, ∃ v : Sp (DualNumber k) ⟶ L.tg.G.left,
      IsTanAtG L.tg (q ≫ C.π) v ∧ v ≫ L.m₁.φ = g.v σ j ∧ v ≫ L.m₂.φ = u σ j ≫ L.mu.φ

end Free


end GlobalTheory.GenDeg
