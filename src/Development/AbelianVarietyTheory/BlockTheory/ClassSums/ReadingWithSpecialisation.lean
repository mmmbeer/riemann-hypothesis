import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.ReadingWithSpecialisation

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

def IsCover (d : DeltaDat Xo c n) : Prop :=
  d.IsLev ∧ Nat.Coprime d.pd l.A ∧
    (∃ j : KA l →+* KA d.l₂, (∀ t, ((j t : KA d.l₂) : ℂ) = ((t : KA l) : ℂ)) ∧ d.r ≫ Xo.s = d.Xo₂.s ≫ spMap j) ∧
    ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂

def IsModulus (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (w : E)
    (v : TF n g) (ρ : ℝ) : Prop :=
  ∀ x ∈ X.dom, IsUnitFr X x → ∀ θ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x X.Λ θ →
    MeanOne X bas idx x X.Λ θ → ∀ z : Fin n → Fin g → ℂ, ‖∏ b, θ (z b)‖ = ρ * ‖thA X bas idx v x z‖

theorem IsModulus.unique {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {w : E}
    {v : TF n g} {ρ ρ' : ℝ} (h : IsModulus X bas idx w v ρ) (h' : IsModulus X bas idx w v ρ')
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hu : IsUnitFr X x) {θ : (Fin g → ℂ) → ℂ}
    (h1 : IsTheta1 X bas idx w x X.Λ θ) (h2 : MeanOne X bas idx x X.Λ θ) {z : Fin n → Fin g → ℂ}
    (hz : thA X bas idx v x z ≠ 0) : ρ = ρ' :=
  mul_right_cancel₀ (norm_ne_zero_iff.mpr hz) ((h x hx hu θ h1 h2 z).symm.trans (h' x hx hu θ h1 h2 z))

end

end GlobalTheory.IndefiniteRowSideFullHecke.ReadingWithSpecialisation
