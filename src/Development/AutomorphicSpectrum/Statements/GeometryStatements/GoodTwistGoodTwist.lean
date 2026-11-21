import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (Rul Ix ex sec Unf IsUnf GoodEmb goodOf rdU laU relab FrPt FrMap FromTest)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

open Classical in

def goodTwist (c : Coeff l) (σ : c.F →+* ℂ) : ℂ →+* ℂ := if GoodEmb c σ then RingHom.id ℂ else starRingEnd ℂ

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx}

theorem goodOf_apply (σ : c.F →+* ℂ) (a : c.F) : goodOf c σ a = goodTwist c σ (σ a) := by
  unfold goodOf goodTwist
  split_ifs <;> rfl

theorem goodTwist_goodTwist (σ : c.F →+* ℂ) (a : ℂ) : goodTwist c σ (goodTwist c σ a) = a := by
  unfold goodTwist
  split_ifs <;> simp

theorem norm_goodTwist (σ : c.F →+* ℂ) (a : ℂ) : ‖goodTwist c σ a‖ = ‖a‖ := by
  unfold goodTwist
  split_ifs <;> simp

theorem hasVal_const {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω F : Type} [Field Ω] [Field F]
    [Algebra F Ω] {y : (Σ k, ι k) → Ω} {σ : F →+* ℂ} {z : (Σ k, ι k) → ℂ} (hz : LiesOver y σ z) {θ : F} {v : ℂ}
    (hv : HasVal y 0 (algebraMap F Ω θ) z v) : v = σ θ := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, h0, hw⟩ := hv
  obtain rfl : dg = dh := funext fun k => by simpa using hd k
  have e : ∀ p : MRing ι, eval z (map (Int.castRingHom ℂ) p) = aeval z p := fun p => by
    rw [aeval_def, eval_map]; rfl
  have := hz dg g h θ hg hh hy
  rw [e, e, hw] at this
  exact mul_right_cancel₀ h0 this

example : ‖(1 : ℂ) * Complex.I + Complex.I * 1‖ ≠ ‖(1 : ℂ) * starRingEnd ℂ Complex.I + Complex.I * 1‖ := by
  simp

end GlobalTheory.CompanionTheory.Ar.Small
