import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NumberField.AdeleRing TensorProduct

namespace PositivityTheory.Rg.Tf.Geo

def HtC : Prop := (∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Y : ℝ),
      IsCompact {g : G1 E n | AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) ≤ Y}) ∧
  (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ f : CC E n, Ell σ f →
      Integrable (twKQ θ f) (quotientMeasure (Gam E n) μ))

def SelmerRankBoundLaurent : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x : GL (Fin n) (v.adicCompletion F),
      x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ GLnLocal.integralGL (v.adicCompletion F) n ↔
      ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧
        ∃ y ∈ GLnLocal.integralGL (v.adicCompletion F) n, x = t * y

end PositivityTheory.Rg.Tf.Geo
