import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

noncomputable section

namespace GlobalTheory.UnifDataTest

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_bijective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Bijective (relab (E := E) c σ) := by
  refine Finite.injective_iff_bijective.1 fun τ τ' h => ?_
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

theorem relab_conj (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) :
    relab c σ (conjEmb τ) = conjEmb (relab c σ τ) := by
  ext a
  have h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm
  show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (relab c σ τ) a






theorem conj_mem (X : Data E r) {τ : E →+* ℂ} (h : τ ∉ X.Ψ) : conjEmb τ ∈ X.Ψ := by
  by_contra h'
  exact h ((X.cmType τ).2 h')

theorem rdU_mul (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  by_cases h : x ∈ (U.X k).dom
  · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply, h, dif_pos]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp [rdU, h]

theorem not_good_conj (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have : starRingEnd ℂ ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h'
    rwa [show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h] at this
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, him, Complex.neg_re, Complex.natCast_re] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.UnifDataTest
