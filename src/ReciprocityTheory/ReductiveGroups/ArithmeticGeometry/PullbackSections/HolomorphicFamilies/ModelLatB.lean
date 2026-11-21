import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA FractionalIdeal

variable {r : ℕ}

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  have hsq : ∀ σ : D.host.E →+* ℂ, σ D.host.xi0 ^ 2 =
      1 / (((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ^ 2 * (-(D.host.d : ℂ))) := by
    intro σ
    have e : D.host.xi0 ^ 2 =
        1 / (((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ^ 2 * (-(D.host.d : D.host.E))) := by
      simp only [Formalism.BasicNotions.Host.xi0]
      rw [div_pow, mul_pow, D.host.sqrtMinusD_sq]
      ring
    rw [← map_pow, e]
    simp
  have e2 : ‖τ D.host.xi0‖ ^ 2 = ‖D.host.φ₀ D.host.xi0‖ ^ 2 := by
    rw [← norm_pow, ← norm_pow, hsq τ, hsq D.host.φ₀]
  have ha := norm_nonneg (τ D.host.xi0)
  have hb := norm_nonneg (D.host.φ₀ D.host.xi0)
  show ‖τ D.host.xi0‖ = ‖D.host.φ₀ D.host.xi0‖
  exact le_antisymm (by nlinarith) (by nlinarith)

theorem xi_eq (hP : FactPrincipalDatum) (D : D7) (X : Data D.host.E r)
    (hX : ∀ τ : D.host.E →+* ℂ, ‖τ X.ξ0‖ = xiR D) : X.ξ0 = D.host.xi0 ∨ X.ξ0 = -D.host.xi0 := by
  have hx0 : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero hP D
  have hcξ : IsCMField.complexConj D.host.E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hcx : IsCMField.complexConj D.host.E D.host.xi0 = -D.host.xi0 := conj_xi0_alt D
  have hcu : IsCMField.complexConj D.host.E (X.ξ0 / D.host.xi0) = X.ξ0 / D.host.xi0 := by
    rw [map_div₀, hcξ, hcx, neg_div_neg_eq]
  have hτx : D.host.φ₀ D.host.xi0 ≠ 0 := (map_ne_zero D.host.φ₀).2 hx0
  have hn : ‖D.host.φ₀ (X.ξ0 / D.host.xi0)‖ = 1 := by
    have e : ‖D.host.φ₀ D.host.xi0‖ = xiR D := rfl
    rw [map_div₀, norm_div, hX D.host.φ₀, ← e, div_self (norm_ne_zero_iff.2 hτx)]
  have hreal : starRingEnd ℂ (D.host.φ₀ (X.ξ0 / D.host.xi0)) = D.host.φ₀ (X.ξ0 / D.host.xi0) := by
    rw [← IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀, hcu]
  have hsq : D.host.φ₀ (X.ξ0 / D.host.xi0) ^ 2 = 1 := by
    have h1 := Complex.conj_eq_iff_re.1 hreal
    rw [← h1] at hn ⊢
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    have h2 : (D.host.φ₀ (X.ξ0 / D.host.xi0)).re ^ 2 = 1 := by rw [← sq_abs, hn, one_pow]
    exact_mod_cast h2
  have hu2 : (X.ξ0 / D.host.xi0) ^ 2 = 1 := by
    apply D.host.φ₀.injective
    rw [map_pow, hsq, map_one]
  have hfac : (X.ξ0 / D.host.xi0 - 1) * (X.ξ0 / D.host.xi0 + 1) = 0 := by
    have e : (X.ξ0 / D.host.xi0 - 1) * (X.ξ0 / D.host.xi0 + 1) = (X.ξ0 / D.host.xi0) ^ 2 - 1 := by ring
    rw [e, hu2, sub_self]
  rcases mul_eq_zero.1 hfac with h | h
  · left
    exact (div_eq_one_iff_eq hx0).1 (sub_eq_zero.1 h)
  · right
    have h3 : X.ξ0 / D.host.xi0 = -1 := eq_neg_of_add_eq_zero_left h
    rw [div_eq_iff hx0] at h3
    rw [h3]
    ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB
