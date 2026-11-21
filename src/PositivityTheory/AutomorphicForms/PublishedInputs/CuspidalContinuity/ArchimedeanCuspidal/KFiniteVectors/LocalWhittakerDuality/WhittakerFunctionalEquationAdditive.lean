import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.DampedFunctionalEquationAtPoint

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

def WhittakerFunctionalEquationAdditive : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ s : ℂ, 0 < s.re → s.re < 1 →
  Integrable (onU (fun a => W (dg2 a 1) * ((μ a : ℂˣ) : ℂ) * mp a (s - 3 / 2))) (selfDualMeasure ψ) ∧
  Integrable (onU (fun a => W (dg2 a 1 * w0) * (((ω a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (-1 / 2 - s))) (selfDualMeasure ψ) ∧
  zA' ψ W ω μ s = G μ s * zA ψ W μ s

open Classical in

def GJm1 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ f : GL (Fin 2) F → ENNReal, Measurable f →
  ∫⁻ g, f g ∂LFS.hG ψ = ∫⁻ r₂, ∫⁻ x, ∫⁻ y, (if h : y = 0 ∨ r₂ 1 = 0 then 0 else
    f (uni2 x * dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r₂) * ENNReal.ofReal ((modulus y : ℝ) ^ (-2 : ℤ)))
      ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂LFS.vol2 ψ

open Classical in

def GJm2 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ f : GL (Fin 2) F → ENNReal, Measurable f →
  ∫⁻ g, f g ∂LFS.hG ψ = ∫⁻ r₂, ∫⁻ t, ∫⁻ y, (if h : y = 0 ∨ r₂ 1 = 0 then 0 else
    f (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * w0 * uni2 t * hr r₂) * ENNReal.ofReal ((modulus y : ℝ) ^ (-1 : ℤ)))
      ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂LFS.vol2 ψ

def GodementKernelBigCell : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (y : Fˣ) (t : F) (r₂ : Fin 2 → F), r₂ 1 ≠ 0 →
  phd ψ Φ (dg2 y 1 * w0 * uni2 t * hr r₂) = phk ψ Φ t r₂

def GodementSectionPartialFourier : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), Φ ∈ LFS.SB F →
  ∀ h : GL (Fin 2) F, LFS.Wp ψ W₀ Φ (em h) = mp (GeneralLinearGroup.det h) (1 / 2) *
    ∫ g, pFT ψ Φ g.val (e2r (h * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * W₀ (h * g⁻¹) ∂LFS.hG ψ

def SchwartzBruhatProductDecomposition : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ Φ ∈ LFS.SB F, ∃ (n : ℕ) (Φ₁ : Fin n → Matrix (Fin 2) (Fin 2) F → ℂ)
  (Φ₂ : Fin n → (Fin 2 → F) → ℂ), (∀ i, SB2 (Φ₁ i)) ∧ (∀ i, Φ₂ i ∈ GodementSectionLocal.schwartzBruhat2 F) ∧
    ∀ A y, Φ (cat3 A y) = ∑ i, Φ₁ i A * Φ₂ i y

def A1 : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ Φ ∈ LFS.SB F, ∀ W' ∈ V',
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (iw (LFS.Wp ψ W₀ Φ) W' s) (mIw ψ) ∧
    Integrable (fun g => mp (GeneralLinearGroup.det g) (s + 1 / 2) * Z2 ψ W₀ (tr2 W' g) (pFT ψ Φ g.val) s) (LFS.hG ψ) ∧
    zetaGL3GL2 ψ (LFS.Wp ψ W₀ Φ) W' s = ∫ g, mp (GeneralLinearGroup.det g) (s + 1 / 2) * Z2 ψ W₀ (tr2 W' g) (pFT ψ Φ g.val) s ∂LFS.hG ψ

def A3 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (n : ℕ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (Φ₁ : Fin n → Matrix (Fin 2) (Fin 2) F → ℂ)
  (Φ₂ : Fin n → (Fin 2 → F) → ℂ), (∀ i, SB2 (Φ₁ i)) → (∀ i, Φ₂ i ∈ GodementSectionLocal.schwartzBruhat2 F) →
  (∀ A y, Φ (cat3 A y) = ∑ i, Φ₁ i A * Φ₂ i y) →
    (∀ A ξ, pFT ψ Φ A ξ = ∑ i, Φ₁ i A * ftN ψ (Φ₂ i) ξ) ∧ (∀ A ξ, dFT ψ Φ A ξ = ∑ i, matrixFourierTransposeInv ψ (Φ₁ i) A * Φ₂ i (-ξ))

def GodementSectionDual : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F,
  dW3 (LFS.Wp ψ W₀ Φ) (em h) = mp (GeneralLinearGroup.det h) (1 / 2) *
    ∫ g, dFT ψ Φ g.val (e2r (h * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * dW2 W₀ (h * g⁻¹) ∂LFS.hG ψ

end Ad3.K.GL2LocalData
