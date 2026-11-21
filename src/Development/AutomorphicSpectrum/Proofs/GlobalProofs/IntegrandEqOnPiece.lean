import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDetStatement
import GroundTheory.AutomorphicForms.GL2.GJUnramifiedCosets
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IwasawaDecompositionUpperTriangular
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SphericalZetaCosets
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.ZetaSph

theorem zeta_spherical : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ), UnrChar nrm q χ α → ∀ (φ : GL (Fin c) F → ℂ), IsSphFn O nrm χ φ → ∀ (κ : Measure (GL (Fin c) F)), κ.IsMulLeftInvariant → κ (GLint O c : Set (GL (Fin c) F)) = 1 → ∀ σ : ℝ, (∀ i, ‖α i‖ * (q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) < 1) → IntegrableOn (fun g => φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ (σ) : ℝ) : ℂ)) (Mint O c) κ ∧ ∫ g in Mint O c, φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ (σ) : ℝ) : ℂ) ∂κ = ∏ i : Fin c, (1 - α i * (((q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) : ℝ) : ℂ))⁻¹ :=
  _root_.UpperTheory.Reformulated.B.SphericalZetaCosets.zeta_spherical

end GlobalTheory.CompanionTheory.ZetaSph
