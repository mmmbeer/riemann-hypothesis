import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

open UpperTheory.V.Af

def mes (k l : ℕ) {N : ℕ} (θ θ' : DirichletCharacter ℂ N) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (f : ZMod (l ^ m) → ℂ) : ℂ :=
  val B c l α m (Zs k l (ch θ) (hat θ') (quo f))

structure Meas {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) {N : ℕ} (θ θ' : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (v : ℂ) : Prop where
  compat : ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (f' : ZMod (l ^ (m + 1)) → ℂ), (∀ x, f (-x) = θ (-1) * f x) →
    (∀ x : ℕ, f' x = f x) → mes (2 * e + 1) l θ θ' α B c (m + 1) f' = mes (2 * e + 1) l θ θ' α B c m f
  bound : ∃ C : ℝ, ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ x, ‖ι.symm (f x)‖ ≤ δ) →
    ‖ι.symm (mes (2 * e + 1) l θ θ' α B c m f)‖ ≤ C * δ
  field : ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ)
    (E' : IntermediateField ℚ_[l] (PadicAlgCl l)), E ≤ E' → (∀ x, ι.symm (f x) ∈ E') → ι.symm (mes (2 * e + 1) l θ θ' α B c m f) ∈ E'
  interp : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ x, f (-x) = θ (-1) * f x) →
    (∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → ‖ι.symm (quo f x y - ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)‖ ≤ δ) →
    ‖ι.symm (mes (2 * e + 1) l θ θ' α B c m f - v)‖ ≤ C * δ

def Chapter : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ), 1 ≤ e → ∀ g : Newform (2 * e + 1), ¬ l ∣ g.M →
    ‖ι.symm (g.a l)‖ = 1 → ∀ ψ : DirichletCharacter ℂ l,
    ∃ (N : ℕ) (χ θ : DirichletCharacter ℂ N) (α v : ℂ) (B : ℕ) (c : ℕ → ℂ) (c₁ d₁ : ℕ),
      5 ≤ N ∧ g.M ∣ N ∧ ¬ l ∣ N ∧ (∀ d : ℕ, d.Coprime N → χ d = g.χ d) ∧ ‖ι.symm α‖ = 1 ∧
      α ^ 2 - χ⁻¹ l * g.a l * α + χ⁻¹ l * (l : ℂ) ^ (2 * e) = 0 ∧
      EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g.a q) α B c ∧
      θ (-1) = (-1) ^ e * ψ (-1) ∧ θ * χ ≠ 1 ∧ χ (-1) = -1 ∧
      Meas ι e θ (θ * χ) ψ α B c v ∧ v ≠ 0 ∧
      1 < c₁ ∧ 1 < d₁ ∧ c₁.Coprime (6 * N * l) ∧ d₁.Coprime (6 * N * l) ∧
      (c₁ : ℂ) ^ e ≠ θ c₁ * ψ⁻¹ c₁ ∧ (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ)⁻¹ d₁ * ψ⁻¹ d₁)

end GlobalTheory.EisM

end
