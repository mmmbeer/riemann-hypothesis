import Mathlib
import Formalism.LogFactorialIndices.StatementIdx

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Matrix

def ComplexHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (A : ℝ), (∀ i j, ‖M i j‖ ≤ A) →
    ‖M.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2) ∧
      ‖M.det‖ ≤ (Real.sqrt n * A) ^ n

def LossSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (be l vdd vcc vg₁ vg₂ : ι → ℝ) (κ e lrd lcc lg₁ lg₂ : ℝ),
    (∀ i, 0 ≤ l i) →
    (∀ i, be i ≤ κ * (vdd i + vcc i + (e + 1) * vg₁ i + vg₂ i)) →
    ∑ i, vdd i * l i = lrd → ∑ i, vcc i * l i = lcc → ∑ i, vg₁ i * l i = lg₁ →
    ∑ i, vg₂ i * l i = lg₂ →
      ∑ i, be i * l i ≤ κ * (lrd + lcc + (e + 1) * lg₁ + lg₂)

def FilteredPoleLength : Prop :=
  ∀ (O' Rr A : Type) [CommRing O'] [IsLocalRing O'] [CommRing Rr] [IsLocalRing Rr] [Algebra O' Rr]
    [IsLocalHom (algebraMap O' Rr)] [AddCommGroup A] [Module Rr A] [Module O' A]
    [IsScalarTower O' Rr A] (x : Rr) (mm n : ℕ) (F : ℕ → Submodule Rr A) (r : ℕ → ℕ),
    F 0 = ⊤ → F n = ⊥ → (∀ k, k < n → F (k + 1) ≤ F k) →
    (∀ k, k < n → ∀ a ∈ F k, x • a ∈ F (k + 1) → a ∈ F (k + 1)) →
    (∀ k, k < n →
      Module.length Rr
          (↥(F k) ⧸ (F (k + 1) ⊔ (F k).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))).comap
            (F k).subtype) = ((r k * mm : ℕ) : ℕ∞)) →
      Module.length O' (A ⧸ (⊤ : Submodule Rr A).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))) =
        (((∑ k ∈ Finset.range n, r k) * mm : ℕ) : ℕ∞) *
          Module.length (IsLocalRing.ResidueField O') (IsLocalRing.ResidueField Rr)

end Formalism.LatticeBaseChangeAlt
