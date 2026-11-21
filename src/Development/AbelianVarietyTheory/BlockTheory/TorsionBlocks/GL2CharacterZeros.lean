import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

open MeasureTheory Matrix GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining

section Defs

variable {k : Type} [Field k]
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]

def uMat (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) :
    Matrix (ρ ⊕ v ⊕ ρ) (ρ ⊕ v ⊕ ρ) k :=
  fromBlocks 1 (fromCols ν' b) 0 (fromBlocks 1 ν 0 1)

theorem det_uMat (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) :
    (uMat ν ν' b).det = 1 := by
  simp [uMat, det_fromBlocks_zero₂₁]

def uGL (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) : GL (ρ ⊕ v ⊕ ρ) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uMat ν ν' b) (by rw [det_uMat]; exact one_ne_zero)

def nGL (ν : Matrix v ρ k) (ν' : Matrix ρ v k) : GL (ρ ⊕ v ⊕ ρ) k := uGL ν ν' 0

def zGL (v : Type) [Fintype v] [DecidableEq v] (b : Matrix ρ ρ k) : GL (ρ ⊕ v ⊕ ρ) k :=
  uGL (0 : Matrix v ρ k) 0 b

def glueCols (ξ : Matrix W ρ k) (x₀ : Matrix W v k) (c : Matrix W ρ k) : Matrix W (ρ ⊕ v ⊕ ρ) k :=
  fromCols ξ (fromCols x₀ c)

def glueRows {u : Type} (r : Matrix τ u k) (m : Matrix w u k) (s : Matrix τ u k) :
    Matrix (τ ⊕ w ⊕ τ) u k :=
  fromRows r (fromRows m s)

def glueFun {u : Type} (a : Matrix u τ k) (m : Matrix u w k) (c : Matrix u τ k) :
    Matrix u (τ ⊕ w ⊕ τ) k :=
  fromCols a (fromCols m c)

abbrev Mix₁ (k ρ v W : Type) := Matrix W ρ k × Matrix ρ W k × Matrix W v k

abbrev Mix₂ (k ρ v τ w : Type) :=
  Matrix (τ ⊕ w ⊕ τ) ρ k × Matrix ρ (τ ⊕ w ⊕ τ) k × Matrix τ v k × Matrix v τ k × Matrix w v k

def chr (ψ : AddChar k Circle) (s : ℤˣ) (t : k) : ℂ := (ψ (((s : ℤ) : k) * t) : ℂ)

variable [MeasurableSpace k]

def four₁ [Fintype W] (ψ : AddChar k Circle) (m : Measure k) (s : ℤˣ)
    (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) : Mix₁ k ρ v W → ℂ := fun z =>
  ∫ c, Φ (glueCols z.1 z.2.2 c) * chr ψ (-s) (trace (z.2.1 * c)) ∂(volM m W ρ)

def four₂ [Fintype τ] (ψ : AddChar k Circle) (m : Measure k) (s : ℤˣ)
    (F : Mix₁ k ρ v (τ ⊕ w ⊕ τ) → ℂ) : Mix₂ k ρ v τ w → ℂ := fun z =>
  ∫ r, F (z.1, z.2.1, glueRows r z.2.2.2.2 z.2.2.1) * chr ψ (-s) (trace (r * z.2.2.2.1)) ∂(volM m τ v)

end Defs

section Clauses

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k]
variable (ψ : AddChar k Circle) (m : Measure k) (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable (ρ v τ w : Type) [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w]

def ModelsIso : Prop :=
  Set.BijOn (four₁ ψ m s₁) {Φ | Φ ∈ SB (Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k)}
      {F | F ∈ SB (Mix₁ k ρ v (τ ⊕ w ⊕ τ))} ∧
    Set.BijOn (four₂ ψ m s₂) {F | F ∈ SB (Mix₁ k ρ v (τ ⊕ w ⊕ τ))} {F | F ∈ SB (Mix₂ k ρ v τ w)}

end Clauses

section Basic₂

variable {k : Type} [Field k]
variable {ρ v W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]

theorem glueCols_mul_uMat (ξ : Matrix W ρ k) (x₀ : Matrix W v k) (c : Matrix W ρ k)
    (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) :
    glueCols ξ x₀ c * uMat ν ν' b = glueCols ξ (x₀ + ξ * ν') (c + ξ * b + x₀ * ν) := by
  simp only [glueCols, uMat, fromCols_mul_fromBlocks, mul_fromCols, Matrix.mul_one, Matrix.mul_zero,
    add_zero]
  ext i (j | j | j) <;> simp [add_comm, add_left_comm, add_assoc]

theorem om_uGL [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype W] [DecidableEq W] (μ : kˣ →* ℂˣ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (b : Matrix ρ ρ k) (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (x : Matrix W (ρ ⊕ v ⊕ ρ) k) :
    om μ (uGL ν ν' b) 1 Φ x = Φ (x * uMat ν ν' b) := by
  have h : Matrix.GeneralLinearGroup.det (uGL ν ν' b) = 1 := by
    ext; simp [uGL, det_uMat]
  have h2 : (uGL ν ν' b).val = uMat ν ν' b := rfl
  simp [om, h, h2, nabs]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
