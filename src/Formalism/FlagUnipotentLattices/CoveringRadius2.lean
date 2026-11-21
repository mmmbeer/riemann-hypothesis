import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound

open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

open Formalism.NuclearRankWeightBounds.D (lead hs q0)

def PolarInv : Prop :=
  ∀ (N : ℕ) (k X : Matrix (Fin N) (Fin N) ℂ), k ∈ Matrix.unitaryGroup (Fin N) ℂ → X.IsHermitian →
    (k * NormedSpace.exp X)⁻¹ = k.conjTranspose * NormedSpace.exp (-(k * X * k.conjTranspose)) ∧
      (-(k * X * k.conjTranspose)).IsHermitian ∧ hs (-(k * X * k.conjTranspose)) = hs X ∧
      ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - (k * NormedSpace.exp X).conjTranspose * (k * NormedSpace.exp X)).PosSemidef

open Classical in

def AllSum : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h ε : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 ≤ B → 0 < ε → ε * Real.sqrt (2 * (q : ℝ)) ≤ 1 → B * ε ≤ 1 →
    32 * B ≤ h * ε → 16 ≤ h * ε ^ 2 →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤ A * 4 ^ Fintype.card ι

open Classical in

def AllSumRate : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 < B → 16 * B * Real.sqrt (2 * (q : ℝ)) ≤ h →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤
      A * (Real.exp B / (1 - Real.exp (-B))) ^ Fintype.card ι

def ThreshCount : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 46 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    16 * (2 * (n : ℝ) ^ 2) * Real.sqrt (2 * (q : ℝ)) ≤ h

def LayerCount : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (N : ℕ) (de la laM : ℝ), 0 ≤ de → 0 < la → la / 2 ≤ laM →
    (1 + 2 * (∏ _v : ι, 3 * de) ^ ((1 : ℝ) / Fintype.card ι) / laM) ^ (N * Fintype.card ι) ≤
      (1 + 12 * de / la) ^ (N * Fintype.card ι)

def KappaAssembly : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (a p q n0 f : ℕ) (j : Fin a → ℕ) (v res cIw volN volR : ℝ) (volGL : Fin a → ℝ),
    (∀ x, 1 ≤ j x) → 1 ≤ a → (∑ x, j x) ≤ q → q ≤ p → p + q = n0 + 2 * ∑ x, j x → 1 ≤ f →
    1 / 2 ≤ v → 0 ≤ res →
    0 ≤ volN → volN ≤ (C * v) ^ ((f : ℝ) * dimN j n0 / 2) →
    (∀ x, 0 ≤ volGL x ∧ volGL x ≤ (C * v) ^ (j x ^ 2 * f) * res * C ^ f) →
    0 ≤ volR → volR ≤ v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2) * C ^ ((p + q) * f) →
    0 ≤ cIw → cIw ≤ (C ^ dimN j n0 * (Vsph p * Vsph q /
      (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)))) ^ f →
    cIw * volN * (∏ x, volGL x) * volR ≤
      v ^ (-((f : ℝ) * dimN j n0 / 2)) * C' ^ ((∑ x, j x) * (p + q) * f) * res ^ a
        * ((C' / (p : ℝ)) ^ ((∑ x, j x) * (p - ∑ x, j x))
          * ((∑ x, j x : ℕ) : ℝ) ^ (((∑ x, j x : ℕ) : ℝ) ^ 2 / 2)) ^ f

def DedekindZetaResidueBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E], 2 ≤ Module.finrank ℚ E →
    dedekindZeta_residue E ≤
      (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E

def LogVolumeBound : Prop :=
  ∀ (a q f : ℕ) (j : Fin a → ℕ) (C₁ Y : ℝ), 1 ≤ C₁ → 2 ≤ Y → 1 ≤ q → (∀ x, j x ≤ q) →
    0 < Y ^ (-(C₁ * q)) ∧ Y ^ (-(C₁ * q)) ≤ 1 / 2 ∧
    ∏ x, (2 * (f : ℝ) * j x * Real.log (1 / (2 * Y ^ (-(C₁ * q))))) ≤
      (2 * C₁ * f * (q : ℝ) ^ 2 * Real.log Y) ^ a

def CoveringRadius2 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y ∈ Formalism.HadamardInequality.zdual M, y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) / (2 * κ)

def StepsRoom : Prop :=
  ∀ (n q f P : ℕ) (b : ℝ), 1 ≤ q → P0 n q f + n ^ 2 * f ≤ 2 * P0 n q f ∧
    (P ≤ 2 * P0 n q f → b ^ 2 + (P : ℝ) * n ≤ b1 n q f b)

end Formalism.HermitianLatticeCounting.S7
