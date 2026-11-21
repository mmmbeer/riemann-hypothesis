import Mathlib
import Formalism.RealPlaceAnalysis.FockPairGl
import Formalism.SatakeDualWeyl.Statement

section
noncomputable section

namespace Formalism.MJ

open MvPolynomial
open scoped Kronecker

universe u v

def linSubst {σ : Type u} {R : Type v} [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (f : MvPolynomial σ R) : MvPolynomial σ R :=
  aeval (fun i => ∑ j, C (g i j) * X j) f

def IsIntegralJet {σ : Type u} {R : Type v} [CommRing R] (A : Subring R)
    (f : MvPolynomial σ R) : Prop :=
  ∀ α, coeff α f ∈ A

def mfac {σ : Type u} (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

def evOp {σ : Type u} {R : Type v} [CommRing R] (P F : MvPolynomial σ R) : R :=
  ∑ α ∈ P.support, (mfac α : R) * coeff α P * coeff α F

def jetTrunc {σ : Type u} {R : Type v} [CommRing R] (N : ℕ) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
  ∑ n ∈ Finset.range (N + 1), homogeneousComponent n f

def hcMat {R : Type v} [CommRing R] {p q : ℕ} (A : Matrix (Fin p) (Fin p) R)
    (D : Matrix (Fin q) (Fin q) R) : Matrix (Fin p × Fin q) (Fin p × Fin q) R :=
  A ⊗ₖ D.transpose

def actK {R : Type v} [CommRing R] {p q r : ℕ}
    (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (k : GL (Fin p) R × GL (Fin q) R) (F : Fin r → MvPolynomial (Fin p × Fin q) R) :
    Fin r → MvPolynomial (Fin p × Fin q) R :=
  fun i => ∑ j, C ((ρ k : Matrix (Fin r) (Fin r) R) i j) *
    linSubst (hcMat ((k.1⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R)
      ((k.2 : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) (F j)

def EvIntegral : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (P F : MvPolynomial σ R),
    IsIntegralJet A P → IsIntegralJet A F → evOp P F ∈ A

def JetRank : Prop :=
  ∀ (σ : Type u) (K : Type v) [Fintype σ] [Field K] (N : ℕ),
    Module.finrank K (restrictTotalDegree σ K N) = Nat.choose (N + Fintype.card σ) N

end Formalism.MJ
end
end

section
noncomputable section

namespace Formalism.MJ

open MvPolynomial

universe u v

end Formalism.MJ
end
end

section
noncomputable section

namespace Formalism.MJ

open MvPolynomial

def partialD {n : ℕ} (i : Fin n) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z => deriv (fun t => f (Function.update z i t)) (z i)

end Formalism.MJ
end
end

section
noncomputable section

namespace Formalism.MJ

open MvPolynomial

def actF {p q r : ℕ} (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ)) :
    (Fin p × Fin q → ℂ) → (Fin r → ℂ) :=
  fun z => ((ρ k : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec
    (F ((hcMat ((k.1⁻¹ : GL (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ)
      ((k.2 : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)).mulVec z))

end Formalism.MJ
end
end

section
noncomputable section

namespace Formalism.MJ

open Matrix
open scoped ComplexOrder

def blk {p q : ℕ} (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) : GL (Fin p ⊕ Fin q) ℂ where
  val := fromBlocks (A : Matrix (Fin p) (Fin p) ℂ) 0 0 (D : Matrix (Fin q) (Fin q) ℂ)
  inv := fromBlocks ((A⁻¹ : GL (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) 0 0
    ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)
  val_inv := by simp [fromBlocks_multiply]
  inv_val := by simp [fromBlocks_multiply]

def moeb {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  (g.toBlocks₁₁ * z + g.toBlocks₁₂) * (g.toBlocks₂₁ * z + g.toBlocks₂₂)⁻¹

def hcDom (p q : ℕ) : Set (Matrix (Fin p) (Fin q) ℂ) :=
  {z | (1 - zᴴ * z).PosDef}

def vecOf {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : Fin p × Fin q → ℂ := fun x => z x.1 x.2

end Formalism.MJ
end
end
