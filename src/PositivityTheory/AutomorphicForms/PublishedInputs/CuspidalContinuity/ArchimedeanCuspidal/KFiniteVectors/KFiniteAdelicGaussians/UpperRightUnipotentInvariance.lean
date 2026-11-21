import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.K.GA

variable (K : Type) [Field K] [NumberField K]

def nx : Multiplicative K →* GL (Fin 2) K where
  toFun x := ⟨!![1, x.toAdd; 0, 1], !![1, -x.toAdd; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def nU : Subgroup (GL (Fin 2) K) := (nx K).range

abbrev NQ : Type := Quotient (QuotientGroup.rightRel (nU K))

def b1M : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun γ := !![γ 0 0, γ 0 1, 0; γ 1 0, γ 1 1, 0; 0, 0, 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def b2M : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun γ := !![1, 0, 0; 0, γ 0 0, γ 0 1; 0, γ 1 0, γ 1 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def e1 : GL (Fin 2) K →* GL (Fin 3) K := Units.map (b1M K)

def e2 : GL (Fin 2) K →* GL (Fin 3) K := Units.map (b2M K)

def sw : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

variable {K}

def uS (W : G3K K → ℂ) (g : G3K K) : ℂ := ∑' q : NQ K, W (diaK (e1 K q.out) * g)

def vS (W : G3K K → ℂ) (g : G3K K) : ℂ := ∑' q : NQ K, W (diaK (e2 K q.out * sw K) * g)

def lowM (c : 𝔸[K]) : G3K K :=
  ⟨!![1, 0, 0; c, 1, 0; 0, 0, 1], !![1, 0, 0; -c, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def yCoef (f : G3K K → ℂ) (ξ : Fin 2 → K) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 2), f (uni 0 (y 0) (y 1) * g) * (adelicChar K (-pair ξ y) : ℂ) ∂vecMeasure K (Fin 2)

def ctY (f : G3K K → ℂ) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 2), f (uni 0 (y 0) (y 1) * g) ∂vecMeasure K (Fin 2)

def ctY' (f : G3K K → ℂ) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 2), f (lowM (y 0) * uni 0 0 (y 1) * g) ∂vecMeasure K (Fin 2)

def hCoef (f : G3K K → ℂ) (ξ : Fin 2 → K) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 3), f (lowM (y 0) * uni 0 (y 1) (y 2) * g) *
    (adelicChar K (-(algebraMap K 𝔸[K] (ξ 0) * y 0 + algebraMap K 𝔸[K] (ξ 1) * y 1)) : ℂ) ∂vecMeasure K (Fin 3)

def RInv (f : G3K K → ℂ) : Prop :=
  ∀ p : GL (Fin 3) K, p.val 0 1 = 0 → p.val 2 0 = 0 → p.val 2 1 = 0 → ∀ g, f (diaK p * g) = f g

variable (K)

def ContW : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, Continuous W

def MajU : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ Kc : Set (G3K K), IsCompact Kc →
  ∃ b : NQ K → ℝ, Summable b ∧ ∀ q g, g ∈ Kc → ‖W (diaK (e1 K q.out) * g)‖ ≤ b q

def MajV : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ Kc : Set (G3K K), IsCompact Kc →
  ∃ b : NQ K → ℝ, Summable b ∧ ∀ q g, g ∈ Kc → ‖W (diaK (e2 K q.out * sw K) * g)‖ ≤ b q

def UpperRightUnipotentInvariance : Prop := ∀ f : G3K K → ℂ, Continuous f → RInv f → (∀ ξ : Fin 2 → K, ξ 1 ≠ 0 → ∀ g, yCoef f ξ g = 0) →
  ∀ (t : 𝔸[K]) g, f (uni 0 0 t * g) = f g

def CtU : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ g, ctY (uS W) g = 0 ∧ ctY' (uS W) g = 0

def CtV : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ g, ctY (vS W) g = 0 ∧ ctY' (vS W) g = 0

def HGen : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ ξ : Fin 2 → K, ξ 0 ≠ 0 → ξ 1 ≠ 0 → ∀ g,
  hCoef (uS W) ξ g = hCoef (vS W) ξ g

end Ad3.K.GA
