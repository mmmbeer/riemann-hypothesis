import Mathlib

open Finset Polynomial

noncomputable section

namespace Formalism.NG

section Idem

variable {T A : Type*} [CommRing T] [Ring A] [Algebra T A]

def Eop (x : A) {t : ℕ} (r : Fin (t + 1) → T) : A :=
  aeval x (∏ i ∈ univ.erase (0 : Fin (t + 1)), (X - C (r i)))

def delta {t : ℕ} (r : Fin (t + 1) → T) : T :=
  ∏ i ∈ univ.erase (0 : Fin (t + 1)), (r 0 - r i)

def Roots (x : A) {t : ℕ} (r : Fin (t + 1) → T) : Prop :=
  aeval x (∏ i, (X - C (r i))) = 0

end Idem

def StatPowSubPow : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (x : ℤ), (l : ℤ) ∣ x - 1 → ¬ (l : ℤ) ^ 2 ∣ x - 1 →
    ∀ a b : ℕ, a < b → padicValInt l (x ^ b - x ^ a) = 1 + padicValNat l (b - a)

def StatDeltaVal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (u : ℤ), ¬ (l : ℤ) ∣ u → ∀ (w t : ℕ),
    padicValInt l (delta (fun i : Fin (t + 1) => u * (1 + (l : ℤ)) ^ (w + (i : ℕ)))) =
      t + padicValNat l t.factorial

def StatDeltaValLe : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (u : ℤ), ¬ (l : ℤ) ∣ u → ∀ (w t : ℕ),
    padicValInt l (delta (fun i : Fin (t + 1) => u * (1 + (l : ℤ)) ^ (w + (i : ℕ)))) ≤ 2 * t

section Pres

variable {R : Type*} [Ring R] {m g : Type*} [Fintype m] [Fintype g]

def relSpan (Θ : Matrix m g R) : Submodule R (g → R) := Submodule.span R (Set.range Θ)

abbrev Coker (Θ : Matrix m g R) : Type _ := (g → R) ⧸ relSpan Θ

def relMap (O : Type*) [CommRing O] (M : Type*) [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] (Θ : Matrix m g R) : (g → M) →ₗ[O] (m → M) where
  toFun v i := ∑ j, Θ i j • v j
  map_add' v w := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext i; simp [Finset.smul_sum, smul_comm]

end Pres

def StatHomCoker : Prop :=
  ∀ (R O M : Type*) [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] (m g : Type) [Fintype m] [Fintype g] [DecidableEq g] (Θ : Matrix m g R),
    Nonempty ((Coker Θ →ₗ[R] M) ≃ₗ[O] LinearMap.ker (relMap O M Θ))

section DVR

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

abbrev KO : Type _ := FractionRing O ⧸ (1 : Submodule O (FractionRing O))

def matQ {ι : Type*} [Fintype ι] (A : Matrix ι ι O) : (ι → KO O) →ₗ[O] (ι → KO O) :=
  relMap O (KO O) A

end DVR

def StatLenKer : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι O),
    Module.length O (LinearMap.ker (matQ O A)) = IsDiscreteValuationRing.addVal O A.det

def bigMat {R O : Type*} [CommRing O] {g d : Type*} (ρ : R → Matrix d d O) (Θ : Matrix g g R) :
    Matrix (g × d) (g × d) O :=
  fun p q => ρ (Θ p.1 q.1) p.2 q.2

def StatDetTri : Prop :=
  ∀ (R O : Type*) [CommRing O] (g d : Type) [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (α : Type) [LinearOrder α] (ρ : R → Matrix d d O) (b : d → α),
    (∀ r, (ρ r).BlockTriangular b) → ∀ Θ : Matrix g g R,
    (bigMat ρ Θ).det = ∏ k ∈ univ.image b, (bigMat (fun r => (ρ r).toSquareBlock b k) Θ).det

abbrev baseChange {T : Type*} (T' : Type*) [CommRing T] [CommRing T'] [Algebra T T'] (J : Ideal T) :
    Type _ :=
  T' ⧸ Ideal.map (algebraMap T T') J

def StatPoints : Prop :=
  ∀ (O B Ω : Type*) [CommRing O] [IsDomain O] [CommRing B] [IsReduced B] [Algebra O B]
    [Module.Finite O B] [NoZeroSMulDivisors O B] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω],
    Function.Injective (algebraMap O Ω) →
    ∀ b : B, (∀ φ : B →ₐ[O] Ω, φ b = 0) → b = 0

end Formalism.NG
