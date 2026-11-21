import Mathlib
import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound

namespace Formalism.HermitianLattices.RamifiedLatticeOperators

open Finset Matrix ComplexConjugate

def TraceOperatorIdentityAllRanks : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (r : ℕ) (R : Type) [CommRing R], 1 ≤ r →
    (∀ (ψ : (Fin r → F) → R) (x : Fin r → F), x ≠ 0 →
      (Fintype.card F : R) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.opD (Formalism.LogVandermondeBounds.product_first_zeroth_parts.opU ψ) x =
        (Fintype.card F : R) ^ r * ψ x - (Fintype.card F : R) ^ (r - 1) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmV ψ x
          + (Fintype.card F : R) ^ (r - 1) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.trV ψ) ∧
    (∀ (φ : (Fin r → F) → R) (f : Fin r → F), f ≠ 0 →
      (Fintype.card F : R) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.opU (Formalism.LogVandermondeBounds.product_first_zeroth_parts.opD φ) f =
        (Fintype.card F : R) ^ r * φ f - (Fintype.card F : R) ^ (r - 1) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP φ f
          + (Fintype.card F : R) ^ (r - 1) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.trP φ)

def Fubini_orbits : Prop :=
  ∀ (Γ P Q V : Type) [Group Γ] [MulAction Γ P] [MulAction Γ Q] [AddCommGroup V] [Module ℚ V]
    (pr : P → Q) (fib : Q → Finset P) (Ψ : P → V) (RP : Finset P) (RQ : Finset Q),
    (∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p) → (∀ p y, p ∈ fib y ↔ pr p = y) →
    (∀ (γ : Γ) (p : P), Ψ (γ • p) = Ψ p) →
    (∀ y : Q, Finite (MulAction.stabilizer Γ y)) →
    (∀ p : P, ∃! r, r ∈ RP ∧ r ∈ MulAction.orbit Γ p) →
    (∀ y : Q, ∃! r, r ∈ RQ ∧ r ∈ MulAction.orbit Γ y) →
    ∑ p ∈ RP, ((Nat.card (MulAction.stabilizer Γ p) : ℚ))⁻¹ • Ψ p =
      ∑ y ∈ RQ, ((Nat.card (MulAction.stabilizer Γ y) : ℚ))⁻¹ • ∑ p ∈ fib y, Ψ p

def Count_orbits : Prop :=
  ∀ (Γ A B V : Type) [Group Γ] [MulAction Γ A] [MulAction Γ B] [AddCommGroup V] [Module ℚ V]
    (up : A → Finset B) (down : B → Finset A) (G : A → B → V) (RA : Finset A) (RB : Finset B),
    (∀ a b, b ∈ up a ↔ a ∈ down b) → (∀ (γ : Γ) a b, b ∈ up a → γ • b ∈ up (γ • a)) →
    (∀ (γ : Γ) a b, b ∈ up a → G (γ • a) (γ • b) = G a b) →
    (∀ a : A, Finite (MulAction.stabilizer Γ a)) → (∀ b : B, Finite (MulAction.stabilizer Γ b)) →
    (∀ a : A, ∃! r, r ∈ RA ∧ r ∈ MulAction.orbit Γ a) →
    (∀ b : B, ∃! r, r ∈ RB ∧ r ∈ MulAction.orbit Γ b) →
    ∑ a ∈ RA, ((Nat.card (MulAction.stabilizer Γ a) : ℚ))⁻¹ • ∑ b ∈ up a, G a b =
      ∑ b ∈ RB, ((Nat.card (MulAction.stabilizer Γ b) : ℚ))⁻¹ • ∑ a ∈ down b, G a b

def LemmaB'_length : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (ι : Type) [Fintype ι] (deg : ι → ℕ),
      Module.length R ((ι → R) ⧸
        (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
        ((∑ i, deg i : ℕ) : ℕ∞)

def LemmaC_sharp : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (P S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      P.map U ≤ P → P.map D ≤ P → (∀ x : M, ϖ • x ∈ P → x ∈ P) →
      (∀ s ∈ S ⊓ P, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R ((S ⊓ P : Submodule R M) ⧸ ((S ⊓ P).map ((ϖ ^ b) • U)).comap (S ⊓ P).subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R (S ⊓ P : Submodule R M) : ℕ)

def Index_det : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (u : Matrix n n R), u.det ≠ 0 →
      Module.length R ((n → R) ⧸ LinearMap.range u.mulVecLin) = emultiplicity ϖ u.det

def AffineFibreCountComparison : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n g : ℕ) (xb : (Fin n → F) →ₗ[F] (Fin (n + g) → F))
    (f : Fin n → F) (uW : Fin (n + g) → F),
    let rk := Module.finrank F (LinearMap.range xb)
    let A : ℤ := Nat.card {fW : Fin (n + g) → F // fW ⬝ᵥ uW = 1 ∧ ∀ l, fW ⬝ᵥ xb l = f ⬝ᵥ l}
    let B : ℤ := Nat.card {u : Fin n → F // f ⬝ᵥ u = 1 ∧ xb u = uW}
    let fker : Prop := ∀ l ∈ LinearMap.ker xb, f ⬝ᵥ l = 0
    (uW ∉ LinearMap.range xb → fker →
      A - (Fintype.card F : ℤ) ^ g * B = (Fintype.card F : ℤ) ^ (n + g - rk - 1)) ∧
    (uW ∈ LinearMap.range xb → ¬ fker →
      A - (Fintype.card F : ℤ) ^ g * B = -(Fintype.card F : ℤ) ^ (n + g - rk - 1)) ∧
    (uW ∈ LinearMap.range xb → fker → A - (Fintype.card F : ℤ) ^ g * B = 0) ∧
    (uW ∉ LinearMap.range xb → ¬ fker → A - (Fintype.card F : ℤ) ^ g * B = 0)

def InvariantKernelTraceVanishes : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (r : ℕ) (R : Type) [CommRing R]
    (k φ : (Fin r → F) → R),
    (∀ (c : Fˣ) (f : Fin r → F), k ((c : F) • f) = k f) →
    (∀ f, f ≠ 0 → Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP φ f = 0) →
    ∑ f ∈ univ.filter (fun f : Fin r → F => f ≠ 0), k f * φ f = 0

def RootOfUnityCongruenceOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (NumberField.RingOfIntegers K)) (T n : ℕ)
    (b : NumberField.RingOfIntegers K),
    T.Prime → P.IsPrime → (T : NumberField.RingOfIntegers K) ∈ P → 0 < n → b ^ n = 1 →
    b - 1 ∈ P → b ≠ 1 → T - 1 ≤ Module.finrank ℚ K

def Gl (q n : ℕ) (f : Fin n → ZMod q) (ε : ℤ) : Set ((Fin n → ℚ) × ℚ) :=
  {p | ∃ (w : Fin n → ℤ) (k : ℤ), (∀ j, p.1 j = w j) ∧ (q : ℚ) * p.2 = k ∧
    (k : ZMod q) = (ε : ZMod q) * ∑ j, f j * (w j : ZMod q)}

def OverlatticeThreeOrbits : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n : ℕ) (La : AddSubgroup ((Fin n → ℚ) × ℚ)),
    ((0 : Fin n → ℚ), (1 : ℚ)) ∈ La → (∀ p ∈ La, ∃ k : ℤ, (q : ℚ) * p.2 = k) →
    let P1 : Prop := ∀ p ∈ La, (p.1, (0 : ℚ)) ∈ La ∧ ∃ k : ℤ, p.2 = k
    let P2 : Prop := ((0 : Fin n → ℚ), ((q : ℚ))⁻¹) ∈ La ∧ ∀ p ∈ La, (p.1, (0 : ℚ)) ∈ La
    let P3 : Prop := ∃! f : (La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ)) →+ ZMod q,
      Function.Surjective f ∧ ∀ p : (Fin n → ℚ) × ℚ, p ∈ La ↔
        ∃ h : p.1 ∈ La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ), ∃ k : ℤ, (q : ℚ) * p.2 = k ∧
          (k : ZMod q) = f ⟨p.1, h⟩
    (P1 ∨ P2 ∨ P3) ∧ ¬ (P1 ∧ P2) ∧ ¬ (P1 ∧ P3) ∧ ¬ (P2 ∧ P3)

end Formalism.HermitianLattices.RamifiedLatticeOperators
