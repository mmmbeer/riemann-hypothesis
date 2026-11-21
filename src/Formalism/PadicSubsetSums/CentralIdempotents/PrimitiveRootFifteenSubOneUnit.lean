import Mathlib

noncomputable section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

def UnitRatio : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E),
    (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
    (∀ ζ : E, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ζ = 1 ∨ ζ = -1) →
    ∀ x : E, x ≠ 0 → IsIntegral ℤ (x / c x) → c x = x ∨ c x = -x

def CircleCharExtends : Prop :=
  ∀ (A : Type) [CommGroup A] (H : Subgroup A) (χ : H →* Circle),
    ∃ χ' : A →* Circle, ∀ h : H, χ' (h : A) = χ h

def expo (D : Multiset ℕ) : Multiset ℤ :=
  D.bind fun d => (Multiset.range d).map fun a : ℕ => (d : ℤ) - 1 - 2 * (a : ℤ)

def CharpolyCoeffClosure : Prop :=
  ∀ (G : Type) [TopologicalSpace G] (R : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (X : Type) [Fintype X] (n : ℕ)
    (r : X → G → Matrix (Fin n) (Fin n) R) (T : Subring (X → R)) (D : Set G),
    (∀ x, Continuous (r x)) → IsClosed (T : Set (X → R)) → Dense D →
    (∀ g ∈ D, ∀ j : ℕ, (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T) →
    ∀ (g : G) (j : ℕ), (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T

def SameResidue : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [Fintype X] (T : Subalgebra O (X → O)),
    IsLocalRing T → ∀ a ∈ T, ∀ x y : X, IsLocalRing.residue O (a x) = IsLocalRing.residue O (a y)

def BrauerNesbitt : Prop :=
  ∀ (k : Type) [Field k] (G : Type) [Group G] (V W : Type) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) τ.asModule →
    (∀ g, (ρ g).charpoly = (τ g).charpoly) →
    ∃ e : V ≃ₗ[k] W, ∀ g, e.toLinearMap ∘ₗ ρ g = τ g ∘ₗ e.toLinearMap

def BrauerNesbittAlg : Prop :=
  ∀ (k A V W : Type) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W],
    IsSemisimpleModule A V → IsSemisimpleModule A W →
    (∀ a : A, (Algebra.lsmul k k V a).charpoly = (Algebra.lsmul k k W a).charpoly) →
    Nonempty (V ≃ₗ[A] W)

def block (q : ℝ) (μ : ℂ) (d : ℕ) : Multiset ℂ :=
  (Multiset.range d).map fun i : ℕ => μ * ((q ^ (((d : ℝ) - 1) / 2 - (i : ℝ)) : ℝ) : ℂ)

def GoodCuspidal : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [Nonempty P] (r : ℕ) (f : P → k[X]) (I : Type) [Fintype I]
    (n d : I → ℕ) (h : P → I → k[X]),
    (∀ v, (f v).natDegree = r) → (∀ v, Squarefree (f v)) → (∀ v, f v = ∏ i, h v i ^ d i) →
    (∀ v i, (h v i).natDegree = n i) → (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ d i) →
    (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ r ∧ ∀ v, ∃ g : k[X], g ∣ f v ∧ g.natDegree = a) →
    (∀ i, d i = 1) ∧ Fintype.card I ≤ 1

def SplitEigenAnnihilator : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (A B : Submodule K V)
    (γ₀ γ : Module.End K V) (c : K), IsCompl A B → (∀ v ∈ A, γ₀ v = v) → (∀ v ∈ A, γ v = v) →
    (∀ v ∈ B, γ v = c • v) → (γ₀ - 1) * (γ - algebraMap K (Module.End K V) c) = 0

def UnitEvalOfMultiplicity : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (t : ℕ) (c : O) (s' : O[X]), s'.Monic →
    ((s' * (X - C c) ^ t).map (IsLocalRing.residue O)).rootMultiplicity (IsLocalRing.residue O c) = t →
    IsUnit (s'.eval c)

def ev {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (x : X) : T →+* O :=
  (Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom

def FactorOverLocalSubalgebra : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (t : ℕ) (c : O) (F : T[X]) (s : X' → O[X]),
    (∀ x, F.map (ev T x) = s x * (X - C c) ^ t) → (∀ x, IsUnit ((s x).eval c)) →
    ∃ P : T[X], F = P * (X - C (algebraMap O T c)) ^ t ∧ IsUnit (P.eval (algebraMap O T c)) ∧
      ∀ x, P.map (ev T x) = s x

def CharpolyFactorAnnihilator : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K V) (γ₀ γ : Module.End K V) (c cγ : K) (t : ℕ) (P : K[X]), IsCompl A B →
    (∀ v ∈ A, γ₀ v ∈ A) → (∀ v ∈ A, γ v ∈ A) → (∀ v ∈ B, γ₀ v = c • v) → (∀ v ∈ B, γ v = cγ • v) →
    Module.finrank K B = t → γ₀.charpoly = P * (X - C c) ^ t →
    (aeval γ₀ P) * (γ - algebraMap K (Module.End K V) cγ) = 0

def PrimitiveRootFifteenSubOneUnit : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ζ : R), IsPrimitiveRoot ζ 15 → IsUnit (ζ - 1)

def TwistInvertible : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (γ₀ : Module.End k V) (c : k), c ≠ 0 → ¬ γ₀.HasEigenvalue c →
    Function.Bijective fun v : V => c⁻¹ • γ₀ v - v

end Formalism.IrreducibleCountingLemmas.Z
