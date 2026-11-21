import Formalism.SmithDeterminants.StatementGram

open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E

def fock {R τ : Type*} [CommRing R] [StarRing R] (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)

def symFact {σ : Type*} [DecidableEq σ] {a : ℕ} (s : Sym σ a) : ℕ :=
  Formalism.A.mfact (Multiset.toFinsupp (s : Multiset σ))

def symPow {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ) (A : Matrix σ σ R) :
    Matrix (Sym σ a) (Sym σ a) R :=
  Matrix.of fun s t => coeff (Multiset.toFinsupp (t : Multiset σ))
    (((s : Multiset σ).map fun i => ∑ j, C (A i j) * X j).prod)

def symGram {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ)
    (G : Matrix σ σ R) : Matrix (Sym σ a) (Sym σ a) R :=
  symPow a G * Matrix.diagonal fun t => (symFact t : R)

def FockSesq : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R],
    ∃ B : MvPolynomial τ R →ₗ[R] MvPolynomial τ R →ₗ⋆[R] R, ∀ f g, B f g = fock f g

def FockHerm : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R] (f g : MvPolynomial τ R),
    star (fock f g) = fock g f

def FockBridge : Prop :=
  (∀ (τ : Type) (f g : MvPolynomial τ ℤ), Formalism.A.fockZ f g = fock f g) ∧
  (∀ (τ : Type) (f g : MvPolynomial τ GaussianInt), Formalism.A.fockG f g = fock f g)

def FockPerm : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R] (a : ℕ) (x y : Fin a → MvPolynomial τ R),
    (∀ s, (x s).IsHomogeneous 1) → (∀ t, (y t).IsHomogeneous 1) →
    fock (∏ s, x s) (∏ t, y t) = (Matrix.of fun s t => fock (x s) (y t)).permanent

def DetSymPow : Prop :=
  ∀ (R σ : Type) [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ) (A : Matrix σ σ R),
    (symPow a A).det = A.det ^ (Fintype.card σ + a - 1).choose (Fintype.card σ)

end Formalism.E
