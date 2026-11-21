import Mathlib

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

def vl {L : Type*} [NormedField L] (ℓ : ℕ) (x : L) : ℝ := -Real.logb ℓ ‖x‖

def lamIdeal (A σ : Type) [CommRing A] (ℓ M : ℕ) : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range fun i : σ => (1 + MvPolynomial.X i) ^ (ℓ ^ M) - 1)

def varIdeal (A σ : Type) [CommRing A] : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range MvPolynomial.X)

def redLam (O σ : Type) [CommRing O] [IsLocalRing O] (ℓ M : ℕ) :
    MvPolynomial σ O →+*
      MvPolynomial σ (IsLocalRing.ResidueField O) ⧸ lamIdeal (IsLocalRing.ResidueField O) σ ℓ M :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.map (IsLocalRing.residue O))

def FewFactors {O σ : Type} [CommRing O] [IsLocalRing O] (ℓ M m : ℕ) (D : MvPolynomial σ O) :
    Prop :=
  ∃ (n : ℕ) (φ : Fin n →
      MvPolynomial σ (IsLocalRing.ResidueField O) ⧸ lamIdeal (IsLocalRing.ResidueField O) σ ℓ M),
    n ≤ m ∧ redLam O σ ℓ M D = ∏ a, φ a ∧
    ∀ a, IsUnit (φ a) ∨ ∃ (i : σ) (u : MvPolynomial σ (IsLocalRing.ResidueField O) ⧸
        lamIdeal (IsLocalRing.ResidueField O) σ ℓ M),
      IsUnit u ∧ φ a = Ideal.Quotient.mk _ (MvPolynomial.X i) * u

def evTw {L : Type} [Field L] {R' : ℕ} (ℓ : ℕ) (z : L) (e'' e' : Fin R' → ℕ) (a : ℤˣ) :
    Fin R' ⊕ Fin R' → L :=
  Sum.elim (fun i => z ^ ((a : ℤ) * ((ℓ ^ e'' i : ℕ) : ℤ)) - 1)
    (fun i => z ^ ((a : ℤ) * ((ℓ ^ e' i : ℕ) : ℤ)) - 1)

def genB {k : Type} [Field k] {m r d R : ℕ} (u : Matrix (Fin R × Bool × Fin r) (Fin m) k)
    (us : Matrix (Fin R × Bool × Fin r) (Fin d) k) (i : Fin R) (x : Fin m → k) (y : Fin d → k) :
    k :=
  ∑ b : Bool, ∑ ρ : Fin r, (u.mulVec x) (i, b, ρ) * (us.mulVec y) (i, b, ρ)

abbrev TruncK (K' : Type) [Field K'] (n : ℕ) : Type := K'[X] ⧸ Ideal.span {(X : K'[X]) ^ n}

def RESModule : Prop :=
  ∀ (K' : Type) [Field K'] (n a C : ℕ) (Φ : Matrix (Fin a) (Fin a) (TruncK K' n))
    (N : Submodule (TruncK K' n) (Fin a → TruncK K' n)),
    C < n → N ≤ LinearMap.ker (Matrix.toLin' Φ) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' Φ) ⧸ N.comap (LinearMap.ker (Matrix.toLin' Φ)).subtype)
      ≤ C →
    ((∀ x ∈ N, (Ideal.Quotient.mk _ X : TruncK K' n) • x = 0 → x = 0) →
      N = ⊥ ∧ Φ.det ∉ Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)}) ∧
    (1 ≤ a → Module.finrank K' ↥(N ⊓ LinearMap.ker
        ((Ideal.Quotient.mk _ X : TruncK K' n) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) ≤ 1 →
      (∃ x, N = Submodule.span (TruncK K' n) {x}) ∧
      ∃ i j : Fin a, ∃ a' : ℕ, ∃ h : a = a' + 1,
        (Matrix.submatrix Φ (fun p : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h i) p))
          (fun q : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h j) q))).det ∉
          Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)})

def gramB {k : Type} [Field k] {m r d R : ℕ} (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k)
    (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t))) (i : Fin R) :
    Matrix (Fin d) (Fin d) k :=
  Matrix.of fun p q => genB u us i (bSel p : Fin m → k) (Pi.single q 1)

end Formalism.CyclotomicNorms
