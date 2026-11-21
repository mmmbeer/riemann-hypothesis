import Formalism.IncomingBounds.StatementThmP
import Formalism.IncomingBounds.LemmaMNumerics

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

variable {C : Type} [Field C]

def lpart {n0 : ℕ} (m : PVar n0 →₀ ℕ) : PVar n0 →₀ ℕ := m.filter (fun x => x.isLeft = true)

def rpart {n0 : ℕ} (m : PVar n0 →₀ ℕ) : PVar n0 →₀ ℕ := m.filter (fun x => x.isRight = true)

def pp {n0 : ℕ} (Q : MvPolynomial (PVar n0) C) (G : MvPowerSeries (PVar n0) C) :
    MvPowerSeries (PVar n0) C :=
  fun m => if rpart m = 0 then
    ∑ a ∈ Q.support, if lpart a ≤ m then
      MvPolynomial.coeff a Q * (mfact (rpart a) : C) *
        MvPowerSeries.coeff (m - lpart a + rpart a) G
    else 0
  else 0

def psZ (l i n0 : ℕ) : MvPolynomial (PVar n0) ℤ :=
  Matrix.det (Matrix.of fun b c : Fin n0 =>
      MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) -
        (l : MvPolynomial (PVar n0) ℤ) ^ (expE l i) * MvPolynomial.X (Sum.inr (b, c))) -
    Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inl (b, c))) ^ (l ^ i)

def psC (C : Type) [Field C] (l i n0 : ℕ) : MvPolynomial (PVar n0) C :=
  MvPolynomial.map (Int.castRingHom C) (psZ l i n0)

def aP (C : Type) [Field C] (l i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) C) (s : ℕ) : C :=
  jetAt0 (detL C n0 ^ (l ^ i * s)) (pp (psC C l i n0 ^ s) (mvExp h1)) /
    (capNat n0 (l ^ i * s) : C)

def ValNat : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime →
    v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ N : ℕ, N ≠ 0 → v (N : C) = (((padicValNat l N : ℕ) : ℝ) : WithTop ℝ)

def ExpAdd : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (σ : Type) (a b : MvPowerSeries σ C),
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      mvExp (a + b) = mvExp a * mvExp b

def ExpWeight : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime →
    v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (σ : Type) (w : (σ →₀ ℕ) → ℝ), (∀ m m', w (m + m') = w m + w m') →
    ∀ h : MvPowerSeries σ C, MvPowerSeries.constantCoeff h = 0 →
      (∀ m, (((1 / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) ≤
        v (MvPowerSeries.coeff m h) + ((w m : ℝ) : WithTop ℝ)) →
      ∀ m, (0 : WithTop ℝ) ≤ v (MvPowerSeries.coeff m (mvExp h)) + ((w m : ℝ) : WithTop ℝ)

end Formalism.IncomingBounds
