import Mathlib

noncomputable section

open MvPolynomial
open scoped ContDiff

namespace PositivityTheory.Rg.Pc1

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev Poly (n : ℕ) := MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ

def ev (g : Mat n) : Poly n →+* ℂ :=
  MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2)))

abbrev Mode (ε : Fin n → Bool) := {x : Fin n × Fin n // ε x.1 = true ∧ ε x.2 = false}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

def barM (ε : Fin n → Bool) (Z : Mat n) : Mat n := fun a b => -(sg ε a * sg ε b * Z b a)

def LieU (ε : Fin n → Bool) (Z : Mat n) : Prop := ∀ a b, star (Z a b) = barM ε Z a b

def dZ (ε : Fin n → Bool) (Z : Mat n) : Derivation ℂ (Poly n) (Poly n) :=
  MvPolynomial.mkDerivation ℂ (Sum.elim
    (fun x => ∑ c, (X (Sum.inl (x.1, c)) * C (Z c x.2) - C (Z x.1 c) * X (Sum.inl (c, x.2))))
    (fun x => ∑ c, (X (Sum.inr (x.1, c)) * C (barM ε Z c x.2) - C (barM ε Z x.1 c) * X (Sum.inr (c, x.2)))))

def dM (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (Poly n) (Poly n) := dZ ε (Matrix.single x.1.2 x.1.1 1)

def rP (ε : Fin n → Bool) : Poly n := ∑ x : Mode ε, X (Sum.inl x.1) * X (Sum.inr x.1)

def rM (ε : Fin n → Bool) (g : Mat n) : ℝ := ∑ x : Mode ε, ‖g x.1.1 x.1.2‖ ^ 2

def OmP (ε : Fin n → Bool) : Matrix (Mode ε) (Mode ε) (Poly n) := fun x y => dM ε x (X (Sum.inr y.1))

def detbP (n : ℕ) : Poly n := (Matrix.of fun a b : Fin n => (X (Sum.inr (a, b)) : Poly n)).det

def topP (ε : Fin n → Bool) (M : ℕ) (P : Poly n) : Poly n := detbP n ^ M * P * (OmP ε).det

def IsCutFn (H : ℝ → ℝ) : Prop := ContDiff ℝ ∞ H ∧ ∃ R : ℝ, ∀ x, R ≤ x → H x = 0

def IsProfile (N : ℕ) (G : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ G ∧ (∀ x, 1 ≤ x → G x = 0) ∧ (∀ x, 0 ≤ (-1) ^ N * iteratedDeriv N G x) ∧ iteratedDeriv N G 0 ≠ 0

def bas (ε : Fin n → Bool) (H : ℝ → ℝ) (P : Poly n) (g : Mat n) : ℂ := (H (rM ε g) : ℂ) * ev g P

def adBas (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n) (g : Mat n) : ℂ :=
  bas ε (deriv H) (dZ ε Z (rP ε) * P) g + bas ε H (dZ ε Z P) g

def ShapeM (ε : Fin n → Bool) (d : ℕ) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ H P, IsCutFn H ∧ P.totalDegree ≤ d ∧ φ = bas ε H P}

def StBasDeriv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n), LieU ε Z → IsCutFn H →
    adBas ε Z H P ∈ ShapeM ε (P.totalDegree + 2) ∧ ∀ (g : Mat n) (s : ℝ),
      HasDerivAt (fun u : ℝ => bas ε H P (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)))
        (adBas ε Z H P (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) s

end PositivityTheory.Rg.Pc1
