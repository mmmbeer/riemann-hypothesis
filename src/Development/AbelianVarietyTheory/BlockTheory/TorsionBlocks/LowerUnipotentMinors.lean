import Mathlib

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials

open MvPolynomial Matrix MeasureTheory

abbrev Var (n p q : ℕ) := Fin n × (Fin p ⊕ Fin q)

abbrev Pol (n p q : ℕ) := MvPolynomial (Var n p q) ℂ

def zPlus (n p q : ℕ) : Matrix (Fin n) (Fin p) (Pol n p q) := fun c a => X (c, Sum.inl a)

def zMinus (n p q : ℕ) : Matrix (Fin n) (Fin q) (Pol n p q) := fun c b => X (c, Sum.inr b)

def subst {n p q : ℕ} (yp : Matrix (Fin n) (Fin p) (Pol n p q))
    (ym : Matrix (Fin n) (Fin q) (Pol n p q)) : Pol n p q →ₐ[ℂ] Pol n p q :=
  aeval fun v : Var n p q => Sum.elim (fun a => yp v.1 a) (fun b => ym v.1 b) v.2

def nextRow {l : ℕ} (a : Fin l → ℕ) (i : Fin l) : ℕ :=
  if h : i.val + 1 < l then a ⟨i.val + 1, h⟩ else 0

section Minors

variable {R : Type*} [CommRing R] {n l : ℕ}

def topMinor (hl : l ≤ n) (y : Matrix (Fin n) (Fin l) R) (i : Fin l) : R :=
  (y.submatrix (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin n))
    (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin l))).det

def botMinor (hl : l ≤ n) (y : Matrix (Fin n) (Fin l) R) (i : Fin l) : R :=
  (y.submatrix (fun k : Fin (i.val + 1) => (⟨n - (i.val + 1) + k.val, by omega⟩ : Fin n))
    (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin l))).det

def powProd (a : Fin l → ℕ) (m : Fin l → R) : R := ∏ i, m i ^ (a i - nextRow a i)

end Minors

def delPlus {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) : Pol n p q :=
  powProd ap (topMinor (by omega) (zPlus n p q))

def delMinus {n p q : ℕ} (h : p + q ≤ n) (am : Fin q → ℕ) : Pol n p q :=
  powProd am (botMinor (by omega) (zMinus n p q))

def del {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ) : Pol n p q :=
  delPlus h ap * delMinus h am

def hookProd {l : ℕ} (a : Fin l → ℕ) : ℝ :=
  (∏ i : Fin l, ((a i + (l - (i.val + 1))).factorial : ℝ)) /
    ∏ i : Fin l, ∏ j ∈ Finset.Ioi i, ((a i : ℝ) - (a j : ℝ) + (j.val : ℝ) - (i.val : ℝ))

section Clauses

variable {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ)

end Clauses

example : hookProd ![2, 1] = 3 := by
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  simp [hookProd, Fin.prod_univ_two, h0, h1, Nat.factorial]
  norm_num

example (k m : ℕ) : del (n := 2) (p := 1) (q := 1) le_rfl ![k] ![m] =
    X (0, Sum.inl 0) ^ k * X (1, Sum.inr 0) ^ m := by
  simp [del, delPlus, delMinus, powProd, nextRow, topMinor, botMinor, zPlus, zMinus,
    Matrix.det_unique]

end GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
