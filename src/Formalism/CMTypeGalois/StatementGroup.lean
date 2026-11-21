import Mathlib
import Formalism.StatementCM

open Finset

namespace Formalism.Q3

def IsCMTypeG {G : Type*} [Mul G] (c : G) (Φ : Finset G) : Prop := ∀ g : G, g ∈ Φ ↔ c * g ∉ Φ

instance {G : Type*} [Mul G] [Fintype G] [DecidableEq G] (c : G) : DecidablePred (IsCMTypeG c) :=
  fun _ => Fintype.decidableForallFintype

def dualTypeG {G : Type*} [Monoid G] [DecidableEq G] (c : G) (Φ : Finset G) : Finset G :=
  insert 1 ((Φ.erase 1).image (fun g => c * g))

def stabG {G : Type*} [Mul G] [Fintype G] [DecidableEq G] (Φ : Finset G) : Finset G :=
  univ.filter (fun h => ∀ g ∈ Φ, h * g ∈ Φ)

open Classical in

def OddCharSum : Prop :=
  ∀ (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (c : G), c ≠ 1 → c * c = 1 → ∀ s : G,
    ∑ ψ ∈ univ.filter (fun ψ : AddChar (Additive G) ℂ => ψ (Additive.ofMul c) = -1),
        ψ (Additive.ofMul s)
      = ((Fintype.card G : ℂ) / 2) * ((if s = 1 then 1 else 0) - (if s = c then 1 else 0))

abbrev Gal3 := Fin 3 → ℤˣ

def cc : Gal3 := fun _ => -1

def chiS (S : Finset (Fin 3)) (g : Gal3) : ℤˣ := ∏ i ∈ S, g i

def chiQ (q : ℕ) (n : ℤ) : ℤ := jacobiSym n q

def Hyp3 (q : Fin 3 → ℕ) : Prop := (∀ i, (q i).Prime ∧ q i % 4 = 3) ∧ Function.Injective q

def KroneckerMeaning : Prop :=
  ∀ q : ℕ, q.Prime → q % 4 = 3 →
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ q → chiQ q p = jacobiSym (-(q : ℤ)) p) ∧
    (chiQ q 2 = 1 ↔ q % 8 = 7) ∧ chiQ q (-1) = -1

def e3 (i : Fin 3) : Gal3 := Pi.mulSingle i (-1)

def sgn (z : ℤ) : ℤˣ := if z = 1 then 1 else -1

end Formalism.Q3
