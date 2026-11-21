import Formalism.FlagUnipotentLattices.PairingOrthogonalComplement

namespace Formalism.HermitianLatticeCounting.S4

open Finset
open Formalism.SL.IwahoriBlocks (IsHerm eich)

section defs
variable {E : Type*} [CommRing E] {V : Type*} [AddCommGroup V] [Module E V]

def InRR (O : Subring E) (th a a' : E) : Prop := a' ∈ O ∧ ∃ x ∈ O, a + a' = th * x

def latM (O : Subring E) (θ : Eˣ) {n : ℕ} (f f' : Fin n → V) : Submodule O V :=
  Submodule.span O (Set.range f ∪ Set.range (fun i => ((θ⁻¹ : Eˣ) : E) • (f' i - f i)))

def spanY (E : Type*) [CommRing E] {V : Type*} [AddCommGroup V] [Module E V] {n : ℕ} (f f' : Fin n → V)
    (J : ℕ) : Submodule E V :=
  Submodule.span E (f '' {i | i.val < J} ∪ f' '' {i | i.val < J})

def LevelLe (O : Subring E) (abelian₂ : AddSubgroup V) (θ : Eˣ) {n : ℕ} (f f' : Fin n → V) (J : ℕ) : Prop :=
  ∀ a a' : Fin n → E, ((θ⁻¹ : Eˣ) : E) • ((∑ i, a i • f i) + (∑ i, a' i • f' i)) ∈ abelian₂ →
    ∀ i, J ≤ i.val → InRR O (θ : E) (a i) (a' i)

end defs

section defs2
variable {E V : Type*} [CommRing E] [StarRing E] [AddCommGroup V] [Module E V]

def capSub {h : V →ₗ[E] V →ₗ⋆[E] E} {O : Subring E} {abelian₂ : AddSubgroup V}
    {O' Lam' : Type*} [CommRing O'] [StarRing O'] [AddCommGroup Lam'] [Module O' Lam']
    {h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O'} {io : O' →+* E} {j : Lam' →+ V}
    (hm : LatModel h O abelian₂ h' io j) (Z : Submodule E V) : Submodule O' Lam' where
  carrier := {w | j w ∈ Z}
  add_mem' := by
    intro a b ha hb
    show j (a + b) ∈ Z
    rw [map_add]; exact Z.add_mem ha hb
  zero_mem' := by
    show j 0 ∈ Z
    rw [map_zero]; exact Z.zero_mem
  smul_mem' := by
    intro c x hx
    show j (c • x) ∈ Z
    rw [hm.j_smul]; exact Z.smul_mem _ hx

def dualIn (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (Z : Submodule E V) :
    AddSubgroup V where
  carrier := {v | v ∈ Z ∧ ∀ w ∈ abelian₂, w ∈ Z → h w v ∈ O}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Z.add_mem ha hb, fun w hw hz => ?_⟩
    rw [map_add]; exact O.add_mem (ha' w hw hz) (hb' w hw hz)
  zero_mem' := ⟨Z.zero_mem, fun w _ _ => by rw [map_zero]; exact O.zero_mem⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Z.neg_mem ha, fun w hw hz => ?_⟩
    rw [map_neg]; exact O.neg_mem (ha' w hw hz)

end defs2

def LevelStep : Prop :=
  ∀ (E : Type) [CommRing E] (V : Type) [AddCommGroup V] [Module E V] (O : Subring E)
    (abelian₂ : AddSubgroup V) (θ : Eˣ) (n : ℕ) (f f' : Fin n → V) (J : Fin n),
    LevelLe O abelian₂ θ f f' J.val →
    ∀ (al al' : E), ∀ l ∈ abelian₂,
      ((θ⁻¹ : Eˣ) : E) • (al • f J + al' • f' J) - l ∈ spanY E f f' J.val → InRR O (θ : E) al al'

def GramSubmersionSplit : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) K)
    (X₁ X₂ : Fin m → Fin n → K) (Hm : Matrix (Fin m) (Fin m) K),
      IsUnit Ph.det → LinearIndependent K X₁ → LinearIndependent K X₂ →
      {Y : (Fin m → Fin n → K) × (Fin m → Fin n → K) | ∀ i j,
          (∑ k, ∑ l, Y.1 i k * Ph k l * X₂ j l) + (∑ k, ∑ l, X₁ i k * Ph k l * Y.2 j l) = Hm i j}.ncard
        * Fintype.card K ^ (m ^ 2) = Fintype.card K ^ (2 * n * m)

end Formalism.HermitianLatticeCounting.S4
