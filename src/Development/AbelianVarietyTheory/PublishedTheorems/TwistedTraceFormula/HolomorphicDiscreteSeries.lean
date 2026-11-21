import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

noncomputable section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta

namespace GlobalTheory.HolDS

variable {n : ℕ}

def IsHolChamber (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  ∀ a b, ε a = true → ε b = false → lam b < lam a

def pPlus (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ a b, ¬ (ε a = true ∧ ε b = false) → Z a b = 0}

def pMinus (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ b a, ¬ (ε b = false ∧ ε a = true) → Z b a = 0}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def raisingSpan (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  Submodule.span ℂ {w | ∃ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) ∧
    ∃ v ∈ S, w = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v}

def IsLowestWeightOver (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧
      μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
  (∀ v, IsKFin ε σ v → SmoothVec {X | inG ε X} σ v) ∧
  (∀ Z ∈ pMinus ε, ∀ v ∈ lowKSub ε lam σ, GlobalTheory.SmVec.dRepC (Jm ε) σ Z v = 0) ∧
  ∀ v, IsKFin ε σ v ↔ v ∈ raisingSpan ε σ (lowKSub ε lam σ)

end GlobalTheory.HolDS

namespace GlobalTheory.Published

open GlobalTheory.HolDS

def HolomorphicDiscreteSeries : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ → IsLowestWeightOver ε lam σ

end GlobalTheory.Published

namespace GlobalTheory.HolDS

open Formalism.L2.NTheta

variable {n : ℕ}

theorem single_mem_pPlus {ε : Fin n → Bool} {a b : Fin n} (ha : ε a = true) (hb : ε b = false) (z : ℂ) :
    Matrix.single a b z ∈ pPlus ε := by
  intro c d h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨ha, hb⟩

theorem IsHolChamber.lt {ε : Fin n → Bool} {lam : Fin n → ℝ} (h : IsHolChamber ε lam) (hl : StrictAnti lam)
    {a b : Fin n} (ha : ε a = true) (hb : ε b = false) : a < b :=
  hl.lt_iff_gt.1 (h a b ha hb)



variable {p q : ℕ} {κ : Fin p ⊕ Fin q → ℤ}

theorem strictAnti_holEnt (h : HolOK p q κ) :
    StrictAnti fun c : Fin (p + q) => holEnt p q κ (finSumFinEquiv.symm c) := by
  intro c d hcd
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective c
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective d
  simp only [Equiv.symm_apply_apply]
  rw [Fin.lt_def] at hcd
  rcases x with i | i <;> rcases y with j | j <;> simp at hcd
  · have h1 : ((κ (Sum.inl j) : ℤ) : ℚ) ≤ κ (Sum.inl i) := by exact_mod_cast h.1 i j (Fin.le_def.2 (by omega))
    have h2 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hcd
    simp only [holEnt, Sum.elim_inl]
    linarith
  · exact h.2.2 i j
  · omega
  · have h1 : ((κ (Sum.inr j) : ℤ) : ℚ) ≤ κ (Sum.inr i) := by exact_mod_cast h.2.1 i j (Fin.le_def.2 (by omega))
    have h2 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hcd
    simp only [holEnt, Sum.elim_inr]
    linarith


theorem enum_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    ∃ hn : p + q = n, ∀ x, lam (Fin.cast hn (finSumFinEquiv x)) = holEnt p q κ x ∧
      ε (Fin.cast hn (finSumFinEquiv x)) = Sum.elim (fun _ => true) (fun _ => false) x := by
  obtain ⟨hl, r, hr, hS⟩ := he
  have hra : StrictAnti r := fun a b hab => by
    have := hl hab
    rw [hr, hr] at this
    exact_mod_cast this
  have hs := strictAnti_holEnt h
  have hinj : Function.Injective (holEnt p q κ) := fun x y hxy =>
    finSumFinEquiv.injective (hs.injective (by simpa using hxy))
  have hn : p + q = n := by
    have := congrArg Finset.card hS
    unfold holPar at this
    rw [Finset.card_image_of_injective _ fun x y hxy => hinj (congrArg Prod.fst hxy),
      Finset.card_image_of_injective _ fun x y hxy => hra.injective (congrArg Prod.fst hxy)] at this
    simpa using this
  subst hn
  have hm : ∀ z, (∃ x, (holEnt p q κ x, Sum.elim (fun _ => true) (fun _ => false) x) = z) ↔
      ∃ a, (r a, ε a) = z := fun z => by
    simpa [holPar] using Finset.ext_iff.1 hS z
  have hrr : (fun c : Fin (p + q) => holEnt p q κ (finSumFinEquiv.symm c)) = r := by
    rw [← hs.range_inj hra]
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := (hm _).1 ⟨finSumFinEquiv.symm c, rfl⟩
      exact ⟨a, congrArg Prod.fst ha⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := (hm _).2 ⟨a, rfl⟩
      exact ⟨finSumFinEquiv x, by simpa using congrArg Prod.fst hx⟩
  refine ⟨rfl, fun x => ?_⟩
  have h1 : r (finSumFinEquiv x) = holEnt p q κ x := by rw [← hrr]; simp
  refine ⟨by rw [Fin.cast_eq_self, hr, h1], ?_⟩
  obtain ⟨y, hy⟩ := (hm _).2 ⟨finSumFinEquiv x, rfl⟩
  obtain rfl : y = x := hinj ((congrArg Prod.fst hy).trans h1)
  exact (congrArg Prod.snd hy).symm


theorem lowK_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    ∃ hn : p + q = n, ∀ x, lowK ε lam (Fin.cast hn (finSumFinEquiv x)) = κ x := by
  obtain ⟨rfl, hx⟩ := enum_holPar h he
  simp only [Fin.cast_eq_self] at hx
  refine ⟨rfl, fun x => ?_⟩
  have hc : ∀ P : Fin (p + q) → Prop, ∀ _ : DecidablePred P, (univ.filter P).card =
      (univ.filter fun i : Fin p => P (finSumFinEquiv (Sum.inl i))).card +
        (univ.filter fun j : Fin q => P (finSumFinEquiv (Sum.inr j))).card := by
    intro P _
    simp only [Finset.card_filter]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Fin.cast_eq_self, lowK, Pi.add_apply, Pi.sub_apply, rhoN, rhoC]
  rw [hc, hc, hc, hc, (hx x).1]
  simp only [(hx _).2]
  rcases x with i | i
  · have h1 : ∀ j : Fin q, Fin.castAdd q i < Fin.natAdd p j := fun j => by
      rw [Fin.lt_def]; simp; omega
    have h2 : ∀ j : Fin q, ¬ Fin.natAdd p j < Fin.castAdd q i := fun j => (h1 j).not_gt
    have h3 : ∀ j j' : Fin p, Fin.castAdd q j < Fin.castAdd q j' ↔ j < j' := fun j j' => by
      rw [Fin.lt_def, Fin.lt_def (a := j)]; simp
    have h4 : (((p - 1 - i : ℕ)) : ℝ) = p - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp [holEnt, h1, h2, h3, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, h4]
    ring
  · have h1 : ∀ j : Fin p, Fin.castAdd q j < Fin.natAdd p i := fun j => by
      rw [Fin.lt_def]; simp; omega
    have h2 : ∀ j : Fin p, ¬ Fin.natAdd p i < Fin.castAdd q j := fun j => (h1 j).not_gt
    have h3 : ∀ j j' : Fin q, Fin.natAdd p j < Fin.natAdd p j' ↔ j < j' := fun j j' => by
      rw [Fin.lt_def, Fin.lt_def (a := j)]; simp
    have h4 : (((q - 1 - i : ℕ)) : ℝ) = q - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp [holEnt, h1, h2, h3, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, h4]
    ring

end GlobalTheory.HolDS

namespace GlobalTheory.Published


end GlobalTheory.Published

end
