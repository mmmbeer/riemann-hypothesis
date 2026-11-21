import Formalism.LocalToGlobal.Columns.ChainLawXiStmt
import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
import Formalism.LocalToGlobal.Columns.RecLevelSym

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Pts

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}







theorem clX_ext_eN {n c : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) {s : ℕ} (hs : n ≤ s) : clL_ext c κ (Loc.eN E (n + c) s) = Loc.eN E (n + c) s := by
  rw [clL_ext_apply, ciExtM_fix]
  intro l
  unfold Loc.eN
  rw [if_neg (by simp; omega)]


theorem first_sum_scalar_mul {k K : Type} [CommRing k] [Field K] {n' c' n c : ℕ} (psi : k → K) (vals : Finset k) (wt : K) (a : K)
    (Φ : Loc.SF k K (n' + c') (n + c)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => a * Φ x) xj = a * Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Φ xj := by
  unfold Loc.E1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring


end Pts

section Res

variable {k : Type} [CommRing k]

theorem clX_ent_fin {n c : ℕ} (φ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (a : ℕ → ℕ → k)
    (h : ∀ l s, l < n + c → s < n + c → Loc.atN (φ (Loc.eN k (n + c) s)) l = if l < n ∧ s < n then a l s else if l = s then 1 else 0)
    (l s : Fin (n + c)) : φ (Pi.single s 1) l = if l.1 < n ∧ s.1 < n then a l.1 s.1 else if l = s then 1 else 0 := by
  have h1 := h l.1 s.1 l.2 s.2
  rw [residue_basisVec_eq_single s.2] at h1
  unfold Loc.atN at h1
  rw [dif_pos l.2] at h1
  rw [h1]
  by_cases h2 : l.1 < n ∧ s.1 < n
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2, if_neg h2]
    by_cases h3 : l = s
    · rw [if_pos h3, if_pos (congrArg Fin.val h3)]
    · rw [if_neg h3, if_neg (fun h4 => h3 (Fin.ext h4))]

theorem clX_fix_of_ent {n c : ℕ} (φ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (a : ℕ → ℕ → k)
    (h : ∀ l s, l < n + c → s < n + c → Loc.atN (φ (Loc.eN k (n + c) s)) l = if l < n ∧ s < n then a l s else if l = s then 1 else 0) :
    (∀ v (j : Fin c), φ v (Fin.natAdd n j) = v (Fin.natAdd n j)) ∧
    (∀ s, n ≤ s → φ (Loc.eN k (n + c) s) = Loc.eN k (n + c) s) ∧
    (∀ v (l : Fin n), φ v (Fin.castAdd c l) = ∑ m : Fin n, a l.1 m.1 * v (Fin.castAdd c m)) := by
  have hent := clX_ent_fin φ a h
  refine ⟨fun v j => ?_, fun s hs => ?_, fun v l => ?_⟩
  · rw [residue_linearEquiv_apply_eq_sum, Fin.sum_univ_add]
    have e1 : ∀ m : Fin n, φ (Pi.single (Fin.castAdd c m) 1) (Fin.natAdd n j) = 0 := by
      intro m
      rw [hent, if_neg (by simp), if_neg (fun h' => by have := congrArg Fin.val h'; simp at this; omega)]
    have e2 : ∀ m : Fin c, φ (Pi.single (Fin.natAdd n m) 1) (Fin.natAdd n j) = if j = m then 1 else 0 := by
      intro m
      rw [hent, if_neg (by simp)]
      by_cases hm : j = m
      · rw [hm, if_pos rfl, if_pos rfl]
      · rw [if_neg hm, if_neg (fun h' => hm (Fin.ext (by have := congrArg Fin.val h'; simp at this; exact this)))]
    simp only [e1, e2, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · funext l
    rw [residue_linearEquiv_apply_eq_sum]
    by_cases hsN : s < n + c
    · rw [Finset.sum_eq_single (⟨s, hsN⟩ : Fin (n + c))]
      · rw [hent, if_neg (fun h' => by simp at h'; omega)]
        unfold Loc.eN
        by_cases hl : l = ⟨s, hsN⟩
        · subst hl
          simp
        · rw [if_neg hl, zero_mul, if_neg (fun h' => hl (Fin.ext h'))]
      · intro b _ hb
        unfold Loc.eN
        rw [if_neg (fun h' => hb (Fin.ext h')), mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · have h0 : Loc.eN k (n + c) s = 0 := by
        funext l'
        unfold Loc.eN
        rw [if_neg (by omega)]
        rfl
      rw [h0]
      simp
  · rw [residue_linearEquiv_apply_eq_sum, Fin.sum_univ_add]
    have e1 : ∀ m : Fin n, φ (Pi.single (Fin.castAdd c m) 1) (Fin.castAdd c l) = a l.1 m.1 := by
      intro m
      rw [hent, if_pos ⟨by simp, by simp⟩]
      simp
    have e2 : ∀ m : Fin c, φ (Pi.single (Fin.natAdd n m) 1) (Fin.castAdd c l) = 0 := by
      intro m
      rw [hent, if_neg (by simp), if_neg (fun h' => by have := congrArg Fin.val h'; simp at this; omega)]
    simp only [e1, e2, zero_mul, Finset.sum_const_zero, add_zero]

theorem clX_R1cond {n c : ℕ} (φ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (hfix : ∀ v (j : Fin c), φ v (Fin.natAdd n j) = v (Fin.natAdd n j))
    (hvec : ∀ s, n ≤ s → φ (Loc.eN k (n + c) s) = Loc.eN k (n + c) s) : Loc.R1cond k n c φ := by
  refine ⟨fun i v hv => ?_, hvec n le_rfl, fun i => ?_⟩
  · intro l hl
    have hl' : ¬ l.1 < n := fun h' => hl (show l.1 < n + i by omega)
    obtain ⟨j, rfl⟩ : ∃ j : Fin c, Fin.natAdd n j = l := ⟨⟨l.1 - n, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [hfix]
    exact hv _ hl
  · rw [hvec (n + i) (by omega), sub_self]
    exact zero_mem _

end Res

section Assemble

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}


end Assemble

section Deep

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

end Deep

end Formalism.L2.Col
