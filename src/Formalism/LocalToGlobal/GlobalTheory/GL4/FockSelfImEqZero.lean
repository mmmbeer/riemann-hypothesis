import Formalism.LocalToGlobal.GlobalTheory.GL4.PLinks
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Formalism.BranchSandwichDivisors.StatementW
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

def BranchingIntegralAt (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n) (T : ℕ) (G : GL (Fin (n + 1)) ℂ) : Prop :=
    ∃ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
      (∀ f ∈ delSq ℂ (n + 1) lt, P f ∈ delSq ℂ n sg) ∧
      (∃ f ∈ delSq ℂ (n + 1) lt, P f ≠ 0) ∧
      (∀ f ∈ delSq ℤ (n + 1) lt, ∃ g ∈ delSq ℤ n sg,
        P (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
      (∀ (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ),
        (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ) →
        ∀ f ∈ delSq ℂ (n + 1) lt, P (sqAct ℂ (n + 1) lt H f) = sqAct ℂ n sg g (P f)) ∧
      (∀ f ∈ delSq ℂ (n + 1) lt,
        (normFock sg (P f) (P f)).re ≤
          Real.exp (-(degP lt sg : ℝ) * Real.log T) *
            ((((Formalism.BranchingDeterminantCap.cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * dimV lt.w) * normTil lt G f)

def BranchingIntegral : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n), Interlace lt sg →
    ∀ (T : ℕ), 0 < T →
    ∀ (G : GL (Fin (n + 1)) ℂ), (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T → BranchingIntegralAt n lt sg T G

def BranchingIntegralNormalised : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n), lt.w (Fin.last n) = 0 → Interlace lt sg →
    ∀ (T : ℕ), 0 < T →
    ∀ (G : GL (Fin (n + 1)) ℂ), (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T → BranchingIntegralAt n lt sg T G




theorem spread_eq {n : ℕ} (lt : DomWeight (n + 1)) :
    lt.spread = lt.w 0 - lt.w (Fin.last n) + ((n : ℤ) + 1) := by
  unfold DomWeight.spread
  rw [dif_pos (Nat.succ_pos n)]
  have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [this]
  push_cast
  rfl




def shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => lam.w i + c
  anti := fun i j h => by have := lam.anti h; simp only; omega







theorem detPow_add (R : Type) [CommRing R] {N : ℕ} (g : GL (Fin N) R) (a b : ℤ) :
    detPow R N g (a + b) = detPow R N g a * detPow R N g b := by
  unfold detPow
  rw [zpow_add, Units.val_mul]



theorem det_blockMat {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : (blockMat g).det = g.det := by
  unfold blockMat
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]












end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree

def colEmb (r n : ℕ) : Fin r × Fin n → Fin r × Fin (n + 1) := fun v => (v.1, v.2.castSucc)

theorem rowGen_rename (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen R a b (rename (colEmb r n) f) =
      Polynomial.map ((rename (colEmb r n) : MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin (n + 1)) R) :
        MvPolynomial (Fin r × Fin n) R →+* MvPolynomial (Fin r × Fin (n + 1)) R) (rowGen R a b f) := by
  have h : (rowGen R (n := n + 1) a b).comp (rename (colEmb r n)) =
      (Polynomial.mapAlgHom (rename (colEmb r n))).comp (rowGen R (n := n) a b) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X, rowGen, aeval_X, Polynomial.coe_mapAlgHom, Polynomial.map_add,
      Polynomial.map_C, colEmb]
    split_ifs <;> simp [colEmb]
  have h2 := congrArg (fun φ => φ f) h
  simpa [Polynomial.coe_mapAlgHom] using h2

theorem rowDiv_rename (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (rename (colEmb r n) f) = rename (colEmb r n) (rowDiv R a b k f) := by
  unfold rowDiv
  rw [rowGen_rename, Polynomial.coeff_map]
  rfl

theorem applyWord_rename (R : Type) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R w (rename (colEmb r n) f) = rename (colEmb r n) (applyWord R w f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih, rowDiv_rename]

theorem lpMinor_rename (R : Type) [CommRing R] {n : ℕ} (s : ℕ) (hr : s ≤ n + 1) (hn : s ≤ n) :
    lpMinor R (r := n + 1) (n := n + 1) s hr (by omega) =
      rename (colEmb (n + 1) n) (lpMinor R (r := n + 1) (n := n) s hr hn) := by
  unfold lpMinor
  rw [show (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _) =
      (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _) from rfl,
    AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, colEmb]
  rfl

theorem hw_rename (R : Type) [CommRing R] {n : ℕ} (ν : Fin (n + 1) → ℕ) (hlast : ν (Fin.last n) = 0) :
    hw R (r := n + 1) (n := n + 1) le_rfl ν =
      rename (colEmb (n + 1) n) (hw R (r := n + 1) (n := n) (Nat.le_succ n) (fun s => ν s.castSucc)) := by
  unfold hw
  rw [Fin.prod_univ_castSucc, map_prod]
  have hl : ν (Fin.last n) - nuNext ν (Fin.last n) = 0 := by rw [hlast]; simp
  rw [hl, pow_zero, mul_one]
  apply Finset.prod_congr rfl
  intro s _
  rw [map_pow]
  have hexp : nuNext ν s.castSucc = nuNext (fun s => ν s.castSucc) s := by
    unfold nuNext
    by_cases h : s.val + 1 < n
    · rw [dif_pos (by simp only [Fin.val_castSucc] <;> omega), dif_pos h]
      rfl
    · rw [dif_neg h]
      have hs : s.val + 1 = n := by omega
      rw [dif_pos (by simp only [Fin.val_castSucc] <;> omega)]
      have : (⟨(s.castSucc : Fin (n + 1)).val + 1, by simp only [Fin.val_castSucc] <;> omega⟩ : Fin (n + 1)) = Fin.last n :=
        Fin.ext (by simp only [Fin.val_castSucc, Fin.val_last] <;> omega)
      rw [this, hlast]
  rw [hexp]
  congr 1
  exact lpMinor_rename R (s.val + 1) (by omega) (by omega)

theorem natW_last {n : ℕ} (lam : DomWeight (n + 1)) : lam.natW (Fin.last n) = 0 := by
  unfold DomWeight.natW DomWeight.detShift
  rw [dif_pos (Nat.succ_pos n)]
  have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [this]
  simp

theorem delSq_eq_map (R : Type) [CommRing R] {n : ℕ} (lam : DomWeight (n + 1)) :
    delSq R (n + 1) lam =
      (weyl R (n + 1) n (Nat.le_succ n) (fun s => lam.natW s.castSucc)).map
        (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _).toLinearMap := by
  unfold delSq weyl
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext w
  change applyWord R w (hw R le_rfl lam.natW) =
    rename (colEmb (n + 1) n) (applyWord R w (hw R (Nat.le_succ n) fun s => lam.natW s.castSucc))
  rw [← applyWord_rename, ← hw_rename R lam.natW (natW_last lam)]

theorem rowAct_rename (R : Type) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowAct R g (rename (colEmb r n) f) = rename (colEmb r n) (rowAct R g f) := by
  have h : (rowAct R (n := n + 1) g).comp (rename (colEmb r n)) =
      (rename (colEmb r n)).comp (rowAct R (n := n) g) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct, colEmb, map_sum]
  exact congrArg (fun φ => φ f) h

theorem blockMat_eq_extM {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : blockMat g = Formalism.BranchingDeterminantCap.extM ℂ g := by
  ext a b
  unfold blockMat Formalism.BranchingDeterminantCap.extM
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last, Fin.ext_iff]
    omega
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last, Fin.ext_iff]
    omega
  · simp [Matrix.reindex_apply]


theorem sqAct_of_last_zero (R : Type) [CommRing R] {n : ℕ} (lt : DomWeight (n + 1))
    (h0 : lt.w (Fin.last n) = 0) (H : GL (Fin (n + 1)) R) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) R) :
    sqAct R (n + 1) lt H f = rowAct R (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R).transpose f := by
  have hd : lt.detShift = 0 := by
    unfold DomWeight.detShift
    rw [dif_pos (Nat.succ_pos n)]
    have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
    rw [this, h0]
  unfold sqAct detPow
  rw [hd, zpow_zero, Units.val_one, one_smul]

theorem fockF_rename {σ τ : Type} (e : σ → τ) (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (rename e f) (rename e g) = Formalism.REAL.fockF f g := by
  classical
  unfold Formalism.REAL.fockF
  rw [support_rename_of_injective he, Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  have hp := Finsupp.prod_mapDomain_index_inj (s := α) (h := fun (_ : τ) (v : ℕ) => v.factorial) he
  unfold Finsupp.prod at hp
  rw [hp]

theorem colEmb_inj (r n : ℕ) : Function.Injective (colEmb r n) := by
  intro v w h
  simp only [colEmb, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castSucc_injective _ h.2)

theorem scaleMat_eq_zScale (n : ℕ) (T : ℝ) : scaleMat n T = Formalism.BranchingDeterminantCap.zScale n (Real.sqrt T) := rfl

theorem scaleMat_transpose (n : ℕ) (T : ℝ) : (scaleMat n T).transpose = scaleMat n T := by
  unfold scaleMat
  exact Matrix.diagonal_transpose _

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility

theorem hw_add_const (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) :
    hw R (r := m + 1) (n := m + 1) le_rfl (fun s => ν s + c) =
      hw R (r := m + 1) (n := m + 1) le_rfl ν * lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c := by
  unfold hw
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
  congr 1
  · apply Finset.prod_congr rfl
    intro s _
    congr 1
    unfold nuNext
    have h : (s.castSucc : Fin (m + 1)).val + 1 < m + 1 := by simp only [Fin.val_castSucc]; omega
    rw [dif_pos h, dif_pos h]
    dsimp only
    omega
  · have h : ¬ ((Fin.last m : Fin (m + 1)).val + 1 < m + 1) := by simp
    unfold nuNext
    rw [dif_neg h, dif_neg h]
    dsimp only
    rw [Nat.sub_zero, Nat.sub_zero, pow_add]
    rfl

theorem rowGen_det (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    rowGen R a b (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a b).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b
        (((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b +
          (Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    ext p q
    by_cases hp : p = b
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_add_smul_self _ (Ne.symm hab)]

theorem rowDiv_det_mul (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a b k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * rowDiv R a b k f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_det R a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul]

theorem rowGen_det_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) :
    rowGen R a a (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      (1 + Polynomial.X) * Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a a).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a
        ((1 + Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    refine Matrix.ext fun p q => ?_
    by_cases hp : p = a
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

theorem rowDiv_det_mul_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a a k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ((c.choose p.1 : ℕ) : MvPolynomial (Fin m × Fin m) R) * rowDiv R a a p.2 f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_det_self, mul_pow, ← Polynomial.C_pow, mul_comm ((1 + Polynomial.X) ^ c) _,
    mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [add_comm (1 : Polynomial (MvPolynomial (Fin m × Fin m) R)), Polynomial.coeff_X_add_one_pow]

theorem rowDiv_add (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add, Polynomial.coeff_add]

theorem rowDiv_smul (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (t : R) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (t • f) = t • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

theorem rowDiv_zero (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    rowDiv R a b k (0 : MvPolynomial (Fin r × Fin n) R) = 0 := by
  unfold rowDiv
  rw [map_zero, Polynomial.coeff_zero]

theorem rowDiv_mem_weyl (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) : rowDiv R a b k f ∈ weyl R r n hn ν := by
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  | zero => rw [rowDiv_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [rowDiv_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [rowDiv_smul]; exact Submodule.smul_mem _ t hx

theorem det_mul_mem_weyl (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ)
    (g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) (hg : g ∈ weyl R (m + 1) (m + 1) le_rfl ν) :
    lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * g ∈
      weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) := by
  set D := lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c with hD
  set W' := weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) with hW'
  have key : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ), D * applyWord R w (hw R le_rfl ν) ∈ W' := by
    intro w
    induction w with
    | nil =>
      simp only [applyWord, List.foldr_nil]
      rw [hD, mul_comm, ← hw_add_const]
      exact Submodule.subset_span ⟨[], rfl⟩
    | cons x w ih =>
      obtain ⟨a, b, k⟩ := x
      show D * rowDiv R a b k (applyWord R w (hw R le_rfl ν)) ∈ W'
      set g := applyWord R w (hw R le_rfl ν)
      by_cases hab : a = b
      · subst hab
        induction k using Nat.strong_induction_on with
        | _ k ihk =>
          have h1 := rowDiv_det_mul_self R a k c g
          have hmem : ((0 : ℕ), k) ∈ Finset.HasAntidiagonal.antidiagonal k := by simp
          rw [← Finset.add_sum_erase _ _ hmem] at h1
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
          have h2 : D * rowDiv R a a k g = rowDiv R a a k (D * g) -
              ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (0, k),
                D * (((c.choose p.1 : ℕ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) * rowDiv R a a p.2 g) := by
            rw [hD, h1, mul_add, Finset.mul_sum]
            ring
          rw [h2]
          refine Submodule.sub_mem _ (rowDiv_mem_weyl R le_rfl _ a a k _ ih) ?_
          refine Submodule.sum_mem _ fun p hp => ?_
          have hp2 : p.2 < k := by
            rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
            have hne : p.1 ≠ 0 := fun h => hp.1 (Prod.ext h (by simp; omega))
            omega
          rw [mul_left_comm, ← nsmul_eq_mul]
          exact Submodule.smul_of_tower_mem _ _ (ihk p.2 hp2)
      · rw [← rowDiv_det_mul R a b hab]
        exact rowDiv_mem_weyl R le_rfl _ a b k _ ih
  unfold weyl at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact key w
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx

theorem initMinor_id_eq_lpMinor (R : Type) [CommRing R] (m : ℕ) :
    initMinor R (r := m) (n := m) (s := m) id le_rfl = lpMinor R (r := m) (n := m) m le_rfl le_rfl := by
  unfold initMinor lpMinor
  congr 1

theorem xnN_det_mul {m : ℕ} (ν : Fin (m + 1) → ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ dualWeyl ℂ (m + 1) (m + 1) ν) :
    Formalism.BranchingDeterminantCap.xnN (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl * f) =
      Formalism.BranchingDeterminantCap.xnC (m + 1) (Formalism.BranchingDeterminantCap.xnLam ν) (m + 1) * Formalism.BranchingDeterminantCap.xnN f := by
  rw [← initMinor_id_eq_lpMinor]
  apply Formalism.BranchingDeterminantCap.xn_L id Function.injective_id (Formalism.BranchingDeterminantCap.xnLam ν) f
  · intro t s hts
    exact Formalism.BranchingDeterminantCap.xn_hR hf t s hts
  · intro s
    have h := Formalism.BranchingDeterminantCap.xn_hW hf s
    have hs : Formalism.BranchingDeterminantCap.xnLam ν s.val = ν s := by
      unfold Formalism.BranchingDeterminantCap.xnLam
      rw [dif_pos s.isLt]
    rw [hs]
    exact h

theorem xnC_pos (M : ℕ) (mm : ℕ → ℕ) : 0 < Formalism.BranchingDeterminantCap.xnC M mm M := by
  unfold Formalism.BranchingDeterminantCap.xnC
  apply Finset.prod_pos
  intro q hq
  rw [Finset.mem_range] at hq
  have h1 : (q : ℝ) < M := by exact_mod_cast hq
  have h2 : (0 : ℝ) ≤ (mm q : ℝ) := Nat.cast_nonneg _
  linarith

def detConst {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) : ℝ :=
  ∏ j ∈ Finset.range c, Formalism.BranchingDeterminantCap.xnC (m + 1) (Formalism.BranchingDeterminantCap.xnLam (fun s => ν s + j)) (m + 1)

theorem detConst_pos {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) : 0 < detConst ν c :=
  Finset.prod_pos fun _ _ => xnC_pos _ _

theorem xnN_det_pow_mul {m : ℕ} (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (c : ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν) :
    Formalism.BranchingDeterminantCap.xnN (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f) = detConst ν c * Formalism.BranchingDeterminantCap.xnN f := by
  induction c with
  | zero => simp [detConst]
  | succ c ih =>
    have hmem : lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f ∈
        dualWeyl ℂ (m + 1) (m + 1) (fun s => ν s + c) :=
      Formalism.GradedWeylDivisibility.weylLeDual ℂ (m + 1) (m + 1) le_rfl _ (fun a b h => Nat.add_le_add_right (hν h) c) (det_mul_mem_weyl ℂ ν c f hf)
    rw [pow_succ', mul_assoc, xnN_det_mul _ _ hmem, ih, detConst, detConst, Finset.prod_range_succ]
    ring

theorem fockF_self_eq {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = ((Formalism.BranchingDeterminantCap.xnN f : ℝ) : ℂ) := by
  unfold Formalism.BranchingDeterminantCap.xnN
  rw [Formalism.GradedWeylDivisibility.LFockb_fockF_self, Complex.ofReal_re]

theorem fock_ratio_det_pow {m : ℕ} (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (c : ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν) :
    Formalism.REAL.fockF (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f)
              (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f) /
      Formalism.REAL.fockF (hw ℂ le_rfl (fun s => ν s + c)) (hw ℂ le_rfl (fun s => ν s + c)) =
    Formalism.REAL.fockF f f / Formalism.REAL.fockF (hw ℂ le_rfl ν) (hw ℂ le_rfl ν) := by
  have hhw : hw ℂ le_rfl ν ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν := Submodule.subset_span ⟨[], rfl⟩
  rw [hw_add_const, mul_comm (hw ℂ le_rfl ν), fockF_self_eq, fockF_self_eq, fockF_self_eq, fockF_self_eq,
    xnN_det_pow_mul ν hν c f hf, xnN_det_pow_mul ν hν c _ hhw, ← Complex.ofReal_div, ← Complex.ofReal_div,
    mul_div_mul_left _ _ (detConst_pos ν c).ne']

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)

theorem fock_eq_sum_coeff {σ : Type} (f g : MvPolynomial σ ℂ) (t : Finset (σ →₀ ℕ)) (ht : f.support ⊆ t) :
    fockF f g = ∑ m ∈ t, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset ht
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

theorem fockF_add_left_g_l4 {σ : Type} (f f' g : MvPolynomial σ ℂ) :
    fockF (f + f') g = fockF f g + fockF f' g := by
  classical
  rw [fock_eq_sum_coeff (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fock_eq_sum_coeff f g (f.support ∪ f'.support) Finset.subset_union_left,
    fock_eq_sum_coeff f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fock_conj_symm {σ : Type} (f g : MvPolynomial σ ℂ) : fockF g f = star (fockF f g) := by
  classical
  rw [fock_eq_sum_coeff g f (f.support ∪ g.support) Finset.subset_union_right,
    fock_eq_sum_coeff f g (f.support ∪ g.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [star_mul', star_mul', star_star, star_natCast]
  ring

theorem fockF_add_right_g_l4 {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

theorem fockF_smul_left' {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (c • f) g = c * fockF f g := by
  rw [fock_eq_sum_coeff (c • f) g f.support MvPolynomial.support_smul]
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockF_smul_right_eq_star_mul {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fock_self_re_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (fockF f f).re := by
  by_cases hf : f = 0
  · subst hf
    unfold fockF
    simp
  · exact (Formalism.GradedWeylDivisibility.fockPos σ f hf).1.le

theorem fock_self_im_eq_zero {σ : Type} (f : MvPolynomial σ ℂ) : (fockF f f).im = 0 := by
  by_cases hf : f = 0
  · subst hf
    unfold fockF
    simp
  · exact (Formalism.GradedWeylDivisibility.fockPos σ f hf).2

theorem fock_self_eq_re {σ : Type} (f : MvPolynomial σ ℂ) : fockF f f = (((fockF f f).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [fock_self_im_eq_zero f]

def fockLin {σ : Type} (G : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun F := fockF F G
  map_add' F F' := fockF_add_left_g_l4 F F' G
  map_smul' c F := by rw [fockF_smul_left', smul_eq_mul, RingHom.id_apply]

theorem fockLin_apply {σ : Type} (G F : MvPolynomial σ ℂ) : fockLin G F = fockF F G := rfl

def FockSp (σ : Type) : Type := MvPolynomial σ ℂ

instance (σ : Type) : AddCommGroup (FockSp σ) := inferInstanceAs (AddCommGroup (MvPolynomial σ ℂ))
instance (σ : Type) : Module ℂ (FockSp σ) := inferInstanceAs (Module ℂ (MvPolynomial σ ℂ))

instance fockCore (σ : Type) : InnerProductSpace.Core ℂ (FockSp σ) where
  inner f g := fockF (show MvPolynomial σ ℂ from g) (show MvPolynomial σ ℂ from f)
  conj_inner_symm x y := by
    show (starRingEnd ℂ) (fockF (show MvPolynomial σ ℂ from x) (show MvPolynomial σ ℂ from y)) =
      fockF (show MvPolynomial σ ℂ from y) (show MvPolynomial σ ℂ from x)
    rw [starRingEnd_apply, ← fock_conj_symm]
  re_inner_nonneg x := fock_self_re_nonneg (show MvPolynomial σ ℂ from x)
  add_left x y z := fockF_add_right_g_l4 (show MvPolynomial σ ℂ from z) (show MvPolynomial σ ℂ from x)
    (show MvPolynomial σ ℂ from y)
  smul_left x y r := by
    show fockF (show MvPolynomial σ ℂ from y) (r • (show MvPolynomial σ ℂ from x)) = _
    rw [fockF_smul_right_eq_star_mul, starRingEnd_apply]
  definite x hx := by
    by_contra hne
    have h := (Formalism.GradedWeylDivisibility.fockPos σ (show MvPolynomial σ ℂ from x) hne).1
    have h0 : fockF (show MvPolynomial σ ℂ from x) (show MvPolynomial σ ℂ from x) = 0 := hx
    rw [h0, Complex.zero_re] at h
    exact lt_irrefl _ h

instance (σ : Type) : NormedAddCommGroup (FockSp σ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (FockSp σ) _ _ _ (fockCore σ)

instance (σ : Type) : InnerProductSpace ℂ (FockSp σ) := InnerProductSpace.ofCore (fockCore σ).toCore


theorem fock_cauchy_schwarz {σ : Type} (f g : MvPolynomial σ ℂ) : ‖fockF f g‖ ^ 2 ≤ (fockF f f).re * (fockF g g).re := by
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (show FockSp σ from f) (show FockSp σ from g)
  have h' : ‖fockF g f‖ * ‖fockF f g‖ ≤ (fockF f f).re * (fockF g g).re := h
  rw [fock_conj_symm f g, norm_star] at h'
  rw [sq]
  exact h'

theorem fock_adjoint_bound {κ ι : Type} (p : MvPolynomial κ ℂ) (Y J : MvPolynomial ι ℂ) (K : ℝ) (hK : 0 ≤ K)
    (h1 : fockF p p = fockF Y J) (h2 : (fockF J J).re ≤ K * (fockF p p).re) :
    (fockF p p).re ≤ K * (fockF Y Y).re := by
  have hP : 0 ≤ (fockF p p).re := fock_self_re_nonneg p
  have hYn : 0 ≤ (fockF Y Y).re := fock_self_re_nonneg Y
  have hJn : 0 ≤ (fockF J J).re := fock_self_re_nonneg J
  have hcs := fock_cauchy_schwarz Y J
  have hre : (fockF p p).re ≤ ‖fockF Y J‖ := by
    rw [h1]
    exact RCLike.re_le_norm (fockF Y J)
  nlinarith [mul_le_mul_of_nonneg_left h2 hYn, mul_self_le_mul_self hP hre, mul_nonneg hK hYn]




end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
