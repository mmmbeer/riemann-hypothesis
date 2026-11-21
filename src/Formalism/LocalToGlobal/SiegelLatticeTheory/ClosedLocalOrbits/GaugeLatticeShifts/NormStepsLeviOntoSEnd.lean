import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoS
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionMapComm

section
noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Matrix Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace LeviEltPf

section Mat

variable (I : AutInst) {k : ℕ}

abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def colM (b : Fin k → VA I) : Matrix (Fin I.n) (Fin k) (I.E ⊗[I.F] Af I.F) := Matrix.of fun l i => b i l

def rowM (b : Fin k → VA I) : Matrix (Fin k) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  Formalism.UG.cT (sigA I) (colM I b) * Jf I

theorem rowM_mulVec (b : Fin k → VA I) (y : VA I) : rowM I b *ᵥ y = fun i => hA I (b i) y := by
  funext i
  simp only [rowM, colM, hA, Formalism.UG.hform, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem rowM_mul_colM (b d : Fin k → VA I) (i j : Fin k) : (rowM I b * colM I d) i j = hA I (b i) (d j) := by
  have h := congrFun (rowM_mulVec I b (d j)) i
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, colM, Matrix.of_apply]

theorem colM_mulVec (b : Fin k → VA I) (w : Fin k → I.E ⊗[I.F] Af I.F) :
    colM I b *ᵥ w = ∑ i, w i • b i := by
  funext l
  simp only [colM, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cT_add' {m p : Type} (M N : Matrix m p (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (M + N) = Formalism.UG.cT (sigA I) M + Formalism.UG.cT (sigA I) N := by
  ext; simp [Formalism.UG.cT]

theorem cT_sub' {m p : Type} (M N : Matrix m p (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (M - N) = Formalism.UG.cT (sigA I) M - Formalism.UG.cT (sigA I) N := by
  ext; simp [Formalism.UG.cT]

theorem cT_smul' {m p : Type} (a : I.E ⊗[I.F] Af I.F) (M : Matrix m p (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (a • M) = sigA I a • Formalism.UG.cT (sigA I) M := by
  ext; simp [Formalism.UG.cT]

theorem cT_cT {m p : Type} (M : Matrix m p (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (Formalism.UG.cT (sigA I) M) = M := by
  ext; simp [Formalism.UG.cT, sigA_sigA]

theorem cT_Jf : Formalism.UG.cT (sigA I) (Jf I) = Jf I := by
  ext i j
  simp only [Formalism.UG.cT, Jf, Matrix.transpose_apply, Matrix.map_apply, sigA_inclE, J_conj]

def Mk (b d : Fin k → VA I) (X Y : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F)) :
    Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  1 + colM I b * X * rowM I d + colM I d * Y * rowM I b

variable {I}

theorem Mk_mul (b d : Fin k → VA I) (η : I.E ⊗[I.F] Af I.F)
    (hDB : rowM I d * colM I b = η • 1) (hDD : rowM I d * colM I d = 0)
    (hBB : rowM I b * colM I b = 0) (hBD : rowM I b * colM I d = sigA I η • 1)
    (X Y X' Y' : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F)) :
    Mk I b d X Y * Mk I b d X' Y' =
      Mk I b d (X + X' + X * ((η • 1) * X')) (Y + Y' + Y * ((sigA I η • 1) * Y')) := by
  first | exact UpperTheory.Reformulated.B.Qk24.Mk_mul .. | (apply UpperTheory.Reformulated.B.Qk24.Mk_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk24.Mk_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk24.Mk_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk24.Mk_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk24.Mk_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD X Y X' Y' | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD X Y X' | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD X Y | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD X | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I

theorem colM_smul (b : Fin k → VA I) (η : I.E ⊗[I.F] Af I.F) (hb : ∀ i, η • b i = b i)
    (Z : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F)) : colM I b * Z = colM I b * (η • Z) := by
  ext l j
  simp only [Matrix.mul_apply, colM, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congrFun (hb i) l
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [← mul_assoc, mul_comm (b i l) η, h]

theorem Mk_eq_one (b d : Fin k → VA I) (X Y : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F))
    (hX : colM I b * X = 0) (hY : colM I d * Y = 0) : Mk I b d X Y = 1 := by
  simp [Mk, hX, hY]

theorem Mk_cT (b d : Fin k → VA I) (X Y : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (Mk I b d X Y) * Jf I =
      Jf I * Mk I b d (Formalism.UG.cT (sigA I) Y) (Formalism.UG.cT (sigA I) X) := by
  simp only [Mk, rowM, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_one, cT_cT, cT_Jf, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
  abel

end Mat

section Frame

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}

theorem eta_sig {η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hew : η * X.ew = η) : η * sigA X.B.I η = 0 := by
  have h : η * sigA X.B.I η = η * sigA X.B.I η * (X.ew * sigA X.B.I X.ew) := by
    conv_lhs => rw [← hew, map_mul]
    ring
  rw [h, X.ew_orth, mul_zero]

theorem sig_eta_ew {η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hew : η * X.ew = η) : sigA X.B.I η * X.ew = 0 := by
  have h : sigA X.B.I η * X.ew = sigA X.B.I η * (X.ew * sigA X.B.I X.ew) := by
    conv_lhs => rw [← hew, map_mul]
    ring
  rw [h, X.ew_orth, mul_zero]

variable {η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {b d : Fin D.R.k → VA X.B.I}

theorem frame_DB (h : IsDualFrame X u η b d) : rowM X.B.I d * colM X.B.I b = η • 1 := by
  ext i j
  rw [rowM_mul_colM, h.2.2.2.2.2.2.2.1 i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem frame_DD (h : IsDualFrame X u η b d) : rowM X.B.I d * colM X.B.I d = 0 := by
  ext i j
  rw [rowM_mul_colM, ← (h.2.2.2.2.2.1 i).2.2.2, ← (h.2.2.2.2.2.1 j).2.2.2, hA_smul_left, hA_smul_right,
    sigA_sigA]
  have := eta_sig h.2.2.1
  simp only [Matrix.zero_apply]
  linear_combination (hA X.B.I (d i) (d j)) * this

theorem frame_BB (h : IsDualFrame X u η b d) : rowM X.B.I b * colM X.B.I b = 0 := by
  ext i j
  rw [rowM_mul_colM, ← (h.2.2.2.2.2.1 i).2.2.1, ← (h.2.2.2.2.2.1 j).2.2.1, hA_smul_left, hA_smul_right]
  have := eta_sig h.2.2.1
  simp only [Matrix.zero_apply]
  linear_combination (hA X.B.I (b i) (b j)) * this

theorem frame_BD (h : IsDualFrame X u η b d) : rowM X.B.I b * colM X.B.I d = sigA X.B.I η • 1 := by
  ext i j
  rw [rowM_mul_colM, hA_symm, h.2.2.2.2.2.2.2.1 j i, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij]; simp

theorem Mk_inv (h : IsDualFrame X u η b d) (C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (h1 : η • (C * C') = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _)) :
    Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) * Mk X.B.I b d (C' - 1) (Formalism.UG.cT (sigA X.B.I) C - 1)
      = 1 := by
  rw [Mk_mul b d η (frame_DB h) (frame_DD h) (frame_BB h) (frame_BD h)]
  have hid : η * η = η := h.2.1
  apply Mk_eq_one
  · rw [colM_smul b η (fun i => (h.2.2.2.2.2.1 i).2.2.1)]
    have e : η • (C - 1 + (C' - 1) + (C - 1) * ((η • 1) * (C' - 1))) = η • (C * C') - η • 1 := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_add, smul_add, smul_smul, hid]
      have : C - 1 + (C' - 1) + (C - 1) * (C' - 1) = C * C' - 1 := by noncomm_ring
      rw [← smul_add, ← smul_add, this, smul_sub]
    rw [e, h1, sub_self, Matrix.mul_zero]
  · have hsid : sigA X.B.I η * sigA X.B.I η = sigA X.B.I η := by rw [← map_mul, hid]
    rw [colM_smul d (sigA X.B.I η) (fun i => (h.2.2.2.2.2.1 i).2.2.2)]
    have h1' : sigA X.B.I η • (Formalism.UG.cT (sigA X.B.I) C' * Formalism.UG.cT (sigA X.B.I) C) = sigA X.B.I η • 1 := by
      have := congrArg (Formalism.UG.cT (sigA X.B.I)) h1
      rwa [cT_smul', cT_smul', Formalism.UG.cT_mul, Formalism.UG.cT_one] at this
    have e : sigA X.B.I η • (Formalism.UG.cT (sigA X.B.I) C' - 1 + (Formalism.UG.cT (sigA X.B.I) C - 1) +
        (Formalism.UG.cT (sigA X.B.I) C' - 1) * ((sigA X.B.I η • 1) * (Formalism.UG.cT (sigA X.B.I) C - 1))) =
        sigA X.B.I η • (Formalism.UG.cT (sigA X.B.I) C' * Formalism.UG.cT (sigA X.B.I) C) - sigA X.B.I η • 1 := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_add, smul_add, smul_smul, hsid]
      have : Formalism.UG.cT (sigA X.B.I) C' - 1 + (Formalism.UG.cT (sigA X.B.I) C - 1) +
          (Formalism.UG.cT (sigA X.B.I) C' - 1) * (Formalism.UG.cT (sigA X.B.I) C - 1) =
          Formalism.UG.cT (sigA X.B.I) C' * Formalism.UG.cT (sigA X.B.I) C - 1 := by noncomm_ring
      rw [← smul_add, ← smul_add, this, smul_sub]
    rw [e, h1', sub_self, Matrix.mul_zero]

end Frame

section Main

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem hA_sum_smul (x : VA X.B.I) {k : ℕ} (w : Fin k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (b : Fin k → VA X.B.I) :
    hA X.B.I x (∑ l, w l • b l) = ∑ l, w l * hA X.B.I x (b l) := by
  rw [← hL_apply, map_sum]
  simp only [LinearMap.map_smul, hL_apply, smul_eq_mul]

theorem resT_of_mem (v : TR.Pl) {x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E) :
    resT TR v x = TR.res v ⟨x, hx⟩ := dif_pos hx

theorem resT_add (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E)
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) : resT TR v (x + y) = resT TR v x + resT TR v y := by
  rw [resT_of_mem TR v (add_mem hx hy), resT_of_mem TR v hx, resT_of_mem TR v hy, ← map_add]; rfl

theorem resT_sub (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E)
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) : resT TR v (x - y) = resT TR v x - resT TR v y := by
  rw [resT_of_mem TR v (sub_mem hx hy), resT_of_mem TR v hx, resT_of_mem TR v hy, ← map_sub]; rfl

theorem resT_mul (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E)
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) : resT TR v (x * y) = resT TR v x * resT TR v y := by
  rw [resT_of_mem TR v (mul_mem hx hy), resT_of_mem TR v hx, resT_of_mem TR v hy, ← map_mul]; rfl

theorem resT_sum (v : TR.Pl) {k : ℕ} (f : Fin k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hf : ∀ l, f l ∈ IntAf X.B.I.F X.B.I.E) : resT TR v (∑ l, f l) = ∑ l, resT TR v (f l) := by
  rw [resT_of_mem TR v (Subring.sum_mem _ fun l _ => hf l)]
  have e : (⟨∑ l, f l, Subring.sum_mem _ fun l _ => hf l⟩ : ↥(IntAf X.B.I.F X.B.I.E)) =
      ∑ l, (⟨f l, hf l⟩ : ↥(IntAf X.B.I.F X.B.I.E)) := Subtype.ext (by simp)
  rw [e, map_sum]
  exact Finset.sum_congr rfl fun l _ => (resT_of_mem TR v (hf l)).symm

theorem resT_one (v : TR.Pl) : resT TR v 1 = 1 := by
  rw [resT_of_mem TR v (one_mem _)]; exact map_one _

theorem resT_zero (v : TR.Pl) : resT TR v 0 = 0 := by
  rw [resT_of_mem TR v (zero_mem _)]; exact map_zero _

theorem resT_ew (v : TR.Pl) : resT TR v X.ew = 1 := by
  rw [resT_of_mem TR v X.ew_int]
  have e : (⟨X.ew, X.ew_int⟩ : ↥(IntAf X.B.I.F X.B.I.E)) =
      ⟨X.ew * ((1 : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (1 : ↥(IntAf X.B.I.F X.B.I.E)).2⟩ :=
    Subtype.ext (by simp)
  rw [e, TR.res_ew, map_one]

theorem resT_zmod (v : TR.Pl) {x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E)
    (c : Prop) [Decidable c] (h : ZMod' X.B.I X.B.g (x - if c then X.ew else 0)) :
    resT TR v x = if c then 1 else 0 := by
  have hc : (if c then X.ew else 0) ∈ IntAf X.B.I.F X.B.I.E := by
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  have hz : resT TR v (x - if c then X.ew else 0) = 0 := by
    rw [resT_of_mem TR v (sub_mem hx hc)]
    obtain ⟨t, ht, e⟩ := h
    refine (TR.res_ker ⟨_, sub_mem hx hc⟩).2 ⟨X.ew * t, mul_mem X.ew_int ht, ?_⟩ v
    show X.ew * (x - if c then X.ew else 0) = _
    rw [e]; ring
  rw [resT_sub TR v hx hc] at hz
  rw [sub_eq_zero.1 hz]
  split_ifs
  · exact resT_ew TR v
  · exact resT_zero TR v

variable (u : D.what₂.Word)

variable {η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {b d : Fin D.R.k → VA X.B.I}

theorem Mk_int (hb : ∀ i, b i ∈ X.B.I.Lf) (hd : ∀ i, d i ∈ X.B.I.Lf)
    (Xm Ym : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hX : ∀ i j, Xm i j ∈ IntAf X.B.I.F X.B.I.E) (hY : ∀ i j, Ym i j ∈ IntAf X.B.I.F X.B.I.E)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : Mk X.B.I b d Xm Ym *ᵥ y ∈ X.B.I.Lf := by
  simp only [Mk, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, rowM_mulVec, colM_mulVec]
  refine add_mem (add_mem hy (Submodule.sum_mem _ fun i _ => ?_)) (Submodule.sum_mem _ fun i _ => ?_)
  · have hc : (Xm *ᵥ fun j => hA X.B.I (d j) y) i ∈ IntAf X.B.I.F X.B.I.E := by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => mul_mem (hX i j) (hA_int X.B.I (hd j) hy)
    exact X.B.I.Lf.smul_mem (⟨_, hc⟩ : ↥(IntAf X.B.I.F X.B.I.E)) (hb i)
  · have hc : (Ym *ᵥ fun j => hA X.B.I (b j) y) i ∈ IntAf X.B.I.F X.B.I.E := by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => mul_mem (hY i j) (hA_int X.B.I (hb j) hy)
    exact X.B.I.Lf.smul_mem (⟨_, hc⟩ : ↥(IntAf X.B.I.F X.B.I.E)) (hd i)

theorem Mk_fix (Xm Ym : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) {y : VA X.B.I}
    (hfix : ∀ i, hA X.B.I y (b i) = 0 ∧ hA X.B.I y (d i) = 0) : Mk X.B.I b d Xm Ym *ᵥ y = y := by
  have h1 : (fun i => hA X.B.I (d i) y) = 0 := funext fun i => by
    rw [hA_symm, (hfix i).2, map_zero]; rfl
  have h2 : (fun i => hA X.B.I (b i) y) = 0 := funext fun i => by
    rw [hA_symm, (hfix i).1, map_zero]; rfl
  simp only [Mk, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, rowM_mulVec, h1, h2,
    Matrix.mulVec_zero, add_zero]

theorem one_int (i j : Fin D.R.k) :
    (1 : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i j ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem levi_element_exists : LeviElt TR u := by
  intro η b d h C C' hC h1 h2
  obtain ⟨-, -, hew, -, -, hbd, hfix, -, hcong⟩ := id h
  have hb : ∀ i, b i ∈ X.B.I.Lf := fun i => (hbd i).1
  have hd : ∀ i, d i ∈ X.B.I.Lf := fun i => (hbd i).2.1
  have hX : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E := fun i j => by
    rw [Matrix.sub_apply]; exact sub_mem (hC i j).1 (one_int i j)
  have hX' : ∀ i j, (C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E := fun i j => by
    rw [Matrix.sub_apply]; exact sub_mem (hC i j).2 (one_int i j)
  have hY : ∀ i j, (Formalism.UG.cT (sigA X.B.I) C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E := fun i j => by
    rw [Matrix.sub_apply]
    exact sub_mem (sigA_mem X.B.I (hC j i).2) (one_int i j)
  have hY' : ∀ i j, (Formalism.UG.cT (sigA X.B.I) C - 1) i j ∈ IntAf X.B.I.F X.B.I.E := fun i j => by
    rw [Matrix.sub_apply]
    exact sub_mem (sigA_mem X.B.I (hC j i).1) (one_int i j)
  have hMN := Mk_inv h C C' h1
  have hNM := Mk_inv h C' C h2
  let g : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
    ⟨Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1), Mk X.B.I b d (C' - 1) (Formalism.UG.cT (sigA X.B.I) C - 1),
      hMN, hNM⟩
  have hU : g ∈ Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F) := by
    show Formalism.UG.cT (sigA X.B.I) (Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1)) * Jf X.B.I *
      Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) = Jf X.B.I
    rw [Mk_cT]
    simp only [cT_sub', cT_cT, Formalism.UG.cT_one]
    rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
  refine ⟨⟨g, hU⟩, ?_, ?_, ?_⟩
  · show ∀ x, x ∈ X.B.I.Lf ↔ Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) *ᵥ x ∈ X.B.I.Lf
    intro x
    refine ⟨fun hx => Mk_int hb hd _ _ hX hY hx, fun hx => ?_⟩
    have := Mk_int hb hd _ _ hX' hY' hx
    rwa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] at this
  · intro y hy
    exact Mk_fix _ _ (hfix y hy)
  · intro v
    ext i j
    have hBw : (fun l => hA X.B.I (b l) (X.bw j)) = 0 := funext fun l => by
      rw [← (hbd l).2.2.1, X.bw_w j, hA_smul_left, hA_smul_right, ← mul_assoc, sig_eta_ew hew, zero_mul]; rfl
    have hbwL : X.bw j ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 j).1
    have hbwdL : X.bwd i ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 i).2
    have hval : hA X.B.I (X.bwd i) (Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) *ᵥ X.bw j) =
        hA X.B.I (X.bwd i) (X.bw j) + ∑ l, (∑ m, (C - 1) l m * hA X.B.I (d m) (X.bw j)) *
          hA X.B.I (X.bwd i) (b l) := by
      simp only [Mk, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, rowM_mulVec, hBw,
        Matrix.mulVec_zero, add_zero, colM_mulVec, hA_add_right, hA_sum_smul]
      rfl
    show resT TR v (hA X.B.I (X.bwd i) (Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) *ᵥ X.bw j)) =
      resT TR v (C i j)
    have hi1 : ∀ m, hA X.B.I (d m) (X.bw j) ∈ IntAf X.B.I.F X.B.I.E := fun m => hA_int X.B.I (hd m) hbwL
    have hi2 : ∀ l, hA X.B.I (X.bwd i) (b l) ∈ IntAf X.B.I.F X.B.I.E := fun l => hA_int X.B.I hbwdL (hb l)
    have hin : ∀ l, (∑ m, (C - 1) l m * hA X.B.I (d m) (X.bw j)) ∈ IntAf X.B.I.F X.B.I.E := fun l =>
      Subring.sum_mem _ fun m _ => mul_mem (hX l m) (hi1 m)
    rw [hval, resT_add TR v (hA_int X.B.I hbwdL hbwL)
      (Subring.sum_mem _ fun l _ => mul_mem (hin l) (hi2 l)),
      resT_sum TR v _ (fun l => mul_mem (hin l) (hi2 l))]
    simp only [resT_mul TR v (hin _) (hi2 _), resT_sum TR v _ (fun m => mul_mem (hX _ m) (hi1 m)),
      resT_mul TR v (hX _ _) (hi1 _)]
    rw [resT_zmod TR v (hA_int X.B.I hbwdL hbwL) (i = j) (X.bw_dual i j)]
    have e2 : ∀ l, resT TR v (hA X.B.I (X.bwd i) (b l)) = if i = l then 1 else 0 := fun l =>
      resT_zmod TR v (hi2 l) (i = l) (hcong i l).1
    have e3 : ∀ m, resT TR v (hA X.B.I (d m) (X.bw j)) = if m = j then 1 else 0 := fun m =>
      resT_zmod TR v (hi1 m) (m = j) (hcong m j).2
    simp only [e2, e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [Matrix.sub_apply, resT_sub TR v (hC i j).1 (one_int i j), Matrix.one_apply]
    split_ifs
    · rw [resT_one]; ring
    · rw [resT_zero]; ring

end Main

end LeviEltPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Matrix Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace MatLiftPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem near_one (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (P : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hP : ∀ v, P.map (TR.res v) = 1) :
    ∃ T : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • P = ηO • (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) := by
  have h : ∀ i j, ∃ t : ↥(IntAf X.B.I.F X.B.I.E), X.ew * ((P - 1) i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
    intro i j
    have h0 : ∀ v, TR.res v ((P - 1) i j) = 0 := fun v => by
      have := congrFun (congrFun (hP v) i) j
      simp only [Matrix.map_apply] at this
      rw [Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨t, ht, e⟩ := (TR.res_ker _).1 h0
    exact ⟨⟨t, ht⟩, e⟩
  choose T hT using h
  refine ⟨Matrix.of T, ?_⟩
  ext i j
  have e := hT i j
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply] at e ⊢
  generalize ((1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) i j) = o at e ⊢
  push_cast at e ⊢
  linear_combination (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e -
    ((P i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - (o : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * hew

theorem det_near (T : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) :
    ∃ s0 : ↥(IntAf X.B.I.F X.B.I.E), (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det = 1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0 := by
  set J := Ideal.span {((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E))}
  have hm : (Ideal.Quotient.mk J).mapMatrix (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) = 1 := by
    have hg : Ideal.Quotient.mk J ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    ext i j
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.add_apply, *]
  have h1 : Ideal.Quotient.mk J ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det) = 1 := by
    rw [RingHom.map_det, hm, Matrix.det_one]
  have h2 : (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
  exact ⟨a, by rw [mul_comm, ha]; ring⟩

theorem right_inv (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (hj : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ηO)
    (A B : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hAB : ∀ v, (A * B).map (TR.res v) = 1) :
    ∃ B' : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • (A * B') = ηO • 1 := by
  obtain ⟨T, hT⟩ := near_one TR ηO hew (A * B) hAB
  obtain ⟨s0, hs0⟩ := det_near (X := X) T
  obtain ⟨s', hs', e⟩ := hj s0 s0.2
  have e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO := Subtype.ext (by simpa using e)
  refine ⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate), ?_⟩
  have e0 : A * ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate)) =
      (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (A * B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate) := by
    rw [Matrix.mul_smul, Matrix.mul_assoc]
  rw [e0, smul_comm, ← Matrix.smul_mul, hT, Matrix.smul_mul, Matrix.mul_adjugate, hs0, smul_smul, smul_smul]
  congr 1
  linear_combination e'

theorem left_inv (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (hj : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ηO)
    (A B : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hAB : ∀ v, (B * A).map (TR.res v) = 1) :
    ∃ B' : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • (B' * A) = ηO • 1 := by
  obtain ⟨T, hT⟩ := near_one TR ηO hew (B * A) hAB
  obtain ⟨s0, hs0⟩ := det_near (X := X) T
  obtain ⟨s', hs', e⟩ := hj s0 s0.2
  have e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO := Subtype.ext (by simpa using e)
  refine ⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B), ?_⟩
  have e0 : ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B)) * A =
      (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * (B * A)) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc]
  rw [e0, smul_comm, ← Matrix.mul_smul, hT, Matrix.mul_smul, Matrix.adjugate_mul, hs0, smul_smul, smul_smul]
  congr 1
  linear_combination e'

theorem coe_eq (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (P Q : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (h : ηO • (P * Q) = ηO • 1) :
    (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P.map Subtype.val * Q.map Subtype.val) =
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (1 : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by
  ext i j
  have := congrArg (fun M : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E) => ((M i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) h
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Subring.coe_mul, Matrix.map_apply,
    Matrix.one_apply] at this ⊢
  push_cast at this
  split_ifs at this ⊢ <;> simpa using this

theorem integral_matrix_lift_exists : MatLift TR := by
  intro η hη _ hew _ hj s
  set ηO : ↥(IntAf X.B.I.F X.B.I.E) := ⟨η, hη⟩
  have hs : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v, TR.res v c = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j :=
    fun i j => by
      obtain ⟨c, hc⟩ := TR.res_joint (fun v => (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
      exact ⟨c, fun v => congrFun hc v⟩
  have hs' : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v,
      TR.res v c = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j :=
    fun i j => by
      obtain ⟨c, hc⟩ := TR.res_joint (fun v => (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
      exact ⟨c, fun v => congrFun hc v⟩
  choose A hA using hs
  choose B hB using hs'
  have hAm : ∀ v, (Matrix.of A).map (TR.res v) = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := fun v => by
    ext i j; simp [hA]
  have hBm : ∀ v, (Matrix.of B).map (TR.res v) = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) :=
    fun v => by ext i j; simp [hB]
  have hAB : ∀ v, (Matrix.of A * Matrix.of B).map (TR.res v) = 1 := fun v => by
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : ∀ v, (Matrix.of B * Matrix.of A).map (TR.res v) = 1 := fun v => by
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨R', hR'⟩ := right_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hAB
  obtain ⟨L', hL'⟩ := left_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hBA
  have e1 : ηO • L' = ηO • R' := by
    calc ηO • L' = L' * (ηO • (1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E))) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = L' * (ηO • (Matrix.of A * R')) := by rw [hR']
      _ = (ηO • (L' * Matrix.of A)) * R' := by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = ηO • R' := by rw [hL', Matrix.smul_mul, Matrix.one_mul]
  refine ⟨(Matrix.of A).map Subtype.val, R'.map Subtype.val, fun i j => ⟨(A i j).2, (R' i j).2⟩, ?_, ?_, ?_⟩
  · exact coe_eq ηO _ _ hR'
  · refine coe_eq ηO _ _ ?_
    calc ηO • (R' * Matrix.of A) = (ηO • R') * Matrix.of A := by rw [Matrix.smul_mul]
      _ = (ηO • L') * Matrix.of A := by rw [e1]
      _ = ηO • 1 := by rw [Matrix.smul_mul, hL']
  · intro v
    ext i j
    show resT TR v ((A i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j
    rw [LeviEltPf.resT_of_mem TR v (A i j).2]
    exact hA i j v

end MatLiftPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Polynomial Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace SIdemPf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def OverG (v : HeightOneSpectrum (𝓞 X.B.I.F)) : Prop := ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal

theorem val_g (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = v.intValuation ((X.B.g : ℕ) : 𝓞 X.B.I.F) := by
  have h : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) =
      ((algebraMap (𝓞 X.B.I.F) X.B.I.F ((X.B.g : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F) := by
    rw [map_natCast]
    first
    | (simp only [map_natCast, UniformSpace.Completion.coe_natCast]; rfl)
    | (induction X.B.g with
        | zero =>
          simp only [Nat.cast_zero]
          first
          | rfl
          | (rw [WithVal.equiv_symm_zero]; rfl)
          | (simp only [map_zero, UniformSpace.Completion.coe_zero]; rfl)
        | succ n ih =>
          push_cast
          rw [ih, map_add, map_one, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_one]
          rfl)
  rw [h, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

def eS : Af X.B.I.F :=
  ⟨fun v => if OverG X v then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if OverG X v then 1 else 0 : v.adicCompletion X.B.I.F) ∈ v.adicCompletionIntegers X.B.I.F
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem eS_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) : eS X v = if OverG X v then 1 else 0 := rfl

def tS : Af X.B.I.F :=
  ⟨fun v => if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹,
    Filter.Eventually.of_forall fun v => by
      show (if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹) ∈ v.adicCompletionIntegers X.B.I.F
      split_ifs with h
      · exact zero_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, val_g]
        have h1 : v.intValuation ((X.B.g : ℕ) : 𝓞 X.B.I.F) = 1 := by
          refine le_antisymm (v.intValuation_le_one _) (not_lt.1 fun hl => h ?_)
          exact (v.intValuation_lt_one_iff_mem _).1 hl
        rw [h1, inv_one]⟩

theorem tS_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    tS X v = if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹ := rfl

theorem eS_int : eS X ∈ Formalism.UG.intAd X.B.I.F := fun v => by
  show eS X v ∈ v.adicCompletionIntegers X.B.I.F
  rw [eS_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem natCast_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) (m : ℕ) :
    ((m : Af X.B.I.F) : Af X.B.I.F) v = (m : v.adicCompletion X.B.I.F) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    rfl

theorem val_g_lt (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : OverG X v) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) < 1 := by
  rw [val_g]
  exact (v.intValuation_lt_one_iff_mem _).2 h

theorem val_g_eq (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : ¬ OverG X v) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = 1 := by
  rw [val_g]
  exact le_antisymm (v.intValuation_le_one _)
    (not_lt.1 fun hl => h ((v.intValuation_lt_one_iff_mem _).1 hl))

theorem tS_int : tS X ∈ Formalism.UG.intAd X.B.I.F := fun v => by
  show tS X v ∈ v.adicCompletionIntegers X.B.I.F
  rw [tS_apply]
  split_ifs with h
  · exact zero_mem _
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, val_g_eq X v h, inv_one]

theorem one_sub_eS : (1 : Af X.B.I.F) - eS X = ((X.B.g : ℕ) : Af X.B.I.F) * tS X := by
  ext v : 1
  show (1 : v.adicCompletion X.B.I.F) - eS X v = ((X.B.g : ℕ) : Af X.B.I.F) v * tS X v
  rw [natCast_apply, eS_apply, tS_apply]
  split_ifs with h
  · simp
  · have hne : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) ≠ 0 := by
      intro h0
      have := val_g_eq X v h
      rw [h0, map_zero] at this
      exact zero_ne_one this
    rw [sub_zero, mul_inv_cancel₀ hne]

theorem eS_idem : eS X * eS X = eS X := by
  ext v : 1
  show eS X v * eS X v = eS X v
  rw [eS_apply]
  split_ifs <;> simp

theorem unit_on_S (d : ↥(Formalism.UG.intAd X.B.I.F)) :
    ∃ z ∈ Formalism.UG.intAd X.B.I.F, eS X * ((1 + ((X.B.g : ℕ) : Af X.B.I.F) * d) * z) = eS X := by

  have hval : ∀ v, OverG X v →
      Valued.v (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * (d : Af X.B.I.F) v) = 1 := by
    intro v hv
    refine Valuation.map_one_add_of_lt _ ?_
    rw [map_mul]
    have hd : Valued.v ((d : Af X.B.I.F) v) ≤ 1 := d.2 v
    calc Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * Valued.v ((d : Af X.B.I.F) v)
        ≤ Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) := mul_le_of_le_one_right' hd
      _ < 1 := val_g_lt X v hv
  have hmem : ∀ v, (if OverG X v then (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) *
      (d : Af X.B.I.F) v)⁻¹ else 0) ∈ v.adicCompletionIntegers X.B.I.F := by
    intro v
    split_ifs with hv
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval v hv, inv_one]
    · exact zero_mem _
  let z : Af X.B.I.F := ⟨fun v => if OverG X v then (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) *
      (d : Af X.B.I.F) v)⁻¹ else 0, Filter.Eventually.of_forall hmem⟩
  refine ⟨z, fun v => hmem v, ?_⟩
  ext v : 1
  show eS X v * ((1 + ((X.B.g : ℕ) : Af X.B.I.F) v * (d : Af X.B.I.F) v) * z v) = eS X v
  rw [natCast_apply, eS_apply]
  show _ * (_ * (if OverG X v then _ else 0)) = _
  split_ifs with hv
  · have hne : (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * (d : Af X.B.I.F) v) ≠ 0 := by
      intro h0
      have := hval v hv
      rw [h0, map_zero] at this
      exact zero_ne_one this
    rw [mul_inv_cancel₀ hne, mul_one]
  · rw [zero_mul]

def phi : ↥(Formalism.UG.intAd X.B.I.F) →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  (Algebra.TensorProduct.includeRight : Af X.B.I.F →ₐ[X.B.I.F] X.B.I.E ⊗[X.B.I.F] Af X.B.I.F).toRingHom.comp
    (Formalism.UG.intAd X.B.I.F).subtype

theorem phi_apply (a : ↥(Formalism.UG.intAd X.B.I.F)) : phi X a = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (a : Af X.B.I.F) := rfl

theorem phi_mem (a : ↥(Formalism.UG.intAd X.B.I.F)) : phi X a ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Set.mem_union_right _ ⟨a, rfl⟩)

theorem integral_of_mem {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) :
    ∃ p : Polynomial ↥(Formalism.UG.intAd X.B.I.F), p.Monic ∧ p.eval₂ (phi X) s = 0 := by
  show (phi X).IsIntegralElem s
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, hx⟩, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨y, rfl⟩ := hx
      have hi : IsIntegral ℤ (algebraMap (𝓞 X.B.I.E) X.B.I.E y) := y.isIntegral_coe
      obtain ⟨q, hq, hev⟩ := hi
      let f : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := (Algebra.TensorProduct.includeLeft :
        X.B.I.E →ₐ[X.B.I.F] X.B.I.E ⊗[X.B.I.F] Af X.B.I.F).toRingHom
      show (phi X).IsIntegralElem (f (algebraMap (𝓞 X.B.I.E) X.B.I.E y))
      refine ⟨q.map (Int.castRingHom ↥(Formalism.UG.intAd X.B.I.F)), hq.map _, ?_⟩
      rw [Polynomial.eval₂_map, show (phi X).comp (Int.castRingHom ↥(Formalism.UG.intAd X.B.I.F)) =
        f.comp (algebraMap ℤ X.B.I.E) from RingHom.ext_int _ _, ← Polynomial.hom_eval₂, hev, map_zero]
    · exact (phi X).isIntegralElem_map
  | zero => simpa using (phi X).isIntegralElem_map (x := 0)
  | one => simpa using (phi X).isIntegralElem_map (x := 1)
  | add x y _ _ hx hy => exact RingHom.IsIntegralElem.add _ hx hy
  | neg x _ hx =>
    have e : -x = phi X (-1) * x := by rw [map_neg, map_one, neg_one_mul]
    rw [e]
    exact RingHom.IsIntegralElem.mul _ (phi X).isIntegralElem_map hx
  | mul x y _ _ hx hy => exact RingHom.IsIntegralElem.mul _ hx hy

theorem eval₂_mem (r : Polynomial ↥(Formalism.UG.intAd X.B.I.F)) {u : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hu : u ∈ IntAf X.B.I.F X.B.I.E) : r.eval₂ (phi X) u ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (phi_mem X _) (Subring.pow_mem _ hu _)

theorem near_inv {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) :
    ∃ w ∈ IntAf X.B.I.F X.B.I.E, ∃ d : ↥(Formalism.UG.intAd X.B.I.F),
      (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * w =
        phi X (1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) := by
  obtain ⟨p, hp, hps⟩ := integral_of_mem X hs
  have hgphi : phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := map_natCast _ _
  have hsc : (p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).eval₂ (phi X)
      (phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * s) = 0 := Polynomial.scaleRoots_eval₂_eq_zero (phi X) hps

  have hdvd : Polynomial.C ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) ∣
      p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) - Polynomial.X ^ p.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_scaleRoots, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, sub_zero]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hi)) _
    · rw [hi, if_pos rfl, Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul, sub_zero]
      exact dvd_zero _
  obtain ⟨q, hq⟩ := hdvd
  have hsr : p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) =
      Polynomial.X ^ p.natDegree + Polynomial.C ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * q := by
    rw [← hq]; ring
  have hP2 : ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1)).eval₂ (phi X)
      (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) = 0 := by
    rw [Polynomial.eval₂_comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one]
    have e : 1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s - 1 = phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * s := by
      rw [hgphi]; ring
    rw [e]; exact hsc
  obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_sub_C (p := (p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1))
  rw [Polynomial.coeff_zero_eq_eval_zero] at hQ
  have hev := congrArg (Polynomial.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s)) hQ
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, hP2,
    zero_sub] at hev
  have h0 : ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1)).eval 0 =
      (-1) ^ p.natDegree + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * q.eval (-1) := by
    rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, zero_sub, hsr,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  refine ⟨phi X ((-1) ^ (p.natDegree + 1)) * Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s),
    Subring.mul_mem _ (phi_mem X _) (eval₂_mem X Q ?_), (-1) ^ p.natDegree * q.eval (-1), ?_⟩
  · refine Subring.add_mem _ (Subring.one_mem _) (Subring.mul_mem _ ?_ hs)
    rw [← hgphi]; exact phi_mem X _
  · have h2 : ((-1 : ↥(Formalism.UG.intAd X.B.I.F)) ^ p.natDegree) * (-1) ^ p.natDegree = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * (phi X ((-1) ^ (p.natDegree + 1)) *
          Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s))
        = phi X ((-1) ^ (p.natDegree + 1)) * ((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) *
          Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s)) := by ring
      _ = phi X ((-1) ^ (p.natDegree + 1)) * -(phi X (((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp
          (Polynomial.X - 1)).eval 0)) := by rw [hev]
      _ = phi X (-((-1) ^ (p.natDegree + 1)) * ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp
          (Polynomial.X - 1)).eval 0) := by rw [map_mul, map_neg]; ring
      _ = phi X (1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * ((-1) ^ p.natDegree * q.eval (-1))) := by
          congr 1
          rw [h0, pow_succ]
          linear_combination h2

theorem idempotent_places_exists : SIdem X := by
  have hes : (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ⟨eS X, eS_int X⟩ = ⟨eS X, eS_int X⟩ :=
    Subtype.ext (eS_idem X)
  have hone : 1 - (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) = ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * ⟨tS X, tS_int X⟩ :=
    Subtype.ext (by push_cast; exact one_sub_eS X)
  refine ⟨phi X ⟨eS X, eS_int X⟩, phi_mem X _, by rw [← map_mul, hes], ?_,
    ⟨phi X ⟨tS X, tS_int X⟩, phi_mem X _, by
      rw [← map_one (phi X), ← map_sub, hone, map_mul, map_natCast]⟩, ?_⟩
  · rw [phi_apply]
    simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  · intro s hs
    obtain ⟨w, hw, d, hwd⟩ := near_inv X hs
    obtain ⟨z, hz, hzd⟩ := unit_on_S X d
    refine ⟨w * phi X ⟨z, hz⟩, Subring.mul_mem _ hw (phi_mem X _), ?_⟩
    have hR : (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ((1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) * ⟨z, hz⟩) =
        ⟨eS X, eS_int X⟩ := Subtype.ext (by push_cast; exact hzd)
    calc phi X ⟨eS X, eS_int X⟩ * ((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * (w * phi X ⟨z, hz⟩))
        = phi X ⟨eS X, eS_int X⟩ * (((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * w) * phi X ⟨z, hz⟩) := by ring
      _ = phi X ((⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ((1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) * ⟨z, hz⟩)) := by
          rw [hwd, map_mul, map_mul]
      _ = phi X ⟨eS X, eS_int X⟩ := by rw [hR]

end SIdemPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
end
end

section
noncomputable section

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LeviFramePf

open Formalism.L2.SG.Pf.unitaryCongruence

section Gen

variable (I : AutInst) (g : ℕ)

theorem lf_memL_smul {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) {x : VA I} (hx : x ∈ I.Lf) :
    c • x ∈ I.Lf := I.Lf.smul_mem ⟨c, hc⟩ hx

theorem lf_mL_smul {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) {x : VA I} (hx : x ∈ mL I g) :
    c • x ∈ mL I g := (mL I g).smul_mem ⟨c, hc⟩ hx

theorem lf_mem_mL {x : VA I} (hx : x ∈ mL I g) : ∃ y ∈ I.Lf, x = (g : I.E ⊗[I.F] Af I.F) • y := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hx'
    exact ⟨y + y', add_mem hy hy', by rw [smul_add]⟩
  | smul c x _ hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(c : I.E ⊗[I.F] Af I.F) • y, lf_memL_smul I c.2 hy, ?_⟩
    show (c : I.E ⊗[I.F] Af I.F) • ((g : I.E ⊗[I.F] Af I.F) • y) = _
    rw [smul_comm]

theorem lf_mL_le {x : VA I} (hx : x ∈ mL I g) : x ∈ I.Lf := by
  obtain ⟨y, hy, rfl⟩ := lf_mem_mL I g hx
  exact lf_memL_smul I (natCast_mem _ g) hy

private theorem hA_smul_right_eq_mul (I : AutInst) (x y : VA I) (a : I.E ⊗[I.F] Af I.F) :
    hA I x (a • y) = a * hA I x y := by
  unfold hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hA_sub_right_gauge_lattice_shifts (I : AutInst) (x y z : VA I) :
    hA I x (y - z) = hA I x y - hA I x z := by
  unfold hA Formalism.UG.hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem hA_smul_left_eq_sigA_mul (I : AutInst) (x y : VA I) (a : I.E ⊗[I.F] Af I.F) :
    hA I (a • x) y = sigA I a * hA I x y := by
  unfold hA Formalism.UG.hform sigA
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem zMod'_mul_of_mem_intAf (I : AutInst) (g : ℕ) {c a : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E)
    (ha : ZMod' I g a) : ZMod' I g (c * a) := by
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨c * t, mul_mem hc ht, by ring⟩

theorem lf_hA_sub_left (u u' v : VA I) : hA I (u - u') v = hA I u v - hA I u' v := by
  unfold hA Formalism.UG.hform
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lf_hA_sum_right (u : VA I) {ι : Type} (s : Finset ι) (f : ι → VA I) :
    hA I u (∑ k ∈ s, f k) = ∑ k ∈ s, hA I u (f k) := by
  unfold hA Formalism.UG.hform
  simp only [Finset.sum_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_comm

theorem lf_hA_mL_right {x y : VA I} (hx : x ∈ I.Lf) (hy : y ∈ mL I g) : ZMod' I g (hA I x y) := by
  obtain ⟨y', hy', rfl⟩ := lf_mem_mL I g hy
  rw [hA_smul_right]
  exact ⟨_, hA_int I hx hy', rfl⟩

theorem lf_hA_mL_left {x y : VA I} (hx : x ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I x y) := by
  obtain ⟨x', hx', rfl⟩ := lf_mem_mL I g hx
  rw [hA_smul_left, map_natCast]
  exact ⟨_, hA_int I hx' hy, rfl⟩

theorem lf_hA_cong {x x' y y' : VA I} (hx' : x' ∈ I.Lf) (hy : y ∈ I.Lf) (hxx : x - x' ∈ mL I g)
    (hyy : y - y' ∈ mL I g) : ZMod' I g (hA I x y - hA I x' y') := by
  obtain ⟨t1, ht1, h1⟩ := lf_hA_mL_left I g hxx hy
  obtain ⟨t2, ht2, h2⟩ := lf_hA_mL_right I g hx' hyy
  refine ⟨t1 + t2, add_mem ht1 ht2, ?_⟩
  rw [lf_hA_sub_left] at h1
  rw [hA_sub_right_gauge_lattice_shifts] at h2
  linear_combination h1 + h2

theorem lf_one_mem {κ : Type} [DecidableEq κ] (i j : κ) :
    (1 : Matrix κ κ (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E := by
  rw [Matrix.one_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

end Gen

section Eps

variable {I : AutInst} {g : ℕ} {ε : I.E ⊗[I.F] Af I.F}

theorem lf_coprime_unit
    (hU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, ε * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = ε)
    {c : ℕ} (hc : Nat.Coprime c g) : ∃ t ∈ IntAf I.F I.E, ε * ((c : I.E ⊗[I.F] Af I.F) * t) = ε := by
  have h1 : (c : ℤ) * Nat.gcdA c g + (g : ℤ) * Nat.gcdB c g = 1 := by
    have := Nat.gcd_eq_gcd_ab c g
    rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at this
    exact this.symm
  obtain ⟨s', hs', he⟩ := hU ((-(Nat.gcdB c g) : ℤ) : I.E ⊗[I.F] Af I.F) (intCast_mem _ _)
  refine ⟨((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) * s', mul_mem (intCast_mem _ _) hs', ?_⟩
  have h2 : (c : I.E ⊗[I.F] Af I.F) * ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) =
      1 + (g : I.E ⊗[I.F] Af I.F) * ((-(Nat.gcdB c g) : ℤ) : I.E ⊗[I.F] Af I.F) := by
    have h3 := congrArg (fun z : ℤ => (z : I.E ⊗[I.F] Af I.F)) h1
    push_cast at h3 ⊢
    linear_combination h3
  rw [show (c : I.E ⊗[I.F] Af I.F) * (((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) * s') =
    ((c : I.E ⊗[I.F] Af I.F) * ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F)) * s' from (mul_assoc _ _ _).symm, h2]
  exact he

theorem lf_inAt_eps (hεO : ε ∈ IntAf I.F I.E)
    (hU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, ε * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = ε)
    {x : VA I} (h : InAt I g g x) : ε • x ∈ mL I g := by
  obtain ⟨c, hc, hcx⟩ := h
  obtain ⟨t, ht, hε⟩ := lf_coprime_unit hU hc
  have hx : ε • x = (ε * t) • ((c : I.E ⊗[I.F] Af I.F) • x) := by
    rw [smul_smul]
    conv_lhs => rw [← hε]
    congr 1
    ring
  rw [hx]
  exact lf_mL_smul I g (mul_mem hεO ht) hcx

theorem lf_eps_vec_cong (h1ε : ZMod' I g (1 - ε)) {x : VA I} (hx : x ∈ I.Lf) : ε • x - x ∈ mL I g := by
  obtain ⟨t, ht, he⟩ := h1ε
  unfold mL
  refine Submodule.subset_span ⟨(-t) • x, lf_memL_smul I (neg_mem ht) hx, ?_⟩
  have hε : ε = 1 - (g : I.E ⊗[I.F] Af I.F) * t := by rw [← he]; ring
  rw [hε, smul_smul, sub_smul, one_smul, mul_neg, neg_smul, sub_sub_cancel_left]

end Eps

theorem lf_det_adj_cong {A : Type*} [CommRing A] {κ : Type*} [Fintype κ] [DecidableEq κ] (O : Subring A)
    (g : ℕ) (t : Matrix κ κ A) (ht : ∀ i j, t i j ∈ O) :
    (∃ s ∈ O, (1 + (g : A) • t).det = 1 + (g : A) * s) ∧
      ∀ i j, ∃ s ∈ O, (1 + (g : A) • t).adjugate i j = (1 : Matrix κ κ A) i j + (g : A) * s := by
  classical
  let t' : Matrix κ κ O := fun i j => ⟨t i j, ht i j⟩
  have hmap : 1 + (g : A) • t = (1 + (g : O) • t').map O.subtype := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, t'] <;> rfl
  have hg : Ideal.Quotient.mk (Ideal.span {(g : O)}) (g : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hone : (1 + (g : O) • t').map (Ideal.Quotient.mk (Ideal.span {(g : O)})) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, hg]
  have hdet : Ideal.Quotient.mk (Ideal.span {(g : O)}) (1 + (g : O) • t').det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hone, Matrix.det_one]
  obtain ⟨s, hs⟩ : ∃ s : O, (1 + (g : O) • t').det = 1 + (g : O) * s := by
    have hm : (1 + (g : O) • t').det - 1 ∈ Ideal.span {(g : O)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdet, map_one, sub_self]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨s, by linear_combination -hs⟩
  refine ⟨⟨s, s.2, ?_⟩, fun i j => ?_⟩
  · rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hs]
    simp
  · have hadj : (1 + (g : O) • t').adjugate.map (Ideal.Quotient.mk (Ideal.span {(g : O)})) = 1 := by
      rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, hone,
        Matrix.adjugate_one]
    have hm : (1 + (g : O) • t').adjugate i j - (1 : Matrix κ κ O) i j ∈ Ideal.span {(g : O)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
      have h1 := congrFun (congrFun hadj i) j
      rw [Matrix.map_apply] at h1
      rw [h1]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨r, r.2, ?_⟩
    have hr' : (1 + (g : O) • t').adjugate i j = (1 : Matrix κ κ O) i j + (g : O) * r := by
      linear_combination -hr
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply,
      Matrix.map_apply, hr']
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem lf_inv_on (I : AutInst) (g : ℕ) {η : I.E ⊗[I.F] Af I.F} (hηO : η ∈ IntAf I.F I.E)
    (hU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, η * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = η)
    {κ : Type} [Fintype κ] [DecidableEq κ] (t : Matrix κ κ (I.E ⊗[I.F] Af I.F))
    (ht : ∀ i j, t i j ∈ IntAf I.F I.E) :
    ∃ M : Matrix κ κ (I.E ⊗[I.F] Af I.F), (∀ i j, M i j ∈ IntAf I.F I.E) ∧
      η • ((1 + (g : I.E ⊗[I.F] Af I.F) • t) * M) = η • 1 ∧
      η • (M * (1 + (g : I.E ⊗[I.F] Af I.F) • t)) = η • 1 ∧
      ∀ i j, ZMod' I g (η * M i j - η * (1 : Matrix κ κ (I.E ⊗[I.F] Af I.F)) i j) := by
  obtain ⟨⟨s, hsO, hs⟩, hadj⟩ := lf_det_adj_cong (IntAf I.F I.E) g t ht
  obtain ⟨s', hs'O, hs'⟩ := hU s hsO
  refine ⟨s' • (1 + (g : I.E ⊗[I.F] Af I.F) • t).adjugate, fun i j => ?_, ?_, ?_, fun i j => ?_⟩
  · obtain ⟨r, hrO, hr⟩ := hadj i j
    rw [Matrix.smul_apply, smul_eq_mul, hr]
    exact mul_mem hs'O (add_mem (lf_one_mem I i j) (mul_mem (natCast_mem _ g) hrO))
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, hs, smul_smul, smul_smul]
    congr 1
    linear_combination hs'
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, hs, smul_smul, smul_smul]
    congr 1
    linear_combination hs'
  · obtain ⟨r, hrO, hr⟩ := hadj i j
    refine ⟨η * r - η * s * s' * (1 : Matrix κ κ (I.E ⊗[I.F] Af I.F)) i j -
      (g : I.E ⊗[I.F] Af I.F) * η * s * s' * r, ?_, ?_⟩
    · exact sub_mem (sub_mem (mul_mem hηO hrO) (mul_mem (mul_mem (mul_mem hηO hsO) hs'O) (lf_one_mem I i j)))
        (mul_mem (mul_mem (mul_mem (mul_mem (natCast_mem _ g) hηO) hsO) hs'O) hrO)
    · rw [Matrix.smul_apply, smul_eq_mul, hr]
      linear_combination ((1 : Matrix κ κ (I.E ⊗[I.F] Af I.F)) i j + (g : I.E ⊗[I.F] Af I.F) * r) * hs'

section Proj

variable (I : AutInst) {ι : Type} [Fintype ι] [DecidableEq ι] (ε : I.E ⊗[I.F] Af I.F) (uR : ι → VA I)
  (Q : Matrix ι ι (I.E ⊗[I.F] Af I.F))

def lfCf (y : VA I) : ι → I.E ⊗[I.F] Af I.F := ε • (Q *ᵥ fun l => hA I (uR l) y)

def lfProj (y : VA I) : VA I := ε • y - ∑ k, lfCf I ε uR Q y k • uR k

def lfGram : Matrix ι ι (I.E ⊗[I.F] Af I.F) := Matrix.of fun k l => hA I (uR k) (uR l)

theorem lf_proj_orth (hPQ : ε • (lfGram I uR * Q) = ε • 1) (y : VA I) (l : ι) :
    hA I (uR l) (lfProj I ε uR Q y) = 0 := by
  have hPQ' : ∀ m, ε * (lfGram I uR * Q) l m = ε * (1 : Matrix ι ι (I.E ⊗[I.F] Af I.F)) l m := fun m => by
    have := congrFun (congrFun hPQ l) m
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  unfold lfProj
  rw [hA_sub_right_gauge_lattice_shifts, lf_hA_sum_right, hA_smul_right_eq_mul]
  simp only [hA_smul_right_eq_mul]
  have key : ∑ k, lfCf I ε uR Q y k * hA I (uR l) (uR k) = ε * hA I (uR l) y := by
    calc ∑ k, lfCf I ε uR Q y k * hA I (uR l) (uR k)
        = ∑ m, (ε * (lfGram I uR * Q) l m) * hA I (uR m) y := by
          simp only [lfCf, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.mul_apply,
            lfGram, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ m, (ε * (1 : Matrix ι ι (I.E ⊗[I.F] Af I.F)) l m) * hA I (uR m) y := by simp only [hPQ']
      _ = ε * hA I (uR l) y := by simp [Matrix.one_apply]
  rw [key, sub_self]

theorem lf_cf_eps (hεε : ε * ε = ε) (y : VA I) (k : ι) : ε * lfCf I ε uR Q y k = lfCf I ε uR Q y k := by
  simp only [lfCf, Pi.smul_apply, smul_eq_mul, ← mul_assoc, hεε]

theorem lf_cf_eq (hσε : sigA I ε = ε) (y : VA I) (k : ι) :
    lfCf I ε uR Q y k = ∑ l, Q k l * hA I (ε • uR l) y := by
  simp only [lfCf, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hA_smul_left_eq_sigA_mul, hσε,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem lf_term_eq (hεε : ε * ε = ε) (y : VA I) (k : ι) :
    lfCf I ε uR Q y k • uR k = lfCf I ε uR Q y k • (ε • uR k) := by
  rw [smul_smul, mul_comm, lf_cf_eps I ε uR Q hεε]

theorem lf_proj_mem (hεO : ε ∈ IntAf I.F I.E) (hεε : ε * ε = ε) (hσε : sigA I ε = ε)
    (hu : ∀ k, ε • uR k ∈ I.Lf) (hQ : ∀ k l, Q k l ∈ IntAf I.F I.E) {y : VA I} (hy : y ∈ I.Lf) :
    lfProj I ε uR Q y ∈ I.Lf := by
  have hc : ∀ k, lfCf I ε uR Q y k ∈ IntAf I.F I.E := fun k => by
    rw [lf_cf_eq I ε uR Q hσε y k]
    exact sum_mem fun l _ => mul_mem (hQ k l) (hA_int (hu := hu l) (hv := hy))
  unfold lfProj
  refine I.Lf.sub_mem (lf_memL_smul I hεO hy) (I.Lf.sum_mem fun k _ => ?_)
  rw [lf_term_eq I ε uR Q hεε y k]
  exact lf_memL_smul I (hc k) (hu k)

theorem lf_proj_cong (g : ℕ) (hεε : ε * ε = ε) (hσε : sigA I ε = ε) (h1ε : ZMod' I g (1 - ε))
    (hu : ∀ k, ε • uR k ∈ I.Lf) (hQ : ∀ k l, Q k l ∈ IntAf I.F I.E) {y : VA I} (hy : y ∈ I.Lf)
    (hZ : ∀ l, ZMod' I g (hA I (ε • uR l) y)) : lfProj I ε uR Q y - y ∈ mL I g := by
  choose t ht he using hZ
  have hc : ∀ k, ZMod' I g (lfCf I ε uR Q y k) := fun k => by
    refine ⟨∑ l, Q k l * t l, sum_mem fun l _ => mul_mem (hQ k l) (ht l), ?_⟩
    rw [lf_cf_eq I ε uR Q hσε y k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [he l]
    ring
  have hsum : ∑ k, lfCf I ε uR Q y k • uR k ∈ mL I g := by
    refine (mL I g).sum_mem fun k _ => ?_
    obtain ⟨s, hs, hse⟩ := hc k
    rw [lf_term_eq I ε uR Q hεε y k, hse, ← smul_smul]
    unfold mL
    exact Submodule.subset_span ⟨s • (ε • uR k), lf_memL_smul I hs (hu k), rfl⟩
  have h1 := lf_eps_vec_cong h1ε hy
  unfold lfProj
  rw [show ε • y - ∑ k, lfCf I ε uR Q y k • uR k - y = (ε • y - y) - ∑ k, lfCf I ε uR Q y k • uR k by abel]
  exact (mL I g).sub_mem h1 hsum

end Proj

def hyperbolicMinusOneMatrix (A : Type*) [Ring A] (r : ℕ) : Matrix ((Fin r ⊕ Fin r) ⊕ Unit) ((Fin r ⊕ Fin r) ⊕ Unit) A :=
  Matrix.of (Sum.elim
    (Sum.elim (fun a => Sum.elim (Sum.elim (fun _ => 0) (fun b => if a = b then 1 else 0)) (fun _ => 0))
      (fun a => Sum.elim (Sum.elim (fun b => if a = b then 1 else 0) (fun _ => 0)) (fun _ => 0)))
    (fun _ => Sum.elim (fun _ => 0) (fun _ => -1)))

theorem hyperbolic_matrix_sq_eq_one (A : Type*) [Ring A] (r : ℕ) : hyperbolicMinusOneMatrix A r * hyperbolicMinusOneMatrix A r = 1 := by
  ext i j
  rcases i with (a | a) | ⟨⟩ <;> rcases j with (b | b) | ⟨⟩ <;>
    simp [hyperbolicMinusOneMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem hyperbolic_matrix_integral (I : AutInst) (r : ℕ) (k l : (Fin r ⊕ Fin r) ⊕ Unit) :
    hyperbolicMinusOneMatrix (I.E ⊗[I.F] Af I.F) r k l ∈ IntAf I.F I.E := by
  rcases k with (a | a) | ⟨⟩ <;> rcases l with (b | b) | ⟨⟩ <;>
    simp only [hyperbolicMinusOneMatrix, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr] <;>
    first
    | exact zero_mem _
    | exact one_mem _
    | exact neg_mem (one_mem _)
    | (split_ifs <;> first | exact zero_mem _ | exact one_mem _)

theorem lf_frame_core (I : AutInst) (g : ℕ) {ε : I.E ⊗[I.F] Af I.F} (hεO : ε ∈ IntAf I.F I.E)
    (hεε : ε * ε = ε) (hσε : sigA I ε = ε) (h1ε : ZMod' I g (1 - ε))
    (hU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, ε * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = ε)
    {ι : Type} [Fintype ι] [DecidableEq ι] (uR u0 : ι → VA I) (Q0 : Matrix ι ι (I.E ⊗[I.F] Af I.F))
    (hQ0O : ∀ k l, Q0 k l ∈ IntAf I.F I.E) (hQ0 : Q0 * Q0 = 1) (hu0 : ∀ k, u0 k ∈ I.Lf)
    (hc : ∀ k, ε • (uR k - u0 k) ∈ mL I g) (hgr : ∀ k l, ZMod' I g (hA I (u0 k) (u0 l) - Q0 k l))
    {m : ℕ} (ew : I.E ⊗[I.F] Af I.F) (bw bwd : Fin m → VA I) (hewi : ew * ew = ew)
    (hewO : ew ∈ IntAf I.F I.E) (hbL : ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf) (hbw : ∀ i, bw i = ew • bw i)
    (hbwd : ∀ i, bwd i = sigA I ew • bwd i)
    (hdual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0))
    (hW : ∀ k j, ZMod' I g (hA I (u0 k) (bw j)) ∧ ZMod' I g (hA I (u0 k) (bwd j))) :
    ∃ (η : I.E ⊗[I.F] Af I.F) (b d : Fin m → VA I), η ∈ IntAf I.F I.E ∧ η * η = η ∧ η * ew = η ∧
      ZMod' I g (ew - η) ∧
      (∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, η * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = η) ∧
      (∀ i, b i ∈ I.Lf ∧ d i ∈ I.Lf ∧ η • b i = b i ∧ sigA I η • d i = d i) ∧
      (∀ k i, hA I (uR k) (b i) = 0 ∧ hA I (uR k) (d i) = 0) ∧
      (∀ i j, hA I (d i) (b j) = if i = j then η else 0) ∧
      ∀ i j, ZMod' I g (hA I (bwd i) (b j) - if i = j then ew else 0) ∧
        ZMod' I g (hA I (d i) (bw j) - if i = j then ew else 0) := by
  classical
  have hεu : ∀ k, ε • uR k - u0 k ∈ mL I g := fun k => by
    have h2 := lf_eps_vec_cong h1ε (hu0 k)
    have e : ε • uR k - u0 k = ε • (uR k - u0 k) + (ε • u0 k - u0 k) := by rw [smul_sub]; abel
    rw [e]
    exact (mL I g).add_mem (hc k) h2
  have huL : ∀ k, ε • uR k ∈ I.Lf := fun k => by
    have e : ε • uR k = (ε • uR k - u0 k) + u0 k := by abel
    rw [e]
    exact I.Lf.add_mem (lf_mL_le I g (hεu k)) (hu0 k)
  have hz0 : ∀ v : VA I, v - v ∈ mL I g := fun v => by
    rw [sub_self]
    exact (mL I g).zero_mem
  have hG : ∀ k l, ZMod' I g (ε * lfGram I uR k l - Q0 k l) := fun k l => by
    have e1 : ε * lfGram I uR k l = hA I (ε • uR k) (ε • uR l) := by
      simp only [lfGram, Matrix.of_apply]
      rw [hA_smul_left_eq_sigA_mul, hA_smul_right_eq_mul, hσε, ← mul_assoc, hεε]
    have h1 := lf_hA_cong I g (hu0 k) (huL l) (hεu k) (hεu l)
    have h2 := Z_add (ha := h1) (hb := hgr k l)
    convert h2 using 1
    rw [e1]
    ring
  have hGQ : ∀ k l, ZMod' I g (ε * (lfGram I uR * Q0) k l - (1 : Matrix ι ι (I.E ⊗[I.F] Af I.F)) k l) := fun k l => by
    have hs := Z_sum (I := I) (g := g) (s := Finset.univ)
      (f := fun m => Q0 m l * (ε * lfGram I uR k m - Q0 k m))
      (h := fun m _ => zMod'_mul_of_mem_intAf I g (hQ0O m l) (hG k m))
    convert hs using 1
    try dsimp only
    rw [← hQ0, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  choose tG htG heG using hGQ
  obtain ⟨M, hMO, hM1, -, -⟩ := lf_inv_on I g hεO hU (Matrix.of tG) (fun i j => htG i j)
  have hE : ε • (lfGram I uR * Q0) = ε • (1 + (g : I.E ⊗[I.F] Af I.F) • Matrix.of tG) := by
    ext k l
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.of_apply]
    linear_combination ε * heG k l - (lfGram I uR * Q0) k l * hεε
  have hPQ : ε • (lfGram I uR * (Q0 * M)) = ε • 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.smul_mul, hE, Matrix.smul_mul, hM1]
  have hQ : ∀ k l, (Q0 * M) k l ∈ IntAf I.F I.E := fun k l => by
    rw [Matrix.mul_apply]
    exact sum_mem fun m _ => mul_mem (hQ0O k m) (hMO m l)
  have hZy : ∀ y, y ∈ I.Lf → (∀ l, ZMod' I g (hA I (u0 l) y)) → ∀ l, ZMod' I g (hA I (ε • uR l) y) :=
    fun y hy hy0 l => by
      have h1 := lf_hA_cong I g (hu0 l) hy (hεu l) (hz0 y)
      have h2 := Z_add (ha := h1) (hb := hy0 l)
      simpa using h2
  obtain ⟨b', hb'L, hb'o, hb'c⟩ : ∃ b' : Fin m → VA I, (∀ i, b' i ∈ I.Lf) ∧
      (∀ i k, hA I (uR k) (b' i) = 0) ∧ ∀ i, b' i - bw i ∈ mL I g :=
    ⟨fun i => lfProj I ε uR (Q0 * M) (bw i),
      fun i => lf_proj_mem I ε uR (Q0 * M) hεO hεε hσε huL hQ (hbL i).1,
      fun i k => lf_proj_orth I ε uR (Q0 * M) hPQ (bw i) k,
      fun i => lf_proj_cong I ε uR (Q0 * M) g hεε hσε h1ε huL hQ (hbL i).1
        (hZy (bw i) (hbL i).1 fun l => (hW l i).1)⟩
  obtain ⟨d', hd'L, hd'o, hd'c⟩ : ∃ d' : Fin m → VA I, (∀ i, d' i ∈ I.Lf) ∧
      (∀ i k, hA I (uR k) (d' i) = 0) ∧ ∀ i, d' i - bwd i ∈ mL I g :=
    ⟨fun i => lfProj I ε uR (Q0 * M) (bwd i),
      fun i => lf_proj_mem I ε uR (Q0 * M) hεO hεε hσε huL hQ (hbL i).2,
      fun i k => lf_proj_orth I ε uR (Q0 * M) hPQ (bwd i) k,
      fun i => lf_proj_cong I ε uR (Q0 * M) g hεε hσε h1ε huL hQ (hbL i).2
        (hZy (bwd i) (hbL i).2 fun l => (hW l i).2)⟩
  have hH : ∀ i j, ZMod' I g (hA I (d' i) (b' j) - if i = j then ew else 0) := fun i j => by
    have h1 := lf_hA_cong I g (hbL i).2 (hb'L j) (hd'c i) (hb'c j)
    have h2 := Z_add (ha := h1) (hb := hdual i j)
    convert h2 using 1
    ring
  have hηO : ε * ew ∈ IntAf I.F I.E := mul_mem hεO hewO
  have hηη : ε * ew * (ε * ew) = ε * ew := by linear_combination ew * ew * hεε + ε * hewi
  have hηew : ε * ew * ew = ε * ew := by rw [mul_assoc, hewi]
  obtain ⟨t1, ht1, he1⟩ := id h1ε
  have hewη : ZMod' I g (ew - ε * ew) := ⟨t1 * ew, mul_mem ht1 hewO, by linear_combination ew * he1⟩
  have hηU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E,
      ε * ew * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = ε * ew := fun s hs => by
    obtain ⟨s', hs', he⟩ := hU s hs
    exact ⟨s', hs', by linear_combination ew * he⟩
  choose tH htH heH using hH
  obtain ⟨N, hNO, hN1, -, hNc⟩ := lf_inv_on I g hηO hηU (Matrix.of tH) (fun i j => htH i j)
  have hEH : (ε * ew) • (Matrix.of fun i j => hA I (d' i) (b' j)) =
      (ε * ew) • (1 + (g : I.E ⊗[I.F] Af I.F) • Matrix.of tH) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    have h := heH i j
    split_ifs at h ⊢
    · linear_combination (ε * ew) * h + hηew
    · linear_combination (ε * ew) * h
  have hHN : ∀ i j, ε * ew * ∑ l, hA I (d' i) (b' l) * N l j =
      ε * ew * (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] Af I.F)) i j := by
    have h : (ε * ew) • ((Matrix.of fun i j => hA I (d' i) (b' j)) * N) = (ε * ew) • 1 := by
      rw [← Matrix.smul_mul, hEH, Matrix.smul_mul, hN1]
    intro i j
    have := congrFun (congrFun h i) j
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.of_apply] using this
  refine ⟨ε * ew, fun j => ∑ l, (ε * ew * N l j) • b' l, fun i => sigA I (ε * ew) • d' i, hηO, hηη, hηew,
    hewη, hηU, fun i => ⟨?_, ?_, ?_, ?_⟩, fun k i => ⟨?_, ?_⟩, fun i j => ?_, fun i j => ⟨?_, ?_⟩⟩
  · exact I.Lf.sum_mem fun l _ => lf_memL_smul I (mul_mem hηO (hNO l i)) (hb'L l)
  · exact lf_memL_smul I (sigA_mem (ha := hηO)) (hd'L i)
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    linear_combination N l i * hηη
  · rw [smul_smul, ← map_mul, hηη]
  · rw [lf_hA_sum_right]
    exact Finset.sum_eq_zero fun l _ => by rw [hA_smul_right_eq_mul, hb'o l k, mul_zero]
  · rw [hA_smul_right_eq_mul, hd'o i k, mul_zero]
  · rw [lf_hA_sum_right]
    have e3 : ∀ l, hA I (sigA I (ε * ew) • d' i) ((ε * ew * N l j) • b' l) =
        ε * ew * (hA I (d' i) (b' l) * N l j) := fun l => by
      rw [hA_smul_right_eq_mul, hA_smul_left_eq_sigA_mul, sigA_sigA]
      linear_combination (N l j * hA I (d' i) (b' l)) * hηη
    rw [Finset.sum_congr rfl fun l _ => e3 l, ← Finset.mul_sum, hHN i j, Matrix.one_apply]
    split_ifs <;> ring
  · have hK : ∀ l, ZMod' I g (hA I (bwd i) (b' l) - if i = l then ew else 0) := fun l => by
      have h1 := lf_hA_cong I g (hbL i).2 (hb'L l) (hz0 (bwd i)) (hb'c l)
      have h2 := Z_add (ha := h1) (hb := hdual i l)
      convert h2 using 1
      ring
    have A1 := Z_sum (I := I) (g := g) (s := Finset.univ)
      (f := fun l => ε * ew * N l j * (hA I (bwd i) (b' l) - if i = l then ew else 0))
      (h := fun l _ => zMod'_mul_of_mem_intAf I g (mul_mem hηO (hNO l j)) (hK l))
    have A3 : ZMod' I g (ε * ew * (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] Af I.F)) i j - if i = j then ew else 0) := by
      rw [Matrix.one_apply]
      split_ifs
      · rw [mul_one]
        obtain ⟨t, ht, he⟩ := hewη
        exact ⟨-t, neg_mem ht, by linear_combination -he⟩
      · exact ⟨0, zero_mem _, by ring⟩
    have hs : ∑ l, ε * ew * N l j * (if i = l then ew else 0) = ε * ew * N i j := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      linear_combination (ε * N i j) * hewi
    have h4 := Z_add (ha := Z_add (ha := A1) (hb := hNc i j)) (hb := A3)
    convert h4 using 1
    try dsimp only
    rw [lf_hA_sum_right]
    simp only [hA_smul_right_eq_mul]
    rw [Finset.sum_congr rfl fun l _ => mul_sub (ε * ew * N l j) (hA I (bwd i) (b' l))
      (if i = l then ew else 0), Finset.sum_sub_distrib, hs]
    ring
  · have hK : ZMod' I g (hA I (d' i) (bw j) - if i = j then ew else 0) := by
      have h1 := lf_hA_cong I g (hbL i).2 (hbL j).1 (hd'c i) (hz0 (bw j))
      have h2 := Z_add (ha := h1) (hb := hdual i j)
      convert h2 using 1
      ring
    have B2 : ZMod' I g (ε * ew * (if i = j then ew else 0) - if i = j then ew else 0) := by
      split_ifs
      · obtain ⟨t, ht, he⟩ := hewη
        exact ⟨-t, neg_mem ht, by linear_combination -he + hηew⟩
      · exact ⟨0, zero_mem _, by ring⟩
    have h4 := Z_add (ha := zMod'_mul_of_mem_intAf I g hηO hK) (hb := B2)
    convert h4 using 1
    rw [hA_smul_left_eq_sigA_mul, sigA_sigA]
    ring

section HidaSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

def lfUR : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit → VA X.B.I :=
  Sum.elim (Sum.elim (fun a => incl X.B.I (X.eR a)) (fun a => incl X.B.I (X.fR a)))
    (fun _ => X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u))

def referenceFrameFamily : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit → VA X.B.I :=
  Sum.elim (Sum.elim X.e0 X.f0) (fun _ => X.z0)

theorem reference_frame_mem_lattice (k : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit) : referenceFrameFamily X k ∈ X.B.I.Lf := by
  rcases k with (a | a) | ⟨⟩
  exacts [(X.vectorsInLattice.1 a).1, (X.vectorsInLattice.1 a).2, X.vectorsInLattice.2.1]

theorem reference_frame_gram_congruence (k l : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit) :
    ZMod' X.B.I X.B.g (hA X.B.I (referenceFrameFamily X k) (referenceFrameFamily X l) - hyperbolicMinusOneMatrix (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) D.R.rS k l) := by
  rcases k with (a | a) | ⟨⟩ <;> rcases l with (b | b) | ⟨⟩ <;>
    simp only [hyperbolicMinusOneMatrix, referenceFrameFamily, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, sub_zero, sub_neg_eq_add]
  · exact (X.gramIntegral a b).1
  · exact (X.gramIntegral a b).2.2
  · exact (X.formsAtZero.2 a).1
  · have h := Z_sig (ha := (X.gramIntegral b a).2.2)
    rw [map_sub, ← hA_symm] at h
    by_cases hab : a = b
    · subst hab
      simpa using h
    · simpa [hab, Ne.symm hab] using h
  · exact (X.gramIntegral a b).2.1
  · exact (X.formsAtZero.2 a).2
  · have h := Z_sig (ha := (X.formsAtZero.2 b).1)
    rwa [← hA_symm] at h
  · have h := Z_sig (ha := (X.formsAtZero.2 b).2)
    rwa [← hA_symm] at h
  · exact X.formsAtZero.1

theorem lf_uR_cong {ε : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hεO : ε ∈ IntAf X.B.I.F X.B.I.E)
    (hU : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      ε * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ε)
    (k : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit) : ε • (lfUR X u k - referenceFrameFamily X k) ∈ mL X.B.I X.B.g := by
  rcases k with (a | a) | ⟨⟩
  · have h := lf_inAt_eps hεO hU (X.basisApprox a).1
    have e : ε • (lfUR X u (Sum.inl (Sum.inl a)) - referenceFrameFamily X (Sum.inl (Sum.inl a))) =
        -(ε • (X.e0 a - incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX a)))) := by
      rw [← smul_neg, neg_sub]; rfl
    rw [e]
    exact neg_mem h
  · have h := lf_inAt_eps hεO hU (X.basisApprox a).2
    have e : ε • (lfUR X u (Sum.inl (Sum.inr a)) - referenceFrameFamily X (Sum.inl (Sum.inr a))) =
        -(ε • (X.f0 a - incl X.B.I (crdOf X.B.I X.ιE X.bas (X.fY a)))) := by
      rw [← smul_neg, neg_sub]; rfl
    rw [e]
    exact neg_mem h
  · exact lf_inAt_eps hεO hU (X.xu_z u)

theorem reference_frame_beta_orthogonal (k : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I (referenceFrameFamily X k) (X.bw j)) ∧ ZMod' X.B.I X.B.g (hA X.B.I (referenceFrameFamily X k) (X.bwd j)) := by
  rcases k with (a | a) | ⟨⟩
  exacts [⟨((X.weightVectorsIntegral j).2.2 a).1, ((X.weightVectorsIntegral j).2.2 a).2.2.1⟩,
    ⟨((X.weightVectorsIntegral j).2.2 a).2.1, ((X.weightVectorsIntegral j).2.2 a).2.2.2⟩, ⟨(X.weightVectorsIntegral j).1, (X.weightVectorsIntegral j).2.1⟩]

end HidaSetting

end LeviFramePf

namespace LeviOntoSPf

open LeviFramePf

theorem exact_dual_frame_exists {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : FrameOfS X u := by
  unfold FrameOfS SIdem DualFrame IsDualFrame
  intro hS
  obtain ⟨ε, hεO, hεε, hσε, h1ε, hU⟩ := hS
  obtain ⟨η, b, d, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := lf_frame_core X.B.I X.B.g hεO hεε hσε h1ε hU
    (lfUR X u) (referenceFrameFamily X) (hyperbolicMinusOneMatrix _ D.R.rS) (hyperbolic_matrix_integral X.B.I D.R.rS) (hyperbolic_matrix_sq_eq_one _ D.R.rS) (reference_frame_mem_lattice X)
    (lf_uR_cong X u hεO hU) (reference_frame_gram_congruence X) X.ew X.bw X.bwd X.ew_idem X.ew_int X.vectorsInLattice.2.2 X.bw_w X.bwd_w
    X.bw_dual (reference_frame_beta_orthogonal X)
  refine ⟨η, b, d, h1, h2, h3, h4, h5, h6, ?_, h8, h9⟩
  intro y hy i
  unfold fixV at hy
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hy
  · exact h7 (Sum.inl (Sum.inl a)) i
  · exact h7 (Sum.inl (Sum.inr a)) i
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h7 (Sum.inr ()) i

end LeviOntoSPf

end Formalism.L2.SG.Pf.NormSteps
end
end

section
noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

theorem leviOntoS_of_frame (hF : LeviOntoSPf.FrameOfS X u) : LeviOntoS TR cs :=
  LeviOntoSPf.leviOntoS_of_steps TR u cs (LeviOntoSPf.SIdemPf.idempotent_places_exists X) hF
    (LeviOntoSPf.LeviEltPf.levi_element_exists TR u) (LeviOntoSPf.MatLiftPf.integral_matrix_lift_exists TR)

theorem levi_onto_reduction : LeviOntoS TR cs :=
  leviOntoS_of_frame TR cs (LeviOntoSPf.exact_dual_frame_exists X u)

end Formalism.L2.SG.Pf.NormSteps
end
end
