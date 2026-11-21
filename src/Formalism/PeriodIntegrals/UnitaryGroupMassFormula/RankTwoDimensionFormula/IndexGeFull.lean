import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IndexGe
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UniAMulDiag
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsUnitDetLeviM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDChk
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
import Formalism.SatakeDualWeyl.Statement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Transp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDSI

section
namespace PI.UnitaryDimensionFormula

open Matrix

section Core

variable {F : Type} [Field F] {k : ℕ}

theorem uniA_mul_diag (A B : Matrix (Fin k) (Fin k) F) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin k) : (A * B) i i = A i i * B i i := by
  first | exact UpperTheory.Reformulated.B.Qh23.uniA_mul_diag .. | (apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB i | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F

theorem uniA_tri (x : GL (Fin k) F) (hx : ∀ i j : Fin k, j < i → (x : Matrix (Fin k) (Fin k) F) i j = 0) :
    (x : Matrix (Fin k) (Fin k) F).BlockTriangular id := fun i j h => hx i j h

theorem uniA_mul (x y : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x)
    (hy : Formalism.L2.SG.GGMirabolic.IsUni k y) : Formalism.L2.SG.GGMirabolic.IsUni k (x * y) := by
  have tx := uniA_tri x hx.2
  have ty := uniA_tri y hy.2
  have txy : ((x : Matrix (Fin k) (Fin k) F) * (y : Matrix (Fin k) (Fin k) F)).BlockTriangular id :=
    tx.mul ty
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · rw [Units.val_mul, uniA_mul_diag _ _ tx ty, hx.1 i, hy.1 i, one_mul]
  · rw [Units.val_mul]; exact txy h

theorem uniA_inv (x : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x) :
    Formalism.L2.SG.GGMirabolic.IsUni k x⁻¹ := by
  have tx := uniA_tri x hx.2
  have : Invertible (x : Matrix (Fin k) (Fin k) F) := Units.invertible x
  have tinv : ((x : Matrix (Fin k) (Fin k) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular tx
  have hc : ((x⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = (x : Matrix (Fin k) (Fin k) F)⁻¹ :=
    Matrix.coe_units_inv x
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · have h1 : ((x : Matrix (Fin k) (Fin k) F)⁻¹ * (x : Matrix (Fin k) (Fin k) F)) i i = 1 := by
      rw [Matrix.inv_mul_of_invertible, Matrix.one_apply_eq]
    rw [uniA_mul_diag _ _ tinv tx, hx.1 i, mul_one] at h1
    rw [hc]; exact h1
  · rw [hc]; exact tinv h

end Core

theorem uniSub : UniSub := by
  intro F _ k x y hx hy
  exact ⟨uniA_mul x y hx hy, uniA_inv x hx⟩

end PI.UnitaryDimensionFormula
end

section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section NCongS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

end NCongS

section K2iff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem res_ew_one (v : TR.Pl) : TR.res v ⟨X.ew, X.ew_int⟩ = 1 := by
  calc TR.res v ⟨X.ew, X.ew_int⟩
      = TR.res v ⟨X.ew * ((1 : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
          (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (1 : IntAf X.B.I.F X.B.I.E).2⟩ := by
        congr 1
        ext
        simp
    _ = TR.res v 1 := TR.res_ew v 1
    _ = 1 := map_one _

theorem res_of_Z_delta (v : TR.Pl) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : c ∈ IntAf X.B.I.F X.B.I.E) (b : Prop)
    [Decidable b] (hZ : ZMod' X.B.I X.B.g (c - if b then X.ew else 0)) :
    TR.res v ⟨c, hc⟩ = if b then 1 else 0 := by
  by_cases hb : b
  · rw [if_pos hb] at hZ ⊢
    have hmem : c - X.ew ∈ IntAf X.B.I.F X.B.I.E := sub_mem hc X.ew_int
    have hk := (TR.res_ker ⟨c - X.ew, hmem⟩).mpr (Z_smul X.B.I X.B.g X.ew_int hZ) v
    have e : (⟨c - X.ew, hmem⟩ : IntAf X.B.I.F X.B.I.E) = ⟨c, hc⟩ - ⟨X.ew, X.ew_int⟩ := rfl
    rw [e, map_sub, res_ew_one, sub_eq_zero] at hk
    exact hk
  · rw [if_neg hb, sub_zero] at hZ
    rw [if_neg hb]
    exact (TR.res_ker ⟨c, hc⟩).mpr (Z_smul X.B.I X.B.g X.ew_int hZ) v

theorem unitriangular_reduction_of_mem_level {x : X.B.I.Gf} (hx : Good X x) (hk : x ∈ X.K2) (v : TR.Pl) :
    Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR x v) := by
  obtain ⟨hK, -, -, hc3⟩ := hk
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  have hbb : ∀ i j : Fin D.R.k, i ≠ j → ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.bw j)) := by
    intro i j hij
    have h := X.bw_dual i j
    rwa [if_neg hij, sub_zero] at h
  have key : ∀ i j : Fin D.R.k, j ≤ i → leviM TR x v i j = if i = j then 1 else 0 := by
    intro i j hji
    have hmv : X.B.I.fmat x *ᵥ X.bw j ∈ X.B.I.Lf := K_mv X.B.I hK (X.vectorsInLattice.2.2 j).1
    have hc : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
      hA_int X.B.I (hbwd i) hmv
    have hsub : Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < j.1}) ≤ Qs X.B.I X.B.g (X.bwd i) :=
      le_trans (Mo_mono X.B.I (Set.union_subset_union_right _
          (Set.image_mono (lt_sub (Fin.le_iff_val_le_val.mp hji)))))
        (Mb_Q X.B.I X.B.g X.e0 X.bw X.bwd hbwd (fun i a => dual_beta_reference_congruence i a) hbb i)
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j)) := hsub (hc3 j)
    have hZ : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - if i = j then X.ew else 0) := by
      have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - (if i = j then X.ew else 0) =
          (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) +
            hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right]
        ring
      rw [e]
      exact Z_add X.B.I X.B.g (X.bw_dual i j) h2
    show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j)) = _
    rw [resT_of_mem TR v hc]
    exact res_of_Z_delta TR v hc (i = j) hZ
  show (∀ i : Fin D.R.k, ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i i = 1) ∧
    ∀ i j : Fin D.R.k, j < i →
      ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j = 0
  rw [levi_coe TR hx v]
  exact ⟨fun i => by rw [key i i le_rfl, if_pos rfl],
    fun i j hji => by rw [key i j hji.le, if_neg (ne_of_lt hji).symm]⟩

end K2iff

end PI.UnitaryDimensionFormula.NormCutK
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cj_good {D : D7} {X : HidaSetting D} (u : D.what₂.Word) (s : Hfin X u) (hs : cj X u s ∈ X.B.I.Kset) :
    NormCutK.Good X (cj X u s) := by
  have hk1 : (((1 : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((s : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    simpa [cj, mul_assoc] using hs
  have hk2 : ((s : X.B.I.Gf) * X.xu u)⁻¹ * (((1 : Hfin X u) : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    have hi := PI.UnitaryDimensionFormula.kset_inv hs
    simpa [cj, mul_assoc, mul_inv_rev] using hi
  have hg := NormCutK.colGood X u 1 s hk1 hk2
  simpa [cj, mul_assoc] using hg

theorem idxHom : IdxHom := by
  intro D X Y u _
  refine ⟨NormCutK.levi_one (TR := Y.TR), fun s t hs ht => ?_, fun s hs hKu v => ?_⟩
  · have hst : cj X u (s * t) = cj X u s * cj X u t := by
      simp [cj, mul_assoc]
    rw [hst, NormCutK.levi_mul (TR := Y.TR) (cj_good u s hs) (cj_good u t ht)]
  · exact NormCutK.unitriangular_reduction_of_mem_level (TR := Y.TR) (cj_good u s hs) hKu v

end PI.UnitaryDimensionFormula
end
end

section
open Matrix

namespace PI.UnitaryDimensionFormula.FrameAlg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)

theorem h_add_right (x y y' : n → A) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem h_smul_right (x y : n → A) (a : A) :
    Formalism.UG.hform σ J x (a • y) = a * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem h_sub_right (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem h_zero_right (x : n → A) : Formalism.UG.hform σ J x 0 = 0 := by
  simp [Formalism.UG.hform]

theorem h_sum_right {ι : Type} (s : Finset ι) (x : n → A) (v : ι → n → A) :
    Formalism.UG.hform σ J x (∑ l ∈ s, v l) = ∑ l ∈ s, Formalism.UG.hform σ J x (v l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_right, ih]

theorem h_add_left (x x' y : n → A) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem h_smul_left (x y : n → A) (a : A) :
    Formalism.UG.hform σ J (a • x) y = σ a * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem h_zero_left (y : n → A) : Formalism.UG.hform σ J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem h_sum_left {ι : Type} (s : Finset ι) (v : ι → n → A) (y : n → A) :
    Formalism.UG.hform σ J (∑ l ∈ s, v l) y = ∑ l ∈ s, Formalism.UG.hform σ J (v l) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_left, ih]

theorem h_symm (hJ : Formalism.UG.cT σ J = J) (hσ : ∀ a, σ (σ a) = a) (x y : n → A) :
    Formalism.UG.hform σ J y x = σ (Formalism.UG.hform σ J x y) := by
  have hJ' : ∀ i j, J i j = σ (J j i) := fun i j => by
    have h := congrFun (congrFun hJ i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h.symm
  simp only [Formalism.UG.hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ' j i]
  ring

variable {r : ℕ}

def Q (e f : Fin r → n → A) (z y : n → A) : n → A :=
  (-Formalism.UG.hform σ J z z) • (y - ∑ a, (Formalism.UG.hform σ J (f a) y • e a + Formalism.UG.hform σ J (e a) y • f a)) +
    Formalism.UG.hform σ J z y • z

structure Hyp (e f : Fin r → n → A) (z : n → A) : Prop where
  ee : ∀ a b, Formalism.UG.hform σ J (e a) (e b) = 0
  ff : ∀ a b, Formalism.UG.hform σ J (f a) (f b) = 0
  ef : ∀ a b, Formalism.UG.hform σ J (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, Formalism.UG.hform σ J (e a) z = 0
  fz : ∀ a, Formalism.UG.hform σ J (f a) z = 0

private theorem Q_eq_hform_expansion (e f : Fin r → n → A) (z y w : n → A) :
    Formalism.UG.hform σ J w (Q σ J e f z y) =
      -Formalism.UG.hform σ J z z * (Formalism.UG.hform σ J w y - ∑ a, (Formalism.UG.hform σ J (f a) y * Formalism.UG.hform σ J w (e a) +
        Formalism.UG.hform σ J (e a) y * Formalism.UG.hform σ J w (f a))) + Formalism.UG.hform σ J z y * Formalism.UG.hform σ J w z := by
  simp only [Q, h_add_right, h_smul_right, h_sub_right, h_sum_right]

theorem dual_fix (hσ : ∀ a, σ (σ a) = a) {k : ℕ} (b c : Fin k → n → A) (ε : A) (M : Matrix (Fin k) (Fin k) A)
    (hM : M * Matrix.of (fun l j => Formalism.UG.hform σ J (c l) (b j)) = ε • (1 : Matrix (Fin k) (Fin k) A))
    (i j : Fin k) :
    Formalism.UG.hform σ J (∑ l, σ (M i l) • c l) (b j) = if i = j then ε else 0 := by
  have h := congrFun (congrFun hM i) j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  rw [h_sum_left]
  simp only [h_smul_left, hσ]
  rw [h]
  split_ifs <;> simp

theorem inv_on {k : ℕ} (G : Matrix (Fin k) (Fin k) A) (ε y : A) (hy : ε * G.det * y = ε) :
    ((ε * y) • G.adjugate) * G = ε • (1 : Matrix (Fin k) (Fin k) A) := by
  rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
  congr 1
  linear_combination hy

theorem Q_perp_idem (hJ : Formalism.UG.cT σ J = J) (hσ : ∀ a, σ (σ a) = a) {e f : Fin r → n → A} {z : n → A} (E₁ : A)
    (hE : E₁ * E₁ = E₁) (hEs : σ E₁ = E₁) (he : ∀ a, e a = E₁ • e a) (hf : ∀ a, f a = E₁ • f a)
    (hee : ∀ a b, Formalism.UG.hform σ J (e a) (e b) = 0) (hff : ∀ a b, Formalism.UG.hform σ J (f a) (f b) = 0)
    (hef : ∀ a b, Formalism.UG.hform σ J (e a) (f b) = if a = b then E₁ else 0)
    (hez : ∀ a, Formalism.UG.hform σ J (e a) z = 0) (hfz : ∀ a, Formalism.UG.hform σ J (f a) z = 0) (y : n → A) :
    (∀ b, Formalism.UG.hform σ J (e b) (Q σ J e f z y) = 0) ∧ (∀ b, Formalism.UG.hform σ J (f b) (Q σ J e f z y) = 0) ∧
      Formalism.UG.hform σ J z (Q σ J e f z y) = 0 := by
  have hfe : ∀ a b, Formalism.UG.hform σ J (f b) (e a) = if a = b then E₁ else 0 := fun a b => by
    rw [h_symm σ J hJ hσ (e a) (f b), hef]; split_ifs <;> simp [hEs]
  have hze : ∀ a, Formalism.UG.hform σ J z (e a) = 0 := fun a => by rw [h_symm σ J hJ hσ (e a) z, hez, map_zero]
  have hzf : ∀ a, Formalism.UG.hform σ J z (f a) = 0 := fun a => by rw [h_symm σ J hJ hσ (f a) z, hfz, map_zero]
  have hEe : ∀ b, Formalism.UG.hform σ J (e b) y = Formalism.UG.hform σ J (e b) y * E₁ := fun b => by
    conv_lhs => rw [he b, h_smul_left, hEs]
    ring
  have hEf : ∀ b, Formalism.UG.hform σ J (f b) y = Formalism.UG.hform σ J (f b) y * E₁ := fun b => by
    conv_lhs => rw [hf b, h_smul_left, hEs]
    ring
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩ <;> rw [Q_eq_hform_expansion]
  · simp [hee, hef, hez]
    rw [← hEe b]; ring
  · simp [hfe, hff, hfz]
    rw [← hEf b]; ring
  · simp [hze, hzf]; ring

end PI.UnitaryDimensionFormula.FrameAlg
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  PI.UnitaryDimensionFormula.unitaryCongruence PI.UnitaryDimensionFormula.NormCutK

namespace PI.UnitaryDimensionFormula.FrameX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def E1 (e : Af X.B.I.F) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e

theorem idempotent_mul_self {e : Af X.B.I.F} (he : e * e = e) : E1 X e * E1 X e = E1 X e := by
  unfold E1; rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he]

theorem idempotent_conj_fixed (e : Af X.B.I.F) : sigA X.B.I (E1 X e) = E1 X e := by
  unfold E1; rw [sigA_tmul, star_one]

theorem tmul_int {e : Af X.B.I.F} (he : e ∈ Formalism.UG.intAd X.B.I.F) :
    (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Or.inr ⟨⟨e, he⟩, rfl⟩)

theorem integral_circleChar {e : Af X.B.I.F} (he : e ∈ Formalism.UG.intAd X.B.I.F) : E1 X e ∈ IntAf X.B.I.F X.B.I.E :=
  tmul_int X he

theorem one_sub_idempotent {e t : Af X.B.I.F} (ht : 1 - e = (X.B.g : Af X.B.I.F) * t) :
    1 - E1 X e = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
  unfold E1
  have h1 : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (X.B.g : Af X.B.I.F) := by
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  rw [h1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← ht, Algebra.TensorProduct.one_def,
    TensorProduct.tmul_sub]

variable {X}

theorem Zfix {e : Af X.B.I.F} (hE : EgProp X.B.I.F X.B.g e) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hc : c ∈ IntAf X.B.I.F X.B.I.E) (h : ZMod' X.B.I X.B.g (E1 X e * c)) : ZMod' X.B.I X.B.g c := by
  obtain ⟨t, ht, he1⟩ := hE.2.2.1
  have hs := one_sub_idempotent X he1
  have e2 : c = E1 X e * c + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) * c) := by
    linear_combination c * hs
  rw [e2]
  exact Z_add X.B.I X.B.g h ⟨_, mul_mem (tmul_int X ht) hc, rfl⟩

theorem idempotent_inv_coprime_nat (hJ : IdxDJacE) {e : Af X.B.I.F} (hE : EgProp X.B.I.F X.B.g e) (c : ℕ)
    (hc : Nat.Coprime c X.B.g) :
    ∃ y ∈ IntAf X.B.I.F X.B.I.E, E1 X e * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y = E1 X e := by
  have hcop : IsCoprime (c : ℤ) (X.B.g : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨y, hy, hyE⟩ := hJ X.B.I.F X.B.I.E X.B.g e hE (-(b : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (neg_mem (intCast_mem _ b))
  refine ⟨(a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y, mul_mem (intCast_mem _ a) hy, ?_⟩
  have hab' : (a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (-(b : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by
    have := congrArg (Int.cast : ℤ → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hab
    push_cast at this
    linear_combination this
  calc E1 X e * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y)
      = E1 X e * ((a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * y := by ring
    _ = E1 X e := by rw [hab']; exact hyE

theorem mL_le_Lf : ∀ v ∈ mL X.B.I X.B.g, v ∈ X.B.I.Lf := by
  intro v hv
  refine (Submodule.span_le (p := X.B.I.Lf)).2 ?_ hv
  rintro _ ⟨x, hx, rfl⟩
  have := X.B.I.Lf.smul_mem (⟨(X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), natCast_mem _ _⟩ : IntAf X.B.I.F X.B.I.E) hx
  rwa [Subring.smul_def] at this

theorem smul_int_mem {N : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I)} {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hc : c ∈ IntAf X.B.I.F X.B.I.E) {v : VA X.B.I} (hv : v ∈ N) : c • v ∈ N := by
  have := N.smul_mem (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) hv
  rwa [Subring.smul_def] at this

theorem congruence_on_idempotent (hJ : IdxDJacE) {e : Af X.B.I.F} (hE : EgProp X.B.I.F X.B.g e) {δ : VA X.B.I}
    (h : InAt X.B.I X.B.g X.B.g δ) : E1 X e • δ ∈ mL X.B.I X.B.g := by
  obtain ⟨c, hc, hcδ⟩ := h
  obtain ⟨y, hy, hyE⟩ := idempotent_inv_coprime_nat hJ hE c hc
  have e2 : E1 X e • δ = (E1 X e * y) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • δ) := by
    rw [smul_smul]
    conv_lhs => rw [← hyE]
    ring_nf
  rw [e2]
  exact smul_int_mem (mul_mem (integral_circleChar X hE.1) hy) hcδ

theorem hA_crd (x y : (VS D).V) :
    hA X.B.I (incl X.B.I (X.crd x)) (incl X.B.I (X.crd y)) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((VS D).hT x y)) := by
  rw [hA_incl, tr_hT, RingEquiv.symm_apply_apply]
  congr 1
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, mul_assoc]

variable (X)

def zv (u : D.what₂.Word) : VA X.B.I := X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)

theorem ev_fix (u : D.what₂.Word) (a : Fin D.R.rS) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) :=
  fixes_inv X (X.xu_fix u a).1

theorem fv_fix (u : D.what₂.Word) (a : Fin D.R.rS) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) :=
  fixes_inv X (X.xu_fix u a).2

theorem rel_ee (a b : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.eR b)) = 0 := by
  show hA X.B.I (incl X.B.I (X.crd (X.eX a))) (incl X.B.I (X.crd (X.eX b))) = 0
  rw [hA_crd, X.ee, map_zero, map_zero]

theorem rel_ff (a b : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (X.fR b)) = 0 := by
  show hA X.B.I (incl X.B.I (X.crd (X.fY a))) (incl X.B.I (X.crd (X.fY b))) = 0
  rw [hA_crd, X.ff, map_zero, map_zero]

theorem rel_ef (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  show hA X.B.I (incl X.B.I (X.crd (X.eX a))) (incl X.B.I (X.crd (X.fY b))) = _
  rw [hA_crd, X.ef]
  split_ifs <;> simp

theorem rel_ez (u : D.what₂.Word) (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (zv X u) = 0 := by
  rw [← ev_fix X u a, zv, hA_unit]
  show hA X.B.I (incl X.B.I (X.crd (X.eX a))) (incl X.B.I (X.crd (X.zu u))) = 0
  rw [hA_crd, (X.zu_orth u a).1, map_zero, map_zero]

theorem rel_fz (u : D.what₂.Word) (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (zv X u) = 0 := by
  rw [← fv_fix X u a, zv, hA_unit]
  show hA X.B.I (incl X.B.I (X.crd (X.fY a))) (incl X.B.I (X.crd (X.zu u))) = 0
  rw [hA_crd, (X.zu_orth u a).2, map_zero, map_zero]

end PI.UnitaryDimensionFormula.FrameX

namespace PI.UnitaryDimensionFormula.FrameX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def eh (e : Af X.B.I.F) (a : Fin D.R.rS) : VA X.B.I := E1 X e • incl X.B.I (X.eR a)
def fh (e : Af X.B.I.F) (a : Fin D.R.rS) : VA X.B.I := E1 X e • incl X.B.I (X.fR a)
def zh (e : Af X.B.I.F) (u : D.what₂.Word) : VA X.B.I := E1 X e • zv X u

def Qv (e : Af X.B.I.F) (u : D.what₂.Word) (y : VA X.B.I) : VA X.B.I :=
  FrameAlg.Q (sigA X.B.I) (JA X.B.I) (eh X e) (fh X e) (zh X e u) y

variable {X}

theorem hermitian_idempotent_smul {e : Af X.B.I.F} (he : e * e = e) (x y : VA X.B.I) :
    hA X.B.I (E1 X e • x) (E1 X e • y) = E1 X e * hA X.B.I x y := by
  rw [hA_smul_left, hA_smul_right, idempotent_conj_fixed, ← mul_assoc, idempotent_mul_self X he]

theorem hermitian_idempotent_smul_left (e : Af X.B.I.F) (x y : VA X.B.I) :
    hA X.B.I (E1 X e • x) y = E1 X e * hA X.B.I x y := by
  rw [hA_smul_left, idempotent_conj_fixed]

theorem idempotent_smul_idem {e : Af X.B.I.F} (he : e * e = e) (x : VA X.B.I) : E1 X e • (E1 X e • x) = E1 X e • x := by
  rw [smul_smul, idempotent_mul_self X he]

theorem sub_hA_left (x x' y : VA X.B.I) : hA X.B.I x y = hA X.B.I (x - x') y + hA X.B.I x' y := by
  rw [← hA_add_left, sub_add_cancel]

theorem Qv_perp (hS : IdxDSig) {e : Af X.B.I.F} (he : e * e = e) (u : D.what₂.Word) (y : VA X.B.I) :
    (∀ b, hA X.B.I (eh X e b) (Qv X e u y) = 0) ∧ (∀ b, hA X.B.I (fh X e b) (Qv X e u y) = 0) ∧
      hA X.B.I (zh X e u) (Qv X e u y) = 0 := by
  have hE := idempotent_mul_self X he
  refine FrameAlg.Q_perp_idem (sigA X.B.I) (JA X.B.I) (hS X.B.I).2 (hS X.B.I).1 (E1 X e) hE (idempotent_conj_fixed X e)
    (fun a => (idempotent_smul_idem he _).symm) (fun a => (idempotent_smul_idem he _).symm) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_) (fun a => ?_) (fun a => ?_) y
  · show hA X.B.I (eh X e a) (eh X e b) = 0
    rw [eh, eh, hermitian_idempotent_smul he, rel_ee, mul_zero]
  · show hA X.B.I (fh X e a) (fh X e b) = 0
    rw [fh, fh, hermitian_idempotent_smul he, rel_ff, mul_zero]
  · show hA X.B.I (eh X e a) (fh X e b) = _
    rw [eh, fh, hermitian_idempotent_smul he, rel_ef]
    split_ifs <;> simp
  · show hA X.B.I (eh X e a) (zh X e u) = 0
    rw [eh, zh, hermitian_idempotent_smul he, rel_ez, mul_zero]
  · show hA X.B.I (fh X e a) (zh X e u) = 0
    rw [fh, zh, hermitian_idempotent_smul he, rel_fz, mul_zero]

theorem fixV_perp (hS : IdxDSig) {e : Af X.B.I.F} (he : e * e = e) (u : D.what₂.Word) (y w : VA X.B.I)
    (hw : w ∈ fixV X u) : E1 X e * hA X.B.I w (Qv X e u y) = 0 := by
  obtain ⟨h1, h2, h3⟩ := Qv_perp hS he u y
  rw [← hermitian_idempotent_smul_left]
  rcases hw with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · exact h1 a
  · exact h2 a
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact h3

variable (hJ : IdxDJacE) {e : Af X.B.I.F} (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word)
include hJ hE

theorem eh_cong (a : Fin D.R.rS) : eh X e a - E1 X e • X.e0 a ∈ mL X.B.I X.B.g := by
  have := congruence_on_idempotent hJ hE (X.basisApprox a).1
  rw [smul_sub] at this
  have h2 := (mL X.B.I X.B.g).neg_mem this
  rw [neg_sub] at h2
  exact h2

theorem fh_cong (a : Fin D.R.rS) : fh X e a - E1 X e • X.f0 a ∈ mL X.B.I X.B.g := by
  have := congruence_on_idempotent hJ hE (X.basisApprox a).2
  rw [smul_sub] at this
  have h2 := (mL X.B.I X.B.g).neg_mem this
  rw [neg_sub] at h2
  exact h2

theorem zh_cong : zh X e u - E1 X e • X.z0 ∈ mL X.B.I X.B.g := by
  have := congruence_on_idempotent hJ hE (X.xu_z u)
  rw [smul_sub] at this
  exact this

theorem mem_of_cong {x x0 : VA X.B.I} (hx0 : x0 ∈ X.B.I.Lf) (h : x - E1 X e • x0 ∈ mL X.B.I X.B.g) :
    x ∈ X.B.I.Lf := by
  have h1 : E1 X e • x0 ∈ X.B.I.Lf := smul_int_mem (integral_circleChar X hE.1) hx0
  have := X.B.I.Lf.add_mem (mL_le_Lf _ h) h1
  rwa [sub_add_cancel] at this

theorem eh_Lf (a : Fin D.R.rS) : eh X e a ∈ X.B.I.Lf :=
  mem_of_cong hJ hE ((frame_Lf X).1 a) (eh_cong hJ hE a)
theorem fh_Lf (a : Fin D.R.rS) : fh X e a ∈ X.B.I.Lf :=
  mem_of_cong hJ hE ((frame_Lf X).2.1 a) (fh_cong hJ hE a)
theorem zh_Lf : zh X e u ∈ X.B.I.Lf :=
  mem_of_cong hJ hE (frame_Lf X).2.2.1 (zh_cong hJ hE u)

theorem Qv_Lf {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : Qv X e u y ∈ X.B.I.Lf := by
  unfold Qv FrameAlg.Q
  have hi : ∀ x w, x ∈ X.B.I.Lf → w ∈ X.B.I.Lf → Formalism.UG.hform (sigA X.B.I) (JA X.B.I) x w ∈ IntAf X.B.I.F X.B.I.E :=
    fun x w hx hw => hA_int X.B.I hx hw
  refine X.B.I.Lf.add_mem (smul_int_mem (neg_mem (hi _ _ (zh_Lf hJ hE u) (zh_Lf hJ hE u)))
    (X.B.I.Lf.sub_mem hy (Submodule.sum_mem _ fun a _ => X.B.I.Lf.add_mem ?_ ?_)))
    (smul_int_mem (hi _ _ (zh_Lf hJ hE u) hy) (zh_Lf hJ hE u))
  · exact smul_int_mem (hi _ _ (fh_Lf hJ hE a) hy) (eh_Lf hJ hE a)
  · exact smul_int_mem (hi _ _ (eh_Lf hJ hE a) hy) (fh_Lf hJ hE a)

omit hJ hE in
theorem Z_hA_mL' {d w : VA X.B.I} (hd : d ∈ mL X.B.I X.B.g) (hw : w ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I w d) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g (Z_hA_mL X hd hw)

omit hJ hE in

theorem Z_pair {x x' y y' : VA X.B.I} (hx : x - x' ∈ mL X.B.I X.B.g) (hy : y - y' ∈ mL X.B.I X.B.g)
    (hyL : y ∈ X.B.I.Lf) (hx'L : x' ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I x y - hA X.B.I x' y') := by
  have e1 : hA X.B.I x y - hA X.B.I x' y' = hA X.B.I (x - x') y + hA X.B.I x' (y - y') := by
    rw [hA_sub_right, sub_hA_left x x' y]; ring
  rw [e1]
  exact Z_add X.B.I X.B.g (Z_hA_mL X hx hyL) (Z_hA_mL' hy hx'L)

theorem N_cong : ZMod' X.B.I X.B.g (hA X.B.I (zh X e u) (zh X e u) + E1 X e) := by
  have hz0 := (frame_Lf X).2.2.1
  have hc := zh_cong hJ hE u
  have h1 := Z_pair hc hc (zh_Lf hJ hE u) (smul_int_mem (integral_circleChar X hE.1) hz0)
  rw [hermitian_idempotent_smul hE.2.1] at h1
  have h2 := Z_smul X.B.I X.B.g (integral_circleChar X hE.1) X.formsAtZero.1
  have := Z_add X.B.I X.B.g h1 h2
  convert this using 1
  ring

theorem Qv_cong {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (he0 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) y))
    (hf0 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) y)) (hz0 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 y)) :
    Qv X e u y - E1 X e • y ∈ mL X.B.I X.B.g := by
  have hEi := integral_circleChar X hE.1
  have Zc : ∀ (x x0 : VA X.B.I), x - E1 X e • x0 ∈ mL X.B.I X.B.g → ZMod' X.B.I X.B.g (hA X.B.I x0 y) →
      ZMod' X.B.I X.B.g (hA X.B.I x y) := fun x x0 hc h0 => by
    rw [sub_hA_left x (E1 X e • x0) y, hermitian_idempotent_smul_left]
    exact Z_add X.B.I X.B.g (Z_hA_mL X hc hy) (Z_smul X.B.I X.B.g hEi h0)
  set N := hA X.B.I (zh X e u) (zh X e u)
  have hN : ZMod' X.B.I X.B.g (-N - E1 X e) := by
    have := Z_sub X.B.I X.B.g (Z_zero X.B.I X.B.g) (N_cong hJ hE u)
    convert this using 1; ring
  have hNi : N ∈ IntAf X.B.I.F X.B.I.E := hA_int X.B.I (zh_Lf hJ hE u) (zh_Lf hJ hE u)
  have e1 : Qv X e u y - E1 X e • y = (-N - E1 X e) • y +
      N • (∑ a, (hA X.B.I (fh X e a) y • eh X e a + hA X.B.I (eh X e a) y • fh X e a)) +
      hA X.B.I (zh X e u) y • zh X e u := by
    simp only [Qv, FrameAlg.Q]
    change (-N) • (y - ∑ a, (hA X.B.I (fh X e a) y • eh X e a + hA X.B.I (eh X e a) y • fh X e a)) +
      hA X.B.I (zh X e u) y • zh X e u - E1 X e • y = _
    simp only [smul_sub, sub_smul, neg_smul]
    abel
  rw [e1]
  refine (mL X.B.I X.B.g).add_mem ((mL X.B.I X.B.g).add_mem (Z_smul_mL X hN hy) (smul_int_mem hNi
    (Submodule.sum_mem _ fun a _ => (mL X.B.I X.B.g).add_mem ?_ ?_))) ?_
  · exact Z_smul_mL X (Zc _ _ (fh_cong hJ hE a) (hf0 a)) (eh_Lf hJ hE a)
  · exact Z_smul_mL X (Zc _ _ (eh_cong hJ hE a) (he0 a)) (fh_Lf hJ hE a)
  · exact Z_smul_mL X (Zc _ _ (zh_cong hJ hE u) hz0) (zh_Lf hJ hE u)

end PI.UnitaryDimensionFormula.FrameX

namespace PI.UnitaryDimensionFormula.FrameX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PI.UnitaryDimensionFormula

variable {D : D7} {X : HidaSetting D}

theorem eps_eq (e : Af X.B.I.F) : epsX X e = E1 X e * X.ew := rfl

theorem int_adj {S : Subring (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)} {k : ℕ}
    {M : Matrix (Fin k) (Fin k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)} (h : ∀ i j, M i j ∈ S) (i j : Fin k) :
    M.adjugate i j ∈ S := by
  let M' : Matrix (Fin k) (Fin k) S := fun i j => ⟨M i j, h i j⟩
  have e1 : M = S.subtype.mapMatrix M' := by ext i j; rfl
  rw [e1, ← RingHom.map_adjugate]
  exact ((M'.adjugate) i j).2

variable {e : Af X.B.I.F}

theorem eps_int (hE : EgProp X.B.I.F X.B.g e) : epsX X e ∈ IntAf X.B.I.F X.B.I.E := mul_mem (integral_circleChar X hE.1) X.ew_int

theorem eps_idem (he : e * e = e) : epsX X e * epsX X e = epsX X e := by
  rw [eps_eq]
  have h1 := idempotent_mul_self X he
  have h2 := X.ew_idem
  linear_combination (X.ew * X.ew) * h1 + E1 X e * h2

theorem sig_eps : sigA X.B.I (epsX X e) = E1 X e * sigA X.B.I X.ew := by
  rw [eps_eq, map_mul, idempotent_conj_fixed]

theorem eps_orth : epsX X e * sigA X.B.I (epsX X e) = 0 := by
  rw [sig_eps, eps_eq]
  have h2 := X.ew_orth
  linear_combination (E1 X e * E1 X e) * h2

theorem epsilon_idempotent_mul (he : e * e = e) : epsX X e * E1 X e = epsX X e := by
  rw [eps_eq]; linear_combination X.ew * idempotent_mul_self X he

theorem eps_ew : epsX X e * X.ew = epsX X e := by
  rw [eps_eq]; linear_combination E1 X e * X.ew_idem

def bv (e : Af X.B.I.F) (u : D.what₂.Word) (j : Fin D.R.k) : VA X.B.I := epsX X e • Qv X e u (X.bw j)
def cv (e : Af X.B.I.F) (u : D.what₂.Word) (l : Fin D.R.k) : VA X.B.I :=
  sigA X.B.I (epsX X e) • Qv X e u (X.bwd l)

theorem Qbw_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (j : Fin D.R.k) : Qv X e u (X.bw j) - E1 X e • X.bw j ∈ mL X.B.I X.B.g :=
  Qv_cong hJ hE u ((frame_Lf X).2.2.2.1 j) (fun a => ((X.weightVectorsIntegral j).2.2 a).1) (fun a => ((X.weightVectorsIntegral j).2.2 a).2.1)
    (X.weightVectorsIntegral j).1

theorem Qbwd_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (l : Fin D.R.k) : Qv X e u (X.bwd l) - E1 X e • X.bwd l ∈ mL X.B.I X.B.g :=
  Qv_cong hJ hE u ((frame_Lf X).2.2.2.2 l) (fun a => ((X.weightVectorsIntegral l).2.2 a).2.2.1)
    (fun a => ((X.weightVectorsIntegral l).2.2 a).2.2.2) (X.weightVectorsIntegral l).2.1

theorem bv_Lf (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (j : Fin D.R.k) : bv e u j ∈ X.B.I.Lf :=
  smul_int_mem (eps_int hE) (Qv_Lf hJ hE u ((frame_Lf X).2.2.2.1 j))

theorem cv_Lf (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (l : Fin D.R.k) : cv e u l ∈ X.B.I.Lf :=
  smul_int_mem (sigA_mem X.B.I (eps_int hE)) (Qv_Lf hJ hE u ((frame_Lf X).2.2.2.2 l))

theorem G_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (l j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I (cv e u l) (bv e u j) - if l = j then epsX X e else 0) := by
  have hp := Z_pair (Qbwd_cong hJ hE u l) (Qbw_cong hJ hE u j) (Qv_Lf hJ hE u ((frame_Lf X).2.2.2.1 j))
    (smul_int_mem (integral_circleChar X hE.1) ((frame_Lf X).2.2.2.2 l))
  rw [hermitian_idempotent_smul hE.2.1] at hp
  have h1 := Z_smul X.B.I X.B.g (eps_int hE) hp
  have h2 := Z_smul X.B.I X.B.g (eps_int hE) (X.bw_dual l j)
  have e1 : hA X.B.I (cv e u l) (bv e u j) = epsX X e * hA X.B.I (Qv X e u (X.bwd l)) (Qv X e u (X.bw j)) := by
    rw [cv, bv, hA_smul_left, hA_smul_right, sigA_sigA, ← mul_assoc, eps_idem hE.2.1]
  rw [e1]
  have := Z_add X.B.I X.B.g h1 h2
  convert this using 1
  have h3 := epsilon_idempotent_mul hE.2.1
  have h4 : epsX X e * X.ew = epsX X e := eps_ew
  split_ifs
  · linear_combination (hA X.B.I (X.bwd l) (X.bw j)) * h3 + h4
  · linear_combination (hA X.B.I (X.bwd l) (X.bw j)) * h3

theorem cbw_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (l j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I (cv e u l) (X.bw j) - if l = j then epsX X e else 0) := by
  have hp : ZMod' X.B.I X.B.g (hA X.B.I (Qv X e u (X.bwd l)) (X.bw j) - hA X.B.I (E1 X e • X.bwd l) (X.bw j)) := by
    rw [sub_hA_left (Qv X e u (X.bwd l)) (E1 X e • X.bwd l) (X.bw j), add_sub_cancel_right]
    exact Z_hA_mL X (Qbwd_cong hJ hE u l) ((frame_Lf X).2.2.2.1 j)
  rw [hermitian_idempotent_smul_left] at hp
  have h1 := Z_smul X.B.I X.B.g (eps_int hE) hp
  have h2 := Z_smul X.B.I X.B.g (eps_int hE) (X.bw_dual l j)
  have e1 : hA X.B.I (cv e u l) (X.bw j) = epsX X e * hA X.B.I (Qv X e u (X.bwd l)) (X.bw j) := by
    rw [cv, hA_smul_left, sigA_sigA]
  rw [e1]
  have := Z_add X.B.I X.B.g h1 h2
  convert this using 1
  have h3 := epsilon_idempotent_mul hE.2.1
  have h4 : epsX X e * X.ew = epsX X e := eps_ew
  split_ifs
  · linear_combination (hA X.B.I (X.bwd l) (X.bw j)) * h3 + h4
  · linear_combination (hA X.B.I (X.bwd l) (X.bw j)) * h3

theorem bwdb_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (i j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (bv e u j) - if i = j then epsX X e else 0) := by
  have hp : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (Qv X e u (X.bw j)) - hA X.B.I (X.bwd i) (E1 X e • X.bw j)) := by
    rw [← hA_sub_right]
    exact Z_hA_mL' (Qbw_cong hJ hE u j) ((frame_Lf X).2.2.2.2 i)
  rw [hA_smul_right] at hp
  have h1 := Z_smul X.B.I X.B.g (eps_int hE) hp
  have h2 := Z_smul X.B.I X.B.g (eps_int hE) (X.bw_dual i j)
  have e1 : hA X.B.I (X.bwd i) (bv e u j) = epsX X e * hA X.B.I (X.bwd i) (Qv X e u (X.bw j)) := by
    rw [bv, hA_smul_right]
  rw [e1]
  have := Z_add X.B.I X.B.g h1 h2
  convert this using 1
  have h3 := epsilon_idempotent_mul hE.2.1
  have h4 : epsX X e * X.ew = epsX X e := eps_ew
  split_ifs
  · linear_combination (hA X.B.I (X.bwd i) (X.bw j)) * h3 + h4
  · linear_combination (hA X.B.I (X.bwd i) (X.bw j)) * h3

theorem to_ew (hE : EgProp X.B.I.F X.B.g e) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : c ∈ IntAf X.B.I.F X.B.I.E) (b : Prop) [Decidable b]
    (h : ZMod' X.B.I X.B.g (c - if b then epsX X e else 0)) : ZMod' X.B.I X.B.g (c - if b then X.ew else 0) := by
  refine Zfix hE (sub_mem hc (by split_ifs; exacts [X.ew_int, zero_mem _])) ?_
  have h1 := Z_smul X.B.I X.B.g (integral_circleChar X hE.1) h
  convert h1 using 1
  have h3 : E1 X e * epsX X e = epsX X e := by rw [mul_comm]; exact epsilon_idempotent_mul hE.2.1
  split_ifs
  · rw [mul_sub, mul_sub, h3, eps_eq]
  · ring

end PI.UnitaryDimensionFormula.FrameX
end
end

section
noncomputable section

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace PI.UnitaryDimensionFormula

def FrGram : Prop := ∀ (D : D7) (X : HidaSetting D) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
  ∀ G : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), (∀ l j, G l j ∈ IntAf X.B.I.F X.B.I.E) →
  (∀ l j, ZMod' X.B.I X.B.g (G l j - if l = j then epsX X e else 0)) →
  ∃ y ∈ IntAf X.B.I.F X.B.I.E, epsX X e * G.det * y = epsX X e

theorem fg_det {B : Type} [CommRing B] (S : Subring B) {k : ℕ} (G : Matrix (Fin k) (Fin k) B) (ε gg : B)
    (hε : ε ∈ S) (hg : gg ∈ S) (hG : ∀ l j, G l j ∈ S)
    (hc : ∀ l j, ∃ t ∈ S, G l j - (if l = j then ε else 0) = gg * t) :
    ∃ m ∈ S, G.det = ε ^ k + gg * m := by
  classical

  let G' : Matrix (Fin k) (Fin k) S := fun l j => ⟨G l j, hG l j⟩
  let ε' : S := ⟨ε, hε⟩
  let g' : S := ⟨gg, hg⟩
  let I : Ideal S := Ideal.span {g'}
  have hmap : (Ideal.Quotient.mk I).mapMatrix G' =
      Matrix.scalar (Fin k) (Ideal.Quotient.mk I ε') := by
    ext l j
    obtain ⟨t, ht, he⟩ := hc l j
    have hsub : G' l j - (if l = j then ε' else 0) ∈ I := by
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨t, ht⟩, ?_⟩
      apply Subtype.ext
      split_ifs at he ⊢ <;> simp [G', ε', g'] <;> first | linear_combination he | linear_combination -he
    have := Ideal.Quotient.eq.mpr hsub
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    rw [this]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I G'.det = Ideal.Quotient.mk I (ε' ^ k) := by
    rw [RingHom.map_det, hmap, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, map_pow]
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hdet)
  refine ⟨m, m.2, ?_⟩
  have hG' : S.subtype.mapMatrix G' = G := by
    ext l j
    rfl
  have h1 : G.det = S.subtype G'.det := by
    rw [RingHom.map_det, hG']
  have h2 : G'.det = ε' ^ k + m * g' := by
    rw [hm]; ring
  rw [h1, h2]
  simp [ε', g', mul_comm]

theorem frGram : FrGram := by
  intro D X e hE G hGi hGc
  have h1 : X.ew * X.ew = X.ew := X.ew_idem
  have h2 : X.ew ∈ IntAf X.B.I.F X.B.I.E := X.ew_int
  have h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e ∈ IntAf X.B.I.F X.B.I.E := by
    unfold IntAf Formalism.UG.tensInt
    exact Subring.subset_closure (Or.inr ⟨⟨e, hE.1⟩, rfl⟩)
  have hε : epsX X e ∈ IntAf X.B.I.F X.B.I.E := (IntAf X.B.I.F X.B.I.E).mul_mem h3 h2
  have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E :=
    natCast_mem (IntAf X.B.I.F X.B.I.E) _
  obtain ⟨m, hm, hdet⟩ := fg_det (IntAf X.B.I.F X.B.I.E) G (epsX X e)
    ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hε hg hGi (fun l j => hGc l j)

  have hidem : epsX X e * epsX X e = epsX X e := by
    unfold epsX
    calc (1 ⊗ₜ[X.B.I.F] e * X.ew) * (1 ⊗ₜ[X.B.I.F] e * X.ew)
        = ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e * (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (X.ew * X.ew) := by ring
      _ = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e * X.ew := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hE.2.1, h1]
  have hpow : ∀ n : ℕ, epsX X e * epsX X e ^ n = epsX X e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hidem]
  obtain ⟨y, hy, hyeq⟩ := idxDJacE X.B.I.F X.B.I.E X.B.g e hE m hm
  refine ⟨y, hy, ?_⟩
  rw [hdet, mul_add, hpow]
  have hfac : epsX X e + epsX X e * (((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) =
      X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e *
        (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m)) := by
    unfold epsX
    ring
  rw [hfac, mul_assoc, hyeq]
  unfold epsX
  ring

end PI.UnitaryDimensionFormula
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  PI.UnitaryDimensionFormula.unitaryCongruence PI.UnitaryDimensionFormula.NormCutK PI.UnitaryDimensionFormula.FrameX

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxDFrame_of (hS : IdxDSig) (hJ : IdxDJacE) (hG : FrGram) : IdxDFrame := by
  intro D X u e hE
  set eps := epsX X e with heps
  set G : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
    Matrix.of fun l j => Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (cv e u l) (bv e u j) with hGdef
  have hGint : ∀ l j, G l j ∈ IntAf X.B.I.F X.B.I.E := fun l j =>
    hA_int X.B.I (cv_Lf hJ hE u l) (bv_Lf hJ hE u j)
  have hGc : ∀ l j, ZMod' X.B.I X.B.g (G l j - if l = j then eps else 0) := fun l j => G_cong hJ hE u l j
  obtain ⟨y, hy, hyE⟩ := hG D X e hE G hGint hGc
  set M := (eps * y) • G.adjugate with hMdef
  have hM : M * G = eps • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) := FrameAlg.inv_on G eps y hyE
  have hMint : ∀ i l, M i l ∈ IntAf X.B.I.F X.B.I.E := fun i l =>
    mul_mem (mul_mem (eps_int hE) hy) (int_adj hGint i l)
  have hMe : ∀ i l, M i l * eps = M i l := fun i l => by
    show eps * y * G.adjugate i l * eps = eps * y * G.adjugate i l
    have := eps_idem (X := X) hE.2.1
    linear_combination (y * G.adjugate i l) * this
  have hse : sigA X.B.I eps * sigA X.B.I eps = sigA X.B.I eps := by
    rw [← map_mul, eps_idem hE.2.1]
  refine ⟨bv e u, fun i => ∑ l, sigA X.B.I (M i l) • cv e u l, ⟨eps_idem hE.2.1, eps_orth, fun i => ?_,
    fun i => ?_, fun i j => ?_⟩, fun i => ⟨bv_Lf hJ hE u i, ?_⟩, fun i w hw => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩⟩
  · rw [bv, smul_smul, eps_idem hE.2.1]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [cv, smul_comm (sigA X.B.I eps) (sigA X.B.I (M i l)), smul_smul (sigA X.B.I eps), hse]
  · exact FrameAlg.dual_fix (sigA X.B.I) (JA X.B.I) (hS X.B.I).1 (bv e u) (cv e u) eps M hM i j
  · exact Submodule.sum_mem _ fun l _ => smul_int_mem (sigA_mem X.B.I (hMint i l)) (cv_Lf hJ hE u l)
  · rw [hA_symm X.B.I w, bv, hA_smul_right]
    have := fixV_perp hS hE.2.1 u (X.bw i) w hw
    rw [eps_eq, show E1 X e * X.ew * hA X.B.I w (Qv X e u (X.bw i)) =
      X.ew * (E1 X e * hA X.B.I w (Qv X e u (X.bw i))) by ring, this, mul_zero, map_zero]
  · rw [hA_symm X.B.I w, ← hL_apply, map_sum]
    have hz : ∀ l, hL X.B.I w (sigA X.B.I (M i l) • cv e u l) = 0 := fun l => by
      rw [hL_apply, hA_smul_right, cv, hA_smul_right, sig_eps]
      have := fixV_perp hS hE.2.1 u (X.bwd l) w hw
      rw [show sigA X.B.I (M i l) * (E1 X e * sigA X.B.I X.ew * hA X.B.I w (Qv X e u (X.bwd l))) =
        sigA X.B.I (M i l) * sigA X.B.I X.ew * (E1 X e * hA X.B.I w (Qv X e u (X.bwd l))) by ring, this, mul_zero]
    rw [Finset.sum_eq_zero fun l _ => hz l, map_zero]
  ·
    have hsum : hA X.B.I (∑ l, sigA X.B.I (M i l) • cv e u l) (X.bw j) =
        ∑ l, M i l * hA X.B.I (cv e u l) (X.bw j) := by
      show Formalism.UG.hform (sigA X.B.I) (JA X.B.I) _ _ = _
      rw [FrameAlg.h_sum_left]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [FrameAlg.h_smul_left, sigA_sigA]; rfl
    have h1 : ZMod' X.B.I X.B.g (∑ l, M i l * (hA X.B.I (cv e u l) (X.bw j) - if l = j then eps else 0)) :=
      Z_sum X.B.I X.B.g _ _ fun l _ => Z_smul X.B.I X.B.g (hMint i l) (cbw_cong hJ hE u l j)
    have h2 : ZMod' X.B.I X.B.g (∑ l, M i l * (G l j - if l = j then eps else 0)) :=
      Z_sum X.B.I X.B.g _ _ fun l _ => Z_smul X.B.I X.B.g (hMint i l) (hGc l j)
    have hMG : ∑ l, M i l * G l j = if i = j then eps else 0 := by
      have := congrFun (congrFun hM i) j
      simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using this
    have hs : ∀ (F : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        ∑ l, M i l * (F l - if l = j then eps else 0) = ∑ l, M i l * F l - M i j := fun F => by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, hMe]
    rw [hs, hMG] at h2
    rw [hs] at h1
    refine to_ew hE (hA_int X.B.I (Submodule.sum_mem _ fun l _ =>
      smul_int_mem (sigA_mem X.B.I (hMint i l)) (cv_Lf hJ hE u l)) ((frame_Lf X).2.2.2.1 j)) (i = j) ?_
    rw [hsum]
    have := Z_sub X.B.I X.B.g h1 h2
    convert this using 1
    ring
  · exact to_ew hE (hA_int X.B.I ((frame_Lf X).2.2.2.2 i) (bv_Lf hJ hE u j)) (i = j) (bwdb_cong hJ hE u i j)

theorem idxDFrame : IdxDFrame := idxDFrame_of idxDSig idxDJacE frGram

end PI.UnitaryDimensionFormula
end
end

section
namespace PI.UnitaryDimensionFormula

theorem indexGe : IndexGe := indexGe_of uniSub idxHom (idxSurj_of_frame idxDFrame)

end PI.UnitaryDimensionFormula
end
