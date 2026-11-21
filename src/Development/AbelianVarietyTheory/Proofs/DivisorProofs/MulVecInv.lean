import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSettingHeightContinuous

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisCT

theorem exists_col0_ne_zero_of_witt {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, X i 0 ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h1 := congrArg (fun M => M 0 0) hW.xy
  simp only [Matrix.one_apply_eq] at h1
  rw [Matrix.mul_apply] at h1
  simp [Matrix.mul_apply, Formalism.UG.cT, hc] at h1

theorem iwaHt_mul_rat_stabL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ p ∈ ratPts σ J, GlobalTheory.EisCT.StabL σ J (col0 X) p → ∀ v, h (p * v) = h v := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS p hp hst v
  obtain ⟨-, -, -, -, hW, -, hI1, hI2⟩ := hS
  obtain ⟨lp, hlp⟩ := hst
  have key : absE F E lp = 1 := by
    rw [← range_ratEmb] at hp
    obtain ⟨γ, rfl⟩ := hp
    obtain ⟨i, hi⟩ := exists_col0_ne_zero_of_witt hW
    have hmat : (matHom _ σ J (ratEmb σ J γ)).1 = (γ.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
      ext s t; rfl
    rw [hmat] at hlp
    have hent := congrArg (fun M => M i 0) hlp
    simp only [adMat] at hent
    rw [← RingHom.map_matrix_mul] at hent
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hent
    have hx : col0 X i 0 = X i 0 := rfl
    rw [hx] at hent
    set e : E := ((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0 / X i 0 with he_def
    have he : inclR (F := F) (AF F) e * inclR (F := F) (AF F) (X i 0) =
        inclR (F := F) (AF F) (((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0) := by
      rw [← map_mul, he_def, div_mul_cancel₀ _ hi]
    have hu : IsUnit (inclR (F := F) (AF F) (X i 0)) := (isUnit_iff_ne_zero.2 hi).map _
    have hl : lp.1 = inclR (F := F) (AF F) e := by
      rw [← he] at hent
      exact (hu.mul_left_inj.1 hent).symm
    by_cases he0 : e = 0
    · rw [he0, map_zero] at hl
      have : Subsingleton (AF F ⊗[F] E) := by
        have h01 := lp.mul_inv
        rw [hl, zero_mul] at h01
        exact subsingleton_of_zero_eq_one h01
      rw [Subsingleton.elim lp 1, map_one]
    · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 e he0)
      rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 e he0)) = lp from
        Units.ext (by simp [hl])] at this
  obtain ⟨q, lq, hq, k, hk, rfl⟩ := hI1 v
  have e1 : h (q * k) = absE F E lq := hI2 q lq hq k hk
  have hpq : (matHom _ σ J (p * q)).1 * adMat F (col0 X) = (lp * lq).1 • adMat F (col0 X) := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hlp, smul_smul, Units.val_mul, mul_comm]
  have e2 : h (p * q * k) = absE F E (lp * lq) := hI2 (p * q) (lp * lq) hpq k hk
  rw [← mul_assoc, e2, e1, map_mul, key, one_mul]

end GlobalTheory.EisCT
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open IsDedekindDomain
open GlobalTheory.Doubling (absE absEv absEw)

namespace GlobalTheory.EisMidHt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable (F) in

def adVec (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def firstColumn {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => X i 0

variable (F) in

def normFin (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (u : Fin n → Fv F v ⊗[F] E) : ℝ≥0 :=
  sInf {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈ latLoc F L v ∧ c = absEv F E v l}

def normInf (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (u : Fin n → w.Completion ⊗[F] E) : ℝ :=
  let b : GL (Fin n) (w.Completion ⊗[F] E) := (Formalism.UG.bc (compInf F E w) a)⁻¹
  Norm.norm (Finset.univ.sum fun i => Algebra.norm w.Completion ((b.1 *ᵥ u) i)) ^ w.mult

def ht (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (u : Fin n → AF F ⊗[F] E) : ℝ :=
  (∏ᶠ v, (normFin F L v (fun i => compFin F E v (u i)) : ℝ)) * ∏ w, normInf a w (fun i => compInf F E w (u i))

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

def IsLineReps (x y : Fin n → E) (Y : Set (Fin n → E)) : Prop :=
  (∀ z ∈ Y, z ≠ 0 ∧ hE σ J z z = 0 ∧ hE σ J x z = 0 ∧ hE σ J y z = 0) ∧
  (∀ z ∈ Y, ∀ z' ∈ Y, ∀ c : E, z = c • z' → z = z') ∧
  ∀ z : Fin n → E, z ≠ 0 → hE σ J z z = 0 → hE σ J x z = 0 → hE σ J y z = 0 → ∃ z' ∈ Y, ∃ c : E, z = c • z'

end GlobalTheory.EisMidHt

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisUnfold

open GlobalTheory.EisMidHt (adVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in
theorem inv_mulVec_cancel (p : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J p⁻¹).1 *ᵥ (matHom _ σ J p).1 *ᵥ y = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

def vecStab (z : Fin n → AF F ⊗[F] E) (H : Subgroup (AF F ⊗[F] E)ˣ) : Subgroup (GAd σ J) where
  carrier := {p | ∃ l ∈ H, (matHom _ σ J p).1 *ᵥ z = l.1 • z}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro p q ⟨l, hl, e⟩ ⟨l', hl', e'⟩
    refine ⟨l * l', mul_mem hl hl', ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_smul, e, smul_smul, Units.val_mul, mul_comm]
  inv_mem' := by
    rintro p ⟨l, hl, e⟩
    refine ⟨l⁻¹, inv_mem hl, ?_⟩
    have h := inv_mulVec_cancel σ J p z
    rw [e, Matrix.mulVec_smul] at h
    conv_rhs => rw [← h, smul_smul, Units.inv_mul, one_smul]

def vecFix (z : Fin n → AF F ⊗[F] E) : Subgroup (GAd σ J) := vecStab σ J z ⊥

def vecLine (z : Fin n → AF F ⊗[F] E) : Subgroup (GAd σ J) := vecStab σ J z ⊤

def vecLineOne (z : Fin n → AF F ⊗[F] E) : Subgroup (GAd σ J) := vecStab σ J z (absE F E).ker

variable {σ J}

omit [NumberField E] in
theorem mem_vecFix {z : Fin n → AF F ⊗[F] E} {p : GAd σ J} : p ∈ vecFix σ J z ↔ (matHom _ σ J p).1 *ᵥ z = z :=
  ⟨fun ⟨l, hl, e⟩ => by rw [e, Subgroup.mem_bot.1 hl, Units.val_one, one_smul], fun e => ⟨1, one_mem _, by simpa using e⟩⟩

omit [NumberField E] in
theorem mem_vecLine {z : Fin n → AF F ⊗[F] E} {p : GAd σ J} :
    p ∈ vecLine σ J z ↔ ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 *ᵥ z = l.1 • z :=
  ⟨fun ⟨l, _, e⟩ => ⟨l, e⟩, fun ⟨l, e⟩ => ⟨l, trivial, e⟩⟩

omit [NumberField E] in

theorem conj_mem_vecStab {z : Fin n → AF F ⊗[F] E} {H : Subgroup (AF F ⊗[F] E)ˣ} {p q : GAd σ J} (hp : p ∈ vecLine σ J z)
    (hq : q ∈ vecStab σ J z H) : p * q * p⁻¹ ∈ vecStab σ J z H := by
  obtain ⟨l, -, e⟩ := hp
  obtain ⟨l', -, e'⟩ := inv_mem (show p ∈ vecLine σ J z from ⟨l, trivial, e⟩)
  obtain ⟨k, hk, ek⟩ := hq
  refine ⟨k, hk, ?_⟩
  have h := inv_mulVec_cancel σ J p⁻¹ z
  rw [inv_inv] at h
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_smul, ek,
    smul_comm, ← e', Matrix.mulVec_smul, h]

omit [NumberField E] in

theorem conj_mem_vecStab_iff {z w : Fin n → AF F ⊗[F] E} {H : Subgroup (AF F ⊗[F] E)ˣ} {γ p : GAd σ J} {c : (AF F ⊗[F] E)ˣ}
    (e : (matHom _ σ J γ).1 *ᵥ z = c.1 • w) : γ⁻¹ * p * γ ∈ vecStab σ J z H ↔ p ∈ vecStab σ J w H := by
  refine exists_congr fun l => and_congr_right fun _ => ?_
  have h := inv_mulVec_cancel σ J γ⁻¹
  rw [inv_inv] at h
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e]
  constructor
  · intro h1
    have h2 := congrArg ((matHom _ σ J γ).1 *ᵥ ·) h1
    simp only [h, Matrix.mulVec_smul, e] at h2
    rw [smul_comm] at h2
    exact (c.isUnit.smul_left_cancel).1 h2
  · intro h1
    rw [Matrix.mulVec_smul, h1, smul_comm, ← e, Matrix.mulVec_smul, inv_mulVec_cancel]


def IsStart {r : ℕ} (S : Finset (Fin r)) (j : Fin r) : Prop := j.val = 0 ∨ ∃ k ∈ S, k.val + 1 = j.val

def IsStdVec {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r)) (z : Fin n → E) : Prop :=
  (∃ j, IsStart S j ∧ z = Xᵀ j) ∨ ∃ j ∈ S, z = Yᵀ j

example {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E) (S : Finset (Fin (r + 1))) : IsStdVec X Y S (Xᵀ 0) :=
  Or.inl ⟨0, Or.inl rfl, rfl⟩

omit [NumberField E] in
theorem col0_eq_iff {r : ℕ} {X : Matrix (Fin n) (Fin (r + 1)) E} {m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {l : AF F ⊗[F] E} :
    m * adMat F (col0 X) = l • adMat F (col0 X) ↔ m *ᵥ adVec F (Xᵀ 0) = l • adVec F (Xᵀ 0) :=
  ⟨fun h => funext fun i => congrFun (congrFun h i) 0, fun h => Matrix.ext fun i _ => congrFun h i⟩

variable (σ J) in

abbrev Lines {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Type := ratPts σ J ⧸ lineStab σ J (col0 X)

def term {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) (h : GAd σ J → ℝ) (e : ℂ) (q : Lines σ J X) (g : GAd σ J) : ℂ :=
  (h ((q.out : ratPts σ J).1⁻¹ * g) : ℂ) ^ e



section HidaSetting

variable {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ} (hS : HidaSetting σ J X Y L a h)
include hS

theorem ht_pos (g : GAd σ J) : 0 < h g := by
  obtain ⟨p, l, e, k, hk, rfl⟩ := hS.2.2.2.2.2.2.1 g
  rw [hS.2.2.2.2.2.2.2 p l e k hk]
  exact_mod_cast GlobalTheory.Doubling.hom_pos _ l

theorem continuous_term (e : ℂ) (q : Lines σ J X) : Continuous (term X h e q) :=
  (Complex.continuous_ofReal.comp ((HtCont.continuous_iwaHt F E σ n J r X Y L a h hS).comp (continuous_mul_left _))).cpow
    continuous_const fun _ => Complex.ofReal_mem_slitPlane.2 (ht_pos hS _)

theorem norm_term (e : ℂ) (q : Lines σ J X) (g : GAd σ J) : ‖term X h e q g‖ = h ((q.out : ratPts σ J).1⁻¹ * g) ^ e.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hS _) e

end HidaSetting

end GlobalTheory.EisUnfold

end
end

section
open scoped TensorProduct NNReal ENNReal Matrix ComplexConjugate
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.StdPar GlobalTheory.EisUnfold
open GlobalTheory.Doubling (absE)
open GlobalTheory.EisMidHt (adVec)
open Matrix

noncomputable section

namespace GlobalTheory.FlagNorm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in
theorem mulVec_inv (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g).1 *ᵥ (matHom _ σ J g⁻¹).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem inv_mulVec (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem keep_inv {g : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hA : ∀ y, y ∈ A ↔ (matHom _ σ J g).1 *ᵥ y ∈ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A ↔ (matHom _ σ J g⁻¹).1 *ᵥ y ∈ A := by
  rw [hA ((matHom _ σ J g⁻¹).1 *ᵥ y), mulVec_inv]

omit [NumberField E] in
theorem conj_mulVec (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]

omit [NumberField E] in
theorem conj_sub (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y - y =
      (matHom _ σ J m).1 *ᵥ ((matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y - (matHom _ σ J m⁻¹).1 *ᵥ y) := by
  rw [conj_mulVec, mulVec_sub, mulVec_inv]

omit [NumberField E] in
theorem keep_conj {m u : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hm : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A) (hu : ∀ y, y ∈ A ↔ (matHom _ σ J u).1 *ᵥ y ∈ A)
    (y : Fin n → AF F ⊗[F] E) : y ∈ A ↔ (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y ∈ A := by
  rw [conj_mulVec]
  exact (keep_inv hm y).trans ((hu _).trans (hm _))

theorem perp_inv {X : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (hg : ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X {i | i ≤ k})
    {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colPerp σ J X {i | i ≤ k}) :
    (matHom _ σ J g⁻¹).1 *ᵥ y ∈ colPerp σ J X {i | i ≤ k} := by
  have hcol : ∀ i : Fin (k.val + 1), (matHom _ σ J g).1 *ᵥ (fun l => adMat F (initCols X k) l i) ∈
      colSpan F X {i | i ≤ k} := fun i =>
    (hg _).1 (Submodule.subset_span ⟨i.castLE k.2, Nat.le_of_lt_succ i.2, rfl⟩)
  choose a ha using fun i => mem_colSpan_iff.1 (hcol i)
  have hB : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) * Matrix.of (fun l i => a i l) :=
    Matrix.ext fun l i => (congrFun (ha i) l).symm
  have hF := GlobalTheory.UAut.form_mul_of_mul_cols hB
  rw [mem_colPerp_iff] at hy ⊢
  rw [mulVec_mulVec, hF, ← mulVec_mulVec, hy, mulVec_zero]

end GlobalTheory.FlagNorm

open GlobalTheory.FlagNorm in

theorem GlobalTheory.FlagNorm.conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (m : GAd σ J),
      (∀ k ∈ T, ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k}) →
      ∀ u ∈ unip σ J X T, m * u * m⁻¹ ∈ unip σ J X T := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW T m hm u hu
  by_cases hT : T = ∅
  · subst hT
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  have hne := Finset.nonempty_iff_ne_empty.2 hT
  have hkMT : T.max' hne ∈ T := T.max'_mem _
  have eB : {i | ∃ k ∈ T, i ≤ k} = {i | i ≤ T.max' hne} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T.le_max' k hk), fun hi => ⟨_, hkMT, hi⟩⟩

  have keepSub : ∀ T' : Finset (Fin r), T' ⊆ T → ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} := by
    intro T' hT' y
    by_cases h0 : T' = ∅
    · subst h0
      have e : {i : Fin r | ∃ k ∈ (∅ : Finset (Fin r)), i ≤ k} = ∅ := by simp
      rw [e, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun hy => by rw [hy, mulVec_zero], fun hy => by rw [← inv_mulVec m y, hy, mulVec_zero]⟩
    · have hne' := Finset.nonempty_iff_ne_empty.2 h0
      have e : {i | ∃ k ∈ T', i ≤ k} = {i | i ≤ T'.max' hne'} :=
        Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T'.le_max' k hk), fun hi => ⟨_, T'.max'_mem _, hi⟩⟩
      rw [e]
      exact hm _ (hT' (T'.max'_mem _)) y
  have eA : ∀ j : Fin r, {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | ∃ k ∈ T.filter (· < j), i ≤ k} := fun j =>
    Set.ext fun i => ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, Finset.mem_filter.2 ⟨hk, h2⟩, h1⟩,
      fun ⟨k, hk, h1⟩ => ⟨k, (Finset.mem_filter.1 hk).1, h1, (Finset.mem_filter.1 hk).2⟩⟩
  have keepA : ∀ j : Fin r, ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := fun j => by
    rw [eA j]
    exact keepSub _ (Finset.filter_subset _ _)
  have keepB := keepSub T subset_rfl
  rw [eB] at keepB
  have hu1 : ∀ j, u ∈ trivOn σ J (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}) (colSpan F X {j}) :=
    fun j => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).1 j
  have hu2 : u ∈ trivOn σ J (colSpan F X {i | i ≤ T.max' hne}) (colPerp σ J X {i | i ≤ T.max' hne}) := by
    have := (Subgroup.mem_inf.1 hu).2
    rw [eB] at this
    exact this
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ⟨keep_conj (keepA j) (hu1 j).1, fun y hy => ?_⟩, ?_⟩
  ·
    unfold colSpan at hy
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ a ?_
    rw [conj_sub]
    refine (keepA j _).1 ?_
    set z := (matHom _ σ J m⁻¹).1 *ᵥ (adMat F X)ᵀ j
    by_cases hex : ∃ k ∈ T, j ≤ k
    · have hne2 : (T.filter (j ≤ ·)).Nonempty := let ⟨k, hk, hjk⟩ := hex; ⟨k, Finset.mem_filter.2 ⟨hk, hjk⟩⟩
      set k0 := (T.filter (j ≤ ·)).min' hne2
      have hk0 := Finset.mem_filter.1 ((T.filter (j ≤ ·)).min'_mem hne2)
      have hmin : ∀ k ∈ T, j ≤ k → k0 ≤ k := fun k hk hjk => (T.filter (j ≤ ·)).min'_le k (Finset.mem_filter.2 ⟨hk, hjk⟩)
      have hz : z ∈ colSpan F X {i | i ≤ k0} :=
        (keep_inv (hm k0 hk0.1) _).1 (Submodule.subset_span ⟨j, hk0.2, rfl⟩)
      have hle : colSpan F X {i | i ≤ k0} ≤
          (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}).comap ((matHom _ σ J u).1 - 1).mulVecLin := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        have h1 := (hu1 i).2 _ (Submodule.subset_span ⟨i, Set.mem_singleton i, rfl⟩)
        have hsub : {l | ∃ k ∈ T, l ≤ k ∧ k < i} ⊆ {l | ∃ k ∈ T, l ≤ k ∧ k < j} := by
          rintro l ⟨k', hk', hlk', hk'i⟩
          refine ⟨k', hk', hlk', not_le.1 fun hjk' => ?_⟩
          exact absurd (hmin k' hk' hjk') (not_le.2 (lt_of_lt_of_le hk'i hi))
        have h2 := Submodule.span_mono (R := AF F ⊗[F] E) (Set.image_mono (f := fun i => (adMat F X)ᵀ i) hsub) h1
        change _ ∈ colSpan F X _ at h2
        simpa [sub_mulVec] using h2
      simpa [sub_mulVec] using hle hz
    · push_neg at hex
      have eAj : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | i ≤ T.max' hne} := by
        rw [← eB]
        exact Set.ext fun i => ⟨fun ⟨k, hk, h1, _⟩ => ⟨k, hk, h1⟩, fun ⟨k, hk, h1⟩ => ⟨k, hk, h1, hex k hk⟩⟩
      rw [eAj]
      have hxj : (adMat F X)ᵀ j ∈ colPerp σ J X {i | i ≤ T.max' hne} := by
        refine mem_colPerp_iff.2 (funext fun i => ?_)
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ (Xᵀ j) i).symm.trans
          ((congrArg _ (congrFun (congrFun hW.xx (i.castLE (T.max' hne).2)) j)).trans (map_zero _))
      exact hu2.2 z (perp_inv (hm _ hkMT) hxj)
  · rw [eB]
    refine ⟨keep_conj keepB hu2.1, fun y hy => ?_⟩
    rw [conj_sub]
    exact (keepB _).1 (hu2.2 _ (perp_inv (hm _ hkMT) hy))
end
end
