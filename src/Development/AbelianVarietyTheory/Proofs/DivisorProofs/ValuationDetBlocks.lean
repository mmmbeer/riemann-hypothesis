import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepIdentities
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMeasureTopBlockIntegralGLMaxIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeConjugateSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

def StdSupp (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : Prop :=
  (∀ i j, x.toRows₁ i j ∈ 𝒪[k]) ∧ valuation k x.toRows₁.det = 1 ∧ ∀ i j, x.toRows₂ i j ∈ cball (ϖ ^ c)

theorem StdSupp.det_ne {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x) :
    x.toRows₁.det ≠ 0 := fun h0 => by
  have := h.2.1
  rw [h0, map_zero] at this
  exact zero_ne_one this

open Classical in

def stdDatum (μ : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : ℂ :=
  if h : StdSupp ϖ c x then (((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

theorem int_mul {m p r : Type} [Fintype p] {A : Matrix m p k} {B : Matrix p r k} (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j) : (A * B) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hA i l) (hB l j)

theorem cball_mul {m p r : Type} [Fintype p] {s : kˣ} {A : Matrix m p k} {B : Matrix p r k}
    (hA : ∀ i j, A i j ∈ cball s) (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j) : (A * B) i j ∈ cball s := by
  rw [Matrix.mul_apply]
  refine Finset.sum_induction _ (· ∈ cball s) (fun _ _ => add_mem_cball) (by simp [cball]) fun l _ => ?_
  have h1 := hA i l
  have h2 := hB l j
  simp only [cball, Set.mem_setOf_eq, map_mul] at h1 ⊢
  rw [Valuation.mem_integer_iff] at h2
  calc valuation k (A i l) * valuation k (B l j) ≤ valuation k (s : k) * 1 := mul_le_mul' h1 h2
    _ = _ := mul_one _

theorem toRows₁_mul {m : Type} [Fintype m] (x : Matrix (Fin n ⊕ Fin n') m k) (g : Matrix m (Fin n) k) :
    (x * g).toRows₁ = x.toRows₁ * g := by ext i j; simp [Matrix.toRows₁, Matrix.mul_apply]

theorem toRows₂_mul {m : Type} [Fintype m] (x : Matrix (Fin n ⊕ Fin n') m k) (g : Matrix m (Fin n) k) :
    (x * g).toRows₂ = x.toRows₂ * g := by ext i j; simp [Matrix.toRows₂, Matrix.mul_apply]

theorem valuation_det_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : valuation k g.val.det = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have h1 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val.det = algebraMap 𝒪[k] k u.val.det :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)

theorem StdSupp.mul {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x)
    {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : StdSupp ϖ c (x * g.val) := by
  have hgi := ((SplitFlip.mem_KO_iff g).1 hg).1
  refine ⟨?_, ?_, ?_⟩
  · rw [toRows₁_mul]; exact int_mul h.1 hgi
  · rw [toRows₁_mul, Matrix.det_mul, map_mul, h.2.1, valuation_det_KO hg, one_mul]
  · rw [toRows₂_mul]; exact cball_mul h.2.2 hgi

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta
end
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open GlobalTheory.SplitFlip (omA omB invT IsUnif mem_KO_iff isOpen_KO)
open GlobalTheory.StdLocZeta (StdSupp stdDatum)
open GlobalTheory.StdLoc (glVol blockIdx)
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.LocStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Renumber

variable {X a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] [MeasurableSpace X]

def renum (E : b × a ≃ b' × a') : Matrix b' a' X ≃ᵐ Matrix b a X :=
  (MeasurableEquiv.curry b' a' X).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ => X) E).symm.trans (MeasurableEquiv.curry b a X))

end Renumber

section Level

variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem mem_image_KO {M : Matrix D D k} :
    M ∈ Units.val '' (KO k D : Set (GL D k)) ↔ (∀ i j, M i j ∈ 𝒪[k]) ∧ valuation k M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨((mem_KO_iff g).1 hg).1, SplitFlip.valuation_gdet_of_mem_KO hg⟩
  · rintro ⟨hM, hd⟩
    let N : Matrix D D 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
    have e : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
    have hu : IsUnit N.det := by
      refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
      rw [RingHom.map_det, e, hd]
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    change (algebraMap 𝒪[k] k).mapMatrix u.val = M
    rw [hu', e]

theorem mem_KO_iff_det {g : GL D k} : g ∈ KO k D ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ valuation k g.val.det = 1 := by
  rw [← mem_image_KO]
  exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨u, hu, e⟩ => Units.ext e ▸ hu⟩

def blockDiag (s : kˣ) (σ : A ⊕ A' ≃ D) : GL D k := SplitFlip.diagGL fun i => Sum.elim (fun _ => 1) (fun _ => s) (σ.symm i)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] [DecidableEq A] [Fintype A']
  [DecidableEq A'] in
theorem conj_blockDiag (s : kˣ) (σ : A ⊕ A' ≃ D) (h : GL D k) (i j : A ⊕ A') :
    ((blockDiag s σ)⁻¹ * h * blockDiag s σ).val (σ i) (σ j) =
      ((Sum.elim (fun _ => 1) (fun _ => s) i : kˣ)⁻¹ : kˣ) * h.val (σ i) (σ j) *
        (Sum.elim (fun _ => 1) (fun _ => s) j : kˣ) := by
  have : ((blockDiag s σ)⁻¹).val =
    diagonal fun i => (((Sum.elim (fun _ => 1) (fun _ => s) (σ.symm i) : kˣ)⁻¹ : kˣ) : k) := rfl
  rw [Units.val_mul, Units.val_mul, this]
  simp only [blockDiag, SplitFlip.diagGL_val, mul_diagonal, diagonal_mul, Equiv.symm_apply_apply]

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] in

theorem conj_mem_KO_iff {s : kˣ} (hs : (s : k) ∈ 𝒪[k]) (σ : A ⊕ A' ≃ D) {h : GL D k} (hh : h ∈ KO k D) :
    (blockDiag s σ)⁻¹ * h * blockDiag s σ ∈ KO k D ↔ ∀ i j, h.val (σ (.inr i)) (σ (.inl j)) ∈ cball s := by
  have key : ∀ x : k, ((s⁻¹ : kˣ) : k) * x ∈ 𝒪[k] ↔ x ∈ cball s := fun x => by
    rw [cball_eq_smul, Set.mem_smul_set_iff_inv_smul_mem]; rfl
  have hi := ((mem_KO_iff h).1 hh).1
  constructor
  · intro H i j
    have := ((mem_KO_iff _).1 H).1 (σ (.inr i)) (σ (.inl j))
    rw [conj_blockDiag] at this
    exact (key _).1 (by simpa using this)
  · intro H
    refine mem_KO_iff_det.2 ⟨fun i j => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := σ.surjective i
      obtain ⟨j, rfl⟩ := σ.surjective j
      rw [conj_blockDiag]
      rcases i with i | i <;> rcases j with j | j
      · simpa using hi _ _
      · simpa using mul_mem (hi _ _) hs
      · simpa using (key _).2 (H i j)
      · have : ((s⁻¹ : kˣ) : k) * h.val (σ (.inr i)) (σ (.inr j)) * s = h.val (σ (.inr i)) (σ (.inr j)) := by
          rw [mul_right_comm, Units.inv_mul, one_mul]
        simpa only [Sum.elim_inr, this] using hi _ _
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]
      exact (mem_KO_iff_det.1 hh).2

def levelJ {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (σ : A ⊕ A' ≃ D) : Subgroup (GL D k) where
  carrier := {h | h ∈ KO k D ∧ ∀ i j, h.val (σ (.inr i)) (σ (.inl j)) ∈ cball (ϖ ^ c)}
  one_mem' := ⟨one_mem _, fun i j => by simp [cball, Matrix.one_apply]⟩
  mul_mem' := fun {x y} hx hy => by
    have hs : ((ϖ ^ c : kˣ) : k) ∈ 𝒪[k] := by rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem c
    refine ⟨mul_mem hx.1 hy.1, (conj_mem_KO_iff hs σ (mul_mem hx.1 hy.1)).1 ?_⟩
    have := mul_mem ((conj_mem_KO_iff hs σ hx.1).2 hx.2) ((conj_mem_KO_iff hs σ hy.1).2 hy.2)
    simpa only [mul_assoc, mul_inv_cancel_left] using this
  inv_mem' := fun {x} hx => by
    have hs : ((ϖ ^ c : kˣ) : k) ∈ 𝒪[k] := by rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem c
    refine ⟨inv_mem hx.1, (conj_mem_KO_iff hs σ (inv_mem hx.1)).1 ?_⟩
    have := inv_mem ((conj_mem_KO_iff hs σ hx.1).2 hx.2)
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using this

variable {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (σ : A ⊕ A' ≃ D)

variable [MeasurableSpace k] [BorelSpace k]

end Level

section Pair

variable {n n' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

def colDatum (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D) (X : Matrix (Fin n) D k) : ℂ :=
  stdDatum ν ϖ c (Xᵀ.submatrix σ id)

variable (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D)

omit [Fintype D] [DecidableEq D] in

theorem colDatum_eq {X : Matrix (Fin n) D k} {u : GL (Fin n) k} (hu : u ∈ KO k (Fin n))
    (h₁ : ∀ i j, X i (σ (.inl j)) = u.val i j) (h₂ : ∀ i j, X i (σ (.inr j)) ∈ cball (ϖ ^ c)) :
    colDatum ν ϖ c σ X = (((ν (GeneralLinearGroup.det u))⁻¹ : ℂˣ) : ℂ) := by
  have e : (Xᵀ.submatrix σ id).toRows₁ = u.valᵀ := by ext i j; exact h₁ j i
  have h : StdSupp ϖ c (Xᵀ.submatrix σ id) :=
    ⟨fun i j => by rw [e]; exact (mem_KO_iff_det.1 hu).1 j i, by rw [e, det_transpose]; exact (mem_KO_iff_det.1 hu).2,
      fun i j => h₂ j i⟩
  rw [colDatum, stdDatum, dif_pos h]
  congr 3
  exact Units.ext (by simp [e])

variable [MeasurableSpace k] [BorelSpace k] {m : Measure k}

variable {ν ϖ}

omit [MeasurableSpace k] [BorelSpace k] in

def zetaIntegrand (φ : GL (Fin n) k → ℂ) (s₀ s : ℂ) (g : GL (Fin n) k) : ℂ :=
  φ g * npow (iwAbs (absRatio k (Fin n)) (KO k (Fin n ⊕ Fin n)) (io k (Fin n) (g, 1))) (s - s₀)

end Pair

section Main

variable {a a' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

def swapNum (σ : Fin a ⊕ Fin a' ≃ D) : Fin a' ⊕ Fin a ≃ D := (Equiv.sumComm _ _).trans σ

end Main

section Place

open IsDedekindDomain NumberField GlobalTheory.CMVal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Place

example {n n' : ℕ} (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) :
    colDatum ν ϖ c (Equiv.refl (Fin n ⊕ Fin n')) (fromCols 1 0) = 1 := by
  rw [colDatum_eq ν ϖ c _ (one_mem _) (fun i j => rfl) fun i j => by simp [cball]]
  simp

end GlobalTheory.LocStd

end
end
