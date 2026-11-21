import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagMatLower

section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

def truncMat {R : Type} [CommRing R] {d : ℕ} (m : ℕ) (M : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin d) (Fin d) R :=
  fun c e => if (c : ℕ) < m ∧ (e : ℕ) < m then M c e else if c = e then 1 else 0

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def frameMat (b g : Frames k V) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c e => (b i).repr (g i e) c

open Classical in

def flagLow (b : Frames k V) (F : Flags k V) (i : ι) :
    Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c a => if h : ∃! v : V i, v ∈ F.step i ((a : ℕ) + 1) ∧ (b i).repr v a = 1 ∧
      ∀ c' : Fin (finrank k (V i)), c' < a → (b i).repr v c' = 0
    then (b i).repr h.exists.choose c else 0

def cellDisc [Fintype ι] (b g : Frames k V) : k :=
  ∏ i, ∏ m : Fin (finrank k (V i) + 1), (truncMat (m : ℕ) (frameMat b g i)).det

theorem det_mem_subalgebra {X : Type} {n : Type} [Fintype n] [DecidableEq n]
    (A : Subalgebra k (X → k)) (M : X → Matrix n n k) (h : ∀ c e, (fun x => M x c e) ∈ A) :
    (fun x => (M x).det) ∈ A := by
  simp only [Matrix.det_apply]
  have : (fun x => ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ c, M x (σ c) c) =
      ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ c, (fun x => M x (σ c) c) := by
    ext x
    simp [Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun c _ => h _ _) _

theorem frameMat_mem_regFns (b : Frames k V) (i : ι) (c e : Fin (finrank k (V i))) :
    (fun g : Frames k V => frameMat b g i c e) ∈ regFns k V :=
  Algebra.subset_adjoin (.inl ⟨i, (b i).coord c, e, rfl⟩)

theorem truncMat_mem_subalgebra {X : Type} {d : ℕ} (A : Subalgebra k (X → k)) (m : ℕ)
    (M : X → Matrix (Fin d) (Fin d) k) (h : ∀ c e, (fun x => M x c e) ∈ A) (c e : Fin d) :
    (fun x => truncMat m (M x) c e) ∈ A := by
  simp only [truncMat]
  split_ifs
  · exact h c e
  · exact (show (fun _ : X => (1 : k)) = 1 from rfl) ▸ one_mem A
  · exact (show (fun _ : X => (0 : k)) = 0 from rfl) ▸ zero_mem A

theorem cellDisc_mem_regFns [Fintype ι] (b : Frames k V) : (fun g => cellDisc b g) ∈ regFns k V := by
  have : (fun g => cellDisc b g) = ∏ i, ∏ m : Fin (finrank k (V i) + 1),
      (fun g : Frames k V => (truncMat (m : ℕ) (frameMat b g i)).det) := by
    ext g
    simp [cellDisc, Finset.prod_apply]
  rw [this]
  exact Subalgebra.prod_mem _ fun i _ => Subalgebra.prod_mem _ fun m _ =>
    det_mem_subalgebra _ _ (truncMat_mem_subalgebra _ _ _ (frameMat_mem_regFns b i))

def fracAlg [Fintype ι] (b : Frames k V) : Subalgebra k (Frames k V → k) where
  carrier := {f | ∃ R ∈ regFns k V, ∃ K : ℕ, ∀ g, cellDisc b g ≠ 0 → f g * cellDisc b g ^ K = R g}
  mul_mem' := by
    rintro f₁ f₂ ⟨R₁, hR₁, K₁, h₁⟩ ⟨R₂, hR₂, K₂, h₂⟩
    refine ⟨R₁ * R₂, mul_mem hR₁ hR₂, K₁ + K₂, fun g hg => ?_⟩
    simp only [Pi.mul_apply, ← h₁ g hg, ← h₂ g hg]
    ring
  add_mem' := by
    rintro f₁ f₂ ⟨R₁, hR₁, K₁, h₁⟩ ⟨R₂, hR₂, K₂, h₂⟩
    have hD := cellDisc_mem_regFns b
    refine ⟨R₁ * (fun g => cellDisc b g) ^ K₂ + R₂ * (fun g => cellDisc b g) ^ K₁,
      add_mem (mul_mem hR₁ (pow_mem hD _)) (mul_mem hR₂ (pow_mem hD _)), K₁ + K₂, fun g hg => ?_⟩
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, ← h₁ g hg, ← h₂ g hg]
    ring
  algebraMap_mem' := fun r =>
    ⟨algebraMap k _ r, Subalgebra.algebraMap_mem _ r, 0, fun g _ => by simp⟩


example [Fintype ι] (b : Frames k V) : cellDisc b b = 1 := by
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun m _ => ?_
  have : truncMat (m : ℕ) (frameMat b b i) = 1 := by
    ext c e
    simp only [truncMat, frameMat, Basis.repr_self, Matrix.one_apply]
    by_cases h : e = c
    · subst h; simp
    · simp [Finsupp.single_apply, h, Ne.symm h]
  rw [this, Matrix.det_one]

end GlobalTheory.FlagPts
end
end

section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace Matrix

namespace GlobalTheory.FlagPts

theorem mem_span_tail_iff {W : Type} [AddCommGroup W] {k : Type} [Field k] [Module k W] {d : ℕ}
    (e : Basis (Fin d) k W) (m : ℕ) (v : W) :
    v ∈ Submodule.span k (e '' {a | m ≤ (a : ℕ)}) ↔ ∀ c : Fin d, (c : ℕ) < m → e.repr v c = 0 := by
  rw [Basis.mem_span_image]
  constructor
  · intro h c hc
    by_contra hne
    have := h (Finsupp.mem_support_iff.2 hne)
    simp only [Set.mem_setOf_eq] at this
    omega
  · intro h c hc
    simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hc
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    exact hc (h c (by omega))

theorem truncMat_mulVec_eq_zero_iff {R : Type} [CommRing R] {d : ℕ} (m : ℕ)
    (M : Matrix (Fin d) (Fin d) R) (y : Fin d → R) :
    truncMat m M *ᵥ y = 0 ↔
      (∀ e : Fin d, m ≤ (e : ℕ) → y e = 0) ∧ ∀ c : Fin d, (c : ℕ) < m → (M *ᵥ y) c = 0 := by
  have hlow (c : Fin d) (hc : (c : ℕ) < m) :
      (truncMat m M *ᵥ y) c = ∑ e : Fin d, (if (e : ℕ) < m then M c e else 0) * y e := by
    simp only [Matrix.mulVec, dotProduct, truncMat]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : (e : ℕ) < m
    · simp [hc, he]
    · have hce : c ≠ e := fun h => he (h ▸ hc)
      simp [he, hce]
  have hhigh (c : Fin d) (hc : ¬ (c : ℕ) < m) : (truncMat m M *ᵥ y) c = y c := by
    simp only [Matrix.mulVec, dotProduct, truncMat]
    rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro e _ hec
      simp [hc, Ne.symm hec]
    · simp
  have hsum (h : ∀ e : Fin d, m ≤ (e : ℕ) → y e = 0) (c : Fin d) :
      ∑ e : Fin d, (if (e : ℕ) < m then M c e else 0) * y e = (M *ᵥ y) c := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : (e : ℕ) < m
    · simp [he]
    · simp [he, h e (by omega)]
  constructor
  · intro h
    have h1 : ∀ e : Fin d, m ≤ (e : ℕ) → y e = 0 := fun e he => by
      rw [← hhigh e (by omega)]; exact congrFun h e
    refine ⟨h1, fun c hc => ?_⟩
    rw [← hsum h1 c, ← hlow c hc]
    exact congrFun h c
  · rintro ⟨h1, h2⟩
    funext c
    by_cases hc : (c : ℕ) < m
    · rw [hlow c hc, hsum h1 c]; exact h2 c hc
    · rw [hhigh c hc]; exact h1 c (by omega)

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem repr_eq_frameMat_mulVec (b g : Frames k V) (i : ι) (v : V i) (c : Fin (finrank k (V i))) :
    (b i).repr v c = (frameMat b g i *ᵥ (g i).equivFun v) c := by
  have h := congrArg (fun w => (b i).repr w c) ((g i).sum_equivFun v)
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, frameMat]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

theorem disjoint_step_iff_det_truncMat_ne_zero (b g : Frames k V) (i : ι) (m : ℕ) :
    Disjoint (g.flags.step i m) (Submodule.span k (b i '' {a | m ≤ (a : ℕ)})) ↔
      (truncMat m (frameMat b g i)).det ≠ 0 := by
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff, Submodule.disjoint_def]
  constructor
  · rintro h ⟨y, hy0, hy⟩
    apply hy0
    rw [truncMat_mulVec_eq_zero_iff] at hy
    have hv : (g i).equivFun ((g i).equivFun.symm y) = y := LinearEquiv.apply_symm_apply _ _
    have h0 := h ((g i).equivFun.symm y)
      (mem_step_flags.2 fun a ha => by rw [← Basis.equivFun_apply, hv]; exact hy.1 a ha)
      ((mem_span_tail_iff (b i) m _).2 fun c hc => by
        rw [repr_eq_frameMat_mulVec b g, hv]; exact hy.2 c hc)
    rw [← hv, h0, map_zero]
  · intro h v hv1 hv2
    by_contra hv
    refine h ⟨(g i).equivFun v, fun h0 => hv ((g i).equivFun.map_eq_zero_iff.1 h0), ?_⟩
    rw [truncMat_mulVec_eq_zero_iff]
    refine ⟨fun e he => ?_, fun c hc => ?_⟩
    · rw [Basis.equivFun_apply]; exact mem_step_flags.1 hv1 e he
    · rw [← repr_eq_frameMat_mulVec b g]; exact (mem_span_tail_iff (b i) m v).1 hv2 c hc

theorem mem_bigCell_iff_cellDisc_ne_zero (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (b g : Frames k V) : g.flags ∈ bigCell b ↔ cellDisc b g ≠ 0 := by
  simp only [bigCell, Set.mem_setOf_eq, disjoint_step_iff_det_truncMat_ne_zero, cellDisc,
    Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h i m
    exact h i m
  · intro h i m
    by_cases hm : m ≤ finrank k (V i)
    · exact h i ⟨m, by omega⟩
    · have heq : truncMat m (frameMat b g i) = truncMat (finrank k (V i)) (frameMat b g i) := by
        ext c e
        have hc := c.2
        have he := e.2
        simp only [truncMat]
        rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨hc, he⟩]
      rw [heq]
      exact h i ⟨finrank k (V i), by omega⟩

example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b g : Frames k V),
    g.flags ∈ bigCell b ↔ cellDisc b g ≠ 0 := mem_bigCell_iff_cellDisc_ne_zero

end GlobalTheory.FlagPts
end
end
