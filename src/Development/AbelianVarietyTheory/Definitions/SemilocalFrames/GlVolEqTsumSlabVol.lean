import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaussDensDefinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagBase.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def colM (x : Fin 3 → E) : Matrix (Fin 3) (Fin 1) E := Matrix.of fun a _ => x a

def lineFlag (E : Type) [Field E] [NumberField E] : Fin 2 → Submodule (𝓞 E) (Fin 3 → E) :=
  ![⊥, (intLat E 1).map ((Matrix.mulVecLin (colM (E := E) ![1, 1, 0])).restrictScalars (𝓞 E))]

theorem star_mem_int {x : E} (hx : x ∈ (algebraMap (𝓞 E) E).range) : star x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨s, hs⟩ := hx
  exact ⟨⟨star (s : E), s.2.map (starRingEnd E).toIntAlgHom⟩, by rw [← hs]; rfl⟩

theorem dual_intLat_one (u : Fin 1 → E) :
    (∀ t ∈ intLat E 1, star t ⬝ᵥ u ∈ (algebraMap (𝓞 E) E).range) ↔ u 0 ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro h
    have := h (fun _ => 1) ((mem_intLat _).2 fun _ => one_mem _)
    simpa [dotProduct] using this
  · intro h t ht
    have := mul_mem (star_mem_int ((mem_intLat _).1 ht 0)) h
    simpa [dotProduct] using this

theorem colM_gram (x y : Fin 3 → E) : (colM x)ᴴ * signMat E ![true, false, true] * colM y =
    Matrix.of fun _ _ => star (x 0) * y 0 - star (x 1) * y 1 + star (x 2) * y 2 := by
  ext a b
  rw [Matrix.mul_apply]
  simp [signMat, Matrix.mul_diagonal, colM, Fin.sum_univ_three, sub_eq_add_neg]

theorem colM_mulVec (x : Fin 3 → E) (u : Fin 1 → E) : colM x *ᵥ u = fun a => x a * u 0 := by
  funext a; simp [colM, Matrix.mulVec, dotProduct]

theorem isAdapted_rank_three (cm : Formalism.BasicNotions.CMData F E) :
    IsAdapted (ofSigns cm ![true, false, true]) (ofSigns cm ![true]) (RingEquiv.refl E) 1 (a := 1) (fun _ => 1)
      (lineFlag E) (fun _ => intLat E 1) 1 (fun _ => colM (E := E) ![1, 1, 0]) (fun _ => colM (E := E) ![0, -1, 1])
      (colM (E := E) ![1, 1, -1]) := by
  unfold IsAdapted
  rw [GlobalTheory.GaussMean.Test.lamX_one, GlobalTheory.GaussMean.Test.lamX_one]
  refine ⟨fun _ => rfl, rfl, fun _ => (⟨intLat_fg 1, intLat_span 1⟩ : Submodule.IsLattice E (intLat E 1)), fun i k => ⟨?_, ?_, fun h => absurd (Subsingleton.elim _ _) h⟩,
    fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have h : (colM (E := E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, 0] = 0 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![0, -1, 1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![0, -1, 1] = 0 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![0, -1, 1] = 1 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = 0 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![0, -1, 1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = 0 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![1, 1, -1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = (signMat E ![true]).map (RingEquiv.refl E) := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · show ∀ z : Fin 3 → E, z ∈ intLat E 3 ↔ ∃ (u u' : Fin 1 → Fin 1 → E) (y : Fin 1 → E), (∀ i, u i ∈ intLat E 1) ∧
      (∀ i, ∀ t ∈ intLat E 1, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 E) E).range) ∧ y ∈ intLat E 1 ∧
      z = ∑ i, colM (E := E) ![1, 1, 0] *ᵥ u i + ∑ i, colM (E := E) ![0, -1, 1] *ᵥ u' i + colM (E := E) ![1, 1, -1] *ᵥ y
    intro z
    simp only [dual_intLat_one]
    simp only [mem_intLat, colM_mulVec, Fin.sum_univ_one]
    constructor
    · intro h
      refine ⟨fun _ _ => z 1 + z 2, fun _ _ => z 0 - z 1, fun _ => z 0 - z 1 - z 2, fun _ _ => add_mem (h 1) (h 2),
        fun _ => sub_mem (h 0) (h 1), fun _ => sub_mem (sub_mem (h 0) (h 1)) (h 2), ?_⟩
      funext a; fin_cases a <;> simp <;> ring
    · rintro ⟨u, u', y, hu, hu', hy, rfl⟩ a
      fin_cases a
      · simpa using add_mem (hu 0 0) (hy 0)
      · simpa using add_mem (add_mem (hu 0 0) (neg_mem (hu' 0))) (hy 0)
      · simpa using add_mem (hu' 0) (neg_mem (hy 0))
  · show ∀ (k : Fin 2) (z : Fin 3 → E), z ∈ lineFlag E k ↔ ∃ u : Fin 1 → Fin 1 → E, (∀ i, u i ∈ intLat E 1) ∧
      (∀ i : Fin 1, ¬ i.castSucc < k → u i = 0) ∧ z = ∑ i, colM (E := E) ![1, 1, 0] *ᵥ u i
    intro k z
    fin_cases k
    · simp only [lineFlag, Fin.sum_univ_one]
      constructor
      · intro h
        exact ⟨0, fun _ => zero_mem _, fun _ _ => rfl, by simpa using h⟩
      · rintro ⟨u, -, h, rfl⟩
        simp [h 0 (by simp)]
    · simp only [lineFlag, Fin.sum_univ_one]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨fun _ => u, fun _ => hu, fun i hi => absurd (by fin_cases i; simp) hi, rfl⟩
      · rintro ⟨u, hu, -, rfl⟩
        exact ⟨u 0, hu 0, rfl⟩

theorem exists_isAdapted : ∃ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf)
    (S : Fin 2 → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ _ : Fin 1, Submodule (𝓞 I.E) (Fin 1 → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ _ : Fin 1, Matrix (Fin I.n) (Fin 1) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E),
    I.n = 3 ∧ I₀.n = 1 ∧ IsAdapted I I₀ e xf (a := 1) (fun _ => 1) S Λ x₀ T T' T₀ := by
  obtain ⟨I, -⟩ := exists_signature 0 0
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, isAdapted_rank_three I.cm⟩




open MeasureTheory NumberField Matrix Finset in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in

theorem _root_.GlobalTheory.FlagBase.Test.latAt_aut_mul (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) {γ : _root_.GlobalTheory.FlagMeas.MatInf E j}
    (hγ : γ ∈ _root_.GlobalTheory.FlagMeas.autGL E j Λ) (g : _root_.GlobalTheory.FlagMeas.MatInf E j) :
    _root_.GlobalTheory.FlagBase.latAt E j Λ (γ * g) = _root_.GlobalTheory.FlagBase.latAt E j Λ g := by
  obtain ⟨γ', hγΛ, hγ'⟩ := hγ
  have hγw : ∀ w : InfinitePlace E,
      Matrix.of (γ w) = (γ' : Matrix (Fin j) (Fin j) E).map w.embedding := fun w => by
    ext a b
    simp [hγ' w a b]
  have hinv : ∀ w : InfinitePlace E, (Matrix.of (γ w))⁻¹ =
      ((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).map w.embedding := fun w => by
    rw [hγw]
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp
  have key : ∀ (w : InfinitePlace E) (y : Fin j → E),
      (Matrix.of ((γ * g) w))⁻¹ *ᵥ (fun a => w.embedding (y a)) =
        (Matrix.of (g w))⁻¹ *ᵥ
          (fun a => w.embedding ((((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y) a)) := by
    intro w y
    rw [_root_.GlobalTheory.OrbitTerm.of_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    congr 1
    funext a
    exact (RingHom.map_mulVec w.embedding _ y a).symm
  unfold _root_.GlobalTheory.FlagBase.latAt
  congr 1
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y, ?_, ?_⟩
    · rw [← hγΛ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
      exact hy
    · funext w
      exact (key w y).symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(γ' : Matrix (Fin j) (Fin j) E) *ᵥ z, (hγΛ z).mpr hz, ?_⟩
    funext w
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

end GlobalTheory.FlagBase.Test
