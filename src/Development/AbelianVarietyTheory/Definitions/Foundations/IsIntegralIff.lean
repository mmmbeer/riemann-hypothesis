import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HermitianLattices

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.HL.Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_add_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a + b) y = hf L H a y + hf L H b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a - b) y = hf L H a y - hf L H b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H (c • a) y = c * hf L H a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H y (a + b) = hf L H y a + hf L H y b := by
  simp [hf, map_add, mul_add, Finset.sum_add_distrib]

theorem hf_sub_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H y (a - b) = hf L H y a - hf L H y b := by
  simp [hf, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem hf_smul_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H y (c • a) = L.cj c * hf L H y a := by
  unfold hf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hf_symm (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x y : Fin n → E) : hf L H y x = L.cj (hf L H x y) := by
  have hH : ∀ i j, L.cj (H j i) = H i j := fun i j => congrFun (congrFun h i) j
  unfold hf
  simp only [map_sum, map_mul, L.cj_cj, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eich_isom (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x u : Fin n → E) (s : E) (hxx : hf L H x x = 0) (hux : hf L H u x = 0)
    (hs : s + L.cj s = hf L H u u) (v w : Fin n → E) :
    hf L H (eich L H x u s v) (eich L H x u s w) = hf L H v w := by
  have hxu : hf L H x u = 0 := by rw [hf_symm L h u x, hux, map_zero]
  have hxw : hf L H x w = L.cj (hf L H w x) := hf_symm L h w x
  have huw : hf L H u w = L.cj (hf L H w u) := hf_symm L h w u
  simp only [eich, hf_add_left, hf_sub_left, hf_smul_left, hf_add_right, hf_sub_right,
    hf_smul_right, hxx, hux, hxu, hxw, huw]
  linear_combination (-(hf L H v x * L.cj (hf L H w x))) * hs

theorem isHermND_one (L : LocE F E) (n : ℕ) : IsHermND L (1 : Matrix (Fin n) (Fin n) E) := by
  refine ⟨?_, by simp⟩
  ext i j
  show L.cj ((1 : Matrix (Fin n) (Fin n) E) j i) = (1 : Matrix (Fin n) (Fin n) E) i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

def stdLat (L : LocE F E) (n : ℕ) : Submodule L.O (Fin n → E) :=
  Submodule.span L.O (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E))




theorem nontrivial (L : LocE F E) : Nontrivial E := by
  exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)




theorem lead_zero {N : ℕ} (Z : Matrix (Fin N) (Fin N) E) : lead Z 0 = 1 := by
  unfold lead
  have : IsEmpty (Fin ((0 : Fin (N + 1)) : ℕ)) := ⟨fun i => absurd i.2 (by simp)⟩
  exact Matrix.det_isEmpty


theorem lead_one {N : ℕ} (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) E) :
    lead Z ⟨1, by omega⟩ = Z 0 0 := by
  rw [lead, Matrix.det_fin_one]
  rfl

theorem algebraMap_mem_iff (L : LocE F E) (a : F) : algebraMap F E a ∈ L.O ↔ a ∈ 𝒪[F] := by
  have := nontrivial L
  rw [L.O_def, isIntegral_algebraMap_iff (algebraMap F E).injective]
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    exact isIntegral_algebraMap (x := (⟨a, h⟩ : 𝒪[F]))

theorem vE_pow (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (u : 𝒪[F]ˣ) (k : ℤ) :
    vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by
  have hϖ0 : (ϖ : F) ≠ 0 := fun e => hϖ.ne_zero (Subtype.ext e)
  have := nontrivial L
  unfold vE
  apply IsGreatest.csSup_eq
  refine ⟨⟨algebraMap F E ((u : 𝒪[F]) : F), (algebraMap_mem_iff L _).mpr (u : 𝒪[F]).2, by
    rw [map_mul]⟩, ?_⟩
  rintro m ⟨y, hy, he⟩
  by_contra hlt
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m = k + ((j + 1 : ℕ) : ℤ) := ⟨(m - k - 1).toNat, by omega⟩
  have h1 : algebraMap F E ((ϖ : F) ^ m)⁻¹ * algebraMap F E ((ϖ : F) ^ m) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0), map_one]
  have hy' : y = algebraMap F E (((ϖ : F) ^ (j + 1))⁻¹ * ((u : 𝒪[F]) : F)) := by
    calc y = algebraMap F E ((ϖ : F) ^ m)⁻¹ * (algebraMap F E ((ϖ : F) ^ m) * y) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [← he, ← map_mul]
          congr 1
          rw [hj, zpow_add₀ hϖ0, zpow_natCast]
          field_simp
  have hz : ((ϖ : F) ^ (j + 1))⁻¹ * ((u : 𝒪[F]) : F) ∈ 𝒪[F] :=
    (algebraMap_mem_iff L _).mp (hy' ▸ hy)
  have hu : ϖ ^ (j + 1) * (⟨_, hz⟩ : 𝒪[F]) = (u : 𝒪[F]) := by
    apply Subtype.ext
    push_cast
    field_simp
  have hunit : IsUnit (ϖ ^ (j + 1)) := isUnit_of_mul_isUnit_left (hu ▸ u.isUnit)
  exact hϖ.not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero j)).mp hunit)

theorem exists_char (a : F) (ha : a ∉ 𝒪[F]) :
    ∃ ψ : AddChar F ℂ, (∀ y ∈ 𝒪[F], ψ y = 1) ∧ ψ a ≠ 1 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero
    (A := F ⧸ (𝒪[F]).toAddSubgroup) (a := (a : F ⧸ (𝒪[F]).toAddSubgroup))
    (by rw [ne_eq, QuotientAddGroup.eq_zero_iff]; exact ha)
  let ι : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      intro q hq
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simp⟩)
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      change (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at hx
      obtain ⟨k, hk⟩ := hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
      refine ⟨k, ?_⟩
      have hk' : ((k : ℚ) : ℝ) = (q : ℝ) := by simpa using hk
      simpa using (Rat.cast_injective hk')
  refine ⟨{ toFun := fun x => ((AddCircle.toCircle (ι (c (x : F ⧸ (𝒪[F]).toAddSubgroup))) : Circle) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [AddCircle.toCircle_add] }, ?_, ?_⟩
  · intro y hy
    have hy0 : (y : F ⧸ (𝒪[F]).toAddSubgroup) = 0 := (QuotientAddGroup.eq_zero_iff y).mpr hy
    simp [hy0]
  · intro h
    apply hc
    apply hι
    apply AddCircle.injective_toCircle one_ne_zero
    rw [map_zero, AddCircle.toCircle_zero]
    exact Circle.ext (by simpa using h)

theorem isIntegral_iff (a : F) : IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    exact isIntegral_algebraMap (x := (⟨a, h⟩ : 𝒪[F]))




end GlobalTheory.HL.Model
