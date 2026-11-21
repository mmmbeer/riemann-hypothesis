import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible

open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.SW.Model

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_cc (x : E) : cc (cc x) = x := by simp [cc]

theorem cc_integral {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)

omit [IsCMField E] in
theorem mem_stdL {m : ℕ} (x : Fin m → E) : x ∈ stdL E m ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      by_cases h : a = b
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx =>
      intro a
      have : (c • x) a = (c : E) * x a := rfl
      rw [this]; exact c.isIntegral_coe.mul (hx a)
  · intro hx
    have : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin m → E) := by
      ext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · change x b = x b * (Pi.single b (1 : E) : Fin m → E) b
        simp
      · intro a _ h
        change x a * (Pi.single a (1 : E) : Fin m → E) b = 0
        simp [Pi.single_apply, Ne.symm h]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem herm_one {m : ℕ} (x y : Fin m → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  unfold herm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a] <;> simp +contextual [Matrix.one_apply, eq_comm]

theorem stdL_mem_Vset (n M : ℕ) : stdL E n ∈ Vset E n M := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩,
    1, one_pos, Nat.coprime_one_left M, by simp, by simp⟩
  · rw [herm_one]
    rw [mem_stdL] at hx hy
    exact IsIntegral.sum _ fun a _ => (hx a).mul (cc_integral (hy a))
  · rw [mem_stdL]
    intro a
    have := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [herm_one, Finset.sum_eq_single a] at this
    · simpa [cc] using this
    · intro b _ hb; simp [Pi.single_apply, hb, cc]
    · simp

theorem one_mem_DH (n M : ℕ) : (1 : Matrix (Fin n) (Fin n) E) ∈ DH E n M := by
  refine ⟨?_, 1, one_pos, Nat.coprime_one_left M, 0, fun _ _ => isIntegral_zero, by simp⟩
  have : ccT (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
  rw [this, one_mul]

omit [IsCMField E] in
theorem nat_smul_mem {m : ℕ} (Λ : Lt E m) (s : ℕ) {v : Fin m → E} (hv : v ∈ Λ) :
    (s : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact Λ.toAddSubgroup.nsmul_mem hv s

omit [IsCMField E] in
theorem mem_of_coprime {m : ℕ} (Λ : Lt E m) {s R : ℕ} (h : s.Coprime R) {v : Fin m → E}
    (h1 : (s : E) • v ∈ Λ) (h2 : (R : E) • v ∈ Λ) : v ∈ Λ := by
  have hc : IsCoprime (s : ℤ) (R : ℤ) := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨a, b, hab⟩ := hc
  have e : v = a • ((s : E) • v) + b • ((R : E) • v) := by
    rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]
    have : (a : E) * s + b * R = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → E) hab
    rw [this, one_smul]
  rw [e]
  exact Λ.add_mem (Λ.toAddSubgroup.zsmul_mem h1 a) (Λ.toAddSubgroup.zsmul_mem h2 b)

open Classical in

def indFam (E : Type) [Field E] [NumberField E] (n N : ℕ) : Fam E n N := fun Λ x =>
  if ColsIn Λ x then 1 else 0



theorem I_mem_Hn (Ψ : Finset (E →+* ℂ)) (N : ℕ) :
    (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) : CM Ψ N N) ∈ Hn Ψ N := by
  intro τ
  have : imH (I • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 := by
    unfold imH
    rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul]
    have : (2 * I)⁻¹ * (I - star I) = 1 := by
      have : star I = -I := conj_I
      rw [this]; field_simp; ring
    rw [this, one_smul]
  simpa [this] using Matrix.PosDef.one

theorem ccT_J (N : ℕ) : ccT (Matrix.J (Fin N) E) = -Matrix.J (Fin N) E := by
  have : (Matrix.J (Fin N) E).map cc = Matrix.J (Fin N) E := by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [Matrix.J, cc, Matrix.one_apply, h]
  rw [ccT, this, Matrix.J_transpose]


theorem one_mem_UU (N : ℕ) : (1 : M2 E N) ∈ UU E N := by
  change ccT _ * _ * _ = _
  have : ccT (1 : M2 E N) = 1 := by
    ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
  rw [this]; simp

omit [IsCMField E] in

theorem expo_ofQ (Ψ : Finset (E →+* ℂ)) {n N : ℕ} (m : Matrix (Fin n) (QI E N) ℚ) (Z : CM Ψ N N)
    (z z' : CM Ψ n N) :
    ∑ k, (qv (m k) ⬝ᵥ tauOf Ψ Z *ᵥ qv (m k) + 2 * (qv (m k) ⬝ᵥ zetaOf Ψ z z' k)) =
      2 * expo Ψ (ofQ m) Z z z' := by
  unfold expo
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set e : Ψ → Fin (Module.finrank ℚ E) → ℂ := fun τ j => τ.1 (Module.finBasis ℚ E j) with he
  have hx : ∀ (τ : Ψ) a, τ.1 (ofQ m k a) = ∑ j, (m k (a, j) : ℂ) * e τ j := fun τ a => by
    simp [ofQ, he, Rat.smul_def]
  have hq : ∀ τ : Ψ, (fun a => τ.1 (ofQ m k a)) ⬝ᵥ Z τ *ᵥ (fun a => conj (τ.1 (ofQ m k a))) =
      ∑ p : QI E N, ∑ q : QI E N, (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
    intro τ
    simp only [hx, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum, map_ratCast]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have hl : ∀ τ : Ψ, (fun a => τ.1 (ofQ m k a)) ⬝ᵥ z τ k + z' τ k ⬝ᵥ (fun a => conj (τ.1 (ofQ m k a))) =
      ∑ p : QI E N, (m k p : ℂ) * (e τ p.2 * z τ k p.1 + z' τ k p.1 * conj (e τ p.2)) := by
    intro τ
    simp only [hx, dotProduct, Fintype.sum_prod_type, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum, map_ratCast, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [add_assoc, hq, hl]
  have h1 : qv (m k) ⬝ᵥ tauOf Ψ Z *ᵥ qv (m k) = 2 * ∑ τ : Ψ, ∑ p : QI E N, ∑ q : QI E N,
      (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
    have s1 : ∑ τ : Ψ, ∑ p : QI E N, ∑ q : QI E N,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) =
        ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    have s2 : ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) =
        ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ q.2 * Z τ q.1 p.1 * conj (e τ p.2) * m k q) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
    rw [two_mul, s1]
    nth_rewrite 2 [s2]
    simp only [dotProduct, Matrix.mulVec, tauOf, qv, Matrix.of_apply, Finset.sum_mul,
      Finset.mul_sum, add_mul, mul_add, Finset.sum_add_distrib, he]
  have h2 : qv (m k) ⬝ᵥ zetaOf Ψ z z' k = ∑ τ : Ψ, ∑ p : QI E N,
      (m k p : ℂ) * (e τ p.2 * z τ k p.1 + z' τ k p.1 * conj (e τ p.2)) := by
    simp only [dotProduct, zetaOf, qv, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h1, h2, Finset.sum_add_distrib]
  ring



open Classical in

def divFam (E : Type) [Field E] [NumberField E] (n N R : ℕ) : Fam E n N := fun Λ x =>
  if ColsIn Λ ((R : E) • x) then 1 else 0



theorem exists_isType : ∃ Ψ : Finset (E →+* ℂ), IsType Ψ ∧ Ψ.Nonempty := by
  classical
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => (InfinitePlace.mk τ).embedding = τ
  have hT : IsType Ψ := by
    intro τ
    have hne : ComplexEmbedding.conjugate τ ≠ τ := IsTotallyComplex.complexEmbedding_not_isReal τ
    simp only [Ψ, Finset.mem_filter, Finset.mem_univ, true_and, InfinitePlace.mk_conjugate_eq]
    rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.mk_embedding (InfinitePlace.mk τ)) with h | h
    · rw [h]; simp [hne.symm]
    · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ := by
        rw [← h]; ext x; simp
      rw [h2]; simp [hne]
  refine ⟨Ψ, hT, ?_⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ Ψ
  · exact ⟨τ, h⟩
  · exact ⟨_, by simpa [h] using (hT τ).not⟩



omit [IsCMField E] in

theorem twist_indFam_zero {n N R : ℕ} (Λ : Lt E n) :
    twist R (stdL E N) (indFam E n N) Λ 0 = 1 := by
  have h : (∀ ξ ∈ stdL E N, (R : E) • ((0 : Matrix (Fin n) (Fin N) E) *ᵥ ξ) ∈ Λ) ∧
      ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ stdL E N, (s : E) • v ∈ stdL E N :=
    ⟨fun _ _ => by simp, 1, Nat.ModEq.refl 1, by simp⟩
  unfold twist
  rw [dif_pos h, smul_zero]
  exact if_pos fun _ => Λ.zero_mem


end

end GlobalTheory.SW.Model
