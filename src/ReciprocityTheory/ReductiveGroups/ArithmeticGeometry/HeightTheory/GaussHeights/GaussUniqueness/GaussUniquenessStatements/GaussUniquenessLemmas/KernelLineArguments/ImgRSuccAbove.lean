import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtLeafSt

section
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem mem_vRing_iff {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) (x : Ω) :
    x ∈ vRing v ↔ 0 ≤ v x := by
  rfl

theorem pos_of_not_isUnit {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ))
    (x : vRing v) (hx : ¬ IsUnit x) : 0 < v (x : Ω) := by
  have h0 : 0 ≤ v (x : Ω) := x.2
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hx0 : (x : Ω) ≠ 0 := by
      intro h'
      rw [h', AddValuation.map_zero] at h
      exact WithTop.top_ne_zero h.symm
    have hinv : (x : Ω)⁻¹ ∈ vRing v := by
      show 0 ≤ v ((x : Ω)⁻¹)
      rw [AddValuation.map_inv, ← h, neg_zero]
    exact ⟨⟨x, ⟨(x : Ω)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem ratio_eq_of {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  unfold ratio
  have hex : ∃ a : Ω, f = a • g := ⟨a, h⟩
  rw [dif_pos hex]
  have h2 := hex.choose_spec
  exact smul_left_injective Ω hg (h.symm.trans h2).symm

theorem exists_smul_of_line {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    {l : Submodule Ω V} (h1 : Module.finrank Ω l = 1) {f g : V} (hf : f ∈ l) (hg : g ∈ l)
    (hg0 : g ≠ 0) : ∃ a : Ω, f = a • g := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hg⟩ : l) (by simpa using hg0)).mp h1 ⟨f, hf⟩
  refine ⟨c, ?_⟩
  have h2 := congrArg Subtype.val hc
  simpa using h2.symm

theorem eq_of_le_ht {R : Type*} [CommRing R] [IsDomain R] {Q P : Ideal R} [Q.IsPrime]
    [P.IsPrime] (hP : P.height = 1) (hQ : Q ≠ ⊥) (hle : Q ≤ P) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hle hne
  have hP1 : P.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hP]; rfl
  have h1 : Q.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp hP1) Q inferInstance hlt
  have h2 : Q.height = 0 := ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast h1)
  have hmin := Ideal.height_eq_zero_iff.mp h2
  have hbot : Q ≤ ⊥ := hmin.2 ⟨Ideal.bot_prime, le_refl _⟩ bot_le
  exact hQ (le_bot_iff.mp hbot)

theorem sac_same {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α) :
    Fin.succAboveCases (α := fun _ => α) i x f i = x := Fin.insertNth_apply_same (α := fun _ => α) i x f

theorem sac_succAbove {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α)
    (k : Fin n) : Fin.succAboveCases (α := fun _ => α) i x f (i.succAbove k) = f k := Fin.insertNth_apply_succAbove (α := fun _ => α) i x f k

end GaussValuationUniqueness
end

section
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

noncomputable def imgR {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (p : TVar D N) : MvPolynomial (SVar D N) R :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) R) j0
    (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (ρ k))
    (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2

theorem imgR_same {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (i : Fin (D + 1)) : imgR (D := D) j0 ρ (i, j0) = if i = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (ρ k) := by
  unfold imgR
  exact sac_same j0 _ _

theorem imgR_succAbove {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (i : Fin (D + 1)) (k : Fin N) :
    imgR (D := D) j0 ρ (i, j0.succAbove k) = MvPolynomial.X (Sum.inr (i, k)) := by
  unfold imgR
  exact sac_succAbove j0 _ _ k

theorem imgR_map {R R' : Type*} [CommRing R] [CommRing R'] {D N : ℕ} (φ : R →+* R')
    (j0 : Fin (N + 1)) (ρ : Fin N → R) (t : TVar D N) :
    MvPolynomial.map φ (imgR j0 ρ t) = imgR j0 (fun k => φ (ρ k)) t := by
  obtain ⟨i, j⟩ := t
  rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
  · rw [imgR_same, imgR_same]
    split_ifs
    · exact MvPolynomial.map_X φ _
    · simp only [map_neg, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  · rw [imgR_succAbove, imgR_succAbove, MvPolynomial.map_X]

section Ker

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem alg_mem (hv : IsTrivOn K v) (x : K) : algebraMap K Ω x ∈ vRing v := by
  rw [mem_vRing_iff]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [hv x hx]

noncomputable def kap (hv : IsTrivOn K v) : K →+* vRing v :=
  (algebraMap K Ω).codRestrict (vRing v) (alg_mem v hv)

noncomputable def psiT (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (ρ : Fin N → vRing v) :
    MvPolynomial (TVar D N) K →+* MvPolynomial (SVar D N) (vRing v) :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C : vRing v →+* MvPolynomial (SVar D N) (vRing v)).comp
    (kap v hv)) (imgR j0 ρ)

noncomputable def psiR (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (ρ : Fin N → vRing v) :
    MvPolynomial (TVar D N) K →+* MvPolynomial (SVar D N) (IsLocalRing.ResidueField (vRing v)) :=
  (MvPolynomial.map (IsLocalRing.residue (vRing v))).comp (psiT (D := D) v hv j0 ρ)

theorem pos_of_ker {w : AddValuation (OmS Ω D N) (WithTop ℤ)}
    (hw : ∀ a : Ω, w (algebraMap Ω (OmS Ω D N) a) = v a)
    (e : SVar D N → OmS Ω D N) (he : ∀ s, 0 ≤ w (e s))
    (q : MvPolynomial (SVar D N) (vRing v))
    (hq : MvPolynomial.map (IsLocalRing.residue (vRing v)) q = 0) :
    0 < w (MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) e q) := by
  rw [MvPolynomial.eval₂_eq]
  refine Finset.sum_induction _ (fun x => 0 < w x)
    (fun a b ha hb => lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add w a b)) (by simp) ?_
  intro d _
  have hprod : 0 ≤ w (∏ s ∈ d.support, e s ^ d s) :=
    Finset.prod_induction _ (fun x => 0 ≤ w x)
      (fun a b ha hb => by rw [AddValuation.map_mul]; exact add_nonneg ha hb)
      (le_of_eq (AddValuation.map_one w).symm)
      (fun s _ => by rw [AddValuation.map_pow]; exact nsmul_nonneg (he s) _)
  have hnu : ¬ IsUnit (q.coeff d) := by
    have h0 := congrArg (MvPolynomial.coeff d) hq
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h0
    exact (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)
  have hc : 0 < w (((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) (q.coeff d)) := by
    rw [RingHom.comp_apply, hw]
    exact pos_of_not_isUnit v _ hnu
  rw [AddValuation.map_mul]
  exact lt_of_lt_of_le hc (le_add_of_nonneg_right hprod)

end Ker

end GaussValuationUniqueness
end
