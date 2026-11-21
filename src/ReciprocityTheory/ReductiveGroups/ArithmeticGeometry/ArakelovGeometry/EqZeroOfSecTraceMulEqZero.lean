import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisFurther

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem fnField_comp_le' (x : κ → Ω) (e : Fin (D + 1) → κ) : fnField (x ∘ e) ≤ fnField x := by
  unfold fnField
  rw [IntermediateField.adjoin_le_iff]
  rintro t ⟨i, j, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨e i, e j, rfl⟩

theorem coord_ne_zero {o : Type*} [CommRing o] [Algebra o Ω] [Nontrivial o] {ι : Type*}
    (y : ι → Ω) (h : coordIdeal o y = ⊥) (k : ι) : y k ≠ 0 := by
  intro hk
  have : (MvPolynomial.X k : MvPolynomial ι o) ∈ coordIdeal o y := by
    simp [coordIdeal, coneMap, RingHom.mem_ker, hk]
  rw [h, Ideal.mem_bot] at this
  exact MvPolynomial.X_ne_zero k this

theorem aeval_mem_subring {o σ : Type*} [CommRing o] [Algebra o Ω] (F : Subring Ω)
    (hc : ∀ a : o, algebraMap o Ω a ∈ F) (v : σ → Ω) (hv : ∀ k, v k ∈ F)
    (f : MvPolynomial σ o) : MvPolynomial.aeval v f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hc a
  | add p q hp hq => simpa using F.add_mem hp hq
  | mul_X p k hp => simpa using F.mul_mem hp (hv k)

theorem aeval_mem_field {o σ : Type*} [CommRing o] [Algebra o Ω] (F : IntermediateField ℚ Ω)
    (hc : ∀ a : o, algebraMap o Ω a ∈ F) (v : σ → Ω) (hv : ∀ k, v k ∈ F)
    (f : MvPolynomial σ o) : MvPolynomial.aeval v f ∈ F :=
  aeval_mem_subring F.toSubfield.toSubring hc v hv f

theorem div_mem_fnField (x : κ → Ω) (i j : κ) : x i / x j ∈ fnField x :=
  IntermediateField.subset_adjoin _ _ ⟨i, j, rfl⟩

theorem div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) (i : κ) :
    IsIntegral (fnField (x ∘ e)) (x i / x (e 0)) := by
  set y := x ∘ e with hy
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (y 0)⁻¹
  change IsIntegral _ (x i / y 0)
  have hev : ∀ f : MvPolynomial (Fin (D + 1)) ℚ,
      ψ (coneMap ℚ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]; simp [coneMap, ψ]
  have hmem : ∀ r : coneRing ℚ y, ψ r ∈ fnField y := by
    intro r
    obtain ⟨f, hf⟩ := r.2
    rw [← hf]
    change ψ (coneMap ℚ y f) ∈ _
    rw [hev]
    refine aeval_mem_field _ (fun a => IntermediateField.algebraMap_mem _ a) _ (fun k => ?_) f
    simpa [div_eq_mul_inv] using div_mem_fnField y k 0
  let φ : coneRing ℚ y →+* fnField y :=
    (ψ.comp (coneRing ℚ y).val.toRingHom).codRestrict (fnField y).toSubfield.toSubring hmem
  have := IsIntegral.map_of_comp_eq φ ψ (by ext r; rfl) (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this

theorem projective_frame_coord_ne_zero (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) : x (e 0) ≠ 0 :=
  coord_ne_zero (x ∘ e) h.free 0

theorem mem_sec_iff {o : Type*} [CommRing o] [Algebra o Ω] {ι : Type*} (x : ι → Ω) (d : ℕ) (s : Ω) :
    s ∈ sec o x d ↔ ∃ f : MvPolynomial ι o, f.IsHomogeneous d ∧ MvPolynomial.aeval x f = s := by
  simp [sec, Submodule.mem_map, MvPolynomial.mem_homogeneousSubmodule]

theorem mul_mem_sec {o : Type*} [CommRing o] [Algebra o Ω] {ι : Type*} (x : ι → Ω) {d d' : ℕ}
    {s t : Ω} (hs : s ∈ sec o x d) (ht : t ∈ sec o x d') : s * t ∈ sec o x (d + d') := by
  obtain ⟨f, hf, rfl⟩ := (mem_sec_iff x d s).1 hs
  obtain ⟨g, hg, rfl⟩ := (mem_sec_iff x d' t).1 ht
  exact (mem_sec_iff x _ _).2 ⟨f * g, hf.mul hg, by simp⟩

theorem aeval_smul_homog {o ι : Type*} [Fintype ι] [CommRing o] [Algebra o Ω]
    {f : MvPolynomial ι o} {d : ℕ} (hf : f.IsHomogeneous d) (c : Ω) (v : ι → Ω) :
    MvPolynomial.aeval (fun i => c * v i) f = c ^ d * MvPolynomial.aeval v f := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hf (MvPolynomial.mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem sec_div_mem [Fintype κ] (x : κ → Ω) (j : κ) {d : ℕ} {s : Ω}
    (hs : s ∈ sec ℤ x d) : s / x j ^ d ∈ fnField x := by
  obtain ⟨f, hf, rfl⟩ := (mem_sec_iff x d s).1 hs
  have : MvPolynomial.aeval x f / x j ^ d = MvPolynomial.aeval (fun i => (x j)⁻¹ * x i) f := by
    rw [aeval_smul_homog hf, inv_pow, div_eq_mul_inv, mul_comm]
  rw [this]
  refine aeval_mem_field _ (fun a => ?_) _ (fun i => ?_) f
  · simpa using IntermediateField.intCast_mem (fnField x) a
  · simpa [div_eq_inv_mul] using div_mem_fnField x i j

theorem fnField_eq_adjoin (x : κ → Ω) (e : Fin (D + 1) → κ) (hy0 : x (e 0) ≠ 0) :
    IntermediateField.extendScalars (fnField_comp_le' x e) =
      IntermediateField.adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  apply le_antisymm
  · rw [IntermediateField.extendScalars_le_iff]
    change IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j} ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro t ⟨i, j, rfl⟩
    have hi : x i / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0)) := IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    have hj : x j / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0)) := IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
    have : x i / x j = (x i / x (e 0)) / (x j / x (e 0)) := by
      rw [div_div_div_cancel_right₀ hy0]
    rw [this]
    exact div_mem hi hj
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact div_mem_fnField x i (e 0)

theorem finiteDimensional_ext [Finite κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  rw [fnField_eq_adjoin x e (projective_frame_coord_ne_zero x e h)]
  have : Finite (Set.range fun i => x i / x (e 0)) := Set.finite_range _ |>.to_subtype
  exact IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact div_isIntegral x e h i)

theorem projDeg_eq (x : κ → Ω) (e : Fin (D + 1) → κ) :
    projDeg x e = finrank (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) :=
  IntermediateField.relfinrank_eq_finrank_of_le _

theorem projDeg_pos' [Finite κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    0 < projDeg x e := by
  have := finiteDimensional_ext x e h
  rw [projDeg_eq]
  exact Module.finrank_pos

def dehom (l : Fin (D + 1)) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial {k // k ≠ l} ℤ :=
  MvPolynomial.aeval fun k => if h : k = l then 1 else MvPolynomial.X ⟨k, h⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem closure_mem (x : κ → Ω) (e : Fin (D + 1) → κ) (m : Ω)
    (hm : m ∈ Submonoid.closure (Set.range fun i => x i / x (e 0))) :
    ∃ d, ∃ s ∈ sec ℤ x d, m = s / x (e 0) ^ d := by
  induction hm using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨1, x i, ?_, by rw [pow_one]⟩
    unfold sec
    exact Submodule.mem_map.2 ⟨MvPolynomial.X i,
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X ℤ i), by simp⟩
  | one =>
    refine ⟨0, 1, ?_, by simp⟩
    unfold sec
    exact Submodule.mem_map.2 ⟨1,
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_one κ ℤ), by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨d1, s1, hs1, rfl⟩ := ha
    obtain ⟨d2, s2, hs2, rfl⟩ := hb
    unfold sec at hs1 hs2
    obtain ⟨p1, hp1, rfl⟩ := Submodule.mem_map.1 hs1
    obtain ⟨p2, hp2, rfl⟩ := Submodule.mem_map.1 hs2
    refine ⟨d1 + d2, (MvPolynomial.aeval x).toLinearMap (p1 * p2), ?_, ?_⟩
    · unfold sec
      exact Submodule.mem_map.2 ⟨p1 * p2, (MvPolynomial.mem_homogeneousSubmodule _ _).2
        (((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp1).mul
          ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp2)), rfl⟩
    · simp only [AlgHom.toLinearMap_apply, map_mul]
      rw [div_mul_div_comm, pow_add]

private theorem gens_lemma_2 [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    (∀ i, IsIntegral (fnField (x ∘ e)) (x i / x (e 0))) ∧
      IntermediateField.extendScalars (fnField_comp_le' x e) =
        IntermediateField.adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  classical
  have hne : x (e 0) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X 0 ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero 0 hk
  have hgen : ∀ k, x (e k) / x (e 0) ∈ fnField (x ∘ e) := fun k => div_mem_fnField (x ∘ e) k 0
  have hcone : ∀ q : MvPolynomial (Fin (D + 1)) ℚ,
      Polynomial.evalRingHom (x (e 0))⁻¹ (coneMap ℚ (x ∘ e) q) ∈ fnField (x ∘ e) := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      unfold coneMap
      rw [MvPolynomial.aeval_C]
      first
        | (rw [Polynomial.algebraMap_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
           exact IntermediateField.algebraMap_mem _ a)
        | simpa using IntermediateField.algebraMap_mem (fnField (x ∘ e)) a
    next p1 p2 h1 h2 =>
      rw [map_add, map_add]
      exact add_mem h1 h2
    next p1 k h1 =>
      rw [map_mul, map_mul]
      refine mul_mem h1 ?_
      unfold coneMap
      rw [MvPolynomial.aeval_X]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Function.comp_apply]
      rw [← div_eq_mul_inv]
      exact hgen k
  have hmem : ∀ v : coneRing ℚ (x ∘ e),
      ((Polynomial.evalRingHom (x (e 0))⁻¹).comp (coneRing ℚ (x ∘ e)).val.toRingHom) v ∈
        fnField (x ∘ e) := by
    rintro ⟨v, q, rfl⟩
    exact hcone q
  let φ : coneRing ℚ (x ∘ e) →+* fnField (x ∘ e) :=
    ((Polynomial.evalRingHom (x (e 0))⁻¹).comp (coneRing ℚ (x ∘ e)).val.toRingHom).codRestrict
      (fnField (x ∘ e)) hmem
  have hint : ∀ i, IsIntegral (fnField (x ∘ e)) (x i / x (e 0)) := by
    intro i
    obtain ⟨p, hm, hp⟩ := h.integral i
    refine ⟨p.map φ, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (fnField (x ∘ e)) Ω).comp φ =
        (Polynomial.evalRingHom (x (e 0))⁻¹).comp
          (algebraMap (coneRing ℚ (x ∘ e)) (Polynomial Ω)) := RingHom.ext fun _ => rfl
    have hpt : x i / x (e 0) =
        Polynomial.evalRingHom (x (e 0))⁻¹ (Polynomial.C (x i) * Polynomial.X) := by
      simp [div_eq_mul_inv]
    rw [hcomp, hpt, ← Polynomial.hom_eval₂, hp, map_zero]
  let S : Set Ω := Set.range fun i => x i / x (e 0)
  have heq : IntermediateField.extendScalars (fnField_comp_le' x e) =
      IntermediateField.adjoin (fnField (x ∘ e)) S := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ fnField x := (IntermediateField.mem_extendScalars _).1 hz
      have hle : IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j} ≤
          (IntermediateField.adjoin (fnField (x ∘ e)) S).restrictScalars ℚ := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨i, j, rfl⟩
        have h3 : x i / x j = x i / x (e 0) / (x j / x (e 0)) := by
          first
            | rw [div_div_div_cancel_right₀ hne]
            | field_simp
        show x i / x j ∈ IntermediateField.adjoin (fnField (x ∘ e)) S
        rw [h3]
        have hi : x i / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e)) S :=
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
        have hj : x j / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e)) S :=
          IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
        exact div_mem hi hj
      exact hle hz'
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact (IntermediateField.mem_extendScalars _).2 (div_mem_fnField x i (e 0))
  exact ⟨hint, heq⟩

private theorem finrat_lemma [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  obtain ⟨hint, heq⟩ := gens_lemma_2 x e h
  rw [heq]
  exact IntermediateField.finiteDimensional_adjoin fun z hz => by
    obtain ⟨i, rfl⟩ := hz
    exact hint i

theorem exists_indep_sections' [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ)
    (h : IsRatProjFrame x e) :
    ∃ (k : ℕ) (ε : Fin (projDeg x e) → Ω), (∀ l, ε l ∈ sec ℤ x k) ∧
      LinearIndependent (fnField (x ∘ e)) ε := by
  classical
  obtain ⟨hint, heq⟩ := gens_lemma_2 x e h
  haveI := finrat_lemma x e h
  have hne : x (e 0) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X 0 ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero 0 hk

  let T : Set Ω := Submonoid.closure (Set.range fun i => x i / x (e 0))
  have hTL : ∀ z ∈ T, z ∈ IntermediateField.extendScalars (fnField_comp_le' x e) := by
    intro z hz
    obtain ⟨d, σ, hσ, rfl⟩ := closure_mem x e z hz
    exact sec_div_mem x (e 0) hσ
  let s : Set (IntermediateField.extendScalars (fnField_comp_le' x e)) := {z | (z : Ω) ∈ T}
  have hspanΩ : ∀ z ∈ IntermediateField.extendScalars (fnField_comp_le' x e),
      z ∈ Submodule.span (fnField (x ∘ e)) T := by
    intro z hz
    rw [heq] at hz
    have h1 : z ∈ (IntermediateField.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0))).toSubalgebra := hz
    have hSi : ∀ w ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) w := by
      rintro w ⟨i, rfl⟩
      exact hint i
    first
      | rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun w hw => (hSi w hw).isAlgebraic)] at h1
      | rw [IntermediateField.adjoin_toSubalgebra_of_isIntegral hSi] at h1
      | rw [IntermediateField.adjoin_algebraic_toSubalgebra (fun w hw => (hSi w hw).isAlgebraic)] at h1
      | rw [IntermediateField.adjoin_integral_toSubalgebra hSi] at h1
    have h2 : z ∈ Subalgebra.toSubmodule (Algebra.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0))) := h1
    rwa [Algebra.adjoin_eq_span] at h2
  have hspan : Submodule.span (fnField (x ∘ e)) s = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have h1 := hspanΩ z z.2
    have h2 : Submodule.span (fnField (x ∘ e)) T = (Submodule.span (fnField (x ∘ e)) s).map
        (IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      ext w
      constructor
      · intro hw
        exact ⟨⟨w, hTL w hw⟩, hw, rfl⟩
      · rintro ⟨w', hw', rfl⟩
        exact hw'
    rw [h2] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    have hwz' : w = z := Subtype.ext hwz
    rwa [← hwz']
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (fnField (x ∘ e)) s
  have hbtop : ⊤ ≤ Submodule.span (fnField (x ∘ e))
      (Set.range (Subtype.val : b → IntermediateField.extendScalars (fnField_comp_le' x e))) := by
    first
      | rw [Subtype.range_coe, hbspan, hspan]
      | rw [Subtype.range_val, hbspan, hspan]
  let B := Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis B
  haveI : Fintype b := Fintype.ofFinite b
  have hpd : projDeg x e = Module.finrank (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
    unfold projDeg
    first
      | exact IntermediateField.relfinrank_eq_finrank_of_le (fnField_comp_le' x e)
      | rfl
  have hcard : Fintype.card b = projDeg x e := by
    rw [hpd, Module.finrank_eq_card_basis B]
  let eqv : Fin (projDeg x e) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hdec : ∀ j, ∃ d, ∃ σ ∈ sec ℤ x d, (((eqv j : b) : IntermediateField.extendScalars
      (fnField_comp_le' x e)) : Ω) = σ / x (e 0) ^ d :=
    fun j => closure_mem x e _ (hbs (eqv j).2)
  choose d σ hσ hdeq using hdec
  obtain ⟨k, hk⟩ : ∃ k, k = Finset.univ.sup d := ⟨_, rfl⟩
  have hdk : ∀ j, d j ≤ k := fun j => hk ▸ Finset.le_sup (Finset.mem_univ j)
  refine ⟨k, fun j => σ j * x (e 0) ^ (k - d j), fun j => ?_, ?_⟩
  · obtain ⟨p, hp, hps⟩ := Submodule.mem_map.1 (hσ j)
    refine Submodule.mem_map.2 ⟨p * MvPolynomial.X (e 0) ^ (k - d j), ?_, ?_⟩
    · have h3 := ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp).mul
        ((MvPolynomial.isHomogeneous_X ℤ (e 0)).pow (k - d j))
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa [Nat.add_sub_of_le (hdk j)] using h3
    · show (MvPolynomial.aeval x).toLinearMap (p * MvPolynomial.X (e 0) ^ (k - d j)) =
        σ j * x (e 0) ^ (k - d j)
      rw [← hps]
      simp
  · have hli1 : LinearIndependent (fnField (x ∘ e))
        (fun j => (((eqv j : b) : IntermediateField.extendScalars (fnField_comp_le' x e)) : Ω)) :=
      (hbli.comp eqv eqv.injective).map'
        (IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap
        (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    have hli2 := hli1.map' (LinearMap.mulRight (fnField (x ∘ e)) (x (e 0) ^ k))
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (pow_ne_zero k hne)))
    have hfun : (⇑(LinearMap.mulRight (fnField (x ∘ e)) (x (e 0) ^ k)) ∘
        fun j => (((eqv j : b) : IntermediateField.extendScalars (fnField_comp_le' x e)) : Ω)) =
        fun j => σ j * x (e 0) ^ (k - d j) := by
      funext j
      simp only [Function.comp_apply, LinearMap.mulRight_apply, hdeq j]
      have hk' : x (e 0) ^ k = x (e 0) ^ d j * x (e 0) ^ (k - d j) := by
        rw [← pow_add, Nat.add_sub_of_le (hdk j)]
      rw [hk']
      have hc := pow_ne_zero (d j) hne
      field_simp
      try ring
    rw [hfun] at hli2
    exact hli2

theorem eq_zero_of_trace [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε)
    (t : IntermediateField.extendScalars (fnField_comp_le' x e))
    (h0 : ∀ l, Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      (t * ⟨ε l / x (e 0) ^ k, sec_div_mem x (e 0) (hε l)⟩) = 0) : t = 0 := by
  classical
  haveI := finrat_lemma x e h
  have hne : x (e 0) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X 0 ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero 0 hk
  let b : Fin (projDeg x e) → IntermediateField.extendScalars (fnField_comp_le' x e) :=
    fun j => ⟨ε j / x (e 0) ^ k, sec_div_mem x (e 0) (hε j)⟩
  have hb : LinearIndependent (fnField (x ∘ e)) b := by
    apply LinearIndependent.of_comp (IntermediateField.val _).toLinearMap
    have h2 := hli.map' (LinearMap.mulRight (fnField (x ∘ e)) ((x (e 0) ^ k)⁻¹))
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (inv_ne_zero (pow_ne_zero k hne))))
    have h3 : (⇑(IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap ∘ b) =
        ⇑(LinearMap.mulRight (fnField (x ∘ e)) ((x (e 0) ^ k)⁻¹)) ∘ ε := by
      funext j
      exact div_eq_mul_inv _ _
    rw [h3]
    exact h2
  have hrank : Fintype.card (Fin (projDeg x e)) = Module.finrank (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
    rw [Fintype.card_fin]
    unfold projDeg
    first
      | exact IntermediateField.relfinrank_eq_finrank_of_le (fnField_comp_le' x e)
      | rfl
  haveI : Nonempty (Fin (projDeg x e)) := ⟨⟨0, by
    have h4 := hrank
    rw [Fintype.card_fin] at h4
    rw [h4]
    first
      | exact Module.finrank_pos
      | exact FiniteDimensional.finrank_pos⟩⟩
  obtain ⟨B, hB⟩ : ∃ B : Basis (Fin (projDeg x e)) (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)),
      ∀ j, B j = ⟨ε j / x (e 0) ^ k, sec_div_mem x (e 0) (hε j)⟩ :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hb hrank, fun j => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]⟩
  have hnd : (Algebra.traceForm (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))).Nondegenerate := by
    first
      | exact traceForm_nondegenerate _ _
      | exact Algebra.traceForm_nondegenerate _ _
  have key : ∀ n, Algebra.traceForm (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)) t n = 0 := by
    intro n
    rw [Algebra.traceForm_apply, ← B.sum_repr n, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, hB j, h0 j, smul_zero]
  first
    | exact hnd t key
    | exact hnd.1 t key
    | exact hnd.1.1 t key
    | (unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate LinearMap.SeparatingLeft at hnd
       exact hnd.1 t key)


def chartGen (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (k : {k // k ≠ l}) :
    fnField (x ∘ e) :=
  ⟨x (e k) / x (e l), div_mem_fnField (x ∘ e) k l⟩

def chartRing (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) : Subalgebra ℤ (fnField (x ∘ e)) :=
  Algebra.adjoin ℤ (Set.range (chartGen x e l))

theorem chartGen_indep (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : AlgebraicIndependent ℤ (chartGen x e l) := by
  classical
  have hne : x (e l) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X l ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [hfree, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero l hk

  have hdehom : ∀ (F : MvPolynomial (Fin (D + 1)) ℤ) (n : ℕ), F.IsHomogeneous n →
      MvPolynomial.aeval (fun i => (x ∘ e) i / x (e l)) F =
        MvPolynomial.aeval (x ∘ e) F / x (e l) ^ n := by
    intro F n hF
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hF (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [mul_div_assoc]
    congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]

  have hform : ∀ (F : MvPolynomial (Fin (D + 1)) ℤ) (n : ℕ), F.IsHomogeneous n →
      coneMap ℤ (x ∘ e) F = Polynomial.C (MvPolynomial.aeval (x ∘ e) F) * Polynomial.X ^ n := by
    intro F n hF
    unfold coneMap
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hF (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [← hdeg]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, eq_intCast, map_mul,
      map_prod, map_pow, map_intCast]
    ring
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  have hPΩ : MvPolynomial.aeval (fun k : {k // k ≠ l} => x (e k) / x (e l)) P = 0 := by
    have h1 := congrArg ((fnField (x ∘ e)).val.restrictScalars ℤ) hP
    rw [map_zero, ← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h1
    exact h1
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = MvPolynomial.rename (Subtype.val : {k // k ≠ l} → Fin (D + 1)) P :=
    ⟨_, rfl⟩

  obtain ⟨H, hH⟩ : ∃ H : MvPolynomial (Fin (D + 1)) ℤ, H = ∑ n ∈ Finset.range (Q.totalDegree + 1),
      MvPolynomial.homogeneousComponent n Q * MvPolynomial.X l ^ (Q.totalDegree - n) := ⟨_, rfl⟩
  have hHhom : H.IsHomogeneous Q.totalDegree := by
    rw [hH]
    apply MvPolynomial.IsHomogeneous.sum
    intro n hn
    have hn' : n ≤ Q.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    have h2 := (MvPolynomial.homogeneousComponent_isHomogeneous n Q).mul
      ((MvPolynomial.isHomogeneous_X ℤ l).pow (Q.totalDegree - n))
    simpa [Nat.add_sub_of_le hn'] using h2
  have hterm : ∀ n ∈ Finset.range (Q.totalDegree + 1),
      MvPolynomial.aeval (x ∘ e) (MvPolynomial.homogeneousComponent n Q *
        MvPolynomial.X l ^ (Q.totalDegree - n)) =
      x (e l) ^ Q.totalDegree *
        MvPolynomial.aeval (fun i => (x ∘ e) i / x (e l)) (MvPolynomial.homogeneousComponent n Q) := by
    intro n hn
    have hn' : n ≤ Q.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [map_mul, map_pow, MvPolynomial.aeval_X,
      hdehom _ n (MvPolynomial.homogeneousComponent_isHomogeneous n Q)]
    conv_rhs => rw [← Nat.add_sub_of_le hn', pow_add]
    have hc := pow_ne_zero n hne
    simp only [Function.comp_apply]
    field_simp
    try ring
  have hHy : MvPolynomial.aeval (x ∘ e) H = 0 := by
    rw [hH, map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum,
      MvPolynomial.sum_homogeneousComponent, hQ, MvPolynomial.aeval_rename]
    have h3 : MvPolynomial.aeval ((fun i => (x ∘ e) i / x (e l)) ∘ Subtype.val) P = 0 := hPΩ
    rw [h3, mul_zero]
  have hH0 : H = 0 := by
    have hc : coneMap ℤ (x ∘ e) H = 0 := by
      rw [hform H _ hHhom, hHy, map_zero, zero_mul]
    have hk : H ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      exact hc
    rw [hfree, Ideal.mem_bot] at hk
    exact hk

  have hψ : (MvPolynomial.aeval fun k => if k = l then (1 : MvPolynomial (Fin (D + 1)) ℤ)
      else MvPolynomial.X k).comp (MvPolynomial.rename Subtype.val) =
      MvPolynomial.rename (R := ℤ) (Subtype.val : {k // k ≠ l} → Fin (D + 1)) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [k.2]
  have hQ0 : Q = 0 := by
    have h4 := congrArg (MvPolynomial.aeval fun k => if k = l then (1 : MvPolynomial (Fin (D + 1)) ℤ)
      else MvPolynomial.X k) hH0
    rw [hH, map_sum, map_zero] at h4
    simp only [map_mul, map_pow, MvPolynomial.aeval_X, ↓reduceIte, one_pow, mul_one] at h4
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent, hQ, ← AlgHom.comp_apply, hψ] at h4
    rw [hQ]
    exact h4
  rw [hQ] at hQ0
  exact MvPolynomial.rename_injective _ Subtype.val_injective (hQ0.trans (map_zero _).symm)

theorem chartRing_closed (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : IsIntegrallyClosed (chartRing x e l) := by
  unfold chartRing
  haveI : UniqueFactorizationMonoid (Algebra.adjoin ℤ (Set.range (chartGen x e l))) :=
    (chartGen_indep x e hfree l).aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem chartRing_frac (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : IsFractionRing (chartRing x e l) (fnField (x ∘ e)) := by
  classical

  have hne : ∀ i, x (e i) ≠ 0 := by
    intro i hi
    have hk : MvPolynomial.X i ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [hfree, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero i hk
  let R : Subring Ω := ((chartRing x e l).toSubring).map (fnField (x ∘ e)).val.toRingHom
  have hR : ∀ w ∈ R, ∃ a : chartRing x e l, ((a : fnField (x ∘ e)) : Ω) = w := by
    rintro w ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  let T : Set Ω := Set.range fun k : {k // k ≠ l} => x (e k) / x (e l)
  have hTR : Subring.closure T ≤ R := by
    rw [Subring.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨chartGen x e l k, Algebra.subset_adjoin ⟨k, rfl⟩, rfl⟩
  let F : IntermediateField ℚ Ω := (Subfield.closure T).toIntermediateField (fun q => by
    rw [eq_ratCast]
    exact SubfieldClass.ratCast_mem _ q)
  have hgen : ∀ i, x (e i) / x (e l) ∈ Subfield.closure T := by
    intro i
    by_cases h : i = l
    · subst h
      rw [div_self (hne i)]
      exact one_mem _
    · exact Subfield.subset_closure ⟨⟨i, h⟩, rfl⟩
  have hle : fnField (x ∘ e) ≤ F := by
    unfold fnField
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, j, rfl⟩
    have h3 : (x ∘ e) i / (x ∘ e) j = x (e i) / x (e l) / (x (e j) / x (e l)) := by
      simp only [Function.comp_apply]
      first
        | rw [div_div_div_cancel_right₀ (hne l)]
        | field_simp
    show _ ∈ Subfield.closure T
    rw [h3]
    exact div_mem (hgen i) (hgen j)
  have hsurj : ∀ z : fnField (x ∘ e), ∃ a b : chartRing x e l, b ≠ 0 ∧
      z * (b : fnField (x ∘ e)) = a := by
    intro z
    have hz : (z : Ω) ∈ Subfield.closure T := hle z.2
    obtain ⟨p, hp, q, hq, hpq⟩ := Subfield.mem_closure_iff.1 hz
    obtain ⟨a, ha⟩ := hR p (hTR hp)
    obtain ⟨b, hb⟩ := hR q (hTR hq)
    by_cases hq0 : q = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      apply Subtype.ext
      simp [← hpq, hq0]
    · refine ⟨a, b, ?_, ?_⟩
      · intro hb0
        apply hq0
        simp [← hb, hb0]
      · apply Subtype.ext
        show (z : Ω) * ((b : fnField (x ∘ e)) : Ω) = ((a : fnField (x ∘ e)) : Ω)
        rw [ha, hb, ← hpq, div_mul_cancel₀ _ hq0]
  have hinj : Function.Injective (algebraMap (chartRing x e l) (fnField (x ∘ e))) :=
    Subtype.val_injective
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb))
  · intro z
    obtain ⟨a, b, hb, h⟩ := hsurj z
    exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩⟩, h⟩
  · intro a b h
    exact ⟨1, by simp [hinj h]⟩

theorem coord_div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e)
    (l : Fin (D + 1)) (i : κ) : IsIntegral (chartRing x e l) (x i / x (e l)) := by
  classical
  have hne : x (e l) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X l ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero l hk
  let R : Subring Ω := ((chartRing x e l).toSubring).map (fnField (x ∘ e)).val.toRingHom
  have hgen : ∀ k, x (e k) / x (e l) ∈ R := by
    intro k
    by_cases hk : k = l
    · subst hk
      rw [div_self hne]
      exact one_mem _
    · exact ⟨chartGen x e l ⟨k, hk⟩, Algebra.subset_adjoin ⟨⟨k, hk⟩, rfl⟩, rfl⟩

  have hcone : ∀ q : MvPolynomial (Fin (D + 1)) ℤ,
      Polynomial.evalRingHom (x (e l))⁻¹ (coneMap ℤ (x ∘ e) q) ∈ R := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      unfold coneMap
      rw [MvPolynomial.aeval_C, eq_intCast, map_intCast]
      exact intCast_mem R a
    next p1 p2 h1 h2 =>
      rw [map_add, map_add]
      exact add_mem h1 h2
    next p1 k h1 =>
      rw [map_mul, map_mul]
      refine mul_mem h1 ?_
      unfold coneMap
      rw [MvPolynomial.aeval_X]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Function.comp_apply]
      rw [← div_eq_mul_inv]
      exact hgen k
  have hmem : ∀ v : coneRing ℤ (x ∘ e),
      ((Polynomial.evalRingHom (x (e l))⁻¹).comp (coneRing ℤ (x ∘ e)).val.toRingHom) v ∈ R := by
    rintro ⟨v, q, rfl⟩
    exact hcone q
  let φ : coneRing ℤ (x ∘ e) →+* R :=
    ((Polynomial.evalRingHom (x (e l))⁻¹).comp (coneRing ℤ (x ∘ e)).val.toRingHom).codRestrict R hmem
  let eqv : (chartRing x e l).toSubring ≃+* R :=
    Subring.equivMapOfInjective _ _ (fun a b hab => Subtype.ext hab)
  let ψ : R →+* chartRing x e l := eqv.symm.toRingHom
  obtain ⟨p, hm, hp⟩ := h.integral i
  refine ⟨(p.map φ).map ψ, (hm.map _).map _, ?_⟩
  rw [Polynomial.eval₂_map, Polynomial.eval₂_map]
  have hcomp : ((algebraMap (chartRing x e l) Ω).comp ψ).comp φ =
      (Polynomial.evalRingHom (x (e l))⁻¹).comp (algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω)) := by
    refine RingHom.ext fun v => ?_
    have h2 := congrArg Subtype.val (eqv.apply_symm_apply (φ v))
    first
      | exact h2
      | (simp only [eqv, Subring.coe_equivMapOfInjective_apply] at h2; exact h2)
  have hpt : x i / x (e l) = Polynomial.evalRingHom (x (e l))⁻¹ (Polynomial.C (x i) * Polynomial.X) := by
    simp [div_eq_mul_inv]
  rw [hcomp, hpt, ← Polynomial.hom_eval₂, hp, map_zero]

theorem sec_div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) [Fintype κ] (h : IsProjFrame x e)
    (l : Fin (D + 1)) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    IsIntegral (chartRing x e l) (⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ :
      IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  classical
  obtain ⟨p, hp, hps⟩ := Submodule.mem_map.1 hs
  have hph : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hp

  have hhom : MvPolynomial.aeval (fun i => x i / x (e l)) p = s / x (e l) ^ n := by
    rw [← hps]
    show MvPolynomial.aeval (fun i => x i / x (e l)) p = MvPolynomial.aeval x p / x (e l) ^ n
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hph (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [mul_div_assoc]
    congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  have hΩ : IsIntegral (chartRing x e l) (s / x (e l) ^ n) := by
    let S := (integralClosure (chartRing x e l) Ω).restrictScalars ℤ
    have hy : ∀ i, x i / x (e l) ∈ S := fun i => coord_div_isIntegral x e h l i
    let y' : κ → S := fun i => ⟨x i / x (e l), hy i⟩
    have hS : MvPolynomial.aeval (fun i => x i / x (e l)) p = S.val (MvPolynomial.aeval y' p) := by
      first
        | (rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]; rfl)
        | (rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval])
        | exact (DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℤ) S.val) p).symm
    rw [← hhom, hS]
    exact (MvPolynomial.aeval y' p).2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (chartRing x e l)
    (IntermediateField.extendScalars (fnField_comp_le' x e)) Ω)
    (fun a b hab => Subtype.ext hab)).1 hΩ

theorem trace_mem_chart [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e)
    (l : Fin (D + 1)) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      ⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ ∈ chartRing x e l := by
  have hi := sec_div_isIntegral x e h l n hs
  haveI := chartRing_frac x e h.free l
  haveI := chartRing_closed x e h.free l
  by_cases hfd : FiniteDimensional (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
  · haveI := hfd
    have ht := Algebra.isIntegral_trace (L := fnField (x ∘ e)) hi
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := fnField (x ∘ e))).1 ht
    rw [← hy]
    exact y.2
  · have hnb : ¬∃ s : Finset (IntermediateField.extendScalars (fnField_comp_le' x e)),
        Nonempty (Basis s (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))) := by
      rintro ⟨s, ⟨b⟩⟩
      first
        | exact hfd (FiniteDimensional.of_fintype_basis b)
        | exact hfd (Module.Finite.of_basis b)
    have h0 : Algebra.trace (fnField (x ∘ e))
        (IntermediateField.extendScalars (fnField_comp_le' x e)) = 0 := by
      first
        | exact Algebra.trace_eq_zero_of_not_exists_basis _ hnb
        | exact Algebra.trace_eq_zero_of_not_exists_basis hnb
    rw [h0, LinearMap.zero_apply]
    exact zero_mem _

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem hc_mul_homog {σ : Type*} {p : MvPolynomial σ ℤ} {a : ℕ} (hp : p.IsHomogeneous a)
    (q : MvPolynomial σ ℤ) (b : ℕ) :
    MvPolynomial.homogeneousComponent (a + b) (p * q) =
      p * MvPolynomial.homogeneousComponent b q := by
  classical
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent q]
  rw [Finset.mul_sum, map_sum, Finset.sum_eq_single b]
  · rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (hp.mul (MvPolynomial.homogeneousComponent_isHomogeneous b q))), if_pos rfl]
  · intro k _ hk
    rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (hp.mul (MvPolynomial.homogeneousComponent_isHomogeneous k q))), if_neg (by omega)]
  · intro hb
    rw [MvPolynomial.homogeneousComponent_eq_zero b q (by simp at hb; omega), mul_zero, map_zero]

private theorem X_pow_dvd_of_le_degrees {σ : Type*} (i : σ) (m : ℕ) (p : MvPolynomial σ ℤ)
    (h : ∀ d ∈ p.support, m ≤ d i) : MvPolynomial.X i ^ m ∣ p := by
  classical
  rw [p.as_sum]
  refine Finset.dvd_sum fun d hd => ?_
  have hle : Finsupp.single i m ≤ d := Finsupp.single_le_iff.mpr (h d hd)
  exact ⟨MvPolynomial.monomial (d - Finsupp.single i m) (MvPolynomial.coeff d p), by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le hle]⟩

theorem X_pow_dvd_homogeneous_one_var {H : MvPolynomial (Fin (0 + 1)) ℤ} {M m : ℕ} (hH : H.IsHomogeneous M)
    (hm : m ≤ M) : MvPolynomial.X 0 ^ m ∣ H := by
  apply X_pow_dvd_of_le_degrees
  intro d hd
  have hdeg : d.degree = M := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hH.coeff_eq_zero hne)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_one] at hdeg
  omega

private theorem coord_ne_zero_of_coordIdeal_eq_bot (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (i : Fin (D + 1)) :
    y i ≠ 0 := by
  intro h0
  have hmem : (MvPolynomial.X i : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h0]
  rw [hfree, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero i hmem

private theorem coneMap_of_isHomogeneous_arakelov_geometry {n : ℕ} (y : Fin (D + 1) → Ω) (P : MvPolynomial (Fin (D + 1)) ℤ)
    (hP : P.IsHomogeneous n) :
    coneMap ℤ y P = Polynomial.C (MvPolynomial.aeval y P) * Polynomial.X ^ n := by
  classical
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero hne)
  rw [← hdeg, Finsupp.degree_eq_sum]
  simp only [coneMap, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_pow, ← map_prod, map_mul,
    eq_intCast, map_intCast]
  ring

theorem X_zero_pow_dvd_of_isHomogeneous_aeval (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (u : Ω) (n m : ℕ)
    (H : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) (hH : ∀ l, (H l).IsHomogeneous (m + n))
    (hu : ∀ l, y l ^ m * u = MvPolynomial.aeval y (H l)) : MvPolynomial.X 0 ^ m ∣ H 0 := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact X_pow_dvd_homogeneous_one_var (hH 0) (by omega)
  have hl1 : (⟨1, by omega⟩ : Fin (D + 1)) ≠ 0 := by simp [Fin.ext_iff]
  have hPh : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ).IsHomogeneous (m + (m + n)) :=
    ((MvPolynomial.isHomogeneous_X_pow _ _).mul (hH 0)).sub ((MvPolynomial.isHomogeneous_X_pow _ _).mul (hH _))
  have hPy : MvPolynomial.aeval y (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ) = 0 := by
    simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_X, ← hu]
    ring
  have hP0 : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ) = 0 := by
    have hmem : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
        MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
      rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous_arakelov_geometry y _ hPh, hPy]
      simp
    rw [hfree, Ideal.mem_bot] at hmem
    exact hmem
  have hPeq := sub_eq_zero.mp hP0
  apply X_pow_dvd_of_le_degrees
  intro d hd
  have h1 : MvPolynomial.coeff (d + Finsupp.single ⟨1, by omega⟩ m) (MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩) ≠ 0 := by
    rw [← hPeq, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul', if_pos le_add_self,
      add_tsub_cancel_right, one_mul]
    exact MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at h1
  split_ifs at h1 with hle
  · have := Finsupp.single_le_iff.mp hle
    simpa [Finsupp.single_apply, Ne.symm hl1] using this
  · exact absurd rfl h1

theorem mem_sec_of_charts (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (u : Ω) (n m : ℕ)
    (H : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) (hH : ∀ l, (H l).IsHomogeneous (m + n))
    (hu : ∀ l, y l ^ m * u = MvPolynomial.aeval y (H l)) : u ∈ sec ℤ y n := by
  have hy0 : y 0 ≠ 0 := coord_ne_zero_of_coordIdeal_eq_bot y hfree 0
  obtain ⟨G, hG⟩ := X_zero_pow_dvd_of_isHomogeneous_aeval y hfree u n m H hH hu
  have hG' : MvPolynomial.X 0 ^ m * MvPolynomial.homogeneousComponent n G = H 0 := by
    rw [← hc_mul_homog (MvPolynomial.isHomogeneous_X_pow (0 : Fin (D + 1)) m) G n, ← hG,
      MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hH 0)), if_pos rfl]
  refine Submodule.mem_map.mpr ⟨MvPolynomial.homogeneousComponent n G,
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.homogeneousComponent_isHomogeneous n G), ?_⟩
  show MvPolynomial.aeval y (MvPolynomial.homogeneousComponent n G) = u
  have h2 := hu 0
  rw [← hG', map_mul, map_pow, MvPolynomial.aeval_X] at h2
  exact (mul_left_cancel₀ (pow_ne_zero m hy0) h2).symm

theorem trace_chart_eq [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h0 : x (e 0) ≠ 0)
    (l : Fin (D + 1)) (hl : x (e l) ≠ 0) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    ((Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      ⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ : fnField (x ∘ e)) : Ω) =
    (x (e 0) / x (e l)) ^ n *
      ((Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : fnField (x ∘ e)) : Ω) := by
  have hc : (x (e 0) / x (e l)) ^ n ∈ fnField (x ∘ e) := pow_mem (div_mem_fnField (x ∘ e) 0 l) n
  have heq : (⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ : IntermediateField.extendScalars (fnField_comp_le' x e)) =
      (⟨(x (e 0) / x (e l)) ^ n, hc⟩ : fnField (x ∘ e)) • ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ := by
    apply Subtype.ext
    show s / x (e l) ^ n = (x (e 0) / x (e l)) ^ n * (s / x (e 0) ^ n)
    rw [div_pow]
    field_simp
  rw [heq, LinearMap.map_smul, smul_eq_mul]
  rfl

theorem chart_elem (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (a : fnField (x ∘ e))
    (ha : a ∈ chartRing x e l) :
    ∃ g : MvPolynomial {k // k ≠ l} ℤ, (a : Ω) = MvPolynomial.aeval (fun k => x (e k.1) / x (e l)) g := by
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at ha
  obtain ⟨g, rfl⟩ := ha
  refine ⟨g, ?_⟩
  induction g using MvPolynomial.induction_on <;> simp_all [chartGen]

theorem homog_of_chart (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (a : fnField (x ∘ e))
    (ha : a ∈ chartRing x e l) (hl : x (e l) ≠ 0) :
    ∃ N0, ∀ N, N0 ≤ N → ∃ H : MvPolynomial (Fin (D + 1)) ℤ, H.IsHomogeneous N ∧
      x (e l) ^ N * (a : Ω) = MvPolynomial.aeval (x ∘ e) H := by
  obtain ⟨g, hg⟩ := chart_elem x e l a ha
  rw [hg]
  clear hg
  induction g using MvPolynomial.induction_on
  · rename_i c
    refine ⟨0, fun N _ => ⟨MvPolynomial.C c * MvPolynomial.X l ^ N, ?_, ?_⟩⟩
    · simpa using (MvPolynomial.isHomogeneous_C (Fin (D + 1)) c).mul (MvPolynomial.isHomogeneous_X_pow l N)
    · simp [mul_comm]
  · rename_i p q hp hq
    obtain ⟨N1, h1⟩ := hp
    obtain ⟨N2, h2⟩ := hq
    refine ⟨max N1 N2, fun N hN => ?_⟩
    obtain ⟨H1, hH1, e1⟩ := h1 N (le_of_max_le_left hN)
    obtain ⟨H2, hH2, e2⟩ := h2 N (le_of_max_le_right hN)
    exact ⟨H1 + H2, hH1.add hH2, by rw [map_add, mul_add, e1, e2, map_add]⟩
  · rename_i p k hp
    obtain ⟨N1, h1⟩ := hp
    refine ⟨N1 + 1, fun N hN => ?_⟩
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    obtain ⟨H, hH, e1⟩ := h1 N' (by omega)
    refine ⟨H * MvPolynomial.X k.1, hH.mul (MvPolynomial.isHomogeneous_X ℤ k.1), ?_⟩
    rw [map_mul, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_X, ← e1]
    simp only [Function.comp]
    field_simp
    ring

theorem trace_mem_sec [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) (n : ℕ)
    {s : Ω} (hs : s ∈ sec ℤ x n) :
    x (e 0) ^ n * ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : fnField (x ∘ e)) : Ω) ∈ sec ℤ (x ∘ e) n := by
  have hne : ∀ j, x (e j) ≠ 0 := fun j => coord_ne_zero_of_coordIdeal_eq_bot (x ∘ e) h.free j
  choose N0 hN0 using fun j => homog_of_chart x e j _ (trace_mem_chart x e h j n hs) (hne j)
  choose H hHh hHe using fun j => hN0 j (Finset.univ.sup N0 + n)
    (le_trans (Finset.le_sup (Finset.mem_univ j)) (Nat.le_add_right _ _))
  refine mem_sec_of_charts (x ∘ e) h.free _ n (Finset.univ.sup N0) H hHh (fun j => ?_)
  rw [← hHe j, trace_chart_eq x e (hne 0) j (hne j) n hs]
  simp only [Function.comp_apply]
  have hj := hne j
  rw [div_pow, pow_add]
  field_simp

theorem eq_zero_of_trace' [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n)
    (h0 : ∀ l, ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s * ε l / x (e 0) ^ (n + k), sec_div_mem x (e 0) (mul_mem_sec x hs (hε l))⟩ :
          fnField (x ∘ e)) : Ω) = 0) : s = 0 := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero_of_coordIdeal_eq_bot (x ∘ e) h.free 0
  have ht := eq_zero_of_trace x e h ε hε hli ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ (fun l => by
    have e1 : (⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : IntermediateField.extendScalars (fnField_comp_le' x e)) *
        ⟨ε l / x (e 0) ^ k, sec_div_mem x (e 0) (hε l)⟩ =
        ⟨s * ε l / x (e 0) ^ (n + k), sec_div_mem x (e 0) (mul_mem_sec x hs (hε l))⟩ := by
      apply Subtype.ext
      show s / x (e 0) ^ n * (ε l / x (e 0) ^ k) = s * ε l / x (e 0) ^ (n + k)
      rw [pow_add, div_mul_div_comm]
    rw [e1]
    exact Subtype.ext (h0 l))
  have h2 := congrArg Subtype.val ht
  simpa [hx0] using h2

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}

theorem fnField_comp_le (x : κ → Ω) (e : Fin (D + 1) → κ) : fnField (x ∘ e) ≤ fnField x := by
  exact TraceNormBounds.fnField_comp_le' x e

theorem projDeg_pos (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    0 < projDeg x e :=
  TraceNormBounds.projDeg_pos' x e h

def fnTrace (x : κ → Ω) (e : Fin (D + 1) → κ) (t : Ω) : Ω :=
  open Classical in
  if ht : t ∈ fnField x then
    ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le x e)) ⟨t, ht⟩ : fnField (x ∘ e)) : Ω)
  else 0

def secTrace (x : κ → Ω) (e : Fin (D + 1) → κ) (n : ℕ) (s : Ω) : Ω :=
  x (e 0) ^ n * fnTrace x e (s / x (e 0) ^ n)

theorem exists_indep_sections (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    ∃ (k : ℕ) (ε : Fin (projDeg x e) → Ω), (∀ l, ε l ∈ sec ℤ x k) ∧
      LinearIndependent (fnField (x ∘ e)) ε := by
  exact TraceNormBounds.exists_indep_sections' x e h

theorem secTrace_mem (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) (n : ℕ) {s : Ω}
    (hs : s ∈ sec ℤ x n) : secTrace x e n s ∈ sec ℤ (x ∘ e) n := by
  unfold secTrace fnTrace
  rw [dif_pos (TraceNormBounds.sec_div_mem x (e 0) hs)]
  exact TraceNormBounds.trace_mem_sec x e h n hs

theorem eq_zero_of_secTrace_mul_eq_zero (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n)
    (h0 : ∀ l, secTrace x e (n + k) (s * ε l) = 0) : s = 0 := by
  have hx0 : x (e 0) ≠ 0 := by
    intro h0
    have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
      rw [coordIdeal, RingHom.mem_ker]
      simp [coneMap, h0]
    rw [h.free] at hmem
    exact MvPolynomial.X_ne_zero 0 ((Ideal.mem_bot).1 hmem)
  refine TraceNormBounds.eq_zero_of_trace' x e h ε hε hli n hs (fun l => ?_)
  have h1 := h0 l
  unfold secTrace fnTrace at h1
  split_ifs at h1 with hm
  · exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hx0)
  · exact absurd (TraceNormBounds.sec_div_mem x (e 0) (by first | exact TraceNormBounds.mul_mem_sec x hs (hε l) | exact mul_mem_sec x hs (hε l) | exact ReciprocityTheory.ChartRestriction.G.Geo.mul_mem_sec x hs (hε l))) hm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
