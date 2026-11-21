import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.InnerCompactWordActionAdjoint
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PsiDatum

section
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem psiDatum_std {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h)
    (hstd : StdGap ε lam) (h8 : 8 * (n : ℝ) * S7.q0 ε < h) (hq : 1 ≤ S7.q0 ε) (hμ : S7.IsMu lam μ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) (ι : V ≃ₗ[ℂ] T.V),
      IsURepOn (UJset ε) σ ∧ IsDerivedOn ε σ D E ∧ IsKIrrHW ε E (lowK ε lam) V ∧
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) ∧
      (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) ∧
      ∀ g ∈ UJset ε, ∀ v v' : V,
        ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ := by
  have hP := S7.isPsiFor_psiM ε lam h T μ hlam hμ hgap hq h8
  set Ψ := S7.PsiM T μ with hΨ
  replace hP : IsPsiFor ε lam T Ψ := by first | exact hP | exact hP.1
  have hv₀ : T.w ≠ 0 := fun h0 => by
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0 := norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hstd hP hv₀)
  set c : ℂ := ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast inv_ne_zero hN0
  let j : T.V →ₗ[ℂ] datumV ε Ψ T.w :=
    { toFun := fun v => ⟨⟨uniformisationL2 ε Ψ T.w (c • v), datumEmbedding_mem_smooth hP T.w _⟩,
        (mem_datumV_iff hP T.w _).2 ⟨c • v, rfl⟩⟩
      map_add' := fun v v' => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (v + v')) = uniformisationL2 ε Ψ T.w (c • v) + uniformisationL2 ε Ψ T.w (c • v')
        rw [smul_add, datumEmbedding_add hP]))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (a • v)) = a • uniformisationL2 ε Ψ T.w (c • v)
        rw [smul_comm, datumEmbedding_smul hP])) }
  have hj : Function.Bijective j := by
    refine ⟨fun v v' hv => ?_, fun x => ?_⟩
    · have : uniformisationL2 ε Ψ T.w (c • v) = uniformisationL2 ε Ψ T.w (c • v') :=
        congrArg (fun x : datumV ε Ψ T.w => ((x : smD ε (rreg ε)) : L2 ε)) hv
      exact smul_right_injective _ hc0 (uniformisationL2_injective hP hv₀ this)
    · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 x.2
      refine ⟨c⁻¹ • v, Subtype.ext (Subtype.ext ?_)⟩
      show uniformisationL2 ε Ψ T.w (c • c⁻¹ • v) = _
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, hv]
  let e := LinearEquiv.ofBijective j hj
  refine ⟨L2 ε, inferInstance, inferInstance, inferInstance, rreg ε, smD ε (rreg ε), smE ε (rreg ε),
    datumV ε Ψ T.w, e.symm, rreg_isURepOn ε, isDerivedOn_smE (rreg_isURepOn ε),
    datumV_isKIrrHW hP hv₀, datumV_casimir hP T.w, datumV_kStable hP T.w, fun g hgm v v' => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective v
  obtain ⟨x', rfl⟩ := e.surjective v'
  rw [e.symm_apply_apply, e.symm_apply_apply]
  show ⟪uniformisationL2 ε Ψ T.w (c • x'), rreg ε g (uniformisationL2 ε Ψ T.w (c • x))⟫_ℂ = _
  have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1 := by
    rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    rw [pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]
  rw [formulaF hstd hP hv₀ hgm, map_smul, inner_smul_left, inner_smul_right]
  linear_combination ⟪x', Ψ g x⟫_ℂ * key

theorem datum_link_std {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h) (hstd : StdGap ε lam)
    (h8 : 8 * (n : ℝ) * S7.q0 ε < h) (hq : 1 ≤ S7.q0 ε)
    (T : S7.KType ε (lowK ε lam)) {μ : Fin n → ℤ} (hμ : S7.IsMu lam μ) :
    ∃ ι : V ≃ₗ[ℂ] T.V,
      (∀ g ∈ UJset ε, ∀ v v' : V,
        ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) ∧
      (∀ v v' : V, ⟪ι v', ι v⟫_ℂ = ⟪((v' : D) : H), ((v : D) : H)⟫_ℂ) ∧
      ∀ (k : S7.KG ε) (v w : V), ((w : D) : H) = σ (S7.toMK k) ((v : D) : H) →
        ι w = T.op k (ι v) := by
  obtain ⟨H₂, _, _, _, σ₂, D₂, E₂, V₂, ι₂, hσ₂, hD₂, hV₂, hc₂, hVK₂, hco⟩ :=
    psiDatum_std ε lam h T μ hlam hgap hstd h8 hq hμ
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ hD hV hσ₂ hD₂ hV₂
  obtain ⟨ψ, -, hψI⟩ := KTypeIsomorphism.exists_phi hσ₂ hD₂ hV₂ hσ hD hV
  have := hV.1
  have := hV₂.1
  have hφi : Function.Injective φ := (injective_iff_map_eq_zero φ).mpr fun v hv => by
    have h1 := hφI v v
    rw [hv] at h1
    simpa using h1.symm
  have hψi : Function.Injective ψ := (injective_iff_map_eq_zero ψ).mpr fun v hv => by
    have h1 := hψI v v
    rw [hv] at h1
    simpa using h1.symm
  have hrk : Module.finrank ℂ V = Module.finrank ℂ V₂ :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hφi)
      (LinearMap.finrank_le_finrank_of_injective hψi)
  let e : V ≃ₗ[ℂ] V₂ := φ.linearEquivOfInjective hφi hrk
  have hU := rigid_universal hσ hD hV hc hVK hσ₂ hD₂ hV₂ hc₂ hVK₂ hstd φ hφK hφI
  have h1J : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hcoef : ∀ g ∈ UJset ε, ∀ v v' : V, ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ =
      ⟪(e.trans ι₂) v', S7.PsiM T μ g ((e.trans ι₂) v)⟫_ℂ := fun g hgm v v' => by
    rw [← hU g hgm v v', hco g hgm]; rfl
  have hiso : ∀ v v' : V, ⟪(e.trans ι₂) v', (e.trans ι₂) v⟫_ℂ =
      ⟪((v' : D) : H), ((v : D) : H)⟫_ℂ := fun v v' => by
    have := hcoef 1 h1J v v'
    rw [hσ.1.1, S7.psiM_one] at this
    exact this.symm
  refine ⟨e.trans ι₂, hcoef, hiso, fun k v w hw => ?_⟩
  have hk : S7.PsiM T μ (S7.toMK k) = T.op k := by
    have := S7.psiM_equiv T μ k 1 (g := 1) h1J
    rwa [S7.toMK_one', Matrix.mul_one, Matrix.mul_one, S7.psiM_one, S7.op_one', mul_one, mul_one] at this
  refine ext_inner_left ℂ fun x => ?_
  obtain ⟨v', rfl⟩ := (e.trans ι₂).surjective x
  rw [hiso, hw, hcoef _ k.1.2, hk]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Irr

variable {n : ℕ} {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

end Irr

section Main

theorem lowestKType_casimir_cone (n : ℕ) : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapAtLeast ε lam h →
      max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
        (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ))) < h →
      1 ≤ pOf ε → 1 ≤ qOf ε →
      ∀ (μ : Fin n → ℝ) (w : D), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w →
        InRootCone (μ - lowK ε lam) := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgap hbig hp hq ν w hw hw0 hk
  have hlam : S7.IsHCParam lam := ⟨hanti, hint⟩
  have hstd : StdGap ε lam := ⟨hanti, h, hgap, lt_of_le_of_lt (le_max_left _ _) hbig⟩
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 := lt_of_le_of_lt (le_max_right _ _) hbig
    have e : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ) := by simp [S7.q0, Nat.cast_min]
    rw [e] at h1
    have : 0 ≤ (n : ℝ) * S7.q0 ε := by positivity
    nlinarith [Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))]
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨μ, hμ⟩ := exists_isMu hlam
  obtain ⟨ι, hcoef, -, hιK⟩ := datum_link_std hσ hD hV hc hVK hlam hgap hstd h8 (le_min hp hq) T hμ
  obtain ⟨hEM, hlow, hwt, hgen⟩ := k2vM lam μ hμ
  have hVst := hV.2.1
  have : FiniteDimensional ℂ V := hV.1
  have hw1 := lowestKType_vector_exists ε lam σ D E V hσ hD hV T ι hιK
  have hU := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hℓ : ∀ (a : Fin n) (v w : V), (w : D) = E a a v →
      submoduleEvaluationFunctional V (ι.symm T.w) w = ((lowK ε lam a : ℝ) : ℂ) * submoduleEvaluationFunctional V (ι.symm T.w) v := by
    intro a v w hw
    have e1 : submoduleEvaluationFunctional V (ι.symm T.w) w = inner ℂ ((ι.symm T.w : V) : D) (w : D) := rfl
    have e2 : submoduleEvaluationFunctional V (ι.symm T.w) v = inner ℂ ((ι.symm T.w : V) : D) (v : D) := rfl
    rw [e1, e2, hw, ← hU a a rfl, hw1.1 a, inner_smul_left, Complex.conj_ofReal]
  obtain ⟨u, hu, hTu⟩ := Cone.lift0 hVst hD.glRep hU (f := fun _ => w) (fun _ => hw) (fun _ => hk)
  have hA := Cone.isKRelation_compactWordAction hVst hD.glRep
  set θ := sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) with hθ
  have hex : ∃ l, KirrLow ε l ∧ θ (kirrWord (Cone.compactWordAction ε E V hVst) u l) ≠ 0 := by
    by_contra hno
    push Not at hno
    obtain ⟨W, h1, h2, h3⟩ := Cone.exists_stable hVst (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) _
      (wordSpan_isKStable hA hu) (fun x hx =>
        (Submodule.span_le (p := LinearMap.ker θ)).mpr (by rintro _ ⟨l, hl, rfl⟩; exact hno l hl) hx)
    have h4 := lowestKType_trace_integral ε lam H σ D E V hσ hD hV hint hanti T μ ι hμ hcoef W h2 h3 u
      (h1 (kirrWord_mem (l := []) u (by simp [KirrLow])))
    rw [hTu] at h4
    have hn : 0 < n := lt_of_lt_of_le hp (by
      simpa [pOf] using Finset.card_filter_le (univ : Finset (Fin n)) fun a => ε a = true)
    exact hw0 (congrFun h4 ⟨0, hn⟩)
  obtain ⟨l, hl, hx⟩ := hex
  set x := kirrWord (Cone.compactWordAction ε E V hVst) u l with hxd
  obtain ⟨c, hc0⟩ := Function.ne_iff.mp hx
  have hwt2 : ∀ a, eMM μ a a (θ x c) =
      (((kirrWt ν l - lowK ε lam + (lam + rho n)) a : ℝ) : ℂ) • θ x c := by
    intro a
    have h1 := congrFun (sθ_sA ε E V hVst (eMM μ) hEM (phiMM μ) (lam + rho n) (lowK ε lam) hwt
      (submoduleEvaluationFunctional V (ι.symm T.w)) hℓ a x) c
    have h2 := congrFun (congrArg θ (word_isWeightVector hA hu.1 l hl a)) c
    rw [← hxd, Cone.compactWordAction, LinearMap.sub_apply, map_sub, map_smul, Pi.sub_apply, h1, Cone.sθ_sC,
      Pi.add_apply, Cone.tensV_eq] at h2
    simp only [Pi.smul_apply, ← hθ] at h2
    have h3 : eMM μ a a (θ x c) = (kirrWt ν l a : ℂ) • θ x c -
        ((lowK ε lam a - (lam + rho n) a : ℝ) : ℂ) • θ x c := by rw [← h2]; abel
    rw [h3, ← sub_smul]
    congr 1
    simp only [Pi.add_apply, Pi.sub_apply]; push_cast; ring
  have h5 := Cone.verma_weight (eMM μ) hEM (phiMM μ) (lam + rho n) hlow hwt hgen hc0 hwt2
  have h6 := root_swap_eq_neg (weight_sub_mem_rootCone ν l hl) h5
  convert h6 using 1
  abel

end Main

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
