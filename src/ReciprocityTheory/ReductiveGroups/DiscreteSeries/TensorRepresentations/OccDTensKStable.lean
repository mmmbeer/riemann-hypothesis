import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccATensWordMem
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ProjectionCommutesDerivedAction
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Unitarize

section
noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Phi

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

def occC2phi (dual : Bool) (ε : Fin n → Bool) (η f : Fin n → smD ε (rreg ε)) : L2 ε :=
  toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε)) (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))

theorem occurrence_phi_add (dual : Bool)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    {η f f' : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf' : f' ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    occC2phi dual ε η (f + f') = occC2phi dual ε η f + occC2phi dual ε η f' := by
  unfold occC2phi
  have e : (fun c => (((f + f') c : smD ε (rreg ε)) : L2 ε)) =
      (fun c => ((f c : smD ε (rreg ε)) : L2 ε)) + (fun c => ((f' c : smD ε (rreg ε)) : L2 ε)) := by
    funext c; simp
  rw [e, occurrence_coef_add]
  exact toL2_add_smooth ε (occA_coef_memLp dual (rreg_isURepOn ε) hW η f hη hf)
    (occA_coef_memLp dual (rreg_isURepOn ε) hW η f' hη hf')

theorem occurrence_phi_smul (dual : Bool) (η f : Fin n → smD ε (rreg ε)) (a : ℂ) :
    occC2phi dual ε η (a • f) = a • occC2phi dual ε η f := by
  unfold occC2phi
  have e : (fun c => (((a • f) c : smD ε (rreg ε)) : L2 ε)) = a • (fun c => ((f c : smD ε (rreg ε)) : L2 ε)) := by
    funext c; simp
  rw [e, occurrence_coef_smul]
  exact toL2_smul_smooth ε a _

theorem occurrence_phi_k_equivariant (dual : Bool) (η f f' : Fin n → smD ε (rreg ε)) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε)
    (hff : (fun c => ((f' c : smD ε (rreg ε)) : L2 ε)) = kDiag dual (rreg ε) k (fun c => ((f c : smD ε (rreg ε)) : L2 ε))) :
    rreg ε k (occC2phi dual ε η f) = occC2phi dual ε η f' := by
  unfold occC2phi
  rw [rightRegular_toL2 ε _ (cf_kset_sub hk)]
  apply toL2_congr_of_forall_inUJ_eq
  intro g hg
  show ∑ c, _ = ∑ c, _
  rw [occA_tensGrp_mul dual (rreg_isURepOn ε) hg hk, ← hff]

end Phi

section Mem

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occurrence_projection_mem (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (η f : Fin n → smD ε (rreg ε)) (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f) ∈
      (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')).map (smD ε (rreg ε)).subtype := by
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  obtain ⟨j, hj⟩ := tensor_generated_mem_layer hD.glRep hV.2.1 hf
  set W := layer ε (smE ε (rreg ε)) (datumV ε Ψ v₀) j with hWdef
  have : FiniteDimensional ℂ W := finiteDimensional_layer hV.1 j
  have hWM : ∀ u : Fin n → W, (fun c => ((u c : W) : smD ε (rreg ε))) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :=
    fun u => (tset_mem).2 fun c => layer_le_genSub j (u c).2
  let P := (Hlam ε Ψ' v₀').starProjection
  let Φ : (Fin n → W) →ₗ[ℂ] L2 ε :=
    { toFun := fun u => P (occC2phi dual ε η (fun c => ((u c : W) : smD ε (rreg ε))))
      map_add' := fun u u' => by
        have e : (fun c => (((u + u') c : W) : smD ε (rreg ε))) =
            (fun c => ((u c : W) : smD ε (rreg ε))) + (fun c => ((u' c : W) : smD ε (rreg ε))) := by
          funext c; simp
        rw [e, occurrence_phi_add dual hW hη (hWM u) (hWM u'), map_add]
      map_smul' := fun a u => by
        have e : (fun c => (((a • u) c : W) : smD ε (rreg ε))) = a • (fun c => ((u c : W) : smD ε (rreg ε))) := by
          funext c; simp
        simp only [RingHom.id_apply]
        rw [e, occurrence_phi_smul, map_smul] }
  have hSf : FiniteDimensional ℂ (LinearMap.range Φ) := LinearMap.finiteDimensional_range Φ
  have hS : LinearMap.range Φ ≤ closGen (smE ε (rreg ε)) (datumV ε Ψ' v₀') := by
    rintro x ⟨u, rfl⟩
    exact Submodule.starProjection_apply_mem (Hlam ε Ψ' v₀') _
  have hSK : ∀ k ∈ Kset ε, ∀ x ∈ LinearMap.range Φ, rreg ε k x ∈ LinearMap.range Φ := by
    rintro k hk x ⟨u, rfl⟩
    have hy := fun d => layer_k_stable hσ hD hV.2.1 (datumV_kStable hP v₀) j k hk (u d : W) (u d).2
    choose y hyW hy using hy
    let u' : Fin n → W := fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • (⟨y d, hyW d⟩ : W)
    refine ⟨u', ?_⟩
    show P _ = rreg ε k (P _)
    rw [← projection_commutes_right_regular hgap' hP' hv₀' k (cf_kset_sub hk)]
    congr 1
    refine (occurrence_phi_k_equivariant dual η _ _ hk ?_).symm
    funext c
    simp only [u', kDiag, Submodule.coe_sum, Submodule.coe_smul, hy]
  have hle := data_kfin_le hgap' hσ hD (datumV_isKIrrHW hP' hv₀') (datumV_casimir hP' v₀') (datumV_kStable hP' v₀')
    (LinearMap.range Φ) hS hSf hSK
  apply hle
  refine ⟨fun c => ⟨f c, hj c⟩, ?_⟩
  rfl

end Mem

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occurrence_pairing (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hP' : IsPsiFor ε lam' T' Ψ')
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hB : ∃ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) ≠ 0) :
    ∃ η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
          (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) ((x' : smD ε (rreg ε)) : L2 ε) ≠ 0 := by
  obtain ⟨ξ, ζ, v', hI⟩ := hB
  have hσ := rreg_isURepOn ε
  let jm : T.V → smD ε (rreg ε) := fun v => ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩
  have hjm : ∀ v, jm v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) := fun v =>
    layer_le_genSub (ε := ε) 0 ((mem_datumV_iff hP v₀ _).2 ⟨v, rfl⟩)
  have hη : (fun c => jm (ξ c)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := tset_mem.2 fun c => hjm _
  have hf : (fun c => jm (ζ c)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := tset_mem.2 fun c => hjm _
  refine ⟨fun c => jm (ξ c), hη, fun c => jm (ζ c), hf, ⟨uniformisationL2 ε Ψ' v₀' v', datumEmbedding_mem_smooth hP' v₀' v'⟩,
    layer_le_genSub (ε := ε) 0 ((mem_datumV_iff hP' v₀' _).2 ⟨v', rfl⟩), ?_⟩
  have hF : ∀ g, inUJ ε g → occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε)) g =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g := by
    intro g hg
    have hg' : g ∈ UJset ε := hg
    simp only [occCoef, occPsiCoef, tensGrp, jm, inner_sum, inner_smul_right, formulaF hgap hP hv₀ hg',
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have hM1 : MemLp (fun g : Formalism.REAL.UJ ε => (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) *
      occPsiCoef dual Ψ ξ ζ g) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    (occA_coef_memLp dual hσ hW _ _ hη hf).ae_eq (Filter.Eventually.of_forall fun g => hF _ g.2)
  have e1 : toL2 ε (occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε))) =
      toL2 ε (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g) := toL2_congr_of_forall_inUJ_eq hF
  have e2 : inner ℂ (toL2 ε (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g))
      (toL2 ε (jfun Ψ' v₀' v')) = starRingEnd ℂ (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)) *
        ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
          inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v') ∂(Formalism.REAL.muG ε) := by
    rw [inner_toL2_eq_theta_pairing ε (F := fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g)
      (G := jfun Ψ' v₀' v') hM1 (dt_memLp hP' v₀' v'), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, jfun, mul_assoc]
  have hC : starRingEnd ℂ (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.conj_ofReal]
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 (datumEmbedding_highest_ne_zero hgap hP hv₀))
  have ex : ((⟨uniformisationL2 ε Ψ' v₀' v', datumEmbedding_mem_smooth hP' v₀' v'⟩ : smD ε (rreg ε)) : L2 ε) = toL2 ε (jfun Ψ' v₀' v') := rfl
  rw [ex]
  show inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε)))) (toL2 ε (jfun Ψ' v₀' v')) ≠ 0
  rw [e1, e2]
  exact mul_ne_zero hC hI

theorem occurrence_phi_smooth_L2 (dual : Bool)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    {η f : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    IsSmoothL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε)) (fun c => ((f c : smD ε (rreg ε)) : L2 ε))) := by
  have hσ := rreg_isURepOn ε
  refine ⟨occA_coef_smooth dual hσ _ _ (fun d => (mem_smD_iff ε (rreg ε) _).1 (f d).2), fun w => ?_⟩
  exact (occA_coef_memLp dual hσ hW η (tensWord dual (smE ε (rreg ε)) w f) hη (occA_tensWord_mem dual w f hf)).ae_eq
    (Filter.Eventually.of_forall fun g => (occA_coef_Eword dual hσ (isDerivedOn_smE hσ) _ w f g.2).symm)

end Psi

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def occPsOK (dual : Bool) (ε : Fin n → Bool) (M M' : Submodule ℂ (smD ε (rreg ε)))
    (ps : (Fin n → smD ε (rreg ε)) →ₗ[ℂ] smD ε (rreg ε)) : Prop :=
  (∀ f ∈ tensSub M, ps f ∈ M') ∧
    (∀ a b, ∀ f ∈ tensSub M, ps (tensF dual (smE ε (rreg ε)) a b f) = smE ε (rreg ε) a b (ps f)) ∧
    ∀ k ∈ Kset ε, ∀ f ∈ tensSub M, ∀ f' ∈ tensSub M,
      (fun c => ((f' c : smD ε (rreg ε)) : L2 ε)) = kDiag dual (rreg ε) k (fun c => ((f c : smD ε (rreg ε)) : L2 ε)) →
      ((ps f' : smD ε (rreg ε)) : L2 ε) = rreg ε k ((ps f : smD ε (rreg ε)) : L2 ε)

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occC_pairing (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hP' : IsPsiFor ε lam' T' Ψ')
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hB : ∃ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) ≠ 0) :
    ∃ η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
          (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) ((x' : smD ε (rreg ε)) : L2 ε) ≠ 0 := by
  exact occurrence_pairing dual hgap hP hv₀ hP' hW hB




theorem occC_exists_ps (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hne : ∃ η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
          (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) ((x' : smD ε (rreg ε)) : L2 ε) ≠ 0) :
    ∃ ps : (Fin n → smD ε (rreg ε)) →ₗ[ℂ] smD ε (rreg ε),
      occPsOK dual ε (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ps ∧
      ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ps f ≠ 0 := by
  obtain ⟨η, hη, f₀, hf₀, x', hx', hne0⟩ := hne
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hsm : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), occC2phi dual ε η f ∈ smD ε (rreg ε) :=
    fun f hf => toL2_mem_smD_of_isSmoothL2 (occurrence_phi_smooth_L2 dual hW hη hf)
  have hsmP : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f) ∈ smD ε (rreg ε) :=
    fun f hf => projection_preserves_smooth hgap' hP' hv₀' _ (hsm f hf)
  let ps0 : tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun f => ⟨(Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f.1), hsmP f.1 f.2⟩
      map_add' := fun f f' => Subtype.ext (by
        show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (f.1 + f'.1)) = _
        rw [occurrence_phi_add dual hW hη f.2 f'.2, map_add]
        rfl)
      map_smul' := fun a f => Subtype.ext (by
        show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (a • f.1)) = _
        rw [occurrence_phi_smul, map_smul]
        rfl) }
  obtain ⟨ps, hps⟩ := LinearMap.exists_extend ps0
  have hpsf : ∀ f (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))),
      ps f = ⟨(Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f), hsmP f hf⟩ :=
    fun f hf => LinearMap.congr_fun hps ⟨f, hf⟩
  refine ⟨ps, ⟨fun f hf => ?_, fun a b f hf => ?_, fun k hk f hf f' hf' hff => ?_⟩, f₀, hf₀, ?_⟩
  · obtain ⟨y, hy, hyeq⟩ := occurrence_projection_mem dual hP hv₀ hgap' hP' hv₀' hW η f hη hf
    have e : ps f = y := by rw [hpsf f hf]; exact Subtype.ext hyeq.symm
    rw [e]; exact hy
  · have hf2 := tensSub_stable dual a b f hf
    rw [hpsf _ hf2, hpsf f hf]
    have h3 := projection_commutes_derived_action hgap' hP' hv₀' (⟨occC2phi dual ε η f, hsm f hf⟩ : smD ε (rreg ε)) (hsmP f hf) a b
    apply Subtype.ext
    refine Eq.trans ?_ h3.symm
    show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (tensF dual (smE ε (rreg ε)) a b f)) =
      (Hlam ε Ψ' v₀').starProjection ((smE ε (rreg ε) a b ⟨occC2phi dual ε η f, hsm f hf⟩ : smD ε (rreg ε)) : L2 ε)
    congr 1
    refine Eq.trans ?_ (rightDerivative_toL2 (occurrence_phi_smooth_L2 dual hW hη hf) a b).symm
    apply toL2_congr_of_forall_inUJ_eq
    intro g hg
    exact (occA_coef_Eab dual hσ hD _ f a b hg).symm
  · rw [hpsf f' hf', hpsf f hf]
    show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f') =
      rreg ε k ((Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f))
    rw [← occurrence_phi_k_equivariant dual η f f' hk hff, projection_commutes_right_regular hgap' hP' hv₀' k (cf_kset_sub hk)]
  · intro h0
    apply hne0
    have hP0 : (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f₀) = 0 := by
      have := congrArg Subtype.val ((hpsf f₀ hf₀).symm.trans h0)
      exact this
    have hx'H : ((x' : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ' v₀' :=
      Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hx')
    rw [← (Submodule.starProjection_eq_self_iff (K := Hlam ε Ψ' v₀')).2 hx'H,
      ← Submodule.inner_starProjection_left_eq_right]
    show inner ℂ ((Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f₀)) _ = 0
    rw [hP0, inner_zero_left]

end Psi

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem occD_genSub_K {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {x : D} (hx : x ∈ genSub E V) :
    ∃ y ∈ genSub E V, (y : H) = σ k (x : H) := by
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hD.glRep hVk hx
  have hf : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hVf m
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk
  have hs := KTypeIsomorphism.orbit_hasSum hσ hD hf (layer_kStable hD.glRep hVk m) hZ ⟨x, hm⟩
  let P : Submodule ℂ H := LinearMap.range (D.subtype ∘ₗ (layer ε E V m).subtype)
  have hmem : σ (NormedSpace.exp Z) (x : H) ∈ P :=
    P.closed_of_finiteDimensional.mem_of_tendsto hs (Filter.Eventually.of_forall fun t =>
      P.sum_mem fun j _ => P.smul_mem _ ⟨_, rfl⟩)
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, layer_le_genSub m w.2, hw⟩

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occD_eeF (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') (s : Fin n)
    (hlam' : lam' = shiftF dual lam s) {ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε))}
    (hι : IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
      (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι) :
    ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      eeF dual (smE ε (rreg ε)) (ι x) = poleF dual lam s • ι x := by
  intro x hx
  have hE := (isDerivedOn_smE (rreg_isURepOn ε)).glRep
  have h1 : casimir (tensF dual (smE ε (rreg ε))) (ι x) = ((casVal lam' : ℝ) : ℂ) • ι x := by
    rw [← map_smul, ← casimir_genSub hE (datumV_casimir hP' v₀') x hx]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [hι.2.2.1 a b _ (tset_genSub_E _ _ b a hx), hι.2.2.1 b a x hx]
  have h2 : casimir (tensF dual (smE ε (rreg ε))) (ι x) = ((casVal lam : ℝ) : ℂ) • ι x + (n : ℂ) • ι x +
      (2 : ℂ) • eeF dual (smE ε (rreg ε)) (ι x) := by
    have h3 : diagOp (casimir (smE ε (rreg ε))) (ι x) = ((casVal lam : ℝ) : ℂ) • ι x := funext fun c => by
      rw [diagOp_coord, casimir_genSub hE (datumV_casimir hP v₀) _ (tset_mem.mp (hι.1 x hx) c)]; rfl
    rw [← h3]
    cases dual
    · exact LinearMap.congr_fun (casimir_tensV hE) _
    · exact LinearMap.congr_fun (casimir_tensVd hE) _
  rw [h1, hlam', ← casVal_shiftF] at h2
  refine smul_right_injective _ (two_ne_zero (α := ℂ)) ?_
  show (2 : ℂ) • _ = (2 : ℂ) • _
  rw [smul_smul, ← add_right_inj (((casVal lam : ℝ) : ℂ) • ι x + (n : ℂ) • ι x), ← h2, ← add_smul, ← add_smul]
  push_cast; rfl

end Psi

end ReciprocityTheory.ChartRestriction.DS
end
end
