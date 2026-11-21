import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.MemLpOfBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapVal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ListProdMemOfForall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotMA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ToL2CongrOnUnitaryBis
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirValueSubSingle
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.SmInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ToL2EqZeroOfEqZeroOnUJset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Imports
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TMapSpec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ThreeAddLeGapBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsCommutingProjectionImage
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Transport

section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace ConjugateTransportSingles

variable {k r : ℕ}

theorem inv_conj (P G : Mat k r) (hP : IsUnit P.det) : (P * G * P⁻¹)⁻¹ = P * G⁻¹ * P⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP, Matrix.mul_assoc]

theorem cJd_transport (P : Mat k r) (hP : IsUnit P.det) (x1 β : Fin (2 * r + k + 1) → ℂ) (G : Mat k r) :
    cJd (P *ᵥ x1) β (P * G * P⁻¹) = (β ᵥ* P) ⬝ᵥ (G⁻¹ *ᵥ x1) := by
  unfold cJd
  rw [inv_conj P G hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ P⁻¹ P,
    Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec, Matrix.dotProduct_mulVec]

theorem cJd_sinv (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (β : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r) (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z)
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    cJd (xJ P z) β (P * (s * x) * P⁻¹) = cJd (xJ P z) β (P * x * P⁻¹) := by
  unfold xJ
  rw [cJd_transport P hP, cJd_transport P hP]
  exact ((mult k r z hz).1 (0 : Fin (2 * r + k + 1) → ℂ) (β ᵥ* P) s hs x hx).2

theorem cJd_single (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (d : Fin (2 * r + k + 1))
    (x : Mat k r) :
    cJd (xJ P z) (Pi.single d 1) (P * x * P⁻¹) = (P *ᵥ (x⁻¹ *ᵥ xOne k r z)) d := by
  unfold xJ
  rw [cJd_transport P hP, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, Pi.single_apply]

theorem tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H) (G : Mat k r) :
    tMapD σ x1 x₀ w (Pi.single d m) G = cJd x1 (Pi.single d 1) G * coefX σ x₀ w m G := by
  unfold tMapD
  rw [Finset.sum_eq_single d]
  · simp
  · intro c _ hc
    simp [Pi.single_eq_of_ne hc, coefX]
  · simp

theorem tMapD_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H) (G : Mat k r) :
    tMapD σ x1 x₀ w f G = ∑ d, tMapD σ x1 x₀ w (Pi.single d (f d)) G := by
  rw [Finset.sum_congr rfl fun d _ => tMapD_single σ x1 x₀ w d (f d) G]
  rfl

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem perI_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    CapelliMinorRestriction.perI P ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =ᵐ[μW.prod μN]
      fun p => (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • CapelliMinorRestriction.perI P ψ π (coefX σ x₀ w m) ξ g p := by
  filter_upwards [CapelliMinorRestriction.ae_S hW hN] with p hp
  simp only [CapelliMinorRestriction.perI]
  rw [tMapD_single, cJd_sinv P hP z hz _ _ g hp hg, cJd_single P hP, mul_smul]

theorem per_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =
      (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • per P μW μN ψ π (coefX σ x₀ w m) ξ g := by
  rw [CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, ← integral_smul]
  exact integral_congr_ae (perI_tMapD_single σ z hz P hP μW μN hW hN ψ π x₀ w d m ξ g hg)

theorem per_add (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F₁ F₂ : Mat k r → ℂ) (ξ : Vp) (x : Mat k r)
    (h₁ : Integrable (CapelliMinorRestriction.perI P ψ π F₁ ξ x) (μW.prod μN))
    (h₂ : Integrable (CapelliMinorRestriction.perI P ψ π F₂ ξ x) (μW.prod μN)) :
    per P μW μN ψ π (fun G => F₁ G + F₂ G) ξ x = per P μW μN ψ π F₁ ξ x + per P μW μN ψ π F₂ ξ x := by
  rw [CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, ← integral_add h₁ h₂]
  congr 1
  funext p
  simp [CapelliMinorRestriction.perI, add_smul]

end ConjugateTransportSingles

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem sum_gamma_nnMinus {M : Type*} [AddCommGroup M] [Module ℂ M] (m : ℕ)
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hQ : Q⁻¹ * Q = 1) (c₀ : ℂ) (j₀ : Fin (m + 1)) (om : ℂ) (v : M) :
    ∑ d, (c₀ * Q⁻¹ d j₀) • Capelli.nnMinus E (Q (Fin.last m)) om v d =
      (c₀ * (-1 : ℂ) ^ (m + (j₀ : ℕ))) •
        Capelli.cminor (frameE Q E) (Fin.last m).succAbove j₀.succAbove om v := by
  have h := congrArg (fun f => f v) (capelliCov (Module.End ℂ M) m E Q⁻¹ Q om hE hQ (Fin.last m) j₀)
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Fin.val_last] at h
  have hF : (fun a b => ∑ c', ∑ d', (Q⁻¹ c' a * Q b d') • E c' d') = frameE Q E := rfl
  rw [hF] at h
  rw [mul_smul, h, Finset.sum_comm, Finset.smul_sum]
  unfold Capelli.nnMinus
  simp_rw [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [add_comm (c : ℕ)]
  ring

theorem gamma_formula {k r : ℕ} (P : Mat k r) (z : Fin (2 * r + k + 1) → ℂ)
    (hTz : 0 < Formalism.QuantumDeterminants.Tz k r z) (g g₀ : Mat k r) (hg₀ : Formalism.MainNotions.S.IsFrameW k r z g₀)
    (hd : IsUnit g₀.det) (hPd : IsUnit P.det) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ d, (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d =
      c₀ * (g₀⁻¹ * g * P⁻¹)⁻¹ d (if r = 0 then Fin.last _ else 0) := by
  have e : (g₀⁻¹ * g * P⁻¹)⁻¹ = P * (g⁻¹ * g₀) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd,
      Matrix.nonsing_inv_nonsing_inv _ hPd]
  have key : ∀ (c₀ : ℂ) (j : Fin (2 * r + k + 1)), g₀ *ᵥ (c₀ • Formalism.QuantumDeterminants.bvec j) = xOne k r z → ∀ d,
      (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d = c₀ * (g₀⁻¹ * g * P⁻¹)⁻¹ d j := fun c₀ j hj d => by
    rw [e, ← hj, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mul_assoc]
    simp [Formalism.QuantumDeterminants.bvec]
  by_cases hr : r = 0
  · refine ⟨_, by exact_mod_cast (Real.sqrt_pos.mpr hTz).ne', key ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) _ ?_⟩
    rw [if_pos hr, xOne, if_pos hr]
    have e2 : Fin.last (2 * r + k) = Formalism.QuantumDeterminants.wI k r (Fin.last k) :=
      Fin.ext (by simp [Formalism.QuantumDeterminants.wI]; omega)
    rw [e2]
    exact hg₀.2.2
  · refine ⟨1, one_ne_zero, key 1 _ ?_⟩
    rw [if_neg hr, xOne, if_neg hr, one_smul]
    exact (hg₀.2.1 ⟨0, Nat.pos_of_ne_zero hr⟩).1

open CapelliMinorRestriction in
theorem evalM : EvalMStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hder hV hcas hK hμ hcoef hp hq hgap hHC hgapl z c Vp _ _ _
    π μW μN P hP hB x₀ w v ξ s g hx₀ hg hu hne
  obtain ⟨g₀, Dk, ψ', hfr, hlU, hψ0, hκ, hlW, hCD⟩ := frameLaw k r ε u lam h H σ D E V T μ ι hσ hder hV hcas
    hK hμ hcoef hp hq hgap hHC hgapl z c Vp π μW μN P hP hB x₀ w ξ g hx₀ hg
  have hPer := per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hgap
  obtain ⟨hWb, hTz, hc, hHCW, hW, hN⟩ := hB
  have hE : IsGlRep E := hder.glRep
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hH2 := ExponentialSlopeDerivatives.hpk_mul_self k r
  have hgd : IsUnit g.det := Matrix.isUnit_det_of_left_inverse (ExponentialSlopeDerivatives.inv_mul_of_UH hH2 hg)
  have hg₀d : IsUnit g₀.det := Matrix.isUnit_det_of_left_inverse (ExponentialSlopeDerivatives.inv_mul_of_UH hH2 hfr.1)
  set Q : Mat k r := g₀⁻¹ * g * P⁻¹ with hQdef
  have hQd : IsUnit Q.det := by
    rw [hQdef, Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det g₀ hg₀d).mul hgd).mul (Matrix.isUnit_nonsing_inv_det P hPd)
  have hQ1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQ2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  set j₀ : Fin (2 * r + k + 1) := if r = 0 then Fin.last _ else 0 with hj₀
  obtain ⟨c₀, hc₀, hβ⟩ := gamma_formula P z hTz g g₀ hfr hg₀d hPd
  rw [← hQdef, ← hj₀] at hβ
  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψdef
  set wH : H := ((w : D) : H) with hwH
  let L : H → Vp := fun m => per P μW μN ψ π (coefX σ x₀ wH m) ξ g
  have hInt : ∀ f : Fin (2 * r + k + 1) → D, (∀ c', f c' ∈ genSub E V) →
      Integrable (perI P ψ π (tMapD σ (xJ P z) x₀ wH (fun c' => ((f c' : D) : H))) ξ g) (μW.prod μN) := by
    intro f hf
    obtain ⟨hsm, -, hbd⟩ := tMapD_spec k r ε lam h H σ D E V T μ ι hσ hder hV hcas hK hμ hcoef hp hq hgap
      hHC hgapl (xJ P z) x₀ w hx₀ f hf
    obtain ⟨C, hC⟩ := hbd []
    exact hPer.1 _ C (cont_of_smoothOnG hsm.1) (fun g' hg' => hC g' hg') g hg ξ
  have hsing : ∀ (d : Fin (2 * r + k + 1)) (m : D),
      (fun c' => (((Pi.single d m : Fin (2 * r + k + 1) → D) c' : D) : H)) = Pi.single d (m : H) := by
    intro d m; funext c'
    by_cases hcd : c' = d
    · subst hcd; simp
    · simp [Pi.single_eq_of_ne hcd]
  have hsingM : ∀ (d : Fin (2 * r + k + 1)) (m : D), m ∈ genSub E V →
      ∀ c', (Pi.single d m : Fin (2 * r + k + 1) → D) c' ∈ genSub E V := by
    intro d m hm c'
    by_cases hcd : c' = d
    · subst hcd; simpa using hm
    · simp [Pi.single_eq_of_ne hcd]
  have hper1 : ∀ (d : Fin (2 * r + k + 1)) (m : H),
      per P μW μN ψ π (tMapD σ (xJ P z) x₀ wH (Pi.single d m)) ξ g = (c₀ * Q⁻¹ d j₀) • L m := by
    intro d m
    rw [ConjugateTransportSingles.per_tMapD_single σ z hWb P hPd μW μN hW hN ψ π x₀ wH d m ξ g hg, hβ d]
  have hIntS : ∀ (d : Fin (2 * r + k + 1)) (m : D), m ∈ genSub E V →
      Integrable (perI P ψ π (tMapD σ (xJ P z) x₀ wH (Pi.single d (m : H))) ξ g) (μW.prod μN) := by
    intro d m hm
    have := hInt _ (hsingM d m hm)
    rwa [hsing] at this
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, Q⁻¹ d₀ j₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have := congrFun (congrFun hQ1 j₀) j₀
    simp [Matrix.mul_apply, hcon] at this
  have hβ0 : c₀ * Q⁻¹ d₀ j₀ ≠ 0 := mul_ne_zero hc₀ hd₀
  have hadd : ∀ m₁ m₂ : D, m₁ ∈ genSub E V → m₂ ∈ genSub E V →
      L ((m₁ : H) + (m₂ : H)) = L m₁ + L m₂ := by
    intro m₁ m₂ h₁ h₂
    refine smul_right_injective Vp hβ0 ?_
    dsimp only
    rw [smul_add, ← hper1, ← hper1, ← hper1]
    have e : tMapD σ (xJ P z) x₀ wH (Pi.single d₀ ((m₁ : H) + (m₂ : H))) = fun G =>
        tMapD σ (xJ P z) x₀ wH (Pi.single d₀ (m₁ : H)) G + tMapD σ (xJ P z) x₀ wH (Pi.single d₀ (m₂ : H)) G := by
      funext G
      simp only [ConjugateTransportSingles.tMapD_single, coefX_add, mul_add]
    rw [e]
    exact per_add P μW μN ψ π _ _ ξ g (hIntS d₀ m₁ h₁) (hIntS d₀ m₂ h₂)
  have hsmul : ∀ (a : ℂ) (m : H), L (a • m) = a • L m := by
    intro a m
    show per P μW μN ψ π (coefX σ x₀ wH (a • m)) ξ g = _
    rw [show coefX σ x₀ wH (a • m) = fun G => a * coefX σ x₀ wH m G from funext (coefX_smul σ x₀ wH m a)]
    exact per_smul P μW μN ψ π _ a ξ g
  let lin : genSub E V →ₗ[ℂ] Vp :=
    { toFun := fun m => L ((m : D) : H)
      map_add' := fun m₁ m₂ => by
        simp only [Submodule.coe_add]
        exact hadd _ _ m₁.2 m₂.2
      map_smul' := fun a m => by
        simp only [Submodule.coe_smul, RingHom.id_apply]
        exact hsmul a _ }
  set om : ℂ := ((-(LemK.thV lam s) : ℝ) : ℂ) with hom
  refine ⟨Q (Fin.last _), ?_⟩
  have hv : (v : D) ∈ genSub E V := le_gen E V v.2
  have hnn : ∀ d, Capelli.nnMinus E (Q (Fin.last _)) om (v : D) d ∈ genSub E V := by
    intro d
    unfold Capelli.nnMinus
    exact Submodule.sum_mem _ fun c' _ => Submodule.smul_mem _ _
      (CapelliMinorMembership.cminor_mem (fun a b x hx => gen_stable E V a b hx) _ _ _ _ hv)
  have hexp : per P μW μN ψ π (tMapD σ (xJ P z) x₀ wH
      (fun c' => ((Capelli.nnMinus E (Q (Fin.last _)) om (v : D) c' : D) : H))) ξ g =
      L (((∑ d, (c₀ * Q⁻¹ d j₀) • Capelli.nnMinus E (Q (Fin.last _)) om (v : D) d : D)) : H) := by
    rw [show tMapD σ (xJ P z) x₀ wH
        (fun c' => ((Capelli.nnMinus E (Q (Fin.last _)) om (v : D) c' : D) : H)) = fun G =>
        ∑ d, tMapD σ (xJ P z) x₀ wH
          (Pi.single d ((Capelli.nnMinus E (Q (Fin.last _)) om (v : D) d : D) : H)) G
        from funext (ConjugateTransportSingles.tMapD_sum σ (xJ P z) x₀ wH _)]
    rw [per_sum P μW μN ψ π Finset.univ _ ξ g (fun d _ => hIntS d _ (hnn d))]
    simp_rw [hper1]
    have hco : (((∑ d, (c₀ * Q⁻¹ d j₀) •
        (⟨_, hnn d⟩ : genSub E V) : genSub E V)) : D) =
        ∑ d, (c₀ * Q⁻¹ d j₀) • Capelli.nnMinus E (Q (Fin.last _)) om (v : D) d := by
      simp
    rw [← hco]
    show _ = lin _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [hexp, sum_gamma_nnMinus (2 * r + k) E hE Q hQ2 c₀ j₀ om (v : D), Submodule.coe_smul, hsmul]
  refine smul_ne_zero (mul_ne_zero hc₀ (pow_ne_zero _ (by norm_num))) ?_
  have hinj : Function.Injective (capIdx k r) := fun a b hab =>
    Fin.ext (by simpa [capIdx] using congrArg Fin.val hab)
  have hS₃ : ∀ a b, ∀ x ∈ genSub E V,
      (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) a b x ∈ genSub E V :=
    fun a b x hx => gen_stable_frame E V Q _ _ hx
  have hfac : ∀ j : Fin k, (om - (r : ℂ)) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2 ≠ 0 := by
    intro j
    have e : (om - (r : ℂ)) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2 = (((u j - lam s + 1 / 2) : ℝ) : ℂ) := by
      simp only [hom, LemK.thV]
      push_cast
      ring
    rw [e, Complex.ofReal_ne_zero]
    intro h0
    exact hu j (by linarith)
  have hvL : lin ⟨(v : D), hv⟩ ≠ 0 := hne
  by_cases hr : r = 0
  · have hj : j₀ = Fin.last _ := by rw [hj₀, if_pos hr]
    rw [hj]
    have hk0 : k + 1 = 2 * r + k + 1 := by omega
    have hinj0 : Function.Injective (Fin.cast hk0) := Fin.cast_injective hk0
    have hS₀ : ∀ a b, ∀ x ∈ genSub E V,
        (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) a b x ∈ genSub E V :=
      fun a b x hx => gen_stable_frame E V Q _ _ hx
    have hD0 : ∀ i j, lin ∘ₗ resE (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) (genSub E V) hS₀
        (Fin.castSucc i) (Fin.castSucc j) = Dk i j ∘ₗ lin := by
      intro i j
      have ei : ∀ i : Fin k, Fin.cast hk0 (Fin.castSucc i) = capIdx k r (Capelli.wIdx k r i) := by
        intro i; apply Fin.ext; simp [capIdx, Capelli.wIdx]; omega
      refine LinearMap.ext fun m => ?_
      have := hlW i j (m : D) m.2
      rw [← ei, ← ei] at this
      exact this
    have hB := Capelli.whittakerZeroStatement (genSub E V) Vp k
      (resE (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) (genSub E V) hS₀) Dk lin om hD0
    have hB' := congrArg (fun f => f (⟨(v : D), hv⟩ : genSub E V)) hB
    simp only [LinearMap.comp_apply] at hB'
    have eC : (Fin.cast hk0 ∘ Fin.castSucc : Fin k → Fin (2 * r + k + 1)) =
        (Fin.last (2 * r + k)).succAbove ∘ Fin.cast (by omega : k = 2 * r + k) := by
      funext i; apply Fin.ext; simp [Fin.succAbove_last]
    have hLHS : L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove
        (Fin.last (2 * r + k)).succAbove om (v : D) : D) : H) =
        lin (Capelli.cminor (resE (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) (genSub E V) hS₀)
          Fin.castSucc Fin.castSucc om ⟨(v : D), hv⟩) := by
      show _ = L (((Capelli.cminor (resE (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) (genSub E V) hS₀)
          Fin.castSucc Fin.castSucc om ⟨(v : D), hv⟩ : genSub E V) : D) : H)
      rw [cminor_resE, cminor_reindex (frameE Q E) (Fin.cast hk0) hinj0, eC, cminor_cast]
    rw [hLHS, hB', hCD]
    refine smul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => ?_) hvL
    have := hfac j
    simpa [hr] using this
  · have hj : j₀ = 0 := by rw [hj₀, if_neg hr]
    rw [hj]
    have hrp : 0 < r := Nat.pos_of_ne_zero hr
    have hl : ∀ a b, Capelli.blk k r a < Capelli.blk k r b →
        lin ∘ₗ resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃ a b = ψ' a b • lin :=
      fun a b hab => LinearMap.ext fun m => hlU a b hab (m : D) m.2
    have hD : ∀ i j, lin ∘ₗ resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃
        (Capelli.wIdx k r i) (Capelli.wIdx k r j) = Dk i j ∘ₗ lin :=
      fun i j => LinearMap.ext fun m => hlW i j (m : D) m.2
    have hGl : IsGlRep (resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃) :=
      isGlRep_resE _ _ _ (isGlRep_reindex (frameE Q E) (capIdx k r) hinj (frameGl Q E hQ1 hQ2 hE))
    have hB := Capelli.capelliB (genSub E V) Vp k r
      (resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃) Dk ψ' lin om hGl hrp
      hl hψ0 hD
    have hB' := congrArg (fun f => f (⟨(v : D), hv⟩ : genSub E V)) hB
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hB'
    have hcast : k + 2 * r = 2 * r + k := by omega
    have eC : (capIdx k r ∘ Fin.castSucc : Fin (k + 2 * r) → Fin (2 * r + k + 1)) =
        (Fin.last (2 * r + k)).succAbove ∘ Fin.cast hcast := by
      funext i; apply Fin.ext; simp [capIdx, Fin.succAbove_last]
    have eS : (capIdx k r ∘ Fin.succ : Fin (k + 2 * r) → Fin (2 * r + k + 1)) =
        (0 : Fin (2 * r + k + 1)).succAbove ∘ Fin.cast hcast := by
      funext i; apply Fin.ext; simp [capIdx, Fin.succAbove_zero]
    have hLHS : L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove
        (0 : Fin (2 * r + k + 1)).succAbove om (v : D) : D) : H) =
        lin (Capelli.cminor (resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃)
          Fin.castSucc Fin.succ om ⟨(v : D), hv⟩) := by
      show _ = L (((Capelli.cminor (resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃)
          Fin.castSucc Fin.succ om ⟨(v : D), hv⟩ : genSub E V) : D) : H)
      rw [cminor_resE, cminor_reindex (frameE Q E) (capIdx k r) hinj, eC, eS, cminor_cast]
    rw [hLHS, hB', hCD]
    exact smul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hκ hrp))
      (smul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hfac j) hvL)

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS TransportMapLinear

theorem quotM : QuotMStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ s x hx₀ hHC' hGap' hx hper
  classical
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  have hmin : 1 ≤ min (pOf ε) (qOf ε) := hq0
  have hp1 : 1 ≤ pOf ε := le_trans hmin (min_le_left _ _)
  have hq1 : 1 ≤ qOf ε := le_trans hmin (min_le_right _ _)
  have hGL : GapLap ε lam h := ⟨hHC.1, hGap, hNeed⟩
  have hstd : StdGap ε (lam - Pi.single s 1) :=
    ⟨hHC'.1, h, hGap', by linarith [LemK.three_add_le_gapBound_dual ε]⟩
  have hE := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hR := rreg_isURepOn ε
  have hDR := isDerivedOn_smE hR
  have hUR : IsInfUnitary ε (smE ε (rreg ε)) := Base.smInfUnitary _ ε (L2 ε) (rreg ε) hR
  set G : Submodule ℂ (Fin (2 * r + k + 1) → D) := Submodule.pi Set.univ (fun _ => genSub E V) with hGdef
  set X : Submodule ℂ (Fin (2 * r + k + 1) → D) := LemK.Xs (LemK.eeVd E) (genSub E V) (LemK.thVd lam s)
    with hXdef
  set L := tMapDL (D := D) σ (xJ P z) x₀ ((w : D) : H) with hLdef
  have hmemG : ∀ f, f ∈ G ↔ ∀ c, f c ∈ genSub E V := fun f => LemK.mem_pi_submodule_iff
  have hXG : X ≤ G := fun f hf => (hmemG f).2 (LemK.mem_euler_eigenspace_iff.1 hf).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => LemK.generated_submodule_stable_under_action V a b hv
  have hGA : ∀ a b, ∀ f ∈ G, LemK.tensVd E a b f ∈ G := fun a b f hf =>
    (hmemG _).2 (LemK.dualTensorAction_mem hGs a b ((hmemG f).1 hf))
  have hXA : ∀ a b, ∀ f ∈ X, LemK.tensVd E a b f ∈ X := fun a b f hf => LemK.euler_eigenspace_stable_under_action hE hGs a b hf
  have hspec := fun (f : Fin (2 * r + k + 1) → D) (hf : f ∈ G) =>
    tMapD_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) x₀ w hx₀ f
      ((hmemG f).1 hf)
  have hsm : ∀ f ∈ G, IsSmoothL2 ε (L f) := fun f hf => (hspec f hf).1
  have hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (LemK.tensVd E a b f) g :=
    fun f hf a b g hg => (hspec f hf).2.1 a b g hg
  obtain ⟨Tl, hTl, hTint⟩ := exists_lin ε (LemK.tensVd E) G L hsm hGA hder
  have hbd : ∀ f ∈ G, ∃ C : ℝ, ∀ g ∈ UJset ε, ‖L f g‖ ≤ C * frob g ^ (1 - aExp ε h) := fun f hf => by
    obtain ⟨C, hC⟩ := (hspec f hf).2.2 []
    exact ⟨C, hC⟩
  have hcont : ∀ f ∈ G, ContinuousOn (L f) (UJset ε) := fun f hf => QuotA.contOn_of_smooth (hsm f hf).1
  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψdef
  let Z : Submodule ℂ (Fin (2 * r + k + 1) → D) :=
    { carrier := {y | y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0}
      add_mem' := by
        rintro y₁ y₂ ⟨h1X, h1⟩ ⟨h2X, h2⟩
        refine ⟨X.add_mem h1X h2X, fun g hg => ?_⟩
        rw [map_add, QuotA.per_add hP hB hp hq hsg (hcont _ (hXG h1X)) (hbd _ (hXG h1X)) (hcont _ (hXG h2X))
          (hbd _ (hXG h2X)) ξ hg, h1 g hg, h2 g hg, add_zero]
      zero_mem' := by
        refine ⟨X.zero_mem, fun g hg => ?_⟩
        have := QuotA.per_smul P μW μN ψ π 0 0 ξ g
        rw [zero_smul, zero_smul] at this
        rw [map_zero, this]
      smul_mem' := by
        rintro a y ⟨hyX, hy⟩
        refine ⟨X.smul_mem a hyX, fun g hg => ?_⟩
        rw [map_smul, QuotA.per_smul, hy g hg, smul_zero] }
  have hmemZ : ∀ y, y ∈ Z ↔ y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0 :=
    fun y => Iff.rfl
  have hZX : Z ≤ X := fun y hy => ((hmemZ y).1 hy).1
  have hZA : ∀ a b, ∀ y ∈ Z, LemK.tensVd E a b y ∈ Z := by
    intro a b y hy
    obtain ⟨hyX, hy0⟩ := (hmemZ y).1 hy
    refine (hmemZ _).2 ⟨hXA a b y hyX, fun g hg => ?_⟩
    rw [← QuotA.per_congr hP hB ψ (fun g' hg' => hder y (hXG hyX) a b g' hg') ξ hg,
      (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hsg).2 (L y) (hsm y (hXG hyX)).1
        (fun wd => (hspec y (hXG hyX)).2.2 wd) a b g hg ξ]
    exact QuotA.eabB_zero hP (fun y' hy' => hy0 y' hy') a b hg
  have hZφ : ∀ y ∈ X, ∀ y' ∈ Z, Tl y = Tl y' → y ∈ Z := by
    intro y hy y' hy' he
    have e := congrArg Subtype.val he
    rw [hTl y (hXG hy), hTl y' (hXG (hZX hy'))] at e
    have hEq := QuotA.eqOn_unitary_of_toL2_eq (hsm y (hXG hy)) (hsm y' (hXG (hZX hy'))) e
    refine (hmemZ y).2 ⟨hy, fun g hg => ?_⟩
    rw [QuotA.per_congr hP hB ψ hEq ξ hg]
    exact ((hmemZ y').1 hy').2 g hg
  have hxZ : x ∉ Z := by
    intro hxZ
    obtain ⟨g, hg, hne⟩ := hper
    exact hne (((hmemZ x).1 hxZ).2 g hg)
  have hkfin : ∀ x' ∈ X, ∃ S : Submodule ℂ (Fin (2 * r + k + 1) → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensVd E) S ∧ x' ∈ S := fun x' hx' => LemK.eigenspace_K_finite hE hV.1 hV.2.1 hx'
  have hK2 := (LemK.k2Vd _ ε lam h H σ D E V s hσ hD hV hc hVK hHC.2 hHC.1 hGL hp1 hq1).2
  have hK3 : ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensVd E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ x' ∈ X, ψ' x' ≠ 0 → ∃ W : Submodule ℂ (smD ε (rreg ε)), W ≤ X.map ψ' ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε (lam - Pi.single s 1)) W ∧
        ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal (lam - Pi.single s 1) : ℂ) • v := by
    intro ψ' hψ' x' hx' hψx'
    exact LemK.k3Vd _ ε lam h H σ D E V s (smD ε (rreg ε)) (smE ε (rreg ε)) ψ' x' hσ hD hV hc hVK hHC.2
      hHC.1 hGL hp1 hq1 hHC'.1 hDR.glRep hUR (fun a b f hf => hψ' a b f ((hmemG f).2 hf)) hx' hψx'
  have hline : ∃ ys ∈ X, ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensVd E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ w' ∈ X.map ψ', IsKHWVec ε (smE ε (rreg ε)) (lowK ε (lam - Pi.single s 1)) w' →
        ∃ c : ℂ, w' = c • ψ' ys := by
    obtain ⟨ys, hys, hl⟩ := line (isKUnitary_of_isInfUnitary hU) X (lowK ε (lam - Pi.single s 1)) hkfin hK2
    exact ⟨ys, hys, fun ψ' hψ' w' hw' hwK =>
      hl _ (smE ε (rreg ε)) ψ' (fun a b _ x' hx' => hψ' a b x' (hXG hx')) w' hw' hwK⟩
  obtain ⟨Y', W, hY'X, hW, hY'Z, hirr, hcas, hK⟩ :=
    QuotA.quot_generic (LemK.tensVd E) G X Z (lam - Pi.single s 1) hstd Tl hXG hTint hK3 hline hkfin hZX hZA
      hZφ hx hxZ
  refine ⟨Y'.map L, W, ?_, ?_, hirr, hcas, hK, ?_⟩
  · rintro F hF
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    exact ⟨y, hY'X hy, rfl⟩
  · intro v
    rw [hW]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨L y, Submodule.mem_map_of_mem hy, hTl y (hXG (hY'X hy))⟩
    · rintro ⟨F, hF, hv⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
      exact ⟨y, hy, Subtype.ext (hv.trans (hTl y (hXG (hY'X hy))).symm)⟩
  · rintro F hF hF0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    have hyZ : y ∈ Z := (hmemZ y).2 ⟨hY'X hy, hF0⟩
    rw [hY'Z y hy hyZ, map_zero]
    intro g _
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

theorem stepDown : StepDownStatement := by
  intro hIS k r ε u h hsg hp hq lam s hHC hGap hHC' hGap' hu hBNZ
  classical
  obtain ⟨T, μ, P, z, c, Vp, _, _, _, π, μW, μN, hμ, hP, hBd, v₁, v₂, ξ, x₀, x, hx₀, hx, hne⟩ := hBNZ
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  obtain ⟨H, _, _, _, σ, D, E, V, ι, hσ, hD, hV, hc, hVK, hcoef⟩ :=
    LemK.psiDatum (2 * r + k + 1) ε lam h T μ hHC hGap hNeed hq0 hμ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  set y₀ : Mat k r := P * x₀ * P⁻¹ with hy₀
  have hy₀J : y₀ ∈ UJset ε := CurveContinuity.inUJ_conj hP hx₀
  have hy₀inv : y₀⁻¹ = P * (x₀⁻¹ * P⁻¹) := by
    rw [hy₀, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hdet]
  set v : V := ι.symm v₁ with hv
  set w : V := ι.symm v₂ with hw

  have hper : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ y₀ ((w : D) : H) ((v : D) : H)) ξ x ≠ 0 := by
    have hcg : ∀ g ∈ UJset ε, coefX σ y₀ ((w : D) : H) ((v : D) : H) g =
        ⟪v₂, S7.PsiM T μ (y₀⁻¹ * g) v₁⟫_ℂ := by
      intro g hg
      have hm : y₀⁻¹ * g ∈ UJset ε := CapelliClosureMembership.inUJ_mul (TDAux.inv_mem hy₀J) hg
      unfold coefX
      rw [hcoef _ hm v w, hv, hw, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [QuotA.per_congr hP hBd _ hcg ξ hx]
    intro h0
    apply hne
    rw [← h0]
    unfold per aaFun
    congr 1
    funext g
    unfold psiCoef
    congr 2
    rw [hy₀inv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, hPP', Matrix.one_mul]
  obtain ⟨β, hβ⟩ := evalM k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp π
    μW μN P hP hBd y₀ w v ξ s x hy₀J hx hu hper

  have hGs : ∀ a b, ∀ m ∈ genSub E V, E a b m ∈ genSub E V := fun a b m hm => LemK.generated_submodule_stable_under_action V a b hm
  have hvG : (v : D) ∈ genSub E V := LemK.le_generatedSubmodule_dual V v.2
  have hC : ∀ m ∈ genSub E V, Capelli.capelliC E (((-(LemK.thV lam s)) : ℝ) : ℂ) m = 0 := by
    intro m hm
    rw [capVal (2 * r + k + 1) ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hHC hGap hNeed hq0 _ m hm]
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by push_cast; ring), zero_smul]
  have hxs : Capelli.nnMinus E β (((-(LemK.thV lam s)) : ℝ) : ℂ) (v : D) ∈
      LemK.Xs (LemK.eeVd E) (genSub E V) (LemK.thVd lam s) := by
    have he := (eig D (2 * r + k) E (genSub E V) (-(LemK.thV lam s)) β β (v : D) hD.glRep hGs hC hvG).2
    have hθ : LemK.thVd lam s = -(LemK.thV lam s) - ((2 * r + k : ℕ) : ℝ) := by
      unfold LemK.thV LemK.thVd
      push_cast
      ring
    rw [hθ]
    exact he
  obtain ⟨Wf, W', hWf, hW', hirr, hcas, hK, hinj⟩ :=
    quotM k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp π μW μN P hP hBd
      y₀ w ξ s _ hy₀J hHC' hGap' hxs ⟨x, hx, hβ⟩
  refine finStep hIS k r ε u (lam - Pi.single s 1) h z c Vp π μW μN P hP hBd hp hq hsg hHC' hGap' ξ Wf W'
    ?_ hW' hirr hcas hK hinj
  intro F hF
  obtain ⟨y, hy, rfl⟩ := hWf F hF
  have hyG : ∀ c', y c' ∈ genSub E V := (LemK.mem_euler_eigenspace_iff.1 hy).1
  have hspec := tMapD_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) y₀ w
    hy₀J y hyG
  exact ⟨QuotA.contOn_of_smooth hspec.1.1, hspec.2.2 []⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

open CapelliMinorRestriction in
theorem evalP : EvalPStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap z c Vp _ _ _ π μW μN P hP hB x₀ w v ξ s g hx₀ hg hu hne
  have hE : IsGlRep E := hD.1
  have hB2 := hB
  unfold IsBData at hB2
  obtain ⟨-, hTz, -, -, hW, hN⟩ := hB2
  have hP2 := hP
  unfold Formalism.MainNotions.S.IsCayley at hP2
  obtain ⟨hPunit, hPJ⟩ := hP2
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPunit
  have hGN := gapNeed k r ε h hp hq hgap
  have hdec := S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hGN.2 hGN.1 hμ
  set a := aExp ε h with ha_def
  have hb : S0.bS k r < a - 1 := CurveContinuity.per_gap hgap
  have hh : 0 ≤ h := by
    have h1 := hgap
    unfold StepGap at h1
    have h2 : (0 : ℝ) < h - 2 := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_left _ _) h1.1)
    linarith
  have ha0 : 0 ≤ a := by
    rw [ha_def]; unfold aExp; positivity
  set S := genSub E V with hS
  have hgood : ∀ f : D, f ∈ S → TmGood ε σ x₀ ((w : D) : H) a ((f : D) : H) :=
    fun f hf => tmC_good_genSub hσ hD hμ hψ ha0 hdec hx₀ w hf
  set ψg := Formalism.MainNotions.S.psiGen k r z c with hψg
  obtain ⟨L, hLdef⟩ : ∃ L : H → Vp, L = fun m => per P μW μN ψg π (coefX σ x₀ ((w : D) : H) m) ξ g :=
    ⟨_, rfl⟩
  have hlin : ∀ m m' : D, m ∈ S → m' ∈ S → ∀ t : ℂ,
      L ((m : H) + t • (m' : H)) = L m + t • L m' := by
    intro m m' hm hm' t
    rw [hLdef]
    exact EvaluationEquivalence.per_lin hP hB hg hb ξ (hgood m hm) (hgood m' hm') t
  have hL0 : L 0 = 0 := by
    have h1 := hlin 0 0 S.zero_mem S.zero_mem 1
    simp only [ZeroMemClass.coe_zero, smul_zero, add_zero, one_smul] at h1
    simpa using h1
  let l : S →ₗ[ℂ] Vp :=
    { toFun := fun m => L ((m : D) : H)
      map_add' := fun m m' => by
        have h1 := hlin m m' m.2 m'.2 1
        simpa using h1
      map_smul' := fun t m => by
        have h1 := hlin 0 m S.zero_mem m.2 t
        simpa [hL0] using h1 }
  have hl : ∀ m : S, l m = L ((m : D) : H) := fun m => rfl

  obtain ⟨g₀, Dk, ψ', hfr, hup, hzero, hkap, hWW, hCD⟩ :=
    frameLaw k r ε u lam h H σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap z c Vp π μW μN P hP hB
      x₀ w ξ g hx₀ hg
  have hfr2 := hfr
  unfold Formalism.MainNotions.S.IsFrameW at hfr2
  have hg₀u : IsUnit g₀.det := TransportGeo.uh_det hfr2.1
  have hgu : IsUnit g.det := TransportGeo.uh_det hg
  set Q : Mat k r := g₀⁻¹ * g * P⁻¹ with hQdef
  have hQu : IsUnit Q.det := by
    rw [hQdef, Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det _ hg₀u).mul hgu).mul (Matrix.isUnit_nonsing_inv_det _ hPu)
  have hQQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  have hQQ' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
  have hgQ : g * P⁻¹ = g₀ * Q := by
    rw [hQdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hg₀u, Matrix.one_mul]
  obtain ⟨c₀, hc₀, hcJ⟩ := CapelliMinorRestriction.beta_formula ε P hPJ z hTz g g₀ Q hfr hgQ
  have hSE : ∀ a' b', ∀ x ∈ S, E a' b' x ∈ S := fun a' b' x hx => CapelliMinorRestriction.gen_stable E V a' b' hx
  have hSF : ∀ a' b', ∀ x ∈ S, frameE Q E a' b' x ∈ S :=
    fun a' b' x hx => CapelliMinorRestriction.gen_stable_frame E V Q a' b' hx
  have hvS : (v : D) ∈ S := CapelliMinorRestriction.le_gen E V v.2
  have hcontT : ∀ (x1 : Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → D), (∀ c', f c' ∈ S) →
      ContinuousOn (tMap ε σ x1 x₀ ((w : D) : H) (fun c' => ((f c' : D) : H))) (UJset ε) := by
    intro x1 f hf
    unfold tMap
    apply continuousOn_finset_sum
    intro c' _
    apply ContinuousOn.mul
    · rw [← tmD_cJL_coe]
      exact (tmD_cJL ε x1 (Pi.single c' 1)).continuous.continuousOn
    · exact CapelliMinorRestriction.cont_of_smoothOnG (hgood _ (hf c')).1
  have hintT : ∀ f : Fin (2 * r + k + 1) → D, (∀ c', f c' ∈ S) →
      Integrable (CapelliMinorRestriction.perI P ψg π (tMap ε σ (xJ P z) x₀ ((w : D) : H) (fun c' => ((f c' : D) : H))) ξ g)
        (μW.prod μN) := by
    intro f hf
    obtain ⟨C, hC⟩ := (tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap
      (xJ P z) x₀ w hx₀ f hf).2.2 []
    exact CurveContinuity.int_of_bound hP hB hg ξ a hb _ (hcontT _ f hf) C hC

  set om : ℂ := ((-(LemK.thV lam s) : ℝ) : ℂ) with hom
  have hcmS : ∀ (p : ℕ) (R C : Fin p → Fin (2 * r + k + 1)) (t : ℂ),
      Capelli.cminor (frameE Q E) R C t (v : D) ∈ S :=
    fun p R C t => CapelliMinorMembership.cminor_mem hSF R C t _ hvS
  have key : ∀ j₀ : Fin (2 * r + k + 1),
      per P μW μN ψg π (tMap ε σ (xJ P z) x₀ ((w : D) : H)
        (fun c' => ((Capelli.nnPlus E (Q⁻¹ *ᵥ Pi.single j₀ 1) om (v : D) c' : D) : H))) ξ g =
      (c₀ * (-1 : ℂ) ^ (2 * r + k + (j₀ : ℕ))) •
        L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D) : D) : H) := by
    intro j₀
    set y := Q⁻¹ *ᵥ Pi.single j₀ 1 with hy
    have hnnS : ∀ d, Capelli.nnPlus E y om (v : D) d ∈ S := by
      intro d
      unfold Capelli.nnPlus
      apply Submodule.sum_mem
      intro c' _
      exact S.smul_mem _ (CapelliMinorMembership.cminor_mem hSE _ _ _ _ hvS)
    set F : Fin (2 * r + k + 1) → Mat k r → ℂ := fun d =>
      tMap ε σ (xJ P z) x₀ ((w : D) : H) (Pi.single d ((Capelli.nnPlus E y om (v : D) d : D) : H)) with hF
    have hsing : ∀ d, Pi.single d ((Capelli.nnPlus E y om (v : D) d : D) : H) =
        fun c' => (((Pi.single d (Capelli.nnPlus E y om (v : D) d) : Fin (2 * r + k + 1) → D) c' : D) : H) := by
      intro d
      funext c'
      by_cases hc : c' = d
      · subst hc; simp
      · simp [Pi.single_eq_of_ne hc]
    have hint : ∀ d ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))),
        Integrable (CapelliMinorRestriction.perI P ψg π (F d) ξ g) (μW.prod μN) := by
      intro d _
      simp only [hF]
      rw [hsing d]
      apply hintT
      intro c'
      by_cases hc : c' = d
      · subst hc; simpa using hnnS c'
      · simp [Pi.single_eq_of_ne hc]
    have hfs : tMap ε σ (xJ P z) x₀ ((w : D) : H)
        (fun c' => ((Capelli.nnPlus E y om (v : D) c' : D) : H)) = fun G => ∑ d ∈ Finset.univ, F d G :=
      funext fun G => CapelliMinorRestriction.tMap_sum ε σ (xJ P z) x₀ ((w : D) : H) _ G
    rw [hfs, CapelliMinorRestriction.per_sum P μW μN ψg π Finset.univ F ξ g hint]
    rw [Finset.sum_congr rfl (fun d _ => CapelliMinorRestriction.per_tMap_single ε σ z P hPJ μW μN hW hN ψg π x₀ ((w : D) : H) d
      ((Capelli.nnPlus E y om (v : D) d : D) : H) ξ g)]
    simp only [hcJ]
    have hsumS : (∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • (⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ : S)) =
        (c₀ * (-1 : ℂ) ^ (2 * r + k + (j₀ : ℕ))) •
          (⟨Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D),
            hcmS _ _ _ _⟩ : S) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      exact CapelliMinorRestriction.sum_beta_nnPlus (2 * r + k) E hE Q hQQ c₀ j₀ om (v : D)
    have h1 : ∀ d, per P μW μN ψg π (coefX σ x₀ ((w : D) : H) ((Capelli.nnPlus E y om (v : D) d : D) : H)) ξ g =
        l ⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ := by
      intro d; rw [hl, hLdef]
    simp only [h1]
    calc ∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • l ⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩
        = l (∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • (⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ : S)) := by
          rw [map_sum]; simp only [map_smul]
      _ = _ := by rw [hsumS, map_smul]; rfl

  have hfac : ∀ j, (om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2) ≠ 0 := by
    intro j
    have e : om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2 = ((u j - (lam s + 1 / 2) : ℝ) : ℂ) := by
      rw [hom]; unfold LemK.thV; push_cast; ring
    rw [e, Complex.ofReal_ne_zero, sub_ne_zero]; exact hu j
  have hprod : (∏ j : Fin k, (om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hfac j
  have hlv : l ⟨(v : D), hvS⟩ ≠ 0 := by
    rw [hl, hLdef]; exact hne
  have hFE : IsGlRep (frameE Q E) := CapelliMinorRestriction.frameGl Q E hQQ' hQQ hE
  have hRE : IsGlRep (CapelliMinorRestriction.resE (frameE Q E) S hSF) := CapelliMinorRestriction.isGlRep_resE (frameE Q E) S hSF hFE
  have hres : ∀ (R C : Fin (2 * r + k) → Fin (2 * r + k + 1)) (x : ℂ),
      l (Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) R C x ⟨(v : D), hvS⟩) =
        L ((Capelli.cminor (frameE Q E) R C x (v : D) : D) : H) := by
    intro R C x
    rw [hl, CapelliMinorRestriction.cminor_resE]
  have hnz : ∃ j₀ : Fin (2 * r + k + 1),
      L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D) : D) : H) ≠ 0 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · refine ⟨Fin.last (2 * r + k), ?_⟩
      have hkn : k = 2 * r + k := by omega
      obtain ⟨e, he_def⟩ : ∃ e : Fin (k + 1) → Fin (2 * r + k + 1), e = Fin.cast (by omega) := ⟨_, rfl⟩
      have he : Function.Injective e := fun a' b' hab => by
        rw [he_def] at hab; exact Fin.cast_injective _ hab
      have hWW' : ∀ i j, l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b'))
          (Fin.castSucc i) (Fin.castSucc j) = Dk i j ∘ₗ l := by
        intro i j
        apply LinearMap.ext
        intro m
        have hi : e (Fin.castSucc i) = capIdx k r (Capelli.wIdx k r i) :=
          Fin.ext (by simp [he_def, capIdx, Capelli.wIdx, hr])
        have hj : e (Fin.castSucc j) = capIdx k r (Capelli.wIdx k r j) :=
          Fin.ext (by simp [he_def, capIdx, Capelli.wIdx, hr])
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (e (Fin.castSucc i)) (e (Fin.castSucc j)) m : S) : D) : H) =
          Dk i j (L ((m : D) : H))
        rw [hi, hj, hLdef]
        exact hWW i j m m.2
      have hB0 := Capelli.whittakerZeroStatement S Vp k (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b')) Dk l
        (om - 1) hWW'
      have hcm : Capelli.cminor (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b'))
          Fin.castSucc Fin.castSucc (om - 1) =
          Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn)
            ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn) (om - 1) := by
        rw [CapelliMinorRestriction.cminor_reindex _ e he]
        congr 1 <;> funext i <;> exact Fin.ext (by simp [he_def, Fin.succAbove_last])
      rw [CapelliMinorRestriction.cminor_cast _ hkn] at hcm
      have h1 := LinearMap.congr_fun hB0 ⟨(v : D), hvS⟩
      simp only [LinearMap.comp_apply] at h1
      rw [hcm, hCD, hres] at h1
      rw [h1]
      have hprod0 : (∏ j : Fin k, (om - 1 + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) ≠ 0 := by
        simpa [hr] using hprod
      exact smul_ne_zero hprod0 hlv
    · refine ⟨0, ?_⟩
      have hkn : k + 2 * r = 2 * r + k := by omega
      have hcapinj : Function.Injective (capIdx k r) := fun a' b' hab => by
        unfold capIdx at hab; exact Fin.cast_injective _ hab
      have hup' : ∀ a' b', Capelli.blk k r a' < Capelli.blk k r b' →
          l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b')) a' b' =
            ψ' a' b' • l := by
        intro a' b' hab
        apply LinearMap.ext
        intro m
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b') m : S) : D) : H) =
          ψ' a' b' • L ((m : D) : H)
        rw [hLdef]
        exact hup a' b' hab m m.2
      have hWW' : ∀ i j, l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b'))
          (Capelli.wIdx k r i) (Capelli.wIdx k r j) = Dk i j ∘ₗ l := by
        intro i j
        apply LinearMap.ext
        intro m
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) m :
          S) : D) : H) = Dk i j (L ((m : D) : H))
        rw [hLdef]
        exact hWW i j m m.2
      have hB1 := Capelli.capelliB S Vp k r
        (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b')) Dk ψ' l (om - 1)
        (CapelliMinorRestriction.isGlRep_reindex _ (capIdx k r) hcapinj hRE) hr hup' hzero hWW'
      have hcm : Capelli.cminor (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b'))
          Fin.castSucc Fin.succ (om - 1) =
          Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn)
            ((0 : Fin (2 * r + k + 1)).succAbove ∘ Fin.cast hkn) (om - 1) := by
        rw [CapelliMinorRestriction.cminor_reindex _ (capIdx k r) hcapinj]
        congr 1 <;> funext i <;> exact Fin.ext (by simp [capIdx, Fin.succAbove_last])
      rw [CapelliMinorRestriction.cminor_cast _ hkn] at hcm
      have h1 := LinearMap.congr_fun hB1 ⟨(v : D), hvS⟩
      simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h1
      rw [hcm, hCD, hres] at h1
      rw [h1]
      exact smul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hkap hr)) (smul_ne_zero hprod hlv)
  obtain ⟨j₀, hj₀⟩ := hnz
  refine ⟨Q⁻¹ *ᵥ Pi.single j₀ 1, ?_⟩
  rw [key j₀]
  exact smul_ne_zero (mul_ne_zero hc₀ (pow_ne_zero _ (by norm_num))) hj₀

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
noncomputable section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

section Map

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tL (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f f' := by
    funext g
    simp only [tMap, coefX, Pi.add_apply, Submodule.coe_add, map_add, inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [tMap, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

end Map

section Hull

variable {n : ℕ} {ε : Fin n → Bool} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem exists_kStable_finiteDimensional_submodule_of_mem_Xs (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {θ : ℝ}
    {x : Fin n → M} (hx : x ∈ Xs (LemK.eeV E) (genSub E V) θ) :
    ∃ S : Submodule ℂ (Fin n → M), S ≤ Xs (LemK.eeV E) (genSub E V) θ ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensV E) S ∧ x ∈ S := by
  classical
  have hxg := (mem_eigenTensorSpace_gen_iff.1 hx).1
  choose m hm using fun c => exists_layer_of_mem_genSub hE hVk (hxg c)
  set K := Finset.univ.sup m
  have hxK : ∀ c, x c ∈ layer ε E V K := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hfdL : FiniteDimensional ℂ (layer ε E V K) := finiteDimensional_layer hVfd K
  have hLk := layer_kStable hE hVk K
  have := pi_submodule_finiteDimensional (n := n) (layer ε E V K)
  refine ⟨Submodule.pi Set.univ (fun _ => layer ε E V K) ⊓ Xs (LemK.eeV E) (genSub E V) θ, inf_le_right,
    Submodule.finiteDimensional_of_le inf_le_left, ?_, ⟨mem_pi_submodule_iff.2 hxK, hx⟩⟩
  intro a b hab f hf
  refine ⟨mem_pi_submodule_iff.2 fun c => ?_, eigenTensorSpace_stable hE a b hf.2⟩
  rw [entry_bounds_of_partialSum]
  refine add_mem (hLk a b hab _ (mem_pi_submodule_iff.1 hf.1 c)) ?_
  split_ifs
  · exact mem_pi_submodule_iff.1 hf.1 b
  · exact zero_mem _

end Hull

section Line

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D}

theorem line_V (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hmono : StrictAnti lam) (hGL : GapLap ε lam h)
    (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (s : Fin n) {N : Type*} [AddCommGroup N] [Module ℂ N]
    (EN : Fin n → Fin n → Module.End ℂ N) :
    ∃ ys ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' → ∃ c : ℂ, w' = c • ψ ys := by
  classical
  have hK2 := (k2V n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hGL hp hq).2
  have hKD : IsKUnitary ε E := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hE : IsGlRep E := hD.glRep
  have hXG : ∀ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ∈ Submodule.pi Set.univ (fun _ => genSub E V) :=
    fun y hy => by simpa [Submodule.mem_pi] using (mem_eigenTensorSpace_gen_iff.1 hy).1

  have hlift : ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' →
        ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y ∧
          ψ y = w' := by
    intro ψ hψ w' hw' hw'K
    obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.1 hw'
    obtain ⟨S, hSX, hfd, hSk, hy₀S⟩ := exists_kStable_finiteDimensional_submodule_of_mem_Xs hE hV.1 hV.2.1 hy₀
    obtain ⟨y, hyS, hyK, hyeq⟩ := partialSum_succ_alt hKD ψ hfd hSk (fun a b _ z hz => hψ a b z (hXG z (hSX hz)))
      hy₀S hw'K
    exact ⟨y, hSX hyS, hyK, hyeq⟩
  by_cases hex : ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ≠ 0 ∧
      IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y
  · obtain ⟨ys, hysX, hys0, hysK⟩ := hex
    refine ⟨ys, hysX, fun ψ hψ w' hw' hw'K => ?_⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    obtain ⟨c₁, c₂, hne, hrel⟩ := hK2 y ys hyX hysX hyK hysK
    by_cases hc1 : c₁ = 0
    · exfalso
      rw [hc1, zero_smul, zero_add] at hrel
      exact hys0 ((smul_eq_zero.1 hrel).resolve_left (hne.resolve_left (not_not.2 hc1)))
    · refine ⟨-(c₁⁻¹ * c₂), ?_⟩
      have h2 : c₁ • y = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hrel
      have hy : y = -(c₁⁻¹ * c₂) • ys := by
        calc y = c₁⁻¹ • (c₁ • y) := by rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
          _ = -(c₁⁻¹ * c₂) • ys := by rw [h2, smul_neg, smul_smul, neg_smul]
      rw [hy, map_smul]
  · refine ⟨0, zero_mem _, fun ψ hψ w' hw' hw'K => ⟨0, ?_⟩⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    have hy0 : y = 0 := by
      by_contra hy0
      exact hex ⟨y, hyX, hy0, hyK⟩
    rw [hy0, map_zero, zero_smul]

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS TransportMapLinear

theorem quotP : QuotPStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ s x hx₀ hHC' hGap' hx hper
  classical
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  have hmin : 1 ≤ min (pOf ε) (qOf ε) := hq0
  have hp1 : 1 ≤ pOf ε := le_trans hmin (min_le_left _ _)
  have hq1 : 1 ≤ qOf ε := le_trans hmin (min_le_right _ _)
  have hGL : GapLap ε lam h := ⟨hHC.1, hGap, hNeed⟩
  have hstd : StdGap ε (lam + Pi.single s 1) :=
    ⟨hHC'.1, h, hGap', by linarith [LemK.three_add_le_gapBound ε]⟩
  have hE := hD.glRep
  have hR := rreg_isURepOn ε
  have hDR := isDerivedOn_smE hR
  have hUR : IsInfUnitary ε (smE ε (rreg ε)) := Base.smInfUnitary _ ε (L2 ε) (rreg ε) hR
  set G : Submodule ℂ (Fin (2 * r + k + 1) → D) := Submodule.pi Set.univ (fun _ => genSub E V) with hGdef
  set X : Submodule ℂ (Fin (2 * r + k + 1) → D) := LemK.Xs (LemK.eeV E) (genSub E V) (LemK.thV lam s)
    with hXdef
  set L := QuotA.tL (D := D) ε σ (xJ P z) x₀ ((w : D) : H) with hLdef
  have hmemG : ∀ f, f ∈ G ↔ ∀ c, f c ∈ genSub E V := fun f => LemK.mem_pi_submodule_iff
  have hXG : X ≤ G := fun f hf => (hmemG f).2 (LemK.mem_eigenTensorSpace_gen_iff.1 hf).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => LemK.generated_submodule_stable_under_action V a b hv
  have hGA : ∀ a b, ∀ f ∈ G, LemK.tensV E a b f ∈ G := fun a b f hf => by
    refine (hmemG _).2 fun c' => ?_
    rw [LemK.entry_bounds_of_partialSum]
    refine add_mem (hGs a b _ ((hmemG f).1 hf c')) ?_
    split_ifs
    · exact (hmemG f).1 hf b
    · exact zero_mem _
  have hXA : ∀ a b, ∀ f ∈ X, LemK.tensV E a b f ∈ X := fun a b f hf => LemK.eigenTensorSpace_stable hE a b hf
  have hspec := fun (f : Fin (2 * r + k + 1) → D) (hf : f ∈ G) =>
    tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) x₀ w hx₀ f
      ((hmemG f).1 hf)
  have hsm : ∀ f ∈ G, IsSmoothL2 ε (L f) := fun f hf => (hspec f hf).1
  have hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (LemK.tensV E a b f) g :=
    fun f hf a b g hg => (hspec f hf).2.1 a b g hg
  obtain ⟨Tl, hTl, hTint⟩ := exists_lin ε (LemK.tensV E) G L hsm hGA hder
  have hbd : ∀ f ∈ G, ∃ C : ℝ, ∀ g ∈ UJset ε, ‖L f g‖ ≤ C * frob g ^ (1 - aExp ε h) := fun f hf => by
    obtain ⟨C, hC⟩ := (hspec f hf).2.2 []
    exact ⟨C, hC⟩
  have hcont : ∀ f ∈ G, ContinuousOn (L f) (UJset ε) := fun f hf => QuotA.contOn_of_smooth (hsm f hf).1
  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψdef
  let Z : Submodule ℂ (Fin (2 * r + k + 1) → D) :=
    { carrier := {y | y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0}
      add_mem' := by
        rintro y₁ y₂ ⟨h1X, h1⟩ ⟨h2X, h2⟩
        refine ⟨X.add_mem h1X h2X, fun g hg => ?_⟩
        rw [map_add, QuotA.per_add hP hB hp hq hsg (hcont _ (hXG h1X)) (hbd _ (hXG h1X)) (hcont _ (hXG h2X))
          (hbd _ (hXG h2X)) ξ hg, h1 g hg, h2 g hg, add_zero]
      zero_mem' := by
        refine ⟨X.zero_mem, fun g hg => ?_⟩
        have := QuotA.per_smul P μW μN ψ π 0 0 ξ g
        rw [zero_smul, zero_smul] at this
        rw [map_zero, this]
      smul_mem' := by
        rintro a y ⟨hyX, hy⟩
        refine ⟨X.smul_mem a hyX, fun g hg => ?_⟩
        rw [map_smul, QuotA.per_smul, hy g hg, smul_zero] }
  have hmemZ : ∀ y, y ∈ Z ↔ y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0 :=
    fun y => Iff.rfl
  have hZX : Z ≤ X := fun y hy => ((hmemZ y).1 hy).1
  have hZA : ∀ a b, ∀ y ∈ Z, LemK.tensV E a b y ∈ Z := by
    intro a b y hy
    obtain ⟨hyX, hy0⟩ := (hmemZ y).1 hy
    refine (hmemZ _).2 ⟨hXA a b y hyX, fun g hg => ?_⟩
    rw [← QuotA.per_congr hP hB ψ (fun g' hg' => hder y (hXG hyX) a b g' hg') ξ hg,
      (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hsg).2 (L y) (hsm y (hXG hyX)).1
        (fun wd => (hspec y (hXG hyX)).2.2 wd) a b g hg ξ]
    exact QuotA.eabB_zero hP (fun y' hy' => hy0 y' hy') a b hg
  have hZφ : ∀ y ∈ X, ∀ y' ∈ Z, Tl y = Tl y' → y ∈ Z := by
    intro y hy y' hy' he
    have e := congrArg Subtype.val he
    rw [hTl y (hXG hy), hTl y' (hXG (hZX hy'))] at e
    have hEq := QuotA.eqOn_unitary_of_toL2_eq (hsm y (hXG hy)) (hsm y' (hXG (hZX hy'))) e
    refine (hmemZ y).2 ⟨hy, fun g hg => ?_⟩
    rw [QuotA.per_congr hP hB ψ hEq ξ hg]
    exact ((hmemZ y').1 hy').2 g hg
  have hxZ : x ∉ Z := by
    intro hxZ
    obtain ⟨g, hg, hne⟩ := hper
    exact hne (((hmemZ x).1 hxZ).2 g hg)
  have hkfin : ∀ x' ∈ X, ∃ S : Submodule ℂ (Fin (2 * r + k + 1) → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensV E) S ∧ x' ∈ S := fun x' hx' => QuotA.exists_kStable_finiteDimensional_submodule_of_mem_Xs hE hV.1 hV.2.1 hx'
  have hK3 : ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensV E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ x' ∈ X, ψ' x' ≠ 0 → ∃ W : Submodule ℂ (smD ε (rreg ε)), W ≤ X.map ψ' ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε (lam + Pi.single s 1)) W ∧
        ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal (lam + Pi.single s 1) : ℂ) • v := by
    intro ψ' hψ' x' hx' hψx'
    exact LemK.k3V _ ε lam h H σ D E V s (smD ε (rreg ε)) (smE ε (rreg ε)) ψ' x' hσ hD hV hc hVK hHC.2
      hHC.1 hGL hp1 hq1 hHC'.1 hDR.glRep hUR (fun a b f hf => hψ' a b f ((hmemG f).2 hf)) hx' hψx'
  have hline : ∃ ys ∈ X, ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensV E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ w' ∈ X.map ψ', IsKHWVec ε (smE ε (rreg ε)) (lowK ε (lam + Pi.single s 1)) w' →
        ∃ c : ℂ, w' = c • ψ' ys :=
    QuotA.line_V hσ hD hV hc hVK hHC.2 hHC.1 hGL hp1 hq1 s (smE ε (rreg ε))
  obtain ⟨Y', W, hY'X, hW, hY'Z, hirr, hcas, hK⟩ :=
    QuotA.quot_generic (LemK.tensV E) G X Z (lam + Pi.single s 1) hstd Tl hXG hTint hK3 hline hkfin hZX hZA
      hZφ hx hxZ
  refine ⟨Y'.map L, W, ?_, ?_, hirr, hcas, hK, ?_⟩
  · rintro F hF
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    exact ⟨y, hY'X hy, rfl⟩
  · intro v
    rw [hW]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨L y, Submodule.mem_map_of_mem hy, hTl y (hXG (hY'X hy))⟩
    · rintro ⟨F, hF, hv⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
      exact ⟨y, hy, Subtype.ext (hv.trans (hTl y (hXG (hY'X hy))).symm)⟩
  · rintro F hF hF0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    have hyZ : y ∈ Z := (hmemZ y).2 ⟨hY'X hy, hF0⟩
    rw [hY'Z y hy hyZ, map_zero]
    intro g _
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem stepUp : StepUpStatement := by
  intro hIS k r ε u h hgap hp hq lam s hlam hgl hlam' hgl' hu hB
  classical
  obtain ⟨T, μ, P, z, c, Vp, _, _, _, π, μW, μN, hμ, hP, hBD, v₁, v₂, ξ, x₀, x, hx₀, hx, hne⟩ := hB
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hgap
  obtain ⟨H, _, _, _, σ, D, E, V, ι, hσ, hD, hV, hc, hVK, hcoef⟩ :=
    LemK.psiDatum (2 * r + k + 1) ε lam h T μ hlam hgl hNeed hq0 hμ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hX₀ : P * x₀ * P⁻¹ ∈ UJset ε := cayley_conj_mem_unitary_group hP hx₀
  have hper : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
      (coefX σ (P * x₀ * P⁻¹) (((ι.symm v₂ : V) : D) : H) (((ι.symm v₁ : V) : D) : H)) ξ x =
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x := by
    have hHW := hBD.2.2.2.2.1
    have hHN := hBD.2.2.2.2.2
    have : SigmaFinite μW := hHW.1
    have : SigmaFinite μN := hHN.1
    unfold per aaFun sInt
    apply integral_congr_ae
    filter_upwards [ae_mem_unitary_nilpotent_product z μW μN hHW hHN] with p hp'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      unitary_hermitian_form_mul_mem hp'.1.1 hp'.2.1
    have hg := unitary_hermitian_form_mul_mem hs hx
    have hinv : x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := (Transport.uh_facts hP hx₀).2.1
    have hG : P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹ ∈ UJset ε :=
      cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem hinv hg)
    have hX : P⁻¹ * (P * x₀ * P⁻¹) * P = x₀ := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
        Matrix.mul_one]
    have heq : (P * x₀ * P⁻¹)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) =
        P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹ := by
      have h1 := conj_inv_mul_conj P (P * x₀ * P⁻¹) (Matrix.of p.1 * Matrix.of p.2 * x) hd
      rw [hX] at h1
      exact h1.symm
    show coefX σ (P * x₀ * P⁻¹) _ _ (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • _ =
      psiCoef T μ P v₁ v₂ (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) • _
    unfold coefX psiCoef
    rw [heq, hcoef _ hG (ι.symm v₁) (ι.symm v₂)]
    simp only [LinearEquiv.apply_symm_apply]
  have hne' : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
      (coefX σ (P * x₀ * P⁻¹) (((ι.symm v₂ : V) : D) : H) (((ι.symm v₁ : V) : D) : H)) ξ x ≠ 0 := by
    rw [hper]; exact hne
  obtain ⟨y, hy⟩ := evalP k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hgap hlam hgl z c Vp π
    μW μN P hP hBD (P * x₀ * P⁻¹) (ι.symm v₂) (ι.symm v₁) ξ s x hX₀ hx hu hne'
  have hGl : IsGlRep E := hD.glRep
  have hstab : ∀ a b, ∀ m ∈ genSub E V, E a b m ∈ genSub E V := fun a b m hm =>
    Submodule.mem_sInf.2 fun S hS => hS.2 a b m (Submodule.mem_sInf.1 hm S hS)
  have hkill : ∀ m ∈ genSub E V, Capelli.capelliC E (((-(LemK.thV lam s)) : ℝ) : ℂ) m = 0 := by
    intro m hm
    rw [capVal (2 * r + k + 1) ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hlam hgl hNeed hq0 _ m hm,
      Finset.prod_eq_zero (Finset.mem_univ s) (by push_cast; ring), zero_smul]
  have hvS : (((ι.symm v₁ : V) : D)) ∈ genSub E V :=
    Submodule.mem_sInf.2 fun S hS => hS.1 (ι.symm v₁).2
  have hXs := (eig D (2 * r + k) E (genSub E V) (-(LemK.thV lam s)) y y ((ι.symm v₁ : V) : D) hGl hstab
    hkill hvS).1
  rw [neg_neg] at hXs
  obtain ⟨Wf, W', hWf, hW', hirr, hcas, hK, hinj⟩ := quotP k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ
    hcoef hp hq hgap hlam hgl z c Vp π μW μN P hP hBD (P * x₀ * P⁻¹) (ι.symm v₂) ξ s
    (Capelli.nnPlus E y (((-(LemK.thV lam s)) : ℝ) : ℂ) ((ι.symm v₁ : V) : D)) hX₀ hlam' hgl' hXs ⟨x, hx, hy⟩
  refine finStep hIS k r ε u (lam + Pi.single s 1) h z c Vp π μW μN P hP hBD hp hq hgap hlam' hgl' ξ Wf W'
    ?_ hW' hirr hcas hK hinj
  intro F hF
  obtain ⟨y', hy', rfl⟩ := hWf F hF
  have hyS : ∀ c', y' c' ∈ genSub E V := fun c' =>
    (Submodule.mem_pi.1 (Submodule.mem_inf.1 hy').1) c' (Set.mem_univ _)
  obtain ⟨hsm, -, hbd⟩ := tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hgap hlam hgl
    (xJ P z) (P * x₀ * P⁻¹) (ι.symm v₂) hX₀ y' hyS
  obtain ⟨C, hC⟩ := hbd []
  exact ⟨CapelliMinorRestriction.cont_of_smoothOnG hsm.1, C, hC⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem step : StepStatement := by
  intro hIS k r ε u h hg hp hq
  exact ⟨stepDown hIS k r ε u h hg hp hq, stepUp hIS k r ε u h hg hp hq⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
