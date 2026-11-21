import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

section Herm

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

def HermDatum.hodgeVec (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Em) →+ EuclideanSpace ℂ (Ψ × Fin N) where
  toFun v := WithLp.toLp 2 fun p =>
    (Real.sqrt (2 * ‖A.emb p.1 A.ξ‖) : ℂ) * ((P p.1)⁻¹ *ᵥ fun a => A.emb p.1 (v a)) p.2
  map_zero' := by
    ext p
    have h0 : (fun a => A.emb p.1 ((0 : Fin N → Em) a)) = 0 := by
      ext
      simp
    simp only [h0]
    simp
  map_add' v w := by
    ext p
    have h0 : (fun a => A.emb p.1 ((v + w) a)) = (fun a => A.emb p.1 (v a)) + fun a => A.emb p.1 (w a) := by
      ext
      simp
    simp only [h0]
    simp [Matrix.mulVec_add, mul_add]

def HermDatum.hodgeLen (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) (v : Fin N → Em) : ℝ :=
  ‖A.hodgeVec P v‖

end Herm

variable (Em : Type) [Field Em] [NumberField Em] in

def IsConjRadius (vr : ℝ) : Prop :=
  ∃ s : Finset (𝓞 Em), Submodule.span ℚ ((fun α : 𝓞 Em => (α : Em)) '' (s : Set (𝓞 Em))) = ⊤ ∧
    ∀ α ∈ s, ∀ σ : Em →+* ℂ, ‖σ (α : Em)‖ ≤ vr

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def hodgeLen (z : (Σ k, ι k) → ℂ) (v : Fin D.N → Em) : ℝ :=
  D.herm.hodgeLen (D.per z) v

end FullerData

namespace Gauss

end Gauss

namespace LineFuller

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])


end LineFuller

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField
open scoped Matrix

def IsotropicRank.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] [IsCMField Em] (Ψ : Type) [Fintype Ψ] (N j : ℕ)
    (A : HermDatum Em Ψ N j) (S : Set (Fin N → Em)),
      (∀ v ∈ S, ∀ w ∈ S, hermForm Em A.H v w = 0) → Module.finrank Em (Submodule.span Em S) ≤ N - j

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

section Herm

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

def HermDatum.IsWittPoint (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ τ, (P τ)ᴴ * A.H.map (A.emb τ) * P τ = signMat N j

def HermDatum.hodgeNormSq (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) (v : Fin N → Em) : ℝ :=
  ∑ τ, 2 * ‖A.emb τ A.ξ‖ * ∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (v a)) c‖ ^ 2

def HermDatum.hodgeNorm (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) (v : Fin N → Em) : ℝ :=
  Real.sqrt (A.hodgeNormSq P v)

def HermDatum.shortSpan (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) (r : ℝ) :
    Submodule (𝓞 Em) (Fin N → Em) :=
  Submodule.span (𝓞 Em) {v | v ∈ A.L ∧ A.hodgeNorm P v < r}

variable (Em) in

def IntegralBasisBound (vr : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (a : κ → 𝓞 Em), Fintype.card κ = Module.finrank ℚ Em ∧
    LinearIndependent ℚ (fun i => (a i : Em)) ∧ ∀ i (σ : Em →+* ℂ), ‖σ (a i)‖ ≤ vr

end Herm

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

def ShortIsotropic.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ z ∈ mcPts (mCoordIdeal D.y) \ D.Bd, ∀ vr : ℝ, IntegralBasisBound Em vr →
    D.herm.IsIso (D.herm.shortSpan (D.per z) (Real.sqrt vr)⁻¹)

namespace ShortIsotropic

section Herm

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

theorem hermForm_zero_left (H : Matrix (Fin N) (Fin N) Em) (y : Fin N → Em) : hermForm Em H 0 y = 0 := by
  simp [hermForm]

theorem hermForm_zero_right (H : Matrix (Fin N) (Fin N) Em) (x : Fin N → Em) : hermForm Em H x 0 = 0 := by
  simp [hermForm]

theorem hermForm_add_left (H : Matrix (Fin N) (Fin N) Em) (x x' y : Fin N → Em) :
    hermForm Em H (x + x') y = hermForm Em H x y + hermForm Em H x' y := by
  simp only [hermForm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hermForm_add_right (H : Matrix (Fin N) (Fin N) Em) (x y y' : Fin N → Em) :
    hermForm Em H x (y + y') = hermForm Em H x y + hermForm Em H x y' := by
  simp only [hermForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermForm_smul_left (H : Matrix (Fin N) (Fin N) Em) (c : Em) (x y : Fin N → Em) :
    hermForm Em H (c • x) y = IsCMField.complexConj Em c * hermForm Em H x y := by
  simp only [hermForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermForm_smul_right (H : Matrix (Fin N) (Fin N) Em) (c : Em) (x y : Fin N → Em) :
    hermForm Em H x (c • y) = c * hermForm Em H x y := by
  simp only [hermForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField Em] [IsCMField Em] in
theorem oSmul_eq (c : 𝓞 Em) (x : Fin N → Em) : c • x = (c : Em) • x := rfl

theorem emb_hermForm (σ : Em →+* ℂ) (H : Matrix (Fin N) (Fin N) Em) (x y : Fin N → Em) :
    σ (hermForm Em H x y) = star (fun a => σ (x a)) ⬝ᵥ (H.map σ *ᵥ fun b => σ (y b)) := by
  simp only [hermForm, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, dotProduct, Matrix.mulVec,
    Matrix.map_apply, Pi.star_apply, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem det_signMat_ne_zero (N j : ℕ) : (signMat N j).det ≠ 0 := by
  rw [signMat, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => by split_ifs <;> norm_num

theorem isUnit_det_of_witt {M P : Matrix (Fin N) (Fin N) ℂ} (hW : Pᴴ * M * P = signMat N j) : IsUnit P.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := congrArg Matrix.det hW
  rw [Matrix.det_mul, h0, mul_zero] at h
  exact det_signMat_ne_zero N j h.symm

theorem form_witt {M P : Matrix (Fin N) (Fin N) ℂ} (hW : Pᴴ * M * P = signMat N j) (x y : Fin N → ℂ) :
    star x ⬝ᵥ (M *ᵥ y) = star (P⁻¹ *ᵥ x) ⬝ᵥ (signMat N j *ᵥ (P⁻¹ *ᵥ y)) := by
  have hu := isUnit_det_of_witt hW
  have hx : x = P *ᵥ (P⁻¹ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hy : y = P *ᵥ (P⁻¹ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  generalize P⁻¹ *ᵥ x = a at hx ⊢
  generalize P⁻¹ *ᵥ y = b at hy ⊢
  subst hx hy
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW]

theorem norm_sign_form_le (a b : Fin N → ℂ) :
    ‖star a ⬝ᵥ (signMat N j *ᵥ b)‖ ≤ Real.sqrt (∑ c, ‖a c‖ ^ 2) * Real.sqrt (∑ c, ‖b c‖ ^ 2) := by
  have h1 : ‖star a ⬝ᵥ (signMat N j *ᵥ b)‖ ≤ ∑ c, ‖a c‖ * ‖b c‖ := by
    simp only [signMat, dotProduct, Matrix.mulVec_diagonal]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
    simp only [Pi.star_apply, norm_mul, norm_star]
    split_ifs <;> simp
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

theorem sum_embeddings (A : HermDatum Em Ψ N j) (g : (Em →+* ℂ) → ℝ) :
    ∑ σ : Em →+* ℂ, g σ = ∑ τ, (g (A.emb τ) + g ((starRingEnd ℂ).comp (A.emb τ))) := by
  let e : Ψ × Bool → (Em →+* ℂ) := fun p => if p.2 then (starRingEnd ℂ).comp (A.emb p.1) else A.emb p.1
  have cc : ∀ σ : Em →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := by
    intro σ; ext x; simp
  have key : ∀ τ τ', A.emb τ ≠ (starRingEnd ℂ).comp (A.emb τ') := by
    intro τ τ' h
    refine (A.cmType (A.emb τ)).1 ⟨τ, rfl⟩ ⟨τ', ?_⟩
    rw [h, cc]
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨τ, b⟩ ⟨τ', b'⟩ h
      cases b <;> cases b' <;> simp only [e, Bool.false_eq_true, if_true, if_false] at h
      · rw [A.emb_inj h]
      · exact absurd h (key _ _)
      · exact absurd h.symm (key _ _)
      · have h' := congrArg (fun f : Em →+* ℂ => (starRingEnd ℂ).comp f) h
        simp only [cc] at h'
        rw [A.emb_inj h']
    · intro σ
      by_cases hσ : ∃ τ, A.emb τ = σ
      · obtain ⟨τ, rfl⟩ := hσ
        exact ⟨(τ, false), rfl⟩
      · obtain ⟨τ, hτ⟩ := not_not.mp (mt (A.cmType σ).2 hσ)
        refine ⟨(τ, true), ?_⟩
        simp only [e, if_true]
        rw [hτ, cc]
  rw [← he.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_bool]
  simp only [e, if_true, Bool.false_eq_true, if_false, add_comm]

theorem abs_trace_le (A : HermDatum Em Ψ N j) (x : Em) :
    |((Algebra.trace ℚ Em x : ℚ) : ℝ)| ≤ ∑ τ, 2 * ‖A.emb τ x‖ := by
  have htr : ((Algebra.trace ℚ Em x : ℚ) : ℂ) = ∑ σ : Em →+* ℂ, σ x := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := Em) (E := ℂ) (x := x)
    rw [eq_ratCast (algebraMap ℚ ℂ)] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom Em ℂ) _ _ (fun _ => rfl)).symm
  have habs : |((Algebra.trace ℚ Em x : ℚ) : ℝ)| = ‖((Algebra.trace ℚ Em x : ℚ) : ℂ)‖ := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, htr]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  rw [sum_embeddings A (fun σ => ‖σ x‖)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [two_mul]

theorem abs_trForm_le (A : HermDatum Em Ψ N j) {P : Ψ → Matrix (Fin N) (Fin N) ℂ} (hP : A.IsWittPoint P)
    (x y : Fin N → Em) :
    |((trForm Em A.ξ A.H x y : ℚ) : ℝ)| ≤ A.hodgeNorm P x * A.hodgeNorm P y := by
  set nx : Ψ → ℝ := fun τ => Real.sqrt (∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c‖ ^ 2) with hnx
  set ny : Ψ → ℝ := fun τ => Real.sqrt (∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (y a)) c‖ ^ 2) with hny
  set s : Ψ → ℝ := fun τ => Real.sqrt (2 * ‖A.emb τ A.ξ‖) with hs
  have hτ : ∀ τ, ‖A.emb τ (A.ξ * hermForm Em A.H x y)‖ ≤ ‖A.emb τ A.ξ‖ * (nx τ * ny τ) := by
    intro τ
    rw [map_mul, norm_mul, emb_hermForm, form_witt (hP τ)]
    exact mul_le_mul_of_nonneg_left (norm_sign_form_le _ _) (norm_nonneg _)
  have hw : ∀ τ, 2 * (‖A.emb τ A.ξ‖ * (nx τ * ny τ)) = (s τ * nx τ) * (s τ * ny τ) := by
    intro τ
    have h := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 * ‖A.emb τ A.ξ‖)
    calc 2 * (‖A.emb τ A.ξ‖ * (nx τ * ny τ))
        = (Real.sqrt (2 * ‖A.emb τ A.ξ‖) * Real.sqrt (2 * ‖A.emb τ A.ξ‖)) * (nx τ * ny τ) := by rw [h]; ring
      _ = (s τ * nx τ) * (s τ * ny τ) := by simp only [hs]; ring
  have hsq : ∀ u : Fin N → Em, ∑ τ, (s τ * Real.sqrt (∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (u a)) c‖ ^ 2)) ^ 2 =
      A.hodgeNormSq P u := by
    intro u
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  calc |((trForm Em A.ξ A.H x y : ℚ) : ℝ)| ≤ ∑ τ, 2 * ‖A.emb τ (A.ξ * hermForm Em A.H x y)‖ := abs_trace_le A _
    _ ≤ ∑ τ, 2 * (‖A.emb τ A.ξ‖ * (nx τ * ny τ)) :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hτ τ) (by norm_num)
    _ = ∑ τ, (s τ * nx τ) * (s τ * ny τ) := Finset.sum_congr rfl fun τ _ => hw τ
    _ ≤ Real.sqrt (∑ τ, (s τ * nx τ) ^ 2) * Real.sqrt (∑ τ, (s τ * ny τ) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = A.hodgeNorm P x * A.hodgeNorm P y := by rw [hsq x, hsq y]; rfl

theorem hodgeNorm_smul_le (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) {vr : ℝ} (c : Em)
    (hc : ∀ σ : Em →+* ℂ, ‖σ c‖ ≤ vr) (x : Fin N → Em) :
    A.hodgeNorm P (c • x) ≤ vr * A.hodgeNorm P x := by
  have h0 : 0 ≤ vr := (norm_nonneg _).trans (hc (Classical.choice inferInstance))
  have hsq : A.hodgeNormSq P (c • x) ≤ vr ^ 2 * A.hodgeNormSq P x := by
    unfold HermDatum.hodgeNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hv : ((P τ)⁻¹ *ᵥ fun a => A.emb τ ((c • x) a)) =
        A.emb τ c • ((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) := by
      rw [← Matrix.mulVec_smul]
      congr 1
      ext a
      simp [smul_eq_mul]
    have hS : ∑ c', ‖(A.emb τ c • ((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a))) c'‖ ^ 2 =
        ‖A.emb τ c‖ ^ 2 * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2 := by
      rw [Finset.mul_sum]
      simp [mul_pow]
    rw [hv, hS]
    have ht : ‖A.emb τ c‖ ^ 2 ≤ vr ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc _) 2
    calc 2 * ‖A.emb τ A.ξ‖ * (‖A.emb τ c‖ ^ 2 * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2)
        = ‖A.emb τ c‖ ^ 2 * (2 * ‖A.emb τ A.ξ‖ * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2) := by ring
      _ ≤ vr ^ 2 * (2 * ‖A.emb τ A.ξ‖ * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
  unfold HermDatum.hodgeNorm
  calc Real.sqrt (A.hodgeNormSq P (c • x)) ≤ Real.sqrt (vr ^ 2 * A.hodgeNormSq P x) := Real.sqrt_le_sqrt hsq
    _ = vr * Real.sqrt (A.hodgeNormSq P x) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h0]

theorem hermForm_eq_zero_of_short (A : HermDatum Em Ψ N j) {P : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hP : A.IsWittPoint P) {vr : ℝ} (hvr : IntegralBasisBound Em vr) {v w : Fin N → Em} (hv : v ∈ A.L)
    (hw : w ∈ A.L) (hvs : A.hodgeNorm P v < (Real.sqrt vr)⁻¹) (hws : A.hodgeNorm P w < (Real.sqrt vr)⁻¹) :
    hermForm Em A.H v w = 0 := by
  obtain ⟨κ, _, a, hcard, hli, hbd⟩ := hvr
  have hvr0 : 0 < vr := by
    have h1 : 0 < (Real.sqrt vr)⁻¹ := lt_of_le_of_lt (Real.sqrt_nonneg _) hvs
    exact Real.sqrt_pos.mp (inv_pos.mp h1)
  have step : ∀ i, trForm Em A.ξ A.H ((a i : Em) • v) w = 0 := by
    intro i
    have hmem : (a i : Em) • v ∈ A.L := A.L.smul_mem (a i) hv
    obtain ⟨m, hm⟩ := (A.selfDual _).1 hmem w hw
    have hlt : |((trForm Em A.ξ A.H ((a i : Em) • v) w : ℚ) : ℝ)| < 1 := by
      refine lt_of_le_of_lt (abs_trForm_le A hP _ _) ?_
      have hnv := Real.sqrt_nonneg (A.hodgeNormSq P v)
      have hnw := Real.sqrt_nonneg (A.hodgeNormSq P w)
      calc A.hodgeNorm P ((a i : Em) • v) * A.hodgeNorm P w ≤ vr * A.hodgeNorm P v * A.hodgeNorm P w :=
            mul_le_mul_of_nonneg_right (hodgeNorm_smul_le A P _ (hbd i) v) hnw
        _ < vr * (Real.sqrt vr)⁻¹ * (Real.sqrt vr)⁻¹ :=
            mul_lt_mul'' (mul_lt_mul_of_pos_left hvs hvr0) hws (by positivity) hnw
        _ = 1 := by
            rw [mul_assoc, ← mul_inv, Real.mul_self_sqrt hvr0.le, mul_inv_cancel₀ hvr0.ne']
    rw [hm, Rat.cast_intCast] at hlt
    have hm0 : m = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
    rw [hm, hm0, Int.cast_zero]
  set t := hermForm Em A.H v w
  let conjQ : Em →ₗ[ℚ] Em := ((IsCMField.complexConj Em : Em →+* Em).toRatAlgHom).toLinearMap
  let φ : Em →ₗ[ℚ] ℚ := (Algebra.trace ℚ Em).comp ((LinearMap.mulRight ℚ (A.ξ * t)).comp conjQ)
  have hφ : ∀ b : Em, φ b = trForm Em A.ξ A.H (b • v) w := by
    intro b
    simp only [φ, conjQ, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
      RingHom.toRatAlgHom_apply, trForm, hermForm_smul_left, t]
    congr 1
    simp only [RingHom.coe_coe]
    ring
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hφ0 : φ = 0 := LinearMap.ext_on_range hspan fun i => by rw [hφ, LinearMap.zero_apply]; exact step i
  by_contra ht
  have hξt : A.ξ * t ≠ 0 := mul_ne_zero A.ξ_ne ht
  have h1 := LinearMap.congr_fun hφ0 (IsCMField.complexConj Em (A.ξ * t)⁻¹)
  simp only [φ, conjQ, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
    RingHom.toRatAlgHom_apply, LinearMap.zero_apply, RingHom.coe_coe, IsCMField.complexConj_apply_apply,
    inv_mul_cancel₀ hξt] at h1
  rw [show (1 : Em) = algebraMap ℚ Em 1 from (map_one _).symm, Algebra.trace_algebraMap] at h1
  simp only [nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h1
  exact (Module.finrank_pos (R := ℚ) (M := Em)).ne' h1

theorem isIso_shortSpan (A : HermDatum Em Ψ N j) {P : Ψ → Matrix (Fin N) (Fin N) ℂ} (hP : A.IsWittPoint P)
    {vr : ℝ} (hvr : IntegralBasisBound Em vr) : A.IsIso (A.shortSpan P (Real.sqrt vr)⁻¹) := by
  have right : ∀ v ∈ {v | v ∈ A.L ∧ A.hodgeNorm P v < (Real.sqrt vr)⁻¹},
      ∀ y ∈ A.shortSpan P (Real.sqrt vr)⁻¹, hermForm Em A.H v y = 0 := by
    intro v hv y hy
    induction hy using Submodule.span_induction with
    | mem w hw => exact hermForm_eq_zero_of_short A hP hvr hv.1 hw.1 hv.2 hw.2
    | zero => exact hermForm_zero_right _ _
    | add y y' _ _ h h' => rw [hermForm_add_right, h, h', add_zero]
    | smul c y _ h => rw [oSmul_eq, hermForm_smul_right, h, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem v hv => exact right v hv y hy
  | zero => exact hermForm_zero_left _ _
  | add x x' _ _ h h' => rw [hermForm_add_left, h, h', add_zero]
  | smul c x _ h => rw [oSmul_eq, hermForm_smul_left, h, mul_zero]

end Herm

theorem proof (D : FullerData II Ψ K ι Ω E Em) : ShortIsotropic.Statement D :=
  fun z hz _ hvr => isIso_shortSpan D.herm (fun τ => D.per_witt z hz τ) hvr

end ShortIsotropic

namespace ShortIsotropic





end ShortIsotropic

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField
open scoped Matrix

namespace IsotropicRank

theorem hermForm_span_eq_zero {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {N : ℕ}
    (H : Matrix (Fin N) (Fin N) Em) (S : Set (Fin N → Em)) (hS : ∀ v ∈ S, ∀ w ∈ S, hermForm Em H v w = 0) :
    ∀ x ∈ Submodule.span Em S, ∀ y ∈ Submodule.span Em S, hermForm Em H x y = 0 := by
  have h1 : ∀ v ∈ S, ∀ y ∈ Submodule.span Em S, hermForm Em H v y = 0 := by
    intro v hv y hy
    induction hy using Submodule.span_induction with
    | mem w hw => exact hS v hv w hw
    | zero => exact ShortIsotropic.hermForm_zero_right H v
    | add y y' _ _ h h' => rw [ShortIsotropic.hermForm_add_right, h, h', add_zero]
    | smul c y _ h => rw [ShortIsotropic.hermForm_smul_right, h, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem v hv => exact h1 v hv y hy
  | zero => exact ShortIsotropic.hermForm_zero_left H y
  | add x x' _ _ h h' => rw [ShortIsotropic.hermForm_add_left, h, h', add_zero]
  | smul c x _ h => rw [ShortIsotropic.hermForm_smul_left, h, mul_zero]

theorem nonempty_cmType {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}
    (A : HermDatum Em Ψ N j) : Nonempty Ψ := by
  obtain ⟨σ⟩ : Nonempty (Em →+* ℂ) := inferInstance
  by_cases h : ∃ τ, A.emb τ = σ
  · exact ⟨h.choose⟩
  · obtain ⟨τ, _⟩ := not_not.mp (mt (A.cmType σ).mpr h)
    exact ⟨τ⟩

theorem mulVec_map_injective {K L : Type*} [Field K] [Field L] {n r : ℕ} (σ : K →+* L)
    (M : Matrix (Fin n) (Fin r) K) (hM : Function.Injective M.mulVec) : Function.Injective (M.map σ).mulVec := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin M)
    (LinearMap.ker_eq_bot.mpr hM)
  have hL : LinearMap.toMatrix' g * M = 1 := by
    have hM' : LinearMap.toMatrix' (Matrix.mulVecLin M) = M := by
      rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    rw [← hM', ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hLσ : (LinearMap.toMatrix' g).map σ * M.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro c d hcd
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hcd
  simpa only [Matrix.mulVec_mulVec, hLσ, Matrix.one_mulVec] using h

theorem proof : IsotropicRank.Statement := by
  intro Em _ _ _ Ψ _ N j A S hS
  obtain ⟨τ⟩ := nonempty_cmType A
  obtain ⟨P, hPu, hP⟩ := A.signature τ
  set U := Submodule.span Em S
  set r := Module.finrank Em U
  let b := Module.finBasis Em U
  let M : Matrix (Fin N) (Fin r) Em := Matrix.of fun i a => (b a : Fin N → Em) i
  have hMv : ∀ c, M *ᵥ c = ∑ a, c a • (b a : Fin N → Em) := by
    intro c
    ext i
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hli : LinearIndependent Em fun a => (b a : Fin N → Em) :=
    b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hM : Function.Injective M.mulVec := by
    intro c d hcd
    have h0 : ∑ a, (c - d) a • (b a : Fin N → Em) = 0 := by
      rw [← hMv, Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hcd
    funext a
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 a)
  have hz : ∀ a a', hermForm Em A.H (b a) (b a') = 0 := fun a a' =>
    hermForm_span_eq_zero A.H S hS _ (b a).2 _ (b a').2
  set Mτ := M.map (A.emb τ)
  set Hτ := A.H.map (A.emb τ)
  have hG : Mτᴴ * Hτ * Mτ = 0 := by
    ext a a'
    have h := ShortIsotropic.emb_hermForm (A.emb τ) A.H (b a) (b a')
    rw [hz a a', map_zero] at h
    rw [Matrix.zero_apply, h]
    simp only [Mτ, Hτ, M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hq : ∀ c, star (Mτ *ᵥ c) ⬝ᵥ (Hτ *ᵥ (Mτ *ᵥ c)) = 0 := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hG, Matrix.zero_mulVec, dotProduct_zero]
  let g : Fin (N - j) → Fin N := fun k => ⟨j + k, by omega⟩
  let f : (Fin r → ℂ) →ₗ[ℂ] (Fin (N - j) → ℂ) := LinearMap.funLeft ℂ ℂ g ∘ₗ Matrix.mulVecLin (P⁻¹ * Mτ)
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun c hc => ?_
    set y := P⁻¹ *ᵥ (Mτ *ᵥ c)
    have hy0 : ∀ a : Fin N, j ≤ (a : ℕ) → y a = 0 := by
      intro a ha
      have h := congrFun hc ⟨a - j, by omega⟩
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
        ← Matrix.mulVec_mulVec, Pi.zero_apply] at h
      have hg : g ⟨a - j, by omega⟩ = a := Fin.ext (by simp only [g]; omega)
      rwa [hg] at h
    have hw := ShortIsotropic.form_witt hP (Mτ *ᵥ c) (Mτ *ᵥ c)
    rw [hq c] at hw
    have hsum : ∑ a, Complex.normSq (y a) = 0 := by
      have h := congrArg Complex.re hw.symm
      simp only [signMat, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum,
        Complex.zero_re] at h
      rw [← h]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : (a : ℕ) < j
      · simp only [ha, if_true, one_mul, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
          Complex.normSq_apply]
        ring
      · have h0 : ((P⁻¹ * Mτ) *ᵥ c) a = 0 := by
          rw [← Matrix.mulVec_mulVec]
          exact hy0 a (by omega)
        have h1 : y a = 0 := hy0 a (by omega)
        simp [ha, h0, h1]
    have hy : y = 0 := by
      funext a
      have h := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg (y a)).mp hsum a
        (Finset.mem_univ a)
      exact Complex.normSq_eq_zero.mp h
    have hMc : Mτ *ᵥ c = 0 := by
      have : Mτ *ᵥ c = P *ᵥ y := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
      rw [this, hy, Matrix.mulVec_zero]
    exact mulVec_map_injective (A.emb τ) M hM (hMc.trans (Matrix.mulVec_zero Mτ).symm)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fin_fun] using this

end IsotropicRank

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

theorem UnitaryIsotropicRank.proof : UnitaryIsotropicRank.Statement := by
  intro Em _ _ _ Ψ _ N j A I hI ρ v hv
  obtain ⟨-, hvI, hli, -⟩ := hv
  have hliE : LinearIndependent Em v := (LinearIndependent.iff_fractionRing (𝓞 Em) Em).mp hli
  have hS : ∀ x ∈ (I : Set (Fin N → Em)), ∀ y ∈ (I : Set (Fin N → Em)), hermForm Em A.H x y = 0 := hI
  have hle : Submodule.span Em (Set.range v) ≤ Submodule.span Em (I : Set (Fin N → Em)) :=
    Submodule.span_mono (Set.range_subset_iff.2 hvI)
  calc ρ = Module.finrank Em (Submodule.span Em (Set.range v)) := by
        rw [finrank_span_eq_card hliE, Fintype.card_fin]
    _ ≤ Module.finrank Em (Submodule.span Em (I : Set (Fin N → Em))) := Submodule.finrank_mono hle
    _ ≤ N - j := IsotropicRank.proof Em Ψ N j A (I : Set (Fin N → Em)) hS

end GroundTheory.Heights₂.Heights.NineStatements
end
end
