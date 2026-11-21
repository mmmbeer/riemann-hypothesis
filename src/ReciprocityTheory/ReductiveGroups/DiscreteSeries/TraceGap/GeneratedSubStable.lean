import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemHighestWeightSubIff
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ExistsNonzeroPhysicalHighestWeightVectorTensFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARKinv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SecondKernelCoupled

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def gaW (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam - rhoC ε + rhoHol ε

section General

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def kFinSub (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Submodule ℂ M :=
  ⨆ (S : Submodule ℂ M) (_ : FiniteDimensional ℂ S ∧ IsKStableSub ε E S), S

end General

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def coordSpan (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))) : Submodule ℂ M :=
  Submodule.span ℂ {v | ∃ (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)), y ∈ Z ∧ v = tco s y}

def lineSub (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (W : Submodule ℂ M) :
    Submodule ℂ (TensorProduct ℂ M (Fock n)) :=
  khwSub ε (diagE ε (eT E) cpT cmT) (gaW ε lam) ⊓ tensFock W ⊓ physicalSubspace ε

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section Gen

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem mem_highestWeightSub_iff (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ W) (γ : Fin n → ℝ) (x : W) :
    x ∈ khwSub ε F γ ↔ IsKHWVec ε F γ x := by
  simp only [khwSub, IsKHWVec, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b h => h2 a b h.1 h.2⟩

theorem support_subset_physicalModes {ε : Fin n → Bool} {z : TensorProduct ℂ W (Fock n)} (hz : z ∈ physicalSubspace ε)
    {s : Finset (Fin (n * n))} (hs : tcoef ((fockBasis n).coord s) z ≠ 0) : s ⊆ lfPhysModes ε := by
  intro m hm
  by_contra hnot
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  have hx : ¬ (ε x.1 = true ∧ ε x.2 = false) := fun h => hnot ((lf_mem_phys ε x.1 x.2).2 h)
  have h0 : cmT (N := W) x.1 x.2 z = 0 := by
    simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker] at hz
    exact hz x.1 x.2 hx
  have h1 : LinearMap.lTensor W (cpFock x.1 x.2 ∘ₗ cmFock x.1 x.2) z = 0 := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
    have : LinearMap.lTensor W (cmFock x.1 x.2) z = 0 := h0
    rw [this, map_zero]
  have h2 := congrArg (tcoef ((fockBasis n).coord s)) h1
  rw [tcoef_lTensor, gc_coord_num x s, if_pos hm, one_smul, map_zero] at h2
  exact hs h2

theorem signedAction_tensor (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := W) (n := n)) cmT a b = LinearMap.lTensor W (sgE ε cpFock cmFock a b) := by
  apply TensorProduct.ext'
  intro m f
  unfold sgE
  split_ifs <;> simp [cpT, cmT, LinearMap.sum_apply, TensorProduct.tmul_sum]

end Gen

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem line_exists {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W) :
    ∃ z ∈ lineSub ε E lam W, z ≠ 0 := by
  obtain ⟨x, hxT, hxP, hx0, hxK⟩ := lowFock_exists ε hE hlam hW
  exact ⟨x, ⟨⟨(mem_highestWeightSub_iff _ _ _ x).2 hxK, hxT⟩, hxP⟩, hx0⟩

theorem tensorCoeff_diagAction (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a : Fin n)
    (s : Finset (Fin (n * n))) (z : TensorProduct ℂ M (Fock n)) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a a z) =
      E a a (tcoef ((fockBasis n).coord s) z) + ((fockWt ε s a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) z := by
  rw [diagE, LinearMap.add_apply, map_add, signedAction_tensor, eT, tcoef_map_left, tcoef_lTensor, coord_comp_sg, tcoef_smul]

theorem line_deg {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W)
    {z : TensorProduct ℂ M (Fock n)} (hz : z ∈ lineSub ε E lam W) :
    z ∈ LinearMap.range (TensorProduct.map W.subtype (⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ)).subtype) := by
  obtain ⟨⟨hK, hT⟩, hP⟩ := hz
  replace hK := (mem_highestWeightSub_iff _ _ _ z).1 hK
  have hdeg : ∀ s, tcoef ((fockBasis n).coord s) z ≠ 0 → s.card = sDeg ε := by
    intro s hs
    have hsub := support_subset_physicalModes hP hs
    have hmem : tcoef ((fockBasis n).coord s) z ∈ W := tcoef_mem hT _
    have hEa : ∀ a, E a a (tcoef ((fockBasis n).coord s) z) =
        (((gaW ε lam a - fockWt ε s a : ℝ) : ℂ)) • tcoef ((fockBasis n).coord s) z := by
      intro a
      have h := congrArg (tcoef ((fockBasis n).coord s)) (hK.1 a)
      rw [tensorCoeff_diagAction, map_smul] at h
      rw [Complex.ofReal_sub, sub_smul, ← h]
      abel
    have hZ := zPlus_V hE hW _ hmem
    have hZ' : zPlus ε E (tcoef ((fockBasis n).coord s) z) =
        (∑ c ∈ plusIdx ε, (((gaW ε lam c - fockWt ε s c : ℝ) : ℂ))) • tcoef ((fockBasis n).coord s) z := by
      unfold zPlus
      rw [LinearMap.sum_apply, Finset.sum_smul]
      exact Finset.sum_congr rfl fun c _ => hEa c
    rw [hZ] at hZ'
    have hc : (∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) = ∑ c ∈ plusIdx ε, (((gaW ε lam c - fockWt ε s c : ℝ) : ℂ)) :=
      smul_left_injective ℂ hs hZ'
    have hr : (∑ c ∈ plusIdx ε, lowK ε lam c) = ∑ c ∈ plusIdx ε, (gaW ε lam c - fockWt ε s c) := by
      exact_mod_cast hc
    rw [Finset.sum_sub_distrib, gc_plus_sum hsub] at hr
    have h2 := sDeg_eq_sum ε
    have h3 : (sDeg ε : ℝ) = (s.card : ℝ) := by
      rw [h2]
      have : ∀ c, (rhoHol ε - rhoN ε) c = gaW ε lam c - lowK ε lam c := by
        intro c
        simp only [gaW, lowK, Pi.add_apply, Pi.sub_apply]
        ring
      rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_sub_distrib]
      linarith
    exact_mod_cast h3.symm
  rw [tcoef_expand z]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : tcoef ((fockBasis n).coord s) z = 0
  · rw [hs, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _
  · have hb : fockBasis n s ∈ ⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ) := by
      rw [← hdeg s hs]
      exact gs_basis_deg s
    exact ⟨(⟨tcoef ((fockBasis n).coord s) z, tcoef_mem hT _⟩ : W) ⊗ₜ (⟨fockBasis n s, hb⟩ : ⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ)), by
      simp [TensorProduct.map_tmul]⟩

theorem line_ker {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W)
    (hc : ∀ v ∈ W, casimir E v = ((casVal lam : ℝ) : ℂ) • v)
    {z : TensorProduct ℂ M (Fock n)} (hz : z ∈ lineSub ε E lam W) : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0 := by
  obtain ⟨⟨hK, hT⟩, hP⟩ := hz
  replace hK := (mem_highestWeightSub_iff _ _ _ z).1 hK
  have hKv : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - rhoC ε) + rhoHol ε) z := hK
  have hcas : casimir (eT (n := n) E) z = ((casVal lam : ℝ) : ℂ) • z := by
    rw [ssh_casimir_eT]
    obtain ⟨y, rfl⟩ := hT
    have hcomp : casimir E ∘ₗ W.subtype = ((casVal lam : ℝ) : ℂ) • W.subtype := by
      ext v
      simp [hc v v.2]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, hcomp, TensorProduct.map_smul_left,
      LinearMap.smul_apply]
  have h2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hKv hcas
  have hzero : (((nsq (lam - rhoC ε + rhoC ε) - nsq (rho n) : ℝ) : ℂ) - ((casVal lam : ℝ) : ℂ)) = 0 := by
    rw [sub_add_cancel, casVal, sub_self]
  rw [hzero, zero_smul] at h2
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hD
  have hDD : D (D z) = 0 := by
    have h3 : (2 : ℂ) • (D * D) z = 0 := h2
    rw [smul_eq_zero] at h3
    rcases h3 with h3 | h3
    · norm_num at h3
    · exact h3
  have hf : tform (D z) (D z) = 0 := by
    rw [hD, tform_D hU, ← hD, hDD]
    unfold tform
    simp
  by_contra hne
  have := tform_self_re_pos hne
  rw [hf] at this
  simp at this

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section Gen

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {A : Fin n → Fin n → Module.End ℂ X}

theorem exists_joint_eigenvector_alt (hcomm : ∀ a c (v : X), A a a (A c c v) = A c c (A a a v)) (s : Finset (Fin n)) :
    ∀ T : Submodule ℂ X, FiniteDimensional ℂ T → (∀ c, ∀ v ∈ T, A c c v ∈ T) → T ≠ ⊥ →
      ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro T _ _ hT
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
    exact ⟨w, hw, hw0, 0, by simp⟩
  | insert a s ha ih =>
    intro T hfd hst hT
    have : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hT
    let f : Module.End ℂ T := (A a a).restrict (fun v hv => hst a v hv)
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue f
    obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
    have hv1 : f v = lam • v := Module.End.mem_eigenspace_iff.mp hv.1
    have hv2 : (v : X) ≠ 0 := fun h => hv.2 (Subtype.ext h)
    have hv3 : A a a v = lam • (v : X) := by
      have := congrArg Subtype.val hv1
      simpa [f] using this
    let T' : Submodule ℂ X := T ⊓ Module.End.eigenspace (A a a) lam
    have hfd' : FiniteDimensional ℂ T' := Submodule.finiteDimensional_of_le inf_le_left
    have hst' : ∀ c, ∀ u ∈ T', A c c u ∈ T' := by
      intro c u hu
      refine ⟨hst c u hu.1, ?_⟩
      have h2 : A a a u = lam • u := Module.End.mem_eigenspace_iff.mp hu.2
      show A c c u ∈ Module.End.eigenspace (A a a) lam
      rw [Module.End.mem_eigenspace_iff, hcomm a c u, h2, map_smul]
    have hT' : T' ≠ ⊥ := by
      intro h
      have : (v : X) ∈ T' := ⟨v.2, Module.End.mem_eigenspace_iff.mpr hv3⟩
      rw [h, Submodule.mem_bot] at this
      exact hv2 this
    obtain ⟨w, hw, hw0, μ, hμ⟩ := ih T' hfd' hst' hT'
    refine ⟨w, hw.1, hw0, Function.update μ a lam, ?_⟩
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [Function.update_self]
      exact Module.End.mem_eigenspace_iff.mp hw.2
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      rw [Function.update_of_ne hca]
      exact hμ c hc

theorem exists_highestWeight_general (ε : Fin n → Bool)
    (hK : ∀ a b c d, ε a = ε b → ε c = ε d →
      A a b * A c d - A c d * A a b = (if b = c then A a d else 0) - (if d = a then A c b else 0))
    (hreal : ∀ c (w : X) (z : ℂ), w ≠ 0 → A c c w = z • w → z = ((z.re : ℝ) : ℂ))
    {S : Submodule ℂ X} (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hcomm : ∀ a c (v : X), A a a (A c c v) = A c c (A a a v) := by
    intro a c v
    have h := LinearMap.congr_fun (hK a a c c rfl rfl) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    by_cases hac : a = c
    · subst hac; rfl
    · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
      exact h
  have hshift : ∀ {μ : Fin n → ℝ} {w : X}, (∀ c, A c c w = (μ c : ℂ) • w) → ∀ {a b : Fin n}, a ≠ b → ε a = ε b →
      ∀ c, A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
    intro μ w hw a b hab hεab c
    have h := LinearMap.congr_fun (hK c c a b rfl hεab) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
    by_cases hca : c = a
    · subst hca
      simp [hab, Ne.symm hab] at h ⊢
      linear_combination (norm := module) h
    · by_cases hcb : c = b
      · subst hcb
        simp [hca] at h ⊢
        linear_combination (norm := module) h
      · simp [hca, hcb, Ne.symm hcb] at h ⊢
        linear_combination (norm := module) h
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := exists_joint_eigenvector_alt hcomm Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact hreal c w (z c) hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => hshift hμ (ne_of_lt hab) hεab c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))

end Gen

section Alg

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem diagAction_commutator {W : Type*} [AddCommGroup W] [Module ℂ W] {E cp cm : Fin n → Fin n → Module.End ℂ W}
    (hE : IsGlRep E) (hC : IsCAR cp cm) (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool)
    (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    diagE ε E cp cm a b * diagE ε E cp cm c d - diagE ε E cp cm c d * diagE ε E cp cm a b =
      (if b = c then diagE ε E cp cm a d else 0) - (if d = a then diagE ε E cp cm c b else 0) := by
  have e1 := hE a b c d
  have e2 := sgE_comm hC ε a b c d hab hcd
  have h1 := E_comm_sgE hEC ε a b c d
  have h2 := E_comm_sgE hEC ε c d a b
  have key : (E a b + sgE ε cp cm a b) * (E c d + sgE ε cp cm c d) -
      (E c d + sgE ε cp cm c d) * (E a b + sgE ε cp cm a b) =
      (E a b * E c d - E c d * E a b) + (sgE ε cp cm a b * sgE ε cp cm c d - sgE ε cp cm c d * sgE ε cp cm a b) := by
    simp only [add_mul, mul_add]
    rw [h1, ← h2]
    abel
  unfold diagE
  rw [key, e1, e2]
  split_ifs <;> abel

theorem tmul_mem_tensorFock {S : Submodule ℂ N} {v : N} (hv : v ∈ S) (f : Fock n) :
    v ⊗ₜ f ∈ tensFock (n := n) S :=
  ⟨⟨v, hv⟩ ⊗ₜ f, by simp [TensorProduct.map_tmul]⟩

theorem mem_tensorFock_of_coeffs {S : Submodule ℂ N} {y : TensorProduct ℂ N (Fock n)}
    (hy : ∀ s, tcoef ((fockBasis n).coord s) y ∈ S) : y ∈ tensFock S := by
  rw [tcoef_expand y]
  exact Submodule.sum_mem _ fun s _ => tmul_mem_tensorFock (hy s) _

theorem tensorFock_finiteDimensional {S : Submodule ℂ N} (hS : FiniteDimensional ℂ S) :
    FiniteDimensional ℂ (tensFock (n := n) S) := by
  have : Module.Finite ℂ (Fock n) := Module.Finite.of_basis (fockBasis n)
  exact LinearMap.finiteDimensional_range _

theorem tensorFock_mono {S T : Submodule ℂ N} (h : S ≤ T) : tensFock (n := n) S ≤ tensFock T := by
  intro y hy
  exact mem_tensorFock_of_coeffs fun s => h (tcoef_mem hy _)

theorem tensorFock_diagAction_stable (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} {S : Submodule ℂ N}
    (hS : IsKStableSub ε E S) {a b : Fin n} (hab : ε a = ε b) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ tensFock S) : diagE ε (eT E) cpT cmT a b y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v f =>
    rw [diagE, LinearMap.add_apply, signedAction_tensor]
    refine add_mem ?_ ?_
    · simp only [eT, TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]
      exact tmul_mem_tensorFock (hS a b hab _ v.2) f
    · simp only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, LinearMap.lTensor_tmul]
      exact tmul_mem_tensorFock v.2 _
  | add x x' hx hx' =>
    rw [map_add, map_add]
    exact add_mem hx hx'

end Alg

section Form

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem tensorForm_smul_left (c : ℂ) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (c • y) y' = star c * tform y y' := by
  rw [← tform_conj y' (c • y), tform_smul_right, star_mul', tform_conj]

theorem tensorForm_signedAction_adjoint (ε : Fin n → Bool) (a b : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (sgE ε cpT cmT a b y) y' = tform y (sgE ε cpT cmT b a y') := by
  unfold sgE
  have s1 : (ε b = true ∧ ε a = true) ↔ (ε a = true ∧ ε b = true) := and_comm
  have s2 : (ε b = false ∧ ε a = false) ↔ (ε a = false ∧ ε b = false) := and_comm
  simp only [s1, s2]
  split_ifs with h1 h2
  · simp only [LinearMap.sum_apply, Module.End.mul_apply, tform_sum_left, tform_sum_right]
    refine sum_congr rfl fun x _ => ?_
    rw [tform_cpT, tform_cmT]
  · simp only [LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply, tform_neg_left,
      tform_neg_right, tform_sum_left, tform_sum_right]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [tform_cpT, tform_cmT]
  · simp [tform]

theorem tensorForm_diagAction_adjoint {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {a b : Fin n} (hab : ε a = ε b) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (diagE ε (eT E) cpT cmT a b y) y' = tform y (diagE ε (eT E) cpT cmT b a y') := by
  simp only [diagE, LinearMap.add_apply, tform_add_left, tform_add_right, tform_eT hU, tensorForm_signedAction_adjoint]
  simp [adjSign, hab]

theorem exists_highestWeight_in_stable {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (hU : IsInfUnitary ε E) {S : Submodule ℂ (TensorProduct ℂ M (Fock n))} (hfd : FiniteDimensional ℂ S)
    (hS : IsKStableSub ε (diagE ε (eT E) cpT cmT) S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε (diagE ε (eT E) cpT cmT) μ w := by
  refine exists_highestWeight_general ε (fun a b c d hab hcd =>
    diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd) ?_ hfd hS hne
  intro c w z hw0 hw
  have h := tensorForm_diagAction_adjoint hU (a := c) (b := c) rfl w w
  rw [hw, tensorForm_smul_left, tform_smul_right] at h
  have hne : tform w w ≠ 0 := fun h0 => by
    have := tform_self_re_pos hw0
    rw [h0] at this
    simp at this
  have h2 : star z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm

end Form

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section Low

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ X}

theorem dot_add_right_alt (c : ℂ) {μ : Fin n → ℝ} {v : X} (h : IsKHWVec ε A μ v) : IsKHWVec ε A μ (c • v) :=
  ⟨fun a => by rw [map_smul, h.1 a, smul_comm], fun a b h1 h2 => by rw [map_smul, h.2 a b h1 h2, smul_zero]⟩

theorem highestWeight_sub {μ : Fin n → ℝ} {v w : X} (hv : IsKHWVec ε A μ v) (hw : IsKHWVec ε A μ w) :
    IsKHWVec ε A μ (v - w) :=
  ⟨fun a => by rw [map_sub, hv.1 a, hw.1 a, smul_sub],
    fun a b h1 h2 => by rw [map_sub, hv.2 a b h1 h2, hw.2 a b h1 h2, sub_zero]⟩

variable (hK : ∀ a b c d, ε a = ε b → ε c = ε d →
  A a b * A c d - A c d * A a b = (if b = c then A a d else 0) - (if d = a then A c b else 0))
include hK

theorem loweringWord_weight {μ : Fin n → ℝ} {y : X} (hy : ∀ a, A a a y = (μ a : ℂ) • y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ (a : Fin n),
      A a a (lowWord A y l) = (lowWt μ l a : ℂ) • lowWord A y l
  | [], _, a => by simpa [lowWord, lowWt] using hy a
  | p :: l, hl, a => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have h := congrArg (fun Y : Module.End ℂ X => Y (lowWord A y l)) (hK a a c d rfl hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [loweringWord_weight hy l hl' a, map_smul, sub_eq_iff_eq_add] at h
    simp only [lowWord, lowWt]
    rw [h]
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases hac : a = c <;> by_cases had : a = d
    · subst hac; subst had; simp
    · subst hac
      simp only [if_neg had, if_neg (Ne.symm had), LinearMap.zero_apply, sub_zero]
      push_cast
      module
    · subst had
      simp only [if_neg hac, LinearMap.zero_apply, zero_sub]
      push_cast
      module
    · simp [hac, had, Ne.symm had]

theorem loweringSpan_diag_stable {μ : Fin n → ℝ} {y : X} (hy : ∀ a, A a a y = (μ a : ℂ) • y)
    (a : Fin n) : ∀ x ∈ kLowSpan ε A y, A a a x ∈ kLowSpan ε A y := by
  have : kLowSpan ε A y ≤ (kLowSpan ε A y).comap (A a a) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨l, hl, rfl⟩
    show A a a (lowWord A y l) ∈ kLowSpan ε A y
    rw [loweringWord_weight hK hy l hl a]
    exact Submodule.smul_mem _ _ (lowWord_mem hl)
  exact fun x hx => this hx

theorem loweringWord_mem_span_of_ge {μ : Fin n → ℝ} {y : X} (hy : ∀ a, A a a y = (μ a : ℂ) • y)
    {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) {a b : Fin n} (hab : b ≤ a) (hε : ε a = ε b) :
    A a b (lowWord A y l) ∈ kLowSpan ε A y := by
  rcases hab.lt_or_eq with h | rfl
  · exact kLowSpan_low_stable (c := a) (d := b) ⟨h, hε⟩ _ (lowWord_mem hl)
  · exact loweringSpan_diag_stable hK hy b _ (lowWord_mem hl)

theorem loweringWord_raise_mem_span {μ : Fin n → ℝ} {y : X} (hy : IsKHWVec ε A μ y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ a b : Fin n, a < b → ε a = ε b →
      A a b (lowWord A y l) ∈ kLowSpan ε A y
  | [], _, a, b, hab, hε => by
    simp only [lowWord]
    rw [hy.2 a b hab hε]
    exact Submodule.zero_mem _
  | p :: l, hl, a, b, hab, hε => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have ih := loweringWord_raise_mem_span hy l hl'
    have key : ∀ a' b' : Fin n, ε a' = ε b' → A a' b' (lowWord A y l) ∈ kLowSpan ε A y := by
      intro a' b' h'
      rcases lt_or_ge a' b' with h | h
      · exact ih a' b' h h'
      · exact loweringWord_mem_span_of_ge hK hy.1 hl' h h'
    have h := congrArg (fun Y : Module.End ℂ X => Y (lowWord A y l)) (hK a b c d hε hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [sub_eq_iff_eq_add] at h
    simp only [lowWord]
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (kLowSpan_low_stable hcd _ (ih a b hab hε))
    · split_ifs with hbc
      · subst hbc; exact key a d (hε.trans hcd.2)
      · simp
    · split_ifs with hda
      · subst hda; exact key c b (hcd.2.trans hε)
      · simp

theorem loweringSpan_kStable {μ : Fin n → ℝ} {y : X} (hy : IsKHWVec ε A μ y) :
    IsKStableSub ε A (kLowSpan ε A y) := by
  intro a b hab
  rcases lt_or_ge a b with h | h
  · have : kLowSpan ε A y ≤ (kLowSpan ε A y).comap (A a b) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨l, hl, rfl⟩
      exact loweringWord_raise_mem_span hK hy l hl a b h hab
    exact fun x hx => this hx
  · rcases h.lt_or_eq with h | rfl
    · exact kLowSpan_low_stable ⟨h, hab⟩
    · exact loweringSpan_diag_stable hK hy.1 b

end Low

section Weights

theorem highestWeight_smul (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  unfold dot
  simp [mul_add, sum_add_distrib]

theorem dot_positiveRootSum (lam : Fin n → ℝ) (Ph : Finset (Fin n × Fin n)) :
    dot lam (phSum Ph) = ∑ x ∈ Ph, (lam x.1 - lam x.2) := by
  unfold dot phSum
  simp only [Finset.sum_apply, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  have := Lap.LemK.cone_norm_dot_root lam x.1 x.2 1
  simpa using this

theorem normSq_nonneg_alt (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact sum_nonneg fun i _ => mul_self_nonneg (u i)

end Weights

section Form

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem highestWeight_extraction {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {V : Submodule ℂ M}
    (hcone : ∀ (μ : Fin n → ℝ) (w : M), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w →
      Lap.LemK.InRootCone (μ - lowK ε lam))
    (hcas : ∀ v ∈ genSub E V, casimir E v = ((casVal lam : ℝ) : ℂ) • v)
    {y : TensorProduct ℂ M (Fock n)} (hyT : y ∈ tensFock (genSub E V)) (hyP : y ∈ physicalSubspace ε)
    (hyD : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y = 0) (hy0 : y ≠ 0) {μ : Fin n → ℝ}
    (hy : IsKHWVec ε (diagE ε (eT E) cpT cmT) μ y) :
    μ = gaW ε lam ∧ tco (sIdx ε) y ≠ 0 ∧ IsKHWVec ε E (lowK ε lam) (tco (sIdx ε) y) := by
  have hfun : (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) = diagE ε (eT E) cpT cmT := by
    funext a b
    rw [diagE, signedAction_tensor]
    rfl
  have hy' := hy
  rw [← hfun] at hy'
  obtain ⟨s, hs0, hsK⟩ := khw_extract ε hlam hy' hy0
  have hsP : s ⊆ lfPhysModes ε := support_subset_physicalModes hyP hs0
  have hwM : tcoef ((fockBasis n).coord s) y ∈ genSub E V := tcoef_mem hyT _
  have hν := hcone _ _ hwM hs0 hsK
  have hPh : IsPosNC ε (gcPh ε s) := gc_isPosNC ε hsP
  have hwt : fockWt ε s = rhoHol ε - rhoN ε + phSum (gcPh ε s) := gc_wt_eq ε hsP
  have hcasT : casimir (eT (n := n) E) y = ((casVal lam : ℝ) : ℂ) • y := by
    rw [ssh_casimir_eT]
    obtain ⟨x, rfl⟩ := hyT
    have hcomp : casimir E ∘ₗ (genSub E V).subtype = ((casVal lam : ℝ) : ℂ) • (genSub E V).subtype := by
      ext v
      simp [hcas v v.2]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, hcomp, TensorProduct.map_smul_left,
      LinearMap.smul_apply]
  have hKv : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((μ - rhoHol ε) + rhoHol ε) y := by
    rw [sub_add_cancel]; exact hy
  have h2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hKv hcasT
  rw [Module.End.mul_apply, hyD, map_zero, smul_zero] at h2
  have hc0 := (smul_eq_zero.mp h2.symm).resolve_right hy0
  have hreal : nsq (μ - rhoHol ε + rhoC ε) = nsq lam := by
    have h3 : nsq (μ - rhoHol ε + rhoC ε) - nsq (rho n) - casVal lam = 0 := by exact_mod_cast hc0
    unfold casVal at h3
    linarith
  have hsplit : μ - rhoHol ε + rhoC ε = lam + ((μ - fockWt ε s - lowK ε lam) + phSum (gcPh ε s)) := by
    rw [hwt]
    funext a
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit, carU_nsq_add, highestWeight_smul, dot_positiveRootSum] at hreal
  have hdb : 0 ≤ dot lam (μ - fockWt ε s - lowK ε lam) := Lap.LemK.cone_norm_dot_nonneg lam _ hlam.antitone hν
  have hdp : 0 ≤ ∑ x ∈ gcPh ε s, (lam x.1 - lam x.2) :=
    sum_nonneg fun x hx => sub_nonneg.2 (hlam.antitone (hPh x hx).1.le)
  have hnn := normSq_nonneg_alt ((μ - fockWt ε s - lowK ε lam) + phSum (gcPh ε s))
  have hPh0 : gcPh ε s = ∅ := by
    by_contra hne
    have : 0 < ∑ x ∈ gcPh ε s, (lam x.1 - lam x.2) :=
      sum_pos (fun x hx => sub_pos.2 (hlam (hPh x hx).1)) (nonempty_iff_ne_empty.2 hne)
    linarith
  have hγ : (μ - fockWt ε s - lowK ε lam) + phSum (gcPh ε s) = 0 :=
    Lap.LemK.cone_norm_eq_zero _ (by linarith)
  have hp0 : phSum (gcPh ε s) = 0 := by rw [hPh0]; simp [phSum]
  rw [hp0, add_zero] at hγ
  rw [hp0, add_zero] at hwt
  have hss : s = sIdx ε := by rw [sIdx_eq]; exact gc_Ph_empty hPh0
  have hμ : μ = gaW ε lam := by
    funext a
    have ha := congrFun hγ a
    have hw := congrFun hwt a
    simp only [gaW, lowK, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at ha hw ⊢
    linarith
  subst hss
  refine ⟨hμ, hs0, ?_⟩
  have hwt2 : μ - fockWt ε (sIdx ε) = lowK ε lam := by
    rw [hwt, hμ]
    funext a
    simp only [gaW, lowK, Pi.add_apply, Pi.sub_apply]
    ring
  rw [← hwt2]
  exact hsK

theorem highestWeight_uniqueness {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hcone : ∀ (μ : Fin n → ℝ) (w : M), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w →
      Lap.LemK.InRootCone (μ - lowK ε lam))
    (hcas : ∀ v ∈ genSub E V, casimir E v = ((casVal lam : ℝ) : ℂ) • v)
    (hlowK : ∀ w ∈ genSub E V, IsKHWVec ε E (lowK ε lam) w → w ∈ V)
    {y z : TensorProduct ℂ M (Fock n)} (hyT : y ∈ tensFock (genSub E V)) (hyP : y ∈ physicalSubspace ε)
    (hyD : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y = 0) {μ : Fin n → ℝ}
    (hy : IsKHWVec ε (diagE ε (eT E) cpT cmT) μ y)
    (hzT : z ∈ tensFock (genSub E V)) (hzP : z ∈ physicalSubspace ε)
    (hzD : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0) (hz0 : z ≠ 0) {ν : Fin n → ℝ}
    (hz : IsKHWVec ε (diagE ε (eT E) cpT cmT) ν z) :
    ∃ c : ℂ, y = c • z := by
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0, zero_smul]⟩
  obtain ⟨hμ, hy1, hyK⟩ := highestWeight_extraction hlam hE hcone hcas hyT hyP hyD hy0 hy
  obtain ⟨hν, hz1, hzK⟩ := highestWeight_extraction hlam hE hcone hcas hzT hzP hzD hz0 hz
  obtain ⟨c, hc⟩ := khw_line_of_irr hE hU hV (hlowK _ (tcoef_mem hyT _) hyK) (hlowK _ (tcoef_mem hzT _) hzK)
    hyK hzK hz1
  refine ⟨c, ?_⟩
  by_contra hne
  have hd0 : y - c • z ≠ 0 := sub_ne_zero.2 hne
  rw [hμ] at hy
  rw [hν] at hz
  have hK := highestWeight_sub hy (dot_add_right_alt c hz)
  have hDd : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) (y - c • z) = 0 := by
    rw [map_sub, map_smul, hyD, hzD, smul_zero, sub_zero]
  have := highestWeight_extraction hlam hE hcone hcas (sub_mem hyT (Submodule.smul_mem _ _ hzT))
    (sub_mem hyP (Submodule.smul_mem _ _ hzP)) hDd hd0 hK
  apply this.2.1
  show tcoef ((fockBasis n).coord (sIdx ε)) (y - c • z) = 0
  rw [map_sub, map_smul]
  exact sub_eq_zero.2 hc

end Form

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section SlopeTestRemainingChoices

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem generatedSub_stable (E : Fin n → Fin n → Module.End ℂ N) (V : Submodule ℂ N) (a b : Fin n) {v : N}
    (hv : v ∈ genSub E V) : E a b v ∈ genSub E V :=
  Submodule.mem_sInf.2 fun T hT => hT.2 a b v (Submodule.mem_sInf.1 hv T hT)

theorem casimir_scalar_on_generated {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) {V : Submodule ℂ N} {c : ℂ}
    (hc : ∀ v ∈ V, casimir E v = c • v) : ∀ v ∈ genSub E V, casimir E v = c • v := by
  let T : Submodule ℂ N := LinearMap.ker (casimir E - c • (1 : Module.End ℂ N))
  have hmem : ∀ v, v ∈ T ↔ casimir E v = c • v := by
    intro v
    simp only [T, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  have hT : genSub E V ≤ T := by
    refine sInf_le ⟨fun v hv => (hmem v).2 (hc v hv), fun a b v hv => ?_⟩
    rw [hmem] at hv ⊢
    have := LinearMap.congr_fun (casimir_comm hE a b) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  exact fun v hv => (hmem v).1 (hT hv)

end SlopeTestRemainingChoices

section Form

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def tensorFormRight (w : TensorProduct ℂ M (Fock n)) : TensorProduct ℂ M (Fock n) →ₗ[ℂ] ℂ where
  toFun := tform w
  map_add' := tform_add_right w
  map_smul' c y := by rw [tform_smul_right]; rfl

end Form

theorem ker_D_eq_kLowSpan {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) (hthr : thrStar ε < h) (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) :
    ∃ z : TensorProduct ℂ D (Fock n), z ≠ 0 ∧ z ∈ tensFock V ∧
      IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z ∧
      z ∈ LinearMap.range (TensorProduct.map V.subtype (⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ)).subtype) ∧
      LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε =
        kLowSpan ε (diagE ε (eT E) cpT cmT) z ∧
      IsKIrrHW ε (diagE ε (eT E) cpT cmT) (gaW ε lam) (kLowSpan ε (diagE ε (eT E) cpT cmT) z) := by
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have e : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ) := by simp [S7.q0, Nat.cast_min]
  have hbig : max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
      (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ))) < h := by
    rw [e]; exact hthr
  have hstd : StdGap ε lam := ⟨hanti, h, hgap, lt_of_le_of_lt (le_max_left _ _) hbig⟩
  have hcone : ∀ (μ : Fin n → ℝ) (w : D), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w →
      Lap.LemK.InRootCone (μ - lowK ε lam) :=
    Lap.LemK.lowestKType_casimir_cone n ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hbig hp hq
  have hcas : ∀ v ∈ genSub E V, casimir E v = ((casVal lam : ℝ) : ℂ) • v := casimir_scalar_on_generated hE hc
  have hlowK : ∀ w ∈ genSub E V, IsKHWVec ε E (lowK ε lam) w → w ∈ V :=
    fun w hw hk => khw_lowK_mem hE hU hV hc hstd hw hk
  obtain ⟨z, hzL, hz0⟩ := line_exists hanti hE hV
  have hzD := line_ker hE hU hV hc hzL
  have hzdeg := line_deg hE hU hV hzL
  obtain ⟨⟨hzK', hzT⟩, hzP⟩ := hzL
  have hzK := (mem_highestWeightSub_iff _ _ _ z).1 hzK'
  have hVk : IsKStableSub ε E V := hV.2.1
  have hGk : IsKStableSub ε E (genSub E V) := fun a b _ v hv => generatedSub_stable E V a b hv
  have hVG : V ≤ genSub E V := fun v hv => Submodule.mem_sInf.2 fun T hT => hT.1 hv
  have hK : ∀ a b c d, ε a = ε b → ε c = ε d →
      diagE ε (eT E) cpT cmT a b * diagE ε (eT E) cpT cmT c d -
        diagE ε (eT E) cpT cmT c d * diagE ε (eT E) cpT cmT a b =
      (if b = c then diagE ε (eT E) cpT cmT a d else 0) - (if d = a then diagE ε (eT E) cpT cmT c b else 0) :=
    fun a b c d hab hcd => diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd
  set A := diagE ε (eT E) cpT cmT with hA
  set KK := LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε with hKK
  have hKKs : IsKStableSub ε A KK := by
    intro a b hab y hy
    obtain ⟨⟨hyD, hyT⟩, hyP⟩ := hy
    refine ⟨⟨?_, tensorFock_diagAction_stable ε hGk hab hyT⟩, (physSub_stable ε E).2.1 a b y hyP⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hyD ⊢
    have h1 := LinearMap.congr_fun
      (dOp_comm_diagE (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b hab) y
    have h2 := LinearMap.congr_fun
      (dOp'_comm_diagE (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b hab) y
    simp only [Module.End.mul_apply] at h1 h2
    rw [LinearMap.add_apply, h1, h2, ← map_add, ← LinearMap.add_apply, hyD, map_zero]
  have hzKK : z ∈ KK := ⟨⟨hzD, tensorFock_mono hVG hzT⟩, hzP⟩
  have hZs : IsKStableSub ε A (kLowSpan ε A z) := loweringSpan_kStable hK hzK
  have hZKK : kLowSpan ε A z ≤ KK := kLowSpan_le hKKs hzKK
  have huniq : ∀ y ∈ KK, ∀ μ, IsKHWVec ε A μ y → ∃ c : ℂ, y = c • z := by
    intro y hy μ hyK
    obtain ⟨⟨hyD, hyT⟩, hyP⟩ := hy
    exact highestWeight_uniqueness hanti hE hU hV hcone hcas hlowK hyT hyP hyD hyK (tensorFock_mono hVG hzT) hzP hzD hz0 hzK
  have hTVs : IsKStableSub ε A (tensFock V) := fun a b hab y hy => tensorFock_diagAction_stable ε hVk hab hy
  have hZV : kLowSpan ε A z ≤ tensFock V := kLowSpan_le hTVs hzT
  have hZfd : FiniteDimensional ℂ (kLowSpan ε A z) := by
    have := tensorFock_finiteDimensional (n := n) hV.1
    exact Submodule.finiteDimensional_of_le hZV

  have hfill : ∀ Y : Submodule ℂ (TensorProduct ℂ D (Fock n)), FiniteDimensional ℂ Y → IsKStableSub ε A Y →
      Y ≤ KK → kLowSpan ε A z ≤ Y → Y ≤ kLowSpan ε A z := by
    intro Y hYfd hYs hYK hZY
    let Y' : Submodule ℂ (TensorProduct ℂ D (Fock n)) :=
      { carrier := {y | y ∈ Y ∧ ∀ w ∈ kLowSpan ε A z, tform y w = 0}
        add_mem' := fun {x y} hx hy => ⟨Y.add_mem hx.1 hy.1, fun w hw => by
          rw [tform_add_left, hx.2 w hw, hy.2 w hw, add_zero]⟩
        zero_mem' := ⟨Y.zero_mem, fun w _ => by simp [tform]⟩
        smul_mem' := fun c x hx => ⟨Y.smul_mem c hx.1, fun w hw => by
          rw [tensorForm_smul_left, hx.2 w hw, mul_zero]⟩ }
    have hY'Y : Y' ≤ Y := fun y hy => hy.1
    have hY's : IsKStableSub ε A Y' := by
      intro a b hab y hy
      refine ⟨hYs a b hab y hy.1, fun w hw => ?_⟩
      rw [tensorForm_diagAction_adjoint hU hab]
      exact hy.2 _ (hZs b a hab.symm w hw)
    have hY'0 : Y' = ⊥ := by
      by_contra hne
      have : FiniteDimensional ℂ Y' := Submodule.finiteDimensional_of_le hY'Y
      obtain ⟨w, hw, hw0, μ, hwK⟩ := exists_highestWeight_in_stable hE hU this hY's hne
      obtain ⟨c, rfl⟩ := huniq w (hYK hw.1) μ hwK
      have h0 := hw.2 _ (Submodule.smul_mem _ c (self_mem_kLowSpan z))
      have hpos := tform_self_re_pos hw0
      rw [h0] at hpos
      simp at hpos
    let b := Module.finBasis ℂ (kLowSpan ε A z)
    let f : Y →ₗ[ℂ] (Fin (Module.finrank ℂ (kLowSpan ε A z)) → ℂ) :=
      LinearMap.pi fun i => (tensorFormRight ((b i : kLowSpan ε A z) : TensorProduct ℂ D (Fock n))).comp Y.subtype
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker] at hy
      have hfi : ∀ i, tform ((b i : kLowSpan ε A z) : TensorProduct ℂ D (Fock n)) (y : TensorProduct ℂ D (Fock n)) = 0 :=
        fun i => congrFun hy i
      have hyY' : (y : TensorProduct ℂ D (Fock n)) ∈ Y' := by
        refine ⟨y.2, fun w hw => ?_⟩
        have hw' : w = ∑ i, (b.repr ⟨w, hw⟩ i) • ((b i : kLowSpan ε A z) : TensorProduct ℂ D (Fock n)) := by
          have := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
          rw [Submodule.coe_sum] at this
          simp only [Submodule.coe_smul] at this
          exact this.symm
        have h1 : tform w (y : TensorProduct ℂ D (Fock n)) = 0 := by
          rw [hw', tform_sum_left]
          exact sum_eq_zero fun i _ => by rw [tensorForm_smul_left, hfi i, mul_zero]
        rw [← tform_conj, h1, star_zero]
      rw [hY'0, Submodule.mem_bot] at hyY'
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext hyY')
    have hle : Module.finrank ℂ Y ≤ Module.finrank ℂ (kLowSpan ε A z) := by
      have := LinearMap.finrank_le_finrank_of_injective hf
      simpa using this
    exact (Submodule.eq_of_le_of_finrank_le hZY hle).symm.le

  have hKKle : KK ≤ kLowSpan ε A z := by
    intro x hx
    have hxT : x ∈ tensFock (genSub E V) := hx.1.2
    rw [genSub_eq_iSup_layer hE hVk] at hxT
    have hdir : Directed (· ≤ ·) (fun k => layer ε E V k) :=
      fun i j => ⟨max i j, layer_mono (le_max_left i j), layer_mono (le_max_right i j)⟩
    have hco : ∀ s, ∃ k, tcoef ((fockBasis n).coord s) x ∈ layer ε E V k :=
      fun s => (Submodule.mem_iSup_of_directed _ hdir).1 (tcoef_mem hxT _)
    choose j hj using hco
    set J := univ.sup j
    have hxJ : x ∈ tensFock (layer ε E V J) :=
      mem_tensorFock_of_coeffs fun s => layer_mono (le_sup (mem_univ s)) (hj s)
    let Y := tensFock (layer ε E V J) ⊓ KK
    have hLs : IsKStableSub ε A (tensFock (layer ε E V J)) :=
      fun a b hab y hy => tensorFock_diagAction_stable ε (layer_kStable hE hVk J) hab hy
    have hYs : IsKStableSub ε A Y := fun a b hab y hy => ⟨hLs a b hab y hy.1, hKKs a b hab y hy.2⟩
    have hYfd : FiniteDimensional ℂ Y := by
      have := tensorFock_finiteDimensional (n := n) (finiteDimensional_layer (ε := ε) (E := E) hV.1 J)
      exact Submodule.finiteDimensional_of_le inf_le_left
    have hzY : z ∈ Y := ⟨tensorFock_mono (layer_mono (Nat.zero_le J)) hzT, hzKK⟩
    exact hfill Y hYfd hYs inf_le_right (kLowSpan_le hYs hzY) ⟨hxJ, hx⟩
  refine ⟨z, hz0, hzT, hzK, hzdeg, le_antisymm hKKle hZKK, hZfd, hZs, ?_, z, self_mem_kLowSpan z, hz0, hzK⟩
  intro S hSle hSs
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSle
  obtain ⟨w, hw, hw0, μ, hwK⟩ := exists_highestWeight_in_stable hE hU this hSs hS0
  obtain ⟨c, rfl⟩ := huniq w (hZKK (hSle hw)) μ hwK
  have hc0 : c ≠ 0 := fun h0 => hw0 (by rw [h0, zero_smul])
  have hzS : z ∈ S := by
    have := S.smul_mem c⁻¹ hw
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  exact le_antisymm hSle (kLowSpan_le hSs hzS)

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end
