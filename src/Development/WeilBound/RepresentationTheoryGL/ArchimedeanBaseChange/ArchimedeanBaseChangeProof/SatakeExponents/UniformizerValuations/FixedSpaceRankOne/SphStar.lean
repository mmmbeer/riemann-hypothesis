import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitaryStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.FinrankFixedEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentraliz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseDoubleCosetNonsplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphStarU

section
noncomputable section

open scoped Pointwise

namespace PositivityTheory.Rg.BcB.F.EigA

section Inv

variable {G : Type} [Group G]

theorem finsum_inv_eq {K : Subgroup G} (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (hK : ∀ k ∈ K, τ k ∈ K)
    {M : Type} [AddCommMonoid M] (F : G → M) (hF : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ x, F (k₁ * x * k₂) = F x) :
    ∑ᶠ q : G ⧸ K, F (q.out)⁻¹ = ∑ᶠ q : G ⧸ K, F q.out := by
  have hone : τ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  have hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹ := fun a => by
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  let σ : G → G := fun x => τ x⁻¹
  have hσmul : ∀ a b, σ (a * b) = σ a * σ b := by
    intro a b
    simp only [σ, mul_inv_rev, hmul]
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    simp only [σ, hτinv, inv_inv, hinv]
  have hσK : ∀ k ∈ K, σ k ∈ K := fun k hk => hK _ (K.inv_mem hk)
  have hFτ : ∀ x, F (τ x) = F x := fun x => by
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hdc x
    rw [e, hF _ h₁ _ h₂]
  have hFr : ∀ x, ∀ k ∈ K, F (x * k) = F x := fun x k hk => by
    simpa using hF 1 K.one_mem k hk x
  let s : G ⧸ K → G ⧸ K := fun q => ((σ q.out : G) : G ⧸ K)
  have hs : ∀ q, s (s q) = q := by
    intro q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (σ q.out)
    show ((σ ((σ q.out : G) : G ⧸ K).out : G) : G ⧸ K) = q
    rw [hk, hσmul, hσσ, QuotientGroup.mk_mul_of_mem _ (hσK _ k.2), QuotientGroup.out_eq']
  let e : G ⧸ K ≃ G ⧸ K := ⟨s, s, hs, hs⟩
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  show F (q.out)⁻¹ = F ((σ q.out : G) : G ⧸ K).out
  rw [out_mk_inv K F hFr]
  show F (q.out)⁻¹ = F (τ (q.out)⁻¹)
  rw [hFτ]

end Inv

section Top

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_support_quot (K : Subgroup G) (hK : IsOpen (K : Set G)) {M : Type} [Zero M] [TopologicalSpace M]
    (f : G → M) (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  obtain ⟨s, hs⟩ := hf.isCompact.elim_finite_subcover (fun x : tsupport f => (x : G) • (K : Set G))
    (fun x => hK.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K.one_mem, mul_one x⟩⟩)
  refine (s.finite_toSet.image (fun i : tsupport f => ((i : G) : G ⧸ K))).subset ?_
  intro q hq
  have hx : q.out ∈ tsupport f := subset_tsupport _ hq
  have h2 := hs hx
  simp only [Set.mem_iUnion] at h2
  obtain ⟨i, hi, k, hk, hik⟩ := h2
  refine ⟨i, hi, ?_⟩
  show ((i : G) : G ⧸ K) = q
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [← hik]
  exact (QuotientGroup.mk_mul_of_mem (i : G) hk).symm

end Top

section Line

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem end_eq_trace_smul (h : Module.finrank ℂ M = 1) (f : Module.End ℂ M) : f = LinearMap.trace ℂ M f • 1 := by
  haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h
  let b : Module.Basis (Fin 1) ℂ M := Module.finBasisOfFinrankEq ℂ M h
  apply b.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [LinearMap.trace_eq_matrix_trace ℂ b f, Matrix.trace_fin_one, LinearMap.toMatrix_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  conv_lhs => rw [← b.sum_repr (f (b 0))]
  rw [Fin.sum_univ_one]

theorem trace_mul_of_finrank_one (h : Module.finrank ℂ M = 1) (f g : Module.End ℂ M) :
    LinearMap.trace ℂ M (f * g) = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by
  haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h
  have hf := end_eq_trace_smul h f
  have hg := end_eq_trace_smul h g
  calc LinearMap.trace ℂ M (f * g)
      = LinearMap.trace ℂ M ((LinearMap.trace ℂ M f • 1) * (LinearMap.trace ℂ M g • 1)) := by
        rw [← hf, ← hg]
    _ = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by
        rw [smul_mul_smul_comm, one_mul, map_smul, LinearMap.trace_one, h, smul_eq_mul, Nat.cast_one, mul_one]

end Line

end PositivityTheory.Rg.BcB.F.EigA

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.EigA

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_conj_KL_ne_zero (n : ℕ) (w : Pl E) (g : UL n w) :
    ((KL n w).map (MulAut.conj g).toMonoidHom).relIndex (KL n w) ≠ 0 := by
  have hK : IsCompact (KL n w : Set (UL n w)) := GlobalTheory.LocFinU.isCompact_KL n w
  have hKo : IsOpen (KL n w : Set (UL n w)) := GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w
  have hH : IsOpen (((KL n w).map (MulAut.conj g).toMonoidHom : Subgroup (UL n w)) : Set (UL n w)) := by
    rw [GlobalTheory.LocFinU.conj_map_eq]
    exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hKo
  exact GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hH hK

theorem gelPair_split (n : ℕ) (w : Pl E) (hw : IsSplitAt w) : GelPair (KL n w) := by
  have hmem : ∀ x : GLw n w, x ∈ UL n w := fun x => by
    have h : UL n w = ⊤ := if_pos hw
    rw [h]
    exact Subgroup.mem_top x
  refine ⟨relIndex_conj_KL_ne_zero n w, fun g => ⟨Formalism.UG.P.heckecomm_tr g.1, hmem _⟩, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact Subtype.ext (Formalism.UG.P.heckecomm_tr_mul a.1 b.1)
  · intro a
    exact Subtype.ext (Formalism.UG.P.heckecomm_tr_tr a.1)
  · intro g
    obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w n g.1
    exact ⟨⟨a, hmem _⟩, Subgroup.mem_subgroupOf.2 a.2, ⟨b, hmem _⟩, Subgroup.mem_subgroupOf.2 b.2, Subtype.ext e⟩
  · intro k hk
    exact Subgroup.mem_subgroupOf.2 (Formalism.UG.P.heckecomm_tr_mem (Ov E w) k.1 (Subgroup.mem_subgroupOf.1 hk))

theorem gelPair_inert (hE : Unr E) (n : ℕ) (w : Pl E) (hw : ¬ IsSplitAt w) : GelPair (KL n w) :=
  ⟨relIndex_conj_KL_ne_zero n w, fun g => g⁻¹, fun a b => mul_inv_rev a b, fun a => inv_inv a,
    fun g => GlobalTheory.T.inverse_double_coset_nonsplit E hE w hw n g, fun _ hk => (KL n w).inv_mem hk⟩

theorem gelPair_KL (hE : Unr E) (n : ℕ) (w : Pl E) : GelPair (KL n w) := by
  by_cases hw : IsSplitAt w
  · exact gelPair_split n w hw
  · exact gelPair_inert hE n w hw


end PositivityTheory.Rg.BcB.F.EigA

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.EigA

open PositivityTheory.Rg.BcB.F.Eig (locOp lconv lstar LocAlg SphStarU)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem levOp_KL_apply {n : ℕ} {w : Pl E} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (UL n w) V) (f : UL n w → ℂ) (S : Finset (UL n w ⧸ KL n w))
    (hS : ∀ q : UL n w ⧸ KL n w, f q.out ≠ 0 → q ∈ S) (v : V) :
    levOp ρ (KL n w) (KL n w) f LinearMap.id v = ∑ q ∈ S, f q.out • ρ q.out v := by
  have hsub : Function.support (fun q : UL n w ⧸ KL n w => f q.out • (ρ q.out ∘ₗ LinearMap.id)) ⊆ ↑S := by
    intro q hq
    refine Finset.mem_coe.2 (hS q fun h0 => ?_)
    apply Function.mem_support.1 hq
    simp only [h0, zero_smul]
  rw [levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul,
    finsum_eq_sum_of_support_subset _ hsub, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply]

theorem sphStar : LocAlg → SphStarU := by
  intro hLA E _ _ _ hE n w σ hU hrank h₁ h₂ hh₁ hh₂
  have hlev : IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w) :=
    ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w, le_rfl, fun k hk => hk⟩
  have LA := fun f₁ f₂ (hf₁ : IsHecke (KL n w) f₁) (hf₂ : IsHecke (KL n w) f₂) =>
    hLA E n w σ (KL n w) hlev f₁ f₂ hf₁ hf₂
  obtain ⟨tr1, app1, hconv, hstar, hmul, -, -, -⟩ := LA h₁ h₂ hh₁ hh₂
  obtain ⟨tr2, -⟩ := LA h₂ h₁ hh₂ hh₁
  obtain ⟨trc, -⟩ := LA (lconv h₁ h₂) h₁ hconv hh₁
  obtain ⟨trs, apps, -⟩ := LA (lstar h₁) h₁ hstar hh₁
  refine ⟨?_, ?_, ?_⟩
  · rw [trc, hmul, trace_mul_of_finrank_one hrank, ← tr1, ← tr2]
  · obtain ⟨B, hBh, hBpos, hBinv⟩ := hU
    haveI : Nontrivial (fixed σ.ρ (KL n w)) := Module.nontrivial_of_finrank_eq_succ hrank
    obtain ⟨v, hv0⟩ := exists_ne (0 : fixed σ.ρ (KL n w))
    have hvfix := mem_fixed_iff.1 v.2
    let φ : UL n w → ℂ := fun x => B (σ.ρ x v) v
    have key : ∀ f, IsHecke (KL n w) f →
        twTr σ.ρ (KL n w) (KL n w) f LinearMap.id = LinearMap.trace ℂ _ (locOp σ (KL n w) f) →
        (∀ u : fixed σ.ρ (KL n w), (locOp σ (KL n w) f u).1 = levOp σ.ρ (KL n w) (KL n w) f LinearMap.id u.1) →
        twTr σ.ρ (KL n w) (KL n w) f LinearMap.id * B v v = ∑ᶠ q : UL n w ⧸ KL n w, f q.out * φ q.out := by
      intro f hf htr happ
      have hfin := finite_support_quot (KL n w) (GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w) f hf.1
      have hS : ∀ q : UL n w ⧸ KL n w, f q.out ≠ 0 → q ∈ hfin.toFinset := fun q hq => hfin.mem_toFinset.2 hq
      have hline : locOp σ (KL n w) f v = twTr σ.ρ (KL n w) (KL n w) f LinearMap.id • v := by
        rw [htr]
        conv_lhs => rw [end_eq_trace_smul hrank (locOp σ (KL n w) f)]
        rfl
      have h1 : levOp σ.ρ (KL n w) (KL n w) f LinearMap.id v.1 = twTr σ.ρ (KL n w) (KL n w) f LinearMap.id • v.1 := by
        rw [← happ, hline]
        rfl
      rw [levOp_KL_apply σ.ρ f hfin.toFinset hS] at h1
      have h2 := congrArg (fun x => B x v.1) h1
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h2
      have hsub : Function.support (fun q : UL n w ⧸ KL n w => f q.out * φ q.out) ⊆ ↑hfin.toFinset := by
        intro q hq
        exact Finset.mem_coe.2 (hS q (left_ne_zero_of_mul (Function.mem_support.1 hq)))
      rw [← h2, finsum_eq_sum_of_support_subset _ hsub]
    have hφ : ∀ x, starRingEnd ℂ (φ x) = φ x⁻¹ := by
      intro x
      show starRingEnd ℂ (B (σ.ρ x v) v) = B (σ.ρ x⁻¹ v) v
      rw [← hBh, ← hBinv x⁻¹ (v : σ.V) (σ.ρ x v), ← Module.End.mul_apply (σ.ρ x⁻¹) (σ.ρ x), ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    have hφbi : ∀ k₁ ∈ KL n w, ∀ k₂ ∈ KL n w, ∀ x, φ (k₁ * x * k₂) = φ x := by
      intro k₁ hk₁ k₂ hk₂ x
      show B (σ.ρ (k₁ * x * k₂) v) v = B (σ.ρ x v) v
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hvfix k₂ hk₂,
        ← hBinv k₁⁻¹ (σ.ρ k₁ (σ.ρ x v)) (v : σ.V), hvfix _ ((KL n w).inv_mem hk₁),
        ← Module.End.mul_apply (σ.ρ k₁⁻¹) (σ.ρ k₁), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    let F : UL n w → ℂ := fun x => starRingEnd ℂ (h₁ x) * φ x⁻¹
    have hF : ∀ k₁ ∈ KL n w, ∀ k₂ ∈ KL n w, ∀ x, F (k₁ * x * k₂) = F x := by
      intro k₁ hk₁ k₂ hk₂ x
      show starRingEnd ℂ (h₁ (k₁ * x * k₂)) * φ (k₁ * x * k₂)⁻¹ = starRingEnd ℂ (h₁ x) * φ x⁻¹
      rw [(hh₁.2 k₂ hk₂ _).2, mul_assoc, (hh₁.2 k₁ hk₁ _).1, _root_.mul_inv_rev, _root_.mul_inv_rev,
        hφbi _ ((KL n w).inv_mem hk₂) _ ((KL n w).inv_mem hk₁)]
    have eqL := key h₁ hh₁ tr1 app1
    have eqμ := key (lstar h₁) hstar trs apps
    have hBvv : starRingEnd ℂ (B v v) = B v v := (hBh v v).symm
    have hBne : B v v ≠ 0 := by
      intro h
      have := hBpos (v : σ.V) (fun h0 => hv0 (Subtype.ext h0))
      rw [h] at this
      simp at this
    have hfin1 := finite_support_quot (KL n w) (GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w) h₁ hh₁.1
    have hsupp : (Function.support fun q : UL n w ⧸ KL n w => h₁ q.out * φ q.out).Finite :=
      hfin1.subset fun q hq => left_ne_zero_of_mul (Function.mem_support.1 hq)
    have eqc : starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) * B v v =
        ∑ᶠ q : UL n w ⧸ KL n w, F q.out := by
      have h := congrArg (starRingEnd ℂ) eqL
      rw [map_mul, hBvv, map_finsum _ hsupp] at h
      rw [h]
      refine finsum_congr fun q => ?_
      simp only [map_mul, hφ, F]
    have eqμ' : twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id * B v v =
        ∑ᶠ q : UL n w ⧸ KL n w, F (q.out)⁻¹ := by
      rw [eqμ]
      refine finsum_congr fun q => ?_
      simp only [F, lstar, inv_inv]
    obtain ⟨-, τ, hmulτ, hinvτ, hdcτ, hKτ⟩ := gelPair_KL hE n w
    have heq := finsum_inv_eq τ hmulτ hinvτ hdcτ hKτ F hF
    rw [← eqμ', ← eqc] at heq
    exact mul_right_cancel₀ hBne heq
  · have h := (GlobalTheory.T.twistedTrace_indicator_level_localUnitary E n w (KL n w) hlev σ).2.2.1
    rw [h, Subgroup.relIndex_self, hrank]
    simp

end PositivityTheory.Rg.BcB.F.EigA

end
end
