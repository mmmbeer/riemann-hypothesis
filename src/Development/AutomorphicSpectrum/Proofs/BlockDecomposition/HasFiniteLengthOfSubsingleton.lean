import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedRankQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantsFiniteOfSmoothLevi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.CoinvExact

theorem hasFiniteLength_of_exact {G A B C : Type} [Group G] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (α : Representation ℂ G A) (β : Representation ℂ G B) (γ : Representation ℂ G C)
    (f : α.IntertwiningMap β) (g : β.IntertwiningMap γ)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hA : HasFiniteLength α) (hC : HasFiniteLength γ) : HasFiniteLength β := by
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule α β f
  let g' := Representation.IntertwiningMap.equivLinearMapAsModule β γ g
  have hg' : Function.Surjective g' := hg
  have hr : IsFiniteLength (MonoidAlgebra ℂ G) (LinearMap.range f') :=
    IsFiniteLength.of_surjective hA f'.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.range f').subtype g' := by
    intro y
    have h1 : g' y = 0 ↔ g y = 0 := Iff.rfl
    have h2 : y ∈ Set.range (LinearMap.range f').subtype ↔ y ∈ Set.range f := by
      constructor
      · rintro ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨⟨f' a, ⟨a, rfl⟩⟩, rfl⟩
    rw [h1, h2]
    exact hfg y
  have hlen := Module.length_eq_add_of_exact (LinearMap.range f').subtype g'
    (LinearMap.range f').injective_subtype hg' hex
  rw [HasFiniteLength, ← Module.length_ne_top_iff, hlen]
  exact WithTop.add_ne_top.2 ⟨Module.length_ne_top_iff.2 hr, Module.length_ne_top_iff.2 hC⟩

section Coinv

variable {Γ G V₁ V₂ : Type} [Group Γ] [Group G] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {τ₁ : Representation ℂ (Γ × G) V₁} {τ₂ : Representation ℂ (Γ × G) V₂}

theorem twRel_le_comap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ).comap φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, v, rfl⟩
  refine Submodule.subset_span ⟨γ, φ v, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]

def coinvMap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    (coinv τ₁ ψ).IntertwiningMap (coinv τ₂ ψ) where
  toLinearMap := Submodule.mapQ _ _ φ.toLinearMap (twRel_le_comap φ ψ)
  isIntertwining' := fun g => by
    refine Submodule.linearMap_qext _ ?_
    ext v
    exact congrArg (Submodule.Quotient.mk (p := twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ))
      (φ.isIntertwining _ _ (1, g) v)

theorem coinvMap_mk (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) (v : V₁) :
    coinvMap φ ψ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v) := rfl

theorem twRel_le_map (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ).map φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, u, rfl⟩
  obtain ⟨v, rfl⟩ := hφ u
  refine ⟨τ₁ (γ, 1) v - (ψ γ : ℂ) • v, Submodule.subset_span ⟨γ, v, rfl⟩, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]

theorem coinvMap_surjective (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    Function.Surjective (coinvMap φ ψ) := by
  intro y
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hφ u
  exact ⟨Submodule.Quotient.mk v, rfl⟩

end Coinv

theorem coinvMap_exact {Γ G W V U : Type} [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {τW : Representation ℂ (Γ × G) W} {τ : Representation ℂ (Γ × G) V}
    {τU : Representation ℂ (Γ × G) U} (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU)
    (hf : Function.Surjective f) (hif : Function.Exact i f) (ψ : Γ →* ℂˣ) :
    Function.Exact (coinvMap i ψ) (coinvMap f ψ) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro h
    have hv : f v ∈ twRel (τU.comp (MonoidHom.inl Γ G)) ψ :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨r, hr, hrv⟩ := twRel_le_map f hf ψ hv
    have hrv' : f r = f v := hrv
    have hz : f (v - r) = 0 := by rw [map_sub, hrv', sub_self]
    obtain ⟨w, hw⟩ := (hif (v - r)).1 hz
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    rw [coinvMap_mk, hw]
    exact (Submodule.Quotient.eq _).2 (by simpa using (Submodule.neg_mem _ hr))
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h0 : f (i w) = 0 := (hif (i w)).2 ⟨w, rfl⟩
    rw [← hy, coinvMap_mk, coinvMap_mk, h0]
    rfl

theorem main : ∀ (Γ G W V U : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (τW : Representation ℂ (Γ × G) W) (τ : Representation ℂ (Γ × G) V) (τU : Representation ℂ (Γ × G) U) (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU), Function.Surjective f → Function.Exact i f → ∀ ψ : Γ →* ℂˣ, HasFiniteLength (coinv τW ψ) → HasFiniteLength (coinv τU ψ) → HasFiniteLength (coinv τ ψ) := by
  intro Γ G W V U _ _ _ _ _ _ _ _ τW τ τU i f hf hif ψ hW hU
  exact hasFiniteLength_of_exact _ _ _ (coinvMap i ψ) (coinvMap f ψ)
    (coinvMap_surjective f hf ψ) (coinvMap_exact i f hf hif ψ) hW hU

end GlobalTheory.CompanionTheory.CoinvExact
end
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_coinvariants_exact : ∀ (Γ G W V U : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (τW : Representation ℂ (Γ × G) W) (τ : Representation ℂ (Γ × G) V) (τU : Representation ℂ (Γ × G) U) (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU), Function.Surjective f → Function.Exact i f → ∀ ψ : Γ →* ℂˣ, HasFiniteLength (coinv τW ψ) → HasFiniteLength (coinv τU ψ) → HasFiniteLength (coinv τ ψ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CoinvExact.main
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_twisted_rank_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] (κ : ℕ), κ = Fintype.card c → ∀ θ : GL a k →* ℂˣ, Module.Finite ℂ (SB (RankIn k a c {κ}) ⧸ twRel (rightRep (k := k) a c κ) θ) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep | exact GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep <;> assumption)
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinvariants_finite_of_smooth_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd | exact GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd <;> assumption)
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen.Swap

section Abstract

variable {Γ G V V' : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem coinv_of_intertwine (τ : Representation ℂ (Γ × G) V) (τ' : Representation ℂ (Γ × G) V')
    (ψ ψ' : Γ →* ℂˣ) (T : V ≃ₗ[ℂ] V') (θ : Γ →* Γ) (θ' : G →* G)
    (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ')
    (hT : ∀ γ g v, T (τ (γ, g) v) = τ' (θ γ, θ' g) (T v)) (hψ : ∀ γ, ψ' (θ γ) = ψ γ)
    (h : HasFiniteLength (coinv τ' ψ')) : HasFiniteLength (coinv τ ψ) := by
  have key : ∀ (γ : Γ) (v : V), T (τ (γ, 1) v - (ψ γ : ℂ) • v) =
      τ' (θ γ, 1) (T v) - (ψ' (θ γ) : ℂ) • T v := fun γ v => by
    rw [map_sub, map_smul, hT, map_one, hψ]
  have hrel : (twRel (τ.comp (MonoidHom.inl Γ G)) ψ).map (T : V →ₗ[ℂ] V') =
      twRel (τ'.comp (MonoidHom.inl Γ G)) ψ' := by
    unfold twRel
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨γ, v, rfl⟩, rfl⟩
      exact ⟨θ γ, T v, key γ v⟩
    · rintro ⟨γ', v', rfl⟩
      obtain ⟨γ, rfl⟩ := hθ γ'
      refine ⟨_, ⟨γ, T.symm v', rfl⟩, ?_⟩
      have := key γ (T.symm v')
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
  let E : (coinv τ ψ).Equiv ((coinv τ' ψ').comp θ' : Representation ℂ G _) :=
    Representation.Equiv.mk (Submodule.Quotient.equiv _ _ T hrel) fun g =>
      Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        show Submodule.Quotient.mk (T (τ (1, g) v)) = Submodule.Quotient.mk (τ' (1, θ' g) (T v))
        rw [hT, map_one])
  exact HasFiniteLength.of_equiv ((hasFiniteLength_comp_iff _ θ' hθ').2 h) E.symm

end Abstract

section Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def invT (n : Type) [Fintype n] [DecidableEq n] : GL n k →* GL n k where
  toFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [transpose_mul])

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invT_invT (g : GL a k) : invT a (invT a g) = g := Units.ext (transpose_transpose _)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invT_surjective : Function.Surjective (invT a : GL a k → GL a k) :=
  fun g => ⟨invT a g, invT_invT g⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_invT (g : GL a k) :
    GeneralLinearGroup.det (invT a g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  refine Units.ext ?_
  show ((g⁻¹).valᵀ).det = ((g⁻¹ : GL a k).val).det
  rw [det_transpose]

def trHomeo (a b : Type) : Matrix b a k ≃ₜ Matrix a b k where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

def trSB (a b : Type) : SB (Matrix b a k) ≃ₗ[ℂ] SB (Matrix a b k) where
  toFun Φ := ⟨fun y => Φ.1 yᵀ, Φ.2.1.comp_continuous (trHomeo b a).continuous,
    Φ.2.2.comp_homeomorph (trHomeo b a)⟩
  invFun Φ := ⟨fun y => Φ.1 yᵀ, Φ.2.1.comp_continuous (trHomeo a b).continuous,
    Φ.2.2.comp_homeomorph (trHomeo a b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv Φ := Subtype.ext (funext fun y => congrArg Φ.1 (transpose_transpose y))
  right_inv Φ := Subtype.ext (funext fun y => congrArg Φ.1 (transpose_transpose y))

theorem omChar_swap (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) :
    omChar b a μ (invT b h, invT a g) = omChar a b μ (g, h) := by
  simp only [omChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    detChar_apply, det_invT, MonoidHom.inv_apply, map_inv, neg_div, absPow_neg, inv_inv, mul_inv]
  exact mul_comm _ _

theorem trSB_omega (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)) :
    trSB a b (omega a b μ (g, h) Φ) = omega b a μ (invT b h, invT a g) (trSB a b Φ) := by
  refine Subtype.ext (funext fun y => ?_)
  show (omChar a b μ (g, h) : ℂ) * Φ.1 (act yᵀ (g, h)) =
    (omChar b a μ (invT b h, invT a g) : ℂ) * Φ.1 (act y (invT b h, invT a g))ᵀ
  have e : act yᵀ (g, h) = (act y (invT b h, invT a g))ᵀ := by
    show (h⁻¹).val * yᵀ * g.val = (g.valᵀ * y * (h⁻¹).valᵀ)ᵀ
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [omChar_swap, e]

end Model

theorem coinv_swap_finiteLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ), HasFiniteLength (coinv (omega b a μ⁻¹) (detChar b χ⁻¹)) → HasFiniteLength (coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)) := by
  intro k _ _ _ _ a b _ _ _ _ μ χ h
  refine coinv_of_intertwine _ _ _ _ (trSB a b) (invT b) (invT a) invT_surjective invT_surjective
    (fun γ g v => trSB_omega μ⁻¹ g γ v) (fun γ => ?_) h
  simp [det_invT]

end GlobalTheory.CompanionTheory.ThetaGLLen.Swap
end
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_coinvariants_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ), HasFiniteLength (coinv (omega b a μ⁻¹) (detChar b χ⁻¹)) → HasFiniteLength (coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ThetaGLLen.Swap.coinv_swap_finiteLength
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Small

variable {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

theorem hasFiniteLength_of_subsingleton [Subsingleton V] (ρ : Representation ℂ G V) : HasFiniteLength ρ := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, inferInstance⟩

theorem coinv_of_subsingleton [Subsingleton V] (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ) :
    HasFiniteLength (coinv τ ψ) :=
  have : Subsingleton (V ⧸ twRel (τ.comp (MonoidHom.inl Γ G)) ψ) := Submodule.Quotient.subsingleton_iff.2 (Subsingleton.elim _ _)
  hasFiniteLength_of_subsingleton _

theorem coinv_of_equiv {τ : Representation ℂ (Γ × G) V} {τ' : Representation ℂ (Γ × G) U} (E : τ.Equiv τ')
    (ψ : Γ →* ℂˣ) (h : HasFiniteLength (coinv τ' ψ)) : HasFiniteLength (coinv τ ψ) := by
  let τ₀ : Representation ℂ (Γ × G) PUnit := Representation.trivial ℂ _ _
  let i : τ₀.IntertwiningMap τ := ⟨0, fun g => by ext v; simp⟩
  refine GlobalTheory.T.finite_length_coinvariants_exact Γ G PUnit V U τ₀ τ τ' i E.toIntertwiningMap E.toLinearEquiv.surjective
    (fun x => ?_) ψ (coinv_of_subsingleton _ _) h
  constructor
  · intro hx
    refine ⟨0, ?_⟩
    have : E.toLinearEquiv x = 0 := hx
    exact ((E.toLinearEquiv.map_eq_zero_iff).1 this).symm ▸ rfl
  · rintro ⟨y, rfl⟩
    show E.toLinearEquiv 0 = 0
    simp

end Small

section Strata

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem stratum_finiteLength (hI : InductionFiniteLength k) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) (κ : ℕ)
    (ψ : GL a k →* ℂˣ) : HasFiniteLength (coinv (omegaOn a b μ {κ}) ψ) := by
  by_cases hκ : κ ≤ Fintype.card b
  · let e : Fin κ ⊕ Fin (Fintype.card b - κ) ≃ b :=
      (stdSum (Nat.add_sub_cancel' hκ)).trans (Fintype.equivFin b).symm
    obtain ⟨E⟩ := GlobalTheory.T.omega_equiv_induced_fibre k a b (Fin κ) (Fin (Fintype.card b - κ)) e κ (Fintype.card_fin κ).symm μ hμ
    refine coinv_of_equiv E ψ (GlobalTheory.T.coinvariants_finite_of_smooth_levi k hI _ _ b _ _ e _ (GlobalTheory.T.fibre_representation_smooth k a _ _ μ hμ κ) ψ ?_)
    let τ := fibRep (k := k) a (Fin κ) (Fin (Fintype.card b - κ)) μ κ
    let ω : GL a k →* ℂˣ := (fibChar a (Fin κ) (Fin (Fintype.card b - κ)) μ).comp (MonoidHom.inl _ _)
    have hfin := GlobalTheory.T.finite_twisted_rank_quotient k a (Fin κ) κ (Fintype.card_fin κ).symm (ψ * ω⁻¹)
    have hle : twRel (rightRep (k := k) a (Fin κ) κ) (ψ * ω⁻¹) ≤ twRel (τ.comp (MonoidHom.inl _ _)) ψ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, φ, rfl⟩
      have h1 : ∀ φ' : SB (RankIn k a (Fin κ) {κ}), τ (g, 1) φ' = (ω g : ℂ) • rightRep (k := k) a (Fin κ) κ g φ' := by
        intro φ'
        refine Subtype.ext (funext fun y => ?_)
        show (fibRep a (Fin κ) (Fin (Fintype.card b - κ)) μ κ (g, 1, 1) φ').1 y = _
        rw [fibRep_apply]
        rfl
      have h2 : rightRep (k := k) a (Fin κ) κ g φ - (((ψ * ω⁻¹) g : ℂˣ) : ℂ) • φ =
          ((ω g)⁻¹ : ℂˣ).1 • (τ (g, 1) φ - (ψ g : ℂ) • φ) := by
        rw [h1, smul_sub, smul_smul, smul_smul]
        simp [mul_comm]
      rw [SetLike.mem_coe, h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, φ, rfl⟩)
    exact Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  · have : IsEmpty (RankIn k a b {κ}) := ⟨fun x => hκ (by
      have h := rank_le_card_height x.1
      rw [show x.1.rank = κ from x.2] at h
      exact h)⟩
    have : Subsingleton (SB (RankIn k a b {κ})) :=
      ⟨fun f g => Subtype.ext (funext fun x => isEmptyElim x)⟩
    exact coinv_of_subsingleton _ _

theorem filt_finiteLength (hI : InductionFiniteLength k) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (ψ : GL a k →* ℂˣ) (N : ℕ) (j κ : ℕ) (h : κ + j = N) :
    HasFiniteLength (coinv (filt a b μ (Set.Iio N) κ).toRepresentation ψ) := by
  induction j generalizing κ with
  | zero =>
    obtain rfl : κ = N := h
    have : Subsingleton (filt a b μ (Set.Iio κ) κ).toSubmodule :=
      ⟨fun f g => Subtype.ext (Subtype.ext (funext fun x =>
        (f.2 x x.2).trans (g.2 x x.2).symm))⟩
    exact coinv_of_subsingleton _ _
  | succ j ih =>
    have hs : ∀ r, r ∈ ({κ} : Set ℕ) ↔ κ ≤ r ∧ r < κ + 1 := fun r => by
      rw [Set.mem_singleton_iff]; omega
    have hmn : κ + 1 ≤ N := by omega
    have hle : (filt a b μ (Set.Iio N) (κ + 1)).toSubmodule ≤ (filt a b μ (Set.Iio N) κ).toSubmodule :=
      fun Φ hΦ x hx => hΦ x (Nat.lt_succ_of_lt hx)
    let i : (filt a b μ (Set.Iio N) (κ + 1)).toRepresentation.IntertwiningMap
        (filt a b μ (Set.Iio N) κ).toRepresentation :=
      ⟨Submodule.inclusion hle, fun g => by ext; rfl⟩
    refine GlobalTheory.T.finite_length_coinvariants_exact _ _ _ _ _ _ _ _ i (resFilt μ hmn hs) (resFilt_surjective μ hmn hs) (fun Φ => ?_) ψ
      (ih (κ + 1) (by omega)) (stratum_finiteLength hI hμ κ ψ)
    constructor
    · intro h0
      have := (ker_resFilt μ hmn hs Φ).1 h0
      exact ⟨⟨Φ.1, this⟩, rfl⟩
    · rintro ⟨Ψ, rfl⟩
      exact (ker_resFilt μ hmn hs _).2 Ψ.2

def toFilt (μ : kˣ →* ℂˣ) (N : ℕ) (hN : ∀ x : Matrix b a k, x.rank < N) :
    (omega a b μ).Equiv (filt a b μ (Set.Iio N) 0).toRepresentation :=
  .mk
    { toFun := fun Φ => ⟨⟨fun x => Φ.1 x.1, comp_mem_SB_of_isInducing IsInducing.subtypeVal Φ isClosed_univ
          (fun _ => trivial) fun x _ _ => ⟨⟨x, hN x⟩, rfl⟩⟩, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun Ψ => ⟨fun x => Ψ.1.1 ⟨x, hN x⟩, comp_mem_SB_of_isInducing
          ((IsInducing.subtypeVal.of_comp_iff (f := fun x : Matrix b a k => (⟨x, hN x⟩ : RankIn k a b (Set.Iio N)))).1 IsInducing.id) Ψ.1 isClosed_univ (fun _ => trivial)
          fun x _ _ => ⟨x.1, rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } (fun _ => rfl)

end Strata

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

abbrev thetaQuot (μ χ : kˣ →* ℂˣ) := coinv (omega a b μ⁻¹) (detChar a χ)

variable {a b}


theorem thetaQuot_finiteLength (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuot a b μ χ) := by
  have hI : InductionFiniteLength k := (hBZ k).2.2.1
  have hN : ∀ x : Matrix b a k, x.rank < Fintype.card a + 1 := fun x =>
    Nat.lt_succ_of_le (rank_le_card_width x)
  exact coinv_of_equiv (toFilt μ⁻¹ _ hN) _
    (filt_finiteLength hI hμ.inv _ (Fintype.card a + 1) (Fintype.card a + 1) 0 (by omega))

variable (a b)

abbrev thetaQuotSwap (μ χ : kˣ →* ℂˣ) :=
  coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)

variable {a b}

theorem thetaQuotSwap_finiteLength (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuotSwap a b μ χ) :=
  GlobalTheory.T.finite_length_coinvariants_swap k a b μ χ (thetaQuot_finiteLength hBZ hμ χ⁻¹)

theorem main (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (n r : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuot (k := k) (Fin r) (Fin n) μ χ) ∧
      HasFiniteLength (thetaQuotSwap (k := k) (Fin r) (Fin n) μ χ) :=
  ⟨thetaQuot_finiteLength hBZ hμ χ, thetaQuotSwap_finiteLength hBZ hμ χ⟩

end Main

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end
