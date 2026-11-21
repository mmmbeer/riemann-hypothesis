import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealsMeetingSubspaceCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientDualWeylEmbedsHighestWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycFieldA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotient

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial TensorProduct

namespace GlobalTheory.ChainStab

theorem hw_rowHom (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    ∃ μ : Fin r → ℕ, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (Formalism.GradedWeylDivisibility.hw R hn ν) μ := by
  unfold Formalism.GradedWeylDivisibility.hw
  exact ⟨_, IsWeightedHomogeneous.prod _ _ _ fun s _ => (Formalism.GradedWeylDivisibility.lpMinor_rowHom R _ _ _).pow _⟩

theorem homZ_of_homN {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℕ)
    (h : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f (fun i => (μ i : ℤ)) := by
  intro m hm
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast, h hm]

theorem applyWord_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ' : Fin r → ℤ, IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) (Formalism.GradedWeylDivisibility.applyWord R w f) μ' := by
  induction w with
  | nil => exact ⟨μ, hf⟩
  | cons x w ih =>
    obtain ⟨μ', h⟩ := ih
    exact ⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_G_of_homog x.1 x.2.1 _ μ' h x.2.2⟩

theorem comp_of_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (m : Fin r → ℕ) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = f ∨
      weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = 0 := by
  classical
  by_cases hg : f = 0
  · right; rw [hg, map_zero]
  · obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.1 hg
    have hN : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m0) := by
      intro d hd
      have h1 := hf hd
      have h2 := hf hm0
      rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast] at h1 h2
      funext i
      exact_mod_cast congrFun (h1.trans h2.symm) i
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hN)]
    split_ifs
    · left; rfl
    · right; rfl

theorem weyl_comp_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (m : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  obtain ⟨μ0, h0⟩ := hw_rowHom R hn ν
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ⟩ := applyWord_homZ _ _ (homZ_of_homN _ _ h0) w
    rcases comp_of_homZ _ μ hμ m with h | h <;> rw [h]
    · exact Submodule.subset_span ⟨w, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem tprod_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (x : ∀ i, A i) (hx : ∀ i, x i ∈ B i) :
    PiTensorProduct.tprod O x ∈ tensSub B :=
  LinearMap.mem_range.2 ⟨PiTensorProduct.tprod O (fun i => ⟨x i, hx i⟩), by rw [PiTensorProduct.map_tprod]; rfl⟩

theorem map_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (f : ∀ i, A i →ₗ[O] A i)
    (hf : ∀ i, ∀ x ∈ B i, f i x ∈ B i) (y : ⨂[O] i, A i) (hy : y ∈ tensSub B) :
    PiTensorProduct.map f y ∈ tensSub B := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  refine LinearMap.mem_range.2 ⟨PiTensorProduct.map (fun i => (f i).restrict (hf i)) z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rfl

variable {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam : ι → ℕ → ℕ}

theorem grp_stab (s : Finset ι) (g : ι → GL (Fin N) O) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), grp O N lam g y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  have h1 : grp O N lam g = PiTensorProduct.map
      (fun i => Formalism.UG.dualWeylRep O N N (res N (lam i)) (g i)) := rfl
  rw [h1]
  refine map_mem_tensSub _ _ (fun i x hx => ?_) y hy
  unfold chainB at hx ⊢
  split_ifs at hx ⊢ with hi
  · exact Submodule.mem_top
  · exact Formalism.UG.P.weyl_module_GL_stable O N N le_rfl (res N (lam i)) (g i) x.1 hx

theorem proj_stab (s : Finset ι) (τ : ι) (w : Fin N → ℕ) (a : Module.End O (NablaT O N lam))
    (ha : IsProj O N lam τ w a) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), a y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    rw [map_smul, PiTensorProduct.map_tprod, map_smul]
    refine Submodule.smul_mem _ c ?_
    let x : ∀ i, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)) := fun i => (f i : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)))
    have hc := Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N (res N (lam τ)) w _ (x τ).2
    change a (PiTensorProduct.tprod O x) ∈ _
    rw [ha x ⟨_, hc⟩ rfl]
    apply tprod_mem_tensSub
    intro i
    by_cases hi : i = τ
    · subst hi
      rw [Function.update_self]
      have hf := (f i).2
      unfold chainB at hf ⊢
      split_ifs at hf ⊢ with hs
      · exact Submodule.mem_top
      · exact weyl_comp_mem O le_rfl (res N (lam i)) w _ hf
    · rw [Function.update_of_ne hi]
      exact (f i).2
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ (h₁ (LinearMap.mem_range_self _ _)) (h₂ (LinearMap.mem_range_self _ _))

end GlobalTheory.ChainStab

namespace GlobalTheory.ExpFrame

open GlobalTheory.ChainStab

theorem alg_chainB_stable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (s : Finset ι) (a : alg O N lam),
    ∀ x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s), a • x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s) := by
  intro O _ _ _ _ N ι _ _ lam s a
  let L := tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s)
  let St : Subalgebra O (Module.End O (NablaT O N lam)) :=
    { carrier := {f | ∀ x ∈ L, f x ∈ L}
      mul_mem' := fun ha hb x hx => ha _ (hb x hx)
      add_mem' := fun ha hb x hx => L.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := fun c x hx => by
        rw [Module.algebraMap_end_apply]; exact L.smul_mem c hx }
  have hle : alg O N lam ≤ St := Algebra.adjoin_le (by
    rintro f (⟨g, rfl⟩ | ⟨τ, w, hf⟩)
    · exact grp_stab s g
    · exact proj_stab s τ w f hf)
  intro x hx
  exact hle a.2 x hx

end GlobalTheory.ExpFrame

end
end

section
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame

theorem map_mk_smul_sum {O A : Type} [CommRing O] [Ring A] [Algebra O A] {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W] (U : Submodule A V)
    (ψ : U →ₗ[A] W) {κ : Type} (S : Finset κ) (c : O) (v : κ → V) (hv : ∀ s, v s ∈ U) (x : V) (hx : x ∈ U)
    (e : x = c • ∑ s ∈ S, v s) : c • ∑ s ∈ S, ψ ⟨v s, hv s⟩ = ψ ⟨x, hx⟩ := by
  have e' : (⟨x, hx⟩ : U) = c • ∑ s ∈ S, (⟨v s, hv s⟩ : U) := by
    apply Subtype.ext
    simpa using e
  rw [e', LinearMap.map_smul_of_tower, map_sum]

section
variable {O A G I : Type} [CommRing O] [Ring A] [Algebra O A] [Group G] (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A)
  (tr : I → Finset G) (cst : I → O)

theorem hecke_values_mem {V : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule A V) (t : MvPolynomial I O) :
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ U) →
      ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f hf g
    rw [hV.1 c f]
    exact U.smul_of_tower_mem c (hf g)
  | add p q hp hq =>
    intro f hf g
    rw [add_smul]
    exact U.add_mem (hp f hf g) (hq f hf g)
  | mul_X p i hp =>
    intro f hf g
    rw [mul_smul]
    apply hp
    intro g'
    rw [hV.2 i f g']
    exact U.smul_of_tower_mem _ (U.sum_mem fun s _ => hf _)

theorem hecke_values_map {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s))
    (U : Submodule A V)
    (ψ : U →ₗ[A] W) (t : MvPolynomial I O) :
    ∀ (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
      (hf : ∀ g, (f : G → V) g ∈ U), (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
      ∀ g (h : ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
        ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨_, h⟩ := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f φ hf hφ g h
    have e : (⟨_, h⟩ : U) = c • ⟨(f : G → V) g, hf g⟩ := by
      apply Subtype.ext
      simp only [hV.1 c f]
      rfl
    rw [e, LinearMap.map_smul_of_tower, ← hφ g, hW.1 c φ]
    rfl
  | add p q hp hq =>
    intro f φ hf hφ g h
    have hp' := hecke_values_mem Γ jK tr cst hV U p f hf g
    have hq' := hecke_values_mem Γ jK tr cst hV U q f hf g
    have e : (⟨_, h⟩ : U) = ⟨_, hp'⟩ + ⟨_, hq'⟩ := by
      apply Subtype.ext
      simp only [add_smul]
      rfl
    rw [e, map_add, ← hp f φ hf hφ g hp', ← hq f φ hf hφ g hq', add_smul]
    rfl
  | mul_X p i hp =>
    intro f φ hf hφ g h
    have hX := hecke_values_mem Γ jK tr cst hV U (X i) f hf
    have hφX : ∀ g', (((X i : MvPolynomial I O) • φ : Forms O Γ jK W) : G → W) g' = ψ ⟨_, hX g'⟩ := by
      intro g'
      refine (hW.2 i φ g').trans (Eq.trans ?_ (map_mk_smul_sum U ψ (tr i) (cst i) (fun s => (f : G → V) (g' * s))
        (fun s => hf _) _ (hX g') (hV.2 i f g')))
      exact congrArg (fun z => cst i • z) (Finset.sum_congr rfl fun s _ => hφ (g' * s))
    have h2 : ((p • ((X i : MvPolynomial I O) • f) : Forms O Γ jK V) : G → V) g ∈ U := by
      rw [← mul_smul]
      exact h
    have e : (⟨_, h⟩ : U) = ⟨_, h2⟩ := by
      apply Subtype.ext
      simp only [mul_smul]
    rw [e, mul_smul]
    exact hp _ _ hX hφX g h2

theorem hecke_stable_nat (V W : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s)) :
    HeckeStable O Γ jK (MvPolynomial I O) V ∧ HeckeNat O Γ jK (MvPolynomial I O) V W :=
  ⟨fun U t f hf => hecke_values_mem Γ jK tr cst hV U t f hf,
    fun U ψ t f φ hf hf' hφ g => hecke_values_map Γ jK tr cst hV hW U ψ t f φ hf hφ g (hf' g)⟩

end

set_option maxHeartbeats 1000000 in

theorem heckeStable_heckeNat_of_isHecke : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  intro l _ ι _ _ N F lam jK i1 W i2 i3 i4 i5 i6 hV hW
  refine @hecke_stable_nat F.O (alg F.O N lam) F.G F.I _ _ _ _ F.Γ F.K jK F.tr F.cst (NablaT F.O N lam) W _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · exact hV
  · exact hW

end GlobalTheory.ExpFrame
end

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  atlas_forward_decl GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke
end

section
section
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.FrobEmb

theorem norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

def compPerm {E C : Type} [Field E] [Field C] (f : C ≃+* C) : Equiv.Perm (E →+* C) where
  toFun τ := f.toRingHom.comp τ
  invFun τ := f.symm.toRingHom.comp τ
  left_inv τ := by ext x; simp
  right_inv τ := by ext x; simp

theorem exists_frobPerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E →
    ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  intro E _ _ _ l _ _
  obtain ⟨Fr, hFr⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := ReciprocityTheory.DiscreteGroups.LocalClassField.Q0 l) ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_base_field
  refine ⟨compPerm Fr.toRingEquiv, ?_, fun τ => rfl⟩
  intro τ x
  have hx : ‖τ (x : E)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int τ x.isIntegral_coe)
  have h := hFr (τ (x : E)) hx
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.residue_cardinality_base_field] at h
  exact h

end GlobalTheory.FrobEmb
end

open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E → ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  atlas_forward_decl GlobalTheory.FrobEmb.exists_frobPerm
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpLink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

theorem cj_cj (τ : E →+* PadicAlgCl l) : cj (cj τ) = τ := by
  ext x; simp [cj, IsCMField.complexConj_apply_apply]

theorem cj_injective : Function.Injective (cj : (E →+* PadicAlgCl l) → (E →+* PadicAlgCl l)) := fun a b h => by
  rw [← cj_cj a, h, cj_cj]

open Classical in

def glue {ι X : Type} [Inhabited X] (inc : ι → (E →+* PadicAlgCl l)) (f g : ι → X) (i : E →+* PadicAlgCl l) : X :=
  if h : ∃ τ, inc τ = i then f h.choose else if h' : ∃ τ, cj (inc τ) = i then g h'.choose else default

theorem glue_inc {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (inc τ) = f τ := by
  have h : ∃ τ', inc τ' = inc τ := ⟨τ, rfl⟩
  rw [glue, dif_pos h]
  exact congrArg f (hH.1 h.choose_spec)

theorem glue_cj {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (cj (inc τ)) = g τ := by
  have h : ¬ ∃ τ', inc τ' = cj (inc τ) := fun ⟨τ', h'⟩ => hH.2.1 τ τ' h'.symm
  have h' : ∃ τ', cj (inc τ') = cj (inc τ) := ⟨τ, rfl⟩
  rw [glue, dif_neg h, dif_pos h']
  exact congrArg g (hH.1 (cj_injective h'.choose_spec))

def labels {ι : Type} (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (mu : ι → ℕ → ℕ) :
    Formalism.CohomologicalDescent.WorkedExample.Labels (E →+* PadicAlgCl l) P.Nr where
  cc := cj
  Φ := Set.range inc
  U := glue inc (fun τ a => W.U P τ (a : ℕ)) (fun τ a => (h0 P : ℤ) - W.U P τ ((Fin.rev a : Fin P.Nr) : ℕ))
  U' := glue inc (fun τ a => Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) (a : ℕ))
    (fun τ a => (h0 P : ℤ) - Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) ((Fin.rev a : Fin P.Nr) : ℕ))
  bot := glue inc (fun τ => W.bot P τ) (fun τ => (h0 P : ℤ) - (W.bot P τ + (P.t : ℤ) - 1))

theorem U_block {ι : Type} {P : Par} {W : Wts ι} (hOk : W.Ok P) (τ : ι) (s : ℕ) (hs : s < P.t) :
    W.U P τ (kc P + W.j τ + P.t - 1 - s) = W.bot P τ + (s : ℤ) := by
  have h1 := hOk.block τ (kc P + W.j τ + P.t - 1 - s) (by omega) (by omega)
  have h2 := hOk.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)
  simp only [Wts.bot, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, h1, h2]
  omega

theorem latticeLink_of_blockFor : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc ι inc hH
  obtain ⟨σ, hσF, hσc⟩ := GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj E l hdisc
  choose hf hb using hH.2.2
  classical
  set fr : ℕ → ι → ι := fun _ τ => hf (σ (inc τ)) with hfr
  set cjj : ℕ → ι → Bool := fun _ τ => decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) with hcjj
  refine ⟨fr, cjj, ?_⟩
  intro P W hP hOk hbox mu hLk hBF τ
  obtain ⟨ep, J, bot, hep, hBP, hJ⟩ := hBF
  have hall : ∀ i, ∃ τ', i = ep (inc τ') ∨ i = ep (cj (inc τ')) := by
    intro i
    rcases hep with rfl | rfl
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inl h⟩
      · exact ⟨hf i, Or.inr h⟩
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inr (by rw [cj_cj]; exact h)⟩
      · exact ⟨hf i, Or.inl h⟩
  have hUN : ∀ τ' (a : Fin P.Nr), 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ∧
      Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ≤ (h0 P : ℤ) := by
    intro τ' a
    have h1 := ((hLk τ').2.2.1 a).2
    have ha := a.2
    have h2 := hbox τ' 0 (by omega)
    simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN] at h2 ⊢
    constructor <;> omega
  have hJb : ∀ i a, 0 ≤ J i a ∧ J i a ≤ (h0 P : ℤ) := by
    intro i a
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [((hJ τ').1 a).1]; exact hUN τ' a
    · rw [((hJ τ').1 a).2]
      have := hUN τ' (Fin.rev a)
      constructor <;> linarith [this.1, this.2]
  have hbb : ∀ i (s : Fin P.t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h0 P : ℤ) := by
    intro i s
    have hs := s.2
    have hr := hOk.what₂
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [(hJ τ').2.1]
      have e := U_block hOk τ' s hs
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - s) (by have := hr τ'; omega)
      rw [e] at b; exact b
    · rw [(hJ τ').2.2]
      have e := U_block hOk τ' (P.t - 1 - s) (by omega)
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - (P.t - 1 - s)) (by have := hr τ'; omega)
      rw [e] at b
      constructor <;> omega
  obtain ⟨O', F, L', _, _, _, _, _, _, I, _, Wl, u, c, kap, ζ, em, jj, hN⟩ :=
    GlobalTheory.T.crystalline_block_lattices_over_power_series_ring hBS E Ω l hl2 hdisc σ hσF P.Nr P.t (h0 P) J bot hJb hbb hBP
  have hn : kc P + (reFr W fr cjj).j τ + P.t + (reFr W fr cjj).q τ = P.Nr := hOk.what₂ τ
  unfold LatticeLink
  rw [hn]
  refine ⟨E →+* PadicAlgCl l, inferInstance, σ, ‹_›, O', F, L', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, I, ‹_›, Wl, u, c,
    labels inc P W mu, fun _ => 1 - (P.Nr : ℤ), ep, J, bot, kap, ζ, em, jj, inc, ?_⟩
  refine ⟨?_, ?_, ?_, hN, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨cj_cj, fun i => hσc i, ?_, ?_, ?_, ?_⟩
    · intro i
      rcases hb i with h | h
      · exact Or.inl ⟨hf i, h.symm⟩
      · exact Or.inr ⟨hf i, by show inc (hf i) = cj i; rw [← cj_cj (inc (hf i)), ← h]⟩
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj]; ring
  ·
    rintro _ ⟨τ', rfl⟩
    have hr := hOk.what₂ τ'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := hOk.anti τ' a b hab'.le b.2
      simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := (hLk τ').1 hab.le
      simp only [Formalism.CohomologicalDescent.LD.res] at h1
      simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro s
      have hs := s.2
      refine ⟨⟨kc P + W.j τ' + P.t - 1 - s, by omega⟩, ?_⟩
      simp only [labels, glue_inc hH]
      exact U_block hOk τ' s hs
    · have hp := congrArg (Polynomial.map (ZMod.castHom (dvd_refl l) F)) (hLk τ').2.2.2
      simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C] at hp
      simp only [map_intCast] at hp
      have e1 : ∀ a : Fin P.Nr, (((W.U P τ' (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((W.lam τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      have e2 : ∀ a : Fin P.Nr, (((Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((mu τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      simp only [labels, glue_inc hH, e1, e2]
      exact hp
  ·
    refine ⟨hep, fun i => ?_, fun i => ?_⟩
    · funext a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact ((hJ τ').1 a).1
      · simp only [labels, glue_cj hH]; exact ((hJ τ').1 a).2
    · obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact (hJ τ').2.1
      · simp only [labels, glue_cj hH]; exact (hJ τ').2.2
  · intro τ' a
    simp only [labels, glue_inc hH]
    rfl
  · intro τ'
    simp only [labels, glue_inc hH]
    rfl
  ·
    show σ (inc τ) = if decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) = true then cj (inc (hf (σ (inc τ))))
      else inc (hf (σ (inc τ)))
    by_cases h : σ (inc τ) = inc (hf (σ (inc τ)))
    · rw [decide_eq_false (not_not.mpr h), if_neg Bool.false_ne_true]; exact h
    · rcases hb (σ (inc τ)) with h' | h'
      · exact absurd h' h
      · rw [decide_eq_true h, if_pos rfl]; exact h'
  · intro a a' haa'
    obtain rfl : a = a' := Fin.ext haa'
    simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN, Formalism.CohomologicalDescent.LD.res]
  · have hs := (hLk τ).2.1
    have h2 : (∑ a : Fin P.Nr, (mu τ a : ℤ)) = ∑ a : Fin P.Nr, (W.lam τ a : ℤ) := by exact_mod_cast hs
    simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith [h2]

end GlobalTheory.ExpLink
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLatticeLink_of_blockData : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  atlas_forward_decl GlobalTheory.ExpLink.latticeLink_of_blockFor
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.OccBlock

open Module Module.End

section Gen

variable {L V J : Type} [Field L] [DecidableEq L] [AddCommGroup V] [Module L V]

def jointGen (T : J → End L V) (y : J → L) : Submodule L V := ⨅ j, (T j).maxGenEigenspace (y j)

theorem mem_iSup_filter (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y) {θ : J → L} {f : V}
    (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (j : J) (hY : f ∈ ⨆ y ∈ Y, p y) :
    f ∈ ⨆ y ∈ Y.filter (fun y => y j = θ j), p y := by
  have hsplit : (⨆ y ∈ Y, p y) ≤ (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ⊔
      (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) := by
    refine iSup₂_le fun y hy => ?_
    by_cases h : y j = θ j
    · exact le_sup_of_le_left (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
    · exact le_sup_of_le_right (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hsplit hY)
  have hA : (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ≤ (T j).maxGenEigenspace (θ j) := by
    refine iSup₂_le fun y hy => ?_
    have hyj := (Finset.mem_filter.1 hy).2
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ = (T j).maxGenEigenspace (θ j) := by rw [hyj]
  have hB : (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) ≤ ⨆ (μ : L) (_ : μ ≠ θ j), (T j).maxGenEigenspace μ := by
    refine iSup₂_le fun y hy => ?_
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ ≤ _ := le_biSup (fun μ => (T j).maxGenEigenspace μ) (show y j ∈ {μ | μ ≠ θ j} from (Finset.mem_filter.1 hy).2)
  have hfθ : f ∈ (T j).maxGenEigenspace (θ j) := by
    rw [mem_maxGenEigenspace]
    exact ⟨1, by simp [hf j]⟩
  have hb0 : b = 0 := by
    have hb1 : b ∈ (T j).maxGenEigenspace (θ j) := by
      have hbe : b = f - a := by rw [← hab]; abel
      rw [hbe]
      exact Submodule.sub_mem _ hfθ (hA ha)
    exact (Submodule.disjoint_def.1 ((Module.End.independent_maxGenEigenspace (T j)) (θ j))) b hb1 (hB hb)
  rw [← hab, hb0, add_zero]
  exact ha

theorem mem_of_mem_iSup_finset (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y)
    {θ : J → L} {f : V} (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (hY : f ∈ ⨆ y ∈ Y, p y) : f ∈ p θ := by
  induction Y using Finset.strongInduction with
  | H Y ih =>
    by_cases h : ∃ y ∈ Y, y ≠ θ
    · obtain ⟨y0, hy0, hne⟩ := h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      exact ih _ (Finset.filter_ssubset.2 ⟨y0, hy0, hj⟩) (mem_iSup_filter T p hp hf Y j hY)
    · push_neg at h
      exact (iSup₂_le fun y hy => by rw [h y hy] : (⨆ y ∈ Y, p y) ≤ p θ) hY

end Gen

section Read

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)

def heckeQ (i : F.I) : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) where
  toFun h g := F.emb (F.cst i) • ∑ s ∈ F.tr i, h (g * s)
  map_add' h h' := by
    funext g
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' c h := by
    funext g
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul, smul_smul, mul_comm]

variable {F lam} {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  {B : BlockDat K G0 Pl0} {w : HeightOneSpectrum (𝓞 K)}

theorem rd_pow (R : Reads F lam B w) (i : F.I) (a : K) (k : ℕ) (v : B.S.Forms) :
    R.rd (((B.op (R.ix i) - a • (1 : End K B.S.Forms)) ^ k) v) =
      ((heckeQ F lam i - R.e0 a • (1 : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam))) ^ k) (R.rd v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    funext g
    simp [map_sub, map_smulₛₗ, R.hecke, heckeQ]

end Read

theorem hasBlock_of_occurs : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type)
    (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) →
    Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  intro K _ _ _ G0 _ _ Pl0 B w l _ ι _ N F lam R Z hop hZ θ hocc
  obtain ⟨f, hfspan, hfe⟩ := hocc
  refine ⟨?_, ⟨f, hfe⟩⟩
  classical
  let S : Set (F.I → PadicAlgCl l) :=
    {y | ∃ x : B.Pl × ℕ → K, (∀ P, x (P, 0) = 1) ∧ Formalism.L2.Col.HasBlocks B.n B.q B.t B.bl x ∧ ∀ i, y i = R.e0 (x (R.ix i))}
  let p : (F.I → PadicAlgCl l) → Submodule (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) :=
    fun y => ⨆ (_ : y ∈ S), jointGen (heckeQ F lam) y
  have hp : ∀ y, p y ≤ jointGen (heckeQ F lam) y := fun y => iSup_le fun _ => le_rfl
  have key : B.ZH ≤ (⨆ y, p y).comap R.rd := by
    rw [BlockDat.ZH, Formalism.L2.Col.blockSum, Formalism.L2.Col.eigSum]
    refine iSup₂_le fun x hx => ?_
    intro v hv
    rw [Submodule.mem_comap]
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
      exact Submodule.zero_mem _
    have hx1 : ∀ P, x (P, 0) = 1 := fun P =>
      GlobalTheory.ExpFrame.eq_one_of_occurs (op := B.op) ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩) (hop P)
    refine Submodule.mem_iSup_of_mem (fun i => R.e0 (x (R.ix i))) ?_
    refine Submodule.mem_iSup_of_mem (show (fun i => R.e0 (x (R.ix i))) ∈ S from ⟨x, hx1, hx, fun i => rfl⟩) ?_
    rw [jointGen, Submodule.mem_iInf]
    intro i
    have hv' := Formalism.L2.Col.eigAt_le B.op x (R.ix i) hv
    rw [mem_maxGenEigenspace] at hv' ⊢
    obtain ⟨k, hk⟩ := hv'
    exact ⟨k, by rw [← rd_pow, hk, map_zero]⟩
  have hspan : Submodule.span (PadicAlgCl l) (R.rd '' Z) ≤ ⨆ y, p y := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact key (hZ hz)
  obtain ⟨Y, hY⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hspan hfspan)
  have hf : ∀ i, heckeQ F lam i f = θ i • f := fun i => by
    funext g
    exact hfe.2.2 i g
  have hθ := mem_of_mem_iSup_finset (heckeQ F lam) p hp hf Y hY
  by_cases hθS : θ ∈ S
  · exact hθS
  · exfalso
    have h0 : p θ = ⊥ := by simp [p, hθS]
    rw [h0, Submodule.mem_bot] at hθ
    exact hfe.1 hθ

end GlobalTheory.OccBlock

end
end

section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasBlocks_of_system_occurs_in_block_part : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type) (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) → Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  first | exact @GlobalTheory.OccBlock.hasBlock_of_occurs | exact GlobalTheory.OccBlock.hasBlock_of_occurs | (intros; apply GlobalTheory.OccBlock.hasBlock_of_occurs <;> assumption)
end

section
section
open GlobalTheory.ExpFrame

namespace GlobalTheory.ExpFrame

theorem Frame.prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  intro l _ ι N F hF hu
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  obtain ⟨L, -, hL⟩ := hF.ring.2
  have hmem : F.emb u ∈ Set.range F.emb := ⟨u, rfl⟩
  rw [hL] at hmem
  have h1 : F.emb u * (l : PadicAlgCl l) = 1 := by
    have := congrArg F.emb hu
    rwa [map_mul, map_natCast, map_one] at this
  have hl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have e : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.norm_p]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one, hl] at h2
  have hlgt : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  have h3 : ‖F.emb u‖ * (l : ℝ)⁻¹ < 1 := by
    calc ‖F.emb u‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ := by gcongr; exact hmem.2
      _ = (l : ℝ)⁻¹ := one_mul _
      _ < 1 := inv_lt_one_of_one_lt₀ hlgt
  linarith

end GlobalTheory.ExpFrame
end

open GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameCoeffRing_prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  atlas_forward_decl GlobalTheory.ExpFrame.Frame.prime_not_isUnit
end

section
section
open GlobalTheory.ExpFrame Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.FrameQuot

theorem finite_quot_prime (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N) (hF : F.Ok) :
    Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  obtain ⟨hinj, L, hL, hrange⟩ := hF.ring
  haveI := hL
  have hmem : ∀ x : F.O, F.emb x ∈ L ∧ ‖F.emb x‖ ≤ 1 := fun x => by
    have hx : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at hx
    exact hx
  let f : F.O →+* integralClosure ℤ_[l] L :=
    { toFun := fun x => ⟨⟨F.emb x, (hmem x).1⟩,
        (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨F.emb x, (hmem x).1⟩).2 (hmem x).2⟩
      map_one' := Subtype.ext (Subtype.ext (map_one F.emb))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul F.emb x y))
      map_zero' := Subtype.ext (Subtype.ext (map_zero F.emb))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add F.emb x y)) }
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨y, hyL⟩, hy⟩
    have hn := (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨y, hyL⟩).1 hy
    have hy' : y ∈ Set.range F.emb := by
      rw [hrange]
      exact ⟨hyL, hn⟩
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨x, rfl⟩
  have hbij : Function.Bijective f :=
    ⟨fun x y h => hinj (congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : PadicAlgCl l)) h), hsurj⟩
  let e := RingEquiv.ofBijective f hbij
  have hfin : Finite (integralClosure ℤ_[l] L ⧸
      Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1}) :=
    GlobalTheory.LocalIntegers.finite_quotient_pow l (integralClosure ℤ_[l] L) 1
  have hIJ : Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1} =
      (Ideal.span {((l : ℕ) : F.O)}).map (e : F.O →+* integralClosure ℤ_[l] L) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, pow_one]
  exact Finite.of_equiv _ (Ideal.quotientEquiv _ _ e hIJ).symm.toEquiv

end GlobalTheory.FrameQuot
end

open GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_frameCoeffRing_quotient_prime : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  atlas_forward_decl GlobalTheory.FrameQuot.finite_quot_prime
end

section
set_option autoImplicit false

noncomputable section

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.ExpFrame

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

theorem exists_unif_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (l : ℕ)
    (hl : l ≠ 0) (hu : ¬ IsUnit ((l : ℕ) : O)) :
    ∃ (ϖ : O) (n : ℕ), Irreducible ϖ ∧ ϖ ∣ (l : O) ∧ (l : O) ∣ ϖ ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : ((l : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  refine ⟨ϖ, n, hϖ, ?_, hn.dvd⟩
  rcases n with _ | n
  · exact absurd (hn.isUnit_iff.2 (by simp)) hu
  · exact (dvd_pow_self ϖ n.succ_ne_zero).trans hn.symm.dvd

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

section Sub

variable {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} (X : HidaSetting ι N lam) (ϖ : X.O)

abbrev Red : Type := NablaT X.O N lam ⧸ scaleSub X.A (NablaT X.O N lam) ϖ

abbrev SimpIx : Type :=
  Σ E : Submodule X.A (Red X ϖ), {N' : Submodule X.A E // IsSimpleModule X.A (E ⧸ N')}

abbrev SimpMod (μ : SimpIx X ϖ) : Type := μ.1 ⧸ μ.2.1

variable {X ϖ}

theorem exists_simpMod (Gm : Type) [AddCommGroup Gm] [Module X.A Gm] [IsSimpleModule X.A Gm]
    (h : IsSubquot X.A (Red X ϖ) Gm) :
    ∃ μ : SimpIx X ϖ, Nonempty (Gm ≃ₗ[X.A] SimpMod X ϖ μ) := by
  obtain ⟨E, ψ, hψ⟩ := h
  let e := ψ.quotKerEquivOfSurjective hψ
  haveI : IsSimpleModule X.A (E ⧸ LinearMap.ker ψ) := IsSimpleModule.congr e
  exact ⟨⟨E, LinearMap.ker ψ, inferInstance⟩, ⟨e.symm⟩⟩

end Sub

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

section SubF

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))]
  [IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (m : Ideal F.T) [m.IsPrime] (ϖ : F.O)

end SubF

end GlobalTheory.ExpModel

end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization GlobalTheory.ExpModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atPts_and2 {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : AtPts Q) (h' : AtPts Q') : AtPts fun Fm x hx i p => Q Fm x hx i p ∧ Q' Fm x hx i p :=
  Closed.imp (Closed.and h h') fun _ _ _ H => by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := H
    exact ⟨max a b, fun x hx hle i p hp hm => ⟨ha x hx ((le_max_left _ _).trans hle) i p hp hm,
      hb x hx ((le_max_right _ _).trans hle) i p hp hm⟩⟩

theorem atPts_imp2 {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : AtPts Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), More p →
      Q Fm x hx i p → Q' Fm x hx i p) : AtPts Q' :=
  Closed.imp h fun Fm _ _ H => by
    obtain ⟨a, ha⟩ := H
    exact ⟨a, fun x hx hle i p hp hm => f Fm x hx i p hm (ha x hx hle i p hp hm)⟩

theorem exists_lift_subquot {A V : Type} [Ring A] [AddCommGroup V] [Module A V] (S : Submodule A V) (E : Submodule A (V ⧸ S))
    (N' : Submodule A E) : ∃ (U : Submodule A V) (π : U →ₗ[A] (E ⧸ N')), Function.Surjective π ∧ ∀ x : U, (x : V) ∈ S → π x = 0 := by
  let g : E.comap S.mkQ →ₗ[A] E := (S.mkQ.domRestrict (E.comap S.mkQ)).codRestrict E (fun x => x.2)
  refine ⟨E.comap S.mkQ, N'.mkQ ∘ₗ g, fun z => ?_, fun x hx => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective S a
    have hvU : v ∈ E.comap S.mkQ := by rw [Submodule.mem_comap, hv]; exact a.2
    have hg : g ⟨v, hvU⟩ = a := Subtype.ext hv
    exact ⟨⟨v, hvU⟩, congrArg N'.mkQ hg⟩
  · have hg : g x = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero S).2 hx)
    exact (congrArg N'.mkQ hg).trans (map_zero _)

set_option maxHeartbeats 800000 in

theorem winputs_of_simple {ι : Type} [DecidableEq ι] (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (W : Wts ι) (X : HidaSetting ι P.Nr W.lam) (l : ℕ) (ϖ : X.O)
    (n₀ : ℕ) (e : ι → (Fin P.Nr → ℕ) → X.A) (hfin : Finite (X.O ⧸ Ideal.span {(l : X.O)})) (hd : (l : X.O) ∣ ϖ ^ n₀)
    (hA : X.FrameA e) (hS : HeckeStable X.O X.Γ X.jK X.T (NablaT X.O P.Nr W.lam))
    (hQ : ∀ (Gm : Type) [AddCommGroup Gm] [Module X.O Gm] [Module X.A Gm] [IsScalarTower X.O X.A Gm], IsSimpleModule X.A Gm →
      (∃ (U : Submodule X.A (NablaT X.O P.Nr W.lam)) (π : U →ₗ[X.A] Gm), Function.Surjective π ∧
        ∀ (x : U) (y : NablaT X.O P.Nr W.lam), (x : NablaT X.O P.Nr W.lam) = ϖ • y → π x = 0) →
      ∃ (_ : Module X.T (Forms X.O X.Γ X.jK Gm)) (hw : ι → Fin P.Nr → ℕ),
        HeckeNat X.O X.Γ X.jK X.T (NablaT X.O P.Nr W.lam) Gm ∧ (∀ τ, ∃ z : Gm, e τ (hw τ) • z ≠ 0) ∧
        (¬ Subsingleton (LocalizedModule X.S (Forms X.O X.Γ X.jK Gm)) → ∀ τ, LatticeLink P W l τ (hw τ))) :
    WInputsLink P W X l := by
  have hsq : ∀ μ : SimpIx X ϖ, ∃ (U : Submodule X.A (NablaT X.O P.Nr W.lam)) (π : U →ₗ[X.A] SimpMod X ϖ μ), Function.Surjective π ∧
      ∀ (x : U) (y : NablaT X.O P.Nr W.lam), (x : NablaT X.O P.Nr W.lam) = ϖ • y → π x = 0 := by
    intro μ
    obtain ⟨U, π, h1, h2⟩ := exists_lift_subquot _ μ.1 μ.2.1
    exact ⟨U, π, h1, fun x y hxy => h2 x ⟨y, hxy⟩⟩
  have h := fun μ : SimpIx X ϖ => hQ (SimpMod X ϖ μ) μ.2.2 (hsq μ)
  choose mT hw h1 h2 h3 using h
  exact ⟨ϖ, n₀, e, SimpIx X ϖ, SimpMod X ϖ, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, mT, hw, hfin, hd, hA, ⟨hS, h1⟩, ⟨fun Gm _ _ _ hq => exists_simpMod Gm hq, h2⟩,
    fun μ _ hn τ _ => h3 μ hn τ⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem winputs_frame : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), W.Ok P → (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK (NablaT F.O P.Nr W.lam))] [IsScalarTower F.O F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK (NablaT F.O P.Nr W.lam))], F.IsHecke W.lam jK (NablaT F.O P.Nr W.lam) → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) → ¬ IsUnit ((l : ℕ) : F.O) → ∀ (m : Ideal F.T) [hm : m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → haveI := hm.isPrime; WInputsLink P (reFr W fr cjj) (F.setting W.lam jK m) l := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hW hlink F hF Bk hG jK hJ _ _ hH hfin hnu m hm θ0 h0e h0b h0o
  obtain ⟨ϖ, n₀, hϖ, hϖl, hlϖ⟩ := exists_unif_dvd F.O l (Fact.out : l.Prime).ne_zero hnu
  have hanti : ∀ τ, Antitone (res P.Nr (W.lam τ)) := fun τ a b h => hW.anti τ a b h b.2
  choose e0 he0 hu0 using GlobalTheory.ExpFrame.exists_unique_isProj F.O P.Nr ι W.lam
  let e : ι → (Fin P.Nr → ℕ) → alg F.O P.Nr W.lam := fun τ w => ⟨e0 τ w, Algebra.subset_adjoin (Or.inr ⟨τ, w, he0 τ w⟩)⟩
  have hQ : ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm]
      [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm], IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm →
      ∃ (_ : Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) (hw : ι → Fin P.Nr → ℕ),
        HeckeNat F.O (A := alg F.O P.Nr W.lam) F.Γ jK F.T (NablaT F.O P.Nr W.lam) Gm ∧ (∀ τ, ∃ z : Gm, e τ (hw τ) • z ≠ 0) ∧
        (¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) →
          ∀ τ, LatticeLink P (reFr W fr cjj) l τ (hw τ)) := by
    intro Gm _ _ _ _ hs hq
    obtain ⟨mT, _, hHG⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module l ι P.Nr F W.lam jK hF hJ Gm
    obtain ⟨mu, hmu, hemb⟩ := GlobalTheory.T.simpleSubquotient_dualWeyl_embeds_highestWeight F.O P.Nr ι W.lam ϖ hϖ hanti Gm hs hq
    refine ⟨mT, fun τ => res P.Nr (mu τ), (GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action l ι P.Nr F W.lam jK Gm hH hHG).2, fun τ => ?_, fun hn =>
      GlobalTheory.T.latticeLink_of_surviving_simple_subquotient E Ω hCheb l ι inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hanti Gm hHG hs hq mu
        (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2.1⟩) hemb m θ0 h0e h0b h0o hn⟩
    obtain ⟨e', z, hp, hz⟩ := (hmu τ).2.2.2
    have hee : e τ (res P.Nr (mu τ)) = e' := Subtype.ext (hu0 τ _ _ hp).symm
    exact ⟨z, hee ▸ hz⟩
  haveI := hm.isPrime
  exact winputs_of_simple P (reFr W fr cjj) (F.setting W.lam jK m) l ϖ n₀ e hfin hlϖ
    ⟨GlobalTheory.ExpFrame.alg_chainB_stable F.O P.Nr ι W.lam, fun τ w => he0 τ w⟩
    (GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action l ι P.Nr F W.lam jK (NablaT F.O P.Nr W.lam) hH hH).1
    (fun Gm i1 i2 i3 i4 => @hQ Gm i1 i2 i3 i4)

open Classical in
set_option maxHeartbeats 1600000 in

theorem modelSt_of_frames : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.ChebotarevDegreeOne → SmallSt → FrameSt →
    GlobalTheory.ExpTie.GalSt → ModelSt := by
  intro hBS hCheb hS hFr hGal
  refine atPts_imp2 (atPts_and2 hS (atPts_and2 hFr hGal)) ?_
  intro eps Fm x hx i p _ H j P W hD hN w hw hR
  obtain ⟨hs, hf, hg⟩ := H
  have hsm : SmallAt p j P w := hs j P W hD hN w hw hR
  haveI hl : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hsm.1⟩
  obtain ⟨F, R, inc, hFok, ⟨T⟩⟩ := @hf j P W hD hN w hw hR hl
  have hG := @hg j P W hD hN w hw hR hl F R inc hFok T
  have hNr := hN.1.Nr_eq
  have ht := hN.1.t_ge
  have hl2 : Formalism.EigenvalueLevelCeiling.plc w ≠ 2 := by have := hsm.2.1; omega
  obtain ⟨fr, cjj, hlk⟩ := GlobalTheory.T.crystallineLatticeLink_of_blockData hBS _ (AlgebraicClosure (Fm.D x i).host.E) (Formalism.EigenvalueLevelCeiling.plc w) hl2 hsm.2.2.1 _ inc T.half
  obtain ⟨jK, hJ⟩ := GlobalTheory.ExpFrame.levelMap_exists (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam
  obtain ⟨_, _, hH⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam jK hFok hJ (NablaT F.O P.Nr W.lam)
  refine ⟨fr, cjj, {m : MaximalSpectrum F.T // ∃ θ, R.Occurs (subZ p j (p.R.mu w)) θ ∧ F.Over θ m.asIdeal},
    fun m => haveI := m.1.isMaximal.isPrime; F.setting W.lam jK m.1.asIdeal, ?_, ?_⟩
  · exact GlobalTheory.T.maximalIdeals_meeting_subspace_cover _ _ _ (blk p j (p.R.mu w)) w _ P.Nr F W.lam jK hFok hJ hH R (lvlL p) _ hsm.2.2.2.1
  · rintro ⟨m, θ0, hocc, hov⟩
    have hop : ∀ Q, (blk p j (p.R.mu w)).op (Q, 0) = 1 := fun Q => (p.charW.base.fam.degL j (p.R.mu w) Q).1
    obtain ⟨hb, he⟩ := GlobalTheory.T.hasBlocks_of_system_occurs_in_block_part _ _ _ (blk p j (p.R.mu w)) w (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam R _ hop hsm.2.2.2.2 θ0 hocc
    exact ⟨GlobalTheory.T.frameCoeffRing_prime_not_isUnit _ _ _ F hFok, winputs_frame _ (AlgebraicClosure (Fm.D x i).host.E) hCheb (Formalism.EigenvalueLevelCeiling.plc w) _ inc fr cjj P W hN.2.2.1
      (hlk P W hN.1 hN.2.2.1 hD.box) F hFok R.HasBlock hG jK hJ hH (GlobalTheory.T.finite_frameCoeffRing_quotient_prime _ _ _ F hFok) (GlobalTheory.T.frameCoeffRing_prime_not_isUnit _ _ _ F hFok) m.asIdeal θ0 he hb hov⟩

end GlobalTheory.ExpModel

end
end
