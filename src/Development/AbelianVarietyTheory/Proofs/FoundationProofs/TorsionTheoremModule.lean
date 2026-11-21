import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisUniformizerRingStable
import BuildAid.ForwardExisting

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

namespace GlobalTheory

theorem isOpen_integers_finExt (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    IsOpen ((OL LL : Subalgebra ℤ_[l] ↥LL.1) : Set ↥LL.1) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  let b := Module.finBasis ℚ_[l] ↥LL.1
  have h : ∀ i, ∃ c : ℤ_[l], c ≠ 0 ∧ IsIntegral ℤ_[l] (c • b i) := by
    intro i
    have h1 : IsAlgebraic ℤ_[l] (b i) :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic _)
    exact h1.exists_integral_multiple
  choose c hc0 hc using h
  have hcont : ∀ i, Continuous (fun x : ↥LL.1 => b.coord i x) := fun i =>
    (b.coord i).continuous_of_finiteDimensional
  have hopen : IsOpen {x : ↥LL.1 | ∀ i, ‖b.coord i x‖ < ‖(c i : ℚ_[l])‖} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (hcont i).norm continuous_const
  have hcq : ∀ i, (c i : ℚ_[l]) ≠ 0 := fun i h => hc0 i (Subtype.ext h)
  refine AddSubgroup.isOpen_of_mem_nhds (OL LL).toSubring.toAddSubgroup (g := 0) ?_
  refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
  · intro i
    simpa using hcq i
  · intro x hx
    change x ∈ OL LL
    rw [← b.sum_repr x]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    have hle : ‖b.repr x i / (c i : ℚ_[l])‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.2 (hcq i))]
      exact (hx i).le
    let d : ℤ_[l] := ⟨_, hle⟩
    have : b.repr x i • b i = d • (c i • b i) := by
      rw [← algebraMap_smul ℚ_[l] (c i), ← algebraMap_smul ℚ_[l] d, smul_smul]
      congr 1
      change _ = b.repr x i / (c i : ℚ_[l]) * (c i : ℚ_[l])
      rw [div_mul_cancel₀ _ (hcq i)]
    rw [this]
    exact Subalgebra.smul_mem _ (hc i) _

end GlobalTheory
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_integers_finite_extension_open : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), IsOpen ((OL LL : Subalgebra ℤ_[l] ↥LL.1) : Set ↥LL.1) := by
  atlas_forward_decl GlobalTheory.isOpen_integers_finExt
end

section
noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Bases

variable {Z O R M J ι : Type} [CommRing Z] [CommRing O] [CommRing R] [Algebra Z O] [Algebra Z R]
  [AddCommGroup M] [Module O M] [Fintype J] [Fintype ι] (o : Module.Basis J Z O) {r : ℕ}
  (e : Fin r ≃ ι × J)

def cmb (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (a : Fin r → R) : (O ⊗[Z] R) ⊗[O] M :=
  ∑ i, ((1 : O) ⊗ₜ[Z] a i : O ⊗[Z] R) • n i

theorem cmb_eq (m : ι → (O ⊗[Z] R) ⊗[O] M) (a : Fin r → R) :
    cmb (fun k => o (e k).2 • m (e k).1) a =
      ∑ i, (∑ j, o j ⊗ₜ[Z] a (e.symm (i, j)) : O ⊗[Z] R) • m i := by
  rw [cmb, ← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.apply_symm_apply, ← algebraMap_smul (O ⊗[Z] R) (o j), smul_smul]
  simp

theorem cmb_desc (m : ι → (O ⊗[Z] R) ⊗[O] M) (c : ι → O ⊗[Z] R) :
    ∑ i, c i • m i =
      cmb (fun k => o (e k).2 • m (e k).1) fun k => cf (o.coord (e k).2) (c (e k).1) := by
  rw [cmb_eq]
  simp only [Equiv.apply_symm_apply, ← cf_sum]

theorem cmb_bij (m : ι → (O ⊗[Z] R) ⊗[O] M) (h1 : LinearIndependent (O ⊗[Z] R) m)
    (h2 : Submodule.span (O ⊗[Z] R) (Set.range m) = ⊤) :
    Function.Bijective (cmb (fun k => o (e k).2 • m (e k).1)) := by
  refine ⟨fun a a' h => ?_, fun y => ?_⟩
  · rw [cmb_eq, cmb_eq] at h
    funext k
    have h3 := congrArg (cf (o.coord (e k).2)) (Fintype.linearIndependent_iffₛ.mp h1 _ _ h (e k).1)
    rw [cf_basis, cf_basis] at h3
    simpa using h3
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
      (h2.ge (Submodule.mem_top (x := y)))
    exact ⟨_, (cmb_desc o e m c).symm⟩

theorem cmb_smul (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (c : R) (a : Fin r → R) :
    ((1 : O) ⊗ₜ[Z] c : O ⊗[Z] R) • cmb n a = cmb n fun k => c * a k := by
  simp [cmb, Finset.smul_sum, smul_smul]

theorem cmb_add (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (a b : Fin r → R) :
    cmb n a + cmb n b = cmb n (a + b) := by
  simp [cmb, Finset.sum_add_distrib, TensorProduct.tmul_add, add_smul]

theorem cmb_cmb (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (P : Matrix (Fin r) (Fin r) R) (a : Fin r → R) :
    cmb (fun i => cmb n (P i)) a = cmb n (Matrix.vecMul a P) := by
  simp only [cmb, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, TensorProduct.tmul_sum,
    Finset.sum_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact Finset.sum_comm

theorem cmb_single (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (i : Fin r) :
    cmb n ((1 : Matrix (Fin r) (Fin r) R) i) = n i := by
  rw [cmb, Finset.sum_eq_single i]
  · simp [← Algebra.TensorProduct.one_def]
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · simp

theorem exists_matrices (A : Subring R) (ξ : R) (hξ : IsUnit ξ) (M₀ h₀ : ℕ)
    (n n' : Fin r → (O ⊗[Z] R) ⊗[O] M) (hn : Function.Injective (cmb n))
    (h1 : ∀ k, ∃ a, (∀ j, a j ∈ A) ∧ ((1 : O) ⊗ₜ[Z] (ξ ^ M₀) : O ⊗[Z] R) • n' k = cmb n a)
    (h2 : ∀ k, ∃ a, (∀ j, a j ∈ A) ∧ ((1 : O) ⊗ₜ[Z] (ξ ^ h₀) : O ⊗[Z] R) • n k = cmb n' a) :
    ∃ Pm Pi : Matrix (Fin r) (Fin r) R, Pm * Pi = 1 ∧ Pi * Pm = 1 ∧
      (∀ i, n' i = cmb n (Pm i)) ∧ (∀ i j, ξ ^ M₀ * Pm i j ∈ A) ∧ (∀ i j, ξ ^ h₀ * Pi i j ∈ A) := by
  obtain ⟨u, rfl⟩ := hξ
  choose P hP hP' using h1
  choose Q hQ hQ' using h2
  have key : ∀ (k : ℕ) (x : (O ⊗[Z] R) ⊗[O] M) (m : Fin r → (O ⊗[Z] R) ⊗[O] M) (a : Fin r → R),
      ((1 : O) ⊗ₜ[Z] ((u : R) ^ k) : O ⊗[Z] R) • x = cmb m a →
        x = cmb m fun j => ((u⁻¹ : Rˣ) : R) ^ k * a j := by
    intro k x m a h
    rw [← cmb_smul, ← h, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, ← mul_pow]
    simp [← Algebra.TensorProduct.one_def]
  let Pm : Matrix (Fin r) (Fin r) R := fun i j => ((u⁻¹ : Rˣ) : R) ^ M₀ * P i j
  let Pi : Matrix (Fin r) (Fin r) R := fun i j => ((u⁻¹ : Rˣ) : R) ^ h₀ * Q i j
  have e1 : ∀ i, n' i = cmb n (Pm i) := fun i => key _ _ _ _ (hP' i)
  have e2 : Pi * Pm = 1 := by
    funext i
    apply hn
    rw [cmb_single, key _ _ _ _ (hQ' i), funext e1, cmb_cmb]
    rfl
  refine ⟨Pm, Pi, mul_eq_one_comm.mp e2, e2, e1, fun i j => ?_, fun i j => ?_⟩
  · simpa [Pm, ← mul_assoc, ← mul_pow] using hP i j
  · simpa [Pi, ← mul_assoc, ← mul_pow] using hQ i j

theorem sub_mem_of_gen (A : Subring R) (π : R) (σ : R → R)
    (T : (O ⊗[Z] R) ⊗[O] M →ₗ[O] (O ⊗[Z] R) ⊗[O] M)
    (hT : ∀ (a : R) y, T (((1 : O) ⊗ₜ[Z] a : O ⊗[Z] R) • y) = ((1 : O) ⊗ₜ[Z] σ a : O ⊗[Z] R) • T y)
    (hσ : ∀ a ∈ A, σ a ∈ A ∧ ∃ b ∈ A, σ a - a = π * b) (n : Fin r → (O ⊗[Z] R) ⊗[O] M)
    (hn : ∀ k, ∃ a, (∀ j, a j ∈ A) ∧ T (n k) - n k = ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R) • cmb n a)
    (a : Fin r → R) (ha : ∀ j, a j ∈ A) :
    ∃ b, (∀ j, b j ∈ A) ∧ T (cmb n a) - cmb n a = ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R) • cmb n b := by
  choose P hP hP' using hn
  choose b hb hb' using fun j => (hσ _ (ha j)).2
  refine ⟨b + Matrix.vecMul (fun j => σ (a j)) (Matrix.of P), fun j => A.add_mem (hb j)
    (show ∑ k, σ (a k) * P k j ∈ A from
      A.sum_mem fun k _ => A.mul_mem (hσ _ (ha k)).1 (hP k j)), ?_⟩
  rw [← cmb_add, ← cmb_cmb, smul_add]
  have h1 : ∀ k, T (n k) = n k + ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R) • cmb n (P k) := fun k => by
    rw [← hP']; abel
  have h2 : ∀ k, σ (a k) = a k + π * b k := fun k => by rw [← hb']; ring
  rw [cmb_smul n π b]
  conv_lhs => rw [cmb, map_sum]
  simp only [hT, h1, smul_add, Finset.sum_add_distrib]
  have h3 : ∑ k, ((1 : O) ⊗ₜ[Z] σ (a k) : O ⊗[Z] R) • n k = cmb n a + cmb n fun k => π * b k := by
    rw [cmb_add]
    simp only [h2]
    rfl
  rw [h3, cmb, cmb, cmb, Finset.smul_sum]
  simp only [smul_comm ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R), Matrix.of_apply]
  abel

end Bases

section Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {Z R RA : Type} [CommRing Z] [CommRing R] [CommRing RA] [Algebra Z O]
    [Algebra Z R] [Algebra O RA] {inclR : RA →ₐ[O] O ⊗[Z] R} {φR : O ⊗[Z] R →ₐ[O] O ⊗[Z] R}
    {gR : G → (O ⊗[Z] R →ₐ[O] O ⊗[Z] R)} {πA : RA}
    (E : EtTie W RA (O ⊗[Z] R) inclR φR gR πA) (A : Subring R)
    (hA : ∀ (lam : O →ₗ[Z] Z) a, cf lam (sc E a) ∈ A) {Y : LocLat G Qp LL O}
    {J ι : Type} [Fintype J] [Fintype ι] (o : Module.Basis J Z O)

include hA in
theorem jD_desc {r : ℕ} (e : Fin r ≃ ι × J) (m : ι → W.DD Y) (y : W.DD Y)
    (hy : y ∈ Submodule.span (LetA O n) (Set.range m)) :
    ∃ a : Fin r → R, (∀ j, a j ∈ A) ∧ E.jD Y y = cmb (fun k => o (e k).2 • E.jD Y (m (e k).1)) a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  refine ⟨fun k => cf (o.coord (e k).2) (sc E (c (e k).1)), fun k => hA _ _, ?_⟩
  rw [map_sum (E.jD Y)]
  exact (Finset.sum_congr rfl fun i _ => jD_sc E _ _).trans
    (cmb_desc o e (fun i => E.jD Y (m i)) fun i => sc E (c i))

include hA o in

theorem basis_of_module (ξ π : R) (hξ : IsUnit ξ) (hQ : ∀ k, sc E (W.Q ^ k) = (1 : O) ⊗ₜ[Z] (ξ ^ k))
    (hπ : sc E letπ = (1 : O) ⊗ₜ[Z] π) (σ : G → R → R)
    (hσ : ∀ g a, gR g ((1 : O) ⊗ₜ[Z] a) = (1 : O) ⊗ₜ[Z] σ g a)
    (hσA : ∀ g, ∀ a ∈ A, σ g a ∈ A ∧ ∃ b ∈ A, σ g a - a = π * b)
    (N : Submodule (LetA O n) (W.DD Y)) (b : Module.Basis ι (LetA O n) ↥N)
    (hli : LinearIndependent (O ⊗[Z] R) fun i => E.jD Y (b i : W.DD Y))
    (hsp : Submodule.span (O ⊗[Z] R) (Set.range fun i => E.jD Y (b i : W.DD Y)) = ⊤) (M₀ h₀ : ℕ)
    (h1 : ∀ x ∈ N, W.Q ^ M₀ • W.φD Y x ∈ N)
    (h2 : ∀ y ∈ N, W.Q ^ h₀ • y ∈ Submodule.span (LetA O n) (W.φD Y '' (N : Set (W.DD Y))))
    (h3 : ∀ g ∈ W.GKs, ∀ x ∈ N, W.γD Y (W.resΓ g) x - x ∈ (Ideal.span {(letπ : LetA O n)}) • N) :
    ∃ (r : ℕ) (m : Fin r → TW (O ⊗[Z] R) Y), Function.Bijective (cmb m) ∧
      (∀ g, W.resΓ g = 1 → ∀ i, TWact (gR g) Y g (m i) = m i) ∧
      (∃ Pm Pi : Matrix (Fin r) (Fin r) R, Pm * Pi = 1 ∧ Pi * Pm = 1 ∧
        (∀ i, TWmap φR Y (m i) = cmb m (Pm i)) ∧ (∀ i j, ξ ^ M₀ * Pm i j ∈ A) ∧
        (∀ i j, ξ ^ h₀ * Pi i j ∈ A)) ∧
      ∀ g ∈ W.GKs, ∀ a : Fin r → R, (∀ j, a j ∈ A) → ∃ a' : Fin r → R, (∀ j, a' j ∈ A) ∧
        TWact (gR g) Y g (cmb m a) - cmb m a = ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R) • cmb m a' := by
  classical
  let e : Fin (Fintype.card (ι × J)) ≃ ι × J := (Fintype.equivFin _).symm
  let x : Fin (Fintype.card (ι × J)) → W.DD Y := fun k => o (e k).2 • (b (e k).1 : W.DD Y)
  have hx : ∀ k, o (e k).2 • E.jD Y (b (e k).1 : W.DD Y) = E.jD Y (x k) := fun k => (map_smul _ _ _).symm
  have hxN : ∀ k, x k ∈ N := fun k => by
    simp only [x]
    rw [← algebraMap_smul (LetA O n)]
    exact Submodule.smul_mem _ _ (b _).2
  have hn : ∀ y ∈ N, ∃ c : ι → LetA O n, ∑ i, c i • (b i : W.DD Y) = y := fun y hy =>
    ⟨fun i => b.repr ⟨y, hy⟩ i, by
      have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
      rwa [Submodule.coe_sum] at this⟩
  have hS := fun y hy => jD_desc E A hA o e (fun i => (b i : W.DD Y)) y
    ((Submodule.mem_span_range_iff_exists_fun _).mpr (hn y hy))
  have hbij := cmb_bij o e _ hli hsp
  refine ⟨_, _, hbij, fun g hg k => ?_, exists_matrices A ξ hξ M₀ h₀ _ _ hbij.1 (fun k => ?_) (fun k => ?_),
    fun g hg a ha => sub_mem_of_gen A π (σ g) _ (fun a y => by rw [TWact_smul, hσ]) (hσA g) _
      (fun k => ?_) a ha⟩
  · rw [hx, ← E.jD_act, hg, W.γD_one]
  · obtain ⟨a, ha, ha'⟩ := hS _ (h1 _ (hxN k))
    exact ⟨a, ha, by rw [← ha', hx, jD_sc, hQ, E.jD_φ]⟩
  · obtain ⟨a, ha, ha'⟩ := jD_desc E A hA o e (fun i => W.φD Y (b i : W.DD Y)) _
      ((Submodule.span_le.mpr (by
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hn z hz
        simp only [map_sum, φD_smulA]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i, rfl⟩)) : _ ≤ _) (h2 _ (hxN k)))
    refine ⟨a, ha, ?_⟩
    rw [hx, ← hQ, ← jD_sc, ha']
    simp only [E.jD_φ, map_smul]
  · have h4 := h3 g hg _ (hxN k)
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h4
    obtain ⟨y, hy, hy'⟩ := h4
    obtain ⟨a, ha, ha'⟩ := hS y hy
    exact ⟨a, ha, by rw [← ha', hx, ← E.jD_act, ← map_sub, ← hy', jD_sc, hπ]⟩

end Module

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}

def qmap (F : LatHom L L') : (V ⧸ L.T) →ₗ[O] (V' ⧸ L'.T) :=
  L.T.mapQ L'.T (F.f.restrictScalars O) F.T_le

def qpost (F : LatHom L L') : (G → V ⧸ L.T) →ₗ[O] (G → V' ⧸ L'.T) := LinearMap.compLeft (qmap F) G

theorem qmap_act (F : LatHom L L') (g : G) (x : V ⧸ L.T) :
    qmap F (actD L g x) = actD L' g (qmap F x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (F.equiv g x)

theorem qmap_inv {F : LatHom L L'} {F' : LatHom L' L} (h : ∀ x, F'.f (F.f x) = x) (x : V ⧸ L.T) :
    qmap F' (qmap F x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (h x)

theorem qpost_inv {F : LatHom L L'} {F' : LatHom L' L} (h : ∀ x, F'.f (F.f x) = x)
    (c : G → V ⧸ L.T) : qpost F' (qpost F c) = c := funext fun g => qmap_inv h (c g)

theorem qpost_Z1D (F : LatHom L L') (c : G → V ⧸ L.T) (hc : c ∈ divisibleCocycles L) : qpost F c ∈ divisibleCocycles L' := by
  refine ⟨hc.1.comp (qmap F), fun g h => ?_⟩
  change qmap F (c (g * h)) = qmap F (c g) + actD L' g (qmap F (c h))
  rw [hc.2, map_add, qmap_act]

theorem mem_BD (c : G → V ⧸ L.T) : c ∈ BD L ↔ ∃ x, ∀ g, c g = actD L g x - x :=
  ⟨fun ⟨x, hx⟩ => ⟨x, fun g => (congrFun hx g).symm⟩, fun ⟨x, hx⟩ => ⟨x, funext fun g => (hx g).symm⟩⟩

theorem qpost_BD (F : LatHom L L') (c : G → V ⧸ L.T) (hc : c ∈ BD L) : qpost F c ∈ BD L' := by
  obtain ⟨x, hx⟩ := (mem_BD c).mp hc
  refine (mem_BD _).mpr ⟨qmap F x, fun g => ?_⟩
  change qmap F (c g) = _
  rw [hx, map_sub, qmap_act]

theorem post_compose_bloch_kato_cocycle (F : LatHom L L') (c : G → V) (hc : c ∈ finiteCocycles PD ρ) :
    (fun g => F.f (c g)) ∈ finiteCocycles PD ρ' := by
  obtain ⟨⟨h1, h2⟩, x, hx⟩ := hc
  refine ⟨⟨F.cont.comp h1, fun g h => by simp only [h2, map_add, F.equiv]⟩,
    AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) x, fun g => ?_⟩
  have h3 : ∀ y, actVB PD ρ' g (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) =
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, F.equiv]
    | add a b ha hb => simp [ha, hb]
  rw [h3, ← map_sub, ← hx]
  simp

theorem qpost_HfD (F : LatHom L L') (c : G → V ⧸ L.T) (hc : c ∈ HfD PD L) :
    qpost F c ∈ HfD PD L' := by
  obtain ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
  rw [map_add]
  exact Submodule.add_mem_sup ⟨_, post_compose_bloch_kato_cocycle PD F a ha, rfl⟩ (qpost_BD F b hb)

theorem mk_mem_H1fD (z : ↥(divisibleCocycles L)) :
    (Submodule.Quotient.mk z : DivisibleCohomology L) ∈ divisibleFiniteCohomology PD L ↔ (z : G → V ⧸ L.T) ∈ HfD PD L := by
  refine ⟨fun ⟨y, hy, h⟩ => ?_, fun h => ⟨z, h, rfl⟩⟩
  have h1 : ((y - z : ↥(divisibleCocycles L)) : G → V ⧸ L.T) ∈ BD L :=
    (Submodule.Quotient.eq ((BD L).comap (divisibleCocycles L).subtype)).mp h
  have h2 := (HfD PD L).sub_mem hy (Submodule.mem_sup_right h1)
  simpa using h2

def h1map (F : LatHom L L') : DivisibleCohomology L →ₗ[O] DivisibleCohomology L' :=
  Submodule.mapQ _ _ ((qpost F).restrict (qpost_Z1D F)) fun c hc => qpost_BD F c hc

theorem length_le {F : LatHom L L'} {F' : LatHom L' L} (h : ∀ x, F'.f (F.f x) = x) (r : O) :
    Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) r) ≤
      Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L' ⧸ divisibleFiniteCohomology PD L') r) := by
  have h1 : ∀ x : DivisibleCohomology L, x ∈ divisibleFiniteCohomology PD L ↔ h1map F x ∈ divisibleFiniteCohomology PD L' := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_mem_H1fD]
    refine Iff.trans ?_ (mk_mem_H1fD PD ((qpost F).restrict (qpost_Z1D F) z)).symm
    refine ⟨qpost_HfD PD F _, fun hz => ?_⟩
    have := qpost_HfD PD F' _ hz
    rwa [LinearMap.restrict_coe_apply, qpost_inv h] at this
  let f : (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) →ₗ[O] (DivisibleCohomology L' ⧸ divisibleFiniteCohomology PD L') :=
    Submodule.mapQ _ _ (h1map F) fun x hx => (h1 x).mp hx
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).mpr fun x hx => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((h1 x).mpr ((Submodule.Quotient.mk_eq_zero _).mp hx))
  refine Module.length_le_of_injective (f.restrict (p := Submodule.torsionBy O _ r)
    (q := Submodule.torsionBy O _ r) fun x hx => ?_) fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab))
  rw [Submodule.mem_torsionBy_iff] at hx ⊢
  rw [← map_smul, hx, map_zero]

theorem HfD_le (hT : IsOpen (L.T : Set V)) (hc : ∀ x, Continuous fun g => ρ g x) :
    HfD PD L ≤ divisibleCocycles L := by
  have key : ∀ c : G → V, Continuous c →
      IsLocallyConstant fun g => (Submodule.Quotient.mk (c g) : V ⧸ L.T) := by
    intro c hc
    refine IsLocallyConstant.iff_isOpen_fiber.mpr fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have : (fun g => (Submodule.Quotient.mk (c g) : V ⧸ L.T)) ⁻¹' {Submodule.Quotient.mk y} =
        (fun g => c g + -y) ⁻¹' (L.T : Set V) := by
      ext g
      simp [Submodule.Quotient.eq, sub_eq_add_neg]
    rw [this]
    exact hT.preimage (hc.add continuous_const)
  refine sup_le ?_ fun c hc' => ?_
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨key c hc.1.1, fun g h => ?_⟩
    change Submodule.Quotient.mk (c (g * h)) = Submodule.Quotient.mk (c g + ρ g (c h))
    rw [hc.1.2]
  · obtain ⟨x, hx⟩ := (mem_BD c).mp hc'
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : c = fun g => (Submodule.Quotient.mk (ρ g x + -x) : V ⧸ L.T) := funext fun g => by
      rw [hx, ← sub_eq_add_neg]; rfl
    rw [h1]
    refine ⟨key _ ((hc x).add continuous_const), fun g h => ?_⟩
    change _ = Submodule.Quotient.mk (ρ g x + -x + ρ g (ρ h x + -x))
    congr 1
    simp only [map_mul, Module.End.mul_apply, map_add, map_neg]
    abel

variable (L) in

def Facts (I : Subgroup G) (e d : ℕ) : Prop :=
  (∀ n : ℕ, Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) ((PD.p : O) ^ n)) ≤
    (((d + 1) * n : ℕ) : ℕ∞) * lenOl PD (O := O)) ∧
  (0 < e → HfD PD L = BD L) ∧
  (e = 0 → ∀ c : G → V ⧸ L.T, c ∈ HfD PD L ↔ (c ∈ divisibleCocycles L ∧ ∃ x, ∀ g ∈ I, c g = actD L g x - x))

theorem Facts.of_iso {F : LatHom L L'} {F' : LatHom L' L} (h : ∀ x, F'.f (F.f x) = x)
    {I : Subgroup G} {e d : ℕ} (H : Facts PD L' I e d) : Facts PD L I e d := by
  refine ⟨fun n => (length_le PD h _).trans (H.1 n), fun he => le_antisymm (fun c hc => ?_) le_sup_right,
    fun he c => ⟨fun hc => ?_, fun ⟨hc, x, hx⟩ => ?_⟩⟩
  · rw [← qpost_inv h c]
    exact qpost_BD F' _ (H.2.1 he ▸ qpost_HfD PD F c hc)
  · obtain ⟨h1, x, hx⟩ := (H.2.2 he _).mp (qpost_HfD PD F c hc)
    rw [← qpost_inv h c]
    refine ⟨qpost_Z1D F' _ h1, qmap F' x, fun g hg => ?_⟩
    change qmap F' (qpost F c g) = _
    rw [hx g hg, map_sub, qmap_act]
  · rw [← qpost_inv h c]
    refine qpost_HfD PD F' _ ((H.2.2 he _).mpr ⟨qpost_Z1D F c hc, qmap F x, fun g hg => ?_⟩)
    change qmap F (c g) = _
    rw [hx g hg, map_sub, qmap_act]

end Transport

section RankOne

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))


omit [IsTopologicalRing LL] in

theorem exists_gen [IsDomain O] [IsFractionRing O LL] (Z : LocLat G Qp LL O)
    (h1 : Module.finrank LL Z.V = 1) : ∃ t ∈ Z.L.T, ∀ z ∈ Z.L.T, ∃ a : O, z = a • t := by
  haveI := Z.L.free
  let b := Module.Free.chooseBasis O ↥Z.L.T
  have hli : LinearIndependent LL fun i => (b i : Z.V) :=
    (LinearIndependent.iff_fractionRing O LL).mp
      (b.linearIndependent.map' Z.L.T.subtype (Submodule.ker_subtype _))
  haveI := hli.finite
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex O ↥Z.L.T)
  haveI : Subsingleton (Module.Free.ChooseBasisIndex O ↥Z.L.T) :=
    Fintype.card_le_one_iff_subsingleton.mp (h1 ▸ hli.fintype_card_le_finrank)
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex O ↥Z.L.T) with h | ⟨⟨i⟩⟩
  · refine ⟨0, zero_mem _, fun z hz => ⟨0, ?_⟩⟩
    simpa using (congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)).symm
  · refine ⟨b i, (b i).2, fun z hz => ⟨b.repr ⟨z, hz⟩ i, ?_⟩⟩
    have := b.sum_repr ⟨z, hz⟩
    rw [Fintype.sum_subsingleton _ i] at this
    exact (congrArg Subtype.val this).symm

theorem exists_iso (hL : L.T = LinearMap.range (Algebra.linearMap O LL)) (Z : LocLat G Qp LL O)
    (h1 : Module.finrank LL Z.V = 1) (hψ : ∀ g x, Z.ρ g x = ((ψ g : LLˣ) : LL) • x)
    (t : Z.V) (ht : t ∈ Z.L.T) (hg : ∀ z ∈ Z.L.T, ∃ a : O, z = a • t) :
    ∃ (F : LatHom Z.L L) (F' : LatHom L Z.L), (∀ x, F'.f (F.f x) = x) ∧ (∀ x, F.f (F'.f x) = x) ∧
      F.f t = 1 := by
  have h0 : t ≠ 0 := by
    rintro rfl
    have : Submodule.span LL (Z.L.T : Set Z.V) ≤ ⊥ := Submodule.span_le.mpr fun z hz => by
      obtain ⟨a, ha⟩ := hg z hz
      simpa using ha
    rw [Z.L.span, top_le_iff] at this
    have h2 := finrank_top LL Z.V
    rw [← this, finrank_bot, h1] at h2
    exact zero_ne_one h2
  have hb : Function.Bijective (LinearMap.toSpanSingleton LL Z.V t) :=
    ⟨fun a b h => smul_left_injective LL h0 h, (finrank_eq_one_iff_of_nonzero' t h0).mp h1⟩
  let e := LinearEquiv.ofBijective _ hb
  have he : ∀ c, e c = c • t := fun _ => rfl
  haveI := IsModuleTopology.toContinuousSMul LL Z.V
  refine ⟨⟨e.symm.toLinearMap, fun g x => ?_, IsModuleTopology.continuous_of_linearMap _, fun x hx => ?_⟩,
    ⟨e.toLinearMap, fun g x => ?_, continuous_id.smul continuous_const, fun x hx => ?_⟩,
    e.apply_symm_apply, e.symm_apply_apply, ?_⟩
  · rw [hψ, map_smul]; rfl
  · obtain ⟨a, rfl⟩ := hg x hx
    rw [hL]
    refine ⟨a, (e.eq_symm_apply).mpr ?_⟩
    rw [he, Algebra.linearMap_apply, algebraMap_smul]
  · rw [hψ, ← map_smul]; rfl
  · rw [hL] at hx
    obtain ⟨a, rfl⟩ := hx
    change algebraMap O LL a • t ∈ _
    rw [algebraMap_smul]
    exact Z.L.T.smul_mem a ht
  · exact (e.symm_apply_eq).mpr (one_smul LL t).symm



end RankOne

section Situation

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_levelFieldFiniteExtension (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) :
    Module.finrank ℚ_[l] ↥(K0 (levelField K s)) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h1 : Ks (levelField K s) s = Ks K s := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le_sup_right ?_ _)
    exact le_inf le_sup_left inf_le_right
  have h2 := GlobalTheory.Cyc.finrank_Ks (levelField K s) s hs
  rw [h1, GlobalTheory.Cyc.finrank_Ks K s hs] at h2
  have h3 : 2 ≤ l := (Fact.out : l.Prime).two_le
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by omega) (pow_pos (by omega) _)) h2).symm

theorem val_le_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (s : ℕ) :
    (s : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl1 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨y, rfl⟩ : ∃ y, x = (l : ℚ_[l]) ^ s * y := ⟨((l : ℚ_[l]) ^ s)⁻¹ * x, by field_simp⟩
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l,
    norm_mul, norm_pow, Padic.norm_p, nsmul_one, inv_pow, ← zpow_natCast, ← zpow_neg,
    mul_le_iff_le_one_right (zpow_pos hl1 _)]
  have h1 : (s : WithTop ℚ) ≤ s + P.v LL (algebraMap ℚ_[l] ↥LL.1 y) ↔
      0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y) := by
    conv_lhs => lhs; rw [← add_zero (s : WithTop ℚ)]
    exact WithTop.add_le_add_iff_left (WithTop.natCast_ne_top s)
  rw [h1, P.v_O]
  change IsIntegral ℤ_[l] _ ↔ _
  rw [isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective, IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩

theorem absoluteGalois_mem_fixingSubgroup_maxUnramified {K : FinExt l} (g : ↥(GK K)) : (g : GQ l) ∈ (K0 K).fixingSubgroup :=
  fun x => g.2 ⟨x.1, x.2.1⟩

section Wach

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}

theorem mem_GKs (hs : W.s = s) (g : ↥(GK K)) : g ∈ W.GKs ↔ (g : GQ l) ∈ GK (levelField K s) := by
  rw [W.GKs_def, hs, P.PD_χ, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, val_le_iff]
  exact (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g (absoluteGalois_mem_fixingSubgroup_maxUnramified g)).1 s).symm

theorem prim_ζQ (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h : ∀ j, P.ζQ (j + 1) ^ l ^ j = P.ζQ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [h]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by rw [pow_succ, pow_mul, h, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem resΓ_eq_one (g : ↥(GK K)) (hg : ∀ j : ℕ, (g : GQ l) (P.ζQ j) = P.ζQ j) : W.resΓ g = 1 := by
  have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
    by_contra hne
    obtain ⟨m, hm⟩ := GlobalTheory.Cyc.exists_zpow_neg_lt (l := l) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have h2 := GlobalTheory.Cyc.IsCyc.norm_sub_one_le_of_prim P.χQ_cyc g _ (prim_ζQ P m) (hg _)
    have h3 : (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(m : ℤ)) :=
      zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_le) (by push_cast; omega)
    exact absurd (h2.trans h3) (not_le.mpr hm)
  apply W.χΓ_inj
  apply Units.ext
  apply Subtype.val_injective
  have h2 := W.χΓ_res g
  rw [P.PD_χ, h1, map_one] at h2
  rw [map_one]
  exact h2


variable (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))


end Wach

end Situation

end GlobalTheory.TorsionBoundCompare
end
end

section
noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Hyp

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime] (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem actVB_res (Y : Lat K LL) (g : ↥(GK K)) (g' : ↥(GK (levelField K s))) (hg : (g : GQ l) = g') :
    actVB ((LT l).PD K) Y.ρ g = actVB ((LT l).PD (levelField K s)) (resKs h Y) g' := by
  have h2 : Y.ρ g = resKs h Y g' := congrArg Y.ρ (Subtype.ext hg)
  have h3 : (((LT l).PD K).actB g).toAlgHom.toLinearMap.restrictScalars ℚ_[l] =
      (((LT l).PD (levelField K s)).actB g').toAlgHom.toLinearMap.restrictScalars ℚ_[l] :=
    LinearMap.ext fun b => (((LT l).PD_actB K g b).trans (by rw [hg])).trans
      ((LT l).PD_actB (levelField K s) g' b).symm
  unfold actVB
  rw [h2, h3]

theorem iInf_eq_of {α β γ : Type} [CompleteLattice γ] (f : α → γ) (g : β → γ)
    (h1 : ∀ a, ∃ b, f a = g b) (h2 : ∀ b, ∃ a, f a = g b) : ⨅ a, f a = ⨅ b, g b :=
  le_antisymm (le_iInf fun b => by obtain ⟨a, ha⟩ := h2 b; exact ha ▸ iInf_le f a)
    (le_iInf fun a => by obtain ⟨b, hb⟩ := h1 a; exact hb ▸ iInf_le g b)

theorem finrank_congr {R M : Type} [Field R] [AddCommGroup M] [Module R M] {X X' : Submodule R M}
    (e : X = X') : Module.finrank R ↥X = Module.finrank R ↥X' := by rw [e]

theorem fixed_eq (Y : Lat K LL) : (⨅ g : ((HW l).W K s LL h).GKs,
      LinearMap.ker (actVB ((LT l).PD K) Y.ρ (g : ↥(GK K)) - LinearMap.id)) =
      Dcris ((LT l).PD (levelField K s)) (resKs h Y) := by
  refine iInf_eq_of _ _ (fun g => ?_) fun g' => ?_
  · have hg : (g.1.1 : GQ l) ∈ GK (levelField K s) := (mem_GKs ((HW l).W_s K s LL h) g.1).mp g.2
    exact ⟨⟨g.1.1, hg⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y g.1 ⟨g.1.1, hg⟩ rfl)⟩
  · exact ⟨⟨⟨g'.1, GK_le (K := K) (K' := levelField K s) h.2.2.1 g'.2⟩,
      (mem_GKs ((HW l).W_s K s LL h) _).mpr g'.2⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y _ _ rfl)⟩

theorem crys_iff (Y : Lat K LL) :
    IsCrysOn (sit LT HW l AI K s LL h) (sit LT HW l AI K s LL h).W.GKs Y ↔
      IsCrys ((LT l).PD (levelField K s)) (resKs h Y) := by
  have h1 := finrank_congr (fixed_eq LT HW h Y)
  have h2 := congrArg (· * Module.finrank ↥LL.1 Y.V) (finrank_maxUnramified_levelFieldFiniteExtension K s h.1).symm
  exact iff_of_eq (congrArg₂ Eq h1 h2)

end Hyp

section Final

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

def lineLat {K LL : FinExt l} {ψ : ↥(GK K) →* (↥LL.1)ˣ} (L : Lattice (O := ↥(OL LL)) (charRep ψ))
    (hψ : Continuous fun g => ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) : Lat K LL where
  V := ↥LL.1
  modO := Algebra.toModule
  towO := inferInstance
  ρ := charRep ψ
  cont := fun _ => hψ.mul continuous_const
  L := L

variable (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

def TorsionBoundUnder {P : LocPrime l} {K LL : FinExt l} {s : ℕ} (h : Good K s LL)
    (Hyp : Lat K LL → ℕ → ℕ → Prop) (e : ℕ) : Prop :=
  ∀ (Y Yt : Lat K LL) (ι : LatHom Y.L Yt.L) (π : LatHom Yt.L (unitLat K LL)),
    IsSESLat (Qp := ℚ_[l]) ι π →
    IsCrys (P.PD (levelField K s)) (resKs h Yt) →
  ∀ M₀ h₀ : ℕ, Hyp Y M₀ h₀ →
  ∀ U : Finset ℤ, (∀ u, u ∈ U ↔ IsJump P h Y u) →
  ∀ x ∈ Yt.L.T, π.f x = 1 →
  ∀ c : ↥(GK K) → ↥Y.L.T, (∀ g, ι.f (c g : Y.V) = Yt.ρ g x - x) →
    PushInHf (P.PD K) (tateLat P K LL e) l (cTor K s (M₀ + h₀) U e) Y c

variable (D : Formalism.BasicNotions.D7) (H : HWOf D.loc) (F : FonOf D.loc D.locA H)

def TorsionTheoremModule : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (e : ℕ),
    TorsionBoundUnder (P := D.loc l) h
        (HypW (sit D.loc H l (D.locA l) K s LL h) ((F l).E K s LL h).tie) e ∧
      FiniteClasses (D.loc l) K LL e ∧ LengthBound (D.loc l) K LL e

end Final

end GlobalTheory.TorsionBoundCompare
end
end
