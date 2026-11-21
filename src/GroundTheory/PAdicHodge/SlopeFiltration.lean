import Mathlib
import GroundTheory.PAdicHodge.SlopeFrobenius
import GroundTheory.PAdicHodge.SlopePhiModule
import GroundTheory.PAdicHodge.SlopeCauchyBinet

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Module Submodule

section Embedding

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_injective_linearMap_pi [Module.Finite R M] [IsTorsionFree R M] :
    ∃ (n : ℕ) (f : M →ₗ[R] (Fin n → R)), Function.Injective f := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨I, indepI, hI⟩ := exists_maximal_linearIndepOn R s
  let N := span R (Set.range (fun i : I => s i))
  let b : Basis I R N := Basis.span indepI
  have exists_a : ∀ i : Fin k, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
    intro i
    by_cases hi : i ∈ I
    · exact ⟨1, one_ne_zero, by
        rw [one_smul]; exact subset_span ⟨⟨i, hi⟩, rfl⟩⟩
    · obtain ⟨a, ha, ha'⟩ := hI i hi
      refine ⟨a, ha, ?_⟩
      have : s '' I = Set.range (fun i : I => s i) := Set.image_eq_range s I
      rw [this] at ha'
      exact ha'
  choose a ha ha' using exists_a
  let A : R := ∏ i, a i
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)
  have hAM : ∀ x : M, A • x ∈ N := by
    intro x
    have hx : x ∈ span R (Set.range s) := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have : A • s i = (∏ j ∈ ({i}ᶜ : Finset (Fin k)), a j) • a i • s i := by
        rw [← mul_smul, ← Fintype.prod_eq_prod_compl_mul i]
      rw [this]
      exact N.smul_mem _ (ha' i)
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact N.smul_mem r hy
  let φ : M →ₗ[R] N := LinearMap.codRestrict N (A • LinearMap.id) (fun x => by simpa using hAM x)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have : A • x = A • y := by simpa [φ] using congrArg Subtype.val hxy
    exact smul_right_injective M hA this
  have : Finite I := Set.toFinite I
  let b' := b.reindex (Finite.equivFin I)
  exact ⟨Nat.card I, b'.equivFun.toLinearMap.comp φ, b'.equivFun.injective.comp hφ⟩

end Embedding

section Bezout

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]

theorem free_of_fg_ideal (I : Ideal R) (hI : I.FG) : Module.Free R I := by
  obtain ⟨a, ha⟩ := (IsBezout.isPrincipal_of_FG I hI).principal
  by_cases h0 : a = 0
  · subst h0
    have : I = ⊥ := by rw [ha]; simp
    subst this
    infer_instance
  · exact Module.Free.of_equiv
      ((LinearEquiv.toSpanNonzeroSingleton R R a h0).trans (LinearEquiv.ofEq _ _ ha.symm))

theorem free_of_injective_linearMap_pi (n : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (f : M →ₗ[R] (Fin n → R)),
      Function.Injective f → Module.Free R M := by
  induction n with
  | zero =>
    intro M _ _ _ f hf
    have : Subsingleton M := hf.subsingleton
    infer_instance
  | succ n ih =>
    intro M _ _ _ f hf
    let p : M →ₗ[R] R := (LinearMap.proj (Fin.last n)).comp f
    have : Module.Free R (LinearMap.range p) :=
      free_of_fg_ideal _ ((Module.Finite.iff_fg (R := R) (N := LinearMap.range p)).mp inferInstance)
    let g := p.rangeRestrict
    obtain ⟨l, hl⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict p)
    have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
    let e := ((hex.splitSurjectiveEquiv (LinearMap.ker g).injective_subtype) ⟨l, hl⟩).1
    have : Module.Finite R (LinearMap.ker g) :=
      Module.Finite.of_surjective ((LinearMap.fst R _ _).comp e.toLinearMap)
        (Prod.fst_surjective.comp e.surjective)
    let f' : LinearMap.ker g →ₗ[R] (Fin n → R) :=
      (LinearMap.funLeft R R Fin.castSucc).comp (f.comp (LinearMap.ker g).subtype)
    have hf' : Function.Injective f' := by
      intro x y hxy
      apply Subtype.ext
      apply hf
      funext i
      induction i using Fin.lastCases with
      | last =>
        have hx : g x = 0 := x.2
        have hy : g y = 0 := y.2
        have hx' : p x = 0 := congrArg Subtype.val hx
        have hy' : p y = 0 := congrArg Subtype.val hy
        simp only [p, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval] at hx' hy'
        rw [hx', hy']
      | cast i => exact congrFun hxy i
    have : Module.Free R (LinearMap.ker g) := ih _ f' hf'
    exact Module.Free.of_equiv e.symm

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem free_of_finite_of_isTorsionFree [Module.Finite R M] [IsTorsionFree R M] :
    Module.Free R M := by
  obtain ⟨n, f, hf⟩ := exists_injective_linearMap_pi (R := R) (M := M)
  exact free_of_injective_linearMap_pi n M f hf


end Bezout

section Compl

variable {R : Type*} [CommRing R]
variable {M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

theorem isCompl_ker_range_of_comp_eq_id (g : M →ₗ[R] P) (l : P →ₗ[R] M)
    (hl : g ∘ₗ l = LinearMap.id) : IsCompl (LinearMap.ker g) (LinearMap.range l) := by
  have h1 : ∀ y, g (l y) = y := fun y => LinearMap.congr_fun hl y
  constructor
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    rw [LinearMap.mem_ker, h1] at hx
    simp [hx]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    exact ⟨x - l (g x), by simp [h1], l (g x), ⟨_, rfl⟩, by abel⟩

end Compl

section Saturated

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (N : Submodule R M) [IsTorsionFree R (M ⧸ N)]

theorem free_quotient_of_isTorsionFree : Module.Free R (M ⧸ N) :=
  free_of_finite_of_isTorsionFree

theorem exists_isCompl_of_isTorsionFree_quotient : ∃ N' : Submodule R M, IsCompl N N' := by
  have := free_quotient_of_isTorsionFree N
  obtain ⟨l, hl⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  refine ⟨LinearMap.range l, ?_⟩
  have := isCompl_ker_range_of_comp_eq_id N.mkQ l hl
  rwa [Submodule.ker_mkQ] at this

theorem finite_of_isTorsionFree_quotient : Module.Finite R N := by
  obtain ⟨N', h⟩ := exists_isCompl_of_isTorsionFree_quotient N
  exact Module.Finite.equiv (Submodule.quotientEquivOfIsCompl N' N h.symm)

theorem free_of_isTorsionFree_quotient [IsTorsionFree R M] : Module.Free R N := by
  have := finite_of_isTorsionFree_quotient N
  exact free_of_finite_of_isTorsionFree

end Saturated

section Rank

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

theorem finrank_add_finrank_quotient [Module.Finite R M] (N : Submodule R M) :
    finrank R N + finrank R (M ⧸ N) = finrank R M := by
  rw [add_comm]
  exact N.finrank_quotient_add_finrank

end Rank

section Saturation

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

def saturation (N : Submodule R M) : Submodule R M where
  carrier := {x | ∃ r : R, r ≠ 0 ∧ r • x ∈ N}
  add_mem' := by
    rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem s hx
    · rw [mul_smul]; exact N.smul_mem r hy
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨r, hr, hx⟩
    exact ⟨r, hr, by rw [smul_comm]; exact N.smul_mem c hx⟩

variable {N N₁ N₂ : Submodule R M}


variable (N) in

theorem le_saturation : N ≤ saturation N := fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩

variable (N) in

@[simp]
theorem saturation_saturation : saturation (saturation N) = saturation N := by
  refine le_antisymm ?_ (le_saturation _)
  rintro x ⟨r, hr, s, hs, hx⟩
  exact ⟨s * r, mul_ne_zero hs hr, by rw [mul_smul]; exact hx⟩

variable (N) in

instance isTorsionFree_quotient_saturation : IsTorsionFree R (M ⧸ saturation N) where
  isSMulRegular r hr := by
    intro a b hab
    obtain ⟨x, rfl⟩ := (saturation N).mkQ_surjective a
    obtain ⟨y, rfl⟩ := (saturation N).mkQ_surjective b
    simp only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hab ⊢
    obtain ⟨s, hs, h⟩ := hab
    exact ⟨s * r, mul_ne_zero hs hr.ne_zero, by rw [mul_smul, smul_sub r x y]; exact h⟩

theorem saturation_eq_self_iff : saturation N = N ↔ IsTorsionFree R (M ⧸ N) := by
  constructor
  · intro h
    rw [← h]
    infer_instance
  · intro _
    refine le_antisymm ?_ (le_saturation N)
    rintro x ⟨r, hr, hx⟩
    have h1 : r • (N.mkQ x) = r • 0 := by
      rw [smul_zero, ← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    have h2 : N.mkQ x = 0 := smul_right_injective (M ⧸ N) hr h1
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2

theorem saturation_eq_self [IsTorsionFree R (M ⧸ N)] : saturation N = N :=
  saturation_eq_self_iff.mpr inferInstance

variable (N) in

theorem rank_saturation : Module.rank R (saturation N) = Module.rank R N := by
  let N₀ : Submodule R (saturation N) := N.comap (saturation N).subtype
  have h0 : Module.rank R (saturation N ⧸ N₀) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨x, rfl⟩ := N₀.mkQ_surjective q
    obtain ⟨r, hr, hx⟩ := x.2
    refine ⟨r, hr, ?_⟩
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  have h := HasRankNullity.rank_quotient_add_rank N₀
  rw [h0, zero_add] at h
  rw [← h]
  exact (Submodule.comapSubtypeEquivOfLe (le_saturation N)).rank_eq

variable (N) in

theorem finrank_saturation : finrank R (saturation N) = finrank R N := by
  simp only [Module.finrank, rank_saturation N]

theorem eq_of_le_of_finrank_eq [Module.Finite R M] [IsTorsionFree R (M ⧸ N)] {N' : Submodule R M}
    (hle : N ≤ N') (hrank : finrank R N = finrank R N') : N = N' := by
  have hfin : ∀ P : Submodule R M, Module.rank R P < Cardinal.aleph0 :=
    fun P => lt_of_le_of_lt P.rank_le (Module.rank_lt_aleph0 (R := R) (M := M))
  let N₀ : Submodule R N' := N.comap N'.subtype
  have h := HasRankNullity.rank_quotient_add_rank N₀
  rw [(Submodule.comapSubtypeEquivOfLe hle).rank_eq] at h
  have heq : Module.rank R N = Module.rank R N' :=
    Cardinal.toNat_injOn (hfin N) (hfin N') hrank
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 (hfin N)
  rw [← heq, hm] at h
  have hq : Module.rank R (N' ⧸ N₀) < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_self_add.trans_eq h) Cardinal.natCast_lt_aleph0
  obtain ⟨j, hj⟩ := Cardinal.lt_aleph0.1 hq
  rw [hj] at h
  have hj0 : j = 0 := by
    have : ((j + m : ℕ) : Cardinal) = m := by push_cast; exact h
    have := Nat.cast_injective this
    omega
  have hzero : Module.rank R (N' ⧸ N₀) = 0 := by rw [hj, hj0, Nat.cast_zero]
  rw [rank_eq_zero_iff] at hzero
  refine le_antisymm hle ?_
  intro x hx
  obtain ⟨r, hr, hrx⟩ := hzero (N₀.mkQ ⟨x, hx⟩)
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrx
  rw [← saturation_eq_self (N := N)]
  exact ⟨r, hr, hrx⟩

end Saturation

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace PhiModule

open Matrix Module

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {φ : R →+* R}
variable {M : Type*} [AddCommGroup M] [Module R M]

def IsStable (Φ : M →ₛₗ[φ] M) (N : Submodule R M) : Prop := ∀ x ∈ N, Φ x ∈ N

def restrict (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) : N →ₛₗ[φ] N where
  toFun x := ⟨Φ (x : M), h _ x.2⟩
  map_add' x y := Subtype.ext (map_add Φ (x : M) y)
  map_smul' r x := Subtype.ext (Φ.map_smulₛₗ r (x : M))

@[simp] theorem coe_restrict_apply (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N)
    (x : N) : (restrict Φ N h x : M) = Φ (x : M) := rfl

def quot (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) :
    (M ⧸ N) →ₛₗ[φ] (M ⧸ N) :=
  N.mapQ N Φ h

@[simp] theorem quot_mk (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) (x : M) :
    quot Φ N h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Φ x) := rfl

theorem IsStable.saturation [IsDomain R] {Φ : M →ₛₗ[φ] M} {N : Submodule R M} (h : IsStable Φ N)
    (hφ : Function.Injective φ) : IsStable Φ (saturation N) := by
  rintro x ⟨r, hr, hx⟩
  refine ⟨φ r, fun h0 => hr (hφ (by rw [h0, map_zero])), ?_⟩
  rw [← Φ.map_smulₛₗ]
  exact h _ hx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem phiMatrix_map {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] (b : Basis ι R M)
    (e : M ≃ₗ[R] M₂) {Φ : M →ₛₗ[φ] M} {Φ₂ : M₂ →ₛₗ[φ] M₂} (he : ∀ x, e (Φ x) = Φ₂ (e x)) :
    phiMatrix (b.map e) Φ₂ = phiMatrix b Φ := by
  ext i j
  simp [phiMatrix_apply, ← he]

theorem isPhiModule_congr {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [Module.Free R M]
    [Module.Finite R M] (e : M ≃ₗ[R] M₂) {Φ : M →ₛₗ[φ] M} {Φ₂ : M₂ →ₛₗ[φ] M₂}
    (he : ∀ x, e (Φ x) = Φ₂ (e x)) : IsPhiModule Φ ↔ IsPhiModule Φ₂ := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [isPhiModule_iff_isUnit_det b, isPhiModule_iff_isUnit_det (b.map e), phiMatrix_map b e he]

theorem deg_congr [Nontrivial R] (v : UnitOrd R φ) {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [Module.Free R M] [Module.Finite R M] [Module.Free R M₂] [Module.Finite R M₂]
    (e : M ≃ₗ[R] M₂) {Φ : M →ₛₗ[φ] M} {Φ₂ : M₂ →ₛₗ[φ] M₂} (he : ∀ x, e (Φ x) = Φ₂ (e x)) :
    deg v Φ₂ = deg v Φ := by
  classical
  let b := Module.Free.chooseBasis R M
  by_cases h : IsPhiModule Φ
  · have h₂ := (isPhiModule_congr e he).1 h
    rw [deg_eq v b Φ h, deg_eq v (b.map e) Φ₂ h₂, degIn, degIn]
    exact v.ord_unit_eq _ _ (by rw [phiMatrix_map b e he])
  · have h₂ : ¬ IsPhiModule Φ₂ := fun h₂ => h ((isPhiModule_congr e he).2 h₂)
    rw [deg, deg, dif_neg h, dif_neg h₂]

section Adapted

variable {N N' : Submodule R M} (hc : IsCompl N N') {κ κ' : Type*} [Fintype κ] [Fintype κ']
  [DecidableEq κ] [DecidableEq κ'] (bN : Basis κ R N) (bN' : Basis κ' R N')

def adaptedBasis : Basis (κ ⊕ κ') R M := (bN.prod bN').map (Submodule.prodEquivOfIsCompl N N' hc)

theorem adaptedBasis_inl (i : κ) : adaptedBasis hc bN bN' (Sum.inl i) = bN i := by
  simp [adaptedBasis, Basis.prod_apply]

theorem adaptedBasis_inr (i : κ') : adaptedBasis hc bN bN' (Sum.inr i) = bN' i := by
  simp [adaptedBasis, Basis.prod_apply]

theorem adaptedBasis_repr_inl (x : M) (i : κ) :
    (adaptedBasis hc bN bN').repr x (Sum.inl i) = bN.repr (N.projectionOnto N' hc x) i := by
  simp [adaptedBasis, Basis.prod_repr_inl]

theorem adaptedBasis_repr_inr (x : M) (i : κ') :
    (adaptedBasis hc bN bN').repr x (Sum.inr i) = bN'.repr (N'.projectionOnto N hc.symm x) i := by
  simp [adaptedBasis, Basis.prod_repr_inr]

def quotBasis : Basis κ' R (M ⧸ N) := bN'.map (N.quotientEquivOfIsCompl N' hc).symm

theorem quotBasis_apply (i : κ') : quotBasis hc bN' i = Submodule.Quotient.mk (bN' i : M) := by
  simp [quotBasis]

theorem quotBasis_repr_mk (x : M) (i : κ') :
    (quotBasis hc bN').repr (Submodule.Quotient.mk x) i = bN'.repr (N'.projectionOnto N hc.symm x) i := by
  simp [quotBasis]

theorem det_phiMatrix_adapted (Φ : M →ₛₗ[φ] M) (h : IsStable Φ N) :
    (phiMatrix (adaptedBasis hc bN bN') Φ).det =
      (phiMatrix bN (restrict Φ N h)).det * (phiMatrix (quotBasis hc bN') (quot Φ N h)).det := by
  have e : phiMatrix (adaptedBasis hc bN bN') Φ = Matrix.fromBlocks (phiMatrix bN (restrict Φ N h))
      (Matrix.of fun i j => (adaptedBasis hc bN bN').repr (Φ (bN' j)) (Sum.inl i)) 0
      (phiMatrix (quotBasis hc bN') (quot Φ N h)) := by
    ext (i | i) (j | j)
    · rw [phiMatrix_apply, adaptedBasis_inl, adaptedBasis_repr_inl, Matrix.fromBlocks_apply₁₁,
        phiMatrix_apply, ← coe_restrict_apply Φ N h, Submodule.projectionOnto_apply_left]
    · rw [phiMatrix_apply, adaptedBasis_inr, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    · rw [phiMatrix_apply, adaptedBasis_inl, adaptedBasis_repr_inr, Matrix.fromBlocks_apply₂₁,
        ← coe_restrict_apply Φ N h, Submodule.projectionOnto_apply_right]
      simp
    · rw [phiMatrix_apply, adaptedBasis_inr, adaptedBasis_repr_inr, Matrix.fromBlocks_apply₂₂,
        phiMatrix_apply, quotBasis_apply, quot_mk, quotBasis_repr_mk]
  rw [e, Matrix.det_fromBlocks_zero₂₁]

end Adapted

section Bezout

variable [IsDomain R] [IsBezout R] [Module.Free R M] [Module.Finite R M]

theorem free_of_saturated (N : Submodule R M) [Module.IsTorsionFree R (M ⧸ N)] : Module.Free R N :=
  free_of_isTorsionFree_quotient N

theorem finite_of_saturated (N : Submodule R M) [Module.IsTorsionFree R (M ⧸ N)] :
    Module.Finite R N :=
  finite_of_isTorsionFree_quotient N

theorem free_quot_of_saturated (N : Submodule R M) [Module.IsTorsionFree R (M ⧸ N)] :
    Module.Free R (M ⧸ N) :=
  free_quotient_of_isTorsionFree N

theorem exists_det_eq_mul (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N)
    [Module.IsTorsionFree R (M ⧸ N)] [Module.Free R N] [Module.Finite R N]
    [Module.Free R (M ⧸ N)] :
    ∃ b : Basis (Module.Free.ChooseBasisIndex R N ⊕ Module.Free.ChooseBasisIndex R (M ⧸ N)) R M,
      (phiMatrix b Φ).det = (phiMatrix (Module.Free.chooseBasis R N) (restrict Φ N h)).det *
        (phiMatrix (Module.Free.chooseBasis R (M ⧸ N)) (quot Φ N h)).det := by
  classical
  obtain ⟨N', hc⟩ := exists_isCompl_of_isTorsionFree_quotient N
  let bN := Module.Free.chooseBasis R N
  let bQ := Module.Free.chooseBasis R (M ⧸ N)
  let bN' := bQ.map (N.quotientEquivOfIsCompl N' hc)
  have hq : quotBasis hc bN' = bQ := by
    ext i
    simp [quotBasis, bN']
  refine ⟨adaptedBasis hc bN bN', ?_⟩
  rw [det_phiMatrix_adapted hc bN bN' Φ h, hq]

theorem isPhiModule_restrict {Φ : M →ₛₗ[φ] M} (hΦ : IsPhiModule Φ) {N : Submodule R M}
    (h : IsStable Φ N) [Module.IsTorsionFree R (M ⧸ N)] : IsPhiModule (restrict Φ N h) := by
  classical
  have := free_of_saturated N
  have := finite_of_saturated N
  have := free_quot_of_saturated N
  obtain ⟨b, hb⟩ := exists_det_eq_mul Φ N h
  rw [isPhiModule_iff_isUnit_det b, hb] at hΦ
  rw [isPhiModule_iff_isUnit_det (Module.Free.chooseBasis R N)]
  exact isUnit_of_mul_isUnit_left hΦ

theorem isPhiModule_quot {Φ : M →ₛₗ[φ] M} (hΦ : IsPhiModule Φ) {N : Submodule R M}
    (h : IsStable Φ N) [Module.IsTorsionFree R (M ⧸ N)] : IsPhiModule (quot Φ N h) := by
  classical
  have := free_of_saturated N
  have := finite_of_saturated N
  have := free_quot_of_saturated N
  obtain ⟨b, hb⟩ := exists_det_eq_mul Φ N h
  rw [isPhiModule_iff_isUnit_det b, hb] at hΦ
  rw [isPhiModule_iff_isUnit_det (Module.Free.chooseBasis R (M ⧸ N))]
  exact isUnit_of_mul_isUnit_right hΦ

theorem deg_eq_deg_restrict_add (v : UnitOrd R φ) {Φ : M →ₛₗ[φ] M}
    (hΦ : IsPhiModule Φ) {N : Submodule R M} (h : IsStable Φ N) [Module.IsTorsionFree R (M ⧸ N)]
    [Module.Free R N] [Module.Finite R N] [Module.Free R (M ⧸ N)] :
    deg v Φ = deg v (restrict Φ N h) + deg v (quot Φ N h) := by
  classical
  obtain ⟨b, hb⟩ := exists_det_eq_mul Φ N h
  have hN := isPhiModule_restrict hΦ h
  have hQ := isPhiModule_quot hΦ h
  rw [deg_eq v b Φ hΦ, deg_eq v (Module.Free.chooseBasis R N) _ hN,
    deg_eq v (Module.Free.chooseBasis R (M ⧸ N)) _ hQ, degIn, degIn, degIn,
    ← v.ord_unit_mul]
  exact v.ord_unit_eq _ _ hb

end Bezout

section FullRank

theorem mul_phiMatrix_eq_of_le {Φ : M →ₛₗ[φ] M} {I N : Submodule R M} (hIN : I ≤ N)
    (hI : IsStable Φ I) (hN : IsStable Φ N) (bI : Basis ι R I) (bN : Basis ι R N) :
    (Matrix.of fun k j => bN.repr (Submodule.inclusion hIN (bI j)) k) *
        phiMatrix bI (restrict Φ I hI) =
      phiMatrix bN (restrict Φ N hN) *
        (Matrix.of fun k j => bN.repr (Submodule.inclusion hIN (bI j)) k).map φ := by
  ext k j
  have hlin : ∀ y : I, ∑ m, bN.repr (Submodule.inclusion hIN (bI m)) k * bI.repr y m =
      bN.repr (Submodule.inclusion hIN y) k := by
    intro y
    have := congrArg (fun z => bN.repr (Submodule.inclusion hIN z) k) (bI.sum_repr y)
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have e1 : Submodule.inclusion hIN (restrict Φ I hI (bI j)) =
      restrict Φ N hN (Submodule.inclusion hIN (bI j)) := rfl
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, phiMatrix_apply]
  rw [hlin, e1, repr_phi]
  simp [Matrix.mul_apply, mulVec, dotProduct, phiMatrix_apply]

theorem exists_det_mul_eq_of_le [IsDomain R] {Φ : M →ₛₗ[φ] M} {I N : Submodule R M}
    (hIN : I ≤ N) (hI : IsStable Φ I) (hN : IsStable Φ N) (bI : Basis ι R I) (bN : Basis ι R N) :
    ∃ f : R, f ≠ 0 ∧ f * (phiMatrix bI (restrict Φ I hI)).det =
      (phiMatrix bN (restrict Φ N hN)).det * φ f := by
  set X : Matrix ι ι R := Matrix.of fun k j => bN.repr (Submodule.inclusion hIN (bI j)) k
  refine ⟨X.det, ?_, ?_⟩
  · intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc0
    have key : Submodule.inclusion hIN (∑ j, c j • bI j) = 0 := by
      apply bN.repr.injective
      ext k
      have := congrFun hc k
      simp only [mulVec, dotProduct, X, Matrix.of_apply, Pi.zero_apply] at this
      simp [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, ← this, mul_comm]
    have h2 : ∑ j, c j • bI j = 0 := Submodule.inclusion_injective hIN (by rw [key, map_zero])
    have := bI.linearIndependent
    rw [Fintype.linearIndependent_iff] at this
    funext j
    exact this c h2 j
  · rw [← det_mul, mul_phiMatrix_eq_of_le hIN hI hN bI bN, det_mul, RingHom.map_det]
    rfl

end FullRank

section Equivariant

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

def IsEquivariant (f : M →ₗ[R] M₂) (Φ : M →ₛₗ[φ] M) (Φ₂ : M₂ →ₛₗ[φ] M₂) : Prop :=
  ∀ x, f (Φ x) = Φ₂ (f x)

variable {f : M →ₗ[R] M₂} {Φ : M →ₛₗ[φ] M} {Φ₂ : M₂ →ₛₗ[φ] M₂}

theorem IsEquivariant.isStable_ker (hf : IsEquivariant f Φ Φ₂) : IsStable Φ (LinearMap.ker f) :=
  fun x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hf, hx, map_zero]

theorem IsEquivariant.isStable_range (hf : IsEquivariant f Φ Φ₂) :
    IsStable Φ₂ (LinearMap.range f) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Φ x, hf x⟩

theorem isTorsionFree_quotient_ker [IsDomain R] [Module.IsTorsionFree R M₂] (f : M →ₗ[R] M₂) :
    Module.IsTorsionFree R (M ⧸ LinearMap.ker f) :=
  (saturation_eq_self_iff (N := LinearMap.ker f)).1 (le_antisymm (fun x ⟨r, hr, hx⟩ => by
    rw [LinearMap.mem_ker, map_smul] at hx
    rw [LinearMap.mem_ker]
    exact (smul_eq_zero.1 hx).resolve_left hr) (le_saturation _))

theorem IsEquivariant.quotKerEquivRange (hf : IsEquivariant f Φ Φ₂) (x : M ⧸ LinearMap.ker f) :
    f.quotKerEquivRange (quot Φ _ hf.isStable_ker x) =
      restrict Φ₂ _ hf.isStable_range (f.quotKerEquivRange x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  apply Subtype.ext
  simp [quot_mk, LinearMap.quotKerEquivRange_apply_mk, hf x]

end Equivariant

section Subquot

variable {Φ : M →ₛₗ[φ] M} {N N' : Submodule R M}

abbrev inSub (N N' : Submodule R M) : Submodule R N' := N.comap N'.subtype

theorem isStable_inSub (h : IsStable Φ N) (h' : IsStable Φ N') :
    IsStable (restrict Φ N' h') (inSub N N') := fun _ hx => h _ hx

def subquot (Φ : M →ₛₗ[φ] M) (N N' : Submodule R M) (h : IsStable Φ N) (h' : IsStable Φ N') :
    (N' ⧸ inSub N N') →ₛₗ[φ] (N' ⧸ inSub N N') :=
  quot (restrict Φ N' h') (inSub N N') (isStable_inSub h h')

theorem isTorsionFree_subquot [IsDomain R] [Module.IsTorsionFree R (M ⧸ N)] :
    Module.IsTorsionFree R (N' ⧸ inSub N N') := by
  refine (saturation_eq_self_iff (N := inSub N N')).1 (le_antisymm (fun _ ⟨r, hr, hx⟩ => ?_)
    (le_saturation _))
  have hsat := saturation_eq_self (N := N)
  exact hsat ▸ (⟨r, hr, hx⟩ : _ ∈ saturation N)

theorem free_subquot [IsDomain R] [IsBezout R] [Module.Free R M] [Module.Finite R M]
    [Module.IsTorsionFree R (M ⧸ N)] [Module.IsTorsionFree R (M ⧸ N')] :
    Module.Free R (N' ⧸ inSub N N') := by
  have := finite_of_saturated N'
  have := isTorsionFree_subquot (N := N) (N' := N')
  exact free_quotient_of_isTorsionFree _

theorem finite_subquot [IsDomain R] [IsBezout R] [Module.Free R M] [Module.Finite R M]
    [Module.IsTorsionFree R (M ⧸ N')] : Module.Finite R (N' ⧸ inSub N N') := by
  have := finite_of_saturated N'
  infer_instance

end Subquot

end PhiModule

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Module

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

variable (K) in

def dvUnif : K := ((IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose : K)

theorem irreducible_dvUnif :
    Irreducible (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose :=
  (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose_spec

theorem norm_eq_one_of_isUnit {z : normInteger K} (hz : IsUnit z) : ‖(z : K)‖ = 1 := by
  have := (normInteger_integers (K := K)).isUnit_iff_valuation_eq_one.1 hz
  rw [NormedField.valuation_apply, ← NNReal.coe_eq_one] at this
  exact this

theorem dvUnif_ne_zero : dvUnif K ≠ 0 := by
  intro h
  have := (irreducible_dvUnif (K := K)).ne_zero
  exact this (Subtype.ext h)

theorem norm_dvUnif_pos : 0 < ‖dvUnif K‖ := norm_pos_iff.2 dvUnif_ne_zero

theorem norm_dvUnif_lt_one : ‖dvUnif K‖ < 1 := by
  have h1 : ‖dvUnif K‖ ≤ 1 := mem_normInteger.1
    (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose.2
  refine lt_of_le_of_ne h1 fun h => (irreducible_dvUnif (K := K)).not_isUnit ?_
  rw [(normInteger_integers (K := K)).isUnit_iff_valuation_eq_one, NormedField.valuation_apply,
    ← NNReal.coe_eq_one]
  exact h

theorem exists_norm_eq_zpow {x : K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖dvUnif K‖ ^ n := by
  have key : ∀ y : K, y ≠ 0 → ‖y‖ ≤ 1 → ∃ n : ℕ, ‖y‖ = ‖dvUnif K‖ ^ n := by
    intro y hy hy1
    let z : normInteger K := ⟨y, mem_normInteger.2 hy1⟩
    have hz : z ≠ 0 := fun h => hy (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz irreducible_dvUnif
    refine ⟨n, ?_⟩
    have h2 := congrArg (fun w : normInteger K => (w : K)) hu
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at h2
    rw [show y = (z : K) from rfl, h2, norm_mul, norm_pow, norm_eq_one_of_isUnit u.isUnit, one_mul]
    rfl
  rcases le_total ‖x‖ 1 with h | h
  · obtain ⟨n, hn⟩ := key x hx h
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  · obtain ⟨n, hn⟩ := key x⁻¹ (inv_ne_zero hx) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
    refine ⟨-(n : ℤ), ?_⟩
    rw [norm_inv] at hn
    rw [zpow_neg, zpow_natCast, ← hn, inv_inv]

theorem zpow_dvUnif_injective : Function.Injective fun n : ℤ => ‖dvUnif K‖ ^ n :=
  (zpow_right_strictAnti₀ norm_dvUnif_pos norm_dvUnif_lt_one).injective

namespace Robba

def intBounded (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    Subring (Robba K) where
  carrier := {f | f ∈ bounded K ∧ norm1 f ≤ 1}
  mul_mem' {f g} hf hg := ⟨(bounded K).mul_mem hf.1 hg.1, by
    rw [gaussNorm_mul_alt hf.1 hg.1]; nlinarith [gaussNorm_nonneg_alt f, gaussNorm_nonneg_alt g, hf.2, hg.2]⟩
  one_mem' := ⟨(bounded K).one_mem, by
    refine ciSup_le fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]⟩
  add_mem' {f g} hf hg := ⟨(bounded K).add_mem hf.1 hg.1,
    (gaussNorm_add_le_max_alt hf.1 hg.1).trans (max_le hf.2 hg.2)⟩
  zero_mem' := ⟨(bounded K).zero_mem, by simp [norm1]⟩
  neg_mem' {f} hf := ⟨(bounded K).neg_mem hf.1, by simpa [norm1] using hf.2⟩


theorem unit_mem_bounded (u : (Robba K)ˣ) : (u : Robba K) ∈ bounded K :=
  mem_bounded_of_mul_eq_one u.mul_inv

theorem unit_ne_zero (u : (Robba K)ˣ) : (u : Robba K) ≠ 0 := u.ne_zero

theorem gaussNorm_unit_pos (u : (Robba K)ˣ) : 0 < norm1 (u : Robba K) :=
  lt_of_le_of_ne (gaussNorm_nonneg_alt _) fun h =>
    unit_ne_zero u ((gaussNorm_eq_zero_iff_alt (unit_mem_bounded u)).1 h.symm)

theorem exists_norm1_eq_zpow (u : (Robba K)ˣ) : ∃ n : ℤ, norm1 (u : Robba K) = ‖dvUnif K‖ ^ n := by
  obtain ⟨m, hm⟩ := exists_norm1_eq (unit_mem_bounded u)
  have hne : (u : Robba K).coeff m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hm
    exact (gaussNorm_unit_pos u).ne' hm
  obtain ⟨n, hn⟩ := exists_norm_eq_zpow hne
  exact ⟨n, hm.trans hn⟩

def ord (u : (Robba K)ˣ) : ℤ := (exists_norm1_eq_zpow u).choose

theorem gaussNorm_eq_zpow_ord (u : (Robba K)ˣ) : norm1 (u : Robba K) = ‖dvUnif K‖ ^ ord u :=
  (exists_norm1_eq_zpow u).choose_spec

theorem ord_eq_of_norm1_eq {u : (Robba K)ˣ} {n : ℤ} (h : norm1 (u : Robba K) = ‖dvUnif K‖ ^ n) :
    ord u = n :=
  zpow_dvUnif_injective ((gaussNorm_eq_zpow_ord u).symm.trans h)

theorem ord_mul (u w : (Robba K)ˣ) : ord (u * w) = ord u + ord w := by
  apply ord_eq_of_norm1_eq
  rw [Units.val_mul, gaussNorm_mul_alt (unit_mem_bounded u) (unit_mem_bounded w), gaussNorm_eq_zpow_ord,
    gaussNorm_eq_zpow_ord, zpow_add₀ norm_dvUnif_pos.ne']

theorem ord_nonneg_iff (u : (Robba K)ˣ) : 0 ≤ ord u ↔ norm1 (u : Robba K) ≤ 1 := by
  rw [gaussNorm_eq_zpow_ord, ← zpow_zero ‖dvUnif K‖]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ norm_dvUnif_pos norm_dvUnif_lt_one).symm

theorem ord_eq_zero_iff (u : (Robba K)ˣ) : ord u = 0 ↔ norm1 (u : Robba K) = 1 := by
  constructor
  · intro h; rw [gaussNorm_eq_zpow_ord, h, zpow_zero]
  · intro h; exact ord_eq_of_norm1_eq (by rw [h, zpow_zero])

def unitOrd (ψ : Robba K →+* Robba K)
    (hψ : ∀ u : (Robba K)ˣ, norm1 (ψ u) = norm1 (u : Robba K)) : PhiModule.UnitOrd (Robba K) ψ where
  ord := ord
  map_mul := ord_mul
  map_phi u := ord_eq_of_norm1_eq (by
    change norm1 (ψ (u : Robba K)) = _
    rw [hψ, gaussNorm_eq_zpow_ord])

end Robba

namespace Robba

def IsGaussScaling (ψ : Robba K →+* Robba K) (Q : ℕ) : Prop :=
  ∀ f : Robba K, ∀ᶠ ρ in 𝓝[<] (1 : ℝ), gaussNorm (ψ f).coeff ρ = gaussNorm f.coeff (ρ ^ Q)

theorem tendsto_pow_nhdsLT {Q : ℕ} (hQ : 0 < Q) :
    Tendsto (fun ρ : ℝ => ρ ^ Q) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((continuous_pow Q).tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    exact pow_lt_one₀ hρ.1.le hρ.2 hQ.ne'

theorem IsGaussScaling.pow {ψ : Robba K →+* Robba K} {Q : ℕ} (h : IsGaussScaling ψ Q)
    (hQ : 0 < Q) : ∀ d : ℕ, IsGaussScaling (ψ ^ d) (Q ^ d)
  | 0 => fun f => Eventually.of_forall fun ρ => by simp
  | d + 1 => fun f => by
    have ih := (IsGaussScaling.pow h hQ d f)
    filter_upwards [h ((ψ ^ d) f), (tendsto_pow_nhdsLT hQ).eventually ih] with ρ h1 h2
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, h1, h2, ← pow_mul, pow_succ']

theorem eventually_mem_Ioo : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo 0 1 :=
  Ioo_mem_nhdsLT (by norm_num)

theorem exists_gaussNorm_pow_le (f : Robba K) {Q : ℕ} (hQ : 0 < Q) :
    ∃ n₀ : ℤ, ∀ᶠ ρ in 𝓝[<] (1 : ℝ),
      gaussNorm f.coeff (ρ ^ Q) ≤ ρ ^ (((Q : ℤ) - 1) * n₀) * gaussNorm f.coeff ρ := by
  by_cases hf : f.coeff = 0
  · exact ⟨0, Eventually.of_forall fun ρ => by simp [hf, gaussNorm_zero]⟩
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f f
  have hQ1 : (0 : ℤ) ≤ (Q : ℤ) - 1 := by omega
  refine ⟨lowIndex f.coeff r, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT hr1, (tendsto_pow_nhdsLT hQ).eventually (Ioo_mem_nhdsLT hr1)]
    with ρ hρ hρQ
  have hρ0 : 0 < ρ := hr0.trans hρ.1
  have c' := (hc (ρ ^ Q) hρQ.1.le hρQ.2).1
  have c := (hc ρ hρ.1.le hρ.2).1
  have cr := (hc r le_rfl hr1).1
  have hn : lowIndex f.coeff r ≤ lowIndex f.coeff (ρ ^ Q) :=
    (lowIndex_le_highIndex hr0 cr hf).trans (highIndex_le_lowIndex hr0 hρQ.1 cr c' hf)
  have hmem : ‖f.coeff (lowIndex f.coeff (ρ ^ Q))‖ * (ρ ^ Q) ^ lowIndex f.coeff (ρ ^ Q) =
      gaussNorm f.coeff (ρ ^ Q) := lowIndex_mem (hr0.trans hρQ.1) c' hf
  set n := lowIndex f.coeff (ρ ^ Q)
  rw [← hmem]
  have h1 : ‖f.coeff n‖ * ρ ^ n ≤ gaussNorm f.coeff ρ := c.le_gaussNorm n
  have e : (ρ ^ Q) ^ n = ρ ^ n * ρ ^ (((Q : ℤ) - 1) * n) := by
    rw [← zpow_add₀ hρ0.ne', ← zpow_natCast, ← zpow_mul]; congr 1; ring
  have h2 : ρ ^ (((Q : ℤ) - 1) * n) ≤ ρ ^ (((Q : ℤ) - 1) * lowIndex f.coeff r) :=
    zpow_le_zpow_right_of_le_one₀ hρ0 hρ.2.le (mul_le_mul_of_nonneg_left hn hQ1)
  calc ‖f.coeff n‖ * (ρ ^ Q) ^ n = (‖f.coeff n‖ * ρ ^ n) * ρ ^ (((Q : ℤ) - 1) * n) := by
        rw [e]; ring
    _ ≤ gaussNorm f.coeff ρ * ρ ^ (((Q : ℤ) - 1) * lowIndex f.coeff r) :=
        mul_le_mul h1 h2 (by positivity) (gaussNorm_nonneg hρ0)
    _ = _ := mul_comm _ _

theorem exists_gaussNorm_pow_le_family {ι : Type*} [Finite ι] (x : ι → Robba K) {Q : ℕ}
    (hQ : 0 < Q) : ∃ n₀ : ℤ, ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ∀ i,
      gaussNorm (x i).coeff (ρ ^ Q) ≤ ρ ^ (((Q : ℤ) - 1) * n₀) * gaussNorm (x i).coeff ρ := by
  have := Fintype.ofFinite ι
  choose n hn using fun i => exists_gaussNorm_pow_le (x i) hQ
  have hQ1 : (0 : ℤ) ≤ (Q : ℤ) - 1 := by omega
  refine ⟨-∑ i, |n i|, ?_⟩
  filter_upwards [eventually_all.2 hn, eventually_mem_Ioo] with ρ h hρ i
  refine (h i).trans (mul_le_mul_of_nonneg_right ?_ (gaussNorm_nonneg hρ.1))
  refine zpow_le_zpow_right_of_le_one₀ hρ.1 hρ.2.le (mul_le_mul_of_nonneg_left ?_ hQ1)
  have h1 : |n i| ≤ ∑ j, |n j| :=
    Finset.single_le_sum (f := fun j => |n j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 := neg_abs_le (n i)
  linarith

theorem gaussNorm_sum_le {ι : Type*} (s : Finset ι) (y : ι → Robba K) {ρ C : ℝ} (hρ : 0 < ρ)
    (hC : 0 ≤ C) (hc : ∀ i ∈ s, ConvergesAt (y i).coeff ρ)
    (h : ∀ i ∈ s, gaussNorm (y i).coeff ρ ≤ C) :
    ConvergesAt (∑ i ∈ s, y i).coeff ρ ∧ gaussNorm (∑ i ∈ s, y i).coeff ρ ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussNorm_zero, hC, convergesAt_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨ic, ib⟩ := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ca := hc a (Finset.mem_insert_self a s)
    exact ⟨convergesAt_add hρ ca ic, (gaussNorm_add_le' hρ ca ic).trans
      (max_le (h a (Finset.mem_insert_self a s)) ib)⟩

theorem gaussNorm_le_one_of_smul_eq {ψ : Robba K →+* Robba K} {Q : ℕ} (hψ : IsGaussScaling ψ Q)
    (hQ : 0 < Q) {ι : Type*} [Fintype ι] {x : ι → Robba K} (hx : x ≠ 0)
    {B : Matrix ι ι (Robba K)} (hB : ∀ i j, B i j ∈ intBounded K) {l : Robba K}
    (hl : l ∈ bounded K) (h : ∀ i, l * x i = ∑ j, B i j * ψ (x j)) : norm1 l ≤ 1 := by
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.1 hx
  have hne : Nonempty ι := ⟨i₁⟩
  obtain ⟨n₀, hn₀⟩ := exists_gaussNorm_pow_le_family x hQ
  have hzpow : Tendsto (fun ρ : ℝ => ρ ^ (((Q : ℤ) - 1) * n₀)) (𝓝[<] 1) (𝓝 1) := by
    have := ((continuousAt_zpow₀ (1 : ℝ) (((Q : ℤ) - 1) * n₀) (Or.inl one_ne_zero)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hBε : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ∀ i j, gaussNorm (B i j).coeff ρ < 1 + ε :=
    eventually_all.2 fun i => eventually_all.2 fun j =>
      (tendsto_gaussNorm_norm1 (hB i j).1).eventually_lt_const (by linarith [(hB i j).2])
  have hbound : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), gaussNorm l.coeff ρ ≤ (1 + ε) * ρ ^ (((Q : ℤ) - 1) * n₀) := by
    filter_upwards [hn₀, hBε, eventually_mem_Ioo, eventually_all.2 fun i => (x i).eventually_convergesAt,
      eventually_all.2 fun i => eventually_all.2 fun j => (B i j).eventually_convergesAt,
      l.eventually_convergesAt, eventually_all.2 fun j => (ψ (x j)).eventually_convergesAt,
      eventually_all.2 fun j => hψ (x j)] with ρ h1 h2 hρ cx cB cl cψ hψρ
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => gaussNorm (x i).coeff ρ
    set X := gaussNorm (x i₀).coeff ρ
    have hx1 : (x i₁).coeff ≠ 0 := fun h0 => hi₁ (Robba.ext h0)
    have hX : 0 < X := lt_of_lt_of_le (gaussNorm_pos hρ.1 (cx i₁) hx1) (hi₀ i₁)
    have hz : 0 ≤ ρ ^ (((Q : ℤ) - 1) * n₀) := by have := hρ.1; positivity
    have key := gaussNorm_sum_le Finset.univ (fun j => B i₀ j * ψ (x j)) hρ.1
      (C := (1 + ε) * ρ ^ (((Q : ℤ) - 1) * n₀) * X) (by positivity)
      (fun j _ => convergesAt_mul hρ.1 (cB i₀ j) (cψ j)) (fun j _ => by
        rw [gaussNorm_mul hρ.1 (cB i₀ j) (cψ j), hψρ j]
        calc gaussNorm (B i₀ j).coeff ρ * gaussNorm (x j).coeff (ρ ^ Q)
            ≤ (1 + ε) * (ρ ^ (((Q : ℤ) - 1) * n₀) * gaussNorm (x j).coeff ρ) :=
              mul_le_mul (h2 i₀ j).le (h1 j) (gaussNorm_nonneg (by have := hρ.1; positivity))
                (by linarith)
          _ ≤ (1 + ε) * (ρ ^ (((Q : ℤ) - 1) * n₀) * X) := by gcongr; exact hi₀ j
          _ = _ := by ring)
    rw [← h i₀, gaussNorm_mul hρ.1 cl (cx i₀)] at key
    have := key.2
    rw [mul_le_mul_iff_left₀ hX] at this
    exact this
  have hlim := hzpow.const_mul (1 + ε)
  rw [mul_one] at hlim
  exact le_of_tendsto_of_tendsto (tendsto_gaussNorm_norm1 hl) hlim hbound

end Robba

theorem FrobeniusLift.isGaussScaling (F : FrobeniusLift K) : Robba.IsGaussScaling F.phi F.q :=
  fun f => FrobeniusLift.eventually_gaussNorm_phi f

namespace PhiModule

open Matrix

variable {ψ : Robba K →+* Robba K} {Q : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

theorem det_mem_of_forall_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (S : Subring R) (A : Matrix ι ι R) (h : ∀ i j, A i j ∈ S) : A.det ∈ S := by
  let A' : Matrix ι ι S := Matrix.of fun i j => ⟨A i j, h i j⟩
  have e : A = A'.map S.subtype := by ext i j; rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (A'.det).2

theorem le_deg_of_le (hψ : Robba.IsGaussScaling ψ Q) (hQ : 0 < Q)
    (hψn : ∀ u : (Robba K)ˣ, Robba.norm1 (ψ u) = Robba.norm1 (u : Robba K))
    {Φ : M →ₛₗ[ψ] M} {I N : Submodule (Robba K) M} (hIN : I ≤ N) (hI : IsStable Φ I)
    (hN : IsStable Φ N) [Module.Free (Robba K) I] [Module.Finite (Robba K) I]
    [Module.Free (Robba K) N] [Module.Finite (Robba K) N] (hIphi : IsPhiModule (restrict Φ I hI))
    (hNphi : IsPhiModule (restrict Φ N hN)) (hrank : finrank (Robba K) I = finrank (Robba K) N) :
    deg (Robba.unitOrd ψ hψn) (restrict Φ N hN) ≤ deg (Robba.unitOrd ψ hψn) (restrict Φ I hI) := by
  classical
  set r := finrank (Robba K) N
  let bN : Basis (Fin r) (Robba K) N := Module.finBasisOfFinrankEq _ _ rfl
  let bI : Basis (Fin r) (Robba K) I := Module.finBasisOfFinrankEq _ _ hrank
  obtain ⟨f, hf0, hf⟩ := exists_det_mul_eq_of_le hIN hI hN bI bN
  have uI := (isPhiModule_iff_isUnit_det bI _).1 hIphi
  have uN := (isPhiModule_iff_isUnit_det bN _).1 hNphi
  rw [deg_eq _ bN _ hNphi, deg_eq _ bI _ hIphi, degIn, degIn]
  set lu : (Robba K)ˣ := uI.unit * uN.unit⁻¹
  have hl : (lu : Robba K) * f = ψ f := by
    have : (uN.unit : Robba K) * (lu * f) = (uN.unit : Robba K) * ψ f := by
      simp only [lu, Units.val_mul, IsUnit.unit_spec]
      calc (phiMatrix bN (restrict Φ N hN)).det *
            ((phiMatrix bI (restrict Φ I hI)).det * ↑uN.unit⁻¹ * f)
          = f * (phiMatrix bI (restrict Φ I hI)).det *
              ((phiMatrix bN (restrict Φ N hN)).det * ↑uN.unit⁻¹) := by ring
        _ = f * (phiMatrix bI (restrict Φ I hI)).det := by
              rw [uN.mul_val_inv, mul_one]
        _ = _ := hf
    exact (uN.unit.isUnit.mul_left_cancel this)
  have key := Robba.gaussNorm_le_one_of_smul_eq (ι := Unit) hψ hQ (x := fun _ => f)
    (fun h0 => hf0 (congrFun h0 ())) (B := 1)
    (fun i j => by
      by_cases h : i = j
      · subst h; simp [(Robba.intBounded K).one_mem]
      · simp [Matrix.one_apply_ne h, (Robba.intBounded K).zero_mem])
    (Robba.unit_mem_bounded lu) (fun i => by simp [hl])
  have hord := (Robba.ord_nonneg_iff lu).2 key
  have hmul : Robba.ord lu = Robba.ord uI.unit - Robba.ord uN.unit := by
    simp only [lu, Robba.ord_mul]
    have := Robba.ord_mul uN.unit uN.unit⁻¹
    rw [mul_inv_cancel] at this
    have h1 : Robba.ord (1 : (Robba K)ˣ) = 0 := (Robba.ord_eq_zero_iff 1).2 (by
      rw [Units.val_one]
      refine le_antisymm (ciSup_le fun n => ?_) ?_
      · by_cases hn : n = 0
        · subst hn; simp
        · simp [hn]
      · simpa using Robba.norm_coeff_le_norm1 (Robba.bounded K).one_mem 0)
    omega
  change Robba.ord _ ≤ Robba.ord _
  omega

def IsEtale (Ψ : M →ₛₗ[ψ] M) : Prop :=
  ∃ b : Basis (Fin (finrank (Robba K) M)) (Robba K) M,
    (∀ i j, phiMatrix b Ψ i j ∈ Robba.intBounded K) ∧ Robba.norm1 (phiMatrix b Ψ).det = 1

theorem IsEtale.isUnit_det {Ψ : M →ₛₗ[ψ] M} {b : Basis (Fin (finrank (Robba K) M)) (Robba K) M}
    (hb : (∀ i j, phiMatrix b Ψ i j ∈ Robba.intBounded K) ∧ Robba.norm1 (phiMatrix b Ψ).det = 1) :
    IsUnit (phiMatrix b Ψ).det := by
  have hmem := det_mem_of_forall_mem _ _ hb.1
  refine Robba.isUnit_of_mem_bounded hmem.1 fun h0 => ?_
  have := hb.2
  rw [h0] at this
  simp [Robba.norm1] at this

theorem IsEtale.isPhiModule {Ψ : M →ₛₗ[ψ] M} (h : IsEtale Ψ) : IsPhiModule Ψ := by
  obtain ⟨b, hb⟩ := h
  exact (isPhiModule_iff_isUnit_det b Ψ).2 (IsEtale.isUnit_det hb)

theorem IsEtale.deg_eq_zero (hψn : ∀ u : (Robba K)ˣ, Robba.norm1 (ψ u) = Robba.norm1 (u : Robba K))
    {Ψ : M →ₛₗ[ψ] M} (h : IsEtale Ψ) : deg (Robba.unitOrd ψ hψn) Ψ = 0 := by
  classical
  obtain ⟨b, hb⟩ := h
  rw [deg_eq _ b _ ((isPhiModule_iff_isUnit_det b Ψ).2 (IsEtale.isUnit_det hb)), degIn]
  exact (Robba.ord_eq_zero_iff _).2 hb.2

theorem mul_map_eq_mul_phiMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Ψ : M →ₛₗ[ψ] M} (b : Basis ι (Robba K) M) {N : Submodule (Robba K) M}
    (h : IsStable Ψ N) (bN : Basis κ (Robba K) N) :
    phiMatrix b Ψ * (Matrix.of fun i j => b.repr (bN j : M) i).map ψ =
      (Matrix.of fun i j => b.repr (bN j : M) i) * phiMatrix bN (restrict Ψ N h) := by
  ext i j
  have lhs : (phiMatrix b Ψ * (Matrix.of fun i j => b.repr (bN j : M) i).map ψ) i j =
      b.repr (Ψ (bN j : M)) i := by
    rw [repr_phi]
    simp [Matrix.mul_apply, mulVec, dotProduct]
  have rhs : ((Matrix.of fun i j => b.repr (bN j : M) i) * phiMatrix bN (restrict Ψ N h)) i j =
      b.repr (Ψ (bN j : M)) i := by
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, phiMatrix_apply]
    have := congrArg (fun z : N => b.repr (z : M) i) (bN.sum_repr (restrict Ψ N h (bN j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, coe_restrict_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [lhs, rhs]

theorem deg_restrict_nonneg_of_isEtale (hψ : Robba.IsGaussScaling ψ Q) (hQ : 0 < Q)
    (hψn : ∀ u : (Robba K)ˣ, Robba.norm1 (ψ u) = Robba.norm1 (u : Robba K))
    {Ψ : M →ₛₗ[ψ] M} (hΨ : IsEtale Ψ) {N : Submodule (Robba K) M} (h : IsStable Ψ N)
    [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.Free (Robba K) N] [Module.Finite (Robba K) N] :
    0 ≤ deg (Robba.unitOrd ψ hψn) (restrict Ψ N h) := by
  classical
  obtain ⟨b, hb⟩ := hΨ
  have hNphi := isPhiModule_restrict ((isPhiModule_iff_isUnit_det b Ψ).2 (IsEtale.isUnit_det hb)) h
  set k := finrank (Robba K) N
  let bN : Basis (Fin k) (Robba K) N := Module.finBasisOfFinrankEq _ _ rfl
  set Y : Matrix (Fin (finrank (Robba K) M)) (Fin k) (Robba K) :=
    Matrix.of fun i j => b.repr (bN j : M) i
  set C := phiMatrix bN (restrict Ψ N h)
  have hrel := mul_map_eq_mul_phiMatrix b h bN
  have hx : maxMinor Y ≠ 0 := by
    rw [maxMinor_ne_zero_iff_linearIndependent]
    have hli := bN.linearIndependent.map' (b.equivFun.toLinearMap ∘ₗ N.subtype)
      (by rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_subtype])
    have hcol : Y.col = (b.equivFun.toLinearMap ∘ₗ N.subtype) ∘ bN := by
      funext j i
      simp [Y, Matrix.col, Basis.equivFun_apply]
    rw [hcol]
    exact hli
  have hC := (isPhiModule_iff_isUnit_det bN _).1 hNphi
  have key := compound_mulVec_map_maxMinor_of_mul_eq ψ (phiMatrix b Ψ) Y C hrel
  have hle := Robba.gaussNorm_le_one_of_smul_eq hψ hQ hx (B := compound k (phiMatrix b Ψ))
    (fun s t => det_mem_of_forall_mem _ _ fun i j => hb.1 _ _)
    (Robba.unit_mem_bounded hC.unit) (fun s => by
      have := congrFun key s
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [IsUnit.unit_spec, ← this])
  rw [deg_eq _ bN _ hNphi, degIn]
  exact (Robba.ord_nonneg_iff _).2 hle

end PhiModule

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Module Matrix

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

theorem Robba.gaussNorm_single_alt (k : ℤ) (c : K) : Robba.norm1 (Robba.single k c) = ‖c‖ := by
  refine le_antisymm (ciSup_le fun n => ?_) ?_
  · by_cases hn : n = k
    · subst hn; simp
    · simp [hn]
  · simpa using Robba.norm_coeff_le_norm1 (Robba.single_mem_bounded k c) k

namespace FrobeniusLift

variable (F : FrobeniusLift K)

theorem gaussNorm_phi_unit (u : (Robba K)ˣ) :
    Robba.norm1 (F.phi u) = Robba.norm1 (u : Robba K) :=
  gaussNorm_phi (Robba.unit_mem_bounded u)

theorem gaussNorm_phi_pow_unit (d : ℕ) (u : (Robba K)ˣ) :
    Robba.norm1 ((F.phi ^ d) u) = Robba.norm1 (u : Robba K) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
    have hu : IsUnit ((F.phi ^ d) (u : Robba K)) := u.isUnit.map _
    have := F.gaussNorm_phi_unit hu.unit
    rw [IsUnit.unit_spec] at this
    rw [this, ih]

def unitOrd : PhiModule.UnitOrd (Robba K) F.phi := Robba.unitOrd F.phi F.gaussNorm_phi_unit

def unitOrdPow (d : ℕ) : PhiModule.UnitOrd (Robba K) (F.phi ^ d) :=
  Robba.unitOrd (F.phi ^ d) (F.gaussNorm_phi_pow_unit d)

theorem unitOrdPow_eq (d : ℕ) : F.unitOrdPow d = F.unitOrd.pow d := rfl

end FrobeniusLift

namespace PhiModule

variable {R : Type*} [CommRing R] {φ : R →+* R}

theorem isPhiModule_of_smul [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {Ψ : M →ₛₗ[φ] M} {c : R} (h : IsPhiModule (c • Ψ)) : IsPhiModule Ψ := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [isPhiModule_iff_isUnit_det b, phiMatrix_smul, det_smul] at h
  rw [isPhiModule_iff_isUnit_det b]
  exact isUnit_of_mul_isUnit_right h

theorem isPhiModule_of_iterate [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {Φ : M →ₛₗ[φ] M} {d : ℕ} (hd : 0 < d) (h : IsPhiModule (iterate Φ d)) :
    IsPhiModule Φ := by
  classical
  let b := Module.Free.chooseBasis R M
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hd
  rw [isPhiModule_iff_isUnit_det b, zero_add, phiMatrix_iterate_succ, det_mul] at h
  rw [isPhiModule_iff_isUnit_det b]
  exact isUnit_of_mul_isUnit_left h

theorem IsStable.iterate [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] {Φ : M →ₛₗ[φ] M} {N : Submodule R M} (h : IsStable Φ N) : ∀ d, IsStable (iterate Φ d) N
  | 0 => fun x hx => hx
  | d + 1 => fun x hx => by rw [iterate_succ_apply]; exact h _ (IsStable.iterate h d x hx)

theorem IsStable.smul {M : Type*} [AddCommGroup M] [Module R M] {ψ : R →+* R} {Ψ : M →ₛₗ[ψ] M}
    {N : Submodule R M} (h : IsStable Ψ N) (c : R) : IsStable (c • Ψ) N :=
  fun x hx => N.smul_mem c (h x hx)

theorem coe_iterate_restrict [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] {Φ : M →ₛₗ[φ] M} {N : Submodule R M}
    [Module.Free R N] [Module.Finite R N] (h : IsStable Φ N) : ∀ (d : ℕ) (x : N),
    ((iterate (restrict Φ N h) d x : N) : M) = iterate Φ d (x : M)
  | 0, _ => rfl
  | d + 1, x => by
    rw [iterate_succ_apply, iterate_succ_apply, coe_restrict_apply, coe_iterate_restrict h d x]

theorem restrict_smul_iterate [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] {Φ : M →ₛₗ[φ] M} {N : Submodule R M}
    [Module.Free R N] [Module.Finite R N] (h : IsStable Φ N) (d : ℕ) (c : R) :
    restrict (c • iterate Φ d) N ((h.iterate d).smul c) = c • iterate (restrict Φ N h) d := by
  ext x
  simp [coe_iterate_restrict h d x]

end PhiModule

namespace PhiModule

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M]
variable (F : FrobeniusLift K)

def twistUnit (c : ℤ) : (Robba K)ˣ :=
  (Robba.isUnit_single 0 (zpow_ne_zero (-c) (dvUnif_ne_zero (K := K)))).unit

theorem coe_twistUnit (c : ℤ) : (twistUnit (K := K) c : Robba K) = Robba.single 0 (dvUnif K ^ (-c)) := rfl

theorem ord_twistUnit (c : ℤ) : Robba.ord (twistUnit (K := K) c) = -c := by
  apply Robba.ord_eq_of_norm1_eq
  rw [coe_twistUnit, Robba.gaussNorm_single_alt, norm_zpow]

def twistIter (Φ : M →ₛₗ[F.phi] M) (s : ℚ) : M →ₛₗ[F.phi ^ s.den] M :=
  (twistUnit (K := K) s.num : Robba K) • iterate Φ s.den

def IsPure (Φ : M →ₛₗ[F.phi] M) (s : ℚ) : Prop := IsEtale (twistIter F Φ s)

variable [Module.Free (Robba K) M] [Module.Finite (Robba K) M] {F}

theorem IsPure.isPhiModule {Φ : M →ₛₗ[F.phi] M} {s : ℚ} (h : IsPure F Φ s) : IsPhiModule Φ :=
  isPhiModule_of_iterate s.den_pos (isPhiModule_of_smul (IsEtale.isPhiModule h))

theorem deg_twistIter {Φ : M →ₛₗ[F.phi] M} (hΦ : IsPhiModule Φ) (s : ℚ) :
    deg (F.unitOrdPow s.den) (twistIter F Φ s) =
      s.den * deg F.unitOrd Φ - finrank (Robba K) M * s.num := by
  rw [twistIter, deg_smul _ (isPhiModule_iterate hΦ _) (twistUnit s.num), F.unitOrdPow_eq,
    deg_iterate F.unitOrd hΦ s.den]
  change _ + _ * Robba.ord _ = _
  rw [ord_twistUnit]
  ring

theorem IsPure.deg_eq {Φ : M →ₛₗ[F.phi] M} {s : ℚ} (h : IsPure F Φ s) :
    (deg F.unitOrd Φ : ℚ) = s * finrank (Robba K) M := by
  have h0 := IsEtale.deg_eq_zero (F.gaussNorm_phi_pow_unit s.den) (show IsEtale _ from h)
  rw [show Robba.unitOrd (F.phi ^ s.den) (F.gaussNorm_phi_pow_unit s.den) = F.unitOrdPow s.den from rfl,
    deg_twistIter h.isPhiModule] at h0
  have hd : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_pos.ne'
  have e : (s.den : ℚ) * deg F.unitOrd Φ = finrank (Robba K) M * s.num := by exact_mod_cast (by linarith)
  rw [← Rat.num_div_den s]
  field_simp
  linarith

theorem IsPure.le_deg {Φ : M →ₛₗ[F.phi] M} {s : ℚ} (h : IsPure F Φ s) {N : Submodule (Robba K) M}
    (hN : IsStable Φ N) [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.Free (Robba K) N]
    [Module.Finite (Robba K) N] :
    s * finrank (Robba K) N ≤ deg F.unitOrd (restrict Φ N hN) := by
  have hNphi := isPhiModule_restrict h.isPhiModule hN
  have hst : IsStable (twistIter F Φ s) N := (hN.iterate s.den).smul _
  have h0 := deg_restrict_nonneg_of_isEtale ((F.isGaussScaling).pow F.q_pos s.den)
    (pow_pos F.q_pos _) (F.gaussNorm_phi_pow_unit s.den) h hst
  rw [show Robba.unitOrd (F.phi ^ s.den) (F.gaussNorm_phi_pow_unit s.den) = F.unitOrdPow s.den from rfl]
    at h0
  have e : restrict (twistIter F Φ s) N hst = twistIter F (restrict Φ N hN) s :=
    restrict_smul_iterate hN s.den _
  rw [e, deg_twistIter hNphi] at h0
  have hd : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
  have h1 : (finrank (Robba K) N : ℚ) * s.num ≤ s.den * deg F.unitOrd (restrict Φ N hN) := by
    exact_mod_cast (by linarith)
  rw [← Rat.num_div_den s, div_mul_eq_mul_div, div_le_iff₀ hd]
  linarith

def degSub (v : UnitOrd (Robba K) F.phi) (Φ : M →ₛₗ[F.phi] M) (N : Submodule (Robba K) M)
    (h : IsStable Φ N) [Module.IsTorsionFree (Robba K) (M ⧸ N)] : ℤ :=
  letI := free_of_saturated N
  letI := finite_of_saturated N
  deg v (restrict Φ N h)


variable (F) in

def IsSemistable (Φ : M →ₛₗ[F.phi] M) : Prop :=
  IsPhiModule Φ ∧ ∀ (N : Submodule (Robba K) M) (h : IsStable Φ N)
    [Module.IsTorsionFree (Robba K) (M ⧸ N)],
    deg F.unitOrd Φ * (finrank (Robba K) N : ℤ) ≤ degSub F.unitOrd Φ N h * finrank (Robba K) M


end PhiModule

namespace PhiModule

variable {F : FrobeniusLift K}
variable {A B : Type*} [AddCommGroup A] [Module (Robba K) A] [Module.Free (Robba K) A]
  [Module.Finite (Robba K) A] [AddCommGroup B] [Module (Robba K) B] [Module.Free (Robba K) B]
  [Module.Finite (Robba K) B]

theorem IsPure.hom_eq_zero {ΦA : A →ₛₗ[F.phi] A} {ΦB : B →ₛₗ[F.phi] B} {s t : ℚ}
    (hA : IsPure F ΦA s) (hB : IsPure F ΦB t) (hst : s < t) {f : A →ₗ[Robba K] B}
    (hf : IsEquivariant f ΦA ΦB) : f = 0 := by
  by_contra hf0

  have hK : IsStable ΦA (LinearMap.ker f) := hf.isStable_ker
  have : Module.IsTorsionFree (Robba K) (A ⧸ LinearMap.ker f) := isTorsionFree_quotient_ker f
  have := free_of_saturated (LinearMap.ker f)
  have := finite_of_saturated (LinearMap.ker f)
  have := free_quot_of_saturated (LinearMap.ker f)

  have hI : IsStable ΦB (LinearMap.range f) := hf.isStable_range
  let e : (A ⧸ LinearMap.ker f) ≃ₗ[Robba K] LinearMap.range f := f.quotKerEquivRange
  have : Module.Free (Robba K) (LinearMap.range f) := Module.Free.of_equiv e
  have : Module.Finite (Robba K) (LinearMap.range f) := Module.Finite.equiv e
  have he : ∀ x, e (quot ΦA _ hK x) = restrict ΦB _ hI (e x) := hf.quotKerEquivRange
  have hQphi : IsPhiModule (quot ΦA _ hK) := isPhiModule_quot hA.isPhiModule hK
  have hIphi : IsPhiModule (restrict ΦB _ hI) := (isPhiModule_congr e he).1 hQphi
  have hdegI : deg F.unitOrd (restrict ΦB _ hI) = deg F.unitOrd (quot ΦA _ hK) :=
    deg_congr _ e he

  have hN : IsStable ΦB (saturation (LinearMap.range f)) := hI.saturation F.phi_injective
  have := free_of_saturated (saturation (LinearMap.range f))
  have := finite_of_saturated (saturation (LinearMap.range f))
  have hNphi := isPhiModule_restrict hB.isPhiModule hN
  have hrank : finrank (Robba K) (LinearMap.range f) =
      finrank (Robba K) (saturation (LinearMap.range f)) := (finrank_saturation _).symm
  have hle : deg F.unitOrd (restrict ΦB _ hN) ≤ deg F.unitOrd (restrict ΦB _ hI) :=
    le_deg_of_le F.isGaussScaling F.q_pos F.gaussNorm_phi_unit (le_saturation _) hI hN hIphi hNphi hrank

  have h1 := hB.le_deg hN
  have hadd := deg_eq_deg_restrict_add F.unitOrd hA.isPhiModule hK
  have h2 := hA.le_deg hK
  have h3 := hA.deg_eq
  have hrk := finrank_add_finrank_quotient (LinearMap.ker f)
  have hrkI : finrank (Robba K) (LinearMap.range f) = finrank (Robba K) (A ⧸ LinearMap.ker f) :=
    e.finrank_eq.symm
  have hIne : LinearMap.range f ≠ ⊥ := fun h => hf0 (LinearMap.range_eq_bot.1 h)
  have hpos : 0 < finrank (Robba K) (LinearMap.range f) := Submodule.one_le_finrank_iff.2 hIne

  set r := finrank (Robba K) (LinearMap.range f)
  have hrQ : (r : ℚ) > 0 := by exact_mod_cast hpos
  have hle' : (deg F.unitOrd (restrict ΦB _ hN) : ℚ) ≤ deg F.unitOrd (restrict ΦB _ hI) := by
    exact_mod_cast hle
  have hadd' : (deg F.unitOrd ΦA : ℚ) = deg F.unitOrd (restrict ΦA _ hK) + deg F.unitOrd (quot ΦA _ hK) := by
    exact_mod_cast hadd
  have hdegI' : (deg F.unitOrd (restrict ΦB _ hI) : ℚ) = deg F.unitOrd (quot ΦA _ hK) := by
    exact_mod_cast hdegI
  have hrk' : (finrank (Robba K) (LinearMap.ker f) : ℚ) + finrank (Robba K) (A ⧸ LinearMap.ker f) =
      finrank (Robba K) A := by exact_mod_cast hrk
  rw [← hrank] at h1
  have hrkI' : (r : ℚ) = finrank (Robba K) (A ⧸ LinearMap.ker f) := by exact_mod_cast hrkI
  have key : t * r ≤ s * r := by
    have : s * finrank (Robba K) A - s * finrank (Robba K) (LinearMap.ker f) = s * r := by
      rw [hrkI', ← hrk']; ring
    linarith
  nlinarith

section Subquotients

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

def subquotMap {P X Z Y : Submodule (Robba K) M} (hXY : X ≤ Y) (hPZ : P ≤ Z) :
    (X ⧸ inSub P X) →ₗ[Robba K] (Y ⧸ inSub Z Y) :=
  (inSub P X).mapQ (inSub Z Y) (Submodule.inclusion hXY) fun _ hx => hPZ hx

theorem subquotMap_mk {P X Z Y : Submodule (Robba K) M} (hXY : X ≤ Y) (hPZ : P ≤ Z) (x : X) :
    subquotMap hXY hPZ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hXY x) :=
  rfl

theorem isEquivariant_subquotMap {Φ : M →ₛₗ[F.phi] M} {P X Z Y : Submodule (Robba K) M}
    (hP : IsStable Φ P) (hX : IsStable Φ X) (hZ : IsStable Φ Z) (hY : IsStable Φ Y)
    (hXY : X ≤ Y) (hPZ : P ≤ Z) :
    IsEquivariant (subquotMap hXY hPZ) (subquot Φ P X hP hX) (subquot Φ Z Y hZ hY) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem subquotMap_ne_zero {P X Z Y : Submodule (Robba K) M} (hXY : X ≤ Y) (hPZ : P ≤ Z)
    (hXZ : ¬ X ≤ Z) : subquotMap hXY hPZ ≠ 0 := by
  intro h0
  apply hXZ
  intro x hx
  have := LinearMap.congr_fun h0 (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [subquotMap_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this
  exact this

variable (F) in

def IsPureSubquot (Φ : M →ₛₗ[F.phi] M) (N N' : Submodule (Robba K) M) (h : IsStable Φ N)
    (h' : IsStable Φ N') [Module.IsTorsionFree (Robba K) (M ⧸ N)]
    [Module.IsTorsionFree (Robba K) (M ⧸ N')] (s : ℚ) : Prop :=
  letI := free_subquot (N := N) (N' := N')
  letI := finite_subquot (N := N) (N' := N')
  IsPure F (subquot Φ N N' h h') s

theorem subquotMap_eq_zero {Φ : M →ₛₗ[F.phi] M} {P X Z Y : Submodule (Robba K) M}
    (hP : IsStable Φ P) (hX : IsStable Φ X) (hZ : IsStable Φ Z) (hY : IsStable Φ Y)
    [Module.IsTorsionFree (Robba K) (M ⧸ P)] [Module.IsTorsionFree (Robba K) (M ⧸ X)]
    [Module.IsTorsionFree (Robba K) (M ⧸ Z)] [Module.IsTorsionFree (Robba K) (M ⧸ Y)]
    (hXY : X ≤ Y) (hPZ : P ≤ Z) {s t : ℚ} (hs : IsPureSubquot F Φ P X hP hX s)
    (ht : IsPureSubquot F Φ Z Y hZ hY t) (hst : s < t) : subquotMap hXY hPZ = 0 := by
  have := free_subquot (N := P) (N' := X)
  have := finite_subquot (N := P) (N' := X)
  have := free_subquot (N := Z) (N' := Y)
  have := finite_subquot (N := Z) (N' := Y)
  exact IsPure.hom_eq_zero hs ht hst (isEquivariant_subquotMap hP hX hZ hY hXY hPZ)

end Subquotients

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

variable (F) in

structure SlopeFiltration (Φ : M →ₛₗ[F.phi] M) where

  length : ℕ

  N : ℕ → Submodule (Robba K) M

  slope : ℕ → ℚ
  N_zero : N 0 = ⊥
  N_of_le : ∀ i, length ≤ i → N i = ⊤
  lt_succ : ∀ i, i < length → N i < N (i + 1)
  stable : ∀ i, IsStable Φ (N i)
  saturated : ∀ i, Module.IsTorsionFree (Robba K) (M ⧸ N i)
  pure : ∀ i, i < length →
    haveI := saturated i
    haveI := saturated (i + 1)
    IsPureSubquot F Φ (N i) (N (i + 1)) (stable i) (stable (i + 1)) (slope i)
  slope_lt : ∀ i j, i < j → j < length → slope i < slope j

namespace SlopeFiltration

variable {Φ : M →ₛₗ[F.phi] M}

theorem N_mono (S : SlopeFiltration F Φ) : Monotone S.N := by
  refine monotone_nat_of_le_succ fun i => ?_
  by_cases hi : i < S.length
  · exact (S.lt_succ i hi).le
  · rw [S.N_of_le i (not_lt.1 hi), S.N_of_le (i + 1) (by omega)]

theorem lt_length_of_ne_top (S : SlopeFiltration F Φ) {i : ℕ} (h : S.N i ≠ ⊤) : i < S.length := by
  by_contra hi
  exact h (S.N_of_le i (not_lt.1 hi))

theorem step (S₁ S₂ : SlopeFiltration F Φ) {i : ℕ} (hi₁ : i < S₁.length) (hi₂ : i < S₂.length)
    (hN : S₁.N i = S₂.N i) (hs : S₁.slope i ≤ S₂.slope i) :
    S₁.N (i + 1) ≤ S₂.N (i + 1) ∧ S₂.slope i ≤ S₁.slope i := by
  classical
  have := S₁.saturated i
  have := S₁.saturated (i + 1)
  constructor
  · by_contra hcon
    have hex : ∃ j, S₁.N (i + 1) ≤ S₂.N j := ⟨S₂.length, by rw [S₂.N_of_le _ le_rfl]; exact le_top⟩
    set j := Nat.find hex
    have hj : S₁.N (i + 1) ≤ S₂.N j := Nat.find_spec hex
    have hj1 : i + 1 < j := by
      by_contra hle
      exact hcon (hj.trans (S₂.N_mono (not_lt.1 hle)))
    obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hkmin : ¬ S₁.N (i + 1) ≤ S₂.N k := Nat.find_min hex (by omega)
    have hkl : k < S₂.length := S₂.lt_length_of_ne_top fun htop => hkmin (htop ▸ le_top)
    have := S₂.saturated k
    have := S₂.saturated (k + 1)
    have hPZ : S₁.N i ≤ S₂.N k := hN ▸ S₂.N_mono (by omega)
    have hXY : S₁.N (i + 1) ≤ S₂.N (k + 1) := hk ▸ hj
    have hlt : S₁.slope i < S₂.slope k := lt_of_le_of_lt hs (S₂.slope_lt i k (by omega) hkl)
    exact subquotMap_ne_zero hXY hPZ hkmin (subquotMap_eq_zero (S₁.stable i) (S₁.stable (i + 1))
      (S₂.stable k) (S₂.stable (k + 1)) hXY hPZ (S₁.pure i hi₁) (S₂.pure k hkl) hlt)
  · by_contra hcon
    rw [not_le] at hcon

    have hle : S₁.N (i + 1) ≤ S₂.N (i + 1) := by
      by_contra hcon'
      have hex : ∃ j, S₁.N (i + 1) ≤ S₂.N j :=
        ⟨S₂.length, by rw [S₂.N_of_le _ le_rfl]; exact le_top⟩
      set j := Nat.find hex
      have hj : S₁.N (i + 1) ≤ S₂.N j := Nat.find_spec hex
      have hj1 : i + 1 < j := by
        by_contra hle
        exact hcon' (hj.trans (S₂.N_mono (not_lt.1 hle)))
      obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hkmin : ¬ S₁.N (i + 1) ≤ S₂.N k := Nat.find_min hex (by omega)
      have hkl : k < S₂.length := S₂.lt_length_of_ne_top fun htop => hkmin (htop ▸ le_top)
      have := S₂.saturated k
      have := S₂.saturated (k + 1)
      have hPZ : S₁.N i ≤ S₂.N k := hN ▸ S₂.N_mono (by omega)
      have hXY : S₁.N (i + 1) ≤ S₂.N (k + 1) := hk ▸ hj
      have hlt : S₁.slope i < S₂.slope k := lt_of_le_of_lt hs (S₂.slope_lt i k (by omega) hkl)
      exact subquotMap_ne_zero hXY hPZ hkmin (subquotMap_eq_zero (S₁.stable i) (S₁.stable (i + 1))
        (S₂.stable k) (S₂.stable (k + 1)) hXY hPZ (S₁.pure i hi₁) (S₂.pure k hkl) hlt)
    have := S₂.saturated i
    have := S₂.saturated (i + 1)
    have hnot : ¬ S₁.N (i + 1) ≤ S₂.N i := fun h' =>
      not_le_of_gt (S₁.lt_succ i hi₁) (by rw [hN]; exact h')
    exact subquotMap_ne_zero hle hN.le hnot (subquotMap_eq_zero (S₁.stable i) (S₁.stable (i + 1))
      (S₂.stable i) (S₂.stable (i + 1)) hle hN.le (S₁.pure i hi₁) (S₂.pure i hi₂) hcon)

theorem unique (S₁ S₂ : SlopeFiltration F Φ) :
    S₁.length = S₂.length ∧ S₁.N = S₂.N ∧ ∀ i < S₁.length, S₁.slope i = S₂.slope i := by

  have hN : ∀ i, S₁.N i = S₂.N i := by
    intro i
    induction i with
    | zero => rw [S₁.N_zero, S₂.N_zero]
    | succ i ih =>
      by_cases h₁ : i < S₁.length
      · by_cases h₂ : i < S₂.length
        · rcases le_total (S₁.slope i) (S₂.slope i) with hs | hs
          · obtain ⟨hle, hs'⟩ := step S₁ S₂ h₁ h₂ ih hs
            exact le_antisymm hle (step S₂ S₁ h₂ h₁ ih.symm hs').1
          · obtain ⟨hle, hs'⟩ := step S₂ S₁ h₂ h₁ ih.symm hs
            exact le_antisymm (step S₁ S₂ h₁ h₂ ih hs').1 hle
        · exfalso
          have h2 := S₂.N_of_le i (not_lt.1 h₂)
          have := S₁.lt_succ i h₁
          rw [ih, h2] at this
          exact (this.trans_le le_top).false
      · have h1 := S₁.N_of_le i (not_lt.1 h₁)
        by_cases h₂ : i < S₂.length
        · exfalso
          have := S₂.lt_succ i h₂
          rw [← ih, h1] at this
          exact (this.trans_le le_top).false
        · rw [S₁.N_of_le (i + 1) (by omega), S₂.N_of_le (i + 1) (by omega)]

  have hlen : S₁.length = S₂.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := S₂.lt_succ S₁.length h
      rw [← hN, ← hN, S₁.N_of_le _ le_rfl, S₁.N_of_le _ (by omega)] at this
      exact this.false
    · have := S₁.lt_succ S₂.length h
      rw [hN, hN, S₂.N_of_le _ le_rfl, S₂.N_of_le _ (by omega)] at this
      exact this.false
  refine ⟨hlen, funext hN, fun i hi => ?_⟩
  have hi₂ : i < S₂.length := hlen ▸ hi
  rcases le_total (S₁.slope i) (S₂.slope i) with hs | hs
  · exact le_antisymm hs (step S₁ S₂ hi hi₂ (hN i) hs).2
  · exact le_antisymm (step S₂ S₁ hi₂ hi (hN i).symm hs).2 hs

end SlopeFiltration

end PhiModule

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Module

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

namespace PhiModule

universe u

variable {F : FrobeniusLift K}
variable {M : Type u} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

variable (F) in

def IsSemistableSubquot (Φ : M →ₛₗ[F.phi] M) (N N' : Submodule (Robba K) M) (h : IsStable Φ N)
    (h' : IsStable Φ N') [Module.IsTorsionFree (Robba K) (M ⧸ N)]
    [Module.IsTorsionFree (Robba K) (M ⧸ N')] : Prop :=
  letI := free_subquot (N := N) (N' := N')
  letI := finite_subquot (N := N) (N' := N')
  IsSemistable F (subquot Φ N N' h h')

variable (F) in

def degSubquot (Φ : M →ₛₗ[F.phi] M) (N N' : Submodule (Robba K) M) (h : IsStable Φ N)
    (h' : IsStable Φ N') [Module.IsTorsionFree (Robba K) (M ⧸ N)]
    [Module.IsTorsionFree (Robba K) (M ⧸ N')] : ℤ :=
  letI := free_subquot (N := N) (N' := N')
  letI := finite_subquot (N := N) (N' := N')
  deg F.unitOrd (subquot Φ N N' h h')

variable (F) in

structure HNFiltration (Φ : M →ₛₗ[F.phi] M) where

  length : ℕ

  N : ℕ → Submodule (Robba K) M

  slope : ℕ → ℚ
  N_zero : N 0 = ⊥
  N_of_le : ∀ i, length ≤ i → N i = ⊤
  lt_succ : ∀ i, i < length → N i < N (i + 1)
  stable : ∀ i, IsStable Φ (N i)
  saturated : ∀ i, Module.IsTorsionFree (Robba K) (M ⧸ N i)
  semistable : ∀ i, i < length →
    haveI := saturated i
    haveI := saturated (i + 1)
    IsSemistableSubquot F Φ (N i) (N (i + 1)) (stable i) (stable (i + 1))
  deg_eq : ∀ i, i < length →
    haveI := saturated i
    haveI := saturated (i + 1)
    (degSubquot F Φ (N i) (N (i + 1)) (stable i) (stable (i + 1)) : ℚ) =
      slope i * finrank (Robba K) (N (i + 1) ⧸ inSub (N i) (N (i + 1)))
  slope_lt : ∀ i j, i < j → j < length → slope i < slope j

theorem finrank_subquot_pos {N N' : Submodule (Robba K) M} (hlt : N < N')
    [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.IsTorsionFree (Robba K) (M ⧸ N')] :
    0 < finrank (Robba K) (N' ⧸ inSub N N') := by
  have := free_subquot (N := N) (N' := N')
  have := finite_subquot (N := N) (N' := N')
  have := isTorsionFree_subquot (N := N) (N' := N')
  rw [Module.finrank_pos_iff_exists_ne_zero]
  obtain ⟨x, hx, hxN⟩ := SetLike.exists_of_lt hlt
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, fun h0 => hxN ?_⟩
  rw [Submodule.Quotient.mk_eq_zero] at h0
  exact h0

def HNFiltration.toSlopeFiltration {Φ : M →ₛₗ[F.phi] M}
    (hss : ∀ (M' : Type u) [AddCommGroup M'] [Module (Robba K) M'] [Module.Free (Robba K) M']
      [Module.Finite (Robba K) M'] (Φ' : M' →ₛₗ[F.phi] M'), IsSemistable F Φ' →
      0 < finrank (Robba K) M' → IsPure F Φ' ((deg F.unitOrd Φ' : ℚ) / finrank (Robba K) M'))
    (S : HNFiltration F Φ) : SlopeFiltration F Φ where
  length := S.length
  N := S.N
  slope := S.slope
  N_zero := S.N_zero
  N_of_le := S.N_of_le
  lt_succ := S.lt_succ
  stable := S.stable
  saturated := S.saturated
  pure i hi := by
    have := S.saturated i
    have := S.saturated (i + 1)
    have := free_subquot (N := S.N i) (N' := S.N (i + 1))
    have := finite_subquot (N := S.N i) (N' := S.N (i + 1))
    have hpos := finrank_subquot_pos (S.lt_succ i hi)
    have hp := hss _ _ (S.semistable i hi) hpos
    have hdeg := S.deg_eq i hi
    have hr : (finrank (Robba K) (S.N (i + 1) ⧸ inSub (S.N i) (S.N (i + 1))) : ℚ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    change IsPure F (subquot Φ (S.N i) (S.N (i + 1)) (S.stable i) (S.stable (i + 1))) (S.slope i)
    change (degSubquot F Φ _ _ _ _ : ℚ) = _ at hdeg
    unfold degSubquot at hdeg
    rw [hdeg, mul_div_assoc, div_self hr, mul_one] at hp
    exact hp
  slope_lt := S.slope_lt


end PhiModule

end GroundTheory.PAdicHodge
end
end
