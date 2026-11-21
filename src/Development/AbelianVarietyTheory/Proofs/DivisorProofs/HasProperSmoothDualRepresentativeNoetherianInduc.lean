import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelAmpleOfAffineOpenMeetsFibres
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcCompOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCover
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfHasRepUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRhamCpl

open GlobalTheory.PDiv (ModPow)

section Rings

variable (p : ℕ) (O : Type) [CommRing O]

def modPowTr (N : ℕ) : ModPow p O (N + 1) →+* ModPow p O N :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ N.le_succ))

end Rings

section BaseChange

variable {O O' B B' : Type} [CommRing O] [CommRing O'] [CommRing B] [CommRing B']

abbrev bcObj (a : O →+* B) (A : Over (Sp O)) : Over (Sp B) := (Over.pullback (spMap a)).obj A

instance bcObj.instGrpObj (a : O →+* B) (A : Over (Sp O)) [GrpObj A] : GrpObj (bcObj a A) :=
  Functor.grpObjObj

theorem bcObj_isGrpPullback (a : O →+* B) (A : Over (Sp O)) [GrpObj A] :
    IsGrpPullback (bcObj a A) A (spMap a) (pullback.fst _ _) :=
  isGrpPullback_pullback A (spMap a)

theorem bcObj_isAbelianScheme (a : O →+* B) {A : Over (Sp O)} [GrpObj A] (hA : IsAbelianScheme A) :
    IsAbelianScheme (bcObj a A) :=
  GlobalTheory.isAbelianScheme_pullback_obj _ A hA

def bcHom {σ : O →+* O'} {a : O →+* B} {a' : O' →+* B'} {τ : B →+* B'} (h : a'.comp σ = τ.comp a)
    {A : Over (Sp O)} {A' : Over (Sp O')} {φ : A'.left ⟶ A.left} (hφ : φ ≫ A.hom = A'.hom ≫ spMap σ) :
    (bcObj a' A').left ⟶ (bcObj a A).left :=
  pullback.lift (pullback.fst _ _ ≫ φ) (pullback.snd _ _ ≫ spMap τ) (by
    rw [Category.assoc, hφ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← Cris.spMap_comp, ← Cris.spMap_comp, h])

@[simp] theorem bcHom_fst {σ : O →+* O'} {a : O →+* B} {a' : O' →+* B'} {τ : B →+* B'}
    (h : a'.comp σ = τ.comp a) {A : Over (Sp O)} {A' : Over (Sp O')} {φ : A'.left ⟶ A.left}
    (hφ : φ ≫ A.hom = A'.hom ≫ spMap σ) :
    bcHom h hφ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ := pullback.lift_fst _ _ _

@[simp] theorem bcHom_snd {σ : O →+* O'} {a : O →+* B} {a' : O' →+* B'} {τ : B →+* B'}
    (h : a'.comp σ = τ.comp a) {A : Over (Sp O)} {A' : Over (Sp O')} {φ : A'.left ⟶ A.left}
    (hφ : φ ≫ A.hom = A'.hom ≫ spMap σ) :
    bcHom h hφ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap τ := pullback.lift_snd _ _ _

end BaseChange

section Levels

variable (p : ℕ) {O : Type} [CommRing O]

abbrev lev (A : Over (Sp O)) (N : ℕ) : Over (Sp (ModPow p O N)) :=
  bcObj (algebraMap O (ModPow p O N)) A

variable {p} {A : Over (Sp O)} [GrpObj A]

theorem lev_isAbelianScheme (hA : IsAbelianScheme A) (N : ℕ) : IsAbelianScheme (lev p A N) :=
  bcObj_isAbelianScheme _ hA

variable (p A) in

def levPull (N : ℕ) : primDR A →ₛₗ[algebraMap O (ModPow p O N)] primDR (lev p A N) :=
  (PDiv.grpMor_of_isGrpPullback (bcObj_isGrpPullback (algebraMap O (ModPow p O N)) A)).pull

end Levels

abbrev Family (p : ℕ) : Type 1 :=
  ∀ ⦃R : Type⦄ [CommRing R], IsAdicComplete (Ideal.span {(p : R)}) R → ∀ ⦃A : Over (Sp R)⦄ [GrpObj A],
    IsAbelianScheme A → (∃ g : ℕ, SmoothOfRelativeDimension g A.hom) →
    ∀ ⦃G : PDivGroup p R⦄, G.TorsionTower A → (primDR A ≃ₗ[R] G.RigExt)

variable {p : ℕ} (E : Family p)

end GlobalTheory.DeRhamCpl
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem lbIso_of_isEmpty {X : Scheme.{0}} [IsEmpty X] (L M : LB X) : LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have hU : (LB.div M L).U i ⊓ (LB.div M L).U j = ⊥ := by ext x; exact (IsEmpty.false x).elim
  have : Subsingleton Γ(X, (LB.div M L).U i ⊓ (LB.div M L).U j) := by rw [hU]; infer_instance
  exact Subsingleton.elim _ _

theorem hasRepAF_of_isEmpty : ∀ (S : Scheme.{0}) (A S' : Over S) [GrpObj A] (g : ℕ), IsEmpty S'.left →
    HasRepAF A g S' := by
  intro S A S' _ g hS
  have emp : ∀ {Y : Over S} (_ : Y ⟶ S'), IsEmpty Y.left := fun y => ⟨fun p => hS.false (y.left p)⟩
  refine ⟨S', 𝟙 S', LB.triv _, ⟨⟨LB.isLB_triv _, fun Y a a' t => ?_⟩, fun T t N _ => ?_⟩, ?_, ?_⟩
  · have := emp t; exact lbIso_of_isEmpty _ _
  · have := emp (snd A T ≫ t)
    exact ⟨t, ⟨Category.comp_id _, lbIso_of_isEmpty _ _⟩, fun x hx => (Category.comp_id x).symm.trans hx.1⟩
  · rw [Over.id_left]
    refine ⟨inferInstance, ⟨fun x => isEmptyElim x⟩, ⟨?_⟩⟩
    intro K _ y Z fst snd h
    exact isEmptyElim (y (IsLocalRing.closedPoint K))
  · intro F; exact ⟨⊥, isAffineOpen_bot _, fun x _ => isEmptyElim x⟩

end GlobalTheory.DualCon
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_isEmpty : ∀ (S : Scheme.{0}) (A S' : Over S) [GrpObj A] (g : ℕ), IsEmpty S'.left → HasRepAF A g S' := by
  atlas_forward_decl GlobalTheory.DualCon.hasRepAF_of_isEmpty
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relAmple_of_affineOpen_meets_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  first | exact @GlobalTheory.ProjNormal.exists_relAmple_of_affine | exact GlobalTheory.ProjNormal.exists_relAmple_of_affine | (intros; apply GlobalTheory.ProjNormal.exists_relAmple_of_affine <;> assumption)
end

section
section
open scoped nonZeroDivisors

namespace GlobalTheory.ReducedNormalisation

theorem exists_mem_others_not_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Ideal R) (hp : ∀ i, (p i).IsPrime) (hmin : ∀ i j, p i ≤ p j → i = j) (i : ι) :
    ∃ a : R, a ∉ p i ∧ ∀ j, j ≠ i → a ∈ p j := by
  by_contra h
  push_neg at h
  have hle : (Finset.univ.erase i).inf p ≤ p i := by
    intro a ha
    by_contra hai
    obtain ⟨j, hj, hja⟩ := h a hai
    exact hja ((Finset.inf_le (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) : _ ≤ p j) ha)
  obtain ⟨j, hj, hji⟩ := ((hp i).inf_le').1 hle
  exact (Finset.mem_erase.1 hj).1 (hmin j i hji)

theorem exists_conductor_elem {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] (J : Ideal R)
    (e : R) (he : e ∈ J) (hep : e ∉ p)
    [Module.Finite (R ⧸ p) (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))] :
    ∃ c : R, c ∉ p ∧ c ∈ J ∧ ∀ d : integralClosure (R ⧸ p) (FractionRing (R ⧸ p)),
      ∃ y ∈ J, algebraMap R (FractionRing (R ⧸ p)) y =
        algebraMap R (FractionRing (R ⧸ p)) c * (d : FractionRing (R ⧸ p)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R ⧸ p)
    (M := integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (R ⧸ p)⁰
    (S := FractionRing (R ⧸ p)) (s.image Subtype.val)
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ p)
  have htp : t ∉ p := by
    intro h
    have h0 : (b : R ⧸ p) = 0 := by rw [← ht]; exact Ideal.Quotient.eq_zero_iff_mem.2 h
    exact nonZeroDivisors.coe_ne_zero b h0
  refine ⟨e * t, fun h => (hp.mem_or_mem h).elim hep htp, J.mul_mem_right t he, fun d => ?_⟩
  have key : ∀ d ∈ Submodule.span (R ⧸ p)
      (s : Set (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))),
      ∃ y ∈ J, algebraMap R (FractionRing (R ⧸ p)) y =
        algebraMap R (FractionRing (R ⧸ p)) (e * t) * (d : FractionRing (R ⧸ p)) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨x, hx⟩ := hb (g : FractionRing (R ⧸ p)) (Finset.mem_image_of_mem Subtype.val hg)
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨e * x', J.mul_mem_right x' he, ?_⟩
      have h1 : algebraMap R (FractionRing (R ⧸ p)) x' =
          algebraMap R (FractionRing (R ⧸ p)) t * (g : FractionRing (R ⧸ p)) := by
        rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) x',
          IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) t,
          Ideal.Quotient.algebraMap_eq, hx, ht]
        exact Algebra.smul_def _ _
      rw [map_mul, map_mul, h1, mul_assoc]
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨y1, hy1, e1⟩ := hx
      obtain ⟨y2, hy2, e2⟩ := hy
      exact ⟨y1 + y2, J.add_mem hy1 hy2, by
        rw [map_add, e1, e2, ← mul_add]; rfl⟩
    | smul q x _ hx =>
      obtain ⟨y1, hy1, e1⟩ := hx
      obtain ⟨q', rfl⟩ := Ideal.Quotient.mk_surjective q
      refine ⟨q' * y1, J.mul_mem_left q' hy1, ?_⟩
      rw [map_mul, e1]
      show _ = _ * ((Ideal.Quotient.mk p q') • (x : FractionRing (R ⧸ p)))
      rw [Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      ring
  exact key d (by rw [hs]; trivial)

theorem algebraMap_eq_zero_of_mem {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] {z : R}
    (hz : z ∈ p) : algebraMap R (FractionRing (R ⧸ p)) z = 0 := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hz, map_zero]

theorem exists_conductor {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Ideal R) [hp : ∀ i, (p i).IsPrime] (hmin : ∀ i j, p i ≤ p j → i = j)
    [∀ i, Module.Finite (R ⧸ p i) (integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i)))] :
    ∃ a : R, (∀ i, a ∉ p i) ∧
      ∀ r : (∀ i, integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i))),
        ∃ y : R, algebraMap R _ y = algebraMap R _ a * r := by
  classical
  have hc : ∀ i, ∃ c : R, c ∉ p i ∧ c ∈ (⨅ (j : ι) (_ : j ≠ i), p j) ∧
      ∀ d : integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i)),
        ∃ y ∈ (⨅ (j : ι) (_ : j ≠ i), p j), algebraMap R (FractionRing (R ⧸ p i)) y =
          algebraMap R (FractionRing (R ⧸ p i)) c * (d : FractionRing (R ⧸ p i)) := by
    intro i
    obtain ⟨e, hei, hej⟩ := exists_mem_others_not_mem p hp hmin i
    exact exists_conductor_elem (p i) _ e
      ((Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).2 fun hj => hej j hj) hei
  choose c hcp hcJ hcd using hc
  have hmemJ : ∀ {i k : ι} {z : R}, z ∈ (⨅ (j : ι) (_ : j ≠ i), p j) → i ≠ k → z ∈ p k :=
    fun hz hik => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz _) (Ne.symm hik)
  refine ⟨∑ i, c i, fun i h => hcp i ?_, fun r => ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    refine (Submodule.add_mem_iff_left _ (Submodule.sum_mem _ fun j hj => ?_)).1 h
    exact hmemJ (hcJ j) (Finset.mem_erase.1 hj).1
  choose y hyJ hy using fun i => hcd i (r i)
  refine ⟨∑ i, y i, funext fun k => Subtype.ext ?_⟩
  change algebraMap R (FractionRing (R ⧸ p k)) (∑ i, y i) =
    algebraMap R (FractionRing (R ⧸ p k)) (∑ i, c i) * (r k : FractionRing (R ⧸ p k))
  rw [map_sum, map_sum, Finset.sum_mul, Finset.sum_eq_single k, Finset.sum_eq_single k, hy k]
  · intro i _ hik
    rw [algebraMap_eq_zero_of_mem (p k) (hmemJ (hcJ i) hik), zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h
  · intro i _ hik
    exact algebraMap_eq_zero_of_mem (p k) (hmemJ (hyJ i) hik)
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.ReducedNormalisation

namespace GlobalTheory.ReducedNormalisation

theorem exists_finiteIndex_prod_normalDomains :
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R],
      ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)),
        (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧
        Function.Injective (algebraMap R (∀ i, D i)) ∧
        ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R,
          algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r := by
  intro R _ _ _ _
  classical
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  letI : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let e := Fintype.equivFin (minimalPrimes R)
  let p : Fin (Fintype.card (minimalPrimes R)) → Ideal R := fun k => (e.symm k).1
  haveI hp : ∀ k, (p k).IsPrime := fun k => Ideal.minimalPrimes_isPrime (e.symm k).2
  have hmin : ∀ k l, p k ≤ p l → k = l := by
    intro k l h
    have h2 : p l ≤ p k := (e.symm l).2.2 ⟨hp k, bot_le⟩ h
    exact e.symm.injective (Subtype.ext (le_antisymm h h2))
  haveI : ∀ k, Module.Finite (R ⧸ p k) (integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k))) :=
    fun k => by
      have h : Algebra.EssFiniteType ℤ (R ⧸ p k) := Algebra.instEssFiniteTypeQuotientIdeal ℤ R (p k)
      refine @GlobalTheory.finite_integralClosure_of_essFiniteType_int (R ⧸ p k) _ _ ?_
      convert h
      first | exact Subsingleton.elim _ _ | exact Algebra.algebra_ext _ _ fun r => (eq_intCast _ r).trans (eq_intCast _ r).symm
  obtain ⟨a, ha, hr⟩ := exists_conductor p hmin
  have hzero : ∀ {x : R} (k), algebraMap R (integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k))) x = 0 →
      x ∈ p k := by
    intro x k hx
    have h1 : algebraMap R (FractionRing (R ⧸ p k)) x = 0 := congrArg Subtype.val hx
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p k) (FractionRing (R ⧸ p k)),
      Ideal.Quotient.algebraMap_eq] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1
      ((map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ p k) (FractionRing (R ⧸ p k)))).1 h1)
  refine ⟨Fintype.card (minimalPrimes R),
    fun k => integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k)), fun k => inferInstance,
    fun k => inferInstance, fun k => ⟨inferInstance,
      integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (R ⧸ p k)),
      Module.Finite.trans (R ⧸ p k) _⟩, ?_, a, ?_, hr⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hmem : x ∈ sInf (minimalPrimes R) := Submodule.mem_sInf.2 fun q hq => by
      have := hzero (e ⟨q, hq⟩) (congrFun hx (e ⟨q, hq⟩))
      simpa [p] using this
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    exact IsReduced.eq_zero x (mem_nilradical.mp hmem)
  · intro h0
    obtain ⟨q⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
    apply ha (e q)
    rw [h0]
    exact zero_mem _

end GlobalTheory.ReducedNormalisation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

example : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R], ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)), (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧ Function.Injective (algebraMap R (∀ i, D i)) ∧ ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R, algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r :=
  GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_finiteType_int_exists_finite_prod_normalDomains_nonzero_conductor : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R], ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)), (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧ Function.Injective (algebraMap R (∀ i, D i)) ∧ ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R, algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r := by
  atlas_forward_decl GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  first | exact @GlobalTheory.CechPic.Glue.exists_pic_glue | exact GlobalTheory.CechPic.Glue.exists_pic_glue | (intros; apply GlobalTheory.CechPic.Glue.exists_pic_glue <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd : ∀ {S : Scheme.{0}} (A : Over S) {B' B : Over S} (j : B' ⟶ B) [IsOpenImmersion j.left], IsOpenImmersion (A ◁ j).left ∧ Set.range (A ◁ j).left = (snd A B).left ⁻¹' Set.range j.left := by
  first | exact @GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range | exact GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range | (intros; apply GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem of_isPullback_opens_cover (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have e := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ e (h i), MorphismProperty.cancel_left_of_respectsIso Q]
  exact hq i

theorem isPullback_sigmaι_desc {X : Scheme.{0}} {κ : Type} (V : κ → X.Opens)
    (hd : Pairwise fun i i' => Disjoint (V i) (V i')) {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme)
    (i : κ) : IsPullback (Sigma.ι B i) (f i) (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι := by
  have : IsOpenImmersion (Sigma.ι B i) := inferInstance
  have hr : ∀ s : PullbackCone (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι,
      Set.range s.fst ⊆ Set.range (Sigma.ι B i) := by
    rintro s _ ⟨t, rfl⟩
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk B).surjective (s.fst t)
    rw [sigmaMk_mk] at hy
    have e1 : (Sigma.desc fun j => f j ≫ (V j).ι) (s.fst t) = (V i).ι (s.snd t) := congr($(s.condition) t)
    rw [← hy, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply] at e1
    by_cases hji : j = i
    · subst hji
      exact ⟨y, hy⟩
    · exfalso
      have h1 : (V j).ι (f j y) ∈ V j := ((V j).ι_apply _ ▸ ((f j y).2))
      have h2 : (V i).ι (s.snd t) ∈ V i := ((V i).ι_apply _ ▸ ((s.snd t).2))
      rw [e1] at h1
      have h3 := (hd hji).le_bot (show (V i).ι (s.snd t) ∈ V j ⊓ V i from ⟨h1, h2⟩)
      simp at h3
  refine ⟨⟨Sigma.ι_desc _ _⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => IsOpenImmersion.lift (Sigma.ι B i) s.fst (hr s)) ?_ ?_ ?_⟩⟩
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono (V i).ι, Category.assoc, ← Sigma.ι_desc (fun j => f j ≫ (V j).ι) i,
      IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s m h1 _
    rw [← cancel_mono (Sigma.ι B i), IsOpenImmersion.lift_fac, h1]

theorem good_sigmaDesc_of_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  intro X κ _ V hU hd B f g hf
  have sq := isPullback_sigmaι_desc V hd f
  have hc : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  have hs : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact
    { proper := of_isPullback_opens_cover @IsProper hU sq fun i => (hf i).proper
      smooth := of_isPullback_opens_cover (@SmoothOfRelativeDimension.{0} g) hU sq fun i => (hf i).smooth
      conn := of_isPullback_opens_cover @GeometricallyConnected hU sq fun i => (hf i).conn }

end GlobalTheory.DualCon
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properSmoothGeomConnected_sigmaDesc_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  atlas_forward_decl GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem finAff_sigma : ∀ {κ : Type} [Finite κ] (B : κ → Scheme.{0}), (∀ i, FinAff (B i)) → FinAff (∐ B) := by
  intro κ _ B hB F
  classical
  have hfin : ∀ i, {y : B i | Sigma.ι B i y ∈ F}.Finite := fun i =>
    (F.finite_toSet).preimage (Sigma.ι B i).isOpenEmbedding.injective.injOn
  choose V hV hFV using fun i => hB i (hfin i).toFinset
  refine ⟨⨆ i, Sigma.ι B i ''ᵁ V i, IsAffineOpen.iSup_of_disjoint
    (fun i => (hV i).image_of_isOpenImmersion _) fun i j hij => ?_, fun x hx => ?_⟩
  · exact (disjoint_opensRange_sigmaι B i j hij).mono (Scheme.Hom.image_le_opensRange _ _)
      (Scheme.Hom.image_le_opensRange _ _)
  · obtain ⟨i, y, rfl⟩ := (sigmaOpenCover B).exists_eq x
    have hy : y ∈ V i := hFV i y ((Set.Finite.mem_toFinset _).2 hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨y, hy, rfl⟩⟩

end GlobalTheory.DualCon
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteSetsInAffineOpen_finite_coproduct : ∀ {κ : Type} [Finite κ] (B : κ → Scheme.{0}), (∀ i, FinAff (B i)) → FinAff (∐ B) := by
  atlas_forward_decl GlobalTheory.DualCon.finAff_sigma
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hasRepAF_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  intro S A _ g Y Y' e h
  obtain ⟨B, b, P, hR, hG, hF⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, ?_⟩, ?_, hF⟩
  · intro T t N hN
    obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨?_, hx2⟩, fun y hy => hu y ⟨?_, hy.2⟩⟩
    · rw [← Category.assoc, hx1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [← hy.1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Over.comp_left]
    obtain ⟨hp, hs, hc⟩ := hG
    have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]⟩⟩
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine ⟨inferInstance, ?_, MorphismProperty.RespectsIso.postcomp (@GeometricallyConnected : MorphismProperty Scheme.{0}) e.hom.left b.left hc⟩
    have := smoothOfRelativeDimension_comp (n := g) (m := 0) b.left e.hom.left
    simpa using this

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  atlas_forward_decl GlobalTheory.hasRepAF_of_iso
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecPi

theorem specPi_cover : ∀ (R : Type) [CommRing R] (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], ∃ V : Fin n → (Sp (∀ i, D i)).Opens, (⨆ i, V i = ⊤) ∧ (Pairwise fun i i' => Disjoint (V i) (V i')) ∧ ∀ i, Nonempty (Over.mk ((V i).ι ≫ spMap (algebraMap R (∀ i, D i))) ≅ Over.mk (spMap (algebraMap R (D i)))) := by
  intro R _ n D _ _
  let S := sigmaSpec (fun i => CommRingCat.of (D i))
  have hS : ∀ i, Sigma.ι (fun i => Spec (CommRingCat.of (D i))) i ≫ S = spMap (Pi.evalRingHom D i) :=
    fun i => ι_sigmaSpec _ i
  have hinv : ∀ y, (inv S) (S y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hsurj : ∀ x, S ((inv S) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  refine ⟨fun i => (spMap (Pi.evalRingHom D i)).opensRange, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have hcov : ∀ y : ↥(∐ fun i => Spec (CommRingCat.of (D i))), ∃ k, ∃ z : Sp (D k),
        (Sigma.ι (fun i => Spec (CommRingCat.of (D i))) k) z = y :=
      fun y => ⟨_, (sigmaOpenCover (fun i => Spec (CommRingCat.of (D i)))).covers y⟩
    obtain ⟨k, z, hz⟩ := hcov ((inv S) x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨k, z, ?_⟩
    rw [← hS k, Scheme.Hom.comp_apply, hz, hsurj]
  · intro i j hij
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [← hS, Scheme.Hom.comp_apply] at ha hb
    have e := congrArg (inv S) (ha.trans hb.symm)
    rw [hinv, hinv] at e
    obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp e
    exact absurd rfl hij
  · intro i
    refine ⟨Over.isoMk (spMap (Pi.evalRingHom D i)).isoOpensRange.symm ?_⟩
    simp only [Over.mk_hom, Iso.symm_hom]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl

end GlobalTheory.SpecPi
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_pi_disjoint_open_cover_factors : ∀ (R : Type) [CommRing R] (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], ∃ V : Fin n → (Sp (∀ i, D i)).Opens, (⨆ i, V i = ⊤) ∧ (Pairwise fun i i' => Disjoint (V i) (V i')) ∧ ∀ i, Nonempty (Over.mk ((V i).ι ≫ spMap (algebraMap R (∀ i, D i))) ≅ Over.mk (spMap (algebraMap R (D i)))) := by
  atlas_forward_decl GlobalTheory.SpecPi.specPi_cover
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem fam_of_pieces {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left] (hcov : ⨆ i, (j i).left.opensRange = ⊤) (hdisj : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Fam A (P i)) (hPt : Pt.IsLB) (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) : Fam A Pt := by
  refine ⟨hPt, (GlobalTheory.AbDual.isAdditive_iff hPt).mpr ?_⟩
  intro Y a a' t

  have hcovY : ⨆ i, (pullback.fst t.left (j i).left).opensRange = ⊤ := by
    simp only [Scheme.Hom.opensRange_pullbackFst]
    rw [← Scheme.Hom.preimage_iSup, hcov]
    try simp
  have hdisjY : Pairwise fun i i' => Disjoint (pullback.fst t.left (j i).left).opensRange
      (pullback.fst t.left (j i').left).opensRange := by
    intro i i' hii
    have h : Disjoint (j i).left.opensRange (j i').left.opensRange := hdisj hii
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]
    rw [disjoint_iff] at h ⊢
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : t.left x ∈ (j i).left.opensRange ⊓ (j i').left.opensRange := ⟨hx.1, hx.2⟩
    rw [h] at hx'
    simp at hx'

  rw [← sub_eq_zero]
  refine GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i => pullback.fst t.left (j i).left) hcovY hdisjY _ (fun i => ?_)
  let Zi : Over S := Over.mk (pullback.fst t.left (j i).left ≫ Y.hom)
  let u : Zi ⟶ Y := Over.homMk (pullback.fst t.left (j i).left) rfl
  have hv : pullback.snd t.left (j i).left ≫ (B i).hom = Zi.hom := by
    show pullback.snd t.left (j i).left ≫ (B i).hom = pullback.fst t.left (j i).left ≫ Y.hom
    rw [← Over.w (j i), ← Over.w t, ← Category.assoc, ← Category.assoc, pullback.condition]
  let v : Zi ⟶ B i := Over.homMk (pullback.snd t.left (j i).left) hv
  have huv : u ≫ t = v ≫ j i := by
    ext
    simp [u, v, pullback.condition]
  change GlobalTheory.CechPic.pull u.left _ = 0
  rw [map_sub, map_add, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, huv,
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i),
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), MonObj.comp_mul,
    (GlobalTheory.AbDual.isAdditive_iff (hP i).isLB).mp (hP i).add]
  exact sub_self _

end GlobalTheory.DualCon.ProdGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveLineBundleFamily_of_disjoint_open_pieces : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Fam A (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → Fam A Pt := by
  atlas_forward_decl GlobalTheory.DualCon.ProdGlue.fam_of_pieces
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem opens_disjoint_of {Y : Scheme.{0}} {U U' : Y.Opens} (h : ∀ z, z ∈ U → z ∉ U') : Disjoint U U' :=
  disjoint_iff.2 (eq_bot_iff.2 fun z hz ↦ (h z hz.1 hz.2).elim)

theorem not_mem_of_disjoint {Y : Scheme.{0}} {U U' : Y.Opens} (h : Disjoint U U') {z : Y} (hz : z ∈ U)
    (hz' : z ∈ U') : False := by
  have := h.le_bot (show z ∈ U ⊓ U' from ⟨hz, hz'⟩)
  simpa using this

theorem rep_exists {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hV : ⨆ i, V i = ⊤) (hVd : Pairwise fun i i' => Disjoint (V i) (V i'))
    (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left]
    (hj : ⨆ i, (j i).left.opensRange = ⊤)
    (hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange)
    (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X) (hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι)
    (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Rep A (b i) (P i)) (hPt : Pt.IsLB)
    (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left)
    (hN : Fam A N) : ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  let W : κ → T.left.Opens := fun i ↦ t.left ⁻¹ᵁ V i
  let Ti : κ → Over S := fun i ↦ Over.mk ((W i).ι ≫ T.hom)
  let w : ∀ i, Ti i ⟶ T := fun i ↦ Over.homMk (W i).ι
  let ti : ∀ i, Ti i ⟶ Over.mk ((V i).ι ≫ X.hom) := fun i ↦ Over.homMk (t.left ∣_ V i) (by
    simp [Ti, W, morphismRestrict_ι_assoc])
  have hti : ∀ i, ti i ≫ Over.homMk (V i).ι = w i ≫ t := fun i ↦ by
    ext1; simp [ti, w, W, morphismRestrict_ι]
  have hNi : ∀ i, Fam A (ev N (fst A (Ti i)) (snd A (Ti i) ≫ w i)) := fun i ↦ Model.fam_ev hN (w i)
  choose x hx _ using fun i ↦ (hP i).univ (Ti i) (ti i) _ (hNi i)
  have hWc : ⨆ i, (W i).ι.opensRange = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left z ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by simpa [W] using hi⟩
  have hWd : _root_.Pairwise fun i i' ↦ Disjoint (W i).ι.opensRange (W i').ι.opensRange := by
    intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    simp only [Scheme.Opens.opensRange_ι, W] at hz hz'
    exact not_mem_of_disjoint (hVd h) hz hz'
  obtain ⟨hT⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (W i).ι) hWc hWd
  let xl : T.left ⟶ Bt.left := Cofan.IsColimit.desc hT fun i ↦ (x i).left ≫ (j i).left
  have hxl : ∀ i, (W i).ι ≫ xl = (x i).left ≫ (j i).left := fun i ↦ Cofan.IsColimit.fac hT _ i
  have hxo : xl ≫ Bt.hom = T.hom := Cofan.IsColimit.hom_ext hT _ _ fun i ↦ by
    change (W i).ι ≫ _ = (W i).ι ≫ _
    rw [reassoc_of% hxl i, Over.w (j i), Over.w (x i)]
    rfl
  let xx : T ⟶ Bt := Over.homMk xl hxo
  have wxx : ∀ i, w i ≫ xx = x i ≫ j i := fun i ↦ by
    ext1
    simp only [Over.comp_left, Over.homMk_left, w, xx]
    exact hxl i
  have hxt : xx ≫ bt = t := by
    ext1
    refine Cofan.IsColimit.hom_ext hT _ _ fun i ↦ ?_
    change (W i).ι ≫ _ = (W i).ι ≫ _
    have e : w i ≫ xx ≫ bt = w i ≫ t := by
      rw [reassoc_of% wxx i, hb i, reassoc_of% (hx i).1, hti i]
    simpa [w, xx] using congrArg (fun q ↦ q.left) e
  refine ⟨xx, hxt, ?_⟩
  have hNl := hN.isLB
  refine (same_id_iff hNl hPt xx).1 ((same_iff hNl hPt _ _).2 ?_)
  have hwo : ∀ i, IsOpenImmersion (w i).left := fun i ↦ by
    show IsOpenImmersion (W i).ι; infer_instance
  have hwa : ∀ i, IsOpenImmersion (A ◁ w i).left := fun i ↦
    (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).1
  have hwr : ∀ i z, z ∈ (A ◁ w i).left.opensRange ↔ (snd A T).left z ∈ W i := fun i z ↦ by
    have := (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).2
    change z ∈ Set.range (A ◁ w i).left ↔ _
    rw [this, Set.mem_preimage]
    change _ ∈ Set.range (W i).ι ↔ _
    rw [Scheme.Opens.range_ι]
    rfl
  rw [← sub_eq_zero]
  refine GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i ↦ (A ◁ w i).left) ?_ ?_ _ fun i ↦ ?_
  · refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left ((snd A T).left z) ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hwr i z).2 hi⟩
  · intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    exact not_mem_of_disjoint (hVd h) ((hwr i z).1 hz) ((hwr i' z).1 hz')
  · rw [map_sub, pull_evc, pull_evc, sub_eq_zero]
    simp only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd, Category.comp_id]
    rw [wxx i, ← Category.assoc, evc_comp_of_iso (j i) hPt (hP i).fam.isLB (hiso i)]
    exact (cls_eq_iff (hNi i).isLB (pull_isLB (hP i).fam.isLB _)).2 (hx i).2

end GlobalTheory.DualCon.ProdGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_disjointUnion_representingAdditiveFamily : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left), Fam A N → ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  atlas_forward_decl GlobalTheory.DualCon.ProdGlue.rep_exists
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem same_precomp {S : Scheme.{0}} {A T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : N.IsLB) (hM : M.IsLB) {y : Y ⟶ T} {u : Y ⟶ U} (z : Z ⟶ Y)
    (e : Same A N M y u) : Same A N M (z ≫ y) (z ≫ u) := by
  have e' := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM _ _).1 e)
  rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc, Category.assoc, Category.assoc] at e'
  exact (same_iff hN hM _ _).2 e'

theorem eq_of_same_of_disjoint_cover : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  intro S A _ κ _ X V hV hVd Bt B j _ hj hjd b bt hb P Pt hP hPt hPi T x y hxy e

  have mem : ∀ i (p : Bt.left), bt.left p ∈ V i → p ∈ Set.range (j i).left := by
    intro i p hp
    have hp' : p ∈ (⨆ i', (j i').left.opensRange) := by rw [hj]; trivial
    obtain ⟨i', q, rfl⟩ := (TopologicalSpace.Opens.mem_iSup.1 hp')
    have h1 : bt.left ((j i').left q) ∈ V i' := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb i', Over.comp_left, Scheme.Hom.comp_apply]
      change (V i').ι ((b i').left q) ∈ V i'
      exact (Scheme.Opens.range_ι (V i')).subset ⟨_, rfl⟩
    by_cases hii : i' = i
    · subst hii; exact ⟨q, rfl⟩
    · exact absurd (⟨h1, hp⟩ : bt.left ((j i').left q) ∈ (V i' ⊓ V i : X.left.Opens))
        (fun h ↦ (hVd hii).le_bot h)
  have loc : ∀ i, ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ x.left = ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ y.left := by
    intro i
    let Ti : Over S := Over.mk (((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ T.hom)
    let w : Ti ⟶ T := Over.homMk ((x ≫ bt).left ⁻¹ᵁ V i).ι rfl
    have lf : ∀ z : T ⟶ Bt, z ≫ bt = x ≫ bt → ∃ zi : Ti ⟶ B i, zi ≫ j i = w ≫ z := by
      intro z hz
      have r : Set.range (w ≫ z).left ⊆ Set.range (j i).left := by
        rintro _ ⟨p, rfl⟩
        apply mem i
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, hz, Over.comp_left,
          Scheme.Hom.comp_apply]
        exact (Scheme.Opens.range_ι ((x ≫ bt).left ⁻¹ᵁ V i)).subset ⟨p, rfl⟩
      exact ⟨Over.homMk (IsOpenImmersion.lift (j i).left _ r)
        (by rw [← Over.w (j i), IsOpenImmersion.lift_fac_assoc, Over.w]),
        Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    obtain ⟨xi, hx⟩ := lf x rfl
    obtain ⟨yi, hy⟩ := lf y hxy.symm
    have hQ := (hP i).fam.isLB
    have hb' : xi ≫ b i = yi ≫ b i := by
      have k : xi ≫ b i ≫ Over.homMk (V i).ι = yi ≫ b i ≫ Over.homMk (V i).ι := by
        rw [← hb, reassoc_of% hx, reassoc_of% hy, hxy]
      apply Over.OverMorphism.ext
      rw [← cancel_mono (V i).ι]
      exact congrArg (fun q ↦ q.left) k
    have hs : Same A (P i) (P i) xi yi := by
      have e2 := (same_iff hPt hPt _ _).1 (same_precomp hPt hPt w e)
      rw [same_iff hQ hQ, ← evc_comp_of_iso (j i) hPt hQ (hPi i), ← evc_comp_of_iso (j i) hPt hQ (hPi i),
        Category.assoc, Category.assoc, hx, hy]
      exact e2
    have h3 := Model.rep_ext (hP i) hb' hs
    exact congrArg (fun q ↦ q.left) (show w ≫ x = w ≫ y by rw [← hx, ← hy, h3])
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun z ↦ ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show (x ≫ bt).left z ∈ ⨆ i, V i by rw [hV]; trivial)
  exact ⟨_, hi, loc i⟩

end GlobalTheory.DualCon.ProdGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_disjointUnion_representingFamily_unique : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  atlas_forward_decl GlobalTheory.DualCon.ProdGlue.eq_of_same_of_disjoint_cover
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem hasRepAF_of_disjoint_cover {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hcov : ⨆ i, V i = ⊤) (hdisj : Pairwise fun i i' => Disjoint (V i) (V i'))
    (h : ∀ i, HasRepAF A g (Over.mk ((V i).ι ≫ X.hom))) : HasRepAF A g X := by
  choose B b P hP using h
  let Bt : Over S := Over.mk (Sigma.desc fun i => (B i).hom)
  let j : ∀ i, B i ⟶ Bt := fun i => Over.homMk (Sigma.ι (fun i => (B i).left) i) (by simp [Bt])
  have hjl : ∀ i, (j i).left = Sigma.ι (fun i => (B i).left) i := fun i => rfl
  haveI : ∀ i, IsOpenImmersion (j i).left := fun i => by rw [hjl]; infer_instance
  have hjc : ⨆ i, (j i).left.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk fun i => (B i).left).surjective x
    rw [sigmaMk_mk]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, by rw [hjl]⟩
  have hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange := fun i i' hii' => by
    simp only [hjl]; exact disjoint_opensRange_sigmaι _ i i' hii'
  let bt : Bt ⟶ X := Over.homMk (Sigma.desc fun i => (b i).left ≫ (V i).ι) (by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [Bt, Over.mk_hom, colimit.ι_desc_assoc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as, colimit.ι_desc, Category.assoc]
    exact Over.w (b i))
  have hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι := fun i => by
    ext1; simp [j, bt]

  have hk : ∀ i, IsOpenImmersion (A ◁ j i).left := fun i => (GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).1
  have hkc : ⨆ i, (A ◁ j i).left.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : (snd A Bt).left z ∈ ⨆ i, (j i).left.opensRange := by rw [hjc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    change z ∈ Set.range (A ◁ j i).left
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).2]
    exact hi
  have hkd : Pairwise fun i i' => Disjoint (A ◁ j i).left.opensRange (A ◁ j i').left.opensRange := by
    intro i i' hii'
    rw [disjoint_iff, eq_bot_iff]
    rintro z ⟨h1, h2⟩
    change z ∈ Set.range (A ◁ j i).left at h1
    change z ∈ Set.range (A ◁ j i').left at h2
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).2] at h1
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i')).2] at h2
    exact (disjoint_iff.1 (hjd hii')).le ⟨h1, h2⟩
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover (fun i => (A ◁ j i).left) hkc hkd (fun i => cls (P i) (hP i).1.fam.isLB)
  obtain ⟨Pt, hPt, rfl⟩ := cls_surj d
  have hPi : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i) := fun i =>
    (cls_eq_iff (pull_isLB hPt _) (hP i).1.fam.isLB).1 ((cls_pull hPt _ _).trans (hd i))
  refine ⟨Bt, bt, Pt, ⟨GlobalTheory.T.additiveLineBundleFamily_of_disjoint_open_pieces A Bt B j hjc hjd P Pt (fun i => (hP i).1.fam) hPt hPi, fun T t N hN => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx, hxN⟩ := GlobalTheory.T.exists_point_disjointUnion_representingAdditiveFamily A X V hcov hdisj Bt B j hjc hjd b bt hb P Pt (fun i => (hP i).1) hPt hPi T t N hN
    refine ⟨x, ⟨hx, hxN⟩, fun y hy => ?_⟩
    refine GlobalTheory.T.point_disjointUnion_representingFamily_unique A X V hcov hdisj Bt B j hjc hjd b bt hb P Pt (fun i => (hP i).1) hPt hPi T y x (hy.1.trans hx.symm) ?_
    rw [Same, ← cls_eq_iff (pull_isLB hPt _) (pull_isLB hPt _), ← (cls_eq_iff hN.isLB (pull_isLB hPt _)).2 hy.2,
      ← (cls_eq_iff hN.isLB (pull_isLB hPt _)).2 hxN]
  · exact GlobalTheory.T.properSmoothGeomConnected_sigmaDesc_disjoint_cover V hcov hdisj (fun i => (b i).left) g (fun i => (hP i).2.1)
  · exact GlobalTheory.T.finiteSetsInAffineOpen_finite_coproduct (fun i => (B i).left) (fun i => (hP i).2.2)

theorem hasRepAF_pi : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  intro R _ A _ g _ n D _ _ h
  obtain ⟨V, hcov, hdisj, he⟩ := GlobalTheory.T.spec_pi_disjoint_open_cover_factors R n D
  exact hasRepAF_of_disjoint_cover A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) V hcov hdisj
    (fun i => GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_iso A g (he i).some.symm (h i))

end GlobalTheory.DualCon.ProdGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  atlas_forward_decl GlobalTheory.DualCon.ProdGlue.hasRepAF_pi
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A f φ → ∀ (g : ℕ) (T : Over S'), (HasRep A' g T ↔ HasRep A g (Over.mk (T.hom ≫ f))) ∧ (HasRepAF A' g T ↔ HasRepAF A g (Over.mk (T.hom ≫ f))) := by
  first | exact @GlobalTheory.DualCon.hasRep_baseChange_iff | exact GlobalTheory.DualCon.hasRep_baseChange_iff | (intros; apply GlobalTheory.DualCon.hasRep_baseChange_iff <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualConStep

def conductor (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] : Ideal R where
  carrier := {x | ∀ r : R', ∃ y : R, algebraMap R R' y = algebraMap R R' x * r}
  add_mem' {x x'} hx hx' r := by
    obtain ⟨y, hy⟩ := hx r
    obtain ⟨y', hy'⟩ := hx' r
    exact ⟨y + y', by rw [map_add, map_add, hy, hy', add_mul]⟩
  zero_mem' r := ⟨0, by simp⟩
  smul_mem' b {x} hx r := by
    obtain ⟨y, hy⟩ := hx r
    exact ⟨b * y, by rw [smul_eq_mul, map_mul, map_mul, hy, _root_.mul_assoc]⟩

theorem conductor_mul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] :
    ∀ x ∈ conductor R R', ∀ r : R', ∃ y ∈ conductor R R', algebraMap R R' y = algebraMap R R' x * r := by
  intro x hx r
  obtain ⟨y, hy⟩ := hx r
  refine ⟨y, fun r' ↦ ?_, hy⟩
  obtain ⟨z, hz⟩ := hx (r * r')
  exact ⟨z, by rw [hz, hy, _root_.mul_assoc]⟩

theorem hasRepAF_factor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (V : A.left.Opens) (hV : IsAffineOpen V)
    (hVs : ∀ s : Sp R, ∃ x ∈ V, A.hom x = s) (D : Type) [CommRing D] [Algebra R D] [IsNoetherianRing D]
    [IsDomain D] [IsIntegrallyClosed D] :
    HasRepAF A g (Over.mk (spMap (algebraMap R D))) := by
  set f := algebraMap R D
  have hP := isGrpPullback_pullback A (spMap f)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A
    ((Over.pullback (spMap f)).obj A) _ g hP hA hg
  haveI : IsAffineHom (pullback.fst A.hom (spMap f)) :=
    (AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.{0}).of_isPullback (IsPullback.of_hasPullback _ _).flip
      (inferInstance : IsAffineHom (spMap f))
  have hV' : IsAffineOpen (pullback.fst A.hom (spMap f) ⁻¹ᵁ V) := hV.preimage _
  have hVs' : ∀ s : Sp D, ∃ x ∈ pullback.fst A.hom (spMap f) ⁻¹ᵁ V,
      ((Over.pullback (spMap f)).obj A).hom x = s := by
    intro s
    obtain ⟨x, hx, hxs⟩ := hVs (spMap f s)
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x s hxs
    exact ⟨z, by simpa [hz1] using hx, hz2⟩
  obtain ⟨L, hL, hLa⟩ := GlobalTheory.T.exists_relAmple_of_affineOpen_meets_fibres D _ hA' _ hV' hVs'
  have h1 := GlobalTheory.T.hasDualRepresentative_of_relAmple_noetherian D _ g hA' hg' L hL hLa
  have h2 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap f) A _ _ hP g (𝟙_ _)).2).1 h1
  simpa using h2

theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ _ A _ g hA hg V hV hVs hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : IsEmpty (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    obtain ⟨B, b, P, hP, hG, -⟩ := GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_isEmpty _ A (𝟙_ _) g this
    exact ⟨B, b, P, hP, hG⟩
  obtain ⟨n, D, iR, iA, hD, hinj, a, ha0, ha⟩ := GlobalTheory.T.reduced_finiteType_int_exists_finite_prod_normalDomains_nonzero_conductor R
  have hfac : ∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i)))) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hD i
    haveI : IsNoetherianRing (D i) := by
      haveI : Algebra.FiniteType R (D i) := inferInstance
      exact Algebra.FiniteType.isNoetherianRing R (D i)
    exact hasRepAF_factor R A g hA hg V hV hVs (D i)
  haveI : ∀ i, Module.Finite R (D i) := fun i ↦ (hD i).2.2
  have hprod := GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras R A g hA n D hfac
  have hac : a ∈ conductor R (∀ i, D i) := ha
  have hc : conductor R (∀ i, D i) ≠ ⊥ := fun h ↦ ha0 (by rw [h] at hac; exact (Submodule.mem_bot R).1 hac)
  exact GlobalTheory.T.hasRepresentingScheme_pinchedBase R A g hA hg (∀ i, D i) hinj _ conductor_mul hprod (hJ _ hc)

end GlobalTheory.DualConStep
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_noetherianInduction : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  atlas_forward_decl GlobalTheory.DualConStep.step
end
