import Mathlib
import ReciprocityTheory.GroupCohomology.FiveTerm
import ReciprocityTheory.GroupCohomology.CupCor
import ReciprocityTheory.GroupCohomology.FiberFirstH0Injective
import ReciprocityTheory.GroupCohomology.ProdHolds
import ReciprocityTheory.GroupCohomology.EqZeroOfLe
import ReciprocityTheory.GroupCohomology.LowLES
import ReciprocityTheory.GroupCohomology.TransgressionStatement
import ReciprocityTheory.GroupCohomology.FinGen
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.ResNormalHolds
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.FiniteLevel
import ReciprocityTheory.GroupCohomology.Shapiro
import ReciprocityTheory.GroupCohomology.Section
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.LengthKerEqCoker
import ReciprocityTheory.GroupCohomology.IsLowExists

section
namespace ReciprocityTheory.Coh.RevCh

open Finsupp

noncomputable section

abbrev Ch (m : ℕ) (S : Type*) := (Fin (m + 1) → S) →₀ ℤ

variable {S T U : Type*}

def bd (m : ℕ) : Ch (m + 1) S →ₗ[ℤ] Ch m S :=
  linearCombination ℤ fun t => ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • single (t ∘ i.succAbove) (1 : ℤ)

def mp (f : S → T) (m : ℕ) : Ch m S →ₗ[ℤ] Ch m T := lmapDomain ℤ ℤ fun t => f ∘ t

def eps (m : ℕ) : ℤ := (-1) ^ (m * (m + 1) / 2)

def rv (m : ℕ) : Ch m S →ₗ[ℤ] Ch m S := eps m • lmapDomain ℤ ℤ fun t : Fin (m + 1) → S => t ∘ Fin.rev

def cone (v : S) (m : ℕ) : Ch m S →ₗ[ℤ] Ch (m + 1) S :=
  lmapDomain ℤ ℤ fun t : Fin (m + 1) → S => (Fin.cons v t : Fin (m + 2) → S)

def HHof (k : ℕ) (w : Ch (k + 1) (Fin (k + 1))) : Ch k S →ₗ[ℤ] Ch (k + 1) S :=
  linearCombination ℤ fun t => mp t (k + 1) w

def uu : (k : ℕ) → Ch (k + 1) (Fin (k + 1))
  | 0 => 0
  | k + 1 => cone (0 : Fin (k + 2)) (k + 1)
      (rv (k + 1) (single (id : Fin (k + 2) → Fin (k + 2)) 1) - single id 1 -
        HHof k (uu k) (bd k (single (id : Fin (k + 2) → Fin (k + 2)) 1)))

abbrev HH (k : ℕ) : Ch k S →ₗ[ℤ] Ch (k + 1) S := HHof k (uu k)

def Q (k : ℕ) : Prop :=
  bd (k + 1) (uu (k + 1)) + HH k (bd k (single (id : Fin (k + 2) → Fin (k + 2)) 1)) =
    rv (k + 1) (single (id : Fin (k + 2) → Fin (k + 2)) 1) - single id 1

end

end ReciprocityTheory.Coh.RevCh
end

section
namespace ReciprocityTheory.Coh.SelH

open ReciprocityTheory.Coh Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R]

def piHom {ι : Type u} {A B : ι → Cx R} (f : ∀ v, Hom (A v) (B v)) : Hom (pi A) (pi B) where
  f n := LinearMap.pi fun v => ((f v).f n).comp (LinearMap.proj v)
  comm n x := funext fun v => (f v).comm n (x v)

def negHom {A B : Cx R} (φ : Hom A B) : Hom A B where
  f n := -(φ.f n)
  comm n x := by simp [φ.comm]

def inr (A B : Cx R) : Hom B (prod A B) where
  f _ := LinearMap.inr R _ _
  comm n _ := Prod.ext (map_zero (A.d n)).symm rfl

end

end ReciprocityTheory.Coh.SelH
end

section
namespace ReciprocityTheory.Coh.EulerCharacteristicRank

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

open Function Module

def FG (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : Prop :=
  (∀ n, Module.Finite R (a n)) ∧ ∀ n, N < n → Subsingleton (a n)

noncomputable def cr (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (finrank R (a n) : ℤ)

section LES

variable {a b c : ℕ → Type u} [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)]
  [∀ n, AddCommGroup (b n)] [∀ n, Module R (b n)] [∀ n, AddCommGroup (c n)] [∀ n, Module R (c n)]
  (f : ∀ n, a n →ₗ[R] b n) (g : ∀ n, b n →ₗ[R] c n) (δ : ∀ n, c n →ₗ[R] a (n + 1))

end LES

end ReciprocityTheory.Coh.EulerCharacteristicRank
end

section
namespace ReciprocityTheory.Coh.TorsionRankLength

universe u

open Module Submodule Function
open scoped Pointwise TensorProduct

section General

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

abbrev K (M : Type u) [AddCommGroup M] [Module R M] (r : R) : Submodule R M :=
  LinearMap.ker (r • LinearMap.id : M →ₗ[R] M)

theorem mem_K {r : R} {x : M} : x ∈ K M r ↔ r • x = 0 := by
  simp [K]

theorem smul_top_eq_range (r : R) :
    (r • ⊤ : Submodule R M) = LinearMap.range (r • LinearMap.id : M →ₗ[R] M) := by
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range]
  simp

theorem len_sub_add_quot (N : Submodule R M) :
    Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)

theorem len_K_eq_len_quot (hM : IsFiniteLength R M) (r : R) :
    Module.length R (K M r) = Module.length R (QuotSMulTop r M) := by
  set φ : M →ₗ[R] M := r • LinearMap.id with hφ
  have h1 : Module.length R M = Module.length R (K M r) + Module.length R (LinearMap.range φ) :=
    Module.length_eq_add_of_exact (K M r).subtype φ.rangeRestrict (Submodule.injective_subtype _)
      φ.surjective_rangeRestrict
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length R M = Module.length R (r • ⊤ : Submodule R M) + Module.length R (QuotSMulTop r M) :=
    len_sub_add_quot (r • ⊤ : Submodule R M)
  have h3 : Module.length R (r • ⊤ : Submodule R M) = Module.length R (LinearMap.range φ) :=
    (LinearEquiv.ofEq _ _ (smul_top_eq_range r)).length_eq
  have hMt : Module.length R M ≠ ⊤ := Module.length_ne_top_iff.2 hM
  have hL : Module.length R (LinearMap.range φ) ≠ ⊤ := fun h => hMt (by rw [h1, h, add_top])
  rw [h3] at h2
  rw [h1, add_comm (Module.length R (LinearMap.range φ))] at h2
  exact WithTop.add_right_cancel hL h2

end General

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem len_quot_pow {t : R} (ht : Irreducible t) (k : ℕ) :
    Module.length R (R ⧸ Ideal.span {t ^ k}) = k := by
  have hmax : (Ideal.span {t} : Ideal R).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible ht
  have h1 : Module.length R (R ⧸ Ideal.span {t}) = 1 := by
    rw [Module.length_eq_one_iff]
    exact isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 hmax)
  have ht0 : t ≠ 0 := ht.ne_zero
  induction k with
  | zero =>
    haveI : Subsingleton (R ⧸ Ideal.span {t ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.span_singleton_one])
    rw [Nat.cast_zero]
    exact Module.length_eq_zero_iff.2 this
  | succ k ih =>
    have hle : Ideal.span {t} ≤ Submodule.comap (LinearMap.mulLeft R (t ^ k)) (Ideal.span {t ^ (k + 1)}) := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      rw [Ideal.mem_span_singleton']
      exact ⟨y, by ring⟩
    let f := Submodule.mapQ (Ideal.span {t}) (Ideal.span {t ^ (k + 1)}) (LinearMap.mulLeft R (t ^ k)) hle
    have hfac : Ideal.span {t ^ (k + 1)} ≤ Ideal.span {t ^ k} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨t, by ring⟩
    let g := (Ideal.Quotient.factorₐ R hfac).toLinearMap
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker] at hx
      simp only [f, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
      rw [Ideal.mem_span_singleton']
      refine ⟨y, ?_⟩
      have : t ^ k * (y * t) = t ^ k * x := by rw [← hy]; ring
      exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ z, rfl⟩
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      constructor
      · intro hz
        have hz' : z ∈ Ideal.span {t ^ k} := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          exact hz
        obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz'
        exact ⟨Submodule.Quotient.mk w, by
          simp only [f, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
          congr 1
          ring⟩
      · rintro ⟨x, hx⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [← hx]
        simp only [f, g, Submodule.mapQ_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
        show Ideal.Quotient.factor hfac (Ideal.Quotient.mk _ (t ^ k * x)) = 0
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
        exact ⟨x, by ring⟩
    rw [Module.length_eq_add_of_exact f g hf hg hex, h1, ih]
    push_cast
    ring

variable (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H]

theorem torsion_finLen : IsFiniteLength R (torsion R H) := by
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (R := R) (M := torsion R H) (torsion_isTorsion)
  rw [← Module.length_ne_top_iff, f.length_eq,
    (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ R ∙ p i ^ e i)).length_eq,
    Module.length_pi_of_fintype]
  have : ∀ i, Module.length R (R ⧸ R ∙ p i ^ e i) = e i := fun i => len_quot_pow (hp i) (e i)
  simp only [this]
  exact (ENat.sum_lt_top.mpr fun i _ => ENat.natCast_lt_top _).ne

theorem finrank_torsion_eq_zero : Module.finrank R (torsion R H) = 0 := by
  rw [Module.finrank_eq_zero_iff]
  intro x
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x : H)).1 x.2
  exact ⟨a, nonZeroDivisors.ne_zero a.2, Subtype.ext ha⟩

theorem len_quot_split (r : R) :
    Module.length R (QuotSMulTop r H) = Module.length R (QuotSMulTop r (torsion R H)) +
      Module.finrank R H * Module.length R (R ⧸ Ideal.span {r}) := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := H ⧸ torsion R H)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (torsion R H).mkQ LinearMap.id
    (torsion R H).mkQ_surjective
  have e : (torsion R H × (H ⧸ torsion R H)) ≃ₗ[R] H :=
    lequivProdOfRightSplitExact (torsion R H).injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf
  have hrank : Module.finrank R H = n := by
    have h := Submodule.finrank_quotient_add_finrank (torsion R H)
    rw [finrank_torsion_eq_zero, add_zero, Module.finrank_eq_card_basis b, Fintype.card_fin] at h
    exact h.symm
  have e2 : QuotSMulTop r H ≃ₗ[R]
      ((R ⧸ Ideal.span {r}) ⊗[R] torsion R H) × ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) :=
    (QuotSMulTop.congr r e.symm).trans ((QuotSMulTop.equivQuotTensor r _).trans
      (TensorProduct.prodRight R R _ _ _))
  have e3 : ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) ≃ₗ[R] (Fin n →₀ (R ⧸ Ideal.span {r})) :=
    (LinearEquiv.lTensor _ b.repr).trans (TensorProduct.finsuppScalarRight R R _ _)
  rw [e2.length_eq, Module.length_prod, ← (QuotSMulTop.equivQuotTensor r _).length_eq,
    e3.length_eq, Module.length_finsupp, hrank]
  simp

theorem len_K_torsion {r : R} (hr : r ≠ 0) :
    Module.length R (K H r) = Module.length R (K (torsion R H) r) := by
  have hmem : ∀ y : H, r • y = 0 → y ∈ torsion R H := fun y hy =>
    (Submodule.mem_torsion_iff y).2 ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, hy⟩
  let f : K (torsion R H) r →ₗ[R] K H r :=
    { toFun := fun x => ⟨((x : torsion R H) : H), by
        have h1 := mem_K.1 x.2
        rw [mem_K]
        simpa using congrArg Subtype.val h1⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : K H r => (z : H)) hxy
    · intro y
      refine ⟨⟨⟨y, hmem y (mem_K.1 y.2)⟩, ?_⟩, rfl⟩
      rw [mem_K]
      apply Subtype.ext
      exact mem_K.1 y.2
  exact ((LinearEquiv.ofBijective f hf).length_eq).symm

end DVR

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem len_quot_eq (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H] {t : R}
    (ht : Irreducible t) (m : ℕ) :
    Module.length R (QuotSMulTop (t ^ m) H) =
        ((m * Module.finrank R H : ℕ) : ℕ∞) + Module.length R (K H (t ^ m)) ∧
      Module.length R (K H (t ^ m)) ≤ Module.length R (torsion R H) ∧
      Module.length R (torsion R H) ≠ ⊤ := by
  have htm : t ^ m ≠ 0 := pow_ne_zero _ ht.ne_zero
  have hT := torsion_finLen (R := R) H
  have hK := len_K_torsion (R := R) H htm
  have hQ := len_K_eq_len_quot hT (t ^ m)
  have hS := len_quot_split (R := R) H (t ^ m)
  have hP := len_quot_pow ht m
  refine ⟨?_, ?_, Module.length_ne_top_iff.2 hT⟩
  · rw [hS, ← hQ, ← hK, hP]
    push_cast
    ring
  · rw [hK]
    have h := len_sub_add_quot (K (torsion R H) (t ^ m))
    rw [h]
    exact le_self_add

end Main

end ReciprocityTheory.Coh.TorsionRankLength
end

section
namespace ReciprocityTheory.Coh

open Cx Function TorsionRankLength
open scoped Pointwise

universe u

theorem alt_sum_telescope (a : ℕ → ℤ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (a n + a (n + 1)) = a 0 + (-1) ^ N * a (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem rankLen_holds : RankLenStatement.{u} := by
  intro R _ _ _ t ht L C i p m N hi hses hfg
  obtain ⟨⟨δ, hconn, hles⟩, -⟩ := lES_holds R L L C i p hses
  have hiH : ∀ n, i.H n = (t ^ m) • (LinearMap.id : L.H n →ₗ[R] L.H n) := by
    intro n
    refine LinearMap.ext fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [Cx.Hom.H, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact hi n z.1
  have hrange : ∀ n, LinearMap.range (i.H n) = (t ^ m) • (⊤ : Submodule R (L.H n)) := by
    intro n
    ext x
    rw [hiH, LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hlen : ∀ n, Module.length R (C.H n) =
      Module.length R (QuotSMulTop (t ^ m) (L.H n)) + Module.length R (K (L.H (n + 1)) (t ^ m)) := by
    intro n
    have hexs : Function.Exact (LinearMap.ker (δ n)).subtype (δ n).rangeRestrict := by
      intro y
      constructor
      · intro hy
        refine ⟨⟨y, ?_⟩, rfl⟩
        rw [LinearMap.mem_ker]
        have := congrArg Subtype.val hy
        simpa using this
      · rintro ⟨z, rfl⟩
        apply Subtype.ext
        simpa using z.2
    rw [Module.length_eq_add_of_exact _ _ (LinearMap.ker (δ n)).injective_subtype
      (LinearMap.surjective_rangeRestrict _) hexs]
    congr 1
    · rw [LinearMap.exact_iff.1 (hles.exC n), ← (LinearMap.quotKerEquivRange (p.H n)).length_eq,
        LinearMap.exact_iff.1 (hles.exB n), hrange]
      try rfl
    · rw [← LinearMap.exact_iff.1 (hles.exA n), hiH]
  have hfin : ∀ n, Module.Finite R (L.H n) := hfg.1
  have hq := fun n => @len_quot_eq R _ _ _ (L.H n) _ _ (hfin n) t ht m
  have hKfin : ∀ n, Module.length R (K (L.H n) (t ^ m)) ≠ ⊤ :=
    fun n => ne_top_of_le_ne_top (hq n).2.2 (hq n).2.1
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ → ℕ, kk = fun n => (Module.length R (K (L.H n) (t ^ m))).toNat := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ rr : ℕ → ℕ, rr = fun n => Module.finrank R (L.H n) := ⟨_, rfl⟩
  have hKn : ∀ n, Module.length R (K (L.H n) (t ^ m)) = (kk n : ℕ∞) := by
    intro n; rw [hkk]; exact (ENat.coe_toNat (hKfin n)).symm
  have hCn : ∀ n, Module.length R (C.H n) = ((m * rr n + kk n + kk (n + 1) : ℕ) : ℕ∞) := by
    intro n
    rw [hlen, (hq n).1, hKn, hKn, hrr]
    push_cast
    ring
  have hCnat : ∀ n, (Module.length R (C.H n)).toNat = m * rr n + kk n + kk (n + 1) := by
    intro n; rw [hCn, ENat.toNat_coe]
  have hzero : ∀ n, N < n → kk n = 0 ∧ rr n = 0 := by
    intro n hn
    haveI := hfg.2 n hn
    refine ⟨?_, ?_⟩
    · have h0 : Module.length R (K (L.H n) (t ^ m)) = 0 := Module.length_eq_zero_iff.2 inferInstance
      rw [hKn] at h0
      exact_mod_cast h0
    · rw [hrr]; exact Module.finrank_zero_of_subsingleton
  have hk0 : kk 0 = 0 := by
    have hker : K (L.H 0) (t ^ m) = ⊥ := by
      show LinearMap.ker ((t ^ m) • (LinearMap.id : L.H 0 →ₗ[R] L.H 0)) = ⊥
      rw [← hiH]
      exact LinearMap.ker_eq_bot.2 hles.inj
    have h0 : Module.length R (K (L.H 0) (t ^ m)) = 0 := by
      rw [hker]; exact Module.length_eq_zero_iff.2 inferInstance
    rw [hKn] at h0
    exact_mod_cast h0
  refine ⟨⟨fun n => Module.length_ne_top_iff.1 (by rw [hCn]; exact ENat.coe_ne_top _), fun n hn => ?_⟩,
    ?_, fun n => ⟨?_, ?_⟩⟩
  · apply (Module.length_eq_zero_iff (R := R)).1
    rw [hCn, (hzero n hn).1, (hzero n hn).2, (hzero (n + 1) (by omega)).1]
    simp
  · unfold Cx.chi Cx.chiRk
    simp_rw [hCnat]
    have hterm : ∀ n, (-1 : ℤ) ^ n * ((m * rr n + kk n + kk (n + 1) : ℕ) : ℤ) =
        (m : ℤ) * ((-1) ^ n * (Module.finrank R (L.H n) : ℤ)) + (-1) ^ n * ((kk n : ℤ) + kk (n + 1)) := by
      intro n; rw [hrr]; push_cast; ring
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_add_distrib, ← Finset.mul_sum,
      alt_sum_telescope (fun n => (kk n : ℤ)) N, hk0, (hzero (N + 1) (by omega)).1]
    simp
  · rw [hCnat]
    have h1 : kk n ≤ (Module.length R (Submodule.torsion R (L.H n))).toNat := by
      rw [hkk]; exact ENat.toNat_le_toNat (hq n).2.1 (hq n).2.2
    have h2 : kk (n + 1) ≤ (Module.length R (Submodule.torsion R (L.H (n + 1)))).toNat := by
      rw [hkk]; exact ENat.toNat_le_toNat (hq (n + 1)).2.1 (hq (n + 1)).2.2
    rw [hrr] at *
    simp only at h1 h2 ⊢
    omega
  · rw [hCnat, hrr]
    simp only
    omega

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

open Cx Function

universe u

section Alg

variable {R : Type u} [CommRing R] {A B : Cx R}

theorem cx_smul_d {n : ℕ} (t : R) (x : B.X n) : B.d n (t • x) = t • B.d n x := map_smul _ _ _

theorem bij_H_of_bij (t : R) (ht : ∀ n, Bijective fun x : B.X n => t • x) (n : ℕ) :
    Bijective (algebraMap R (Module.End R (B.H n)) t) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Module.algebraMap_end_apply, cls_smul, cls_eq_zero_iff] at hc
      rw [cls_eq_zero_iff]
      cases n with
      | zero =>
        have h0 : t • x = 0 := hc
        exact (ht 0).1 (h0.trans (smul_zero t).symm)
      | succ n =>
        obtain ⟨y, hy⟩ := hc
        obtain ⟨y', rfl⟩ := (ht n).2 y
        refine ⟨y', (ht (n + 1)).1 ?_⟩
        show t • B.d n y' = t • x
        rw [← cx_smul_d, hy]
  · intro c
    induction c using H_ind with
    | h x hx =>
      obtain ⟨x', rfl⟩ := (ht n).2 x
      have hx' : B.d n x' = 0 := (ht (n + 1)).1 (by
        show t • B.d n x' = t • 0
        rw [← cx_smul_d, smul_zero]; exact hx)
      exact ⟨B.cls n x' hx', by rw [Module.algebraMap_end_apply, cls_smul]⟩

theorem isLocalized_of_cx (j : Hom A B) (t : R) (hj : ∀ n, Injective (j.f n))
    (ht : ∀ n, Bijective fun x : B.X n => t • x)
    (hc : ∀ n (x : B.X n), ∃ (m : ℕ) (y : A.X n), j.f n y = t ^ m • x) (n : ℕ) :
    IsLocalizedModule (Submonoid.powers t) (j.H n) where
  map_units := by
    rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap R (Module.End R (B.H n)) (t ^ k))
    rw [map_pow]
    exact ((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht n)).pow k
  surj := by
    intro y
    induction y using H_ind with
    | h x hx =>
      obtain ⟨m, a, ha⟩ := hc n x
      have ha0 : A.d n a = 0 := (hj (n + 1)) (by
        rw [j.comm, ha, cx_smul_d, hx, smul_zero, map_zero])
      refine ⟨(A.cls n a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩
      show (t ^ m) • B.cls n x hx = j.H n (A.cls n a ha0)
      rw [cls_smul, Hom.H_cls]
      exact cls_congr _ _ ha.symm
  exists_of_eq := by
    have key : ∀ z : A.H n, j.H n z = 0 → ∃ c : Submonoid.powers t, c • z = 0 := by
      intro z hz
      induction z using H_ind with
      | h g hg =>
        rw [Hom.H_cls, cls_eq_zero_iff] at hz
        cases n with
        | zero =>
          have h0 : j.f 0 g = 0 := hz
          refine ⟨1, ?_⟩
          rw [one_smul, cls_eq_zero_iff]
          exact (hj 0) (h0.trans (map_zero _).symm)
        | succ n =>
          obtain ⟨h, hh⟩ := hz
          obtain ⟨m, k, hk⟩ := hc n h
          refine ⟨⟨t ^ m, m, rfl⟩, ?_⟩
          show (t ^ m) • A.cls (n + 1) g hg = 0
          rw [cls_smul, cls_eq_zero_iff]
          refine ⟨k, (hj (n + 1)) ?_⟩
          rw [j.comm, hk, cx_smul_d, hh, map_smul]
    intro x₁ x₂ h
    obtain ⟨c, hc'⟩ := key (x₁ - x₂) (by rw [map_sub, h, sub_self])
    exact ⟨c, by rw [smul_sub, sub_eq_zero] at hc'; exact hc'⟩

end Alg

section Trunc

variable {R : Type u} [CommRing R] (A : Cx R) (L : Submodule R (A.H 1))

def truncW : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊤
  | 1 => (L.comap ((A.B 1).comap (A.Z 1).subtype).mkQ).map (A.Z 1).subtype
  | _ + 2 => ⊥

theorem mem_truncW_one {x : A.X 1} :
    x ∈ truncW A L 1 ↔ ∃ hx : A.d 1 x = 0, A.cls 1 x hx ∈ L := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem truncW_d (n : ℕ) (x : A.X n) (hx : x ∈ truncW A L n) : A.d n x ∈ truncW A L (n + 1) := by
  match n, x, hx with
  | 0, x, _ =>
    rw [mem_truncW_one]
    refine ⟨A.dd 0 x, ?_⟩
    rw [cls_d]; exact L.zero_mem
  | 1, x, hx =>
    obtain ⟨hx0, _⟩ := (mem_truncW_one A L).1 hx
    show A.d 1 x ∈ (⊥ : Submodule R _)
    rw [hx0]; exact Submodule.zero_mem _
  | n + 2, x, hx =>
    have : x = 0 := (Submodule.mem_bot R).1 hx
    subst this
    rw [map_zero]; exact Submodule.zero_mem _

def truncCx : Cx R where
  X n := truncW A L n
  d n := (A.d n).restrict fun x hx => truncW_d A L n x hx
  dd n x := Subtype.ext (A.dd n x.1)

def truncHom : Hom (truncCx A L) A where
  f n := (truncW A L n).subtype
  comm _ _ := rfl

end Trunc

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

theorem localise_holds : LocaliseStatement.{u} := by
  intro R _ G _ _ _ _ t L V j hφ hu he hcov n
  obtain ⟨e, he⟩ := he
  refine isLocalized_of_cx j.hom t ?_ ?_ ?_ n
  · intro k x y hxy
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu
    subst hφ
    refine Subtype.ext (funext fun g => hu.injective ?_)
    exact congrFun (congrArg Subtype.val hxy) g
  · intro k
    constructor
    · intro x y hxy
      refine Subtype.ext (funext fun g => e.injective ?_)
      rw [he, he]
      exact congrFun (congrArg Subtype.val hxy) g
    · intro y
      refine ⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩
      show t • e.symm (y.1 g) = y.1 g
      rw [← he, e.apply_symm_apply]
  · intro k x
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu hcov
    subst hφ
    have hx : Continuous x.1 := x.2
    let O : ℕ → Set (Fin k → G) := fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)
    have hO : ∀ m, IsOpen (O m) := fun m =>
      ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx
    have hmono : Monotone O := by
      refine monotone_nat_of_le_succ fun m g hg => ?_
      obtain ⟨l, hl⟩ := hg
      refine ⟨t • l, ?_⟩
      simp only at hl ⊢
      rw [map_smul, hl, pow_succ', mul_smul]
    have hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m := by
      intro g _
      obtain ⟨m, l, hl⟩ := hcov (x.1 g)
      exact Set.mem_iUnion.2 ⟨m, l, hl⟩
    obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le
    have hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g := fun g =>
      invFun_eq (hm (Set.mem_univ g))
    have hyc : Continuous fun g => invFun u (t ^ m • x.1 g) := by
      rw [hu.isEmbedding.continuous_iff]
      have : (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g := funext hy
      rw [this]
      exact hx.const_smul _
    refine ⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩
    exact hy g


end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

namespace QuadraticConjugation

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjHom (U : Subgroup G) [U.Normal] (s : G) : U →* U where
  toFun g := ⟨s⁻¹ * g * s, by simpa using ‹U.Normal›.conj_mem g g.2 s⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp] theorem conjHom_coe (U : Subgroup G) [U.Normal] (s : G) (g : U) :
    ((conjHom U s g : U) : G) = s⁻¹ * g * s := rfl

theorem continuous_rho' (N : TRep R G) (s : G) : Continuous (N.rho s) :=
  N.cont.comp (f := fun m : N.V => (s, m)) (continuous_const.prodMk continuous_id)

theorem rho_conj (N : TRep R G) (s g : G) (m : N.V) :
    N.rho s (N.rho (s⁻¹ * g * s) m) = N.rho g (N.rho s m) := by
  have : s * (s⁻¹ * g * s) = g * s := by group
  rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply]

def conjPair (N : TRep R G) (U : Subgroup G) [U.Normal] (s : G) : Pair (N.resSub U) (N.resSub U) where
  φ := conjHom U s
  u := N.rho s
  φ_cont := Continuous.subtype_mk
    ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  u_cont := continuous_rho' N s
  equiv g m := rho_conj N s g m

def conjG (s : G) : G →* G where
  toFun g := s⁻¹ * g * s
  map_one' := by simp
  map_mul' a b := by group

def innerPair (N : TRep R G) (s : G) : Pair N N where
  φ := conjG s
  u := N.rho s
  φ_cont := (continuous_const.mul continuous_id).mul continuous_const
  u_cont := continuous_rho' N s
  equiv g m := rho_conj N s g m

end

section Lemmas

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Lemmas

section Main

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M M' : TRep R G} {U : Subgroup G} [U.Normal] (P : Pair M' (M.resSub U))

theorem phi_apply (hφ : P.φ = U.subtype) (g : U) : P.φ g = (g : G) := by rw [hφ]; rfl

noncomputable def PU (hφ : P.φ = U.subtype) : Pair (M'.resSub U) (M.resSub U) where
  φ := MonoidHom.id U
  u := P.u
  φ_cont := continuous_id
  u_cont := P.u_cont
  equiv g m := by
    have := P.equiv g m
    rw [phi_apply P hφ] at this
    exact this

noncomputable def eqv (hP : IsHomeomorph P.u) : M'.V ≃ₗ[R] (M.resSub U).V := LinearEquiv.ofBijective P.u hP.bijective

theorem eqv_symm (hP : IsHomeomorph P.u) (m : (M.resSub U).V) : P.u ((eqv P hP).symm m) = m :=
  (eqv P hP).apply_symm_apply m

noncomputable def PInv (hφ : P.φ = U.subtype) (hP : IsHomeomorph P.u) : Pair (M.resSub U) (M'.resSub U) where
  φ := MonoidHom.id U
  u := (eqv P hP).symm.toLinearMap
  φ_cont := continuous_id
  u_cont := by
    have h1 : ∀ m, P.u ((hP.homeomorph P.u).symm m) = m := fun m =>
      (hP.homeomorph P.u).apply_symm_apply m
    refine (hP.homeomorph P.u).symm.continuous.congr fun m => hP.bijective.1 ?_
    show P.u _ = P.u ((eqv P hP).symm m)
    rw [h1, eqv_symm]
  equiv g m := by
    apply hP.bijective.1
    show P.u ((eqv P hP).symm ((M.resSub U).rho g m)) = P.u (M'.rho g ((eqv P hP).symm m))
    have := P.equiv g ((eqv P hP).symm m)
    rw [phi_apply P hφ] at this
    rw [this, eqv_symm, eqv_symm]

end Main

end QuadraticConjugation

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def stabN (A : TRep R G) (N : Subgroup G) (a : A.V) : Subgroup N where
  carrier := {n | A.rho (n : G) a = a}
  mul_mem' {x y} hx hy := by
    show A.rho ((x * y : N) : G) a = a
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, show A.rho (y : G) a = a from hy]
    exact hx
  one_mem' := by show A.rho ((1 : N) : G) a = a; simp
  inv_mem' {x} hx := by
    show A.rho ((x⁻¹ : N) : G) a = a
    have hx' : A.rho (x : G) a = a := hx
    conv_lhs => rw [← hx']
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one,
      Module.End.one_apply]

theorem stabN_open (A : TRep R G) [DiscreteTopology A.V] (N : Subgroup G) (a : A.V) :
    IsOpen (stabN A N a : Set N) := by
  have hc : Continuous fun n : N => A.rho (n : G) a :=
    A.cont.comp (f := fun n : N => ((n : G), a)) (continuous_subtype_val.prodMk continuous_const)
  exact (isOpen_discrete {a}).preimage hc

theorem finite_quot_of_open {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] (W : Subgroup K) (hW : IsOpen (W : Set K)) : Finite (K ⧸ W) := by
  have := QuotientGroup.discreteTopology hW
  exact finite_of_compact_of_discrete

theorem inv_lift [CompactSpace G] (N : Subgroup G) (hN : IsClosed (N : Set G))
    (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (A B : TRep R G) [DiscreteTopology A.V] (p : A.V →ₗ[R] B.V)
    (hp : ∀ g a, p (A.rho g a) = B.rho g (p a)) (hs : Surjective p) (b : B.V)
    (hb : ∀ g ∈ N, B.rho g b = b) : ∃ a, (∀ g ∈ N, A.rho g a = a) ∧ p a = b := by
  have : CompactSpace N := isCompact_iff_compactSpace.1 hN.isCompact
  obtain ⟨a₀, rfl⟩ := hs b
  set W := stabN A N a₀
  have hWo := stabN_open A N a₀
  have : Finite (N ⧸ W) := finite_quot_of_open W hWo
  have : Fintype (N ⧸ W) := Fintype.ofFinite _
  obtain ⟨v, hv⟩ := hW W hWo
  set s : A.V := ∑ c : N ⧸ W, A.rho ((c.out : N) : G) a₀ with hs_def
  have key : ∀ (x : N), A.rho ((x : N) : G) a₀ = A.rho (((QuotientGroup.mk x : N ⧸ W).out : N) : G) a₀ := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul W x
    rw [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, show A.rho ((h : N) : G) a₀ = a₀ from h.2]
  have hinv : ∀ g ∈ N, A.rho g s = s := by
    intro g hg
    rw [hs_def, map_sum]
    have e : ∀ c : N ⧸ W, A.rho g (A.rho ((c.out : N) : G) a₀) =
        A.rho ((((⟨g, hg⟩ : N) • c).out : N) : G) a₀ := by
      intro c
      rw [← Module.End.mul_apply, ← map_mul]
      have := key (⟨g, hg⟩ * c.out)
      rw [Subgroup.coe_mul] at this
      rw [this]
      congr 4
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    simp only [e]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨g, hg⟩ : N)) _ _ (fun _ => rfl)
  refine ⟨((v⁻¹ : Rˣ) : R) • s, fun g hg => by rw [map_smul, hinv g hg], ?_⟩
  rw [map_smul, hs_def, map_sum]
  simp only [hp, fun c : N ⧸ W => hb _ c.out.2]
  have hcard : (Finset.univ : Finset (N ⧸ W)).card = W.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card, Finset.card_univ]
  rw [Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul R, ← hv, smul_smul, Units.inv_mul, one_smul]

theorem emb_disc {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology X]
    [DiscreteTopology Y] (f : X → Y) (hf : Injective f) : IsEmbedding f := by
  refine ⟨⟨(DiscreteTopology.eq_bot).trans (eq_bot_of_singletons_open fun x => ?_).symm⟩, hf⟩
  refine isOpen_induced_iff.2 ⟨{f x}, isOpen_discrete _, ?_⟩
  ext y; simp [hf.eq_iff]

theorem cmap_disc (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [DiscreteTopology Y] : DiscreteTopology C(X, Y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun f => ?_
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have hset : ({f} : Set C(X, Y)) = ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro rfl y _ x hx; exact hx
    · intro h
      ext x
      exact h (f x) ⟨x, rfl⟩ (show x ∈ f ⁻¹' {f x} from rfl)
  rw [hset]
  exact hfin.isOpen_biInter fun y _ => ContinuousMap.isOpen_setOfPred_mapsTo
    ((isClosed_discrete {y}).preimage f.continuous).isCompact (isOpen_discrete _)

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

abbrev CG (M : TRep R G) : TRep R G := coindRep (⊥ : Subgroup G) (M.resSub ⊥)

instance CG_disc [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : DiscreteTopology (CG M).V := by
  have : DiscreteTopology (M.resSub (⊥ : Subgroup G)).V := ‹DiscreteTopology M.V›
  have := cmap_disc G (M.resSub (⊥ : Subgroup G)).V
  exact (IsEmbedding.subtypeVal (p := fun f => f ∈ coindSub (⊥ : Subgroup G) (M.resSub ⊥))).discreteTopology

def iCG (M : TRep R G) : M.V →ₗ[R] (CG M).V where
  toFun m := ⟨⟨fun x => M.rho x m, M.cont.comp (f := fun x : G => (x, m)) (continuous_id.prodMk continuous_const)⟩,
    fun x g => by
      show M.rho ((x : G) * g) m = M.rho (x : G) (M.rho g m)
      rw [map_mul, Module.End.mul_apply]⟩
  map_add' a b := Subtype.ext (ContinuousMap.ext fun x => by
    show M.rho x (a + b) = M.rho x a + M.rho x b; simp)
  map_smul' r a := Subtype.ext (ContinuousMap.ext fun x => by
    show M.rho x (r • a) = r • M.rho x a; simp)

@[simp] theorem iCG_apply (M : TRep R G) (m : M.V) (x : G) : (iCG M m).1 x = M.rho x m := rfl

theorem iCG_equiv (M : TRep R G) (g : G) (m : M.V) : iCG M (M.rho g m) = (CG M).rho g (iCG M m) := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  show M.rho x (M.rho g m) = M.rho (x * g) m
  rw [map_mul, Module.End.mul_apply]

theorem iCG_inj (M : TRep R G) : Injective (iCG M) := fun a b h => by
  have h1 : M.rho 1 a = M.rho 1 b := congrArg (fun f : (CG M).V => f.1 1) h
  simpa using h1

def iP (M : TRep R G) [DiscreteTopology M.V] : Pair M (CG M) :=
  Pair.ofMap (iCG M) continuous_of_discreteTopology (iCG_equiv M)

def QG (M : TRep R G) : TRep R G where
  V := (CG M).V ⧸ LinearMap.range (iCG M)
  rho := (CG M).rho.quotient (LinearMap.range (iCG M)) (fun g x hx => by
    obtain ⟨m, rfl⟩ := hx
    exact ⟨M.rho g m, iCG_equiv M g m⟩)
  cont := by
    have hq : IsQuotientMap (fun p : G × (CG M).V => (p.1, (LinearMap.range (iCG M)).mkQ p.2)) :=
      (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ _)).isQuotientMap
    unfold Gal.ContAction
    rw [hq.continuous_iff]
    exact (Submodule.isQuotientMap_mkQ _).continuous.comp (CG M).cont

instance QG_disc [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : DiscreteTopology (QG M).V := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
  exact (Submodule.isQuotientMap_mkQ (LinearMap.range (iCG M))).isOpen_preimage.1 (isOpen_discrete _)

def pLin (M : TRep R G) : (CG M).V →ₗ[R] (QG M).V := (LinearMap.range (iCG M)).mkQ

theorem pLin_cont (M : TRep R G) : Continuous (pLin M) := (Submodule.isQuotientMap_mkQ _).continuous

theorem pLin_equiv (M : TRep R G) (g : G) (c : (CG M).V) : pLin M ((CG M).rho g c) = (QG M).rho g (pLin M c) := rfl

theorem pLin_eq_zero (M : TRep R G) (c : (CG M).V) : pLin M c = 0 ↔ c ∈ LinearMap.range (iCG M) :=
  Submodule.Quotient.mk_eq_zero _

theorem pLin_surj (M : TRep R G) : Surjective (pLin M) := Submodule.mkQ_surjective _

def pP (M : TRep R G) : Pair (CG M) (QG M) := Pair.ofMap (pLin M) (pLin_cont M) (pLin_equiv M)

theorem admissible_compact_discrete [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : admitted (iP M) (pP M) where
  i_id := rfl
  p_id := rfl
  emb := emb_disc _ (iCG_inj M)
  exact := LinearMap.exact_map_mkQ_range _
  sec := ⟨surjInv (pLin_surj M), continuous_of_discreteTopology,
    surjInv_eq _⟩

theorem CG_acyc (M : TRep R G) (m : ℕ) (z : (CG M).H (m + 1)) : z = 0 := by
  have hq := shapiro_holds R G (⊥ : Subgroup G) (M.resSub ⊥) (CG M) (coindEv _ _) (coindEv_isCoind _ _)
    ⟨fun _ => 1, continuous_const, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      rw [hx, one_mul]⟩
  have : Subsingleton (⊥ : Subgroup G) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  refine (hq (m + 1)).1 ?_
  rw [map_zero]
  exact FiniteLevelCohomology.H_succ_trivial _ m _

end InflationIsomorphism

end

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Inv

variable {N : Subgroup G} [N.Normal]

theorem inv_disc {A : TRep R G} [DiscreteTopology A.V] {Q : TRep R (G ⧸ N)} {P : Pair Q A}
    (hP : IsInvRep A N Q P) : DiscreteTopology Q.V := hP.2.1.discreteTopology

theorem inv_mem {A : TRep R G} {Q : TRep R (G ⧸ N)} {P : Pair Q A} (hP : IsInvRep A N Q P) (q : Q.V) :
    ∀ g ∈ N, A.rho g (P.u q) = P.u q := (hP.2.2 _).1 ⟨q, rfl⟩

theorem inv_equiv {A : TRep R G} {Q : TRep R (G ⧸ N)} {P : Pair Q A} (hP : IsInvRep A N Q P) (g : G)
    (q : Q.V) : P.u (Q.rho (g : G ⧸ N) q) = A.rho g (P.u q) := by
  have h := P.equiv g q
  rw [hP.1] at h
  exact h

def invLin {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)} {PB : Pair QB B}
    (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) : QA.V →ₗ[R] QB.V :=
  (LinearEquiv.ofInjective PB.u hB.2.1.injective).symm.toLinearMap.comp
    ((a.comp PA.u).codRestrict (LinearMap.range PB.u) fun q => (hB.2.2 _).2 fun g hg => by
      rw [LinearMap.comp_apply, ← ha, inv_mem hA q g hg])

theorem invLin_spec {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (q : QA.V) : PB.u (invLin hA hB a ha q) = a (PA.u q) := by
  unfold invLin
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply]
  rfl

def invPair {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)} {PB : Pair QB B}
    [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) : Pair QA QB :=
  have := inv_disc hA
  Pair.ofMap (invLin hA hB a ha) continuous_of_discreteTopology fun y q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    apply hB.2.1.injective
    rw [inv_equiv hB, invLin_spec, invLin_spec, inv_equiv hA, ha]

theorem invPair_u {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB)
    (a : A.V →ₗ[R] B.V) (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (q : QA.V) :
    PB.u ((invPair hA hB a ha).u q) = a (PA.u q) := invLin_spec hA hB a ha q

theorem invPair_comm {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB)
    (a : A.V →ₗ[R] B.V) (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (hac : Continuous a) (n : ℕ)
    (x : QA.coch.X n) :
    PB.hom.f n ((invPair hA hB a ha).hom.f n x) = (Pair.ofMap a hac ha).hom.f n (PA.hom.f n x) := by
  refine Subtype.ext (funext fun g => ?_)
  show PB.u ((invPair hA hB a ha).u (x.1 fun i => (invPair hA hB a ha).φ (PB.φ (g i)))) =
    a (PA.u (x.1 fun i => PA.φ (g i)))
  rw [invPair_u, hA.1, hB.1]
  rfl

theorem deg0 (A : TRep R G) (Q : TRep R (G ⧸ N)) (P : Pair Q A) (hP : IsInvRep A N Q P) :
    Bijective (P.hom.H 0) := by
  have hsub : ∀ {X : Type u} (f f' : Fin 0 → X), f = f' := fun f f' => Subsingleton.elim _ _
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [InflationRestrictionInvariants.H_mk, InflationRestrictionInvariants.mk_eq_zero_iff] at hz
    have h0 : P.hom.f 0 x = 0 := hz
    have hx0 : x = 0 := by
      refine Subtype.ext (funext fun f => ?_)
      have : P.u (x.1 fun i => P.φ (![] i)) = 0 := congrArg (fun y : A.coch.X 0 => y.1 ![]) h0
      apply hP.2.1.injective
      refine (show P.u (x.1 f) = P.u 0 from ?_)
      rw [map_zero, hsub f (fun i => P.φ (![] i))]
      exact this
    rw [InflationRestrictionInvariants.mk_eq_zero_iff]
    subst hx0
    exact Submodule.zero_mem _
  · intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hy' : A.coch.d 0 y = 0 := hy
    have hinvG : ∀ a, A.rho a (y.1 ![]) = y.1 ![] := fun a => by
      have := congrArg (fun w : A.coch.X 1 => w.1 (InflationRestrictionInvariants.e1 a)) hy'
      simp only [InflationRestrictionInvariants.zeroDifferential_val] at this
      exact sub_eq_zero.1 this
    obtain ⟨q, hq⟩ := (hP.2.2 (y.1 ![])).2 fun g _ => hinvG g
    have hdq : Q.coch.d 0 (InflationRestrictionInvariants.const0 Q q) = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      rw [InflationRestrictionInvariants.oneCochain_apply_fin_one, InflationRestrictionInvariants.zeroDifferential_val]
      show Q.rho (g 0) q - q = 0
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (g 0)
      rw [← ha, sub_eq_zero]
      apply hP.2.1.injective
      rw [inv_equiv hP, hq, hinvG]
    refine ⟨Submodule.Quotient.mk ⟨InflationRestrictionInvariants.const0 Q q, hdq⟩, ?_⟩
    rw [InflationRestrictionInvariants.H_mk]
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun f => ?_))
    show P.u q = y.1 f
    rw [hq, hsub f ![]]

end Inv

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]

abbrev Mbot (M : TRep R G) : TRep R (⊥ : Subgroup (G ⧸ N)) := M.res 1 continuous_const

def evC (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) : Pair QC (Mbot (N := N) M) :=
  have := inv_disc hC
  { φ := (⊥ : Subgroup (G ⧸ N)).subtype
    u := (coindEv (⊥ : Subgroup G) (M.resSub ⊥)).u.comp PC.u
    φ_cont := continuous_subtype_val
    u_cont := continuous_of_discreteTopology
    equiv := fun g m => by
      have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
      subst hg
      show _ = M.rho 1 _
      rw [map_one, map_one, map_one]
      rfl }

theorem evC_rho (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) (q : QC.V) (g : G) :
    (evC M hC).u (QC.rho (g : G ⧸ N) q) = (PC.u q).1 g := by
  show (PC.u (QC.rho (g : G ⧸ N) q)).1 1 = _
  rw [inv_equiv hC]
  show (PC.u q).1 (1 * g) = _
  rw [one_mul]

theorem QC_coind (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) : IsCoind (⊥ : Subgroup (G ⧸ N)) (Mbot M) QC (evC M hC) := by
  have := inv_disc hC
  have : DiscreteTopology (Mbot (N := N) M).V := ‹DiscreteTopology M.V›
  have := cmap_disc (G ⧸ N) (Mbot (N := N) M).V
  let j : QC.V → C(G ⧸ N, (Mbot (N := N) M).V) := fun q =>
    ⟨fun y => (evC M hC).u (QC.rho y q),
      (evC M hC).u_cont.comp (QC.cont.comp (f := fun y => (y, q)) (continuous_id.prodMk continuous_const))⟩
  have hj : ∀ q (g : G), j q (g : G ⧸ N) = (PC.u q).1 g := evC_rho M hC
  refine ⟨rfl, j, emb_disc _ fun q q' h => ?_, fun c g => rfl, fun f _ => ?_⟩
  · apply hC.2.1.injective
    refine Subtype.ext (ContinuousMap.ext fun g => ?_)
    rw [← hj, ← hj, h]
  · let F : (CG M).V := ⟨f.comp ⟨QuotientGroup.mk, continuous_quot_mk⟩, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      subst hx
      show f ((((1 : (⊥ : Subgroup G)) : G) * g : G) : G ⧸ N) = M.rho 1 (f (g : G ⧸ N))
      rw [map_one, Subgroup.coe_one, one_mul]
      rfl⟩
    obtain ⟨q, hq⟩ := (hC.2.2 F).2 fun n hn => Subtype.ext (ContinuousMap.ext fun h => by
      show f ((h * n : G) : G ⧸ N) = f (h : G ⧸ N)
      rw [QuotientGroup.mk_mul_of_mem h hn])
    refine ⟨q, ContinuousMap.ext fun y => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hj, hq]
    rfl

theorem QC_acyc (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) (m : ℕ) (z : QC.H (m + 1)) : z = 0 := by
  have hq := shapiro_holds R (G ⧸ N) (⊥ : Subgroup (G ⧸ N)) (Mbot M) QC (evC M hC) (QC_coind M hC)
    ⟨fun _ => 1, continuous_const, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      rw [hx, one_mul]⟩
  have : Subsingleton (⊥ : Subgroup (G ⧸ N)) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  refine (hq (m + 1)).1 ?_
  rw [map_zero]
  exact FiniteLevelCohomology.H_succ_trivial _ m _

end InflationIsomorphism

end

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R]

theorem H_comm {A B A' B' : Cx R} (i : Hom A B) (i' : Hom A' B') (α : Hom A A') (β : Hom B B')
    (h : ∀ n x, β.f n (i.f n x) = i'.f n (α.f n x)) (n : ℕ) (z : A.H n) :
    β.H n (i.H n z) = i'.H n (α.H n z) := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [InflationRestrictionInvariants.H_mk]
  congr 1
  exact Subtype.ext (h n x)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]

theorem admissible_character_inv (hN : IsClosed (N : Set G)) (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (M : TRep R G) [DiscreteTopology M.V] {Q : TRep R (G ⧸ N)} {P : Pair Q M} (hP : IsInvRep M N Q P)
    {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)} (hC : IsInvRep (CG M) N QC PC)
    {QQ : TRep R (G ⧸ N)} {PQ : Pair QQ (QG M)} (hQ : IsInvRep (QG M) N QQ PQ) :
    admitted (invPair hP hC (iCG M) (iCG_equiv M))
      (invPair hC hQ (pLin M) (pLin_equiv M)) := by
  have := inv_disc hP
  have := inv_disc hC
  have := inv_disc hQ
  refine ⟨rfl, rfl, emb_disc _ fun a b h => ?_, fun c => ?_, ?_⟩
  · have h' := congrArg PC.u h
    rw [invPair_u, invPair_u] at h'
    exact hP.2.1.injective (iCG_inj M h')
  · constructor
    · intro hc
      have h1 := congrArg PQ.u hc
      rw [invPair_u, map_zero, pLin_eq_zero] at h1
      obtain ⟨m, hm⟩ := h1
      have hmN : ∀ g ∈ N, M.rho g m = m := fun g hg => iCG_inj M (by
        rw [iCG_equiv, hm, inv_mem hC c g hg])
      obtain ⟨q, rfl⟩ := (hP.2.2 m).2 hmN
      refine ⟨q, hC.2.1.injective ?_⟩
      rw [invPair_u, hm]
    · rintro ⟨q, rfl⟩
      apply hQ.2.1.injective
      rw [invPair_u, invPair_u, map_zero, pLin_eq_zero]
      exact ⟨_, rfl⟩
  · have hs : Surjective (invPair hC hQ (pLin M) (pLin_equiv M)).u := by
      intro y
      obtain ⟨c, hcN, hc⟩ := inv_lift (R := R) N hN hW (CG M) (QG M) (pLin M)
        (pLin_equiv M) (pLin_surj M) (PQ.u y) (inv_mem hQ y)
      obtain ⟨c', rfl⟩ := (hC.2.2 c).2 hcN
      exact ⟨c', hQ.2.1.injective (by rw [invPair_u, hc])⟩
    exact ⟨surjInv hs, continuous_of_discreteTopology, surjInv_eq hs⟩

theorem main (hN : IsClosed (N : Set G)) (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (n : ℕ) : ∀ (M : TRep R G) [DiscreteTopology M.V] (Q : TRep R (G ⧸ N)) (P : Pair Q M),
    IsInvRep M N Q P → Bijective (P.hom.H n) := by
  induction n with
  | zero => exact fun M _ Q P hP => deg0 M Q P hP
  | succ n ih =>
  intro M _ Q P hP
  have hC := InflationRestrictionInvariants.invariants_isInvRep (CG M) N
  have hQ := InflationRestrictionInvariants.invariants_isInvRep (QG M) N
  have hadm := admissible_character_inv hN hW M hP hC hQ
  have hs := admissibility_holds R (G ⧸ N) _ _ _ _ _ hadm
  have hs' := admissibility_holds R G _ _ _ _ _ (admissible_compact_discrete M)
  obtain ⟨⟨δ, hδ, hL⟩, -⟩ := lES_holds R _ _ _ _ _ hs
  obtain ⟨⟨δ', hδ', hL'⟩, -⟩ := lES_holds R _ _ _ _ _ hs'
  have c1 := invPair_comm hP hC (iCG M) (iCG_equiv M) continuous_of_discreteTopology
  have c2 := invPair_comm hC hQ (pLin M) (pLin_equiv M)
    (pLin_cont M)
  have hnat := connNat_holds R _ _ _ _ _ _ _ _ _ _ P.hom _ _ δ δ' hs hs' c1 c2 hδ hδ'
  have hβ := ih (CG M) _ _ hC
  have hγ := ih (QG M) _ _ hQ
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    obtain ⟨x, rfl⟩ := ((hL.exA n) y).1 (QC_acyc M hC n _)
    rw [← hnat] at hy
    obtain ⟨c, hc⟩ := ((hL'.exC n) _).1 hy
    obtain ⟨c', rfl⟩ := hβ.2 c
    rw [← H_comm _ (pP M).hom _ _ c2 n c'] at hc
    rw [← hγ.1 hc]
    exact ((hL.exC n) _).2 ⟨c', rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := ((hL'.exA n) y).1 (CG_acyc M n _)
    obtain ⟨x', rfl⟩ := hγ.2 x
    exact ⟨δ n x', (hnat n x').symm⟩

end InflationIsomorphism

end

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh.PowerKernelFiltration

universe u

section Art

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]

def kerPow (t : R) (m : ℕ) : Submodule R N := LinearMap.ker ((t ^ m) • (LinearMap.id : N →ₗ[R] N))

def layer (t : R) (P : Submodule R N) (m : ℕ) : Submodule R N :=
  (P ⊓ kerPow t (m + 1)).map ((t ^ m) • (LinearMap.id : N →ₗ[R] N))

end Art

section Card

end Card

end ReciprocityTheory.Coh.PowerKernelFiltration
end
