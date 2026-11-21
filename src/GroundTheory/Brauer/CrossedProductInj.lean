import Mathlib
import GroundTheory.Brauer.CrossedProductMaps
import GroundTheory.Brauer.SkolemNoether
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open groupCohomology

universe u v u' v'

section Cochains

variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]

def mulCocycles₂ : Subgroup (G × G → M) where
  carrier := {f | IsMulCocycle₂ f}
  one_mem' := by
    intro g h j
    simp
  mul_mem' := by
    intro f k hf hk g h j
    simp only [Pi.mul_apply]
    rw [mul_mul_mul_comm, hf g h j, hk g h j, smul_mul', mul_mul_mul_comm]
  inv_mem' := by
    intro f hf g h j
    simp only [Pi.inv_apply]
    rw [← mul_inv, hf g h j, mul_inv, smul_inv']

def mulCoboundaries₂ : Subgroup (G × G → M) where
  carrier := {f | IsMulCoboundary₂ f}
  one_mem' := ⟨1, fun g h => by simp⟩
  mul_mem' := by
    rintro f k ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, fun g h => ?_⟩
    simp only [Pi.mul_apply, ← hx g h, ← hy g h, smul_mul']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  inv_mem' := by
    rintro f ⟨x, hx⟩
    refine ⟨x⁻¹, fun g h => ?_⟩
    simp only [Pi.inv_apply, ← hx g h, smul_inv']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel

variable {G M}

@[simp]
theorem mem_mulCocycles₂_iff (f : G × G → M) : f ∈ mulCocycles₂ G M ↔ IsMulCocycle₂ f :=
  Iff.rfl

@[simp]
theorem mem_mulCoboundaries₂_iff (f : G × G → M) :
    f ∈ mulCoboundaries₂ G M ↔ IsMulCoboundary₂ f :=
  Iff.rfl

theorem isMulCocycle₂_of_isMulCoboundary₂ {f : G × G → M} (hf : IsMulCoboundary₂ f) :
    IsMulCocycle₂ f := by
  obtain ⟨x, hx⟩ := hf
  intro g h j
  rw [← hx, ← hx, ← hx, ← hx]
  simp only [smul_mul', smul_div', mul_smul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, mul_assoc]
  abel

variable (G M) in

theorem mulCoboundaries₂_le_mulCocycles₂ : mulCoboundaries₂ G M ≤ mulCocycles₂ G M :=
  fun _ hf => isMulCocycle₂_of_isMulCoboundary₂ hf

theorem map_one_fst_of_isMulCocycle₂_of_eq_one {f : G × G → M} (hf : IsMulCocycle₂ f)
    (h1 : f (1, 1) = 1) (g : G) : f (1, g) = 1 := by
  rw [map_one_fst_of_isMulCocycle₂ hf, h1]

theorem map_one_snd_of_isMulCocycle₂_of_eq_one {f : G × G → M} (hf : IsMulCocycle₂ f)
    (h1 : f (1, 1) = 1) (g : G) : f (g, 1) = 1 := by
  rw [map_one_snd_of_isMulCocycle₂ hf, h1, smul_one]

end Cochains

section H2mul

variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]

abbrev H2mul : Type (max u v) :=
  mulCocycles₂ G M ⧸ (mulCoboundaries₂ G M).subgroupOf (mulCocycles₂ G M)

namespace H2mul

def mk : mulCocycles₂ G M →* H2mul G M :=
  QuotientGroup.mk' ((mulCoboundaries₂ G M).subgroupOf (mulCocycles₂ G M))

variable {G M}

theorem mk_surjective : Function.Surjective (mk G M) :=
  QuotientGroup.mk'_surjective _

@[elab_as_elim]
theorem induction_on {C : H2mul G M → Prop} (x : H2mul G M) (h : ∀ f, C (mk G M f)) : C x := by
  obtain ⟨f, rfl⟩ := mk_surjective x
  exact h f

theorem mk_eq_one_iff (f : mulCocycles₂ G M) :
    mk G M f = 1 ↔ IsMulCoboundary₂ (f : G × G → M) := by
  rw [mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem mk_eq_mk_iff (f f' : mulCocycles₂ G M) :
    mk G M f = mk G M f' ↔ IsMulCoboundary₂ ((f : G × G → M) / (f' : G × G → M)) := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff]
  rfl

section Functoriality

variable {G' : Type u'} {M' : Type v'} [Group G'] [CommGroup M'] [MulDistribMulAction G' M']

def mapCocycles₂ (f : G' →* G) (φ : M →* M') (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m) :
    mulCocycles₂ G M →* mulCocycles₂ G' M' where
  toFun c := ⟨fun p => φ ((c : G × G → M) (f p.1, f p.2)), by
    intro g h j
    simp only [map_mul, ← hφ]
    rw [← map_mul, c.2 (f g) (f h) (f j), map_mul]⟩
  map_one' := by
    ext p
    simp
  map_mul' c c' := by
    ext p
    simp

@[simp]
theorem mapCocycles₂_apply (f : G' →* G) (φ : M →* M')
    (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m) (c : mulCocycles₂ G M) (p : G' × G') :
    (mapCocycles₂ f φ hφ c : G' × G' → M') p = φ ((c : G × G → M) (f p.1, f p.2)) :=
  rfl

def mapPair (f : G' →* G) (φ : M →* M') (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m) :
    H2mul G M →* H2mul G' M' :=
  QuotientGroup.map _ _ (mapCocycles₂ f φ hφ) (by
    rintro c ⟨x, hx⟩
    refine ⟨fun g => φ (x (f g)), fun g h => ?_⟩
    have hxgh := hx (f g) (f h)
    change _ = (c : G × G → M) (f g, f h) at hxgh
    change _ = φ ((c : G × G → M) (f g, f h))
    rw [← hxgh]
    simp only [map_mul, map_div, hφ])

@[simp]
theorem mapPair_mk (f : G' →* G) (φ : M →* M') (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m)
    (c : mulCocycles₂ G M) :
    mapPair f φ hφ (mk G M c) = mk G' M' (mapCocycles₂ f φ hφ c) :=
  rfl



variable {N : Type v'} [CommGroup N] [MulDistribMulAction G N]

def map (φ : M →*[G] N) : H2mul G M →* H2mul G N :=
  mapPair (MonoidHom.id G) (φ : M →* N) (fun g m => by simp)

@[simp]
theorem map_mk (φ : M →*[G] N) (c : mulCocycles₂ G M) :
    map φ (mk G M c) =
      mk G N (mapCocycles₂ (MonoidHom.id G) (φ : M →* N) (fun g m => by simp) c) :=
  rfl

theorem map_id : map (MulDistribMulActionHom.id G : M →*[G] M) = MonoidHom.id (H2mul G M) := by
  ext x
  rfl

theorem map_comp {P : Type*} [CommGroup P] [MulDistribMulAction G P] (φ : M →*[G] N)
    (ψ : N →*[G] P) : map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext x
  rfl

end Functoriality

section ResInf

def res (H : Subgroup G) : H2mul G M →* H2mul H M :=
  mapPair H.subtype (MonoidHom.id M) (fun _ _ => rfl)

@[simp]
theorem res_mk (H : Subgroup G) (c : mulCocycles₂ G M) :
    res H (mk G M c) = mk H M (mapCocycles₂ H.subtype (MonoidHom.id M) (fun _ _ => rfl) c) :=
  rfl

variable (N : Subgroup G) [N.Normal]

theorem smul_mem_fixedPoints_of_normal (g : G) {m : M}
    (hm : m ∈ FixedPoints.subgroup N M) : g • m ∈ FixedPoints.subgroup N M := by
  intro n
  have hn : g⁻¹ * (n : G) * g ∈ N := by
    simpa using ‹N.Normal›.conj_mem _ n.2 g⁻¹
  have := hm ⟨_, hn⟩
  change (g⁻¹ * (n : G) * g) • m = m at this
  change (n : G) • g • m = g • m
  calc (n : G) • g • m = g • (g⁻¹ * (n : G) * g) • m := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • m := by rw [this]

instance mulDistribMulActionQuotientFixedPoints :
    MulDistribMulAction (G ⧸ N) (FixedPoints.subgroup N M) where
  smul q m := Quotient.liftOn' q
    (fun g => (⟨g • (m : M), smul_mem_fixedPoints_of_normal N g m.2⟩ :
      FixedPoints.subgroup N M)) (by
    intro g g' h
    apply Subtype.ext
    rw [QuotientGroup.leftRel_apply] at h
    have := m.2 ⟨_, h⟩
    change (g⁻¹ * g') • (m : M) = m at this
    change g • (m : M) = g' • (m : M)
    conv_lhs => rw [← this]
    rw [← mul_smul, mul_inv_cancel_left])
  one_smul m := Subtype.ext (one_smul G (m : M))
  mul_smul q q' m := by
    induction q using QuotientGroup.induction_on
    induction q' using QuotientGroup.induction_on
    exact Subtype.ext (mul_smul _ _ (m : M))
  smul_mul q m m' := by
    induction q using QuotientGroup.induction_on
    exact Subtype.ext (smul_mul' _ (m : M) m')
  smul_one q := by
    induction q using QuotientGroup.induction_on
    exact Subtype.ext (smul_one _)

@[simp]
theorem coe_mk_smul_fixedPoints (g : G) (m : FixedPoints.subgroup N M) :
    (((g : G ⧸ N) • m : FixedPoints.subgroup N M) : M) = g • (m : M) :=
  rfl

def inf : H2mul (G ⧸ N) (FixedPoints.subgroup N M) →* H2mul G M :=
  mapPair (QuotientGroup.mk' N) (FixedPoints.subgroup N M).subtype (fun _ _ => rfl)

@[simp]
theorem inf_mk (c : mulCocycles₂ (G ⧸ N) (FixedPoints.subgroup N M)) :
    inf N (mk _ _ c) =
      mk G M (mapCocycles₂ (QuotientGroup.mk' N) (FixedPoints.subgroup N M).subtype
        (fun _ _ => rfl) c) :=
  rfl

end ResInf

end H2mul

end H2mul

section Bridge

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

namespace H2mul

noncomputable def toH2Cocycles :
    mulCocycles₂ G M →* Multiplicative (H2 (Rep.ofMulDistribMulAction G M)) where
  toFun c := Multiplicative.ofAdd (H2π (Rep.ofMulDistribMulAction G M)
    (cocyclesOfIsMulCocycle₂ (f := (c : G × G → M)) c.2))
  map_one' := by
    have h0 : cocyclesOfIsMulCocycle₂ (f := ((1 : mulCocycles₂ G M) : G × G → M))
        (1 : mulCocycles₂ G M).2 = 0 := Subtype.ext rfl
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    rw [h0, map_zero]
  map_mul' c c' := by
    rw [← ofAdd_add]
    congr 1
    rw [← map_add]
    rfl

theorem toH2Cocycles_eq_one_iff (c : mulCocycles₂ G M) :
    toH2Cocycles c = 1 ↔ IsMulCoboundary₂ (c : G × G → M) := by
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0 ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, H2π_eq_zero_iff]
  constructor
  · intro h
    exact isMulCoboundary₂_of_mem_coboundaries₂ _ h
  · intro h
    exact (coboundariesOfIsMulCoboundary₂ h).2

noncomputable def mulEquivH2 :
    H2mul G M ≃* Multiplicative (H2 (Rep.ofMulDistribMulAction G M)) :=
  MulEquiv.ofBijective
    (QuotientGroup.lift _ toH2Cocycles (fun c hc => (toH2Cocycles_eq_one_iff c).2 hc)) (by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x
      induction x using induction_on with
      | h c =>
        intro hx
        exact (mk_eq_one_iff c).2 ((toH2Cocycles_eq_one_iff c).1 hx)
    · intro y
      induction y using Multiplicative.rec with
      | ofAdd y =>
      induction y using H2_induction_on with
      | h y =>
      exact ⟨mk G M ⟨Additive.toMul ∘ (y : G × G → Rep.ofMulDistribMulAction G M),
        isMulCocycle₂_of_mem_cocycles₂ _ y.2⟩, rfl⟩)

@[simp]
theorem mulEquivH2_mk (c : mulCocycles₂ G M) :
    mulEquivH2 (mk G M c) = Multiplicative.ofAdd (H2π (Rep.ofMulDistribMulAction G M)
      (cocyclesOfIsMulCocycle₂ (f := (c : G × G → M)) c.2)) :=
  rfl

end H2mul

end Bridge

end GroundTheory.Brauer
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open groupCohomology

universe u v

namespace CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}

theorem eq_single_of_mul_incl (σ : L ≃ₐ[K] L) (x : CrossedProduct hf)
    (hx : ∀ b : L, x * incl b = incl (σ b) * x) : x = single σ (x.coeff σ) := by
  have hzero : ∀ τ, τ ≠ σ → x.coeff τ = 0 := by
    intro τ hτ
    obtain ⟨b, hb⟩ : ∃ b, σ b ≠ τ b := by
      by_contra h
      push Not at h
      exact hτ (AlgEquiv.ext fun b => (h b).symm)
    have h : (incl (σ b) * x - x * incl b).coeff τ = 0 := by
      rw [hx b, sub_self]
      rfl
    rw [coeff_incl_mul_sub_mul_incl] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hb)
  rw [← incl_mul_u]
  exact eq_incl_mul_u_of_coeff_eq_zero x σ hzero

variable [FiniteDimensional K L] [IsGalois K L]

theorem isMulCoboundary₂_div_of_algEquiv {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) (e : CrossedProduct hf ≃ₐ[K] CrossedProduct hg) :
    IsMulCoboundary₂ (f / g) := by
  obtain ⟨a, ha⟩ := exists_unit_conj
    ((e : CrossedProduct hf →ₐ[K] CrossedProduct hg).comp incl) (incl : L →ₐ[K] CrossedProduct hg)

  set φ : CrossedProduct hf → CrossedProduct hg := fun y => (a : CrossedProduct hg) * e y * ↑a⁻¹
    with hφ
  have φmul : ∀ y z, φ (y * z) = φ y * φ z := by
    intro y z
    simp only [hφ, map_mul, mul_assoc, Units.inv_mul_cancel_left]
  have φone : φ 1 = 1 := by
    simp only [hφ, map_one, mul_one, Units.mul_inv]
  have φincl : ∀ b, φ (incl b) = incl b := fun b => (ha b).symm
  obtain ⟨c, hw⟩ : ∃ c : (L ≃ₐ[K] L) → L, ∀ σ, φ (u σ) = single σ (c σ) :=
    ⟨fun σ => (φ (u σ)).coeff σ, fun σ =>
      eq_single_of_mul_incl σ _ fun b => by rw [← φincl, ← φmul, u_mul_incl, φmul, φincl]⟩
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ h0
    obtain ⟨w, hw'⟩ := (isUnit_u σ (hf := hf)).exists_right_inv
    have h := congrArg φ hw'
    rw [φmul, φone, hw σ, h0, single_zero, zero_mul] at h
    exact zero_ne_one h
  have key : ∀ σ τ, c σ * σ (c τ) * g (σ, τ) = f (σ, τ) * c (σ * τ) := by
    intro σ τ
    have h := congrArg φ (u_mul_u (hf := hf) σ τ)
    simp only [φmul, φincl] at h
    rw [hw σ, hw τ, hw (σ * τ), single_mul_single, incl_mul_single] at h
    exact single_injective _ h
  refine ⟨fun σ => Units.mk0 (c σ) (hc0 σ), fun σ τ => ?_⟩
  ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, val_smul_units, Units.val_mk0, Pi.div_apply]
  rw [div_mul_eq_mul_div, div_eq_div_iff (hc0 _) (g (σ, τ)).ne_zero]
  linear_combination key σ τ

theorem isMulCoboundary₂_of_algEquiv_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsMulCocycle₂ f) (e : CrossedProduct hf ≃ₐ[K] Matrix ι ι K) : IsMulCoboundary₂ f := by
  have hcard : Fintype.card ι = Module.finrank K L := by
    have h1 := e.toLinearEquiv.finrank_eq
    rw [finrank_eq_sq, Module.finrank_matrix, Module.finrank_self, mul_one, ← sq] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  have h := isMulCoboundary₂_div_of_algEquiv hf isMulCocycle₂_one
    (e.trans ((Matrix.reindexAlgEquiv K K (Fintype.equivFinOfCardEq hcard)).trans
      (matrixEquiv isMulCocycle₂_one).symm))
  rwa [div_one] at h

end CrossedProduct

theorem nonempty_algEquiv_of_isBrauerEquivalent {K : Type u} [Field K] {A B : CSA.{u, v} K}
    (h : IsBrauerEquivalent A B) (hd : Module.finrank K A = Module.finrank K B) :
    Nonempty (A ≃ₐ[K] B) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨n, hn, D, _, _, _, ⟨eA⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  obtain ⟨m, hm, D', _, _, _, ⟨eB⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K B
  obtain ⟨φ⟩ := (isBrauerEquivalent_iff_nonempty_algEquiv eA eB).1 h
  have hdA := eA.toLinearEquiv.finrank_eq
  have hdB := eB.toLinearEquiv.finrank_eq
  rw [Module.finrank_matrix, Fintype.card_fin] at hdA hdB
  have hDD : Module.finrank K D = Module.finrank K D' := φ.toLinearEquiv.finrank_eq
  have hD0 : 0 < Module.finrank K D := Module.finrank_pos
  obtain rfl : n = m := by
    rw [hdA, hdB, ← hDD] at hd
    exact Nat.mul_self_inj.1 (Nat.eq_of_mul_eq_mul_right hD0 hd)
  exact ⟨eA.trans (φ.mapMatrix.trans eB.symm)⟩

namespace CrossedProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

theorem isBrauerEquivalent_one_one :
    IsBrauerEquivalent (csaOf K (CrossedProduct (isMulCocycle₂_one (K := K) (L := L))))
      (oneCSA K) := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  exact isBrauerEquivalent_of_algEquiv_matrix (C := K) (matrixEquiv isMulCocycle₂_one)
    (matrixFinOneAlgEquiv K).symm

theorem nonempty_algEquiv_of_isBrauerEquivalent {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g)
    (h : IsBrauerEquivalent (csaOf K (CrossedProduct hf)) (csaOf K (CrossedProduct hg))) :
    Nonempty (CrossedProduct hf ≃ₐ[K] CrossedProduct hg) :=
  GroundTheory.Brauer.nonempty_algEquiv_of_isBrauerEquivalent h
    (show Module.finrank K (CrossedProduct hf) = Module.finrank K (CrossedProduct hg) by
      rw [finrank_eq_sq, finrank_eq_sq])

theorem isMulCoboundary₂_of_isBrauerEquivalent_one (hf : IsMulCocycle₂ f)
    (h : IsBrauerEquivalent (csaOf K (CrossedProduct hf)) (oneCSA K)) : IsMulCoboundary₂ f := by
  obtain ⟨e⟩ := nonempty_algEquiv_of_isBrauerEquivalent hf isMulCocycle₂_one
    (h.trans (isBrauerEquivalent_one_one (L := L)).symm)
  have h' := isMulCoboundary₂_div_of_algEquiv hf isMulCocycle₂_one e
  rwa [div_one] at h'

theorem isMulCoboundary₂_of_mk_eq_one (hf : IsMulCocycle₂ f)
    (h : (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) = 1) : IsMulCoboundary₂ f :=
  isMulCoboundary₂_of_isBrauerEquivalent_one hf (Quotient.exact (h.trans BrauerGroup.one_def))

theorem mk_eq_one_of_isMulCoboundary₂ (hf : IsMulCocycle₂ f) (h : IsMulCoboundary₂ f) :
    (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) = 1 := by
  rw [BrauerGroup.one_def]
  refine Quotient.sound (IsBrauerEquivalent.trans ?_ (isBrauerEquivalent_one_one (L := L)))
  refine isBrauerEquivalent_of_algEquiv
    (A := csaOf K (CrossedProduct hf)) (B := csaOf K (CrossedProduct (isMulCocycle₂_one (K := K)
      (L := L)))) (equivOfIsMulCoboundary₂ hf isMulCocycle₂_one ?_)
  rw [one_div]
  exact isMulCoboundary₂_inv h

end CrossedProduct

theorem isMulCocycle₂_of_mem {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (c : mulCocycles₂ G M) : IsMulCocycle₂ (c : G × G → M) := c.2

namespace H2mul

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def toBrauer : H2mul (L ≃ₐ[K] L) Lˣ → BrauerGroup.{u, u} K :=
  Quotient.lift (fun c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ => ⟦csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))⟧)
    (fun c c' h => by
      have h' : mk _ _ c = mk _ _ c' := Quotient.sound h
      rw [mk_eq_mk_iff] at h'
      exact Quotient.sound (isBrauerEquivalent_of_algEquiv
        (A := csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))) (B := csaOf K (CrossedProduct (isMulCocycle₂_of_mem c')))
        (CrossedProduct.equivOfIsMulCoboundary₂ (isMulCocycle₂_of_mem c') (isMulCocycle₂_of_mem c) h').symm))

variable {K L}

@[simp]
theorem toBrauer_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    toBrauer K L (mk _ _ c) = ⟦csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))⟧ := rfl

theorem toBrauer_injective : Function.Injective (toBrauer K L) := by
  intro x y hxy
  induction x using H2mul.induction_on with
  | h c =>
  induction y using H2mul.induction_on with
  | h c' =>
  rw [toBrauer_mk, toBrauer_mk] at hxy
  obtain ⟨e⟩ := CrossedProduct.nonempty_algEquiv_of_isBrauerEquivalent
    (isMulCocycle₂_of_mem c) (isMulCocycle₂_of_mem c') (Quotient.exact hxy)
  exact (mk_eq_mk_iff c c').2 (CrossedProduct.isMulCoboundary₂_div_of_algEquiv _ _ e)

theorem toBrauer_eq_one_iff (x : H2mul (L ≃ₐ[K] L) Lˣ) : toBrauer K L x = 1 ↔ x = 1 := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [toBrauer_mk, mk_eq_one_iff]
  exact ⟨CrossedProduct.isMulCoboundary₂_of_mk_eq_one (isMulCocycle₂_of_mem c),
    CrossedProduct.mk_eq_one_of_isMulCoboundary₂ (isMulCocycle₂_of_mem c)⟩

theorem toBrauer_one : toBrauer K L (1 : H2mul (L ≃ₐ[K] L) Lˣ) = 1 :=
  (toBrauer_eq_one_iff _).2 rfl

end H2mul

end GroundTheory.Brauer

end
end
