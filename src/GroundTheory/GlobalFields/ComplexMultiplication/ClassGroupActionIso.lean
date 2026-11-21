import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicIsogeny
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariant

section
open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L₁ L₂ : PeriodPair}

theorem homConst_ne_zero {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)} (hQ : Q ≠ 0) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ≠ 0 := by
  set φ := isogOfHom Q hQ
  have hsep : φ.IsSeparable := by
    have := φ.finiteDimensional
    exact Algebra.IsSeparable.of_integral _ _
  have h1 := (isSeparable_iff_isogConst_ne_zero φ).1 hsep
  have h2 : isogConst φ = homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q := by
    apply (algebraMap ℂ (weierstrassCurve L₁).toAffine.FunctionField).injective
    rw [algebraMap_isogConst, algebraMap_homConst]
    rfl
  rwa [← h2]

theorem homConst_injective :
    Function.Injective (homConst (weierstrassCurve L₁) (weierstrassCurve L₂)) := by
  rw [injective_iff_map_eq_zero]
  intro Q h
  by_contra hQ
  exact homConst_ne_zero hQ h

theorem exists_eq_constMap_of_omegaDeriv {W : WeierstrassCurve ℂ}
    (P : (W.baseChange MeroField).toAffine.Point) (h : omegaDeriv (omegaAt W P) = 0) :
    ∃ R : W.toAffine.Point, P = constMap W MeroField R := by
  rcases P with _ | ⟨u, v, hP⟩
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨s₁, s₂⟩ := omegaAt_some_spec W hP
  have e₁ := congrArg omegaDeriv s₁
  have e₂ := congrArg omegaDeriv s₂
  rw [LinearMap.map_smul, h, smul_eq_mul, mul_zero, omegaDeriv_D, eq_comm] at e₁ e₂
  obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₁
  obtain ⟨d, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₂
  have hcd : W.toAffine.Nonsingular c d :=
    (W.toAffine.baseChange_nonsingular (f := Algebra.ofId ℂ MeroField)
      (algebraMap ℂ MeroField).injective c d).1 hP
  exact ⟨.some c d hcd, rfl⟩

theorem exists_map_ellEval_eq {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)}
    (hQ : Q ≠ 0) :
    ∃ c : ℂ, Point.map (ellEval L₁) Q.1 =
      affinePoint L₂ (homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q) c
        (homConst_ne_zero hQ) := by
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  have e := omegaAt_eq_homConst_smul Q
  have e' := congrArg (kpush (ellEval L₁)) e
  rw [kpush_omegaAt, kpush_const_smul, invariantDifferential, kpush_omegaAt,
    map_ellEval_genericPoint, basePoint_eq] at e'
  have hω : omegaDeriv (omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1)) =
      algebraMap ℂ MeroField α := by
    rw [e', ← algebraMap_smul MeroField, LinearMap.map_smul, omegaDeriv_affinePoint, smul_eq_mul,
      map_one, mul_one]
  have hD : omegaDeriv (omegaAt (weierstrassCurve L₂)
      (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0)) = 0 := by
    have h1 : omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0) =
        omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1) -
          omegaAt (weierstrassCurve L₂) (affinePoint L₂ α 0 h0) :=
      map_sub (omegaHom (weierstrassCurve L₂)) _ _
    rw [h1, map_sub, hω, omegaDeriv_affinePoint, sub_self]
  obtain ⟨R, hR⟩ := exists_eq_constMap_of_omegaDeriv _ hD
  obtain ⟨c, rfl⟩ := toPoint_surjective (L := L₂) R
  refine ⟨0 + c, ?_⟩
  rw [← affinePoint_add_constMap, ← hR]
  abel

theorem homConst_mem_latticeHom (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ∈ latticeHom L₁ L₂ := by
  by_cases hQ : Q = 0
  · rw [hQ, map_zero]
    exact zero_mem _
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  obtain ⟨c, hc⟩ := exists_map_ellEval_eq hQ
  have hg : IsGenPt (weierstrassCurve L₂) Q.1 := isGenPt_of_mem_isogHom Q.2 (fun h ↦ hQ (Subtype.ext h))
  obtain ⟨hne, hQs⟩ := eq_some_xOf_yOf _ (isGenPt_ne_zero _ hg)
  rw [hQs, Point.map_some, affinePoint, Point.some.injEq] at hc
  obtain ⟨f, hf, hfe⟩ := exists_isEllipticFunction_ellEval_eq L₁ (xOf _ Q.1)
  obtain ⟨g, hg', hge⟩ := exists_isEllipticFunction_ellEval_eq L₁ (yOf _ Q.1)
  rw [hfe, germ_eq_germ_iff hf.1 (meromorphic_weierstrassP_affine L₂ α c)] at hc
  rw [hge, germ_eq_germ_iff hg'.1 (meromorphic_derivWeierstrassP_half_affine L₂ α c)] at hc
  obtain ⟨hcx, hcy⟩ := hc
  intro l hl
  obtain ⟨z, h1, h2, h3, h4, h5, h6⟩ := nonempty_of_mem_codiscrete (hcx.and (hcy.and
    ((eventually_affine hcx one_ne_zero l).and ((eventually_affine hcy one_ne_zero l).and
    ((eventually_affine (eventually_notMem_lattice L₂) h0 c).and
    (eventually_affine (eventually_notMem_lattice L₂) h0 (α * l + c)))))))
  beta_reduce at h1 h2
  simp only [one_mul] at h3 h4
  rw [hf.2 z l hl] at h3
  rw [hg'.2 z l hl] at h4
  have e₁ : ℘[L₂] (α * z + (α * l + c)) = ℘[L₂] (α * z + c) := by
    rw [← h1, h3, show α * (z + l) + c = α * z + (α * l + c) by ring]
  have e₂ : ℘'[L₂] (α * z + (α * l + c)) = ℘'[L₂] (α * z + c) := by
    have := h2.symm.trans h4
    rw [show α * (z + l) + c = α * z + (α * l + c) by ring] at this
    linear_combination 2 * this.symm
  have hpt : toPoint L₂ (α * z + (α * l + c)) = toPoint L₂ (α * z + c) := by
    rw [toPoint_of_notMem h6, toPoint_of_notMem h5]
    exact point_some_congr e₁ (by rw [e₂])
  have := torusToPoint_injective (L := L₂) (a₁ := Torus.mk L₂ _) (a₂ := Torus.mk L₂ _) hpt
  rw [Torus.mk_eq_mk_iff] at this
  simpa using this

theorem latticeToHom_homConst (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    latticeToHom ⟨_, homConst_mem_latticeHom Q⟩ = Q :=
  homConst_injective (by rw [homConst_latticeToHom])

theorem latticeToHom_add (α β : latticeHom L₁ L₂) :
    latticeToHom (α + β) = latticeToHom α + latticeToHom β :=
  homConst_injective (by
    rw [map_add, homConst_latticeToHom, homConst_latticeToHom, homConst_latticeToHom]
    rfl)

theorem ellEval_comp_translate (L : PeriodPair) (z : ℂ) :
    (ellEval L).comp (translate (weierstrassCurve L) (toPoint L z)) =
      (affineComp 1 z one_ne_zero).comp (ellEval L) := by
  apply algHom_eq_of_map_genericPoint' (E := weierstrassCurve L)
  rw [← Point.map_map, map_translate_genericPoint, map_add, map_ellEval_genericPoint,
    show constPoint (weierstrassCurve L) (toPoint L z) =
      constMap (weierstrassCurve L) _ (toPoint L z) from rfl, map_constMap, basePoint_eq,
    affinePoint_add_constMap, ← Point.map_map, map_ellEval_genericPoint, basePoint_eq,
    map_affineComp_affinePoint]
  exact affinePoint_congr L _ _ (by ring) (by ring)

theorem homPt_latticeToHom (α : latticeHom L₁ L₂) (z : ℂ) :
    homPt (latticeToHom α) (toPoint L₁ z) = toPoint L₂ (α * z) := by
  by_cases h0 : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α h0, homPt_zero, AddMonoidHom.zero_apply, h0, zero_mul,
      toPoint_zero]
  apply homPt_eq_of
  apply Point.map_injective (ellEval L₁)
  rw [Point.map_map, ellEval_comp_translate, ← Point.map_map, latticeToHom_of_ne_zero α h0,
    map_ellEval_isogPt, map_affineComp_affinePoint, map_add, map_ellEval_isogPt, map_constMap,
    affinePoint_add_constMap]
  exact affinePoint_congr L₂ _ _ (by ring) (by ring)

section End

variable {L : PeriodPair}

theorem latticeToHom_mul (α β : latticeHom L L) (h : (α : ℂ) * β ∈ latticeHom L L) :
    latticeToHom ⟨_, h⟩ = latticeToHom α * latticeToHom β := by
  by_cases hα : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α hα, zero_mul, latticeToHom_of_eq_zero _ (by simp [hα])]
  by_cases hβ : (β : ℂ) = 0
  · rw [latticeToHom_of_eq_zero β hβ, mul_zero, latticeToHom_of_eq_zero _ (by simp [hβ])]
  have hg : IsGenPt (weierstrassCurve L) (latticeToHom β).1 := by
    rw [latticeToHom_of_ne_zero β hβ]
    exact isGenPt_isogPt _ _
  apply Subtype.ext
  apply Point.map_injective (ellEval L)
  have e : Point.map (ellEval L) (latticeToHom β).1 = affinePoint L β 0 hβ := by
    rw [latticeToHom_of_ne_zero β hβ, map_ellEval_isogPt]
  rw [isogEnd_mul_def, homComp_of_isGenPt _ _ hg, Point.map_map, ← genEval_map _ (ellEval L) hg,
    genEval_congr _ e _ (isGenPt_affinePoint L β 0 hβ), genEval_affinePoint, ← Point.map_map,
    latticeToHom_of_ne_zero α hα, map_ellEval_isogPt, map_affineComp_affinePoint,
    latticeToHom_of_ne_zero _ (mul_ne_zero hα hβ), map_ellEval_isogPt]
  exact affinePoint_congr L _ _ rfl (by ring)

end End

end Elliptic
end GroundTheory.Global
end
end

section
open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L₁ L₂ : PeriodPair}

variable (L₁ L₂) in

def latticeHomEquiv : latticeHom L₁ L₂ ≃+ isogHom (weierstrassCurve L₁) (weierstrassCurve L₂) where
  toFun := latticeToHom
  invFun Q := ⟨_, homConst_mem_latticeHom Q⟩
  left_inv α := Subtype.ext (homConst_latticeToHom α)
  right_inv Q := latticeToHom_homConst Q
  map_add' := latticeToHom_add

theorem homPt_latticeHomEquiv (α : latticeHom L₁ L₂) (z : ℂ) :
    homPt (latticeHomEquiv L₁ L₂ α) (toPoint L₁ z) = toPoint L₂ (α * z) :=
  homPt_latticeToHom α z

variable (L : PeriodPair)

def latticeEnd : Subring ℂ where
  carrier := {α | ∀ l ∈ L.lattice, α * l ∈ L.lattice}
  add_mem' ha hb := (latticeHom L L).add_mem ha hb
  zero_mem' := (latticeHom L L).zero_mem
  neg_mem' ha := (latticeHom L L).neg_mem ha
  one_mem' l hl := by rwa [one_mul]
  mul_mem' {a b} ha hb l hl := by
    rw [mul_assoc]
    exact ha _ (hb l hl)

def latticeEndEquiv : latticeEnd L ≃+* isogEnd (weierstrassCurve L) where
  toFun α := latticeToHom ⟨α, α.2⟩
  invFun Q := ⟨homConst (weierstrassCurve L) (weierstrassCurve L) Q, homConst_mem_latticeHom Q⟩
  left_inv _ := Subtype.ext (homConst_latticeToHom _)
  right_inv Q := latticeToHom_homConst Q
  map_mul' α β := latticeToHom_mul ⟨α, α.2⟩ ⟨β, β.2⟩ (α * β).2
  map_add' α β := latticeToHom_add ⟨α, α.2⟩ ⟨β, β.2⟩

theorem homConst_latticeEndEquiv (α : latticeEnd L) :
    homConst (weierstrassCurve L) (weierstrassCurve L) (latticeEndEquiv L α) = α :=
  homConst_latticeToHom _

variable {L}

def mulLattice (α : latticeHom L₁ L₂) : AddSubgroup L₂.lattice where
  carrier := {w | ∃ l ∈ L₁.lattice, (w : ℂ) = α * l}
  add_mem' := by
    rintro a b ⟨l, hl, ha⟩ ⟨l', hl', hb⟩
    exact ⟨l + l', add_mem hl hl', by rw [Submodule.coe_add, ha, hb, mul_add]⟩
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    rintro a ⟨l, hl, ha⟩
    exact ⟨-l, neg_mem hl, by rw [Submodule.coe_neg, ha, mul_neg]⟩

theorem mem_mulLattice {α : latticeHom L₁ L₂} {w : L₂.lattice} :
    w ∈ mulLattice α ↔ ∃ l ∈ L₁.lattice, (w : ℂ) = α * l :=
  Iff.rfl

def kerMap (α : latticeHom L₁ L₂) (h0 : (α : ℂ) ≠ 0) :
    L₂.lattice →+ (homPt (latticeHomEquiv L₁ L₂ α)).ker where
  toFun w := ⟨toPoint L₁ (w / α), by
    rw [AddMonoidHom.mem_ker, homPt_latticeHomEquiv, mul_div_cancel₀ _ h0]
    exact toPoint_of_mem w.2⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Subtype.ext
    simp only [Submodule.coe_add, add_div, AddMemClass.mk_add_mk, toPoint_add]

theorem kerMap_surjective (α : latticeHom L₁ L₂) (h0 : (α : ℂ) ≠ 0) :
    Function.Surjective (kerMap α h0) := by
  rintro ⟨P, hP⟩
  obtain ⟨z, rfl⟩ := toPoint_surjective (L := L₁) P
  rw [AddMonoidHom.mem_ker, homPt_latticeHomEquiv, toPoint_eq_zero_iff] at hP
  refine ⟨⟨_, hP⟩, Subtype.ext ?_⟩
  show toPoint L₁ (α * z / α) = toPoint L₁ z
  rw [mul_div_cancel_left₀ _ h0]

theorem ker_kerMap (α : latticeHom L₁ L₂) (h0 : (α : ℂ) ≠ 0) :
    (kerMap α h0).ker = mulLattice α := by
  ext w
  rw [AddMonoidHom.mem_ker, mem_mulLattice]
  constructor
  · intro h
    have h' : toPoint L₁ (w / α) = 0 := congrArg Subtype.val h
    rw [toPoint_eq_zero_iff] at h'
    exact ⟨_, h', by rw [mul_div_cancel₀ _ h0]⟩
  · rintro ⟨l, hl, hw⟩
    apply Subtype.ext
    show toPoint L₁ (w / α) = 0
    rw [hw, mul_div_cancel_left₀ _ h0]
    exact toPoint_of_mem hl

end Elliptic
end GroundTheory.Global
end
end

section
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem tendsto_E₄_atImInfty : Tendsto (fun τ : ℍ ↦ E₄ τ) atImInfty (𝓝 1) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero (f := E₄) one_pos
    one_mem_strictPeriods_SL
  have h0 : cuspFunction 1 E₄ 0 = 1 := by
    have := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    simpa [qExpansion_coeff] using this
  have hcomp : ∀ τ : ℍ, cuspFunction 1 E₄ (Function.Periodic.qParam 1 τ) = E₄ τ := fun τ ↦
    SlashInvariantFormClass.eq_cuspFunction E₄ τ one_mem_strictPeriods_SL one_ne_zero
  have := ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)
  rw [h0] at this
  exact this.congr hcomp

theorem tendsto_discriminant_atImInfty :
    Tendsto (fun τ : ℍ ↦ ModularForm.discriminant τ) atImInfty (𝓝 0) :=
  ModularForm.discriminant_isZeroAtImInfty

theorem eventually_le_norm_modularJ (R : ℝ) : ∀ᶠ τ in atImInfty, R ≤ ‖modularJ τ‖ := by
  have h1 : ∀ᶠ τ in atImInfty, (1 / 2 : ℝ) ≤ ‖E₄ τ‖ :=
    tendsto_E₄_atImInfty.norm.eventually (Ici_mem_nhds (by norm_num))
  have hc : (0 : ℝ) < 1 / (8 * (|R| + 1)) := by positivity
  have h2 : ∀ᶠ τ in atImInfty, ‖ModularForm.discriminant τ‖ < 1 / (8 * (|R| + 1)) :=
    tendsto_discriminant_atImInfty.norm.eventually (Iio_mem_nhds (by simpa using hc))
  filter_upwards [h1, h2] with τ h1 h2
  have hpos : 0 < ‖ModularForm.discriminant τ‖ :=
    norm_pos_iff.2 (ModularForm.discriminant_ne_zero τ)
  rw [modularJ, norm_div, norm_pow, le_div_iff₀ hpos]
  have hR : R ≤ |R| + 1 := by linarith [le_abs_self R]
  have h3 : (|R| + 1) * ‖ModularForm.discriminant τ‖ ≤ 1 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at h2
    linarith
  have h4 : (1 / 2 : ℝ) ^ 3 ≤ ‖E₄ τ‖ ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  nlinarith

theorem exists_le_norm_modularJ (R : ℝ) : ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → R ≤ ‖modularJ τ‖ :=
  (atImInfty_mem _).1 (eventually_le_norm_modularJ R)

def modularJC (z : ℂ) : ℂ := modularJ (ofComplex z)

lemma modularJC_coe (τ : ℍ) : modularJC τ = modularJ τ := by
  rw [modularJC, ofComplex_apply]

lemma differentiableOn_modularJC : DifferentiableOn ℂ modularJC {z : ℂ | 0 < z.im} := by
  have h4 : DifferentiableOn ℂ ((fun τ : ℍ ↦ E₄ τ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo E₄)
  have hΔ : DifferentiableOn ℂ ((fun τ : ℍ ↦ ModularForm.discriminant τ) ∘ ofComplex)
      {z : ℂ | 0 < z.im} := by
    have := UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo CuspForm.discriminant)
    simpa [CuspForm.coe_discriminant] using this
  refine (h4.pow 3).div hΔ fun z _ ↦ ModularForm.discriminant_ne_zero _

lemma analyticOnNhd_modularJC : AnalyticOnNhd ℂ modularJC {z : ℂ | 0 < z.im} :=
  differentiableOn_modularJC.analyticOnNhd isOpen_upperHalfPlaneSet

lemma range_modularJ : range modularJ = modularJC '' {z : ℂ | 0 < z.im} := by
  ext w
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ, τ.im_pos, modularJC_coe τ⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ofComplex z, rfl⟩

lemma not_exists_modularJC_const : ¬ ∃ w, ∀ z ∈ {z : ℂ | 0 < z.im}, modularJC z = w := by
  rintro ⟨w, hw⟩
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  let τ : ℍ := ⟨(|A| + 1) * Complex.I, by simp; positivity⟩
  have hτ : A ≤ τ.im := by
    show A ≤ ((|A| + 1) * Complex.I).im
    simp
    linarith [le_abs_self A]
  have h1 := hA τ hτ
  rw [← modularJC_coe, hw _ τ.im_pos] at h1
  linarith

def fdBelow (A : ℝ) : Set ℂ :=
  {z | 1 ≤ normSq z ∧ |z.re| ≤ 1 / 2 ∧ 0 ≤ z.im ∧ z.im ≤ A}

lemma im_pos_of_mem_fdBelow {A : ℝ} {z : ℂ} (hz : z ∈ fdBelow A) : 0 < z.im := by
  obtain ⟨h1, h2, h3, -⟩ := hz
  rw [normSq_apply] at h1
  have hre : z.re * z.re ≤ 1 / 4 := by
    have := abs_le.1 h2
    nlinarith
  rcases h3.lt_or_eq with h | h
  · exact h
  · rw [← h] at h1
    nlinarith

lemma isCompact_fdBelow (A : ℝ) : IsCompact (fdBelow A) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_normSq).inter
      ((isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / 2 + |A|)).subset fun z hz ↦ ?_
    obtain ⟨-, h2, h3, h4⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
      _ ≤ 1 / 2 + |A| :=
        add_le_add h2 (by rw [abs_of_nonneg h3]; exact h4.trans (le_abs_self A))

lemma isOpen_range_modularJ : IsOpen (range modularJ) := by
  rw [range_modularJ]
  rcases analyticOnNhd_modularJC.is_constant_or_isOpen
      (convex_halfSpace_im_gt 0).isPreconnected with h | h
  · exact absurd h not_exists_modularJC_const
  · exact h _ subset_rfl isOpen_upperHalfPlaneSet

lemma isClosed_range_modularJ : IsClosed (range modularJ) := by
  refine closure_subset_iff_isClosed.1 fun w hw ↦ ?_
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  have hK : IsCompact (modularJC '' fdBelow A) :=
    (isCompact_fdBelow A).image_of_continuousOn
      (differentiableOn_modularJC.continuousOn.mono fun z hz ↦ im_pos_of_mem_fdBelow hz)
  have hsub : range modularJ ⊆ modularJC '' fdBelow A ∪ {y | ‖w‖ + 1 ≤ ‖y‖} := by
    rintro _ ⟨τ, rfl⟩
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    rw [← modularJ_smul g τ]
    by_cases him : A ≤ (g • τ).im
    · exact Or.inr (hA _ him)
    · refine Or.inl ⟨(g • τ : ℍ), ⟨hg.1, hg.2, (g • τ).im_pos.le, ?_⟩, modularJC_coe _⟩
      exact (not_le.1 him).le
  have hclosed : IsClosed (modularJC '' fdBelow A ∪ {y : ℂ | ‖w‖ + 1 ≤ ‖y‖}) :=
    hK.isClosed.union (isClosed_le continuous_const continuous_norm)
  rcases closure_minimal hsub hclosed hw with h | h
  · obtain ⟨z, hz, rfl⟩ := h
    exact ⟨ofComplex z, rfl⟩
  · have h' : ‖w‖ + 1 ≤ ‖w‖ := h
    linarith

theorem modularJ_surjective : Function.Surjective modularJ := by
  have h : range modularJ = univ :=
    IsClopen.eq_univ ⟨isClosed_range_modularJ, isOpen_range_modularJ⟩ (range_nonempty _)
  exact Set.range_eq_univ.1 h

theorem exists_variableChange_eq_weierstrassCurve_latticeOfTau (W : WeierstrassCurve ℂ)
    [W.IsElliptic] :
    ∃ τ : ℍ, ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = weierstrassCurve (latticeOfTau τ) := by
  obtain ⟨τ, hτ⟩ := modularJ_surjective W.j
  refine ⟨τ, W.exists_variableChange_of_j_eq _ ?_⟩
  rw [weierstrassCurve_latticeOfTau_j, hτ]

theorem exists_variableChange_eq_weierstrassCurve (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ L : PeriodPair, ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = weierstrassCurve L := by
  obtain ⟨τ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve_latticeOfTau W
  exact ⟨latticeOfTau τ, C, hC⟩

end Elliptic
end GroundTheory.Global
end
end

section
open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

universe u

section Points

variable {F : Type u} [Field F] (C : VariableChange F) {E E' : WeierstrassCurve F}

theorem baseChange_smul_eq (L : Type*) [Field L] [Algebra F L] (h : C • E = E') :
    C.baseChange L • E.baseChange L = E'.baseChange L := by
  subst h
  exact map_variableChange _ _ _

theorem map_vcPoint {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L'] [DecidableEq L]
    [DecidableEq L'] (f : L →ₐ[F] L') (h : C • E = E') (P : (E.baseChange L).toAffine.Point) :
    Point.map f (vcPoint (C.baseChange L) (baseChange_smul_eq C L h) P) =
      vcPoint (C.baseChange L') (baseChange_smul_eq C L' h) (Point.map f P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rw [vcPoint_some, Point.map_some, Point.map_some, vcPoint_some, Point.some.injEq]
    have hC : (C.baseChange L).map (f : L →+* L') = C.baseChange L' :=
      VariableChange.map_baseChange C f
    constructor
    · have := map_vcX (C.baseChange L) (f : L →+* L') x
      rw [hC] at this
      exact this
    · have := map_vcY (C.baseChange L) (f : L →+* L') x y
      rw [hC] at this
      exact this

theorem vcPoint_vcPoint_of_eq_inv {L : Type*} [Field L] {W W₂ : WeierstrassCurve L}
    (D D' : VariableChange L) (hD : D' = D⁻¹) (h₁ : D • W = W₂) (h₂ : D' • W₂ = W)
    (P : W.toAffine.Point) : vcPoint D' h₂ (vcPoint D h₁ P) = P := by
  subst hD
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rw [vcPoint_some, vcPoint_some, Point.some.injEq]
    have hu := D.u.inv_mul
    simp only [vcX, vcY, VariableChange.inv_def, inv_inv]
    constructor
    · linear_combination x * (((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu
    · linear_combination y * ((((D.u⁻¹ : Lˣ) : L) * D.u) ^ 2 + ((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu

theorem vcPoint_eq_zero_iff {L : Type*} [Field L] {W W₂ : WeierstrassCurve L} (D : VariableChange L)
    (h : D • W = W₂) {P : W.toAffine.Point} : vcPoint D h P = 0 ↔ P = 0 := by
  constructor
  · intro e
    exact vcPoint_injective D h (e.trans (vcPoint_zero D h).symm)
  · rintro rfl
    rfl

end Points

section Hom

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] (C : VariableChange F)
  {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

def vcPt (h : C • E = E') : (E'.baseChange E.toAffine.FunctionField).toAffine.Point :=
  vcPoint (C.baseChange _) (baseChange_smul_eq C _ h) (genericPoint E)

theorem respectsAdd_vcPt (h : C • E = E') : RespectsAdd E E' (vcPt C h) := by
  intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ h₁ h₂ h₃ t₁ t₂ t₃ hs
  simp only [ratMapValue, vcPt]
  rw [map_vcPoint C _ h, map_vcPoint C _ h, map_vcPoint C _ h, map_liftPoint_genericPoint E h₁ t₁,
    map_liftPoint_genericPoint E h₂ t₂, map_liftPoint_genericPoint E h₃ t₃, ← vcPoint_add, hs]

def vcHom (h : C • E = E') : isogHom E E' := ⟨vcPt C h, respectsAdd_vcPt C h⟩

theorem vcPt_ne_zero (h : C • E = E') : vcPt C h ≠ 0 := by
  rw [vcPt, Ne, vcPoint_eq_zero_iff]
  exact isGenPt_ne_zero E isGenPt_genericPoint

theorem isGenPt_vcHom (h : C • E = E') : IsGenPt E' (vcHom C h).1 :=
  isGenPt_of_mem_isogHom (vcHom C h).2 (vcPt_ne_zero C h)

theorem map_vcHom {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (g : E.toAffine.FunctionField →ₐ[F] L) (h : C • E = E') :
    Point.map g (vcHom C h).1 =
      vcPoint (C.baseChange L) (baseChange_smul_eq C L h) (Point.map g (genericPoint E)) :=
  map_vcPoint C g h (genericPoint E)

omit [IsAlgClosed F] [DecidableEq F] [E.IsElliptic] [E'.IsElliptic] in
theorem inv_smul_eq_of_smul_eq (h : C • E = E') : C⁻¹ • E' = E := by
  rw [← h, inv_smul_smul]

theorem homComp_vcHom_vcHom (D : VariableChange F) (hD : D = C⁻¹) (h : C • E = E')
    (h' : D • E' = E) : homComp (vcHom D h') (vcHom C h) = homId := by
  apply Subtype.ext
  rw [homComp_of_isGenPt _ _ (isGenPt_vcHom C h)]
  rw [map_vcHom, map_genEval_genericPoint]
  have hD' : D.baseChange E.toAffine.FunctionField = (C.baseChange E.toAffine.FunctionField)⁻¹ := by
    subst hD
    exact map_inv (VariableChange.mapHom (algebraMap F E.toAffine.FunctionField)) C
  exact vcPoint_vcPoint_of_eq_inv _ _ hD' (baseChange_smul_eq C _ h) (baseChange_smul_eq D _ h')
    (genericPoint E)

def vcEndEquiv (h : C • E = E') : isogEnd E ≃+* isogEnd E' where
  toFun f := homComp (vcHom C h) (homComp f (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)))
  invFun g := homComp (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)) (homComp g (vcHom C h))
  left_inv f := by
    simp only [homComp_assoc, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h),
      homComp_id_right]
    rw [← homComp_assoc, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h),
      homComp_id_left]
  right_inv g := by
    simp only [homComp_assoc,
      homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homComp_id_right]
    rw [← homComp_assoc,
      homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homComp_id_left]
  map_mul' f g := by
    simp only [isogEnd_mul_def, homComp_assoc]
    rw [← homComp_assoc (vcHom C⁻¹ _) (vcHom C h),
      homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h), homComp_id_left]
  map_add' f g := by
    rw [homComp_add_left, homComp_add_right]

theorem vcEndEquiv_apply (h : C • E = E') (f : isogEnd E) :
    vcEndEquiv C h f = homComp (vcHom C h) (homComp f (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))) :=
  rfl

end Hom

section Const

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem homConst_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homConst E E'' (homComp R Q) = homConst E' E'' R * homConst E E' Q := by
  by_cases hQ : IsGenPt E' Q.1
  · set g := genEval E' Q.1 hQ
    have key : algebraMap F E.toAffine.FunctionField (homConst E' E'' R * homConst E E' Q) •
        invariantDifferential E = omegaAt E'' (homComp R Q).1 := by
      rw [homComp_of_isGenPt _ _ hQ, ← kpush_omegaAt, omegaAt_eq_homConst_smul,
        ← algebraMap_smul E'.toAffine.FunctionField (homConst E' E'' R) (invariantDifferential E'),
        kpush_smul, AlgHom.commutes,
        show invariantDifferential E' = omegaAt E' (genericPoint E') from rfl, kpush_omegaAt, map_genEval_genericPoint,
        omegaAt_eq_homConst_smul, ← algebraMap_smul E.toAffine.FunctionField (homConst E E' Q),
        smul_smul, ← map_mul]
    apply (algebraMap F E.toAffine.FunctionField).injective
    rw [algebraMap_homConst]
    have h2 := homCoeff_smul (homComp R Q)
    rw [← key] at h2
    exact smul_left_injective _ (invariantDifferential_ne_zero E) h2
  · rw [eq_zero_of_not_isGenPt Q hQ, homComp_zero_right, map_zero, map_zero, mul_zero]

theorem homConst_homId : homConst E E (homId : isogEnd E) = 1 := by
  apply (algebraMap F E.toAffine.FunctionField).injective
  rw [algebraMap_homConst, map_one]
  exact invCoeff_invariantDifferential E

variable (E) in

def endConst : isogEnd E →+* F where
  toFun := homConst E E
  map_one' := homConst_homId
  map_mul' f g := homConst_homComp f g
  map_zero' := map_zero _
  map_add' := map_add _

theorem endConst_apply (f : isogEnd E) : endConst E f = homConst E E f := rfl

theorem endConst_vcEndEquiv (C : VariableChange F) (h : C • E = E') (f : isogEnd E) :
    endConst E' (vcEndEquiv C h f) = endConst E f := by
  have e := homConst_homComp (vcHom C h) (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))
  rw [homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h,
    homConst_homId] at e
  rw [endConst_apply, endConst_apply, vcEndEquiv_apply, homConst_homComp, homConst_homComp]
  linear_combination (-(homConst E E f)) * e

end Const

section Complex

variable {E : WeierstrassCurve ℂ} [E.IsElliptic]

theorem endConst_latticeEndEquiv (L : PeriodPair) (α : latticeEnd L) :
    endConst (weierstrassCurve L) (latticeEndEquiv L α) = α :=
  homConst_latticeEndEquiv L α

theorem range_endConst_weierstrassCurve (L : PeriodPair) :
    (endConst (weierstrassCurve L)).range = latticeEnd L := by
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨α, rfl⟩ := (latticeEndEquiv L).surjective f
    rw [endConst_latticeEndEquiv]
    exact α.2
  · intro hz
    exact ⟨latticeEndEquiv L ⟨z, hz⟩, endConst_latticeEndEquiv L ⟨z, hz⟩⟩

theorem endConst_injective : Function.Injective (endConst E) := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_weierstrassCurve E
  intro f g hfg
  apply (vcEndEquiv C hC).injective
  apply (latticeEndEquiv L).symm.injective
  apply Subtype.ext
  have hf := endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC f))
  have hg := endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC g))
  rw [RingEquiv.apply_symm_apply, endConst_vcEndEquiv] at hf hg
  rw [← hf, ← hg, hfg]

theorem range_endConst {L : PeriodPair} {C : VariableChange ℂ} (hC : C • E = weierstrassCurve L) :
    (endConst E).range = latticeEnd L := by
  rw [← range_endConst_weierstrassCurve]
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨vcEndEquiv C hC f, endConst_vcEndEquiv C hC f⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨f, rfl⟩ := (vcEndEquiv C hC).surjective g
    exact ⟨f, (endConst_vcEndEquiv C hC f).symm⟩

end Complex

end Elliptic
end GroundTheory.Global
end
end
