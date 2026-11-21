import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveAdelic
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveBase
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleDual
import GroundTheory.FunctionField.WeilDifferential
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveFunctionField

section
open CategoryTheory AlgebraicGeometry Order Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

theorem isNoetherian_of_finiteType {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] : IsNoetherian X := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  exact ⟨⟩

theorem isLocallyFactorial_of_dim_le_one {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (hX : topologicalKrullDim X ≤ 1) : IsLocallyFactorial X := by
  refine ⟨fun x => ?_⟩
  by_cases hx : x = genericPoint X
  · subst hx
    change UniqueFactorizationMonoid X.functionField
    infer_instance
  · let Z : PrimeDivisor X := ⟨x, ringKrullDim_stalk_eq_one hX hx⟩
    have : IsDedekindDomain (X.presheaf.stalk x) := Z.isDedekindDomain_stalk
    have : IsPrincipalIdealRing (X.presheaf.stalk x) := by
      refine IsPrincipalIdealRing.of_finite_maximals ?_
      refine (Set.finite_singleton (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).subset ?_
      intro I hI
      exact IsLocalRing.eq_maximalIdeal hI
    infer_instance

end GroundTheory.Arith.SchemeCoh
end

section
namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}}

section Mul

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

lemma mul_mem_divisorSections {D E : WeilDivisor X} (c : (X.functionField)ˣ)
    (hc : ∀ Z : PrimeDivisor X, D Z - E Z ≤ Z.ord (c : X.functionField)) {V : X.Opens}
    {f : V → X.functionField} (hf : f ∈ divisorSections D V) :
    (fun y => f y * (c : X.functionField)) ∈ divisorSections E V := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨W, hyW, h⟩ := hf.1 y
    exact ⟨W, hyW, fun z hz => by simp only [h z hz]⟩
  · set Z := PrimeDivisor.ofPoint y.1 hy
    by_cases hfy : f y = 0
    · simp [hfy]
    · have h1 := hf.2 y hy
      change Z.valuation (f y) ≤ WithZero.exp (D Z) at h1
      change Z.valuation (f y * c) ≤ WithZero.exp (E Z)
      rw [Z.valuation_le_exp_iff hfy] at h1
      rw [Z.valuation_le_exp_iff (mul_ne_zero hfy (Units.ne_zero c)),
        Z.ord_mul hfy (Units.ne_zero c)]
      have := hc Z
      omega

noncomputable def divisorMulPresheaf {D E : WeilDivisor X} (c : (X.functionField)ˣ)
    (hc : ∀ Z : PrimeDivisor X, D Z - E Z ≤ Z.ord (c : X.functionField)) :
    divisorPresheaf D ⟶ divisorPresheaf E where
  app _ := AddCommGrpCat.ofHom
    { toFun := fun f => ⟨fun y => f.1 y * c, mul_mem_divisorSections c hc f.2⟩
      map_zero' := Subtype.ext (funext fun _ => zero_mul _)
      map_add' := fun _ _ => Subtype.ext (funext fun _ => add_mul _ _ _) }
  naturality _ _ _ := rfl

noncomputable def divisorMul {D E : WeilDivisor X} (c : (X.functionField)ˣ)
    (hc : ∀ Z : PrimeDivisor X, D Z - E Z ≤ Z.ord (c : X.functionField)) :
    divisorSheaf D ⟶ divisorSheaf E :=
  ⟨PresheafOfModules.homMk (divisorMulPresheaf c hc) (fun _ _ _ =>
    Subtype.ext (funext fun _ => mul_assoc _ _ _))⟩

end Mul

section MulIso

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

noncomputable def divisorMulIso {D E : WeilDivisor X} (c : (X.functionField)ˣ)
    (hc : D - E = principalDivisor (Additive.ofMul c)) : divisorSheaf D ≅ divisorSheaf E where
  hom := divisorMul c (fun Z => by
    have := congrArg (fun F : WeilDivisor X => F Z) hc
    simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply] at this
    omega)
  inv := divisorMul c⁻¹ (fun Z => by
    have := congrArg (fun F : WeilDivisor X => F Z) hc
    simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply] at this
    have h := Z.ord_mul (Units.ne_zero c) (Units.ne_zero c⁻¹)
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, PrimeDivisor.ord_one] at h
    omega)
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext f
    apply Subtype.ext
    funext y
    change f.1 y * c * ((c⁻¹ : (X.functionField)ˣ) : X.functionField) = f.1 y
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext f
    apply Subtype.ext
    funext y
    change f.1 y * ((c⁻¹ : (X.functionField)ˣ) : X.functionField) * c = f.1 y
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end MulIso

section Basis

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

noncomputable def localBasis (D : WeilDivisor X) (U : X.Opens) (g : (X.functionField)ˣ)
    (hg : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z) :
    divisorSections D U :=
  ⟨fun _ => ((g⁻¹ : (X.functionField)ˣ) : X.functionField), by
    refine ⟨fun y => ⟨⊤, trivial, fun _ _ => rfl⟩, fun y hy => ?_⟩
    rw [PrimeDivisor.valuation_le_exp_iff _ (Units.ne_zero _)]
    have h1 := PrimeDivisor.ord_mul (PrimeDivisor.ofPoint y.1 hy) (Units.ne_zero g)
      (Units.ne_zero g⁻¹)
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, PrimeDivisor.ord_one,
      hg (PrimeDivisor.ofPoint y.1 hy) y.2] at h1
    dsimp only
    omega⟩

theorem localBasis_bijective (D : WeilDivisor X) (U : X.Opens) (g : (X.functionField)ˣ)
    (hg : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z)
    (V : X.Opens) (hVU : V ≤ U) :
    Function.Bijective (fun r : Γ(X, V) => r • divisorSectionsRes D hVU (localBasis D U g hg)) := by
  by_cases hne : Nonempty V
  · constructor
    · intro r₁ r₂ h12
      obtain ⟨y⟩ := hne
      have : Nonempty V := ⟨y⟩
      have := congrArg (fun t : divisorSections D V => t.1 y) h12
      have h := mul_right_cancel₀ (Units.ne_zero g⁻¹) this
      rw [sectionValue_eq V y r₁, sectionValue_eq V y r₂] at h
      exact Scheme.germToFunctionField_injective X V h
    · intro t
      obtain ⟨y0⟩ := hne
      have : Nonempty V := ⟨y0⟩
      set c := t.1 y0
      have hord : ∀ Z : PrimeDivisor X, Z.point ∈ V →
          0 ≤ Z.ord (c * (g : X.functionField)) := by
        intro Z hZ
        by_cases hc : c = 0
        · rw [hc, zero_mul, PrimeDivisor.ord_zero]
        · rw [PrimeDivisor.ord_mul Z hc (Units.ne_zero g), hg Z (hVU hZ)]
          have ht := t.2.2 ⟨Z.point, hZ⟩ Z.2
          have hcZ : t.1 ⟨Z.point, hZ⟩ = c := divisorSections_apply_eq D t _ y0
          rw [hcZ] at ht
          have := (PrimeDivisor.valuation_le_exp_iff Z hc (D Z)).mp ht
          omega
      obtain ⟨r, hr⟩ := exists_section_of_ord_nonneg V _ hord
      refine ⟨r, Subtype.ext (funext fun y => ?_)⟩
      rw [divisorSections_smul_apply, sectionValue_eq, hr, divisorSections_apply_eq D t y y0]
      change c * (g : X.functionField) * ((g⁻¹ : (X.functionField)ˣ) : X.functionField) = c
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · have hV : V = ⊥ := by
      ext y
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hne ⟨⟨y, hy⟩⟩
    have : Subsingleton Γ(X, V) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun t => ⟨0, Subtype.ext (funext fun y => ?_)⟩⟩
    exact (hne ⟨y⟩).elim

noncomputable def divisorSectionsOne (V : X.Opens) : divisorSections (0 : WeilDivisor X) V :=
  divisorSectionsRes 0 le_top (localBasis 0 ⊤ 1 (fun Z _ => by simp [PrimeDivisor.ord_one]))

noncomputable def unitToDivisorZero (V : (Opens X)ᵒᵖ) :
    (X.ringCatSheaf.obj.obj V) →ₗ[X.ringCatSheaf.obj.obj V]
      ((divisorPresheaf (0 : WeilDivisor X)).obj V) :=
  LinearMap.toSpanSingleton _ _ (divisorSectionsOne V.unop)

lemma unitToDivisorZero_bijective (V : (Opens X)ᵒᵖ) :
    Function.Bijective (unitToDivisorZero (X := X) V) :=
  localBasis_bijective 0 ⊤ 1 (fun Z _ => by simp [PrimeDivisor.ord_one]) V.unop le_top

noncomputable def divisorSheafZeroIso :
    SheafOfModules.unit X.ringCatSheaf ≅ divisorSheaf (0 : WeilDivisor X) :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective (unitToDivisorZero V)
        (unitToDivisorZero_bijective V)).toModuleIso)
      (fun V W i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        funext y
        change sectionValue W.unop y (X.presheaf.map i r) * 1 =
          sectionValue V.unop ⟨y.1, i.unop.le y.2⟩ r * 1
        exact congrArg (· * 1) (sectionValue_res i.unop.le y (show Γ(X, V.unop) from r))))

end Basis

section Hom

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

theorem divisorSheaf_hom_eq_mul {D E : WeilDivisor X} (φ : divisorSheaf D ⟶ divisorSheaf E) :
    ∃ c : X.functionField, ∀ (V : (Opens X)ᵒᵖ) (f : divisorSections D V.unop) (y : V.unop),
      ((φ.val.app V).hom f : divisorSections E V.unop).1 y = f.1 y * c := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, g, hxU, hg⟩ := WeilDivisor.exists_local_equation D x
  have hg' : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g Z).symm.trans (hg Z hZ)
  set s := localBasis D U g hg'
  set t : divisorSections E U := (φ.val.app (op U)).hom s
  refine ⟨t.1 ⟨x, hxU⟩ * g, fun V f y => ?_⟩
  obtain ⟨w, hwV, hwU⟩ := nonempty_preirreducible_inter V.unop.isOpen U.isOpen ⟨y.1, y.2⟩ ⟨x, hxU⟩
  set W : X.Opens := V.unop ⊓ U
  have hWU : W ≤ U := inf_le_right
  have hWV : W ≤ V.unop := inf_le_left
  obtain ⟨r, hr⟩ := (localBasis_bijective D U g hg' W hWU).2
    (divisorSectionsRes D hWV f)
  have hnat := PresheafOfModules.naturality_apply φ.val (homOfLE hWV).op f
  have hnat' := PresheafOfModules.naturality_apply φ.val (homOfLE hWU).op s
  have hw : w ∈ W := ⟨hwV, hwU⟩
  have key : ((φ.val.app V).hom f : divisorSections E V.unop).1 ⟨w, hwV⟩ =
      f.1 ⟨w, hwV⟩ * (t.1 ⟨x, hxU⟩ * g) := by
    have e1 := congrArg (fun m : divisorSections E W => m.1 ⟨w, hw⟩) hnat
    have e2 := congrArg (fun m : divisorSections D W => m.1 ⟨w, hw⟩) hr
    change ((φ.val.app (op W)).hom (divisorSectionsRes D hWV f)).1 ⟨w, hw⟩ =
      ((φ.val.app V).hom f).1 ⟨w, hwV⟩ at e1
    change sectionValue W ⟨w, hw⟩ r * ((g⁻¹ : (X.functionField)ˣ) : X.functionField) =
      f.1 ⟨w, hwV⟩ at e2
    have e3 := congrArg (fun m : divisorSections E W => m.1 ⟨w, hw⟩) hnat'
    change ((φ.val.app (op W)).hom (divisorSectionsRes D hWU s)).1 ⟨w, hw⟩ = t.1 ⟨w, hwU⟩ at e3
    have hr' : r • divisorSectionsRes D hWU s = divisorSectionsRes D hWV f := hr
    let ψ : divisorSections D W → divisorSections E W := fun m => (φ.val.app (op W)).hom m
    have hlin : ψ (r • divisorSectionsRes D hWU s) = r • ψ (divisorSectionsRes D hWU s) :=
      (φ.val.app (op W)).hom.map_smul r _
    have hg0 : (g : X.functionField) ≠ 0 := g.ne_zero
    calc ((φ.val.app V).hom f : divisorSections E V.unop).1 ⟨w, hwV⟩
        = ((φ.val.app (op W)).hom (divisorSectionsRes D hWV f) : divisorSections E W).1
            ⟨w, hw⟩ := e1.symm
      _ = (ψ (r • divisorSectionsRes D hWU s)).1 ⟨w, hw⟩ := by rw [hr']
      _ = (r • ψ (divisorSectionsRes D hWU s)).1 ⟨w, hw⟩ := by rw [hlin]
      _ = sectionValue W ⟨w, hw⟩ r * t.1 ⟨w, hwU⟩ := by
            rw [divisorSections_smul_apply, e3]
      _ = sectionValue W ⟨w, hw⟩ r * t.1 ⟨x, hxU⟩ := by
            rw [divisorSections_apply_eq E t ⟨w, hwU⟩ ⟨x, hxU⟩]
      _ = f.1 ⟨w, hwV⟩ * (t.1 ⟨x, hxU⟩ * g) := by
            rw [← e2, Units.val_inv_eq_inv_val]
            field_simp
  have h1 := divisorSections_apply_eq E ((φ.val.app V).hom f : divisorSections E V.unop) y
    ⟨w, hwV⟩
  rw [h1, key, divisorSections_apply_eq D f ⟨w, hwV⟩ y]

end Hom

section Iso

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

lemma neg_le_ord_of_mem (D : WeilDivisor X) {U : X.Opens} (m : divisorSections D U)
    (Z : PrimeDivisor X) (hZ : Z.point ∈ U) (hm : m.1 ⟨Z.point, hZ⟩ ≠ 0) :
    -D Z ≤ Z.ord (m.1 ⟨Z.point, hZ⟩) :=
  (Z.valuation_le_exp_iff hm (D Z)).mp (m.2.2 ⟨Z.point, hZ⟩ Z.2)

lemma ord_inv_units (Z : PrimeDivisor X) (g : (X.functionField)ˣ) :
    Z.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) = - Z.ord (g : X.functionField) := by
  have h := Z.ord_mul (Units.ne_zero g) (Units.ne_zero g⁻¹)
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, PrimeDivisor.ord_one] at h
  omega

lemma sub_le_ord_of_hom {D E : WeilDivisor X} (φ : divisorSheaf D ⟶ divisorSheaf E)
    {c : X.functionField} (hc0 : c ≠ 0)
    (hc : ∀ (V : (Opens X)ᵒᵖ) (f : divisorSections D V.unop) (y : V.unop),
      ((φ.val.app V).hom f : divisorSections E V.unop).1 y = f.1 y * c)
    (Z : PrimeDivisor X) : D Z - E Z ≤ Z.ord c := by
  obtain ⟨U, g, hZU, hg⟩ := WeilDivisor.exists_local_equation D Z.point
  have hg' : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g Z).symm.trans (hg Z hZ)
  set s := localBasis D U g hg'
  let m : divisorSections E U := (φ.val.app (op U)).hom s
  have hval : m.1 ⟨Z.point, hZU⟩ = s.1 ⟨Z.point, hZU⟩ * c := hc (op U) s ⟨Z.point, hZU⟩
  have hs0 : s.1 ⟨Z.point, hZU⟩ ≠ 0 := Units.ne_zero g⁻¹
  have hne : m.1 ⟨Z.point, hZU⟩ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero hs0 hc0
  have h := neg_le_ord_of_mem E m Z hZU hne
  rw [hval] at h
  change -E Z ≤ Z.ord (((g⁻¹ : (X.functionField)ˣ) : X.functionField) * c) at h
  rw [Z.ord_mul (Units.ne_zero _) hc0, ord_inv_units, hg' Z hZU] at h
  omega

theorem exists_principal_of_iso {D E : WeilDivisor X} (e : divisorSheaf D ≅ divisorSheaf E) :
    ∃ c : (X.functionField)ˣ, D - E = principalDivisor (Additive.ofMul c) := by
  obtain ⟨c, hc⟩ := divisorSheaf_hom_eq_mul e.hom
  obtain ⟨c', hc'⟩ := divisorSheaf_hom_eq_mul e.inv
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, g, hxU, hg⟩ := WeilDivisor.exists_local_equation D x
  have hg' : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g Z).symm.trans (hg Z hZ)
  set s := localBasis D U g hg'
  have hid := congrArg (fun φ : divisorSheaf D ⟶ divisorSheaf D =>
    ((φ.val.app (op U)).hom s : divisorSections D U).1 ⟨x, hxU⟩) e.hom_inv_id
  have e1 := hc' (op U) ((e.hom.val.app (op U)).hom s) ⟨x, hxU⟩
  have e2 := hc (op U) s ⟨x, hxU⟩
  have hid' : s.1 ⟨x, hxU⟩ * c * c' = s.1 ⟨x, hxU⟩ := by
    rw [← e2]
    exact e1.symm.trans hid
  have hcc' : c * c' = 1 := by
    have hs0 : s.1 ⟨x, hxU⟩ ≠ 0 := Units.ne_zero g⁻¹
    rw [mul_assoc] at hid'
    exact (mul_right_eq_self₀.mp hid').resolve_right hs0
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc'
  have hc'0 : c' ≠ 0 := right_ne_zero_of_mul_eq_one hcc'
  refine ⟨Units.mk c c' hcc' (by rw [mul_comm]; exact hcc'), ?_⟩
  ext Z
  simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply]
  have h1 := sub_le_ord_of_hom e.hom hc0 hc Z
  have h2 := sub_le_ord_of_hom e.inv hc'0 hc' Z
  have h3 := Z.ord_mul hc0 hc'0
  rw [hcc', PrimeDivisor.ord_one] at h3
  omega

theorem nonempty_divisorSheaf_iso_iff (D E : WeilDivisor X) :
    Nonempty (divisorSheaf D ≅ divisorSheaf E) ↔ D - E ∈ principalDivisors X := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨c, hc⟩ := exists_principal_of_iso e
    exact ⟨Additive.ofMul c, hc.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨divisorMulIso (Additive.toMul a) ha.symm⟩

end Iso

end GroundTheory.Arith.SchemeCoh
end

section
namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

lemma isBasisOn_localBasis (D : WeilDivisor X) (U : X.Opens) (g : (X.functionField)ˣ)
    (hg : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z) :
    IsBasisOn ((preMod X).obj (divisorSheaf D)) U (localBasis D U g hg) :=
  fun V h => localBasis_bijective D U g hg V h

theorem isInvertibleSheaf_divisorSheaf (D : WeilDivisor X) :
    IsInvertibleSheaf (divisorSheaf D) := by
  intro x
  obtain ⟨U, g, hxU, hg⟩ := WeilDivisor.exists_local_equation D x
  have hg' : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g Z).symm.trans (hg Z hZ)
  exact ⟨U, hxU, localBasis D U g hg', isBasisOn_localBasis D U g hg'⟩

lemma mul_mem_divisorSections_add {D E : WeilDivisor X} {V : X.Opens}
    {f g : V → X.functionField} (hf : f ∈ divisorSections D V) (hg : g ∈ divisorSections E V) :
    (fun y => f y * g y) ∈ divisorSections (D + E) V := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨W₁, hy₁, h₁⟩ := hf.1 y
    obtain ⟨W₂, hy₂, h₂⟩ := hg.1 y
    exact ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, fun z hz => by simp only [h₁ z hz.1, h₂ z hz.2]⟩
  · simp only [map_mul, Finsupp.coe_add, Pi.add_apply, WithZero.exp_add]
    exact mul_le_mul' (hf.2 y hy) (hg.2 y hy)

noncomputable def divisorSectionsMul {D E : WeilDivisor X} {V : X.Opens} (f : divisorSections D V)
    (g : divisorSections E V) : divisorSections (D + E) V :=
  ⟨fun y => f.1 y * g.1 y, mul_mem_divisorSections_add f.2 g.2⟩

noncomputable def divisorTensorMul (D E : WeilDivisor X) :
    (preMod X).obj (divisorSheaf D) ⊗ (preMod X).obj (divisorSheaf E) ⟶
      (preMod X).obj (divisorSheaf (D + E)) where
  app V := ModuleCat.MonoidalCategory.tensorLift
    (M₁ := ((preMod X).obj (divisorSheaf D)).obj V)
    (M₂ := ((preMod X).obj (divisorSheaf E)).obj V)
    (M₃ := ((preMod X).obj (divisorSheaf (D + E))).obj V)
    (fun f g => divisorSectionsMul (V := V.unop) f g)
    (fun f₁ f₂ g => Subtype.ext (funext fun y => add_mul _ _ _))
    (fun r f g => Subtype.ext (funext fun y => mul_assoc _ _ _))
    (fun f g₁ g₂ => Subtype.ext (funext fun y => mul_add _ _ _))
    (fun r f g => Subtype.ext (funext fun y => by
      change f.1 y * (sectionValue V.unop y r * g.1 y) = sectionValue V.unop y r * (f.1 y * g.1 y)
      ring))
  naturality {V W} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro f g
    apply Subtype.ext
    funext y
    rfl

noncomputable def divisorTensorHom (D E : WeilDivisor X) :
    divisorSheaf D ⊗ divisorSheaf E ⟶ divisorSheaf (D + E) :=
  tensorLift (divisorTensorMul D E)

lemma ord_mul_units (Z : PrimeDivisor X) (g h : (X.functionField)ˣ) :
    Z.ord ((g * h : (X.functionField)ˣ) : X.functionField) =
      Z.ord (g : X.functionField) + Z.ord (h : X.functionField) := by
  rw [Units.val_mul, Z.ord_mul (Units.ne_zero g) (Units.ne_zero h)]

instance (D E : WeilDivisor X) : IsIso (divisorTensorHom D E) := by
  apply isIso_of_isBasisOn
  intro x
  obtain ⟨U₁, g₁, hx₁, hg₁⟩ := WeilDivisor.exists_local_equation D x
  obtain ⟨U₂, g₂, hx₂, hg₂⟩ := WeilDivisor.exists_local_equation E x
  set U := U₁ ⊓ U₂
  have h₁ : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g₁ : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g₁ Z).symm.trans (hg₁ Z hZ.1)
  have h₂ : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g₂ : X.functionField) = E Z :=
    fun Z hZ => (principalDivisor_apply g₂ Z).symm.trans (hg₂ Z hZ.2)
  have h₁₂ : ∀ Z : PrimeDivisor X, Z.point ∈ U →
      Z.ord ((g₁ * g₂ : (X.functionField)ˣ) : X.functionField) = (D + E) Z := by
    intro Z hZ
    rw [ord_mul_units, h₁ Z hZ, h₂ Z hZ, Finsupp.coe_add, Pi.add_apply]
  set s := localBasis D U g₁ h₁
  set t := localBasis E U g₂ h₂
  have hst := ((isBasisOn_localBasis D U g₁ h₁).tmul (isBasisOn_localBasis E U g₂ h₂)).map_of_alt
    (tensorToSheaf (divisorSheaf D) (divisorSheaf E))
    (W_tensorToSheaf (divisorSheaf D) (divisorSheaf E))
  refine ⟨U, ⟨hx₁, hx₂⟩, _, hst, ?_⟩
  have himg : ((preMod X).map (divisorTensorHom D E)).app (op U)
      ((tensorToSheaf (divisorSheaf D) (divisorSheaf E)).app (op U)
        (s ⊗ₜ t : ((preMod X).obj (divisorSheaf D) ⊗ (preMod X).obj (divisorSheaf E)).obj (op U))) =
      localBasis (D + E) U (g₁ * g₂) h₁₂ := by
    have := congrArg (fun φ => φ.app (op U) (s ⊗ₜ t :
      ((preMod X).obj (divisorSheaf D) ⊗ (preMod X).obj (divisorSheaf E)).obj (op U)))
      (tensorToSheaf_tensorLift (divisorTensorMul D E))
    refine this.trans ?_
    apply Subtype.ext
    funext y
    change ((g₁⁻¹ : (X.functionField)ˣ) : X.functionField) * ((g₂⁻¹ : (X.functionField)ˣ) :
      X.functionField) = (((g₁ * g₂)⁻¹ : (X.functionField)ˣ) : X.functionField)
    rw [← Units.val_mul, mul_inv_rev, mul_comm]
  rw [himg]
  exact isBasisOn_localBasis (D + E) U (g₁ * g₂) h₁₂

noncomputable def divisorTensorIso (D E : WeilDivisor X) :
    divisorSheaf D ⊗ divisorSheaf E ≅ divisorSheaf (D + E) :=
  asIso (divisorTensorHom D E)

end GroundTheory.Arith.SchemeCoh
end

section
namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory

universe u

variable {X : Scheme.{u}}

lemma nonempty_inf_of_mem [IsIntegral X] {V W : X.Opens} (y : V) (w : W) : Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨y.1, y.2⟩ ⟨w.1, w.2⟩
  exact ⟨⟨z, hz⟩⟩

abbrev asRing (V : X.Opens) (r : Γ(X, V)) : ringOn X V := r

section RatVal

variable {P : PMod X} {U₀ : X.Opens} {s₀ : P.obj (op U₀)} (hs₀ : IsBasisOn P U₀ s₀)

noncomputable def coeffOn {V : X.Opens} (l : P.obj (op V)) : ringOn X (V ⊓ U₀) :=
  (Equiv.ofBijective _ (hs₀ (V ⊓ U₀) inf_le_right)).symm (resM P inf_le_left l)

lemma coeffOn_spec {V : X.Opens} (l : P.obj (op V)) :
    coeffOn hs₀ l • resM P inf_le_right s₀ = resM P inf_le_left l :=
  (Equiv.ofBijective _ (hs₀ (V ⊓ U₀) inf_le_right)).apply_symm_apply _

variable [IsIntegral X] [Nonempty U₀]

noncomputable def ratVal {V : X.Opens} (l : P.obj (op V)) (y : V) : X.functionField :=
  haveI := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  X.germToFunctionField (V ⊓ U₀) (coeffOn hs₀ l)

theorem ratVal_eq {V W : X.Opens} (hWV : W ≤ V) (hWU : W ≤ U₀) [Nonempty W]
    (l : P.obj (op V)) (a : ringOn X W) (ha : a • resM P hWU s₀ = resM P hWV l) (y : V) :
    ratVal hs₀ l y = X.germToFunctionField W a := by
  have hW' : W ≤ V ⊓ U₀ := le_inf hWV hWU
  have h1 := congrArg (resM P hW') (coeffOn_spec hs₀ l)
  rw [resM_smul_res, resM_resM] at h1
  have h2 : a = resR hW' (coeffOn hs₀ l) := (hs₀ W hWU).1 (ha.trans h1.symm)
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [h2]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

lemma ratVal_const {V : X.Opens} (l : P.obj (op V)) (y z : V) :
    ratVal hs₀ l y = ratVal hs₀ l z := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) z]

lemma ratVal_res {V W : X.Opens} (h : W ≤ V) (l : P.obj (op V)) (y : W) :
    ratVal hs₀ (resM P h l) y = ratVal hs₀ l ⟨y.1, h y.2⟩ := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e := coeffOn_spec hs₀ (resM P h l)
  rw [resM_resM] at e
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ (coeffOn_spec hs₀ (resM P h l)) y,
    ratVal_eq hs₀ ((inf_le_left : W ⊓ U₀ ≤ W).trans h) inf_le_right l _ e]

lemma ratVal_smul {V : X.Opens} (a : ringOn X V) (l : P.obj (op V)) (y : V) :
    ratVal hs₀ (a • l) y = sectionValue V y a * ratVal hs₀ l y := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e : (resR inf_le_left a * coeffOn hs₀ l) • resM P (inf_le_right : V ⊓ U₀ ≤ U₀) s₀ =
      resM P inf_le_left (a • l) := by
    rw [mul_smul, coeffOn_spec, resM_smul]
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ e y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y]
  refine (map_mul (X.germToFunctionField (V ⊓ U₀)).hom
    (show Γ(X, V ⊓ U₀) from resR inf_le_left a) (show Γ(X, V ⊓ U₀) from coeffOn hs₀ l)).trans ?_
  congr 1
  refine Eq.trans ?_ (sectionValue_eq V y (show Γ(X, V) from a)).symm
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

lemma ratVal_add {V : X.Opens} (l m : P.obj (op V)) (y : V) :
    ratVal hs₀ (l + m) y = ratVal hs₀ l y + ratVal hs₀ m y := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e : (coeffOn hs₀ l + coeffOn hs₀ m) • resM P (inf_le_right : V ⊓ U₀ ≤ U₀) s₀ =
      resM P inf_le_left (l + m) := by
    rw [add_smul, coeffOn_spec, coeffOn_spec, resM_add]
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ e y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y,
    ratVal_eq hs₀ inf_le_left inf_le_right m _ (coeffOn_spec hs₀ m) y]
  exact map_add (X.germToFunctionField (V ⊓ U₀)).hom (show Γ(X, V ⊓ U₀) from coeffOn hs₀ l)
    (show Γ(X, V ⊓ U₀) from coeffOn hs₀ m)

lemma ratVal_zero {V : X.Opens} (y : V) : ratVal hs₀ (0 : P.obj (op V)) y = 0 := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right (0 : P.obj (op V)) 0
    (by rw [zero_smul, resM_zero]) y]
  exact map_zero _

lemma ratVal_sub {V : X.Opens} (l m : P.obj (op V)) (y : V) :
    ratVal hs₀ (l - m) y = ratVal hs₀ l y - ratVal hs₀ m y := by
  have h := ratVal_add hs₀ (l - m) m y
  rw [sub_add_cancel] at h
  rw [h]
  ring

end RatVal

section Invertible

variable [IsIntegral X]
  {P : PMod X} {U₀ : X.Opens} {s₀ : P.obj (op U₀)} (hs₀ : IsBasisOn P U₀ s₀) [Nonempty U₀]

lemma ratVal_ne_zero_of_isBasisOn {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    (y : U) : ratVal hs₀ s y ≠ 0 := by
  intro h
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right s _ (coeffOn_spec hs₀ s) y] at h
  have hr : coeffOn hs₀ s = 0 := Scheme.germToFunctionField_injective X (U ⊓ U₀)
    (h.trans (map_zero _).symm)
  have hz : resM P (inf_le_left : U ⊓ U₀ ≤ U) s = 0 := by
    rw [← coeffOn_spec hs₀ s, hr, zero_smul]
  have hb := (hs (U ⊓ U₀) inf_le_left).1
  have h10 : (1 : ringOn X (U ⊓ U₀)) = 0 := hb (by simp only [hz, smul_zero])
  exact one_ne_zero (α := Γ(X, U ⊓ U₀)) h10

omit hs₀ in

lemma eq_zero_of_ratVal_eq_zero {L : X.Modules} (hL : IsInvertibleSheaf L) {U₀ : X.Opens}
    {s₀ : ((preMod X).obj L).obj (op U₀)} (hs₀ : IsBasisOn ((preMod X).obj L) U₀ s₀)
    [Nonempty U₀] {V : X.Opens} (l : ((preMod X).obj L).obj (op V))
    (h : ∀ y, ratVal hs₀ l y = 0) : l = 0 := by
  apply sheaf_eq_of_locally ⟨L.presheaf, L.isSheaf⟩ (V := V) l 0
  intro x hxV
  obtain ⟨U, hxU, s, hs⟩ := hL x
  refine ⟨V ⊓ U, inf_le_left, ⟨hxV, hxU⟩, ?_⟩
  obtain ⟨a, ha⟩ := (hs (V ⊓ U) inf_le_right).2 (resM _ inf_le_left l)
  have ha' : a • resM _ inf_le_right s = resM _ inf_le_left l := ha
  have hW : Nonempty (V ⊓ U : X.Opens) := ⟨⟨x, hxV, hxU⟩⟩
  have h1 := ratVal_smul hs₀ a (resM _ inf_le_right s) ⟨x, hxV, hxU⟩
  rw [ha', ratVal_res, h, ratVal_res] at h1
  have hs0 := ratVal_ne_zero_of_isBasisOn hs₀ hs ⟨x, hxU⟩
  have ha0 : sectionValue (V ⊓ U) ⟨x, hxV, hxU⟩ a = 0 :=
    (mul_eq_zero.mp h1.symm).resolve_right hs0
  have ha0' : a = 0 := Scheme.germToFunctionField_injective X (V ⊓ U)
    ((sectionValue_eq _ _ _).symm.trans (ha0.trans (map_zero _).symm))
  change resM _ inf_le_left l = resM _ inf_le_left (0 : ((preMod X).obj L).obj (op V))
  rw [← ha', ha0', zero_smul, resM_zero]

variable {L : X.Modules} (hL : IsInvertibleSheaf L)

noncomputable def basisOpen (x : X) : X.Opens := (hL x).choose

omit [IsIntegral X] in
lemma mem_basisOpen (x : X) : x ∈ basisOpen hL x := (hL x).choose_spec.choose

noncomputable def basisSec (x : X) : ((preMod X).obj L).obj (op (basisOpen hL x)) :=
  (hL x).choose_spec.choose_spec.choose

omit [IsIntegral X] in
lemma isBasisOn_basisSec (x : X) :
    IsBasisOn ((preMod X).obj L) (basisOpen hL x) (basisSec hL x) :=
  (hL x).choose_spec.choose_spec.choose_spec

instance (x : X) : Nonempty (basisOpen hL x) := ⟨⟨x, mem_basisOpen hL x⟩⟩

noncomputable def secVal {V : X.Opens} (l : ((preMod X).obj L).obj (op V)) (y : V) :
    X.functionField :=
  ratVal (isBasisOn_basisSec hL (Classical.arbitrary X)) l y

lemma secVal_basisSec_ne_zero (x : X) (y : basisOpen hL x) :
    secVal hL (basisSec hL x) y ≠ 0 :=
  ratVal_ne_zero_of_isBasisOn _ (isBasisOn_basisSec hL x) y

variable [IsNoetherian X] [IsLocallyFactorial X]

lemma ord_secVal_basisSec (Z : PrimeDivisor X) (x : X) (hZ : Z.point ∈ basisOpen hL x) :
    Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZ⟩) =
      Z.ord (secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩) := by
  set W := basisOpen hL x ⊓ basisOpen hL Z.point
  have hZW : Z.point ∈ W := ⟨hZ, mem_basisOpen hL Z.point⟩
  have : Nonempty W := ⟨⟨Z.point, hZW⟩⟩
  obtain ⟨u, hu⟩ := (isBasisOn_basisSec hL Z.point W inf_le_right).2
    (resM _ inf_le_left (basisSec hL x))
  obtain ⟨v, hv⟩ := (isBasisOn_basisSec hL x W inf_le_left).2
    (resM _ inf_le_right (basisSec hL Z.point))
  have hu' : u • resM _ inf_le_right (basisSec hL Z.point) = resM _ inf_le_left (basisSec hL x) :=
    hu
  have hv' : v • resM _ inf_le_left (basisSec hL x) = resM _ inf_le_right (basisSec hL Z.point) :=
    hv
  have huv : u * v = 1 := (isBasisOn_basisSec hL x W inf_le_left).1 (by
    change (u * v) • resM _ inf_le_left (basisSec hL x) = (1 : ringOn X W) • _
    rw [mul_smul, hv', hu', one_smul])
  have hunit : IsUnit (M := Γ(X, W)) u := isUnit_iff_exists_inv.mpr ⟨v, huv⟩
  have h1 := ratVal_smul (isBasisOn_basisSec hL (Classical.arbitrary X)) u
    (resM _ inf_le_right (basisSec hL Z.point)) ⟨Z.point, hZW⟩
  rw [hu', ratVal_res, ratVal_res] at h1
  change secVal hL (basisSec hL x) ⟨Z.point, hZ⟩ = sectionValue W ⟨Z.point, hZW⟩ u *
    secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩ at h1
  have hsv : sectionValue W ⟨Z.point, hZW⟩ u ≠ 0 := by
    intro h0
    apply hunit.ne_zero
    exact Scheme.germToFunctionField_injective X W
      ((sectionValue_eq _ _ _).symm.trans (h0.trans (map_zero _).symm))
  have h0 : Z.ord (sectionValue W ⟨Z.point, hZW⟩ u) = 0 :=
    (congrArg Z.ord (sectionValue_eq _ _ _)).trans (Z.ord_germToFunctionField_of_isUnit hZW hunit)
  rw [h1, Z.ord_mul hsv (secVal_basisSec_ne_zero hL _ _), h0, zero_add]

noncomputable def divisorOfInvertible : WeilDivisor X :=
  Finsupp.ofSupportFinite
    (fun Z => - Z.ord (secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩)) (by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (basisOpen hL x : Set X))
      (fun x => (basisOpen hL x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_basisOpen hL x⟩)
    refine (t.finite_toSet.biUnion fun x _ => PrimeDivisor.finite_ord_ne_zero
      (secVal_basisSec_ne_zero hL x ⟨x, mem_basisOpen hL x⟩)).subset ?_
    intro Z hZ
    obtain ⟨x, hx, hZx⟩ : ∃ x ∈ t, Z.point ∈ basisOpen hL x := by
      have := ht (Set.mem_univ Z.point)
      simpa using this
    refine Set.mem_biUnion hx ?_
    simp only [Function.mem_support, ne_eq, neg_eq_zero] at hZ
    change Z.ord (ratVal _ (basisSec hL x) ⟨x, mem_basisOpen hL x⟩) ≠ 0
    rw [ratVal_const _ (basisSec hL x) ⟨x, mem_basisOpen hL x⟩ ⟨Z.point, hZx⟩]
    change Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZx⟩) ≠ 0
    rwa [ord_secVal_basisSec hL Z x hZx])

lemma ord_secVal_basisSec_eq (Z : PrimeDivisor X) (x : X) (hZ : Z.point ∈ basisOpen hL x) :
    Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZ⟩) = - divisorOfInvertible hL Z := by
  rw [ord_secVal_basisSec hL Z x hZ]
  change _ = - - _
  rw [neg_neg]

lemma secVal_mem {V : X.Opens} (l : ((preMod X).obj L).obj (op V)) :
    (fun y => secVal hL l y) ∈ divisorSections (divisorOfInvertible hL) V := by
  refine ⟨fun y => ⟨⊤, trivial, fun z _ => ratVal_const _ l z y⟩, fun y hy => ?_⟩
  set Z := PrimeDivisor.ofPoint y.1 hy
  by_cases h0 : secVal hL l y = 0
  · change Z.valuation (secVal hL l y) ≤ _
    rw [h0, map_zero]
    exact zero_le
  change Z.valuation (secVal hL l y) ≤ WithZero.exp (divisorOfInvertible hL Z)
  rw [Z.valuation_le_exp_iff h0]
  set W := V ⊓ basisOpen hL y.1
  have hyW : y.1 ∈ W := ⟨y.2, mem_basisOpen hL y.1⟩
  have : Nonempty W := ⟨⟨y.1, hyW⟩⟩
  obtain ⟨a, ha⟩ := (isBasisOn_basisSec hL y.1 W inf_le_right).2 (resM _ inf_le_left l)
  have ha' : a • resM _ inf_le_right (basisSec hL y.1) = resM _ inf_le_left l := ha
  have h1 := ratVal_smul (isBasisOn_basisSec hL (Classical.arbitrary X)) a
    (resM _ inf_le_right (basisSec hL y.1)) ⟨y.1, hyW⟩
  rw [ha', ratVal_res, ratVal_res] at h1
  change secVal hL l y = sectionValue W ⟨y.1, hyW⟩ a *
    secVal hL (basisSec hL y.1) ⟨y.1, mem_basisOpen hL y.1⟩ at h1
  have hb0 := secVal_basisSec_ne_zero hL y.1 ⟨y.1, mem_basisOpen hL y.1⟩
  have ha0 : sectionValue W ⟨y.1, hyW⟩ a ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact h0 h1
  have hpos : 0 ≤ Z.ord (sectionValue W ⟨y.1, hyW⟩ a) :=
    (Z.ord_nonneg_iff ha0).mpr ⟨X.presheaf.germ W y.1 hyW a, rfl⟩
  rw [h1, Z.ord_mul ha0 hb0]
  have := ord_secVal_basisSec_eq hL Z y.1 (mem_basisOpen hL y.1)
  change Z.ord (secVal hL (basisSec hL y.1) ⟨y.1, mem_basisOpen hL y.1⟩) = _ at this
  omega

noncomputable def toDivisorPresheaf :
    (preMod X).obj L ⟶ (preMod X).obj (divisorSheaf (divisorOfInvertible hL)) :=
  PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun l => (⟨fun y => secVal hL l y, secVal_mem hL l⟩ :
            divisorSections (divisorOfInvertible hL) V.unop)
          map_zero' := Subtype.ext (funext fun y => ratVal_zero _ y)
          map_add' := fun l m => Subtype.ext (funext fun y => ratVal_add _ l m y) }
      naturality := fun V W i => by
        ext l
        apply Subtype.ext
        funext y
        exact ratVal_res _ i.unop.le l y }
    (fun V r l => Subtype.ext (funext fun y => ratVal_smul _ r l y))

noncomputable def toDivisorSheaf : L ⟶ divisorSheaf (divisorOfInvertible hL) :=
  ⟨toDivisorPresheaf hL⟩

theorem secVal_bijective (V : X.Opens) :
    Function.Bijective (fun l : ((preMod X).obj L).obj (op V) =>
      (⟨fun y => secVal hL l y, secVal_mem hL l⟩ :
        divisorSections (divisorOfInvertible hL) V)) := by
  constructor
  · intro l m h
    have hlm : l - m = 0 := eq_zero_of_ratVal_eq_zero hL _ (l - m) (fun y => by
      rw [ratVal_sub]
      have := congrArg (fun t : divisorSections (divisorOfInvertible hL) V => t.1 y) h
      exact sub_eq_zero.mpr this)
    exact sub_eq_zero.mp hlm
  · intro t
    by_cases hne : Nonempty V
    swap
    · exact ⟨0, Subtype.ext (funext fun y => (hne ⟨y⟩).elim)⟩
    obtain ⟨y₀⟩ := hne
    set c := t.1 y₀
    have hW : ∀ x : V, Nonempty (V ⊓ basisOpen hL x.1 : X.Opens) :=
      fun x => ⟨⟨x.1, x.2, mem_basisOpen hL x.1⟩⟩
    have hord : ∀ x : V, ∀ Z : PrimeDivisor X, Z.point ∈ V ⊓ basisOpen hL x.1 →
        0 ≤ Z.ord (c * (secVal hL (basisSec hL x.1) ⟨x.1, mem_basisOpen hL x.1⟩)⁻¹) := by
      intro x Z hZ
      set β := secVal hL (basisSec hL x.1) ⟨x.1, mem_basisOpen hL x.1⟩
      have hβ : β ≠ 0 := secVal_basisSec_ne_zero hL _ _
      by_cases hc : c = 0
      · rw [hc, zero_mul, PrimeDivisor.ord_zero]
      have hβinv : Z.ord β⁻¹ = - Z.ord β := by
        have h := Z.ord_mul hβ (inv_ne_zero hβ)
        rw [mul_inv_cancel₀ hβ, PrimeDivisor.ord_one] at h
        omega
      have hβZ : Z.ord β = - divisorOfInvertible hL Z := by
        have := ord_secVal_basisSec_eq hL Z x.1 hZ.2
        rw [← this]
        exact congrArg Z.ord (ratVal_const _ _ _ _)
      have hcZ : -divisorOfInvertible hL Z ≤ Z.ord c := by
        have ht := t.2.2 ⟨Z.point, hZ.1⟩ Z.2
        have hct : t.1 ⟨Z.point, hZ.1⟩ = c := divisorSections_apply_eq _ t _ y₀
        rw [hct] at ht
        exact (Z.valuation_le_exp_iff hc (divisorOfInvertible hL Z)).mp ht
      rw [Z.ord_mul hc (inv_ne_zero hβ), hβinv, hβZ]
      omega
    choose a ha using fun x : V => exists_section_of_ord_nonneg (V ⊓ basisOpen hL x.1) _ (hord x)
    let lx : ∀ x : V, ((preMod X).obj L).obj (op (V ⊓ basisOpen hL x.1)) :=
      fun x => asRing _ (a x) • resM _ inf_le_right (basisSec hL x.1)
    have hlx : ∀ (x : V) (z : (V ⊓ basisOpen hL x.1 : X.Opens)), secVal hL (lx x) z = c := by
      intro x z
      have h1 := ratVal_smul (isBasisOn_basisSec hL (Classical.arbitrary X)) (asRing _ (a x))
        (resM _ inf_le_right (basisSec hL x.1)) z
      rw [ratVal_res] at h1
      refine h1.trans ((congrArg (· * ratVal _ (basisSec hL x.1) _)
        (sectionValue_eq _ z (a x))).trans ?_)
      simp only
      rw [ha x, ratVal_const _ (basisSec hL x.1) _ ⟨x.1, mem_basisOpen hL x.1⟩]
      exact inv_mul_cancel_right₀ (secVal_basisSec_ne_zero hL _ _) c
    obtain ⟨l, hl⟩ := sheaf_exists_glue ⟨L.presheaf, L.isSheaf⟩ (V := V) (ι := V)
      (fun x => V ⊓ basisOpen hL x.1) (fun _ => inf_le_left)
      (fun x hx => ⟨⟨x, hx⟩, hx, mem_basisOpen hL x⟩) lx (by
        intro p q
        have hsub : resM _ (inf_le_left : (V ⊓ basisOpen hL p.1) ⊓ (V ⊓ basisOpen hL q.1) ≤ _)
            (lx p) - resM _ inf_le_right (lx q) = 0 :=
          eq_zero_of_ratVal_eq_zero hL _ _ (fun z => by
            rw [ratVal_sub, ratVal_res, ratVal_res]
            change secVal hL (lx p) _ - secVal hL (lx q) _ = 0
            exact (congrArg₂ (· - ·) (hlx p _) (hlx q _)).trans (sub_self c))
        exact sub_eq_zero.mp hsub)
    refine ⟨l, Subtype.ext (funext fun y => ?_)⟩
    have e : resM ((preMod X).obj L) (inf_le_left : V ⊓ basisOpen hL y.1 ≤ V) l = lx y := hl y
    have h2 := ratVal_res (isBasisOn_basisSec hL (Classical.arbitrary X))
      (inf_le_left : V ⊓ basisOpen hL y.1 ≤ V) l ⟨y.1, y.2, mem_basisOpen hL y.1⟩
    rw [e] at h2
    change secVal hL (lx y) _ = secVal hL l y at h2
    change secVal hL l y = t.1 y
    rw [← h2, hlx, divisorSections_apply_eq _ t y y₀]

instance : IsIso (toDivisorSheaf hL) :=
  isIso_of_locally_bijective _ (fun _ => ⟨⊤, trivial, fun V _ => secVal_bijective hL V⟩)

end Invertible

end GroundTheory.Arith.SchemeCoh
end

section
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace GroundTheory.Arith.SchemeCoh

section
variable {X : Scheme.{u}}

lemma toSkeleton_dualSheaf_mul {L : X.Modules} (hL : IsInvertibleSheaf L) :
    toSkeleton (dualSheaf L) * toSkeleton L = 1 := by
  rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
  have := isIso_dualEval hL
  exact congr_toSkeleton_of_iso (asIso (dualEval L))

noncomputable def unitOfInvertible {L : X.Modules} (hL : IsInvertibleSheaf L) :
    (Skeleton X.Modules)ˣ where
  val := toSkeleton L
  inv := toSkeleton (dualSheaf L)
  val_inv := by rw [mul_comm]; exact toSkeleton_dualSheaf_mul hL
  inv_val := toSkeleton_dualSheaf_mul hL

end

variable (X : Scheme.{u})

noncomputable def picardSubgroup : Subgroup (Skeleton X.Modules)ˣ where
  carrier := {v | ∃ L : X.Modules, IsInvertibleSheaf L ∧ toSkeleton L = (v : Skeleton X.Modules)}
  mul_mem' := by
    rintro v w ⟨L, hL, hv⟩ ⟨M, hM, hw⟩
    exact ⟨L ⊗ M, hL.tensor hM, by rw [Units.val_mul, Skeleton.toSkeleton_tensorObj, hv, hw]⟩
  one_mem' := ⟨𝟙_ X.Modules, isInvertibleSheaf_unit, rfl⟩
  inv_mem' := by
    rintro v ⟨L, hL, hv⟩
    refine ⟨dualSheaf L, hL.dual, ?_⟩
    change toSkeleton (dualSheaf L) = ((v⁻¹ : (Skeleton X.Modules)ˣ) : Skeleton X.Modules)
    apply Units.eq_inv_of_mul_eq_one_left
    rw [← hv, mul_comm]
    exact toSkeleton_dualSheaf_mul hL

abbrev Pic : Type (u + 1) := ↥(picardSubgroup X)

variable {X}

namespace Pic

noncomputable def mk (L : X.Modules) (hL : IsInvertibleSheaf L) : Pic X :=
  ⟨unitOfInvertible hL, L, hL, rfl⟩

def toClass (p : Pic X) : Skeleton X.Modules := ((p : ↥(picardSubgroup X)) : (Skeleton X.Modules)ˣ)

theorem mk_eq_mk_iff {L M : X.Modules} (hL : IsInvertibleSheaf L) (hM : IsInvertibleSheaf M) :
    mk L hL = mk M hM ↔ Nonempty (L ≅ M) := by
  rw [← toSkeleton_eq_toSkeleton_iff]
  constructor
  · intro h
    exact congrArg toClass h
  · intro h
    apply Subtype.ext
    apply Units.ext
    exact h

theorem mk_tensor {L M : X.Modules} (hL : IsInvertibleSheaf L) (hM : IsInvertibleSheaf M) :
    mk (L ⊗ M) (hL.tensor hM) = mk L hL * mk M hM := by
  apply Subtype.ext
  apply Units.ext
  exact Skeleton.toSkeleton_tensorObj L M

theorem mk_unit : mk (𝟙_ X.Modules) isInvertibleSheaf_unit = 1 := by
  apply Subtype.ext
  apply Units.ext
  rfl

theorem mk_dualSheaf {L : X.Modules} (hL : IsInvertibleSheaf L) :
    mk (dualSheaf L) hL.dual = (mk L hL)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← mk_tensor, ← mk_unit, mk_eq_mk_iff]
  have := isIso_dualEval hL
  exact ⟨asIso (dualEval L)⟩

theorem mk_eq_one_iff {L : X.Modules} (hL : IsInvertibleSheaf L) :
    mk L hL = 1 ↔ Nonempty (L ≅ 𝟙_ X.Modules) := by
  rw [← mk_unit, mk_eq_mk_iff]

end Pic

end GroundTheory.Arith.SchemeCoh
end

section
namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

noncomputable def weilDivisorToPic : WeilDivisor X →+ Additive (Pic X) where
  toFun D := Additive.ofMul (Pic.mk (divisorSheaf D) (isInvertibleSheaf_divisorSheaf D))
  map_zero' := by
    rw [ofMul_eq_zero, ← Pic.mk_unit, Pic.mk_eq_mk_iff]
    exact ⟨divisorSheafZeroIso.symm⟩
  map_add' D E := by
    rw [← ofMul_mul, ← Pic.mk_tensor]
    congr 1
    exact (Pic.mk_eq_mk_iff _ _).mpr ⟨(divisorTensorIso D E).symm⟩

lemma weilDivisorToPic_apply (D : WeilDivisor X) :
    weilDivisorToPic D =
      Additive.ofMul (Pic.mk (divisorSheaf D) (isInvertibleSheaf_divisorSheaf D)) := rfl

theorem ker_weilDivisorToPic : (weilDivisorToPic (X := X)).ker = principalDivisors X := by
  ext D
  rw [AddMonoidHom.mem_ker, weilDivisorToPic_apply, ofMul_eq_zero, Pic.mk_eq_one_iff,
    ← sub_zero D, ← nonempty_divisorSheaf_iso_iff, sub_zero]
  constructor
  · rintro ⟨e⟩
    exact ⟨e ≪≫ divisorSheafZeroIso⟩
  · rintro ⟨e⟩
    exact ⟨e ≪≫ divisorSheafZeroIso.symm⟩

end GroundTheory.Arith.SchemeCoh
end

section
open CategoryTheory AlgebraicGeometry Order Topology Module MonoidalCategory

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsNoetherian X] [IsLocallyFactorial X] [IsProper (X ↘ Spec (.of k))]
  [IsFunctionField k X.functionField]

omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in

noncomputable def invertibleDegree {L : X.Modules} (hL : IsInvertibleSheaf L) : ℤ :=
  WeilDivisor.degree (k := k) (divisorOfInvertible hL)

omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in

lemma nonempty_iso_of_weilDivisorToPic {M : X.Modules} (hM : IsInvertibleSheaf M)
    {D : WeilDivisor X} (h : Additive.ofMul (Pic.mk M hM) = weilDivisorToPic D) :
    Nonempty (M ≅ divisorSheaf D) := by
  rw [weilDivisorToPic_apply] at h
  exact (Pic.mk_eq_mk_iff _ _).mp (Additive.ofMul.injective h)

omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in

theorem nonempty_tensor_dualSheaf_iso (D : WeilDivisor X) {L : X.Modules}
    (hL : IsInvertibleSheaf L) {E : WeilDivisor X} (e : L ≅ divisorSheaf E) :
    Nonempty (divisorSheaf D ⊗ dualSheaf L ≅ divisorSheaf (D - E)) := by
  refine nonempty_iso_of_weilDivisorToPic ((isInvertibleSheaf_divisorSheaf D).tensor hL.dual) ?_
  have hLE : Pic.mk L hL = Pic.mk (divisorSheaf E) (isInvertibleSheaf_divisorSheaf E) :=
    (Pic.mk_eq_mk_iff _ _).mpr ⟨e⟩
  rw [Pic.mk_tensor (isInvertibleSheaf_divisorSheaf D) hL.dual, Pic.mk_dualSheaf hL, hLE, map_sub,
    weilDivisorToPic_apply, weilDivisorToPic_apply, ofMul_mul, ofMul_inv, sub_eq_add_neg]

variable (hX : topologicalKrullDim X ≤ 1)

noncomputable def canonicalDifferential : WeilDifferential k X.functionField :=
  (WeilDifferential.exists_ne_zero (k := k) (K := X.functionField)).choose

omit [AlgebraicGeometry.IsNoetherian X] [IsLocallyFactorial X] [IsProper (X ↘ Spec (.of k))] in
lemma canonicalDifferential_ne_zero : canonicalDifferential (k := k) (X := X) ≠ 0 :=
  (WeilDifferential.exists_ne_zero (k := k) (K := X.functionField)).choose_spec

noncomputable def canonicalDivisor : WeilDivisor X :=
  (divisorEquiv (k := k) hX).symm (canonicalDifferential (k := k) (X := X)).divisor

lemma divisorEquiv_canonicalDivisor :
    divisorEquiv (k := k) hX (canonicalDivisor (k := k) hX) =
      (canonicalDifferential (k := k) (X := X)).divisor := by
  simp [canonicalDivisor]

noncomputable def canonicalSheaf : X.Modules :=
  divisorSheaf (canonicalDivisor (k := k) hX)

end GroundTheory.Arith.SchemeCoh
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Module MonoidalCategory

universe w' u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

noncomputable def HLinearEquivOfIso [IsIntegral X] {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    Sheaf.H.{w'} (modulesAb F) n ≃ₗ[k] Sheaf.H.{w'} (modulesAb G) n :=
  ((H.moduleFunctor.{w'} k n).mapIso e).toLinearEquiv

variable [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [IsNormalScheme X]

section Instances

variable (hX : topologicalKrullDim X = 1)

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
include hX in

theorem curve_instances :
    IsNoetherian X ∧ IsLocallyFactorial X ∧ IsFunctionField k X.functionField := by
  have : IsNoetherian X := isNoetherian_of_finiteType (k := k) X
  exact ⟨this, isLocallyFactorial_of_dim_le_one hX.le, isFunctionField X hX⟩

end Instances

section Genus

variable (X) in

noncomputable def structureSheafModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

variable (k X) in

noncomputable def genus : ℕ :=
  finrank k (Sheaf.H.{w'} (modulesAb (structureSheafModule X)) 1)

end Genus

section Degree

end Degree

section Canonical

noncomputable def omega (hX : topologicalKrullDim X = 1) : X.Modules :=
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  haveI := (curve_instances (k := k) hX).2.2
  canonicalSheaf (k := k) hX.le

end Canonical

section RiemannRoch

end RiemannRoch

end GroundTheory.Arith.SchemeCoh
end
