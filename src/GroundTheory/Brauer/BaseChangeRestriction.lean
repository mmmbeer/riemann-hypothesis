import Mathlib
import GroundTheory.Brauer.CrossedProductIso
import GroundTheory.Brauer.CrossedProductInj
import GroundTheory.Brauer.CrossedProductTensor
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open groupCohomology

universe u

namespace CrossedProduct

section Inflate

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]

theorem algebraMap_restrictNormalHom (σ : L' ≃ₐ[K] L') (x : L) :
    algebraMap L L' (AlgEquiv.restrictNormalHom L σ x) = σ (algebraMap L L' x) :=
  AlgEquiv.restrictNormal_commutes σ L x

theorem map_smul_restrictNormalHom (σ : L' ≃ₐ[K] L') (c : L) (y : L') :
    σ (c • y) = AlgEquiv.restrictNormalHom L σ c • σ y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, algebraMap_restrictNormalHom]

theorem unitsMap_smul (σ : L' ≃ₐ[K] L') (m : Lˣ) :
    Units.map (algebraMap L L' : L →* L') (AlgEquiv.restrictNormalHom L σ • m) =
      σ • Units.map (algebraMap L L' : L →* L') m := by
  ext
  exact algebraMap_restrictNormalHom σ (m : L)

variable (L') in

def inflate (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L') → L'ˣ :=
  fun p => Units.map (algebraMap L L' : L →* L')
    (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))

theorem val_inflate (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (p : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L')) :
    ((inflate L' f p : L'ˣ) : L') =
      algebraMap L L' (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2)) :=
  rfl

variable (L') in

theorem isMulCocycle₂_inflate {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (inflate L' f) :=
  (H2mul.mapCocycles₂ (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    unitsMap_smul ⟨f, hf⟩).2

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L L')

def galMatrix (σ : L' ≃ₐ[K] L') : Matrix ι ι L :=
  fun i j => b.repr (σ (b j)) i

omit [DecidableEq ι] in

theorem repr_apply_algEquiv (σ : L' ≃ₐ[K] L') (x : L') (i : ι) :
    b.repr (σ x) i = ∑ j, galMatrix b σ i j * AlgEquiv.restrictNormalHom L σ (b.repr x j) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul_restrictNormalHom, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, galMatrix]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

omit [DecidableEq ι] in

theorem galMatrix_mul (σ τ : L' ≃ₐ[K] L') :
    galMatrix b (σ * τ) = galMatrix b σ * (galMatrix b τ).map (AlgEquiv.restrictNormalHom L σ) := by
  ext i k
  change b.repr ((σ * τ) (b k)) i = _
  rw [AlgEquiv.mul_apply, repr_apply_algEquiv, Matrix.mul_apply]
  rfl

omit [Algebra K L] [IsScalarTower K L L'] [Normal K L] [Fintype ι] in

theorem galMatrix_one : galMatrix b (1 : L' ≃ₐ[K] L') = 1 := by
  ext i j
  simp only [galMatrix, AlgEquiv.one_apply, Module.Basis.repr_self, Finsupp.single_apply,
    Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

theorem galMatrix_mul_leftMulMatrix (σ : L' ≃ₐ[K] L') (a : L') :
    galMatrix b σ * (Algebra.leftMulMatrix b a).map (AlgEquiv.restrictNormalHom L σ) =
      Algebra.leftMulMatrix b (σ a) * galMatrix b σ := by
  ext i k
  have h : b.repr (σ (a * b k)) i =
      ∑ j, galMatrix b σ i j * AlgEquiv.restrictNormalHom L σ (Algebra.leftMulMatrix b a j k) := by
    rw [repr_apply_algEquiv]
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [← h, map_mul, ← Algebra.leftMulMatrix_mulVec_repr]
  rfl

end Basis

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L L')
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)

def inflateIncl : L' →ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  (incl : L →ₐ[K] CrossedProduct hf).mapMatrix.comp ((Algebra.leftMulMatrix b).restrictScalars K)

def inflateU (σ : L' ≃ₐ[K] L') : Matrix ι ι (CrossedProduct hf) :=
  (galMatrix b σ).map incl * Matrix.diagonal fun _ => u (AlgEquiv.restrictNormalHom L σ)

omit [Normal K L] in
theorem inflateIncl_apply (a : L') :
    inflateIncl b hf a = (Algebra.leftMulMatrix b a).map incl :=
  rfl

omit [IsScalarTower K L L'] [Normal K L] in

theorem diagonal_u_mul_map_incl (τ : L ≃ₐ[K] L) (M : Matrix ι ι L) :
    (Matrix.diagonal fun _ => (u τ : CrossedProduct hf)) * M.map incl =
      (M.map τ).map incl * Matrix.diagonal fun _ => (u τ : CrossedProduct hf) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, u_mul_incl]

omit [IsScalarTower K L L'] [Normal K L] in

theorem diagonal_u_mul_diagonal_u (σ τ : L ≃ₐ[K] L) :
    (Matrix.diagonal fun _ => (u σ : CrossedProduct hf)) * Matrix.diagonal (fun _ => u τ) =
      (algebraMap L (Matrix ι ι L) (f (σ, τ) : L)).map incl *
        Matrix.diagonal fun _ => (u (σ * τ) : CrossedProduct hf) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext _
  simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact u_mul_u σ τ

theorem inflateU_mul_inflateIncl (σ : L' ≃ₐ[K] L') (a : L') :
    inflateU b hf σ * inflateIncl b hf a = inflateIncl b hf (σ a) * inflateU b hf σ := by
  rw [inflateU, inflateIncl_apply, inflateIncl_apply, mul_assoc, diagonal_u_mul_map_incl,
    ← mul_assoc, ← Matrix.map_mul, galMatrix_mul_leftMulMatrix, Matrix.map_mul, mul_assoc]

theorem inflateU_mul_inflateU (σ τ : L' ≃ₐ[K] L') :
    inflateU b hf σ * inflateU b hf τ =
      inflateIncl b hf (inflate L' f (σ, τ) : L') * inflateU b hf (σ * τ) := by
  rw [inflateU, inflateU, inflateU, inflateIncl_apply, val_inflate, mul_assoc,
    ← mul_assoc (Matrix.diagonal _), diagonal_u_mul_map_incl, mul_assoc,
    diagonal_u_mul_diagonal_u, ← mul_assoc, ← mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul,
    ← galMatrix_mul, ← map_mul, AlgHom.commutes, ← mul_assoc, ← Matrix.map_mul,
    Algebra.commutes]

theorem inflateU_one :
    inflateU b hf 1 = inflateIncl b hf (inflate L' f (1, 1) : L') := by
  rw [inflateU, inflateIncl_apply, val_inflate, map_one, galMatrix_one, AlgHom.commutes,
    Matrix.map_one _ (map_zero _) (map_one _), one_mul, u_one, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_map (map_zero _)]
  rfl

def inflateHom :
    CrossedProduct (isMulCocycle₂_inflate L' hf) →ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  lift (inflateIncl b hf) (inflateU b hf) (inflateU_mul_inflateIncl b hf)
    (inflateU_mul_inflateU b hf) (inflateU_one b hf)

variable [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K L'] [IsGalois K L']
  [Nonempty ι]

theorem inflateHom_bijective : Function.Bijective (inflateHom b hf) := by
  have hinj : Function.Injective (inflateHom b hf) :=
    RingHom.injective (inflateHom b hf).toRingHom
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank K (CrossedProduct (isMulCocycle₂_inflate L' hf)) =
      Module.finrank K (Matrix ι ι (CrossedProduct hf)) := by
    rw [finrank_eq_sq, Module.finrank_matrix, finrank_eq_sq, ← Module.finrank_eq_card_basis b,
      ← Module.finrank_mul_finrank K L L']
    ring
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (inflateHom b hf).toLinearMap)).1 hinj

def inflateAlgEquiv :
    CrossedProduct (isMulCocycle₂_inflate L' hf) ≃ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  AlgEquiv.ofBijective _ (inflateHom_bijective b hf)

end Matrix

end Inflate

section Brauer

variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']

variable (L') in

theorem isBrauerEquivalent_inflate {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsBrauerEquivalent (csaOf K (CrossedProduct (isMulCocycle₂_inflate L' hf)))
      (csaOf K (CrossedProduct hf)) := by
  have : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite K L L'
  have : Nonempty (Fin (Module.finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact isBrauerEquivalent_of_algEquiv_matrix (C := CrossedProduct hf)
    (inflateAlgEquiv (Module.finBasis L L') hf) (matrixFinOneAlgEquiv (CrossedProduct hf)).symm

end Brauer

end CrossedProduct

namespace BrauerGroup

variable (K L L' : Type u) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L']

theorem relBrauer_le_relBrauer : relBrauer K L ≤ relBrauer K L' := by
  intro x hx
  rw [mem_relBrauer_iff] at hx ⊢
  rw [← baseChange_baseChange K L L', hx, map_one]

end BrauerGroup

namespace H2mul

section Inflation

variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]

def inflation : H2mul (L ≃ₐ[K] L) Lˣ →* H2mul (L' ≃ₐ[K] L') L'ˣ :=
  mapPair (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    CrossedProduct.unitsMap_smul

variable {K L L'}

theorem inflation_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    inflation K L L' (mk _ _ c) =
      mk _ _ ⟨CrossedProduct.inflate L' (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ),
        CrossedProduct.isMulCocycle₂_inflate L' c.2⟩ :=
  rfl

end Inflation

section Brauer

variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']

theorem toBrauer_inflation (x : H2mul (L ≃ₐ[K] L) Lˣ) :
    toBrauer K L' (inflation K L L' x) = toBrauer K L x := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [inflation_mk, toBrauer_mk, toBrauer_mk]
  exact Quotient.sound (CrossedProduct.isBrauerEquivalent_inflate L' c.2)

theorem inflation_injective : Function.Injective (inflation K L L') := by
  intro x y h
  apply toBrauer_injective (K := K) (L := L)
  have h' := congrArg (toBrauer K L') h
  rwa [toBrauer_inflation, toBrauer_inflation] at h'

end Brauer

end H2mul

end GroundTheory.Brauer

end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

namespace H2mul

section Bridge

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem ofMul_mem_cocycles₂_galUnits (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    (fun p => Additive.ofMul ((c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) p)) ∈
      cocycles₂ (galUnits.{u} K L) := by
  rw [mem_cocycles₂_iff]
  intro g h j
  exact congrArg Additive.ofMul ((mem_mulCocycles₂_iff _).1 c.2 g h j)

def galUnitsCocycle (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) : cocycles₂ (galUnits.{u} K L) :=
  ⟨_, ofMul_mem_cocycles₂_galUnits c⟩

@[simp]
theorem galUnitsCocycle_apply (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) :
    galUnitsCocycle c p = Additive.ofMul ((c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) p) :=
  rfl

def toGalUnitsH2 : mulCocycles₂ (L ≃ₐ[K] L) Lˣ →* Multiplicative (H2 (galUnits.{u} K L)) where
  toFun c := Multiplicative.ofAdd (H2π (galUnits.{u} K L) (galUnitsCocycle c))
  map_one' := by
    have h0 : galUnitsCocycle (1 : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) = 0 := Subtype.ext rfl
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    rw [h0, map_zero]
  map_mul' c c' := by
    rw [← ofAdd_add]
    congr 1
    rw [← map_add]
    rfl

theorem toGalUnitsH2_eq_one_iff (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    toGalUnitsH2 c = 1 ↔ IsMulCoboundary₂ (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) := by
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0 ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, H2π_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun g => Additive.toMul (x g), fun g h => ?_⟩
    exact congrArg Additive.toMul (congrFun hx (g, h))
  · rintro ⟨x, hx⟩
    exact ⟨fun g => Additive.ofMul (x g), funext fun p => congrArg Additive.ofMul (hx p.1 p.2)⟩

def galUnitsEquivH2 : H2mul (L ≃ₐ[K] L) Lˣ ≃* Multiplicative (H2 (galUnits.{u} K L)) :=
  MulEquiv.ofBijective
    (QuotientGroup.lift _ toGalUnitsH2 (fun c hc => (toGalUnitsH2_eq_one_iff c).2 hc)) (by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x
      induction x using induction_on with
      | h c =>
        intro hx
        exact (mk_eq_one_iff c).2 ((toGalUnitsH2_eq_one_iff c).1 hx)
    · intro y
      induction y using Multiplicative.rec with
      | ofAdd y =>
      induction y using H2_induction_on with
      | h y =>
      refine ⟨mk _ _ ⟨fun p => Additive.toMul (y p), fun g h j => ?_⟩, rfl⟩
      exact congrArg Additive.toMul ((mem_cocycles₂_iff (y : _ → Additive Lˣ)).1 y.2 g h j))

@[simp]
theorem galUnitsEquivH2_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    galUnitsEquivH2 (mk _ _ c) = Multiplicative.ofAdd (H2π (galUnits.{u} K L) (galUnitsCocycle c)) :=
  rfl

end Bridge

end H2mul

section Tower

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
  [Algebra E F] [IsScalarTower K E F] [Normal K E]

variable (K E F) in

def galUnitsInclusion :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E) (galUnits.{u} K E) ⟶
      galUnits.{u} K F :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Eˣ) (B := Additive Fˣ) (MonoidHom.toAdditive
    (Units.map ((algebraMap E F : E →+* F) : E →* F))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ E ((Additive.toMul (α := Eˣ) x : Eˣ) : E)⟩

@[simp]
theorem galUnitsInclusion_hom_apply (x : Additive Eˣ) :
    ((Additive.toMul (α := Fˣ) ((galUnitsInclusion K E F).hom x) : Fˣ) : F) =
      algebraMap E F ((Additive.toMul (α := Eˣ) x : Eˣ) : E) :=
  rfl

theorem galUnitsEquivH2_inflation (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    H2mul.galUnitsEquivH2 (H2mul.inflation K E F x) = Multiplicative.ofAdd
      (groupCohomology.map (AlgEquiv.restrictNormalHom E) (galUnitsInclusion K E F) 2
        (Multiplicative.toAdd (H2mul.galUnitsEquivH2 x))) := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [H2mul.inflation_mk, H2mul.galUnitsEquivH2_mk, H2mul.galUnitsEquivH2_mk, toAdd_ofAdd,
    H2π_comp_map_apply]
  congr 2

end Tower

section Absolute

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

theorem coe_algebraMap_intermediateField {E F : IntermediateField K Ks} [Algebra E F]
    [IsScalarTower E F Ks] (y : E) : ((algebraMap E F y : F) : Ks) = (y : Ks) :=
  (IsScalarTower.algebraMap_apply E F Ks y).symm

variable [IsGalois K Ks]

variable (K) in

def unitsInflationH2 (E : IntermediateField K Ks) [FiniteDimensional K E] [Normal K E] :
    H2 (galUnits.{u} K E) ⟶ cohomology (galUnits.{u} K Ks) 2 :=
  HomologicalComplex.homologyMap (unitsInflationCochains E) 2

theorem map_comp_unitsInflationH2 (E F : IntermediateField K Ks) [FiniteDimensional K E]
    [Normal K E] [FiniteDimensional K F] [Normal K F] [Algebra E F] [IsScalarTower K E F]
    [IsScalarTower E F Ks] :
    groupCohomology.map (AlgEquiv.restrictNormalHom E) (galUnitsInclusion K E F) 2 ≫
      unitsInflationH2 K F = unitsInflationH2 K E := by
  unfold unitsInflationH2
  refine (HomologicalComplex.homologyMap_comp _ _ 2).symm.trans ?_
  congr 1
  ext n : 1
  rw [← cancel_mono ((cochainsComplexι (galUnits.{u} K Ks)).f n), HomologicalComplex.comp_f,
    Category.assoc]
  have hE := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (unitsInflationCochains_comp_cochainsComplexι (L := Ks) E)
  have hF := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (unitsInflationCochains_comp_cochainsComplexι (L := Ks) F)
  simp only [HomologicalComplex.comp_f] at hE hF
  rw [hE, hF, ← HomologicalComplex.comp_f, ← groupCohomology.cochainsMap_comp]
  congr 1
  refine cochainsMap_congr ?_ ?_
  · exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp K E F Ks).symm
  · refine LinearMap.ext fun x => Additive.toMul.injective (Units.ext ?_)
    exact coe_algebraMap_intermediateField ((Additive.toMul (α := Eˣ) x : Eˣ) : E)

theorem inflation_eq_iso_comp_unitsInflationH2 (U : OpenNormalSubgroup (Ks ≃ₐ[K] Ks)) :
    inflation (galUnits.{u} K Ks) U 2 = (groupCohomologyQuotientGalUnitsIso U 2).hom ≫
      unitsInflationH2 K (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks))) := by
  rw [groupCohomologyQuotientGalUnitsIso, mapIso_hom]
  unfold unitsInflationH2 inflation
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ 2)
  congr 1
  ext n : 1
  rw [← cancel_mono ((cochainsComplexι (galUnits.{u} K Ks)).f n), HomologicalComplex.comp_f,
    Category.assoc]
  have hU := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (inflationCochains_comp_cochainsComplexι (galUnits.{u} K Ks) U)
  have hE := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (unitsInflationCochains_comp_cochainsComplexι (L := Ks)
      (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks))))
  simp only [HomologicalComplex.comp_f] at hU hE
  rw [hU, hE, ← HomologicalComplex.comp_f, ← groupCohomology.cochainsMap_comp]
  congr 1
  refine cochainsMap_congr ?_ ?_
  · refine MonoidHom.ext fun σ => ?_
    change (σ : _ ⧸ _) = (quotientEquivGal U).symm (AlgEquiv.restrictNormalHom _ σ)
    rw [eq_comm, MulEquiv.symm_apply_eq]
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [quotientEquivGal_mk_apply, AlgEquiv.restrictNormalHom_apply]
  · exact LinearMap.ext fun x => Additive.toMul.injective (Units.ext rfl)

theorem transition_comp_iso_hom {U V : OpenNormalSubgroup (Ks ≃ₐ[K] Ks)} (h : V ≤ U)
    [Algebra (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))
      (IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks)))]
    [IsScalarTower K (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))
      (IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks)))]
    [IsScalarTower (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))
      (IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks))) Ks] :
    transition (galUnits.{u} K Ks) h 2 ≫ (groupCohomologyQuotientGalUnitsIso V 2).hom =
      (groupCohomologyQuotientGalUnitsIso U 2).hom ≫
        groupCohomology.map (AlgEquiv.restrictNormalHom _)
          (galUnitsInclusion K (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))
            (IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks)))) 2 := by
  rw [groupCohomologyQuotientGalUnitsIso, groupCohomologyQuotientGalUnitsIso, mapIso_hom,
    mapIso_hom, transition, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ 2
  · refine MonoidHom.ext fun τ => ?_
    obtain ⟨q, rfl⟩ := (quotientEquivGal V).surjective τ
    induction q using QuotientGroup.induction_on with
    | H σ =>
    change quotientMapOfLE h ((quotientEquivGal V).symm (quotientEquivGal V σ)) =
      (quotientEquivGal U).symm (AlgEquiv.restrictNormalHom _ (quotientEquivGal V σ))
    rw [MulEquiv.symm_apply_apply, quotientMapOfLE_mk, eq_comm, MulEquiv.symm_apply_eq]
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [quotientEquivGal_mk_apply, ← coe_algebraMap_intermediateField
      (F := IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks))),
      CrossedProduct.algebraMap_restrictNormalHom, quotientEquivGal_mk_apply,
      coe_algebraMap_intermediateField]
  · refine LinearMap.ext fun x => Additive.toMul.injective (Units.ext ?_)
    exact Subtype.ext (coe_algebraMap_intermediateField
      (F := IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks)))
      (⟨_, mem_fixedField_of_mem_invariants_galUnits _ x.2⟩ :
        IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))).symm

end Absolute

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

section Galois

variable [IsGalois K Ks]

variable (K) in

def inflationToAbsolute (E : IntermediateField K Ks) [FiniteDimensional K E] [IsGalois K E] :
    H2mul (E ≃ₐ[K] E) Eˣ →* Multiplicative (cohomology (galUnits.{u} K Ks) 2) :=
  (AddMonoidHom.toMultiplicative (unitsInflationH2 K E).hom.toAddMonoidHom).comp
    (H2mul.galUnitsEquivH2 : H2mul (E ≃ₐ[K] E) Eˣ ≃* _).toMonoidHom

theorem inflationToAbsolute_apply (E : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    inflationToAbsolute K E x = Multiplicative.ofAdd
      ((unitsInflationH2 K E).hom (Multiplicative.toAdd (H2mul.galUnitsEquivH2 x))) :=
  rfl

theorem inflationToAbsolute_inflation (E F : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] [FiniteDimensional K F] [IsGalois K F] [Algebra E F] [IsScalarTower K E F]
    [IsScalarTower E F Ks] (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    inflationToAbsolute K F (H2mul.inflation K E F x) = inflationToAbsolute K E x := by
  rw [inflationToAbsolute_apply, inflationToAbsolute_apply, galUnitsEquivH2_inflation, toAdd_ofAdd]
  congr 1
  exact congrArg (fun φ => φ.hom (Multiplicative.toAdd (H2mul.galUnitsEquivH2 x)))
    (map_comp_unitsInflationH2 E F)

theorem exists_inflationToAbsolute_eq (x : Multiplicative (cohomology (galUnits.{u} K Ks) 2)) :
    ∃ (E : IntermediateField K Ks) (_ : FiniteDimensional K E) (_ : IsGalois K E)
      (y : H2mul (E ≃ₐ[K] E) Eˣ), inflationToAbsolute K E y = x := by
  obtain ⟨U, z, hz⟩ := exists_inflation_eq (galUnits.{u} K Ks) 2 (Multiplicative.toAdd x)
  refine ⟨IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)), inferInstance, inferInstance,
    H2mul.galUnitsEquivH2.symm
      (Multiplicative.ofAdd ((groupCohomologyQuotientGalUnitsIso U 2).hom z)), ?_⟩
  rw [inflationToAbsolute_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, ← hz, inflation_eq_iso_comp_unitsInflationH2]
  rfl

theorem inflationToAbsolute_injective (E : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] : Function.Injective (inflationToAbsolute K E) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  let U : OpenNormalSubgroup (Ks ≃ₐ[K] Ks) :=
    fixingOpenNormalSubgroup ({ toIntermediateField := E } : FiniteGaloisIntermediateField K Ks)
  let E' := IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks))
  have hEE' : E ≤ E' := fun x hx => (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx
  let _ : Algebra E E' := (IntermediateField.inclusion hEE').toAlgebra
  have : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E E' Ks := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← inflationToAbsolute_inflation E E'] at hy
  set y' := H2mul.inflation K E E' y with hy'
  set z := Multiplicative.toAdd (H2mul.galUnitsEquivH2 y') with hz
  obtain ⟨V, hVU, hV⟩ := exists_transition_eq_zero (galUnits.{u} K Ks) 2 U
    ((groupCohomologyQuotientGalUnitsIso U 2).inv z) (by
      rw [inflation_eq_iso_comp_unitsInflationH2]
      change (unitsInflationH2 K E').hom
        ((groupCohomologyQuotientGalUnitsIso U 2).hom.hom
          ((groupCohomologyQuotientGalUnitsIso U 2).inv.hom z)) = 0
      rw [Iso.inv_hom_id_apply]
      exact congrArg Multiplicative.toAdd hy)
  let E'' := IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks))
  have hE'E'' : E' ≤ E'' := fun x hx => (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ =>
    (IntermediateField.mem_fixedField_iff _ _).1 hx σ (hVU hσ)
  let _ : Algebra E' E'' := (IntermediateField.inclusion hE'E'').toAlgebra
  have : IsScalarTower K E' E'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E' E'' Ks := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 := congrArg (groupCohomologyQuotientGalUnitsIso V 2).hom.hom hV
  rw [map_zero] at h2
  change (transition (galUnits.{u} K Ks) hVU 2 ≫ (groupCohomologyQuotientGalUnitsIso V 2).hom).hom
    ((groupCohomologyQuotientGalUnitsIso U 2).inv.hom z) = 0 at h2
  rw [transition_comp_iso_hom hVU] at h2
  change (groupCohomology.map (AlgEquiv.restrictNormalHom _) (galUnitsInclusion K E' E'') 2).hom
    ((groupCohomologyQuotientGalUnitsIso U 2).hom.hom
      ((groupCohomologyQuotientGalUnitsIso U 2).inv.hom z)) = 0 at h2
  rw [Iso.inv_hom_id_apply, hz] at h2
  have h3 : H2mul.galUnitsEquivH2 (H2mul.inflation K E' E'' y') = 1 := by
    rw [galUnitsEquivH2_inflation, h2]
    rfl
  rw [MulEquivClass.map_eq_one_iff] at h3
  have h4 : y' = 1 := H2mul.inflation_injective (K := K) (L := E') (L' := E'') (by rw [h3, map_one])
  exact H2mul.inflation_injective (K := K) (L := E) (L' := E') (by rw [← hy', h4, map_one])

theorem inflationToAbsolute_symm_relBrauerEquiv_of_le {E F : IntermediateField K Ks}
    [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional K F] [IsGalois K F] (hEF : E ≤ F)
    (b : BrauerGroup.{u, u} K) (hb : b ∈ BrauerGroup.relBrauer K E)
    (hb' : b ∈ BrauerGroup.relBrauer K F) :
    inflationToAbsolute K E ((H2mul.relBrauerEquiv K E).symm ⟨b, hb⟩) =
      inflationToAbsolute K F ((H2mul.relBrauerEquiv K F).symm ⟨b, hb'⟩) := by
  let _ : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E F Ks := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← inflationToAbsolute_inflation E F]
  congr 1
  apply (H2mul.relBrauerEquiv K F).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [H2mul.coe_relBrauerEquiv, H2mul.toBrauer_inflation, ← H2mul.coe_relBrauerEquiv,
    MulEquiv.apply_symm_apply]

theorem inflationToAbsolute_symm_relBrauerEquiv_eq {E F : IntermediateField K Ks}
    [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional K F] [IsGalois K F]
    (b : BrauerGroup.{u, u} K) (hb : b ∈ BrauerGroup.relBrauer K E)
    (hb' : b ∈ BrauerGroup.relBrauer K F) :
    inflationToAbsolute K E ((H2mul.relBrauerEquiv K E).symm ⟨b, hb⟩) =
      inflationToAbsolute K F ((H2mul.relBrauerEquiv K F).symm ⟨b, hb'⟩) := by
  have hE : E ≤ E ⊔ F := le_sup_left
  have hF : F ≤ E ⊔ F := le_sup_right
  have hbEF : b ∈ BrauerGroup.relBrauer K ↥(E ⊔ F) := by
    let _ : Algebra E ↥(E ⊔ F) := (IntermediateField.inclusion hE).toAlgebra
    have : IsScalarTower K E ↥(E ⊔ F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact BrauerGroup.relBrauer_le_relBrauer K E _ hb
  rw [inflationToAbsolute_symm_relBrauerEquiv_of_le hE b hb hbEF,
    inflationToAbsolute_symm_relBrauerEquiv_of_le hF b hb' hbEF]

end Galois

end Main

section SepClosure

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

theorem BrauerGroup.exists_finiteGalois_mem_relBrauer (b : BrauerGroup.{u, u} K) :
    ∃ E : FiniteGaloisIntermediateField K Ks, b ∈ BrauerGroup.relBrauer K E := by
  obtain ⟨L, _, _, _, _, hb⟩ := BrauerGroup.exists_mem_relBrauer b
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  let σ : L →ₐ[K] Ks := IsSepClosed.lift
  let e : L ≃ₐ[K] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  let _ : Algebra L σ.fieldRange := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K L σ.fieldRange :=
    IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  have : FiniteDimensional K σ.fieldRange := e.toLinearEquiv.finiteDimensional
  have : IsGalois K σ.fieldRange := IsGalois.of_algEquiv e
  exact ⟨{ toIntermediateField := σ.fieldRange }, BrauerGroup.relBrauer_le_relBrauer K L _ hb⟩

variable (K Ks) in

def brauerToH2Fun (b : BrauerGroup.{u, u} K) : Multiplicative (cohomology (galUnits.{u} K Ks) 2) :=
  inflationToAbsolute K
    (BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b).choose.toIntermediateField
    ((H2mul.relBrauerEquiv K _).symm
      ⟨b, (BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b).choose_spec⟩)

theorem brauerToH2Fun_eq (b : BrauerGroup.{u, u} K) (E : IntermediateField K Ks)
    [FiniteDimensional K E] [IsGalois K E] (hb : b ∈ BrauerGroup.relBrauer K E) :
    brauerToH2Fun K Ks b = inflationToAbsolute K E ((H2mul.relBrauerEquiv K E).symm ⟨b, hb⟩) :=
  inflationToAbsolute_symm_relBrauerEquiv_eq b _ hb

variable (K Ks) in

def brauerToH2 : BrauerGroup.{u, u} K →* Multiplicative (cohomology (galUnits.{u} K Ks) 2) where
  toFun := brauerToH2Fun K Ks
  map_one' := by
    obtain ⟨E, hE⟩ := BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) (1 : BrauerGroup.{u, u} K)
    rw [brauerToH2Fun_eq 1 E.toIntermediateField hE]
    exact (map_one ((inflationToAbsolute K E.toIntermediateField).comp
      (H2mul.relBrauerEquiv K E).symm.toMonoidHom) :)
  map_mul' b b' := by
    obtain ⟨E, hb⟩ := BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b
    obtain ⟨E', hb'⟩ := BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b'
    let F := E ⊔ E'
    have hbF : b ∈ BrauerGroup.relBrauer K F := by
      let _ : Algebra E F := (IntermediateField.inclusion
        (le_sup_left : E.toIntermediateField ≤ F.toIntermediateField)).toAlgebra
      have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact BrauerGroup.relBrauer_le_relBrauer K E F hb
    have hb'F : b' ∈ BrauerGroup.relBrauer K F := by
      let _ : Algebra E' F := (IntermediateField.inclusion
        (le_sup_right : E'.toIntermediateField ≤ F.toIntermediateField)).toAlgebra
      have : IsScalarTower K E' F := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact BrauerGroup.relBrauer_le_relBrauer K E' F hb'
    rw [brauerToH2Fun_eq b F.toIntermediateField hbF, brauerToH2Fun_eq b' F.toIntermediateField hb'F,
      brauerToH2Fun_eq (b * b') F.toIntermediateField (mul_mem hbF hb'F), ← map_mul, ← map_mul]
    rfl

theorem brauerToH2_eq (b : BrauerGroup.{u, u} K) (E : IntermediateField K Ks)
    [FiniteDimensional K E] [IsGalois K E] (hb : b ∈ BrauerGroup.relBrauer K E) :
    brauerToH2 K Ks b = inflationToAbsolute K E ((H2mul.relBrauerEquiv K E).symm ⟨b, hb⟩) :=
  brauerToH2Fun_eq b E hb

theorem brauerToH2_relBrauerEquiv (E : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    brauerToH2 K Ks (H2mul.relBrauerEquiv K E x) = inflationToAbsolute K E x := by
  rw [brauerToH2_eq _ E (H2mul.relBrauerEquiv K E x).2]
  congr 1
  exact (H2mul.relBrauerEquiv K E).symm_apply_apply x

theorem brauerToH2_injective : Function.Injective (brauerToH2 K Ks) := by
  rw [injective_iff_map_eq_one]
  intro b hb1
  obtain ⟨E, hb⟩ := BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b
  rw [brauerToH2_eq b E.toIntermediateField hb] at hb1
  have h := (injective_iff_map_eq_one _).1 (inflationToAbsolute_injective E.toIntermediateField) _ hb1
  rw [MulEquiv.symm_apply_eq, map_one] at h
  exact congrArg Subtype.val h

theorem brauerToH2_surjective : Function.Surjective (brauerToH2 K Ks) := by
  intro x
  obtain ⟨E, _, _, y, rfl⟩ := exists_inflationToAbsolute_eq (K := K) x
  exact ⟨_, brauerToH2_relBrauerEquiv E y⟩

variable (K Ks) in

def brauerEquivH2 : BrauerGroup.{u, u} K ≃* Multiplicative (cohomologicalBrauerGroup K Ks) :=
  MulEquiv.ofBijective (brauerToH2 K Ks) ⟨brauerToH2_injective, brauerToH2_surjective⟩

end SepClosure

end GroundTheory.Brauer
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open Module groupCohomology

open scoped TensorProduct

universe u

namespace CrossedProduct

section Restrict

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]

variable (K E) in

def resCocycle (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : (L ≃ₐ[E] L) × (L ≃ₐ[E] L) → Lˣ :=
  fun p => f (p.1.restrictScalars K, p.2.restrictScalars K)

@[simp]
theorem resCocycle_apply (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (p : (L ≃ₐ[E] L) × (L ≃ₐ[E] L)) :
    resCocycle K E f p = f (p.1.restrictScalars K, p.2.restrictScalars K) :=
  rfl

theorem isMulCocycle₂_resCocycle {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (resCocycle K E f) := by
  intro g h j
  exact hf (g.restrictScalars K) (h.restrictScalars K) (j.restrictScalars K)

end Restrict

section Action

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)

variable (E) in

def inclBase : E →ₐ[K] CrossedProduct hf :=
  (incl (hf := hf)).comp (IsScalarTower.toAlgHom K E L)

theorem inclBase_apply (e : E) : inclBase E hf e = incl (algebraMap E L e) :=
  rfl

theorem incl_mul_inclBase (a : L) (e : E) :
    incl a * inclBase E hf e = inclBase E hf e * (incl a : CrossedProduct hf) := by
  rw [inclBase_apply, ← map_mul, mul_comm, map_mul]

theorem u_mul_inclBase (τ : L ≃ₐ[E] L) (e : E) :
    u (τ.restrictScalars K) * inclBase E hf e = inclBase E hf e * (u (τ.restrictScalars K) : CrossedProduct hf) := by
  rw [inclBase_apply, u_mul_incl, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]

def rightMulEnd (c : CrossedProduct hf) (hc : ∀ e : E, c * inclBase E hf e = inclBase E hf e * c) :
    Module.End E (RightMul (inclBase E hf)) where
  toFun x := RightMul.of _ (x.val * c)
  map_add' x y := add_mul x.val y.val c
  map_smul' e x := by
    change x.val * inclBase E hf e * c = x.val * c * inclBase E hf e
    rw [mul_assoc, ← hc, mul_assoc]

def rightInclHom : L →ₐ[E] (Module.End E (RightMul (inclBase E hf)))ᵐᵒᵖ where
  toFun a := MulOpposite.op (rightMulEnd hf (incl a) (incl_mul_inclBase hf a))
  map_one' := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl 1) = x
    rw [map_one, mul_one]
    rfl
  map_mul' a b := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (a * b)) = RightMul.of _ ((x.val * incl a) * incl b)
    rw [map_mul, mul_assoc]
  map_zero' := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl 0) = 0
    rw [map_zero, mul_zero]
    rfl
  map_add' a b := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (a + b)) = RightMul.of _ (x.val * incl a + x.val * incl b)
    rw [map_add, mul_add]
  commutes' e := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (algebraMap E L e)) = e • x
    rfl

def rightSymbol (τ : L ≃ₐ[E] L) : (Module.End E (RightMul (inclBase E hf)))ᵐᵒᵖ :=
  MulOpposite.op (rightMulEnd hf (u (τ.restrictScalars K)) (u_mul_inclBase hf τ))

end Action

section Main

variable {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)

end Main

end CrossedProduct

namespace H2mul

section Res

variable (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]

def resBase : H2mul (L ≃ₐ[K] L) Lˣ →* H2mul (L ≃ₐ[E] L) Lˣ :=
  mapPair (AlgEquiv.restrictScalarsHom K) (MonoidHom.id Lˣ) (fun _ _ => rfl)

variable {K E L}

end Res

section Brauer

variable {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K L]

end Brauer

end H2mul

end GroundTheory.Brauer
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

section Cocycles

variable {k : Type u} [CommRing k] {H : Type u} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] {B : Rep.{u} k H} [IsDiscreteRep B]

theorem homologyMap_H2π {G : Type u} [Group G] {A : Rep.{u} k G}
    (F : inhomogeneousCochains A ⟶ cochainsComplex B) (c : cocycles₂ A) :
    (HomologicalComplex.homologyMap F 2).hom (H2π A c) =
      (cohomologyπ B 2).hom ((HomologicalComplex.cyclesMap F 2).hom ((isoCocycles₂ A).inv.hom c)) := by
  exact congrArg (fun φ => φ.hom ((isoCocycles₂ A).inv.hom c))
    (HomologicalComplex.homologyπ_naturality F 2)

theorem homologyMap_H2π_eq {G₁ G₂ : Type u} [Group G₁] [Group G₂] {A₁ : Rep.{u} k G₁}
    {A₂ : Rep.{u} k G₂} (F₁ : inhomogeneousCochains A₁ ⟶ cochainsComplex B)
    (F₂ : inhomogeneousCochains A₂ ⟶ cochainsComplex B) (c₁ : cocycles₂ A₁) (c₂ : cocycles₂ A₂)
    (h : ((cochainsComplexι B).f 2).hom ((F₁.f 2).hom ((cochainsIso₂ A₁).inv.hom c₁)) =
      ((cochainsComplexι B).f 2).hom ((F₂.f 2).hom ((cochainsIso₂ A₂).inv.hom c₂))) :
    (HomologicalComplex.homologyMap F₁ 2).hom (H2π A₁ c₁) =
      (HomologicalComplex.homologyMap F₂ 2).hom (H2π A₂ c₂) := by
  rw [homologyMap_H2π, homologyMap_H2π]
  congr 1
  apply (ModuleCat.mono_iff_injective ((cochainsComplex B).iCycles 2)).1 inferInstance
  have hi : ∀ {G : Type u} [Group G] {A : Rep.{u} k G}
      (F : inhomogeneousCochains A ⟶ cochainsComplex B) (c : cocycles₂ A),
      ((cochainsComplex B).iCycles 2).hom ((HomologicalComplex.cyclesMap F 2).hom
        ((isoCocycles₂ A).inv.hom c)) = (F.f 2).hom ((cochainsIso₂ A).inv.hom c) := by
    intro G _ A F c
    change ((HomologicalComplex.cyclesMap F 2 ≫ (cochainsComplex B).iCycles 2).hom
      ((isoCocycles₂ A).inv.hom c)) = _
    rw [HomologicalComplex.cyclesMap_i]
    change (F.f 2).hom ((((isoCocycles₂ A).inv ≫ iCocycles A 2)).hom c) = _
    rw [isoCocycles₂_inv_comp_iCocycles]
    rfl
  rw [hi, hi]
  exact (ModuleCat.mono_iff_injective ((cochainsComplexι B).f 2)).1 inferInstance h

end Cocycles

section Topology

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

theorem continuous_restrictScalarsHom (E : IntermediateField K Ks) :
    Continuous (AlgEquiv.restrictScalarsHom K : (Ks ≃ₐ[E] Ks) →* (Ks ≃ₐ[K] Ks)) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨S, hS, hSs⟩ := (krullTopology_mem_nhds_one_iff K Ks s).1 hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis K S
  let T : Set Ks := Set.range fun i => (b i : Ks)
  refine ⟨IntermediateField.adjoin E T, ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact ((IsIntegral.of_finite K (b i)).map S.val).tower_top
  · intro σ hσ
    apply hSs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hT : ∀ i, (AlgEquiv.restrictScalarsHom K σ) (b i : Ks) = b i := fun i =>
      hσ _ (IntermediateField.subset_adjoin E T ⟨i, rfl⟩)
    have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ks) := by
      calc x = S.val (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ks) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => map_smul S.val _ _
    rw [hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT]

def galUnitsRestrictScalars (E : IntermediateField K Ks) :
    Rep.res (AlgEquiv.restrictScalarsHom K : (Ks ≃ₐ[E] Ks) →* (Ks ≃ₐ[K] Ks)) (galUnits.{u} K Ks) ⟶
      galUnits.{u} E Ks :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Ksˣ) (B := Additive Ksˣ) (AddMonoidHom.id _),
    fun σ => by
      ext x
      rfl⟩

@[simp]
theorem galUnitsRestrictScalars_hom_apply (E : IntermediateField K Ks) (x : Additive Ksˣ) :
    (galUnitsRestrictScalars E).hom x = x :=
  rfl

end Topology

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

instance isSepClosure_intermediateField (E : IntermediateField K Ks) : IsSepClosure E Ks :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ks⟩

variable (E : IntermediateField K Ks)

instance isDiscreteRep_res_fixingSubgroup :
    IsDiscreteRep (Rep.res E.fixingSubgroup.subtype (galUnits.{u} K Ks)) :=
  isDiscreteRep_res_subtype _ _

end Main

end GroundTheory.Brauer
end
end
