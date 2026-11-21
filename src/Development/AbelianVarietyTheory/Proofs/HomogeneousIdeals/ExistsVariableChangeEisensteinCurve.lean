import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomExtOfLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver

section
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeightScale

variable {A B : Type*} [CommRing A] [CommRing B]

def curve (u : A) (V : WeierstrassCurve A) : WeierstrassCurve A :=
  ⟨u * V.a₁, u ^ 2 * V.a₂, u ^ 3 * V.a₃, u ^ 4 * V.a₄, u ^ 6 * V.a₆⟩

def triple (u : A) (P : Fin 3 → A) : Fin 3 → A := ![u ^ 2 * P 0, u ^ 3 * P 1, P 2]


theorem map_curve (g : A →+* B) (u : A) (V : WeierstrassCurve A) :
    (curve u V).map g = curve (g u) (V.map g) := by
  ext <;> simp [curve]

theorem curve_map_eq (g : A →+* B) {u : A} {V : WeierstrassCurve A} (h : curve u V = V) :
    curve (g u) (V.map g) = V.map g := by
  rw [← map_curve, h]


theorem triple_triple (u v : A) (P : Fin 3 → A) : triple u (triple v P) = triple (u * v) P := by
  ext i; fin_cases i <;> simp [triple] <;> ring


theorem equation_triple (u : A) {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : V.toProjective.Equation P) : (curve u V).toProjective.Equation (triple u P) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [curve, triple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination u ^ 6 * h

theorem span_le_span_triple {u : A} (hu : IsUnit u) (P : Fin 3 → A) :
    Ideal.span (Set.range P) ≤ Ideal.span (Set.range (triple u P)) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow 2)).mp (Ideal.subset_span ⟨0, rfl⟩)
  · exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow 3)).mp (Ideal.subset_span ⟨1, rfl⟩)
  · exact Ideal.subset_span ⟨2, rfl⟩

theorem isUnimodularSol_triple {u : A} (hu : IsUnit u) {V : WeierstrassCurve A}
    (hV : curve u V = V) {P : Fin 3 → A} (h : IsUnimodularSol V P) :
    IsUnimodularSol V (triple u P) :=
  ⟨hV ▸ equation_triple u h.equation,
    top_le_iff.mp (h.span_eq_top.ge.trans (span_le_span_triple hu P))⟩

open WeierstrassCurve.Projective in
theorem addXYZ_triple (u : A) (V : WeierstrassCurve A) (P Q : Fin 3 → A) :
    (curve u V).toProjective.addXYZ (triple u P) (triple u Q) =
      u ^ 6 • triple u (V.toProjective.addXYZ P Q) := by
  ext i
  fin_cases i <;>
    simp [curve, triple, addXYZ, addX, addY, negAddY, addZ, negY] <;> ring

open WeierstrassCurve.Projective in
theorem diagXYZ_triple (u : A) (V : WeierstrassCurve A) (P Q : Fin 3 → A) :
    diagXYZ (curve u V).toProjective (triple u P) (triple u Q) =
      u ^ 9 • triple u (diagXYZ V.toProjective P Q) := by
  ext i
  fin_cases i <;>
    simp [curve, triple, diagXYZ, diagX, diagY, negDiagY, diagZ, negY] <;> ring

theorem proportional_triple (u c : A) {T S : Fin 3 → A} (h : Proportional T S) :
    Proportional (triple u T) (c • triple u S) := by
  refine (Proportional.smul_left (fun i j => ?_) c).symm
  fin_cases i <;> fin_cases j <;> simp only [triple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linear_combination u ^ 5 * h 1 0
  · linear_combination u ^ 2 * h 2 0
  · linear_combination u ^ 5 * h 0 1
  · linear_combination u ^ 3 * h 2 1
  · linear_combination u ^ 2 * h 0 2
  · linear_combination u ^ 3 * h 1 2

theorem isSumTriple_triple {u : A} {V : WeierstrassCurve A} (hV : curve u V = V)
    {P Q T : Fin 3 → A} (h : IsSumTriple V P Q T) :
    IsSumTriple V (triple u P) (triple u Q) (triple u T) := by
  have h₁ := addXYZ_triple u V P Q
  have h₂ := diagXYZ_triple u V P Q
  rw [hV] at h₁ h₂
  exact ⟨h₁ ▸ proportional_triple u _ h.add, h₂ ▸ proportional_triple u _ h.diag⟩

open WeierstrassCurve.Projective in
theorem isSumTriple_cubeRoot {w : A} (hw : w ^ 2 + w + 1 = 0) {X Y Z : A}
    (h : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve A).toProjective.Equation ![X, Y, Z]) :
    IsSumTriple ⟨0, 0, 1, 0, 0⟩ ![X, Y, Z] ![w * X, Y, Z] ![w ^ 2 * X, -Y - Z, Z] := by
  rw [WeierstrassCurve.Projective.equation_iff] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [addXYZ, addX, addY, negAddY, addZ, diagXYZ, diagX, diagY, negDiagY, diagZ, negY] <;>
    grind

end GlobalTheory.WeightScale
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

noncomputable section

namespace GlobalTheory.WeightScale

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) {u : R} (hu : IsUnit u)
  (hW : curve u W = W)

def scaledCoord (u : R) : Fin 3 → HomRing W := triple (algebraMap R _ u) (coord W)

theorem scaledCoord_mem (u : R) (i : Fin 3) : scaledCoord W u i ∈ grading W 1 := by
  fin_cases i
  · change algebraMap R _ u ^ 2 * coord W 0 ∈ _
    rw [← map_pow, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (coord_mem W 0)
  · change algebraMap R _ u ^ 3 * coord W 1 ∈ _
    rw [← map_pow, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (coord_mem W 1)
  · exact coord_mem W 2

include hW in
theorem equation_scaledCoord :
    (W.map (algebraMap R (HomRing W))).toProjective.Equation (scaledCoord W u) := by
  have := equation_triple (algebraMap R (HomRing W) u) (V := W.map (algebraMap R (HomRing W)))
    (equation_coord W)
  rwa [curve_map_eq _ hW] at this

def scaleGraded : grading W →+*ᵍ grading W where
  toRingHom := evalHom W (algebraMap R (HomRing W)) (scaledCoord W u) (equation_scaledCoord W hW)
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    have hp' : p.IsHomogeneous n := hp
    change MvPolynomial.eval₂ (algebraMap R (HomRing W)) (scaledCoord W u) p ∈ _
    rw [MvPolynomial.eval₂_eq]
    refine Submodule.sum_mem _ fun d hd => ?_
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    have := SetLike.prod_pow_mem_graded (grading W) (fun _ => 1) (scaledCoord W u)
      (F := d.support) d (fun i _ => scaledCoord_mem W u i)
    rw [hp'.degree_eq_sum_deg_support hd]
    simpa using this

include hu in
theorem irrelevant_le_map_scaleGraded :
    irrelevant (grading W) ≤ (irrelevant (grading W)).map (scaleGraded W hW) := by
  rw [← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord]
  refine (span_le_span_triple (hu.map (algebraMap R (HomRing W))) (coord W)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have : triple (algebraMap R (HomRing W) u) (coord W) i = scaleGraded W hW (coord W i) :=
    (evalHom_coord W (algebraMap R (HomRing W)) (scaledCoord W u)
      (equation_scaledCoord W hW) i).symm
  rw [this]
  exact Ideal.mem_map_of_mem (scaleGraded W hW) (mem_irrelevant_of_mem _ one_pos (coord_mem W i))

def scaleMap : scheme W ⟶ scheme W :=
  Proj.map (scaleGraded W hW) (irrelevant_le_map_scaleGraded W hu hW)

@[reassoc]
theorem ptHom_scaleMap {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ scaleMap W hu hW = ptHom W ρ (triple (ρ u) P)
      (isUnimodularSol_triple (hu.map ρ) (curve_map_eq ρ hW) hP) := by
  refine (ProjPoint.ofHom_map (scaleGraded W hW) (irrelevant_le_map_scaleGraded W hu hW) _
    (map_irrelevant_evalHom W hP)).trans ?_
  have : (evalHom W ρ P hP.equation).comp (scaleGraded W hW).toRingHom =
      evalHom W ρ _ (isUnimodularSol_triple (hu.map ρ) (curve_map_eq ρ hW) hP).equation := by
    refine homRing_hom_ext W (fun r => ?_) (fun i => ?_)
    · refine (congrArg (evalHom W ρ P hP.equation) (evalHom_algebraMap W _ (scaledCoord W u)
        (equation_scaledCoord W hW) r)).trans ?_
      rw [evalHom_algebraMap, evalHom_algebraMap]
    refine (congrArg (evalHom W ρ P hP.equation) (evalHom_coord W _ (scaledCoord W u)
      (equation_scaledCoord W hW) i)).trans ?_
    rw [evalHom_coord]
    fin_cases i <;> simp [scaledCoord, triple]
  simp only [this]
  rfl

theorem scaleMap_toSpec : scaleMap W hu hW ≫ toSpec W = toSpec W := by
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_scaleMap_assoc, ptHom_toSpec, ptHom_toSpec]
  · rw [chartZ, pt_eq_ptHom, ptHom_scaleMap_assoc, ptHom_toSpec, ptHom_toSpec]

def scaleOver : schemeOver W ⟶ schemeOver W :=
  Over.homMk (scaleMap W hu hW) (scaleMap_toSpec W hu hW)

theorem ptOver_scaleOver {A : Type} [CommRing A] [Algebra R A] (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.baseChange A) P) :
    ptOver W P hP ≫ scaleOver W hu hW = ptOver W (triple (algebraMap R A u) P)
      (isUnimodularSol_triple (hu.map _) (curve_map_eq (algebraMap R A) hW) hP) :=
  Over.OverMorphism.ext (ptHom_scaleMap W hu hW _ P hP)

omit hu hW in

theorem over_hom_ext_of_isLocalRing {T Y : Over (Spec (.of R))} {f g : T ⟶ Y}
    (h : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra R A] (x : specOver R A ⟶ T),
      x ≫ f = x ≫ g) : f = g := by
  refine Over.OverMorphism.ext (hom_ext_of_localRing_points _ _ _ _ fun A _ _ t => ?_)
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (t ≫ T.hom)
  let : Algebra R A := ρ.hom.toAlgebra
  exact congrArg (·.left) (h A (Over.homMk t hρ.symm))

omit hu hW in

theorem over_hom_ext_ptOver {Y : Over (Spec (.of R))} {f g : schemeOver W ⟶ Y}
    (h : ∀ (A : Type) [CommRing A] [Algebra R A] (P : Fin 3 → A)
      (hP : IsUnimodularSol (W.baseChange A) P), ptOver W P hP ≫ f = ptOver W P hP ≫ g) : f = g :=
  over_hom_ext_of_isLocalRing fun A _ _ _ x => by
    obtain ⟨P, hP, rfl⟩ := exists_eq_ptOver W x
    exact h A P hP

omit hu hW in
theorem ptOver_congr {A : Type} [CommRing A] [Algebra R A] {P Q : Fin 3 → A}
    {hP : IsUnimodularSol (W.baseChange A) P} {hQ : IsUnimodularSol (W.baseChange A) Q}
    (e : P = Q) : ptOver W P hP = ptOver W Q hQ := by
  subst e; rfl

omit hu hW in

theorem exists_isSumTriple [W.IsElliptic] {A : Type} [CommRing A] [IsLocalRing A] [Algebra R A]
    {P Q : Fin 3 → A} (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    ∃ S, IsUnimodularSol (W.baseChange A) S ∧ IsSumTriple (W.baseChange A) P Q S := by
  obtain ⟨S, hS, h, -⟩ := exists_ptOver_mul_ptOver_eq W hP hQ
  refine ⟨S, hS, ?_⟩
  rcases h with rfl | rfl
  exacts [isSumTriple_addXYZ hP.equation hQ.equation, isSumTriple_diagXYZ hP.equation hQ.equation]

theorem isMonHom_scaleOver [W.IsElliptic] : IsMonHom (scaleOver W hu hW) := by
  have key : μ[schemeOver W] ≫ scaleOver W hu hW =
      (scaleOver W hu hW ⊗ₘ scaleOver W hu hW) ≫ μ[schemeOver W] :=
    over_hom_ext_of_isLocalRing fun A _ _ _ x => by
      rw [← lift_comp_fst_snd x, lift_map_assoc, ← Category.assoc]
      obtain ⟨P, hP, eP⟩ := exists_eq_ptOver W (x ≫ fst _ _)
      obtain ⟨Q, hQ, eQ⟩ := exists_eq_ptOver W (x ≫ snd _ _)
      obtain ⟨S, hS, h⟩ := exists_isSumTriple W hP hQ
      rw [eP, eQ, ← Hom.mul_def, ← Hom.mul_def, ptOver_mul_ptOver W hP hQ hS h, ptOver_scaleOver,
        ptOver_scaleOver, ptOver_scaleOver]
      exact (ptOver_mul_ptOver W _ _ _ (isSumTriple_triple (curve_map_eq _ hW) h)).symm
  refine ⟨?_, key⟩
  have e : (η[schemeOver W] * η[schemeOver W]) ≫ scaleOver W hu hW =
      (η[schemeOver W] ≫ scaleOver W hu hW) * (η[schemeOver W] ≫ scaleOver W hu hW) := by
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, key, lift_map_assoc]
  have h1 : η[schemeOver W] = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  rw [h1] at e ⊢
  rw [_root_.mul_one] at e
  exact mul_eq_left.1 e.symm

omit hu hW in

def AddsByLaws (m : schemeOver W ⊗ schemeOver W ⟶ schemeOver W) : Prop :=
  ∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (hT : IsUnimodularSol (W.map ρ) T),
    (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧
      Proportional T (diagXYZ (W.map ρ).toProjective P Q)) →
    ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP →
      y.left = ptHom W ρ Q hQ → (lift x y ≫ m).left = ptHom W ρ T hT

omit hu hW in

theorem AddsByLaws.unique [W.IsElliptic] {m m' : schemeOver W ⊗ schemeOver W ⟶ schemeOver W}
    (hm : AddsByLaws W m) (hm' : AddsByLaws W m') : m = m' :=
  over_hom_ext_of_isLocalRing fun A _ _ _ x => by
    rw [← lift_comp_fst_snd x]
    obtain ⟨P, hP, eP⟩ := exists_eq_ptOver W (x ≫ fst _ _)
    obtain ⟨Q, hQ, eQ⟩ := exists_eq_ptOver W (x ≫ snd _ _)
    obtain ⟨S, hS, h⟩ := exists_isSumTriple W hP hQ
    rw [eP, eQ]
    exact Over.OverMorphism.ext ((hm A _ P Q S hP hQ hS ⟨h.1, h.2⟩ _ _ rfl rfl).trans
      (hm' A _ P Q S hP hQ hS ⟨h.1, h.2⟩ _ _ rfl rfl).symm)

end GlobalTheory.WeightScale
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.QuadraticAction

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def comb (φ : G ⟶ G) (m n : ℤ) : G ⟶ G := (𝟙 G) ^ m * φ ^ n

omit [IsCommMonObj G] in
theorem comb_one_zero (φ : G ⟶ G) : comb φ 1 0 = 𝟙 G := by simp [comb]

theorem isMonHom_zpow (f : G ⟶ G) [IsMonHom f] (n : ℤ) : IsMonHom (f ^ n) := by
  have h1 : IsMonHom (1 : G ⟶ G) := by rw [Hom.one_def]; infer_instance
  have hm : ∀ f g : G ⟶ G, IsMonHom f → IsMonHom g → IsMonHom (f * g) := fun f g _ _ => by
    rw [Hom.mul_def]; infer_instance
  induction n using Int.induction_on with
  | zero => rwa [zpow_zero]
  | succ n h => rw [zpow_add_one]; exact hm _ _ h inferInstance
  | pred n h => rw [zpow_sub_one]; exact hm _ _ h inferInstance

theorem isMonHom_comb (φ : G ⟶ G) [IsMonHom φ] (m n : ℤ) : IsMonHom (comb φ m n) := by
  have := isMonHom_zpow (𝟙 G) m
  have := isMonHom_zpow φ n
  rw [comb, Hom.mul_def]
  infer_instance

theorem comb_add (φ : G ⟶ G) (m n m' n' : ℤ) :
    comb φ (m + m') (n + n') = comb φ m n * comb φ m' n' := by
  simp only [comb, zpow_add]
  exact mul_mul_mul_comm _ _ _ _

theorem zpow_identity {M : Type*} [CommGroup M] (x y : M) (a b m n m' n' : ℤ) :
    (x ^ m * y ^ n) ^ m' * (y ^ m * (x ^ a * y ^ b) ^ n) ^ n' =
      x ^ (m * m' + a * n * n') * y ^ (m * n' + n * m' + b * n * n') := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

theorem comb_comp (φ : G ⟶ G) [IsMonHom φ] {a b : ℤ} (h : φ ≫ φ = comb φ a b) (m n m' n' : ℤ) :
    comb φ m n ≫ comb φ m' n' =
      comb φ (m * m' + a * n * n') (m * n' + n * m' + b * n * n') := by
  have e : comb φ m n ≫ φ = φ ^ m * comb φ a b ^ n := by
    rw [comb, MonObj.mul_comp, GrpObj.zpow_comp, GrpObj.zpow_comp, Category.id_comp, h]
  conv_lhs => rw [comb.eq_1 φ m' n', MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow,
    Category.comp_id, e]
  exact zpow_identity (M := G ⟶ G) _ _ _ _ _ _ _ _

def quadAct (φ : G ⟶ G) [IsMonHom φ] {a b : ℤ} (h : φ ≫ φ = comb φ a b) :
    OAct (QuadraticAlgebra ℤ a b) G where
  act z := comb φ z.re z.im
  hom _ := isMonHom_comb ..
  one := comb_one_zero φ
  mul z w := by rw [comb_comp φ h, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  add z w := comb_add ..

def zsqrtdAct (φ : G ⟶ G) [IsMonHom φ] {d : ℤ} (h : φ ≫ φ = comb φ d 0) :
    OAct (ℤ√d) G where
  act z := comb φ z.re z.im
  hom _ := isMonHom_comb ..
  one := comb_one_zero φ
  mul z w := by rw [comb_comp φ h, Zsqrtd.re_mul, Zsqrtd.im_mul]; simp
  add z w := comb_add ..

end Act

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

end Lie

end GlobalTheory.QuadraticAction
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw GlobalTheory.WeightScale GlobalTheory.QuadraticAction

noncomputable section

namespace GlobalTheory.CMCurve

variable {R : Type} [CommRing R]

variable (R) in

def gaussianCurve : WeierstrassCurve R := ⟨0, 0, 0, -1, 0⟩

theorem gaussianCurve_Δ : (gaussianCurve R).Δ = 2 ^ 6 := by
  simp [gaussianCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num


section Gaussian

variable {i : R} (hi : i ^ 2 = -1)
include hi

theorem neg_mul_self_eq_one : -i * i = 1 := by linear_combination -hi

theorem curve_gaussianCurve : curve (-i) (gaussianCurve R) = gaussianCurve R := by
  ext <;> simp only [curve, gaussianCurve, mul_zero]
  linear_combination (1 - i ^ 2) * hi

def gaussianAut : schemeOver (gaussianCurve R) ⟶ schemeOver (gaussianCurve R) :=
  scaleOver _ (IsUnit.of_mul_eq_one _ (neg_mul_self_eq_one hi)) (curve_gaussianCurve hi)

variable [(gaussianCurve R).IsElliptic]

instance isMonHom_gaussianAut : IsMonHom (gaussianAut hi) := isMonHom_scaleOver ..

theorem gaussianAut_sq : gaussianAut hi ≫ gaussianAut hi = ι[schemeOver (gaussianCurve R)] := by
  refine over_hom_ext_ptOver _ fun A _ _ P hP => ?_
  rw [← Hom.inv_def, ptOver_inv, gaussianAut, ← Category.assoc, ptOver_scaleOver]
  refine (ptOver_scaleOver _ _ _ _ _).trans (ptOver_congr _ ?_)
  rw [triple_triple, ← map_mul, show -i * -i = -1 by linear_combination hi]
  ext j
  fin_cases j <;> simp [triple, WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY,
    gaussianCurve, WeierstrassCurve.baseChange]
  ring

def gaussianAct : OAct GaussianInt (schemeOver (gaussianCurve R)) :=
  zsqrtdAct (gaussianAut hi) (by
    rw [gaussianAut_sq, comb, zpow_zero, _root_.mul_one, zpow_neg_one, Hom.inv_def,
      Category.id_comp])

end Gaussian

variable (R) in

def eisensteinCurve : WeierstrassCurve R := ⟨0, 0, 1, 0, 0⟩

theorem eisensteinCurve_Δ : (eisensteinCurve R).Δ = -3 ^ 3 := by
  simp [eisensteinCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

theorem isElliptic_eisensteinCurve (h3 : IsUnit (3 : R)) : (eisensteinCurve R).IsElliptic :=
  ⟨eisensteinCurve_Δ (R := R) ▸ (h3.pow 3).neg⟩

section Eisenstein

variable {w : R} (hw : w ^ 2 + w + 1 = 0)
include hw

theorem sq_mul_self_eq_one : w ^ 2 * w = 1 := by linear_combination (w - 1) * hw

theorem curve_eisensteinCurve : curve (w ^ 2) (eisensteinCurve R) = eisensteinCurve R := by
  ext <;> simp only [curve, eisensteinCurve, mul_zero]
  linear_combination (w ^ 3 + 1) * sq_mul_self_eq_one hw

theorem triple_sq {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) :
    triple (ρ (w ^ 2)) P = ![ρ w * P 0, P 1, P 2] := by
  have h : ρ w ^ 2 * ρ w = 1 := by rw [← map_pow, ← map_mul, sq_mul_self_eq_one hw, map_one]
  rw [triple, map_pow]
  congr 1
  · linear_combination (ρ w * P 0) * h
  · congr 1
    linear_combination ((ρ w ^ 3 + 1) * P 1) * h

def eisensteinAut : schemeOver (eisensteinCurve R) ⟶ schemeOver (eisensteinCurve R) :=
  scaleOver _ (IsUnit.of_mul_eq_one _ (sq_mul_self_eq_one hw)) (curve_eisensteinCurve hw)

variable [(eisensteinCurve R).IsElliptic]

instance isMonHom_eisensteinAut : IsMonHom (eisensteinAut hw) := isMonHom_scaleOver ..

theorem eisensteinAut_sq :
    (eisensteinAut hw ≫ eisensteinAut hw) * eisensteinAut hw * 𝟙 _ = 1 := by
  rw [_root_.mul_assoc, mul_eq_one_iff_inv_eq, _root_.mul_comm]
  refine over_hom_ext_ptOver _ fun A _ _ P hP => ?_
  rw [GrpObj.comp_inv, MonObj.comp_mul, Category.comp_id, eisensteinAut, ← Category.assoc,
    ptOver_scaleOver]
  refine ((congrArg (·⁻¹) (ptOver_scaleOver _ _ _ _ _)).trans (ptOver_inv _ _)).trans
    (ptOver_mul_ptOver _ _ _ _ ?_).symm
  have e : (eisensteinCurve R).baseChange A = ⟨0, 0, 1, 0, 0⟩ := by
    ext <;> simp [eisensteinCurve, WeierstrassCurve.baseChange]
  have hA : algebraMap R A w ^ 2 + algebraMap R A w + 1 = 0 := by
    simpa using congrArg (algebraMap R A) hw
  have hE := hP.equation
  rw [e, ← WeierstrassCurve.Projective.fin3_def P] at hE
  have := isSumTriple_cubeRoot hA hE
  rw [WeierstrassCurve.Projective.fin3_def] at this
  rw [e, triple_sq hw, triple_sq hw]
  convert this using 1
  ext j
  fin_cases j <;> simp [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY]
  ring

end Eisenstein

example : ∃ i : Localization.Away (2 : GaussianInt), i ^ 2 = -1 ∧
    IsUnit (2 : Localization.Away (2 : GaussianInt)) ∧
    CharZero (Localization.Away (2 : GaussianInt)) := by
  refine ⟨algebraMap GaussianInt _ ⟨0, 1⟩, ?_, ?_, ?_⟩
  · rw [← map_pow, show (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 by decide, map_neg, map_one]
  · simpa only [map_ofNat] using IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (2 : GaussianInt)) (2 : GaussianInt)
  · exact charZero_of_injective_algebraMap (R := GaussianInt) (IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (two_ne_zero (α := GaussianInt))))

end GlobalTheory.CMCurve
end
end
