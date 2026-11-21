import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperZeroTriple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Definitions.Degenerations.LabKerUnique

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace DimZero
open Out.Inh GlobalTheory.ZM.Model

theorem translT_zero {T : Over S} (x : T ⟶ (zeroPolAV S).A) : (Out.translT (zeroPolAV S).A x).left = 𝟙 _ := by
  have : Out.translT (zeroPolAV S).A x = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [Out.translT]
    · exact toUnit_unique _ _
  rw [this]; rfl

theorem exists_gen {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : ∃ t : L.Gen, t.IsGen ∧ ∀ i, t.s i = 1 :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm, fun _ => rfl⟩

theorem corr_comm {X Y : Scheme.{0}} (L : LB X) [Unique L.ι] {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L φ ε)) (b : LB.Gen (LB.LinComb L φ' ε)) (h h' : Y ⟶ Y) (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j' _ _ _
  obtain rfl : j = fun _ => default := Subsingleton.elim _ _
  obtain rfl : j' = fun _ => default := Subsingleton.elim _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, DVR.res_res', DVR.res_res']
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (map_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (DVR.res_res' _ _ _)
  · exact (DVR.res_res' _ _ _).symm

theorem weilIs_zero (L : LB (zeroPolAV S).A.left) [Unique L.ι] (hL : ∀ i j, L.g i j = 1) (n : ℤ) {T : Over S}
    (x y : T ⟶ (zeroPolAV S).A) : Out.WeilIs (zeroPolAV S).A L n x y 1 := by
  intro p
  have ex : ∀ z : Out.overRes (T := T) ⊤ ⟶ (zeroPolAV S).A, ∃ θ : Out.ThetaGrp _ L n _, θ.pt = z := fun z => by
    obtain ⟨t, ht, -⟩ := exists_gen (Out.thetaLB _ L n z) (linComb_g_one L hL _ _)
    exact ⟨⟨z, t, ht⟩, rfl⟩
  refine ⟨⊤, trivial, ?_, fun θx θy _ _ => ?_⟩
  · obtain ⟨θx, hx⟩ := ex (Out.overResι ⊤ ≫ x)
    obtain ⟨θy, hy⟩ := ex (Out.overResι ⊤ ≫ y)
    exact ⟨θx, θy, hx, hy⟩
  · have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
    rw [hc]
    exact corr_comm L _ _ _ _ _ _ _ (translT_zero _) (translT_zero _) _
      (fun j => (congrArg _ (map_one _)).trans (map_one _))

def zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : SiegPre 0 k ζ s where
  A := (zeroPolAV S).A
  comm := (zeroPolAV S).isAb.comm
  ab := (zeroPolAV S).isAb
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  rig₂ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => by
    refine ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ => ⟨0, toUnit_unique _ _⟩, fun a a' => ?_⟩
    have h1 : unitOn (z ^ (2 * omegaStd a a')) = 1 := by
      have : omegaStd a a' = 0 := by simp [omegaStd]
      rw [this, mul_zero, zpow_zero]
      exact map_one _
    rw [h1]
    exact @weilIs_zero S _ (inferInstanceAs (Unique (PUnit → PUnit))) (linComb_triv_g _ _) _ _ _ _

theorem principal_zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : (zeroSieg k ζ s).Principal := by
  refine ⟨?_, fun _ _ _ => toUnit_unique _ _⟩
  generalize hM : (zeroSieg k ζ s).diag = M
  have hg : ∀ i j, M.g i j = 1 := by subst hM; exact linComb_triv_g _ _
  have hU : ∃ i, M.U i = ⊤ := by
    subst hM; exact ⟨fun _ => PUnit.unit, top_unique fun y _ => Set.mem_iInter.2 fun _ => trivial⟩
  obtain ⟨i₀, hi₀⟩ := hU
  change LB (𝟙_ (Over S)).left at M
  change Out.RelAmple (𝟙_ (Over S)) M
  intro U hU
  haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
  let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
  have hp : ∀ i j, (Out.powOver (𝟙_ (Over S)) M U 1).g i j = 1 := fun i j => by
    exact linComb_g_one M hg _ _ i j
  let s0 : LB.Sec (Out.powOver (𝟙_ (Over S)) M U 1) :=
    ⟨fun _ => 1, by
      intro i j; rw [hp, Units.val_one, _root_.one_mul]; repeat erw [map_one]
      all_goals rfl⟩
  have hD : Out.nonzeroLocus s0 = ⊤ := by
    apply top_unique
    intro x _
    simp only [Out.nonzeroLocus, s0, Scheme.basicOpen_one]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, Set.mem_iInter.2 fun _ => by
      show _ ∈ M.U i₀
      rw [hi₀]; trivial⟩
  refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
    fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [hD]
    have : IsAffine Y := hU
    exact isAffineOpen_top Y
  · intro j k
    erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
  · intro p
    obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩

def zeroBas (H : Host E) : (Fin (2 * 0) → ℤ) ≃ₗ[ℤ] (Test.zeroDatum H).La :=
  haveI : Subsingleton (Fin (2 * 0) → ℤ) := ⟨fun _ _ => funext fun i => i.elim0⟩
  haveI : Subsingleton (Test.zeroDatum H).La := inferInstanceAs (Subsingleton PUnit)
  LinearEquiv.ofSubsingleton _ _


end DimZero

end GlobalTheory.ZM
end
end

section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZM.Model

theorem isE8_W8 : IsE8 W8 := by
  unfold IsE8
  rw [w8_add_transpose_eq_e8]
  exact ⟨e8_posDef, e8_det_eq_one⟩




section Away
variable {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {n : ℕ} (hn : n ≠ 0)

def awayEmb : Localization.Away (n : 𝓞 F) →+* ℂ :=
  IsLocalization.Away.lift (n : 𝓞 F) (g := φ.comp (algebraMap (𝓞 F) F)) (by simpa using hn)


def tbaseAway (z : 𝓞 F) (hz : IsPrimitiveRoot z n) : TBase (Localization.Away (n : 𝓞 F)) n where
  ζ := Units.map (algebraMap (𝓞 F) (Localization.Away (n : 𝓞 F))).toMonoidHom (hz.isUnit hn).unit
  unit := by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F)) (n : 𝓞 F)
  prim := by
    intro K _ β
    have hu : IsUnit (n : Localization.Away (n : 𝓞 F)) := by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F)) (n : 𝓞 F)
    haveI : NeZero (n : K) := ⟨by simpa using (hu.map β).ne_zero⟩
    have h0 := (hz.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map
      (f := β.comp (algebraMap (𝓞 F) (Localization.Away (n : 𝓞 F))))
    rw [Polynomial.map_cyclotomic] at h0
    simpa using Polynomial.isRoot_cyclotomic_iff.1 h0
end Away

section Basis
variable (h : ℕ)

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (a : Fin g) : (halves g (.inl a) : ℕ) = a := by simp [halves]
theorem halves_inr (g : ℕ) (a : Fin g) : (halves g (.inr a) : ℕ) = g + a := by simp [halves, add_comm]

theorem sum_halves (g : ℕ) (i j : Fin (2 * g)) :
    ∑ a : Fin g, ((Pi.single i 1 : Fin (2 * g) → ℤ) (halves g (.inl a)) * (Pi.single j 1 : Fin (2 * g) → ℤ) (halves g (.inr a)) -
      (Pi.single i 1 : Fin (2 * g) → ℤ) (halves g (.inr a)) * (Pi.single j 1 : Fin (2 * g) → ℤ) (halves g (.inl a))) =
      Out.stdSymp g i j := by
  obtain ⟨i, rfl⟩ := (halves g).surjective i
  obtain ⟨j, rfl⟩ := (halves g).surjective j
  unfold Out.stdSymp
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Pi.single_apply, (halves g).injective.eq_iff, halves_inl, halves_inr, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, if_false, mul_zero, zero_mul, sub_zero, zero_sub, ite_mul, one_mul, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  all_goals
    try simp only [Fin.ext_iff]
    have := i.2
    have := j.2
    split_ifs <;> omega

def sharpBas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun x u := Sum.elim (fun i => x (halves _ (.inl (finProdFinEquiv (u, i)))))
    (fun i => ∑ v, E8inv u v * x (halves _ (.inr (finProdFinEquiv (v, i)))))
  invFun y k := Sum.elim (fun a => y (finProdFinEquiv.symm a).1 (.inl (finProdFinEquiv.symm a).2))
    (fun a => ∑ v, E8 (finProdFinEquiv.symm a).1 v * y v (.inr (finProdFinEquiv.symm a).2)) ((halves _).symm k)
  map_add' x y := by
    funext u i; rcases i with i | i <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext u i; rcases i with i | i <;> simp [Finset.mul_sum, mul_left_comm]
  left_inv x := by
    funext k
    obtain ⟨k, rfl⟩ := (halves _).surjective k
    rcases k with a | a
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl, Prod.mk.eta, Equiv.apply_symm_apply]
    · obtain ⟨⟨u, i⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Matrix.mul_apply, e8_mul_e8inv, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
  right_inv y := by
    funext u i
    rcases i with i | i
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl]
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Matrix.mul_apply, e8inv_mul_e8, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem dual_sum (y : Fin 8 → ℤ) (u : Fin 8) : ∑ v, E8 u v * ∑ w, E8inv v w * y w = y u := by
  have : E8.mulVec (E8inv.mulVec y) = y := by rw [Matrix.mulVec_mulVec, e8_mul_e8inv, Matrix.one_mulVec]
  exact congrFun this u

theorem sharp_form (x x' : Fin (2 * (8 * h)) → ℤ) :
    ∑ u, ∑ v, E8 u v * omegaStd (sharpBas h x u) (sharpBas h x' v) =
      ∑ a : Fin (8 * h), (x (halves _ (.inl a)) * x' (halves _ (.inr a)) - x (halves _ (.inr a)) * x' (halves _ (.inl a))) := by
  have hs : ∀ u v, E8 u v = E8 v u := fun u v => congrFun (congrFun e8_transpose v) u
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  have key : ∀ (A B : Fin 8 → Fin h → ℤ), ∑ u, ∑ v, ∑ i, E8 u v * (A u i * ∑ w, E8inv v w * B w i) = ∑ u, ∑ i, A u i * B u i := by
    intro A B
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← dual_sum (fun w => B w i) u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have k1 := key (fun u i => x (halves _ (.inl (finProdFinEquiv (u, i))))) (fun u i => x' (halves _ (.inr (finProdFinEquiv (u, i)))))
  have k2 := key (fun u i => x' (halves _ (.inl (finProdFinEquiv (u, i))))) (fun u i => x (halves _ (.inr (finProdFinEquiv (u, i)))))
  rw [Finset.sum_comm] at k2
  simp only [Finset.sum_sub_distrib]
  rw [← k1, show (∑ u, ∑ i, x (halves _ (.inr (finProdFinEquiv (u, i)))) * x' (halves _ (.inl (finProdFinEquiv (u, i))))) =
    ∑ u, ∑ i, x' (halves _ (.inl (finProdFinEquiv (u, i)))) * x (halves _ (.inr (finProdFinEquiv (u, i)))) from by
      simp only [mul_comm], ← k2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_sub_distrib, omegaStd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs v u]
  simp only [sharpBas, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
  ring

theorem isSharpBasis_sharpBas : IsSharpBasis W8 (sharpBas h) := by
  intro i j
  rw [w8_add_transpose_eq_e8, sharp_form, sum_halves]

end Basis

theorem exists_isE8_isSharpBasis : ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ∀ h : ℕ,
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas :=
  ⟨W8, isE8_W8, fun h => ⟨sharpBas h, isSharpBasis_sharpBas h⟩⟩


section Use
open AlgebraicGeometry CategoryTheory MonObj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}


end Use

section Zero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi Out.Inh
open scoped CategoryTheory.Obj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {k : ℕ} {J : Type}

theorem corr_comm_pull {X X' Y : Scheme.{0}} (f : X ⟶ X') {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb ((trivLB X').pull f) φ ε)) (b : LB.Gen (LB.LinComb ((trivLB X').pull f) φ' ε)) (h h' : Y ⟶ Y)
    (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb ((trivLB X').pull f) (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr ((trivLB X').pull f) _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j'
  obtain rfl : j = fun _ _ => PUnit.unit := rfl
  obtain rfl : j' = fun _ _ => PUnit.unit := rfl
  intro _ _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, ZH.RealModel.res_res, ZH.RealModel.res_res]
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (ZH.RealModel.res_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (ZH.RealModel.res_res _ _ _)
  · exact (ZH.RealModel.res_res _ _ _).symm

theorem isGen_one {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : (⟨fun _ => 1⟩ : L.Gen).IsGen := by
  intro i j; rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm

theorem weil_pull_zero {X : Scheme.{0}} (f : (𝟙_ (Over S)).left ⟶ X) (n : ℤ) {T : Over S} (x y : T ⟶ 𝟙_ (Over S)) :
    Out.WeilIs (𝟙_ (Over S)) ((trivLB X).pull f) n x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩,
    ⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩, rfl, rfl⟩, ?_⟩
  intro θx θy _ _
  have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [hc]
  exact corr_comm_pull _ _ _ _ _ _ _ _ (ZH.RealModel.translT_id S _) (ZH.RealModel.translT_id S _) _
    (fun j => (congrArg _ (map_one _)).trans (ZH.RealModel.res_one _))


def zeroSieg (ζ : o) (s : S ⟶ Sp o) : SiegPre 0 k ζ s where
  A := 𝟙_ (Over S)
  ab := UU.isAbelianScheme_unit S
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  rig₂ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 𝟙 _
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
    fun g _ => ⟨0, toUnit_unique _ _⟩, fun a b => by
      have : unitOn (z ^ (2 * omegaStd a b)) = 1 := by simp [omegaStd, unitOn]
      rw [this]; exact weil_pull_zero _ _ _ _⟩







end Zero

end GlobalTheory.ZM.Model
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM.SFamModel
open Out.Inh GlobalTheory.ZM.Model GlobalTheory.ZM.DimZero

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {k : ℕ}

theorem isIso_of_points [IsReduced S] (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hp : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y = 1) : IsIso A.hom := by
  haveI := h.proper
  haveI := h.smooth
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : Surjective e := ⟨fun a => by
    let K := AlgebraicClosure (A.left.residueField a)
    let y : Sp K ⟶ A.left := spMap (algebraMap (A.left.residueField a) K) ≫ A.left.fromSpecResidueField a
    have h1 := hp K (y ≫ A.hom) (Over.homMk y rfl)
    have h2 : y = (y ≫ A.hom) ≫ e := by
      have := congrArg (·.left) h1
      simpa [Hom.one_def, e, eSec] using this
    have h3 : y default = a := by
      simp only [y, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    exact ⟨(y ≫ A.hom) default, by rw [← Scheme.Hom.comp_apply, ← h2, h3]⟩⟩
  haveI : IsIso e := isIso_of_isClosedImmersion_of_surjective e
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem siegPB_zero {B : Type} [CommRing B] {ζ' : B} {s' : S' ⟶ Sp B} (c : SiegPre 0 k ζ' s') [IsIso c.A.hom]
    (ζ : o) (s : S ⟶ Sp o) (f : S' ⟶ S) : SiegPB c (zeroSieg k ζ s) f := by
  have uniq : ∀ {T : Over S'} (x y : T ⟶ c.A), x = y := fun x y =>
    Over.OverMorphism.ext (by rw [← cancel_mono c.A.hom, Over.w x, Over.w y])
  have aux : ∀ {X Y Z : Scheme.{0}} (u : X ⟶ S') (d : S ⟶ Z) (p : Z ⟶ S) (q : X ⟶ Y) (a : Y ⟶ S') (f : S' ⟶ S),
      d ≫ p = 𝟙 S → q ≫ a = u → (u ≫ f ≫ d) ≫ p = q ≫ a ≫ f := by
    rintro X Y Z _ d p q a f h rfl
    simp [h]
  obtain ⟨r, hr⟩ := c.rig₁
  have hF : (fst c.A c.A).left ≫ (lift (1 : c.A ⟶ c.A) (𝟙 c.A)).left = 𝟙 _ := by
    have : fst c.A c.A ≫ lift (1 : c.A ⟶ c.A) (𝟙 c.A) = 𝟙 _ :=
      CartesianMonoidalCategory.hom_ext _ _ (uniq _ _) (uniq _ _)
    exact congrArg (·.left) this
  let d : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ 𝟙_ (Over S) := lift (𝟙 _) (𝟙 _)
  have d1 : d.left ≫ (fst _ _ : 𝟙_ (Over S) ⊗ 𝟙_ (Over S) ⟶ _).left = 𝟙 S := by
    rw [← Over.comp_left, lift_fst]; rfl
  have d2 : d.left ≫ (snd _ _ : 𝟙_ (Over S) ⊗ 𝟙_ (Over S) ⟶ _).left = 𝟙 S := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨c.A.hom ≫ f, (c.A ⊗ c.A).hom ≫ f ≫ d.left, ⟨?_, fun T x y x₀ y₀ _ _ => ?_⟩, ⟨?_, ?_⟩,
    lbIso_of_gen _ _ _ hF _ (DVR.pullGen_isGen _ _ _ r hr (fst c.A c.A).left) (linComb_triv_g _ _), fun a => ?_⟩
  · show IsPullback (c.A.hom ≫ f) c.A.hom (𝟙 S) f
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  · have h1 : (x₀ * y₀).left ≫ 𝟙 S = T.hom ≫ f := Over.w (x₀ * y₀)
    exact ((Category.comp_id _).symm.trans h1).trans
      ((congrArg (· ≫ f) (Over.w (x * y))).symm.trans (Category.assoc _ _ _))
  · exact aux _ _ _ _ _ _ d1 (Over.w (fst c.A c.A))
  · exact aux _ _ _ _ _ _ d2 (Over.w (snd c.A c.A))
  · have h1 : (c.lev a).left ≫ c.A.hom = 𝟙 S' := Over.w (c.lev a)
    have h2 : ((zeroSieg k ζ s).lev a).left ≫ 𝟙 S = 𝟙 S := Over.w ((zeroSieg k ζ s).lev a)
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) h1).trans (Category.id_comp _))).trans
      ((congrArg (f ≫ ·) ((Category.comp_id _).symm.trans h2)).trans (Category.comp_id _)).symm

def zeroFam (k : ℕ) (ζ : o)
    (hz : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre 0 k ζ s'), IsReduced S → IsIso c.A.hom) : SFam 0 k ζ where
  X := Sp o
  s := 𝟙 _
  smooth := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 _))
  qproj := OnePoint.isQProjOver_id o
  univ := zeroSieg k ζ _
  princ := principal_zeroSieg k ζ _
  rep := fun S s' c hS _ _ => by
    haveI := hz S s' c hS
    exact ⟨s', Category.comp_id _, siegPB_zero c ζ _ s'⟩
  inj := fun _ _ _ _ _ _ _ h _ _ => by simpa using h

theorem tors_eq_one {ζ : o} (hζ : IsUnit ζ) {s' : S ⟶ Sp o} (c : SiegPre 0 k ζ s') (K : Type) [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ c.A) (hy : y ^ k = 1) : y = 1 := by
  let β : o →+* K := (Spec.preimage (x ≫ s')).hom
  have hβ : x ≫ s' = spMap β := by simp [β, spMap]
  obtain ⟨h1, h2, -⟩ := c.geom K x β (hζ.map β).unit hβ rfl
  obtain ⟨a, rfl⟩ := h2 y hy
  exact (h1 a).2 ⟨0, Subsingleton.elim _ _⟩

def zeroFamLevelZero {ζ : o} (hζ : IsUnit ζ) : SFam 0 0 ζ :=
  zeroFam 0 ζ fun _ _ c _ => isIso_of_points c.A c.ab fun K _ _ x y => tors_eq_one hζ c K x y (pow_zero y)

theorem isIso_of_count
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (g n : ℕ), IsAbelianScheme B →
      SmoothOfRelativeDimension g B.hom → (n : K) ≠ 0 →
      Nat.card {x : (𝟙_ (Over (Sp K)) ⟶ B) // x ^ n = 1} = n ^ (2 * g))
    {ζ : o} (hζ : IsUnit ζ) (hku : IsUnit (k : o)) (hk : 2 ≤ k) {s' : S ⟶ Sp o} (c : SiegPre 0 k ζ s') [IsReduced S] :
    IsIso c.A.hom :=
  isIso_of_points c.A c.ab fun K _ _ t y => by
    have hB' : IsAbelianScheme ((Over.pullback t).obj c.A) :=
      { comm := by have := c.ab.comm; infer_instance
        smooth := by have := c.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := c.ab.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := c.ab.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K _ hB'
    have hn : (k : K) ≠ 0 := by
      have := hku.map (Spec.preimage (t ≫ s')).hom
      rw [map_natCast] at this
      exact this.ne_zero
    have h := H K _ g k hB' hg hn
    have hp := isGrpPullback_pullback c.A t
    have hinj : Function.Injective (pushHom hp (𝟙_ (Over (Sp K)))) := by
      intro x y hxy
      have e : x.left ≫ pullback.fst c.A.hom t = y.left ≫ pullback.fst c.A.hom t := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    have h1 : Nat.card {x : (𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj c.A) // x ^ k = 1} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, one_pow k⟩, fun x => Subtype.ext (hinj ?_)⟩
      rw [map_one]
      exact tors_eq_one hζ c K _ _ (by rw [← map_pow, x.2, map_one])
    rw [h1] at h
    obtain rfl : g = 0 := by
      rcases (Nat.pow_eq_one.1 h.symm) with h | h <;> omega
    haveI : IsIso (pullback.snd c.A.hom t) := isIso_of_dim_zero _ hB' hg
    have u : ∀ z z' : Over.mk t ⟶ c.A, z = z' := fun z z' => by
      have e : pullback.lift z.left (𝟙 _) ((Over.w z).trans (Category.id_comp t).symm) =
          pullback.lift z'.left (𝟙 _) ((Over.w z').trans (Category.id_comp t).symm) := by
        rw [← cancel_mono (pullback.snd c.A.hom t), pullback.lift_snd, pullback.lift_snd]
      have := congrArg (· ≫ pullback.fst c.A.hom t) e
      simp only [pullback.lift_fst] at this
      exact Over.OverMorphism.ext this
    exact u _ _

def emptyFam (h k : ℕ) (ζ : o) (ho : ¬ (⊥ : Ideal o).IsPrime) : SFam h k ζ where
  X := ∅
  s := Scheme.emptyTo _
  smooth := by
    have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} (h * (h + 1) / 2)) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} (h * (h + 1) / 2))
      (PEmpty.elim : PEmpty.{1} → _) (Subsingleton.elim _ _) fun i => i.elim
  qproj := ⟨0, Scheme.emptyTo _, inferInstance, inferInstance, Subsingleton.elim _ _⟩
  univ :=
    { A := (zeroSieg k ζ (Scheme.emptyTo _)).A
      ab := (zeroSieg k ζ (Scheme.emptyTo _)).ab
      P := (zeroSieg k ζ (Scheme.emptyTo _)).P
      isLB := (zeroSieg k ζ (Scheme.emptyTo _)).isLB
      rig₁ := (zeroSieg k ζ (Scheme.emptyTo _)).rig₁
      rig₂ := (zeroSieg k ζ (Scheme.emptyTo _)).rig₂
      symm := (zeroSieg k ζ (Scheme.emptyTo _)).symm
      lev := fun _ => 1
      lev_add := fun _ _ => (_root_.mul_one _).symm
      lev_tors := fun _ => one_pow _
      geom := fun K _ _ x => (IsEmpty.false (x default)).elim }
  princ := principal_zeroSieg k ζ (Scheme.emptyTo _)
  rep := fun S s' c _ hd _ => by
    haveI : IsEmpty S := ⟨fun x => by
      haveI : Nonempty S := ⟨x⟩
      obtain ⟨y, hy⟩ := hd.nonempty
      exact ho (hy ▸ (s' y).isPrime)⟩
    haveI : IsEmpty c.A.left := ⟨fun x => IsEmpty.false (c.A.hom x)⟩
    haveI : IsIso c.A.hom := isIso_of_isEmpty _
    let c' : SiegPre 0 k ζ s' :=
      { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
        lev := fun _ => 1
        lev_add := fun _ _ => (_root_.mul_one _).symm
        lev_tors := fun _ => one_pow _
        geom := fun K _ _ x => (IsEmpty.false (x default)).elim }
    let f : S ⟶ (∅ : Scheme.{0}) := (isInitialOfIsEmpty (X := S)).to _
    obtain ⟨φ, φ₂, h1, h2, h3, -⟩ := siegPB_zero c' ζ (Scheme.emptyTo _) f
    exact ⟨f, (isInitialOfIsEmpty (X := S)).hom_ext _ _, φ, φ₂, h1, h2, h3,
      fun _ => (isInitialOfIsEmpty (X := S)).hom_ext _ _⟩
  inj := fun R _ _ x => (IsEmpty.false (x (IsLocalRing.closedPoint R))).elim

theorem hom_ext {h : ℕ} {ζ : o} (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (f f' : S ⟶ F.X)
    (hs : f ≫ F.s = f' ≫ F.s) (h₁ : SiegPB c F.univ f) (h₂ : SiegPB c F.univ f') : f = f' := by
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  obtain ⟨c', hc'⟩ := (GlobalTheory.siegPre_pullback h k o ζ S (Sp (S.presheaf.stalk x)) s' _ (S.fromSpecStalk x) c rfl).1
  exact F.inj (S.presheaf.stalk x) _ _ _ c'
    ((Category.assoc _ _ _).trans ((congrArg (S.fromSpecStalk x ≫ ·) hs).trans (Category.assoc _ _ _).symm))
    (GlobalTheory.SiegelPullComp.pb_comp h₁ hc') (GlobalTheory.SiegelPullComp.pb_comp h₂ hc')

example : Nonempty (SFam 0 0 (1 : ℤ)) := ⟨zeroFamLevelZero isUnit_one⟩



def zeroFamLevel {ζ : o} (hζ : IsUnit ζ) (hku : IsUnit (k : o)) (hk : 2 ≤ k) : SFam 0 k ζ :=
  zeroFam k ζ fun _ _ c _ => isIso_of_count GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional hζ hku hk c

end GlobalTheory.ZM.SFamModel
end
end
