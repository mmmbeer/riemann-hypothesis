import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCoset
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionGeneratorPower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaValueTorsionFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsOfGeometric

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RealCompare
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds hiding fn PsiNorm

section General
variable {B : Scheme.{0}}

theorem exists_heis (hL : Laws) [IsLocallyNoetherian B] (P : PolAV B) {k : ℕ} (hk : Odd k) (hu : IsUnit (k : Γ(B, ⊤)))
    {T : Over B} {x : T ⟶ P.A} (hx : x ^ k = 1) {U : ThetaGrp P.A P.L k T} (hU : SymLift P.A P.L k k x U)
    (s s' : LB.Sec (LPow P.A P.L k T)) : IsHeis P k x s s' ↔ IsActOf P.A P.L k U s s' := by
  refine ⟨fun ⟨_, U', hU', H⟩ => ?_, fun H => ⟨hx, U, hU, H⟩⟩
  have hc := (hL.symLift B P k hk hu T x hx).2 U U' hU hU'
  have e := hU.pt_eq.trans hU'.pt_eq.symm
  obtain ⟨y, φ, hφ⟩ := U
  obtain ⟨y', φ', hφ'⟩ := U'
  obtain rfl : y = y' := e
  refine VVRank.isTwistPull_of_sv P.A P.isLB hφ fun z J hJ => ?_
  exact (VVRank.sv_of_isTwistPull P.A H _ z hJ).trans
    (congrArg (fun q : ((T ⊗ P.A).left.presheaf.stalk z)ˣ => q.val * _) (val_corr hJ hc _).symm)

theorem exists_heis_linear (hL : Laws) [IsLocallyNoetherian B] (P : PolAV B) {k : ℕ} (hk : Odd k)
    (hu : IsUnit (k : Γ(B, ⊤))) {T : Over B} {x : T ⟶ P.A} (hx : x ^ k = 1) :
    ∃ u : SecM P.A P.L k T →ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T,
      ∀ s s', IsHeis P k x s s' ↔ u (SecM.ofSec P.A s) = SecM.ofSec P.A s' := by
  obtain ⟨U, hU⟩ := GlobalTheory.exists_symLift_global hL B P k hk hu T x hx
  obtain ⟨r, hr, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns B P k T
  exact ⟨(r U).toLinearMap, fun s s' => (exists_heis hL P hk hu hx hU s s').trans (hr _ _ _)⟩

theorem isValueAt_sum {A : Over B} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over B} {x : T ⟶ A} {τ}
    {I : Type} [Fintype I] (c v : I → Γ(T.left, ⊤)) (s : I → LB.Sec (LPow A L k T))
    (h : ∀ i, IsValueAt A L k (s i) x τ (v i)) {σ : LB.Sec (LPow A L k T)}
    (e : SecM.ofSec A σ = ∑ i, c i • SecM.ofSec A (s i)) : IsValueAt A L k σ x τ (∑ i, c i * v i) := by
  refine ThetaPtMove.isValueAt_of_sv hL fun y J hJ => ?_
  have a := (congrArg (fun q => ThetaAct.sv q (𝟙 _ ≫ (ptSecT A x).left) y J) e).trans (ThetaGeom.sv_sum _ _ _ y hJ)
  refine a.trans ?_
  have g : gs (𝟙 T.left) y ⊤ (∑ i, c i * v i) = ∑ i, gs (𝟙 T.left) y ⊤ (c i) * gs (𝟙 T.left) y ⊤ (v i) := by
    simp only [gs_eq (𝟙 T.left) y ⊤ trivial, map_sum, map_mul]
  rw [g, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, ThetaPtMove.ptSecT_fst, Category.comp_id, _root_.mul_assoc]
  exact congrArg (_ * ·) (ThetaPtMove.sv_of_isValueAt (h i) (𝟙 _) y hJ)

open SquareLevel ThetaCoord in

theorem tor_props (hL : Laws) [IsLocallyNoetherian B] (P : PolAV B) (M : ℕ) (ze : Γ(B, ⊤)ˣ) (hM : 1 ≤ M)
    (hu : IsUnit (M : Γ(B, ⊤))) (lev : Out.Level P (M ^ 2) ze) {g : ℕ} (h : P.g = g)
    (pt : (Fin g ⊕ Fin g → ZMod M) → (baseOver B ⟶ P.A))
    (hpt : ∀ a, pt a = linComb lev.pt (fun i => (a (idx h i)).val) ^ M) :
    (∀ a b, pt (a + b) = pt a * pt b) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ B) (z : Over.mk x ⟶ P.A), z ^ M = 1 →
      ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver B) ≫ pt a = z) ∧
    ∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd g M a b).val)) := by
  subst h
  have : NeZero M := ⟨by omega⟩
  have hq : ∀ i, (lev.pt i ^ M) ^ M = 1 := fun i => by rw [← pow_mul, ← sq, lev.torsion]
  obtain ⟨pt', h₁, h₂, h₃, -, h₅⟩ := GlobalTheory.exists_torsionPoints_of_squareLevel hL B P M ze hM hu lev
  have e : ∀ a, pt a = lab (fun i => lev.pt i ^ M) (a ∘ (halves P.g).symm) := fun a =>
    (hpt a).trans ((linComb_pow_right _ _ _).trans (linComb_pow_left _ _ _).symm)
  have e' : ∀ a, pt' (a ∘ halves P.g) = lab (fun i => lev.pt i ^ M) a := fun a => by
    refine char_ext (fun a => pt' (a ∘ halves P.g)) _ (fun a b => h₁ _ _) (lab_add hq) (fun i => ?_) a
    obtain ⟨s, rfl⟩ := (halves P.g).surjective i
    have q : (Pi.single (halves P.g s) (1 : ZMod M) : _ → ZMod M) ∘ halves P.g = Pi.single s 1 := by
      funext j
      simp [Pi.single_apply]
    beta_reduce
    rw [q, lab_single hq]
    rcases s with i | i
    · exact (h₅ i _ (halves P.g (.inr i)) rfl (Nat.add_comm _ _)).1
    · exact (h₅ i (halves P.g (.inl i)) _ rfl (Nat.add_comm _ _)).2
  obtain rfl : pt = pt' := funext fun a => by
    rw [e, ← e']
    congr 1
    funext j
    simp
  exact ⟨h₁, h₂, h₃⟩

end General

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_cstSpan (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {X : Set M} {x : M}
    (h : x ∈ X) : x ∈ cstSpan S X := AddSubgroup.subset_closure ⟨1, x, h, by rw [map_one, one_smul]⟩

theorem smul_mem_cstSpan (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {X : Set M}
    (c : o) {x : M} (h : x ∈ cstSpan S X) : cst S c • x ∈ cstSpan S X := by
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨d, y, hy, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨c * d, y, hy, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem cstSpan_le (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {X Y : Set M}
    (h : ∀ x ∈ X, x ∈ cstSpan S Y) : cstSpan S X ≤ cstSpan S Y :=
  (AddSubgroup.closure_le _).2 fun _ ⟨c, x, hx, e⟩ => e ▸ smul_mem_cstSpan S c (h x hx)

theorem mem_cstSpan_range (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {I : Type}
    [Fintype I] (b : I → M) (x : M) : x ∈ cstSpan S (Set.range b) ↔ ∃ c : I → o, x = ∑ i, cst S (c i) • b i := by
  refine ⟨fun h => ?_, fun ⟨c, e⟩ => e ▸ sum_mem fun i _ => smul_mem_cstSpan S _ (mem_cstSpan S ⟨i, rfl⟩)⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨d, _, ⟨i, rfl⟩, rfl⟩ := hx
    exact ⟨Pi.single i d, by
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_smul]) (fun h => (h (Finset.mem_univ i)).elim),
        Pi.single_eq_same]⟩
  | zero => exact ⟨0, (Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, map_zero, zero_smul]).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨-c, by simp⟩

theorem comb_comb (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {I J : Type}
    [Fintype I] [Fintype J] (b : I → M) (A : Matrix I J o) (c : J → o) :
    ∑ j, cst S (c j) • ∑ i, cst S (A i j) • b i = ∑ i, cst S (∑ j, A i j * c j) • b i := by
  simp only [Finset.smul_sum, map_sum, Finset.sum_smul, smul_smul, map_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

structure Change (S : ThetaSys o Ω) where
  J : Type
  [fin : Fintype J]
  [ne : Nonempty J]
  M : Matrix S.J J o
  M' : Matrix J S.J o
  mul_inv : M * M' = 1
  inv_mul : M' * M = 1
  e : S.Gam → ℕ

attribute [instance] Change.fin Change.ne

def Change.scalar (S : ThetaSys o Ω) (u : oˣ) (e : S.Gam → ℕ) : Change S where
  J := S.J
  M := (u : o) • 1
  M' := (↑u⁻¹ : o) • 1
  mul_inv := by simp [smul_smul]
  inv_mul := by simp [smul_smul]
  e := e

theorem Change.sum_mul {S : ThetaSys o Ω} (c : Change S) (l i : S.J) :
    ∑ j, c.M l j * c.M' j i = if l = i then 1 else 0 :=
  Matrix.mul_apply.symm.trans ((congrFun (congrFun c.mul_inv l) i).trans Matrix.one_apply)


theorem zeta_ne_zero (S : ThetaSys o Ω) (e : ℕ) : algebraMap o Ω (S.ζ ^ e) ≠ 0 :=
  (((S.prim.isUnit (level_ne_zero S)).pow e).map _).ne_zero

def change (S : ThetaSys o Ω) (c : Change S) : ThetaSys o Ω :=
  { S with
    J := c.J
    fin := c.fin
    ne := c.ne
    ρ := fun a => c.M' * S.ρ a * c.M
    ρ_one := fun a h => by rw [S.ρ_one a h, Matrix.mul_one, c.inv_mul]
    ρ_mul := fun a b => (S.ρ_mul a b).imp fun k hk => by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc c.M, c.mul_inv, Matrix.one_mul]
    ρ_add := fun a b h => by
      rw [← S.ρ_add a b h]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc c.M, c.mul_inv, Matrix.one_mul]
    th := fun a => algebraMap o Ω (S.ζ ^ c.e a) * S.th a
    ev := fun a j => ∑ i, algebraMap o Ω (c.M i j) * S.ev a i
    th_mem := fun a => mul_mem (S.R.algebraMap_mem _) (S.th_mem a)
    ev_mem := fun a j => sum_mem fun i _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem a i)
    supp := by
      rw [← S.supp]
      congr 1
      ext a
      simp only [Set.mem_setOf_eq, ne_eq, mul_eq_zero, zeta_ne_zero S, false_or]
    th_ne := S.th_ne.imp fun a h => mul_ne_zero (zeta_ne_zero S _) h }

def Change.inv {S : ThetaSys o Ω} (c : Change S) : Change (change S c) where
  J := S.J
  M := c.M'
  M' := c.M
  mul_inv := c.inv_mul
  inv_mul := c.mul_inv
  e := fun a => ((S.r * S.N) ^ 2 - 1) * c.e a

theorem big_iff (S : ThetaSys o Ω) (h : 7 ≤ S.N) : S.Big ↔ LowerBounds S.g S.N (S.r * S.N) := by
  refine ⟨fun H => ⟨H.1, H.2.1⟩, fun H => ?_⟩
  rcases Nat.eq_zero_or_pos S.g with h0 | h0
  · refine ⟨H.1, H.2, ?_⟩
    rw [h0]
    have := S.r_pos
    simp only [pow_zero, Nat.factorial_zero]
    nlinarith
  · exact RealCase.big_third S h0 H.1 H.2

end GlobalTheory.RealCompare
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RealCompare
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds hiding fn PsiNorm
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

instance noeth [ArithBase o Ω] (S : ThetaSys o Ω) : IsNoetherianRing S.R := by
  have := ArithBase.ded (o := o) (Ω := Ω)
  exact isNoetherianRing_of_fg S.fg

theorem unit_rN (S : ThetaSys o Ω) : IsUnit ((S.r * S.N : ℕ) : Γ(Sp S.R, ⊤)) := by
  have := S.unit.map (cst S)
  rwa [map_natCast] at this

theorem unit_N (S : ThetaSys o Ω) : IsUnit ((S.N : ℕ) : Γ(Sp S.R, ⊤)) := by
  have := unit_rN S
  rw [Nat.cast_mul] at this
  exact isUnit_of_mul_isUnit_right this

theorem one_le_rN (S : ThetaSys o Ω) : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)

theorem odd_N {S : ThetaSys o Ω} (Z : Realisation S) : Odd S.N := Z.N_eq ▸ Z.odd.pow.pow

def newBasis {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) (j : c.J) : SecM Z.P.A Z.P.L S.N (Base S) :=
  ∑ i, cst S (c.M i j) • SecM.ofSec Z.P.A (Z.b i)

theorem comb_single (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {I : Type}
    [Fintype I] (b : I → M) (i : I) (d : o) : ∑ l, cst S (if l = i then d else 0) • b l = cst S d • b i := by
  rw [Finset.sum_eq_single i (fun l _ hl => by rw [if_neg hl, map_zero, zero_smul])
    (fun h => (h (Finset.mem_univ i)).elim), if_pos rfl]

theorem map_comb (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {I J : Type}
    [Fintype I] [Fintype J] (u : M →ₗ[Γ((Base S).left, ⊤)] M) (b : I → M) (b' : J → M) (A : Matrix J I o)
    (h : ∀ i, u (b i) = ∑ j, cst S (A j i) • b' j) (c : I → o) :
    u (∑ i, cst S (c i) • b i) = ∑ j, cst S (∑ i, A j i * c i) • b' j := by
  simp only [map_sum u, map_smul, h]
  exact comb_comb S b' A c

theorem old_eq {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) (i : S.J) :
    SecM.ofSec Z.P.A (Z.b i) = ∑ j, cst S (c.M' j i) • newBasis Z c j := by
  refine Eq.trans ?_ (comb_comb S _ c.M fun j => c.M' j i).symm
  refine Eq.trans ?_ (Finset.sum_congr rfl fun l _ => congrArg (fun q => cst S q • _) (c.sum_mul l i)).symm
  refine Eq.symm ((comb_single S (fun i => SecM.ofSec Z.P.A (Z.b i)) i 1).trans ?_)
  rw [(cst S).map_one, one_smul]

theorem newBasis_indep {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) (d : c.J → o)
    (h : ∑ j, cst S (d j) • newBasis Z c j = 0) : d = 0 := by
  simp only [newBasis] at h
  rw [comb_comb] at h
  have e : c.M.mulVec d = 0 := Z.b_indep _ h
  rw [← Matrix.one_mulVec d, ← c.inv_mul, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]

theorem newBasis_span {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) :
    cstSpan S (Set.range (newBasis Z c)) = cstSpan S (Set.range fun i => SecM.ofSec Z.P.A (Z.b i)) :=
  le_antisymm (cstSpan_le S fun _ ⟨j, e⟩ => (mem_cstSpan_range S _ _).2 ⟨fun i => c.M i j, e.symm⟩)
    (cstSpan_le S fun _ ⟨i, e⟩ => (mem_cstSpan_range S _ _).2 ⟨fun j => c.M' j i, e.symm.trans (old_eq Z c i)⟩)

theorem newBasis_act [ArithBase o Ω] {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) (a : S.Gam) (j : c.J) :
    ∃ s, IsHeis Z.P S.N (Z.tor a ^ S.r) (SecM.toSec Z.P.A (newBasis Z c j)) s ∧
      SecM.ofSec Z.P.A s = ∑ l, cst S ((c.M' * S.ρ a * c.M) l j) • newBasis Z c l := by
  obtain ⟨_, ⟨hx, -⟩, -⟩ := Z.ρ_eq a (Classical.arbitrary _)
  obtain ⟨u, hu⟩ := exists_heis_linear abelianSchemeLaws_all.1 Z.P (odd_N Z) (unit_N S) hx
  have hb : ∀ i, u (SecM.ofSec Z.P.A (Z.b i)) = ∑ i', cst S (S.ρ a i' i) • SecM.ofSec Z.P.A (Z.b i') := fun i => by
    obtain ⟨s, h₁, h₂⟩ := Z.ρ_eq a i
    exact ((hu _ _).1 h₁).trans h₂
  refine ⟨SecM.toSec Z.P.A (u (newBasis Z c j)), (hu _ _).2 rfl, ?_⟩
  refine (map_comb S u _ _ (S.ρ a) hb fun i => c.M i j).trans
    (Eq.trans ?_ (comb_comb S _ c.M fun l => (c.M' * S.ρ a * c.M) l j).symm)
  have e : c.M * (c.M' * S.ρ a * c.M) = S.ρ a * c.M := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, c.mul_inv, Matrix.one_mul]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun q => cst S q • _) (congrFun (congrFun e i) j).symm

theorem fn_ev (S : ThetaSys o Ω) (c : Change S) (a : S.Gam) (j : c.J) :
    IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S ⟨(change S c).ev a j, (change S c).ev_mem a j⟩ =
      ∑ i, cst S (c.M i j) * IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S ⟨S.ev a i, S.ev_mem a i⟩ := by
  have : (⟨(change S c).ev a j, (change S c).ev_mem a j⟩ : S.R) =
      ∑ i, algebraMap o S.R (c.M i j) * ⟨S.ev a i, S.ev_mem a i⟩ := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finset_sum]; rfl)
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_mul _ _ _

theorem fn_th (S : ThetaSys o Ω) (c : Change S) (a : S.Gam) :
    IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S ⟨(change S c).th a, (change S c).th_mem a⟩ =
      cst S S.ζ ^ c.e a * IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S ⟨S.th a, S.th_mem a⟩ := by
  rw [← map_pow]
  exact map_mul (IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S) (algebraMap o S.R (S.ζ ^ c.e a)) ⟨S.th a, S.th_mem a⟩

def changeReal [ArithBase o Ω] {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) : Realisation (change S c) where
  n := Z.n
  k := Z.k
  j := Z.j
  prime := Z.prime
  odd := Z.odd
  two_le := Z.two_le
  N_eq := Z.N_eq
  r_eq := Z.r_eq
  bounds := Z.bounds
  P := Z.P
  dim := Z.dim
  rig := Z.rig
  rig_gen := Z.rig_gen
  w := Z.w
  w_hom := Z.w_hom
  selfPaired := Z.selfPaired
  lev := Z.lev
  θ := Z.θ
  θ_gen := Z.θ_gen
  th_eq := fun a => by
    obtain ⟨x', v, e, h₁, h₂, h₃⟩ := Z.th_eq a
    refine ⟨x', v, c.e a + e, h₁, h₂, (fn_th S c a).trans ?_⟩
    rw [h₃, ← _root_.mul_assoc, ← pow_add]
    rfl
  s₁ := Z.s₁
  s₁_eq := Z.s₁_eq
  b := fun j => SecM.toSec Z.P.A (newBasis Z c j)
  b_indep := newBasis_indep Z c
  b_span := (newBasis_span Z c).trans Z.b_span
  ρ_eq := newBasis_act Z c
  ev_eq := fun a => (Z.ev_eq a).imp fun e he => ⟨he.1, fun j =>
    (congrArg (IsValueAt _ _ _ _ _ _) (fn_ev S c a j)).mpr
      (isValueAt_sum Z.P.isLB (fun i => cst S (c.M i j)) _ Z.b he.2 rfl)⟩

structure Agree {S : ThetaSys o Ω} (ρ : S.Real) (Z : Realisation S) : Prop where
  P : ρ.P = Z.P
  n : ρ.n = Z.n
  k : ρ.k = Z.k
  pt : ∀ a, HEq (ρ.pt a) (Z.tor a)
  rig : HEq ρ.rig Z.rig
  θ : HEq ρ.th₁ Z.θ
  s₁ : HEq (ρ.s ρ.i₀) Z.s₁
  b : ∀ i, HEq (ρ.s i) (Z.b i)

end GlobalTheory.RealCompare
end
end
