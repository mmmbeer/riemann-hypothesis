import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPointsStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRootsUnity

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.TowerWeil

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem eq_one_of_pow_eq_one {R : Type} [CommRing R] {J : Ideal R} (hJ : J ≤ Ideal.jacobson ⊥) {n : ℕ}
    (hn : IsUnit (n : R)) {w : R} (hw : w ^ n = 1) (h : w - 1 ∈ J) : w = 1 := by
  have hs : (∑ i ∈ Finset.range n, w ^ i) - n ∈ J := by
    have e : (∑ i ∈ Finset.range n, w ^ i) - n = ∑ i ∈ Finset.range n, (w ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow w 1 i
    rw [one_pow] at hq
    rw [hq]
    exact J.mul_mem_right _ h
  obtain ⟨v, hv⟩ := hn
  have hu : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    have e : (∑ i ∈ Finset.range n, w ^ i) = (v : R) * (((∑ i ∈ Finset.range n, w ^ i) - n) * (↑v⁻¹ : R) + 1) := by
      rw [mul_add, mul_comm ((∑ i ∈ Finset.range n, w ^ i) - n), ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul, _root_.mul_one, hv]
      ring
    rw [e]
    exact v.isUnit.mul ((Ideal.mem_jacobson_bot.1 (hJ hs)) _)
  have h0 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by rw [geom_sum_mul, hw, sub_self]
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom (c : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_bijective {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem exists_weilIs_root {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (P : LB (G2 A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) (N : ℕ) (hN : 0 < N) {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) :
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N x y c₀ := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP r₁ r₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP r₁ r₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag hP hB hB' (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG hA hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG hA hD hp (e₁' ▸ hc₁), hc₀⟩

theorem unitOn_pow' {R : Type} [CommRing R] (u : Rˣ) (m : ℕ) : unitOn (u ^ m) = unitOn u ^ m := by
  unfold unitOn; exact map_pow _ u m

theorem unitOn_one' {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := by
  unfold unitOn; exact map_one _

theorem exists_spMap {R K : Type} [CommRing R] [CommRing K] (x : Sp K ⟶ Sp R) : ∃ f : R →+* K, spMap f = x :=
  ⟨(Spec.preimage x).hom, by simp [spMap]⟩

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl


end GlobalTheory.TowerWeil
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

theorem lbIso_lbPow_hecke {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (k : ℕ) :
    LBIso (lbPow P k) ((Hecke.lbPow P k).pull (𝟙 X)) := by
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have h₁ : LBIso (lbPow P k) (Hecke.lbPow P k) := by
    unfold Hecke.lbPow lbPow
    refine (GlobalTheory.PrimNorm.lbIso_iff hP _ _ _ _).2 ?_
    simp
  exact h₁.trans (LB.isLB_linComb hP _ _) hQ (pull_isLB hQ _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hQ).symm

theorem weilIs_of_hecke_lbPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {P : LB A.left} (hP : P.IsLB) (k : ℕ) {T : Over S} {X Y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A (Hecke.lbPow P k) 1 X Y u) : Out.WeilIs A P k X Y u := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have := (GlobalTheory.weilIs_along_hom hG S A A (𝟙 _) P (Hecke.lbPow P k) k 1 T X Y u u hA hA hP hQ inferInstance
    (lbIso_lbPow_hecke hP k) (by simpa using h)).1
  simpa using this

end GlobalTheory.BiextPairing

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

end GlobalTheory.BiextPairing
end
end
