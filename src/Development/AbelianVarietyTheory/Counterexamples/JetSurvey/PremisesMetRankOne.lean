import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DiagonalPowerBalanced
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxTauBalOfLinear
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxRosati
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesDvrAdmissibleXIdeal

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowActProbe

theorem exists_pow (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (n : ℕ) :
    ∃ D' : DegData R I, Nonempty (IsPowDeg D'.toPre D.toPre n) :=
  GlobalTheory.PowDegData.main GlobalTheory.globalFns_holds R I D n

section Unique

variable {R : Type} [CommRing R] [IsDomain R] {D' D : DegPre R} {n : ℕ}

end Unique


theorem premises_met (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Δ : Datum H)
    (h : 1 ≤ Δ.p + Δ.q) (n : ℕ) :
    ∃ (t : SAB H (Sp (PowerSeries ℂ))) (P : PELUnif (maximalIdeal (PowerSeries ℂ)) t), 0 < P.A.g ∧
      ∃ D' : DegData (PowerSeries ℂ) (maximalIdeal _), Nonempty (IsPowDeg D'.toPre P.D.toPre n) := by
  obtain ⟨t, P, -, -, hg, -⟩ := GlobalTheory.ConstantFamily.exists_pelUnif_powerSeries E H Δ h
  exact ⟨t, P, hg, exists_pow _ _ P.D n⟩

end GlobalTheory.PowActProbe
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPowerBalanced

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowBalanceProbe

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def AdjCls (c : Pic A.left) (f g : A ⟶ A) : Prop :=
  ∀ (T : Over S) (x y : T ⟶ A), pull ((x ≫ f) * y).left c - pull (x ≫ f).left c - pull y.left c -
    pull (x * (y ≫ g)).left c + pull x.left c + pull (y ≫ g).left c = 0



theorem eq_one_of_cls {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L) {T : Over S} (p : T ⟶ A) (d : Pic T.left)
    (h : pull ((fst T A ≫ p) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) =
      pull (fst T A).left d) : p = 1 := by
  refine KerPow.eq_one_of_locGen hK p ((KerPow.locGen_iff _ _ _).1 ?_)
  refine (locZero_iff (fst T A).left (N := Out.translDiff A L p) (LB.isLB_linComb hL _ _)).2 ?_
  rw [cls_translDiff hL, h]
  exact locZero_base _ _


variable {A' : Over S} [GrpObj A'] [IsCommMonObj A']


end Group

variable {R : Type} [CommRing R] [IsDomain R]




theorem tauBal_id (D : DegPre R) : D.TauBal (𝟙 _) (𝟙 _) id id := by
  intro u hu hn y y'
  have sj : Function.Surjective ((snd D.P.A D.P.A).left ≫ D.P.A.hom).appTop.hom :=
    surj_comp (surj_snd GlobalTheory.globalFns_holds D.P.isAb _) (GlobalTheory.globalFns_holds _ _ D.P.isAb).2
  have he : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  have hF : FormEq (Y := (D.P.A ⊗ D.P.A).left) (K := PEmpty) PEmpty.elim PEmpty.elim
      (rosatiφ D.P.A (𝟙 _) (𝟙 _)) rosatiε := fun U _ k => by
    have := prod_ros (𝟙 D.P.A) (𝟙 D.P.A) (fst D.P.A D.P.A) (snd D.P.A D.P.A) k
    rw [lift_fst_snd, Category.comp_id, Category.comp_id] at this
    simp only [Over.id_left, Category.id_comp] at this
    rw [this, Fintype.prod_empty]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  refine corr_of_val D.P.isLB fun z J hJ => ?_
  have key := gen_unique' D.P.isLB hF _ (zero2 D.P.A) he sj hu (GlobalTheory.IntAct.isGen_oneGen D.P.L)
    (fun s I hI => by
      have v := val_corr hI hn (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at v
      rw [v, val_one]) _ (D.pt2 y y') z J hJ
  rw [val_mul hJ, val_pull hJ, Category.id_comp, key, val_one, _root_.mul_one]
  rfl

theorem premises_met (I : Ideal R) (D : DegData R I) (n : ℕ) :
    ∃ (D' : DegData R I) (p : IsPowDeg D'.toPre D.toPre n),
      DiagOnB p (𝟙 _) (𝟙 _) ∧ DiagOnX p id id ∧ CLinear D.toPre (𝟙 _) id ∧
        D.toPre.TauBal (𝟙 _) (𝟙 _) id id := by
  obtain ⟨D', ⟨p⟩⟩ := GlobalTheory.PowActProbe.exists_pow R I D n
  exact ⟨D', p, fun _ => by simp, fun _ _ => rfl, fun _ => (Category.comp_id _).symm, tauBal_id _⟩


end GlobalTheory.PowBalanceProbe
end
end
