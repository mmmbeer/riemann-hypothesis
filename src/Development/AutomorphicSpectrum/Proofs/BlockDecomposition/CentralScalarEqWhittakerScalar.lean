import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusAverageIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionCentralCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCentralCharacterHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentralCharacterHypothesis
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdelicNormVecMulLeMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizationPureIntegrand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalWhittakerUnipotentCharacter
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCentralScalarsTrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedStandardValuesAtIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalThetaCentralCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AddCharConductorInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundNumberField

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalWhittakerNorm

variable {K : Type} [Field K] [NumberField K]

theorem isUnit1_localChar' (c : HeckeCharacter K) (w : PlK K) : IsUnit1 (localChar c w) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩

theorem isUnit1_cAt' (c : HeckeCharacter K) (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] :
    IsUnit1 (cAt c v w) :=
  ⟨(isUnit1_localChar' c w).1.comp (Continuous.units_map _ (_root_.continuous_algebraMap (Qv v) (Kv K w))),
    fun x => (isUnit1_localChar' c w).2 _⟩

theorem norm_nsg (F E : Type) [Field F] [CommRing E] [Algebra F E] (a : F) :
    ‖GL2LocalData.nsg (F := F) E a‖ = 1 := by
  unfold GL2LocalData.nsg
  split_ifs <;> simp

theorem norm_W_central (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K} {v : Pl} (m : LM c v)
    (hok : m.ok) (z : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)) :
    ‖m.W (dg2 z z * g)‖ = ‖m.W g‖ := by
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    have h := GlobalTheory.CompanionTheory.SplitCentre.sCen (Qv v) _ hχc hχ1 _ _ (isUnit1_cAt' c v w₁) (isUnit1_cAt' c v w₂)
      Φ ⟨hok.2.1, hok.2.2⟩ z g
    show ‖GL2LocalData.WcS _ _ _ _ _‖ = ‖GL2LocalData.WcS _ _ _ _ _‖
    rw [h, norm_mul, Units.val_mul, norm_mul, (isUnit1_cAt' c v w₁).2, (isUnit1_cAt' c v w₂).2]
    simp
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨-, hσ, hη, hΦ⟩ := hok
    have h := GlobalTheory.CompanionTheory.WeilCentral.wCen (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη (localChar c w) Φ hΦ z g
    have hn : ‖(((GL2LocalData.resF (F := Qv v) (localChar c w) * η) z : ℂˣ) : ℂ)‖ = 1 := by
      rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hη, norm_nsg, mul_one]
      exact (isUnit1_localChar' c w).2 _
    show ‖GL2LocalData.WcE _ _ _ _ _ Φ _‖ = ‖GL2LocalData.WcE _ _ _ _ _ Φ _‖
    rw [h, norm_mul, hn, one_mul]

theorem main : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok →
  ∀ (x : Qv v) (y z : (Qv v)ˣ) (k : GL (Fin 2) (Qv v)),
    ‖m.W (uni2 x * dg2 y 1 * dg2 z z * k)‖ = ‖m.W (dg2 y 1 * k)‖ := by
  intro K _ _ h2 c v m hok x y z k
  have e : uni2 x * dg2 y 1 * dg2 z z * k = uni2 x * (dg2 z z * (dg2 y 1 * k)) := by
    rw [mul_assoc (uni2 x), GlobalTheory.CompanionTheory.GL2Factorization.PT.diagonal_mul_diagonal_alt, mul_assoc (uni2 x), ← mul_assoc (dg2 z z),
      GlobalTheory.CompanionTheory.GL2Factorization.PT.diagonal_mul_diagonal_alt]
    simp [mul_comm]
  rw [e, GlobalTheory.CompanionTheory.GlobalWhittakerPsi.local_whittaker_unipotent_character h2 m hok, norm_mul, Circle.norm_coe, one_mul]
  exact norm_W_central h2 m hok z _

end GlobalTheory.CompanionTheory.LocalWhittakerNorm
end
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem W_central : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), m.W (dg2 a a * g) = omW m a * m.W g := by
  intro K _ _ h2 c v m hok a g
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    exact GlobalTheory.CompanionTheory.SplitCentre.sCen (Qv v) _ hχc hχ1 _ _
      (GlobalTheory.CompanionTheory.LocalWhittakerNorm.isUnit1_cAt' c v w₁) (GlobalTheory.CompanionTheory.LocalWhittakerNorm.isUnit1_cAt' c v w₂)
      Φ ⟨hok.2.1, hok.2.2⟩ a g
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨-, hσ, hη, hΦ⟩ := hok
    exact GlobalTheory.CompanionTheory.WeilCentral.wCen (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη (localChar c w) Φ hΦ a g

end GlobalTheory.CompanionTheory.CenTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_whittaker_central_character : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), m.W (dg2 a a * g) = omW m a * m.W g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CenTheta.W_central
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

namespace GlobalTheory.CompanionTheory.CenTheta

theorem WM_central : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd) (g : G2), WM n t M (dg2 z z * g) = uW n t M z * WM n t M g := by
  intro K _ _ h2 c n t M hM z g
  classical
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨hc1, hc2, hc3, hc4⟩ := GlobalTheory.T.adelic_realPart_properties
  obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
  obtain ⟨S2, hS2⟩ := hc4 z
  have hreal : WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart (dg2 z z * g)) =
      omR n t (RationalIdeles.realPart z) *
        WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart g) := by
    rw [hc2, hc3]
    exact GlobalTheory.T.real_weil_action_central_character n t _ _ 1
  have hloc : ∀ v, (M v).W (finAt v (dg2 z z * g)) =
      omW (M v) (Ad3.R.lc v z) * (M v).W (finAt v g) := by
    intro v
    rw [GroundTheory.Automorphic.Reduction.finAt_mul, hc1]
    exact GlobalTheory.T.local_whittaker_central_character K h2 c v (M v) (hok v) _ _
  have hs1 : (Function.mulSupport fun v => omW (M v) (Ad3.R.lc v z)).Finite := by
    refine (S0 ∪ S2).finite_toSet.subset fun v hv => ?_
    by_contra hn
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
    exact hv (GlobalTheory.T.unramified_central_scalars_trivial K h2 c v (M v) (hS0 v hn.1).1 (hok v) _ (hS2 v hn.2)).1
  have hs2 : (Function.mulSupport fun v => (M v).W (finAt v g)).Finite := by
    refine (S0 ∪ S1).finite_toSet.subset fun v hv => ?_
    by_contra hn
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
    exact hv (GlobalTheory.T.unramified_standard_values_at_integral K h2 c v (M v) (hS0 v hn.1).1 (hok v) (hS0 v hn.1).2 _ (hS1 v hn.2)).1
  unfold WM pw2 uW
  rw [hreal, finprod_congr hloc, finprod_mul_distrib hs1 hs2]
  ring

end GlobalTheory.CompanionTheory.CenTheta
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_whittaker_central_character : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd) (g : G2), WM n t M (dg2 z z * g) = uW n t M z * WM n t M g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CenTheta.WM_central
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_theta_central_character : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ¬ m.IsSp → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)) (ξ : K), m.val (dg2 a a * g) ξ = omW m a * m.val g ξ := by
  first | exact @GlobalTheory.CompanionTheory.CenThetaNs.val_central | exact GlobalTheory.CompanionTheory.CenThetaNs.val_central | (intros; apply GlobalTheory.CompanionTheory.CenThetaNs.val_central <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem degreeOneEmbedding_zero {K : Type} [Field K] [NumberField K] (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] : dg1 v w (0 : K) = 0 := by
  have hinj : Function.Injective (algebraMap (Qv v) (Kv K w)) := (algebraMap (Qv v) (Kv K w)).injective
  have h := Function.leftInverse_invFun hinj (0 : Qv v)
  simpa [dg1] using h

theorem val_zero_central_sp : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl)
    (m : LM c v), m.ok → m.IsSp → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)),
      m.val (dg2 a a * g) 0 = om0 m a * m.val g 0 := by
  intro K _ _ c v m hok hsp a g
  have hχ := GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    have hΦ : Φ ∈ GL2LocalData.SBE (Qv v × Qv v) := ⟨hok.2.1, hok.2.2⟩
    simp only [LM.val, om0, degreeOneEmbedding_zero]
    rw [GlobalTheory.CompanionTheory.SplitPi.piS_mul hχ.1 hχ.2.1 _ hΦ, GlobalTheory.CompanionTheory.SplitCentre.piS_scalar]
    simp
  | ns w σ η Φ => exact hsp.elim

end GlobalTheory.CompanionTheory.CenTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_datum_central_character_at_zero : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → m.IsSp → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), m.val (dg2 a a * g) 0 = om0 m a * m.val g 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CenTheta.val_zero_central_sp
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem thT_zero_central : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd) (g : G2), thT n t M (dg2 z z * g) 0 = u0 n t M z * thT n t M g 0 := by
  intro K _ _ h2 c n t M hM z g
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨hfin, hreal, hrealdg, hcomp⟩ := GlobalTheory.T.adelic_realPart_properties
  obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
  obtain ⟨S2, hS2⟩ := hcomp z
  classical
  have hloc : ∀ v : Pl, (M v).val (finAt v (dg2 z z * g)) 0 =
      om0 (M v) (Ad3.R.lc v z) * (M v).val (finAt v g) 0 := by
    intro v
    have hmul : finAt v (dg2 z z * g) = dg2 (Ad3.R.lc v z) (Ad3.R.lc v z) * finAt v g := by
      rw [GroundTheory.Automorphic.Reduction.finAt_mul, hfin]
    rw [hmul]
    by_cases hs : (M v).IsSp
    · exact GlobalTheory.T.special_datum_central_character_at_zero K c v (M v) (hok v) hs _ _
    · have h := GlobalTheory.T.local_theta_central_character K h2 c v (M v) (hok v) hs (Ad3.R.lc v z) (finAt v g) 0
      rw [h]
      congr 1
      cases hm : M v with
      | sp w₁ w₂ Φ => rw [hm] at hs; exact absurd trivial hs
      | ns w σ η Φ => rfl
  have hoff : ∀ v ∉ S0 ∪ S1 ∪ S2, om0 (M v) (Ad3.R.lc v z) = 1 ∧ (M v).val (finAt v g) 0 = 1 := by
    intro v hv
    simp only [Finset.mem_union, not_or] at hv
    obtain ⟨⟨h0, h1⟩, h2'⟩ := hv
    obtain ⟨hU, hs⟩ := hS0 v h0
    exact ⟨(GlobalTheory.T.unramified_central_scalars_trivial K h2 c v (M v) hU (hok v) _ (hS2 v h2')).2,
      (GlobalTheory.T.unramified_standard_values_at_integral K h2 c v (M v) hU (hok v) hs _ (hS1 v h1)).2⟩
  have hA : (Function.mulSupport fun v => om0 (M v) (Ad3.R.lc v z)).Finite :=
    (S0 ∪ S1 ∪ S2).finite_toSet.subset fun v hv => by
      by_contra hn
      exact hv (hoff v (by simpa using hn)).1
  have hB : (Function.mulSupport fun v => (M v).val (finAt v g) 0).Finite :=
    (S0 ∪ S1 ∪ S2).finite_toSet.subset fun v hv => by
      by_contra hn
      exact hv (hoff v (by simpa using hn)).2
  simp only [thT, u0]
  rw [hreal, hrealdg, GlobalTheory.T.real_weil_action_central_character n t, finprod_congr hloc, finprod_mul_distrib hA hB]
  ring

end GlobalTheory.CompanionTheory.CenTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_central_character_at_zero : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd) (g : G2), thT n t M (dg2 z z * g) 0 = u0 n t M z * thT n t M g 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CenTheta.thT_zero_central
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

namespace GlobalTheory.CompanionTheory.CenTheta

theorem norm_omR (n : ℤ) (t : ℝ) (a : ℝˣ) : ‖omR n t a‖ = 1 := by
  have ha : 0 < |(a : ℝ)| := abs_pos.mpr a.ne_zero
  have hq : (((|(a : ℝ)| : ℝ) : ℂ)) / ((‖(((|(a : ℝ)| : ℝ) : ℂ))‖ : ℝ) : ℂ) = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact div_self (Complex.ofReal_ne_zero.mpr ha.ne')
  have hpos : (0 : ℝ) < ‖(((|(a : ℝ)| : ℝ) : ℂ))‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_abs]
    positivity
  have hch : ‖chC n (Complex.I * t) (Units.mk0 ((|(a : ℝ)| : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr a.ne_zero)))‖ = 1 := by
    unfold chC
    simp only [Units.val_mk0]
    rw [hq, one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hsg : ‖sgR (a : ℝ)‖ = 1 := by
    unfold sgR
    split_ifs <;> simp
  have hs : ‖(if 0 < (a : ℝ) then 1 else (-1 : ℂ) ^ n)‖ = 1 := by
    split_ifs
    · simp
    · rw [norm_zpow]; simp
  unfold omR
  rw [norm_mul, norm_mul, hch, hsg, hs]
  simp

end GlobalTheory.CompanionTheory.CenTheta
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_real_central_character_eq_one : ∀ (n : ℤ) (t : ℝ) (a : ℝˣ), ‖omR n t a‖ = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CenTheta.norm_omR
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem norm_localChar_val {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (w : PlK K)
    (x : (Kv K w)ˣ) : ‖((localChar c w x : ℂˣ) : ℂ)‖ = 1 := by
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar]
  exact Circle.norm_coe _

theorem norm_cAt_val {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] (a : (Qv v)ˣ) : ‖((cAt c v w a : ℂˣ) : ℂ)‖ = 1 :=
  norm_localChar_val c w _

theorem norm_resF_val {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] (a : (Qv v)ˣ) :
    ‖((GL2LocalData.resF (F := Qv v) (localChar c w) a : ℂˣ) : ℂ)‖ = 1 :=
  norm_localChar_val c w _

theorem norm_nsg {F E : Type} [Field F] [Field E] [Algebra F E] (a : F) : ‖GL2LocalData.nsg E a‖ = 1 := by
  unfold GL2LocalData.nsg
  split_ifs <;> simp

theorem norm_central_scalars_eq_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ∀ (a : (Qv v)ˣ), ‖omW m a‖ = 1 ∧ ‖om0 m a‖ = 1 := by
  intro K _ _ _ c v m hm a
  cases m with
  | sp w₁ w₂ Φ =>
    constructor
    · simp only [omW, Units.val_mul, norm_mul, norm_cAt_val, mul_one]
    · simp only [om0, Units.val_mul, norm_mul, norm_cAt_val, mul_one]
  | ns w σ η Φ =>
    have hη : ‖((η a : ℂˣ) : ℂ)‖ = 1 := by
      rw [hm.2.2.1 a]; exact norm_nsg _
    constructor
    · simp only [omW, MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_resF_val, hη, mul_one]
    · simp only [om0, MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_resF_val, hη, mul_one]

end GlobalTheory.CompanionTheory.CenTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_local_central_scalars_eq_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ∀ (a : (Qv v)ˣ), ‖omW m a‖ = 1 ∧ ‖om0 m a‖ = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CenTheta.norm_central_scalars_eq_one
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

namespace GlobalTheory.CompanionTheory.CenTheta

theorem norm_uW_eq_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd), ‖uW n t M z‖ = 1 := by
  classical
  intro K _ _ h2 c n t M hM z
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨S, hS⟩ := GlobalTheory.T.adelic_realPart_properties.2.2.2 z
  have hsupp : (Function.mulSupport fun v : Pl => omW (M v) (Ad3.R.lc v z)) ⊆
      ((S0 ∪ S : Finset Pl) : Set Pl) := by
    intro v hv
    by_contra hn
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
    exact hv (GlobalTheory.T.unramified_central_scalars_trivial K h2 c v (M v) (hS0 v hn.1).1 (hok v) _ (hS v hn.2)).1
  unfold uW
  rw [norm_mul, GlobalTheory.T.norm_real_central_character_eq_one, one_mul, finprod_eq_prod_of_mulSupport_subset _ hsupp, norm_prod]
  exact Finset.prod_eq_one fun v _ => (GlobalTheory.T.norm_local_central_scalars_eq_one K h2 c v (M v) (hok v) _).1

end GlobalTheory.CompanionTheory.CenTheta
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_global_central_scalar_eq_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd), ‖uW n t M z‖ = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CenTheta.norm_uW_eq_one
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem centralScalar_twisted_data {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K} (n : ℤ) (t : ℝ)
    (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (x : ∀ v : Sv, (Qv v.1)ˣ) (z : Jd) :
    u0 n t (twM M Sv m x) z = u0 n t M z := by
  have h : ∀ v, om0 (twM M Sv m x v) (Ad3.R.lc v z) = om0 (M v) (Ad3.R.lc v z) := by
    intro v
    simp only [twM]
    cases M v <;> rfl
  simp only [u0, h]

theorem theta_central_character {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K}
    (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl)
    (z : Jd) (g : G2) : th0 R Sv n t M (dg2 z z * g) = u0 n t M z * th0 R Sv n t M g := by
  simp only [th0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have := GlobalTheory.T.theta_central_character_at_zero K h2 c n t (twM M Sv m x) (GlobalTheory.CompanionTheory.TorusAverage.admissible_twisted_local_data hM Sv m x) z g
  rw [centralScalar_twisted_data] at this
  simp only [this]
  ring

end GlobalTheory.CompanionTheory.CenTheta
end
end
