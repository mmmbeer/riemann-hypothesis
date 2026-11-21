import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerRosatiTauBalAction
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesMetRankOne

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Out.InhTate

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxPowerProbe

theorem both_hold : BoxRosatiSt ∧ BoxTauBalSt :=
  ⟨GlobalTheory.powerRosati_tauBal_action.1, GlobalTheory.powerRosati_tauBal_action.2.1⟩

section General

variable {R : Type} [CommRing R] [IsDomain R]



theorem tauBal_id_iff (D : DegPre R) (hr : RosatiAdj D.P.A D.P.L (𝟙 _) (𝟙 _)) (a a' : D.X → D.X) :
    D.TauBal (𝟙 _) (𝟙 _) a a' ↔ ∀ y y' z J, Good D.P.L z J →
      val (D.tau (a y) y') (𝟙 _) z J = val (D.tau y (a' y')) (𝟙 _) z J := by
  have one : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (𝟙 _) (𝟙 _)) rosatiε)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ y y' z J, Good D.P.L z J → val (LB.pullGen D.P.L _ _ u (D.pt2 y y')) (𝟙 _) z J = 1 := by
    intro u hu hn y y' z J hJ
    have := val_corr hJ (GlobalTheory.PowBalanceProbe.tauBal_id D u hu hn y y') (𝟙 _)
    rw [val_mul hJ] at this
    exact mul_eq_left.1 this
  constructor
  · intro h y y' z J hJ
    obtain ⟨u, hu, hn⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB _ _ hr
    have := val_corr hJ (h u hu hn y y') (𝟙 _)
    rwa [val_mul hJ, one u hu hn y y' z J hJ, _root_.mul_one] at this
  · intro h u hu hn y y'
    refine corr_of_val D.P.isLB fun z J hJ => ?_
    rw [val_mul hJ, one u hu hn y y' z J hJ, _root_.mul_one]
    exact h y y' z J hJ

end General

theorem pi_zpow_injective {a b : ℤ} (h : pi0 ^ a = pi0 ^ b) : a = b := by
  have inj : Function.Injective (Units.map
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing InhTate.R))).inv.hom.toMonoidHom) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of (FractionRing InhTate.R))).symm.commRingCatIsoToRingEquiv.injective
  have h' : piK ^ a = piK ^ b := inj (by rw [map_zpow, map_zpow]; exact h)
  have aux : ∀ k : ℕ, piK ^ k = 1 → k = 0 := fun k hk => by
    have e : algebraMap InhTate.R (FractionRing InhTate.R) (PowerSeries.X ^ k) =
        algebraMap InhTate.R (FractionRing InhTate.R) 1 := by
      rw [map_pow, map_one]
      exact congrArg Units.val hk
    have e' := congrArg PowerSeries.constantCoeff (IsFractionRing.injective _ _ e)
    by_contra h0
    simp [h0] at e'
  have fin : ¬ IsOfFinOrder piK := fun hf => by
    obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    exact hk.ne' (aux k e)
  exact (injective_zpow_iff_not_isOfFinOrder.2 fin) h'

theorem rosati_tate : RosatiAdj tatePre.P.A tatePre.P.L (𝟙 _) (𝟙 _) :=
  fun _ => ⟨⊤, trivial, cg _ _ 1, cg_isGen _ _ 1⟩

theorem good_tate (z : (TK InhTate.R).left) (J) : Good tatePre.P.L z J := fun _ => trivial

theorem val_tau_tate (a b : ℤ) (z : (TK InhTate.R).left) (J) :
    val (tatePre.tau a b) (𝟙 _) z J = gm (𝟙 _) z ⊤ (pi0 ^ (2 * a * b)) := by
  unfold val
  erw [tau_isConst a b]
  exact gm_res _ z _ ((good_tate z J).mem _ _) _

theorem gm_pi_zpow_injective (z : (TK InhTate.R).left) {a b : ℤ}
    (h : gm (𝟙 _) z ⊤ (pi0 ^ a) = gm (𝟙 _) z ⊤ (pi0 ^ b)) : a = b := by
  have : Subsingleton (TK InhTate.R).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing InhTate.R)))
  exact pi_zpow_injective (unit_ext fun x _ => by rw [Subsingleton.elim x z]; exact h)

theorem nonempty_TK : Nonempty (TK InhTate.R).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing InhTate.R)))

theorem tauBal_tate_iff (a a' : ℤ → ℤ) :
    tatePre.TauBal (𝟙 _) (𝟙 _) a a' ↔ ∀ y y', a y * y' = y * a' y' := by
  refine (tauBal_id_iff tatePre rosati_tate a a').trans ⟨fun h y y' => ?_, fun h y y' z J _ => ?_⟩
  · obtain ⟨z⟩ := nonempty_TK
    have := h y y' z (fun _ => PUnit.unit) (good_tate _ _)
    erw [val_tau_tate, val_tau_tate] at this
    have := gm_pi_zpow_injective z this
    linarith
  · erw [val_tau_tate, val_tau_tate]
    have k : ∀ y y' : ℤ, 2 * a y * y' = 2 * y * a' y' := fun y y' => by linarith [h y y']
    exact congrArg (fun t : ℤ => gm (𝟙 _) z ⊤ (pi0 ^ t)) (k y y')

end GlobalTheory.BoxPowerProbe
