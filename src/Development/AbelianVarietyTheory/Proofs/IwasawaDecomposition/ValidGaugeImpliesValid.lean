import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PreUniformization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratingFramesComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPoint
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.JetTruncNotInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_generating_at_point : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] (φ : R →+* W) (ξ : GtPt D.toPre (Over.mk (spMap φ))) (x' : Over.mk (spMap φ) ⟶ G), IsPointOf U ξ x' → ∀ (b : Sp W ⟶ D.toPre.P.A.left), ξ.b.left = b → ∀ (g' : Frame U.LG.L (Y := Sp W) x'.left) (g : Frame D.toPre.P.L b), g'.IsGen → g.IsGen → FrRel U (T := Sp W) x'.left b g' g → ∀ (k : ℕ) (σ : H0 U.LG.L k) (F : ∀ α, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ F) → ∃ (s : W) (t : D.toPre.X → W), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL → sval σ (r ≫ x'.left) z JL = gs r z ⊤ (toΓ W s) * (val g' r z JL ^ k).val) ∧ (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM → sval (F α) (r ≫ b) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ (toΓ W (t α)) * (val g r z JM ^ k).val) ∧ ∀ e : ℕ, ∃ S : Finset D.toPre.X, (∀ α ∉ S, t α ∈ I.map φ ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map φ ^ (e + 1) := by
  first | exact @GlobalTheory.RayEv.Transport.exists_adic_expansion | exact GlobalTheory.RayEv.Transport.exists_adic_expansion | (intros; apply GlobalTheory.RayEv.Transport.exists_adic_expansion <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AdicConverge

open MvPolynomial Formalism.L2.Pj

section Coef

variable {K : Type} [CommRing K] {ρ : Type} {m : ℕ}

def jetCoef (n : ρ →₀ ℕ) (j : Jet K ρ m) : K := (Ideal.Quotient.mk_surjective j).choose.coeff n

theorem jetCoef_mk {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (p : MvPolynomial ρ K) :
    jetCoef (m := m) n (Ideal.Quotient.mk _ p) = p.coeff n := by
  have hs := Ideal.Quotient.mk_surjective (I := orig K ρ ^ (m + 1)) (Ideal.Quotient.mk (orig K ρ ^ (m + 1)) p)
  show hs.choose.coeff n = _
  have h2 : (Ideal.Quotient.mk (orig K ρ ^ (m + 1)) (hs.choose - p) : Jet K ρ m) = 0 := by
    rw [map_sub, hs.choose_spec, sub_self]
  have := (GlobalTheory.JetTest.mk_eq_zero_iff _).1 h2 n hn
  rwa [coeff_sub, sub_eq_zero] at this

theorem jetCoef_add {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (a b : Jet K ρ m) :
    jetCoef n (a + b) = jetCoef n a + jetCoef n b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_add, jetCoef_mk hn, jetCoef_mk hn, jetCoef_mk hn, coeff_add]

theorem jetCoef_smul {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (c : K) (a : Jet K ρ m) :
    jetCoef n (algebraMap K (Jet K ρ m) c * a) = c * jetCoef n a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have : algebraMap K (Jet K ρ m) c * Ideal.Quotient.mk _ p = Ideal.Quotient.mk _ (MvPolynomial.C c * p) := by
    rw [map_mul, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  rw [this, jetCoef_mk hn, jetCoef_mk hn, coeff_C_mul]

theorem jetCoef_psJet [Fintype ρ] [DecidableEq ρ] {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (h : MvPowerSeries ρ K) :
    jetCoef n (psJet m h) = MvPowerSeries.coeff n h := by
  rw [psJet, jetCoef_mk hn, GlobalTheory.JetTest.coeff_psTrunc, if_pos hn]

theorem jet_ext (a b : Jet K ρ m) (h : ∀ n : ρ →₀ ℕ, n.degree ≤ m → jetCoef n a = jetCoef n b) : a = b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← sub_eq_zero, ← map_sub, GlobalTheory.JetTest.mk_eq_zero_iff]
  intro e he
  rw [coeff_sub, ← jetCoef_mk he, ← jetCoef_mk he, h e he, sub_self]

end Coef

theorem exists_bound {α : Type} (S : Finset α) (φ : α → ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ (∀ x ∈ S, φ x ≤ q) ∧ (q = 0 ∨ ∃ x ∈ S, q = φ x) := by
  classical
  have hne : (insert 0 (S.image φ)).Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨(insert 0 (S.image φ)).max' hne, Finset.le_max' _ 0 (Finset.mem_insert_self _ _),
    fun x hx => Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem φ hx)), ?_⟩
  rcases Finset.mem_insert.1 (Finset.max'_mem _ hne) with h | h
  · exact Or.inl h
  · obtain ⟨x, hx, hq⟩ := Finset.mem_image.1 h
    exact Or.inr ⟨x, hx, hq.symm⟩

section Norms

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {R : Type} [CommRing R] (f : R →+* C)

def normIdeal (hf : ∀ r, ‖f r‖ ≤ 1) (c : ℝ) (hc : 0 ≤ c) : Ideal R where
  carrier := {a | ‖f a‖ ≤ c}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp [hc]
  smul_mem' := fun r a ha => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖f r‖ * ‖f a‖ ≤ 1 * c := mul_le_mul (hf r) ha (norm_nonneg _) zero_le_one
      _ = c := one_mul c

theorem norm_le_of_mem_pow {I : Ideal R} (hI : I.FG) (hf1 : ∀ r, ‖f r‖ ≤ 1) (hfI : ∀ r ∈ I, ‖f r‖ < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ k : ℕ, ∀ a ∈ I ^ k, ‖f a‖ ≤ q ^ k := by
  classical
  obtain ⟨G, hG⟩ := hI
  obtain ⟨q, hq0, hqG, hq⟩ := exists_bound G (fun x => ‖f x‖)
  have hq1 : q < 1 := by
    rcases hq with h | ⟨x, hx, h⟩
    · rw [h]; exact one_pos
    · rw [h]; exact hfI x (hG ▸ Ideal.subset_span hx)
  refine ⟨q, hq0, hq1, fun k => ?_⟩
  suffices h : I ^ k ≤ normIdeal f hf1 (q ^ k) (pow_nonneg hq0 k) from fun a ha => h ha
  induction k with
  | zero => intro a _; show ‖f a‖ ≤ q ^ 0; rw [pow_zero]; exact hf1 a
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    have ha' : ‖f a‖ ≤ q ^ k := ih ha
    have hspan : Ideal.span (G : Set R) ≤ normIdeal f hf1 (q ^ 1) (pow_nonneg hq0 1) :=
      Ideal.span_le.2 fun x hx => by show ‖f x‖ ≤ q ^ 1; rw [pow_one]; exact hqG x hx
    have hb' : ‖f b‖ ≤ q ^ 1 := hspan (hG.symm ▸ hb)
    show ‖f (a * b)‖ ≤ q ^ (k + 1)
    rw [map_mul, norm_mul, pow_succ]
    exact mul_le_mul ha' (by simpa using hb') (norm_nonneg _) (pow_nonneg hq0 k)

variable {W : Type} [CommRing W] [Algebra R W]

def normSub (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C) (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w) (c : ℝ)
    (hc : 0 ≤ c) : Submodule R W where
  carrier := {w | ‖Λ w‖ ≤ c}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp [hc]
  smul_mem' := fun r a ha => by
    simp only [Set.mem_setOf_eq] at *
    rw [hΛ, norm_mul]
    calc ‖f r‖ * ‖Λ a‖ ≤ 1 * c := mul_le_mul (hf r) ha (norm_nonneg _) zero_le_one
      _ = c := one_mul c

theorem bound_of_finite [Module.Finite R W] (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C)
    (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w) : ∃ B : ℝ, 0 ≤ B ∧ ∀ w, ‖Λ w‖ ≤ B := by
  classical
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := W)
  obtain ⟨B, hB0, hBT, -⟩ := exists_bound T (fun w => ‖Λ w‖)
  refine ⟨B, hB0, fun w => ?_⟩
  have h : (⊤ : Submodule R W) ≤ normSub f hf Λ hΛ B hB0 := hT ▸ Submodule.span_le.2 (fun x hx => hBT x hx)
  exact h Submodule.mem_top

theorem bound_pow (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C) (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w)
    {I : Ideal R} {q B : ℝ} (hq0 : 0 ≤ q) (hq : ∀ k : ℕ, ∀ a ∈ I ^ k, ‖f a‖ ≤ q ^ k) (hB : ∀ w, ‖Λ w‖ ≤ B)
    (e : ℕ) (x : W) (hx : x ∈ I.map (algebraMap R W) ^ e) : ‖Λ x‖ ≤ q ^ e * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [← Ideal.map_pow] at hx
  have hx' : x ∈ (I ^ e) • (⊤ : Submodule R W) := by
    rw [Ideal.smul_top_eq_map]; exact hx
  have hle : (I ^ e) • (⊤ : Submodule R W) ≤ normSub f hf Λ hΛ (q ^ e * B) (mul_nonneg (pow_nonneg hq0 e) hB0) :=
    Submodule.smul_le.2 fun a ha w _ => by
      show ‖Λ (a • w)‖ ≤ q ^ e * B
      rw [hΛ, norm_mul]
      exact mul_le_mul (hq e a ha) (hB w) (norm_nonneg _) (pow_nonneg hq0 e)
  exact hle hx'

theorem hasSum_of_adic (Λ : W →+ C) (J : Ideal W)
    (hbound : ∀ ε > 0, ∃ e : ℕ, ∀ x ∈ J ^ (e + 1), ‖Λ x‖ < ε) {X : Type} (s : W) (t : X → W)
    (hst : ∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ J ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ J ^ (e + 1)) :
    HasSum (fun α => Λ (t α)) (Λ s) := by
  classical
  change Filter.Tendsto (fun S : Finset X => ∑ b ∈ S, Λ (t b)) Filter.atTop (nhds (Λ s))
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨e, he⟩ := hbound ε hε
  obtain ⟨S, hS1, hS2⟩ := hst e
  refine ⟨S, fun S' hS' => ?_⟩
  have hmem : s - ∑ α ∈ S', t α ∈ J ^ (e + 1) := by
    have h : s - ∑ α ∈ S', t α = (s - ∑ α ∈ S, t α) - ∑ α ∈ S' \ S, t α := by
      rw [← Finset.sum_sdiff hS']; abel
    rw [h]
    exact sub_mem hS2 (sum_mem fun α hα => hS1 α (Finset.mem_sdiff.1 hα).2)
  rw [dist_eq_norm, ← map_sum, ← map_sub, ← norm_neg, ← map_neg, neg_sub]
  exact he _ hmem

end Norms

theorem converge : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (R : Type) [CommRing R] (I : Ideal R), I.FG → ∀ f : R →+* C, (∀ r, ‖f r‖ ≤ 1) → (∀ r ∈ I, ‖f r‖ < 1) → ∀ (W : Type) [CommRing W] [Algebra R W] [Module.Finite R W] (ρ : Type) [Fintype ρ] [DecidableEq ρ] (m : ℕ) (κ : W →+* Jet C ρ m), (∀ r, κ (algebraMap R W r) = algebraMap C (Jet C ρ m) (f r)) → ∀ (X : Type) (s : W) (t : X → W), (∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) → ∀ (u : Jet C ρ m) (g : X → MvPowerSeries ρ C), (∀ α, psJet m (g α) = u * κ (t α)) → (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → Summable fun α => MvPowerSeries.coeff n (g α)) ∧ ∀ g₀ : MvPowerSeries ρ C, (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → HasSum (fun α => MvPowerSeries.coeff n (g α)) (MvPowerSeries.coeff n g₀)) → psJet m g₀ = u * κ s := by
  intro C _ _ _ R _ I hI f hf1 hfI W _ _ _ ρ _ _ m κ hκ X s t hst u g hg
  obtain ⟨q, hq0, hq1, hq⟩ := norm_le_of_mem_pow f hI hf1 hfI
  have key : ∀ n : ρ →₀ ℕ, n.degree ≤ m →
      HasSum (fun α => MvPowerSeries.coeff n (g α)) (jetCoef n (u * κ s)) := by
    intro n hn
    let Λ : W →+ C := AddMonoidHom.mk' (fun w => jetCoef n (u * κ w)) (fun a b => by
      simp only [map_add, mul_add]; exact jetCoef_add hn _ _)
    have hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w := by
      intro r w
      show jetCoef n (u * κ (r • w)) = f r * jetCoef n (u * κ w)
      rw [Algebra.smul_def, map_mul, hκ, mul_left_comm, jetCoef_smul hn]
    obtain ⟨B, hB0, hB⟩ := bound_of_finite f hf1 Λ hΛ
    have hcoef : ∀ α, MvPowerSeries.coeff n (g α) = Λ (t α) := fun α => by
      rw [← jetCoef_psJet hn, hg α]; rfl
    have hbound : ∀ ε > 0, ∃ e : ℕ, ∀ x ∈ I.map (algebraMap R W) ^ (e + 1), ‖Λ x‖ < ε := by
      intro ε hε
      have hB1 : (0 : ℝ) < B + 1 := by linarith
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hB1) hq1
      refine ⟨k, fun x hx => ?_⟩
      calc ‖Λ x‖ ≤ q ^ (k + 1) * B := bound_pow f hf1 Λ hΛ hq0 hq hB (k + 1) x hx
        _ ≤ q ^ k * (B + 1) :=
          mul_le_mul (pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ k)) (by linarith) hB0 (pow_nonneg hq0 k)
        _ < ε / (B + 1) * (B + 1) := mul_lt_mul_of_pos_right hk hB1
        _ = ε := div_mul_cancel₀ _ (ne_of_gt hB1)
    have h := hasSum_of_adic Λ (I.map (algebraMap R W)) hbound s t hst
    simp only [← hcoef] at h
    exact h
  refine ⟨fun n hn => (key n hn).summable, fun g₀ hg₀ => jet_ext _ _ fun n hn => ?_⟩
  rw [jetCoef_psJet hn]
  exact (hg₀ n hn).unique (key n hn)

end GlobalTheory.AdicConverge
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_evaluation_power_series : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (R : Type) [CommRing R] (I : Ideal R), I.FG → ∀ f : R →+* C, (∀ r, ‖f r‖ ≤ 1) → (∀ r ∈ I, ‖f r‖ < 1) → ∀ (W : Type) [CommRing W] [Algebra R W] [Module.Finite R W] (ρ : Type) [Fintype ρ] [DecidableEq ρ] (m : ℕ) (κ : W →+* Jet C ρ m), (∀ r, κ (algebraMap R W r) = algebraMap C (Jet C ρ m) (f r)) → ∀ (X : Type) (s : W) (t : X → W), (∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) → ∀ (u : Jet C ρ m) (g : X → MvPowerSeries ρ C), (∀ α, psJet m (g α) = u * κ (t α)) → (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → Summable fun α => MvPowerSeries.coeff n (g α)) ∧ ∀ g₀ : MvPowerSeries ρ C, (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → HasSum (fun α => MvPowerSeries.coeff n (g α)) (MvPowerSeries.coeff n g₀)) → psJet m g₀ = u * κ s := by
  atlas_forward_decl GlobalTheory.AdicConverge.converge
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv.Transport

open GlobalTheory.TorusModel

theorem exists_refine {S : Scheme.{0}} {H T₁ T₂ Z : Over S} [IsSeparated H.hom] [IsFinite T₁.hom] [IsFinite T₂.hom]
    {w₁ : T₁ ⟶ H} {w₂ : T₂ ⟶ H} {k₁ : Z ⟶ T₁} {k₂ : Z ⟶ T₂} (h : k₁ ≫ w₁ = k₂ ≫ w₂) :
    ∃ (T : Over S) (_ : IsFinite T.hom) (p₁ : T ⟶ T₁) (p₂ : T ⟶ T₂) (k : Z ⟶ T),
      p₁ ≫ w₁ = p₂ ≫ w₂ ∧ k ≫ p₁ = k₁ ∧ k ≫ p₂ = k₂ := by
  have : IsFinite (w₂.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have : IsFinite w₂.left := IsFinite.of_comp w₂.left H.hom
  have hl : k₁.left ≫ w₁.left = k₂.left ≫ w₂.left := congrArg (·.left) h
  refine ⟨Over.mk (pullback.fst w₁.left w₂.left ≫ T₁.hom),
    inferInstanceAs (IsFinite (pullback.fst w₁.left w₂.left ≫ T₁.hom)), Over.homMk (pullback.fst _ _) rfl,
    Over.homMk (pullback.snd _ _) ?_, Over.homMk (pullback.lift k₁.left k₂.left hl) ?_,
    Over.OverMorphism.ext pullback.condition, Over.OverMorphism.ext (pullback.lift_fst _ _ _),
    Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  · change pullback.snd w₁.left w₂.left ≫ T₂.hom = pullback.fst w₁.left w₂.left ≫ T₁.hom
    rw [← Over.w w₂, ← Over.w w₁, pullback.condition_assoc]
  · change pullback.lift k₁.left k₂.left hl ≫ pullback.fst w₁.left w₂.left ≫ T₁.hom = Z.hom
    rw [pullback.lift_fst_assoc, Over.w]

def rat {X X' Y Z : Scheme.{0}} {L : LB X'} {M : LB X} {ψ' : Y ⟶ X'} {ψ : Y ⟶ X} (g' : Frame L ψ') (g : Frame M ψ)
    (r : Z ⟶ Y) (z : Z) (JM : (Z ⟶ X) → M.ι) (JL : (Z ⟶ X') → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val g r z JM * (val g' r z JL)⁻¹

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G)
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} (Y : Ray oa)

def Near {Z : Over (Sp R)} (x : Z ⟶ Y.H) (x' : Z ⟶ G) : Prop :=
  ∃ (T : Over (Sp R)) (_ : IsFinite T.hom) (k : Z ⟶ T) (w : T ⟶ Y.H) (w' : T ⟶ G),
    IsPointOf U (Y.Φ T w) w' ∧ k ≫ w = x ∧ k ≫ w' = x'

variable {U Y}

instance : IsSeparated Y.H.hom := (isSemiAbelian_of_isGt _ _ _ Y.isGt).separated

instance : Smooth Y.H.hom := (isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth

theorem pt_pull {T T' : Over (Sp R)} (k : T' ⟶ T) {w : T ⟶ Y.H} {w' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w') :
    IsPointOf U (Y.Φ T' (k ≫ w)) (k ≫ w') := h.pull k (Y.rep.1 _ _ k w)

theorem pt_act {ιA : A.OAct O} {a : OAct O G} (hO : U.OLinear O oa ιA a.toRingAct) (c : O) {T : Over (Sp R)}
    {w : T ⟶ Y.H} {w' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w') :
    IsPointOf U (Y.Φ T (w ≫ Y.act.act c)) (w' ≫ a.act c) :=
  h.smul GlobalTheory.allSixLaws.1.globalFns hO c (Y.smul c T w)

theorem Near.comp {Z Z' : Over (Sp R)} {x : Z ⟶ Y.H} {x' : Z ⟶ G} (h : Near U Y x x') (r : Z' ⟶ Z) :
    Near U Y (r ≫ x) (r ≫ x') := by
  obtain ⟨T, hT, k, w, w', hw, rfl, rfl⟩ := h
  exact ⟨T, hT, r ≫ k, w, w', hw, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem Near.act {ιA : A.OAct O} {a : OAct O G} (hO : U.OLinear O oa ιA a.toRingAct) (c : O) {Z : Over (Sp R)}
    {x : Z ⟶ Y.H} {x' : Z ⟶ G} (h : Near U Y x x') : Near U Y (x ≫ Y.act.act c) (x' ≫ a.act c) := by
  obtain ⟨T, hT, k, w, w', hw, rfl, rfl⟩ := h
  exact ⟨T, hT, k, _, _, pt_act hO c hw, (Category.assoc _ _ _).symm, (Category.assoc _ _ _).symm⟩

theorem FrRel.pull {T T' : Scheme.{0}} {x' : T ⟶ G.left} {b : T ⟶ D.toPre.P.A.left} {g' : Frame U.LG.L x'}
    {g : Frame D.toPre.P.L b} (h : FrRel U x' b g' g) (p : T' ⟶ T) :
    FrRel U (p ≫ x') (p ≫ b) (LB.pullGen _ _ _ g' p) (LB.pullGen _ _ _ g p) := fun e Z r y hy z JM JL hM hL =>
  (val_pull hM g p r).trans ((h e Z (r ≫ p) y (hy.trans (Category.assoc _ _ _).symm) z JM JL hM hL).trans
    (congrArg _ (val_pull hL g' p r).symm))

variable [IsNoetherianRing R] [hc : IsAdicComplete (maximalIdeal R) R]

theorem adic (T : Over (Sp R)) [IsFinite T.hom] : IsAdicColimit (maximalIdeal R) T :=
  FiniteTorsLift.isAdicColimit_of_isFinite_noetherian hc T

theorem pt_unique {T : Over (Sp R)} [IsFinite T.hom] {w : T ⟶ Y.H} {w' w'' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w')
    (h' : IsPointOf U (Y.Φ T w) w'') : w' = w'' := (existsUnique_point U (adic T) _).unique h h'

theorem Near.unique {Z : Over (Sp R)} {x : Z ⟶ Y.H} {x' x'' : Z ⟶ G} (h : Near U Y x x') (h' : Near U Y x x'') :
    x' = x'' := by
  obtain ⟨T, hT, k, w, w', hw, e, rfl⟩ := h
  obtain ⟨T₂, hT₂, k₂, w₂, w₂', hw₂, e₂, rfl⟩ := h'
  obtain ⟨T₃, _, p₁, p₂, l, h₁, rfl, rfl⟩ := exists_refine (e.trans e₂.symm)
  rw [Category.assoc, Category.assoc, pt_unique (pt_pull p₁ hw) (h₁ ▸ pt_pull p₂ hw₂)]

variable (U Y) in

def Loc {Z : Over (Sp R)} (x : Z ⟶ Y.H) (x' : Z ⟶ G) (e' : Frame U.LG.L x'.left)
    (e : Frame D.toPre.P.L (x ≫ Y.q).left) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra R W) (_ : Module.Finite R W)
    (k : Z ⟶ Over.mk (spMap (algebraMap R W))) (w : Over.mk (spMap (algebraMap R W)) ⟶ Y.H)
    (w' : Over.mk (spMap (algebraMap R W)) ⟶ G) (g' : Frame U.LG.L w'.left) (g : Frame D.toPre.P.L (w ≫ Y.q).left)
    (ρ : Γ(Z.left, ⊤)ˣ), IsPointOf U (Y.Φ _ w) w' ∧ k ≫ w = x ∧ k ≫ w' = x' ∧ g'.IsGen ∧ g.IsGen ∧
    FrRel U w'.left (w ≫ Y.q).left g' g ∧
    (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z.left) (z : Z') (J), Good U.LG.L z J →
      val e' r z J = gm r z ⊤ ρ * val g' (r ≫ k.left) z J) ∧
    ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z.left) (z : Z') (J), Good D.toPre.P.L z J →
      val e r z J = gm r z ⊤ ρ * val g (r ≫ k.left) z J

section Loc

variable {Z : Over (Sp R)} {x : Z ⟶ Y.H} {x' : Z ⟶ G} {e' : Frame U.LG.L x'.left}
  {e : Frame D.toPre.P.L (x ≫ Y.q).left} (h : Loc U Y x x' e' e)
include h

end Loc

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] hc in
theorem gs_toΓ {W J : Type} [CommRing W] [CommRing J] (κ : W →+* J) (y : Sp J) (t : W) :
    gs (spMap κ) y ⊤ (toΓ W t) = gs (𝟙 (Sp J)) y ⊤ (toΓ J (κ t)) := by
  have h := congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom κ))
  have h' : toΓ J (κ t) = (spMap κ).appTop.hom (toΓ W t) := h
  rw [h']
  exact ((gs_pull (𝟙 _) (spMap κ) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem Loc.germ {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (f : R →+* C)
    (hf : ∀ r, ‖f r‖ ≤ 1) (hf' : ∀ r ∈ maximalIdeal R, ‖f r‖ < 1) {ρ : Type} [Fintype ρ] [DecidableEq ρ] {m : ℕ}
    {x : overAt (spMap f) (Jet C ρ m) ⟶ Y.H} {x' : overAt (spMap f) (Jet C ρ m) ⟶ G} {e' : Frame U.LG.L x'.left}
    {e : Frame D.toPre.P.L (x ≫ Y.q).left} (h : Loc U Y x x' e' e) {k : ℕ} {σ : H0 U.LG.L k}
    {F : ∀ α, D.toPre.SecB k α} (hF : ∀ l, U.ExpandsAt l k σ F) {g : D.toPre.X → MvPowerSeries ρ C}
    (hg : ∀ α y J, Good D.toPre.P.L y J → sval (F α) (x ≫ Y.q).left y J * (val ((Y.Φ _ x).s α) (𝟙 _) y J).val =
      gs (𝟙 _) y ⊤ (toΓ _ (psJet m (g α))) * (val e (𝟙 _) y J ^ k).val) :
    (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → Summable fun α => MvPowerSeries.coeff n (g α)) ∧
      ∀ g₀ : MvPowerSeries ρ C, (∀ n : ρ →₀ ℕ, HasSum (fun α => MvPowerSeries.coeff n (g α)) (MvPowerSeries.coeff n g₀)) →
        ∀ y J, Good U.LG.L y J →
          sval σ x'.left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g₀)) * (val e' (𝟙 _) y J ^ k).val := by
  obtain ⟨W, _, _, _, _, l, w, w', c', c, u, hw, rfl, rfl, a', a, fr, v', v⟩ := h
  obtain ⟨κ, hκ⟩ : ∃ κ : W →+* Jet C ρ m, spMap κ = l.left := by
    obtain ⟨κ, hκ⟩ := Spec.map_surjective (show Spec (.of (Jet C ρ m)) ⟶ Spec (.of W) from l.left)
    exact ⟨κ.hom, hκ⟩
  have hκ' : ∀ r, κ (algebraMap R W r) = algebraMap C (Jet C ρ m) (f r) := fun r => by
    have h₁ : spMap κ ≫ spMap (algebraMap R W) = spMap (algebraMap C (Jet C ρ m)) ≫ spMap f :=
      (congrArg (· ≫ spMap (algebraMap R W)) hκ).trans (Over.w l)
    rw [← Spec.map_comp, ← Spec.map_comp] at h₁
    exact congrArg (fun q => q.hom r) (Spec.map_injective h₁)
  obtain ⟨s, t, hs, ht, hst⟩ := GlobalTheory.T.frames_generating_at_point R _ D A G U W (algebraMap R W) _ w' hw _
    (congrArg (·.left) (Y.Φ_b w)) c' c a' a fr k σ F hF
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Jet C ρ m, toΓ _ u₀ = (u⁻¹ ^ k).val :=
    ⟨(Scheme.ΓSpecIso (.of (Jet C ρ m))).hom.hom (u⁻¹ ^ k).val, Iso.hom_inv_id_apply _ _⟩
  have key : ∀ (y : Sp (Jet C ρ m)) (a : W) (b : ((Sp (Jet C ρ m)).presheaf.stalk y)ˣ),
      gs (𝟙 _) y ⊤ (toΓ _ (u₀ * κ a)) * ((gm (𝟙 (Sp (Jet C ρ m))) y ⊤ u * b) ^ k).val =
        gs (spMap κ) y ⊤ (toΓ W a) * (b ^ k).val := fun y a b => by
    rw [gs_toΓ, map_mul, gs_mul _ y ⊤ trivial, hu₀]
    erw [gs_unit (𝟙 (Sp (Jet C ρ m))) y ⊤ trivial]
    rw [map_pow, map_inv, mul_right_comm, ← Units.val_mul, ← mul_pow, inv_mul_cancel_left, mul_comm]
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.jet_evaluation_power_series C R _ (maximalIdeal R).fg_of_isNoetherianRing f hf hf' W ρ m κ hκ' _ s t hst u₀ g
    fun α => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Jet C ρ m))).inv).1
      (fn_ext (V := ⊤) fun y _ => by
        obtain ⟨J, hJ⟩ := UU.exists_good_pt D.toPre.P.isLB y
        have e₁ := hg α y J hJ
        have e₂ := ht α _ l.left y J hJ
        have e₃ := ((isPull_iff _ _ _).1 (Y.rep.1 _ _ l w)).2 α y J hJ
        have e₄ := v _ (𝟙 _) y J hJ
        rw [Category.id_comp] at e₄
        refine (val e (𝟙 _) y J ^ k).mul_left_inj.1 (e₁.symm.trans ?_)
        rw [e₄]
        refine Eq.trans ?_ (key y (t α) (val c l.left y J)).symm
        rw [hκ]
        refine Eq.trans (congrArg₂ (· * ·) ?_ (congrArg Units.val e₃)) e₂
        rw [Category.assoc]
        rfl)
  refine ⟨h₁, fun g₀ hg₀ y J hJ => ?_⟩
  have e₄ := v' _ (𝟙 _) y J hJ
  rw [Category.id_comp] at e₄
  rw [h₂ g₀ fun n _ => hg₀ n, e₄]
  refine (hs _ l.left y J hJ).trans (Eq.trans ?_ (key y s _).symm)
  rw [hκ]

open NumberField
open Formalism.MainNotions.DIV.Cons (SCF intO)

end GlobalTheory.RayEv.Transport
end
end
