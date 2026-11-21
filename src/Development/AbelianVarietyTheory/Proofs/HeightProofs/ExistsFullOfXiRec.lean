import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Formalism.LocalToGlobal.ProjectiveLattices.FullXi
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullDataExtension
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Hilbert90FiniteIdelesCongruence
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FieldTwistConditions
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGeneratingCharacters

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdeles_normOne_eq_div_conj_of_congOne : ∀ (D : D7), (∀ x : (AfE D)ˣ, NormOne x → ∃ y, x = y / cjFin D y) ∧ (∀ y : (AfE D)ˣ, cjFin D y = y → ∃ a : Af D.host.F, (y : AfE D) = a ⊗ₜ 1) ∧ ∀ (p N : ℕ) (x : (AfE D)ˣ), p.Prime → p ≠ 2 → p ∣ N → 0 < N → NormOne x → CongOne N x → ∃ y, IntUnit y ∧ CongOne p y ∧ x = y / cjFin D y := by
  first | exact @GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence | exact GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence | (intros; apply GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.TwistFieldCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.L2.Theta
open GlobalTheory.FinalJoin GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

variable {D : D7}

theorem cF_eq (a : D.host.E) : GlobalTheory.Member.cF D a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [GlobalTheory.XiCounterexample.conj_emb]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

theorem barF_tmul (a : Af D.host.F) (e : D.host.E) :
    barF D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] D.host.conj e := by
  rw [← cF_eq]; rfl

theorem bar_eq (x : AfE D) : FieldTwistConditions.bar D x = barF D x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [barF_tmul, ← D.conjF_eq]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem normOne_iff (x : (AfE D)ˣ) : FieldTwistConditions.NormOne D x ↔ NormOne x := by
  unfold FieldTwistConditions.NormOne NormOne
  rw [bar_eq]

def UnramOff (D : D7) (p : ℕ) (xi : (AfE D)ˣ →* ℂˣ) : Prop := ∀ x, NormOne x → CongOne p x → xi x = 1

end GlobalTheory.TwistFieldCompare
end
end

section
noncomputable section

namespace GlobalTheory.FinalJoin2.ReadTwist

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val (D : D7) (y : (AfE D)ˣ) :
    ((cjFin D y : (AfE D)ˣ) : AfE D) = GlobalTheory.NormOneChar.bar (cF D) (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin
  rw [h]
  rfl

theorem normOne_iff {D : D7} (x : (AfE D)ˣ) :
    NormOne x ↔ (x : AfE D) * GlobalTheory.NormOneChar.bar (cF D) (x : AfE D) = 1 := Iff.rfl

theorem congOne_iff {D : D7} (N : ℕ) (x : (AfE D)ˣ) :
    x ∈ GlobalTheory.NormOneChar.congOne (cF D) N ↔ CongOne N x ∧ NormOne x := by
  unfold CongOne
  simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
  exact Iff.rfl

theorem cF_cF (D : D7) (y : D.host.E) : cF D (cF D y) = y := star_star y

theorem exists_rat {D : D7} (x : (AfE D)ˣ) (a : D.host.E) (h : (x : AfE D) = 1 ⊗ₜ a) (hn : NormOne x) :
    ∃ (y : (AfE D)ˣ) (b : D.host.E), (y : AfE D) = 1 ⊗ₜ b ∧ x = y / cjFin D y := by
  have key : ∀ b : D.host.E, b ≠ 0 → (x : AfE D) * GlobalTheory.NormOneChar.diag D.host.F D.host.E (cF D b) =
      GlobalTheory.NormOneChar.diag D.host.F D.host.E b →
      ∃ (y : (AfE D)ˣ) (b : D.host.E), (y : AfE D) = 1 ⊗ₜ b ∧ x = y / cjFin D y := fun b hb e => by
    refine ⟨(GlobalTheory.NormOneChar.isUnit_diag D.host.F D.host.E hb).unit, b, rfl, eq_div_iff_mul_eq'.2 (Units.ext ?_)⟩
    rw [Units.val_mul, cjFin_val]
    exact e
  have hx : (x : AfE D) = GlobalTheory.NormOneChar.diag D.host.F D.host.E a := h
  by_cases ha : 1 + a = 0
  · have hc : cF D ≠ 1 := by
      have : cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
      rw [this]
      exact IsCMField.complexConj_ne_one _
    obtain ⟨z, hz⟩ : ∃ z, cF D z ≠ z := by
      by_contra h0
      push_neg at h0
      exact hc (AlgEquiv.ext h0)
    refine key (z - cF D z) (sub_ne_zero.2 hz.symm) ?_
    rw [hx, ← map_mul, map_sub, cF_cF]
    congr 1
    linear_combination (cF D z - z) * ha
  · refine key (1 + a) ha ?_
    have h1 : (x : AfE D) * GlobalTheory.NormOneChar.diag D.host.F D.host.E (cF D a) = 1 := by
      have := (normOne_iff x).1 hn
      rw [h] at this
      rw [h]
      exact this
    rw [map_add, map_one, map_add, map_add, map_one, mul_add, h1, ← hx, mul_one, add_comm]

theorem cong_div {D : D7} (N : ℕ) (y : (AfE D)ˣ) (hu : IntUnit y) (hy : CongOne N y) :
    CongOne N (y / cjFin D y) ∧ NormOne (y / cjFin D y) := by
  have hv : ((y / cjFin D y : (AfE D)ˣ) : AfE D) =
      (y : AfE D) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D) := by
    rw [div_eq_mul_inv, ← map_inv, Units.val_mul, cjFin_val]
  have h1 : (y : AfE D) * ((y⁻¹ : (AfE D)ˣ) : AfE D) = 1 := Units.mul_inv y
  have h2 : GlobalTheory.NormOneChar.bar (cF D) (y : AfE D) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D) = 1 := by
    rw [← map_mul, h1, map_one]
  rw [← congOne_iff]
  obtain ⟨-, hi⟩ := hu
  obtain ⟨w, hw, e⟩ := hy
  rw [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers] at hi hw
  rw [nsmul_eq_mul] at e
  have e' := congrArg (GlobalTheory.NormOneChar.bar (cF D)) e
  rw [map_sub, map_one, map_mul, map_natCast] at e'
  have hi' := GlobalTheory.NormOneChar.bar_mem (cF D) hi
  have hw' := GlobalTheory.NormOneChar.bar_mem (cF D) hw
  refine ⟨⟨(w - GlobalTheory.NormOneChar.bar (cF D) w) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D),
    mul_mem (sub_mem hw hw') hi', ?_⟩, ?_⟩
  · rw [hv]
    linear_combination (GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D)) * (e - e') + h2
  · rw [hv, map_mul, GlobalTheory.NormOneChar.bar_bar _ (cF_cF D)]
    linear_combination ((y : AfE D) * ((y⁻¹ : (AfE D)ˣ) : AfE D)) * h2 + h1

theorem exists_xiOK_xiTilde : ∀ (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ), (p = D.host.pde ∨ p = D.host.pde') → XiRec D p de → ∃ xi, XiOK D p xi ∧ XiTilde xi de := by
  intro D p de hp h
  obtain ⟨h90, hfix, hcong⟩ := GlobalTheory.T.finiteIdeles_normOne_eq_div_conj_of_congOne D
  have hpp : p.Prime ∧ p % 15 = 1 := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2⟩
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hpp.2 (by norm_num)
  let q : (AfE D)ˣ →* (AfE D)ˣ := MonoidHom.id _ / cjFin D
  obtain ⟨xi, hxi⟩ := GlobalTheory.PrimaryCharacter.exists_factor_of_ker_le q de fun x hx => by
    have h1 : x = cjFin D x := div_eq_one.1 hx
    obtain ⟨a, ha⟩ := hfix x h1.symm
    exact h.real x a ha
  have ht : XiTilde xi de := hxi
  refine ⟨xi, ⟨fun x a ha hn => ?_, fun x hn hc => ?_, ?_, ?_, fun x hn => ?_⟩, ht⟩
  · obtain ⟨y, b, hb, rfl⟩ := exists_rat x a ha hn
    rw [ht, h.rat y b hb]
  · obtain ⟨y, hy, hyc, rfl⟩ := hcong p _ x hpp.1 hp2 (Dvd.intro_left _ rfl)
      (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hpp.1.pos) hn hc
    rw [ht, h.tame y hy hyc]
  · obtain ⟨y, hy, hyc, hne⟩ := h.ram
    obtain ⟨c1, c2⟩ := cong_div _ y hy hyc
    exact ⟨_, c2, c1, by rwa [ht]⟩
  · obtain ⟨m, hm, hf⟩ := h.fin
    refine ⟨m, hm, fun x hn => ?_⟩
    obtain ⟨y, rfl⟩ := h90 x hn
    rw [ht, hf]
  · obtain ⟨y, rfl⟩ := h90 x hn
    rw [ht]
    exact h.val y

end GlobalTheory.FinalJoin2.ReadTwist
end
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shortSeriesTwistChar_of_twistingIdeleChar : ∀ (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ), (p = D.host.pde ∨ p = D.host.pde') → XiRec D p de → ∃ xi, XiOK D p xi ∧ XiTilde xi de := by
  first | exact @GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde | exact GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde | (intros; apply GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.FullExt

theorem exists_full_of_xiRec : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ de, XiRec D p de → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ XiTilde TF.xi de ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  intro D J T hJ hT hc hcan p hp P hP de hde
  obtain ⟨xi, hxi, ht⟩ := GlobalTheory.T.exists_shortSeriesTwistChar_of_twistingIdeleChar D p de hp.own hde
  obtain ⟨dd, TF, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiOK_noVol D J T hJ hT hc hcan p hp P hP xi hxi
  exact ⟨dd, TF, h1, h2, h3, h4 ▸ ht, h5⟩

end GlobalTheory.FinalJoin2.FullExt
end
