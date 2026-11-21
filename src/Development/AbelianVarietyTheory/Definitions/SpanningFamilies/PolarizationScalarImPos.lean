import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticBasisOfSelfD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_int (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

theorem trace_int {a : F} (h : algebraMap F (Af F) a ∈ intAf F) : ∃ n : ℤ, Algebra.trace ℚ F a = n := by
  have h1 : a ∈ (algebraMap (𝓞 F) F).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F a fun v => ?_
    have h2 : Valued.v ((a : F) : v.adicCompletion F) ≤ 1 := h v
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
  obtain ⟨b, rfl⟩ := h1
  have h3 : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F b)) := Algebra.isIntegral_trace b.2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  exact ⟨n, hn.symm⟩

theorem int_sub {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a - b ∈ intAf F := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem int_add {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a + b ∈ intAf F := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem int_zero : (0 : Af F) ∈ intAf F := fun v => by
  rw [map_zero]; exact zero_mem _

theorem exists_char (t : Ainf F →+ ℂ) (hc : Continuous t) (hre : ∀ x, (t x).im = 0)
    (ht : ∀ a : F, t (algebraMap F (Ainf F) a) = ((Algebra.trace ℚ F a : ℚ) : ℂ)) :
    ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
      ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x) := by
  have hap : ∀ y : Af F, ∃ a : F, y - algebraMap F (Af F) a ∈ intAf F := fun y => by
    obtain ⟨a, β, hβ, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 y
    refine ⟨a, ?_⟩
    rw [h, one_smul, add_sub_cancel_left]
    exact hβ
  choose ap hap using hap
  let c : ℂ := 2 * Real.pi * Complex.I
  let f : AF F → ℂ := fun x => Complex.exp (c * (((Algebra.trace ℚ F (ap x.2) : ℚ) : ℂ) - t x.1))
  have key : ∀ (x : AF F) (a : F), x.2 - algebraMap F (Af F) a ∈ intAf F →
      f x = Complex.exp (c * (((Algebra.trace ℚ F a : ℚ) : ℂ) - t x.1)) := by
    intro x a h
    have h1 : algebraMap F (Af F) (ap x.2 - a) ∈ intAf F := by
      have := int_sub h (hap x.2)
      rw [map_sub]
      convert this using 1
      ring
    obtain ⟨n, hn⟩ := trace_int h1
    rw [map_sub, sub_eq_iff_eq_add] at hn
    show Complex.exp _ = _
    rw [hn, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨n, ?_⟩
    push_cast
    ring
  have f0 : ∀ x : AF F, x.2 ∈ intAf F → f x = Complex.exp (-(c * t x.1)) := fun x hx => by
    rw [key x 0 (by rwa [map_zero, sub_zero])]
    simp
  have fadd : ∀ x y, f (x + y) = f x * f y := fun x y => by
    rw [key (x + y) (ap x.2 + ap y.2) (by
      have := int_add (hap x.2) (hap y.2)
      rw [map_add]
      convert this using 1
      show x.2 + y.2 - _ = _
      ring), ← Complex.exp_add]
    congr 1
    rw [map_add, show (x + y).1 = x.1 + y.1 from rfl, map_add]
    push_cast
    ring
  let ψ : AddChar (AF F) ℂ :=
    { toFun := f
      map_zero_eq_one' := by
        rw [f0 0 int_zero, show (0 : AF F).1 = 0 from rfl, map_zero]; simp
      map_add_eq_mul' := fadd }
  have hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x) := fun x => by
    show f (x, 0) = _
    rw [f0 (x, 0) int_zero]
    congr 1
    push_cast
    ring
  refine ⟨ψ, ⟨?_, fun x => ?_, fun a => ?_, ?_⟩, hinf⟩
  · rw [continuous_iff_continuousAt]
    intro x₀
    have hU : {x : AF F | x.2 - x₀.2 ∈ intAf F} ∈ nhds x₀ :=
      ((isOpen_int F).preimage (continuous_snd.sub continuous_const)).mem_nhds (by
        show x₀.2 - x₀.2 ∈ intAf F
        rw [sub_self]; exact int_zero)
    have hg : Continuous fun x : AF F => f x₀ * Complex.exp (-(c * t (x.1 - x₀.1))) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul (hc.comp (continuous_fst.sub continuous_const))).neg)
    refine hg.continuousAt.congr (Filter.eventually_of_mem hU fun x hx => ?_)
    show _ = f x
    rw [← add_sub_cancel x₀ x, fadd, f0 (x - x₀) hx, add_sub_cancel]
    rfl
  · show ‖Complex.exp _‖ = 1
    rw [Complex.norm_exp]
    simp [c, hre]
  · show f _ = 1
    rw [key _ a (by
      show algebraMap F (Af F) a - _ ∈ _
      rw [sub_self]; exact int_zero)]
    show Complex.exp (c * (_ - t (algebraMap F (Ainf F) a))) = 1
    rw [ht, sub_self, mul_zero, Complex.exp_zero]
  · have hn : (Module.finrank ℚ F : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    refine ⟨pairA F (algebraMap F (Ainf F) (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))) 0, ?_⟩
    show psiInf F ψ _ ≠ 1
    rw [hinf, ht, Algebra.trace_algebraMap, nsmul_eq_mul,
      show (Module.finrank ℚ F : ℚ) * (1 / (2 * Module.finrank ℚ F)) = 1 / 2 by field_simp,
      show 2 * (Real.pi : ℂ) * Complex.I * (((-1 : ℤ)) : ℂ) * ((1 / 2 : ℚ) : ℂ) = -(Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

end Char

theorem exists_stdChar (D : D7) : ∃ ψ, IsStdChar D ψ (-1) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let t : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)))
    fun x y => by simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]
  have hts : ∀ x, t x = (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x : ℂ) := GlobalTheory.DualPairCompare.sum_infFam θ hθ
  obtain ⟨ψ, h1, h2⟩ := exists_char t (continuous_finset_sum _ fun ρ _ => (hθ ρ).2)
    (fun x => by rw [hts, Complex.ofReal_im]) (fun a => by
      show ∑ ρ, θ ρ _ = _
      rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])
  exact ⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => by rw [h2, hts, GlobalTheory.DualPairCompare.sum_infFam θ' hθ']⟩

section Lattice

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA FractionalIdeal

variable (D : D7)

def latA (r : ℕ) : Lt D.host.E r := Submodule.pi Set.univ fun _ => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)

theorem mem_latA {r : ℕ} {x : Fin r → D.host.E} : x ∈ latA D r ↔ ∀ a, x a ∈ D.host.AA :=
  ⟨fun h a => h a trivial, fun h a _ => h a⟩

theorem AA_fg : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
  FractionalIdeal.fg_of_isUnit _ (IsUnit.mk0 _ (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D))

theorem single_mem {r : ℕ} (i : Fin r) {b : D.host.E} (hb : b ∈ D.host.AA) : Pi.single i b ∈ latA D r := by
  rw [mem_latA]
  intro a
  by_cases h : a = i
  · subst h; simpa using hb
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem exists_den : ∃ n : ℕ, 0 < n ∧ ∀ a ∈ D.host.AA, IsIntegral ℤ ((n : D.host.E) * a) := by
  obtain ⟨s, hs⟩ := AA_fg D
  obtain ⟨k, hk, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, fun a ha => ?_⟩
  have ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E) := by rw [hs]; exact ha
  have : IsIntegral ℤ ((k : D.host.E) * a) := by
    clear ha
    induction ha' using Submodule.span_induction with
    | mem x hx => simpa using h x hx
    | zero => rw [mul_zero]; exact isIntegral_zero
    | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
    | smul c x _ hx => rw [Algebra.smul_def, mul_left_comm]; exact IsIntegral.mul c.2 hx
  rcases Int.natAbs_eq k with h | h
  · rw [h] at this
    simpa only [Int.cast_natCast] using this
  · rw [h] at this
    simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] using this.neg

theorem herm_diag {r : ℕ} (ε : Fin r → D.host.E) (x y : Fin r → D.host.E) :
    herm (Matrix.diagonal ε) x y = ∑ a, x a * ε a * cc (y a) := by
  unfold herm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb.symm]; simp) (by simp),
    Matrix.diagonal_apply_eq]

theorem selfD {r : ℕ} (X : Data D.host.E r) (neg : Fin r → Bool)
    (hG : X.Gm = Matrix.diagonal fun a => Examples₂.sgn (neg a)) (hΛ : X.Λ = latA D r) (hκ : X.κ0 = 2 * D.host.xi0) :
    SelfD X X.Λ := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hE : ∀ x y, EF X x y = Algebra.trace ℚ D.host.E (D.host.xi0 * -∑ a, x a * Examples₂.sgn (neg a) * cc (y a)) := by
    intro x y
    rw [EF_def, hG, herm_diag, hκ]
    congr 1
    ring
  have hs : ∀ (s : Bool) (b : D.host.E), b ∈ D.host.AA → Examples₂.sgn s * b ∈ D.host.AA := by
    intro s b hb
    cases s
    · simpa [Examples₂.sgn] using hb
    · simpa [Examples₂.sgn] using mem_coe.1 (neg_mem (mem_coe.2 hb))
  refine ⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  · rw [hΛ, mem_latA] at hx hy
    rw [hE]
    refine trace_int_of_mem hP D (neg_mem (Submodule.sum_mem _ fun a _ => ?_))
    rw [mul_comm (x a), cc_eq_conj]
    exact mem_coe.2 (mul_mem_mul (hs _ _ (hx a)) (conj_mem_AAbar D (hy a)))
  · rw [hΛ] at h ⊢
    rw [mem_latA]
    intro a
    have h1 : ∀ b ∈ D.host.AA, ∃ k : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (x a * cc b)) = k := by
      intro b hb
      obtain ⟨k, hk⟩ := h _ (single_mem D a (hs (neg a) _ (mem_coe.1 (neg_mem (mem_coe.2 hb)))))
      refine ⟨k, ?_⟩
      rw [← hk, hE, Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc]; simp [cc]) (by simp),
        Pi.single_eq_same]
      congr 2
      cases neg a <;> simp [Examples₂.sgn, cc]
    refine mem_AA_of hP D fun b hb => int_of_xi hP D fun a' ha' j hj => ?_
    obtain ⟨c, hc⟩ := int_of_AA_mul hP D ha' hb
    rw [mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
    intro u hu
    obtain ⟨u, rfl⟩ := (mem_one_iff _).1 hu
    have hm : cc (algebraMap (𝓞 D.host.E) D.host.E (c * u)) * D.host.conj j ∈ D.host.AA :=
      mem_coe.1 (Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
        (⟨_, int_cc D (c * u).2⟩ : 𝓞 D.host.E) (mem_coe.2 (conj_mem_AA D hj)))
    obtain ⟨k, hk⟩ := h1 _ hm
    refine ⟨k, ?_⟩
    rw [cc_mul, cc_cc, cc_eq_conj, conj_conj, RingHom.map_mul, hc] at hk
    rw [Algebra.traceForm_apply, eq_intCast, ← hk]
    congr 1
    ring

end Lattice

def sp (D : D7) (p q : ℕ) : HSp D :=
  Examples₂.stdSpace Examples₂.star_isIntegral (p + q) (fun a => decide (p ≤ (a : ℕ))) p q

variable {D : D7} {S T : HSp D} (C : Ctx S T)


end GlobalTheory.Ker.Model

end
