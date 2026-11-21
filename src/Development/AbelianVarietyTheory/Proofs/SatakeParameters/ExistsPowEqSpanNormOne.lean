import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalRingCardinality.DataKerI
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LatticeFramesPrimeToLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI

section
noncomputable section

namespace GlobalTheory.UnUnitCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

section Units

variable {l : ℕ} [Fact l.Prime] {lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]}

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem exists_place {K : Type} [Field K] [NumberField K] (ψ : K →+* ℂ_[l]) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal ∧ ∀ x : K, v.valuation K x ≤ 1 → ‖ψ x‖ ≤ 1 := by
  have hint : ∀ a : 𝓞 K, ‖ψ (a : K)‖ ≤ 1 := fun a => norm_le_one_of_isIntegral (map_isIntegral_int ψ a.isIntegral_coe)
  let P : Ideal (𝓞 K) :=
    { carrier := {a | ‖ψ (a : K)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        have e : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
        simp only [Set.mem_ofPred_eq, e, map_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        have e : ((c * a : 𝓞 K) : K) = (c : K) * (a : K) := by simp
        simp only [Set.mem_ofPred_eq, smul_eq_mul, e, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (hint c)).trans_lt ha }
  have hP : ∀ a : 𝓞 K, a ∈ P ↔ ‖ψ (a : K)‖ < 1 := fun _ => Iff.rfl
  have hl : ((l : ℕ) : 𝓞 K) ∈ P := by
    rw [hP]
    have : (((l : ℕ) : 𝓞 K) : K) = (l : K) := by simp
    rw [this, map_natCast]
    have h2 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [h2, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hpr : P.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} h => ?_⟩
    · have : (1 : 𝓞 K) ∈ P := h ▸ Submodule.mem_top
      rw [hP] at this
      simp at this
    · rw [hP, hP]
      rw [hP] at h
      by_contra hn
      push Not at hn
      have e : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := by simp
      rw [e, map_mul, norm_mul] at h
      exact absurd (one_le_mul_of_one_le_of_one_le hn.1 hn.2) (not_le.2 h)
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hl
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hl)
  refine ⟨⟨P, hpr, hne⟩, hl, fun x hx => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := ⟨P, hpr, hne⟩) x hx
  have hd : ‖ψ ((d : 𝓞 K) : K)‖ = 1 := le_antisymm (hint _) (not_lt.1 d.2)
  have h2 := congrArg (fun t => ‖ψ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖ψ x‖ * ‖ψ ((d : 𝓞 K) : K)‖ = ‖ψ (n : K)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact hint n

theorem emb_mem {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) : φ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))

end Units

section Rescale

theorem applyAt0_smul {Lt : Type} (N0 N1 l : ℕ) [Fact l.Prime] (a : ℂ_[l])
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (KM.XZ Lt N0 N1) ℤ) :
    KM.applyAt0 N0 N1 l (a • Th) P = a • KM.applyAt0 N0 N1 l Th P := by
  unfold KM.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.smul_monomial, map_smul, smul_eq_mul, smul_eq_mul]
  congr 1
  ring

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

def rescale (E : KerEnt D Dx Tw)
    (t : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) → ℂ_[D.what₂.places.resChar w])
    (ht : ∀ u μ w i c c', t u μ w i c c' ≠ 0) : KerEnt D Dx Tw :=
  { E with
    Th := fun u μ w i c c' => (E.un u μ w i c c' / t u μ w i c c') • E.Th u μ w i c c'
    un := t
    un_ne := ht
    kform := fun u μ w hw i hi c c' v v' h I => by
      rw [E.kform u μ w hw i hi c c' v v' h I, applyAt0_smul, map_smul, smul_eq_mul, ← mul_assoc,
        mul_div_cancel₀ _ (ht u μ w i c c')] }

end Rescale

section Ties

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {C : CharFrame D} {nch : NChoice D}

variable (E : KerEnt D Dx Tw) (Tp : TupTied D C nch) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ)

end Ties

end GlobalTheory.UnUnitCmp
end
end

section
noncomputable section

namespace GlobalTheory.KernelScalarUnit

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts GlobalTheory.UnUnitCmp
open scoped nonZeroDivisors

section Ideals

variable {K : Type} [Field K] [NumberField K]

theorem exists_pow_eq_span {𝔞 𝔟 : Submodule (𝓞 K) K} (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (a : K), 0 < n ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {a} := by
  have hu : IsUnit 𝔞 := IsUnit.of_mul_eq_one 𝔟 h
  have hv : IsUnit 𝔟 := IsUnit.of_mul_eq_one 𝔞 (by rw [mul_comm]; exact h)
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔞, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hu)⟩
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔟, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hv)⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact h
  let U : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mkOfMulEqOne I J hIJ
  have h1 : ClassGroup.mk K (U ^ Fintype.card (ClassGroup (𝓞 K))) = 1 := by rw [map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := ClassGroup.mk_eq_one_iff.1 h1
  refine ⟨_, a, Fintype.card_pos (α := ClassGroup (𝓞 K)), ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

omit [NumberField K] in
theorem map_mem_one (c : K →+* K) {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, rfl⟩

omit [NumberField K] in
theorem map_mem_pow (c : K →+* K) {𝔞 𝔟 : Submodule (𝓞 K) K} (h : ∀ x ∈ 𝔞, c x ∈ 𝔟) :
    ∀ (n : ℕ), ∀ x ∈ 𝔞 ^ n, c x ∈ 𝔟 ^ n
  | 0, x, hx => by rw [pow_zero] at *; exact map_mem_one c hx
  | n + 1, x, hx => by
    rw [pow_succ] at *
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]; exact Submodule.mul_mem_mul (map_mem_pow c h n a ha) (h b hb)
    · rw [map_add]; exact add_mem ha hb

theorem exists_pow_eq_span_normOne (c : K →+* K) (hc : ∀ x, c (c x) = x) {𝔞 𝔟 : Submodule (𝓞 K) K}
    (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (z : K), 0 < n ∧ c z * z = 1 ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {z} := by
  obtain ⟨n, a, hn, ha⟩ := exists_pow_eq_span h
  have hb' : 𝔟 ^ n = Submodule.span (𝓞 K) {c a} := by
    apply le_antisymm
    · intro y hy
      have h1 := map_mem_pow c (fun x hx => (hb x).1 hx) n y hy
      rw [ha, Submodule.mem_span_singleton] at h1
      obtain ⟨r, hr⟩ := h1
      refine Submodule.mem_span_singleton.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, ?_⟩
      rw [← hc y, ← hr, Algebra.smul_def r, map_mul]
      rfl
    · rw [Submodule.span_singleton_le_iff_mem]
      exact map_mem_pow c (fun x hx => (hb _).2 (by rwa [hc])) n a (ha ▸ Submodule.mem_span_singleton_self a)
  have h2 : Submodule.span (𝓞 K) {a * c a} = 1 := by
    rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, ← ha, ← hb', ← mul_pow, h, one_pow]
  have h0 : a * c a ≠ 0 := fun h0 => by
    rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at h2
    have : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K) := h2 ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    simp at this
  have a0 : a ≠ 0 := left_ne_zero_of_mul h0
  have c0 : c a ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨n + n, a / c a, by omega, ?_, ?_⟩
  · rw [map_div₀, hc]; field_simp
  · rw [pow_add, ha, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_one (Submodule.span (𝓞 K) {a / c a}), ← h2,
      Submodule.span_mul_span, Set.singleton_mul_singleton]
    congr 2
    field_simp

end Ideals

theorem normOne_pow (D : D7) : NormOnePowerPrincipal D := by
  let := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rintro 𝔞 ⟨𝔟, hb, h⟩
  obtain ⟨n, z, hn, hz, e⟩ := exists_pow_eq_span_normOne (D.host.conj : D.host.E →+* D.host.E)
    (fun x => by change D.host.conj (D.host.conj x) = x; rw [← hs, ← hs, star_star]) hb h
  have hz' : star z * z = 1 := by rw [hs]; exact hz
  exact ⟨n, ⟨z, hz', by rw [mul_comm]; exact hz'⟩, hn, e⟩

section Local

variable {K : Type} [Field K] [NumberField K] {C : Type} [NormedField C] [IsUltrametricDist C] (ψ : K →+* C)

omit [NumberField K] in
theorem norm_int_le (a : 𝓞 K) : ‖ψ (a : K)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int ψ a.isIntegral_coe)

def ball (r : ℝ) (hr : 0 ≤ r) : Submodule (𝓞 K) K where
  carrier := {x | ‖ψ x‖ ≤ r}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simpa using hr
  smul_mem' := fun c a ha => by
    simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le ψ c)).trans ha

end Local

section Det

variable (D : D7) {l : ℕ} [Fact l.Prime] (ψ : D.host.E →+* ℂ_[l]) {N : ℕ}
  {L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {P : Matrix (Fin N) (Fin N) D.host.E}

end Det

section Power

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def lamTau (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (emb_mem (embT D τ)))

theorem tauEmb_eq (τ : D.what₂.Tau) : tauEmb D lam τ = lamTau D lam τ := by
  funext x
  unfold tauEmb lamC
  rw [dif_pos (emb_mem (embT D τ) x)]
  rfl

end Power

section Main

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

def detU (D : D7) {N : ℕ} (γ : letI := D.host.cmStar; Matrix.unitaryGroup (Fin N) D.host.E) : D.Dt :=
  letI := D.host.cmStar
  D.e1Dt ⟨(γ : Matrix (Fin N) (Fin N) D.host.E).det, Matrix.det_of_mem_unitary γ.2⟩

variable (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ))

end Main

end GlobalTheory.KernelScalarUnit
end
end
