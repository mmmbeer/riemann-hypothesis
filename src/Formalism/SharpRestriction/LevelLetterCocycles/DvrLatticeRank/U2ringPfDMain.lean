import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
import Formalism.PadicSubsetSums.StableGradedCounts.ConcreteDictionaryHolds
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB

section
namespace DualFramesAlt.EigenUniformiser

open PowerSeries

structure Data (O : Type*) [CommRing O] (Δ : Type*) [Group Δ] [Fintype Δ] where
  ρ : Δ →* (PowerSeries O ≃ₐ[O] PowerSeries O)
  ω : Δ →* Oˣ
  hω : Function.Injective ω
  v : Δ → PowerSeries O
  hv : ∀ δ, ρ δ X = X * v δ
  hv0 : ∀ δ, constantCoeff (v δ) = (ω δ : O)

variable {O : Type*} [CommRing O] [IsDomain O] {Δ : Type*} [Group Δ] [Fintype Δ] [IsCyclic Δ]

noncomputable def piPrime (D : Data O Δ) : PowerSeries O := ∏ δ, D.ρ δ X

noncomputable def pi1 (D : Data O Δ) (hs : IsUnit (Fintype.card Δ : O)) : PowerSeries O :=
  ((hs.unit⁻¹ : Oˣ) : O) • ∑ δ, (((D.ω δ)⁻¹ : Oˣ) : O) • D.ρ δ X

section Lemmas

variable (D : Data O Δ)

theorem constantCoeff_rho_X (δ : Δ) : constantCoeff (D.ρ δ X) = 0 := by
  rw [D.hv, map_mul, constantCoeff_X, zero_mul]

theorem rho_rho_X (δ ε : Δ) : D.ρ δ (D.ρ ε X) = D.ρ (δ * ε) X := by
  rw [map_mul, AlgEquiv.mul_apply]

theorem rho_subst (δ : Δ) {p : PowerSeries O} (hp : constantCoeff p = 0) (g : PowerSeries O) :
    D.ρ δ (PowerSeries.subst p g) = PowerSeries.subst (D.ρ δ p) g :=
  algHom_subst (D.ρ δ).toAlgHom (constantCoeff_rho_X D δ) hp g

theorem omega_pow_card (δ : Δ) : ((D.ω δ : Oˣ) : O) ^ Fintype.card Δ = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

theorem card_ne_zero : Fintype.card Δ ≠ 0 := Fintype.card_ne_zero

theorem piPrime_invariant (δ : Δ) : D.ρ δ (piPrime D) = piPrime D := by
  unfold piPrime
  rw [map_prod]
  simp_rw [rho_rho_X]
  exact Equiv.prod_comp (Equiv.mulLeft δ) (fun ε => D.ρ ε X)

variable (hs : IsUnit (Fintype.card Δ : O))

theorem coeff_eigen_uniformiser (n : ℕ) : coeff n (pi1 D hs) =
    ((hs.unit⁻¹ : Oˣ) : O) * ∑ δ, (((D.ω δ)⁻¹ : Oˣ) : O) * coeff n (D.ρ δ X) := by
  simp [pi1, map_sum, smul_eq_mul]

theorem coeff_zero_eigen_uniformiser : coeff 0 (pi1 D hs) = 0 := by
  rw [coeff_eigen_uniformiser]
  simp [D.hv]

theorem coeff_one_eigen_uniformiser : coeff 1 (pi1 D hs) = 1 := by
  rw [coeff_eigen_uniformiser]
  have h1 : ∀ δ, coeff 1 (D.ρ δ X) = (D.ω δ : O) := by
    intro δ
    rw [D.hv, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      D.hv0]
  simp_rw [h1, Units.inv_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact hs.val_inv_mul

theorem constantCoeff_eigen_uniformiser : constantCoeff (pi1 D hs) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_zero_eigen_uniformiser]

theorem isUnit_coeff_one_eigen_uniformiser : IsUnit (coeff 1 (pi1 D hs)) := by
  rw [coeff_one_eigen_uniformiser]; exact isUnit_one

theorem rho_eigen_uniformiser (δ : Δ) : D.ρ δ (pi1 D hs) = (D.ω δ : O) • pi1 D hs := by
  unfold pi1
  rw [map_smul, map_sum]
  simp_rw [map_smul, rho_rho_X]
  have key : ∑ ε, (((D.ω ε)⁻¹ : Oˣ) : O) • D.ρ (δ * ε) X =
      (D.ω δ : O) • ∑ η, (((D.ω η)⁻¹ : Oˣ) : O) • D.ρ η X := by
    conv_rhs => rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft δ)]
    refine Finset.sum_congr rfl fun ε _ => ?_
    simp only [Equiv.coe_mulLeft]
    rw [smul_smul]
    congr 1
    have hu : (D.ω ε)⁻¹ = D.ω δ * (D.ω (δ * ε))⁻¹ := by
      rw [map_mul, mul_inv, mul_inv_cancel_left]
    rw [hu, Units.val_mul]
  rw [key]
  exact smul_comm _ _ _

theorem uniformiser_pow_card_subst (g : PowerSeries O) :
    PowerSeries.subst (pi1 D hs) (PowerSeries.subst (X ^ Fintype.card Δ : PowerSeries O) g) =
      PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) g := by
  have hp := HasSubst.of_constantCoeff_zero' (constantCoeff_eigen_uniformiser D hs)
  rw [subst_comp_subst_apply (HasSubst.X_pow (card_ne_zero (Δ := Δ))) hp, subst_pow hp,
    subst_X hp]

theorem rho_subst_uniformiser (δ : Δ) (g : PowerSeries O) :
    D.ρ δ (PowerSeries.subst (pi1 D hs) g) =
      PowerSeries.subst (pi1 D hs) (rescale (D.ω δ : O) g) := by
  have hp := HasSubst.of_constantCoeff_zero' (constantCoeff_eigen_uniformiser D hs)
  rw [rho_subst D δ (constantCoeff_eigen_uniformiser D hs), rho_eigen_uniformiser, rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' _) hp, subst_smul hp, subst_X hp]

theorem invariant_subst_iff_card_dvd (g : PowerSeries O) :
    (∀ δ, D.ρ δ (PowerSeries.subst (pi1 D hs) g) = PowerSeries.subst (pi1 D hs) g) ↔
      ∀ k, coeff k g ≠ 0 → Fintype.card Δ ∣ k := by
  constructor
  · intro H k hk
    obtain ⟨δ₀, hδ₀⟩ := IsCyclic.exists_generator (α := Δ)
    have h := H δ₀
    rw [rho_subst_uniformiser] at h
    have h2 := congrArg (coeff k)
      (subst_injective (constantCoeff_eigen_uniformiser D hs) (isUnit_coeff_one_eigen_uniformiser D hs) h)
    rw [coeff_rescale] at h2
    have h3 : (((D.ω δ₀ : Oˣ) : O) ^ k - 1) * coeff k g = 0 := by
      rw [sub_mul, h2, one_mul, sub_self]
    have h4 : ((D.ω δ₀ : Oˣ) : O) ^ k = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hk)
    have h5 : δ₀ ^ k = 1 := by
      apply D.hω
      rw [map_pow, map_one]
      ext
      rw [Units.val_pow_eq_pow_val, h4, Units.val_one]
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [orderOf_eq_card_of_forall_mem_zpowers hδ₀] at h6
    simpa [Nat.card_eq_fintype_card] using h6
  · intro H δ
    rw [rho_subst_uniformiser]
    congr 1
    ext k
    rw [coeff_rescale]
    by_cases hk : coeff k g = 0
    · rw [hk, mul_zero]
    · obtain ⟨t, rfl⟩ := H k hk
      rw [pow_mul, omega_pow_card, one_pow, one_mul]

end Lemmas

theorem piPrime_eq (D : Data O Δ) :
    ∃ v' : PowerSeries O, IsUnit v' ∧ piPrime D = X ^ Fintype.card Δ * v' ∧
      constantCoeff v' = ∏ δ, (D.ω δ : O) := by
  refine ⟨∏ δ, D.v δ, ?_, ?_, ?_⟩
  · rw [isUnit_iff_constantCoeff, map_prod]
    simp_rw [D.hv0]
    rw [← Units.coe_prod]
    exact Units.isUnit _
  · unfold piPrime
    simp_rw [D.hv]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  · rw [map_prod]
    simp_rw [D.hv0]


theorem invariants (D : Data O Δ) (hs : IsUnit (Fintype.card Δ : O)) :
    (∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) ↔
        ∃ g : PowerSeries O, f = PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) g) ∧
    (∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) ↔
        ∃ g : PowerSeries O, f = PowerSeries.subst (piPrime D) g) ∧
    (∀ f : PowerSeries O, ∃! a : Fin (Fintype.card Δ) → PowerSeries O,
        f = ∑ j : Fin (Fintype.card Δ), pi1 D hs ^ (j : ℕ) * PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) (a j)) ∧
    (∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) → constantCoeff f = 0 →
        ∃ g : PowerSeries O, (∀ δ, D.ρ δ g = g) ∧ f = piPrime D * g) := by
  have hs0 : Fintype.card Δ ≠ 0 := card_ne_zero
  have hp0 := constantCoeff_eigen_uniformiser D hs
  have hp1 := isUnit_coeff_one_eigen_uniformiser D hs
  have hps0 : constantCoeff (pi1 D hs ^ Fintype.card Δ) = 0 := by
    rw [map_pow, hp0, zero_pow hs0]
  have hps := HasSubst.of_constantCoeff_zero' hps0
  have part1 : ∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) ↔
      ∃ g : PowerSeries O, f = PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) g := by
    intro f
    obtain ⟨g, rfl⟩ := subst_surjective hp0 hp1 f
    rw [invariant_subst_iff_card_dvd D hs g]
    constructor
    · intro H
      exact ⟨_, by rw [← uniformiser_pow_card_subst D hs, ← subst_X_pow_of_dvd hs0 g H]⟩
    · rintro ⟨h, hh⟩ k hk
      rw [← uniformiser_pow_card_subst D hs] at hh
      rw [subst_injective hp0 hp1 hh] at hk
      exact dvd_of_coeff_subst_X_pow_ne_zero hs0 h k hk
  have hpp0 : constantCoeff (piPrime D) = 0 := by
    obtain ⟨v', -, hv', -⟩ := piPrime_eq D
    rw [hv', map_mul, map_pow, constantCoeff_X, zero_pow hs0, zero_mul]
  obtain ⟨P0, hP0⟩ := (part1 (piPrime D)).mp (piPrime_invariant D)
  have hP0c : constantCoeff P0 = 0 := by
    have e := congrArg constantCoeff hP0
    rw [subst_eq_C_add hps0, map_add, map_mul, hps0, zero_mul, add_zero, constantCoeff_C,
      hpp0] at e
    exact e.symm
  have hP0u : IsUnit (coeff 1 P0) := by
    obtain ⟨v', -, hv', hv'0⟩ := piPrime_eq D
    obtain ⟨w, hw⟩ : X ∣ pi1 D hs := X_dvd_iff.mpr hp0
    have hw0 : constantCoeff w = 1 := by
      have e := coeff_one_eigen_uniformiser D hs
      rwa [hw, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
        coeff_zero_eq_constantCoeff_apply] at e
    have e := hP0
    rw [subst_eq_C_add hps0, hP0c, map_zero, zero_add, subst_eq_C_add hps0, hv', hw] at e
    have e2 := congrArg (coeff (Fintype.card Δ)) e
    rw [mul_pow, mul_assoc (X ^ Fintype.card Δ)] at e2
    simp only [coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_add, map_pow, hv'0, hw0, constantCoeff_X,
      zero_pow hs0, one_pow, one_mul, zero_mul, add_zero, constantCoeff_C] at e2
    have e3 : constantCoeff (mk fun n => coeff (n + 1) P0) = coeff 1 P0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    rw [← e3, ← e2, ← Units.coe_prod]
    exact Units.isUnit _
  have hP0s : HasSubst P0 := HasSubst.of_constantCoeff_zero' hP0c
  have part2 : ∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) ↔
      ∃ g : PowerSeries O, f = PowerSeries.subst (piPrime D) g := by
    intro f
    rw [part1 f]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨PowerSeries.subst (substInvOfIsUnit P0 hP0u) g, ?_⟩
      rw [hP0, ← subst_comp_subst_apply hP0s hps, subst_subst_substInv hP0c hP0u]
    · rintro ⟨g, rfl⟩
      exact ⟨PowerSeries.subst P0 g, by rw [hP0, subst_comp_subst_apply hP0s hps]⟩
  have part3 : ∀ f : PowerSeries O, ∃! a : Fin (Fintype.card Δ) → PowerSeries O,
      f = ∑ j : Fin (Fintype.card Δ),
        pi1 D hs ^ (j : ℕ) * PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) (a j) := by
    intro f
    have hp := HasSubst.of_constantCoeff_zero' hp0
    have hE : ∀ a : Fin (Fintype.card Δ) → PowerSeries O,
        ∑ j : Fin (Fintype.card Δ),
          pi1 D hs ^ (j : ℕ) * PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) (a j) =
        PowerSeries.subst (pi1 D hs) (∑ j : Fin (Fintype.card Δ),
          X ^ (j : ℕ) * PowerSeries.subst (X ^ Fintype.card Δ : PowerSeries O) (a j)) := by
      intro a
      rw [← coe_substAlgHom hp, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, coe_substAlgHom, subst_X hp, uniformiser_pow_card_subst]
    obtain ⟨g, rfl⟩ := subst_surjective hp0 hp1 f
    obtain ⟨a, ha, hu⟩ := existsUnique_sum_X_pow_mul_subst hs0 g
    refine ⟨a, ?_, fun b hb => hu b ?_⟩
    · dsimp only
      rw [hE, ← ha]
    · dsimp only at hb ⊢
      rw [hE] at hb
      exact subst_injective hp0 hp1 hb
  have part4 : ∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) → constantCoeff f = 0 →
      ∃ g : PowerSeries O, (∀ δ, D.ρ δ g = g) ∧ f = piPrime D * g := by
    intro f hf hf0
    obtain ⟨h, rfl⟩ := (part2 f).mp hf
    refine ⟨PowerSeries.subst (piPrime D) (mk fun n => coeff (n + 1) h), (part2 _).mpr ⟨_, rfl⟩,
      ?_⟩
    have e := subst_eq_C_add hpp0 h
    have e0 := congrArg constantCoeff e
    rw [hf0, map_add, map_mul, hpp0, zero_mul, add_zero, constantCoeff_C] at e0
    rw [e, ← e0, map_zero, zero_add]
  exact ⟨part1, part2, part3, part4⟩

end DualFramesAlt.EigenUniformiser
end

section
namespace DualFramesAlt.eigenRingInvariants

open PowerSeries

noncomputable abbrev Ia {O : Type*} [CommRing O] (a : O) : Ideal (PowerSeries O) := Ideal.span {X - C a}

theorem mk_X {O : Type*} [CommRing O] (a : O) : Ideal.Quotient.mk (Ia a) X = Ideal.Quotient.mk (Ia a) (C a) :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)

section Ev

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem map_residue_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    (X - C a : PowerSeries O).map (IsLocalRing.residue O) = X := by
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, sub_zero]

theorem order_map_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    ((X - C a : PowerSeries O).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat = 1 := by
  change ((X - C a : PowerSeries O).map (IsLocalRing.residue O)).order.toNat = 1
  rw [map_residue_X_sub_C ha, PowerSeries.order_X]
  rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem ev_exists {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O) :
    ∃ c : O, Ideal.Quotient.mk (Ia a) f = Ideal.Quotient.mk (Ia a) (C c) := by
  have hg : (X - C a : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [map_residue_X_sub_C ha]
    exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hW⟩ := f.exists_isWeierstrassDivision hg
  obtain ⟨hdeg, heq⟩ := hW
  rw [order_map_X_sub_C ha] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hdeg))
  refine ⟨r.coeff 0, ?_⟩
  rw [heq, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)),
    zero_add]
  congr 1
  conv_lhs => rw [hr]
  exact Polynomial.coe_C _

theorem ev_inj {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c c' : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = Ideal.Quotient.mk (Ia a) (C c')) : c = c' := by
  rw [Ideal.Quotient.eq, ← map_sub] at h
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp h
  have hrec : ∀ n, PowerSeries.coeff (R := O) n H = a * PowerSeries.coeff (R := O) (n + 1) H := by
    intro n
    have hn := congrArg (PowerSeries.coeff (R := O) (n + 1)) hH
    rw [PowerSeries.coeff_C, if_neg (by omega : n + 1 ≠ 0), sub_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul] at hn
    linear_combination -hn
  have hmem : ∀ n, PowerSeries.coeff (R := O) 0 H ∈ (IsLocalRing.maximalIdeal O) ^ n := by
    intro n
    have hpow : PowerSeries.coeff (R := O) 0 H = a ^ n * PowerSeries.coeff (R := O) n H := by
      induction n with
      | zero => simp
      | succ n ih => rw [ih, hrec n, pow_succ]; ring
    rw [hpow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha n)
  have h0 : PowerSeries.coeff (R := O) 0 H = 0 := by
    apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal O)
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hmem n
  have hc := congrArg (PowerSeries.coeff (R := O) 0) hH
  rw [PowerSeries.coeff_zero_C, sub_mul, map_sub, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul, h0,
    mul_zero, sub_zero] at hc
  exact sub_eq_zero.mp hc

theorem ev_zero {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = 0) : c = 0 := by
  exact ev_inj ha (by rw [h, map_zero, map_zero])

end Ev

theorem ev_subst {O : Type*} [CommRing O] {P : PowerSeries O} (hP : constantCoeff P = 0) {a b c : O}
    {F : PowerSeries O}
    (hPb : Ideal.Quotient.mk (Ideal.span {X - C a}) P = Ideal.Quotient.mk (Ideal.span {X - C a}) (C b))
    (hF : Ideal.Quotient.mk (Ideal.span {X - C b}) F = Ideal.Quotient.mk (Ideal.span {X - C b}) (C c)) :
    Ideal.Quotient.mk (Ideal.span {X - C a}) (PowerSeries.subst P F) =
      Ideal.Quotient.mk (Ideal.span {X - C a}) (C c) := by
  have hs : HasSubst P := HasSubst.of_constantCoeff_zero' hP
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton'] at hF
  obtain ⟨k, hk⟩ := hF
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hPb ⊢
  have e : PowerSeries.subst P F - C c = PowerSeries.subst P k * (P - C b) := by
    have := congrArg (PowerSeries.subst P) hk
    rw [subst_mul hs, subst_sub hs, subst_sub hs, subst_X hs, subst_C, subst_C] at this
    exact this.symm
  rw [e]; exact Ideal.mul_mem_left _ _ hPb

section Dvd

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]


theorem prod_dvd (T : Finset O) (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O)
    (hf : ∀ t ∈ T, Ideal.Quotient.mk (Ia t) f = 0) : (∏ t ∈ T, (X - C t)) ∣ f := by
  classical
  induction T using Finset.induction_on generalizing f with
  | empty => simp
  | @insert t0 T ht0 ih =>
    rw [Finset.prod_insert ht0]
    have h0 : (X - C t0) ∣ f :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hf t0 (Finset.mem_insert_self _ _)))
    obtain ⟨g, rfl⟩ := h0
    apply mul_dvd_mul_left
    apply ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
    intro t ht
    have htm := hT t (Finset.mem_insert_of_mem ht)
    obtain ⟨c, hc⟩ := ev_exists htm g
    have hft := hf t (Finset.mem_insert_of_mem ht)
    have key : Ideal.Quotient.mk (Ia t) (C ((t - t0) * c)) = 0 := by
      rw [← hft]
      simp only [map_mul, map_sub, mk_X, hc]
    have hz := ev_zero htm key
    have hne : t - t0 ≠ 0 := sub_ne_zero.mpr (fun h => ht0 (h ▸ ht))
    have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_left hne
    rw [hc, hc0, map_zero, map_zero]

end Dvd

section Order

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem card_le_of_dvd {f v k : PowerSeries O} {s : ℕ} (T : Finset O)
    (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (hv : IsUnit v)
    (hf : f.map (IsLocalRing.residue O) = (X ^ s * v).map (IsLocalRing.residue O))
    (hk : f = (∏ t ∈ T, (X - C t)) * k) :
    T.card ≤ s ∧ (T.card = s → IsUnit k) := by
  set κ := IsLocalRing.ResidueField O
  have hprod : (∏ t ∈ T, (X - C t) : PowerSeries O).map (IsLocalRing.residue O) = X ^ T.card := by
    rw [map_prod]
    rw [Finset.prod_congr rfl fun t ht => (map_residue_X_sub_C (hT t ht))]
    rw [Finset.prod_const]
  have e : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
      X ^ T.card * k.map (IsLocalRing.residue O) := by
    rw [← map_X (IsLocalRing.residue O), ← map_pow, ← map_mul, ← hf, hk, map_mul, hprod, map_X]
  have hv' : constantCoeff (v.map (IsLocalRing.residue O)) ≠ 0 := by
    have := (hv.map (PowerSeries.map (IsLocalRing.residue O)))
    rw [isUnit_iff_constantCoeff] at this
    exact this.ne_zero
  have hX : (X : PowerSeries κ) ≠ 0 := X_ne_zero
  by_cases hle : T.card ≤ s
  · refine ⟨hle, fun hcs => ?_⟩
    rw [hcs] at e
    have e2 := mul_left_cancel₀ (pow_ne_zero _ hX) e
    rw [isUnit_iff_constantCoeff]
    by_contra hnu
    apply hv'
    rw [e2, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)]
  · exfalso
    replace hle := not_le.mp hle
    have e2 : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
        X ^ s * (X ^ (T.card - s) * k.map (IsLocalRing.residue O)) := by
      rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle.le]
    have e3 := mul_left_cancel₀ (pow_ne_zero _ hX) e2
    apply hv'
    rw [e3, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul]

end Order

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums

variable {l : ℕ} [hl : Fact l.Prime]



section O

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O] {a ζ : O}

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)








end O

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_of_toZMod_ne_zero {x : ℤ_[l]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr hx)
  rw [← PadicInt.ker_toZMod] at hm
  exact RingHom.mem_ker.mp hm

theorem natCast_ne_zero_zmod {n : ℕ} (h0 : 0 < n) (hn : n < l) : (n : ZMod l) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt h0 hn ((CharP.cast_eq_zero_iff (ZMod l) l n).mp h)

theorem toZMod_ne_zero_of_pow {s : ℕ} (hs : 0 < s) {ω : ℤ_[l]} (hω : ω ^ s = 1) :
    PadicInt.toZMod ω ≠ 0 := by
  intro h
  have h1 := congrArg PadicInt.toZMod hω
  rw [map_pow, h, zero_pow hs.ne', map_one] at h1
  exact zero_ne_one h1

theorem val_pos_of_pow {s : ℕ} (hs : 0 < s) {ω : ℤ_[l]} (hω : ω ^ s = 1) :
    0 < (PadicInt.toZMod ω).val := by
  exact ZMod.val_pos.mpr (toZMod_ne_zero_of_pow hs hω)

theorem val_lt (ω : ℤ_[l]) : (PadicInt.toZMod ω).val < l := ZMod.val_lt _


theorem sub_one_mem {O : Type*} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {ζ : O}
    (hζ : IsPrimitiveRoot ζ l) (hmax : (algebraMap ℤ_[l] O) l ∈ IsLocalRing.maximalIdeal O) :
    ζ - 1 ∈ IsLocalRing.maximalIdeal O := by
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), ← map_natCast (algebraMap ℤ_[l] O)]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  have : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl.out).mpr hl0
  have h2 : (IsLocalRing.residue O (ζ - 1)) ^ l = 0 := by
    rw [map_sub, map_one, sub_pow_char, ← map_pow, hζ.pow_eq_one, map_one, one_pow, sub_self]
  exact (IsLocalRing.residue_eq_zero_iff _).mp ((pow_eq_zero_iff hl.out.ne_zero).mp h2)

noncomputable instance instFintypeRoots (s : ℕ) [NeZero s] : Fintype (rootsOfUnity s ℤ_[l]) := Fintype.ofFinite _

theorem prod_roots {M : Type*} [CommMonoid M] (s : ℕ) [NeZero s] (hs : 0 < s) (f : ℤ_[l] → M) :
    ∏ δ : rootsOfUnity s ℤ_[l], f ((δ : ℤ_[l]ˣ) : ℤ_[l]) =
      ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), f ω := by
  rw [← Finset.prod_image (f := f) (s := Finset.univ)
    (g := fun δ : rootsOfUnity s ℤ_[l] => ((δ : ℤ_[l]ˣ) : ℤ_[l]))
    (by intro δ _ ε _ h; exact Subtype.ext (Units.ext h))]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Polynomial.mem_nthRootsFinset hs]
  constructor
  · rintro ⟨δ, rfl⟩
    have h1 := δ.2
    rw [mem_rootsOfUnity] at h1
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · intro hx
    have hu : IsUnit x := IsUnit.of_pow_eq_one hx hs.ne'
    refine ⟨⟨hu.unit, ?_⟩, rfl⟩
    rw [mem_rootsOfUnity]; apply Units.ext; simp [hx]

section Act

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O]

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)

theorem toO_const_zero {a : PowerSeries ℤ_[l]} (ha : constantCoeff a = 0) : constantCoeff (toO a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, ha, map_zero]

theorem toO_brk_const (a : ℤ_[l]) : constantCoeff (toO (brk l a)) = 0 :=
  toO_const_zero (by rw [(Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).1, map_mul, constantCoeff_X, zero_mul])

theorem hasSubst_brk (a : ℤ_[l]) : HasSubst (toO (brk l a)) :=
  HasSubst.of_constantCoeff_zero (toO_brk_const a)

theorem toO_subst {a : PowerSeries ℤ_[l]} (ha : constantCoeff a = 0) (f : PowerSeries ℤ_[l]) :
    toO (subst a f) = subst (toO a) (toO f) :=
  map_subst (HasSubst.of_constantCoeff_zero' ha) f

theorem subst_brk_brk (a b : ℤ_[l]) (f : PowerSeries O) :
    subst (toO (brk l b)) (subst (toO (brk l a)) f) = subst (toO (brk l (a * b))) f := by
  rw [subst_comp_subst_apply (hasSubst_brk a) (hasSubst_brk b),
    ← toO_subst (ConcreteDictionaryLemmas.brk_const b), ConcreteDictionaryLemmas.brk_comp]

theorem brk_one : brk l (1 : ℤ_[l]) = X := by
  unfold brk
  rw [← Nat.cast_one, PowerSeries.binomialSeries_nat, pow_one, add_sub_cancel_left]

theorem subst_brk_one (f : PowerSeries O) : subst (toO (brk l 1)) f = f := by
  rw [brk_one, map_X, X_subst]

noncomputable def rhoE (δ : ℤ_[l]ˣ) : PowerSeries O ≃ₐ[O] PowerSeries O :=
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_brk (O := O) (δ : ℤ_[l])))
    (substAlgHom (hasSubst_brk (O := O) ((δ⁻¹ : ℤ_[l]ˣ) : ℤ_[l])))
    (AlgHom.ext fun f => by
      simp only [AlgHom.comp_apply, coe_substAlgHom, AlgHom.id_apply]
      rw [subst_brk_brk, ← Units.val_mul, inv_mul_cancel, Units.val_one, subst_brk_one])
    (AlgHom.ext fun f => by
      simp only [AlgHom.comp_apply, coe_substAlgHom, AlgHom.id_apply]
      rw [subst_brk_brk, ← Units.val_mul, mul_inv_cancel, Units.val_one, subst_brk_one])

theorem rhoE_apply (δ : ℤ_[l]ˣ) (f : PowerSeries O) : rhoE δ f = subst (toO (brk l δ)) f := by
  exact congrFun (coe_substAlgHom (hasSubst_brk (O := O) (δ : ℤ_[l]))) f

noncomputable def rhoHom (s : ℕ) : rootsOfUnity s ℤ_[l] →* (PowerSeries O ≃ₐ[O] PowerSeries O) where
  toFun δ := rhoE (δ : ℤ_[l]ˣ)
  map_one' := AlgEquiv.ext fun f => by
    rw [rhoE_apply]; simp only [OneMemClass.coe_one, Units.val_one, subst_brk_one, AlgEquiv.one_apply]
  map_mul' δ ε := AlgEquiv.ext fun f => by
    simp only [AlgEquiv.mul_apply, rhoE_apply, subst_brk_brk]
    congr 3
    simp only [MulMemClass.coe_mul, Units.val_mul]
    ring

theorem rhoHom_apply (s : ℕ) (δ : rootsOfUnity s ℤ_[l]) (f : PowerSeries O) :
    rhoHom s δ f = subst (toO (brk l ((δ : ℤ_[l]ˣ) : ℤ_[l]))) f :=
  rhoE_apply _ f

noncomputable def vS (a : ℤ_[l]) : PowerSeries ℤ_[l] := Classical.choose (ConcreteDictionaryLemmas.brk_factor a)

theorem brk_eq_X_mul (a : ℤ_[l]) : brk l a = X * vS a :=
  (Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).1

theorem vS_const (a : ℤ_[l]) : constantCoeff (vS a) = a :=
  (Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).2

variable [IsDomain O]

noncomputable def dataS (s : ℕ) [NeZero s] (hinj : Function.Injective (algebraMap ℤ_[l] O)) :
    EigenUniformiser.Data O (rootsOfUnity s ℤ_[l]) where
  ρ := rhoHom s
  ω := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (rootsOfUnity s ℤ_[l]).subtype
  hω := by
    intro δ ε h
    apply Subtype.ext; apply Units.ext
    have h2 := congrArg Units.val h
    exact hinj h2
  v δ := toO (vS ((δ : ℤ_[l]ˣ) : ℤ_[l]))
  hv δ := by
    show rhoHom s δ X = _
    rw [rhoHom_apply, subst_X (hasSubst_brk _), brk_eq_X_mul, map_mul, map_X]
  hv0 δ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, vS_const]
    rfl


end Act

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]




section Fiber

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[l] O]

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)

noncomputable def vp (l s : ℕ) [Fact l.Prime] (ζ : O) : O :=
  ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), (ζ ^ (PadicInt.toZMod ω).val - 1)

noncomputable def PRt (l : ℕ) (O : Type*) [CommRing O] [IsDomain O] : Finset O :=
  (Polynomial.nthRoots l (1 : O)).toFinset.filter fun z => IsPrimitiveRoot z l


theorem coprime_val {s : ℕ} (hs : 0 < s) {δ : ℤ_[l]} (hδ : δ ^ s = 1) :
    (PadicInt.toZMod δ).val.Coprime l :=
  ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr
    (Nat.not_dvd_of_pos_of_lt (val_pos_of_pow hs hδ) (val_lt δ))).symm

theorem pow_eq_pow_val {ζ : O} (hζ : IsPrimitiveRoot ζ l) (n : ℕ) :
    ζ ^ n = ζ ^ ((n : ZMod l).val) := by
  conv_lhs => rw [← Nat.mod_add_div n l]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one, ZMod.val_natCast]

theorem vp_pow {s : ℕ} (hs : 0 < s) {ζ : O} (hζ : IsPrimitiveRoot ζ l) {δ : ℤ_[l]} (hδ : δ ^ s = 1) :
    vp l s (ζ ^ (PadicInt.toZMod δ).val) = vp l s ζ := by
  have : NeZero l := ⟨hl.out.ne_zero⟩
  unfold vp
  have key : ∀ ω : ℤ_[l], (ζ ^ (PadicInt.toZMod δ).val) ^ (PadicInt.toZMod ω).val =
      ζ ^ (PadicInt.toZMod (δ * ω)).val := by
    intro ω
    rw [← pow_mul, pow_eq_pow_val hζ, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      map_mul]
  simp_rw [key]
  have hμ : ∀ ω, ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]) ↔ ω ^ s = 1 := fun ω =>
    Polynomial.mem_nthRootsFinset hs 1
  have h02 : δ * δ ^ (s - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hs, hδ]
  refine Finset.prod_nbij' (fun ω => δ * ω) (fun ω => δ ^ (s - 1) * ω) ?_ ?_ ?_ ?_ ?_
  · intro ω hω; rw [hμ] at hω ⊢; rw [mul_pow, hω, hδ, one_mul]
  · intro ω hω
    rw [hμ] at hω ⊢
    rw [mul_pow, hω, ← pow_mul, mul_comm (s - 1) s, pow_mul, hδ, one_pow, one_mul]
  · intro ω _; rw [← mul_assoc, mul_comm (δ ^ (s - 1)) δ, h02, one_mul]
  · intro ω _; rw [← mul_assoc, h02, one_mul]
  · intro ω _; rfl




noncomputable def Tp (l s : ℕ) [Fact l.Prime] (ζ : O) : Finset O :=
  (Polynomial.nthRootsFinset s (1 : ℤ_[l])).image fun δ => ζ ^ (PadicInt.toZMod δ).val - 1




variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]




end Fiber

end DualFramesAlt.eigenRingInvariants
end

section
namespace DualFramesAlt.BlockProductRing

open PowerSeries

theorem prod_div_block {M : Type*} [CommMonoid M] (m : ℕ) (hm : 0 < m) (g : ℕ → M) (e : ℕ) :
    ∏ k ∈ Finset.range (m * e), g (k / m) = ∏ j ∈ Finset.range e, g j ^ m := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [mul_add_one, Finset.prod_range_add, ih, Finset.prod_range_succ]
    congr 1
    have hc : ∀ x ∈ Finset.range m, g ((m * e + x) / m) = g e := by
      intro x hx
      rw [Finset.mem_range] at hx
      congr 1
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hx, zero_add]
    rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_range]

theorem prod_ite_block {M : Type*} [CommMonoid M] (m : ℕ) (hm : 0 < m) (x : M) (k : ℕ) :
    ∏ i ∈ Finset.range k, (if i / m = k / m then x else 1) = x ^ (k % m) := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have hset : Finset.filter (fun i => i / m = k / m) (Finset.range k) = Finset.Ico (m * (k / m)) k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hik, hd⟩
      refine ⟨?_, hik⟩
      rw [← hd]
      exact Nat.mul_div_le i m
    · rintro ⟨hle, hik⟩
      refine ⟨hik, le_antisymm (Nat.div_le_div_right hik.le) ?_⟩
      rw [Nat.le_div_iff_mul_le hm, mul_comm]
      exact hle
  rw [hset, Nat.card_Ico]
  have h := Nat.mod_add_div k m
  generalize m * (k / m) = q at h ⊢
  generalize k % m = r at h ⊢
  omega

theorem dvd_of_mk_eq {O : Type*} [CommRing O] {y c : O} {F : PowerSeries O}
    (h : Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) F = Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) (C c)) :
    ∃ H, F - C c = (X - C y) * H := by
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  exact ⟨H, hH⟩

theorem mk_eq_of_mem {O : Type*} [CommRing O] {y : O} {F G : PowerSeries O} (h : F - G ∈ DualFramesAlt.eigenRingInvariants.Ia y) :
    Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) F = Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) G :=
  Ideal.Quotient.eq.mpr h

theorem mem_of_factor {O : Type*} [CommRing O] (y : O) (F : PowerSeries O) :
    (X - C y) * F ∈ DualFramesAlt.eigenRingInvariants.Ia y :=
  Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

end DualFramesAlt.BlockProductRing
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section unitaryAbsoluteValueBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u2ringPfB_γ₀_comm (g h : W.Gam) (x : PowerSeries O) :
    W.γ₀ g (W.γ₀ h x) = W.γ₀ h (W.γ₀ g x) := by
  rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]

theorem u2ringPfB_single_mem (c : ZMod n) (x : PowerSeries O) (hx : ∀ δ ∈ W.DelF, W.γ₀ δ x = x) :
    (Pi.single c x : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (Pi.single c x : LetA O n) = Pi.single c x
  intro δ hδ
  funext j
  show W.γ₀ δ ((Pi.single c x : LetA O n) j) = (Pi.single c x : LetA O n) j
  by_cases hj : j = c
  · subst hj
    simp only [Pi.single_eq_same]
    exact hx δ hδ
  · simp only [Pi.single_eq_of_ne hj, map_zero]

theorem u2ringPfB_letter_mem {a : LetA O n} (ha : a ∈ W.AΔ) (i : ZMod n) :
    ∀ δ ∈ W.DelF, W.γ₀ δ (a i) = a i := by
  intro δ hδ
  have h : W.γA δ a = a := ha δ hδ
  exact congrFun h i

theorem u2ringPfB_q₀_ne_zero [IsDomain O] [CharZero O] (hp : PD.p ≠ 0) : W.q₀ ≠ 0 := by
  intro h0
  have h := W.q₀_def
  rw [h0, mul_zero] at h
  have h1 := congrArg (PowerSeries.coeff 1) h.symm
  have e : ((1 + PowerSeries.X : PowerSeries O) ^ PD.p - 1) =
      ((((Polynomial.X + 1) ^ PD.p - 1 : Polynomial O)) : PowerSeries O) := by
    push_cast
    ring
  rw [e, Polynomial.coeff_coe, map_zero] at h1
  simp [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one, hp] at h1

end unitaryAbsoluteValueBounds

end Formalism.MainNotions.N.Ln34
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2C

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem constantCoeff_uniformiser_zero {s' : ℕ} {π' : LetA O n} (w : (LetA O n)ˣ) (hw : π' = (w : LetA O n) * letπ ^ s')
    (hs : 1 ≤ s') (i : ZMod n) : PowerSeries.constantCoeff (π' i) = 0 := by
  have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]

theorem u2ringPfC_subΔ {π' : LetA O n} (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0) :
    ∀ δ ∈ W.DelF, ∀ i (F : PowerSeries O),
      W.γ₀ δ (PowerSeries.subst (π' i) F) = PowerSeries.subst (π' i) F := by
  intro δ hδ i F
  rw [DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ δ) (W.γ₀_X δ).1 (hπ0 i)]
  congr 1
  exact congrFun (hπΔ δ hδ) i

theorem u2ringPfC_inj {π' : LetA O n} (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hsub : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O,
      ∀ i, a i = PowerSeries.subst (π' i) (f i))
    (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0) (c : ZMod n) (F F' : PowerSeries O)
    (hFF : PowerSeries.subst (π' c) F = PowerSeries.subst (π' c) F') : F = F' := by
  have hsub0 : ∀ i, PowerSeries.subst (π' i) (0 : PowerSeries O) = 0 := fun i => by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)), map_zero]
  have hmem := u2ringPfB_single_mem W c (PowerSeries.subst (π' c) F)
    (fun δ hδ => u2ringPfC_subΔ W hπΔ hπ0 δ hδ c F)
  obtain ⟨f, -, huniq⟩ := hsub _ hmem
  have key : ∀ H, PowerSeries.subst (π' c) H = PowerSeries.subst (π' c) F →
      (Pi.single c H : ZMod n → PowerSeries O) = f := fun H hH => huniq _ (fun i => by
    by_cases hi : i = c
    · subst hi; simp only [Pi.single_eq_same]; exact hH.symm
    · simp only [Pi.single_eq_of_ne hi, hsub0])
  have := congrFun ((key F rfl).trans (key F' hFF.symm).symm) c
  simpa using this

theorem u2ringPfC_pre {π' : LetA O n}
    (hsub : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O,
      ∀ i, a i = PowerSeries.subst (π' i) (f i)) (c : ZMod n) (x : PowerSeries O)
    (hx : ∀ δ ∈ W.DelF, W.γ₀ δ x = x) : ∃ F : PowerSeries O, PowerSeries.subst (π' c) F = x := by
  obtain ⟨f, hf, -⟩ := hsub _ (u2ringPfB_single_mem W c x hx)
  refine ⟨f c, ?_⟩
  have := hf c
  simp only [Pi.single_eq_same] at this
  exact this.symm

theorem u2ringPfC_nu [IsDomain O] [CharZero O] {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hK : W.gamK = W.gam) (h' : ℕ) :
    ∃ ν : LetA O n, ν ∈ W.AΔ ∧
      ν * W.γA W.gamK (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
  obtain ⟨hπΔ, -, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, ⟨w₂, hγ⟩, -⟩ := hR
  have hπ0 := constantCoeff_uniformiser_zero w hw hs
  set Ê := Formalism.MainNotions.DeltaInvariantLattices.Eat E π' with hÊdef
  have hq₀ := u2ringPfB_q₀_ne_zero W PD.hp.ne_zero
  have hÊ0 : ∀ i, Ê i ≠ 0 := by
    intro i h
    apply hq₀
    have e1 : W.q₀ = (w₁ : LetA O n) i * Ê i := congrFun hq i
    rw [e1, h, mul_zero]
  have hπΔ' : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (π' i) = π' i := fun δ hδ i => congrFun (hπΔ δ hδ) i
  have hÊΔ : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (Ê i) = Ê i := by
    intro δ hδ i
    show W.γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply, hπΔ' δ hδ i]
  have hU : ∀ i, ∃ u : PowerSeries O, IsUnit u ∧ W.γ₀ W.gam (Ê i) = Ê i * u := by
    intro i
    have hγi : W.γ₀ W.gam (π' i) - π' i = (w₂ : LetA O n) i * π' i * Ê i := congrFun hγ i
    obtain ⟨D, hD⟩ := Polynomial.sub_dvd_eval_sub (W.γ₀ W.gam (π' i)) (π' i)
      ((E i).map (algebraMap O (PowerSeries O)))
    refine ⟨1 + (w₂ : LetA O n) i * π' i * D, ?_, ?_⟩
    · rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [hπ0 i]
    · have e2 : W.γ₀ W.gam (Ê i) = Polynomial.aeval (W.γ₀ W.gam (π' i)) (E i) :=
        (Polynomial.aeval_algHom_apply (W.γ₀ W.gam) (π' i) (E i)).symm
      have e3 : Ê i = Polynomial.aeval (π' i) (E i) := rfl
      have hD' : Polynomial.aeval (W.γ₀ W.gam (π' i)) (E i) - Polynomial.aeval (π' i) (E i) =
          (W.γ₀ W.gam (π' i) - π' i) * D := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          Polynomial.eval₂_eq_eval_map]
        exact hD
      rw [e3] at hγi
      rw [hγi] at hD'
      rw [e2, e3]
      linear_combination hD'
  choose U hUu hUeq using hU
  have hUunit : IsUnit (U : LetA O n) := Pi.isUnit_iff.2 hUu
  set V : LetA O n := ((hUunit.unit⁻¹ : (LetA O n)ˣ) : LetA O n) with hV
  have hVU : V * U = 1 := by rw [hV]; exact hUunit.val_inv_mul
  have hUΔ : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (U i) = U i := by
    intro δ hδ i
    have h1 := congrArg (W.γ₀ δ) (hUeq i)
    rw [u2ringPfB_γ₀_comm, map_mul, hÊΔ δ hδ i, hUeq i] at h1
    exact (mul_left_cancel₀ (hÊ0 i) h1).symm
  refine ⟨V ^ h', ?_, ?_⟩
  · intro δ hδ
    funext i
    show W.γ₀ δ ((V ^ h') i) = (V ^ h') i
    rw [Pi.pow_apply, map_pow]
    congr 1
    have hVi : V i * U i = 1 := congrFun hVU i
    have h1 := congrArg (W.γ₀ δ) hVi
    rw [map_mul, hUΔ δ hδ i, map_one] at h1
    exact mul_right_cancel₀ (hUu i).ne_zero (h1.trans hVi.symm)
  · have hγÊ : W.γA W.gam Ê = Ê * U := funext fun i => hUeq i
    rw [hK, map_pow, hγÊ]
    calc V ^ h' * (Ê * U) ^ h' = (V * U) ^ h' * Ê ^ h' := by ring
      _ = Ê ^ h' := by rw [hVU, one_pow, one_mul]

end U2C

end Formalism.MainNotions.N.Ln34
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2D

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

theorem u2ringPfD_main [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hK : W.gamK = W.gam)
    (he : e ≤ finrank K₀ K) (c : ZMod n) (a : O) (ha : IsUnit a) (r : Fin e → O)
    (hrm : ∀ j, r j ∈ IsLocalRing.maximalIdeal O)
    (hE : E c = Polynomial.C a * ∏ j, (Polynomial.X - Polynomial.C (r j)))
    (hnr : ∀ (j : Fin e) (w₀ : O), IsUnit w₀ → ∀ t : ℕ, 0 < t →
      (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) ^ t ≠ 1)
    (h' : ℕ) (hh' : 1 ≤ h') :
    SecondPropositionRingInput W π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c := by
  obtain ⟨ν, hνΔ, hνeq⟩ := u2ringPfC_nu W hR hs hK h'
  obtain ⟨hπΔ, hsub, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, ⟨w₂, hγ⟩, -⟩ := hR
  have hπ0 := constantCoeff_uniformiser_zero w hw hs
  have hHS : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  set ψ : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom (hHS c) with hψdef
  have hψ : ∀ F, ψ F = PowerSeries.subst (π' c) F := fun F => by
    rw [hψdef, PowerSeries.coe_substAlgHom]
  have hψX : ψ PowerSeries.X = π' c := by rw [hψ, PowerSeries.subst_X (hHS c)]
  have hψC : ∀ x : O, ψ (PowerSeries.C x) = PowerSeries.C x := fun x => by
    rw [hψ, PowerSeries.subst_C]; rfl
  have hψΔ : ∀ δ ∈ W.DelF, ∀ F, W.γ₀ δ (ψ F) = ψ F := fun δ hδ F => by
    rw [hψ]; exact u2ringPfC_subΔ W hπΔ hπ0 δ hδ c F
  have hψinj : ∀ F F', ψ F = ψ F' → F = F' := fun F F' h =>
    u2ringPfC_inj W hπΔ hsub hπ0 c F F' (by rwa [hψ, hψ] at h)
  have hpre : ∀ x, (∀ δ ∈ W.DelF, W.γ₀ δ x = x) → ∃ F, ψ F = x := fun x hx => by
    obtain ⟨F, hF⟩ := u2ringPfC_pre W hsub c x hx
    exact ⟨F, by rw [hψ]; exact hF⟩
  have hsingle : ∀ F, (Pi.single c (ψ F) : LetA O n) ∈ W.AΔ := fun F =>
    u2ringPfB_single_mem W c _ (fun δ hδ => hψΔ δ hδ F)
  have halg : ∀ x : O, (algebraMap O (LetA O n) x) c = PowerSeries.C x := fun x => by
    rw [Pi.algebraMap_apply, PowerSeries.algebraMap_apply]; rfl

  set EY : PowerSeries O := PowerSeries.C a * ∏ j, (PowerSeries.X - PowerSeries.C (r j)) with hEY
  have hÊc : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c = ψ EY := by
    show Polynomial.aeval (π' c) (E c) = ψ EY
    rw [hE, hEY, map_mul, map_prod, map_mul, map_prod, Polynomial.aeval_C, hψC]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hψX, hψC]
    rfl
  have hXC0 : ∀ y : O, (PowerSeries.X - PowerSeries.C y : PowerSeries O) ≠ 0 := fun y h => by
    have := congrArg (PowerSeries.coeff 1) h; simp at this
  have hEY0 : EY ≠ 0 := by
    rw [hEY]
    refine mul_ne_zero (fun h => ha.ne_zero ?_) (Finset.prod_ne_zero_iff.2 fun j _ => hXC0 _)
    simpa using congrArg PowerSeries.constantCoeff h
  have hψEY0 : ψ EY ≠ 0 := fun h => hEY0 (hψinj _ _ (by rw [h, map_zero]))
  have hπc0 : π' c ≠ 0 := by
    have : π' c = (w : LetA O n) c * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this]
    exact mul_ne_zero (w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)).ne_zero
      (pow_ne_zero _ PowerSeries.X_ne_zero)

  have hγc : W.γ₀ W.gam (π' c) = π' c + (w₂ : LetA O n) c * π' c * ψ EY := by
    have e1 : W.γ₀ W.gam (π' c) - π' c = (w₂ : LetA O n) c * π' c * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c :=
      congrFun hγ c
    rw [← hÊc, ← e1]; ring
  have hw2Δ : ∀ δ ∈ W.DelF, W.γ₀ δ ((w₂ : LetA O n) c) = (w₂ : LetA O n) c := by
    intro δ hδ
    have hπc : W.γ₀ δ (π' c) = π' c := congrFun (hπΔ δ hδ) c
    have h1 := congrArg (W.γ₀ δ) hγc
    rw [u2ringPfB_γ₀_comm, hπc, map_add, map_mul, map_mul, hπc, hψΔ δ hδ] at h1
    have h2 : (W.γ₀ δ ((w₂ : LetA O n) c) - (w₂ : LetA O n) c) * (π' c * ψ EY) = 0 := by
      linear_combination h1.symm.trans hγc
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero hπc0 hψEY0))
  obtain ⟨Ŵ, hŴ⟩ := hpre _ hw2Δ
  have hŴ0 : IsUnit (PowerSeries.constantCoeff Ŵ) := by
    have h1 : IsUnit ((w₂ : LetA O n) c) :=
      w₂.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
    rw [← hŴ, hψ, DualFramesAlt.EigenUniformiser.subst_eq_C_add (hπ0 c), PowerSeries.isUnit_iff_constantCoeff] at h1
    simpa [hπ0 c] using h1
  set Gt : PowerSeries O := 1 + Ŵ * EY with hGt
  set XG : PowerSeries O := PowerSeries.X * Gt with hXG
  have hXG0 : PowerSeries.constantCoeff XG = 0 := by
    rw [hXG, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hHSXG := PowerSeries.HasSubst.of_constantCoeff_zero' hXG0
  set Γ : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom hHSXG with hΓdef
  have hΓ : ∀ F, Γ F = PowerSeries.subst XG F := fun F => by rw [hΓdef, PowerSeries.coe_substAlgHom]
  have hΓX : Γ PowerSeries.X = XG := by rw [hΓ, PowerSeries.subst_X hHSXG]
  have hΓC : ∀ x : O, Γ (PowerSeries.C x) = PowerSeries.C x := fun x => by
    rw [hΓ, PowerSeries.subst_C]; rfl
  have hγπc : W.γ₀ W.gam (π' c) = ψ XG := by
    rw [hγc, hXG, hGt]
    simp only [map_mul, map_add, map_one, hψX, hŴ]
    ring
  have hγψ : ∀ F, W.γ₀ W.gam (ψ F) = ψ (Γ F) := by
    intro F
    rw [hψ F, DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ W.gam) (W.γ₀_X _).1 (hπ0 c), hγπc, hψ XG, hΓ F,
      hψ (PowerSeries.subst XG F), PowerSeries.subst_comp_subst_apply hHSXG (hHS c)]

  let θ : Fin e → PowerSeries O := fun j => 1 + PowerSeries.X * Ŵ * PowerSeries.C a *
      ∏ j' ∈ Finset.univ.erase j, (PowerSeries.X - PowerSeries.C (r j'))
  have hEYsplit : ∀ j, EY = (PowerSeries.X - PowerSeries.C (r j)) *
      (PowerSeries.C a * ∏ j' ∈ Finset.univ.erase j, (PowerSeries.X - PowerSeries.C (r j'))) := by
    intro j; rw [hEY, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]; ring
  have hΓlin : ∀ j, Γ (PowerSeries.X - PowerSeries.C (r j)) =
      (PowerSeries.X - PowerSeries.C (r j)) * θ j := by
    intro j
    rw [map_sub, hΓX, hΓC, hXG, hGt, hEYsplit j]
    ring
  have hΓEY : Γ EY = EY * ∏ j, θ j := by
    conv_lhs => rw [hEY]
    rw [map_mul, map_prod, hΓC, Finset.prod_congr rfl fun j _ => hΓlin j, Finset.prod_mul_distrib, hEY]
    ring

  obtain ⟨nh, hnh⟩ := hpre _ (u2ringPfB_letter_mem W hνΔ c)
  have hnθ : nh * (∏ j, θ j) ^ h' = 1 := by
    have h2 : ν c * W.γ₀ W.gamK (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c ^ h' :=
      congrFun hνeq c
    rw [hK, map_pow, hÊc, hγψ, ← hnh, ← map_pow ψ (Γ EY) h', ← map_pow ψ EY h', ← map_mul,
      hΓEY] at h2
    have h3 := hψinj _ _ h2
    have h4 : EY ^ h' * (nh * (∏ j, θ j) ^ h' - 1) = 0 := by linear_combination h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left (pow_ne_zero _ hEY0))

  have hm : 0 < 2 * h' := by omega
  set m := 2 * h' with hmdef
  set NR := m * e with hNR
  let rI : ℕ → O := fun k => if h : k < e then r ⟨k, h⟩ else 0
  have hrI : ∀ j : Fin e, rI j = r j := fun j => by simp [rI, j.2]
  have hdiv : ∀ k, k < NR → k / m < e := fun k hk => Nat.div_lt_of_lt_mul hk
  let root : ℕ → O := fun k => if k < NR then rI (k / m) else 0
  have hrootm : ∀ k, root k ∈ IsLocalRing.maximalIdeal O := by
    intro k
    simp only [root, rI]
    split_ifs
    · exact hrm _
    · exact Ideal.zero_mem _
    · exact Ideal.zero_mem _
  let φY : ℕ → PowerSeries O := fun k =>
    if k < NR then PowerSeries.X - PowerSeries.C (root k) else PowerSeries.C (a ^ m) * PowerSeries.X
  let θ' : ℕ → PowerSeries O := fun j => if h : j < e then θ ⟨j, h⟩ else 1
  let θY : ℕ → PowerSeries O := fun k => if k < NR then θ' (k / m) else Gt
  let f : ℕ → LetA O n := fun k =>
    if k < NR then π' - algebraMap O (LetA O n) (root k) else algebraMap O (LetA O n) (a ^ m) * π'
  have hfc : ∀ k, f k c = ψ (φY k) := by
    intro k
    simp only [f, φY]
    split_ifs
    · rw [Pi.sub_apply, halg, map_sub, hψX, hψC]
    · rw [Pi.mul_apply, halg, map_mul, hψX, hψC]
  have hfΔ : ∀ k, f k ∈ W.AΔ := by
    intro k
    simp only [f]
    split_ifs
    · exact W.AΔ.sub_mem hπΔ (W.AΔ.algebraMap_mem _)
    · exact W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) hπΔ
  have hφroot : ∀ k, ∃ u : PowerSeries O, PowerSeries.X - PowerSeries.C (root k) = φY k * u := by
    intro k
    by_cases hk : k < NR
    · exact ⟨1, by simp only [φY, if_pos hk, mul_one]⟩
    · refine ⟨PowerSeries.C (((ha.unit⁻¹ : Oˣ) : O) ^ m), ?_⟩
      simp only [φY, root, if_neg hk, map_zero, sub_zero]
      rw [mul_comm, ← mul_assoc, ← map_mul, ← mul_pow, ha.val_inv_mul, one_pow, map_one, one_mul]
  have hΓφ : ∀ k, Γ (φY k) = φY k * θY k := by
    intro k
    by_cases hk : k < NR
    · have hj := hdiv k hk
      simp only [φY, θY, θ', root, rI, if_pos hk, dif_pos hj]
      exact hΓlin ⟨k / m, hj⟩
    · simp only [φY, θY, if_neg hk]
      rw [map_mul, hΓC, hΓX, hXG]
      ring
  have hPY : ∀ k, (∏ j ∈ Finset.range k, f j) c = ψ (∏ j ∈ Finset.range k, φY j) := by
    intro k
    rw [Finset.prod_apply, map_prod]
    exact Finset.prod_congr rfl fun j _ => hfc j
  have hΓP : ∀ k, Γ (∏ j ∈ Finset.range k, φY j) =
      (∏ j ∈ Finset.range k, φY j) * ∏ j ∈ Finset.range k, θY j := by
    intro k
    rw [map_prod, Finset.prod_congr rfl fun j _ => hΓφ j, Finset.prod_mul_distrib]
  have hprod : ∏ k ∈ Finset.range (NR + 1), φY k = PowerSeries.X * EY ^ m := by
    have h0 : φY NR = PowerSeries.C (a ^ m) * PowerSeries.X := by
      simp only [φY, if_neg (lt_irrefl NR)]
    have h1 : ∏ k ∈ Finset.range NR, φY k =
        ∏ k ∈ Finset.range NR, (PowerSeries.X - PowerSeries.C (rI (k / m))) :=
      Finset.prod_congr rfl fun k hk => by simp only [φY, root, if_pos (Finset.mem_range.1 hk)]
    have h3 := DualFramesAlt.BlockProductRing.prod_div_block m hm (fun j => PowerSeries.X - PowerSeries.C (rI j)) e
    have h2 : ∏ j ∈ Finset.range e, (PowerSeries.X - PowerSeries.C (rI j)) =
        ∏ j, (PowerSeries.X - PowerSeries.C (r j)) := by
      rw [← Fin.prod_univ_eq_prod_range]
      exact Finset.prod_congr rfl fun j _ => by rw [hrI j]
    rw [Finset.prod_range_succ, h0, h1, hNR, h3, Finset.prod_pow,
      h2, hEY, mul_pow, map_pow]
    ring

  let ρ : ℕ → PowerSeries O := fun k => nh * ∏ i ∈ Finset.range k, θY i
  let cc : ℕ → O := fun k => Classical.choose (DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) (ρ k))
  have hcc : ∀ k, (mkI (root k)) (ρ k) = (mkI (root k)) (PowerSeries.C (cc k)) := fun k =>
    Classical.choose_spec (DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) (ρ k))
  have hmkΓ : ∀ k F, (mkI (root k)) (Γ F) = (mkI (root k)) F := by
    intro k F
    obtain ⟨c₀, hc₀⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) F
    have hXGr : (mkI (root k)) XG = (mkI (root k)) (PowerSeries.C (root k)) := by
      apply DualFramesAlt.BlockProductRing.mk_eq_of_mem
      by_cases hkN : k < NR
      · have hj := hdiv k hkN
        have hrk : root k = r ⟨k / m, hj⟩ := by simp [root, rI, hkN, hj]
        have key : XG - PowerSeries.C (root k) = (PowerSeries.X - PowerSeries.C (root k)) *
            (1 + PowerSeries.X * Ŵ * (PowerSeries.C a *
              ∏ j' ∈ Finset.univ.erase ⟨k / m, hj⟩, (PowerSeries.X - PowerSeries.C (r j')))) := by
          rw [hXG, hGt, hEYsplit ⟨k / m, hj⟩, hrk]; ring
        rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
      · have hrk : root k = 0 := by simp [root, hkN]
        have key : XG - PowerSeries.C (root k) = (PowerSeries.X - PowerSeries.C (root k)) * Gt := by
          rw [hXG, hrk, map_zero, sub_zero, sub_zero]
        rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
    rw [hΓ, DualFramesAlt.eigenRingInvariants.ev_subst hXG0 hXGr hc₀, hc₀]
  refine ⟨?_, ?_, ⟨1 + (w₂ : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π', ?_, ?_⟩, ν, hνΔ, hνeq, NR + 1, f, cc,
    hfΔ, ?_, ?_, ?_, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · have h1 := Formalism.MainNotions.LiftingTheory.liftb_q_unit W
    rw [hq, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  · exact gradNPf_fΔ W s' w π' _ hw hπΔ (by linear_combination hγ)
  · rw [hK]; linear_combination hγ
  · funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply]
      congr 1
      rw [hPY, hprod, map_mul, map_pow, hψX, ← hÊc]
      rfl
    · simp [letE, hi]
  · intro k hk x hx
    obtain ⟨F, hF⟩ := hpre _ (u2ringPfB_letter_mem W hx c)
    obtain ⟨a₀, ha₀⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) F
    obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq ha₀
    obtain ⟨u, hu⟩ := hφroot k
    refine ⟨a₀, Pi.single c (ψ (u * H)), hsingle _, ?_⟩
    funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply, Pi.add_apply, Pi.single_eq_same]
      congr 1
      rw [halg, hfc, ← hF, ← hψC, ← map_mul, ← map_add]
      congr 1
      linear_combination hH + H * hu
    · simp [letE, hi]
  · intro k hk x hx
    obtain ⟨F, hF⟩ := hpre _ (u2ringPfB_letter_mem W hx c)
    have hZ0 : (mkI (root k)) (ρ k * Γ F - PowerSeries.C (cc k) * F) =
        (mkI (root k)) (PowerSeries.C 0) := by
      rw [map_sub, map_mul (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (root k))) (ρ k) (Γ F),
        map_mul (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (root k))) (PowerSeries.C (cc k)) F, hcc k, hmkΓ,
        map_zero, sub_self, map_zero]
    obtain ⟨Z', hZ'⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hZ0
    rw [map_zero, sub_zero] at hZ'
    obtain ⟨u, hu⟩ := hφroot k
    refine ⟨Pi.single c (ψ (u * Z')), hsingle _, ?_⟩
    funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.single_eq_same]
      congr 1
      have hγA : ∀ (g : W.Gam) (y : LetA O n), (W.γA g y) c = W.γ₀ g (y c) := fun _ _ => rfl
      rw [hγA, Pi.mul_apply, hK, hPY, ← hF, ← map_mul, hγψ, ← hnh, halg, ← hψC, hPY (k + 1),
        ← map_mul, ← map_mul, ← map_mul, ← map_sub]
      congr 1
      rw [map_mul, hΓP, Finset.prod_range_succ]
      simp only [ρ] at hZ'
      linear_combination (∏ j ∈ Finset.range k, φY j) * hZ' + (∏ j ∈ Finset.range k, φY j) * Z' * hu
    · simp [letE, hi]
  · have hθother : ∀ j j' : Fin e, j ≠ j' → (mkI (r j)) (θ j') = 1 := by
      intro j j' hjj'
      rw [← map_one (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (r j)))]
      apply DualFramesAlt.BlockProductRing.mk_eq_of_mem
      have hjmem : j ∈ Finset.univ.erase j' := Finset.mem_erase.2 ⟨hjj', Finset.mem_univ j⟩
      have key : θ j' - 1 = (PowerSeries.X - PowerSeries.C (r j)) * (PowerSeries.X * Ŵ * PowerSeries.C a *
          ∏ i ∈ (Finset.univ.erase j').erase j, (PowerSeries.X - PowerSeries.C (r i))) := by
        simp only [θ]
        rw [← Finset.mul_prod_erase _ _ hjmem]; ring
      rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
    have hcval : ∀ j : Fin e, ∃ cj : O, IsUnit cj ∧ (∀ t : ℕ, 0 < t → cj ^ t ≠ 1) ∧
        (mkI (r j)) (θ j) = (mkI (r j)) (PowerSeries.C cj) := by
      intro j
      obtain ⟨wj, hwj⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrm j) Ŵ
      have hwju : IsUnit wj := by
        obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hwj
        have h0 := congrArg PowerSeries.constantCoeff hH
        simp only [map_sub, map_mul, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C,
          zero_sub] at h0
        by_contra hnu
        have hwm : wj ∈ IsLocalRing.maximalIdeal O :=
          (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
        have hŴm : PowerSeries.constantCoeff Ŵ ∈ IsLocalRing.maximalIdeal O := by
          have e0 : PowerSeries.constantCoeff Ŵ = wj + -r j * PowerSeries.constantCoeff H := by
            linear_combination h0
          rw [e0]
          exact Ideal.add_mem _ hwm (Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 (hrm j)))
        exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hŴm)) hŴ0
      refine ⟨1 + r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j'), ?_, hnr j wj hwju, ?_⟩
      · by_contra hnu
        have h1 : 1 + r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') ∈
            IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
        have h2 : r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') ∈
            IsLocalRing.maximalIdeal O :=
          Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hrm j)))
        have h3 := Ideal.sub_mem _ h1 h2
        rw [add_sub_cancel_right] at h3
        exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
      · simp only [θ, map_add, map_one, map_mul, map_prod, map_sub, DualFramesAlt.eigenRingInvariants.mk_X, hwj]
    have hcount : (Finset.range (NR + 1)).filter (fun k => cc k = 1) ⊆
        ((Finset.range e).image fun j => m * j + h') ∪ {NR} := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkN, hk1⟩ := hk
      rcases Nat.lt_or_ge k NR with hlt | hge
      · apply Finset.mem_union_left
        have hj := hdiv k hlt
        obtain ⟨cj, hcju, hcjt, hcjmk⟩ := hcval ⟨k / m, hj⟩
        have hrk : root k = r ⟨k / m, hj⟩ := by simp [root, rI, hlt, hj]
        have hθY : ∀ i ∈ Finset.range k, (mkI (r ⟨k / m, hj⟩)) (θY i) =
            if i / m = k / m then (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) else 1 := by
          intro i hi
          have hiN : i < NR := lt_trans (Finset.mem_range.1 hi) hlt
          have hij := hdiv i hiN
          simp only [θY, θ', if_pos hiN, dif_pos hij]
          split_ifs with hik
          · have e0 : (⟨i / m, hij⟩ : Fin e) = ⟨k / m, hj⟩ := Fin.ext hik
            rw [e0]; exact hcjmk
          · exact hθother _ _ (fun h => hik (congrArg Fin.val h).symm)
        have hprodθ : (mkI (r ⟨k / m, hj⟩)) (∏ j, θ j) = (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) := by
          rw [map_prod, Finset.prod_eq_single ⟨k / m, hj⟩
            (fun j' _ hne => hθother _ _ (Ne.symm hne)) (fun h => absurd (Finset.mem_univ _) h)]
          exact hcjmk
        have hn : (mkI (r ⟨k / m, hj⟩)) nh * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ h' = 1 := by
          have e0 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (r ⟨k / m, hj⟩))) hnθ
          rwa [map_mul, map_pow, hprodθ, map_one] at e0
        have hρ : (mkI (r ⟨k / m, hj⟩)) (ρ k) =
            (mkI (r ⟨k / m, hj⟩)) nh * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) := by
          rw [show ρ k = nh * ∏ i ∈ Finset.range k, θY i from rfl, map_mul, map_prod,
            Finset.prod_congr rfl hθY, DualFramesAlt.BlockProductRing.prod_ite_block m hm _ k]
        have hkey : cc k * cj ^ h' = cj ^ (k % m) := by
          apply DualFramesAlt.eigenRingInvariants.ev_inj (hrm ⟨k / m, hj⟩)
          have h1 := hcc k
          rw [hrk, hρ] at h1
          have e1 : (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cc k * cj ^ h')) =
              (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cc k)) * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ h' := by
            simp only [map_mul, map_pow]
          have e2 : (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cj ^ (k % m))) =
              (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) := by
            simp only [map_pow]
          rw [e1, e2, ← h1]
          linear_combination (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) * hn
        rw [hk1, one_mul] at hkey
        have ht : k % m = h' := by
          rcases lt_trichotomy (k % m) h' with h1 | h1 | h1
          · exfalso
            apply hcjt (h' - k % m) (by omega)
            have e0 : cj ^ (k % m) * (cj ^ (h' - k % m) - 1) = 0 := by
              rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h1.le, hkey, sub_self]
            exact sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left (pow_ne_zero _ hcju.ne_zero))
          · exact h1
          · exfalso
            apply hcjt (k % m - h') (by omega)
            have e0 : cj ^ h' * (cj ^ (k % m - h') - 1) = 0 := by
              rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h1.le, hkey, sub_self]
            exact sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left (pow_ne_zero _ hcju.ne_zero))
        rw [Finset.mem_image]
        refine ⟨k / m, Finset.mem_range.2 hj, ?_⟩
        have e0 := Nat.div_add_mod k m
        rw [ht] at e0; exact e0
      · have e0 : k = NR := by omega
        exact Finset.mem_union_right _ (Finset.mem_singleton.2 e0)
    calc ((Finset.range (NR + 1)).filter fun k => cc k = 1).card
        ≤ (((Finset.range e).image fun j => m * j + h') ∪ {NR}).card := Finset.card_le_card hcount
      _ ≤ ((Finset.range e).image fun j => m * j + h').card + ({NR} : Finset ℕ).card :=
          Finset.card_union_le _ _
      _ ≤ e + 1 := by
        rw [Finset.card_singleton]
        exact Nat.add_le_add_right (Finset.card_image_le.trans (by rw [Finset.card_range])) 1
      _ ≤ finrank K₀ K + 1 := by omega

end U2D

end Formalism.MainNotions.N.Ln34
end
end
