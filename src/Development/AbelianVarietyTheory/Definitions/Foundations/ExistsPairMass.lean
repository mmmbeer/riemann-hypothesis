import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Model

theorem wd_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pres_vac (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) :
    Pres D cc δ 1 e0 e0 := by
  have h0 : pt D (tor0 D cc δ) δ (0 : Matrix (Fin d) (Fin a) D.host.E) = 0 := by
    funext τ i j
    simp [pt, embV, tor0]
  refine ⟨1, fun _ => 1, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i; rw [h0]; simp
  · intro i; simpa using isIntegral_one
  · intro ρ; simp
  · funext y; simp [h0, wd_zero]

def spherical {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (crv : Crv D cc δ)
    (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {a d : ℕ} (had : a ≤ d) (hd : Even d)
    (e0 : VC D a d → ℂ) (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0)
    (n : D.what₂.Tau → ℕ) (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ))
    (hfix : ∀ k ∈ intG D a, W.Om k 1 e0 = e0)
    (heig : ∀ j ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j e0 = c • e0) : Pair D cc δ t0 1 where
  crv := crv
  pt0 := pt0
  a := a
  d := d
  a_le := had
  d_even := hd
  e0 := e0
  vac := vac
  W := W
  n := n
  wt := wt
  F := e0
  pres := pres_vac D cc δ e0
  fix := hfix
  J := intG D d
  J_le := le_rfl
  idx_ne := by simp
  idx_le := by simp
  eig := heig


theorem mem_intG {D : D7} {N : ℕ} (k : GA D N) : k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D)) := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro i j
    have : ((1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    simpa using this
  | mul x y _ _ hx hy =>
    intro i j
    constructor
    · simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hx i l).1 (hy l j).1
    · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hy i l).2 (hx l j).2
  | inv x _ hx =>
    intro i j
    refine ⟨?_, ?_⟩
    · exact (hx i j).2
    · rw [Subgroup.coe_inv, inv_inv]; exact (hx i j).1


instance vcUnique (D : D7) : Unique (VC D 0 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

instance gaSub (D : D7) : Subsingleton (GA D 0) :=
  ⟨fun x y => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩

theorem hf0 (D : D7) (T : Tor D) (z w : VC D 0 0) : Hf D T z w = 0 := by simp [Hf]

theorem iop0 (D : D7) (T : Tor D) (A B : AddSubgroup (VC D 0 0)) (G : VC D 0 0 → ℂ) : Iop D T A B G = G := by
  funext z
  have hi : (A.addSubgroupOf B).index = 1 := by
    rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
  haveI : Subsingleton (B ⧸ A.addSubgroupOf B) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    congr 1
    exact Subsingleton.elim _ _
  haveI : Unique (B ⧸ A.addSubgroupOf B) := ⟨⟨((0 : B) : B ⧸ A.addSubgroupOf B)⟩, fun _ => Subsingleton.elim _ _⟩
  unfold Iop
  rw [hi, finsum_unique]
  simp only [al, U, hf0]
  simp
  congr 1
  exact Subsingleton.elim _ _

def triv (D : D7) : HeckeU D 0 where
  f := 1
  n := 0
  unitary := by simp
  cont := ⟨1, one_pos, by simp⟩
  aut := by simp
  norm := by simp
  par := by simp
  unr := by simp

def weil0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : WeilO D cc δ 0 0 (fun _ => 1) where
  nz := fun h => by simpa using congrFun h 0
  chV := triv D
  chV' := triv D
  ep := 1
  ep' := 1
  ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩
  Om := fun _ _ F => F
  maps := fun _ _ _ h => h
  add := fun _ _ _ _ _ _ => rfl
  smul := fun _ _ _ _ _ => rfl
  one := fun _ _ => rfl
  mul := fun _ _ _ _ _ _ => rfl
  lift := fun _ _ z _ _ => ⟨1, one_pos, fun z' _ => by rw [Subsingleton.elim z z']⟩
  inert := fun _ _ _ _ _ _ => rfl
  split := by
    intros
    rw [iop0]; simp [triv]

theorem taylor0 (D : D7) (α : Mono D 0 0) (c : ℂ) : taylor D (fun _ => c) α = c := by
  have : α = 0 := by ext k; exact k.2.1.elim0
  subst this
  have h : ∀ (k : ℕ) (v : Fin k → VC D 0 0), k = 0 → iteratedFDeriv ℂ k (fun _ : VC D 0 0 => c) 0 v = c := by
    intro k v hk; subst hk; simp
  unfold taylor
  rw [h _ _ (by simp)]
  simp

theorem normSq0 (D : D7) (T : Tor D) (A : AddSubgroup (VC D 0 0)) : normSq D T A (fun _ => 1) = 1 := by
  have hex : ∃ Fd : Set (VC D 0 0), MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume := by
    refine ⟨Set.univ, MeasureTheory.IsAddFundamentalDomain.mk' (by simp) fun x => ⟨0, by simp, fun y _ => Subsingleton.elim _ _⟩⟩
  have hs := Classical.epsilon_spec hex
  unfold normSq
  simp only [hf0]
  set Fd := Classical.epsilon (fun Fd : Set (VC D 0 0) => MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume)
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (VC D 0 0)) Set.univ = 1 := by
    simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  have hF : Fd = Set.univ := by
    have hc := hs.ae_covers
    by_contra hne
    have he : Fd = ∅ := by
      rcases Set.eq_empty_or_nonempty Fd with h | ⟨x, hx⟩
      · exact h
      · exact absurd (Set.eq_univ_of_forall fun y => by rw [Subsingleton.elim y x]; exact hx) hne
    rw [he] at hc
    simp only [Set.mem_empty_iff_false, exists_false, Filter.eventually_false_iff_eq_bot,
      MeasureTheory.ae_eq_bot] at hc
    rw [hc] at hv; simp at hv
  rw [hF]
  simp [MeasureTheory.average_eq, MeasureTheory.Measure.real, hv]

theorem vac0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) : oddE0 D cc δ t0 0 0 (fun _ => 1) := by
  haveI : IsEmpty (Fin (fF D * 0 * 0)) := by simp only [mul_zero]; infer_instance
  have hon : OnB D (fun _ : Fin (fF D * 0 * 0) => (0 : Matrix (Fin 0) (Fin 0) D.host.E)) :=
    ⟨fun i => isEmptyElim i, Subsingleton.elim _ _⟩
  refine ⟨⟨differentiable_const _, fun x _ z => ?_⟩, fun α => ?_, ?_, ⟨fun _ => 0, 1, hon, ⟨one_mem _, fun σ => ?_⟩, ?_⟩, ?_⟩
  · simp [al, U, hf0]
  · rw [taylor0]; exact one_mem _
  · rw [La0, normSq0]; simp
  · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
    rw [this]; simp
  · rw [iop0]; funext z; simp [pullB]
  · intro p _ lam _
    refine ⟨fun _ => 0, 1, hon, ⟨linearIndependent_empty_type, fun i => isEmptyElim i,
      fun y _ => ⟨1, by simp, fun i => isEmptyElim i, Subsingleton.elim _ _⟩⟩, one_mem _, ?_, ?_, ?_⟩
    · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
      simp [lamC, this]
    · have hi : ((LaB D (tor0 D cc δ) (fun _ : Fin (fF D * 0 * 0) => (0 : Matrix (Fin 0) (Fin 0) D.host.E))).addSubgroupOf
          (La0 D (tor0 D cc δ) 0 0)).index = 1 := by
        rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
      rw [hi]; simp
    · rw [iop0]; funext z; simp [pullB]


def pair0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (crv : Crv D cc δ)
    (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) : Pair D cc δ t0 1 :=
  spherical crv pt0 le_rfl (by simp) (fun _ => 1) (vac0 D cc δ t0) (weil0 D cc δ) 0
    (by simp [weil0, triv]) (fun _ _ => rfl) (fun _ _ => ⟨1, by simp, by simp [weil0]⟩)

theorem gam0 (D : D7) (J : Subgroup (GA D 0)) (g : GA D 0) : gam D J g = 1 := by
  unfold gam
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, ⟨⟨1, one_mem _, by rw [Subsingleton.elim (_ * _ * _) 1]; exact one_mem _⟩⟩⟩

instance cls0 (D : D7) (J : Subgroup (GA D 0)) : Unique (Cls D 0 J) :=
  ⟨⟨Quotient.mk'' 1⟩, fun x => by
    induction x using Quotient.inductionOn'
    congr 1
    exact Subsingleton.elim _ _⟩

theorem vac_mem_TT {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {e0 : VC D a d → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) : e0 ∈ TT D (tor0 D cc δ) a d := by
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc a d (La0 D (tor0 D cc δ) a d)
    (Or.inr ⟨_, _, RepInv.sd_std D _, RepInv.sd_std D _, rfl⟩)
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, hW x hx]
  funext w
  exact he.2 x hx w


theorem eq_zero_of_zeroAt (D : D7) {z : AE D} (h : ∀ q : ℕ, q.Prime → ZeroAt D q z) : z = 0 := by
  obtain ⟨n, hn, hw⟩ := VacMove.exists_nat_denom D z
  have hw0 : (n : AE D) * z = 0 := by
    refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 _ fun N hN => ?_
    let I : Ideal ℤ :=
      { carrier := {m | ∃ s ∈ OhE D, (m : AE D) * ((n : AE D) * z) = (N : AE D) * s}
        add_mem' := by
          rintro a b ⟨s, hs, e⟩ ⟨t, ht, e'⟩
          exact ⟨s + t, add_mem hs ht, by push_cast; rw [add_mul, e, e', mul_add]⟩
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        smul_mem' := by
          rintro c a ⟨s, hs, e⟩
          exact ⟨c * s, mul_mem (intCast_mem _ c) hs, by
            rw [smul_eq_mul]; push_cast; rw [mul_assoc, e]; ring⟩ }
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨Mx, hM, hle⟩ := Ideal.exists_le_maximal I hne
      have hNI : (N : ℤ) ∈ I := ⟨_, hw, by simp⟩
      obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal Mx).principal
      have hg0 : g ≠ 0 := by
        rintro rfl
        have := hle hNI
        rw [hg] at this
        simp at this
        omega
      have hp : Prime g := by
        have := hM.isPrime
        rw [hg] at this
        exact (Ideal.span_singleton_prime hg0).1 this
      have hq : g.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hp
      obtain ⟨k, N', hN', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' g.natAbs hq.ne_one
      obtain ⟨m, -, hm, s, hs, e⟩ := h _ hq k
      have hmI : ((m * N' : ℕ) : ℤ) ∈ I := ⟨n * s, mul_mem (natCast_mem _ n) hs, by
        push_cast; linear_combination (N' : AE D) * (n : AE D) * e⟩
      have := hle hmI
      rw [hg] at this
      have hd : g.natAbs ∣ m * N' := by
        have := Ideal.mem_span_singleton.1 this
        exact Int.natAbs_dvd_natAbs.2 this
      rcases (Nat.Prime.dvd_mul hq).1 hd with h1 | h1
      · exact (Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm h1
      · exact hN' h1
    have h1 : (1 : ℤ) ∈ I := hI ▸ Submodule.mem_top
    obtain ⟨s, hs, e⟩ := h1
    exact ⟨s, hs, by simpa using e⟩
  have hu : IsUnit (n : AE D) := by
    have : (n : AE D) = inc D n := by simp
    rw [this]
    exact (IsUnit.mk0 _ (by exact_mod_cast hn.ne')).map _
  exact (hu.mul_right_eq_zero).1 hw0

theorem hecke_eq_one {D : D7} {N : ℕ} (χ : HeckeU D N) (x : (AE D)ˣ) (hx : x = sgU D x)
    (hi : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) : χ.f x = 1 := by
  obtain ⟨ε, -, h1, h2, h3⟩ := VacMove.exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  have hx' : sgA D x = x := (congrArg Units.val hx).symm
  have hz : (1 - (ε + sgA D ε)) * ((x : AE D) - 1) = 0 := by
    refine eq_zero_of_zeroAt D fun q hq => ?_
    by_cases h : InertQ D q
    · rw [mul_comm]; exact VacMove.zeroAt_mul D hq (hi q hq h) _
    · exact VacMove.zeroAt_mul D hq ((h3 q hq).2 h) _
  have hu : (x : AE D) * (x⁻¹ : (AE D)ˣ) = 1 := x.mul_inv
  have hy : ((1 - ε) + ε * x) * ((1 - ε) + ε * (x⁻¹ : (AE D)ˣ)) = 1 := by
    linear_combination (1 - x - (x⁻¹ : (AE D)ˣ) + x * (x⁻¹ : (AE D)ˣ)) * h1 + ε * hu
  let y : (AE D)ˣ := ⟨_, _, hy, by rw [mul_comm, hy]⟩
  have e : x = y * sgU D y := by
    ext
    change (x : AE D) = ((1 - ε) + ε * x) * sgA D ((1 - ε) + ε * x)
    rw [map_add, map_mul, map_sub, map_one, hx']
    linear_combination hz - (1 - x) ^ 2 * h2
  rw [e, χ.norm]

instance vcUniqueD (D : D7) (d : ℕ) : Unique (VC D 0 d) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

theorem hfD (D : D7) (T : Tor D) {d : ℕ} (z w : VC D 0 d) : Hf D T z w = 0 := by simp [Hf]

theorem iopD (D : D7) (T : Tor D) {d : ℕ} (A B : AddSubgroup (VC D 0 d)) (G : VC D 0 d → ℂ) : Iop D T A B G = G := by
  funext z
  have hi : (A.addSubgroupOf B).index = 1 := by
    rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
  haveI : Subsingleton (B ⧸ A.addSubgroupOf B) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    congr 1
    exact Subsingleton.elim _ _
  haveI : Unique (B ⧸ A.addSubgroupOf B) := ⟨⟨((0 : B) : B ⧸ A.addSubgroupOf B)⟩, fun _ => Subsingleton.elim _ _⟩
  unfold Iop
  rw [hi, finsum_unique]
  simp only [al, U, hfD]
  simp
  congr 1
  exact Subsingleton.elim _ _

def weilD (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {d : ℕ} (χ : HeckeU D d) :
    WeilO D cc δ 0 d (fun _ => 1) where
  nz := fun h => by simpa using congrFun h 0
  chV := triv D
  chV' := χ
  ep := 1
  ep' := 1
  ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩
  Om := fun _ _ F => F
  maps := fun _ _ _ h => h
  add := fun _ _ _ _ _ _ => rfl
  smul := fun _ _ _ _ _ => rfl
  one := fun _ _ => rfl
  mul := fun _ _ _ _ _ _ => rfl
  lift := fun _ _ z _ _ => ⟨1, one_pos, fun z' _ => by rw [Subsingleton.elim z z']⟩
  inert := fun _ _ _ _ _ _ => rfl
  split := by
    intro g g' x x' L₁ L₁' _ _ hi hx _ _ _
    have hd : Matrix.GeneralLinearGroup.det (g : GL (Fin 0) (AE D)) = 1 := by
      ext; simp [Matrix.det_isEmpty]
    rw [hd, one_mul] at hx
    rw [iopD, hecke_eq_one χ x hx fun q hq h => (hi q hq h).1]; simp [triv]





example (D : D7) (T : Tup D 2 2 (fun _ => 1)) :
    minorPol D T = ∏ τ, (MvPolynomial.X (τ, (T τ 0).1 0, 0) * MvPolynomial.X (τ, (T τ 0).1 1, 1) -
      MvPolynomial.X (τ, (T τ 0).1 0, 1) * MvPolynomial.X (τ, (T τ 0).1 1, 0)) := by
  simp [minorPol, Matrix.det_fin_two]

end GlobalTheory.NormSum.Model
