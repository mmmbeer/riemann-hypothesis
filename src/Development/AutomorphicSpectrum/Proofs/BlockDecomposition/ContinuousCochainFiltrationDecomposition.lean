import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.SmoothUniform

theorem smooth_uniform_exponent : ∀ {R : Type} [CommRing R] (l : ℕ) [Fact l.Prime] (k : ℕ) {M : Type w} [AddCommGroup M] [Module R M] (ρ : Multiplicative (Fin k → ℤ_[l]) →* (M →ₗ[R] M)) (n : ℕ), (∀ x : M, ∃ a : ℕ, ∀ g : Fin k → ℤ_[l], ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) x = x) → ∀ f : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M, ∃ a : ℕ, ∀ (g : Fin k → ℤ_[l]) (x : Fin (n + 1) → Fin k → ℤ_[l]), f (fun i => (l : ℤ_[l]) ^ a • g + x i) = f x ∧ ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) (f x) = f x := by
  intro R _ l _ k M _ _ ρ n hsm f
  have hl : (1 : ℝ) < (l : ℝ) := by
    exact_mod_cast (Fact.out : l.Prime).one_lt
  have hfin : (Set.range f).Finite := f.range_finite
  choose A hA using hsm
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℕ, ∀ m ∈ Set.range f, A m ≤ a₁ := by
    obtain ⟨b, hb⟩ := (hfin.image A).bddAbove
    exact ⟨b, fun m hm => hb (Set.mem_image_of_mem A hm)⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (s := (Set.univ : Set (Fin (n + 1) → Fin k → ℤ_[l])))
    (c := fun m : M => f ⁻¹' {m}) isCompact_univ
    (fun m => f.isLocallyConstant.isOpen_fiber m)
    (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : ℕ, (1 / (l : ℝ)) ^ a₂ < δ :=
    exists_pow_lt_of_lt_one hδ (by
      rw [div_lt_one (by linarith)]
      exact hl)
  refine ⟨max a₁ a₂, fun g x => ⟨?_, ?_⟩⟩
  · have hnorm : ‖(l : ℤ_[l]) ^ (max a₁ a₂) • g‖ < δ := by
      have hle : ‖(l : ℤ_[l]) ^ (max a₁ a₂) • g‖ ≤ (1 / (l : ℝ)) ^ a₂ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
        have h1 : ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ = (1 / (l : ℝ)) ^ (max a₁ a₂) := by
          rw [PadicInt.norm_p_pow, zpow_neg, zpow_natCast, one_div, inv_pow]
        have h2 : (1 / (l : ℝ)) ^ (max a₁ a₂) ≤ (1 / (l : ℝ)) ^ a₂ :=
          pow_le_pow_of_le_one (by positivity)
            (by rw [div_le_one (by linarith)]; exact hl.le) (le_max_right _ _)
        calc ‖((l : ℤ_[l]) ^ (max a₁ a₂) • g) j‖
            = ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ * ‖g j‖ := by
              simp [Pi.smul_apply, norm_mul]
          _ ≤ ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ * 1 :=
              mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
          _ ≤ (1 / (l : ℝ)) ^ a₂ := by rw [mul_one, h1]; exact h2
      exact hle.trans_lt ha₂
    obtain ⟨m, hm⟩ := hball x (Set.mem_univ x)
    have hx : f x = m := hm (Metric.mem_ball_self hδ)
    have hy : f (fun i => (l : ℤ_[l]) ^ (max a₁ a₂) • g + x i) = m := by
      apply hm
      rw [Metric.mem_ball, dist_eq_norm]
      refine lt_of_le_of_lt ?_ hnorm
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simp
    rw [hx, hy]
  · have hle : A (f x) ≤ max a₁ a₂ := (ha₁ _ ⟨x, rfl⟩).trans (le_max_left _ _)
    have hsplit : (l : ℤ_[l]) ^ (max a₁ a₂) • g
        = (l : ℤ_[l]) ^ (A (f x)) • ((l : ℤ_[l]) ^ (max a₁ a₂ - A (f x)) • g) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hle]
    rw [hsplit]
    exact hA (f x) _

end GlobalTheory.CompanionTheory.SmoothUniform
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.GrpOnto

theorem sum_range_periodic {A : Type*} [AddCommMonoid A] (u : ℕ → A) (p : ℕ)
    (hu : ∀ t, u (t + p) = u t) (q : ℕ) :
    ∑ t ∈ Finset.range (p * q), u t = q • ∑ t ∈ Finset.range p, u t := by
  have hper : ∀ q t, u (p * q + t) = u t := by
    intro q t
    induction q with
    | zero => simp
    | succ q ih => rw [show p * (q + 1) + t = (p * q + t) + p by ring, hu, ih]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hper q t

theorem val_sub_one {P : ℕ} [NeZero P] (z : ZMod P) :
    (z.val ≠ 0 → (z - 1).val = z.val - 1) ∧ (z.val = 0 → (z - 1).val = P - 1) := by
  have hlt := ZMod.val_lt z
  have hz : ((z.val : ℕ) : ZMod P) = z := ZMod.natCast_zmod_val z
  have hP := NeZero.pos P
  constructor
  · intro h
    have e1 : z - 1 = ((z.val - 1 : ℕ) : ZMod P) := by
      rw [Nat.cast_sub (by omega), hz]; simp
    rw [e1, ZMod.val_natCast_of_lt (by omega)]
  · intro h
    have hz0 : z = 0 := by rw [← hz, h]; simp
    have e1 : z - 1 = ((P - 1 : ℕ) : ZMod P) := by
      rw [Nat.cast_sub hP, hz0]; simp
    rw [e1, ZMod.val_natCast_of_lt (by omega)]

theorem core {R : Type} [CommRing R] (l : ℕ) [Fact l.Prime] (k : ℕ) {M : Type w} [AddCommGroup M]
    [Module R M] (ρ : Multiplicative (Fin k → ℤ_[l]) →* (M →ₗ[R] M)) (n c : ℕ) (S : Set (Fin k))
    (i : Fin k) (hiS : i ∉ S) (hc : ∀ x : M, l ^ c • x = 0)
    (hsm : ∀ x : M, ∃ a : ℕ, ∀ g : Fin k → ℤ_[l], ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) x = x)
    (f : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M)
    (hf : ∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      f (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (f x)) :
    ∃ g : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M,
      (∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
        g (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (g x)) ∧
      ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
        ρ (Multiplicative.ofAdd (Pi.single i 1)) (g fun j => x j - Pi.single i 1) - g x = f x := by
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.SmoothUniform.smooth_uniform_exponent (R := R) l k ρ n hsm f
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨e, he⟩ : ∃ e : Fin k → ℤ_[l], e = Pi.single i 1 := ⟨_, rfl⟩
  rw [← he]
  have hcomm : ∀ (p q : Multiplicative (Fin k → ℤ_[l])) (y : M), ρ p (ρ q y) = ρ q (ρ p y) := by
    intro p q y
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hmul : ∀ (p q : Fin k → ℤ_[l]) (y : M),
      ρ (Multiplicative.ofAdd (p + q)) y = ρ (Multiplicative.ofAdd p) (ρ (Multiplicative.ofAdd q) y) := by
    intro p q y
    rw [ofAdd_add, map_mul, Module.End.mul_apply]
  let sh : ℕ → (Fin (n + 1) → Fin k → ℤ_[l]) → (Fin (n + 1) → Fin k → ℤ_[l]) :=
    fun t x j => x j - t • e
  let F : ℕ → (Fin (n + 1) → Fin k → ℤ_[l]) → M :=
    fun t x => ρ (Multiplicative.ofAdd (t • e)) (f (sh t x))
  have hF0 : ∀ x, F 0 x = f x := by
    intro x
    have h1 : sh 0 x = x := by funext j; simp [sh]
    simp [F, h1]
  have hFs : ∀ t x, ρ (Multiplicative.ofAdd e) (F t fun j => x j - e) = F (t + 1) x := by
    intro t x
    have h1 : sh t (fun j => x j - e) = sh (t + 1) x := by
      funext j
      simp only [sh, succ_nsmul]
      abel
    change ρ _ (ρ _ (f (sh t fun j => x j - e))) = ρ _ (f (sh (t + 1) x))
    rw [h1, succ_nsmul', hmul]
  have hE : (l ^ a) • e = (l : ℤ_[l]) ^ a • e := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    rfl
  have hper : ∀ t x, F (t + l ^ a) x = F t x := by
    intro t x
    have h1 := (ha e (sh (t + l ^ a) x)).1
    have h2 := (ha e (sh (t + l ^ a) x)).2
    have h3 : (fun s => (l : ℤ_[l]) ^ a • e + sh (t + l ^ a) x s) = sh t x := by
      funext s
      simp only [sh, add_nsmul, ← hE]
      abel
    rw [h3] at h1
    change ρ _ (f (sh (t + l ^ a) x)) = ρ _ (f (sh t x))
    rw [add_nsmul, hmul, hE, h2, h1]
  have hsum : ∀ x, ∑ t ∈ Finset.range (l ^ (a + c)), F (t + 1) x = 0 := by
    intro x
    rw [pow_add, sum_range_periodic (fun t => F (t + 1) x) (l ^ a)
      (fun t => by
        change F (t + l ^ a + 1) x = F (t + 1) x
        rw [add_right_comm]
        exact hper (t + 1) x) (l ^ c)]
    exact hc _
  haveI : NeZero (l ^ (a + c)) := ⟨pow_ne_zero _ hlpos.ne'⟩
  let z : (Fin (n + 1) → Fin k → ℤ_[l]) → ZMod (l ^ (a + c)) :=
    fun x => PadicInt.toZModPow (a + c) (x 0 i)
  have hz1 : ∀ x, z (fun j => x j - e) = z x - 1 := by
    intro x
    simp [z, he, map_sub]
  have hzj : ∀ j ∈ S, ∀ x, z (fun t => Pi.single j (1 : ℤ_[l]) + x t) = z x := by
    intro j hj x
    have hij : i ≠ j := fun h => hiS (h ▸ hj)
    simp [z, Pi.single_eq_of_ne hij]
  have hzl : IsLocallyConstant z := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have hb : Metric.closedBall (x 0 i) ((l : ℝ) ^ (-((a + c : ℕ) : ℤ))) ∈ nhds (x 0 i) :=
      Metric.closedBall_mem_nhds _ (zpow_pos (by exact_mod_cast hlpos) _)
    have hcont : Continuous (fun y : Fin (n + 1) → Fin k → ℤ_[l] => y 0 i) :=
      (continuous_apply i).comp (continuous_apply 0)
    filter_upwards [hcont.continuousAt.preimage_mem_nhds hb] with y hy
    have h1 : ‖y 0 i - x 0 i‖ ≤ (l : ℝ) ^ (-((a + c : ℕ) : ℤ)) := by
      simpa [dist_eq_norm] using hy
    have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 h1
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2
  have hFl : ∀ t, IsLocallyConstant (F t) := by
    intro t
    have hsh : Continuous (sh t) := continuous_pi fun j => (continuous_apply j).sub continuous_const
    exact (f.isLocallyConstant.comp_continuous hsh).comp _
  let gf : (Fin (n + 1) → Fin k → ℤ_[l]) → M :=
    fun x => -∑ t ∈ Finset.range ((z x).val + 1), F t x
  have hg : IsLocallyConstant gf := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h1 := (IsLocallyConstant.iff_eventually_eq _).1 hzl x
    have h2 : ∀ᶠ y in nhds x, ∀ t ∈ Finset.range ((z x).val + 1), F t y = F t x :=
      (Filter.eventually_all_finset _).2 fun t _ => (IsLocallyConstant.iff_eventually_eq _).1 (hFl t) x
    filter_upwards [h1, h2] with y hy1 hy2
    change -∑ t ∈ Finset.range ((z y).val + 1), F t y = -∑ t ∈ Finset.range ((z x).val + 1), F t x
    rw [hy1]
    exact congrArg _ (Finset.sum_congr rfl hy2)
  have hgE : ∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      gf (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (gf x) := by
    intro j hj x
    have hFj : ∀ t, F t (fun s => Pi.single j (1 : ℤ_[l]) + x s) =
        ρ (Multiplicative.ofAdd (Pi.single j 1)) (F t x) := by
      intro t
      have h1 : sh t (fun s => Pi.single j (1 : ℤ_[l]) + x s) =
          fun s => Pi.single j (1 : ℤ_[l]) + sh t x s := by
        funext s
        simp only [sh, add_sub_assoc]
      change ρ _ (f (sh t _)) = ρ _ (ρ _ (f (sh t x)))
      rw [h1, hf j hj, hcomm]
    simp only [gf]
    rw [hzj j hj x, map_neg, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun t _ => hFj t)
  have hgT : ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      ρ (Multiplicative.ofAdd e) (gf fun j => x j - e) - gf x = f x := by
    intro x
    simp only [gf]
    rw [map_neg, map_sum, hz1 x]
    simp only [hFs]
    obtain ⟨hne, h0⟩ := val_sub_one (z x)
    by_cases hx : (z x).val = 0
    · have hP := NeZero.pos (l ^ (a + c))
      rw [h0 hx, hx, Nat.sub_add_cancel hP, hsum x]
      simp [hF0]
    · rw [hne hx, Nat.sub_add_cancel (Nat.pos_of_ne_zero hx),
        Finset.sum_range_succ' (fun t => F t x) (z x).val, hF0]
      abel
  exact ⟨⟨gf, hg⟩, hgE, hgT⟩

end GlobalTheory.CompanionTheory.GrpOnto
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GrpMain

section
variable {R : Type} [CommRing R] {G : Type} [TopologicalSpace G] [AddCommGroup G]
  {M : Type w} [AddCommGroup M] [Module R M]

omit [TopologicalSpace G] in
theorem rho_comm (ρ : Multiplicative G →* (M →ₗ[R] M)) (g h : G) (x : M) :
    ρ (Multiplicative.ofAdd g) (ρ (Multiplicative.ofAdd h) x) =
      ρ (Multiplicative.ofAdd h) (ρ (Multiplicative.ofAdd g) x) := by
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

def shiftBy [IsTopologicalAddGroup G] (v : G) (n : ℕ) : C(Fin (n + 1) → G, Fin (n + 1) → G) :=
  ⟨fun x j => x j - v, by fun_prop⟩

def tw [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ) :
    (lcCos R G M).cx.X n →ₗ[R] (lcCos R G M).cx.X n where
  toFun f := LocallyConstant.map (ρ (Multiplicative.ofAdd v))
    (LocallyConstant.comap (shiftBy v n) f) - f
  map_add' f g := by
    refine LocallyConstant.ext fun x => ?_
    change ρ (Multiplicative.ofAdd v) (f _ + g _) - (f x + g x) =
      (ρ (Multiplicative.ofAdd v) (f _) - f x) + (ρ (Multiplicative.ofAdd v) (g _) - g x)
    rw [map_add]
    abel
  map_smul' c f := by
    refine LocallyConstant.ext fun x => ?_
    change ρ (Multiplicative.ofAdd v) (c • f _) - c • f x =
      c • (ρ (Multiplicative.ofAdd v) (f _) - f x)
    rw [map_smul, smul_sub]

theorem tw_apply [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ)
    (f : (lcCos R G M).cx.X n) (x : Fin (n + 1) → G) :
    tw ρ v n f x = ρ (Multiplicative.ofAdd v) (f fun j => x j - v) - f x := rfl

theorem tw_mem [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G)
    (n : ℕ) (f : (lcCos R G M).cx.X n) (hf : f ∈ eqv ρ S n) : tw ρ v n f ∈ eqv ρ S n := by
  intro g hg x
  have e : (fun j => (fun i => g + x i) j - v) = fun i => g + (fun j => x j - v) i := by
    funext i
    exact add_sub_assoc _ _ _
  rw [tw_apply, tw_apply, e, hf g hg, hf g hg, map_sub, rho_comm]

theorem tw_d [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ)
    (f : (lcCos R G M).cx.X n) :
    (lcCos R G M).d n (tw ρ v n f) = tw ρ v (n + 1) ((lcCos R G M).d n f) := by
  refine LocallyConstant.ext fun x => ?_
  rw [tw_apply, lc_d_apply, lc_d_apply, lc_d_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tw_apply, map_zsmul, smul_sub]

def twHom [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G) :
    Cx.Hom (grpCx ρ S) (grpCx ρ S) (RingHom.id R) where
  f n := (tw ρ v n).restrict fun f hf => tw_mem ρ S v n f hf
  comm n x := Subtype.ext (tw_d ρ v n x.1)

def Res (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (D : Submodule R M) (t : R) : Prop :=
  (∀ y ∈ eqv ρ S 0, (lcCos R G M).d 0 y = 0 → ∃ x ∈ D, t • y = LocallyConstant.const _ x) ∧
  ∀ n, ∀ y ∈ eqv ρ S (n + 1), (lcCos R G M).d (n + 1) y = 0 →
    ∃ x ∈ eqv ρ S n, (lcCos R G M).d n x = t • y

def invS (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) : Submodule R M where
  carrier := {x | ∀ g ∈ S, ρ (Multiplicative.ofAdd g) x = x}
  add_mem' {a b} ha hb g hg := by rw [map_add, ha g hg, hb g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c a ha g hg := by rw [map_smul, ha g hg]

def invB (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G) : invS ρ S →ₗ[R] invS ρ S :=
  (ρ (Multiplicative.ofAdd v) - LinearMap.id).restrict fun x hx g hg => by
    change ρ (Multiplicative.ofAdd g) (ρ (Multiplicative.ofAdd v) x - x) =
      ρ (Multiplicative.ofAdd v) x - x
    rw [map_sub, rho_comm, hx g hg]

theorem Res.congr (ρ : Multiplicative G →* (M →ₗ[R] M)) {S S' : Set G} (D : Submodule R M) (t : R)
    (h : ∀ n, eqv ρ S n = eqv ρ S' n) (hr : Res ρ S D t) : Res ρ S' D t := by
  have e : eqv ρ S = eqv ρ S' := funext h
  unfold Res at hr ⊢
  rw [← e]
  exact hr

end

def idx {k : ℕ} (e : Fin k ≃ Fin k) (i : ℕ) : Set (Fin k) := {j | ∃ a : Fin k, (a : ℕ) < i ∧ e a = j}

end GlobalTheory.CompanionTheory.GrpMain
end
