import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import BuildAid.ForwardExisting

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

universe w

variable {R : Type} [CommRing R]

structure DFil (K : DCx.{w} R) where
  L : ℤ → ∀ p q, Submodule R (K.X p q)
  mem_h : ∀ r p q x, x ∈ L r p q → K.dh p q x ∈ L r (p + 1) q
  mem_v : ∀ r p q x, x ∈ L r p q → K.dv p q x ∈ L r p (q + 1)
  anti : ∀ {r r' : ℤ}, r ≤ r' → ∀ p q, L r' p q ≤ L r p q

def DFil.Ex {K : DCx.{w} R} (F : DFil K) (r : ℤ) (p : ℕ) : ℕ → Prop
  | 0 => ∀ x ∈ F.L r p 0, K.dv p 0 x ∈ F.L (r + 1) p 1 → x ∈ F.L (r + 1) p 0
  | q + 1 => ∀ x ∈ F.L r p (q + 1), K.dv p (q + 1) x ∈ F.L (r + 1) p (q + 2) →
      ∃ v ∈ F.L r p q, x - K.dv p q v ∈ F.L (r + 1) p (q + 1)

variable {K : DCx.{w} R} (F : DFil K)

theorem sgl_mem {r : ℤ} {p q : ℕ} {x : K.X p q} (hx : x ∈ F.L r p q) (a b : ℕ) : K.sgl p q x a b ∈ F.L r a b := by
  by_cases h : a = p ∧ b = q
  · obtain ⟨rfl, rfl⟩ := h
    rwa [K.sgl_self]
  · rw [K.sgl_ne x (by omega)]
    exact zero_mem _

theorem dv_mem_of {r : ℤ} {e q : ℕ} (y : ∀ p q, K.X p q) (h1 : K.D y e (q + 1) ∈ F.L r e (q + 1))
    (h2 : ∀ e', e = e' + 1 → y e' (q + 1) ∈ F.L r e' (q + 1)) : K.dv e q (y e q) ∈ F.L r e (q + 1) := by
  have h3 : K.Dh y e (q + 1) ∈ F.L r e (q + 1) := by
    cases e with
    | zero => exact zero_mem _
    | succ e => exact F.mem_h _ _ _ _ (h2 e rfl)
  rw [K.D_apply] at h1
  have h4 : (-1 : ℤ) ^ e • K.dv e q (y e q) ∈ F.L r e (q + 1) := (Submodule.add_mem_iff_right _ h3).1 h1
  rcases neg_one_pow_eq_or ℤ e with h | h <;> rw [h] at h4 <;> simpa using h4

theorem kill (r : ℤ) (m : ℕ) (y : ∀ p q, K.X p q) (hy : y ∈ K.T (m + 1)) (hyL : ∀ p q, y p q ∈ F.L r p q) :
    ∀ e : ℕ, (∀ p q, p < e → K.D y p q ∈ F.L (r + 1) p q) → (∀ p q, p < e → p + q = m + 1 → F.Ex r p q) →
      ∃ w ∈ K.T m, (∀ p q, e ≤ p → w p q = 0) ∧ (∀ p q, (y - K.D w) p q ∈ F.L r p q) ∧
        ∀ p q, p < e → (y - K.D w) p q ∈ F.L (r + 1) p q := by
  intro e
  induction e with
  | zero =>
    intro _ _
    refine ⟨0, zero_mem _, fun _ _ _ => rfl, fun p q => ?_, fun p q h => absurd h (by omega)⟩
    simpa using hyL p q
  | succ e ih =>
    intro hD hE
    obtain ⟨w, hwT, hw0, hwL, hwL'⟩ := ih (fun p q hp => hD p q (by omega)) (fun p q hp => hE p q (by omega))
    have hyT : y - K.D w ∈ K.T (m + 1) := sub_mem hy (K.D_mem m w hwT)
    have hDy : K.D (y - K.D w) = K.D y := by rw [map_sub, K.DD, sub_zero]
    generalize hy' : y - K.D w = y' at hyT hDy hwL hwL'
    by_cases he : e ≤ m + 1
    · obtain ⟨q, hq⟩ : ∃ q, e + q = m + 1 := ⟨m + 1 - e, by omega⟩
      have hx : K.dv e q (y' e q) ∈ F.L (r + 1) e (q + 1) :=
        dv_mem_of F y' (by rw [hDy]; exact hD e (q + 1) (by omega)) (fun e' h => hwL' e' (q + 1) (by omega))
      have hEx := hE e q (by omega) hq
      cases q with
      | zero =>
        have hx0 : y' e 0 ∈ F.L (r + 1) e 0 := hEx _ (hwL e 0) hx
        refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
        rw [hy']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact hwL' p q hp
        · by_cases hq0 : q = 0
          · subst hq0; exact hx0
          · rw [hyT p q (by omega)]; exact zero_mem _
      | succ q =>
        obtain ⟨v, hv, hxv⟩ := hEx _ (hwL e (q + 1)) hx
        have hDu : K.D ((-1 : ℤ) ^ e • K.sgl e q v) =
            (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) + K.sgl e (q + 1) (K.dv e q v) := by
          rw [map_zsmul, K.D_sgl, smul_add, smul_smul, ← pow_add, ← two_mul, pow_mul]
          simp
        have hval : ∀ p q', (y - K.D (w + (-1 : ℤ) ^ e • K.sgl e q v)) p q' =
            y' p q' - (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) p q' - K.sgl e (q + 1) (K.dv e q v) p q' := by
          intro p q'
          rw [map_add, hDu, ← sub_sub, hy']
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          abel
        refine ⟨w + (-1 : ℤ) ^ e • K.sgl e q v, add_mem hwT (?_), fun p q' h => ?_, fun p q' => ?_, fun p q' hp => ?_⟩
        · refine (K.T m).smul_of_tower_mem _ ?_
          intro a b hab
          exact K.sgl_ne v (by omega)
        · simp only [Pi.add_apply, Pi.smul_apply]
          rw [hw0 p q' (by omega), K.sgl_ne v (Or.inl (by omega))]
          simp
        · rw [hval]
          exact sub_mem (sub_mem (hwL p q') ((F.L r p q').smul_of_tower_mem _ (sgl_mem F (F.mem_h _ _ _ _ hv) p q')))
            (sgl_mem F (F.mem_v _ _ _ _ hv) p q')
        · rw [hval]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
          · rw [K.sgl_ne _ (Or.inl (by omega)), K.sgl_ne _ (Or.inl (by omega))]
            simpa using hwL' p q' hp
          · rw [K.sgl_ne _ (Or.inl (by omega))]
            by_cases hq0 : q' = q + 1
            · subst hq0
              rw [K.sgl_self]
              simpa using hxv
            · rw [K.sgl_ne _ (Or.inr hq0), hyT p q' (by omega)]
              simp
    · refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
      rw [hy']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact hwL' p q hp
      · rw [hyT p q (by omega)]; exact zero_mem _

theorem stair_up (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) (r : ℕ) (hr : r ≤ n) :
    ∃ y ∈ K.T (2 * n + 1), K.D y = K.sgl (n + 1) (n + 1) P ∧ ∀ p q, y p q ∈ F.L (r : ℤ) p q := by
  induction r with
  | zero =>
    refine ⟨y0, hy0, hD, fun p q => ?_⟩
    rw [Nat.cast_zero, hTop]
    trivial
  | succ r ih =>
    obtain ⟨y, hyT, hDy, hyL⟩ := ih (by omega)
    have hPr : P ∈ F.L ((r : ℤ) + 1) (n + 1) (n + 1) := F.anti (by omega) _ _ hP
    obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (r : ℤ) (2 * n) y hyT hyL (n + 2)
      (fun p q _ => by rw [hDy]; exact sgl_mem F hPr p q)
      (fun p q hp hq => hE r p q (by omega))
    refine ⟨y - K.D w, sub_mem hyT (K.D_mem _ w hwT), by rw [map_sub, K.DD, sub_zero, hDy], fun p q => ?_⟩
    rw [Nat.cast_succ]
    by_cases hp : p < n + 2
    · exact hwL' p q hp
    · have := hV p q (by omega)
      rw [Subsingleton.elim ((y - K.D w) p q) 0]
      exact zero_mem _

theorem stair (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨y, hyT, hDy, hyL⟩ := stair_up F n hTop hV hE P hP y0 hy0 hD n le_rfl

  obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (n : ℤ) (2 * n) y hyT hyL (n + 1)
    (fun p q _ => by rw [hDy]; exact sgl_mem F hP p q) (fun p q hp hq => hE n p q (by omega))
  have hy1T : y - K.D w ∈ K.T (2 * n + 1) := sub_mem hyT (K.D_mem _ w hwT)
  have hDy1 : K.D (y - K.D w) = K.sgl (n + 1) (n + 1) P := by rw [map_sub, K.DD, sub_zero, hDy]
  generalize y - K.D w = y1 at hy1T hDy1 hwL hwL'

  have htT : y1 - K.sgl (n + 1) n (y1 (n + 1) n) ∈ K.T (2 * n + 1) :=
    sub_mem hy1T fun a b hab => K.sgl_ne _ (by omega)
  have hDt : K.D (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    have := hV (n + 2) n (by omega)
    rw [map_sub, K.D_sgl, hDy1, Subsingleton.elim (K.dh (n + 1) n (y1 (n + 1) n)) 0, map_zero, zero_add, map_sub, map_zsmul]
  have htL : ∀ p q, (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) p q ∈ F.L ((n : ℤ) + 1) p q := by
    intro p q
    rw [Pi.sub_apply, Pi.sub_apply]
    by_cases hp : p < n + 1
    · rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
      exact hwL' p q hp
    · by_cases hp' : p = n + 1
      · subst hp'
        by_cases hq : q = n
        · subst hq
          rw [K.sgl_self, sub_self]
          exact zero_mem _
        · rw [K.sgl_ne _ (Or.inr hq), hy1T _ _ (by omega), sub_zero]
          exact zero_mem _
      · have := hV p q (by omega)
        rw [Subsingleton.elim (y1 p q - K.sgl (n + 1) n (y1 (n + 1) n) p q) 0]
        exact zero_mem _
  have ecast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; rfl
  obtain ⟨w2, hw2T, hw20, hw2L, hw2L'⟩ := kill F ((n : ℤ) + 1) (2 * n) _ htT htL n
    (fun p q hp => by
      rw [hDt, K.sgl_ne _ (Or.inl (by omega))]
      exact zero_mem _)
    (fun p q hp hq => by
      have := hE (n + 1) p q (by omega)
      rwa [ecast] at this)
  have hDt' : K.D ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    rw [map_sub, K.DD, sub_zero, hDt]
  have ht0 : ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) (n + 1) n = 0 := by
    have h1 : K.D w2 (n + 1) n = 0 := by
      rw [K.D_apply]
      have h2 : K.Dv w2 (n + 1) n = 0 := by
        cases n with
        | zero => rfl
        | succ n =>
          show K.dv (n + 1 + 1) n (w2 (n + 1 + 1) n) = 0
          rw [hw20 _ _ (by omega), map_zero]
      have h3 : K.Dh w2 (n + 1) n = 0 := by
        show K.dh n n (w2 n n) = 0
        rw [hw20 _ _ le_rfl, map_zero]
      rw [h2, h3]; simp
    show (y1 (n + 1) n - K.sgl (n + 1) n (y1 (n + 1) n) (n + 1) n) - K.D w2 (n + 1) n = 0
    rw [h1, K.sgl_self]
    simp
  generalize (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2 = t at hDt' ht0 hw2L hw2L'
  refine ⟨t n (n + 1), y1 (n + 1) n, hw2L _ _, ?_, hwL _ _, ?_⟩
  · refine dv_mem_of F t ?_ (fun e' h => hw2L' e' _ (by omega))
    rw [hDt', K.sgl_ne _ (Or.inl (by omega))]
    exact zero_mem _
  · have h := congrFun (congrFun hDt' (n + 1)) (n + 1)
    rw [K.sgl_self, K.D_apply] at h
    have h2 : K.Dv t (n + 1) (n + 1) = 0 := by
      show K.dv (n + 1) n (t (n + 1) n) = 0
      rw [ht0, map_zero]
    rw [h2, smul_zero, add_zero] at h
    have h3 : K.Dh t (n + 1) (n + 1) = K.dh n (n + 1) (t n (n + 1)) := rfl
    rw [← h3, h]
    abel

end GlobalTheory.CompanionTheory.ConeCech
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

universe w

variable {R : Type} [CommRing R]

def shift {K : DCx.{w} R} (B : ∀ p q, K.X p q →ₗ[R] K.X (p + 1) (q + 1)) (x : ∀ p q, K.X p q) : ∀ p q, K.X p q
  | 0, _ => 0
  | _ + 1, 0 => 0
  | p + 1, q + 1 => (-1 : ℤ) ^ q • B p q (x p q)

variable {K : DCx.{w} R} (B : ∀ p q, K.X p q →ₗ[R] K.X (p + 1) (q + 1))

theorem shift_sub (x y : ∀ p q, K.X p q) : shift B (x - y) = shift B x - shift B y := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift, smul_sub]

theorem shift_zero : shift B (0 : ∀ p q, K.X p q) = 0 := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift]

theorem shift_add (x y : ∀ p q, K.X p q) : shift B (x + y) = shift B x + shift B y := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift, smul_add]

theorem shift_sgl (p q : ℕ) (x : K.X p q) :
    shift B (K.sgl p q x) = (-1 : ℤ) ^ q • K.sgl (p + 1) (q + 1) (B p q x) := by
  funext a b
  rcases a with _ | a
  · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (Or.inl (by omega))]
    simp [shift]
  · rcases b with _ | b
    · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (Or.inr (by omega))]
      simp [shift]
    · by_cases h : a = p ∧ b = q
      · obtain ⟨rfl, rfl⟩ := h
        simp only [shift, Pi.smul_apply, K.sgl_self]
      · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (by omega)]
        simp only [shift]
        rw [K.sgl_ne _ (by omega)]
        simp

theorem D_shift (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x)) (x : ∀ p q, K.X p q) :
    K.D (shift B x) = shift B (K.D x) := by
  funext p q
  rw [K.D_apply]
  rcases p with _ | p
  · rcases q with _ | q <;> simp [DCx.Dh, DCx.Dv, shift]
  · rcases q with _ | q
    · rcases p with _ | p <;> simp [DCx.Dh, DCx.Dv, shift]
    · have h1 : K.Dh (shift B x) (p + 1) (q + 1) = (-1 : ℤ) ^ q • B p q (K.Dh x p q) := by
        rcases p with _ | p
        · simp [DCx.Dh, shift]
        · simp [DCx.Dh, shift, hh]
      have h2 : K.Dv (shift B x) (p + 1) (q + 1) = (-1 : ℤ) ^ (q + 1) • B p q (K.Dv x p q) := by
        rcases q with _ | q
        · simp [DCx.Dv, shift]
        · simp only [DCx.Dv, shift, map_zsmul, hv]
          rw [pow_succ, pow_succ]
          simp
      rw [h1, h2]
      show _ = (-1 : ℤ) ^ q • B p q (K.D x p q)
      rw [K.D_apply, map_add, map_zsmul, smul_add, smul_smul, smul_smul, pow_succ, pow_succ]
      congr 2
      ring

theorem cone_zigzag_compat (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x))
    (a : ∀ k, K.X 0 (2 * k)) (g : ∀ k, K.X 0 (2 * k + 1)) (P : ∀ k, K.X k k)
    (hg1 : ∀ k, K.dv 0 (2 * k + 1) (g k) = a (k + 1))
    (hg2 : ∀ k, K.dh 0 (2 * k + 1) (g k) = - B 0 (2 * k) (a k))
    (hP0 : P 0 = a 0) (hPs : ∀ k, P (k + 1) = (-1 : ℤ) ^ k • B k k (P k)) (k : ℕ) :
    ∃ U : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ 2 * k → U p q = 0) ∧
      K.D U = K.sgl 0 (2 * k) (a k) - K.sgl k k (P k) := by
  induction k with
  | zero =>
    refine ⟨0, fun _ _ _ => rfl, ?_⟩
    rw [map_zero, hP0]
    exact (sub_self _).symm
  | succ k ih =>
    obtain ⟨U, hU, hDU⟩ := ih
    refine ⟨shift B U + K.sgl 0 (2 * k + 1) (g k), fun p q h => ?_, ?_⟩
    · rw [Pi.add_apply, Pi.add_apply, K.sgl_ne _ (by omega), add_zero]
      rcases p with _ | p
      · rfl
      · rcases q with _ | q
        · rfl
        · simp only [shift]
          rw [hU p q (by omega)]
          simp
    · rw [map_add, D_shift B hh hv, hDU, shift_sub, shift_sgl, shift_sgl, K.D_sgl, hg1, hg2, hPs, map_neg, map_zsmul]
      have e : ((-1 : ℤ) ^ (2 * k)) = 1 := by rw [pow_mul]; simp
      rw [e, one_smul, pow_zero, one_smul]
      have e2 : K.sgl 0 (2 * k + 1 + 1) (a (k + 1)) = K.sgl 0 (2 * (k + 1)) (a (k + 1)) := rfl
      rw [e2]
      abel

theorem zig_stair (F : GlobalTheory.CompanionTheory.ConeCech.DFil K) (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤)
    (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q)) (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q)
    (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x))
    (a : ∀ k, K.X 0 (2 * k)) (g : ∀ k, K.X 0 (2 * k + 1)) (P : ∀ k, K.X k k)
    (hg1 : ∀ k, K.dv 0 (2 * k + 1) (g k) = a (k + 1))
    (hg2 : ∀ k, K.dh 0 (2 * k + 1) (g k) = - B 0 (2 * k) (a k))
    (hP0 : P 0 = a 0) (hPs : ∀ k, P (k + 1) = (-1 : ℤ) ^ k • B k k (P k))
    (hP : P (n + 1) ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (v : K.X 0 (2 * n + 1)) (hv1 : K.dv 0 (2 * n + 1) v = a (n + 1)) (hv2 : K.dh 0 (2 * n + 1) v = 0) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P (n + 1) = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨U, hU, hDU⟩ := cone_zigzag_compat B hh hv a g P hg1 hg2 hP0 hPs (n + 1)
  refine GlobalTheory.CompanionTheory.ConeCech.stair F n hTop hV hE (P (n + 1)) hP (K.sgl 0 (2 * n + 1) v - U) ?_ ?_
  · refine sub_mem (fun p q h => K.sgl_ne _ (by omega)) (fun p q h => hU p q (by omega))
  · rw [map_sub, hDU, K.D_sgl, hv1, hv2, map_zero, zero_add, pow_zero, one_smul]
    have e2 : K.sgl 0 (2 * n + 1 + 1) (a (n + 1)) = K.sgl 0 (2 * (n + 1)) (a (n + 1)) := rfl
    rw [e2]
    abel

end GlobalTheory.CompanionTheory.ConeZig
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)

abbrev Ch (U : ObjectProperty C) (q : ℕ) : Type 1 := CH.Cn (CH.modF (U.ι ⋙ A)) q

def rM {U V : ObjectProperty C} (h : V ≤ U) :
    CH.Mor (CH.modF (U.ι ⋙ A)) (CH.modF (V.ι ⋙ A)) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

variable {A}

theorem d_resB {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (x : Ch A U k) :
    CH.d _ k (resB A h x) = resB A h (CH.d _ k x) := (rM A h).d_pullC k x

theorem resB_resB {U V T : ObjectProperty C} (h : V ≤ U) (h' : T ≤ V) (h'' : T ≤ U) {k : ℕ} (x : Ch A U k) :
    resB A h' (resB A h x) = resB A h'' x := rfl

theorem resB_sub {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (x y : Ch A U k) :
    resB A h (x - y) = resB A h x - resB A h y := map_sub ((rM A h).pullC k) x y

def Lm (a : IdF A) (U : ObjectProperty C) (q : ℕ) : Submodule R (Ch A U q) where
  carrier := {x | ∀ σ, x σ ∈ a.S _}
  add_mem' hx hy σ := (a.S _).add_mem (hx σ) (hy σ)
  zero_mem' σ := (a.S _).zero_mem
  smul_mem' r x hx σ := by
    change r • x σ ∈ a.S _
    exact Submodule.smul_of_tower_mem (a.S _) r (hx σ)

theorem Lm_d {a : IdF A} {U : ObjectProperty C} {q : ℕ} {x : Ch A U q} (hx : x ∈ Lm a U q) :
    CH.d _ q x ∈ Lm a U (q + 1) := by
  intro σ
  change ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • _ ∈ a.S _
  refine (a.S _).sum_mem fun i _ => ?_
  exact Submodule.smul_of_tower_mem (a.S _) _ (a.map_mem _ (hx _))

theorem Lm_res {a : IdF A} {U V : ObjectProperty C} (h : V ≤ U) {q : ℕ} {x : Ch A U q} (hx : x ∈ Lm a U q) :
    resB A h x ∈ Lm a V q := fun σ => hx (σ ⋙ ObjectProperty.ιOfLE h)

theorem Lm_le {a b : IdF A} (hab : ∀ T, a.S T ≤ b.S T) {U : ObjectProperty C} {q : ℕ} {x : Ch A U q}
    (hx : x ∈ Lm a U q) : x ∈ Lm b U q := fun σ => hab _ (hx σ)

theorem Lm_cup {a b c : IdF A} (habc : ∀ (T : C) (x y : A.obj T), x ∈ a.S T → y ∈ b.S T → x * y ∈ c.S T)
    {U : ObjectProperty C} {p q n : ℕ} (e : p + q = n) {x : Ch A U p} {y : Ch A U q}
    (hx : x ∈ Lm a U p) (hy : y ∈ Lm b U q) : (CH.mulP (U.ι ⋙ A)).cupC e x y ∈ Lm c U n := by
  intro σ
  exact habc _ _ _ (a.map_mem _ (hx ((CH.front_mono e).functor ⋙ σ))) (b.map_mem _ (hy ((CH.back_mono e).functor ⋙ σ)))

variable {N : ℕ} (W : Fin N → ObjectProperty C)

def fc {p : ℕ} (k : Fin (p + 2)) (i : Idx (p + 2) N) : Idx (p + 1) N :=
  ⟨i.1 ∘ k.succAbove, i.2.comp (Fin.strictMono_succAbove k)⟩

theorem cap_le {p : ℕ} (k : Fin (p + 2)) (i : Idx (p + 2) N) : capT W i.1 ≤ capT W (fc k i).1 :=
  fun _ h _ => h _

theorem x_congr {ι : Type} {f : ι → ObjectProperty C} {V : ObjectProperty C} {q : ℕ} (x : ∀ i, Ch A (f i) q)
    {i i' : ι} (e : i = i') (h : V ≤ f i) (h' : V ≤ f i') : resB A h (x i) = resB A h' (x i') := by
  subst e; rfl

variable (A)

def cosK : CosCx.{1} R where
  K p :=
    { X := fun q => ∀ i : Idx (p + 1) N, Ch A (capT W i.1) q
      d := fun q => LinearMap.pi fun i => (CH.d _ q).comp (LinearMap.proj i)
      dd := fun q x => funext fun i => CH.d_d _ q (x i) }
  δ p k := ⟨fun q => LinearMap.pi fun i => ((rM A (cap_le W k i)).pullC q).comp (LinearMap.proj (fc k i)),
    fun q x => funext fun i => (rM A (cap_le W k i)).d_pullC q (x (fc k i))⟩
  rel p j t q x := by
    funext i
    have e : fc (t.predAbove j) (fc (j.succAbove t) i) = fc t (fc j i) :=
      Subtype.ext (funext fun k => congrArg i.1 (Fin.succAbove_succAbove_succAbove_predAbove j t k))
    exact x_congr (f := fun i : Idx (p + 1) N => capT W i.1) x e (fun _ h _ => h _) (fun _ h _ => h _)

abbrev KK : DCx.{1} R := (cosK A W).dcx

variable {A W}

theorem dv_apply {p q : ℕ} (x : (KK A W).X p q) (i : Idx (p + 1) N) : (KK A W).dv p q x i = CH.d _ q (x i) := rfl

theorem dh_apply {p q : ℕ} (x : (KK A W).X p q) (i : Idx (p + 2) N) :
    (KK A W).dh p q x i = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • resB A (cap_le W k i) (x (fc k i)) := by
  refine (congrFun (Cos.d_apply ((cosK A W).cos q) p x) i).trans ?_
  rw [Finset.sum_apply]
  rfl

def dfil (Fil : ℤ → IdF A) (hanti : ∀ {r r' : ℤ}, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T) :
    GlobalTheory.CompanionTheory.ConeCech.DFil (KK A W) where
  L r p q := Submodule.pi Set.univ fun i : Idx (p + 1) N => Lm (Fil r) (capT W i.1) q
  mem_h r p q x hx i _ := by
    rw [dh_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Lm_res _ (hx _ trivial))
  mem_v r p q x hx i _ := Lm_d (hx i trivial)
  anti h p q x hx i _ := Lm_le (hanti h) (hx i trivial)

end GlobalTheory.CompanionTheory.ConeZig

namespace GlobalTheory.CompanionTheory.ConeZig

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def bm {U V : ObjectProperty C} (h : V ≤ U) (l : Ch A V 1) (q : ℕ) : Ch A U q →ₗ[R] Ch A V (q + 1) :=
  ((CH.mulP (V.ι ⋙ A)).cupC (rfl : q + 1 = q + 1)).flip l ∘ₗ (rM A h).pullC q

theorem bm_apply {U V : ObjectProperty C} (h : V ≤ U) (l : Ch A V 1) {q : ℕ} (x : Ch A U q) :
    bm h l q x = (CH.mulP (V.ι ⋙ A)).cupC rfl (resB A h x) l := rfl

theorem res_bm {U V T : ObjectProperty C} (h : V ≤ U) (h' : T ≤ V) (h'' : T ≤ U) (l : Ch A V 1) {q : ℕ} (x : Ch A U q) :
    resB A h' (bm h l q x) = bm h'' (resB A h' l) q x := rfl

theorem bm_add {U V : ObjectProperty C} (h : V ≤ U) (l l' : Ch A V 1) {q : ℕ} (x : Ch A U q) :
    bm h (l + l') q x = bm h l q x + bm h l' q x := by
  simp only [bm_apply, map_add]

theorem bm_congr {ι : Type} {f : ι → ObjectProperty C} {V : ObjectProperty C} {q : ℕ} (x : ∀ i, Ch A (f i) q)
    {i i' : ι} (e : i = i') (h : V ≤ f i) (h' : V ≤ f i') (l : Ch A V 1) : bm h l q (x i) = bm h' l q (x i') := by
  subst e; rfl

variable {N : ℕ} {W : Fin N → ObjectProperty C} (b : ∀ α, Ch A (W α) 1)

theorem capT_at {m : ℕ} (i : Idx m N) (a : Fin m) : capT W i.1 ≤ W (i.1 a) := fun _ h => h a

def LL {m : ℕ} (i : Idx m N) (a c : Fin m) : Ch A (capT W i.1) 1 :=
  resB A (capT_at i a) (b (i.1 a)) - resB A (capT_at i c) (b (i.1 c))

theorem LL_add {m : ℕ} (i : Idx m N) (a c e : Fin m) : LL b i a c = LL b i a e + LL b i e c := by
  simp only [LL]; abel

theorem res_LL {m m' : ℕ} (i : Idx m N) (i' : Idx m' N) (h : capT W i.1 ≤ capT W i'.1) (a' c' : Fin m') (a c : Fin m)
    (ha : i'.1 a' = i.1 a) (hc : i'.1 c' = i.1 c) : resB A h (LL b i' a' c') = LL b i a c := by
  rw [LL, LL, resB_sub, resB_resB _ _ (h.trans (capT_at i' a')), resB_resB _ _ (h.trans (capT_at i' c'))]
  exact congrArg₂ (· - ·) (x_congr b ha _ _) (x_congr b hc _ _)

def BB (p q : ℕ) : (KK A W).X p q →ₗ[R] (KK A W).X (p + 1) (q + 1) :=
  LinearMap.pi fun i : Idx (p + 2) N => bm (cap_le W (Fin.last (p + 1)) i)
    (LL b i (Fin.last p).castSucc (Fin.last (p + 1))) q ∘ₗ LinearMap.proj (fc (Fin.last (p + 1)) i)

theorem BB_apply {p q : ℕ} (x : (KK A W).X p q) (i : Idx (p + 2) N) :
    BB b p q x i = bm (cap_le W (Fin.last (p + 1)) i) (LL b i (Fin.last p).castSucc (Fin.last (p + 1))) q
      (x (fc (Fin.last (p + 1)) i)) := rfl

theorem neg_one_smul_cancel {M : Type*} [AddCommGroup M] (s : ℤ) (X Y : M) :
    (s * -1) • X + (s * -1) • Y + (s * -1 * -1) • X = (s * -1) • Y := by
  have e : (s * -1 * -1) • X = - ((s * -1) • X) := by rw [mul_neg_one, mul_neg_one, neg_neg, neg_smul, neg_neg]
  rw [e]; abel

theorem BB_dh (p q : ℕ) (x : (KK A W).X p q) :
    (KK A W).dh (p + 1) (q + 1) (BB b p q x) = BB b (p + 1) q ((KK A W).dh p q x) := by
  funext i
  rw [dh_apply, BB_apply, dh_apply, map_sum]
  have hS : ∀ k : Fin (p + 2), bm (cap_le W (Fin.last (p + 2)) i)
      (LL b i (Fin.last (p + 1)).castSucc (Fin.last (p + 2))) q
      ((-1 : ℤ) ^ (k : ℕ) • resB A (cap_le W k (fc (Fin.last (p + 2)) i)) (x (fc k (fc (Fin.last (p + 2)) i)))) =
      (-1 : ℤ) ^ (k : ℕ) • bm (fun _ h _ => h _) (LL b i (Fin.last (p + 1)).castSucc (Fin.last (p + 2))) q
        (x (fc k (fc (Fin.last (p + 2)) i))) := fun k => by rw [map_zsmul]; rfl
  have h1 : ∀ j : Fin (p + 1), resB A (cap_le W j.castSucc.castSucc i) (BB b p q x (fc j.castSucc.castSucc i)) =
      bm (fun _ h _ => h _) (LL b i (Fin.last (p + 1)).castSucc (Fin.last (p + 2))) q
        (x (fc j.castSucc (fc (Fin.last (p + 2)) i))) := by
    intro j
    have e : fc (Fin.last (p + 1)) (fc j.castSucc.castSucc i) = fc j.castSucc (fc (Fin.last (p + 2)) i) := by
      refine Subtype.ext (funext fun t => congrArg i.1 ?_)
      have := j.2
      have := t.2
      apply Fin.ext
      simp only [Function.comp, CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have ha : (fc j.castSucc.castSucc i).1 (Fin.last p).castSucc = i.1 (Fin.last (p + 1)).castSucc := by
      refine congrArg i.1 ?_
      have := j.2
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have hc : (fc j.castSucc.castSucc i).1 (Fin.last (p + 1)) = i.1 (Fin.last (p + 2)) := by
      refine congrArg i.1 ?_
      have := j.2
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    rw [BB_apply, res_bm _ _ (fun _ h _ => h _), res_LL b i _ _ _ _ _ _ ha hc]
    exact bm_congr (f := fun i : Idx (p + 1) N => capT W i.1) x e _ _ _
  have h2 : resB A (cap_le W (Fin.last (p + 1)).castSucc i) (BB b p q x (fc (Fin.last (p + 1)).castSucc i)) =
      bm (fun _ h _ => h _) (LL b i (Fin.last p).castSucc.castSucc (Fin.last (p + 2))) q
        (x (fc (Fin.last (p + 1)) (fc (Fin.last (p + 2)) i))) := by
    have e : fc (Fin.last (p + 1)) (fc (Fin.last (p + 1)).castSucc i) = fc (Fin.last (p + 1)) (fc (Fin.last (p + 2)) i) := by
      refine Subtype.ext (funext fun t => congrArg i.1 ?_)
      have := t.2
      apply Fin.ext
      simp only [Function.comp, CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have ha : (fc (Fin.last (p + 1)).castSucc i).1 (Fin.last p).castSucc = i.1 (Fin.last p).castSucc.castSucc := by
      refine congrArg i.1 ?_
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have hc : (fc (Fin.last (p + 1)).castSucc i).1 (Fin.last (p + 1)) = i.1 (Fin.last (p + 2)) := by
      refine congrArg i.1 ?_
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    rw [BB_apply, res_bm _ _ (fun _ h _ => h _), res_LL b i _ _ _ _ _ _ ha hc]
    exact bm_congr (f := fun i : Idx (p + 1) N => capT W i.1) x e _ _ _
  have h3 : resB A (cap_le W (Fin.last (p + 2)) i) (BB b p q x (fc (Fin.last (p + 2)) i)) =
      bm (fun _ h _ => h _) (LL b i (Fin.last p).castSucc.castSucc (Fin.last (p + 1)).castSucc) q
        (x (fc (Fin.last (p + 1)) (fc (Fin.last (p + 2)) i))) := by
    have ha : (fc (Fin.last (p + 2)) i).1 (Fin.last p).castSucc = i.1 (Fin.last p).castSucc.castSucc := by
      refine congrArg i.1 ?_
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have hc : (fc (Fin.last (p + 2)) i).1 (Fin.last (p + 1)) = i.1 (Fin.last (p + 1)).castSucc := by
      refine congrArg i.1 ?_
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    rw [BB_apply, res_bm _ _ (fun _ h _ => h _), res_LL b i _ _ _ _ _ _ ha hc]
  simp only [hS]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (n := p + 1)]
  refine (add_assoc _ _ _).trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_) ?_)
  · rw [h1]; rfl
  · rw [h2, h3, LL_add b i (Fin.last p).castSucc.castSucc (Fin.last (p + 2)) (Fin.last (p + 1)).castSucc, bm_add]
    simp only [Fin.val_castSucc, Fin.val_last, smul_add, pow_succ]
    exact neg_one_smul_cancel _ _ _

variable {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch A V 2)

theorem d_LL (hb : ∀ α, resB A (hWV α) z = CH.d _ 1 (b α)) {m : ℕ} (i : Idx m N) (a c : Fin m) :
    CH.d _ 1 (LL b i a c) = 0 := by
  rw [LL, map_sub, d_resB, d_resB, ← hb, ← hb]
  exact sub_self _

theorem BB_dv (hb : ∀ α, resB A (hWV α) z = CH.d _ 1 (b α)) (p q : ℕ) (x : (KK A W).X p q) :
    (KK A W).dv (p + 1) (q + 1) (BB b p q x) = BB b p (q + 1) ((KK A W).dv p q x) := by
  funext i
  rw [dv_apply, BB_apply, BB_apply, bm_apply, bm_apply, CrystallineSemistableComparison.P.leibniz, d_LL b hWV z hb, map_zero, smul_zero, add_zero,
    d_resB]
  rfl

theorem capV (hW : ∀ α, W α ≤ V) {p : ℕ} (i : Idx (p + 1) N) : capT W i.1 ≤ V := (capT_at i 0).trans (hW _)

def aa (k : ℕ) : (KK A W).X 0 (2 * k) := fun i => resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k)

def gg (k : ℕ) : (KK A W).X 0 (2 * k + 1) := fun i =>
  (CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k)) (resB A (capT_at i 0) (b (i.1 0)))

def PP (k : ℕ) : (KK A W).X k k :=
  Nat.rec (motive := fun k => (KK A W).X k k) (aa hWV z 0) (fun k y => (-1 : ℤ) ^ k • BB b k k y) k

theorem cupPow_d (A' : (V.FullSubcategory) ⥤ CommAlgCat.{0} R) (z : CH.Cn (CH.modF A') 2) (hz : CH.d _ 2 z = 0) (k : ℕ) :
    CH.d _ (2 * k) (cupPowC A' z k) = 0 := by
  induction k with
  | zero =>
    funext s
    change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A'.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A'.obj _)
    rw [Fin.sum_univ_two, map_one, map_one]
    simp
  | succ k ih =>
    change CH.d _ _ ((CH.mulP A').cupC _ (cupPowC A' z k) z) = 0
    rw [CrystallineSemistableComparison.P.leibniz, ih, hz]
    simp

theorem gg_dv (hz : CH.d _ 2 z = 0) (hb : ∀ α, resB A (hWV α) z = CH.d _ 1 (b α)) (k : ℕ) :
    (KK A W).dv 0 (2 * k + 1) (gg b hWV z k) = aa hWV z (k + 1) := by
  funext i
  rw [dv_apply]
  change CH.d _ _ ((CH.mulP _).cupC _ _ _) = _
  rw [CrystallineSemistableComparison.P.leibniz, d_resB, cupPow_d _ z hz, d_resB, ← hb]
  have e : ((-1 : ℤ) ^ (2 * k)) = 1 := by rw [pow_mul]; simp
  rw [e, one_smul]
  have h0 : resB A (capV hWV i) (0 : Ch A V (2 * k + 1)) = 0 := map_zero ((rM A (capV hWV i)).pullC _)
  rw [h0, map_zero, LinearMap.zero_apply]
  exact zero_add _

theorem gg_dh (k : ℕ) : (KK A W).dh 0 (2 * k + 1) (gg b hWV z k) = - BB b 0 (2 * k) (aa hWV z k) := by
  funext i
  rw [dh_apply, Fin.sum_univ_two]
  have h0 : resB A (cap_le W 0 i) (gg b hWV z k (fc 0 i)) = (CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k))
      (resB A (capT_at i 1) (b (i.1 1))) := by
    have e : (fc 0 i).1 0 = i.1 1 := rfl
    have e' := x_congr b e (V := capT W i.1) (fun _ h => h _) (capT_at i 1)
    exact congrArg ((CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k))) e'
  have h1 : resB A (cap_le W 1 i) (gg b hWV z k (fc 1 i)) = (CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k))
      (resB A (capT_at i 0) (b (i.1 0))) := by
    have e : (fc 1 i).1 0 = i.1 0 := rfl
    have e' := x_congr b e (V := capT W i.1) (fun _ h => h _) (capT_at i 0)
    exact congrArg ((CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k))) e'
  have hL : LL b i (Fin.last 0).castSucc (Fin.last 1) = resB A (capT_at i 0) (b (i.1 0)) - resB A (capT_at i 1) (b (i.1 1)) := rfl
  rw [h0, h1, Pi.neg_apply, BB_apply, hL, bm_apply]
  have hy : resB A (cap_le W (Fin.last 1) i) (aa hWV z k (fc (Fin.last 1) i)) = resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k) := rfl
  rw [hy, map_sub]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  abel

end GlobalTheory.CompanionTheory.ConeZig
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

section SQ

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] {A : D ⥤ CommAlgCat.{0} R} (a b : IdF A)

def vl (T : D) : (sq a b).obj T →+ A.obj T ⧸ b.S T := (sqM a b T).subtype.toAddMonoidHom

def mk2 (T : D) : (CH.modF A).obj T →+ A.obj T ⧸ b.S T := (Ideal.Quotient.mk (b.S T)).toAddMonoidHom

def gC {q : ℕ} (x : CH.Cn (CH.modF A) q) (hx : ∀ s, x s ∈ a.S _) : CH.Cn (sq a b) q := fun s => sqMk a b (x s) (hx s)

variable {a b}

theorem mk2_eq_zero_iff_mem_S {T : D} (x : (CH.modF A).obj T) : mk2 b T x = 0 ↔ x ∈ b.S T := Ideal.Quotient.eq_zero_iff_mem

theorem map_val {T T' : D} (φ : T ⟶ T') (y : (sq a b).obj T) (x : (CH.modF A).obj T) (h : vl a b T y = mk2 b T x) :
    vl a b T' (((sq a b).map φ).hom y) = mk2 b T' (((CH.modF A).map φ).hom x) := by
  obtain ⟨y, hy⟩ := y
  have h' : y = mk2 b T x := h
  subst h'
  rfl

theorem d_val {q : ℕ} (f : CH.Cn (sq a b) q) (x : CH.Cn (CH.modF A) q)
    (h : ∀ s, vl a b _ (f s) = mk2 b _ (x s)) (s : ComposableArrows D (q + 1)) :
    vl a b _ (CH.d _ q f s) = mk2 b _ (CH.d _ q x s) := by
  change vl a b _ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (GlobalTheory.CatH.toLast i s)).hom (f (GlobalTheory.CatH.face i s))) =
    mk2 b _ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((CH.modF A).map (GlobalTheory.CatH.toLast i s)).hom (x (GlobalTheory.CatH.face i s)))
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, map_val _ _ _ (h _)]

theorem lift_C {q : ℕ} (f : CH.Cn (sq a b) q) : ∃ x : CH.Cn (CH.modF A) q, (∀ s, x s ∈ a.S _) ∧
    ∀ s, vl a b _ (f s) = mk2 b _ (x s) := by
  have h : ∀ s, ∃ y : (CH.modF A).obj (s.obj (Fin.last q)), y ∈ a.S _ ∧ vl a b _ (f s) = mk2 b _ y := by
    intro s
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from f s).2
    exact ⟨y, hy, e.symm⟩
  choose x hx hx' using h
  exact ⟨x, hx, hx'⟩

theorem vl_inj {T : D} {y y' : (sq a b).obj T} (h : vl a b T y = vl a b T y') : y = y' := Subtype.ext h

theorem gC_d {q : ℕ} (x : CH.Cn (CH.modF A) q) (hx : ∀ s, x s ∈ a.S _) (hd : ∀ s, CH.d _ q x s ∈ b.S _) :
    CH.d _ q (gC a b x hx) = 0 := by
  funext s
  refine vl_inj ?_
  rw [d_val _ x (fun _ => rfl) s, (mk2_eq_zero_iff_mem_S _).2 (hd s)]
  exact (map_zero (vl a b _)).symm

theorem ex_zero (hH : Subsingleton (CH.H (sq a b) 0)) (x : CH.Cn (CH.modF A) 0) (hx : ∀ s, x s ∈ a.S _)
    (hd : ∀ s, CH.d _ 0 x s ∈ b.S _) (s) : x s ∈ b.S _ := by
  have h0 := gC_d x hx hd
  have h1 : (CH.cx (sq a b)).cls (gC a b x hx) h0 = 0 := Subsingleton.elim _ _
  have h2 : gC a b x hx = 0 := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) 0).2.1 _ h0).1 h1
  have h3 : vl a b _ (gC a b x hx s) = 0 := by rw [h2]; exact map_zero (vl a b _)
  exact (mk2_eq_zero_iff_mem_S _).1 h3

theorem ex_succ {q : ℕ} (hH : Subsingleton (CH.H (sq a b) (q + 1))) (x : CH.Cn (CH.modF A) (q + 1))
    (hx : ∀ s, x s ∈ a.S _) (hd : ∀ s, CH.d _ (q + 1) x s ∈ b.S _) :
    ∃ v : CH.Cn (CH.modF A) q, (∀ s, v s ∈ a.S _) ∧ ∀ s, (x - CH.d _ q v) s ∈ b.S _ := by
  have h0 := gC_d x hx hd
  have h1 : (CH.cx (sq a b)).cls (gC a b x hx) h0 = 0 := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) (q + 1)).2.1 _ h0).1 h1
  obtain ⟨v, hv, hv'⟩ := lift_C u
  refine ⟨v, hv, fun s => ?_⟩
  have h3 := d_val u v hv' s
  have h4 : vl a b _ (CH.d _ q u s) = mk2 b _ (x s) :=
    congrArg (fun y : CH.Cn (sq a b) (q + 1) => vl a b _ (y s)) hu
  rw [h4] at h3
  refine (mk2_eq_zero_iff_mem_S _).1 ?_
  change mk2 b _ (x s - CH.d _ q v s) = 0
  rw [map_sub, h3, sub_self]

theorem cls_sub_sum {K : Cx.{1} R} {m : ℕ} {ι : Type} [Fintype ι] (g : K.X m) (hg : K.d m g = 0) (Y : ι → K.X m)
    (hY : ∀ k, K.d m (Y k) = 0) (h : K.d m (g - ∑ k, Y k) = 0) :
    K.cls g hg - ∑ k, K.cls (Y k) (hY k) = K.cls (g - ∑ k, Y k) h := by
  have e : (⟨g - ∑ k, Y k, h⟩ : K.Z m) = ⟨g, hg⟩ - ∑ k, (⟨Y k, hY k⟩ : K.Z m) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, Submodule.coe_sum]
  change _ = Submodule.mkQ _ (⟨g - ∑ k, Y k, h⟩ : K.Z m)
  rw [e, map_sub, map_sum]
  rfl

theorem rep_fin {m : ℕ} {ι : Type} [Fintype ι] {Cl E : CH.Cn (CH.modF A) m} {c : CH.H (sq a b) m} (hc : Rep a b Cl c)
    (Y : ι → CH.Cn (sq a b) m) (y : ι → CH.Cn (CH.modF A) m) (hY : ∀ k, CH.d _ m (Y k) = 0)
    (hy : ∀ k s, vl a b _ (Y k s) = mk2 b _ (y k s)) (hE : Cl - ∑ k, y k = E) :
    Rep a b E (c - ∑ k, (CH.cx (sq a b)).cls (Y k) (hY k)) := by
  obtain ⟨g, hg, rfl, hgs⟩ := hc
  have h : CH.d _ m (g - ∑ k, Y k) = 0 := by
    rw [map_sub, map_sum, hg]
    simp [hY]
  refine ⟨g - ∑ k, Y k, h, cls_sub_sum (K := CH.cx (sq a b)) g hg Y hY h, fun s => ?_⟩
  subst hE
  change vl a b _ (g s - (∑ k, Y k) s) = mk2 b _ (Cl s - (∑ k, y k) s)
  rw [Finset.sum_apply, Finset.sum_apply, map_sub, map_sub, map_sum, map_sum]
  exact congrArg₂ (· - ·) (hgs s) (Finset.sum_congr rfl fun k _ => hy k s)

end SQ

end GlobalTheory.CompanionTheory.ConeZig
end
end

section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem res_cupList {A : C ⥤ CommAlgCat.{0} R} {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (l : Fin k → Ch A U 1) :
    resB A h (cupListC (U.ι ⋙ A) l) = cupListC (V.ι ⋙ A) fun j => resB A h (l j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (CH.mulP _).cupC _ (resB A h (cupListC _ fun i => l (Fin.castSucc i))) (resB A h (l (Fin.last k))) = _
    rw [ih]
    rfl

theorem PP_eq {A : C ⥤ CommAlgCat.{0} R} {N : ℕ} {W : Fin N → ObjectProperty C} (b : ∀ α, Ch A (W α) 1)
    {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch A V 2) (k : ℕ) :
    ∃ e : ℤ, e * e = 1 ∧ ∀ i : Idx (k + 1) N, PP b hWV z k i =
      e • cupListC ((capT W i.1).ι ⋙ A) fun j : Fin k => LL b i j.castSucc j.succ := by
  induction k with
  | zero => exact ⟨1, rfl, fun i => (one_smul ℤ _).symm⟩
  | succ k ih =>
    obtain ⟨e, he, h⟩ := ih
    refine ⟨(-1) ^ k * e, ?_, fun i => ?_⟩
    · rw [mul_mul_mul_comm, he, ← mul_pow]; simp
    · change (-1 : ℤ) ^ k • BB b k k (PP b hWV z k) i = _
      have hLL : ∀ j : Fin k, resB A (cap_le W (Fin.last (k + 1)) i) (LL b (fc (Fin.last (k + 1)) i) j.castSucc j.succ) =
          LL b i j.castSucc.castSucc j.castSucc.succ := by
        intro j
        refine res_LL b i _ _ _ _ _ _ (congrArg i.1 ?_) (congrArg i.1 ?_) <;>
        · have := j.2
          apply Fin.ext
          simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last, Fin.val_succ]
          split_ifs <;> omega
      rw [BB_apply, h, map_zsmul, bm_apply, res_cupList, mul_smul]
      simp only [hLL]
      rfl

theorem PP_mem (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (hF : IsFil Φ Fil) {N : ℕ} {W : Fin N → ObjectProperty C}
    (b : ∀ α, Ch Φ.A (W α) 1) {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch Φ.A V 2)
    (hb1 : ∀ α, b α ∈ Lm (Fil 1) (W α) 1) (k : ℕ) :
    PP b hWV z k ∈ (dfil (W := W) Fil hF.anti).L (k : ℤ) k k := by
  induction k with
  | zero =>
    intro i _ σ
    rw [hF.top _ (by simp)]
    trivial
  | succ k ih =>
    refine Submodule.smul_of_tower_mem _ _ ?_
    intro i _
    refine Lm_cup (a := Fil k) (b := Fil 1) (fun T x y hx hy => hF.mul k 1 T hx (by simpa using hy)) rfl
      (Lm_res (cap_le W _ i) (ih (fc (Fin.last (k + 1)) i) trivial)) (sub_mem (Lm_res _ (hb1 _)) (Lm_res _ (hb1 _)))

theorem capT_eq {N : ℕ} (W : Fin N → ObjectProperty C) {m : ℕ} (i : Fin m → Fin N) :
    capT W i = capS W (Finset.univ.image i) := by
  funext T
  refine propext ⟨fun h α hα => ?_, fun h a => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
  exact h a

theorem KEx (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (hF : IsFil Φ Fil) {N : ℕ} (W : Fin N → ObjectProperty C)
    (hS : ∀ S : Finset (Fin N), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j))
    (r : ℕ) (p q : ℕ) (hq : q ≠ r) : (dfil (W := W) Fil hF.anti).Ex (r : ℤ) p q := by
  have hH : ∀ (i : Idx (p + 1) N) (j : ℕ), j ≠ r → Subsingleton (HU (gr Fil r) (capT W i.1) j) := by
    intro i j hj
    rw [capT_eq]
    exact hS _ ⟨i.1 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ _ _ (by exact_mod_cast hj)
  cases q with
  | zero =>
    intro x hx hd i _ σ
    exact ex_zero (a := (Fil r).res (capT W i.1).ι) (b := (Fil (r + 1)).res (capT W i.1).ι) (hH i 0 hq) (x i)
      (hx i trivial) (hd i trivial) σ
  | succ q =>
    intro x hx hd
    have h := fun i : Idx (p + 1) N =>
      ex_succ (a := (Fil r).res (capT W i.1).ι) (b := (Fil (r + 1)).res (capT W i.1).ι) (hH i (q + 1) hq) (x i)
        (hx i trivial) (hd i trivial)
    choose v hv hv' using h
    exact ⟨v, fun i _ => hv i, fun i _ => hv' i⟩

theorem alg_fin {M : Type*} [AddCommGroup M] {ι : Type} [Fintype ι] (e s : ℤ) (he : e * e = 1) (Cl Pv E : M) (t : ι → M)
    (sg : ι → ℤ) (h1 : Pv = e • Cl) (h2 : Pv = ∑ k, sg k • t k + s • E) :
    Cl - ∑ k, (e * sg k) • t k = (e * s) • E := by
  have h3 : Cl = e • Pv := by rw [h1, smul_smul, he, one_smul]
  rw [h3, h2, smul_add, Finset.smul_sum]
  simp only [smul_smul]
  abel

theorem KV (A : C ⥤ CommAlgCat.{0} R) (n : ℕ) (W : Fin (n + 2) → ObjectProperty C) (p q : ℕ) (h : n + 1 < p) :
    Subsingleton ((KK A W).X p q) := by
  have e : IsEmpty (Idx (p + 1) (n + 2)) := ⟨fun i => by
    have := Fintype.card_le_of_injective _ i.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩
  exact ⟨fun x y => funext fun i => (e.false i).elim⟩

theorem fin_step {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (n : ℕ)
    (W : Fin (n + 2) → ObjectProperty C) (Cl : Ch Φ.A (capS W Finset.univ) (n + 1))
    (hCl : Cl ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1))
    (c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1))
    (hc : Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι) Cl c)
    (w : ∀ k : Fin (n + 2), Ch Φ.A (capS W (Finset.univ.erase k)) (n + 1))
    (hw : ∀ k, w k ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1))
    (hdw : ∀ k, CH.d _ (n + 1) (w k) ∈ Lm (Fil ((n : ℤ) + 1 + 1)) _ (n + 2))
    (f : Ch Φ.A (capS W Finset.univ) n) (hf : f ∈ Lm (Fil (n : ℤ)) _ n)
    (hEq : Cl - ∑ k, resB Φ.A (capS_univ_le W (Finset.univ.erase k)) (w k) = CH.d _ n f) :
    ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
      (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
      (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  have hG : ∀ k : Fin (n + 2), CH.d _ (n + 1) (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k)) = 0 := fun k =>
    gC_d (a := (Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      (b := (Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k) (fun s => hdw k s)
  have hY : ∀ k : Fin (n + 2), CH.d _ (n + 1) ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase k))).pullC (n + 1)
      (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
        ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k))) = 0 := fun k => by
    rw [CH.Mor.d_pullC]
    exact (congrArg _ (hG k)).trans (map_zero _)
  refine ⟨fun k => (CH.cx _).cls (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k)) (hG k), f, hf, ?_, ?_⟩
  · rw [← hEq]
    refine (show _ ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) from sub_mem hCl (Submodule.sum_mem _ fun k _ => ?_))
    exact Lm_res _ (hw k)
  · exact rep_fin hc _ (fun k : Fin (n + 2) => resB Φ.A (capS_univ_le W (Finset.univ.erase k)) (w k)) hY (fun k s => rfl) hEq

theorem cech_top_cup_power : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ (s n : ℕ) (W : Fin (n + 2) → ObjectProperty C), (∀ T, (∃ α, W α T) → (Fil s).S T = ⊥) →
    (∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    ∀ (z : CH.Cn (CH.modF ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A)) 2), CH.d _ 2 z = 0 → (∀ σ, z σ ∈ (Fil 1).S _) →
    ∀ (b : ∀ i, CH.Cn (CH.modF ((W i).ι ⋙ Φ.A)) 1), (∀ i σ, b i σ ∈ (Fil 1).S _) →
    (∀ i, resB Φ.A (fun T h => ⟨i, h⟩ : W i ≤ fun T : C => ∃ α, W α T) z = CH.d _ 1 (b i)) →
    (∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1)) h = 0) →
    ∀ c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
          resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) c →
      ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
        (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
        (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
        Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  intro R _ C _ Φ Fil hF s n W _ _ hS _ z hz hz1 b hb1 hb hcob c hc
  have hWV : ∀ α, W α ≤ (fun T : C => ∃ α, W α T) := fun α T h => ⟨α, h⟩
  have hd := cupPow_d _ z hz (n + 1)
  obtain ⟨u, hu⟩ : cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1) ∈
      LinearMap.range (CH.d _ (2 * n + 1)) := ((CrystallineSemistableComparison.P.cls_surj (CH.cx _) _).2.1 _ hd).1 (hcob hd)
  let v : (KK Φ.A W).X 0 (2 * n + 1) := fun i => resB Φ.A (capV hWV i) u
  have hv1 : (KK Φ.A W).dv 0 (2 * n + 1) v = aa hWV z (n + 1) := by
    funext i
    rw [dv_apply]
    change CH.d _ _ (resB Φ.A _ u) = resB Φ.A _ _
    rw [d_resB, hu]
  have hv2 : (KK Φ.A W).dh 0 (2 * n + 1) v = 0 := by
    funext i
    rw [dh_apply, Fin.sum_univ_two]
    have e : resB Φ.A (cap_le W 0 i) (v (fc 0 i)) = resB Φ.A (cap_le W 1 i) (v (fc 1 i)) := rfl
    rw [e, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_smul, add_neg_cancel]
    rfl
  have hTop : ∀ p q, (dfil (W := W) Fil hF.anti).L 0 p q = ⊤ := fun p q =>
    (Submodule.eq_top_iff'.2 fun x i _ σ => by rw [hF.top 0 le_rfl]; trivial)
  have hPm : PP b hWV z (n + 1) ∈ (dfil (W := W) Fil hF.anti).L ((n : ℤ) + 1) (n + 1) (n + 1) := by
    have h := PP_mem Φ Fil hF b hWV z (fun α σ => hb1 α σ) (n + 1)
    rwa [Nat.cast_succ] at h
  obtain ⟨ω, f, hω, hdω, hf, hP⟩ := zig_stair (BB b) (dfil (W := W) Fil hF.anti) n hTop (fun p q h => KV _ n W p q h)
    (KEx Φ Fil hF W hS) (BB_dh b) (BB_dv b hWV z hb) (aa hWV z) (gg b hWV z) (PP b hWV z)
    (gg_dv b hWV z hz hb) (gg_dh b hWV z) rfl (fun k => rfl) hPm v hv1 hv2
  let tp : Idx (n + 1 + 1) (n + 2) := ⟨id, strictMono_id⟩
  obtain ⟨e, he, hPe⟩ := PP_eq b hWV z (n + 1)
  have hU : capS W Finset.univ ≤ capT W tp.1 := fun T h a => h a (Finset.mem_univ a)
  have hEk : ∀ k : Fin (n + 2), capS W (Finset.univ.erase k) ≤ capT W (fc k tp).1 := fun k T h a =>
    h _ (Finset.mem_erase.2 ⟨Fin.succAbove_ne k a, Finset.mem_univ _⟩)
  have hCl : resB Φ.A hU (PP b hWV z (n + 1) tp) = e • cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
      resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ) := by
    rw [hPe]
    refine (map_zsmul ((rM Φ.A hU).pullC (n + 1)) e _).trans ?_
    have h := res_cupList (A := Φ.A) hU (fun j : Fin (n + 1) => LL b tp j.castSucc j.succ)
    exact congrArg (e • ·) (h.trans (congrArg _ (funext fun j => resB_sub hU _ _)))
  have hP2 : resB Φ.A hU (PP b hWV z (n + 1) tp) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      resB Φ.A (hU.trans (cap_le W k tp)) (ω (fc k tp)) + ((-1 : ℤ) ^ (n + 1)) • CH.d _ n (resB Φ.A hU (f tp)) := by
    have h := congrFun hP tp
    rw [h]
    change (rM Φ.A hU).pullC (n + 1) ((KK Φ.A W).dh n (n + 1) ω tp + (-1 : ℤ) ^ (n + 1) • CH.d _ n (f tp)) = _
    rw [dh_apply, map_add, map_sum, map_zsmul]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) ?_
    · rw [map_zsmul]; rfl
    · rw [d_resB]; rfl
  have hEq := alg_fin e ((-1 : ℤ) ^ (n + 1)) he _ _ _ _ (fun k : Fin (n + 2) => (-1 : ℤ) ^ (k : ℕ)) hCl hP2
  have hd' : CH.d _ n ((e * (-1 : ℤ) ^ (n + 1)) • resB Φ.A hU (f tp)) =
      (e * (-1 : ℤ) ^ (n + 1)) • CH.d _ n (resB Φ.A hU (f tp)) := map_zsmul _ _ _
  have hClm : (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
      resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) ∈
      Lm (Fil ((n : ℤ) + 1)) _ (n + 1) := by
    have h1 : resB Φ.A hU (PP b hWV z (n + 1) tp) ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) := Lm_res _ (hPm tp trivial)
    rw [hCl] at h1
    have h2 := Submodule.smul_of_tower_mem _ e h1
    rwa [smul_smul, he, one_smul] at h2
  have hw : ∀ k : Fin (n + 2), (e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp)) ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) :=
    fun k => Submodule.smul_of_tower_mem _ _ (Lm_res _ (hω (fc k tp) trivial))
  have hdw : ∀ k : Fin (n + 2), CH.d _ (n + 1) ((e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp))) ∈
      Lm (Fil ((n : ℤ) + 1 + 1)) _ (n + 2) := fun k => by
    rw [map_zsmul, d_resB]
    exact Submodule.smul_of_tower_mem _ _ (Lm_res _ (hdω (fc k tp) trivial))
  have hfm : (e * (-1 : ℤ) ^ (n + 1)) • resB Φ.A hU (f tp) ∈ Lm (Fil (n : ℤ)) _ n :=
    Submodule.smul_of_tower_mem _ _ (Lm_res hU (hf tp trivial))
  refine fin_step Φ Fil n W _ hClm c hc _ hw hdw _ hfm ?_
  have e3 : ∀ k : Fin (n + 2), resB Φ.A (capS_univ_le W (Finset.univ.erase k))
      ((e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp))) =
      (e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hU.trans (cap_le W k tp)) (ω (fc k tp)) := fun k =>
    map_zsmul ((rM Φ.A (capS_univ_le W (Finset.univ.erase k))).pullC (n + 1)) _ _
  simp only [e3]
  rw [hd']
  exact hEq

end GlobalTheory.CompanionTheory.ConeZig
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_cover_vanishing_induction : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ (s n : ℕ) (W : Fin (n + 2) → ObjectProperty C), (∀ T, (∃ α, W α T) → (Fil s).S T = ⊥) →
    (∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    ∀ (z : CH.Cn (CH.modF ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A)) 2), CH.d _ 2 z = 0 → (∀ σ, z σ ∈ (Fil 1).S _) →
    ∀ (b : ∀ i, CH.Cn (CH.modF ((W i).ι ⋙ Φ.A)) 1), (∀ i σ, b i σ ∈ (Fil 1).S _) →
    (∀ i, resB Φ.A (fun T h => ⟨i, h⟩ : W i ≤ fun T : C => ∃ α, W α T) z = CH.d _ 1 (b i)) →
    (∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1)) h = 0) →
    ∀ c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
          resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) c →
      ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
        (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
        (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
        Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ConeZig.cech_top_cup_power
end
