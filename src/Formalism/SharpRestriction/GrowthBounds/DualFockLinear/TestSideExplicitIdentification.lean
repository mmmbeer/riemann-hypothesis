import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DvdOfCompl
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideCounting
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)

theorem map_thAll {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n' m : ℕ) (vec : Fin n' → Bool)
    (P : MvPolynomial (Fin n' × Fin (m + 1)) R) :
    map f (thAll R n' m vec P) = thAll R' n' m vec (map f P) := by
  have hN : ∀ (b : Bool) (c : Fin (m + 1)),
      map f (Formalism.L2.G.Model.Nv R m b c) = Formalism.L2.G.Model.Nv R' m b c := by
    intro b c
    cases b
    · simp only [Formalism.L2.G.Model.Nv, Bool.false_eq_true, if_false]
      have hg : Formalism.L2.G.Model.genM R' m =
          (map f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R →+* _).mapMatrix (Formalism.L2.G.Model.genM R m) := by
        ext a u
        simp [Formalism.L2.G.Model.genM]
      rw [hg, ← RingHom.map_adjugate]
      rfl
    · simp [Formalism.L2.G.Model.Nv]
  have key : (map f).comp (thAll R n' m vec).toRingHom = (thAll R' n' m vec).toRingHom.comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [thAll]
    · intro v
      simp [thAll, blockEmb, map_rename, hN]
  exact RingHom.congr_fun key P

theorem restricted_weight_first_two_eq {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (s : Fin n') (hs : s ∈ TT) : restW TT lam0 s 0 = restW TT lam0 s 1 := by
  have hle : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le _)
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  have ht := Int.toNat_of_nonneg (sub_nonneg.mpr hle)
  simp only [restW, flW, dT, flatDeg, hs, if_true, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h10]
  omega

theorem nu_odd {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (s : Fin n') (hs : s ∈ TT) (hv : vecE n' s = false) (t : Fin (m + 1)) (ht : m ≤ t.val + 1) :
    nuOf (lamAt (restW TT lam0) s) t = 0 := by
  have hodd : ¬ Even (s : ℕ) := by simpa [vecE] using hv
  have htl := t.isLt
  have hr : restW TT lam0 s t.rev = restW TT lam0 s 0 := by
    have hv' : t.rev.val ≤ 1 := by
      rw [Fin.val_rev]
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv' with h | h
    · have e : t.rev = 0 := Fin.ext (by rw [h, Fin.val_zero])
      rw [e]
    · have e : t.rev = 1 := by
        apply Fin.ext
        rw [h, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [e, restricted_weight_first_two_eq hm TT lam0 hdom s hs]
  simp only [nuOf, lamAt, hodd, if_false, Fin.rev_last, hr]
  simp

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model (Nv Nv_true_eq Nv_false_eq)
open scoped MonomialOrder

def Mv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec = true then initMinor R (fun _ : Fin 1 => c) (Nat.succ_le_succ (Nat.zero_le m))
  else initMinor R c.succAbove (Nat.le_succ m)

def dg (m : ℕ) (vec : Bool) (c : Fin (m + 1)) : Fin (m + 1) × Fin (m + 1) →₀ ℕ :=
  if vec = true then Finsupp.single (c, 0) 1
  else ∑ p : Fin m, Finsupp.single (c.succAbove p, Fin.castLE (Nat.le_succ m) p) 1

theorem Mv_deg (F : Type) [Field F] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    (colLex (m + 1) (m + 1)).degree (Mv F m vec c) = dg m vec c ∧
      (colLex (m + 1) (m + 1)).leadingCoeff (Mv F m vec c) = 1 := by
  unfold Mv dg
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    exact colLexInitMinor F (m + 1) (m + 1) m c.succAbove (Nat.le_succ m) (Fin.strictMono_succAbove c)
  · simp only [if_true]
    have hsm : StrictMono (fun _ : Fin 1 => c) := by
      intro a b hab
      exact absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)
    obtain ⟨h1, h2⟩ := colLexInitMinor F (m + 1) (m + 1) 1 (fun _ : Fin 1 => c)
      (Nat.succ_le_succ (Nat.zero_le m)) hsm
    refine ⟨?_, h2⟩
    rw [h1, Fin.sum_univ_one]
    congr 2

def sg (F : Type) [Field F] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) : Fˣ :=
  if vec = true then 1 else (-1) ^ ((c : ℕ) + m)

theorem Nv_eq (F : Type) [Field F] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    Nv F m vec c = sg F m vec c • Mv F m vec c := by
  cases vec
  · rw [Nv_false_eq]
    simp only [sg, Mv, Bool.false_eq_true, if_false, Units.smul_def, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    rw [smul_eq_C_mul, map_pow, map_neg, map_one]
  · rw [Nv_true_eq]
    simp only [sg, Mv, if_true, one_smul]

theorem fam_deg (F : Type) [Field F] (m : ℕ) (vec : Bool) (α : Fin (m + 1) →₀ ℕ)
    (g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) F) (e : Fin (m + 1) × Fin (m + 1) →₀ ℕ)
    (hg : (colLex (m + 1) (m + 1)).degree g = e ∧ (colLex (m + 1) (m + 1)).leadingCoeff g = 1) :
    (colLex (m + 1) (m + 1)).degree ((∏ c, Mv F m vec c ^ α c) * g) = (∑ c, α c • dg m vec c) + e ∧
      (colLex (m + 1) (m + 1)).leadingCoeff ((∏ c, Mv F m vec c ^ α c) * g) = 1 := by
  have hP1 : ∀ c, (colLex (m + 1) (m + 1)).degree (Mv F m vec c ^ α c) = α c • dg m vec c := by
    intro c
    rw [MonomialOrder.degree_pow, (Mv_deg F m vec c).1]
  have hP2 : ∀ c, (colLex (m + 1) (m + 1)).leadingCoeff (Mv F m vec c ^ α c) = 1 := by
    intro c
    rw [MonomialOrder.leadingCoeff_pow, (Mv_deg F m vec c).2, one_pow]
  have hdeg : (colLex (m + 1) (m + 1)).degree (∏ c, Mv F m vec c ^ α c) = ∑ c, α c • dg m vec c := by
    have h := (colLex (m + 1) (m + 1)).degree_prod_of_regular (P := fun c => Mv F m vec c ^ α c)
      (s := Finset.univ) (fun c _ => by simp only [hP2]; exact isRegular_one)
    simp only [hP1] at h
    exact h
  have hlc : (colLex (m + 1) (m + 1)).leadingCoeff (∏ c, Mv F m vec c ^ α c) = 1 := by
    have h := (colLex (m + 1) (m + 1)).coeff_prod_sum_degree (fun c => Mv F m vec c ^ α c) Finset.univ
    simp only [hP1, hP2, Finset.prod_const_one] at h
    rw [MonomialOrder.leadingCoeff, hdeg]
    exact h
  have hne1 : (∏ c, Mv F m vec c ^ α c) ≠ 0 := by
    intro h0
    rw [h0, MonomialOrder.leadingCoeff_zero] at hlc
    exact zero_ne_one hlc
  have hne2 : g ≠ 0 := by
    intro h0
    have h2 := hg.2
    rw [h0, MonomialOrder.leadingCoeff_zero] at h2
    exact zero_ne_one h2
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.degree_mul hne1 hne2, hdeg, hg.1]
  · rw [MonomialOrder.leadingCoeff_mul, hlc, hg.2, one_mul]

theorem dg_false_diag (m : ℕ) (c t : Fin (m + 1)) (ht : t.val < m) :
    dg m false c (t, t) = if t < c then 1 else 0 := by
  simp only [dg, Bool.false_eq_true, if_false, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single (⟨t.val, ht⟩ : Fin m)]
  · by_cases htc : t < c
    · rw [if_pos htc, if_pos]
      simp only [Prod.mk.injEq]
      constructor
      · rw [Fin.succAbove_of_castSucc_lt]
        · exact Fin.ext rfl
        · exact htc
      · exact Fin.ext rfl
    · rw [if_neg htc, if_neg]
      simp only [Prod.mk.injEq, not_and]
      intro h _
      rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.mp htc)] at h
      rw [Fin.ext_iff] at h
      simp at h
  · intro p _ hp
    rw [if_neg]
    simp only [Prod.mk.injEq, not_and]
    intro _ h2
    apply hp
    ext
    rw [Fin.ext_iff] at h2
    exact h2
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tail_step {k : ℕ} (f : Fin k → ℕ) (n : ℕ) (hn : n < k) :
    (∑ c : Fin k with n ≤ c.val, f c) = f ⟨n, hn⟩ + ∑ c : Fin k with n + 1 ≤ c.val, f c := by
  have hset : (Finset.univ.filter fun c : Fin k => n ≤ c.val) =
      insert ⟨n, hn⟩ (Finset.univ.filter fun c : Fin k => n + 1 ≤ c.val) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hset, Finset.sum_insert]
  simp

theorem tail_inj {k : ℕ} (f g : Fin k → ℕ)
    (h : ∀ n, (∑ c : Fin k with n ≤ c.val, f c) = ∑ c : Fin k with n ≤ c.val, g c) : f = g := by
  funext c
  have h1 := h c.val
  have h2 := h (c.val + 1)
  rw [tail_step f c.val c.isLt, tail_step g c.val c.isLt, h2] at h1
  exact Nat.add_right_cancel h1

theorem no_zero_low {k : ℕ} (x : Fin k × Fin k →₀ ℕ) (hI : Interlaced x) (h0 : ∀ (z : Fin k), z.val = 0 → ∀ t, x (z, t) = 0) :
    ∀ (n : ℕ) (t a : Fin k), t.val = n → a.val ≤ n → x (a, t) = 0 := by
  intro n
  induction n with
  | zero =>
    intro t a _ ha
    exact h0 a (Nat.le_zero.mp ha) t
  | succ n ih =>
    intro t a ht ha
    have hn : n < k := by
      have := t.isLt
      omega
    have hI' := hI ⟨n, hn⟩ t (by simp [ht]) a
    have hzero : ∑ b : Fin k with b < a, x (b, ⟨n, hn⟩) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [Fin.lt_def] at hb
      exact ih ⟨n, hn⟩ b rfl (by omega)
    rw [hzero, add_zero] at hI'
    have hle : x (a, t) ≤ ∑ b : Fin k with b ≤ a, x (b, t) :=
      Finset.single_le_sum (f := fun b => x (b, t)) (fun _ _ => Nat.zero_le _) (by simp)
    omega

private theorem sum_mul_dg_diag_eq_sum_filter (m n : ℕ) (β : Fin (m + 1) →₀ ℕ) (t : Fin (m + 1)) (ht : t.val < m)
    (hn : t.val + 1 = n) :
    ∑ c, β c * dg m false c (t, t) = ∑ c : Fin (m + 1) with n ≤ c.val, β c := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  rw [dg_false_diag m c t ht]
  by_cases hc : t < c
  · rw [Fin.lt_def] at hc
    rw [if_pos (Fin.lt_def.mpr hc), if_pos (by omega), mul_one]
  · rw [Fin.lt_def] at hc
    rw [if_neg (fun h => hc (Fin.lt_def.mp h)), if_neg (by omega), mul_zero]

theorem key_inj (m : ℕ) (top vec : Bool) (d : ℕ) (ν : Fin (m + 1) → ℕ) (htop : top = false → d = 0)
    (α α' : Fin (m + 1) →₀ ℕ) (hα : ∑ c, α c = d) (hα' : ∑ c, α' c = d) (x x' : Xs m top vec ν)
    (h : (∑ c, α c • dg m vec c) + x.1 = (∑ c, α' c • dg m vec c) + x'.1) : α = α' := by
  ext c
  cases top
  · have hd := htop rfl
    have h1 : α c = 0 := Finset.sum_eq_zero_iff.mp (hα.trans hd) c (Finset.mem_univ c)
    have h2 : α' c = 0 := Finset.sum_eq_zero_iff.mp (hα'.trans hd) c (Finset.mem_univ c)
    rw [h1, h2]
  · cases vec
    · have hz : ∀ y : Xs m true false ν, ∀ t : Fin (m + 1), y.1 (t, t) = 0 := by
        intro y t
        obtain ⟨⟨hI, _⟩, htop'⟩ := y.2
        have hrow := (htop' rfl).2 rfl
        exact no_zero_low y.1 hI (fun z hz t' => by
          have hz0 : z = 0 := Fin.ext hz
          rw [hz0]
          exact hrow t') t.val t t rfl le_rfl
      have htail : ∀ n, (∑ c : Fin (m + 1) with n ≤ c.val, α c) =
          ∑ c : Fin (m + 1) with n ≤ c.val, α' c := by
        intro n
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          have z0 : ∀ β : Fin (m + 1) →₀ ℕ, (∑ c : Fin (m + 1) with 0 ≤ c.val, β c) = ∑ c, β c := by
            intro β
            rw [Finset.filter_true_of_mem (fun c _ => Nat.zero_le c.val)]
          rw [z0 α, z0 α', hα, hα']
        · by_cases hnm : n ≤ m
          · have ht : n - 1 < m + 1 := by omega
            have he := congrArg (fun f => f ((⟨n - 1, ht⟩ : Fin (m + 1)), (⟨n - 1, ht⟩ : Fin (m + 1)))) h
            simp only [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at he
            rw [hz x, hz x', add_zero, add_zero,
              sum_mul_dg_diag_eq_sum_filter m n α _ (by show n - 1 < m; omega) (by show n - 1 + 1 = n; omega),
              sum_mul_dg_diag_eq_sum_filter m n α' _ (by show n - 1 < m; omega) (by show n - 1 + 1 = n; omega)] at he
            exact he
          · have z1 : ∀ β : Fin (m + 1) →₀ ℕ, (∑ c : Fin (m + 1) with n ≤ c.val, β c) = 0 := by
              intro β
              apply Finset.sum_eq_zero
              intro c hc
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
              have := c.isLt
              omega
            rw [z1 α, z1 α']
      have hfun := tail_inj (fun c => α c) (fun c => α' c) htail
      exact congrFun hfun c
    · have hcol : ∀ y : Xs m true true ν, ∀ a : Fin (m + 1), y.1 (a, 0) = if a = 0 then ν 0 else 0 := by
        intro y a
        obtain ⟨⟨_, hs⟩, htop'⟩ := y.2
        have h00 : y.1 (0, 0) = ν 0 := (htop' rfl).1 rfl
        have hsum := hs 0
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1))), h00] at hsum
        have hrest : ∑ b ∈ Finset.univ.erase (0 : Fin (m + 1)), y.1 (b, 0) = 0 := by omega
        split_ifs with ha
        · rw [ha]
          exact h00
        · exact Finset.sum_eq_zero_iff.mp hrest a (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)
      have he := congrArg (fun f => f (c, (0 : Fin (m + 1)))) h
      simp only [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at he
      rw [hcol x, hcol x'] at he
      have hs1 : ∀ β : Fin (m + 1) →₀ ℕ, ∑ c', β c' * dg m true c' (c, 0) = β c := by
        intro β
        rw [Finset.sum_eq_single c]
        · simp [dg]
        · intro b _ hb
          simp [dg, Finsupp.single_apply, hb]
        · intro hc
          exact absurd (Finset.mem_univ c) hc
      rw [hs1 α, hs1 α'] at he
      split_ifs at he <;> omega

private theorem linearIndependent_of_degree_injective {σ ι F : Type} [Field F] (M : MonomialOrder σ) (v : ι → MvPolynomial σ F)
    (hv : ∀ i, v i ≠ 0) (hinj : Function.Injective fun i => M.degree (v i)) : LinearIndependent F v := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hne
  have hne' : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hne⟩⟩
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (s.filter fun j => g j ≠ 0)
    (fun j => M.toSyn (M.degree (v j))) hne'
  rw [Finset.mem_filter] at hi0
  have hc := congrArg (MvPolynomial.coeff (M.degree (v i0))) hg
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single i0] at hc
  · rw [MvPolynomial.coeff_smul, smul_eq_mul] at hc
    have hlc : MvPolynomial.coeff (M.degree (v i0)) (v i0) ≠ 0 := M.leadingCoeff_ne_zero_iff.mpr (hv i0)
    exact mul_ne_zero hi0.2 hlc hc
  · intro j hj hji0
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have hle := hmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
      have hlt : M.toSyn (M.degree (v j)) < M.toSyn (M.degree (v i0)) := by
        refine lt_of_le_of_ne hle ?_
        intro heq
        exact hji0 (hinj (M.toSyn.injective heq))
      rw [M.coeff_eq_zero_of_lt hlt, mul_zero]
  · intro h
    exact absurd hi0.1 h

private theorem exists_ne_zero_prod_Nv_pow_eq_smul_prod_Mv (F : Type) [Field F] (m : ℕ) (vec : Bool) (α : Fin (m + 1) →₀ ℕ) :
    ∃ u : F, u ≠ 0 ∧ ∏ c, Nv F m vec c ^ α c = u • ∏ c, Mv F m vec c ^ α c := by
  refine ⟨∏ c, ((sg F m vec c : Fˣ) : F) ^ α c, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun c _ => pow_ne_zero _ (Units.ne_zero _))
  · rw [smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro c _
    rw [Nv_eq, Units.smul_def, smul_eq_C_mul, mul_pow, map_pow]

theorem posInd : PosInd := by
  unfold PosInd
  intro F _ m _ top vec d ν htop _ b hb
  have hdeg : ∀ y : {α : Fin (m + 1) →₀ ℕ // ∑ c, α c = d} × Xs m top vec ν,
      (colLex (m + 1) (m + 1)).degree ((∏ c, Nv F m vec c ^ y.1.1 c) * b y.2) =
          (∑ c, y.1.1 c • dg m vec c) + y.2.1 ∧
        (∏ c, Nv F m vec c ^ y.1.1 c) * b y.2 ≠ 0 := by
    intro y
    obtain ⟨u, hu, he⟩ := exists_ne_zero_prod_Nv_pow_eq_smul_prod_Mv F m vec y.1.1
    obtain ⟨h1, h2⟩ := fam_deg F m vec y.1.1 (b y.2) y.2.1 (hb y.2)
    have hne : (∏ c, Mv F m vec c ^ y.1.1 c) * b y.2 ≠ 0 := by
      intro h0
      rw [h0, MonomialOrder.leadingCoeff_zero] at h2
      exact zero_ne_one h2
    rw [he, smul_mul_assoc]
    refine ⟨?_, smul_ne_zero hu hne⟩
    rw [MonomialOrder.degree_smul_of_isRegular (isRegular_of_ne_zero hu), h1]
  apply linearIndependent_of_degree_injective (colLex (m + 1) (m + 1))
  · intro y
    exact (hdeg y).2
  · intro y y' hyy
    have e : (∑ c, y.1.1 c • dg m vec c) + y.2.1 = (∑ c, y'.1.1 c • dg m vec c) + y'.2.1 := by
      rw [← (hdeg y).1, ← (hdeg y').1]
      exact hyy
    have hα := key_inj m top vec d ν htop y.1.1 y'.1.1 y.1.2 y'.1.2 y.2 y'.2 e
    have h2 : y.2.1 = y'.2.1 := by
      rw [hα] at e
      exact add_left_cancel e
    exact Prod.ext (Subtype.ext hα) (Subtype.ext h2)

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model (Nv)

abbrev Aset (k d : ℕ) := {α : Fin k →₀ ℕ // ∑ c, α c = d}

instance Aset_finite (k d : ℕ) : Finite (Aset k d) := by
  have : ({α : Fin k →₀ ℕ | ∑ c, α c = d}).Finite := by
    refine (Finset.finite_toSet (Finset.univ.finsuppAntidiag d)).subset ?_
    intro α hα
    simp only [Finset.mem_coe, Finset.mem_finsuppAntidiag]
    exact ⟨hα, Finset.subset_univ _⟩
  exact this.to_subtype

theorem XsFinP (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : (Xs m top vec ν).Finite :=
  (sSIdxFinite (m + 1) (m + 1) ν).subset fun _ he => he.1

instance XsFinP' (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : Finite (Xs m top vec ν) :=
  (XsFinP m top vec ν).to_subtype

def glue {n' k : ℕ} {d : Fin n' → ℕ} (a : ∀ s, Aset k (d s)) : Fin n' × Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => (a v.1).1 v.2

theorem expand {R : Type} [CommRing R] {n' k : ℕ} {d : Fin n' → ℕ} [Fintype (∀ s, Aset k (d s))]
    (Q : MvPolynomial (Fin n' × Fin k) R) (hQ : IsMultiHom d Q) :
    Q = ∑ a : (∀ s, Aset k (d s)), monomial (glue a) (coeff (glue a) Q) := by
  classical
  ext e
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases he : e ∈ Q.support
  · let a : ∀ s, Aset k (d s) := fun s =>
      ⟨Finsupp.equivFunOnFinite.symm fun c => e (s, c), by simpa using hQ e he s⟩
    have ha : glue a = e := by
      ext v
      rfl
    rw [Finset.sum_eq_single a]
    · rw [if_pos ha, ha]
    · intro a' _ hne
      rw [if_neg]
      intro h
      apply hne
      funext s
      apply Subtype.ext
      ext c
      have := DFunLike.congr_fun (h.trans ha.symm) (s, c)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : coeff e Q = 0 := by simpa using he
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with h
    · rw [h, h0]
    · rfl

theorem thAll_monomial (F : Type) [CommRing F] (n' m : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ)
    (a : ∀ s, Aset (m + 1) (d s)) (r : F) :
    thAll F n' m vec (monomial (glue a) r) = r • ∏ s, blockEmb F s (∏ c, Nv F m (vec s) c ^ (a s).1 c) := by
  unfold thAll
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Algebra.smul_def]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [map_pow]
  rfl

section Core

variable (F : Type) [Field F] (n' m : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ) {X : Fin n' → Type}
  (b : ∀ s, X s → MvPolynomial (Fin (m + 1) × Fin (m + 1)) F)

def famG (z : (∀ s, Aset (m + 1) (d s)) × (∀ s, X s)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) F :=
  ∏ s, blockEmb F s ((∏ c, Nv F m (vec s) c ^ ((z.1 s).1 c)) * b s (z.2 s))

def fam1 (s : Fin n') (y : Aset (m + 1) (d s) × X s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) F :=
  (∏ c, Nv F m (vec s) c ^ (y.1.1 c)) * b s y.2

def pairUp {n' : ℕ} {A X : Fin n' → Type} (z : (∀ s, A s) × (∀ s, X s)) : ∀ s, A s × X s := fun s => (z.1 s, z.2 s)

theorem pairUp_inj {n' : ℕ} {A X : Fin n' → Type} : Function.Injective (pairUp (A := A) (X := X)) := by
  intro z z' h
  refine Prod.ext ?_ ?_
  · funext s
    exact congrArg Prod.fst (congrFun h s)
  · funext s
    exact congrArg Prod.snd (congrFun h s)

theorem famG_li (hpos : ∀ s, LinearIndependent F (fam1 F n' m vec d b s)) :
    LinearIndependent F (famG F n' m vec d b) := by
  have hli : LinearIndependent F (fun i : (∀ s, Aset (m + 1) (d s) × X s) =>
      ∏ s, blockEmb F s (fam1 F n' m vec d b s (i s))) :=
    ldtensor_prod_linInd_field F (fam1 F n' m vec d b) hpos
  have h2 := hli.comp (pairUp (A := fun s => Aset (m + 1) (d s)) (X := X)) pairUp_inj
  exact h2

theorem famG_sum [Fintype (∀ s, Aset (m + 1) (d s))] (Q : MvPolynomial (Fin n' × Fin (m + 1)) F) (hQ : IsMultiHom d Q)
    (i : ∀ s, X s) :
    (∑ a : (∀ s, Aset (m + 1) (d s)), coeff (glue a) Q • famG F n' m vec d b (a, i)) =
      thAll F n' m vec Q * ∏ s, blockEmb F s (b s (i s)) := by
  have e := expand Q hQ
  have e2 : thAll F n' m vec Q =
      ∑ a : (∀ s, Aset (m + 1) (d s)), coeff (glue a) Q •
        ∏ s, blockEmb F s (∏ c, Nv F m (vec s) c ^ (a s).1 c) := by
    conv_lhs => rw [e]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => thAll_monomial F n' m vec d a _
  rw [e2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  unfold famG
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_mul]

theorem big_core [∀ s, Finite (X s)] (hpos : ∀ s, LinearIndependent F (fam1 F n' m vec d b s))
    (J : Finset (∀ s, X s)) (Q : (∀ s, X s) → MvPolynomial (Fin n' × Fin (m + 1)) F) (hQ : ∀ i, IsMultiHom d (Q i))
    (hsum : ∑ i ∈ J, thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) = 0) : ∀ i ∈ J, Q i = 0 := by
  classical
  have : Fintype (∀ s, Aset (m + 1) (d s)) := Fintype.ofFinite _
  have : Fintype (∀ s, X s) := Fintype.ofFinite _
  have hli2 := famG_li F n' m vec d b hpos
  rw [Fintype.linearIndependent_iff] at hli2
  have key := hli2 (fun z => if z.2 ∈ J then coeff (glue z.1) (Q z.2) else 0) ?_
  · intro i hi
    rw [expand (Q i) (hQ i)]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h1 := key (a, i)
    simp only [hi, if_true] at h1
    rw [h1, monomial_zero]
  · rw [Fintype.sum_prod_type_right, ← hsum]
    have h1 : ∀ i : (∀ s, X s),
        (∑ a : (∀ s, Aset (m + 1) (d s)), (if i ∈ J then coeff (glue a) (Q i) else 0) • famG F n' m vec d b (a, i)) =
        if i ∈ J then thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) else 0 := by
      intro i
      by_cases hi : i ∈ J
      · simp only [hi, if_true]
        exact famG_sum F n' m vec d b (Q i) (hQ i) i
      · simp only [hi, if_false, zero_smul, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_ite_mem, Finset.univ_inter]

end Core

theorem bigInd : BigInd := by
  intro F _ n' m hm top vec d ν htop hν b hb J Q hQ hsum
  exact big_core F n' m vec d b
    (fun s => posInd F m hm (top s) (vec s) (d s) (ν s) (htop s) (hν s) (b s) (hb s)) J Q hQ hsum

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)

set_option maxHeartbeats 1600000 in

theorem primStep_of (hTr : TransStep) (hSub : SubstPol) (C CLa : ℝ) (hSP : SPStep C) : PrimStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hm2 : 2 ≤ m := by omega
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hwirr : Irreducible w := hSet.2.1
  set ν : Fin n' → Fin (m + 1) → ℕ := fun s => nuOf (lamAt (restW TT lam0) s) with hν
  set top : Fin n' → Bool := fun s => decide (s ∈ TT) with htop
  let I := ∀ s : Fin n', Xs m (top s) (vecE n' s) (ν s)
  have : Finite I := Pi.finite
  let _ : Fintype I := Fintype.ofFinite I
  let eI : I ≃ Fin (Nat.card I) := Finite.equivFin I
  have hbas := fun s => sSBasis O (m + 1) (m + 1) (ν s)
  choose b hb1 hb2 using hbas
  let bX : ∀ s, Xs m (top s) (vecE n' s) (ν s) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) O :=
    fun s y => b s ⟨y.1, y.2.1⟩
  let sO : I → MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) O := fun i => ∏ s, blockEmb O s (bX s (i s))
  have hsO : ∀ i, sO i ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lamAt (restW TT lam0) s))) := by
    intro i
    refine Submodule.subset_span ⟨fun s => bX s (i s), fun s => ?_, rfl⟩
    show bX s (i s) ∈ dualWeyl O (m + 1) (m + 1) (ν s)
    rw [← (hb1 s).2.1]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨sh', hsh, hmain⟩ := hTr p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm2 (by omega) (by omega) (dT TT lam0)
    (restW TT lam0) lam0 (lambda_zero_eq_product TT lam0) (restW_dom (by omega) TT lam0 hdom) e he hm g hhm hg hbasis Θ hΘ I sO hsO
  refine ⟨Nat.card I, fun i => sh' (eI.symm i), fun i => hsh _, card_all hm2 TT lam0 hdom, ?_⟩
  intro S hS c hcu hmem
  obtain ⟨x0, hx0⟩ := hcu
  obtain ⟨SPO, hSPO1, hSPO2⟩ := hSP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    hrk F hF g hg (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)
  let P : I → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) :=
    fun i => ∑ bb, c (bb, eI i) • FsB bb
  let T0 : I → RRing O n' (r + K) := fun i => ∑ bb, c (bb, eI i) • B bb
  let Q : I → MvPolynomial (Fin n' × Fin (m + 1)) O := fun i => rename (castV hk) (T0 i) * SPO
  have hPQ : ∀ i, subst p n' O w n' r g (P i : MvPolynomial (TV n' (m + 1)) (KK O)) =
      map (algebraMap O (KK O)) (Q i) := by
    intro i
    have e1 : ((P i : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) :
        MvPolynomial (TV n' (m + 1)) (KK O)) =
        ∑ bb, algebraMap O (KK O) (c (bb, eI i)) • (FsB bb : MvPolynomial (TV n' (m + 1)) (KK O)) := by
      simp only [P, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rw [e1, map_sum]
    simp only [map_smul, hFsB, symB, toK, Q, T0, map_mul, map_sum, ← hSPO1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun bb _ => ?_
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_C, mul_assoc]
  have hv : (((∑ y, c y • S y : Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      ∑ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
        ((sh' i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
    have e2 : ∀ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ∑ bb, c (bb, eI i) • ((Θ (FsB bb) : Vsp Kf (flW (m := m) (dT TT lam0))) :
          MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      intro i
      simp only [P, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    simp only [e2, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_mul]
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← Equiv.sum_comp eI]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun bb _ => ?_
    rw [hS bb (eI i)]
    simp only [Equiv.symm_apply_apply, smul_mul_assoc]
  obtain ⟨R, hR⟩ := hmain P Q hPQ _ hv hmem

  let Fr := IsLocalRing.ResidueField O
  let res : O →+* Fr := IsLocalRing.residue O
  have hresw : res w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hwirr.not_isUnit
  have h0 : ∑ i ∈ (Finset.univ : Finset I), thAll Fr n' m (vecE n') (map res (Q i)) *
      ∏ s, blockEmb Fr s (map res (bX s (i s))) = 0 := by
    have h1 := congrArg (map res) hR
    simp only [map_sum, map_mul, map_thAll, map_C, hresw, C_0, zero_mul, sO, map_prod, blockEmb, map_rename] at h1
    simpa only [blockEmb] using h1
  have hQhom : ∀ i, IsMultiHom (dT TT lam0) (map res (Q i)) := by
    intro i ee hee s
    have h1 : ee ∈ (Q i).support := support_map_subset res (Q i) hee
    have h2 : ee ∈ (map (algebraMap O (KK O)) (Q i)).support := by
      rw [support_map_of_injective _ (IsFractionRing.injective O (KK O))]
      exact h1
    rw [← hPQ i] at h2
    have h3 := hSub p n' W Qq O Kf ι σ j w hSet.1 φ hφ (m + 1) r (dT TT lam0) g hg _ (P i).2
    exact (Formalism.L2.G.Model.mem_Pol.1 h3) ee h2 s
  have hQ0 := bigInd Fr n' m hm2 top (vecE n') (dT TT lam0) ν
    (fun s hs => by
      have : s ∉ TT := by simpa [htop] using hs
      simp [dT, this])
    (fun s hs hv t ht => nu_odd (by omega) TT lam0 hdom s (by simpa [htop] using hs) hv t ht)
    (fun s y => map res (bX s y))
    (fun s y => by
      obtain ⟨d1, d2, -⟩ := hb2 s ⟨y.1, y.2.1⟩
      have := deg_map (colLex (m + 1) (m + 1)) res (bX s y) d2
      exact ⟨this.1.trans d1, this.2⟩)
    Finset.univ (fun i => map res (Q i)) hQhom h0
  have hq := hQ0 (eI.symm x0.2) (Finset.mem_univ _)
  simp only [Q, map_mul] at hq
  have hT : map res (rename (castV hk) (T0 (eI.symm x0.2))) = 0 := by
    rcases mul_eq_zero.1 hq with h1 | h1
    · exact h1
    · exact absurd h1 hSPO2
  rw [map_rename] at hT
  have hinj : Function.Injective (castV (n' := n') hk) := by
    intro u v huv
    simp only [castV, Prod.mk.injEq] at huv
    exact Prod.ext huv.1 (Fin.cast_injective _ huv.2)
  have hT' : map res (T0 (eI.symm x0.2)) = 0 := by
    apply rename_injective _ hinj
    rw [hT, map_zero]
  have hdvd : MvPolynomial.C w ∣ T0 (eI.symm x0.2) := by
    rw [C_dvd_iff_dvd_coeff]
    intro ee
    have h1 : res (coeff ee (T0 (eI.symm x0.2))) = 0 := by
      rw [← coeff_map, hT', coeff_zero]
    rw [IsLocalRing.residue_eq_zero_iff, hwirr.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨y, hy⟩ := hdvd
  obtain ⟨T, hTc⟩ := hc
  have hfin := dvd_of_compl B hli T hTc w (fun bb => c (bb, x0.2)) y (by
    have : T0 (eI.symm x0.2) = ∑ bb, c (bb, x0.2) • B bb := by
      simp only [T0, Equiv.apply_symm_apply]
    rw [← this, hy, MvPolynomial.smul_eq_C_mul]) x0.1
  exact hwirr.not_isUnit (isUnit_of_dvd_unit hfin hx0)

theorem source_integrality_of_substitution (hTr : TransStep) (hSub : SubstPol) (C₀ : ℝ) (hC0 : 0 < C₀) (hSP : ∀ C, C₀ ≤ C → SPStep C)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  fun _ => ⟨C₀, hC0, fun C hC => primStep_of hTr hSub C CLa (hSP C hC)⟩

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model

section Gen

variable {S : Type} [Fintype S] [DecidableEq S]

theorem tr_bA_emb (K : Type) [CommRing K] {k n : ℕ} (g : S → Matrix (Fin k) (Fin k) K) (s : S)
    (F : MvPolynomial (Fin k × Fin n) K) : blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) :=
  (blockActTensor K K S k n g).1 s F

theorem tr_prod_smul (K : Type) [CommRing K] {k n : ℕ} (c : S → K) (F : S → MvPolynomial (Fin k × Fin n) K) :
    (∏ s, c s) • ∏ s, blockEmb K s (F s) = ∏ s, blockEmb K s (c s • F s) := by
  rw [smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_C_mul]

theorem tr_map_emb {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {k n : ℕ} (s : S)
    (P : MvPolynomial (Fin k × Fin n) R) : map f (blockEmb R s P) = blockEmb R' s (map f P) := by
  unfold blockEmb
  exact map_rename f _ P

theorem map_letter_substitution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (m : ℕ) (vec : S → Bool)
    (P : MvPolynomial (S × Fin (m + 1)) R) : map f (Th0 R m vec P) = Th0 R' m vec (map f P) := by
  have key : (map f).comp (Th0 R m vec).toRingHom = (Th0 R' m vec).toRingHom.comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Th0]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, Th0, aeval_X]
      rw [tr_map_emb, map_Nv]
  exact RingHom.congr_fun key P

theorem tr_rowAct_inv (K : Type) [Field K] {k n : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det)
    (x : MvPolynomial (Fin k × Fin n) K) : rowAct K g (rowAct K g⁻¹ x) = x := by
  have := congrArg (fun f => f x) (rowActMul K k n g g⁻¹)
  simp only [AlgHom.comp_apply] at this
  rw [this, Matrix.nonsing_inv_mul g hg, fl_rowAct_one]

theorem tr_multi_twist (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hM : ∀ s, IsUnit (M s).det)
    (G : MvPolynomial (S × Fin (m + 1)) K) (hG : G ∈ Pol K (m + 1) d) :
    (∏ s, (M s).det ^ (letterWt m (d s) (vec s) (Fin.last m))) • blockAct K M (Th0 K m vec G) =
      Th0 K m vec (Lin (fun s => Aa (vec s) (M s)) G) := by
  unfold Formalism.MainNotions.G.Pol at hG
  rw [restrictSupport_eq_span] at hG
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, rfl⟩ := hx
    beta_reduce
    rw [mono_factor, map_prod, map_prod, map_prod, map_prod]
    simp only [Th0_emb, Lin_emb, tr_bA_emb]
    rw [tr_prod_smul]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [twist_theta K m hm (d s) (vec s) (M s) (hM s) _ (partS_Hd K d μ hμ s)]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, smul_add, hx, hy]
  | smul a x _ hx => simp only [map_smul]; rw [smul_comm, hx]

theorem tr_tens_int (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hy : y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s))) :
    ∃ R : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) O,
      (∏ s, (M s).det ^ (lam s (Fin.last m))) • blockAct Kf M y = map (algebraMap O Kf) R := by
  unfold tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have h1 := fun s => (nablaLTwMem O Kf m (lam s) (M s) (hM s) (F s)).1 (hF s)
    choose G _ hG2 using h1
    refine ⟨∏ s, blockEmb O s (G s), ?_⟩
    rw [map_prod, map_prod]
    simp only [tr_bA_emb]
    rw [tr_prod_smul]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [tr_map_emb, ← hG2 s]
    rfl
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨R1, h1⟩ := hx
    obtain ⟨R2, h2⟩ := hy
    exact ⟨R1 + R2, by rw [map_add, smul_add, h1, h2, map_add]⟩
  | smul a x _ hx =>
    obtain ⟨R1, h1⟩ := hx
    refine ⟨a • R1, ?_⟩
    rw [fl_map_smul, ← h1, ← algebraMap_smul Kf a x, map_smul, smul_comm, algebraMap_smul]

theorem tr_tens_lift (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (sO : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) O)
    (h : sO ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lam s)))) :
    ∃ y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s)),
      (∏ s, (M s).det ^ (lam s (Fin.last m))) • blockAct Kf M y = map (algebraMap O Kf) sO := by
  unfold tensorLat at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    have key : ∀ s, (M s).det ^ (lam s (Fin.last m)) • rowAct Kf (M s)
        (((M s).det ^ (lam s (Fin.last m)))⁻¹ • rowAct Kf (M s)⁻¹ (map (algebraMap O Kf) (G s))) =
        map (algebraMap O Kf) (G s) := by
      intro s
      rw [map_smul, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ (hM s).ne_zero), one_smul, tr_rowAct_inv _ _ (hM s)]
    refine ⟨∏ s, blockEmb Kf s (((M s).det ^ (lam s (Fin.last m)))⁻¹ •
      rowAct Kf (M s)⁻¹ (map (algebraMap O Kf) (G s))), ?_, ?_⟩
    · apply Submodule.subset_span
      refine ⟨_, fun s => ?_, rfl⟩
      rw [nablaLTwMem O Kf m (lam s) (M s) (hM s), key s]
      exact ⟨G s, hG s, rfl⟩
    · rw [map_prod, map_prod]
      simp only [tr_bA_emb]
      rw [tr_prod_smul]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [tr_map_emb, key s]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y1, m1, h1⟩ := hx
    obtain ⟨y2, m2, h2⟩ := hy
    exact ⟨y1 + y2, Submodule.add_mem _ m1 m2, by rw [map_add, smul_add, h1, h2, map_add]⟩
  | smul a x _ hx =>
    obtain ⟨y1, m1, h1⟩ := hx
    refine ⟨a • y1, Submodule.smul_mem _ _ m1, ?_⟩
    rw [fl_map_smul, ← h1, ← algebraMap_smul Kf a y1, map_smul, smul_comm, algebraMap_smul]

theorem tr_tens_le (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hy : y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s))) :
    y ∈ tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lam s))) := by
  unfold tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    obtain ⟨x, hx, hxF⟩ := hF s
    rw [← hxF]
    exact Submodule.smul_mem _ _ (nablaLLe O Kf (m + 1) (m + 1) _ (M s) (hM s) x hx)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul Kf a x]
    exact Submodule.smul_mem _ _ hx

end Gen

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem tr_theta (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m r : ℕ)
    (hm : 1 ≤ m) (d : Fin n' → ℕ) (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (P : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (hP : P ∈ Pol (KK O) (m + 1) d)
    (Q : MvPolynomial (Fin n' × Fin (m + 1)) O) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    subst p n' O w n' r g P = map (algebraMap O (KK O)) Q →
    (algebraMap O Kf w ^ (Avec (vecE n') d)) •
      ((∏ s, (Mx ι σ w φ r (fun x : Fin n' => x) hmat g s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m))) •
        blockAct Kf (Mx ι σ w φ r (fun x : Fin n' => x) hmat g)
          (thF hS m (vecE n') (fun x => la_tw ι σ x.val hmat) P)) =
      map (algebraMap O Kf) (Th0 O m (vecE n') Q) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro hPQ
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hP' := (pol_iff hS _ _ _).1 hP
  have hM := Mx_det (ι := ι) (σ := σ) hw φ r (fun x : Fin n' => x) hmat hh g hg
  unfold thF
  rw [tr_multi_twist Kf m hm (vecE n') d _ hM _ (Lin_Pol _ _ hP'), Lin_comp]
  have h1 := lift_eq hS φ hφ r (LLT n') (fun x : Fin n' => x) (fun _ => rfl) g hg P
  have hB : Bm ι σ w φ r (LLT n').vec (fun x : Fin n' => x) g = fun x => (if (LLT n').vec x then c else 1) •
      (Aa ((LLT n').vec x) (la_tw ι σ x.val hmat)⁻¹ *
        Aa ((LLT n').vec x) (Mx ι σ w φ r (fun x : Fin n' => x) hmat g x)) :=
    funext fun x => Bm_eq hw φ r (LLT n').vec (fun x : Fin n' => x) hmat hh g hg x
  rw [hB, Lin_smul _ _ _ hP'] at h1
  have hprod : ∏ x, (if (LLT n').vec x then c else 1) ^ d x = c ^ Avec (vecE n') d := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    show (if vecE n' x then c else 1) ^ d x = _
    split_ifs <;> simp
  rw [hprod] at h1
  have h2 : map (kapR hS) (liftSubst p n' O w r (LLT n') g P) = map (algebraMap O Kf) Q := by
    have : liftSubst p n' O w r (LLT n') g P = map (algebraMap O (KK O)) Q := hPQ
    rw [this, map_map]
    have hk : (kapR hS).comp (algebraMap O (KK O)) = algebraMap O Kf := RingHom.ext fun x => kapR_alg hS x
    rw [hk]
  rw [map_letter_substitution, ← h2, h1, map_smul]
  rfl

end

theorem transStep : TransStep := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS φ hφ m r hm hr1 hr2 d rest lam0 hlam hrest e he hmat g hh hg hbasis
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro Θ hΘ I _ sO hsO
  have hfrac := hS.frac_O
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  set M : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := Mx ι σ w φ r (fun x : Fin n' => x) hmat g with hMdef
  have hM : ∀ s, IsUnit (M s).det := Mx_det hw φ r _ hmat hh g hg
  have hH : ∀ lam : Fin n' → Fin (m + 1) → ℤ, IsDominant lam →
      Hten O lam (fun s => LeAt p ι σ w s.val e) = tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam s) (M s)) := by
    intro lam hl
    unfold Hten
    congr 1
    funext s
    show H0 O m _ (LeAt p ι σ w s.val e) = _
    rw [(edgeLat_of hS m r e _ hbasis).2.1]
    show H0 O m _ (colSpan O (M s)) = _
    rw [H0_eq_twisted_nabla (la_indep hinj) _ _ (lamAt_antitone' lam hl s) _ (hM s)]
  have hV : ∀ lam : Fin n' → Fin (m + 1) → ℤ, IsDominant lam →
      Vsp Kf lam = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam s))) := by
    intro lam hl
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (lamAt_antitone' lam hl s)]
  have hfl : IsDominant (flW (m := m) d) := flW_dom d
  have hl0 : IsDominant lam0 := by rw [hlam]; exact isDominant_add hfl hrest
  let dt : (Fin n' → Fin (m + 1) → ℤ) → Kf := fun lam => ∏ s, (M s).det ^ (lamAt lam s (Fin.last m))
  have hdt : dt lam0 = dt (flW d) * dt rest := by
    show ∏ s, _ = (∏ s, _) * ∏ s, _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hlam, lamAt_add, Pi.add_apply, zpow_add₀ (hM s).ne_zero]
  have hAr : Ar r lam0 = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam, Ar_add]
  have h1 := fun i => tr_tens_lift O Kf m (fun s => lamAt rest s) M hM (sO i) (hsO i)
  choose y hy1 hy2 using h1
  have hyV : ∀ i, y i ∈ Vsp Kf rest := by
    intro i
    rw [hV rest hrest]
    exact tr_tens_le O Kf m _ M hM _ (hy1 i)
  refine ⟨fun i => c ^ (-Ar r rest) • (⟨y i, hyV i⟩ : Vsp Kf rest), ?_, ?_⟩
  · intro i
    refine ⟨⟨y i, hyV i⟩, ?_, rfl⟩
    show y i ∈ Hten O rest (fun s => LeAt p ι σ w s.val e)
    rw [hH rest hrest]
    exact hy1 i
  · intro P Q hPQ v hv hvmem
    obtain ⟨y0, hy0, hvy⟩ := (mem_scale2 (O := O) (Vsp Kf lam0) (Hten O lam0 fun s => LeAt p ι σ w s.val e)
      (c ^ (1 : ℤ)) (c ^ (-Ar r lam0)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) v).1 hvmem
    rw [hH lam0 hl0] at hy0
    obtain ⟨R0, hR0⟩ := tr_tens_int O Kf m (fun s => lamAt lam0 s) M hM y0 hy0
    refine ⟨R0, ?_⟩
    apply map_injective _ hinj
    have way1 : (c ^ (Ar r lam0) * dt lam0) • blockAct Kf M (v : MvPolynomial _ Kf) =
        map (algebraMap O Kf) (C w * R0) := by
      rw [hvy, map_smul, smul_smul, map_mul, map_C, ← hR0, ← smul_eq_C_mul, smul_smul]
      congr 1
      have hcc : c ^ Ar r lam0 * c ^ (-Ar r lam0) = 1 := by rw [← zpow_add₀ hw, add_neg_cancel, zpow_zero]
      show c ^ Ar r lam0 * dt lam0 * (c ^ (1 : ℤ) * c ^ (-Ar r lam0)) = c * dt lam0
      rw [zpow_one]
      linear_combination (dt lam0 * c) * hcc
    have hA : Ar r (flW (m := m) d) = (Avec (vecE n') d : ℤ) :=
      flat_Ar r hr1 hr2 (vecE n') d (flW d) (isFlat_flW d)
    have hdfl : dt (flW d) = ∏ s, (M s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m)) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [flat_lam (vecE n') d (flW d) (isFlat_flW d) s]
    have way2 : (c ^ (Ar r lam0) * dt lam0) • blockAct Kf M (v : MvPolynomial _ Kf) =
        map (algebraMap O Kf) (∑ i, thAll O n' m (vecE n') (Q i) * sO i) := by
      rw [hv, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have t1 := tr_theta hS φ hφ m r (by omega) d hmat hh g hg (P i).1 (P i).2 (Q i) (hPQ i)
      rw [map_mul, map_mul, ← hy2 i]
      have e1 : map (algebraMap O Kf) (thAll O n' m (vecE n') (Q i)) = map (algebraMap O Kf) (Th0 O m (vecE n') (Q i)) :=
        rfl
      rw [e1, ← t1, hΘ (P i), hAr, hdt, hdfl, hA, zpow_add₀ hw, zpow_natCast]
      show _ • (_ * blockAct Kf M (c ^ (-Ar r rest) • y i)) = _
      rw [map_smul]
      simp only [smul_eq_C_mul, map_mul, map_pow]
      have hcc : (C (c ^ Ar r rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * C (c ^ (-Ar r rest)) = 1 := by
        rw [← C_mul, ← zpow_add₀ hw, add_neg_cancel, zpow_zero, C_1]
      linear_combination (C c ^ Avec (vecE n') d * C (∏ s, (M s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m))) *
        C (dt rest) * blockAct Kf M (thF hS m (vecE n') (fun x => la_tw ι σ x.val hmat) (P i).1) *
        blockAct Kf M (y i)) * hcc
    rw [← way2, way1]

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders MvPolynomial

def pmat (R : Type) [CommRing R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (TV n' k) R) :=
  Matrix.of fun l i : Fin r => X (A l, Fin.castLE hrk i) ^ P l

theorem pmat_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {n' r k : ℕ} (hrk : r ≤ k)
    (A : Fin r → Fin n') (P : Fin r → ℕ) : map f (pmat R hrk A P).det = (pmat R' hrk A P).det := by
  rw [RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun l i => ?_)
  simp [pmat]

theorem pmat_ne (R : Type) [CommRing R] [Nontrivial R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n')
    (P : Fin r → ℕ) (hA : Function.Injective A) (hP : ∀ l, P l ≠ 0) : (pmat R hrk A P).det ≠ 0 := by
  classical
  intro h
  let x : TV n' k → R := fun v => if ∃ l : Fin r, A l = v.1 ∧ Fin.castLE hrk l = v.2 then 1 else 0
  have hev : (MvPolynomial.eval x).mapMatrix (pmat R hrk A P) = 1 := by
    ext l i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, pmat, Matrix.of_apply, map_pow, eval_X,
      Matrix.one_apply]
    by_cases hli : l = i
    · subst hli
      have hx : x (A l, Fin.castLE hrk l) = 1 := by
        simp only [x]
        rw [if_pos ⟨l, rfl, rfl⟩]
      rw [hx, one_pow, if_pos rfl]
    · have hx : x (A l, Fin.castLE hrk i) = 0 := by
        simp only [x]
        rw [if_neg]
        rintro ⟨l', h1, h2⟩
        apply hli
        have e1 : l' = l := hA h1
        have e2 : l' = i := Fin.ext (by simpa using congrArg Fin.val h2)
        rw [← e1, e2]
      rw [hx, zero_pow (hP l), if_neg hli]
  have h2 := congrArg (MvPolynomial.eval x) h
  rw [RingHom.map_det, hev, Matrix.det_one, map_zero] at h2
  exact one_ne_zero h2

section Fac

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  {r k : ℕ}

theorem Ifirst_emb (hrk : r ≤ k) (i : Fin r) :
    (Ifirst r k).orderEmbOfFin (first_columns_card hrk) i = Fin.castLE hrk i := by
  have hmono : StrictMono (Fin.castLE hrk) := by
    intro a b hab
    rw [Fin.lt_def] at hab ⊢
    simpa using hab
  have h := Finset.orderEmbOfFin_unique (first_columns_card hrk) (f := Fin.castLE hrk)
    (fun x => by simp [Ifirst]) hmono
  exact (congrFun h i).symm

theorem subst_Del (w : O) (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n') (hrk : r ≤ k)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (j : ℤ) :
    subst p n' O w n' r g (Del p n' O F g j) = map (algebraMap O (KK O))
      (pmat O hrk (fun l => posOf n' (F.fr j l.val)) (fun l => p ^ (zF F j - F.fr j l.val).toNat)).det := by
  have hIc := first_columns_card (k := k) hrk
  simp only [Del, minorI, dif_pos hIc, Ifirst_emb hrk]
  rw [AlgHom.map_det, RingHom.map_det]
  congr 1
  ext l i
  have hE := (hV.2.2.2.2.1 j l.val l.2).2
  have hnn : ¬ IsNormal r ((posOf n' (F.fr j l.val), Fin.castLE hrk i) : TV n' k) := by
    simp only [IsNormal]
    rw [if_pos ((posOf_even hn _).mpr hE)]
    simp only [Fin.coe_castLE, not_le]
    exact i.2
  simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, twRow, pmat,
    map_pow, subst_xg w r hg hn _ hE, newVar, if_neg hnn, map_X]

theorem subst_Dtop' (w : O) (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r)
    (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (s : ℤ) :
    subst p n' O w n' r g (Dtop p n' O F hrk g s) = map (algebraMap O (KK O))
      (pmat O hrk (fun l => posOf n' (Arow F s l.val)) (fun l => p ^ (s - Arow F s l.val).toNat)).det := by
  have hok : RowsEvenTopsBefore F s := by
    intro l hl
    rw [symbolGeneratorData.dv_Arow_get hV hn hr s l hl]
    generalize_proofs hp
    have hm := List.getElem_mem hp
    simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at hm
    exact ⟨hm.2.2, hm.2.1, hm.1.2⟩
  rw [subst_top_determinant w F hrk hg hn s hok]
  rfl

end Fac

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders MvPolynomial

section Inj

variable {n' r : ℕ} [NeZero n']

private theorem fr_lt_fr_of_lt {r : ℕ} (f : ℕ → ℤ) (h : ∀ i, i + 1 < r → f i < f (i + 1)) {a b : ℕ}
    (hab : a < b) (hb : b < r) : f a < f b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h1 | h1
    · exact lt_trans (ih h1 (by omega)) (h b (by omega))
    · subst h1
      exact h a (by omega)

private theorem fr_le_fr_of_le {r : ℕ} (f : ℕ → ℤ) (h : ∀ i, i + 1 < r → f i < f (i + 1)) {a b : ℕ}
    (hab : a ≤ b) (hb : b < r) : f a ≤ f b := by
  rcases hab.lt_or_eq with h1 | h1
  · exact (fr_lt_fr_of_lt f h h1 hb).le
  · rw [h1]

theorem fr_pos_inj {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hG : G' ≤ n') (j : ℤ) : Function.Injective (fun l : Fin r => posOf n' (F.fr j l.val)) := by
  intro a b hab
  have hV := hF.2.1
  have ha := a.2
  have hb := b.2
  have hmono := hV.2.2.1 j
  have hprev : F.fr (j - 1) (r - 1) < F.fr j 0 := by
    have := hV.2.2.2.1 (j - 1)
    simpa using this
  have hprev0 : F.fr (j - 1) 0 ≤ F.fr (j - 1) (r - 1) :=
    fr_le_fr_of_le (F.fr (j - 1)) (hV.2.2.1 (j - 1)) (Nat.zero_le _) (by omega)
  have hwid := hF.2.2.1 j
  have hlo : ∀ l : Fin r, F.fr j 0 ≤ F.fr j l.val := fun l => fr_le_fr_of_le (F.fr j) hmono (Nat.zero_le _) l.2
  have hhi : ∀ l : Fin r, F.fr j l.val ≤ F.fr j (r - 1) := fun l => fr_le_fr_of_le (F.fr j) hmono (by omega) (by omega)
  have heq : F.fr j a.val = F.fr j b.val := by
    refine residue_position_injective_window n' (F.fr j 0) _ _ ⟨hlo a, ?_⟩ ⟨hlo b, ?_⟩ hab
    · have := hhi a
      omega
    · have := hhi b
      omega
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · exact absurd heq (ne_of_lt (fr_lt_fr_of_lt (F.fr j) hmono h1 b.2))
  · exact absurd heq (ne_of_gt (fr_lt_fr_of_lt (F.fr j) hmono h1 a.2))

private theorem emod_eq_of_posOf_eq (n' : ℕ) [NeZero n'] {x y : ℤ} (h : posOf n' x = posOf n' y) :
    x % n' = y % n' := by
  have hpos : (0:ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  simp only [posOf, Fin.mk.injEq] at h
  have hx0 := Int.emod_nonneg x hpos.ne'
  have hx1 := Int.emod_lt_of_pos x hpos
  have hy0 := Int.emod_nonneg y hpos.ne'
  have hy1 := Int.emod_lt_of_pos y hpos
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

private theorem posOf_sub_mul_eq_and_even_iff (n' : ℕ) [NeZero n'] (hn : Even n') (x q : ℤ) :
    posOf n' (x - n' * q) = posOf n' x ∧ (Even (x - n' * q) ↔ Even x) := by
  have hn' : Even (n' : ℤ) := by exact_mod_cast hn
  constructor
  · simp [posOf, Int.sub_emod]
  · simp [Int.even_sub, Int.even_mul, hn']

private theorem arow_lt_self_of_valid {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁)
    (hn : Even n') (hr : 1 ≤ r) (s : ℤ) (l : ℕ) (hl : l < r) : Arow F s l < s := by
  rw [symbolGeneratorData.dv_Arow_get hV hn hr s l hl]
  generalize_proofs hp
  have hm := List.getElem_mem hp
  simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at hm
  exact hm.1.2

theorem arow_pos_inj {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hn : Even n') (hG : G' ≤ n') (s : ℤ) : Function.Injective (fun l : Fin r => posOf n' (Arow F s l.val)) := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    intro a
    exact a.elim0
  have hV := hF.2.1
  have h1 := fr_pos_inj hF hG 0
  have hpos : (0:ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have key : ∀ l l' : ℕ, l < l' → l' < r →
      posOf n' (Arow F s l) = posOf n' (Arow F s l') → False := by
    intro l l' hll hl' heq
    have hbc : Arow F s l' < Arow F s l := symbolGeneratorData.dv_Arow_anti hV hn hr0 s l l' hll hl'
    have hmod := emod_eq_of_posOf_eq n' heq
    have hdvd : (n' : ℤ) ∣ Arow F s l - Arow F s l' := Int.ModEq.dvd hmod.symm
    have hcb : (n' : ℤ) ≤ Arow F s l - Arow F s l' := Int.le_of_dvd (by omega) hdvd
    have hcs := arow_lt_self_of_valid hV hn hr0 s l (by omega)
    have hex : ∀ i : Fin r, ∃ m : Fin l', posOf n' (Arow F s m.val) = posOf n' (F.fr 0 i.val) := by
      intro i
      set b := Arow F s l'
      set x := F.fr 0 i.val
      have hq1 := Int.mul_ediv_add_emod (x - b - 1) n'
      have hq2 := Int.emod_nonneg (x - b - 1) hpos.ne'
      have hq3 := Int.emod_lt_of_pos (x - b - 1) hpos
      obtain ⟨hp1, hp2⟩ := posOf_sub_mul_eq_and_even_iff n' hn x ((x - b - 1) / n')
      have hTT := hV.2.2.2.2.1 0 i.val i.2
      have hlo : b < x - n' * ((x - b - 1) / n') := by
        generalize (n' : ℤ) * ((x - b - 1) / n') = m at hq1 ⊢
        generalize (x - b - 1) % (n' : ℤ) = e at hq1 hq2 hq3
        omega
      have hhi : x - n' * ((x - b - 1) / n') < s := by
        generalize (n' : ℤ) * ((x - b - 1) / n') = m at hq1 ⊢
        generalize (x - b - 1) % (n' : ℤ) = e at hq1 hq2 hq3
        omega
      obtain ⟨m, hm, hy⟩ := symbolGeneratorData.dv_Arow_newer hV hn hr0 s l' hl' (x - n' * ((x - b - 1) / n'))
        ⟨hp1 ▸ hTT.1, hp2.mpr hTT.2⟩ hhi hlo
      exact ⟨⟨m, hm⟩, by rw [← hy, hp1]⟩
    choose ψ hψ using hex
    have hinj : Function.Injective ψ := by
      intro i i' hii
      apply h1
      show posOf n' (F.fr 0 i.val) = posOf n' (F.fr 0 i'.val)
      rw [← hψ i, ← hψ i', hii]
    have := Fintype.card_le_of_injective ψ hinj
    simp at this
    omega
  intro a b hab
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h2 | h2
  · exact key a b h2 b.2 hab
  · exact key b a h2 a.2 hab.symm

end Inj

def SPR (R : Type) [CommRing R] (p : ℕ) {n' r k : ℕ} [NeZero n'] (F : Frames n' r) (hrk : r ≤ k) (c' Q : ℕ) :
    MvPolynomial (TV n' k) R :=
  (∏ j ∈ Finset.range F.J,
      (pmat R hrk (fun l => posOf n' (F.fr (j : ℤ) l.val)) (fun l => p ^ (zF F (j : ℤ) - F.fr (j : ℤ) l.val).toNat)).det ^
        alpha p F k (j : ℤ)) ^ c' *
    (∏ j ∈ Finset.range F.J,
      (pmat R hrk (fun l => posOf n' (F.fr (j : ℤ) l.val)) (fun l => p ^ (zF F (j : ℤ) - F.fr (j : ℤ) l.val).toNat)).det ^
        c') *
    ∏ s ∈ F.TT, (pmat R hrk (fun l => posOf n' (Arow F (s.val : ℤ) l.val))
      (fun l => p ^ ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat)).det ^ ((2 * Q + 3) * c' + k * Q)

theorem SPR_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ℕ) {n' r k : ℕ} [NeZero n']
    (F : Frames n' r) (hrk : r ≤ k) (c' Q : ℕ) : map f (SPR R p F hrk c' Q) = SPR R' p F hrk c' Q := by
  unfold SPR
  simp only [map_mul, map_pow, map_prod, pmat_map]

theorem SPR_ne (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (hp : p ≠ 0) {n' r k : ℕ} [NeZero n']
    {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hn : Even n') (hG : G' ≤ n') (hrk : r ≤ k) (c' Q : ℕ) : SPR R p F hrk c' Q ≠ 0 := by
  unfold SPR
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) ?_) ?_
  · exact Finset.prod_ne_zero_iff.2 fun j _ =>
      pow_ne_zero _ (pmat_ne R hrk _ _ (fr_pos_inj hF hG _) fun l => pow_ne_zero _ hp)
  · exact Finset.prod_ne_zero_iff.2 fun j _ =>
      pow_ne_zero _ (pmat_ne R hrk _ _ (fr_pos_inj hF hG _) fun l => pow_ne_zero _ hp)
  · exact Finset.prod_ne_zero_iff.2 fun s _ =>
      pow_ne_zero _ (pmat_ne R hrk _ _ (arow_pos_inj hF hn hG _) fun l => pow_ne_zero _ hp)

theorem subst_SPtrue {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
    {r k : ℕ} (w : O) (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (hrk : r ≤ k)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (c' Q : ℕ) :
    subst p n' O w n' r g (SPtrue p n' O F hrk g c' Q) = map (algebraMap O (KK O)) (SPR O p F hrk c' Q) := by
  unfold SPtrue SPR R0 DtopProd
  simp only [map_mul, map_pow, map_prod, subst_Del w F hV hn hrk hg, subst_Dtop' w F hV hn hr hrk hg]

theorem spStep (C : ℝ) : SPStep C := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ hrk F hF
    g hg
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro c' Q
  have hn : Even n' := hSet.1.even
  have hr : 1 ≤ r := by have := H.2.1; omega
  have hG : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  refine ⟨SPR O p F hrk c' Q, subst_SPtrue w F hF.2.1 hn hr hrk hg c' Q, ?_⟩
  rw [SPR_map]
  exact SPR_ne _ p (Fact.out : p.Prime).ne_zero hF hn hG hrk c' Q

private theorem weight_single_eq_multideg {n' k : ℕ} (m : Fin n' × Fin k →₀ ℕ) :
    Finsupp.weight (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ)) m = fun i => multideg m i := by
  funext i
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [multideg, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

private theorem mem_Pol_iff_isWeightedHomogeneous {R : Type} [CommRing R] {n' k : ℕ} (d : Fin n' → ℕ)
    (F : MvPolynomial (Fin n' × Fin k) R) :
    F ∈ Pol R k d ↔ IsWeightedHomogeneous (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ)) F d := by
  simp only [Pol, mem_restrictSupport_iff, IsWeightedHomogeneous, weight_single_eq_multideg]
  constructor
  · intro h m hm
    funext i
    exact h (mem_support_iff.mpr hm) i
  · intro h m hm i
    exact congrFun (h (mem_support_iff.mp hm)) i

private theorem isWeightedHomogeneous_aeval_of_homogeneous {σ K M : Type} [CommRing K] [AddCommMonoid M] (w : σ → M)
    (f : σ → MvPolynomial σ K) (hf : ∀ v, IsWeightedHomogeneous w (f v) (w v)) {P : MvPolynomial σ K} {e : M}
    (hP : IsWeightedHomogeneous w P e) : IsWeightedHomogeneous w (aeval f P) e := by
  classical
  rw [P.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  apply IsWeightedHomogeneous.C_mul
  have hme : Finsupp.weight w m = e := hP (mem_support_iff.mp hm)
  rw [← hme, Finsupp.weight_apply]
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hf v).pow _

theorem substPol : SubstPol := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS φ hφ k r d g hg F hF
  rw [mem_Pol_iff_isWeightedHomogeneous] at hF ⊢
  simp only [subst, liftSubst]
  refine isWeightedHomogeneous_aeval_of_homogeneous _ _ ?_ hF
  intro v
  have hX : ∀ b : Fin k, IsWeightedHomogeneous (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ))
      (X (v.1, b) : MvPolynomial (TV n' k) (KK O)) (Pi.single v.1 1) :=
    fun b => isWeightedHomogeneous_X (KK O) _ (v.1, b)
  have hmC : ∀ {P : MvPolynomial (TV n' k) (KK O)} (c : KK O),
      IsWeightedHomogeneous (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ)) P (Pi.single v.1 1) →
      IsWeightedHomogeneous (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ)) (P * C c)
        (Pi.single v.1 1) := by
    intro P c hP
    simpa using hP.mul (isWeightedHomogeneous_C _ c)
  split_ifs
  · apply IsWeightedHomogeneous.sum
    intro b _
    apply hmC
    split_ifs
    · exact (hX b).C_mul _
    · exact hX b
  · apply IsWeightedHomogeneous.sum
    intro b _
    apply hmC
    split_ifs
    · exact (hX b).C_mul _
    · exact hX b

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.Pf14

theorem rest6a (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  source_integrality_of_substitution transStep substPol 1 one_pos (fun C _ => spStep C) D CLa Ck Crk Cdeg

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def opWord {R : Type} [CommRing R] {n' k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) R) :
    MvPolynomial (Fin n' × Fin k) R :=
  l.foldr (fun y f => X (y.1, y.2.1) * pderiv (y.1, y.2.2) f) f

def OpCl {R : Type} [CommRing R] {n' k : ℕ} (TT : Finset (Fin n')) (c : ℕ)
    (M : Submodule R (MvPolynomial (Fin n' × Fin k) R)) : Submodule R (MvPolynomial (Fin n' × Fin k) R) :=
  Submodule.span R {y | ∃ f ∈ M, ∃ l : List (Fin n' × (Fin k × Fin k)), (∀ z ∈ l, z.1 ∈ TT) ∧
    (∀ s, (l.filter fun z => z.1 = s).length ≤ c) ∧ y = opWord l f}

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n'))
  (lam0 : Fin n' → Fin (m + 1) → ℤ)

def SgOp (c0 : ℕ) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) :
    Submodule (KK O) (MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) :=
  OpCl TT c0 (Submodule.span (KK O) (Set.range fun b => (FsB b : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))))

def CloudBAt (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1)) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ κ : ℕ, (κ : ℝ) ≤ bK ∧
    ∀ (n2 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)), (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e) →
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O,
          (∑ x, c x • S x) ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam0 e) →
          ∃ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
            (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB ∧
            Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e ∧
            Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) ∧
            ∃ (Λ : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))) →ₗ[Kf] Module.Dual Kf (Vsp Kf lam0)) (cc : O),
              (∀ T, algebraMap O Kf cc * be p r lam0 (∑ x, c x • S x) (Λ T) =
                (p : Kf) ^ κ * be p r (flW (dT TT lam0)) (Θ F1) T) ∧
              (∀ T ∈ Re' p ι σ w r (flW (dT TT lam0)) e, Λ T ∈ Re' p ι σ w r lam0 e ∧
                be p r lam0 (∑ x, c x • S x) (Λ T) ∈ Set.range (algebraMap O Kf)) ∧
              (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ (i : ℤ),
                ∀ T ∈ scale (algebraMap O Kf w ^ i) (Re' p ι σ w r (flW (dT TT lam0)) e'),
                  Λ T ∈ scale (algebraMap O Kf w ^ (i - loss)) (Re' p ι σ w r lam0 e')) ∧
              (∀ (i : ℤ), ∀ T ∈ scale (algebraMap O Kf w ^ i)
                  (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)),
                Λ T ∈ scale (algebraMap O Kf w ^ (i - loss)) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)))

def FlatAt (c0 cP : ℕ) (bT bD : ℝ) (e : Edge W Qq (m + 1)) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ tF DF : ℕ, (tF : ℝ) ≤ bT ∧ (DF : ℝ) ≤ bD ∧
    ∀ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB →
      Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e →
      Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) →
      ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))),
        T ∈ scale (algebraMap O Kf w ^ (-(tF : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
        T ∈ Re' p ι σ w r (flW (dT TT lam0)) e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          T ∈ scale (algebraMap O Kf w ^ (cP : ℤ)) (Re' p ι σ w r (flW (dT TT lam0)) e')) ∧
        ValLe (p : O) DF (be p r (flW (dT TT lam0)) (Θ F1) T)

end At

def CloudBStep (C CK CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        CloudBAt p n' ι σ w r TT lam0 c0 (r * TT.card * c0 + 2 * r * n' * cpp)
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e FsB Θ

def FlatStep (C Ct0 CD CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        FlatAt p n' ι σ w r TT lam0 c0 (cPrime n' r TT.card c0 cpp cStar)
          (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0)
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e FsB Θ

def RestCloudB (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → CloudBStep C CK CLa

def RestFlat (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CDf C₁ : ℝ, 0 < Ct0 ∧ 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → FlatStep C Ct0 CDf CLa

theorem test_bound_of_two_halves (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hCl : RestCloudB D CLa Ck Crk Cdeg) (hFl : RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RemainingInputsAfter D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨CK, C₂, hCK, hC2, hC⟩ := hCl hA
  obtain ⟨Ct0, CDf, C₃, h0, h1, hC3, hF⟩ := hFl hA h14a h14b
  refine ⟨Ct0, CK + CDf, max C₂ C₃, h0, by linarith, lt_of_lt_of_le hC2 (le_max_left _ _), ?_⟩
  intro C hCC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨κ, hκ, hcl⟩ := hC C (le_trans (le_max_left _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨tF, DF, htF, hDF, hfl⟩ := hF C (le_trans (le_max_right _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0
    aT bT a Y cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  refine ⟨tF + (r * TT.card * c0 + 2 * r * n' * cpp), κ + DF, ?_, ?_, ?_⟩
  · unfold om
    push_cast
    linarith
  · push_cast
    have e1 : (CK + CDf) * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a =
        CK * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a + CDf * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a := by
      ring
    push_cast at hκ hDF
    rw [e1]
    linarith
  intro n2 sh hsh S hS c hv
  obtain ⟨F1, f1, f2, f3, Λ, cc, l1, l2, l3, l4⟩ := hcl n2 sh hsh S hS c hv
  obtain ⟨T, t1, t2, t3, t4⟩ := hfl F1 f1 f2 f3
  refine ⟨Λ T, ?_, (l2 T t2).1, ?_, ?_⟩
  · have := l4 _ T t1
    convert this using 3
    push_cast
    ring
  · intro e' he' htg hne
    have := l3 e' he' htg _ T (t3 e' he' htg hne)
    convert this using 3
    unfold cPrime
    push_cast
    ring
  · obtain ⟨aa, haa⟩ := (l2 T t2).2
    obtain ⟨y, b', hy, hyb⟩ := t4
    refine ⟨aa, cc * b', haa.symm, ?_⟩
    have hinj : Function.Injective (algebraMap O Kf) := by
      have := hSet.1.frac_O
      exact IsFractionRing.injective O Kf
    apply hinj
    have h5 := l1 T
    rw [← haa, hy] at h5
    have : algebraMap O Kf (aa * (cc * b')) = (algebraMap O Kf cc * algebraMap O Kf aa) * algebraMap O Kf b' := by
      simp only [map_mul]; ring
    rw [this, h5, mul_assoc, ← map_mul, hyb]
    simp [pow_add]

end Formalism.MainNotions.TestSideCounting
end
end
