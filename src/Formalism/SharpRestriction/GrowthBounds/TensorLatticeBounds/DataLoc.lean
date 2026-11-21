import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G

section Loc

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem p_ne (h : HidaSetting p n' W Qq O Kf ι σ j w) : (p : Qq) ≠ 0 := by
  have := h.frac_alt
  have h1 : algebraMap W Qq (p : W) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).2 h.p_unif.ne_zero
  simpa using h1

theorem decomp (h : HidaSetting p n' W Qq O Kf ι σ j w) (x : Qq) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : Wˣ), x = algebraMap W Qq u * (p : Qq) ^ n := by
  have := h.frac_alt
  have hp := p_ne h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨i, u1, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 h.p_unif
  obtain ⟨k, u2, hb'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 h.p_unif
  refine ⟨(i : ℤ) - k, u1 * u2⁻¹, ?_⟩
  have hu2 : algebraMap W Qq (u2 : W) * algebraMap W Qq ((u2⁻¹ : Wˣ) : W) = 1 := by
    rw [← map_mul]; simp
  have hu20 : algebraMap W Qq (u2 : W) ≠ 0 := left_ne_zero_of_mul_eq_one hu2
  rw [ha, hb', zpow_sub₀ hp, div_eq_iff (by
    rw [map_mul, map_pow, map_natCast]; exact mul_ne_zero hu20 (pow_ne_zero _ hp))]
  simp only [map_mul, map_pow, map_natCast, Units.val_mul, zpow_natCast]
  have hk : (p : Qq) ^ k ≠ 0 := pow_ne_zero _ hp
  calc algebraMap W Qq (u1 : W) * (p : Qq) ^ i
      = algebraMap W Qq (u1 : W) * (algebraMap W Qq (u2 : W) * algebraMap W Qq ((u2⁻¹ : Wˣ) : W)) *
          ((p : Qq) ^ i / (p : Qq) ^ k * (p : Qq) ^ k) := by
        rw [hu2, mul_one, div_mul_cancel₀ _ hk]
    _ = _ := by ring

def line (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (n : ℤ) : Submodule W (Fin 1 → Qq) :=
  Submodule.span W {fun _ => (p : Qq) ^ n}

theorem colSpan_one (g : Matrix (Fin 1) (Fin 1) Qq) : colSpan W g = Submodule.span W {fun _ => g 0 0} := by
  unfold colSpan
  congr 1
  ext v
  constructor
  · rintro ⟨c, rfl⟩
    rw [Set.mem_singleton_iff]
    funext i
    rw [Subsingleton.elim i 0, Subsingleton.elim c 0]
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    refine ⟨0, ?_⟩
    rw [hv]
    funext i
    rw [Subsingleton.elim i 0]

theorem lat1 (h : HidaSetting p n' W Qq O Kf ι σ j w) (L : Submodule W (Fin 1 → Qq)) (hL : IsLattice W L) :
    ∃ n : ℤ, L = line W p n := by
  obtain ⟨g, hg, rfl⟩ := hL
  rw [Matrix.det_fin_one] at hg
  obtain ⟨n, u, hx⟩ := decomp h (g 0 0) hg.ne_zero
  refine ⟨n, ?_⟩
  rw [colSpan_one, hx, line]
  have : (fun _ : Fin 1 => algebraMap W Qq (u : W) * (p : Qq) ^ n) = (u : W) • (fun _ : Fin 1 => (p : Qq) ^ n) := by
    funext i
    rw [Pi.smul_apply, Algebra.smul_def]
  rw [this]
  exact Submodule.span_singleton_smul_eq u.isUnit _


theorem le_of_mem (h : HidaSetting p n' W Qq O Kf ι σ j w) {a b : ℤ}
    (hm : (fun _ : Fin 1 => (p : Qq) ^ a) ∈ line W (Qq := Qq) p b) : b ≤ a := by
  have := h.frac_alt
  have hp := p_ne h
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
  have hc0 : algebraMap W Qq c * (p : Qq) ^ b = (p : Qq) ^ a := by
    have := congrFun hc 0
    rwa [Pi.smul_apply, Algebra.smul_def] at this
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + (k + 1 : ℕ) := ⟨(b - a - 1).toNat, by push_cast; omega⟩
  have h1 : algebraMap W Qq (c * (p : W) ^ (k + 1)) = 1 := by
    rw [map_mul, map_pow, map_natCast]
    rw [hk, zpow_add₀ hp, zpow_natCast] at hc0
    have ha : (p : Qq) ^ a ≠ 0 := zpow_ne_zero _ hp
    apply mul_left_cancel₀ ha
    calc (p : Qq) ^ a * (algebraMap W Qq c * (p : Qq) ^ (k + 1))
        = algebraMap W Qq c * ((p : Qq) ^ a * (p : Qq) ^ (k + 1)) := by ring
      _ = (p : Qq) ^ a := hc0
      _ = (p : Qq) ^ a * 1 := (mul_one _).symm
  have h2 : c * (p : W) ^ (k + 1) = 1 := IsFractionRing.injective W Qq (by rw [h1, map_one])
  have h3 : IsUnit ((p : W) ^ (k + 1)) := IsUnit.of_mul_eq_one c (by rw [mul_comm]; exact h2)
  exact h.p_unif.not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero k)).1 h3)


theorem map_line (h : HidaSetting p n' W Qq O Kf ι σ j w) (a n : ℤ) :
    (line W (Qq := Qq) p n).map
      ((Matrix.mulVecLin (Matrix.scalar (Fin 1) ((p : Qq) ^ a))).restrictScalars W) = line W p (a + n) := by
  unfold line
  rw [Submodule.map_span, Set.image_singleton]
  congr 2
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, zpow_add₀ (p_ne h)]

abbrev places1 (h : HidaSetting p n' W Qq O Kf ι σ j w) : Places p O Kf where
  w := w
  nV := 1
  n' := fun _ => n'
  W := fun _ => W
  Qq := fun _ => Qq
  ι := fun _ => ι
  σ := fun _ => σ
  j := fun _ => j
  setting := fun _ => h
  m := 0
  r := 1
  lam0 := fun _ _ _ => 0
  dom := fun _ _ _ _ _ => le_rfl

def homoth (h : HidaSetting p n' W Qq O Kf ι σ j w) : Multiplicative ℤ →* GL (Fin 1) Qq :=
  (Units.map ((Matrix.scalar (Fin 1) : Qq →+* Matrix (Fin 1) (Fin 1) Qq) : Qq →* Matrix (Fin 1) (Fin 1) Qq)).comp
    (zpowersHom Qqˣ (Units.mk0 (p : Qq) (p_ne h)))

theorem homoth_val (h : HidaSetting p n' W Qq O Kf ι σ j w) (γ : Multiplicative ℤ) :
    ((homoth h γ : GL (Fin 1) Qq) : Matrix (Fin 1) (Fin 1) Qq) =
      Matrix.scalar (Fin 1) ((p : Qq) ^ (Multiplicative.toAdd γ)) := by
  show (Matrix.scalar (Fin 1)) ((((zpowersHom Qqˣ (Units.mk0 (p : Qq) (p_ne h))) γ : Qqˣ)) : Qq) = _
  rw [zpowersHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

def level1 (h : HidaSetting p n' W Qq O Kf ι σ j w) : Level (places1 h) where
  Γ := Multiplicative ℤ
  act := fun _ => (homoth h : Multiplicative ℤ →* GL (Fin 1) Qq)
  χ := 1

theorem smul1 (h : HidaSetting p n' W Qq O Kf ι σ j w) (γ : Multiplicative ℤ) (L : (places1 h).Tup) (n : ℤ)
    (hL : L (0 : Fin 1) = line W p n) :
    (level1 h).smul γ L (0 : Fin 1) = line W p (Multiplicative.toAdd γ + n) := by
  show Submodule.map ((Matrix.mulVecLin ((homoth h γ : GL (Fin 1) Qq) : Matrix (Fin 1) (Fin 1) Qq)).restrictScalars W)
    (L (0 : Fin 1)) = _
  rw [homoth_val, hL]
  exact map_line h _ _



def gat1 (h : HidaSetting p n' W Qq O Kf ι σ j w) : GAtP p where
  O := O
  Kf := Kf
  P := places1 h
  comp := Unit
  lev := fun _ => level1 h
  e := 0



end Loc

theorem places_nonempty (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] : Nonempty (Places p O Kf) :=
  ⟨{ w := 0, nV := 0, n' := fun v => v.elim0, W := fun v => v.elim0, Qq := fun v => v.elim0,
     ringW := fun v => v.elim0, domW := fun v => v.elim0, dvrW := fun v => v.elim0, fieldQ := fun v => v.elim0,
     algWQ := fun v => v.elim0, ι := fun v => v.elim0, σ := fun v => v.elim0, j := fun v => v.elim0,
     setting := fun v => v.elim0, m := 0, r := 0, lam0 := fun v => v.elim0, dom := fun v => v.elim0 }⟩

def levTriv {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) : Level P where
  Γ := Unit
  act := fun _ => 1
  χ := 1




section Chain

variable {p : ℕ} (G : GAtP p)

def cBound : ℕ := ∑ v, ∑ s, ∑ i, (G.P.lam0 v s i).natAbs

theorem abs_le_cBound (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (i : Fin (G.P.m + 1)) :
    |G.P.lam0 v s i| ≤ (cBound G : ℤ) := by
  have h1 : (G.P.lam0 v s i).natAbs ≤ ∑ i, (G.P.lam0 v s i).natAbs :=
    Finset.single_le_sum (f := fun i => (G.P.lam0 v s i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : ∑ i, (G.P.lam0 v s i).natAbs ≤ ∑ s, ∑ i, (G.P.lam0 v s i).natAbs :=
    Finset.single_le_sum (f := fun s => ∑ i, (G.P.lam0 v s i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  have h3 : ∑ s, ∑ i, (G.P.lam0 v s i).natAbs ≤ cBound G :=
    Finset.single_le_sum (f := fun v => ∑ s, ∑ i, (G.P.lam0 v s i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1.trans (h2.trans h3)

theorem liftWt_anti (t m : ℕ) (lam : Fin (m + 1) → ℤ) (hl : Antitone lam) (c : ℤ) (hc : -lam (Fin.last m) ≤ c)
    (j : ℕ) : Antitone (liftWt t m lam (fun _ => c) j) := by
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  unfold liftWt
  split_ifs with h1 h2 h2
  · exact hl (show (⟨a.val, h2⟩ : Fin (m + 1)) ≤ ⟨b.val, h1⟩ from hab')
  · omega
  · have := hl (Fin.le_last (⟨a.val, h2⟩ : Fin (m + 1)))
    show -c ≤ _
    omega
  · exact le_rfl

def fillsOf (TT : ∀ v : Fin G.P.nV, Finset (Fin (G.P.n' v))) (t mm : ℕ) : Fills G where
  TT := TT
  a := fun v s => G.P.lam0 v s 0
  b := fun v s => -G.P.lam0 v s (Fin.last G.P.m)
  c := cBound G
  base := fun v s => ⟨fun _ => ⟨rfl, (neg_neg _).symm, fun i _ _ => abs_le_cBound G v s i⟩,
    fun _ i => abs_le_cBound G v s i⟩
  t := t
  mm := mm
  w := fun v _ s => max (cBound G : ℤ) (-(G.P.lam0 v s (Fin.last G.P.m)))
  w_ge := fun _ _ => le_rfl
  w_mono := fun _ _ _ _ => le_rfl
  domJ := fun j v s => liftWt_anti t G.P.m (G.P.lam0 v s) (G.P.dom v s) _ (le_max_right _ _) j


variable {G}

def levelsOf (Fl : Fills G) : Levels Fl where
  compS := fun _ => Unit
  levS := fun _ _ => levTriv _

def chainOf {Fl : Fills G} (Lv : Levels Fl) : Chain Lv where
  Kz := fun _ => 0


end Chain

end Formalism.MainNotions.G.Inhab

end
