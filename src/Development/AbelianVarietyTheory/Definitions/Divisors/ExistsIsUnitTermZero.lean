import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums

noncomputable section

open IsLocalRing GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.PreModel

open TateSys

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : VPre bar q W A)

theorem term_mem (y : Φ.Y) (mu : Fin s → Φ.X y) (c : Φ.Q) (j : ℕ) (h : (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) :
    Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := by
  refine Ideal.mul_mem_left _ _ ?_
  have h0 : ∀ i, 0 ≤ qW W (Φ.δ y i) mu := fun i => qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h1 : mono W (Φ.t y) (Φ.δ y) mu ∈ maximalIdeal (Φ.V y) ^ ∑ i, (qW W (Φ.δ y i) mu).toNat := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Φ.t_mem y i).1 _
  refine Ideal.pow_le_pow_right ?_ h1
  have : ((∑ i, (qW W (Φ.δ y i) mu).toNat : ℕ) : ℤ) = ∑ i, qW W (Φ.δ y i) mu := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h0 i)
  omega



theorem low_finite (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (j : ℕ) :
    {mu | P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}.Finite := by
  obtain ⟨c₀, hc₀, hq⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W Φ.posW
  let D : LinearMap.BilinForm ℤ (Φ.X y) := ∑ i, Φ.δ y i
  have hD : ∀ x, D x x = ∑ i, Φ.δ y i x x := fun x => by simp [D, LinearMap.sum_apply]
  have hDs : ∀ a b, D a b = D b a := fun a b => by
    simp only [D, LinearMap.sum_apply]; exact Finset.sum_congr rfl fun i _ => (Φ.bal y i).1 a b
  have hDp : ∀ x, x ≠ 0 → 0 < D x x := fun x hx => by
    rw [hD]
    obtain ⟨i, hi⟩ := Φ.pos y x hx
    exact lt_of_lt_of_le hi (Finset.single_le_sum (f := fun i => Φ.δ y i x x) (fun i _ => Φ.nonneg y i x) (Finset.mem_univ i))
  refine (Set.Finite.pi' fun _ : Fin s => GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite _ D hDs hDp ⌈(j : ℝ) / c₀⌉).subset ?_
  rintro mu ⟨-, hmu⟩ u
  have h1 : ∀ i, c₀ * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) ≤ (qW W (Φ.δ y i) mu : ℝ) := fun i =>
    hq _ (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h2 : c₀ * ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) ≤ ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) := by
    have : ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) = ∑ i, ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) := by
      simp only [hD]; push_cast; exact Finset.sum_comm
    rw [this, Finset.mul_sum]; push_cast
    exact Finset.sum_le_sum fun i _ => by exact_mod_cast h1 i
  have h3 : (D (mu u) (mu u) : ℝ) ≤ ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun u => D (mu u) (mu u)) (fun u _ => by
      by_cases h : mu u = 0
      · simp [h]
      · exact (hDp _ h).le) (Finset.mem_univ u)
  have h4 : ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) < j := by exact_mod_cast hmu
  have h5 : (D (mu u) (mu u) : ℝ) ≤ (j : ℝ) / c₀ := by
    rw [le_div_iff₀' hc₀]; nlinarith
  show D (mu u) (mu u) ≤ ⌈(j : ℝ) / c₀⌉
  exact_mod_cast h5.trans (Int.le_ceil _)

theorem exists_sum (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (c : Φ.Q) : ∃ x : Φ.V y, ∀ j : ℕ,
    ∃ S : Finset (Fin s → Φ.X y), (∀ mu ∈ S, P mu) ∧ (∀ mu, P mu → mu ∉ S → (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) ∧
      x - ∑ mu ∈ S, Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := by
  classical
  haveI : IsAdicComplete (maximalIdeal (Φ.V y)) (Φ.V y) := (Φ.cn y).2.2.1
  let S : ℕ → Finset (Fin s → Φ.X y) := fun j => (low_finite Φ y P j).toFinset
  have hS : ∀ j mu, mu ∈ S j ↔ P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ) := fun j mu => Set.Finite.mem_toFinset _
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := maximalIdeal (Φ.V y)) (M := Φ.V y) inferInstance
    (f := fun j => ∑ mu ∈ S j, Φ.term y mu c) (by
      intro m n hmn
      have hsub : S m ⊆ S n := fun mu hmu => by
        rw [hS] at hmu ⊢; exact ⟨hmu.1, hmu.2.trans_le (by exact_mod_cast hmn)⟩
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Finset.sum_sdiff hsub, sub_add_cancel_right]
      refine neg_mem (Ideal.sum_mem _ fun mu hmu => ?_)
      obtain ⟨p, p'⟩ := Finset.mem_sdiff.1 hmu
      refine term_mem Φ y mu c m ?_
      by_contra h
      exact p' ((hS m mu).2 ⟨((hS n mu).1 p).1, by omega⟩))
  refine ⟨x, fun j => ⟨S j, fun mu h => ((hS j mu).1 h).1, fun mu h hn => ?_, ?_⟩⟩
  · by_contra h'
    exact hn ((hS j mu).2 ⟨h, by omega⟩)
  · have := (hx j).symm
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

def lim (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (c : Φ.Q) : Φ.V y := (exists_sum Φ y P c).choose

end



def const : VPre (O := ℤ) id 1 !![1] ℚ :=
  { posW := VSys.tate.posW, Y := PUnit, V := fun _ => PowerSeries ℚ, cn := fun y => VSys.tate.cn y
    ev := fun _ => PowerSeries.C
    ev_loc := fun _ => ⟨fun a ha => by
      rcases eq_or_ne a 0 with rfl | h
      · simp at ha
      · exact h.isUnit⟩
    X := fun _ => ℤ, rank_le := fun _ => by simp, m := fun _ => 1, t := fun _ _ => PowerSeries.X
    t_mem := fun y => VSys.tate.t_mem y, δ := fun _ _ => LinearMap.mul ℤ ℤ, bal := fun y => VSys.tate.bal y
    nonneg := fun y => VSys.tate.nonneg y, pos := fun y => VSys.tate.pos y, Q := Unit, u := fun _ _ _ => 1
    u_unit := fun _ _ => ⟨(), isUnit_one⟩ }

def cpt : const.Y := PUnit.unit

def toZ (x : const.X cpt) : ℤ := x



end GlobalTheory.Poinc.PreModel
