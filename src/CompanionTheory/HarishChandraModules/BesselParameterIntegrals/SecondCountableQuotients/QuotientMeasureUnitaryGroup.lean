import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.PolarUH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.ModExists

section
open Matrix

namespace CompanionTheory.D.Upq.QuotSetU

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ}

local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def WB (k r : ℕ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), ¬ (inW k r i ∧ inW k r j) → a i j = if i = j then 1 else 0

theorem wb_of_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {h : 𝕄} (hh : h ∈ UWset k r z) : WB k r h :=
  fun i j hij => uw_block hh i j hij

theorem nc_conj {a b m : 𝕄} (ha : WB k r a) (hb : WB k r b) (hab : a * b = 1) (hm : NC k r m) :
    NC k r (a * m * b) := by
  intro i j hj hi
  by_cases hjr : j.val < r
  ·
    have hjW : ¬ inW k r j := by unfold inW; omega
    have hji : j.val ≤ i.val := by omega
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hb j j (fun h => hjW h.2), if_pos rfl, mul_one, Matrix.mul_apply,
        Finset.sum_eq_single j]
      · rw [hm j j hj (by omega), if_pos rfl, mul_one]
        exact ha i j (fun h => hjW h.2)
      · intro p _ hpj
        by_cases hp : j.val ≤ p.val
        · rw [hm p j hj (by omega), if_neg hpj, mul_zero]
        · have hpW : ¬ inW k r p := by unfold inW; omega
          have hip : i ≠ p := by intro e; subst e; omega
          rw [ha i p (fun h => hpW h.2), if_neg hip, zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro q _ hqj
      rw [hb q j (fun h => hjW h.2), if_neg hqj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  ·
    have hjW : inW k r j := by unfold inW; omega
    have hir : r ≤ i.val := by omega
    have key : ∀ q : Fin (2 * r + k + 1), (a * m) i q * b q j = a i q * b q j := by
      intro q
      by_cases hqW : inW k r q
      · congr 1
        rw [Matrix.mul_apply, Finset.sum_eq_single q]
        · rw [hm q q hqW.2 (by unfold inW at hqW; omega), if_pos rfl, mul_one]
        · intro p _ hpq
          by_cases hp : r ≤ p.val
          · rw [hm p q hqW.2 (by unfold inW at hqW; omega), if_neg hpq, mul_zero]
          · have hpW : ¬ inW k r p := by unfold inW; omega
            have hip : i ≠ p := by intro e; subst e; omega
            rw [ha i p (fun h => hpW h.2), if_neg hip, zero_mul]
        · intro h; exact absurd (Finset.mem_univ q) h
      · have hqj : q ≠ j := by intro e; subst e; exact hqW hjW
        rw [hb q j (fun h => hqW h.1), if_neg hqj, mul_zero, mul_zero]
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun q _ => key q), ← Matrix.mul_apply, hab,
      Matrix.one_apply]

theorem conj_mem_N {a b m : 𝕄} (ha : WB k r a) (hb : WB k r b) (hab : a * b = 1)
    (haU : a ∈ UH (Hpk k r)) (hbU : b ∈ UH (Hpk k r)) (hm : m ∈ Nset k r) :
    a * m * b ∈ Nset k r := by
  rw [mem_Nset_iff] at hm ⊢
  exact ⟨mul_mem_UH (mul_mem_UH haU hm.1) hbU, nc_conj ha hb hab hm.2⟩

theorem isClosed_NC : IsClosed {g : 𝕄 | NC k r g} := by
  have e : {g : 𝕄 | NC k r g} = ⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1),
      {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} := by
    ext g; simp only [Set.mem_ofPred_eq, Set.mem_iInter]; rfl
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases h : j.val ≤ r + k ∧ min j.val r ≤ i.val
  · have e2 : {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} =
        {g : 𝕄 | g i j = if i = j then 1 else 0} := by
      ext g; simp only [Set.mem_ofPred_eq, h.1, h.2, forall_const]
    rw [e2]
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  · have e2 : {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} =
        Set.univ := by
      ext g; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e2]; exact isClosed_univ

theorem isClosed_Nset : IsClosed (Nset k r) := by
  have e : Nset k r = UH (Hpk k r) ∩ {g : 𝕄 | NC k r g} := by
    ext g; rw [mem_Nset_iff]; rfl
  rw [e]
  exact (unitary_hermitian_group k r).1.inter isClosed_NC

variable {z : Fin (2 * r + k + 1) → ℂ}

theorem mem_Sset_iff (g : 𝕄) : g ∈ Sset k r z ↔ ∃ h ∈ UWset k r z, h⁻¹ * g ∈ Nset k r := by
  constructor
  · rintro ⟨h, hh, m, hm, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [← Matrix.mul_assoc, inv_mul_UH' hh.1, Matrix.one_mul]
    exact hm
  · rintro ⟨h, hh, hm⟩
    refine ⟨h, hh, h⁻¹ * g, hm, ?_⟩
    rw [← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]

theorem isClosed_Sset (hz : inWb k r z) (hT : 0 < Tz k r z) : IsClosed (Sset k r z) := by
  haveI : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.1 (unitary_weyl_compact k r z hz hT)
  have hc : Continuous fun p : UWset k r z × 𝕄 => Hpk k r * (p.1 : 𝕄)ᴴ * Hpk k r * p.2 :=
    (((continuous_const.matrix_mul
      (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose).matrix_mul
        continuous_const).matrix_mul continuous_snd)
  have hT' : IsClosed {p : UWset k r z × 𝕄 | Hpk k r * (p.1 : 𝕄)ᴴ * Hpk k r * p.2 ∈ Nset k r} :=
    isClosed_Nset.preimage hc
  have e : Sset k r z = Prod.snd '' {p : UWset k r z × 𝕄 |
      Hpk k r * (p.1 : 𝕄)ᴴ * Hpk k r * p.2 ∈ Nset k r} := by
    ext g
    rw [mem_Sset_iff]
    constructor
    · rintro ⟨h, hh, hm⟩
      refine ⟨(⟨h, hh⟩, g), ?_, rfl⟩
      show Hpk k r * hᴴ * Hpk k r * g ∈ Nset k r
      rw [← inv_eq_UH hh.1]; exact hm
    · rintro ⟨⟨⟨h, hh⟩, g'⟩, hm, rfl⟩
      refine ⟨h, hh, ?_⟩
      show h⁻¹ * g' ∈ Nset k r
      rw [inv_eq_UH hh.1]; exact hm
  rw [e]
  exact isClosedMap_snd_of_compactSpace _ hT'

theorem one_mem_Sset : (1 : 𝕄) ∈ Sset k r z :=
  ⟨1, one_mem_UW, 1, (nilpotent_subgroup k r).1, (Matrix.one_mul 1).symm⟩

theorem mul_mem_Sset {a b : 𝕄} (ha : a ∈ Sset k r z) (hb : b ∈ Sset k r z) :
    a * b ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  obtain ⟨h', hh', m', hm', rfl⟩ := hb
  have hconj : h'⁻¹ * m * h' ∈ Nset k r :=
    conj_mem_N (wb_of_mem_UW (inv_mem_UW hh')) (wb_of_mem_UW hh') (inv_mul_UH' hh'.1)
      (inv_mem_UH hh'.1) hh'.1 hm
  refine ⟨h * h', mul_mem_UW hh hh', h'⁻¹ * m * h' * m', (nilpotent_subgroup k r).2.1 _ hconj _ hm', ?_⟩
  calc h * m * (h' * m') = h * (h' * h'⁻¹) * m * h' * m' := by
        rw [mul_inv_UH hh'.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [Matrix.mul_assoc]

theorem inv_mem_Sset {a : 𝕄} (ha : a ∈ Sset k r z) : a⁻¹ ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  have hmi : m⁻¹ ∈ Nset k r := ((nilpotent_subgroup k r).2.2 m hm)
  have hconj : h * m⁻¹ * h⁻¹ ∈ Nset k r :=
    conj_mem_N (wb_of_mem_UW hh) (wb_of_mem_UW (inv_mem_UW hh)) (mul_inv_UH hh.1)
      hh.1 (inv_mem_UH hh.1) hmi
  refine ⟨h⁻¹, inv_mem_UW hh, h * m⁻¹ * h⁻¹, hconj, ?_⟩
  rw [Matrix.mul_inv_rev]
  calc m⁻¹ * h⁻¹ = (h⁻¹ * h) * m⁻¹ * h⁻¹ := by rw [inv_mul_UH' hh.1, Matrix.one_mul]
    _ = h⁻¹ * (h * m⁻¹ * h⁻¹) := by simp only [Matrix.mul_assoc]

theorem stabilizer_closed_matrix_group : SsetGroup := by
  intro k r z hz hT
  refine ⟨isClosed_Sset hz hT, one_mem_Sset, fun a ha b hb => mul_mem_Sset ha hb,
    fun a ha => ⟨inv_mem_Sset ha, ?_⟩⟩
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  exact mul_inv_UH (mul_mem_UH hh.1 hm.1)

end CompanionTheory.D.Upq.QuotSetU
end

section
open Matrix

namespace CompanionTheory.D.Upq.QuotSetU

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ}

local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def expo (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else -((i.val : ℤ) - r - k)

theorem expo_add_piI (i : Fin (2 * r + k + 1)) : expo k r i + expo k r (piI k r i) = 0 := by
  have hp := piI_val (k := k) (r := r) i
  have := i.isLt
  unfold expo
  split_ifs at hp ⊢ <;> omega

theorem expo_eq_zero_of_inW {i : Fin (2 * r + k + 1)} (hi : inW k r i) : expo k r i = 0 := by
  unfold expo; unfold inW at hi; split_ifs <;> omega

noncomputable def dvec (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ := ((t ^ expo k r i : ℝ) : ℂ)

noncomputable def cdiag (k r : ℕ) (t : ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  diagonal (dvec (k := k) (r := r) t)

theorem dvec_mul_inv {t : ℝ} (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) :
    dvec (k := k) (r := r) t i * dvec t⁻¹ i = 1 := by
  rw [dvec, dvec, ← Complex.ofReal_mul, ← mul_zpow, mul_inv_cancel₀ ht, _root_.one_zpow,
    Complex.ofReal_one]

theorem dvec_of_inW {t : ℝ} {i : Fin (2 * r + k + 1)} (hi : inW k r i) : dvec (k := k) (r := r) t i = 1 := by
  rw [dvec, expo_eq_zero_of_inW hi, zpow_zero, Complex.ofReal_one]

theorem cdiag_mul {t : ℝ} (ht : t ≠ 0) : cdiag k r t * cdiag k r t⁻¹ = 1 := by
  rw [cdiag, cdiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; exact dvec_mul_inv ht i

theorem cdiag_mul' {t : ℝ} (ht : t ≠ 0) : cdiag k r t⁻¹ * cdiag k r t = 1 := by
  have := cdiag_mul (k := k) (r := r) (inv_ne_zero ht)
  rwa [inv_inv] at this

theorem cdiag_inv {t : ℝ} (ht : t ≠ 0) : (cdiag k r t)⁻¹ = cdiag k r t⁻¹ :=
  Matrix.inv_eq_right_inv (cdiag_mul ht)

theorem conj_apply (t : ℝ) (g : 𝕄) (i j : Fin (2 * r + k + 1)) :
    (cdiag k r t * g * cdiag k r t⁻¹) i j = dvec t i * g i j * dvec t⁻¹ j := by
  rw [cdiag, cdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem cdiag_mem_UH {t : ℝ} (ht : t ≠ 0) : cdiag k r t ∈ UH (Hpk k r) := by
  show (cdiag k r t)ᴴ * Hpk k r * cdiag k r t = Hpk k r
  ext i j
  rw [cdiag, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Hpk_apply]
  split_ifs with h
  · subst h
    have e : star (dvec (k := k) (r := r) t) i * dvec t (piI k r i) = 1 := by
      rw [Pi.star_apply, dvec, dvec, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← zpow_add₀ ht, expo_add_piI, zpow_zero, Complex.ofReal_one]
    calc star (dvec (k := k) (r := r) t) i * epsI k r i * dvec t (piI k r i)
        = epsI k r i * (star (dvec (k := k) (r := r) t) i * dvec t (piI k r i)) := by ring
      _ = epsI k r i := by rw [e, mul_one]
  · simp

theorem cdiag_conj_WB {t : ℝ} (ht : t ≠ 0) {a : 𝕄} (ha : WB k r a) :
    cdiag k r t * a * cdiag k r t⁻¹ = a := by
  ext i j
  rw [conj_apply]
  by_cases hij : inW k r i ∧ inW k r j
  · rw [dvec_of_inW hij.1, dvec_of_inW hij.2, one_mul, mul_one]
  · rw [ha i j hij]
    split_ifs with h
    · subst h; rw [mul_one, dvec_mul_inv ht]
    · rw [mul_zero, zero_mul]

theorem cdiag_conj_N {t : ℝ} (ht : t ≠ 0) {m : 𝕄} (hm : m ∈ Nset k r) :
    cdiag k r t * m * cdiag k r t⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hm ⊢
  refine ⟨mul_mem_UH (mul_mem_UH (cdiag_mem_UH ht) hm.1) (cdiag_mem_UH (inv_ne_zero ht)),
    fun i j hj hi => ?_⟩
  rw [conj_apply, hm.2 i j hj hi]
  split_ifs with h
  · subst h; rw [mul_one, dvec_mul_inv ht]
  · rw [mul_zero, zero_mul]

variable {z : Fin (2 * r + k + 1) → ℂ}

theorem cdiag_conj_S {t : ℝ} (ht : t ≠ 0) {g : 𝕄} (hg : g ∈ Sset k r z) :
    cdiag k r t * g * cdiag k r t⁻¹ ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  refine ⟨h, hh, cdiag k r t * m * cdiag k r t⁻¹, cdiag_conj_N ht hm, ?_⟩
  calc cdiag k r t * (h * m) * cdiag k r t⁻¹
      = (cdiag k r t * h * cdiag k r t⁻¹) * (cdiag k r t * m * cdiag k r t⁻¹) := by
        rw [show (cdiag k r t * h * cdiag k r t⁻¹) * (cdiag k r t * m * cdiag k r t⁻¹) =
          cdiag k r t * h * (cdiag k r t⁻¹ * cdiag k r t) * m * cdiag k r t⁻¹ by
            simp only [Matrix.mul_assoc], cdiag_mul' ht, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = h * (cdiag k r t * m * cdiag k r t⁻¹) := by rw [cdiag_conj_WB ht (wb_of_mem_UW hh)]

theorem cdiag_normalises {t : ℝ} (ht : t ≠ 0) (g : 𝕄) :
    cdiag k r t * g * (cdiag k r t)⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z := by
  rw [cdiag_inv ht]
  refine ⟨fun h => ?_, cdiag_conj_S ht⟩
  have := cdiag_conj_S (z := z) (inv_ne_zero ht) h
  rwa [inv_inv, show cdiag k r t⁻¹ * (cdiag k r t * g * cdiag k r t⁻¹) * cdiag k r t =
      (cdiag k r t⁻¹ * cdiag k r t) * g * (cdiag k r t⁻¹ * cdiag k r t) by
        simp only [Matrix.mul_assoc], cdiag_mul' ht, Matrix.one_mul, Matrix.mul_one] at this

end CompanionTheory.D.Upq.QuotSetU
end

section
open Matrix

namespace CompanionTheory.D.Upq.QuotSetU

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

theorem pow_mem_Sset {x : 𝕄} (hx : x ∈ Sset k r z) (p : ℕ) : x ^ p ∈ Sset k r z := by
  induction p with
  | zero => rw [pow_zero]; exact one_mem_Sset
  | succ p ih => rw [pow_succ]; exact mul_mem_Sset ih hx

theorem entry_le_two {g : 𝕄} (hg : ∀ i j, ‖(g - 1) i j‖ ≤ 1) (i j : Fin (2 * r + k + 1)) :
    ‖g i j‖ ≤ 2 := by
  have e : g i j = (g - 1) i j + (1 : 𝕄) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  have h1 : ‖(1 : 𝕄) i j‖ ≤ 1 := by rw [Matrix.one_apply]; split_ifs <;> simp
  calc ‖g i j‖ = ‖(g - 1) i j + (1 : 𝕄) i j‖ := by rw [← e]
    _ ≤ ‖(g - 1) i j‖ + ‖(1 : 𝕄) i j‖ := norm_add_le _ _
    _ ≤ 2 := by linarith [hg i j]

theorem isCompact_nearOne (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsCompact {g : 𝕄 | g ∈ Sset k r z ∧ ∀ i j, ‖(g - 1) i j‖ ≤ 1} := by
  have hcl : IsClosed {g : 𝕄 | g ∈ Sset k r z ∧ ∀ i j, ‖(g - 1) i j‖ ≤ 1} := by
    have e : {g : 𝕄 | g ∈ Sset k r z ∧ ∀ i j, ‖(g - 1) i j‖ ≤ 1} =
        Sset k r z ∩ ⋂ i, ⋂ j, {g : 𝕄 | ‖(g - 1) i j‖ ≤ 1} := by
      ext g; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    refine (isClosed_Sset hz hT).inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    exact isClosed_le (((continuous_apply j).comp
      ((continuous_apply i).comp (continuous_id.sub continuous_const))).norm) continuous_const
  have hB : IsCompact ((Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 2) : Set 𝕄) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset hcl ?_
  intro g hg' i _ j _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_le_two hg'.2 i j

section ModFun

variable {D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ}
  (hD : UnitaryGroupMassFormula.ModProps (Sset k r z) D)
include hD

theorem modFun_one : D 1 = 1 := by
  have h := hD.2.1 1 one_mem_Sset 1 one_mem_Sset
  rw [Matrix.one_mul] at h
  have h0 := hD.1 1 one_mem_Sset
  have h' : D 1 * D 1 = D 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ h0.ne' h'

theorem modFun_pow {x : 𝕄} (hx : x ∈ Sset k r z) (p : ℕ) : D (x ^ p) = D x ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero]; exact modFun_one hD
  | succ p ih => rw [pow_succ, pow_succ, hD.2.1 _ (pow_mem_Sset hx p) _ hx, ih]

theorem modFun_eq_one_of_bdd {x : 𝕄} (hx : x ∈ Sset k r z) (hxi : x⁻¹ ∈ Sset k r z)
    (hb : ∃ M : ℝ, ∀ p : ℕ, D (x ^ p) ≤ M) (hbi : ∃ M : ℝ, ∀ p : ℕ, D (x⁻¹ ^ p) ≤ M) :
    D x = 1 := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨M', hM'⟩ := hbi
  have h1 : D x ≤ 1 := pow_bdd_le_one (hD.1 x hx) fun p => by rw [← modFun_pow hD hx]; exact hM p
  have h2 : D x⁻¹ ≤ 1 :=
    pow_bdd_le_one (hD.1 _ hxi) fun p => by rw [← modFun_pow hD hxi]; exact hM' p
  have h3 : D x * D x⁻¹ = 1 := by
    rw [← hD.2.1 x hx _ hxi, mul_inv_UH (siegel_set_subset k r z hx), modFun_one hD]
  have h4 := hD.1 x hx
  have h5 := hD.1 _ hxi
  nlinarith

end ModFun

end CompanionTheory.D.Upq.QuotSetU
end

section
namespace CompanionTheory.D.Upq.QuotSetU

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula

end CompanionTheory.D.Upq.QuotSetU
end
