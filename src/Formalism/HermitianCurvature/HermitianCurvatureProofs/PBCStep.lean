import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanBoundsLimits
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AverageOne

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical



theorem psd_herm {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p q : Z} (hp : p ∈ P)
    (hq : q ∈ P) : K q p = conj (K p q) := by
  have h := hK.1.apply ⟨p, hp⟩ ⟨q, hq⟩
  simp only [Matrix.of_apply] at h
  rw [← h]
  simp

theorem psd_diag {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p : Z} (hp : p ∈ P) :
    0 ≤ K p p := by
  have h := hK.diag_nonneg (i := ⟨p, hp⟩)
  simpa [Matrix.of_apply] using h



end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def Good {f : ℕ} (x : crystallineComparison.V f) : Prop := ∀ v, x v ≠ 0

def blk {α : Type} (a w b : α → α → ℂ) : α ⊕ α → α ⊕ α → ℂ := fun x y =>
  match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q

theorem blockPSD_iff {α : Type} (Y : Finset α) (a w b : α → α → ℂ) :
    KB.BlockPSD Y Y a w b ↔ TB.PSDOn (Y.disjSum Y) (blk a w b) := by
  unfold KB.BlockPSD
  constructor <;> intro h <;> convert h using 1 <;> funext x y <;>
    rcases x with p | p <;> rcases y with q | q <;> rfl

variable {H : Type} {f : ℕ}

def phi (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, K v (h, x v) (h', x' v)

def phiR (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  phi Y κ U x x' - phi Y κ P x x' - conj (phi Y κ P x' x) + phi Y κ Q x x'

def hd : (H × crystallineComparison.V f) ⊕ (H × crystallineComparison.V f) → H := Sum.elim (fun p => p.1) (fun p => p.1)

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def phiG (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  if Good x ∧ Good x' then phi Y κ K x x' else 0

def phiRG (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  if Good x ∧ Good x' then phiR Y κ U P Q x x' else 0

theorem phiG_split (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) :
    phiG Y κ U x x' = phiRG Y κ U P Q x x' + phiG Y κ P x x' + conj (phiG Y κ P x' x) - phiG Y κ Q x x' := by
  unfold phiG phiRG phiR
  by_cases hx : Good x
  · by_cases hx' : Good x'
    · simp only [hx, hx', and_self, if_true]
      ring
    · simp [hx, hx']
  · simp [hx]

theorem phiRG_psd (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ)
    (hblk : ∀ v (Xs : Finset ℂ), (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (U v) (P v) (Q v))
    (T : Finset (crystallineComparison.V f)) : TB.PSDOn T (phiRG Y κ U P Q) := by
  classical
  set T' := T.filter (fun x => Good x) with hT'
  have hXs : ∀ v, ∀ z ∈ T'.image (fun x => x v), z ≠ 0 := by
    intro v z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hx).2 v
  let kv : Fin f → (H × ℂ ⊕ H × ℂ) → (H × ℂ ⊕ H × ℂ) → ℂ := fun v a b => match a, b with
    | .inl p, .inl q => U v p q
    | .inl p, .inr q => P v p q
    | .inr q, .inl p => conj (P v p q)
    | .inr p, .inr q => Q v p q
  have hMv : ∀ v, (Matrix.of fun a b : ((Y ×ˢ T'.image (fun x => x v)).disjSum
      (Y ×ˢ T'.image (fun x => x v))) => kv v a b).PosSemidef := by
    intro v
    have h := hblk v _ (hXs v)
    unfold KB.BlockPSD TB.PSDOn at h
    convert h using 1
    ext a b
    rcases a with ⟨a | a, ha⟩ <;> rcases b with ⟨b | b, hb⟩ <;> rfl
  let pt : Fin f → (T' × Y) × Bool → (H × ℂ ⊕ H × ℂ) := fun v i =>
    if i.2 then Sum.inl (i.1.2.1, i.1.1.1 v) else Sum.inr (i.1.2.1, i.1.1.1 v)
  have hpt : ∀ v i, pt v i ∈ (Y ×ˢ T'.image (fun x => x v)).disjSum (Y ×ˢ T'.image (fun x => x v)) := by
    intro v i
    have hm : (i.1.2.1, i.1.1.1 v) ∈ Y ×ˢ T'.image (fun x => x v) :=
      Finset.mem_product.mpr ⟨i.1.2.2, Finset.mem_image_of_mem _ i.1.1.2⟩
    by_cases hs : i.2
    · simp only [pt, hs, if_true]; exact Finset.inl_mem_disjSum.mpr hm
    · simp only [pt, hs]; exact Finset.inr_mem_disjSum.mpr hm
  let L : Matrix ((T' × Y) × Bool) ((T' × Y) × Bool) ℂ := fun i j =>
    κ i.1.2.1 j.1.2.1 * ∏ v, kv v (pt v i) (pt v j)
  have hL : L.PosSemidef := by
    have hk : (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1).PosSemidef := by
      have := hκ.submatrix (fun i : (T' × Y) × Bool => i.1.2)
      convert this using 1
      ext i j
      simp
    have hprod : ∀ s : Finset (Fin f), (Matrix.of fun i j : (T' × Y) × Bool =>
        κ i.1.2.1 j.1.2.1 * ∏ v ∈ s, kv v (pt v i) (pt v j)).PosSemidef := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hk
      | insert a s ha ih =>
        have hA := (hMv a).submatrix (fun i : (T' × Y) × Bool => (⟨pt a i, hpt a i⟩ :
          ((Y ×ˢ T'.image (fun x => x a)).disjSum (Y ×ˢ T'.image (fun x => x a)))))
        have hh := hA.hadamard ih
        have key : (Matrix.of fun i j : (T' × Y) × Bool =>
            κ i.1.2.1 j.1.2.1 * ∏ v ∈ insert a s, kv v (pt v i) (pt v j)) =
            ((Matrix.of fun a' b' : ((Y ×ˢ T'.image (fun x => x a)).disjSum
              (Y ×ˢ T'.image (fun x => x a))) => kv a a' b').submatrix
              (fun i => (⟨pt a i, hpt a i⟩ : ((Y ×ˢ T'.image (fun x => x a)).disjSum
                (Y ×ˢ T'.image (fun x => x a)))))
              (fun i => (⟨pt a i, hpt a i⟩ : ((Y ×ˢ T'.image (fun x => x a)).disjSum
                (Y ×ˢ T'.image (fun x => x a)))))).hadamard
            (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1 * ∏ v ∈ s, kv v (pt v i) (pt v j)) := by
          ext i j
          simp only [Matrix.hadamard_apply, Matrix.submatrix_apply, Matrix.of_apply, Finset.prod_insert ha]
          ring
        rw [key]
        exact hh
    exact hprod Finset.univ
  let sg : Bool → ℂ := fun s => if s then 1 else -1
  let R : Matrix ((T' × Y) × Bool) T ℂ := fun i x => if i.1.1.1 = x.1 then sg i.2 else 0
  have hR0 : ∀ x : T, ¬ Good x.1 → ∀ i, R i x = 0 := by
    intro x hx i
    have : i.1.1.1 ≠ x.1 := by
      intro he
      exact hx (he ▸ (Finset.mem_filter.mp i.1.1.2).2)
    simp [R, this]
  have hcol : ∀ x : T, ∀ hx : Good x.1, ∀ g : (T' × Y) × Bool → ℂ,
      ∑ i, R i x * g i = ∑ h : Y, (g ((⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩, h), true)
        - g ((⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩, h), false)) := by
    intro x hx g
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single (⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩ : T')]
    · refine Finset.sum_congr rfl fun h _ => ?_
      simp [R, sg, Fintype.sum_bool]
      ring
    · intro a ha
      have : a.1 ≠ x.1 := fun he => ha (Subtype.ext he)
      simp [R, this]
  have hstar : ∀ i x, star (R i x) = R i x := by
    intro i x
    simp only [R, sg]
    split_ifs <;> simp
  have hconjP : ∀ x y : crystallineComparison.V f, conj (phi Y κ P y x) =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, conj (P v (h', y v) (h, x v)) := by
    intro x y
    unfold phi
    simp only [map_sum, map_mul, map_prod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 1
    have := hκ.1.apply ⟨h, hh⟩ ⟨h', hh'⟩
    simpa using this
  unfold TB.PSDOn
  have hfin := hL.conjTranspose_mul_mul_same R
  rw [Matrix.mul_assoc] at hfin
  convert hfin using 1
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hstar, Matrix.of_apply]
  by_cases hx : Good x.1
  · by_cases hy : Good y.1
    · rw [hcol x hx]
      simp only [mul_comm (L _ _) (R _ y), hcol y hy]
      simp only [phiRG, phiR, hx, hy, and_self, if_true, hconjP]
      unfold phi
      simp only [← Finset.sum_coe_sort Y]
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
      simp only [L, pt, kv, if_true, Bool.false_eq_true, if_false]
      ring
    · have : ∀ j, R j y = 0 := hR0 y hy
      simp [this, phiRG, hy]
  · have : ∀ i, R i x = 0 := hR0 x hx
    simp [this, phiRG, hx]

theorem phi_bound (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (x x' : crystallineComparison.V f) (hK : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ‖K v (h, x v) (h', x' v)‖ ≤ B) :
    ‖phi Y κ K x x'‖ ≤ (∑ h ∈ Y, ∑ h' ∈ Y, ‖κ h h'‖) * B ^ f := by
  unfold phi
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' hh' => ?_)
  rw [norm_mul, norm_prod]
  gcongr
  calc ∏ v, ‖K v (h, x v) (h', x' v)‖ ≤ ∏ _v : Fin f, B :=
        Finset.prod_le_prod (fun v _ => norm_nonneg _) (fun v _ => hK v h hh h' hh')
    _ = B ^ f := by simp

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def Hh (Y : Finset H) (κ : H → H → ℂ) (hat : Fin f → ℂ → H → H → ℂ) (σ : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, hat v (σ v) h h'

theorem eventually_norm_gt (v : Fin f) (a : ℝ) : ∀ᶠ x in crystallineComparison.atInfAll f, a < ‖x v‖ := by
  have h : ∀ᶠ x in Filter.comap (fun x : crystallineComparison.V f => ‖x v‖) atTop, a < ‖x v‖ :=
    (Filter.eventually_gt_atTop a).comap _
  unfold crystallineComparison.atInfAll
  exact Filter.mem_iInf_of_mem v h

theorem eventually_good (σ : crystallineComparison.V f) : ∀ᶠ x in crystallineComparison.atInfAll f, Good x ∧ Good (x + σ) := by
  have h1 : ∀ v, ∀ᶠ x in crystallineComparison.atInfAll f, x v ≠ 0 ∧ x v + σ v ≠ 0 := by
    intro v
    filter_upwards [eventually_norm_gt v ‖σ v‖] with x hx
    constructor
    · intro h
      rw [h, norm_zero] at hx
      exact absurd hx (not_lt.mpr (norm_nonneg _))
    · intro h
      have e : x v = -σ v := eq_neg_of_add_eq_zero_left h
      rw [e, norm_neg] at hx
      exact lt_irrefl _ hx
  filter_upwards [Filter.eventually_all.mpr h1] with x hx
  exact ⟨fun v => (hx v).1, fun v => (hx v).2⟩

theorem tendsto_coord (v : Fin f) : Tendsto (fun x : crystallineComparison.V f => x v) (crystallineComparison.atInfAll f) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, Filter.tendsto_comap_iff]
  exact Filter.tendsto_comap.mono_left (iInf_le (fun v => Filter.comap (fun x : crystallineComparison.V f => ‖x v‖) atTop) v)

theorem phiG_tendsto (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ)
    (hat : Fin f → ℂ → H → H → ℂ)
    (hlim : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => K v (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hat v σ h h'))) (σ : crystallineComparison.V f) :
    Tendsto (fun x => phiG Y κ K x (x + σ)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)) := by
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun x => phi Y κ K x (x + σ)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)))
  · filter_upwards [eventually_good σ] with x hx
    rw [phiG, if_pos hx]
  · unfold phi Hh
    refine tendsto_finset_sum _ (fun h hh => tendsto_finset_sum _ (fun h' hh' => ?_))
    refine Tendsto.const_mul _ ?_
    refine tendsto_finset_prod _ (fun v _ => ?_)
    exact (hlim v h hh h' hh' (σ v)).comp (tendsto_coord v)

theorem phiG_conj_tendsto (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (K : Fin f → H × ℂ → H × ℂ → ℂ)
    (hat : Fin f → ℂ → H → H → ℂ)
    (hlim : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => conj (K v (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hat v σ h h'))) (σ : crystallineComparison.V f) :
    Tendsto (fun x => conj (phiG Y κ K (x + σ) x)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)) := by
  have hherm : ∀ h ∈ Y, ∀ h' ∈ Y, conj (κ h' h) = κ h h' := by
    intro h hh h' hh'
    have := hκ.1.apply ⟨h, hh⟩ ⟨h', hh'⟩
    simp only [Matrix.of_apply] at this
    exact this
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun x => ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, conj (K v (h', x v + σ v) (h, x v)))
    (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)))
  · filter_upwards [eventually_good σ] with x hx
    symm
    rw [phiG, if_pos ⟨hx.2, hx.1⟩, phi]
    simp only [map_sum, map_mul, map_prod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun h' hh' => ?_))
    rw [hherm h hh h' hh']
    rfl
  · unfold Hh
    refine tendsto_finset_sum _ (fun h hh => tendsto_finset_sum _ (fun h' hh' => ?_))
    refine Tendsto.const_mul _ ?_
    refine tendsto_finset_prod _ (fun v _ => ?_)
    exact (hlim v h hh h' hh' (σ v)).comp (tendsto_coord v)

section mean

variable (Λ : AddSubgroup (crystallineComparison.V f)) (LIM : (Λ → ℂ) → ℂ)

theorem bdd_add {α : Type} {g k : α → ℂ} (hg : crystallineComparison.Bdd g) (hk : crystallineComparison.Bdd k) : crystallineComparison.Bdd (g + k) := by
  obtain ⟨B1, h1⟩ := hg
  obtain ⟨B2, h2⟩ := hk
  exact ⟨B1 + B2, fun x => (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))⟩

theorem mean_smul (hL : crystallineComparison.IsMean LIM) (c : ℂ) {g : Λ → ℂ} (hg : crystallineComparison.Bdd g) :
    LIM (fun x => c * g x) = c * LIM g := by
  exact hL.2.1 c g hg

end mean

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

structure GermData (Y : Finset H) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (hat : Fin f → ℂ → H → H → ℂ) : Prop where
  blk : ∀ v (Xs : Finset ℂ), (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (U v) (P v) (Q v)
  bd : ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖U v (h, x) (h, x)‖ ≤ B ∧ ‖Q v (h, x) (h, x)‖ ≤ B
  limQ : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => Q v (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hat v σ h h'))
  limP : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => P v (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hat v σ h h'))
  limPc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => conj (P v (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hat v σ h h'))

section

variable {Y : Finset H} {U P Q : Fin f → H × ℂ → H × ℂ → ℂ} {hat : Fin f → ℂ → H → H → ℂ}

private lemma norm_apply_sq_le_mul_of_psdOn {α : Type} {T : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn T k) {a b : α}
    (ha : a ∈ T) (hb : b ∈ T) : ‖k a b‖ ^ 2 ≤ ‖k a a‖ * ‖k b b‖ := by

  have hs := (hk.submatrix ![(⟨a, ha⟩ : T), ⟨b, hb⟩]).det_nonneg
  rw [Matrix.det_fin_two] at hs
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hs
  have hba : k b a = conj (k a b) := by
    have := congrFun (congrFun hk.isHermitian ⟨b, hb⟩) ⟨a, ha⟩
    simpa [Matrix.conjTranspose_apply] using this.symm
  have hda : 0 ≤ k a a := by
    have := (hk.submatrix ![(⟨a, ha⟩ : T)]).det_nonneg
    rw [Matrix.det_fin_one] at this
    simpa using this
  have hdb : 0 ≤ k b b := by
    have := (hk.submatrix ![(⟨b, hb⟩ : T)]).det_nonneg
    rw [Matrix.det_fin_one] at this
    simpa using this
  rw [hba, Complex.mul_conj] at hs
  obtain ⟨hs1, -⟩ := Complex.le_def.mp hs
  obtain ⟨ha1, ha2⟩ := Complex.le_def.mp hda
  obtain ⟨hb1, hb2⟩ := Complex.le_def.mp hdb
  simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.mul_re, Complex.ofReal_re] at hs1 ha1 ha2 hb1 hb2
  have na : ‖k a a‖ = (k a a).re := by
    rw [← Complex.re_add_im (k a a), ← ha2]; simp [abs_of_nonneg ha1]
  have nb : ‖k b b‖ = (k b b).re := by
    rw [← Complex.re_add_im (k b b), ← hb2]; simp [abs_of_nonneg hb1]
  rw [na, nb, ← Complex.normSq_eq_norm_sq]
  rw [← ha2, ← hb2] at hs1
  linarith

private lemma entry_lemma_2 (hG : GermData Y U P Q hat) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ v, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖U v (h, x) (h, x)‖ ≤ B ∧ ‖Q v (h, x) (h, x)‖ ≤ B)
    (v : Fin f) {h h' : H} (hh : h ∈ Y) (hh' : h' ∈ Y) {z z' : ℂ} (hz : z ≠ 0) (hz' : z' ≠ 0) :
    ‖U v (h, z) (h', z')‖ ≤ B ∧ ‖P v (h, z) (h', z')‖ ≤ B ∧ ‖Q v (h, z) (h', z')‖ ≤ B := by
  have hk := hG.blk v {z, z'} (by simp [hz, hz'])
  have hp : ((h, z) : H × ℂ) ∈ Y ×ˢ ({z, z'} : Finset ℂ) := by simp [hh]
  have hq : ((h', z') : H × ℂ) ∈ Y ×ˢ ({z, z'} : Finset ℂ) := by simp [hh']
  obtain ⟨hU1, hQ1⟩ := hB v h hh z hz
  obtain ⟨hU2, hQ2⟩ := hB v h' hh' z' hz'
  have e1 : ‖U v (h, z) (h', z')‖ ^ 2 ≤ ‖U v (h, z) (h, z)‖ * ‖U v (h', z') (h', z')‖ :=
    norm_apply_sq_le_mul_of_psdOn hk (a := Sum.inl (h, z)) (b := Sum.inl (h', z')) (by simp [hp]) (by simp [hq])
  have e2 : ‖P v (h, z) (h', z')‖ ^ 2 ≤ ‖U v (h, z) (h, z)‖ * ‖Q v (h', z') (h', z')‖ :=
    norm_apply_sq_le_mul_of_psdOn hk (a := Sum.inl (h, z)) (b := Sum.inr (h', z')) (by simp [hp]) (by simp [hq])
  have e3 : ‖Q v (h, z) (h', z')‖ ^ 2 ≤ ‖Q v (h, z) (h, z)‖ * ‖Q v (h', z') (h', z')‖ :=
    norm_apply_sq_le_mul_of_psdOn hk (a := Sum.inr (h, z)) (b := Sum.inr (h', z')) (by simp [hp]) (by simp [hq])
  have m1 := mul_le_mul hU1 hU2 (norm_nonneg _) hB0
  have m2 := mul_le_mul hU1 hQ2 (norm_nonneg _) hB0
  have m3 := mul_le_mul hQ1 hQ2 (norm_nonneg _) hB0
  have n1 := norm_nonneg (U v (h, z) (h', z'))
  have n2 := norm_nonneg (P v (h, z) (h', z'))
  have n3 := norm_nonneg (Q v (h, z) (h', z'))
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem GermData.phiG_bdd (hG : GermData Y U P Q hat) (κ : H → H → ℂ) :
    ∃ C : ℝ, ∀ x x' : crystallineComparison.V f, ‖phiG Y κ U x x'‖ ≤ C ∧ ‖phiG Y κ P x x'‖ ≤ C ∧ ‖phiG Y κ Q x x'‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := hG.bd
  have hC : 0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, ‖κ h h'‖) * B ^ f := by positivity
  refine ⟨(∑ h ∈ Y, ∑ h' ∈ Y, ‖κ h h'‖) * B ^ f, fun x x' => ?_⟩
  unfold phiG
  by_cases hg : Good x ∧ Good x'
  · simp only [if_pos hg]
    have hE := fun v h (hh : h ∈ Y) h' (hh' : h' ∈ Y) => entry_lemma_2 hG hB0 hB v hh hh' (hg.1 v) (hg.2 v)
    exact ⟨phi_bound Y κ U B hB0 x x' fun v h hh h' hh' => (hE v h hh h' hh').1,
      phi_bound Y κ P B hB0 x x' fun v h hh h' hh' => (hE v h hh h' hh').2.1,
      phi_bound Y κ Q B hB0 x x' fun v h hh h' hh' => (hE v h hh h' hh').2.2⟩
  · simp only [if_neg hg, norm_zero]
    exact ⟨hC, hC, hC⟩

theorem GermData.phiRG_bdd (hG : GermData Y U P Q hat) (κ : H → H → ℂ) :
    ∃ C : ℝ, ∀ x x' : crystallineComparison.V f, ‖phiRG Y κ U P Q x x'‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG.phiG_bdd κ
  refine ⟨4 * C, fun x x' => ?_⟩
  have hr : phiRG Y κ U P Q x x' =
      phiG Y κ U x x' - phiG Y κ P x x' - conj (phiG Y κ P x' x) + phiG Y κ Q x x' := by
    rw [phiG_split Y κ U P Q x x']; ring
  rw [hr]
  obtain ⟨a1, a2, a3⟩ := hC x x'
  obtain ⟨-, b2, -⟩ := hC x' x
  have c2 : ‖conj (phiG Y κ P x' x)‖ ≤ C := by rw [Complex.norm_conj]; exact b2
  calc _ ≤ ‖phiG Y κ U x x'‖ + ‖phiG Y κ P x x'‖ + ‖conj (phiG Y κ P x' x)‖ + ‖phiG Y κ Q x x'‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ ≤ 4 * C := by linarith

variable (Λ : AddSubgroup (crystallineComparison.V f)) (LIM : (Λ → ℂ) → ℂ)

def A0 (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (τ : crystallineComparison.V f) : ℂ :=
  LIM fun x : Λ => phiRG Y κ U P Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + τ)

private lemma lim_eq_of_tendsto_atInfAll (hL : crystallineComparison.IsMeanInf Λ LIM) {g : Λ → ℂ} (hg : crystallineComparison.Bdd g) {c : ℂ}
    (ht : Tendsto g (comap (fun x : Λ => (x : crystallineComparison.V f)) (crystallineComparison.atInfAll f)) (𝓝 c)) : LIM g = c := by
  obtain ⟨⟨hadd, hsmul, -, hone, -⟩, hinf⟩ := hL
  obtain ⟨B, hB⟩ := hg
  have h1 : crystallineComparison.Bdd (fun _ : Λ => (1 : ℂ)) := ⟨1, fun _ => by simp⟩
  have hc : crystallineComparison.Bdd ((-c) • fun _ : Λ => (1 : ℂ)) := ⟨‖c‖, fun _ => by simp⟩
  have hgc : crystallineComparison.Bdd (g + (-c) • fun _ : Λ => (1 : ℂ)) :=
    ⟨B + ‖c‖, fun x => (norm_add_le _ _).trans (add_le_add (hB x) (by simp))⟩
  have ht' : Tendsto (g + (-c) • fun _ : Λ => (1 : ℂ)) (comap (fun x : Λ => (x : crystallineComparison.V f)) (crystallineComparison.atInfAll f)) (𝓝 0) := by
    have := ht.add_const (-c)
    simp only [add_neg_cancel] at this
    convert this using 1
    funext x; simp
  have h0 := hinf _ hgc ht'
  rw [hadd _ _ ⟨B, hB⟩ hc, hsmul _ _ h1, hone] at h0
  linear_combination h0

theorem mean_split (hG : GermData Y U P Q hat) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (hL : crystallineComparison.IsMeanInf Λ LIM)
    (σ : crystallineComparison.V f) :
    LIM (fun x : Λ => phiG Y κ U (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) = Hh Y κ hat σ + A0 Λ LIM Y κ U P Q σ := by
  obtain ⟨CG, hCG⟩ := hG.phiG_bdd κ
  obtain ⟨CR, hCR⟩ := hG.phiRG_bdd κ
  obtain ⟨hadd, hsmul, -, -, -⟩ := hL.1
  have bR : crystallineComparison.Bdd (fun x : Λ => phiRG Y κ U P Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := ⟨CR, fun _ => hCR _ _⟩
  have bP : crystallineComparison.Bdd (fun x : Λ => phiG Y κ P (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := ⟨CG, fun _ => (hCG _ _).2.1⟩
  have bPc : crystallineComparison.Bdd (fun x : Λ => conj (phiG Y κ P ((x : crystallineComparison.V f) + σ) (x : crystallineComparison.V f))) :=
    ⟨CG, fun _ => by rw [Complex.norm_conj]; exact (hCG _ _).2.1⟩
  have bQ : crystallineComparison.Bdd (fun x : Λ => phiG Y κ Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := ⟨CG, fun _ => (hCG _ _).2.2⟩
  have badd : ∀ {g h : Λ → ℂ}, crystallineComparison.Bdd g → crystallineComparison.Bdd h → crystallineComparison.Bdd (g + h) := by
    rintro g h ⟨B1, h1⟩ ⟨B2, h2⟩
    exact ⟨B1 + B2, fun x => (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))⟩
  have bQ' : crystallineComparison.Bdd ((-1 : ℂ) • fun x : Λ => phiG Y κ Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := by
    obtain ⟨B, hB⟩ := bQ; exact ⟨B, fun x => by simpa using hB x⟩
  have hsplit : (fun x : Λ => phiG Y κ U (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) =
      (fun x : Λ => phiRG Y κ U P Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) +
        (fun x : Λ => phiG Y κ P (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) +
        (fun x : Λ => conj (phiG Y κ P ((x : crystallineComparison.V f) + σ) (x : crystallineComparison.V f))) +
        (-1 : ℂ) • (fun x : Λ => phiG Y κ Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [phiG_split Y κ U P Q]; ring
  have lP := lim_eq_of_tendsto_atInfAll Λ LIM hL bP ((phiG_tendsto Y κ P hat hG.limP σ).comp tendsto_comap)
  have lPc := lim_eq_of_tendsto_atInfAll Λ LIM hL bPc ((phiG_conj_tendsto Y κ hκ P hat hG.limPc σ).comp tendsto_comap)
  have lQ := lim_eq_of_tendsto_atInfAll Λ LIM hL bQ ((phiG_tendsto Y κ Q hat hG.limQ σ).comp tendsto_comap)
  rw [hsplit, hadd _ _ (badd (badd bR bP) bPc) bQ', hadd _ _ (badd bR bP) bPc, hadd _ _ bR bP, hsmul _ _ bQ,
    lP, lPc, lQ]
  simp only [A0]
  ring

theorem limit_average_translate_eq (hG : GermData Y U P Q hat) (κ : H → H → ℂ) (hL : crystallineComparison.IsMean LIM) {σ σ' : crystallineComparison.V f}
    (hσ' : σ' ∈ Λ) :
    A0 Λ LIM Y κ U P Q (σ - σ') =
      LIM (fun x : Λ => phiRG Y κ U P Q ((x : crystallineComparison.V f) + σ') ((x : crystallineComparison.V f) + σ)) := by
  obtain ⟨CR, hCR⟩ := hG.phiRG_bdd κ
  have hb : crystallineComparison.Bdd (fun x : Λ => phiRG Y κ U P Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + (σ - σ'))) :=
    ⟨CR, fun _ => hCR _ _⟩
  have ht := hL.2.2.2.2 _ ⟨σ', hσ'⟩ hb
  simp only [A0]
  rw [← ht]
  congr 1
  funext x
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_mk]
  rw [show (x : crystallineComparison.V f) + σ' + (σ - σ') = (x : crystallineComparison.V f) + σ by abel]

private lemma bdd_finset_sum {β ι : Type} (s : Finset ι) (g : ι → β → ℂ) (hg : ∀ i ∈ s, crystallineComparison.Bdd (g i)) :
    crystallineComparison.Bdd (fun x => ∑ i ∈ s, g i x) := by
  choose! B hB using hg
  exact ⟨∑ i ∈ s, B i, fun x => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => hB i hi x)⟩

private lemma lim_finset_sum_of_isMean (hL : crystallineComparison.IsMean LIM) {ι : Type} (s : Finset ι) (g : ι → Λ → ℂ)
    (hg : ∀ i ∈ s, crystallineComparison.Bdd (g i)) : LIM (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, LIM (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun _ : Λ => (0 : ℂ)) = (0 : ℂ) • (fun _ : Λ => (1 : ℂ)) := by funext; simp
    simp only [Finset.sum_empty]
    rw [e, hL.2.1 _ _ ⟨1, fun _ => by simp⟩, zero_mul]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, crystallineComparison.Bdd (g j) := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have e : (fun x => ∑ j ∈ insert i s, g j x) = g i + fun x => ∑ j ∈ s, g j x := by
      funext x; simp [Finset.sum_insert hi]
    rw [e, Finset.sum_insert hi, hL.1 _ _ (hg i (Finset.mem_insert_self _ _)) (bdd_finset_sum s g hs), ih hs]

theorem limit_average_positive_definite (hG : GermData Y U P Q hat) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (hL : crystallineComparison.IsMean LIM)
    (S : Finset (crystallineComparison.V f)) (hS : ∀ σ ∈ S, σ ∈ Λ) (c : crystallineComparison.V f → ℂ) :
    0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A0 Λ LIM Y κ U P Q (σ - σ') * c σ * conj (c σ')).re := by
  classical
  have qf : ∀ X : crystallineComparison.V f, 0 ≤ ∑ σ ∈ S, ∑ σ' ∈ S, phiRG Y κ U P Q (X + σ') (X + σ) * c σ * conj (c σ') := by
    intro X
    have hinj : Set.InjOn (fun σ => X + σ) S := fun a _ b _ h => add_left_cancel h
    have h := (phiRG_psd Y κ hκ U P Q hG.blk (S.image fun σ => X + σ)).dotProduct_mulVec_nonneg
      (fun t => c ((t : crystallineComparison.V f) - X))
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply, Finset.mul_sum] at h
    rw [Finset.sum_coe_sort (S.image fun σ => X + σ) (fun i => ∑ j : ↥(S.image fun σ => X + σ),
      star (c (i - X)) * (phiRG Y κ U P Q i j * c (j - X)))] at h
    rw [Finset.sum_image hinj] at h
    have e : ∀ x ∈ S, (∑ j : ↥(S.image fun σ => X + σ),
        star (c (X + x - X)) * (phiRG Y κ U P Q (X + x) ↑j * c (↑j - X))) =
        ∑ σ ∈ S, phiRG Y κ U P Q (X + x) (X + σ) * c σ * conj (c x) := by
      intro x _
      rw [Finset.sum_coe_sort (S.image fun σ => X + σ)
        (fun j => star (c (X + x - X)) * (phiRG Y κ U P Q (X + x) j * c (j - X))), Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [add_sub_cancel_left, Complex.star_def]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm] at h
    exact h
  obtain ⟨CR, hCR⟩ := hG.phiRG_bdd κ
  have hb : ∀ σ σ' : crystallineComparison.V f, crystallineComparison.Bdd (fun x : Λ =>
      phiRG Y κ U P Q ((x : crystallineComparison.V f) + σ') ((x : crystallineComparison.V f) + σ) * c σ * conj (c σ')) := fun σ σ' =>
    ⟨CR * ‖c σ‖ * ‖c σ'‖, fun x => by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      gcongr
      exact hCR _ _⟩
  have e1 : ∀ σ ∈ S, ∀ σ' ∈ S, A0 Λ LIM Y κ U P Q (σ - σ') * c σ * conj (c σ') =
      LIM (fun x : Λ => phiRG Y κ U P Q ((x : crystallineComparison.V f) + σ') ((x : crystallineComparison.V f) + σ) * c σ * conj (c σ')) := by
    intro σ _ σ' hσ'
    have hb0 : crystallineComparison.Bdd (fun x : Λ => phiRG Y κ U P Q ((x : crystallineComparison.V f) + σ') ((x : crystallineComparison.V f) + σ)) :=
      ⟨CR, fun _ => hCR _ _⟩
    rw [limit_average_translate_eq Λ LIM hG κ hL (hS σ' hσ'), mul_assoc, mul_comm, ← hL.2.1 _ _ hb0]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl (e1 σ hσ)]
  rw [Finset.sum_congr rfl fun σ _ => (lim_finset_sum_of_isMean Λ LIM hL S _ fun σ' _ => hb σ σ').symm]
  rw [← lim_finset_sum_of_isMean Λ LIM hL S _ fun σ _ => bdd_finset_sum S _ fun σ' _ => hb σ σ']
  refine (hL.2.2.1 _ (bdd_finset_sum S _ fun σ _ => bdd_finset_sum S _ fun σ' _ => hb σ σ') fun x => ?_).1
  have := Complex.le_def.mp (qf x)
  simp only [Complex.zero_re, Complex.zero_im] at this
  exact ⟨this.1, this.2.symm⟩

end

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def psiG (g : ℝ) (l c : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((2 * (l * c).re / g : ℝ) : ℂ))

def Fz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, D v h h' (z v)

def Nz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℝ :=
  if Good z then (Fz Y κ D z).re else 0

theorem Fz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) (hz : Good z) :
    0 ≤ Fz Y κ D z := by
  let k : Option (Fin f) → H → H → ℂ := fun o => match o with
    | none => κ
    | some v => fun h h' => D v h h' (z v)
  have hk : ∀ o, TB.PSDOn Y (k o) := by
    intro o; rcases o with _ | v
    · exact hκ
    · exact hD v (z v) (hz v)
  have hS := Formalism.FourierDecayAlt.P.schur_product _ (Option (Fin f)) Y k hk
  have hC := JCx1.decay.psd_compress Y _ hS (fun _ : Unit => Y) (fun _ => id) (fun _ h hh => hh)
  have := hC.diag_nonneg (i := ())
  simp only [Matrix.of_apply, id] at this
  convert this using 1
  unfold Fz
  simp [Fintype.prod_option, k]

theorem Nz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) : 0 ≤ Nz Y κ D z := by
  unfold Nz; split_ifs with hz
  · exact (Complex.nonneg_iff.1 (Fz_nonneg Y κ hκ D hD z hz)).1
  · exact le_rfl

theorem isOpen_good : IsOpen {z : crystallineComparison.V f | Good z} := by
  have : {z : crystallineComparison.V f | Good z} = ⋂ v, (fun z : crystallineComparison.V f => z v) ⁻¹' {0}ᶜ := by
    ext z; simp [Good]
  rw [this]
  exact isOpen_iInter_of_finite fun v => (continuous_apply v).isOpen_preimage _ isOpen_compl_singleton

theorem Fz_continuousAt (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) (z : crystallineComparison.V f) (hz : Good z) :
    ContinuousAt (Fz Y κ D) z := by
  unfold Fz ContinuousAt
  refine tendsto_finsetSum _ fun h hh => tendsto_finsetSum _ fun h' hh' => ?_
  refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun v _ => ?_)
  have := (hDc v h hh h' hh').continuousAt (isOpen_compl_singleton.mem_nhds (hz v))
  exact this.tendsto.comp (continuous_apply v).continuousAt.tendsto

theorem Nz_lsc (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) : LowerSemicontinuous (Nz Y κ D) := by
  intro z y hy
  by_cases hz : Good z
  · have hc : ContinuousAt (fun z => (Fz Y κ D z).re) z :=
      Complex.continuous_re.continuousAt.comp (Fz_continuousAt Y κ D hDc z hz)
    have h1 : ∀ᶠ z' in 𝓝 z, Good z' := isOpen_good.mem_nhds hz
    have hy' : y < (Fz Y κ D z).re := by simpa [Nz, hz] using hy
    filter_upwards [h1, hc.eventually (lt_mem_nhds hy')] with z' hg hl
    simpa [Nz, hg] using hl
  · have hy' : y < 0 := by simpa [Nz, hz] using hy
    exact Filter.Eventually.of_forall fun z' => hy'.trans_le (Nz_nonneg Y κ hκ D hD z')

theorem ae_good : ∀ᵐ z : crystallineComparison.V f, Good z := by
  have : ∀ v : Fin f, ∀ᵐ z : crystallineComparison.V f, z v ≠ 0 := by
    intro v
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [MeasureTheory.volume_pi]
    exact Measure.pi_hyperplane _ v 0
  exact (ae_all_iff.2 this).mono fun z hz => hz

theorem Fz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Fz Y κ D) := by
  unfold Fz
  refine integrable_finsetSum _ fun h hh => integrable_finsetSum _ fun h' hh' => ?_
  exact (Integrable.fintype_prod (f := fun v => D v h h') fun v => hDi v h hh h' hh').const_mul _

theorem Nz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Nz Y κ D) := by
  refine (Fz_integrable Y κ D hDi).re.congr ?_
  filter_upwards [ae_good] with z hz
  simp [Nz, hz]

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

theorem norm_psiG (g : ℝ) (l c : ℂ) : ‖psiG g l c‖ = 1 := by
  simp only [psiG]
  rw [Complex.norm_exp]
  simp

theorem continuous_psiG (g : ℝ) (l : ℂ) : Continuous (psiG g l) := by
  unfold psiG
  fun_prop

theorem psi_prod (g : ℝ) (hg : g ≠ 0) (σ z : crystallineComparison.V f) :
    crystallineComparison.psi (σ * z) = ∏ v, psiG g ((g • σ) v) (z v) := by
  have key : ∀ v, (2 * (((g • σ) v) * z v).re / g : ℝ) = 2 * (σ v * z v).re := by
    intro v
    rw [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
    field_simp
  simp only [psiG, key]
  rw [← Complex.exp_sum, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.psi_mul, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair, Complex.ofReal_sum,
    Finset.mul_sum]

theorem integrable_mul_psiG {φ : ℂ → ℂ} (hφ : Integrable φ) (g : ℝ) (l : ℂ) :
    Integrable fun c => φ c * psiG g l c := by
  refine hφ.norm.mono' (hφ.aestronglyMeasurable.mul (continuous_psiG g l).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun c => by rw [norm_mul, norm_psiG, mul_one]

theorem fourier_Nz (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : g ≠ 0) (dl : Fin f → ℝ)
    (hdl : ∀ v, dl v ≠ 0) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c) (σ : crystallineComparison.V f) :
    crystallineComparison.fourier (Nz Y κ D) σ = (∏ v, ((dl v : ℝ) : ℂ)) * Hh Y κ hat (g • σ) := by
  have hae : (fun z => ((Nz Y κ D z : ℝ) : ℂ) * crystallineComparison.psi (σ * z)) =ᵐ[volume]
      fun z => Fz Y κ D z * crystallineComparison.psi (σ * z) := by
    filter_upwards [ae_good] with z hz
    have h0 := Complex.nonneg_iff.mp (Fz_nonneg Y κ hκ D hD z hz)
    rw [Nz, if_pos hz]
    congr 1
    exact Complex.ext (by simp) (by simp [← h0.2])
  have hpt : ∀ z : crystallineComparison.V f, Fz Y κ D z * crystallineComparison.psi (σ * z) =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v)) := by
    intro z
    rw [Fz, psi_prod g hg σ z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
  have hone : ∀ v h h', ∫ c, D v h h' c * psiG g ((g • σ) v) c =
      ((dl v : ℝ) : ℂ) * hat v ((g • σ) v) h h' := by
    intro v h h'
    rw [hhat, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hdl v), one_mul]
  have hint : ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z : crystallineComparison.V f =>
      κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v))) := by
    intro h hh h' hh'
    exact (Integrable.fintype_prod (fun v => integrable_mul_psiG (hDi v h hh h' hh') g _)).const_mul _
  unfold crystallineComparison.fourier
  rw [integral_congr_ae hae]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun h hh => integrable_finsetSum _ (fun h' hh' => hint h hh h' hh')),
    Hh, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [integral_finsetSum _ (fun h' hh' => hint h hh h' hh'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun h' hh' => ?_
  have hp := integral_fintype_prod_volume_eq_prod (fun v (c : ℂ) => D v h h' c * psiG g ((g • σ) v) c)
  rw [integral_const_mul, hp]
  simp_rw [hone]
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_good (τ : crystallineComparison.V f) : ∃ x : crystallineComparison.V f, Good x ∧ Good (x + τ) := by
  refine ⟨fun v => ((‖τ v‖ + 1 : ℝ) : ℂ), fun v => ?_, fun v => ?_⟩
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) ≠ 0
    have hpos : (0 : ℝ) < ‖τ v‖ + 1 := by positivity
    exact_mod_cast hpos.ne'
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) + τ v ≠ 0
    intro h
    have h2 : τ v = -(((‖τ v‖ + 1 : ℝ) : ℂ)) := by linear_combination h
    have h3 := congrArg (fun w : ℂ => ‖w‖) h2
    simp only [norm_neg] at h3
    rw [Complex.norm_of_nonneg (by positivity)] at h3
    linarith

theorem herglotz_germ (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (hat : Fin f → ℂ → H → H → ℂ)
    (hG : GermData Y U P Q hat)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (Lm : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology Lm] [IsZLattice ℝ Lm]
    (hLm : ∀ σ ∈ crystallineComparison.dualSet La, g • σ ∈ Lm) (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V f, Good x → Good (x + g • σ) → ‖phi Y κ U x (x + g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  obtain ⟨LIM, hL⟩ := Formalism.FourierDecayAlt.P.invariantMeanExists f Lm
  have hbd : ∀ σ ∈ crystallineComparison.dualSet La,
      ‖Hh Y κ hat (g • σ) + A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)‖ ≤ F σ := by
    intro σ hσ
    rw [← mean_split Lm.toAddSubgroup LIM hG κ hκ hL (g • σ)]
    refine Formalism.FourierDecayAlt.P.mean_bound_estimate _ LIM _ (F σ) hL.1 ?_
    intro x
    unfold phiG
    split_ifs with hx
    · exact hF σ hσ x hx.1 hx.2
    · obtain ⟨x0, h1, h2⟩ := exists_good (g • σ)
      simpa using (norm_nonneg _).trans (hF σ hσ x0 h1 h2)
  let A : crystallineComparison.V f → ℂ := fun σ => ((∏ v, dl v : ℝ) : ℂ) * A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) A := by
    intro T w hT
    have hinj : Set.InjOn (fun σ : crystallineComparison.V f => g • σ) T :=
      fun a _ b _ hab => smul_right_injective (crystallineComparison.V f) hgne hab
    have hT' : ∀ τ ∈ T.image (fun σ : crystallineComparison.V f => g • σ), τ ∈ Lm.toAddSubgroup := by
      intro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      exact hLm σ (hT σ hσ)
    have h0 := limit_average_positive_definite Lm.toAddSubgroup LIM hG κ hκ hL.1 (T.image (fun σ : crystallineComparison.V f => g • σ)) hT'
      (fun τ => w (g⁻¹ • τ))
    simp_rw [Finset.sum_image hinj] at h0
    simp only [inv_smul_smul₀ hgne, ← smul_sub] at h0
    have hsplit : (∑ σ ∈ T, ∑ σ' ∈ T, A (σ - σ') * w σ * starRingEnd ℂ (w σ')) =
        ((∏ v, dl v : ℝ) : ℂ) * ∑ σ ∈ T, ∑ σ' ∈ T,
          A0 Lm.toAddSubgroup LIM Y κ U P Q (g • (σ - σ')) * w σ * starRingEnd ℂ (w σ') := by
      simp only [A, Finset.mul_sum, mul_assoc]
    rw [hsplit, Complex.re_ofReal_mul]
    exact mul_nonneg hc0 h0
  have hb : ∀ σ : crystallineComparison.dualSet La, ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [hfour]
    simp only [A]
    rw [← mul_add, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hbd σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) A (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

theorem herglotz_plain (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La] (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ‖Hh Y κ hat (g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) (0 : crystallineComparison.V f → ℂ) := by
    intro T w _
    simp
  have hb : ∀ σ : crystallineComparison.dualSet La,
      ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [Pi.zero_apply, add_zero, hfour, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hF σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) 0 (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

end

end Formalism.FourierDecayAlt.P.PBC
end
