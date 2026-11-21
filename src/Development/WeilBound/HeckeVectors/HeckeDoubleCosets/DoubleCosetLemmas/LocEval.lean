import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.ExtendedCharacterCongrOfTame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBallsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MatrixHaarRightTranslate
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist

section
noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def dM [MeasurableSpace (Cv v)] (μ : Measure (Cv v)) (n m : ℕ) :
    Measure (Matrix (Fin n) (Fin m) (Cv v)) :=
  (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => μ : Measure (Fin n → Fin m → Cv v))

structure Pack [MeasurableSpace (Cv v)] (μ : Measure (Cv v)) : Prop where
  sf : SigmaFinite μ
  sc : SecondCountableTopology (Cv v)
  pos : ∀ n m, (dM μ n m).IsOpenPosMeasure
  one : μ {x | Valued.v x ≤ 1} = 1
  scale : ∀ c : Cv v, c ≠ 0 → ∀ S, MeasurableSet S →
    μ ((· * c) ⁻¹' S) = ENNReal.ofReal (absV v c)⁻¹ * μ S
  left : ∀ n m, ∀ k ∈ KGL v n, Measure.map (fun x => k.1 * x) (dM μ n m) = dM μ n m
  right : ∀ n m, ∀ k ∈ KGL v m, Measure.map (fun x => x * k.1) (dM μ n m) = dM μ n m
  prod : ∀ r d c, MeasurePreserving
    (fun x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v) => ((bAA x, bDA x), (bAD x, bDD x)))
    (dM μ (r + d) (r + c)) (((dM μ r r).prod (dM μ d r)).prod ((dM μ r c).prod (dM μ d c)))

end CompanionTheory.D.Upq.DoubleCosetLemmas
end
end

section
noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

open Classical in

def gR (y : Cv v) : ℝ := if Valued.v y ≤ 1 then 1 else (absV v y)⁻¹

theorem gR_zero : gR (0 : Cv v) = 1 := by simp [gR]

def wt {a b : ℕ} (y : Matrix (Fin a) (Fin b) (Cv v)) : ℝ := ∏ i, ∏ j, gR (y i j)

theorem clopen_le : IsClopen {x : Cv v | Valued.v x ≤ 1} := by
  have := Valued.isClopen_integer (Cv v)
  exact this

variable [MeasurableSpace (Cv v)] [BorelSpace (Cv v)] {μ : Measure (Cv v)}

theorem Pack.line (h : Pack μ) {ι : Type} [Fintype ι] (y : ι → Cv v)
    (hy : ∀ j, y j ≠ 0 → ∀ j', j' ≠ j → y j' = 0) :
    μ {x | Valued.v x ≤ 1 ∧ ∀ j, Valued.v (x * y j) ≤ 1} = ∏ j, ENNReal.ofReal (gR (y j)) := by
  classical
  by_cases h0 : ∀ j, y j = 0
  · simp [h0, gR_zero, h.one]
  push Not at h0
  obtain ⟨j, hj⟩ := h0
  rw [Finset.prod_eq_single j (fun j' _ h' => by simp [hy j hj j' h', gR_zero]) (by simp)]
  have e : {x : Cv v | Valued.v x ≤ 1 ∧ ∀ j, Valued.v (x * y j) ≤ 1} =
      {x | Valued.v x ≤ 1 ∧ Valued.v (x * y j) ≤ 1} := by
    ext x
    refine and_congr_right fun _ => ⟨fun h => h j, fun h j' => ?_⟩
    by_cases h' : j' = j
    · rwa [h']
    · simp [hy j hj j' h']
  rw [e, gR]
  split_ifs with h1
  · rw [ENNReal.ofReal_one, ← h.one]
    congr 1; ext x
    exact ⟨fun h => h.1, fun h => ⟨h, by rw [map_mul]; exact mul_le_one' h h1⟩⟩
  · rw [← mul_one (ENNReal.ofReal _), ← h.one, ← h.scale _ hj _ clopen_le.1.measurableSet]
    congr 1; ext x
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    have h2 : Valued.v x * Valued.v (y j) ≤ 1 := by simpa using h
    exact (le_mul_of_one_le_right' (not_le.1 h1).le).trans h2

def sg (ϖ : Cv v) : ENNReal := ENNReal.ofReal (absV v ϖ⁻¹)⁻¹

end CompanionTheory.D.Upq.DoubleCosetLemmas
end
end

section
open MeasureTheory Set

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

variable {G M : Type} [Group G] [MeasurableSpace M]

def stab (J : Subgroup G) (g : G) : Set G := {k | k ∈ J ∧ g⁻¹ * k * g ∈ J}

def cos (J : Subgroup G) (g : G) (A : Set G) : Set (G ⧸ J) := {z | ∃ k ∈ A, z = ((k * g : G) : G ⧸ J)}

structure Meas (dx : Measure M) (φ : G → M) (J : Subgroup G) (g : G) : Prop where
  inj : Function.Injective φ
  meas : ∀ k ∈ J, MeasurableSet (φ '' ((k * ·) '' stab J g))
  vol : ∀ k ∈ J, dx (φ '' ((k * ·) '' stab J g)) = dx (φ '' stab J g)
  ne : dx (φ '' stab J g) ≠ 0
  fin : dx (φ '' (J : Set G)) ≠ ⊤

variable {dx : Measure M} {φ : G → M} {J : Subgroup G} {g : G}

theorem fibre_eq {k : G} (hk : k ∈ J) :
    {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) = (k * g : G)} = (k * ·) '' stab J g := by
  ext x
  simp only [mem_setOf_eq, mem_image, stab, QuotientGroup.eq]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨k⁻¹ * x, ⟨J.mul_mem (J.inv_mem hk) hx, ?_⟩, by group⟩
    have := J.inv_mem h
    rwa [show ((x * g)⁻¹ * (k * g))⁻¹ = g⁻¹ * (k⁻¹ * x) * g by group] at this
  · rintro ⟨s, ⟨hs, hs'⟩, rfl⟩
    refine ⟨J.mul_mem hk hs, ?_⟩
    have := J.inv_mem hs'
    rwa [show (g⁻¹ * s * g)⁻¹ = (k * s * g)⁻¹ * (k * g) by group] at this

theorem Meas.finset (h : Meas dx φ J g) (t : Finset (G ⧸ J)) (ht : ↑t ⊆ cos J g J) :
    dx (φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) ∈ t}) = t.card * dx (φ '' stab J g) := by
  have e : φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) ∈ t} =
      ⋃ z ∈ t, φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) = z} := by
    ext y; simp only [mem_image, mem_setOf_eq, mem_iUnion]
    exact ⟨fun ⟨x, ⟨h1, h2⟩, h3⟩ => ⟨_, h2, x, ⟨h1, rfl⟩, h3⟩,
      fun ⟨z, hz, x, ⟨h1, h2⟩, h3⟩ => ⟨x, ⟨h1, h2 ▸ hz⟩, h3⟩⟩
  rw [e, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun z hz => ?_, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨k, hk, rfl⟩ := ht hz
    rw [fibre_eq hk, h.vol k hk]
  · intro a _ b _ hab
    refine (Set.disjoint_image_iff h.inj).2 (Set.disjoint_left.2 fun x h1 h2 => hab ?_)
    exact h1.2.symm.trans h2.2
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := ht hz
    rw [fibre_eq hk]; exact h.meas k hk

theorem Meas.finite (h : Meas dx φ J g) : (cos J g J).Finite := by
  by_contra hinf
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt h.ne h.fin
  obtain ⟨t, ht, rfl⟩ := Set.Infinite.exists_subset_card_eq hinf n
  rw [← h.finset t ht] at hn
  exact hn.not_ge (measure_mono (image_mono fun x hx => hx.1))

theorem Meas.card (h : Meas dx φ J g) {A : Set G} (hA : A ⊆ J)
    (hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A) :
    ((cos J g A).ncard : ENNReal) * dx (φ '' stab J g) = dx (φ '' A) := by
  have hsub : cos J g A ⊆ cos J g J := fun z ⟨k, hk, e⟩ => ⟨k, hA hk, e⟩
  have hf := h.finite.subset hsub
  rw [Set.ncard_eq_toFinset_card _ hf, ← h.finset _ (by simpa using hsub)]
  congr 2
  ext x
  simp only [mem_setOf_eq, Finite.mem_toFinset]
  refine ⟨fun ⟨hx, k, hk, e⟩ => ?_, fun hx => ⟨hA hx, x, hx, rfl⟩⟩
  have : x ∈ (k * ·) '' stab J g := fibre_eq (hA hk) ▸ ⟨hx, e⟩
  obtain ⟨s, hs', rfl⟩ := this
  exact hs k hk s hs'

section Sum

variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] {F : G → Y}

theorem out_eq (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z) (x : G) : F ((x : G ⧸ J).out) = F x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J x
  rw [hk, hR _ _ k.2]

theorem supp_sub (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) :
    (Function.support fun z : G ⧸ J => F z.out) ⊆ cos J g J := by
  intro z hz
  by_contra hn
  refine hz (h0 _ fun hm => hn ?_)
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
  exact ⟨a, ha, by rw [← z.out_eq', e]; exact QuotientGroup.mk_mul_of_mem _ hb⟩

open Classical in
theorem finsum_eq (hf : (cos J g J).Finite) (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z)
    (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) {A : Set G} (hA : A ⊆ J)
    {y : Y} (hF : ∀ k ∈ J, F (k * g) = if k ∈ A then y else 0)
    (hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A) :
    ∑ᶠ z : G ⧸ J, F z.out = ((cos J g A).ncard : ℂ) • y := by
  have hsub : cos J g A ⊆ cos J g J := fun z ⟨k, hk, e⟩ => ⟨k, hA hk, e⟩
  have hf' := hf.subset hsub
  rw [finsum_eq_sum_of_support_subset (s := hf'.toFinset), Set.ncard_eq_toFinset_card _ hf',
    Finset.sum_congr rfl fun z hz => ?_, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  · obtain ⟨k, hk, rfl⟩ := hf'.mem_toFinset.1 hz
    rw [out_eq hR, hF k (hA hk), if_pos hk]
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := supp_sub h0 hz
    have := hz
    rw [Function.mem_support, out_eq hR, hF k hk] at this
    have hkA : k ∈ A := by by_contra hn; exact this (if_neg hn)
    simpa using ⟨k, hkA, rfl⟩

open Classical in

theorem Meas.sum (h : Meas dx φ J g) {F : G → ℂ} (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z)
    (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) {A : Set G} (hA : A ⊆ J)
    {y : ℂ} (hF : ∀ k ∈ J, F (k * g) = if k ∈ A then y else 0) :
    (∑ᶠ z : G ⧸ J, F z.out) * ((dx (φ '' stab J g)).toReal : ℂ) = y * ((dx (φ '' A)).toReal : ℂ) := by
  by_cases hy : y = 0
  · rw [finsum_eq h.finite hR h0 (A := J) subset_rfl (y := 0) (fun k hk => by simp [hF k hk, hy])
      fun k hk s hs => J.mul_mem hk hs.1, hy]
    simp
  have hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A := fun k hk s hs => by
    have h1 := hF _ (J.mul_mem (hA hk) hs.1)
    rw [show k * s * g = k * g * (g⁻¹ * s * g) by group, hR _ _ hs.2, hF k (hA hk), if_pos hk] at h1
    by_contra hn
    exact hy (h1.trans (if_neg hn))
  rw [finsum_eq h.finite hR h0 hA hF hs, ← h.card hA hs, ENNReal.toReal_mul]
  simp only [smul_eq_mul, ENNReal.toReal_natCast]
  push_cast; ring

end Sum

end CompanionTheory.D.Upq.DoubleCosetLemmas
end

section
noncomputable section

open Matrix IsDedekindDomain NumberField
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)
open GlobalTheory.CompanionTheory.Ipf.Val

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

namespace Sp

section Gen

variable {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (w : Valuation F Γ)

def ParMem (r : ℕ) {n : ℕ} (k : GL (Fin n) F) : Prop :=
  (∀ i j, w (k.1 i j) ≤ 1) ∧ (∀ i j, w ((k⁻¹).1 i j) ≤ 1) ∧
    ∀ i j : Fin n, r ≤ i → (j : ℕ) < r → w (k.1 i j) < 1

def Iso {m n : ℕ} (z : Matrix (Fin m) (Fin n) F) (i : Fin m) (j : Fin n) : Prop :=
  z i j ≠ 0 ∧ (∀ j', j' ≠ j → z i j' = 0) ∧ ∀ i', i' ≠ i → z i' j = 0

def unip {n : ℕ} (N : Matrix (Fin n) (Fin n) F) (h : N * N = 0) : GL (Fin n) F :=
  ⟨1 + N, 1 - N, by rw [add_mul, mul_sub, mul_sub, h]; simp,
    by rw [sub_mul, mul_add, mul_add, h]; simp⟩

variable {w} in
theorem parMem_unip {r n : ℕ} {N : Matrix (Fin n) (Fin n) F} (h : N * N = 0)
    (h1 : ∀ i j, w (N i j) ≤ 1) (h2 : ∀ i j : Fin n, r ≤ i → (j : ℕ) < r → w (N i j) < 1) :
    ParMem w r (unip N h) := by
  have one : ∀ i j : Fin n, w ((1 : Matrix (Fin n) (Fin n) F) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]; split_ifs <;> simp
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j hi hj => ?_⟩
  · exact w.map_add_le (one i j) (h1 i j)
  · exact w.map_sub_le (one i j) (h1 i j)
  · have : i ≠ j := by rintro rfl; omega
    change w ((1 + N) i j) < 1
    rw [Matrix.add_apply, Matrix.one_apply_ne this, zero_add]
    exact h2 i j hi hj

theorem step {r m n : ℕ} (z : Matrix (Fin m) (Fin n) F) (i₁ : Fin m) (j₁ : Fin n)
    (h1 : z i₁ j₁ ≠ 0) (hn : ¬ ∃ j, Iso z i₁ j) :
    ∃ (k' : GL (Fin m) F) (k : GL (Fin n) F), ParMem w r k' ∧ ParMem w r k ∧
      (∀ i j, Iso z i j → Iso (k'.1 * z * k.1) i j) ∧
      ∃ i₀ j₀, (¬ ∃ j, Iso z i₀ j) ∧ Iso (k'.1 * z * k.1) i₀ j₀ := by
  classical
  let f : Fin m × Fin n → Lex (Γ × ℕ) := fun p =>
    toLex (w (z p.1 p.2), (if r ≤ (p.1 : ℕ) then 1 else 0) + if (p.2 : ℕ) < r then 1 else 0)
  obtain ⟨⟨i₀, j₀⟩, hm, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun p : Fin m × Fin n => ¬ ∃ j, Iso z p.1 j) f ⟨(i₁, j₁), by simpa using hn⟩
  have hm0 : ¬ ∃ j, Iso z i₀ j := by simpa using hm
  have hle : ∀ i j, (¬ ∃ j, Iso z i j) → w (z i j) < w (z i₀ j₀) ∨ (w (z i j) = w (z i₀ j₀) ∧
      ((if r ≤ (i : ℕ) then 1 else 0) + if (j : ℕ) < r then 1 else 0) ≤
        (if r ≤ (i₀ : ℕ) then 1 else 0) + if (j₀ : ℕ) < r then 1 else 0) := fun i j h => by
    have := hmax (i, j) (by simpa using h)
    exact Prod.Lex.toLex_le_toLex.1 this
  have hp : z i₀ j₀ ≠ 0 := by
    intro h0
    have : 0 < w (z i₁ j₁) := zero_lt_iff.2 (w.ne_zero_iff.2 h1)
    rcases hle i₁ j₁ hn with h | h
    · rw [h0, map_zero] at h; exact absurd h not_lt_zero'
    · rw [h0, map_zero] at h; exact this.ne' h.1
  have hwp : 0 < w (z i₀ j₀) := zero_lt_iff.2 (w.ne_zero_iff.2 hp)
  have hcol : ∀ i j, Iso z i j → z i j₀ = 0 := fun i j h => by
    refine h.2.1 j₀ ?_
    rintro rfl
    by_cases e : i₀ = i
    · exact hm0 ⟨_, e ▸ h⟩
    · exact hp (h.2.2 i₀ e)
  let a : Fin m → F := fun i => if i = i₀ then 0 else -(z i j₀ / z i₀ j₀)
  let b : Fin n → F := fun j => if j = j₀ then 0 else -(z i₀ j / z i₀ j₀)
  let N' : Matrix (Fin m) (Fin m) F := Matrix.of fun i l => if l = i₀ then a i else 0
  let N : Matrix (Fin n) (Fin n) F := Matrix.of fun l j => if l = j₀ then b j else 0
  have hN' : N' * N' = 0 := by
    ext i l
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x = i₀ <;> simp [N', a, hx]
  have hN : N * N = 0 := by
    ext i l; simp [N, Matrix.mul_apply, b]
  have hent : ∀ i j, ((unip N' hN').1 * z * (unip N hN).1) i j =
      (z i j + a i * z i₀ j) + (z i j₀ + a i * z i₀ j₀) * b j := fun i j => by
    have e1 : ∀ j, ((1 + N') * z : Matrix (Fin m) (Fin n) F) i j = z i j + a i * z i₀ j := fun j => by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
      simp [N']
    change ((1 + N') * z * (1 + N) : Matrix (Fin m) (Fin n) F) i j = _
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, e1, Matrix.mul_apply]
    simp only [N, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, e1]
  have hq : ∀ x : F, w x ≤ w (z i₀ j₀) → w (-(x / z i₀ j₀)) ≤ 1 := fun x h => by
    rw [Valuation.map_neg, map_div₀]; exact div_le_one_of_le₀ h zero_le'
  have hq' : ∀ x : F, w x < w (z i₀ j₀) → w (-(x / z i₀ j₀)) < 1 := fun x h => by
    rw [Valuation.map_neg, map_div₀]; exact (div_lt_one₀ hwp).2 h
  refine ⟨unip N' hN', unip N hN, parMem_unip _ (fun i l => ?_) (fun i l hi hl => ?_),
    parMem_unip _ (fun l j => ?_) (fun l j hl hj => ?_), fun i j h => ?_, i₀, j₀, hm0, ?_⟩
  · simp only [N', a, Matrix.of_apply]
    split_ifs
    · simp
    · refine hq _ ?_
      by_cases hi : ∃ j, Iso z i j
      · obtain ⟨j, hj⟩ := hi; simp [hcol i j hj]
      · rcases hle i j₀ hi with h | h
        exacts [h.le, h.1.le]
    · simp
  · simp only [N', a, Matrix.of_apply]
    split_ifs with e1 e2
    · simp
    · refine hq' _ ?_
      subst e1
      by_cases hi' : ∃ j, Iso z i j
      · obtain ⟨j, hj⟩ := hi'; simpa [hcol i j hj] using hwp
      · rcases hle i j₀ hi' with h | h
        · exact h
        · have := h.2
          rw [if_pos hi, if_neg (by omega : ¬ r ≤ (l : ℕ))] at this
          omega
    · simp
  · simp only [N, b, Matrix.of_apply]
    split_ifs
    · simp
    · refine hq _ ?_
      rcases hle i₀ j hm0 with h | h
      exacts [h.le, h.1.le]
    · simp
  · simp only [N, b, Matrix.of_apply]
    split_ifs with e1 e2
    · simp
    · refine hq' _ ?_
      subst e1
      rcases hle i₀ j hm0 with h | h
      · exact h
      · have := h.2
        rw [if_pos hj, if_neg (by omega : ¬ (l : ℕ) < r)] at this
        omega
    · simp
  · have hi : i ≠ i₀ := by rintro rfl; exact hm0 ⟨j, h⟩
    have h0 := hcol i j h
    have hj : j ≠ j₀ := by rintro rfl; exact h.1 h0
    have h0' : z i₀ j = 0 := h.2.2 i₀ hi.symm
    have ha : a i = 0 := by simp [a, h0]
    have hb : b j = 0 := by simp [b, h0']
    refine ⟨?_, fun j' hj' => ?_, fun i' hi' => ?_⟩
    · rw [hent, ha, hb]; simpa using h.1
    · rw [hent, ha, h0, h.2.1 j' hj']; simp
    · rw [hent, hb, h0', h.2.2 i' hi']; simp
  · refine ⟨?_, fun j' hj' => ?_, fun i' hi' => ?_⟩
    · rw [hent]; simpa [a, b] using hp
    · rw [hent]; simp only [a, b, if_true, if_neg hj']; field_simp; ring
    · rw [hent]; simp only [a, b, if_true, if_neg hi']; field_simp; ring

def dg {n : ℕ} (i : Fin n) (u : Fˣ) : GL (Fin n) F :=
  ⟨diagonal (Function.update 1 i (u : F)), diagonal (Function.update 1 i ((u⁻¹ : Fˣ) : F)),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext l; by_cases h : l = i <;> simp [h],
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext l; by_cases h : l = i <;> simp [h]⟩

end Gen

end Sp

end CompanionTheory.D.Upq.DoubleCosetLemmas

end
end

section
noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def UnM {n : ℕ} (x : Matrix (Fin n) (Fin n) (Cv v)) : Prop := IntM x ∧ Valued.v x.det = 1

theorem intM_iff {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) :
    IntM x ↔ IntM (bAA x) ∧ IntM (bDA x) ∧ IntM (bAD x) ∧ IntM (bDD x) := by
  refine ⟨fun h => ⟨fun _ _ => h _ _, fun _ _ => h _ _, fun _ _ => h _ _, fun _ _ => h _ _⟩,
    fun ⟨h1, h2, h3, h4⟩ i j => ?_⟩
  induction i using Fin.addCases <;> induction j using Fin.addCases
  exacts [h1 _ _, h3 _ _, h2 _ _, h4 _ _]

theorem SmM.int {a b : Type} {x : Matrix a b (Cv v)} (h : SmM x) : IntM x := fun i j => (h i j).le

theorem det_blocks {r c : ℕ} {x : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)} (hx : IntM x)
    (h : SmM (bDA x)) : Valued.v (x.det - (bAA x).det * (bDD x).det) < 1 := by
  have h4 := (intM_iff x).1 hx
  let x₀ := Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks (bAA x) (bAD x) 0 (bDD x))
  have hd : x₀.det = (bAA x).det * (bDD x).det := by
    rw [det_reindex_self, det_fromBlocks_zero₂₁]
  rw [← hd]
  refine det_congr hx (fun i j => ?_) fun i j => ?_
  · induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [x₀]
    exacts [h4.1 _ _, h4.2.2.1 _ _, h4.2.2.2 _ _]
  · induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [x₀, bAA, bAD, bDD]
    exact h _ _

def ParM {r c : ℕ} (x : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)) : Prop :=
  UnM (bAA x) ∧ SmM (bDA x) ∧ IntM (bAD x) ∧ UnM (bDD x)

theorem ParM.un {r c : ℕ} {x : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)} (h : ParM x) : UnM x := by
  have hx : IntM x := (intM_iff x).2 ⟨h.1.1, h.2.1.int, h.2.2.1, h.2.2.2.1⟩
  refine ⟨hx, ?_⟩
  have h1 := det_blocks hx h.2.1
  have h2 : Valued.v ((bAA x).det * (bDD x).det) = 1 := by rw [map_mul, h.1.2, h.2.2.2.2, one_mul]
  rw [← sub_add_cancel x.det ((bAA x).det * (bDD x).det),
    Valuation.map_add_eq_of_lt_right _ (by rwa [h2]), h2]

section Clopen

variable {X : Type} [TopologicalSpace X] {a b : ℕ} {ϖ : Cv v}

end Clopen

variable [MeasurableSpace (Cv v)] [BorelSpace (Cv v)] {μ : Measure (Cv v)}

theorem Pack.borel (h : Pack μ) (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) (Cv v)) := by
  haveI := h.sc
  exact inferInstanceAs (BorelSpace (Fin a → Fin b → Cv v))

section Sum

variable {n : ℕ} {H : Subgroup (GL (Fin n) (Cv v))} {Q : Matrix (Fin n) (Fin n) (Cv v) → Prop}
  (hQ : ∀ k, k ∈ H ↔ Q k.1) (hU : ∀ x, Q x → UnM x) (g : GL (Fin n) (Cv v))
include hQ hU

variable (h : Pack μ) (hc : IsClopen {x | Q x})
include h hc

variable {F : GL (Fin n) (Cv v) → ℂ} (hR : ∀ z, ∀ k ∈ H, F (z * k) = F z)
  (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (H : Set _) H → F z = 0)
  {P : Matrix (Fin n) (Fin n) (Cv v) → Prop} {y : ℂ}
include hR h0

end Sum

end CompanionTheory.D.Upq.DoubleCosetLemmas
end
end

section
noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {r d c : ℕ}
  {δ : (Cv v)ˣ →* ℂˣ}

def Cnd (x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) : Prop :=
  UnM (bAA x) ∧ SmM (bDA x) ∧ IntM (bAD x) ∧ IntM (bDD x)

theorem IntM.add {a b : Type} {x y : Matrix a b (Cv v)} (hx : IntM x) (hy : IntM y) :
    IntM (x + y) := fun i j => Valuation.map_add_le _ (hx i j) (hy i j)

theorem UnM.mul {n : ℕ} {x y : Matrix (Fin n) (Fin n) (Cv v)} (hx : UnM x) (hy : UnM y) :
    UnM (x * y) := ⟨hx.1.mul hy.1, by rw [det_mul, map_mul, hx.2, hy.2, one_mul]⟩

theorem un_add_sm (hδ : IsTame v δ) {n : ℕ} {x s : Matrix (Fin n) (Fin n) (Cv v)} (hx : UnM x)
    (hs : SmM s) : UnM (x + s) ∧ chi0 δ (x + s).det = chi0 δ x.det := by
  have hi := hx.1.add hs.int
  have h1 := det_congr hi hx.1 (by rwa [add_sub_cancel_left])
  refine ⟨⟨hi, ?_⟩, extendedCharacter_congr_of_tame hδ hx.2 h1⟩
  rw [← sub_add_cancel (x + s).det x.det, Valuation.map_add_eq_of_lt_right _ (by rwa [hx.2]), hx.2]

theorem Cnd.mul (hδ : IsTame v δ) {e : ℕ} {x : Matrix (Fin (r + e)) (Fin (r + d)) (Cv v)}
    {y : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)} (hx : Cnd x) (hy : Cnd y) :
    Cnd (x * y) ∧ chi0 δ (bAA (x * y)).det = chi0 δ (bAA x).det * chi0 δ (bAA y).det := by
  have h := un_add_sm hδ (hx.1.mul hy.1) (hx.2.2.1.mul_sm hy.2.1)
  rw [Cnd, bAA_mul, bDA_mul, bAD_mul, bDD_mul, h.2, det_mul, unitCharExtendedByZero_mul]
  exact ⟨⟨h.1, (hx.2.1.mul_int hy.1.1).add (hx.2.2.2.mul_sm hy.2.1),
    (hx.1.1.mul hy.2.2.1).add (hx.2.2.1.mul hy.2.2.2),
    (hx.2.1.int.mul hy.2.2.1).add (hx.2.2.2.mul hy.2.2.2)⟩, rfl⟩

variable {J : Subgroup (GL (Fin (r + c)) (Cv v))} {J' : Subgroup (GL (Fin (r + d)) (Cv v))}

end CompanionTheory.D.Upq.DoubleCosetLemmas
end
end

section
noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {r d c : ℕ}
  {δS δT : (Cv v)ˣ →* ℂˣ}
  {J : Subgroup (GL (Fin (r + c)) (Cv v))} {J' : Subgroup (GL (Fin (r + d)) (Cv v))}

def FT (δS δT : (Cv v)ˣ →* ℂˣ) (h : GL (Fin (r + d)) (Cv v) → ℂ)
    (y : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) (z : GL (Fin (r + d)) (Cv v)) : ℂ :=
  h z * linAct v δS δT 1 z (phiB v δT r d c) y

def FS (δS δT : (Cv v)ˣ →* ℂˣ) (h : GL (Fin (r + c)) (Cv v) → ℂ)
    (y : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) (z : GL (Fin (r + c)) (Cv v)) : ℂ :=
  h z * linAct v δS δT z 1 (phiB v δT r d c) y

section Laws

variable (hS : IsTame v δS) (hT : IsTame v δT)
  (he : ∀ x : (Cv v)ˣ, Valued.v (x : Cv v) = 1 → δS x = δT x)
include hS hT he

end Laws

open Classical in

def eps (δ : (Cv v)ˣ →* ℂˣ) (x : Matrix (Fin r) (Fin r) (Cv v)) : ℂ :=
  if UnM x then chi0 δ x.det else 0

end CompanionTheory.D.Upq.DoubleCosetLemmas
end
end
