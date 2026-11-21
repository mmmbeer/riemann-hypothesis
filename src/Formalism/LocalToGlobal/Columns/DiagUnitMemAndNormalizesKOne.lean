import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.HilbertNinetyNormOne
import Formalism.LocalToGlobal.Columns.ChainTwFrA

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwTopQ

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem twTQ_HQ_entry {κ : Type} [CommRing κ] {n r b : ℕ} {M : GL (Fin n) κ} (hM : M ∈ HQ κ n r b) {a l : Fin n} (ha : a.1 < r)
    (hl : r ≤ l.1) : (M : Matrix (Fin n) (Fin n) κ) l a = 0 := by
  apply hM
  show coarse r [b] a.1 < coarse r [b] l.1
  unfold coarse
  simp only [blkIdx, if_pos ha, if_neg (not_lt.2 hl)]
  omega

def twInit {n : ℕ} (x : Sp E n) : Sp E (n - 1) := fun i => x ⟨i.1, by have := i.2; omega⟩

def twSnoc {n : ℕ} (x' : Sp E (n - 1)) (t : E) : Sp E n := fun l => if h : l.1 < n - 1 then x' ⟨l.1, h⟩ else t

theorem twInit_snoc {n : ℕ} (x' : Sp E (n - 1)) (t : E) : twInit (twSnoc (n := n) x' t) = x' := by
  funext i
  simp [twInit, twSnoc, i.2]

variable (P : HeightOneSpectrum (𝓞 E))

def twLastI {n : ℕ} (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

theorem twPar_block {n r : ℕ} (hr : r < n) (H : Sp E n ≃ₗ[E] Sp E n) (h' : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1))
    (hH : ∀ x (l : Fin n), H x l = if h : l.1 < n - 1 then h' (twInit x) ⟨l.1, h⟩ else x l)
    (hint : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (h' x' i))
    (hD : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (h' (Pi.single a 1) l / (qOf P : E)))
    (x : Sp E n) (hx : x ∈ LocE.parL P (qOf P) r n 0) : H x ∈ LocE.parL P (qOf P) r n 0 := by
  have hq0 : (qOf P : E) ≠ 0 := by exact_mod_cast (Formalism.L2.Ker.qOf_pos P).ne'
  rw [twParL_mem] at hx ⊢
  have hxI : ∀ l, IntAt P (x l) := fun l => by
    have := hx l
    by_cases hl : r ≤ l.1 ∧ l.1 < n
    · rw [if_pos hl, zpow_one] at this
      have e : x l = (qOf P : E) * ((qOf P : E)⁻¹ * x l) := by field_simp
      rw [e]; exact (ciIntAt_q (P := P) (q := qOf P)).mul this
    · rw [if_neg hl] at this; simpa using this
  have hxD : ∀ l : Fin n, r ≤ l.1 → IntAt P ((qOf P : E)⁻¹ * x l) := fun l hl => by
    have := hx l
    rw [if_pos ⟨hl, l.2⟩, zpow_one] at this
    exact this
  intro l
  rw [hH]
  by_cases hl : l.1 < n - 1
  · rw [dif_pos hl]
    by_cases hDl : r ≤ l.1
    · rw [if_pos ⟨hDl, l.2⟩, zpow_one]
      rw [twApply_coordE h' (twInit x) ⟨l.1, hl⟩, Finset.mul_sum]
      apply twIntAt_sum
      intro a
      have ea : (twE a : Sp E (n - 1)) = Pi.single a 1 := by
        funext j; unfold twE; simp [Pi.single_apply, eq_comm]
      rw [ea]
      by_cases ha : a.1 < r
      · have e : ((qOf P : E))⁻¹ * (twInit x a * h' (Pi.single a 1) ⟨l.1, hl⟩) =
            twInit x a * (h' (Pi.single a 1) ⟨l.1, hl⟩ / (qOf P : E)) := by field_simp
        rw [e]
        exact (hxI _).mul (hD a ⟨l.1, hl⟩ ha hDl)
      · have hxa := hxD ⟨a.1, by have := a.2; omega⟩ (by show r ≤ a.1; omega)
        have e : ((qOf P : E))⁻¹ * (twInit x a * h' (Pi.single a 1) ⟨l.1, hl⟩) =
            ((qOf P : E))⁻¹ * x ⟨a.1, by have := a.2; omega⟩ * h' (Pi.single a 1) ⟨l.1, hl⟩ := by
          unfold twInit; ring
        rw [e]
        refine hxa.mul (hint _ (fun j => ?_) _)
        by_cases hj : j = a
        · subst hj; simp only [Pi.single_eq_same]; exact ⟨1, 1, one_notMem P, by simp⟩
        · rw [Pi.single_eq_of_ne hj]; exact ⟨0, 1, one_notMem P, by simp⟩
    · rw [if_neg (fun h => hDl h.1), zpow_zero, inv_one, one_mul]
      exact hint (twInit x) (fun i => hxI _) ⟨l.1, hl⟩
  · rw [dif_neg hl]
    exact hx l

theorem mem_kOne_of_block {n r c : ℕ} (hr : r < n) (G : ↥(GLint E n P)) (g' : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1))
    (hblk : ∀ x (l : Fin n), (G : Sp E n ≃ₗ[E] Sp E n) x l = if h : l.1 < n - 1 then g' (twInit x) ⟨l.1, h⟩ else x l)
    (hDA : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (g' (Pi.single a 1) l / (qOf P : E)))
    (hDA' : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (g'.symm (Pi.single a 1) l / (qOf P : E))) :
    G ∈ twK1H P n r c := by
  have hn : 0 < n := by omega
  set Gm : Sp E n ≃ₗ[E] Sp E n := (G : Sp E n ≃ₗ[E] Sp E n) with hGm
  have hinitG : ∀ x, twInit (Gm x) = g' (twInit x) := fun x => by
    funext i
    show Gm x ⟨i.1, by have := i.2; omega⟩ = g' (twInit x) i
    rw [hblk, dif_pos i.2]
  have hlastG : ∀ x, Gm x (twLastI hn) = x (twLastI hn) := fun x => by
    rw [hblk, dif_neg (by unfold twLastI; simp)]
  have hinv : ∀ x (l : Fin n), Gm.symm x l = if h : l.1 < n - 1 then g'.symm (twInit x) ⟨l.1, h⟩ else x l := by
    intro x l
    have hx : Gm (Gm.symm x) = x := Gm.apply_symm_apply x
    by_cases h : l.1 < n - 1
    · rw [dif_pos h]
      have e1 : twInit (Gm.symm x) = g'.symm (twInit x) := by
        have h2 := hinitG (Gm.symm x)
        rw [hx] at h2
        rw [h2, LinearEquiv.symm_apply_apply]
      have := congrFun e1 ⟨l.1, h⟩
      unfold twInit at this
      exact this
    · rw [dif_neg h]
      have := congrFun hx l
      rw [hblk, dif_neg h] at this
      exact this
  have hinitG' : ∀ x, twInit (Gm.symm x) = g'.symm (twInit x) := fun x => by
    funext i
    show Gm.symm x ⟨i.1, by have := i.2; omega⟩ = g'.symm (twInit x) i
    rw [hinv, dif_pos i.2]
  have hlastG' : ∀ x, Gm.symm x (twLastI hn) = x (twLastI hn) := fun x => by
    rw [hinv, dif_neg (by unfold twLastI; simp)]

  have hstd : ∀ v : Sp E n, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (Gm v l) := fun v hv =>
    (twStd_mem _).1 ((G.2 v).2 ((twStd_mem _).2 hv))
  have hstd' : ∀ v : Sp E n, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (Gm.symm v l) := fun v hv =>
    (twStd_mem _).1 (((G⁻¹).2 v).2 ((twStd_mem _).2 hv))
  have hsnoc : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ l, IntAt P (twSnoc (n := n) x' 0 l) := fun x' hx l => by
    unfold twSnoc; split_ifs
    · exact hx _
    · exact ⟨0, 1, one_notMem P, by simp⟩
  have hg1 : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (g' x' i) := fun x' hx i => by
    have h1 := hstd _ (hsnoc x' hx) ⟨i.1, by have := i.2; omega⟩
    rw [hblk, dif_pos i.2, twInit_snoc] at h1
    exact h1
  have hg2 : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (g'.symm x' i) := fun x' hx i => by
    have h1 := hstd' _ (hsnoc x' hx) ⟨i.1, by have := i.2; omega⟩
    rw [hinv, dif_pos i.2, twInit_snoc] at h1
    exact h1
  have hsc : ∀ (f : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1)), (∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (f x' i)) →
      ∀ x' : Sp E (n - 1), (∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * x' i)) → ∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * f x' i) :=
    fun f hf x' hx i => by
      have h1 := hf (((qOf P : E) ^ (c : ℤ))⁻¹ • x') (fun j => by simpa [Pi.smul_apply, smul_eq_mul] using hx j) i
      rw [map_smul] at h1
      simpa [Pi.smul_apply, smul_eq_mul] using h1
  have hJ : Gm ∈ LocE.JQ P (qOf P) r n 0 := by
    refine ⟨G.2, fun x => ⟨fun h => ?_, twPar_block P hr Gm g' hblk hg1 hDA x⟩⟩
    have := twPar_block P hr Gm.symm g'.symm hinv hg2 hDA' _ h
    rwa [LinearEquiv.symm_apply_apply] at this

  have hL : ∀ (x : Sp E n), x ∈ LocE.sclLat P (qOf P) n (kOneLastExponents n c) ↔ (∀ i, IntAt P (twInit x i)) ∧
      IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * x (twLastI hn)) := by
    intro x
    rw [ciMem_sclLat]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h ⟨i.1, by have := i.2; omega⟩
        unfold kOneLastExponents at this
        rw [if_neg (show ¬ (i.1 + 1 = n) by have := i.2; omega)] at this
        simpa [twInit] using this
      · have := h (twLastI hn)
        have e : kOneLastExponents n c (twLastI hn).1 = (c : ℤ) := by unfold kOneLastExponents twLastI; rw [if_pos (by simp; omega)]
        rw [e] at this
        exact this
    · rintro ⟨h1, h2⟩ l
      unfold kOneLastExponents
      by_cases hl : l.1 + 1 = n
      · rw [if_pos hl]
        have e : l = twLastI hn := Fin.ext (by unfold twLastI; simp; omega)
        rw [e]; exact h2
      · rw [if_neg hl]
        simpa [twInit] using h1 ⟨l.1, by have := l.2; omega⟩
  have hX : ∀ (x : Sp E n), x ∈ LocE.sclLat P (qOf P) n (twistedLevelExponent n c) ↔
      (∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * twInit x i)) ∧ IntAt P (x (twLastI hn)) := by
    intro x
    rw [ciMem_sclLat]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h ⟨i.1, by have := i.2; omega⟩
        unfold twistedLevelExponent at this
        rw [if_neg (show ¬ (i.1 + 1 = n) by have := i.2; omega)] at this
        simpa [twInit] using this
      · have := h (twLastI hn)
        have e : twistedLevelExponent n c (twLastI hn).1 = 0 := by unfold twistedLevelExponent twLastI; rw [if_pos (by simp; omega)]
        rw [e, zpow_zero, inv_one, one_mul] at this
        exact this
    · rintro ⟨h1, h2⟩ l
      unfold twistedLevelExponent
      by_cases hl : l.1 + 1 = n
      · rw [if_pos hl]
        have e : l = twLastI hn := Fin.ext (by unfold twLastI; simp; omega)
        rw [e]; simpa using h2
      · rw [if_neg hl]
        simpa [twInit] using h1 ⟨l.1, by have := l.2; omega⟩
  refine ⟨hJ, fun x => ?_, fun x => ?_, fun w hw => ?_⟩
  · show Gm x ∈ _ ↔ x ∈ _
    rw [hL, hL, hinitG, hlastG]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, h2⟩
      have := hg2 _ h1 i
      rwa [LinearEquiv.symm_apply_apply] at this
    · rintro ⟨h1, h2⟩
      exact ⟨hg1 _ h1, h2⟩
  · show Gm x ∈ _ ↔ x ∈ _
    rw [hX, hX, hinitG, hlastG]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, h2⟩
      have := hsc g'.symm hg2 _ h1 i
      rwa [LinearEquiv.symm_apply_apply] at this
    · rintro ⟨h1, h2⟩
      exact ⟨hsc g' hg1 _ h1, h2⟩
  · rw [hX] at hw
    rw [ciMem_sclLat]
    intro l
    show IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * (Gm w l - w l))
    rw [hblk]
    by_cases hl : l.1 < n - 1
    · rw [dif_pos hl, mul_sub]
      have a1 := hsc g' hg1 _ hw.1 ⟨l.1, hl⟩
      have a2 := hw.1 ⟨l.1, hl⟩
      unfold twInit at a2
      exact ciIntAt_sub a1 a2
    · rw [dif_neg hl, sub_self, mul_zero]; exact ⟨0, 1, one_notMem P, by simp⟩

end TwTopQ

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwK1b

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))

theorem twLamQB_red_one (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {kj n' N : ℕ} (hn : n' ≤ N) (y : Sp E N ≃ₗ[E] Sp E N)
    (hent : ∀ s t : Fin N, kj ≤ s.1 → s.1 < n' → kj ≤ t.1 → t.1 < n' →
      IntAt P (y (Pi.single t 1) s) ∧ redP P (y (Pi.single t 1) s) = if s = t then 1 else 0) :
    LocE.lamQB ξ kj n' (y : Sp E N →ₗ[E] Sp E N) = 1 := by
  classical
  have hlt : ∀ u : Fin (n' - kj), kj + u.1 < N := fun u => by have := u.2; omega
  have hlt' : ∀ u : Fin (n' - kj), kj + u.1 < n' := fun u => by have := u.2; omega
  have hM : ∀ s t : Fin (n' - kj), Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1)
      = y (Pi.single (⟨kj + t.1, hlt t⟩ : Fin N) 1) ⟨kj + s.1, hlt s⟩ := by
    intro s t
    have he : Loc.eN E N (kj + t.1) = Pi.single (⟨kj + t.1, hlt t⟩ : Fin N) 1 := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    rw [he]
    simp only [Loc.atN, dif_pos (hlt s)]
    rfl
  have hent' := fun s t : Fin (n' - kj) =>
    hent ⟨kj + s.1, hlt s⟩ ⟨kj + t.1, hlt t⟩ (by simp) (hlt' s) (by simp) (hlt' t)
  have hdet : redP P (Matrix.of fun s t : Fin (n' - kj) =>
      Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1)).det = 1 := by
    rw [reduction_det_eq_det_reduction]
    · have h1 : (Matrix.of fun s t : Fin (n' - kj) =>
          redP P (Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1))) = 1 := by
        ext s t
        rw [Matrix.of_apply, hM, (hent' s t).2, Matrix.one_apply]
        simp [Fin.ext_iff]
      rw [h1, Matrix.det_one]
    · intro s t
      rw [hM]
      exact (hent' s t).1
  unfold LocE.lamQB LocE.unitV
  split_ifs with hu
  · have hu1 : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
    rw [hu1, map_one, Units.val_one, inv_one]
  · exact absurd (hdet ▸ isUnit_one) hu

theorem twRed0_of_val {w : E} (hw : P.valuation E w < 1) : IntAt P w ∧ redP P w = 0 := by
  classical
  obtain ⟨x, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) w
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  obtain ⟨m, hm⟩ : ∃ m : ℕ, P.intValuation s = WithZero.exp (-(m : ℤ)) :=
    ⟨_, P.intValuation_if_neg hs0⟩
  obtain ⟨J, hJ⟩ := (P.intValuation_le_pow_iff_dvd s m).mp hm.le
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    have h2 : P.asIdeal ^ (m + 1) ∣ Ideal.span {s} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have h3 := (P.intValuation_le_pow_iff_dvd s (m + 1)).mpr h2
    rw [hm, WithZero.exp_le_exp] at h3
    push_cast at h3
    omega
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.mp hJP
  have htE : algebraMap (𝓞 E) E t ≠ 0 := by
    have ht0 : t ≠ 0 := fun h => htP (h ▸ P.asIdeal.zero_mem)
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hx : x ∈ P.asIdeal ^ m := by
    rw [← P.intValuation_le_pow_iff_mem, ← hm, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E x) ≤ P.valuation E (algebraMap (𝓞 E) E s)
    have e : algebraMap (𝓞 E) E x = (algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s) * algebraMap (𝓞 E) E s := by
      field_simp
    rw [e, map_mul]
    exact mul_le_of_le_one_left' hw.le
  have hxt : x * t ∈ Ideal.span {s} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hx htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxt
  have hz' : algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E z / algebraMap (𝓞 E) E t := by
    rw [div_eq_div_iff hsE htE, ← map_mul, ← map_mul, ← hz, mul_comm]
  have hrel : algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E z := by
    rw [hz']
    field_simp
  have ht1 : P.valuation E (algebraMap (𝓞 E) E t) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr htP
  have hzP : z ∈ P.asIdeal := by
    rw [← P.intValuation_lt_one_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E z) < 1
    rw [← hrel, map_mul, ht1, one_mul]
    exact hw
  refine ⟨⟨z, t, htP, hrel⟩, redP_eq P htP hrel ?_⟩
  rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
  exact hzP

end TwK1b

end Formalism.L2.Col
end
end
