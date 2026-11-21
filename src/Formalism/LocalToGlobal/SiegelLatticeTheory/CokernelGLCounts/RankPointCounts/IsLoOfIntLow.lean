import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobMoveOf
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMono
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolGrp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxLoc

section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount

section Lat

variable {K : Type*} [CommRing K] (I : Subring K)

def lat (c : K) : AddSubgroup K where
  carrier := {x | ∃ y ∈ I, x = c * y}
  zero_mem' := ⟨0, I.zero_mem, by simp⟩
  add_mem' := by
    rintro x x' ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', I.add_mem hy hy', by ring⟩
  neg_mem' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, I.neg_mem hy, by ring⟩

variable {I}

theorem lat_mul {c c' x x' : K} (hx : x ∈ lat I c) (hx' : x' ∈ lat I c') : x * x' ∈ lat I (c * c') := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hx'
  exact ⟨y * y', I.mul_mem hy hy', by ring⟩

theorem lat_bmul {t c b x : K} (hb : t * b ∈ I) (hx : x ∈ lat I (t * c)) : b * x ∈ lat I c := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨t * b * y, I.mul_mem hb hy, by ring⟩

theorem lat_mulb {t c b x : K} (hb : t * b ∈ I) (hx : x ∈ lat I (t * c)) : x * b ∈ lat I c := by
  rw [mul_comm]; exact lat_bmul hb hx

theorem lat_mono {t c x : K} (ht : t ∈ I) (hx : x ∈ lat I (t * c)) : x ∈ lat I c := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨t * y, I.mul_mem ht hy, by ring⟩

theorem mem_of_lat {c x : K} (hc : c ∈ I) (hx : x ∈ lat I c) : x ∈ I := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact I.mul_mem hc hy

theorem lat_one {x : K} (hx : x ∈ lat I 1) : x ∈ I := mem_of_lat I.one_mem hx

theorem lat_sq {c : K} (hc : c ∈ I) : ∀ x ∈ lat I c, ∀ y ∈ lat I c, x * y ∈ lat I c :=
  fun _ hx _ hy => lat_mono hc (lat_mul hx hy)

variable {n : ℕ}

theorem ent_bmul {t c : K} {B X : Matrix (Fin n) (Fin n) K} (hB : ∀ i j, t * B i j ∈ I)
    (hX : EntIn (lat I (t * c)) X) : EntIn (lat I c) (B * X) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (lat I c).sum_mem fun k _ => lat_bmul (hB i k) (hX k j)

theorem ent_mulb {t c : K} {B X : Matrix (Fin n) (Fin n) K} (hB : ∀ i j, t * B i j ∈ I)
    (hX : EntIn (lat I (t * c)) X) : EntIn (lat I c) (X * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (lat I c).sum_mem fun k _ => lat_mulb (hB k j) (hX i k)

theorem ent_mono {t c : K} (ht : t ∈ I) {X : Matrix (Fin n) (Fin n) K} (hX : EntIn (lat I (t * c)) X) :
    EntIn (lat I c) X := fun i j => lat_mono ht (hX i j)

end Lat

section Bnd

variable {Fp : Type*} [Field Fp] {K : Type*} [CommRing K] [Algebra Fp K] {I : Subring K}

theorem bnd_fin (O : Subring Fp) (hI : ∀ s ∈ O, algebraMap Fp K s ∈ I) {ι : Type*} [Fintype ι] (f : ι → K)
    (h : ∀ i, ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ algebraMap Fp K s * f i ∈ I) :
    ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ ∀ i, algebraMap Fp K s * f i ∈ I := by
  classical
  choose s hs0 hsO hs using h
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, O.prod_mem fun i _ => hsO i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), map_mul,
    mul_comm (algebraMap Fp K (s i)), mul_assoc]
  exact I.mul_mem (hI _ (O.prod_mem fun j _ => hsO j)) (hs i)

end Bnd

section Stab

variable {K : Type*} [CommRing K]

theorem stab_core {r : ℕ} {P P' Q Q' N kL kR : Matrix (Fin (r + 1)) (Fin (r + 1)) K} {s e : K} (hs : IsUnit s)
    (hP : P' * P = 1) (hQ : Q * Q' = 1) (hkL : IsLo kL) (hkR : IsUp kR)
    (hk : kL * (s • (P * N * Q) - e • Ecorner r) * kR = s • (P * N * Q) - e • Ecorner r) :
    (P' * kL * P) * N * (Q * kR * Q') = N := by
  have h1 : kL * (s • (P * N * Q) - e • Ecorner r) * kR = s • (kL * (P * N * Q) * kR) - e • Ecorner r := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hkL hkR]
  rw [h1] at hk
  have h2 : s • (kL * (P * N * Q) * kR) = s • (P * N * Q) := sub_left_injective hk
  have h3 : kL * (P * N * Q) * kR = P * N * Q := hs.smul_left_cancel.mp h2
  calc (P' * kL * P) * N * (Q * kR * Q') = P' * (kL * (P * N * Q) * kR) * Q' := by
        simp only [Matrix.mul_assoc]
    _ = N := by
        rw [h3]
        simp only [Matrix.mul_assoc]
        rw [hQ, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.one_mul]

variable {n : ℕ}

theorem fix_of {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {z w : Matrix (Fin n) (Fin n) K} (hw : IsUp w) (h : z * mono σ ν * w = mono σ ν) :
    (∀ i j, σ j < σ i → z i j = 0) ∧ cOf σ ν z * w = 1 ∧ w * cOf σ ν z = 1 := by
  have hdw : IsUnit w.det := by rw [det_up' hw]; exact isUnit_one
  have e1 : z * mono σ ν = mono σ ν * w⁻¹ := by
    calc z * mono σ ν = z * mono σ ν * (w * w⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdw, Matrix.mul_one]
      _ = mono σ ν * w⁻¹ := by rw [← Matrix.mul_assoc, h]
  have hwi := isUp_inv hw
  have hpat := fix_pat hσ ν hν (fun i j hij => hwi.2 j i hij) e1
  have e2 : cOf σ ν z = w⁻¹ := by
    have e3 : mono σ ν * cOf σ ν z = mono σ ν * w⁻¹ := by rw [← fix_cOf hσ ν hν z, e1]
    ext a b
    have := congrFun (congrFun e3 (σ a)) b
    rw [mono_mul, mono_mul, hσ] at this
    exact (hν (σ a)).mul_left_cancel this
  refine ⟨hpat, ?_, ?_⟩
  · rw [e2, Matrix.nonsing_inv_mul _ hdw]
  · rw [e2, Matrix.mul_nonsing_inv _ hdw]

theorem fix_inv {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {x w : Matrix (Fin n) (Fin n) K} (hx : IsLo x) (hw : IsUp w) (h : x * mono σ ν * w = mono σ ν) :
    IsLo x⁻¹ ∧ (∀ i j, σ j < σ i → x⁻¹ i j = 0) ∧ x * x⁻¹ = 1 := by
  have hdx : IsUnit x.det := by rw [det_lo' hx]; exact isUnit_one
  have e1 : x⁻¹ * mono σ ν = mono σ ν * w := by
    calc x⁻¹ * mono σ ν = x⁻¹ * (x * mono σ ν * w) := by rw [h]
      _ = mono σ ν * w := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdx, Matrix.one_mul]
  exact ⟨isLo_inv hx, fix_pat hσ ν hν (fun i j hij => hw.2 j i hij) e1, Matrix.mul_nonsing_inv _ hdx⟩

end Stab

section Close

variable {K : Type*} [CommRing K] {I : Subring K} {n : ℕ}

theorem cOf_sub_one {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {t c : K} (hb : ∀ a, t * ν a ∈ I) (hb' : ∀ a, t * Ring.inverse (ν a) ∈ I) {z : Matrix (Fin n) (Fin n) K}
    (hz : EntIn (lat I (t * (t * c))) (z - 1)) : EntIn (lat I c) (cOf σ ν z - 1) := by
  intro a b
  have e : (cOf σ ν z - 1) a b = Ring.inverse (ν (σ a)) * (z - 1) (σ a) (σ b) * ν (σ b) := by
    rw [Matrix.sub_apply, Matrix.sub_apply]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      simp only [cOf, Matrix.of_apply]
      rw [mul_sub, sub_mul, mul_one, Ring.inverse_mul_cancel _ (hν _)]
    · have : σ a ≠ σ b := fun h => hab (by rw [← hσ a, h, hσ])
      rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne this]
      simp only [cOf, Matrix.of_apply, sub_zero]
  rw [e]
  exact lat_mulb (hb _) (lat_bmul (hb' _) (hz _ _))

theorem close_of_target {t c : K} {x T G : Matrix (Fin n) (Fin n) K} (hxT : x * T = 1) (bx : ∀ i j, t * x i j ∈ I)
    (hG : EntIn (lat I (t * c)) (G - T)) : EntIn (lat I c) (x * G - 1) := by
  have e : x * G - 1 = x * (G - T) := by rw [Matrix.mul_sub, hxT]
  rw [e]
  exact ent_bmul bx hG

theorem conj_eq {P P' X : Matrix (Fin n) (Fin n) K} (hPP : P * P' = 1) : P * (P' * X * P) * P' = X := by
  simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  rw [Matrix.mul_assoc, hPP, Matrix.mul_one]

theorem conj_sub_one {P P' X : Matrix (Fin n) (Fin n) K} (hPP : P * P' = 1) : P * (P' * X * P - 1) * P' = X - 1 := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP, conj_eq hPP]

theorem close_pair {r : ℕ} {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → K}
    (hν : ∀ a, IsUnit (ν a)) {t c : K} (ht : t ∈ I) (hc : c ∈ I) (hbν : ∀ a, t * ν a ∈ I)
    (hbν' : ∀ a, t * Ring.inverse (ν a) ∈ I) {P P' Q Q' : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hPP : P * P' = 1) (hP'P : P' * P = 1) (hQQ : Q * Q' = 1) (hQ'Q : Q' * Q = 1) (bP : ∀ i j, t * P i j ∈ I)
    (bP' : ∀ i j, t * P' i j ∈ I) (bQ : ∀ i j, t * Q i j ∈ I) (bQ' : ∀ i j, t * Q' i j ∈ I) {s e : K}
    (hs : IsUnit s) {a b : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (ha : IsLo a) (hb : IsUp b)
    (hab : a * (s • (P * mono σ ν * Q) - e • Ecorner r) * b = s • (P * mono σ ν * Q) - e • Ecorner r)
    (hz : IsLo (P' * a * P)) (hw : IsUp (Q * b * Q'))
    (hcl : EntIn (lat I (t * (t * (t * (t * c))))) (P' * a * P - 1)) :
    EntIn (lat I c) (a - 1) ∧ EntIn (lat I c) (b - 1) := by
  have hzw := stab_core hs hP'P hQQ ha hb hab
  obtain ⟨hpat, h1, h2⟩ := fix_of hσ hν hw hzw
  have hz2 : EntIn (lat I (t * (t * c))) (P' * a * P - 1) := ent_mono ht (ent_mono ht hcl)
  refine ⟨?_, ?_⟩
  · rw [← conj_sub_one hPP]
    exact ent_mulb bP' (ent_bmul bP hz2)
  · have hcO := cOf_sub_one hσ hν hbν hbν' hcl
    let x : GL (Fin (r + 1)) K := ⟨cOf σ ν (P' * a * P), Q * b * Q', h1, h2⟩
    have hup := cOf_up hσ ν (P' * a * P) hz.1 hpat hν
    have hJ : ∀ u ∈ lat I (t * (t * c)), ∀ v ∈ lat I (t * (t * c)), u * v ∈ lat I (t * (t * c)) :=
      lat_sq (I.mul_mem ht (I.mul_mem ht hc))
    have hlow : ∀ i j : Fin (r + 1), (fun k : Fin (r + 1) => r - k.val) i ≤ (fun k : Fin (r + 1) => r - k.val) j →
        ((x : Matrix (Fin (r + 1)) (Fin (r + 1)) K) - 1) i j = 0 := by
      intro i j hij
      have hij' : r - i.val ≤ r - j.val := hij
      have hji : j ≤ i := by
        rw [Fin.le_iff_val_le_val]
        have := i.isLt; have := j.isLt
        omega
      rw [Matrix.sub_apply]
      rcases hji.eq_or_lt with hji | hji
      · subst hji
        rw [Matrix.one_apply_eq]
        show cOf σ ν (P' * a * P) j j - 1 = 0
        rw [hup.1 j, sub_self]
      · rw [Matrix.one_apply_ne (Fin.ne_of_gt hji)]
        show cOf σ ν (P' * a * P) i j - 0 = 0
        rw [hup.2 i j hji, sub_self]
    have hinv := (inv_sub_one (fun k : Fin (r + 1) => r - k.val) (fun i => Nat.lt_succ_of_le (Nat.sub_le r i.val)) hJ x hlow hcO).1
    have hw1 : EntIn (lat I (t * (t * c))) (Q * b * Q' - 1) := hinv
    rw [← conj_sub_one hQ'Q]
    exact ent_mulb bQ (ent_bmul bQ' hw1)

end Close

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount

section Comp

variable {E : Type*} [Field E] {K : Type*} [CommRing K] (ψ : E →+* K) {r : ℕ}

def cP (cv : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv * L₁.map ψ

def cP' (cv' : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  L₁⁻¹.map ψ * Matrix.diagonal cv'

def cQ (cv : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  U₁.map ψ * Matrix.diagonal cv

def cQ' (cv' : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv' * U₁⁻¹.map ψ

theorem diag_one {cv cv' : Fin (r + 1) → K} (h : ∀ a, cv a * cv' a = 1) :
    Matrix.diagonal cv * Matrix.diagonal cv' = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext h)

theorem map_one' : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E).map ψ = 1 := Matrix.map_one _ ψ.map_zero ψ.map_one

theorem map_inv_mul {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L⁻¹.map ψ * L.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (by rw [h]; exact isUnit_one), map_one']

theorem map_mul_inv {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L.map ψ * L⁻¹.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (by rw [h]; exact isUnit_one), map_one']

theorem mono_map (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    (mono σ ν).map ψ = mono σ (fun a => ψ (ν a)) := by
  ext a b
  simp only [Matrix.map_apply, mono, Matrix.of_apply]
  split_ifs <;> simp

theorem inv_eq_map {x : E} (hx : x ≠ 0) : Ring.inverse (ψ x) = ψ x⁻¹ := by
  have h1 : ψ x * ψ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  calc Ring.inverse (ψ x) = Ring.inverse (ψ x) * (ψ x * ψ x⁻¹) := by rw [h1, mul_one]
    _ = ψ x⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ ⟨⟨ψ x, ψ x⁻¹, h1, by rw [mul_comm]; exact h1⟩, rfl⟩, one_mul]

theorem hcv'_of {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) : ∀ a, cv' a * cv a = 1 :=
  fun a => by rw [mul_comm]; exact hcv a

variable {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) {L₁ U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
include hcv hL₁ hU₁

theorem conjPrime_conjPrime₂ : cP ψ cv L₁ * cP' ψ cv' L₁ = 1 := by
  unfold cP cP'
  rw [show Matrix.diagonal cv * L₁.map ψ * (L₁⁻¹.map ψ * Matrix.diagonal cv') =
      Matrix.diagonal cv * (L₁.map ψ * L₁⁻¹.map ψ) * Matrix.diagonal cv' by simp only [Matrix.mul_assoc],
    map_mul_inv ψ (det_lo hL₁), Matrix.mul_one, diag_one hcv]

theorem cP'_cP : cP' ψ cv' L₁ * cP ψ cv L₁ = 1 := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc],
    diag_one (hcv'_of hcv), Matrix.mul_one, map_inv_mul ψ (det_lo hL₁)]

theorem cQ_cQ' : cQ ψ cv U₁ * cQ' ψ cv' U₁ = 1 := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc],
    diag_one hcv, Matrix.mul_one, map_mul_inv ψ (det_up hU₁)]

theorem cQ'_cQ : cQ' ψ cv' U₁ * cQ ψ cv U₁ = 1 := by
  unfold cQ cQ'
  rw [show Matrix.diagonal cv' * U₁⁻¹.map ψ * (U₁.map ψ * Matrix.diagonal cv) =
      Matrix.diagonal cv' * (U₁⁻¹.map ψ * U₁.map ψ) * Matrix.diagonal cv by simp only [Matrix.mul_assoc],
    map_inv_mul ψ (det_up hU₁), Matrix.mul_one, diag_one (hcv'_of hcv)]

theorem cP_lo {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsLo k) : IsLo (cP' ψ cv' L₁ * k * cP ψ cv L₁) := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * k * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * k * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc]]
  exact isLo_mul (isLo_mul (isLo_map ψ (isLo_inv hL₁)) (isLo_conj hk cv' cv (hcv'_of hcv))) (isLo_map ψ hL₁)

theorem cQ_up {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsUp k) : IsUp (cQ ψ cv U₁ * k * cQ' ψ cv' U₁) := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * k * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * k * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc]]
  exact isUp_mul (isUp_mul (isUp_map ψ hU₁) (isUp_conj hk cv cv' hcv)) (isUp_map ψ (isUp_inv hU₁))

theorem cW_eq (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) (s e : K) :
    s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r =
      s • (cP ψ cv L₁ * mono σ (fun a => ψ (ν a)) * cQ ψ cv U₁) - e • Ecorner r := by
  unfold cP cQ
  rw [Matrix.map_mul, Matrix.map_mul, mono_map]
  simp only [Matrix.mul_assoc]

theorem cG_eq (X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cP' ψ cv' L₁ * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv') * cP ψ cv L₁ = X'.map ψ := by
  have e : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Matrix.diagonal cv' * (Matrix.diagonal cv * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, diag_one (hcv'_of hcv), Matrix.one_mul]
  have f : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, L₁⁻¹.map ψ * (L₁.map ψ * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, map_inv_mul ψ (det_lo hL₁), Matrix.one_mul]
  unfold cP cP'
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc, e, f, map_inv_mul ψ (det_lo hL₁), Matrix.mul_one]

theorem conj_mul {P P' A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hPP : P * P' = 1) :
    P' * (A * B) * P = (P' * A * P) * (P' * B * P) := by
  rw [show P' * A * P * (P' * B * P) = P' * A * (P * P') * B * P by simp only [Matrix.mul_assoc], hPP,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem comp_target {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {kL kR : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hkL : IsLo kL)
    (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) :
    IsLo (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ ∧ (∀ i j, σ j < σ i → (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ i j = 0) ∧
      (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ = 1 := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  rw [cW_eq ψ hcv hL₁ hU₁] at hk
  have hfix := stab_core hs (cP'_cP ψ hcv hL₁ hU₁) (cQ_cQ' ψ hcv hL₁ hU₁) hkL hkR hk
  exact fix_inv hσ hν' (cP_lo ψ hcv hL₁ hU₁ hkL) (cQ_up ψ hcv hL₁ hU₁ hkR) hfix

theorem comp_main {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {I : Subring K} {kL kR a b : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hkL : IsLo kL) (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    (ha : IsLo a) (hb : IsUp b)
    (hab : a * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * b =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    {X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (haX : a = kL * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv'))
    {t c : K} (ht : t ∈ I) (hc : c ∈ I) (hbν : ∀ a, t * ψ (ν a) ∈ I) (hbν' : ∀ a, t * ψ (ν a)⁻¹ ∈ I)
    (bP : ∀ i j, t * cP ψ cv L₁ i j ∈ I) (bP' : ∀ i j, t * cP' ψ cv' L₁ i j ∈ I)
    (bQ : ∀ i j, t * cQ ψ cv U₁ i j ∈ I) (bQ' : ∀ i j, t * cQ' ψ cv' U₁ i j ∈ I)
    (bx : ∀ i j, t * (cP' ψ cv' L₁ * kL * cP ψ cv L₁) i j ∈ I)
    (hG : EntIn (lat I (t * (t * (t * (t * (t * c)))))) (X'.map ψ - (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹)) :
    EntIn (lat I c) (a - 1) ∧ EntIn (lat I c) (b - 1) := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  have hinv : ∀ x, t * Ring.inverse (ψ (ν x)) ∈ I := fun x => by
    rw [inv_eq_map ψ (hν x)]
    exact hbν' x
  have hT := (comp_target ψ hcv hL₁ hU₁ hσ hν hs hkL hkR hk).2.2
  have hA : cP' ψ cv' L₁ * a * cP ψ cv L₁ = (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * X'.map ψ := by
    rw [haX, conj_mul hcv hL₁ hU₁ (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁), cG_eq ψ hcv hL₁ hU₁]
  have hE := close_of_target hT bx hG
  rw [← hA] at hE
  rw [cW_eq ψ hcv hL₁ hU₁] at hab
  exact close_pair hσ hν' ht hc hbν hinv (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁) (cP'_cP ψ hcv hL₁ hU₁)
    (cQ_cQ' ψ hcv hL₁ hU₁) (cQ'_cQ ψ hcv hL₁ hU₁) bP bP' bQ bQ' hs ha hb hab (cP_lo ψ hcv hL₁ hU₁ ha)
    (cQ_up ψ hcv hL₁ hU₁ hb) hE

end Comp

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Theta

variable {K : Type*} [CommRing K] {r : ℕ}

theorem signMatrix_transpose : (Sg K r).transpose = Sg K r := Matrix.diagonal_transpose _

theorem theta_mul (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (M * N).transpose * Sg K r = (Sg K r * N.transpose * Sg K r) * (Sg K r * M.transpose * Sg K r) := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Sg K r) (Sg K r), sg_sq, Matrix.one_mul]

theorem theta_theta (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (Sg K r * M.transpose * Sg K r).transpose * Sg K r = M := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, signMatrix_transpose, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [sg_sq, Matrix.mul_one, ← Matrix.mul_assoc, sg_sq, Matrix.one_mul]

theorem theta_stab {a Y b : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : a * Y * b = Y) :
    (Sg K r * b.transpose * Sg K r) * (Sg K r * Y.transpose * Sg K r) * (Sg K r * a.transpose * Sg K r) =
      Sg K r * Y.transpose * Sg K r := by
  rw [← theta_mul, ← theta_mul, ← Matrix.mul_assoc, h]

theorem theta_sub_one (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (M - 1).transpose * Sg K r = Sg K r * M.transpose * Sg K r - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sg_sq]

theorem theta_lo {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUp U) : IsLo (Sg K r * U.transpose * Sg K r) :=
  isLo_conj (isLo_transpose h) _ _ (fun a => sgn_sq' r a)

theorem theta_up {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLo L) : IsUp (Sg K r * L.transpose * Sg K r) :=
  isUp_conj (isUp_transpose h) _ _ (fun a => sgn_sq' r a)

theorem neg_one_pow_mem (J : AddSubgroup K) (k : ℕ) {x : K} (hx : x ∈ J) : (-1 : K) ^ k * x ∈ J := by
  rcases neg_one_pow_eq_or K k with h | h <;> rw [h]
  · rwa [one_mul]
  · rw [neg_one_mul]; exact J.neg_mem hx

theorem ent_theta {J : AddSubgroup K} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : EntIn J M) :
    EntIn J (Sg K r * M.transpose * Sg K r) := by
  intro i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  rw [mul_comm]
  exact neg_one_pow_mem J _ (neg_one_pow_mem J _ (h j i))

theorem sign_transpose_twisted (s e : K) (cf : Fin (r + 1) → K) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (s • (Matrix.diagonal cf * (Z.transpose * Sg K r) * Matrix.diagonal cf) - e • Ecorner r).transpose *
      Sg K r = s • (Matrix.diagonal cf * (Z * Sg K r) * Matrix.diagonal cf) - e • Ecorner r := by
  ext i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Ecorner, Matrix.of_apply]
  have hs := sgn_sq' (R := K) r
  by_cases hij : i = Fin.last r ∧ j = Fin.last r
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · have hji : ¬ (j = Fin.last r ∧ i = Fin.last r) := fun h => hij ⟨h.2, h.1⟩
    rw [if_neg hij, if_neg hji]
    linear_combination (s * cf i * cf j * Z i j * (-1 : K) ^ (r - j.val)) * hs i

theorem theta_move (cf cfi : Fin (r + 1) → K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (Matrix.diagonal cfi * (Sg K r * A.transpose * Sg K r) * Matrix.diagonal cf).transpose * Sg K r =
      Matrix.diagonal cf * A * Matrix.diagonal cfi := by
  ext i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have hs := sgn_sq' (R := K) r
  linear_combination (cf i * A i j * cfi j * (-1 : K) ^ (r - j.val) * (-1 : K) ^ (r - j.val)) * hs i +
    (cf i * A i j * cfi j) * hs j

end Theta

section ModelR

variable {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [CommRing Ep] [Algebra Fp Ep]
  [TopologicalSpace Ep] [MeasurableSpace Ep]

theorem mem_R_of (M : Formalism.MainNotions.S.Loc.Model Fp Ep) (g : Formalism.MainNotions.S.Loc.SplitG M.L) (hM : M.split = some g) (x : Ep)
    (h1 : (g.e x).1 ∈ 𝒪[Fp]) (h2 : (g.e x).2 ∈ 𝒪[Fp])
    (h3 : ∃ t ∈ 𝒪[Fp], (g.e x).1 - (g.e x).2 = (g.q : Fp) * t) : x ∈ M.R := by
  obtain ⟨L, sp, mu⟩ := M
  change Formalism.MainNotions.S.Loc.SplitG L at g
  obtain rfl : sp = some g := hM
  exact (Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x).2 ⟨h1, h2, h3⟩

end ModelR

section Place

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem ptMat_mono' (w : Point D.host.E (D.R.rS + 1)) : ptMat w = mono (fσ w) (fun a => pv w.1 a) := by
  ext a b
  rw [ptMat_fσ]
  rfl

def gX (L₁ X' : PairVal.MatR D) : PairVal.MatR D := L₁ * X' * L₁⁻¹

def gY (w : Point D.host.E (D.R.rS + 1)) (U₁ X' : PairVal.MatR D) : PairVal.MatR D :=
  U₁⁻¹ * (cOf (fσ w) (fun a => pv w.1 a) X')⁻¹ * U₁

theorem glob_stab (w : Point D.host.E (D.R.rS + 1)) {Z₁ L₁ U₁ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) :
    IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧
      gX L₁ X' * (Z₁ * Sg D.host.E D.R.rS) * gY w U₁ X' = Z₁ * Sg D.host.E D.R.rS := by
  have hν : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hdc : IsUnit (cOf (fσ w) (fun a => pv w.1 a) X').det := by rw [det_up' hc]; exact isUnit_one
  have hdL : IsUnit L₁.det := by rw [det_lo' hL₁]; exact isUnit_one
  have hdU : IsUnit U₁.det := by rw [det_up' hU₁]; exact isUnit_one
  refine ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, ?_⟩
  have hfix := fix_cOf (fσ_fσ w) (fun a => pv w.1 a) hν X'
  rw [hZ, ptMat_mono']
  simp only [gX, gY, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc L₁⁻¹ L₁, Matrix.nonsing_inv_mul _ hdL, Matrix.one_mul, ← Matrix.mul_assoc U₁ U₁⁻¹,
    Matrix.mul_nonsing_inv _ hdU, Matrix.one_mul, ← Matrix.mul_assoc X' (mono (fσ w) (fun a => pv w.1 a)), hfix,
    Matrix.mul_assoc (mono (fσ w) (fun a => pv w.1 a)),
    ← Matrix.mul_assoc (cOf (fσ w) (fun a => pv w.1 a) X') (cOf (fσ w) (fun a => pv w.1 a) X')⁻¹,
    Matrix.mul_nonsing_inv _ hdc, Matrix.one_mul]

theorem locL_lo (p : PlF D) {A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B) : IsLo (locL Zd p A B) := by
  rcases hM : (Zd.M p).split with _ | g <;> simp only [locL, hM]
  · exact isLo_conj (isLo_map _ hA) _ _ (fun a => by simp only [← map_mul, cf_cfi, map_one])
  · exact isLo_glue _ (isLo_conj (isLo_map _ hA) _ _ (cf_cfi Zd p))
      (isLo_conj (theta_lo (isUp_map _ hB)) _ _ (cf_cfi Zd p))

theorem locR_up (p : PlF D) {A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B) : IsUp (locR Zd p A B) := by
  rcases hM : (Zd.M p).split with _ | g <;> simp only [locR, hM]
  · exact isUp_conj (isUp_map _ hB) _ _ (fun a => by simp only [← map_mul, cfi_cf, map_one])
  · exact isUp_glue _ (isUp_conj (isUp_map _ hB) _ _ (cfi_cf Zd p))
      (isUp_conj (theta_up (isLo_map _ hA)) _ _ (cfi_cf Zd p))

theorem key_stab (p : PlF D) {l ρ L R Yp : MatP D p} (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : L * Yp * R = l * Yp * ρ) : (l⁻¹ * L) * Yp * (R * ρ⁻¹) = Yp := by
  obtain ⟨-, hll, -⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨-, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  calc (l⁻¹ * L) * Yp * (R * ρ⁻¹) = l⁻¹ * (L * Yp * R) * ρ⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Yp := by
      rw [h]
      simp only [Matrix.mul_assoc]
      rw [hρρ, Matrix.mul_one, ← Matrix.mul_assoc, hll, Matrix.one_mul]

theorem corr_move (u u' : D.what₂.Word) (p : PlF D) {Z₁ A₀ B₀ X Y : PairVal.MatR D} (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX : IsLo X) (hY : IsUp Y) (hst : X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS) :
    locL Zd p (A₀ * X) (Y * B₀) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
        locR Zd p (A₀ * X) (Y * B₀) =
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ := by
  have h2 : A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS =
      A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ := by
    rw [Matrix.mul_assoc (A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀), sg_sq, Matrix.mul_one]
  have h3 : A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS =
      (A₀ * X) * (Z₁ * Sg D.host.E D.R.rS) * (Y * B₀) := by
    rw [h2]
    conv_lhs => rw [← hst]
    simp only [Matrix.mul_assoc]
  exact (locMove Zd u u' p (isLo_mul hA₀ hX) (isUp_mul hY hB₀) h3).symm.trans (locMove Zd u u' p hA₀ hB₀ h2)

theorem locL_L (p : PlF D) (hM : (Zd.M p).split = none) (A B : PairVal.MatR D) :
    locL Zd p A B = Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
      A.map (D.s.atP p).ιE * Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) := by
  simp only [locL, hM]

theorem locR_L (p : PlF D) (hM : (Zd.M p).split = none) (A B : PairVal.MatR D) :
    locR Zd p A B = Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) *
      B.map (D.s.atP p).ιE * Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := by
  simp only [locR, hM]

section Typed

variable (p : PlF D) {g : Loc.SplitG (Zd.M p).L} (hM : (Zd.M p).split = some g)
  {e : (D.s.atP p).Ep ≃ₐ[(D.s.atP p).Fp] (D.s.atP p).Fp × (D.s.atP p).Fp} (hge : g.e = e)
include hM hge

theorem leftLocal_firstProj (A B : PairVal.MatR D) : (locL Zd p A B).map (p1 e) =
    Matrix.diagonal (cf Zd p) * A.map ((p1 e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p) := by
  simp only [locL, hM, hge, glue_map_fst]



theorem rightLocal_secondProj (A B : PairVal.MatR D) : (locR Zd p A B).map (p2 e) =
    Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 e).comp (D.s.atP p).ιE)).transpose *
      Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p) := by
  simp only [locR, hM, hge, glue_map_snd]

end Typed

end Place

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Free

def Free {n : ℕ} (σ : Fin n → Fin n) (i j : Fin n) : Prop := j < i ∧ σ i < σ j

theorem off_free {K : Type*} [CommRing K] {n : ℕ} {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a)
    {T : Matrix (Fin n) (Fin n) K} (hT : IsLo T) (hpat : ∀ i j, σ j < σ i → T i j = 0) {i j : Fin n}
    (h : ¬ Free σ i j) : T i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hT.2 i j hij, Matrix.one_apply_ne hij.ne]
  · rw [hT.1 i, Matrix.one_apply_eq]
  · have hne : σ i ≠ σ j := fun e => hij.ne' (by rw [← hσ i, e, hσ])
    have : σ j < σ i := by
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd ⟨hij, h'⟩ h
      · exact h'
    rw [hpat i j this, Matrix.one_apply_ne hij.ne']

theorem ent_free {E K : Type*} [Field E] [CommRing K] (ψ : E →+* K) {n : ℕ} {σ : Fin n → Fin n}
    (hσ : ∀ a, σ (σ a) = a) {X' : Matrix (Fin n) (Fin n) E} (hX' : IsLo X') (hpX : ∀ i j, σ j < σ i → X' i j = 0)
    {T : Matrix (Fin n) (Fin n) K} (hT : IsLo T) (hpT : ∀ i j, σ j < σ i → T i j = 0) {J : AddSubgroup K}
    (h : ∀ i j, Free σ i j → ψ (X' i j) - T i j ∈ J) : EntIn J (X'.map ψ - T) := by
  intro i j
  rw [Matrix.sub_apply, Matrix.map_apply]
  by_cases hf : Free σ i j
  · exact h i j hf
  · rw [off_free hσ hX' hpX hf, off_free hσ hT hpT hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem bnd_mats {Fp : Type*} [Field Fp] {K : Type*} [CommRing K] [Algebra Fp K] {I : Subring K} (O : Subring Fp)
    (hI : ∀ s ∈ O, algebraMap Fp K s ∈ I) (hx : ∀ x : K, ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ algebraMap Fp K s * x ∈ I)
    {n k : ℕ} (Ms : Fin k → Matrix (Fin n) (Fin n) K) :
    ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ ∀ m i j, algebraMap Fp K s * Ms m i j ∈ I := by
  obtain ⟨s, hs0, hsO, hs⟩ := bnd_fin O hI (fun q : Fin k × Fin n × Fin n => Ms q.1 q.2.1 q.2.2) (fun q => hx _)
  exact ⟨s, hs0, hsO, fun m i j => hs (m, i, j)⟩

theorem int_of_close {K : Type*} [CommRing K] {I : Subring K} {n : ℕ} {a : Matrix (Fin n) (Fin n) K}
    (h : EntIn (lat I 1) (a - 1)) (i j : Fin n) : a i j ∈ I := by
  have e : a i j = (a - 1) i j + (1 : Matrix (Fin n) (Fin n) K) i j := by rw [Matrix.sub_apply]; ring
  rw [e]
  refine I.add_mem (lat_one (h i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact I.one_mem
  · exact I.zero_mem

end Free

section BadL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def GoodAt (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (L₁ U₁ A₀ B₀ X' : PairVal.MatR D) : Prop :=
  TieN.IntLow (Zd.M p) (locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) ∧
    TieN.IntUp (Zd.M p) (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀))

def LocTarget (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (L₁ U₁ A₀ B₀ : PairVal.MatR D) : Prop :=
  ∃ (T : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) (c : (D.s.atP p).Fp), c ≠ 0 ∧
    ∀ X' : PairVal.MatR D, IsLo X' → (∀ i j, fσ w j < fσ w i → X' i j = 0) →
      (∀ i j, Free (fσ w) i j → ∃ y ∈ (D.s.atP p).O,
        (D.s.atP p).ιE (X' i j) - T i j = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c * y) →
      GoodAt Zd p w L₁ U₁ A₀ B₀ X'

theorem isLo_of_intLow {p : PlF D} {l : MatP D p} (h : TieN.IntLow (Zd.M p) l) : IsLo l := ⟨h.1, h.2.1⟩

theorem isUp_of_intUp {p : PlF D} {ρ : MatP D p} (h : TieN.IntUp (Zd.M p) ρ) : IsUp ρ :=
  ⟨h.1, fun a b hab => h.2.1 b a hab⟩

theorem target_L (u u' : D.what₂.Word) (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  have hcv : ∀ a, (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) a *
      (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) a = 1 :=
    fun a => by simp only [← map_mul, cf_cfi, map_one]
  have hσ : ∀ a, fσ w (fσ w a) = a := fσ_fσ w
  have hν : ∀ a : Fin (D.R.rS + 1), pv w.1 a ≠ 0 := fun a => pv_ne' w a
  have hYp : CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p =
      (1 : (D.s.atP p).Ep) • (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (L₁ * mono (fσ w) (fun a => pv w.1 a) * U₁).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))) -
      (0 : (D.s.atP p).Ep) • Ecorner D.R.rS := by
    rw [one_smul, zero_smul, sub_zero, zzp_sgn_ord Zd u u' p hM Z₁, hZ, ptMat_mono']
  obtain ⟨hli, -, hll'⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨hρi, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  have hkL : IsLo (l⁻¹ * locL Zd p A₀ B₀) := isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p hA₀ hB₀)
  have hkR : IsUp (locR Zd p A₀ B₀ * ρ⁻¹) := isUp_mul (locR_up Zd p hA₀ hB₀) (isUp_of_intUp Zd hρi)
  have hk := key_stab Zd p hl hρ h
  rw [hYp] at hk
  obtain ⟨hTlo, hTpat, -⟩ := comp_target (D.s.atP p).ιE hcv hL₁ hU₁ hσ hν isUnit_one hkL hkR hk
  obtain ⟨t, ht0, htO, hb⟩ := bnd_mats 𝒪[(D.s.atP p).Fp] (fun s hs => alg_mem_O hs) (fun x => bounded x)
    ![cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁,
      cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁,
      cQ (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) U₁,
      cQ' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) U₁,
      Matrix.of fun i _ => (D.s.atP p).ιE (pv w.1 i), Matrix.of fun i _ => (D.s.atP p).ιE (pv w.1 i)⁻¹,
      cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁]
  refine ⟨(cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁)⁻¹,
    t * (t * (t * (t * (t * 1)))), by simp [ht0], ?_⟩
  intro X' hX' hpat hfree
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ hZ hX' hpat
  have hab := key_stab Zd p hl hρ ((corr_move Zd u u' p hA₀ hB₀ hgX hgY hst).trans h)
  rw [hYp] at hab
  have ha : IsLo (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) :=
    isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀))
  have hb' : IsUp (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) :=
    isUp_mul (locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)) (isUp_of_intUp Zd hρi)
  have haX : l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) = (l⁻¹ * locL Zd p A₀ B₀) *
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (L₁ * X' * L₁⁻¹).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))) := by
    rw [locL_L Zd p hM, locL_L Zd p hM, gX, Matrix.map_mul (L := A₀)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)))
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))), diag_one (hcv'_of hcv),
      Matrix.one_mul]
  have hG : EntIn (lat (D.s.atP p).O (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t *
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t *
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * 1))))))
      (X'.map (D.s.atP p).ιE - (cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁)⁻¹) := by
    refine ent_free (D.s.atP p).ιE hσ hX' hpat hTlo hTpat fun i j hf => ?_
    obtain ⟨y, hy, e⟩ := hfree i j hf
    refine ⟨y, hy, ?_⟩
    rw [e]
    simp only [map_mul, map_one]
  have hcl := comp_main (D.s.atP p).ιE hcv hL₁ hU₁ hσ hν isUnit_one hkL hkR hk ha hb' hab haX
    (alg_mem_O htO) (D.s.atP p).O.one_mem
    (fun a => by simpa using hb 4 a a) (fun a => by simpa using hb 5 a a)
    (fun i j => by simpa using hb 0 i j) (fun i j => by simpa using hb 1 i j)
    (fun i j => by simpa using hb 2 i j) (fun i j => by simpa using hb 3 i j)
    (fun i j => by simpa using hb 6 i j) hG
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  refine ⟨?_, ?_⟩
  · have e : locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        l * (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) := by
      rw [← Matrix.mul_assoc, hll', Matrix.one_mul]
    rw [e]
    refine ZsVolGrp.intLow_mul (Zd.M p) hl ⟨ha.1, ha.2, fun i j => ?_⟩
    rw [hR]
    exact int_of_close hcl.1 i j
  · have e : locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) * ρ := by
      rw [Matrix.mul_assoc, (ZsVolGrp.intUp_inv (Zd.M p) hρ).2.1, Matrix.mul_one]
    rw [e]
    refine ZsVolGrp.intUp_mul (Zd.M p) ⟨hb'.1, fun a b hab => hb'.2 b a hab, fun i j => ?_⟩ hρ
    rw [hR]
    exact int_of_close hcl.2 i j

end BadL

end Formalism.L2.SG.Pf.TupGlobApprox
end
end
