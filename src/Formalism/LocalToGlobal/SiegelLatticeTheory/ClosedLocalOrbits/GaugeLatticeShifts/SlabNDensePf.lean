import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipReal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll

section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section CayInv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]

theorem half_add_half' (M : Matrix ι ι K) : (⅟2 : K) • M + (⅟2 : K) • M = M := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

theorem cay_eq {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) :
    cay N Z = (1 + (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z) := by
  set Y : Matrix ι ι K := (⅟2 : K) • Z with hY
  set G := geo N Y with hG
  have hBG : (1 - Y) * G = 1 := by rw [hG, geo, mul_neg_geom_sum, hN, sub_zero]
  have e1 : G = 1 + Y * G := by
    have := hBG
    rw [Matrix.sub_mul, Matrix.one_mul] at this
    rw [← this]; abel
  have e2 : Z = Y + Y := by rw [hY, half_add_half']
  have e3 : cay N Z = 1 + Z * G := rfl
  rw [e3, Matrix.add_mul, Matrix.one_mul]
  calc 1 + Z * G = (1 + Y * G) + Y * G := by rw [e2, Matrix.add_mul]; abel
    _ = G + Y * G := by rw [← e1]

theorem cay_neg_mul {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) : cay N (-Z) * cay N Z = 1 := by
  have hN' : ((⅟2 : K) • -Z) ^ N = 0 := by rw [smul_neg, neg_pow, hN, mul_zero]
  rw [cay_eq hN, cay_eq hN', smul_neg]
  set Y : Matrix ι ι K := (⅟2 : K) • Z with hY
  have h1 : geo N (-Y) * (1 + Y) = 1 := by
    have := geom_sum_mul_neg (-Y) N
    rw [sub_neg_eq_add] at this
    rw [geo, this, neg_pow, hN, mul_zero, sub_zero]
  have h2 : (1 - Y) * geo N Y = 1 := by rw [geo, mul_neg_geom_sum, hN, sub_zero]
  calc (1 + -Y) * geo N (-Y) * ((1 + Y) * geo N Y) = (1 - Y) * (geo N (-Y) * (1 + Y)) * geo N Y := by
        rw [← sub_eq_add_neg]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, h2]

end CayInv

def mkUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.UJ ε :=
  ⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_comm_one (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]⟩, hg⟩

section RatEl

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev N0 (D : D7) : ℕ := 2 * D.R.rS + 2

theorem lvk_lt (k : Kap X) : lvk X k < N0 D := by show lvk X k < 2 * D.R.rS + 2; have := lvk_le X k; omega

theorem nil_of_pat {K : Type*} [CommRing K] {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) K}
    (hY : InPat (lvk X) k Y) (c : K) : (c • Y) ^ N0 D = 0 :=
  pow_eq_zero_of_inPat hk (lvk_lt X) (inPat_smul c hY)

def gE (Y : Matrix (Kap X) (Kap X) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  Bm X * cay (N0 D) Y * Bm' X

theorem gE_mul {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X (-Y) * gE X Y = 1 := by
  unfold gE
  have e : Bm X * cay (N0 D) (-Y) * Bm' X * (Bm X * cay (N0 D) Y * Bm' X) =
      Bm X * (cay (N0 D) (-Y) * ((Bm' X * Bm X) * cay (N0 D) Y)) * Bm' X := by simp only [Matrix.mul_assoc]
  rw [e, Bm'_mul_Bm, Matrix.one_mul, cay_neg_mul (nil_of_pat X hk hY _), Matrix.mul_one, Bm_mul_Bm']

theorem gE_mul' {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X Y * gE X (-Y) = 1 := by
  have := gE_mul X hk (inPat_neg hY)
  rwa [neg_neg] at this

theorem cT_eq {m p : Type} (M : Matrix m p X.B.I.E) : Formalism.UG.cT (starRingEnd X.B.I.E) M = Mᴴ := by
  ext i j
  simp only [Formalism.UG.cT, conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  rfl

theorem gE_unitary {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gE X Y)ᴴ * X.B.I.J * gE X Y = X.B.I.J := by
  have hc := cay_unitary hYs (nil_of_pat X hk hY (⅟2 : X.B.I.E))
  have hh : (Bm' X)ᴴ * (Bm X)ᴴ = 1 := by rw [← conjTranspose_mul, Bm_mul_Bm', conjTranspose_one]
  have hJB := JB_eq X
  unfold gE
  calc (Bm X * cay (N0 D) Y * Bm' X)ᴴ * X.B.I.J * (Bm X * cay (N0 D) Y * Bm' X)
      = (Bm' X)ᴴ * ((cay (N0 D) Y)ᴴ * ((Bm X)ᴴ * X.B.I.J * Bm X) * cay (N0 D) Y) * Bm' X := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bm' X)ᴴ * (Bm X)ᴴ * X.B.I.J * (Bm X * Bm' X) := by
        rw [← hJB, hc, hJB]; simp only [Matrix.mul_assoc]
    _ = X.B.I.J := by rw [hh, Bm_mul_Bm', Matrix.one_mul, Matrix.mul_one]

def gGL {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    GL (Fin X.B.I.n) X.B.I.E :=
  ⟨gE X Y, gE X (-Y), gE_mul' X hk hY, gE_mul X hk hY⟩

theorem gGL_mem {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gGL X hk hY ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  show Formalism.UG.cT (starRingEnd X.B.I.E) (gE X Y) * X.B.I.J * gE X Y = X.B.I.J
  rw [cT_eq]
  exact gE_unitary X hk hY hYs

theorem sig_eq : (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) = starRingEnd X.B.I.E := RingHom.ext fun _ => rfl

theorem gE_real (v : InfinitePlace X.B.I.F) (Y : Matrix (Kap X) (Kap X) X.B.I.E) :
    (X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v =
      Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v := by
  unfold gE Bv Bv'
  rw [Matrix.map_mul, Matrix.map_mul, cay_map]
  simp only [Matrix.mul_assoc]

theorem skew_map (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hYs : Yᴴ * JB X = -(JB X * Y)) :
    (Y.map (X.B.I.φ v))ᴴ * JBv X v = -(JBv X v * Y.map (X.B.I.φ v)) := by
  rw [JBv, map_conjTranspose, ← Matrix.map_mul, hYs, ← Matrix.map_mul, Matrix.map_neg]
  exact fun a => map_neg _ a

theorem inUJ_real {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Formalism.REAL.inUJ (X.B.I.ε v) ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) := by
  rw [gE_real]
  unfold Formalism.REAL.inUJ
  have hc := cay_unitary (skew_map X v hYs) (nil_of_pat X hk (inPat_map (X.B.I.φ v) hY) (⅟2 : ℂ))
  have hh : (Bv' X v)ᴴ * (Bv X v)ᴴ = 1 := by rw [← conjTranspose_mul, Bv_mul_Bv', conjTranspose_one]
  calc (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)
      = (Bv' X v)ᴴ * ((cay (N0 D) (Y.map (X.B.I.φ v)))ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) *
        cay (N0 D) (Y.map (X.B.I.φ v))) * Bv' X v := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bv' X v)ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * Bv' X v := by rw [Bv_gram, hc]
    _ = ((Bv' X v)ᴴ * (Bv X v)ᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * Bv' X v) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [hh, Bv_mul_Bv', Matrix.one_mul, Matrix.mul_one]

def gA {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : X.B.I.GA :=
  (fun v => mkUJ (X.B.I.ε v) _ (inUJ_real X hk v hY hYs),
    Formalism.L2.SG.ColsDim.ratHom X.B.I.cm.sig X.B.I.J (Af X.B.I.F)
      ⟨gGL X hk hY, by rw [sig_eq]; exact gGL_mem X hk hY hYs⟩)

theorem gA_GF {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gA X hk hY hYs ∈ X.B.I.GFset :=
  ⟨gGL X hk hY, gGL_mem X hk hY hYs, fun v => rfl, rfl⟩

theorem Mv_gA {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Mv X v (gA X hk hY hYs).1 = cay (N0 D) (Y.map (X.B.I.φ v)) := by
  unfold Mv
  show Bv' X v * ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) * Bv X v = _
  rw [gE_real]
  simp only [← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Bv'_mul_Bv, Matrix.mul_one]

theorem gA_ninf {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gA X hk hY hYs).1 ∈ X.NinfU u := by
  intro v
  apply inN_of_pat X u v
  have := Mv_gA X hk v hY hYs
  unfold Mv at this
  rw [this]
  exact inPat_mono hk (cay_sub_one _ (inPat_map (X.B.I.φ v) hY))

end RatEl
end SlabNDensePf
end Pf
end SG
end L2
end Formalism
end
end

section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB PIW.AdelClassFin

section Alg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K] [Invertible (2 : K)]
variable {J J' : Matrix ι ι K}

theorem sharp_mul' (h : J * J' = 1) (A B : Matrix ι ι K) : sharp J J' (A * B) = sharp J J' B * sharp J J' A := by
  unfold sharp
  rw [conjTranspose_mul]
  calc J' * (Bᴴ * Aᴴ) * J = J' * Bᴴ * (J * J') * Aᴴ * J := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem sharp_pow' (h : J * J' = 1) (h' : J' * J = 1) (A : Matrix ι ι K) (j : ℕ) :
    sharp J J' (A ^ j) = sharp J J' A ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, sharp_one h']
  | succ j ih => rw [pow_succ, sharp_mul' h, ih, pow_succ']

theorem sharp_geo (h : J * J' = 1) (h' : J' * J = 1) (A : Matrix ι ι K) (N : ℕ) :
    sharp J J' (geo N A) = geo N (sharp J J' A) := by
  unfold geo
  induction N with
  | zero => simp [sharp]
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, sharp_add, ih, sharp_pow' h h']

def icay (N : ℕ) (M : Matrix ι ι K) : Matrix ι ι K := (M - 1) * geo N (-((⅟2 : K) • (M - 1)))

theorem cay_icay {N : ℕ} {M : Matrix ι ι K} (hT : ((⅟2 : K) • (M - 1)) ^ N = 0)
    (hZ : ((⅟2 : K) • icay N M) ^ N = 0) : cay N (icay N M) = M := by
  set A : Matrix ι ι K := (⅟2 : K) • (M - 1) with hA
  set G := geo N (-A) with hG
  have hAN : (-A) ^ N = 0 := by rw [neg_pow, hT, mul_zero]
  have hAG : (1 + A) * G = 1 := by
    have := mul_neg_geom_sum (-A) N
    rw [sub_neg_eq_add, hAN, sub_zero] at this
    exact this
  have hZ2 : (⅟2 : K) • icay N M = A * G := by rw [icay, Matrix.smul_mul]
  have h1 : 1 - A * G = G := by
    have e : (1 + A) * G = G + A * G := by rw [Matrix.add_mul, Matrix.one_mul]
    rw [e] at hAG
    rw [← hAG]; abel
  have hgeo : (1 - (⅟2 : K) • icay N M) * geo N ((⅟2 : K) • icay N M) = 1 := by
    rw [geo, mul_neg_geom_sum, hZ, sub_zero]
  rw [hZ2, h1] at hgeo
  have hg : geo N ((⅟2 : K) • icay N M) = 1 + A := by
    calc geo N ((⅟2 : K) • icay N M) = (1 + A) * G * geo N ((⅟2 : K) • icay N M) := by rw [hAG, Matrix.one_mul]
      _ = 1 + A := by rw [Matrix.mul_assoc, hZ2, hgeo, Matrix.mul_one]
  have hGA : G * (1 + A) = 1 := by
    have := geom_sum_mul_neg (-A) N
    rw [sub_neg_eq_add, hAN, sub_zero] at this
    exact this
  unfold cay
  rw [hg, icay, ← hG, Matrix.mul_assoc, hGA, Matrix.mul_one]
  abel

theorem icay_skew (h : J * J' = 1) (h' : J' * J = 1) {N : ℕ} {M P : Matrix ι ι K} (hS : sharp J J' M = P)
    (hPM : P * M = 1) (hT : ((⅟2 : K) • (M - 1)) ^ N = 0) (hT' : ((⅟2 : K) • (P - 1)) ^ N = 0) :
    sharp J J' (icay N M) = -icay N M := by
  set A : Matrix ι ι K := (⅟2 : K) • (M - 1) with hA
  set B : Matrix ι ι K := (⅟2 : K) • (P - 1) with hB
  have hsA : sharp J J' A = B := by rw [hA, hB, sharp_smul, star_half, sharp_sub, hS, sharp_one h']
  have hAN : (-A) ^ N = 0 := by rw [neg_pow, hT, mul_zero]
  have hBN : (-B) ^ N = 0 := by rw [neg_pow, hT', mul_zero]
  have hAG : (1 + A) * geo N (-A) = 1 := by
    have := mul_neg_geom_sum (-A) N
    rw [sub_neg_eq_add, hAN, sub_zero] at this
    exact this
  have hGB : geo N (-B) * (1 + B) = 1 := by
    have := geom_sum_mul_neg (-B) N
    rw [sub_neg_eq_add, hBN, sub_zero] at this
    exact this
  have hQ : (P - 1) * (M - 1) = (1 + 1) - P - M := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPM]
    abel
  have hH : (⅟2 : K) • ((P - 1) * (M - 1)) + (⅟2 : K) • ((P - 1) * (M - 1)) = (1 + 1) - P - M := by
    rw [half_add_half', hQ]
  have key : (P - 1) * (1 + A) = -((1 + B) * (M - 1)) := by
    have e1 : (P - 1) * (1 + A) = (P - 1) + (⅟2 : K) • ((P - 1) * (M - 1)) := by
      rw [Matrix.mul_add, Matrix.mul_one, hA, Matrix.mul_smul]
    have e2 : (1 + B) * (M - 1) = (M - 1) + (⅟2 : K) • ((P - 1) * (M - 1)) := by
      rw [Matrix.add_mul, Matrix.one_mul, hB, Matrix.smul_mul]
    rw [e1, e2]
    refine eq_neg_of_add_eq_zero_left ?_
    calc (P - 1) + (⅟2 : K) • ((P - 1) * (M - 1)) + ((M - 1) + (⅟2 : K) • ((P - 1) * (M - 1)))
        = ((⅟2 : K) • ((P - 1) * (M - 1)) + (⅟2 : K) • ((P - 1) * (M - 1))) + (P - 1) + (M - 1) := by abel
      _ = 0 := by rw [hH]; abel
  have hs : sharp J J' (icay N M) = geo N (-B) * (P - 1) := by
    rw [icay, sharp_mul' h, sharp_geo h h', sharp_neg, hsA, sharp_sub, hS, sharp_one h']
  rw [hs]
  calc geo N (-B) * (P - 1) = geo N (-B) * ((P - 1) * (1 + A)) * geo N (-A) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hAG, Matrix.mul_one]
    _ = -(geo N (-B) * (1 + B) * ((M - 1) * geo N (-A))) := by
        rw [key]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -icay N M := by rw [hGB, Matrix.one_mul, icay]

end Alg

section Star

variable {D : D7} (X : HidaSetting D)

abbrev sA : RA X →+* RA X := Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)

theorem sA_invol (r : RA X) : sA X (sA X r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show Algebra.TensorProduct.map X.B.I.cm.sig (AlgHom.id X.B.I.F (Af X.B.I.F))
      (Algebra.TensorProduct.map X.B.I.cm.sig (AlgHom.id X.B.I.F (Af X.B.I.F)) (a ⊗ₜ[X.B.I.F] b)) =
        a ⊗ₜ[X.B.I.F] b
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    have e : X.B.I.cm.sig (X.B.I.cm.sig a) = a := star_star a
    rw [e]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

@[reducible] def starRA : StarRing (RA X) where
  star := sA X
  star_involutive := sA_invol X
  star_mul := fun a b => by rw [map_mul, mul_comm]
  star_add := fun a b => map_add _ a b

attribute [local instance] starRA

theorem star_ic (e : X.B.I.E) : star (ic X e) = ic X (star e) := DictLat.sigR_inclE X.B.I e

theorem map_cT {m p : Type*} (M : Matrix m p X.B.I.E) : (M.map (ic X))ᴴ = (Mᴴ).map (ic X) := by
  ext i j
  simp only [conjTranspose_apply, map_apply]
  exact star_ic X _

theorem cT_eqR {m p : Type} (M : Matrix m p (RA X)) :
    Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) M = Mᴴ := by
  ext i j
  rfl

abbrev JA : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (RA X) := X.B.I.J.map (ic X)
def JBf' : Matrix (Kap X) (Kap X) (RA X) := (JB' X).map (ic X)

theorem Bf_mul_Bf' : Bf X * Bf' X = 1 := by
  unfold Bf Bf'
  rw [← Matrix.map_mul, Bm_mul_Bm', Matrix.map_one _ (map_zero _) (map_one _)]

theorem Bf'_mul_Bf : Bf' X * Bf X = 1 := by
  unfold Bf Bf'
  rw [← Matrix.map_mul, Bm'_mul_Bm, Matrix.map_one _ (map_zero _) (map_one _)]

theorem JBf'_mul : JBf' X * JBf X = 1 := by
  unfold JBf JBf'
  rw [← Matrix.map_mul, JB'_mul_JB, Matrix.map_one _ (map_zero _) (map_one _)]

theorem JBf_mul : JBf X * JBf' X = 1 := by
  unfold JBf JBf'
  rw [← Matrix.map_mul, JB_mul_JB', Matrix.map_one _ (map_zero _) (map_one _)]

theorem JBf_graded : Graded (lvk X) (2 * D.R.rS + 2) (JBf X) := fun i j h =>
  JB_graded X i j fun h0 => h (by simp [JBf, h0])

theorem JBf'_graded : Graded (lvk X) (2 * D.R.rS + 2) (JBf' X) := fun i j h =>
  JB'_graded X i j fun h0 => h (by simp [JBf', h0])

theorem JBf_eq : JBf X = (Bf X)ᴴ * JA X * Bf X := by
  unfold JBf Bf
  rw [JB_eq, Matrix.map_mul, Matrix.map_mul, map_cT]

theorem fmat_unitary (x : X.B.I.Gf) : (X.B.I.fmat x)ᴴ * JA X * X.B.I.fmat x = JA X := by
  have hx : Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (X.B.I.fmat x) * JA X * X.B.I.fmat x = JA X :=
    x.2
  rwa [cT_eqR] at hx

theorem Mf_mul (x y : X.B.I.Gf) : Mf X (x * y) = Mf X x * Mf X y := by
  have e : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := rfl
  unfold Mf
  rw [e]
  calc Bf' X * (X.B.I.fmat x * X.B.I.fmat y) * Bf X
      = Bf' X * X.B.I.fmat x * (Bf X * Bf' X) * X.B.I.fmat y * Bf X := by
        rw [Bf_mul_Bf', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem Mf_one : Mf X 1 = 1 := by
  have e : X.B.I.fmat 1 = 1 := by simp [AutInst.fmat]
  unfold Mf
  rw [e, Matrix.mul_one, Bf'_mul_Bf]

theorem Mf_unitary (x : X.B.I.Gf) : (Mf X x)ᴴ * JBf X * Mf X x = JBf X := by
  have hh : (Bf' X)ᴴ * (Bf X)ᴴ = 1 := by rw [← conjTranspose_mul, Bf_mul_Bf', conjTranspose_one]
  have hu := fmat_unitary X x
  rw [JBf_eq]
  unfold Mf
  calc (Bf' X * X.B.I.fmat x * Bf X)ᴴ * ((Bf X)ᴴ * JA X * Bf X) * (Bf' X * X.B.I.fmat x * Bf X)
      = (Bf X)ᴴ * (X.B.I.fmat x)ᴴ * ((Bf' X)ᴴ * (Bf X)ᴴ) * JA X * (Bf X * Bf' X) * X.B.I.fmat x * Bf X := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bf X)ᴴ * ((X.B.I.fmat x)ᴴ * JA X * X.B.I.fmat x) * Bf X := by
        rw [hh, Bf_mul_Bf', Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

theorem Mf_inv (x : X.B.I.Gf) : Mf X x⁻¹ = sharp (JBf X) (JBf' X) (Mf X x) := by
  have h1 : Mf X x * Mf X x⁻¹ = 1 := by rw [← Mf_mul, mul_inv_cancel, Mf_one]
  have h2 := sharp_mul_self (JBf'_mul X) (Mf_unitary X x)
  calc Mf X x⁻¹ = (sharp (JBf X) (JBf' X) (Mf X x) * Mf X x) * Mf X x⁻¹ := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

end Star

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB PIW.AdelClassFin

attribute [local instance] starRA

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mulVec_cols' {m p : Type*} [Fintype p] [DecidableEq p] (M : Matrix m p (RA X)) (c : p → RA X) :
    M *ᵥ c = ∑ k, c k • (M *ᵥ Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (c k) : p → RA X) = c k • Pi.single k 1 by ext j; simp [Pi.single_apply],
    Matrix.mulVec_smul]

theorem Bf_col (k : Kap X) : Bf X *ᵥ Pi.single k 1 = incl X.B.I (bv X k) := by
  rw [mulVec_single_one]
  rfl

theorem Bf'_incl (k : Kap X) : Bf' X *ᵥ incl X.B.I (bv X k) = Pi.single k 1 := by
  rw [← Bf_col, Matrix.mulVec_mulVec, Bf'_mul_Bf, Matrix.one_mulVec]

theorem hA_sum' (x : VA X.B.I) (s : Finset (Kap X)) (c : Kap X → RA X) (v : Kap X → VA X.B.I) :
    hA X.B.I x (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k * hA X.B.I x (v k) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact DictLat.hhat_zero_right X.B.I x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rw [show hA X.B.I x (c a • v a + ∑ k ∈ s, c k • v k) =
        hA X.B.I x (c a • v a) + hA X.B.I x (∑ k ∈ s, c k • v k) from DictLat.hhat_add_right X.B.I _ _ _]
    rw [show hA X.B.I x (c a • v a) = c a * hA X.B.I x (v a) from DictLat.hhat_smul_right X.B.I _ _ _]

theorem hA_incl (v w : Fin X.B.I.n → X.B.I.E) :
    hA X.B.I (incl X.B.I v) (incl X.B.I w) = ic X (hE X v w) := DictLat.hhat_iv X.B.I v w

theorem hA_e_Bf (a : Fin D.R.rS) (c : Kap X → RA X) :
    hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ c) = c (Sum.inr (Sum.inr a)) := by
  rw [mulVec_cols', hA_sum']
  have e : ∀ k, hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ Pi.single k 1) = ic X (JB X (Sum.inl a) k) := by
    intro k
    rw [Bf_col]
    exact hA_incl X (X.eR a) (bv X k)
  simp only [e, JB_e_row]
  simp

theorem hA_e_w (a : Fin D.R.rS) (i : Fin (mW X)) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (bv X (Sum.inr (Sum.inl i)))) = 0 := by
  rw [hA_incl]
  have := (wb_mem X i a).1
  simp only [bv, Sum.elim_inr, Sum.elim_inl]
  rw [this, map_zero]

theorem adelicHermitian_hyperbolicE_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [hA_incl, hE_ez X u a, map_zero]

theorem Bf_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → RA X) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bf X *ᵥ c ∈ Submodule.span (RA X) ((fun b => incl X.B.I (X.eR b)) '' S) := by
  rw [mulVec_cols']
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    rw [Bf_col]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem Bf'_mulVec_supp (S : Set (Fin D.R.rS)) {y : VA X.B.I}
    (hy : y ∈ Submodule.span (RA X) ((fun b => incl X.B.I (X.eR b)) '' S)) :
    ∀ k, k ∉ Sum.inl '' S → (Bf' X *ᵥ y) k = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro k hk
    show (Bf' X *ᵥ incl X.B.I (bv X (Sum.inl b))) k = 0
    rw [Bf'_incl, Pi.single_apply, if_neg]
    rintro rfl
    exact hk ⟨b, hb, rfl⟩
  | zero => intro k _; simp
  | add x y _ _ hx hy => intro k hk; rw [Matrix.mulVec_add, Pi.add_apply, hx k hk, hy k hk, add_zero]
  | smul c x _ hx => intro k hk; rw [Matrix.mulVec_smul, Pi.smul_apply, hx k hk, smul_zero]

theorem nf_of_pat (x : X.B.I.Gf) (hpat : InPat (lvk X) 1 (Mf X x - 1)) : x ∈ X.NfinU u := by
  set M := Mf X x with hM
  have hg : X.B.I.fmat x - 1 = Bf X * (M - 1) * Bf' X := by
    rw [hM, Mf, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf_mul_Bf']
    simp only [← Matrix.mul_assoc, Bf_mul_Bf', Matrix.one_mul]
    rw [Matrix.mul_assoc, Bf_mul_Bf', Matrix.mul_one]
  have hgv : ∀ y, (X.B.I.fmat x - 1) *ᵥ y = Bf X *ᵥ ((M - 1) *ᵥ (Bf' X *ᵥ y)) := by
    intro y
    rw [hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hperp : ∀ y : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) y = 0) →
      (X.B.I.fmat x - 1) *ᵥ y ∈ Submodule.span (RA X) (Set.range fun b => incl X.B.I (X.eR b)) := by
    intro y hy
    set c := Bf' X *ᵥ y with hc
    have hyc : y = Bf X *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, Bf_mul_Bf', Matrix.one_mulVec]
    have hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0 := by
      intro a
      have := hA_e_Bf X a c
      rw [← hyc, hy a] at this
      exact this.symm
    rw [hgv, ← hc, ← Set.image_univ]
    refine Bf_mulVec_mem X Set.univ _ fun k hk => ?_
    have hk' : ∀ b, k ≠ Sum.inl b := by
      rintro b rfl
      exact hk ⟨b, Set.mem_univ _, rfl⟩
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hlk := lvk_notinl X k hk'
    rcases j with b | i | b
    · rw [hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
    · rw [hpat k _ (by rw [lvk_w]; omega), zero_mul]
    · rw [hcf b, mul_zero]
  show _ ∧ _ ∧ _
  refine ⟨fun a => ?_, hperp _ fun a => adelicHermitian_hyperbolicE_anisotropic_eq_zero X u a, hperp⟩
  rw [hgv]
  rw [show incl X.B.I (X.eR a) = incl X.B.I (bv X (Sum.inl a)) from rfl, Bf'_incl]
  refine Bf_mulVec_mem X {b | b.1 < a.1} _ fun k hk => ?_
  rw [mulVec_single_one]
  refine hpat k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem half_fin {y : X.B.I.Gf} (hy : y ∈ X.NfinU u) :
    ∀ i j, lvk X j ≤ D.R.rS + 1 → lvk X j < lvk X i + 1 → (Mf X y - 1) i j = 0 := by
  intro i j hj hij
  have hM : Mf X y - 1 = Bf' X * (X.B.I.fmat y - 1) * Bf X := by
    unfold Mf
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf'_mul_Bf]
  have hcol : (Mf X y - 1) i j = (Bf' X *ᵥ ((X.B.I.fmat y - 1) *ᵥ incl X.B.I (bv X j))) i := by
    rw [hM, ← Bf_col, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_single_one]
    rfl
  rw [hcol]
  rcases j with a | w | a
  · refine Bf'_mulVec_supp X {b | b.1 < a.1} (hy.1 a) i ?_
    rintro ⟨b, hb, rfl⟩
    simp only [lvk, Sum.elim_inl, Set.mem_setOf_eq] at hij hb
    omega
  · have h := hy.2.2 _ fun a => hA_e_w X a w
    rw [← Set.image_univ] at h
    refine Bf'_mulVec_supp X Set.univ h i ?_
    rintro ⟨b, -, rfl⟩
    simp only [lvk, Sum.elim_inl, Sum.elim_inr] at hij
    have := b.2
    omega
  · simp only [lvk, Sum.elim_inr] at hj
    have := a.2
    omega

theorem pat_of_nf {x : X.B.I.Gf} (hx : x ∈ X.NfinU u) : InPat (lvk X) 1 (Mf X x - 1) := by
  have hx' : x⁻¹ ∈ X.NfinU u := (Formalism.L2.SG.Pf.NfinSub X.eR (X.zR u)).inv_mem hx
  have hMN : Mf X x = sharp (JBf X) (JBf' X) (Mf X x⁻¹) := by
    have := Mf_inv X x⁻¹
    rwa [inv_inv] at this
  exact half_to_full (JBf_graded X) (JBf'_graded X) (JBf'_mul X) (h₀ := D.R.rS + 1) (by omega) hMN
    (half_fin X u hx') (half_fin X u hx)

theorem pattern_of_nilradical : NfPat := fun _ X u _ hx => pat_of_nf X u hx

theorem nilradical_of_pattern : NfOfPat := fun _ X u x h => nf_of_pat X u x h

theorem cay_inv_R (x : X.B.I.Gf) (hT : InPat (lvk X) 1 (Mf X x - 1)) :
    ∃ Z : Matrix (Kap X) (Kap X) (RA X), InPat (lvk X) 1 Z ∧
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) ∧
        cay (2 * D.R.rS + 2) Z = Mf X x := by
  set N := 2 * D.R.rS + 2 with hN
  have hZpat : InPat (lvk X) 1 (icay N (Mf X x)) :=
    inPat_mul hT (inPat_geo (inPat_neg (inPat_smul _ hT)) N)
  have hP : sharp (JBf X) (JBf' X) (Mf X x) = Mf X x⁻¹ := (Mf_inv X x).symm
  have hPM : Mf X x⁻¹ * Mf X x = 1 := by rw [← Mf_mul, inv_mul_cancel, Mf_one]
  have hT' : InPat (lvk X) 1 (Mf X x⁻¹ - 1) := by
    have e : Mf X x⁻¹ - 1 = sharp (JBf X) (JBf' X) (Mf X x - 1) := by
      rw [sharp_sub, hP, sharp_one (JBf'_mul X)]
    rw [e]
    exact inPat_sharp (JBf_graded X) (JBf'_graded X) hT
  have hs := icay_skew (JBf_mul X) (JBf'_mul X) hP hPM (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hT' _)
  refine ⟨icay N (Mf X x), hZpat, ?_, cay_icay (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hZpat _)⟩
  rw [cT_eqR]
  calc (icay N (Mf X x))ᴴ * JBf X = JBf X * sharp (JBf X) (JBf' X) (icay N (Mf X x)) := by
        unfold sharp
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, JBf_mul, Matrix.one_mul]
    _ = -(JBf X * icay N (Mf X x)) := by rw [hs, Matrix.mul_neg]

theorem cayley_inverse_right : CayInvR := fun _ X x h => cay_inv_R X x h

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section Gen

variable {R : Type*} [CommRing R] (O : Subring R)

def cg_C {α β : Type*} (c : ℕ) (A : Matrix α β R) : Prop := ∀ i j, ∃ t ∈ O, A i j = (c : R) * t

def cg_D {α β : Type*} (m : ℕ) (A : Matrix α β R) : Prop := ∀ i j, (m : R) * A i j ∈ O

variable {O} {α β γ : Type*}

theorem cg_C_zero (c : ℕ) : cg_C O c (0 : Matrix α β R) := fun _ _ => ⟨0, zero_mem _, by simp⟩

theorem cg_C_add {c : ℕ} {A B : Matrix α β R} (hA : cg_C O c A) (hB : cg_C O c B) : cg_C O c (A + B) := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  obtain ⟨t, ht, e2⟩ := hB i j
  exact ⟨s + t, add_mem hs ht, by rw [Matrix.add_apply, e1, e2, mul_add]⟩

theorem cg_C_neg {c : ℕ} {A : Matrix α β R} (hA : cg_C O c A) : cg_C O c (-A) := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  exact ⟨-s, neg_mem hs, by rw [Matrix.neg_apply, e1, mul_neg]⟩

theorem cg_C_sub {c : ℕ} {A B : Matrix α β R} (hA : cg_C O c A) (hB : cg_C O c B) : cg_C O c (A - B) := by
  rw [sub_eq_add_neg]; exact cg_C_add hA (cg_C_neg hB)

theorem cg_C_sum {ι : Type*} {s : Finset ι} {c : ℕ} {A : ι → Matrix α β R} (h : ∀ k ∈ s, cg_C O c (A k)) :
    cg_C O c (∑ k ∈ s, A k) :=
  Finset.sum_induction _ (cg_C O c) (fun _ _ => cg_C_add) (cg_C_zero c) h

theorem cg_C_dvd {c k : ℕ} {A : Matrix α β R} (hA : cg_C O (c * k) A) : cg_C O c A := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  exact ⟨k * s, mul_mem (natCast_mem _ _) hs, by rw [e1]; push_cast; ring⟩

theorem cg_D_of_C {m k : ℕ} {A A' : Matrix α β R} (hA : cg_D O m A) (h : cg_C O k (A' - A)) :
    cg_D O m A' := by
  intro i j
  obtain ⟨s, hs, e1⟩ := h i j
  have e2 : A' i j = A i j + k * s := by rw [← e1, Matrix.sub_apply]; ring
  rw [e2, mul_add, ← mul_assoc]
  exact add_mem (hA i j) (mul_mem (mul_mem (natCast_mem _ m) (natCast_mem _ k)) hs)

theorem cg_D_mul_right {m : ℕ} (k : ℕ) {A : Matrix α β R} (hA : cg_D O m A) : cg_D O (m * k) A := by
  intro i j
  rw [Nat.cast_mul, mul_comm (m : R), mul_assoc]
  exact mul_mem (natCast_mem _ _) (hA i j)

theorem cg_D_mul_left {m : ℕ} (k : ℕ) {A : Matrix α β R} (hA : cg_D O m A) : cg_D O (k * m) A := by
  intro i j
  rw [Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (hA i j)

theorem cg_C_mul_left [Fintype β] {m c : ℕ} {P : Matrix α β R} {A : Matrix β γ R} (hP : cg_D O m P)
    (hA : cg_C O (c * m) A) : cg_C O c (P * A) := by
  choose t ht e using hA
  intro i j
  refine ⟨∑ k, ((m : R) * P i k) * t k j, sum_mem fun k _ => mul_mem (hP i k) (ht k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e k j]; push_cast; ring

theorem cg_C_mul_right [Fintype β] {m c : ℕ} {A : Matrix α β R} {Q : Matrix β γ R}
    (hA : cg_C O (c * m) A) (hQ : cg_D O m Q) : cg_C O c (A * Q) := by
  choose t ht e using hA
  intro i j
  refine ⟨∑ k, t i k * ((m : R) * Q k j), sum_mem fun k _ => mul_mem (ht i k) (hQ k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e i k]; push_cast; ring

theorem cg_D_mul [Fintype β] {m k : ℕ} {P : Matrix α β R} {Q : Matrix β γ R} (hP : cg_D O m P)
    (hQ : cg_D O k Q) : cg_D O (m * k) (P * Q) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun l _ => ?_
  rw [show ((m * k : ℕ) : R) * (P i l * Q l j) = ((m : R) * P i l) * ((k : R) * Q l j) by push_cast; ring]
  exact mul_mem (hP i l) (hQ l j)

theorem cg_D_pow [Fintype α] [DecidableEq α] {m : ℕ} {A : Matrix α α R} (hA : cg_D O m A) :
    ∀ j : ℕ, cg_D O (m ^ j) (A ^ j) := by
  intro j
  induction j with
  | zero =>
    intro i k
    rw [pow_zero, pow_zero, Nat.cast_one, one_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact cg_D_mul ih hA

theorem cg_pow [Fintype α] [DecidableEq α] {m : ℕ} {A A' : Matrix α α R} (hA : cg_D O m A)
    (hA' : cg_D O m A') : ∀ (j c : ℕ), cg_C O (c * m ^ j) (A' - A) → cg_C O c (A' ^ j - A ^ j) := by
  intro j
  induction j with
  | zero => intro c _; simpa using cg_C_zero (O := O) (α := α) (β := α) c
  | succ j ih =>
    intro c h
    have e : A' ^ (j + 1) - A ^ (j + 1) = (A' ^ j - A ^ j) * A' + A ^ j * (A' - A) := by
      rw [pow_succ, pow_succ, Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e]
    refine cg_C_add (cg_C_mul_right (ih (c * m) ?_) hA') (cg_C_mul_left (cg_D_pow hA j) ?_)
    · rwa [show c * m * m ^ j = c * m ^ (j + 1) by ring]
    · exact cg_C_dvd (k := m) (by rwa [show c * m ^ j * m = c * m ^ (j + 1) by ring])

theorem cg_geo [Fintype α] [DecidableEq α] {m : ℕ} {A A' : Matrix α α R} (hA : cg_D O m A)
    (hA' : cg_D O m A') (N c : ℕ) (h : cg_C O (c * m ^ N) (A' - A)) : cg_C O c (geo N A' - geo N A) := by
  unfold geo
  rw [← Finset.sum_sub_distrib]
  refine cg_C_sum fun j hj => cg_pow hA hA' j c ?_
  have hj' : j ≤ N := (Finset.mem_range.1 hj).le
  refine cg_C_dvd (k := m ^ (N - j)) ?_
  rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj']

theorem cg_C_half [Invertible (2 : R)] {c : ℕ} {A : Matrix α β R} (h : cg_C O (2 * c) A) :
    cg_C O c ((⅟2 : R) • A) := by
  intro i j
  obtain ⟨t, ht, e⟩ := h i j
  refine ⟨t, ht, ?_⟩
  rw [Matrix.smul_apply, e, smul_eq_mul]
  push_cast
  linear_combination ((c : R) * t) * invOf_mul_self (2 : R)

theorem cg_D_half [Invertible (2 : R)] {m : ℕ} {A : Matrix α β R} (h : cg_D O m A) :
    cg_D O (2 * m) ((⅟2 : R) • A) := by
  intro i j
  have e : ((2 * m : ℕ) : R) * ((⅟2 : R) • A) i j = (m : R) * A i j := by
    rw [Matrix.smul_apply, smul_eq_mul]
    push_cast
    linear_combination ((m : R) * A i j) * invOf_mul_self (2 : R)
  rw [e]; exact h i j

theorem cg_cay [Fintype α] [DecidableEq α] [Invertible (2 : R)]
    (hden : ∀ A : Matrix α α R, ∃ m : ℕ, 1 ≤ m ∧ cg_D O m A) (N : ℕ) (Z : Matrix α α R) (c : ℕ)
    (hc : 1 ≤ c) :
    ∃ c' : ℕ, 1 ≤ c' ∧ ∀ Z' : Matrix α α R, cg_C O c' (Z' - Z) → cg_C O c (cay N Z' - cay N Z) := by
  obtain ⟨mZ, hmZ, hZ⟩ := hden Z
  obtain ⟨mG, hmG, hG⟩ := hden (geo N ((⅟2 : R) • Z))
  refine ⟨2 * (c * (mZ * mG) * (2 * mZ) ^ N), ?_, fun Z' h => ?_⟩
  · have h1 : 0 < (2 * mZ) ^ N := pow_pos (Nat.mul_pos two_pos hmZ) N
    exact Nat.mul_pos two_pos (Nat.mul_pos (Nat.mul_pos hc (Nat.mul_pos hmZ hmG)) h1)
  have hY : cg_D O (2 * mZ) ((⅟2 : R) • Z) := cg_D_half hZ
  have hYd : cg_C O (c * (mZ * mG) * (2 * mZ) ^ N) ((⅟2 : R) • Z' - (⅟2 : R) • Z) := by
    rw [← smul_sub]; exact cg_C_half h
  have hY' : cg_D O (2 * mZ) ((⅟2 : R) • Z') := cg_D_of_C hY hYd
  have hGd := cg_geo hY hY' N (c * (mZ * mG)) hYd
  have hZ0 : cg_D O (mZ * mG) Z := cg_D_mul_right mG hZ
  have hG0 : cg_D O (mZ * mG) (geo N ((⅟2 : R) • Z)) := cg_D_mul_left mZ hG
  have hG0' := cg_D_of_C hG0 hGd
  have e : cay N Z' - cay N Z = (Z' - Z) * geo N ((⅟2 : R) • Z') +
      Z * (geo N ((⅟2 : R) • Z') - geo N ((⅟2 : R) • Z)) := by
    unfold cay; simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e]
  refine cg_C_add (cg_C_mul_right ?_ hG0') (cg_C_mul_left hZ0 hGd)
  exact cg_C_dvd (k := 2 * (2 * mZ) ^ N)
    (by rwa [show c * (mZ * mG) * (2 * (2 * mZ) ^ N) = 2 * (c * (mZ * mG) * (2 * mZ) ^ N) by ring])

end Gen

section Adelic

theorem cg_D_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {α β : Type} [Fintype α] [Fintype β] (A : Matrix α β (E ⊗[F] Af F)) :
    ∃ m : ℕ, 1 ≤ m ∧ cg_D (IntAf F E) m A := by
  obtain ⟨m, hm, h⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.uniform_nat_mul (IntAf F E) (fun p : α × β => A p.1 p.2)
    (fun p => Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_IntAf _)
  exact ⟨m, hm, fun i j => h (i, j)⟩

end Adelic

theorem cayley_continuous : CayCont := by
  intro D X Z c hc
  exact cg_cay (O := IntAf X.B.I.F X.B.I.E) (fun A => cg_D_exists A) _ Z c hc

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section KgPart

theorem cg_Lf_step (I : AutInst) {d₁ d₂ g : ℕ}
    (H₁ : ∀ y ∈ I.Lf, ∀ i, (d₁ : I.E ⊗[I.F] Af I.F) * y i ∈ IntAf I.F I.E)
    (H₂ : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ i, y i ∈ IntAf I.F I.E) →
      (d₂ : I.E ⊗[I.F] Af I.F) • y ∈ I.Lf)
    {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : cg_C (IntAf I.F I.E) (g * d₁ * d₂) M)
    (y : Fin I.n → I.E ⊗[I.F] Af I.F) (hy : y ∈ I.Lf) :
    ∃ z ∈ I.Lf, M *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
  choose t ht e using hM
  refine ⟨(d₂ : I.E ⊗[I.F] Af I.F) • fun i => ∑ j, t i j * ((d₁ : I.E ⊗[I.F] Af I.F) * y j),
    H₂ _ fun i => sum_mem fun j _ => mul_mem (ht i j) (H₁ y hy j), ?_⟩
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e i j]; push_cast; ring

theorem cg_Kg (I : AutInst) (k : I.Gf) (g : ℕ)
    (hk : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat k - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z) : k ∈ I.Kg g := by
  have fwd : ∀ v ∈ I.Lf, I.fmat k *ᵥ v ∈ I.Lf := by
    intro v hv
    obtain ⟨z, hz, e⟩ := hk v hv
    have e2 : I.fmat k *ᵥ v = v + (I.fmat k - 1) *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e2, e, Nat.cast_smul_eq_nsmul]
    exact add_mem hv (nsmul_mem hz g)
  have inv : ∀ w ∈ I.Lf, I.fmat k⁻¹ *ᵥ w ∈ I.Lf := by
    intro w hw
    refine PIW.AdelClassFin.dual_hat_lattice I _ fun y' hy' => ?_
    have e : PIW.AdelClassFin.hhat I y' (I.fmat k⁻¹ *ᵥ w) = PIW.AdelClassFin.hhat I (I.fmat k *ᵥ y') w := by
      rw [← PIW.AdelClassFin.dictTop_hhat_unit I k y' (I.fmat k⁻¹ *ᵥ w), Matrix.mulVec_mulVec,
        PIW.AdelClassFin.dictTop_mul_inv, Matrix.one_mulVec]
    rw [e]
    exact PIW.AdelClassFin.dual_hat_integral I _ (fwd y' hy') w hw
  refine ⟨?_, hk⟩
  show ∀ v, v ∈ I.Lf ↔ I.fmat k *ᵥ v ∈ I.Lf
  intro v
  refine ⟨fwd v, fun h => ?_⟩
  have h2 := inv _ h
  rwa [Matrix.mulVec_mulVec, PIW.AdelClassFin.dictTop_inv_mul, Matrix.one_mulVec] at h2

variable {D : D7} (X : HidaSetting D)

theorem cg_BB : Bf X * Bf' X = 1 := by
  unfold Bf Bf'
  rw [← Matrix.map_mul, Bm_mul_Bm']
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cg_conj (y : X.B.I.Gf) : Bf X * Mf X y * Bf' X = X.B.I.fmat y := by
  simp only [Mf, ← Matrix.mul_assoc, cg_BB, Matrix.one_mul]
  rw [Matrix.mul_assoc, cg_BB, Matrix.mul_one]

theorem cg_fmat_eq (x y : X.B.I.Gf) :
    X.B.I.fmat (x⁻¹ * y) - 1 = X.B.I.fmat x⁻¹ * Bf X * (Mf X y - Mf X x) * Bf' X := by
  have key : Bf X * (Mf X y - Mf X x) * Bf' X = X.B.I.fmat y - X.B.I.fmat x := by
    rw [Matrix.mul_sub, Matrix.sub_mul, cg_conj, cg_conj]
  have h1 : X.B.I.fmat (x⁻¹ * y) = X.B.I.fmat x⁻¹ * X.B.I.fmat y := rfl
  have h2 : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
    rw [show X.B.I.fmat x⁻¹ * X.B.I.fmat x = X.B.I.fmat (x⁻¹ * x) from rfl, inv_mul_cancel]
    rfl
  rw [Matrix.mul_assoc (X.B.I.fmat x⁻¹) (Bf X), Matrix.mul_assoc (X.B.I.fmat x⁻¹), key, Matrix.mul_sub, h1, h2]

end KgPart

theorem level_of_close_element : KgOfClose := by
  intro D X x g hg
  obtain ⟨d₁, hd₁, H₁⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.Lf_upper X.B.I
  obtain ⟨d₂, hd₂, H₂⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.Lf_lower X.B.I
  obtain ⟨mP, hmP, hP⟩ := cg_D_exists (X.B.I.fmat x⁻¹ * Bf X)
  obtain ⟨mQ, hmQ, hQ⟩ := cg_D_exists (Bf' X)
  refine ⟨g * d₁ * d₂ * mQ * mP,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hg hd₁) hd₂) hmQ) hmP, fun y hy => ?_⟩
  have hΔ : cg_C (IntAf X.B.I.F X.B.I.E) (g * d₁ * d₂) (X.B.I.fmat (x⁻¹ * y) - 1) := by
    rw [cg_fmat_eq X x y]
    exact cg_C_mul_right (cg_C_mul_left hP hy) hQ
  exact cg_Kg X.B.I _ g fun y' hy' => cg_Lf_step X.B.I H₁ H₂ hΔ y' hy'

section Approx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cg_approx (k : ℕ) (hk : 1 ≤ k) (z : E ⊗[F] Af F) :
    ∃ a : E, ∃ t ∈ IntAf F E, Formalism.UG.inclE (F := F) (Af F) a - z = (k : E ⊗[F] Af F) * t := by
  obtain ⟨m, hm, hmz⟩ := PIW.AdelClassFin.dual_denominator F E z
  obtain ⟨a, r', hr', e⟩ := PIW.AdelClassFin.dual_dense F E (k * m) (Nat.mul_pos hk hm) _ hmz
  refine ⟨(a : E) / m, -r', neg_mem hr', ?_⟩
  have hm' : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have h2 : Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * (m : E ⊗[F] Af F) = 1 := by
    rw [← map_natCast (Formalism.UG.inclE (F := F) (Af F)) m, ← map_mul, div_mul_cancel₀ _ hm', map_one]
  have hz : z = Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * ((m : E ⊗[F] Af F) * z) := by
    rw [← mul_assoc, h2, one_mul]
  have ha : Formalism.UG.inclE (F := F) (Af F) ((a : E) / m) =
      Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * Formalism.UG.inclE (F := F) (Af F) (a : E) := by
    rw [← map_mul]; congr 1; ring
  rw [ha]
  rw [hz]
  rw [e]
  push_cast
  linear_combination (-(k : E ⊗[F] Af F) * r') * h2

theorem cg_approx_mat {ι : Type} [Fintype ι] (lv : ι → ℕ) (Z : Matrix ι ι (E ⊗[F] Af F))
    (hZ : InPat lv 1 Z) (k : ℕ) (hk : 1 ≤ k) :
    ∃ W : Matrix ι ι E, InPat lv 1 W ∧ cg_C (IntAf F E) k (W.map (Formalism.UG.inclE (F := F) (Af F)) - Z) := by
  choose a t ht e using fun i j => cg_approx (F := F) k hk (Z i j)
  refine ⟨Matrix.of fun i j => if lv j < lv i + 1 then 0 else a i j, fun i j h => ?_, fun i j => ?_⟩
  · simp only [Matrix.of_apply, if_pos h]
  · by_cases h : lv j < lv i + 1
    · refine ⟨0, zero_mem _, ?_⟩
      simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, if_pos h, map_zero, hZ i j h,
        sub_zero, mul_zero]
    · refine ⟨t i j, ht i j, ?_⟩
      simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, if_neg h]
      exact e i j

end Approx

section Skew

variable {D : D7} (X : HidaSetting D)

theorem cg_C_cT (I : AutInst) {α β : Type} {c : ℕ} {A : Matrix α β (I.E ⊗[I.F] Af I.F)}
    (h : cg_C (IntAf I.F I.E) c A) :
    cg_C (IntAf I.F I.E) c (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) A) := by
  have hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    show Formalism.UG.tensInt (F := I.F) (Af I.F) (Formalism.UG.intOE I.E) (Formalism.UG.intAd I.F) ≤ _
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := hx
      rw [SetLike.mem_coe, Subring.mem_comap]
      apply Subring.subset_closure
      left
      exact ⟨⟨algebraMap (𝓞 I.E) I.E (NumberField.RingOfIntegers.mapRingHom (I.cm.sig : I.E →+* I.E) z),
        ⟨_, rfl⟩⟩, rfl⟩
    · rw [SetLike.mem_coe, Subring.mem_comap]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, by simp [Formalism.UG.sigR]⟩
  intro i j
  obtain ⟨t, ht, hA⟩ := h j i
  refine ⟨Formalism.UG.sigR I.cm.sig (Af I.F) t, hle ht, ?_⟩
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hA, map_mul, map_natCast]

theorem cg_cT_sub (I : AutInst) {α β : Type} (A B : Matrix α β (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (A - B) =
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) A - Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) B := by
  ext i j
  simp [Formalism.UG.cT, map_sub]

theorem cg_map_cT {α β : Type} (M : Matrix α β X.B.I.E) :
    (Mᴴ).map (ic X) = Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (M.map (ic X)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT, Matrix.transpose_apply]
  rfl

theorem cg_half : ic X (⅟2 : X.B.I.E) = (⅟2 : RA X) := by
  refine (invOf_eq_right_inv ?_).symm
  rw [← map_ofNat (ic X) 2, ← map_mul, mul_invOf_self, map_one]

theorem cg_JJ : (JB' X).map (ic X) * JBf X = 1 := by
  unfold JBf
  rw [← Matrix.map_mul, JB'_mul_JB]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cg_proj_map (W : Matrix (Kap X) (Kap X) X.B.I.E) :
    (proj (JB X) (JB' X) W).map (ic X) = (⅟2 : RA X) • (W.map (ic X) - (JB' X).map (ic X) *
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X)) * JBf X) := by
  have e1 : (JB' X * Wᴴ * JB X).map (ic X) =
      (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X)) * JBf X := by
    rw [Matrix.map_mul, Matrix.map_mul, cg_map_cT]
    unfold JBf
    rfl
  ext i j
  have e2 := congrFun (congrFun e1 i) j
  simp only [Matrix.map_apply] at e2
  simp only [proj, sharp, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
    map_sub, cg_half, e2]

end Skew

theorem skew_hermitian_approximation : SkewApprox := by
  intro D X Z hZ hskew c hc
  obtain ⟨mJ, hmJ, hJ⟩ := cg_D_exists (JBf X)
  obtain ⟨mJ', hmJ', hJ'⟩ := cg_D_exists ((JB' X).map (ic X))
  obtain ⟨W, hW, hWZ⟩ := cg_approx_mat (lvk X) Z hZ (2 * c * mJ * mJ')
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos hc) hmJ) hmJ')
  refine ⟨proj (JB X) (JB' X) W, inPat_proj (JB_graded X) (JB'_graded X) hW,
    proj_skew (JB_herm X) (JB'_herm X) (JB'_mul_JB X) (JB_mul_JB' X) W, ?_⟩
  have hJZ : (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -Z := by
    rw [Matrix.mul_assoc, hskew, Matrix.mul_neg, ← Matrix.mul_assoc, cg_JJ, Matrix.one_mul]
  have habel : ∀ P Q S : Matrix (Kap X) (Kap X) (RA X), P - S - (Q - -S) = (P - Q) - (S + S) := by
    intro P Q S; abel
  have hhalf : (⅟2 : RA X) • (Z + Z) = Z := by
    rw [← two_smul (RA X) Z, smul_smul, invOf_mul_self, one_smul]
  have e : (proj (JB X) (JB' X) W).map (ic X) - Z = (⅟2 : RA X) • ((W.map (ic X) - Z) -
      (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X) - Z) * JBf X) := by
    rw [cg_proj_map, cg_cT_sub, Matrix.mul_sub, Matrix.sub_mul, hJZ, habel, smul_sub _ _ (Z + Z), hhalf]
  show cg_C (IntAf X.B.I.F X.B.I.E) c _
  rw [e]
  refine cg_C_half (cg_C_sub (cg_C_dvd (k := mJ) (cg_C_dvd (k := mJ') hWZ)) ?_)
  exact cg_C_mul_right (cg_C_mul_left hJ' (cg_C_cT X.B.I hWZ)) hJ

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

theorem mf_gA {D : D7} (X : HidaSetting D) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) 1 Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : Mf X (gA X le_rfl hY hYs).2 = cay (2 * D.R.rS + 2) (Y.map (ic X)) := by
  have hf : X.B.I.fmat (gA X le_rfl hY hYs).2 = (gE X Y).map (ic X) := rfl
  have h1 : (Bm' X).map (ic X) * (Bm X).map (ic X) = 1 := by
    rw [← Matrix.map_mul, Bm'_mul_Bm, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold Mf Bf Bf'
  rw [hf, gE, Matrix.map_mul, Matrix.map_mul, cay_map]
  simp only [← Matrix.mul_assoc]
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem nDense_of (h1 : NfPat) (h2 : NfOfPat) (h3 : CayInvR) (h4 : SkewApprox) (h5 : CayCont)
    (h6 : KgOfClose) : Formalism.L2.SG.Pf.SlabCoverPf.NDense := by
  intro D X u n hn U hU hnU
  obtain ⟨Z, hZ, hZs, hZc⟩ := h3 D X n (h1 D X u n hn)
  have hO : IsOpen {k : X.B.I.Gf | n * k ∈ U} := hU.preimage (continuous_mul_left n)
  have hN : {k : X.B.I.Gf | n * k ∈ U} ∈ nhds (1 : X.B.I.Gf) := hO.mem_nhds (by simpa using hnU)
  obtain ⟨g, hg, hgU⟩ := X.B.I.topf_basis _ hN
  obtain ⟨c, hc, hcK⟩ := h6 D X n g hg
  obtain ⟨c', hc', hcc⟩ := h5 D X Z c hc
  obtain ⟨Y, hY, hYs, hYc⟩ := h4 D X Z hZ hZs c' hc'
  refine ⟨gA X le_rfl hY hYs, (Formalism.MainNotions.LeviCoordinates.rr_mem_GF _ _).2 (gA_GF X le_rfl hY hYs),
    gA_ninf X u le_rfl hY hYs, ?_, ?_⟩
  · apply h2 D X u
    rw [mf_gA]
    exact cay_sub_one _ (inPat_map (ic X) hY)
  · have hK : n⁻¹ * (gA X le_rfl hY hYs).2 ∈ X.B.I.Kg g := hcK _ (by rw [mf_gA, ← hZc]; exact hcc _ hYc)
    have := hgU hK
    simpa using this

theorem nDense_of_two (h4 : SkewApprox) (h6 : KgOfClose) : Formalism.L2.SG.Pf.SlabCoverPf.NDense :=
  nDense_of pattern_of_nilradical nilradical_of_pattern cayley_inverse_right h4 cayley_continuous h6

theorem nilradical_strong_approximation : Formalism.L2.SG.Pf.SlabCoverPf.NDense :=
  nDense_of_two skew_hermitian_approximation level_of_close_element

end Formalism.L2.SG.Pf.SlabNDensePf
end
end
