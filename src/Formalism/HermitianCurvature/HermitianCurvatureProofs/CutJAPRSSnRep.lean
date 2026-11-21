import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRRest
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecomp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConstCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSIo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SsnRepOfOpen2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SRaiseSNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeConstructionHolds

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace WA

variable {k r : ℕ}

def Kl (Z : Q.Mx k r) : Prop :=
  ∀ a : Fin r, Z *ᵥ bvec (eI k r a) = 0 ∧ Z *ᵥ bvec (esI k r a) = 0 ∧
    Zᴴ *ᵥ bvec (eI k r a) = 0 ∧ Zᴴ *ᵥ bvec (esI k r a) = 0

theorem skew_ct {X : Q.Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) : Xᴴ = -(Hpk k r * X * Hpk k r) := by
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, Qx2.hpk_sq', Matrix.mul_one]
    _ = -(Hpk k r * X * Hpk k r) := by rw [h1, Matrix.neg_mul]

theorem kl_of_lev {X : Q.Mx k r} (hX : Q.inLieLev k r (Fin.last r) X) : Kl X := by
  intro a
  have ha : a.val < (Fin.last r).val := a.isLt
  obtain ⟨h1, h2⟩ := hX.2 a ha
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [skew_ct hX.1, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Qx8.hpk_e, ← Matrix.mulVec_mulVec, h2,
      Matrix.mulVec_zero, neg_zero]
  · rw [skew_ct hX.1, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Qx8.hpk_es, ← Matrix.mulVec_mulVec, h1,
      Matrix.mulVec_zero, neg_zero]

theorem kl_add {Z Z' : Q.Mx k r} (h : Kl Z) (h' : Kl Z') : Kl (Z + Z') := by
  intro a
  obtain ⟨a1, a2, a3, a4⟩ := h a
  obtain ⟨b1, b2, b3, b4⟩ := h' a
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.add_mulVec, Matrix.conjTranspose_add, a1, a2, a3, a4, b1, b2, b3, b4, add_zero]

theorem kl_smul {Z : Q.Mx k r} (c : ℂ) (h : Kl Z) : Kl (c • Z) := by
  intro a
  obtain ⟨a1, a2, a3, a4⟩ := h a
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.smul_mulVec, Matrix.conjTranspose_smul, a1, a2, a3, a4, smul_zero]

theorem kl_mul {Z Z' : Q.Mx k r} (h : Kl Z) (h' : Kl Z') : Kl (Z * Z') := by
  intro a
  obtain ⟨a1, a2, a3, a4⟩ := h a
  obtain ⟨b1, b2, b3, b4⟩ := h' a
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, b1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, b2, Matrix.mulVec_zero]
  · rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, a3, Matrix.mulVec_zero]
  · rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, a4, Matrix.mulVec_zero]

theorem kl_sub {Z Z' : Q.Mx k r} (h : Kl Z) (h' : Kl Z') : Kl (Z - Z') := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Z']
  exact kl_add h (kl_smul _ h')

theorem kl_zero : Kl (0 : Q.Mx k r) := by
  intro a; simp

theorem kl_sum {ι : Type*} (s : Finset ι) (Z : ι → Q.Mx k r) (h : ∀ i ∈ s, Kl (Z i)) : Kl (∑ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using kl_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact kl_add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem glc_of_kl {Z : Q.Mx k r} (h : Kl Z) : GLc k r Z := by
  have e1 : ∀ a : Fin r, ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) *ᵥ bvec (eI k r a) = 0 := fun a => by
    rw [← Matrix.mulVec_mulVec, Qx8.hpk_e, ← Matrix.mulVec_mulVec, (h a).2.2.2, Matrix.mulVec_zero]
  have e2 : ∀ a : Fin r, ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) *ᵥ bvec (esI k r a) = 0 := fun a => by
    rw [← Matrix.mulVec_mulVec, Qx8.hpk_es, ← Matrix.mulVec_mulVec, (h a).2.2.1, Matrix.mulVec_zero]
  refine ⟨⟨Qx2.hpart1_lie Z, fun a _ => ⟨?_, ?_⟩⟩, ⟨Qx2.hpart2_lie Z, fun a _ => ⟨?_, ?_⟩⟩⟩
  · unfold hpart1; rw [Matrix.smul_mulVec, Matrix.sub_mulVec, (h a).1, e1, sub_zero, smul_zero]
  · unfold hpart1; rw [Matrix.smul_mulVec, Matrix.sub_mulVec, (h a).2.1, e2, sub_zero, smul_zero]
  · unfold hpart2; rw [Matrix.smul_mulVec, Matrix.add_mulVec, (h a).1, e1, add_zero, smul_zero]
  · unfold hpart2; rw [Matrix.smul_mulVec, Matrix.add_mulVec, (h a).2.1, e2, add_zero, smul_zero]

theorem kl_of_glc {Z : Q.Mx k r} (h : GLc k r Z) : Kl Z := by
  rw [← Qx5.hpart_sum Z]
  exact kl_add (kl_of_lev h.1) (kl_smul _ (kl_of_lev h.2))

theorem glc_of_gwc {z : Fin (2 * r + k + 1) → ℂ} {Z : Q.Mx k r} (h : GWc k r z Z) : GLc k r Z :=
  ⟨h.1.1, h.2.1⟩

end WA

namespace WA

variable {k r : ℕ}

theorem idx_cases (p : Fin (2 * r + k + 1)) :
    (∃ j : Fin (k + 1), p = wI k r j) ∨ (∃ a : Fin r, p = eI k r a) ∨ (∃ a : Fin r, p = esI k r a) := by
  by_cases h1 : p.val < r
  · exact Or.inr (Or.inl ⟨⟨p.val, h1⟩, Fin.ext rfl⟩)
  · by_cases h2 : p.val ≤ r + k
    · exact Or.inl ⟨⟨p.val - r, by omega⟩, Fin.ext (by simp [wI]; omega)⟩
    · refine Or.inr (Or.inr ⟨⟨2 * r + k - p.val, by have := p.isLt; omega⟩, Fin.ext ?_⟩)
      simp [esI]; have := p.isLt; omega

theorem mulVec_bvec_apply (Z : Q.Mx k r) (p q : Fin (2 * r + k + 1)) : (Z *ᵥ bvec q) p = Z p q := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem kl_entry_col {Z : Q.Mx k r} (h : Kl Z) (p : Fin (2 * r + k + 1)) (a : Fin r) :
    Z p (eI k r a) = 0 ∧ Z p (esI k r a) = 0 := by
  constructor
  · have e := congrFun (h a).1 p
    rwa [mulVec_bvec_apply] at e
  · have e := congrFun (h a).2.1 p
    rwa [mulVec_bvec_apply] at e

theorem kl_entry_row {Z : Q.Mx k r} (h : Kl Z) (q : Fin (2 * r + k + 1)) (a : Fin r) :
    Z (eI k r a) q = 0 ∧ Z (esI k r a) q = 0 := by
  constructor
  · have e := congrFun (h a).2.2.1 q
    rw [mulVec_bvec_apply, Matrix.conjTranspose_apply] at e
    simpa using e
  · have e := congrFun (h a).2.2.2 q
    rw [mulVec_bvec_apply, Matrix.conjTranspose_apply] at e
    simpa using e

theorem wI_ne_eI (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ eI k r a := by
  intro h; have := congrArg Fin.val h; simp [wI, eI] at this; omega

theorem wI_ne_esI (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ esI k r a := by
  intro h; have := congrArg Fin.val h; simp [wI, esI] at this; have := a.isLt; have := j.isLt; omega

theorem kl_single (a b : Fin (k + 1)) : Kl (Matrix.single (wI k r a) (wI k r b) (1 : ℂ)) := by
  intro c
  have hb1 := wI_ne_eI (k := k) b c
  have hb2 := wI_ne_esI (k := k) b c
  have ha1 := wI_ne_eI (k := k) a c
  have ha2 := wI_ne_esI (k := k) a c
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext p <;>
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
      hb1, hb2, ha1, ha2, ]

theorem kl_decomp {Z : Q.Mx k r} (h : Kl Z) :
    Z = ∑ a : Fin (k + 1), ∑ b : Fin (k + 1), Z (wI k r a) (wI k r b) • Matrix.single (wI k r a) (wI k r b) (1 : ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rcases idx_cases (k := k) p with ⟨i, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases idx_cases (k := k) q with ⟨j, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have inj : ∀ x y : Fin (k + 1), wI k r x = wI k r y ↔ x = y := fun x y =>
        ⟨fun e => Fin.ext (by have := congrArg Fin.val e; simp [wI] at this; omega), fun e => e ▸ rfl⟩
      simp only [inj]
      rw [Finset.sum_eq_single i (fun x _ hx => by
        rw [Finset.sum_eq_zero]; intro y _; rw [if_neg]; rintro ⟨h1, _⟩; exact hx h1) (by simp)]
      rw [Finset.sum_eq_single j (fun y _ hy => by rw [if_neg]; rintro ⟨_, h2⟩; exact hy h2) (by simp)]
      simp
    · rw [(kl_entry_col h _ c).1]
      refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
      rw [if_neg]; rintro ⟨_, h2⟩; exact wI_ne_eI y c h2
    · rw [(kl_entry_col h _ c).2]
      refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
      rw [if_neg]; rintro ⟨_, h2⟩; exact wI_ne_esI y c h2
  · rw [(kl_entry_row h q a).1]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
    rw [if_neg]; rintro ⟨h1, _⟩; exact wI_ne_eI x a h1
  · rw [(kl_entry_row h q a).2]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
    rw [if_neg]; rintro ⟨h1, _⟩; exact wI_ne_esI x a h1

end WA

namespace WA

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rc_loc {D : Set (Q.Mx k r)} (hD : IsOpen D) {f f₂ : Q.Mx k r → E}
    (h : ∀ x ∈ Q.Glev k r (Fin.last r) ∩ D, f x = f₂ x) {g Z : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D)
    (hZ : GLc k r Z) : Rc Z f g = Rc Z f₂ g := by
  unfold Rc
  rw [Qx2.rd_loc hD h hg hZ.1, Qx2.rd_loc hD h hg hZ.2]

theorem rc_left (Z : Q.Mx k r) (f : Q.Mx k r → E) (h g : Q.Mx k r) :
    Rc Z (fun x => f (h * x)) g = Rc Z f (h * g) := by
  unfold Rc RdV
  simp only [Matrix.mul_assoc]

theorem rc_zeroZ (f : Q.Mx k r → E) (g : Q.Mx k r) : Rc (0 : Q.Mx k r) f g = 0 := by
  unfold Rc RdV hpart1 hpart2
  simp

theorem rc_zeroF (Z : Q.Mx k r) (g : Q.Mx k r) : Rc Z (fun _ => (0 : E)) g = 0 := by
  unfold Rc RdV
  simp

theorem smooth_fsum {D : Set (Q.Mx k r)} {ι : Type*} (s : Finset ι) (f : ι → Q.Mx k r → E)
    (h : ∀ i ∈ s, Q.SmoothLev k r (Fin.last r) D (f i)) :
    Q.SmoothLev k r (Fin.last r) D (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Qx2.smooth_zero (E := E) (k := k) (r := r) (i := Fin.last r) (D := D))
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact Qx2.smooth_add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem rc_fsum (hS : RcSmooth) {D : Set (Q.Mx k r)} (hD : IsOpen D) {ι : Type*} (s : Finset ι)
    (f : ι → Q.Mx k r → E) (h : ∀ i ∈ s, Q.SmoothLev k r (Fin.last r) D (f i)) {Z : Q.Mx k r} (hZ : GLc k r Z)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) :
    Rc Z (fun x => ∑ i ∈ s, f i x) g = ∑ i ∈ s, Rc Z (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rc_zeroF (E := E) Z g
  | insert j s hj ih =>
    have h1 := h j (Finset.mem_insert_self _ _)
    have h2 := smooth_fsum s f fun i hi => h i (Finset.mem_insert_of_mem hi)
    have e := (hS k r E D (f j) (fun x => ∑ i ∈ s, f i x) hD h1 h2 Z hZ).2.1 1 g hg
    simp only [one_smul] at e
    simp only [Finset.sum_insert hj]
    rw [e, ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem rc_add (hL : RcLin) {D : Set (Q.Mx k r)} (hD : IsOpen D) {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D)
    {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') : Rc (Z + Z') f g = Rc Z f g + Rc Z' f g := by
  have := hL k r E D f hD hf g hg 1 Z Z' hZ hZ'
  simpa using this

theorem rc_smul (hL : RcLin) {D : Set (Q.Mx k r)} (hD : IsOpen D) {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D)
    (a : ℂ) {Z : Q.Mx k r} (hZ : GLc k r Z) : Rc (a • Z) f g = a • Rc Z f g := by
  have := hL k r E D f hD hf g hg a Z 0 hZ (glc_of_kl kl_zero)
  rw [add_zero, rc_zeroZ, add_zero] at this
  exact this

theorem rc_lincomb (hL : RcLin) {D : Set (Q.Mx k r)} (hD : IsOpen D) {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Zs : ι → Q.Mx k r) (hZ : ∀ i ∈ s, GLc k r (Zs i)) :
    Rc (∑ i ∈ s, c i • Zs i) f g = ∑ i ∈ s, c i • Rc (Zs i) f g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rc_zeroZ f g
  | insert j s hj ih =>
    have hj' := hZ j (Finset.mem_insert_self _ _)
    have hs' : ∀ i ∈ s, GLc k r (Zs i) := fun i hi => hZ i (Finset.mem_insert_of_mem hi)
    have hsum : GLc k r (∑ i ∈ s, c i • Zs i) :=
      glc_of_kl (kl_sum _ _ fun i hi => kl_smul _ (kl_of_glc (hs' i hi)))
    rw [Finset.sum_insert hj, Finset.sum_insert hj, rc_add hL hD hf hg (glc_of_kl (kl_smul _ (kl_of_glc hj'))) hsum,
      rc_smul hL hD hf hg _ hj', ih hs']

end WA

namespace WA

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smooth_clm {D : Set (Q.Mx k r)} {f : Q.Mx k r → E} (hf : Q.SmoothLev k r (Fin.last r) D f)
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E') :
    Q.SmoothLev k r (Fin.last r) D (fun x => L (f x)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  exact ⟨U, fun x => L (F x), hU, hgU, (L.restrictScalars ℝ).contDiff.comp_contDiffOn hF,
    fun g hg hgl => by show L (f g) = L (F g); rw [he g hg hgl]⟩

theorem wordR_nil (f : Q.Mx k r → E) : wordR [] f = f := rfl

theorem wordR_cons (Z : Q.Mx k r) (w : List (Q.Mx k r)) (f : Q.Mx k r → E) :
    wordR (Z :: w) f = Rc Z (wordR w f) := rfl

theorem word_smooth (hS : RcSmooth) {D : Set (Q.Mx k r)} (hD : IsOpen D) {J : Q.Mx k r → E}
    (hJ : Q.SmoothLev k r (Fin.last r) D J) :
    ∀ w : List (Q.Mx k r), (∀ Z ∈ w, GLc k r Z) → Q.SmoothLev k r (Fin.last r) D (wordR w J) := by
  intro w
  induction w with
  | nil => intro _; exact hJ
  | cons Z w ih =>
    intro hw
    rw [wordR_cons]
    exact (hS k r E D _ _ hD (ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
      (ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) Z (hw Z List.mem_cons_self)).1

theorem glc_getD {w : List (Q.Mx k r)} (hw : ∀ Z ∈ w, GLc k r Z) (i : ℕ) : GLc k r (w.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact glc_of_kl kl_zero
  | some Y => exact hw Y (List.mem_of_getElem? h)

theorem glc_set {w : List (Q.Mx k r)} (hw : ∀ Z ∈ w, GLc k r Z) (i : ℕ) {X : Q.Mx k r} (hX : GLc k r X) :
    ∀ Z ∈ w.set i X, GLc k r Z := by
  intro Z hZ
  rcases List.mem_or_eq_of_mem_set hZ with h | h
  · exact hw Z h
  · exact h ▸ hX

theorem glc_comm {A B : Q.Mx k r} (hA : GLc k r A) (hB : GLc k r B) : GLc k r (A * B - B * A) :=
  glc_of_kl (kl_sub (kl_mul (kl_of_glc hA) (kl_of_glc hB)) (kl_mul (kl_of_glc hB) (kl_of_glc hA)))

section cov

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem word_left (hS : RcSmooth) {D : Set (Q.Mx k r)} (hD : IsOpen D) {U : Set (Q.Mx k r)}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (_hDl : ∀ h ∈ U, ∀ g ∈ D, h * g ∈ D) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJs : Q.SmoothLev k r (Fin.last r) D J)
    (hJl : ∀ h ∈ U, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, J (h * g) = (π h).comp (J g)) :
    ∀ w : List (Q.Mx k r), (∀ Z ∈ w, GLc k r Z) →
      ∀ h ∈ U, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, wordR w J (h * g) = (π h).comp (wordR w J g) := by
  intro w
  induction w with
  | nil => intro _; exact hJl
  | cons Z w ih =>
    intro hw h hh g hg
    have hw' : ∀ Y ∈ w, GLc k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hZ := hw Z List.mem_cons_self
    have hF := word_smooth hS hD hJs w hw'
    show Rc Z (wordR w J) (h * g) = (π h).comp (Rc Z (wordR w J) g)
    rw [← rc_left]
    rw [rc_loc hD (f₂ := fun x => (ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)) (wordR w J x))
      (fun x hx => ih hw' h hh x hx) hg hZ]
    exact (hS k r _ D _ _ hD hF hF Z hZ).2.2 _ (ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)) g hg

theorem word_comm (hS : RcSmooth) (hC : RcComm) {D : Set (Q.Mx k r)} (hD : IsOpen D)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJs : Q.SmoothLev k r (Fin.last r) D J) {A : Q.Mx k r} (hA : GLc k r A)
    (L₀ : Wq →L[ℂ] Wq) (hAJ : ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, Rc A J g = (J g).comp L₀) :
    ∀ w : List (Q.Mx k r), (∀ Z ∈ w, GLc k r Z) → ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
      Rc A (wordR w J) g = (wordR w J g).comp L₀ +
        ∑ i ∈ Finset.range w.length, wordR (w.set i (A * w.getD i 0 - w.getD i 0 * A)) J g := by
  intro w
  induction w with
  | nil => intro _ g hg; rw [wordR_nil]; simp [hAJ g hg]
  | cons Z w ih =>
    intro hw g hg
    have hw' : ∀ Y ∈ w, GLc k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hZ := hw Z List.mem_cons_self
    have hF := word_smooth hS hD hJs w hw'
    set M : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip L₀ with hM
    have hMap : ∀ X : Wq →L[ℂ] Wp, M X = X.comp L₀ := fun X => rfl
    have hsm : ∀ i ∈ Finset.range w.length,
        Q.SmoothLev k r (Fin.last r) D (wordR (w.set i (A * w.getD i 0 - w.getD i 0 * A)) J) :=
      fun i _ => word_smooth hS hD hJs _ (glc_set hw' i (glc_comm hA (glc_getD hw' i)))
    have hsum := smooth_fsum (Finset.range w.length)
      (fun i => wordR (w.set i (A * w.getD i 0 - w.getD i 0 * A)) J) hsm
    have hc := hC k r _ D _ hD hF A Z hA hZ g hg
    rw [wordR_cons, eq_add_of_sub_eq hc]
    rw [rc_loc hD (f₂ := fun x => (1 : ℂ) • M (wordR w J x) +
        ∑ i ∈ Finset.range w.length, wordR (w.set i (A * w.getD i 0 - w.getD i 0 * A)) J x)
      (fun x hx => by rw [one_smul, hMap]; exact ih hw' x hx) hg hZ]
    have e1 := (hS k r _ D _ _ hD (smooth_clm hF M) hsum Z hZ).2.1 1 g hg
    beta_reduce at e1
    have e2 := (hS k r _ D _ _ hD hF hF Z hZ).2.2 _ M g hg
    beta_reduce at e2
    rw [e1, one_smul, e2, hMap, rc_fsum hS hD _ _ hsm hZ hg]
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, wordR_cons]
    abel

end cov

end WA

namespace WA

section psv

variable {TT : ℝ}

theorem psv_congr {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : ℂ → V}
    (h : ∀ ζ, TT < Complex.normSq ζ → f ζ = g ζ) (hf : PSV TT f) : PSV TT g := by
  obtain ⟨n, a, v, ha, he⟩ := hf
  exact ⟨n, a, v, ha, fun ζ hζ => (h ζ hζ).symm.trans (he ζ hζ)⟩

variable (hPS : PSCalc) (hT : 0 < TT) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
include hPS hT

theorem psc_add {f g : ℂ → V} (hf : PSV TT f) (hg : PSV TT g) : PSV TT (fun ζ => f ζ + g ζ) :=
  ((hPS TT hT).2.2.2.2.2.2.2 V V).1 f g hf hg

theorem psc_smul {a : ℂ → ℂ} {f : ℂ → V} (ha : PS TT a) (hf : PSV TT f) : PSV TT (fun ζ => a ζ • f ζ) :=
  ((hPS TT hT).2.2.2.2.2.2.2 V V).2.1 a f ha hf

theorem psc_lin {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V'] (L : V →ₗ[ℂ] V') {f : ℂ → V}
    (hf : PSV TT f) : PSV TT (fun ζ => L (f ζ)) :=
  ((hPS TT hT).2.2.2.2.2.2.2 V V').2.2.1 L f hf

theorem psc_dz {f : ℂ → V} (hf : PSV TT f) : PSV TT (dZV f) :=
  (((hPS TT hT).2.2.2.2.2.2.2 V V).2.2.2.1 f hf).1

theorem psc_dzb {f : ℂ → V} (hf : PSV TT f) : PSV TT (dZbV f) :=
  (((hPS TT hT).2.2.2.2.2.2.2 V V).2.2.2.1 f hf).2

theorem psc_const (v : V) : PSV TT (fun _ => v) :=
  ((hPS TT hT).2.2.2.2.2.2.2 V V).2.2.2.2 v

theorem ps_const (c : ℂ) : PS TT (fun _ => c) := (hPS TT hT).1 c

theorem psc_fsum {ι : Type*} (s : Finset ι) (f : ι → ℂ → V) (h : ∀ i ∈ s, PSV TT (f i)) :
    PSV TT (fun ζ => ∑ i ∈ s, f i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact psv_congr (fun ζ _ => by simp) (psc_const hPS hT (0 : V))
  | insert j s hj ih =>
    refine psv_congr (fun ζ _ => by rw [Finset.sum_insert hj]) (psc_add hPS hT (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

end psv

theorem glc_lincomb {k r : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Zs : ι → Q.Mx k r)
    (h : ∀ i ∈ s, GLc k r (Zs i)) : GLc k r (∑ i ∈ s, c i • Zs i) :=
  glc_of_kl (kl_sum _ _ fun i hi => kl_smul _ (kl_of_glc (h i hi)))

theorem glc_add {k r : ℕ} {Z Z' : Q.Mx k r} (h : GLc k r Z) (h' : GLc k r Z') : GLc k r (Z + Z') :=
  glc_of_kl (kl_add (kl_of_glc h) (kl_of_glc h'))

theorem glc_smul {k r : ℕ} (c : ℂ) {Z : Q.Mx k r} (h : GLc k r Z) : GLc k r (c • Z) :=
  glc_of_kl (kl_smul c (kl_of_glc h))

end WA

open WA in
theorem word_polynomial_vector_holds : WordPSVOfCut := by
  intro hLin hS hC hLeft hRight hSec hDec hPS Wp Wq _ _ _ _ _ _ P Bs hpl hk hsec Φ X₀ hX₀ c hc
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hTpos : 0 < P.TT := hTT ▸ mul_pos Bs.T_pos Bs.T'_pos
  have hk1 : 1 ≤ P.k := by omega
  have hmu : ∀ ζ, NF.muZ P.k P.r Bs.μsec ζ = mu0 P.k P.r Bs.z Bs.z' ζ := fun ζ => by rw [hsec]; rfl
  have hDo : IsOpen (Dp P.k P.r Bs.z Bs.z') := Qx5.Dp_open _ _ _ _
  have hJs : Q.SmoothLev P.k P.r (Fin.last P.r) (Dp P.k P.r Bs.z Bs.z')
      ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) := Qx5.slice_smooth Φ.2 hc
  have hJl : ∀ h ∈ UWset P.k P.r Bs.z, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dp P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (h * g) = (Bs.π h).comp ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) := by
    intro h hh g hg
    have e := Φ.2.2.2 (c, g) ⟨hc, hg.1, hg.2⟩ h hh 1 (Qx8.uw_one Bs.z')
    rw [Matrix.mul_one, Bs.π'_rep.1] at e
    rw [e]; ext v; simp
  have hJr : ∀ h ∈ UWset P.k P.r Bs.z', ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dp P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (g * h) = ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g).comp (Bs.π' h) := by
    intro h hh g hg
    have e := Φ.2.2.2 (c, g) ⟨hc, hg.1, hg.2⟩ 1 (Qx8.uw_one Bs.z) h hh
    rw [Matrix.one_mul, Bs.π_rep.1] at e
    rw [e]; ext v; simp
  have hDl : ∀ h ∈ UWset P.k P.r Bs.z, ∀ g ∈ Dp P.k P.r Bs.z Bs.z', h * g ∈ Dp P.k P.r Bs.z Bs.z' := by
    intro h hh g hg
    have e := Qx5.GG_inv hh (Qx8.uw_one Bs.z') g
    rw [Matrix.mul_one] at e
    show 0 < Q.GGl P.k P.r Bs.z Bs.z' (h * g)
    rw [e]; exact hg
  have hDr : ∀ h ∈ UWset P.k P.r Bs.z', ∀ g ∈ Dp P.k P.r Bs.z Bs.z', g * h ∈ Dp P.k P.r Bs.z Bs.z' := by
    intro h hh g hg
    have e := Qx5.GG_inv (Qx8.uw_one Bs.z) hh g
    rw [Matrix.one_mul] at e
    show 0 < Q.GGl P.k P.r Bs.z Bs.z' (g * h)
    rw [e]; exact hg
  set J := (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c with hJ
  have hWs := word_smooth hS hDo hJs
  have hWl := word_left hS hDo hDl hJs hJl
  have main : ∀ n : ℕ, ∀ w : List (Q.Mx P.k P.r), w.length = n → (∀ Z ∈ w, GLc P.k P.r Z) →
      PSV P.TT (fun ζ => wordR w J (mu0 P.k P.r Bs.z Bs.z' ζ)) := by
    intro n
    induction n with
    | zero =>
      intro w hl _
      rw [List.length_eq_zero_iff.mp hl]
      refine psv_congr (fun ζ hζ => ?_) (psc_const hPS hTpos X₀)
      rw [wordR_nil, ← hmu]
      exact (hX₀ c hc ζ hζ).symm
    | succ n ih =>
      intro w hl hw
      obtain ⟨Z, w', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      have hl' : w'.length = n := by simpa using hl
      have hw' : ∀ Y ∈ w', GLc P.k P.r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
      have hZ := hw Z List.mem_cons_self
      have hF := hWs w' hw'
      have hFl := hWl w' hw'
      have hIH := ih w' hl' hw'
      have hunit : ∀ p : Fin (P.k + 1) × Fin (P.k + 1), PSV P.TT (fun ζ =>
          Rc (Matrix.single (wI P.k P.r p.1) (wI P.k P.r p.2) (1 : ℂ)) (wordR w' J) (mu0 P.k P.r Bs.z Bs.z' ζ)) := by
        intro p
        obtain ⟨n₁, n₂, B₁, b₁, B₂, b₂, β₁, β₂, hB₁, hB₂, hb₁, hb₂, hβ₁, hβ₂, hde⟩ :=
          hDec P.k P.r Bs.z Bs.z' hk1 Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos p.1 p.2
        rw [hTT] at hb₁ hb₂ hβ₁ hβ₂ hde
        have hT1 : ∀ t, PSV P.TT (fun ζ => (wordR w' J (mu0 P.k P.r Bs.z Bs.z' ζ)).comp (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π' (B₁ t)) +
            ∑ i ∈ Finset.range w'.length, wordR (w'.set i (B₁ t * w'.getD i 0 - w'.getD i 0 * B₁ t)) J
              (mu0 P.k P.r Bs.z Bs.z' ζ)) := by
          intro t
          refine psc_add hPS hTpos ?_ (psc_fsum hPS hTpos _ _ fun i _ =>
            ih _ (by simp [hl']) (glc_set hw' i (glc_comm (glc_of_gwc (hB₁ t)) (glc_getD hw' i))))
          exact psc_lin hPS hTpos ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π' (B₁ t))).toLinearMap hIH
        have hT2 : ∀ t, PSV P.TT (fun ζ => (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π (B₂ t)).comp (wordR w' J (mu0 P.k P.r Bs.z Bs.z' ζ))) :=
          fun t => psc_lin hPS hTpos (ContinuousLinearMap.compL ℂ Wq Wp Wp (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π (B₂ t))).toLinearMap hIH
        have hT3 := psc_dz hPS hTpos hIH
        have hT4 := psc_dzb hPS hTpos hIH
        refine psv_congr (fun ζ hζ => ?_) (psc_add hPS hTpos (psc_add hPS hTpos (psc_add hPS hTpos
          (psc_fsum hPS hTpos Finset.univ _ fun t _ => psc_smul hPS hTpos (hb₁ t) (hT1 t))
          (psc_fsum hPS hTpos Finset.univ _ fun t _ => psc_smul hPS hTpos (hb₂ t) (hT2 t)))
          (psc_smul hPS hTpos hβ₁ hT3)) (psc_smul hPS hTpos hβ₂ hT4))
        obtain ⟨hη, hηb, hμ, hSD⟩ := hSec P.k P.r Bs.z Bs.z' hk1 Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos ζ
          (hTT ▸ hζ)
        have hLB : ∀ t, GLc P.k P.r ((mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * B₂ t * mu0 P.k P.r Bs.z Bs.z' ζ) ∧
            Rc ((mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * B₂ t * mu0 P.k P.r Bs.z Bs.z' ζ) (wordR w' J) (mu0 P.k P.r Bs.z Bs.z' ζ) =
              (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π (B₂ t)).comp (wordR w' J (mu0 P.k P.r Bs.z Bs.z' ζ)) :=
          fun t => hLeft P.k P.r Bs.z Wp Wq Bs.π Bs.π_rep Bs.π_cont Bs.z_mem _ _ hDo hDl hF hFl _ hμ (B₂ t) (hB₂ t)
        have hmid : (mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * (∑ t, b₂ t ζ • B₂ t) * mu0 P.k P.r Bs.z Bs.z' ζ =
            ∑ t, b₂ t ζ • ((mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * B₂ t * mu0 P.k P.r Bs.z Bs.z' ζ) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Matrix.mul_smul, Matrix.smul_mul]
        have hG1 : GLc P.k P.r (∑ t, b₁ t ζ • B₁ t) := glc_lincomb _ _ _ fun t _ => glc_of_gwc (hB₁ t)
        have hG2 : GLc P.k P.r (∑ t, b₂ t ζ • ((mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * B₂ t * mu0 P.k P.r Bs.z Bs.z' ζ)) :=
          glc_lincomb _ _ _ fun t _ => (hLB t).1
        have hGη := glc_smul (β₁ ζ) hη
        have hGηb := glc_smul (β₂ ζ) hηb
        rw [hde ζ hζ, hmid, rc_add hLin hDo hF hμ (glc_add (glc_add hG1 hG2) hGη) hGηb,
          rc_add hLin hDo hF hμ (glc_add hG1 hG2) hGη, rc_add hLin hDo hF hμ hG1 hG2,
          rc_lincomb hLin hDo hF hμ _ _ _ fun t _ => glc_of_gwc (hB₁ t),
          rc_lincomb hLin hDo hF hμ _ _ _ fun t _ => (hLB t).1,
          rc_smul hLin hDo hF hμ _ hη, rc_smul hLin hDo hF hμ _ hηb,
          (hSD _ _ hF).1, (hSD _ _ hF).2]
        congr 1
        congr 1
        congr 1
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [word_comm hS hC hDo hJs (glc_of_gwc (hB₁ t)) (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π' (B₁ t))
            (fun g hg => (hRight P.k P.r Bs.z' Wp Wq Bs.π' Bs.π'_rep Bs.π'_cont Bs.z'_mem _ _ hDo hDr hJs hJr g hg
              (B₁ t) (hB₁ t)).2) w' hw' _ hμ]
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [(hLB t).2]
      have hZdec := kl_decomp (kl_of_glc hZ)
      rw [← Fintype.sum_prod_type' (f := fun a b => Z (wI P.k P.r a) (wI P.k P.r b) •
        Matrix.single (wI P.k P.r a) (wI P.k P.r b) (1 : ℂ))] at hZdec
      refine psv_congr (fun ζ hζ => ?_) (psc_fsum hPS hTpos Finset.univ _
        fun p _ => psc_smul hPS hTpos (ps_const hPS hTpos (Z (wI P.k P.r p.1) (wI P.k P.r p.2))) (hunit p))
      obtain ⟨-, -, hμ, -⟩ := hSec P.k P.r Bs.z Bs.z' hk1 Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos ζ (hTT ▸ hζ)
      rw [wordR_cons]
      conv_rhs => rw [hZdec]
      rw [rc_lincomb hLin hDo hF hμ _ _ _ fun p _ => glc_of_kl (kl_single p.1 p.2)]
  intro w hw
  exact psv_congr (fun ζ _ => by simp only [hmu]) (main _ w rfl hw)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem polynomial_radial_holds : PolyRadialS := polyRadialS_of CP.radial_decomposition_holds CP.word_polynomial_vector_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def fam (k r : ℕ) (e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ :=
  fun i => if h : r ≤ i.val ∧ i.val ≤ r + k then e ⟨i.val - r, by omega⟩ else bvec i

def ONb (k r : ℕ) (e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ a, inWb k r (e a)) ∧
    ∀ a b, herm (Hpk k r) (e a) (e b) = if a = b then (if a.val = k then -1 else 1) else 0

theorem hpk_out_in {i j : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    Hpk k r i j = 0 ∧ Hpk k r j i = 0 := by
  constructor <;> simp only [Hpk] <;> split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_bvec (i j : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec i) (bvec j) = Hpk k r j i := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]

theorem herm_bvec_w {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : herm (Hpk k r) (bvec i) w = 0 := by
  have hc : ∀ l, (Hpk k r *ᵥ bvec i) l = Hpk k r l i := fun l => by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [herm, dotProduct, hc]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
  · rw [(hpk_out_in hi hl).2, mul_zero]
  · rw [Pi.star_apply, hw l (by omega), star_zero, zero_mul]

theorem herm_w_bvec {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : herm (Hpk k r) w (bvec i) = 0 := by
  have hc : herm (Hpk k r) w (bvec i) = (Hpk k r *ᵥ w) i := by
    simp [herm, bvec, dotProduct, Pi.single_apply]
  rw [hc]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
  · rw [(hpk_out_in hi hl).1, zero_mul]
  · rw [hw l (by omega), mul_zero]

theorem fam_in {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} {i : Fin (2 * r + k + 1)} (h : r ≤ i.val ∧ i.val ≤ r + k) :
    fam k r e i = e ⟨i.val - r, by omega⟩ := by
  simp only [fam]
  rw [dif_pos h]

theorem fam_out {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) :
    fam k r e i = bvec i := by
  simp only [fam]
  rw [dif_neg]
  omega

theorem famGram {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} (he : ONb k r e) (i j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (fam k r e i) (fam k r e j) = Hpk k r j i := by
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k <;> by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · rw [fam_in hi, fam_in hj, he.2]
    simp only [Hpk]
    split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)
  · rw [fam_in hi, fam_out (i := j) (by omega), herm_w_bvec (i := j) (by omega) (he.1 _),
      (hpk_out_in (i := j) (j := i) (by omega) hi).1]
  · rw [fam_out (i := i) (by omega), fam_in hj, herm_bvec_w (i := i) (by omega) (he.1 _),
      (hpk_out_in (i := i) (j := j) (by omega) hj).2]
  · rw [fam_out (i := i) (by omega), fam_out (i := j) (by omega), herm_bvec_bvec]

theorem out_cases {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) :
    (∃ a : Fin r, i = eI k r a) ∨ (∃ a : Fin r, i = esI k r a) := by
  have := i.isLt
  rcases hi with hi | hi
  · left
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  · right
    refine ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext ?_⟩
    show i.val = 2 * r + k - (2 * r + k - i.val)
    omega

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def mk3 (k : ℕ) {n : ℕ} (v0 : Fin n → ℂ) (F : Fin (k - 1) → Fin n → ℂ) (zz : Fin n → ℂ) : Fin (k + 1) → Fin n → ℂ :=
  fun a => if h0 : a.val = 0 then v0 else if hk : a.val = k then zz else F ⟨a.val - 1, by have := a.isLt; omega⟩

theorem three_part_frame_zero {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h : a.val = 0) :
    mk3 k v0 F zz a = v0 := by
  unfold mk3; rw [dif_pos h]

theorem three_part_frame_last {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} (hk : 1 ≤ k) {a : Fin (k + 1)}
    (h : a.val = k) : mk3 k v0 F zz a = zz := by
  unfold mk3; rw [dif_neg (by omega), dif_pos h]

theorem three_part_frame_middle {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h0 : a.val ≠ 0)
    (hk : a.val ≠ k) : mk3 k v0 F zz a = F ⟨a.val - 1, by have := a.isLt; omega⟩ := by
  unfold mk3; rw [dif_neg h0, dif_neg hk]

theorem three_part_frame_orthonormal (hk : 2 ≤ k) {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hv0 : inWb k r v0) (hzz : inWb k r zz) (hF : ∀ j, inWb k r (F j))
    (h00 : herm (Hpk k r) v0 v0 = 1) (hzz1 : herm (Hpk k r) zz zz = -1) (h0z : herm (Hpk k r) v0 zz = 0)
    (hF0 : ∀ j, herm (Hpk k r) (F j) v0 = 0) (hFz : ∀ j, herm (Hpk k r) (F j) zz = 0)
    (hFF : ∀ i j, herm (Hpk k r) (F i) (F j) = if i = j then 1 else 0) : ONb k r (mk3 k v0 F zz) := by
  have hz0 : herm (Hpk k r) zz v0 = 0 := by rw [DU.hswap, h0z, map_zero]
  have h0F : ∀ j, herm (Hpk k r) v0 (F j) = 0 := fun j => by rw [DU.hswap, hF0 j, map_zero]
  have hzF : ∀ j, herm (Hpk k r) zz (F j) = 0 := fun j => by rw [DU.hswap, hFz j, map_zero]
  constructor
  · intro a
    by_cases h0 : a.val = 0
    · rw [three_part_frame_zero h0]; exact hv0
    · by_cases hl : a.val = k
      · rw [three_part_frame_last (by omega) hl]; exact hzz
      · rw [three_part_frame_middle h0 hl]; exact hF _
  · intro a b
    by_cases ha0 : a.val = 0
    · rw [three_part_frame_zero ha0]
      by_cases hb0 : b.val = 0
      · rw [three_part_frame_zero hb0, h00, if_pos (Fin.ext (by omega)), if_neg (by omega)]
      · rw [if_neg (fun h => hb0 (by rw [← h]; exact ha0))]
        by_cases hbl : b.val = k
        · rw [three_part_frame_last (by omega) hbl, h0z]
        · rw [three_part_frame_middle hb0 hbl, h0F]
    · by_cases hal : a.val = k
      · rw [three_part_frame_last (by omega) hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hz0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hzz1, if_pos (Fin.ext (by omega)), if_pos hal]
          · rw [three_part_frame_middle hb0 hbl, hzF, if_neg (fun h => hbl (by rw [← h]; exact hal))]
      · rw [three_part_frame_middle ha0 hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hF0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hFz, if_neg (fun h => hal (by rw [h]; exact hbl))]
          · rw [three_part_frame_middle hb0 hbl, hFF]
            by_cases hab : a = b
            · subst hab; rw [if_pos rfl, if_pos rfl, if_neg hal]
            · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
              rw [if_neg (fun h => hv (by have := congrArg Fin.val h; simp at this; omega)), if_neg hab]

section pt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem pt_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (SSn.nu0 k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) z = 0 ∧
    herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
    inWb k r (SSn.nu0' k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) z' = 0 ∧
    herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ := by
  obtain ⟨h1, h2, h3, h4⟩ := DU.base hz hz' hT hT' hsec hζ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hνW : inWb k r (SSn.nu0 k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνW' : inWb k r (SSn.nu0' k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz' hyi) _
  refine ⟨hνW, ?_, h2, h1, hνW', ?_, h4, h3⟩
  · rw [← h1]; exact DU.prWv_perp hT hνW
  · rw [← h3]; exact DU.prWv_perp hT' hνW'

theorem mu_frame (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    {m : ℕ} {Fr : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hFr : Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr) :
    (∀ j, inWb k r (NF.muZ k r μsec ζ *ᵥ Fr j)) ∧
    (∀ i j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr i) (NF.muZ k r μsec ζ *ᵥ Fr j) = if i = j then 1 else 0) ∧
    (∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) z = 0) ∧
    ∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) (SSn.nu0 k r z z' μsec ζ) = 0 := by
  obtain ⟨-, -, hνν, -, -, -, hν'ν', -⟩ := pt_facts hz hz' hT hT' hsec hζ
  set μ := NF.muZ k r μsec ζ with hμ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hU : μ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (μ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r (μ⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hFz' : ∀ j, herm (Hpk k r) (Fr j) z' = 0 := fun j => hFr.2.2 j z' (by simp)
  have hFν' : ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0 := fun j => hFr.2.2 j _ (by simp)

  have hz0 : ∀ j, herm (Hpk k r) (μ *ᵥ Fr j) z = 0 := by
    intro j
    rw [FrameEntries.herm_inv hU]
    set t : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) (SSn.prWv k r z' (μ⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ)
      with ht
    have hν' : SSn.nu0' k r z z' μsec ζ = t • SSn.prWv k r z' (μ⁻¹ *ᵥ z) := rfl
    have ht0 : t ≠ 0 := by
      intro h0
      rw [hν', h0, zero_smul] at hν'ν'
      simp [herm] at hν'ν'
    have h1 := hFν' j
    rw [hν', DU.hsmul_r] at h1
    have h2 : herm (Hpk k r) (Fr j) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) ht0
      · exact h
    rw [DU.prWv_of hyi, DU.hadd_r, DU.hsmul_r, hFz' j, mul_zero, add_zero] at h2
    exact h2
  refine ⟨fun j => Qx8.inWb_mulVec hG (hFr.1 j), fun i j => by rw [Qx2.herm_uh hU]; exact hFr.2.1 i j, hz0, ?_⟩
  intro j
  set s : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (μ *ᵥ z')) (SSn.prWv k r z (μ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ)
  have hν : SSn.nu0 k r z z' μsec ζ = s • SSn.prWv k r z (μ *ᵥ z') := rfl
  rw [hν, DU.hsmul_r, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hz0 j, Qx2.herm_uh hU, hFz' j]
  simp

theorem frame'_exists (hk : 2 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr := by
  obtain ⟨-, -, -, -, hW', hz'0, h11, -⟩ := pt_facts hz hz' hT hT' hsec hζ
  exact Topx1.typ_frame_exists k r (by omega) z' _ hz' hT' hW' hz'0 h11

end pt

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {n : ℕ}

def cols (x : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun p i => x i p

theorem cols_mulVec (x : Fin n → Fin n → ℂ) (c : Fin n → ℂ) : cols x *ᵥ c = ∑ i, c i • x i := by
  funext p
  simp [cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem cols_mulVec_single (x : Fin n → Fin n → ℂ) (i : Fin n) : cols x *ᵥ Pi.single i 1 = x i := by
  rw [cols_mulVec, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem mul_cols (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    A * cols x = cols (fun i => A *ᵥ x i) := by
  ext p i
  simp [cols, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_cols (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    (cols x)ᴴ * H * cols x = Matrix.of fun j i => herm H (x i) (x j) := by
  ext j i
  rw [Matrix.mul_assoc, mul_cols]
  simp [cols, Matrix.mul_apply, herm, dotProduct, Matrix.conjTranspose_apply]

theorem gram_eq {H : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → Fin n → ℂ}
    (hx : ∀ i j, herm H (x i) (x j) = H j i) : (cols x)ᴴ * H * cols x = H := by
  rw [gram_cols]
  ext j i
  exact hx i j

theorem cols_unit {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsUnit H.det) {x : Fin n → Fin n → ℂ}
    (hx : ∀ i j, herm H (x i) (x j) = H j i) : IsUnit (cols x).det := by
  have h := congrArg Matrix.det (gram_eq hx)
  rw [Matrix.det_mul] at h
  rw [← h] at hH
  exact isUnit_of_mul_isUnit_right hH

theorem wittGram (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (x y : Fin n → Fin n → ℂ)
    (hx : ∀ i j, herm H (x i) (x j) = H j i) (hy : ∀ i j, herm H (y i) (y j) = H j i) :
    ∃ g ∈ UH H, ∀ i, g *ᵥ x i = y i := by
  have hX := cols_unit hH hx
  have gx := gram_eq hx
  have gy := gram_eq hy
  have e1 : (cols x)⁻¹ * cols x = 1 := Matrix.nonsing_inv_mul _ hX
  have e2 : cols x * (cols x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hX
  refine ⟨cols y * (cols x)⁻¹, ?_, ?_⟩
  · show (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹) = H
    calc (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹)
        = ((cols x)⁻¹)ᴴ * ((cols y)ᴴ * H * cols y) * (cols x)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = ((cols x)⁻¹)ᴴ * ((cols x)ᴴ * H * cols x) * (cols x)⁻¹ := by rw [gy, gx]
      _ = (cols x * (cols x)⁻¹)ᴴ * H * (cols x * (cols x)⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [e2]; simp
  · intro i
    calc (cols y * (cols x)⁻¹) *ᵥ x i = (cols y * (cols x)⁻¹) *ᵥ (cols x *ᵥ Pi.single i 1) := by
          rw [cols_mulVec_single]
      _ = y i := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, e1, Matrix.mul_one, cols_mulVec_single]

theorem extGram (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (x : Fin n → Fin n → ℂ)
    (hx : ∀ i j, herm H (x i) (x j) = H j i) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i, A *ᵥ x i = B *ᵥ x i) : A = B := by
  have hX := cols_unit hH hx
  have e : A * cols x = B * cols x := by
    rw [mul_cols, mul_cols]
    congr 1
    funext i
    exact h i
  calc A = A * cols x * (cols x)⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
    _ = B := by rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

theorem frame_family_middle_index {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    {i : Fin (2 * r + k + 1)} (hi : i.val = r) : fam k r (mk3 k v0 F zz) i = v0 := by
  rw [fam_in (by omega), three_part_frame_zero (by show i.val - r = 0; omega)]

theorem frame_family_last_index {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ} (hk : 1 ≤ k)
    {i : Fin (2 * r + k + 1)} (hi : i.val = r + k) : fam k r (mk3 k v0 F zz) i = zz := by
  rw [fam_in (by omega), three_part_frame_last hk (by show i.val - r = k; omega)]

theorem frame_family_middle_range {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    {i : Fin (2 * r + k + 1)} (hi : r + 1 ≤ i.val ∧ i.val < r + k) :
    fam k r (mk3 k v0 F zz) i = F ⟨i.val - r - 1, by omega⟩ := by
  rw [fam_in (by omega), three_part_frame_middle (by show i.val - r ≠ 0; omega) (by show i.val - r ≠ k; omega)]

theorem blockProjection_basisVector_eq_zero {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) : SSn.wbP k r (bvec i) = 0 := by
  funext p
  unfold SSn.wbP bvec
  split_ifs with hp
  · rw [Pi.single_apply, if_neg (by rintro rfl; omega)]; rfl
  · rfl

theorem prWv_bvec_out (z' : Fin (2 * r + k + 1) → ℂ) {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) :
    SSn.prWv k r z' (bvec i) = 0 := by
  unfold SSn.prWv
  rw [blockProjection_basisVector_eq_zero hi]
  simp [herm]

theorem prWv_self {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    SSn.prWv k r z' z' = 0 := by
  rw [DU.prWv_of hz', FrameEntries.herm_self]
  have hT0 : ((Tz k r z' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  rw [neg_div, div_self hT0, neg_smul, one_smul, add_neg_cancel]

theorem herm_zero_l (w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 w = 0 := by simp [herm]

section pt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem io_fam (hk : 2 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ} (hFr : Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr) (c : ℂ)
    (i : Fin (2 * r + k + 1)) :
    SSn.io0 k r z z' μsec ζ *ᵥ fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ) Fr (c • z')) i =
      if h : r + 1 ≤ i.val ∧ i.val < r + k then NF.muZ k r μsec ζ *ᵥ Fr ⟨i.val - r - 1, by omega⟩ else 0 := by
  obtain ⟨-, -, -, -, -, -, h11, hfix⟩ := pt_facts hz hz' hT hT' hsec hζ
  rw [ioMulVec]
  by_cases hout : i.val < r ∨ r + k < i.val
  · rw [fam_out hout, prWv_bvec_out z' hout, herm_zero_l, zero_smul, sub_zero, Matrix.mulVec_zero,
      dif_neg (by omega)]
  · by_cases h0 : i.val = r
    · rw [frame_family_middle_index h0, hfix, h11, one_smul, sub_self, Matrix.mulVec_zero, dif_neg (by omega)]
    · by_cases hl : i.val = r + k
      · rw [frame_family_last_index (by omega) hl, TF.prWv_smul, prWv_self hz' hT', smul_zero, herm_zero_l, zero_smul, sub_zero,
          Matrix.mulVec_zero, dif_neg (by omega)]
      · have hm : r + 1 ≤ i.val ∧ i.val < r + k := by omega
        rw [frame_family_middle_range hm, dif_pos hm,
          DU.prWv_fix (hFr.1 _) (hFr.2.2 _ z' (by simp)), hFr.2.2 _ _ (by simp), zero_smul, sub_zero]

end pt

theorem hpk_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1

theorem cz_facts {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    inWb k r ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) ∧
    herm (Hpk k r) ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) = -1 ∧
    (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) ≠ 0 := by
  have hs : 0 < Real.sqrt (Tz k r z) := Real.sqrt_pos.2 hT
  refine ⟨Qx8.inWb_smul hz _, ?_, by exact_mod_cast (inv_pos.2 hs).ne'⟩
  rw [DU.hsmul_l, DU.hsmul_r, FrameEntries.herm_self, Complex.conj_ofReal]
  have hsq : Real.sqrt (Tz k r z) ^ 2 = Tz k r z := Real.sq_sqrt hT.le
  have hsq' : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ^ 2 = ((Tz k r z : ℝ) : ℂ) := by exact_mod_cast hsq
  have hne : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp
  rw [hsq']

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

noncomputable section

open DT in
theorem datum_transit_existence : DTExists := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  obtain ⟨Fr₁, hFr₁⟩ := frame'_exists hk hz hz' hT hT' hsec h₁
  obtain ⟨Fr₂, hFr₂⟩ := frame'_exists hk hz hz' hT hT' hsec h₂
  obtain ⟨hW₁, hνz₁, hνν₁, -, hW₁', hνz₁', hνν₁', -⟩ := pt_facts hz hz' hT hT' hsec h₁
  obtain ⟨hW₂, hνz₂, hνν₂, -, hW₂', hνz₂', hνν₂', -⟩ := pt_facts hz hz' hT hT' hsec h₂
  obtain ⟨mW₁, mO₁, mz₁, mν₁⟩ := mu_frame hz hz' hT hT' hsec h₁ hFr₁
  obtain ⟨mW₂, mO₂, mz₂, mν₂⟩ := mu_frame hz hz' hT hT' hsec h₂ hFr₂
  obtain ⟨czW, czz, cz0⟩ := cz_facts hz hT
  obtain ⟨czW', czz', cz0'⟩ := cz_facts hz' hT'
  set c := (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) with hc
  set c' := (((Real.sqrt (Tz k r z'))⁻¹ : ℝ) : ℂ) with hc'
  have hνc : ∀ ν, herm (Hpk k r) ν z = 0 → herm (Hpk k r) ν (c • z) = 0 := fun ν h => by
    rw [DU.hsmul_r, h, mul_zero]
  have hνc' : ∀ ν, herm (Hpk k r) ν z' = 0 → herm (Hpk k r) ν (c' • z') = 0 := fun ν h => by
    rw [DU.hsmul_r, h, mul_zero]
  have hFz' : ∀ {ζ : ℂ} {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ},
      Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr → ∀ j, herm (Hpk k r) (Fr j) z' = 0 :=
    fun hF j => hF.2.2 j z' (by simp)
  have hFν' : ∀ {ζ : ℂ} {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ},
      Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr → ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0 :=
    fun hF j => hF.2.2 j _ (by simp)

  have oX' := three_part_frame_orthonormal hk hW₁' czW' hFr₁.1 hνν₁' czz' (hνc' _ hνz₁') (hFν' hFr₁) (fun j => hνc' _ (hFz' hFr₁ j)) hFr₁.2.1
  have oY' := three_part_frame_orthonormal hk hW₂' czW' hFr₂.1 hνν₂' czz' (hνc' _ hνz₂') (hFν' hFr₂) (fun j => hνc' _ (hFz' hFr₂ j)) hFr₂.2.1
  have oX := three_part_frame_orthonormal hk hW₁ czW mW₁ hνν₁ czz (hνc _ hνz₁) mν₁ (fun j => hνc _ (mz₁ j)) mO₁
  have oY := three_part_frame_orthonormal hk hW₂ czW mW₂ hνν₂ czz (hνc _ hνz₂) mν₂ (fun j => hνc _ (mz₂ j)) mO₂
  set x' := fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ₁) Fr₁ (c' • z')) with hx'
  set y' := fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ₂) Fr₂ (c' • z')) with hy'
  set x := fam k r (mk3 k (SSn.nu0 k r z z' μsec ζ₁) (fun j => NF.muZ k r μsec ζ₁ *ᵥ Fr₁ j) (c • z)) with hx
  set y := fam k r (mk3 k (SSn.nu0 k r z z' μsec ζ₂) (fun j => NF.muZ k r μsec ζ₂ *ᵥ Fr₂ j) (c • z)) with hy
  obtain ⟨h', hh'U, hh'⟩ := wittGram _ (Hpk k r) hpk_det_unit x' y' (famGram oX') (famGram oY')
  obtain ⟨h, hhU, hh⟩ := wittGram _ (Hpk k r) hpk_det_unit x y (famGram oX) (famGram oY)
  have pr : r ≤ r ∧ r ≤ r + k := by omega
  let iR : Fin (2 * r + k + 1) := ⟨r, by omega⟩
  let iL : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩
  have fixOut : ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      (e e' : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ), (∀ i, g *ᵥ fam k r e i = fam k r e' i) →
      ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
    intro g e e' hg a
    have h1 := hg (eI k r a)
    have h2 := hg (esI k r a)
    rw [fam_out (by simp [eI]), fam_out (by simp [eI])] at h1
    rw [fam_out (by simp [esI]; omega), fam_out (by simp [esI]; omega)] at h2
    exact ⟨h1, h2⟩
  have fixZ : ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (w : Fin (2 * r + k + 1) → ℂ) (t : ℂ),
      t ≠ 0 → g *ᵥ (t • w) = t • w → g *ᵥ w = w := by
    intro g w t ht h
    rw [Matrix.mulVec_smul] at h
    exact smul_right_injective _ ht h
  have hhz : h *ᵥ z = z := by
    have := hh iL
    rw [hx, hy, frame_family_last_index (by omega) rfl, frame_family_last_index (by omega) rfl] at this
    exact fixZ h z c cz0 this
  have hh'z : h' *ᵥ z' = z' := by
    have := hh' iL
    rw [hx', hy', frame_family_last_index (by omega) rfl, frame_family_last_index (by omega) rfl] at this
    exact fixZ h' z' c' cz0' this
  have hmem : h ∈ UWset k r z := ⟨hhU, fixOut h _ _ hh, hhz⟩
  have hmem' : h' ∈ UWset k r z' := ⟨hh'U, fixOut h' _ _ hh', hh'z⟩
  refine ⟨h, hmem, h', hmem', ?_, ?_, ?_⟩
  · have := hh iR
    rw [hx, hy, frame_family_middle_index rfl, frame_family_middle_index rfl] at this
    exact this
  · have := hh' iR
    rw [hx', hy', frame_family_middle_index rfl, frame_family_middle_index rfl] at this
    exact this
  · have key : h * SSn.io0 k r z z' μsec ζ₁ = SSn.io0 k r z z' μsec ζ₂ * h' := by
      refine extGram _ (Hpk k r) hpk_det_unit x' (famGram oX') _ _ fun i => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh' i, hx', io_fam hk hz hz' hT hT' hsec h₁ hFr₁ c' i,
        hy', io_fam hk hz hz' hT hT' hsec h₂ hFr₂ c' i]
      by_cases hm : r + 1 ≤ i.val ∧ i.val < r + k
      · rw [dif_pos hm, dif_pos hm]
        have := hh i
        rw [hx, hy, frame_family_middle_range hm, frame_family_middle_range hm] at this
        exact this
      · rw [dif_neg hm, dif_neg hm, Matrix.mulVec_zero]
    rw [key, Matrix.mul_assoc, FrameEntries.mul_inv_uh hh'U, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

namespace DT

variable {k r : ℕ}

theorem eP_uw {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') {g : B.Mat k r} (hg : g ∈ UWset k r z')
    (ν v : Fin (2 * r + k + 1) → ℂ) : eP k r z' (g *ᵥ ν) (g *ᵥ v) = g *ᵥ eP k r z' ν v := by
  unfold eP
  rw [kap_prWv_mulVec hz' hg, Qx2.herm_uh hg.1, Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem decomp (z' ν v : Fin (2 * r + k + 1) → ℂ) :
    ∃ (o : Fin (2 * r + k + 1) → ℂ) (α β : ℂ), (∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → o i = 0) ∧
      v = eP k r z' ν v + o + α • z' + β • ν := by
  refine ⟨v - SSn.wbP k r v, -(herm (Hpk k r) (SSn.wbP k r v) z' / (Tz k r z' : ℂ)),
    herm (Hpk k r) (SSn.prWv k r z' v) ν, ?_, ?_⟩
  · intro i h1 h2
    simp [SSn.wbP, h1, h2]
  · have hP : SSn.prWv k r z' v =
        SSn.wbP k r v + (herm (Hpk k r) (SSn.wbP k r v) z' / (Tz k r z' : ℂ)) • z' := rfl
    unfold eP
    generalize herm (Hpk k r) (SSn.prWv k r z' v) ν = β
    rw [hP, neg_smul]
    abel

theorem fixOut {g : B.Mat k r}
    (hg : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    {o : Fin (2 * r + k + 1) → ℂ} (ho : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → o i = 0) :
    g *ᵥ o = o := by
  have hcol : ∀ j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) →
      g *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j hj
    rcases hj with hj | hj
    · have h1 := (hg ⟨j.val, hj⟩).1
      have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
      rw [e] at h1
      exact h1
    · have hlt : 2 * r + k - j.val < r := by omega
      have h1 := (hg ⟨2 * r + k - j.val, hlt⟩).2
      have e : esI k r ⟨2 * r + k - j.val, hlt⟩ = j := Fin.ext (by simp only [esI]; omega)
      rw [e] at h1
      exact h1
  have hent : ∀ i j : Fin (2 * r + k + 1), (g *ᵥ Pi.single j 1) i = g i j := by
    intro i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  funext i
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ j, g i j * o j = ∑ j, (if j = i then o i else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
        · rw [ho j hj.1 hj.2, mul_zero]
          split_ifs with hji
          · rw [← hji, ho j hj.1 hj.2]
          · rfl
        · rw [← hent i j, hcol j (by omega), Pi.single_apply]
          split_ifs with hij hji hji
          · rw [one_mul, hij]
          · exact absurd hij.symm hji
          · exact absurd hji.symm hij
          · rw [zero_mul]
    _ = o i := by simp

theorem core {z z' ν₁ ν₂ ν₁' ν₂' : Fin (2 * r + k + 1) → ℂ} {μ₁ μ₂ h h' a b : B.Mat k r}
    (hz' : inWb k r z') (hμ₁ : μ₁ ∈ Q.Glev k r (Fin.last r)) (hμ₂ : μ₂ ∈ Q.Glev k r (Fin.last r))
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z')
    (hab : a * μ₂ * b = μ₂) (e1 : h *ᵥ ν₁ = ν₂) (e2 : h' *ᵥ ν₁' = ν₂')
    (e3 : ∀ v, h *ᵥ (μ₁ *ᵥ eP k r z' ν₁' (h'⁻¹ *ᵥ v)) = μ₂ *ᵥ eP k r z' ν₂' v)
    {s₁ c₁ s₂ c₂ s₁' c₁' s₂' c₂' : ℂ} (hs₁ : s₁ ≠ 0)
    (f1 : ν₁ = s₁ • (μ₁ *ᵥ z' + c₁ • z)) (f2 : ν₂ = s₂ • (μ₂ *ᵥ z' + c₂ • z))
    (f1' : ν₁' = s₁' • (μ₁⁻¹ *ᵥ z + c₁' • z')) (f2' : ν₂' = s₂' • (μ₂⁻¹ *ᵥ z + c₂' • z')) :
    h⁻¹ * a * h * μ₁ * (h'⁻¹ * b * h') = μ₁ := by
  have hai : a⁻¹ * a = 1 := NFRadRedS.uw_inv_mul ha
  have hhi : h⁻¹ * h = 1 := NFRadRedS.uw_inv_mul hh
  have hh'i : h'⁻¹ * h' = 1 := NFRadRedS.uw_inv_mul hh'
  have hμ₂i : μ₂⁻¹ * μ₂ = 1 := FrameEntries.inv_mul_uh hμ₂.1
  have hμ₂m : μ₂ * μ₂⁻¹ = 1 := FrameEntries.mul_inv_uh hμ₂.1
  have hμ₁m : μ₁ * μ₁⁻¹ = 1 := FrameEntries.mul_inv_uh hμ₁.1
  have hi' : h'⁻¹ ∈ UWset k r z' := LieBracketMultiplication.uw_inv hh'
  have A0 : a *ᵥ (μ₂ *ᵥ z') = μ₂ *ᵥ z' := by
    have h1 : (a * μ₂ * b) *ᵥ z' = μ₂ *ᵥ z' := by rw [hab]
    rwa [← Matrix.mulVec_mulVec, hb.2.2, ← Matrix.mulVec_mulVec] at h1
  have A : a *ᵥ ν₂ = ν₂ := by
    rw [f2, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, A0, ha.2.2]
  have B0 : b *ᵥ (μ₂⁻¹ *ᵥ z) = μ₂⁻¹ *ᵥ z := by
    have h1 : b * μ₂⁻¹ = μ₂⁻¹ * a⁻¹ := by
      calc b * μ₂⁻¹ = μ₂⁻¹ * (a⁻¹ * a) * μ₂ * b * μ₂⁻¹ := by
            rw [hai, Matrix.mul_one, hμ₂i, Matrix.one_mul]
        _ = μ₂⁻¹ * a⁻¹ * (a * μ₂ * b) * μ₂⁻¹ := by simp only [Matrix.mul_assoc]
        _ = μ₂⁻¹ * a⁻¹ := by rw [hab, Matrix.mul_assoc, hμ₂m, Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, (LieBracketMultiplication.uw_inv ha).2.2]
  have B : b *ᵥ ν₂' = ν₂' := by
    rw [f2', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, B0, hb.2.2]
  have e2i : h'⁻¹ *ᵥ ν₂' = ν₁' := by
    rw [← e2, Matrix.mulVec_mulVec, hh'i, Matrix.one_mulVec]
  have C1 : ∀ v, h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ eP k r z' ν₂' v)) = μ₂ *ᵥ eP k r z' ν₂' v := by
    intro v
    rw [← eP_uw hz' hi', e2i]
    exact e3 v
  have Z0 : μ₁ *ᵥ z' = s₁⁻¹ • ν₁ - c₁ • z := by
    rw [f1, smul_smul, inv_mul_cancel₀ hs₁, one_smul, add_sub_cancel_right]
  have Z1 : h *ᵥ (μ₁ *ᵥ z') = s₁⁻¹ • ν₂ - c₁ • z := by
    rw [Z0, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, hh.2.2]
  have Z2 : a *ᵥ (h *ᵥ (μ₁ *ᵥ z')) = h *ᵥ (μ₁ *ᵥ z') := by
    rw [Z1, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, A, ha.2.2]
  have V0 : μ₁ *ᵥ ν₁' = s₁' • (z + c₁' • (μ₁ *ᵥ z')) := by
    rw [f1', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hμ₁m,
      Matrix.one_mulVec]
  have V1 : h *ᵥ (μ₁ *ᵥ ν₁') = s₁' • (z + c₁' • (h *ᵥ (μ₁ *ᵥ z'))) := by
    rw [V0, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hh.2.2]
  have V2 : a *ᵥ (h *ᵥ (μ₁ *ᵥ ν₁')) = h *ᵥ (μ₁ *ᵥ ν₁') := by
    rw [V1, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, ha.2.2, Z2]
  have key : ∀ v, a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ v)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ v)) := by
    intro v
    obtain ⟨o, α, β, ho, hv⟩ := decomp z' ν₂' v
    have E : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ eP k r z' ν₂' v)))) =
        h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ eP k r z' ν₂' v)) := by
      have h1 : b *ᵥ eP k r z' ν₂' v = eP k r z' ν₂' (b *ᵥ v) := by
        rw [← eP_uw hz' hb, B]
      rw [h1, C1, C1, ← h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hab]
    have O : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ o)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ o)) := by
      rw [fixOut hb.2.1 ho, fixOut hi'.2.1 ho, fixOut (fun c => hμ₁.2 c (by simp)) ho, fixOut hh.2.1 ho,
        fixOut ha.2.1 ho]
    have Zc : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ z')))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ z')) := by
      rw [hb.2.2, hi'.2.2, Z2]
    have Vc : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ ν₂')))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ ν₂')) := by
      rw [B, e2i, V2]
    generalize eP k r z' ν₂' v = u at hv E
    subst hv
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [E, O, Zc, Vc]
  have M : a * (h * μ₁ * h'⁻¹) * b = h * μ₁ * h'⁻¹ := by
    have h1 : ∀ v, (a * (h * μ₁ * h'⁻¹) * b) *ᵥ v = (h * μ₁ * h'⁻¹) *ᵥ v := by
      intro v
      simp only [← Matrix.mulVec_mulVec]
      exact key v
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact h1 v)
  calc h⁻¹ * a * h * μ₁ * (h'⁻¹ * b * h') = h⁻¹ * (a * (h * μ₁ * h'⁻¹) * b) * h' := by
        simp only [Matrix.mul_assoc]
    _ = h⁻¹ * (h * μ₁ * h'⁻¹) * h' := by rw [M]
    _ = (h⁻¹ * h) * μ₁ * (h'⁻¹ * h') := by simp only [Matrix.mul_assoc]
    _ = μ₁ := by rw [hhi, hh'i, Matrix.one_mul, Matrix.mul_one]

theorem herm_zero_zero : herm (Hpk k r) 0 0 = 0 := by
  simp [herm]

theorem first_vector_normal_form {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ s c : ℂ, s ≠ 0 ∧ SSn.nu0 k r z z' μsec ζ = s • (NF.muZ k r μsec ζ *ᵥ z' + c • z) := by
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hb := (DU.base hz hz' hT hT' hsec hζ).2.1
  have e : SSn.nu0 k r z z' μsec ζ =
      (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))
        (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ) • SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z') := rfl
  refine ⟨(((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))
        (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ),
    herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') z / (Tz k r z : ℂ), ?_, ?_⟩
  · intro h0
    rw [e, h0, zero_smul, herm_zero_zero] at hb
    exact zero_ne_one hb
  · rw [← DU.prWv_of hy]
    exact e

theorem nu0'_form {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ s c : ℂ, SSn.nu0' k r z z' μsec ζ = s • ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z + c • z') := by
  have hG := FrameEntries.glev_inv (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ))
  have hy : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hG hz
  refine ⟨(((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z))
        (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ),
    herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) z' / (Tz k r z' : ℂ), ?_⟩
  rw [← DU.prWv_of hy]
  rfl

end DT

theorem datum_transit_stabilizer : DTStab := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂ h hh h' hh' e1 e2 e3 p hp
  obtain ⟨ha, hb, hab⟩ := hp
  refine ⟨LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_inv hh) ha) hh, LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_inv hh') hb) hh', ?_⟩
  obtain ⟨s₁, c₁, hs₁, f1⟩ := DT.first_vector_normal_form hz hz' hT hT' hsec h₁
  obtain ⟨s₂, c₂, -, f2⟩ := DT.first_vector_normal_form hz hz' hT hT' hsec h₂
  obtain ⟨s₁', c₁', f1'⟩ := DT.nu0'_form (z' := z') hz hsec h₁
  obtain ⟨s₂', c₂', f2'⟩ := DT.nu0'_form (z' := z') hz hsec h₂
  have e3' : ∀ v, h *ᵥ (NF.muZ k r μsec ζ₁ *ᵥ DT.eP k r z' (SSn.nu0' k r z z' μsec ζ₁) (h'⁻¹ *ᵥ v)) =
      NF.muZ k r μsec ζ₂ *ᵥ DT.eP k r z' (SSn.nu0' k r z z' μsec ζ₂) v := by
    intro v
    have h3 : (h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹) *ᵥ v = SSn.io0 k r z z' μsec ζ₂ *ᵥ v := by rw [e3]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, DT.ioMulVec, DT.ioMulVec] at h3
    exact h3
  exact DT.core hz' (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec h₁)) (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec h₂))
    hh hh' ha hb hab e1 e2 e3' hs₁ f1 f2 f1' f2'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem datum_transitivity_holds : DatumTransit := datumTransit_of_cut datum_transit_existence datum_transit_stabilizer

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem modular_constancy_holds : ModConst :=
  modConst_of_cut line_nonvanishing_holds line_at_most_one_holds datum_transitivity_holds s_raise_section s_norm_section
    Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.theta_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem ssnRep_of_polyS (h : Core.TC.PolyRadialS) : SSnRep :=
  ssnRep_of_open2 rho_projection_existence Core.TC.MC.modular_constancy_holds Core.TC.line_nonvanishing_holds (Or.inr h)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_polyS (hJ : JfSmoothDS) (h : JA.SSn.Rep.Core.TC.PolyRadialS) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_SSnRep hJ (JA.SSn.Rep.ssnRep_of_polyS h)

end Formalism.FourierDecayAlt.P.CutMP
end

section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_jf (hJ : JfSmoothDS) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_polyS hJ JA.SSn.Rep.Core.TC.PR.polynomial_radial_holds

end Formalism.FourierDecayAlt.P.CutMP
end
