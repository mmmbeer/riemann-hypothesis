import Mathlib
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.SharpRestriction.Divisibility.JumpSets
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

namespace Formalism.MainNotions.WeightDegreeSizes

section PartG

open Formalism.BasicNotions Formalism.BasicNotions.DV

def IsTopAt (D : D7) (τ : D.what₂.Tau) (t : D.host.TT) : Prop :=
  (D.eTau τ : D.R.GG) = D.R.tau1 t

def NotTop (D : D7) (τ : D.what₂.Tau) : Prop := (D.eTau τ : D.R.GG) ∉ D.host.topPlaces

def TrueWeightDegreeBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u τ, (∀ t, IsTopAt D τ t →
      |((D.fm u).deg τ : ℝ) - (L.aT t : ℝ)| ≤ C * (L.sc.b' + L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.N D.R.m : ℝ))) ∧
    (NotTop D τ → |((D.fm u).deg τ : ℝ)| ≤ C * (L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.N D.R.m : ℝ)))

open Classical in

def D1 (D : D7) (L : SizeData₂ D) (τ : D.what₂.Tau) : ℝ :=
  L.Sc + (D.R.m : ℝ) * L.etaSz + if NotTop D τ then 0 else L.sc.b'

def OrthonormalFrameNormBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u τ, (D.fm u).beOn τ ^ 2 ≤
    Real.exp (C * ((D.R.N D.R.m : ℝ) * D1 D L τ + (D.R.N D.R.m : ℝ) ^ 2) * L.La)

def LogLevelPrimeBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ C * (D.R.m : ℝ) * L.sc.L

def OrthoNormProductBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ptB D u ≤ Real.exp (SZbP D L C u)

theorem OrthoNormProductBound.log {D : D7} {L : SizeData₂ D} {C : ℝ} (h : OrthoNormProductBound D L C) (u : D.what₂.Word)
    (h0 : 0 < Formalism.MainNotions.product_first_zeroth_parts.ptB D u) : Real.log (Formalism.MainNotions.product_first_zeroth_parts.ptB D u) ≤ SZbP D L C u :=
  (Real.log_le_iff_le_exp h0).2 (h u)

def OrthoNormBoundUniform : Prop :=
  ∀ C1 C2 C3 : ℝ, ∃ C : ℝ, ∀ (D : D7) (L : SizeData₂ D), L.sc.L ≤ L.La →
    TrueWeightDegreeBound D L C1 → OrthonormalFrameNormBound D L C2 → LogLevelPrimeBound D L C3 → OrthoNormProductBound D L C

section Proof

open Formalism.FrobeniusOrbits

theorem tau1_mem_Psi (φ : Formalism.HC.Frame) (t : φ.A) : φ.tau1 t ∈ φ.Psi := φ.tau1_mem_Psi t

theorem tau1_injective_alt (φ : Formalism.HC.Frame) : Function.Injective φ.tau1 := φ.tau1_injective

def tauOfTop (D : D7) (t : D.host.TT) : D.what₂.Tau := D.eTau.symm ⟨D.R.tau1 t, tau1_mem_Psi _ _⟩

theorem isTopAt_tauOfTop (D : D7) (t : D.host.TT) : IsTopAt D (tauOfTop D t) t := by
  unfold IsTopAt tauOfTop
  rw [Equiv.apply_symm_apply]

theorem not_notTop {D : D7} {τ : D.what₂.Tau} {t : D.host.TT} (h : IsTopAt D τ t) : ¬ NotTop D τ := by
  intro hn
  exact hn (by rw [h]; exact Finset.mem_image.mpr ⟨t, t.2, rfl⟩)

open Classical in

theorem sum_top (D : D7) (g : D.what₂.Tau → ℝ) :
    ∑ τ ∈ Finset.univ.filter (fun τ => ¬ NotTop D τ), g τ = ∑ t : D.host.TT, g (tauOfTop D t) := by
  symm
  refine Finset.sum_bij (fun (t : D.host.TT) _ => tauOfTop D t) ?_ ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_notTop (isTopAt_tauOfTop D t)
  · intro s _ t _ hst
    have := congrArg Subtype.val (D.eTau.symm.injective hst)
    exact Subtype.ext (tau1_injective_alt _ this)
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, NotTop, not_not] at hτ
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hτ
    refine ⟨⟨t, ht⟩, Finset.mem_univ _, ?_⟩
    apply D.eTau.injective
    unfold tauOfTop
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext he
  · intro t _
    rfl




end Proof

def familyOrthoNormBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, OrthoNormProductBound (Fm.D x i) (Fm.L x i) C

theorem L_le_La {D : D7} (L : SizeData₂ D) (h : Formalism.MainNotions.SizesAt L) : L.sc.L ≤ L.La := by
  obtain ⟨_, _, _, _, _, _, hQ, _⟩ := h
  obtain ⟨_, _, _, _, _, _, hr, _⟩ := hQ
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  unfold SizeData₂.La Scale.a Scale.b
  have hb : 0 < Real.exp L.sc.L := Real.exp_pos _
  have : Real.exp L.sc.L ≤ L.sc.x * Real.exp L.sc.L * D.host.rdE := by
    have h1 : Real.exp L.sc.L ≤ L.sc.x * Real.exp L.sc.L := by nlinarith
    have h2 : 0 ≤ L.sc.x * Real.exp L.sc.L := by positivity
    nlinarith
  calc L.sc.L = Real.log (Real.exp L.sc.L) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log hb this

theorem OrthoNormProductBound.mono {D : D7} {L : SizeData₂ D} {C C' : ℝ} (hLa : 0 ≤ L.La) (hC : C ≤ C') (h : OrthoNormProductBound D L C) :
    OrthoNormProductBound D L C' := by
  intro u
  refine (h u).trans (Real.exp_le_exp.2 ?_)
  unfold SZbP
  have hb' : 0 ≤ L.sc.b' := by
    have hx : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
    unfold Scale.b' Scale.a Scale.b Scale.X'; positivity
  have hS := L.Sc_pos.le
  have hE := L.etaSz_pos.le
  have : 0 ≤ ((D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * L.etaSz + L.Sc) * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC this) hLa
  linarith

def AdmSZPF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  (∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, TrueWeightDegreeBound (Fm.D x i) (Fm.L x i) C) ∧
  (∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, OrthonormalFrameNormBound (Fm.D x i) (Fm.L x i) C) ∧
  (∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LogLevelPrimeBound (Fm.D x i) (Fm.L x i) C)

def FamilyOrthoNormBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmSZPF Fm → familyOrthoNormBound Fm



end PartG

section PartA

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G NumberField IsDedekindDomain
open scoped BigOperators

variable {D : D7}

theorem gain_above {L : SizeData₂ D} (X : Inst D L) (K : Consts) (hF : ∀ w, ParametersFill X K w)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (w : D.what₂.places.Pl)
    (hX : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)) : L.gain j w = 0 := by
  by_cases hs : w ∈ L.supp
  · by_cases hin : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)
    · rw [(hF w).2.2.2.1 hs hin j hj]
      unfold gainP
      rw [if_pos (Or.inr hX)]
    · exact (L.not_inert w (fun h => hin (Or.inr h)) (fun h => hin (Or.inl h))).1 j
  · exact L.gain_supp j w hs

def ConclusionZ (D : D7) (L : SizeData₂ D) : Prop := L.ZeroAbove

def Ovr (D : D7) (p : ℕ) (S : Finset D.what₂.places.Pl) : Prop := ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p

theorem resChar_iff (D : D7) (l : ℕ) (hl : l.Prime) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = l ↔ (l : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  constructor
  · intro h; rw [← h]; exact resChar_mem D w
  · intro hmem
    by_contra hne
    have h1 := resChar_mem D w
    have hcop : Nat.Coprime (D.what₂.places.resChar w) l :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime w) hl).mpr hne
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (D.what₂.places.resChar w : ℤ) + b * (l : ℤ) = 1 := by
      refine ⟨Nat.gcdA (D.what₂.places.resChar w) l, Nat.gcdB (D.what₂.places.resChar w) l, ?_⟩
      have := Nat.gcd_eq_gcd_ab (D.what₂.places.resChar w) l
      rw [hcop] at this
      push_cast at this
      linarith
    have h1' : (1 : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
      have : ((a * (D.what₂.places.resChar w : ℤ) + b * (l : ℤ) : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
        push_cast
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hmem)
      rwa [hab, Int.cast_one] at this
    exact (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')

theorem exists_ovr (D : D7) (p : ℕ) (hp : p.Prime) : ∃ S, Ovr D p S := by
  classical
  obtain ⟨S, hS⟩ := finite_places_over (K := D.what₂.LL) p hp
  refine ⟨S.map D.plEq.symm.toEmbedding, fun w => ?_⟩
  rw [Finset.mem_map_equiv, Equiv.symm_symm, hS, resChar_iff D p hp]

theorem loss_bound_nonneg (L : SizeData₂ D) : 0 ≤ L.B0 := by
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  simp only [SizeData₂.B0, sizeBudget, bSize]
  have := Real.rpow_nonneg hx0.le L.sc.eps
  have := Real.exp_pos (L.sc.x ^ L.sc.eps)
  positivity

def sumA (L : SizeData₂ D) : ℝ := ∑ t : D.host.TT, (L.aT t : ℝ)

open Classical in

def C2atG (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ (i : Fin 2) u, ∀ j ∈ SizeData₂.lifts D,
    |(∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g i), SizeData₂.sz w (L.E u j w)) -
      sumA L * Real.log (D.host.g i : ℝ)| ≤ C * L.B0

def C2off (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D,
    ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes), |SizeData₂.sz w (L.E u j w)| ≤ C * L.B0

def IsotypicRank (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop := LocalQuadraticParts.adm11 D L C

theorem secondComplement_of_split (L : SizeData₂ D) (C1 C2 : ℝ) (h0 : 0 ≤ C1) (h1 : C2atG D L C1) (h2 : C2off D L C2) :
    IsotypicRank D L (2 * C1 + C2) := by
  classical
  intro u j hj
  have hB := loss_bound_nonneg L
  refine ⟨?_, (h2 u j hj).trans (by nlinarith)⟩
  have hg0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
  have hlog : Real.log (∏ g ∈ L.gTypes, (g : ℝ)) = Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) := by
    unfold SizeData₂.gTypes
    rw [Finset.prod_pair D.host.g_ne, Real.log_mul hg0.ne' hg1.ne']
  set f : D.what₂.places.Pl → ℝ := fun w => SizeData₂.sz w (L.E u j w) with hf
  have hsplit : ∑ w ∈ L.supp, f w =
      (∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g 0), f w) +
      (∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g 1), f w) +
      ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes), f w := by
    rw [← Finset.sum_filter_add_sum_filter_not L.supp (fun w => D.what₂.places.resChar w = D.host.g 0) f,
      ← Finset.sum_filter_add_sum_filter_not
        (L.supp.filter (fun w => ¬ D.what₂.places.resChar w = D.host.g 0))
        (fun w => D.what₂.places.resChar w = D.host.g 1) f, Finset.filter_filter, Finset.filter_filter, add_assoc]
    congr 2
    · refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun _ _ => rfl
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨fun h' => D.host.g_ne (h'.symm.trans h), h⟩
    · refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun _ _ => rfl
      simp [SizeData₂.gTypes]
  have a0 := h1 0 u j hj
  have a1 := h1 1 u j hj
  have a2 : |∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes), f w| ≤ C2 * L.B0 :=
    (Finset.abs_sum_le_sum_abs _ _).trans (h2 u j hj)
  rw [hlog, hsplit]
  rw [abs_le] at a0 a1 a2 ⊢
  unfold sumA at a0 a1
  constructor <;> nlinarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2]

theorem stmtZ {L : SizeData₂ D} (Gi : Inst D L) (K : Consts) (X : ErrX D) (c : ErrC)
    (hF : ∀ w, ParametersFill Gi K w) (hE : L.EDef X K c) : ConclusionZ D L :=
  fun u j hj w hX hT hg hd hG => ⟨gain_above Gi K hF j hj w hX, hE.zeroAbove u j hj w hX hT hg hd hG⟩

theorem zero_gain_above_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ConclusionZ (Fm.D x i) (Fm.L x i) :=
  fun x hx i => stmtZ (Fm.Gx x i) Fm.GK (Fm.ex x hx i).errX Fm.cX.err (Fm.fills x hx i) (Fm.ex x hx i).err.edef

def NormDecompositionCond (D : D7) (X : ErrX D) : Prop :=
  ∀ (i : Fin 2) u, ∀ j ∈ SizeData₂.lifts D, ∀ S : Finset D.what₂.places.Pl, Ovr D (D.host.g i) S →
    ∑ w ∈ S, SizeData₂.sz w (vNN X i u j w) = (∑ τ : D.what₂.Tau, nuAbs D u j τ) * Real.log (D.host.g i : ℝ)

def LevelPrimeNotTypePrime (D : D7) : Prop := ∀ u (i : Fin 2), D.host.g i ≠ (D.mem u).A.T

def errG (L : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  2 * (∑ τ : D.what₂.Tau, wj D j τ) +
    C * ((D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Nm D) +
      (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x)

def DegreeCountBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D,
    |(∑ τ : D.what₂.Tau, nuAbs D u j τ) - (fockDeg D j : ℝ) - sumA L| ≤ errG L C j

def TypePrimeSizeBound (D : D7) (L : SizeData₂ D) (c : ErrC) (Cd C : ℝ) : Prop :=
  ∀ (i : Fin 2) u, ∀ j ∈ SizeData₂.lifts D,
    (errG L Cd j + 2 * (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) +
      2 * (c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz))) *
        Real.log (D.host.g i : ℝ) ≤ C * L.B0

theorem Eval_atG (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (hT : LevelPrimeNotTypePrime D) (i : Fin 2) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = D.host.g i) :
    Eval L X K c u j w = (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) + EatG L X c i u j w := by
  unfold Eval
  simp only [hw, if_neg (hT u i)]
  fin_cases i
  · simp
  · have : D.host.g 1 ≠ D.host.g 0 := D.host.g_ne.symm
    simp [this]

theorem C2atG_of (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (Cd C : ℝ) (hc : c.Large)
    (hE : L.EDef X K c) (hT : LevelPrimeNotTypePrime D) (hN : NormDecompositionCond D X) (hD : DegreeCountBound D L Cd) (hS : TypePrimeSizeBound D L c Cd C) :
    C2atG D L C := by
  classical
  intro i u j hj
  obtain ⟨S, hSo⟩ := exists_ovr D (D.host.g i) (D.host.g_prime i)
  obtain ⟨er, her⟩ : ∃ er : ℝ, er = c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) := ⟨_, rfl⟩
  obtain ⟨vd, hvd⟩ : ∃ vd : ℝ, vd = (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) := ⟨_, rfl⟩
  have her0 : 0 ≤ er := by
    rw [her]
    have h1 : 0 ≤ c.g := le_trans (by norm_num) hc.2.2
    have h2 := L.etaSz_pos.le
    have h3 : 0 ≤ Nm D := by unfold Nm; positivity
    positivity
  have hvd0 : 0 ≤ vd := by rw [hvd]; positivity
  have h1 : ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g i), SizeData₂.sz w (L.E u j w) =
      ∑ w ∈ S, SizeData₂.sz w (L.E u j w) := by
    refine Finset.sum_subset (fun w hw => (hSo w).2 (Finset.mem_filter.1 hw).2) fun w hw hn => ?_
    have : w ∉ L.supp := fun h => hn (Finset.mem_filter.2 ⟨h, (hSo w).1 hw⟩)
    rw [L.E_supp u j w this]
    simp [SizeData₂.sz]
  have h2 : ∀ w ∈ S, SizeData₂.sz w (L.E u j w) =
      2 * (vd + FTypeG D j + er) * (lw D.what₂.LL (D.plEq w) * (D.what₂.places.ramIdx w : ℝ)) +
        SizeData₂.sz w (vNN X i u j w) := by
    intro w hw
    rw [hE u j hj w, Eval_atG L X K c hT i u j w ((hSo w).1 hw)]
    unfold EatG SizeData₂.sz SizeData₂.lwP
    rw [← her, ← hvd]
    ring
  have hlg : 0 ≤ Real.log (D.host.g i : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (D.host.g_prime i).one_lt.le)
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.mul_sum,
    factEtaMean D (D.host.g i) (D.host.g_prime i) S hSo, hN i u j hj S hSo]
  have hd := hD u j hj
  have hs := hS i u j hj
  rw [← her, ← hvd] at hs
  have e1 : 2 * (vd + FTypeG D j + er) * Real.log (D.host.g i : ℝ) +
      (∑ τ : D.what₂.Tau, nuAbs D u j τ) * Real.log (D.host.g i : ℝ) - sumA L * Real.log (D.host.g i : ℝ) =
      (((∑ τ : D.what₂.Tau, nuAbs D u j τ) - (fockDeg D j : ℝ) - sumA L) + (2 * vd + 2 * er)) *
        Real.log (D.host.g i : ℝ) := by
    unfold FTypeG; ring
  rw [e1, abs_mul, abs_of_nonneg hlg]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hlg) hs
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * vd + 2 * er)]
  linarith

theorem logWeight_nonneg (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  unfold SizeData₂.lwP lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem sum_by_prime (S : Finset D.what₂.places.Pl) (h : ℕ → ℝ) (h0 : ∀ p, 0 ≤ h p) :
    ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * h (D.what₂.places.resChar w) ≤
      ∑ p ∈ S.image D.what₂.places.resChar, Real.log (p : ℝ) * h p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := D.what₂.places.resChar) (t := S.image D.what₂.places.resChar)
    (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨w0, _, hw0⟩ := Finset.mem_image.1 hp
  have hpp : p.Prime := hw0 ▸ D.what₂.places.resChar_prime w0
  obtain ⟨Sp, hSp⟩ := exists_ovr D p hpp
  have e1 : ∑ w ∈ S.filter (fun w => D.what₂.places.resChar w = p),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * h (D.what₂.places.resChar w) =
      (∑ w ∈ S.filter (fun w => D.what₂.places.resChar w = p), SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * h p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [(Finset.mem_filter.1 hw).2]
  rw [e1]
  refine mul_le_mul_of_nonneg_right ?_ (h0 p)
  rw [← factEtaMean D p hpp Sp hSp]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hSp w).2 (Finset.mem_filter.1 hw).2)
    fun w _ _ => mul_nonneg (logWeight_nonneg w) (Nat.cast_nonneg _)

theorem sum_val_log_le (n : ℕ) (hn : 0 < n) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, Real.log (p : ℝ) * (padicValNat p n : ℝ) ≤ Real.log (n : ℝ) := by
  classical
  have h1 : (∏ p ∈ P, p ^ padicValNat p n) ∣ n := by
    induction P using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ pow_padicValNat_dvd
        (ih fun p hp => hP p (Finset.mem_insert_of_mem hp))
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP a (Finset.mem_insert_self _ _))
        (hP q (Finset.mem_insert_of_mem hq))).2 (fun h => ha (h ▸ hq)))
  have h2 : (∏ p ∈ P, p ^ padicValNat p n) ≤ n := Nat.le_of_dvd hn h1
  have h3 : (0 : ℝ) < ((∏ p ∈ P, p ^ padicValNat p n : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _
  calc ∑ p ∈ P, Real.log (p : ℝ) * (padicValNat p n : ℝ)
      = Real.log ((∏ p ∈ P, p ^ padicValNat p n : ℕ) : ℝ) := by
        push_cast
        rw [Real.log_prod (fun p hp => by
          have := (hP p hp).pos
          positivity)]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Real.log_pow]; ring
    _ ≤ Real.log (n : ℝ) := Real.log_le_log h3 (by exact_mod_cast h2)

open Classical in

def EatCI (L : SizeData₂ D) (K : Consts) (c : ErrC) (j p : ℕ) : ℝ :=
  if IsResidueClassZero D p ∧ hP D p = 0 then EatC L c j p else EatI L K c j p

def LevelPrimeBudget (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop := ∀ u, Formalism.MainNotions.product_first_zeroth_parts.WeightBudgetBound D u L C

def StabiliserLogBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop := ∀ u, 2 * Real.log ((D.mem u).C.DGam : ℝ) ≤ C * L.B0

def DiscriminantOffsetBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, 2 * Real.log (D.host.d : ℝ) * |EatD D j| ≤ C * L.B0

def InertPrimeLossBound (D : D7) (L : SizeData₂ D) (K : Consts) (c : ErrC) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ P : Finset ℕ,
    (∀ p ∈ P, p.Prime ∧ (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) →
    ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatCI L K c j p| ≤ C * L.B0

open Classical in

def hOff (L : SizeData₂ D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j p : ℕ) : ℝ :=
  (padicValNat p (D.mem u).C.DGam : ℝ) + (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0) +
    (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0)

theorem hOff_nonneg (L : SizeData₂ D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j p : ℕ) : 0 ≤ hOff L K c u j p := by
  unfold hOff
  have h1 : (0 : ℝ) ≤ (padicValNat p (D.mem u).C.DGam : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0) := by split_ifs <;> simp
  have h3 : 0 ≤ (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0) := by
    split_ifs <;> simp
  linarith

theorem Eval_off (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ) (w : D.what₂.places.Pl)
    (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T) (hg : D.what₂.places.resChar w ∉ L.gTypes) :
    |Eval L X K c u j w| ≤ hOff L K c u j (D.what₂.places.resChar w) := by
  have h0 : D.what₂.places.resChar w ≠ D.host.g 0 := fun h => hg (by simp [SizeData₂.gTypes, h])
  have h1 : D.what₂.places.resChar w ≠ D.host.g 1 := fun h => hg (by simp [SizeData₂.gTypes, h])
  have hv : (0 : ℝ) ≤ (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ) := Nat.cast_nonneg _
  unfold Eval hOff EatCI
  simp only [if_neg h0, if_neg h1, if_neg hT]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hv]
  by_cases hr : D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD
  · simp only [if_pos hr]
    have : 0 ≤ (if (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
        (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        |if IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0 then
          EatC L c j (D.what₂.places.resChar w) else EatI L K c j (D.what₂.places.resChar w)| else 0) := by
      split_ifs <;> simp
    linarith
  · simp only [if_neg hr]
    by_cases hi : (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
        (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hi]; linarith
    · simp only [if_neg hi]; simp

theorem EatT_nonneg (u : D.what₂.Word) (w : D.what₂.places.Pl) : 0 ≤ EatT D u w := by
  unfold EatT
  have h3 : 0 ≤ Nm D := by unfold Nm; positivity
  split_ifs
  · positivity
  · exact le_rfl

theorem abs_sz (w : D.what₂.places.Pl) (y : ℝ) :
    |SizeData₂.sz w y| = 2 * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * |y|) := by
  unfold SizeData₂.sz
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (logWeight_nonneg w), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ))]
  ring

theorem C2off_of (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (CT CG Cd CI : ℝ)
    (hE : L.EDef X K c) (hT : LevelPrimeBudget D L CT) (hG : StabiliserLogBound D L CG) (hD : DiscriminantOffsetBound D L Cd)
    (hI : InertPrimeLossBound D L K c CI) : C2off D L (CT + CG + Cd + CI) := by
  classical
  intro u j hj
  set S := L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes) with hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun w => D.what₂.places.resChar w = (D.mem u).A.T)]
  have p1 : ∑ w ∈ S.filter (fun w => D.what₂.places.resChar w = (D.mem u).A.T), |SizeData₂.sz w (L.E u j w)| ≤ CT * L.B0 := by
    have e : ∀ w ∈ S.filter (fun w => D.what₂.places.resChar w = (D.mem u).A.T),
        |SizeData₂.sz w (L.E u j w)| = SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) := by
      intro w hw
      have hw' := (Finset.mem_filter.1 hw).2
      have : L.E u j w = EatT D u w := by
        rw [hE u j hj w]; unfold Eval; simp only [if_pos hw']
      rw [this, abs_of_nonneg]
      unfold SizeData₂.sz
      have := logWeight_nonneg w
      have := EatT_nonneg u w
      positivity
    rw [Finset.sum_congr rfl e]
    exact (((hT u).1 (S.filter (fun w => D.what₂.places.resChar w = (D.mem u).A.T))
      (fun w hw => (Finset.mem_filter.1 hw).2)).2).trans (hT u).2
  set S2 := S.filter (fun w => ¬ D.what₂.places.resChar w = (D.mem u).A.T) with hS2
  set P := S2.image D.what₂.places.resChar with hP
  have hPp : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨w0, _, hw0⟩ := Finset.mem_image.1 hp
    exact hw0 ▸ D.what₂.places.resChar_prime w0
  have p2 : ∑ w ∈ S2, |SizeData₂.sz w (L.E u j w)| ≤ 2 * ∑ p ∈ P, Real.log (p : ℝ) * hOff L K c u j p := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_by_prime S2 (hOff L K c u j) (hOff_nonneg L K c u j)) (by norm_num))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    have hw2 := Finset.mem_filter.1 hw
    have hw1 := Finset.mem_filter.1 hw2.1
    rw [abs_sz, hE u j hj w]
    have := Eval_off L X K c u j w hw2.2 hw1.2
    have h5 : 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := mul_nonneg (logWeight_nonneg w) (Nat.cast_nonneg _)
    nlinarith
  have q1 : ∑ p ∈ P, Real.log (p : ℝ) * (padicValNat p (D.mem u).C.DGam : ℝ) ≤ Real.log ((D.mem u).C.DGam : ℝ) :=
    sum_val_log_le _ (D.mem u).C.DGam_pos P hPp
  have q2 : ∑ p ∈ P, Real.log (p : ℝ) * (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0) ≤
      Real.log (D.host.d : ℝ) * |EatD D j| := by
    have : ∀ p ∈ P, Real.log (p : ℝ) * (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0) =
        if D.host.cls p = PrimeClass.ramD then Real.log (p : ℝ) * |EatD D j| else 0 := by
      intro p _; split_ifs <;> simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := {D.host.d})
      (fun p hp => Finset.mem_singleton.2 (cls_ramD (Finset.mem_filter.1 hp).2))
      fun p _ _ => mul_nonneg (Real.log_natCast_nonneg _) (abs_nonneg _)).trans ?_
    simp
  have q3 : ∑ p ∈ P, 2 * (Real.log (p : ℝ) *
      (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0)) ≤ CI * L.B0 := by
    have : ∀ p ∈ P, 2 * (Real.log (p : ℝ) *
        (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0)) =
        if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then 2 * Real.log (p : ℝ) * |EatCI L K c j p| else 0 := by
      intro p _; split_ifs <;> ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
    exact hI j hj _ fun p hp => ⟨hPp p (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2⟩
  have q4 : ∑ p ∈ P, Real.log (p : ℝ) * hOff L K c u j p =
      (∑ p ∈ P, Real.log (p : ℝ) * (padicValNat p (D.mem u).C.DGam : ℝ)) +
      (∑ p ∈ P, Real.log (p : ℝ) * (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0)) +
      ∑ p ∈ P, Real.log (p : ℝ) *
        (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold hOff; ring
  rw [← Finset.mul_sum] at q3
  have g1 := hG u
  have g2 := hD j hj
  rw [q4] at p2
  nlinarith

def SecondComplementInputs (D : D7) (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (Cdeg Cg CT CG Cd CI : ℝ) : Prop :=
  LevelPrimeNotTypePrime D ∧ NormDecompositionCond D X ∧ DegreeCountBound D L Cdeg ∧ TypePrimeSizeBound D L c Cdeg Cg ∧ LevelPrimeBudget D L CT ∧ StabiliserLogBound D L CG ∧
    DiscriminantOffsetBound D L Cd ∧ InertPrimeLossBound D L K c CI

theorem secondComplement_of_inputs (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (Cdeg Cg CT CG Cd CI : ℝ) (hc : c.Large) (hCg : 0 ≤ Cg)
    (hE : L.EDef X K c) (h : SecondComplementInputs D L X K c Cdeg Cg CT CG Cd CI) :
    IsotypicRank D L (2 * Cg + (CT + CG + Cd + CI)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact secondComplement_of_split L Cg _ hCg (C2atG_of L X K c Cdeg Cg hc hE a1 a2 a3 a4) (C2off_of L X K c CT CG Cd CI hE a5 a6 a7 a8)

def FamilySecondComplementInputs {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ Cdeg Cg CT CG Cd CI x0 : ℝ, 0 ≤ Cg ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
    SecondComplementInputs (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX Fm.GK Fm.cX.err Cdeg Cg CT CG Cd CI

def familySecondComplement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, IsotypicRank (Fm.D x i) (Fm.L x i) C

theorem secondComplement_family_of_inputs {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : FamilySecondComplementInputs Fm) : familySecondComplement Fm := by
  obtain ⟨Cdeg, Cg, CT, CG, Cd, CI, x0, h0, h⟩ := h
  exact ⟨_, x0, fun x hx0 hx i => secondComplement_of_inputs (Fm.L x i) (Fm.ex x hx i).errX Fm.GK Fm.cX.err Cdeg Cg CT CG Cd CI
    (Fm.ex x hx i).err.large h0 (Fm.ex x hx i).err.edef (h x hx0 hx i)⟩


end PartA

section PartB

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

def PairAtT (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  DGamDef D → (∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ z ∈ locW D.what₂.places w ((D.fm u).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.Ptil ((D.fm u).emb D.R.m z) ((D.eMt u).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ))) ∧
  ∀ u μ, μ ≠ D.what₂.mu0 → ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ z ∈ locW D.what₂.places w ((T.fm u μ).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).Ptil ((T.fm u μ).emb D.R.m z) ((D.eMtTw u μ).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ))

def PairingAtEveryPlace (D : D7) (Dx : DivX D) (T : TwForms D) : Prop := PairInt D Dx T ∧ PairAtT D Dx T

def MemberChainIntegral (D : D7) : Prop := ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u

def TwistedChainIntegral (D : D7) (T : TwForms D) : Prop :=
  ∀ u μ, μ ≠ D.what₂.mu0 → ∃ h : (T.fm u μ).PRat, (T.fm u μ).PtilIntegral h

def PeriodClassSumWeyl (D : D7) : Prop :=
  DGamDef D → ∀ u, ∀ x ∈ (D.fm u).ptLat.L, ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm F) ∧
      ∀ w : D.what₂.places.Pl, y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def TwistedPeriodIntegral (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  DGamDef D → ∀ u μ, μ ≠ D.what₂.mu0 → ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
        y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def PairingFromIntegrality (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  MemberChainIntegral D → TwistedChainIntegral D T → PeriodClassSumWeyl D → TwistedPeriodIntegral D Dx T → PairingAtEveryPlace D Dx T

theorem pair_add_ge (D : D7) (w : D.what₂.places.Pl) {a b : D.what₂.LL} {B : ℝ}
    (ha : a = 0 ∨ B ≤ (vAdd (D.plEq w) a : ℝ)) (hb : b = 0 ∨ B ≤ (vAdd (D.plEq w) b : ℝ)) :
    a + b = 0 ∨ B ≤ (vAdd (D.plEq w) (a + b) : ℝ) := by
  rcases ha with rfl | ha
  · simpa using hb
  rcases hb with rfl | hb
  · simpa using Or.inr ha
  by_cases ha0 : a = 0
  · subst ha0; simpa using Or.inr hb
  by_cases hb0 : b = 0
  · subst hb0; simpa using Or.inr ha
  by_cases hab : a + b = 0
  · exact Or.inl hab
  right
  have h := (D.what₂.places.val w).map_add a b
  rw [D.val_eq w _ ha0, D.val_eq w _ hb0, D.val_eq w _ hab] at h
  have h' : min (vAdd (D.plEq w) a) (vAdd (D.plEq w) b) ≤ vAdd (D.plEq w) (a + b) := by
    rcases le_total (vAdd (D.plEq w) a) (vAdd (D.plEq w) b) with h1 | h1
    · rw [min_eq_left h1]
      rw [min_eq_left (by exact_mod_cast h1)] at h
      exact_mod_cast h
    · rw [min_eq_right h1]
      rw [min_eq_right (by exact_mod_cast h1)] at h
      exact_mod_cast h
  have h2 : (min (vAdd (D.plEq w) a) (vAdd (D.plEq w) b) : ℝ) ≤ (vAdd (D.plEq w) (a + b) : ℝ) := by
    exact_mod_cast h'
  exact le_trans (le_min ha hb) h2

theorem pair_smul_ge (D : D7) (w : D.what₂.places.Pl) {r b : D.what₂.LL} {B : ℝ}
    (hr : r ∈ intW D.what₂.places w) (hb : b = 0 ∨ B ≤ (vAdd (D.plEq w) b : ℝ)) :
    r * b = 0 ∨ B ≤ (vAdd (D.plEq w) (r * b) : ℝ) := by
  rcases hb with rfl | hb
  · left; simp
  by_cases hr0 : r = 0
  · left; simp [hr0]
  by_cases hb0 : b = 0
  · left; simp [hb0]
  right
  rw [vAdd_mul' _ hr0 hb0]
  have h0 : (0 : WithTop ℤ) ≤ D.what₂.places.val w r := hr
  rw [D.val_eq w _ hr0] at h0
  have h1 : (0 : ℤ) ≤ vAdd (D.plEq w) r := by exact_mod_cast h0
  have h2 : (0 : ℝ) ≤ (vAdd (D.plEq w) r : ℝ) := by exact_mod_cast h1
  push_cast
  linarith

theorem pair_core (D : D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
    (Λ : Submodule (𝓞 D.what₂.LL) V) (g : V →ₛₗ[D.what₂.embLL] ℂ) (B : ℝ)
    (h : ∀ x ∈ Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = g x ∧ (y = 0 ∨ B ≤ (vAdd (D.plEq w) y : ℝ))) :
    ∀ z ∈ locW D.what₂.places w Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = g z ∧ (y = 0 ∨ B ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro z hz
  unfold locW at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by simp, Or.inl rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb], pair_add_ge D w ha' hb'⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, ha'⟩ := hx
    refine ⟨(r : D.what₂.LL) * a, ?_, pair_smul_ge D w r.2 ha'⟩
    rw [map_mul, ha, Subring.smul_def, LinearMap.map_smulₛₗ]
    rfl


def ValuationAtLevelPrime (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      ColGe T u μ w x (-((D.R.m : ℝ) * EatT D u w))

def LevelPrimeCoprimeStabiliser (D : D7) : Prop := ∀ u, ¬ (D.mem u).A.T ∣ (D.mem u).C.DGam

def LevelPrimeSizes (D : D7) (L : SizeData₂ D) : Prop := ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ETDef D u L

def ServedHasModel {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ → GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)

def GainLe {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts) : Prop :=
  ∀ (w : D.what₂.places.Pl), ∀ j ∈ SizeData₂.lifts D, L.gainD j w ≤ gainS X K (D.what₂.places.resChar w) j

def NuInM (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)

def L2BoundAlt (D : D7) (L : SizeData₂ D) : Prop := Formalism.MainNotions.LocalQuadraticParts.adm2 D L

def FourthComplement (D : D7) (L : SizeData₂ D) : Prop := Formalism.MainNotions.LocalQuadraticParts.adm12 D L

variable {D : D7} {L : SizeData₂ D}


theorem sg_atT (hE : LevelPrimeSizes D L) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) : L.sg u w = -((D.R.m : ℝ) * EatT D u w) := by
  unfold SizeData₂.sg
  have h : ∀ j ∈ SizeData₂.lifts D, L.gainD j w + L.F j w - L.E u j w = -EatT D u w := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := (hE u w hw).2 j hj
    have h4 : L.gainD j w = 0 := by
      unfold SizeData₂.gainD
      split_ifs
      · rfl
      · exact h1
    rw [h4, h2, h3]
    simp
  rw [Finset.sum_congr rfl h, Finset.sum_const]
  simp [SizeData₂.lifts]




theorem gainLe_of_fills {X : Inst D L} {K : Consts} (hF : ∀ w, ParametersFill X K w)
    (hcs : ∀ p : ℕ, p.Prime → IsCs D p → p ∈ L.drop) : GainLe X K :=
  fun w j hj => WeilJacquetShalikaLaw.gainD_le_gainS hF hcs w j hj

theorem inv_mem_intW (D : D7) (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal) :
    ((s : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact Submodule.zero_mem _
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w ((s : D.what₂.LL))⁻¹
  rw [D.val_eq w _ (inv_ne_zero hs0)]
  have h1 : (D.plEq w).valuation D.what₂.LL (s : D.what₂.LL) = 1 := by
    have := (D.plEq w).valuation_of_algebraMap (K := D.what₂.LL) s
    rw [show (s : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL s from rfl, this]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
  have h2 : vAdd (D.plEq w) ((s : D.what₂.LL))⁻¹ = 0 := by
    unfold vAdd
    rw [map_inv₀, h1]
    simp
  rw [h2]
  rfl

theorem nuIn_mem_Sram_loc (u : D.what₂.Word) (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V)
    (h : LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) (hφ : φ ∈ L.NuLat u) : D.nuIn u φ ∈ LT.Sram D u w := by
  obtain ⟨s, hs, hm⟩ := h φ hφ
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hm
  have h1 := nuIn_mem_Sram D u w (s • φ) hm
  have h2 := (LT.Sram D u w).smul_mem ⟨_, inv_mem_intW D w s hs⟩ h1
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact Submodule.zero_mem _
  have h3 : (⟨_, inv_mem_intW D w s hs⟩ : intW D.what₂.places w) • D.nuIn u (s • φ) = D.nuIn u φ := by
    rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL s φ, map_smul, smul_smul]
    show (((s : D.what₂.LL))⁻¹ * (s : D.what₂.LL)) • D.nuIn u φ = D.nuIn u φ
    rw [inv_mul_cancel₀ hs0, one_smul]
  rw [h3] at h2
  exact h2


def PerColSmul (D : D7) : Prop :=
  ∀ u (μ : D.what₂.Tup) (c : ℂ) (φ : D.what₂.Mu u) (F : D.what₂.Amb μ), D.what₂.perCol u μ (c • φ) F = c * D.what₂.perCol u μ φ F

def SgAtG (D : D7) (L : SizeData₂ D) (Xe : ErrX D) (C1 : ℝ) : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i → ∀ u : D.what₂.Word,
    D.what₂.places.resChar w ≠ (D.mem u).A.T →
      (∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w)) ≤ -(∑ j ∈ Formalism.MainNotions.LiftErrorLocal.lifts D, vNN Xe i u j w) - C1 * Formalism.MainNotions.LiftErrorLocal.errC D L

theorem sg_atG (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)) :
    L.sg u w = ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) := by
  unfold SizeData₂.sg
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : L.gainD j w = 0 := by
    unfold SizeData₂.gainD
    split_ifs
    · rfl
    · exact L.gain_g j w hg
  rw [h0, zero_add]

theorem mem_gTypes_of (w : D.what₂.places.Pl) (i : Fin 2) (hi : D.what₂.places.resChar w = D.host.g i) :
    D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
  rw [hi]; fin_cases i <;> simp






section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def familyL2Bound : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, L2BoundAlt (Fm.D x i) (Fm.L x i)

def familyFourthComplement : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, FourthComplement (Fm.D x i) (Fm.L x i)

def familyPairing : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), PairingAtEveryPlace (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

def familyPairingInputs : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    MemberChainIntegral (Fm.D x i) ∧ TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw ∧ PeriodClassSumWeyl (Fm.D x i) ∧
      TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw


def FamilyLevelPrimeInputs : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ValuationAtLevelPrime (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw ∧ LevelPrimeSizes (Fm.D x i) (Fm.L x i) ∧ LevelPrimeCoprimeStabiliser (Fm.D x i) ∧
      ServedHasModel (Fm.Gx x i) Fm.GK

def FamilyPeriodFormCond (C1 C2 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2

def familySizeBoundAtTypePrime (C1 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, SgAtG (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1


end Fam

end PartB

section PartC

open Formalism.BasicNotions NumberField

section Arch

variable {D : D7} {T : ThetaX D}

structure LocC (X : ZetaProductPairs.Loc D T) where

  Vc : D.what₂.Word → Type
  [acVc : ∀ u, AddCommGroup (Vc u)]
  [moVc : ∀ u, Module ℂ (Vc u)]

  VD : D.what₂.Word → Type
  [acVD : ∀ u, AddCommGroup (VD u)]
  [moVD : ∀ u, Module ℂ (VD u)]

  ell : ∀ u, Vc u →ₗ[ℂ] VD u →ₗ[ℂ] ℂ

  vOf : ∀ u, X.ArchDat u → Vc u

  TOf : ∀ u, X.ArchDat u → VD u

  ellT_eq : ∀ u da, X.ellT u da = ell u (vOf u da) (TOf u da)

  v_free : ∀ u (v : Vc u) (da : X.ArchDat u), ∃ da', vOf u da' = v ∧ TOf u da' = TOf u da

attribute [instance] LocC.acVc LocC.moVc LocC.acVD LocC.moVD

def Chain (T : ThetaX D) (P : TH.TPar D) (μ : ℕ → T.Chr) (π : Submodule ℂ (T.AF (T.Xs P.t 0)))
    (φ : T.AF (T.Xs P.t 0)) (F : ∀ j : ℕ, T.cusp (T.Ys P.t j))
    (Φ : ∀ j : ℕ, T.Sch (T.Ys P.t (j + 1)) (T.Ys P.t j)) : Prop :=
  CayleySignature.IsMu T P μ ∧ CayleySignature.IsAutRep T _ π ∧ π ≤ T.typeX P 0 ∧ φ ∈ π ∧
  CayleySignature.IsDv T P D.R.m (F D.R.m : T.AF (T.Ys P.t D.R.m)) ∧
  (∀ j : ℕ, j < D.R.m → Φ j ∈ T.fact _ _ ∧ Φ j ∈ T.kfin _ _ ∧
    ((F j : T.cusp (T.Ys P.t j)) : T.AF (T.Ys P.t j)) = CayleySignature.vth T P.t μ j (Φ j) (F (j + 1)) ∧
    CayleySignature.IsDv T P j (F j : T.AF (T.Ys P.t j)))

def ParametersPolynomiallyBounded (T : ThetaX D) : Prop := ∀ u, CayleySignature.Hyp3 T (T.parOf u)

def NonzeroBesselPeriodChain (D : D7) (T : ThetaX D) : Prop := CayleySignature.PointsLemma D T

def UnfoldingAnyLevel (X : ZetaProductPairs.Loc D T) : Prop :=
  ∀ u μ π φ F Φ (pos : T.Pos (T.Xs (T.parOf u).t 0) (T.Ys (T.parOf u).t 0) (T.iXYs (T.parOf u).t 0)),
    Chain T (T.parOf u) μ π φ F Φ → CayleySignature.bB T (T.parOf u).t 0 pos 0 φ (F 0) ≠ 0 →
    ∃ Xp Yp : ℂ, Xp ≠ 0 ∧ ∀ da, X.ellT u da * Xp = X.Au u da * Yp

def LinearFormNonzero {X : ZetaProductPairs.Loc D T} (Y : LocC X) : Prop := ∀ u, Y.ell u ≠ 0

def ThetaOntoKFinite {X : ZetaProductPairs.Loc D T} (Y : LocC X) : Prop := ∀ u, Submodule.span ℂ (Set.range (Y.TOf u)) = ⊤

def ArchimedeanNonvanishing (X : ZetaProductPairs.Loc D T) : Prop := Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing D T X


def AdmArch {X : ZetaProductPairs.Loc D T} (Y : LocC X) : Prop :=
  NonzeroBesselPeriodChain D T ∧ ParametersPolynomiallyBounded T ∧ UnfoldingAnyLevel X ∧ LinearFormNonzero Y ∧ ThetaOntoKFinite Y


end Arch

section Rat

variable (D : D7)

def RationalMapValues : Prop :=
  ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V), ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.Bu u (D.jN u φ) (D.jEE x)

def BkDef : Prop :=
  ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V) (y : D.what₂.LL),
    D.what₂.embLL y = D.what₂.Bu u (D.jN u φ) (D.jEE x) → D.div.Bk u φ x = y

def RationalFormOfMap : Prop := D.BuRational


def PeriodRationalReference : Prop :=
  ∀ (u : D.what₂.Word), ∀ y ∈ (D.fm u).ramL, ∀ φ : D.what₂.Mu u,
    ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) = (D.fm u).emb 0 y →
    ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, ∃ x : D.what₂.LL, D.what₂.embLL x = D.what₂.perCol u D.what₂.mu0 φ F

def ExistsIntegralPlace (Z : DivX D) : Prop := ∀ u, ∃ w, ZetaProductPairs.IntPlace Z u D.what₂.mu0 w

theorem exists_integral_place (Z : DivX D) : ExistsIntegralPlace D Z := by
  intro u
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes ((D.mem u).A.T + D.host.g 0 + D.host.g 1 + D.host.d + 1)
  have : Fact p.Prime := ⟨hpp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hP, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.what₂.LL) (Ideal.span {(p : ℤ)})
  have hmem : (p : 𝓞 D.what₂.LL) ∈ P := by
    have : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 D.what₂.LL)) P := by
      show (p : ℤ) ∈ Ideal.under ℤ P
      rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  have hne : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hmem
    exact hpp.ne_zero (by exact_mod_cast hmem)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) := ⟨P, hP.isPrime, hne⟩
  have hr : D.what₂.places.resChar (D.plEq.symm v) = p := by
    rw [resChar_iff D p hpp, Equiv.apply_symm_apply]; exact hmem
  refine ⟨D.plEq.symm v, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; omega
  · rw [hr]; omega
  · rw [hr]; omega
  · rw [hr]; omega
  · rw [Z.degreeZero_partial_set_empty]; simp

variable {D} in
theorem referencePeriodRational_of_integral (Z : DivX D) (h : ZetaProductPairs.PeriodIntegrality Z) : PeriodRationalReference D := by
  intro u y hy φ hφ F hF
  obtain ⟨w, hw⟩ := exists_integral_place D Z u
  obtain ⟨x, hx, _⟩ := h u D.what₂.mu0 w (Or.inl rfl) hw y hy φ hφ F hF
  have hG : (((D.mem u).C.DGam : ℕ) : D.what₂.LL) ^ (D.R.m + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (D.mem u).C.DGam_pos.ne')
  have hG' : (((D.mem u).C.DGam : ℕ) : ℂ) ^ (D.R.m + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (D.mem u).C.DGam_pos.ne')
  refine ⟨x / (((D.mem u).C.DGam : ℕ) : D.what₂.LL) ^ (D.R.m + 1), ?_⟩
  rw [map_div₀, map_pow, map_natCast, hx, mul_div_cancel_left₀ _ hG']

def EEFormDef : Prop := Set.range D.jEE ⊆ AbsolutelyIrreducibleSpan.llSpan D.what₂.embLL (D.what₂.RRset D.what₂.mu0)





end Rat

section C5



variable {D : D7} {T : ThetaX D}

def ScalarUnitaryRows (D : D7) : Prop := LocalQuadraticParts.adm13 D




def FifthComplementInputs (Z : DivX D) (X : ZetaProductPairs.Loc D T) : Prop :=
  ZetaProductPairs.MultiplicityOneWithZeta X ∧ ZetaProductPairs.ExchangeOfPositions X ∧ InnerProductFormulaField.PointsLemma D Z ∧ Rows.BuDefQ D.what₂ ∧ ZetaProductPairs.ZeDef X ∧ ArchimedeanNonvanishing X


end C5

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ZetaProductPairs.Loc (Fm.D x i) (Fm.ex x hx i).th)

def familyArchimedeanNonvanishing : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ArchimedeanNonvanishing (XF x hx i)

def AdmArchF (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocC (XF x hx i)) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AdmArch (YF x hx i)


def familyFifthComplement : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.adm13 (Fm.D x i)

end Family

end PartC

section PartE

open Formalism.BasicNotions NumberField IsDedekindDomain

structure LocE (D : D7) where

  mY : D.what₂.FT → ℕ

  mW : ℕ → D.what₂.FT → ℕ

  smallLevelDimension : D.what₂.FT → ℕ

section Lat

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end Lat

def Lmu (D : D7) (μ : D.what₂.Tup) : Submodule (𝓞 D.what₂.LL) D.div.RR.V :=
  Submodule.span (𝓞 D.what₂.LL) {y | D.jEE y ∈ D.what₂.RRset μ}

def IsFullL (D : D7) (A : Submodule (𝓞 D.what₂.LL) D.div.RR.V) : Prop :=
  A.FG ∧ Submodule.span D.what₂.LL (A : Set D.div.RR.V) = ⊤

def InRR (D : D7) (μ : D.what₂.Tup) : Prop := LocalQuadraticParts.UsedT D μ

def TwFin (D : D7) : Prop := {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite

def TuplesInRowRangeAll (D : D7) : Prop := ∀ μ, InRR D μ → D.what₂.RRset μ ⊆ Set.range D.jEE

def IotaSurjective (D : D7) : Prop :=
  ∀ μ, InRR D μ → Function.Surjective ((D.what₂.iota μ).domRestrict (D.what₂.Qsp μ))

def FullRowLattices (D : D7) : Prop := ∀ μ, InRR D μ → IsFullL D (Lmu D μ)

def FullLatticesFromInputs (D : D7) : Prop := TuplesInRowRangeAll D → IotaSurjective D → Rows.AIntegral D.what₂ → FullRowLattices D

section Form

variable {K : Type} [Field K] {σ : K →+* ℂ} {V : Type} [AddCommGroup V] [Module K V]
  {E : Type} [AddCommGroup E] [Module ℂ E] {ι : Type} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K V) (j : V →ₛₗ[σ] E)

theorem form_expand (v : V) : j v = ∑ i, σ (b.repr v i) • j (b i) := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, LinearMap.map_smulₛₗ]

theorem form_inj (hli : LinearIndependent ℂ (fun i => j (b i))) : Function.Injective j := by
  intro x y hxy
  have h0 : j (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [form_expand b j] at h0
  have h3 := Fintype.linearIndependent_iff.1 hli (fun i => σ (b.repr (x - y) i)) h0
  have h4 : b.repr (x - y) = 0 := Finsupp.ext fun i => (map_eq_zero σ).1 (h3 i)
  exact sub_eq_zero.1 (b.repr.map_eq_zero_iff.1 h4)


end Form

theorem gen_mem {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V)
    (g : V) (hg : g ∈ L.gen) : g ∈ L.carrier := by
  classical
  refine ⟨fun v => if v = g then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single g]
  · simp
  · intro v _ hv; simp [hv]
  · intro h; exact absurd hg h

section Side

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

def LmuS (μ : D.what₂.Tup) : Submodule (𝓞 D.what₂.LL) S.RR.V :=
  Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset μ}

def TuplesInRowRange : Prop := ∀ μ, InRR D μ → S.RRset μ ⊆ Set.range S.jEE

def LevelIotaSurjective : Prop := ∀ μ, InRR D μ → Function.Surjective (S.iotaQ μ)

def FullRowLatticeSide : Prop :=
  ∀ μ, InRR D μ → (LmuS S μ).FG ∧ Submodule.span D.what₂.LL (LmuS S μ : Set S.RR.V) = ⊤

def FullLatticesFromInputsSide : Prop := TuplesInRowRange S → LevelIotaSurjective S → S.AIntegral → FullRowLatticeSide S


end Side

def RowLatticeRankPos (D : D7) : Prop := 0 < D.div.RR.rank






def SmallLevelExtremalVectors (D : D7) (X : LocE D) : Prop := ∀ π, D.what₂.nRows0 π = X.mY π * X.smallLevelDimension π

def HolomorphicLowestVectors (D : D7) (X : LocE D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π, Module.finrank ℂ (D.what₂.isot j π) = X.mW j π * X.smallLevelDimension π

def MultiplicityTransfer (D : D7) (X : LocE D) : Prop := ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π, X.mW j π = X.mY π

def IsotypicRankTransfer (D : D7) : Prop := Rows.IsotRank D.what₂


def IsotypicInternalDecomp (D : D7) : Prop := Rows.IsotInternal D.what₂

def MjRankSmallLevel (D : D7) (Z : DivX D) : Prop := DV.MjRank D Z




def TypeOccursSmallLevel (D : D7) : Prop := ∀ σ : Fin D.what₂.Drows, 0 < D.what₂.nRows0 (D.what₂.ft σ)



def ThetaEquivariantIdempotent (D : D7) : Prop :=
  ∀ μ, ∀ j ∈ SizeData₂.lifts D, D.what₂.thetaP μ j ∘ₗ D.what₂.eMt μ j = D.what₂.thetaP μ j

def ThetaInIdempotentImage (D : D7) : Prop :=
  ∀ μ, ∀ j ∈ SizeData₂.lifts D, LinearMap.range (D.what₂.thetaT μ j) ≤ LinearMap.range (D.what₂.eMt μ j)


def CentralElementPreserves (D : D7) : Prop :=
  ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))),
    (∀ g, (z : MonoidAlgebra ℂ (G0g D.nd)).coeff g ∈ Set.range D.what₂.phiO) →
    ∀ x ∈ (D.what₂.Mtilde μ).carrier, D.ntypes.cenAmb μ z x ∈ (D.what₂.Mtilde μ).carrier

def CentralIdempotentIntegralAlt (D : D7) : Prop :=
  D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) ∧
  ∀ g, ((D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0).coeff g ∈ Set.range D.what₂.phiO

def IdempotentIntegral (D : D7) : Prop := Rows.AIntegral D.what₂



section SideAI

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

def CentralElementPreservesSide : Prop :=
  ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))),
    (∀ g, (z : MonoidAlgebra ℂ (G0g D.nd)).coeff g ∈ Set.range D.what₂.phiO) →
    ∀ x ∈ (S.Mtilde μ).carrier, S.cen μ z x ∈ (S.Mtilde μ).carrier



end SideAI

def SmallIdempotentIntegral {D : D7} (P : BaseLevelRowSide D) : Prop := P.s.AIntegral


section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)


def EvE (P : ∀ x, Fm.Ix x → Prop) : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, P x i

def familyFullLattices : Prop := EvE Fm fun x i => FullRowLattices (Fm.D x i)
def familyTransfer : Prop := EvE Fm fun x i => Rows.IsotRank (Fm.D x i).what₂ ∧ Rows.IsotInternal (Fm.D x i).what₂
def familyThetaInImage : Prop := EvE Fm fun x i => ThetaInIdempotentImage (Fm.D x i)
def familyIdempotentIntegral : Prop := EvE Fm fun x i => Rows.AIntegral (Fm.D x i).what₂
def familyMjRank : Prop := EvE Fm fun x i => DV.MjRank (Fm.D x i) (Fm.X x i)

def familySmallLevelIntegral : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, (Fm.ex x hx i).p0.s.AIntegral





def familySmallFullLattices : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, FullRowLatticeSide (Fm.ex x hx i).p0.s

end Fam

end PartE

section PartEJ

open Formalism.BasicNotions NumberField IsDedekindDomain




end PartEJ

section PartF

open Formalism.BasicNotions Formalism.BasicNotions.DV

variable (D : D7)

variable {D} in
theorem onRj_nonneg {fl : ℕ → ℕ → ℝ} {r : ℕ → D.what₂.places.Pl → ℝ} (h1 : ∀ j l, 0 ≤ fl j l) (h2 : ∀ j w, 0 ≤ r j w)
    (j : ℕ) (w : D.what₂.places.Pl) : 0 ≤ PDVN.onRj D fl r j w :=
  add_nonneg (h1 _ _) (div_nonneg (add_nonneg (h2 _ _) (h2 _ _)) (Nat.cast_nonneg _))

def onCore (L : SizeData₂ D) : ℝ :=
  L.sc.L * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * PDVN.wMax D + (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * Real.log L.sc.x


def JB (L : SizeData₂ D) (CJ A : ℝ) : ℝ :=
  CJ * (D.host.T2.card : ℝ) * (D.R.m : ℝ) * L.sc.b * L.sc.x ^ (2 * L.sc.eps) + A * (D.R.m : ℝ) * L.sc.b

def admJ (L : SizeData₂ D) (X : LocalQuadraticParts.Loc D) (CJ A : ℝ) : Prop :=
  (∀ j w, 0 ≤ X.Jx j w) ∧ ∀ j ∈ SizeData₂.lifts D, ∀ T : Finset D.what₂.places.Pl,
    ∑ w ∈ T, SizeData₂.lwP w * ur D w (X.Jx j w) ≤ JB D L CJ A

def JTie (X : LocalQuadraticParts.Loc D) (J : ℕ → ℕ → ℕ) : Prop := ∀ j w, X.Jx j w = (J j (D.what₂.places.resChar w) : ℝ)

def JSum (L : SizeData₂ D) (J : ℕ → ℕ → ℕ) (CJ A : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ n : ℕ, ∑ l ∈ JumpSetsAlt.primesUpTo n, (J j l : ℝ) * Real.log l ≤ JB D L CJ A

def FibreLe : Prop := ∀ (p : ℕ), p.Prime → ∀ S : Finset D.what₂.places.Pl,
  (∀ w ∈ S, D.what₂.places.resChar w = p) → ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) ≤ Real.log p

theorem fibreLe : FibreLe D := by
  classical
  intro p hp S hS
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  have h1 : ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) =
      ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v * (eWL D.what₂.LL v : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [D.ram_eq w]; rfl
  have hsub : S.map D.plEq.toEmbedding ⊆ T := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
    rw [hT]
    have := resChar_mem D w
    rw [hS w hw] at this
    exact this
  rw [h1, ← sum_lw_e p hp T hT]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => mul_nonneg ?_ (Nat.cast_nonneg _))
  unfold lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

variable {D} in
theorem exponentCond_of_sum {L : SizeData₂ D} {X : LocalQuadraticParts.Loc D} {J : ℕ → ℕ → ℕ} {CJ A : ℝ} (hF : FibreLe D) (hT : JTie D X J)
    (hS : JSum D L J CJ A) : admJ D L X CJ A := by
  classical
  refine ⟨fun j w => by rw [hT]; exact Nat.cast_nonneg _, fun j hj T => ?_⟩
  set n := T.sup D.what₂.places.resChar with hn
  refine le_trans ?_ (hS j hj n)
  have hmap : ∀ w ∈ T, D.what₂.places.resChar w ∈ JumpSetsAlt.primesUpTo n := fun w hw => by
    unfold JumpSetsAlt.primesUpTo
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := D.what₂.places.resChar) hw), D.what₂.places.resChar_prime w⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_le_sum fun l hl => ?_
  have hlp : l.Prime := by
    unfold JumpSetsAlt.primesUpTo at hl
    exact (Finset.mem_filter.1 hl).2
  have h1 : ∑ w ∈ T.filter (fun w => D.what₂.places.resChar w = l), SizeData₂.lwP w * ur D w (X.Jx j w) =
      (J j l : ℝ) * ∑ w ∈ T.filter (fun w => D.what₂.places.resChar w = l),
        SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hT, (Finset.mem_filter.1 hw).2]
    unfold ur; ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left (hF l hlp _ fun w hw => (Finset.mem_filter.1 hw).2) (Nat.cast_nonneg _)

def OntoSizeBound (L : SizeData₂ D) (C Cabs : ℝ) : Prop :=
  onCore D L ≤ C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc)

def ExponentSumSize (L : SizeData₂ D) (CJ A C Cabs : ℝ) : Prop :=
  JB D L CJ A ≤ C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc)

def admW (L : SizeData₂ D) : Prop := PDVN.wMax D ≤ 2 * (D.R.f : ℝ) * L.sc.b

theorem x_pos (L : SizeData₂ D) : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt

theorem B_zero_shape_eq_index (L : SizeData₂ D) : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.x ^ L.sc.eps := rfl

theorem Nc_nonneg (L : SizeData₂ D) : 0 ≤ L.Nc := by
  have hx := x_pos D L
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  positivity

theorem b_pos (L : SizeData₂ D) : 0 < L.sc.b := Real.exp_pos _



variable {D} in
theorem termwise_of {L : SizeData₂ D} {fl : ℕ → ℕ → ℝ} {r : ℕ → D.what₂.places.Pl → ℝ} {w : D.what₂.places.Pl}
    (h : PDVN.onL D L (D.what₂.muAt w) w ≤ PDVN.onR D fl r w) :
    ∑ j ∈ SizeData₂.lifts D,
        (((D.what₂.Ij (D.what₂.muAt w) j w : ℝ) + (D.what₂.Ij (D.what₂.muAt w) j (D.what₂.places.conj w) : ℝ)) /
          (D.what₂.D0 : ℝ) - 2 * ur D w (L.F j w)) ≤
      ur D w ((∑ j ∈ SizeData₂.lifts D, PDVN.onRj D fl r j w) + 2 / ((D.what₂.places.resChar w : ℝ) ^ 2)) := by
  have he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by exact_mod_cast D.what₂.places.ramIdx_pos w
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h he.le)
  unfold PDVN.onL PDVN.inL ur
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PDVN.ramIdx_conj]
  field_simp


def OntoBoundFromExponents (L : SizeData₂ D) (X : LocalQuadraticParts.Loc D) (C1 CJ A C C' Cabs : ℝ) : Prop :=
  0 ≤ C1 → PDVN.ONTwJ D L C1 → admJ D L X CJ A → OntoSizeBound D L C Cabs → ExponentSumSize D L CJ A C' Cabs →
    LocalQuadraticParts.ArchimedeanSignatureMatching D L X (C1 * C + C') Cabs


end PartF

section PartF2

open Formalism.BasicNotions Formalism.BasicNotions.DV

variable (D : D7)

theorem wSz_eq_wj (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) : wSz D j τ = wj D j τ := by
  unfold wSz wj
  rw [dif_pos ⟨h1, h2⟩, dif_pos (by omega : j - 1 < D.R.m)]

theorem two_le_b (L : SizeData₂ D) : 2 ≤ L.sc.b := by
  have h1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have h2 : L.sc.L + 1 ≤ L.sc.b := Real.add_one_le_exp _
  linarith

theorem b'_le (L : SizeData₂ D) (hS : Formalism.MainNotions.SizeLstar L) : L.sc.b' ≤ L.sc.b / 3 := by
  have hb := b_pos D L
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ (D.R.t : ℝ) := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m
    exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hN : (D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold Ranks.N
    have : D.R.m ≤ D.R.k + D.R.m * (D.R.t + 1) := by nlinarith [Nat.zero_le D.R.k, Nat.zero_le (D.R.m * D.R.t)]
    exact_mod_cast this
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hSc := L.Sc_pos
  set Den := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
      (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) with hDen
  have d1 : 3 * (D.R.m : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by
    have a1 : (3 : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 := by nlinarith
    have a2 : (D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) + D.R.t := by linarith
    have a3 : (1 : ℝ) ≤ L.sc.L ^ 2 := by nlinarith
    have a4 : 3 * (D.R.m : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) :=
      mul_le_mul a1 a2 (by linarith) (by linarith)
    nlinarith
  have d2 : 0 ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by positivity
  have d3 : 3 * (D.R.m : ℝ) ≤ Den := by rw [hDen]; linarith
  have hD0 : 0 < Den := by linarith
  have hl : Formalism.MainNotions.szlStar L ≤ L.sc.b / 3 := by
    unfold Formalism.MainNotions.szlStar
    rw [← hDen, div_le_div_iff₀ hD0 (by norm_num)]
    nlinarith
  have h1 := hS.1
  have h2 : 0 ≤ L.sc.b / Formalism.MainNotions.szlStar L := by
    refine div_nonneg hb.le ?_
    unfold Formalism.MainNotions.szlStar
    rw [← hDen]; positivity
  have h3 := L.etaSz_pos
  linarith

theorem eta_le (L : SizeData₂ D) (hE : Formalism.MainNotions.SizeEta L) : L.etaSz ≤ L.sc.b / 8 := by
  have hb := b_pos D L
  refine hE.2.1.trans ?_
  have ht : (2 : ℝ) ≤ (D.R.t : ℝ) := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m
    exact_mod_cast (by omega : 2 ≤ D.R.t)
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have h8 : (8 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by
    have a1 : (8 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by nlinarith [mul_self_nonneg ((D.R.t : ℝ) - 2)]
    have a2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk
    have a3 : (8 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := by nlinarith
    nlinarith
  exact div_le_div_of_nonneg_left hb.le (by norm_num) h8




theorem card_T2_le_degree : (D.host.T2.card : ℝ) ≤ (D.R.f : ℝ) := by
  have h1 : D.host.T2 ⊆ Finset.range D.R.n0 := fun s hs => by
    have h := D.host.second_set_range s hs
    have h2 := D.host.two_le_Lw
    rw [Finset.mem_range]
    nlinarith
  have h2 := Finset.card_le_card h1
  rw [Finset.card_range] at h2
  have : D.host.T2.card ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.cyclic_order_le_exponent; omega
  exact_mod_cast this


section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def familyOntoSize (Cabs : ℝ) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, OntoSizeBound (Fm.D x i) (Fm.L x i) C Cabs


def familyExponentSumSize (CJ A Cabs : ℝ) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, ExponentSumSize (Fm.D x i) (Fm.L x i) CJ A C Cabs



end Fam

structure LocF (D : D7) where
  h : ℕ → ℕ
  lam : ℕ → D.what₂.Tau → DomWeight D.R.nV
  sh : ℕ → D.what₂.Tau → JumpSetsAlt.ShapeData

def LiftParameterConditions (L : SizeData₂ D) (Y : LocF D) (A0 : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, JumpSetsAlt.S2 D L A0 (Y.h j) L.etaSz L.Sc (LevelStarExponents.h0 L) (LevelStarExponents.lStar L) (Y.lam j) (Y.sh j)

variable {D} in

def InclOk (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (j : ℕ) (J : ℕ → ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Z.Lev l) (mt : Ideal (Z.Hk l c)) [mt.IsMaximal],
    JumpSetsAlt.CorIdeal L Z l (Y.h j) c mt (Y.sh j) → JumpSetsAlt.Incl Z l c (Y.lam j) mt (J l)

section IV

open NumberField IsDedekindDomain

def MtO (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).carrier}

def MtZ (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  MtO D μ j ⊓ (Idx.TjV D μ j).restrictScalars (𝓞 D.what₂.LL)

def MtDualZ (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) where
  carrier := {x | x ∈ Idx.TjV D μ j ∧ ∀ a ∈ MtO D μ j, ∃ c : 𝓞 D.what₂.LL,
    inner ℂ (D.what₂.jMt μ j a) (D.what₂.jMt μ j x) = D.what₂.embLL (c : D.what₂.LL)}
  add_mem' := by
    rintro x y ⟨hx, h1⟩ ⟨hy, h2⟩
    refine ⟨(Idx.TjV D μ j).add_mem hx hy, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    obtain ⟨d, hd⟩ := h2 a ha
    exact ⟨c + d, by rw [map_add, inner_add_right, hc, hd]; simp⟩
  zero_mem' := ⟨(Idx.TjV D μ j).zero_mem, fun a _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro s x ⟨hx, h1⟩
    refine ⟨by rw [Idx.smul_def]; exact (Idx.TjV D μ j).smul_mem _ hx, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    exact ⟨s * c, by rw [Idx.smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hc]; simp⟩

def ixW (w : D.what₂.places.Pl) {μ : D.what₂.Tup} {j : ℕ} (A B : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j)) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx (D.plEq w).asIdeal A B

def IdxAdd : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (w : HeightOneSpectrum (𝓞 K)) (A B C : Submodule (𝓞 K) V), A.FG → B.FG → C.FG →
    Submodule.span K (A : Set V) = Submodule.span K (B : Set V) →
    Submodule.span K (B : Set V) = Submodule.span K (C : Set V) →
    Formalism.HermitianLatticesTheory.lidx w.asIdeal A C = Formalism.HermitianLatticesTheory.lidx w.asIdeal A B + Formalism.HermitianLatticesTheory.lidx w.asIdeal B C

def IdxExp : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (n : 𝓞 K) (d : ℕ), A.FG → B.FG →
    Submodule.span K (A : Set V) = Submodule.span K (B : Set V) →
    Module.finrank K (Submodule.span K (A : Set V)) = d → n ≠ 0 →
    (∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • n • x ∈ B) →
    Formalism.HermitianLatticesTheory.lidx w.asIdeal A B ≤ (d : ℤ) * vAdd w (n : K)

def IndexEqualsLatticeIndex : Prop :=
  ∀ μ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.jw μ j w = Idx.jwIdx D μ j w

def EtaLengthDef : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    ur D w (D.what₂.etaJ j w : ℝ) = (ixW D w (Idx.TjL D (D.what₂.muAt w) j) (MtZ D (D.what₂.muAt w) j) : ℝ)

def ProjectionDualCond : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    Idx.TjDual D (D.what₂.muAt w) j = MtDualZ D (D.what₂.muAt w) j

def LatticesOfCommonSpace : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    (Idx.TjL D (D.what₂.muAt w) j).FG ∧ (MtZ D (D.what₂.muAt w) j).FG ∧ (MtDualZ D (D.what₂.muAt w) j).FG ∧
    Submodule.span D.what₂.LL (MtZ D (D.what₂.muAt w) j : Set (D.what₂.MtL (D.what₂.muAt w) j)) = Idx.TjV D (D.what₂.muAt w) j ∧
    Submodule.span D.what₂.LL (MtDualZ D (D.what₂.muAt w) j : Set (D.what₂.MtL (D.what₂.muAt w) j)) = Idx.TjV D (D.what₂.muAt w) j ∧
    Module.finrank D.what₂.LL (Idx.TjV D (D.what₂.muAt w) j) = D.what₂.D0

variable {D}

structure TieIV (Z : JumpSetsAlt.Prov D) (Y : LocF D) where

  lev : ∀ (_j : ℕ) (w : D.what₂.places.Pl), Z.Lev (D.what₂.places.resChar w)

  emb : ∀ w : D.what₂.places.Pl, 𝓞 D.what₂.LL →+* Z.O (D.what₂.places.resChar w)
  emb_w : ∀ w (s : 𝓞 D.what₂.LL), s ∈ (D.plEq w).asIdeal ↔ emb w s ∈ IsLocalRing.maximalIdeal (Z.O (D.what₂.places.resChar w))

  Z0 : ∀ j w, Submodule (Z.Hk (D.what₂.places.resChar w) (lev j w)) (JumpSetsAlt.Frm Z (D.what₂.places.resChar w) (lev j w) (Y.lam j))
  saturated_base : ∀ j w, JumpSetsAlt.Saturated Z (D.what₂.places.resChar w) (lev j w) (Y.lam j) (Z0 j w)

  phi : ∀ j w, MtO D (D.what₂.muAt w) j →+ JumpSetsAlt.Frm Z (D.what₂.places.resChar w) (lev j w) (Y.lam j)
  phi_smul : ∀ j w (s : 𝓞 D.what₂.LL) (x : MtO D (D.what₂.muAt w) j), phi j w (s • x) = emb w s • phi j w x

  phi_nabla : ∀ j w x, phi j w x ∈ JumpSetsAlt.MNsub Z (D.what₂.places.resChar w) (lev j w) (Y.lam j)
  phi_Z : ∀ j w (x : MtO D (D.what₂.muAt w) j),
    (x : D.what₂.MtL (D.what₂.muAt w) j) ∈ Idx.TjV D (D.what₂.muAt w) j ↔ phi j w x ∈ Z0 j w

def HeckeStableBlockSupport (L : SizeData₂ D) {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    ∀ (mt : Ideal (Z.Hk (D.what₂.places.resChar w) (T.lev j w))) [mt.IsMaximal],
      (∃ z ∈ T.Z0 j w, (LocalizedModule.mk z 1 : LocalizedModule mt.primeCompl _) ≠ 0) →
        @JumpSetsAlt.CorIdeal D L Z (D.what₂.places.resChar w) ⟨D.what₂.places.resChar_prime w⟩ (Y.h j) (T.lev j w) mt (Y.sh j)

def dualExp (D : D7) (w : D.what₂.places.Pl) : ℕ :=
  padicValNat (D.what₂.places.resChar w) (D.mem D.u₀).C.DGam +
    (if ∃ i, D.what₂.places.resChar w = D.host.g i then 2 * D.R.f * D.R.N D.R.m ^ 2 else 0)

def DualityUpToStabilisers {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ x : MtO D (D.what₂.muAt w) j,
    (x : D.what₂.MtL (D.what₂.muAt w) j) ∈ Idx.TjV D (D.what₂.muAt w) j →
    T.phi j w x ∈ JumpSetsAlt.MDsub Z (D.what₂.places.resChar w) (T.lev j w) (Y.lam j) →
    ∃ s : 𝓞 D.what₂.LL, s ∉ (D.plEq w).asIdeal ∧
      s • ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ dualExp D w • (x : D.what₂.MtL (D.what₂.muAt w) j) ∈
        MtDualZ D (D.what₂.muAt w) j

theorem mem_of_locSet {T M : Type} [CommRing T] [AddCommGroup M] [Module T M] (N : Submodule T M) (y : M)
    (h : ∀ (mt : Ideal T) [mt.IsMaximal],
      (LocalizedModule.mk y 1 : LocalizedModule mt.primeCompl M) ∈ JumpSetsAlt.locSet mt.primeCompl (N : Set M)) : y ∈ N := by
  by_contra hy
  let I : Ideal T := N.comap (LinearMap.toSpanSingleton T M y)
  have hI : I ≠ ⊤ := by
    intro h1
    have : (1 : T) ∈ I := by rw [h1]; trivial
    exact hy (by simpa [I] using this)
  obtain ⟨mt, hm, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨x, hx, s, hs⟩ := h mt
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hs
  have h2 : ((u : T) * (s : T)) ∈ I := by
    show LinearMap.toSpanSingleton T M y ((u : T) * (s : T)) ∈ N
    have e : ((u : T) * (s : T)) • y = (u : T) • x := by
      have := hu
      simp only [Submonoid.smul_def, one_smul] at this
      rw [mul_smul]; exact this.symm
    rw [LinearMap.toSpanSingleton_apply, e]
    exact N.smul_mem _ hx
  exact (u * s).2 (hle h2)

theorem vAdd_lpow (D : D7) (w : D.what₂.places.Pl) (k : ℕ) :
    vAdd (D.plEq w) ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) =
      (D.what₂.places.ramIdx w : ℤ) * k := by
  have hl : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D.what₂.places.resChar_prime w).ne_zero
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k ≠ 0 := pow_ne_zero _ hl
  have e1 : ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) =
      ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k := by simp
  rw [e1]
  have h1 := D.val_eq w _ hne
  rw [AddValuation.map_pow, D.what₂.places.val_resChar] at h1
  have h2 : (((k • ((D.what₂.places.ramIdx w : ℕ) : ℤ)) : ℤ) : WithTop ℤ) =
      ((vAdd (D.plEq w) (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k) : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_nsmul]; exact h1
  rw [← WithTop.coe_inj.mp h2, nsmul_eq_mul]
  ring

def IndexOk (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (j : ℕ) (J : ℕ → ℕ) : Prop :=
  JumpSetsAlt.CorIndex L Z (Y.h j) (Y.lam j) (Y.sh j) J

theorem h11 {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) (hB : HeckeStableBlockSupport L T)
    {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {w : D.what₂.places.Pl} (hw : D.what₂.muAt w ≠ D.what₂.mu0) {Jj : ℕ → ℕ}
    (hI : IndexOk L Z Y j Jj) (x : MtO D (D.what₂.muAt w) j)
    (hx : (x : D.what₂.MtL (D.what₂.muAt w) j) ∈ Idx.TjV D (D.what₂.muAt w) j) :
    T.phi j w ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ Jj (D.what₂.places.resChar w)) • x) ∈
      JumpSetsAlt.MDsub Z (D.what₂.places.resChar w) (T.lev j w) (Y.lam j) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hZ := (T.phi_Z j w x).1 hx
  have hN := T.phi_nabla j w x
  have key : (algebraMap (Z.O (D.what₂.places.resChar w)) (Z.Hk (D.what₂.places.resChar w) (T.lev j w))
      (((D.what₂.places.resChar w : ℕ) : Z.O (D.what₂.places.resChar w)) ^ Jj (D.what₂.places.resChar w))) • T.phi j w x ∈
        T.Z0 j w ⊓ JumpSetsAlt.MDsub Z (D.what₂.places.resChar w) (T.lev j w) (Y.lam j) := by
    apply mem_of_locSet
    intro mt _
    have h0 := (hI (D.what₂.places.resChar w) (T.lev j w) (T.Z0 j w) (T.saturated_base j w)
      (fun mt' _ h => hB j hj w hw mt' h) mt).1 (LocalizedModule.mk (T.phi j w x) 1) ⟨T.phi j w x, ⟨hZ, hN⟩, 1, rfl⟩
    rw [LocalizedModule.smul'_mk] at h0
    exact h0
  rw [T.phi_smul, map_pow, map_natCast]
  rw [algebraMap_smul] at key
  exact key.2

def AdmIV (L : SizeData₂ D) {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) : Prop :=
  IdxAdd ∧ IdxExp ∧ IndexEqualsLatticeIndex D ∧ EtaLengthDef D ∧ ProjectionDualCond D ∧ LatticesOfCommonSpace D ∧ HeckeStableBlockSupport L T ∧ DualityUpToStabilisers T

def ExponentIndexAnyExponents (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) : Prop :=
  ∀ J : ℕ → ℕ → ℕ, (∀ j ∈ SizeData₂.lifts D, IndexOk L Z Y j (J j)) →
    LocalQuadraticParts.TwistedIndexValuationBound D ⟨fun j w => (J j (D.what₂.places.resChar w) : ℝ)⟩



end IV

variable {D} in

theorem exists_J {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} {A0 CJ A : ℝ} (h : JumpSetsAlt.PointsLemma D L Z A0 CJ A)
    (hS : LiftParameterConditions D L Y A0) :
    ∃ J : ℕ → ℕ → ℕ, JSum D L J CJ A ∧ ∀ j ∈ SizeData₂.lifts D, InclOk L Z Y j (J j) ∧ IndexOk L Z Y j (J j) := by
  classical
  have : ∀ j, ∃ Jj : ℕ → ℕ, j ∈ SizeData₂.lifts D →
      (∀ n : ℕ, ∑ l ∈ JumpSetsAlt.primesUpTo n, (Jj l : ℝ) * Real.log l ≤ JB D L CJ A) ∧ InclOk L Z Y j Jj ∧ IndexOk L Z Y j Jj :=
    fun j => by
    by_cases hj : j ∈ SizeData₂.lifts D
    · obtain ⟨J, h1, h2, h3⟩ := h _ _ _ _ _ _ _ (hS j hj)
      exact ⟨J, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hj⟩
  choose J hJ using this
  exact ⟨J, fun j hj => (hJ j hj).1, fun j hj => (hJ j hj).2⟩

variable {D} in

theorem exists_Jx {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} {A0 CJ A : ℝ}
    (h : JumpSetsAlt.PointsLemma D L Z A0 CJ A) (hS : LiftParameterConditions D L Y A0) :
    ∃ (X : LocalQuadraticParts.Loc D) (J : ℕ → ℕ → ℕ), JTie D X J ∧ admJ D L X CJ A ∧
      ∀ j ∈ SizeData₂.lifts D, InclOk L Z Y j (J j) ∧ IndexOk L Z Y j (J j) := by
  obtain ⟨J, hJ, hI⟩ := exists_J h hS
  exact ⟨⟨fun j w => (J j (D.what₂.places.resChar w) : ℝ)⟩, J, fun _ _ => rfl, exponentCond_of_sum (fibreLe D) (fun _ _ => rfl) hJ, hI⟩

def ExponentBoundIV (X : LocalQuadraticParts.Loc D) : Prop := LocalQuadraticParts.TwistedIndexValuationBound D X

def ExponentAnyForm (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) : Prop := ExponentIndexAnyExponents L Z Y


def ExponentChoiceBounds (L : SizeData₂ D) (CJ A : ℝ) : Prop := ∃ X : LocalQuadraticParts.Loc D, admJ D L X CJ A ∧ ExponentBoundIV D X

def ExponentBoundAnyExponents (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (A0 CJ A : ℝ) : Prop :=
  JumpSetsAlt.PointsLemma D L Z A0 CJ A → LiftParameterConditions D L Y A0 → ExponentAnyForm D L Z Y → ExponentChoiceBounds D L CJ A


def ExponentBoundFromCorollary (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (T : TieIV Z Y) (A0 CJ A : ℝ) : Prop :=
  JumpSetsAlt.PointsLemma D L Z A0 CJ A → LiftParameterConditions D L Y A0 → AdmIV L T → ExponentChoiceBounds D L CJ A


section FamJ

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

open Classical in

theorem jivF {CJ A : ℝ}
    (h : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, ExponentChoiceBounds (Fm.D x i) (Fm.L x i) CJ A) :
    ∃ XF : ∀ x (i : Fm.Ix x), LocalQuadraticParts.Loc (Fm.D x i), ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      admJ (Fm.D x i) (Fm.L x i) (XF x i) CJ A ∧ ExponentBoundIV (Fm.D x i) (XF x i) := by
  obtain ⟨x0, h⟩ := h
  refine ⟨fun x i => if h' : ExponentChoiceBounds (Fm.D x i) (Fm.L x i) CJ A then h'.choose else ⟨fun _ _ => 0⟩, x0, fun x hx h1 i => ?_⟩
  have h' := h x hx h1 i
  show admJ (Fm.D x i) (Fm.L x i) (dite _ _ _) CJ A ∧ ExponentBoundIV (Fm.D x i) (dite _ _ _)
  rw [dif_pos h']
  exact h'.choose_spec


end FamJ

end PartF2

end Formalism.MainNotions.WeightDegreeSizes

end
