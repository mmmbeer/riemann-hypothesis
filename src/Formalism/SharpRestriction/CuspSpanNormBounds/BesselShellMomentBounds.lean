import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

section PieceB2a

open Finset

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.S.Pv.Frames

section Pts

variable {K : Type} [Field K]

def pS (bs : List (K × ℕ)) (p : ℕ) : ℕ := ((bs.map Prod.snd).take p).sum

theorem ptEntry_block (bs : List (K × ℕ)) : ∀ (p : ℕ) (hp : p < bs.length) (i j : ℕ),
    pS bs p ≤ i → i < pS bs (p + 1) →
    ptEntry bs i j = if i + j + 1 = pS bs p + pS bs (p + 1) then (bs[p]).1 else 0 := by
  induction bs with
  | nil => intro p hp; simp at hp
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro p hp i j h1 h2
    cases p with
    | zero =>
      have e1 : pS ((t, s) :: bs) 0 = 0 := by simp [pS]
      have e2 : pS ((t, s) :: bs) (0 + 1) = s := by simp [pS]
      rw [e2] at h2
      rw [e1, e2]
      by_cases hj : j < s
      · simp [ptEntry, h2, hj]
      · have h3 : ¬ (i + j + 1 = s) := by omega
        have h4 : ¬ (s ≤ i) := by omega
        simp [ptEntry, hj, h3, h4]
    | succ p =>
      have e1 : pS ((t, s) :: bs) (p + 1) = s + pS bs p := by simp [pS]
      have e2 : pS ((t, s) :: bs) (p + 1 + 1) = s + pS bs (p + 1) := by simp [pS]
      rw [e1] at h1; rw [e2] at h2
      have hp' : p < bs.length := by simpa using hp
      have h := ih p hp' (i - s) (j - s) (by omega) (by omega)
      rw [e1, e2]
      have hi : s ≤ i := by omega
      have hi' : ¬ (i < s) := by omega
      by_cases hj : s ≤ j
      · have : ptEntry ((t, s) :: bs) i j = ptEntry bs (i - s) (j - s) := by
          simp [ptEntry, hi', hi, hj]
        rw [this, h]
        have hc : (i - s + (j - s) + 1 = pS bs p + pS bs (p + 1)) ↔
            (i + j + 1 = s + pS bs p + (s + pS bs (p + 1))) := by omega
        simp [hc]
      · have h3 : ¬ (i + j + 1 = s + pS bs p + (s + pS bs (p + 1))) := by omega
        simp [ptEntry, hi', hj, h3]

variable {d : ℕ}

def toComp (γ : Point K d) : Composition d where
  blocks := γ.1.map Prod.snd
  blocks_pos := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hi
    exact (γ.2.1 b hb).2
  blocks_sum := γ.2.2

theorem toComp_length (γ : Point K d) : (toComp γ).length = γ.1.length := by
  simp [toComp, Composition.length]

def toT (γ : Point K d) : Fin (toComp γ).length → K :=
  fun a => (γ.1[a.val]'(lt_of_lt_of_eq a.2 (toComp_length γ))).1

theorem toT_ne (γ : Point K d) (a) : toT γ a ≠ 0 := by
  unfold toT
  exact (γ.2.1 _ (by simp)).1

theorem sizeUpTo_toComp (γ : Point K d) (p : ℕ) : (toComp γ).sizeUpTo p = pS γ.1 p := rfl

theorem index_unique (c : Composition d) (j : Fin d) (p : Fin c.length)
    (h1 : c.sizeUpTo p ≤ j) (h2 : (j : ℕ) < c.sizeUpTo (p + 1)) : c.index j = p := by
  apply Fin.ext
  have hq1 := c.sizeUpTo_index_le j
  have hq2 := c.lt_sizeUpTo_index_succ j
  rw [Fin.val_succ] at hq2
  rcases lt_trichotomy (c.index j : ℕ) p with h | h | h
  · exfalso
    have := c.monotone_sizeUpTo (show (c.index j : ℕ) + 1 ≤ (p : ℕ) from h)
    omega
  · exact h
  · exfalso
    have := c.monotone_sizeUpTo (show (p : ℕ) + 1 ≤ (c.index j : ℕ) from h)
    omega

theorem ptMat_eq (γ : Point K d) : ptMat γ = blockAntidiagonalMatrix (toComp γ) (toT γ) := by
  ext i j
  have a1 := (toComp γ).sizeUpTo_index_le i
  have a2 := (toComp γ).lt_sizeUpTo_index_succ i
  simp only [Fin.val_succ] at a2
  have hp : ((toComp γ).index i : ℕ) < γ.1.length := lt_of_lt_of_eq ((toComp γ).index i).2 (toComp_length γ)
  have h := ptEntry_block γ.1 ((toComp γ).index i) hp i j a1 a2
  unfold ptMat blockAntidiagonalMatrix
  rw [h]
  by_cases hc : (i : ℕ) + j + 1 = pS γ.1 ((toComp γ).index i) + pS γ.1 (((toComp γ).index i : ℕ) + 1)
  · have hj : (toComp γ).index j = (toComp γ).index i := by
      apply index_unique
      · rw [sizeUpTo_toComp] at a1 a2 ⊢; omega
      · rw [sizeUpTo_toComp] at a1 a2 ⊢; omega
    rw [if_pos hc, if_pos ⟨hj.symm, hc⟩]
    rfl
  · rw [if_neg hc, if_neg (fun h' => hc h'.2)]

theorem leadMinorK_eq {R : Type} [CommRing R] (A : Matrix (Fin d) (Fin d) R) (l : ℕ) (hl : l ≤ d) :
    leadMinorK A l hl = leadingPrincipalMinor A l := by
  unfold leadMinorK leadingPrincipalMinor
  let e : Fin l ≃ {i : Fin d // (i : ℕ) < l} :=
    { toFun := fun a => ⟨Fin.castLE hl a, a.2⟩
      invFun := fun i => ⟨i.1.1, i.2⟩
      left_inv := fun a => rfl
      right_inv := fun i => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem E5minor_eq (c : Composition d) (t : Fin c.length → K) (a : Fin c.length) :
    IndexedMinorEntry c.blocksFun t a = leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo ((a : ℕ) + 1)) := by
  rw [Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue K d c t ((a : ℕ) + 1)]
  unfold IndexedMinorEntry
  refine Finset.prod_congr (Finset.filter_congr fun x _ => ⟨fun h => Nat.lt_succ_of_le h, fun h => Nat.le_of_lt_succ h⟩) ?_
  · intro x _
    congr 1
    simp [ParitySign, Nat.choose_two_right]

def toSig (γ : Point K d) : Σ c : Composition d, (Fin c.length → K) := ⟨toComp γ, toT γ⟩

def ofSig (x : Σ c : Composition d, (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn (fun a => (x.2 a, x.1.blocksFun a))

theorem ofSig_toSig (γ : Point K d) : ofSig (toSig γ) = γ.1 := by
  apply List.ext_getElem
  · simp [ofSig, toSig, toComp_length]
  · intro n h1 h2
    simp [ofSig, toSig, toT, toComp, Composition.blocksFun]

theorem toSig_inj : Function.Injective (toSig (K := K) (d := d)) := by
  intro γ γ' h
  apply Subtype.ext
  rw [← ofSig_toSig γ, ← ofSig_toSig γ', h]

end Pts

end Formalism.MainNotions.BesselShellMomentBounds

end PieceB2a

section PieceB2b

open Finset NumberField

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.S.Pv.Frames

section Places

variable (D : D7)

instance instCM : NumberField.IsCMField D.host.E := D.host.isCMField_hostE

theorem plEmb_mem (v : D.what₂.Tau) : plEmb D v ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau v).2

theorem cm_iff (φ : D.host.E →+* ℂ) : φ ∈ D.host.cmType ↔
    (starRingEnd ℂ).comp φ ∉ D.host.cmType :=
  (D.host.der.cmType).1 φ

noncomputable def plOf (v : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (plEmb D v)

theorem plOf_apply (v : D.what₂.Tau) (x : D.host.E) : plOf D v x = absV D v x := rfl

theorem conj_eq (φ : D.host.E →+* ℂ) : ComplexEmbedding.conjugate φ = (starRingEnd ℂ).comp φ := rfl

theorem plOf_bij : Function.Bijective (plOf D) := by
  constructor
  · intro v v' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · have := (factEmb D.R D.host).1.1 h
      exact D.eTau.injective (Subtype.ext this)
    · exfalso
      rw [conj_eq] at h
      have h1 := (cm_iff D (plEmb D v)).1 (plEmb_mem D v)
      rw [h] at h1
      exact h1 (plEmb_mem D v')
  · intro w
    obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 w.embedding
    by_cases hP : g ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨g, hP⟩, ?_⟩
      unfold plOf plEmb
      rw [Equiv.apply_symm_apply]
      show InfinitePlace.mk (D.host.emb g) = w
      rw [hg, InfinitePlace.mk_embedding]
    · have h1 : w.embedding ∉ D.host.cmType := by
        rw [← hg]; exact fun h => hP (((factEmb D.R D.host).2 g).1 h)
      have h2 : (starRingEnd ℂ).comp w.embedding ∈ D.host.cmType := by
        by_contra h3
        exact h1 ((cm_iff D _).2 h3)
      obtain ⟨g', hg'⟩ := (factEmb D.R D.host).1.2 ((starRingEnd ℂ).comp w.embedding)
      have hP' : g' ∈ D.R.Psi := ((factEmb D.R D.host).2 g').1 (by rw [hg']; exact h2)
      refine ⟨D.eTau.symm ⟨g', hP'⟩, ?_⟩
      unfold plOf plEmb
      rw [Equiv.apply_symm_apply]
      show InfinitePlace.mk (D.host.emb g') = w
      rw [hg', ← conj_eq, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem card_places : Fintype.card (InfinitePlace D.host.E) = Fintype.card D.what₂.Tau := by
  exact (Fintype.card_of_bijective (plOf_bij D)).symm

theorem blockEnds_prod (F : ℕ → ℝ) (bs : List (D.host.E × ℕ)) : ∀ acc : ℕ,
    ((blockEnds D acc bs).map F).prod = ∏ a : Fin bs.length, F (acc + pS bs ((a : ℕ) + 1)) := by
  induction bs with
  | nil => intro acc; simp [blockEnds]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro acc
    simp only [blockEnds, List.map_cons, List.prod_cons, List.length_cons]
    rw [Fin.prod_univ_succ, ih]
    have e0 : F (acc + s) = F (acc + pS ((t, s) :: bs) (((0 : Fin (bs.length + 1)) : ℕ) + 1)) := by simp [pS]
    rw [e0]
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    congr 1
    simp [pS, add_assoc]

theorem wPt_eq (γ : Point D.host.E (D.R.rS + 1)) : wPt D γ = blockMinorWeight (toSig γ) := by
  unfold wPt blockMinorWeight
  rw [blockEnds_prod]
  refine Fintype.prod_equiv (finCongr (toComp_length γ).symm) _ _ ?_
  intro a
  have hle : 0 + pS γ.1 ((a : ℕ) + 1) ≤ D.R.rS + 1 := by
    rw [zero_add]; exact (toComp γ).sizeUpTo_le _
  rw [dif_pos hle]
  refine (Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ ?_)
  intro v
  rw [plOf_apply]
  congr 4
  show _ = IndexedMinorEntry (toComp γ).blocksFun (toT γ) _
  rw [E5minor_eq, leadMinorK_eq, ptMat_eq]
  simp [sizeUpTo_toComp]

theorem point_embedding_of_boundary_point (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) (h : IsBPt D T T' γ) : BlockEndMinorsIntegral (toSig γ) := by
  obtain ⟨⟨Z, hZ, L, U, hL, hU, rfl⟩, -⟩ := h
  intro (a : Fin (toComp γ).length)
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.integral_evaluation_fourth D.host.E (integralClosure ℤ D.host.E).toSubring (D.R.rS + 1) (toComp γ) (toT γ)
    (toT_ne γ) L U ⟨fun i => (hL i i).2 rfl, fun i j hij => (hL i j).1 hij⟩
    ⟨fun i => (hU i i).2 rfl, fun i j hij => (hU i j).1 hij⟩
    (by intro i j; rw [← ptMat_eq]; exact hZ i j)
  have := key.1 ((a : ℕ) + 1)
  show IsIntegral ℤ (IndexedMinorEntry (toComp γ).blocksFun (toT γ) a) ∧ IndexedMinorEntry (toComp γ).blocksFun (toT γ) a ≠ 0
  rw [E5minor_eq]
  exact this

end Places

theorem theorem_B_second_bound_64 (D : D7) : Formalism.MainNotions.OnePlaceEstimates.PathWeightComponents D 64 := by
  classical
  intro T T' _ _
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hpos : ∀ γ : Point D.host.E (D.R.rS + 1), 0 ≤ (wPt D γ)⁻¹ := by
    intro γ
    rw [wPt_eq]
    unfold blockMinorWeight
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => hpos γ.1)]
  apply ENNReal.ofReal_le_ofReal
  have hinj : Function.Injective (fun γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ} => toSig γ.1) :=
    fun a b h => Subtype.ext (toSig_inj h)
  have h1 : ∑ γ ∈ s, (wPt D γ.1)⁻¹ = ∑ x ∈ s.image (fun γ => toSig γ.1), (blockMinorWeight x)⁻¹ := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    exact Finset.sum_congr rfl (fun γ _ => by rw [wPt_eq])
  rw [h1, ← card_places]
  apply Formalism.HermitianLatticeCounting.Final.ExpansionTerms.component_total_sixty_four
  intro x hx
  obtain ⟨γ, _, rfl⟩ := Finset.mem_image.1 hx
  exact point_embedding_of_boundary_point D T T' γ.1 γ.2

end Formalism.MainNotions.BesselShellMomentBounds

end PieceB2b

section PieceB2c

open Finset NumberField

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.S.Pv.Frames









end Formalism.MainNotions.BesselShellMomentBounds

end PieceB2c

noncomputable section PieceB1

open MeasureTheory Matrix Finset

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.Pv.Frames

theorem strictAnti_of_interlace {k0 : ℕ} {u : Fin (k0 + 1) → ℝ} {ρ : Fin k0 → ℝ} (h : Interlace u ρ) :
    StrictAnti u := by
  exact Fin.strictAnti_iff_succ_lt.2 (fun j => (h j).2.trans (h j).1)








section ThmB

variable (D : D7)

def wLoc (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ((blockEnds D 0 γ.1).map fun l =>
    if hl : l ≤ D.R.rS + 1 then (1 + absV D v (leadMinorK (ptMat γ) l hl) ^ 2) ^ 2 else 1).prod

def dLoc (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) : ℝ :=
  absV D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl) ^ 2

def nLoc (T T' : ℕ) (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ptWeight D.R.k D.R.rS (T : ℝ) (T' : ℝ) (ptLoc D v γ)

theorem list_prod_finset {ι : Type*} [Fintype ι] (L : List ℕ) (f : ℕ → ι → ℝ) :
    (L.map fun l => ∏ v, f l v).prod = ∏ v, (L.map fun l => f l v).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Finset.prod_mul_distrib]

theorem wPt_eq_prod (γ : Point D.host.E (D.R.rS + 1)) : wPt D γ = ∏ v, wLoc D v γ := by
  unfold wPt wLoc
  rw [← list_prod_finset]
  congr 1
  apply List.map_congr_left
  intro l _
  split <;> simp

theorem wLoc_pos (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) : 0 < wLoc D v γ := by
  unfold wLoc
  apply List.prod_pos
  intro x hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  try dsimp only
  split_ifs <;> positivity

theorem wPt_pos (γ : Point D.host.E (D.R.rS + 1)) : 0 < wPt D γ := by
  rw [wPt_eq_prod]
  exact Finset.prod_pos (fun v _ => wLoc_pos D v γ)

theorem dLoc_nonneg (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) : 0 ≤ dLoc D v γ := by
  unfold dLoc
  positivity

theorem ptWeightG_eq_prod (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) :
    ptWeightG D (rhoReal D) T T' γ.1 = ∏ v, nLoc D T T' v γ := rfl

def WLoc (T T' : ℕ) (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) : ℝ :=
  absV D v (Gglob D T T' γ) * ((blockEnds D 0 γ.1).map fun l =>
    if hl : l ≤ D.R.rS + 1 then absV D v (leadMinorK (ptMat γ) l hl) ^ 2 else 1).prod

theorem WLoc_nonneg (T T' : ℕ) (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) : 0 ≤ WLoc D T T' v γ := by
  have habs : ∀ x, 0 ≤ absV D v x := fun x => by
    rw [← plOf_apply D v x]
    simp [plOf]
  unfold WLoc
  refine mul_nonneg (habs _) (List.prod_nonneg ?_)
  intro x hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  try dsimp only
  split_ifs <;> positivity

theorem normWt_eq_prod (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) :
    normWt D T T' γ = ∏ v, WLoc D T T' v γ := by
  unfold normWt WLoc NF
  rw [Finset.prod_mul_distrib, ← list_prod_finset]
  congr 2
  apply List.map_congr_left
  intro l _
  split
  · rfl
  · simp

theorem normWt_rpow (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) (p : ℝ) :
    normWt D T T' γ ^ p = ∏ v, WLoc D T T' v γ ^ p := by
  rw [normWt_eq_prod]
  exact (Real.finset_prod_rpow _ _ (fun v _ => WLoc_nonneg D T T' v γ) p).symm

theorem prod_absV_ge_one (x : D.host.E) (hx : IsIntegral ℤ x) (hx0 : x ≠ 0) : 1 ≤ ∏ v, absV D v x := by
  have : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have h := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.integral_norm_estimate D.host.E ⟨x, hx⟩ (by
    intro h0; apply hx0; exact congrArg Subtype.val h0)
  have hm : ∀ w : NumberField.InfinitePlace D.host.E, w.mult = 2 := by
    intro w
    have := NumberField.IsTotallyComplex.isComplex w
    simp [NumberField.InfinitePlace.mult, NumberField.InfinitePlace.not_isReal_iff_isComplex.2 this]
  simp only [hm, Finset.prod_pow] at h
  have h2 : ∏ v, absV D v x = ∏ w : NumberField.InfinitePlace D.host.E, w x := by
    rw [← Equiv.prod_comp (Equiv.ofBijective (plOf D) (plOf_bij D))]
    rfl
  rw [h2]
  exact (one_le_pow_iff_of_nonneg (Finset.prod_nonneg fun w _ => apply_nonneg w x) two_ne_zero).1 h

theorem plEmb_conj (v : D.what₂.Tau) (x : D.host.E) :
    plEmb D v (D.host.conj x) = starRingEnd ℂ (plEmb D v x) :=
  D.host.conjE_apply (plEmb D v) x

def alf (i : ℕ) : ℝ := D.host.rdE ^ (-((D.R.rS : ℤ) - (i : ℤ)))

theorem alf_pos (i : ℕ) : 0 < alf D i := by
  have h : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    apply Real.rpow_pos_of_pos
    rw [abs_pos]
    exact_mod_cast NumberField.discr_ne_zero D.host.E
  unfold alf
  exact zpow_pos h _

theorem alf_r : alf D D.R.rS = 1 := by
  simp [alf]

theorem ptEntry_loc (v : D.what₂.Tau) (bs : List (D.host.E × ℕ)) : ∀ (a i j : ℕ),
    ptEntry (locBlocksFrom D (rhoReal D) v a bs) i j =
      ((alf D (a + i) * alf D (a + j) : ℝ) : ℂ) * plEmb D v (ptEntry bs i j) := by
  induction bs with
  | nil => intro a i j; simp [locBlocksFrom, ptEntry]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro a i j
    simp only [locBlocksFrom, ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h2, if_pos h2]
        congr 2
        unfold rhoReal alf
        rw [← zpow_add₀ (rdE_pos D).ne', ← h2]
        congr 1
        push_cast
        ring
      · rw [if_neg h2, if_neg h2]; simp
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [if_pos h3, if_pos h3, ih (a + s) (i - s) (j - s)]
        have e1 : a + s + (i - s) = a + i := by omega
        have e2 : a + s + (j - s) = a + j := by omega
        rw [e1, e2]
      · rw [if_neg h3, if_neg h3]; simp

theorem leadMinor_loc (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    leadMinor (ptMat (ptLoc D v γ)) l hl =
      (((∏ i : Fin l, alf D i) ^ 2 : ℝ) : ℂ) * plEmb D v (leadMinorK (ptMat γ) l hl) := by
  unfold leadMinor leadMinorK
  have hM : (ptMat (ptLoc D v γ)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i : Fin l => ((alf D i : ℝ) : ℂ)) *
        (plEmb D v).mapMatrix ((ptMat γ).submatrix (Fin.castLE hl) (Fin.castLE hl)) *
        Matrix.diagonal (fun i : Fin l => ((alf D i : ℝ) : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have := ptEntry_loc D v γ.1 0 i j
    simp only [Nat.zero_add] at this
    simp only [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, ptMat, Fin.val_castLE]
    change ptEntry (locBlocksFrom D (rhoReal D) v 0 γ.1) i j = _
    rw [this]; push_cast; ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det]
  push_cast; ring

theorem GPoint_loc (T T' : ℝ) (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) :
    Gpt T T' (ptLoc D v γ) = ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 *
      (Complex.normSq (plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) -
        T * T' * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _)))) := by
  unfold Gpt
  rw [leadMinor_loc, leadMinor_loc, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, alf_r, mul_one, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem plEmb_Gglob (T T' : ℕ) (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) :
    plEmb D v (Gglob D T T' γ) =
      ((Complex.normSq (plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) -
        (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) : ℝ) : ℂ) := by
  unfold Gglob
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, plEmb_conj, plEmb_conj, Complex.mul_conj, Complex.mul_conj,
    map_natCast, map_natCast]
  push_cast; ring

theorem exists_rep_of_orbSq {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (h : orbSq L F γ ≠ 0) : ∃ g, IsPtRep L γ g := by
  by_contra hn
  simp only [not_exists] at hn
  apply h
  unfold orbSq
  simp only [ENNReal.iSup_eq_zero]
  intro g μR ν hP
  exact absurd hP.1 (hn g)

theorem GPoint_nonneg_of_rep {k r : ℕ} (L : LocBessel k r) (γ : Point ℂ (r + 1)) (g : Mx k r) (h : IsPtRep L γ g) :
    0 ≤ Gpt (Tz k r L.z) (Tz k r L.z') γ := by
  have h1 := Formalism.QuantumDeterminants.gNonneg k r L.z L.z' L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 g h.1
  have h2 : Gf k r L.z L.z' g = Gpt (Tz k r L.z) (Tz k r L.z') γ := by
    unfold Gf Gpt Dmin leadMinor
    rw [h.2]
  rwa [h2] at h1

theorem Grat_nonneg {Ch Cg dist : ℝ} {T T' : ℕ} {b : ℝ} (X : BData D Ch Cg T T' b dist) (γ : Point D.host.E (D.R.rS + 1))
    (hJ : JSqRot D X γ ≠ 0) (v : D.what₂.Tau) :
    0 ≤ Gpt (T : ℝ) (T' : ℝ) (ptLoc D v γ) ∧
    0 ≤ Complex.normSq (plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) -
        (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) := by
  have h1 : orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≠ 0 := Finset.prod_ne_zero_iff.1 hJ v (Finset.mem_univ v)
  obtain ⟨g, hg⟩ := exists_rep_of_orbSq _ _ _ h1
  have h2 := GPoint_nonneg_of_rep _ _ g hg
  rw [GPoint_turnPt] at h2
  rw [(X.hT v).1, (X.hT v).2] at h2
  refine ⟨h2, ?_⟩
  rw [GPoint_loc] at h2
  have hc : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by
    have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
    positivity
  exact nonneg_of_mul_nonneg_right h2 hc

theorem absV_G_le {Ch Cg dist : ℝ} {T T' : ℕ} {b : ℝ} (X : BData D Ch Cg T T' b dist) (γ : Point D.host.E (D.R.rS + 1))
    (hJ : JSqRot D X γ ≠ 0) (v : D.what₂.Tau) : absV D v (Gglob D T T' γ) ≤ dLoc D v γ := by
  have h := (Grat_nonneg D X γ hJ v).2
  unfold absV dLoc absV
  rw [plEmb_Gglob, Complex.norm_real, Real.norm_of_nonneg h, ← Complex.normSq_eq_norm_sq]
  have : 0 ≤ (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) := by
    have := Complex.normSq_nonneg (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _)))
    positivity
  linarith

theorem ptWeightFrom_nonneg (k r : ℕ) (T T' : ℝ) : ∀ (bs : List (ℂ × ℕ)) (a : ℕ),
    (∀ b ∈ bs, 1 ≤ b.2) → a + (bs.map Prod.snd).sum = r + 1 →
    (∀ t, bs.getLast? = some (t, 1) → T * T' ≤ Complex.normSq t) → 0 ≤ ptWeightFrom k r T T' a bs := by
  intro bs
  induction bs with
  | nil => intro a _ _ _; simp [ptWeightFrom]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro a h1 h2 h3
    simp only [ptWeightFrom]
    apply mul_nonneg
    · split_ifs with hc
      · have hbs : bs = [] := by
          cases bs with
          | nil => rfl
          | cons b' bs' =>
            have := h1 b' (by simp)
            simp only [List.map_cons, List.sum_cons] at h2
            omega
        subst hbs
        have := h3 t (by simp [hc.1])
        exact pow_nonneg (by linarith) _
      · positivity
    · apply ih (a + s) (fun b hb => h1 b (by simp [hb]))
      · simp only [List.map_cons, List.sum_cons] at h2; omega
      · intro t' ht'
        cases bs with
        | nil => simp at ht'
        | cons b' bs' => exact h3 t' (by rw [List.getLast?_cons_cons]; exact ht')

open Formalism.HermitianLatticeCounting.ExpansionTerms in

theorem last_block {r : ℕ} (γ : Point ℂ (r + 1)) (t : ℂ) (h : γ.1.getLast? = some (t, 1)) :
    leadMinor (ptMat γ) (r + 1) le_rfl = leadMinor (ptMat γ) r (Nat.le_succ r) * t ∧
      leadMinor (ptMat γ) r (Nat.le_succ r) ≠ 0 := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 h
  have hlen : (toComp γ).length = ys.length + 1 := by rw [toComp_length, hys]; simp
  have hs1 : (toComp γ).sizeUpTo (ys.length + 1) = r + 1 := by rw [← hlen]; exact (toComp γ).sizeUpTo_length
  have hs0 : (toComp γ).sizeUpTo ys.length = r := by
    have e := γ.2.2
    rw [sizeUpTo_toComp]
    unfold pS
    rw [hys] at e ⊢
    simp at e ⊢
    omega
  have v1 := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue ℂ (r + 1) (toComp γ) (toT γ) (ys.length + 1)
  have v0 := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue ℂ (r + 1) (toComp γ) (toT γ) ys.length
  rw [hs1] at v1
  rw [hs0] at v0
  have hf : (Finset.univ.filter fun a : Fin (toComp γ).length => (a : ℕ) < ys.length + 1) =
      insert (⟨ys.length, by omega⟩ : Fin (toComp γ).length)
        (Finset.univ.filter fun a : Fin (toComp γ).length => (a : ℕ) < ys.length) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hf, Finset.prod_insert (by simp), ← v0] at v1
  have hget : γ.1[ys.length]'(by rw [hys]; simp) = (t, 1) := by simp [hys]
  have hb : (toComp γ).blocksFun ⟨ys.length, by omega⟩ = 1 := by
    simp [Composition.blocksFun, toComp, hget]
  have ht : toT γ ⟨ys.length, by omega⟩ = t := by
    simp [toT, hget]
  rw [hb, ht] at v1
  have e1 : leadMinor (ptMat γ) (r + 1) le_rfl = leadingPrincipalMinor (blockAntidiagonalMatrix (toComp γ) (toT γ)) (r + 1) := by
    rw [← ptMat_eq]; exact leadMinorK_eq _ _ _
  have e0 : leadMinor (ptMat γ) r (Nat.le_succ r) = leadingPrincipalMinor (blockAntidiagonalMatrix (toComp γ) (toT γ)) r := by
    rw [← ptMat_eq]; exact leadMinorK_eq _ _ _
  rw [e1, e0]
  constructor
  · rw [v1]; simp [mul_comm]
  · rw [v0]
    refine Finset.prod_ne_zero_iff.2 fun a _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (toT_ne γ a))

theorem last_ok_of_G {r : ℕ} (T T' : ℝ) (γ : Point ℂ (r + 1)) (hG : 0 ≤ Gpt T T' γ) (t : ℂ)
    (h : γ.1.getLast? = some (t, 1)) : T * T' ≤ Complex.normSq t := by
  obtain ⟨h1, h2⟩ := last_block γ t h
  unfold Gpt at hG
  rw [h1, Complex.normSq_mul] at hG
  have hp : 0 < Complex.normSq (leadMinor (ptMat γ) r (Nat.le_succ r)) := Complex.normSq_pos.2 h2
  have : 0 ≤ Complex.normSq (leadMinor (ptMat γ) r (Nat.le_succ r)) * (Complex.normSq t - T * T') := by
    nlinarith
  have := nonneg_of_mul_nonneg_right this hp
  linarith

theorem nLoc_nonneg {Ch Cg dist : ℝ} {T T' : ℕ} {b : ℝ} (X : BData D Ch Cg T T' b dist)
    (γ : Point D.host.E (D.R.rS + 1)) (hJ : JSqRot D X γ ≠ 0) (v : D.what₂.Tau) : 0 ≤ nLoc D T T' v γ := by
  unfold nLoc ptWeight
  exact ptWeightFrom_nonneg _ _ _ _ _ 0 (fun b hb => ((ptLoc D v γ).2.1 b hb).2)
    (by rw [Nat.zero_add]; exact (ptLoc D v γ).2.2)
    (fun t ht => last_ok_of_G _ _ _ (Grat_nonneg D X γ hJ v).1 t ht)

def OnePlace (Ch Cg dist : ℝ) (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (A : ℕ) (CK : ℝ) (e : ℕ)
    (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ → ∀ v,
    ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p) *
        orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≤
      ENNReal.ofReal (b ^ (CK * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) * jNorm2 (X.L v) (X.f v) (X.μsec v)

variable {D}

theorem term_le {Ch Cg dist K : ℝ} {A : ℕ} {T T' : ℕ} {b : ℝ} (hK0 : 0 ≤ K) (X : BData D Ch Cg T T' b dist)
    (γ : Point D.host.E (D.R.rS + 1)) (hγ : IsBPt D T T' γ) (Wl : D.what₂.Tau → ℝ) (hWl : ∀ v, 0 ≤ Wl v)
    (hO : ∀ v, ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * Wl v) *
        orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≤
      ENNReal.ofReal (K * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) * jNorm2 (X.L v) (X.f v) (X.μsec v)) :
    ENNReal.ofReal (wPt D γ * ptWeightG D (rhoReal D) T T' γ.1 * ∏ v, Wl v) * JSqRot D X γ ≤
      ENNReal.ofReal (wPt D γ)⁻¹ * (ENNReal.ofReal (K ^ Fintype.card D.what₂.Tau) * jSqG D X) := by
  by_cases hJ : JSqRot D X γ = 0
  · simp [hJ]
  have hn := nLoc_nonneg D X γ hJ
  have hw := wPt_pos D γ
  have h1 : ENNReal.ofReal (wPt D γ * ptWeightG D (rhoReal D) T T' γ.1 * ∏ v, Wl v) =
      ENNReal.ofReal (wPt D γ)⁻¹ *
        ENNReal.ofReal (wPt D γ ^ 2 * ptWeightG D (rhoReal D) T T' γ.1 * ∏ v, Wl v) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hw.le)]
    congr 1
    field_simp
  have h2 : ENNReal.ofReal (wPt D γ ^ 2 * ptWeightG D (rhoReal D) T T' γ.1 * ∏ v, Wl v) * JSqRot D X γ =
      ∏ v, (ENNReal.ofReal (wLoc D v γ ^ 2 * nLoc D T T' v γ * Wl v) * orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ))) := by
    rw [Finset.prod_mul_distrib,
      ← ENNReal.ofReal_prod_of_nonneg (fun v _ => mul_nonneg (mul_nonneg (sq_nonneg _) (hn v)) (hWl v)),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, ← wPt_eq_prod, ← ptWeightG_eq_prod]
    rfl
  have hd1 : ∀ v, 0 ≤ (1 + dLoc D v γ) ^ A := fun v => pow_nonneg (by have := dLoc_nonneg D v γ; linarith) _
  have h3 : ∀ v, ENNReal.ofReal ((1 + dLoc D v γ) ^ A) *
      (ENNReal.ofReal (wLoc D v γ ^ 2 * nLoc D T T' v γ * Wl v) * orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ))) ≤
      ENNReal.ofReal (K * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) * jNorm2 (X.L v) (X.f v) (X.μsec v) := by
    intro v
    have := hO v
    rw [← mul_assoc, ← ENNReal.ofReal_mul (hd1 v)]
    convert this using 3
    ring
  have h4 : (∏ v, ENNReal.ofReal ((1 + dLoc D v γ) ^ A)) *
      (∏ v, (ENNReal.ofReal (wLoc D v γ ^ 2 * nLoc D T T' v γ * Wl v) * orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)))) ≤
      (∏ v, ENNReal.ofReal (K * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A)) *
        ∏ v, jNorm2 (X.L v) (X.f v) (X.μsec v) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' (fun v _ => h3 v)
  rw [← h2,
    ← ENNReal.ofReal_prod_of_nonneg (fun v _ => hd1 v),
    ← ENNReal.ofReal_prod_of_nonneg (fun v _ => mul_nonneg hK0 (pow_nonneg (le_max_of_le_left zero_le_one) _)),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at h4

  have hG0 : ∀ v, 0 < absV D v (Gglob D T T' γ) := fun v =>
    norm_pos_iff.2 ((map_ne_zero (plEmb D v)).2 hγ.2.1)
  have hE := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.integral_norm_application D.what₂.Tau (fun v => absV D v (Gglob D T T' γ))
    (fun v => plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) A hG0
    (prod_absV_ge_one D _ hγ.2.2 hγ.2.1) (fun v => absV_G_le D X γ hJ v)
  have hE' : ∏ v, max 1 (1 / absV D v (Gglob D T T' γ)) ^ A ≤ ∏ v, (1 + dLoc D v γ) ^ A := hE.1.trans hE.2
  set M : ℝ := ∏ v, (1 + dLoc D v γ) ^ A with hM
  have hM1 : 0 < M := Finset.prod_pos fun v _ => pow_pos (by have := dLoc_nonneg D v γ; linarith) _
  have h5 : ENNReal.ofReal M *
      (ENNReal.ofReal (wPt D γ ^ 2 * ptWeightG D (rhoReal D) T T' γ.1 * ∏ v, Wl v) * JSqRot D X γ) ≤
      ENNReal.ofReal M * (ENNReal.ofReal (K ^ Fintype.card D.what₂.Tau) * jSqG D X) := by
    refine h4.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul hM1.le]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left hE' (pow_nonneg hK0 _)
  have h6 := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hM1).ne' ENNReal.ofReal_ne_top).1 h5
  rw [h1, mul_assoc]
  exact mul_le_mul' le_rfl h6

theorem b_ge_of_StdHyp0 {Ch Cg : ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {u u' : Fin k → ℝ} {T T' ka b : ℝ} (hk : 1 ≤ k) (h : StdHyp0 Ch Cg k r ε lam u u' T T' ka b) :
    Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ b := by
  obtain ⟨-, hI, -, -, -, -, -, -, -, -, hlam, -, -, -, -, ⟨bv, hbv, hSh⟩, -⟩ := h
  have hk0 : 0 < k := hk
  have hnode : ∀ i : Fin k, lam ⟨k - 1, by omega⟩ < u i := by
    obtain ⟨h1, h2⟩ := hI
    have step : ∀ (i : ℕ) (hi : i + 1 < k), u ⟨i + 1, hi⟩ < u ⟨i, by omega⟩ :=
      fun i hi => (h1 i hi).2.trans (h1 i hi).1
    have key : ∀ d : ℕ, ∀ (i : ℕ) (hi : i < k), i + d = k - 1 → u ⟨k - 1, by omega⟩ ≤ u ⟨i, hi⟩ := by
      intro d
      induction d with
      | zero =>
        intro i hi hd
        simp only [add_zero] at hd
        subst hd
        exact le_rfl
      | succ d ih =>
        intro i hi hd
        have hi1 : i + 1 < k := by omega
        exact (ih (i + 1) hi1 (by omega)).trans (step i hi1).le
    intro i
    have hi' := i.2
    exact (h2 hk0).trans_le (key (k - 1 - i.val) i.val i.2 (by omega))
  have hnc : ¬ IsCloud u lam ⟨k - 1, by omega⟩ := fun hc => by
    obtain ⟨i, hi⟩ := hc.2
    exact lt_asymm hi (hnode i)
  have h2 := ((hSh ⟨k - 1, by omega⟩).2 hnc).2
  have h3 := hlam ⟨k - 1, by omega⟩
  have h4 := neg_abs_le (lam ⟨k - 1, by omega⟩)
  linarith

theorem arith_B {b CK : ℝ} (r f e : ℕ) (he : 1 ≤ e) (hb : 2 ≤ b) :
    (64 : ℝ) ^ (f * (r + 1)) * (b ^ (CK * ((2 * r + 2 : ℕ) : ℝ) ^ e)) ^ f ≤
      Real.exp ((CK + 6) * ((2 * r + 2 : ℕ) : ℝ) ^ e * (f : ℝ) * Real.log b) := by
  have hb0 : (0:ℝ) < b := by linarith
  have hlb : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have h1 : (1:ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * r + 2 by omega)
  have hM : (r:ℝ) + 1 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ e := by
    calc (r:ℝ) + 1 ≤ ((2 * r + 2 : ℕ) : ℝ) := by
          push_cast
          linarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
      _ = ((2 * r + 2 : ℕ) : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ ((2 * r + 2 : ℕ) : ℝ) ^ e := pow_le_pow_right₀ h1 he
  have hf : (0:ℝ) ≤ f := Nat.cast_nonneg f
  set M := ((2 * r + 2 : ℕ) : ℝ) ^ e with hMdef
  rw [← Real.rpow_natCast (64:ℝ) (f * (r + 1)), Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 64),
    ← Real.rpow_natCast (b ^ (CK * M)) f, ← Real.rpow_mul hb0.le, Real.rpow_def_of_pos hb0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, h64]
  have key : 6 * Real.log 2 * ((f:ℝ) * ((r:ℝ) + 1)) ≤ 6 * Real.log b * ((f:ℝ) * M) :=
    mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hM hf) (by positivity) (by linarith)
  linarith [key]

theorem BSum_le_of_onePlace {Ch Cg dist CK p : ℝ} {P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop}
    {A e : ℕ} (hCg : 2 ≤ Cg) (he : 1 ≤ e) (hO : OnePlace D Ch Cg dist P A CK e p)
    (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist) (hP : P T T' b X) :
    BSumRot D X (fun γ => normWt D T T' γ ^ p) ≤
      ENNReal.ofReal (Real.exp ((CK + 6) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e * (Fintype.card D.what₂.Tau : ℝ) *
        Real.log b)) * jSqG D X := by
  let v0 : D.what₂.Tau := D.eTau.symm 1
  obtain ⟨hk, -, -, -, -, hStd, -, -⟩ := X.hL v0
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  have hka : (0 : ℝ) < kaRe D := hStd.2.2.2.1
  have hone : (kaRe D / kaRe D) ^ (2 * D.R.rS) = 1 := by rw [div_self hka.ne', one_pow]
  have hT1 : 1 ≤ T := by
    have := hStd.2.2.2.2.2.2.1
    rw [hone, mul_one, (X.hT v0).1] at this
    exact_mod_cast this
  have hT1' : 1 ≤ T' := by
    have := hStd.2.2.2.2.2.2.2.1
    rw [hone, mul_one, (X.hT v0).2] at this
    exact_mod_cast this
  have h1 : BSumRot D X (fun γ => normWt D T T' γ ^ p) ≤
      ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ}, ENNReal.ofReal (wPt D γ.1)⁻¹ *
        (ENNReal.ofReal ((b ^ (CK * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e)) ^ Fintype.card D.what₂.Tau) * jSqG D X) := by
    unfold BSumRot
    refine ENNReal.tsum_le_tsum fun γ => ?_
    have hW : (fun γ => normWt D T T' γ ^ p) γ.1 = ∏ v, WLoc D T T' v γ.1 ^ p := normWt_rpow D T T' γ.1 p
    rw [hW]
    exact term_le (Real.rpow_nonneg (by linarith) _) X γ.1 γ.2 _
      (fun v => Real.rpow_nonneg (WLoc_nonneg D T T' v γ.1) _) (fun v => hO T T' b X hP γ.1 γ.2 v)
  rw [ENNReal.tsum_mul_right] at h1
  refine h1.trans ?_
  refine (mul_le_mul' (theorem_B_second_bound_64 D T T' hT1 hT1') le_rfl).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (arith_B D.R.rS _ e he hb2)) le_rfl


theorem theorem_B_weighted_bound_one_place {Aw Ch Cg CK : ℝ} {A : ℕ} (hCg : 2 ≤ Cg)
    (hO : OnePlace D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) A CK 5
      (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) : Formalism.MainNotions.OnePlaceEstimates.ConclusionB3 D Aw Ch Cg (CK + 6) := by
  intro T T' b X hG
  exact BSum_le_of_onePlace hCg (by norm_num) hO T T' b X hG


end ThmB

end Formalism.MainNotions.BesselShellMomentBounds

end PieceB1

section PieceA

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def AdmOpen (D : D7) (Gm : GM) (CB Co Cd C0 CA Cg₁ Cg₂ c C₁ : ℝ) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Cg Cq : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D ∧ adm3a D ∧ RTTRelation D ∧ adm5 D ∧ adm6 D ∧ adm7 D CB Co Cd ∧ DualityForLists D ∧ adm9 D CB ∧ adm10 D C0 CA ∧
    adm11 D Cg₁ Cg₂ ∧ adm12 D CB ∧ adm13 D Gm Ks E₀ Eg E₁ E₂ ∧ adm15 D Gm Ks E₀ Eg E₁ E₂ ∧ adm17 D Gm Ks E₀ Eg E₁ E₂ E₃ ∧
    ShortGridGramBound D Gm CB Cs ∧ LiftGridGramBound D Gm CB Cs ∧ LargeBlockGridBound D Gm CB Cs C₃ ∧ UniformGridGramBound D Gm CB Cs C₃ ∧
    adm18 D ∧ DualTranslationPrinciple D ∧ adm19 D ∧ adm20 D ∧ adm21 D c C₁ ∧ adm22 D Ch Cg Cq ∧ CapelliEigenvalueAlt D


end Formalism.MainNotions.BesselShellMomentBounds

end PieceA

section PieceE92

open Finset

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.P Formalism.MainNotions.S.Pv.Frames


def wordOf {ι : Type} (ls : List ι) (α : ι → ℕ) : List ι := ls.flatMap fun l => List.replicate (α l) l




def mulOp {X W : Type} [AddCommGroup W] [Module ℂ W] (φ : X → ℂ) : Module.End ℂ (X → W) where
  toFun F := fun q => φ q • F q
  map_add' F G := by ext q; simp
  map_smul' c F := by
    funext q
    show φ q • (c • F q) = c • (φ q • F q)
    exact smul_comm _ _ _


def nat1 {n : ℕ} (ν : Fin n → ℤ) : ℕ := ∑ s, (ν s).natAbs



def FamilyDerivativeExpansion (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ)
    (Hν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Type) [∀ ν, NormedAddCommGroup (Hν ν)]
    [∀ ν, InnerProductSpace ℂ (Hν ν)] [∀ ν, CompleteSpace (Hν ν)]
    (σν : ∀ ν, Mx D.R.k D.R.rS → (Hν ν →L[ℂ] Hν ν)) (fν : ∀ _ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → Formalism.MainNotions.OnePlaceEstimates.GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    (∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
      IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) (σν ν) ∧ IsKFinCoefH (σν ν) (fν ν) ∧
      (jNorm2 L (fν ν) μsec = 1 ∨
        ((∀ q : (Fin D.R.rS → ℂ) × ℂ, Formalism.MainNotions.OnePlaceEstimates.InBig L q → L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH (σν ν) f' →
            ∀ q : (Fin D.R.rS → ℂ) × ℂ, Formalism.MainNotions.OnePlaceEstimates.InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))) →
    ∀ (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℤ) (l : Fin (D.R.rS + 1)),
      ∑ s, |(μ s : ℝ)| + ((l : ℕ) + 1 : ℕ) ≤ ((D.R.rS + 1) * p : ℕ) →
      ∃ a : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) →₀ ℂ,
        (∀ ν ∈ a.support, ∑ s, |(ν s : ℝ)| ≤ ((l : ℕ) + 1 : ℕ)) ∧
        (a.sum fun _ c => ‖c‖) ≤ b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) ∧
        ∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
          Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' < Complex.normSq q.2 →
          Dbig ((l : ℕ) + 1) q • L.J (fν μ) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) =
            a.sum fun ν c => c • L.J (fν (μ + ν)) (bigCell D.R.k D.R.rS q.1 (μsec q.2))




end Formalism.MainNotions.BesselShellMomentBounds

end PieceE92

noncomputable section PieceN92

open MeasureTheory Finset
open scoped InnerProductSpace

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.Frames

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsNormSq_eq (A : Wq →L[ℂ] Wp) : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (A (stdOrthonormalBasis ℂ Wq i))
  rw [RCLike.re_to_complex] at h
  exact h

theorem hsNormSq_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq]
  positivity

theorem hsNormSq_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : hsNormSq (c • A) = ‖c‖ ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq, hsNormSq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smul_apply, norm_smul, mul_pow]

theorem norm_sum_sq_le {ι : Type} (s : Finset ι) (a : ι → ℂ) (v : ι → Wp) :
    ‖∑ i ∈ s, a i • v i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖) * ∑ i ∈ s, ‖a i‖ * ‖v i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, a i • v i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖v i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt ‖a i‖) (fun i => Real.sqrt ‖a i‖ * ‖v i‖)
  have e1 : ∀ i, Real.sqrt ‖a i‖ * (Real.sqrt ‖a i‖ * ‖v i‖) = ‖a i‖ * ‖v i‖ := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  have e2 : ∀ i, Real.sqrt ‖a i‖ ^ 2 = ‖a i‖ := fun i => Real.sq_sqrt (norm_nonneg _)
  have e3 : ∀ i, (Real.sqrt ‖a i‖ * ‖v i‖) ^ 2 = ‖a i‖ * ‖v i‖ ^ 2 := fun i => by rw [mul_pow, e2]
  simp only [e1, e2, e3] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem hsNormSq_sum_le {ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → (Wq →L[ℂ] Wp)) :
    hsNormSq (∑ i ∈ s, a i • x i) ≤ (∑ i ∈ s, ‖a i‖) * ∑ i ∈ s, ‖a i‖ * hsNormSq (x i) := by
  simp_rw [hsNormSq_eq]
  calc ∑ j, ‖(∑ i ∈ s, a i • x i) (stdOrthonormalBasis ℂ Wq j)‖ ^ 2
      = ∑ j, ‖∑ i ∈ s, a i • x i (stdOrthonormalBasis ℂ Wq j)‖ ^ 2 := by
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    _ ≤ ∑ j, (∑ i ∈ s, ‖a i‖) * ∑ i ∈ s, ‖a i‖ * ‖x i (stdOrthonormalBasis ℂ Wq j)‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => norm_sum_sq_le _ _ _)
    _ = (∑ i ∈ s, ‖a i‖) * ∑ i ∈ s, ‖a i‖ * ∑ j, ‖x i (stdOrthonormalBasis ℂ Wq j)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]

end HS

section Loc

variable {k r : ℕ}

theorem J_smul (L : LocBessel k r) (c : ℂ) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) :
    L.J (fun x => c • F x) g = c • L.J F g := by
  unfold LocBessel.J besselJ
  rw [← integral_smul]
  congr 1
  funext p
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [smul_comm]

theorem coef_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : LocBessel k r)
    (σ : Mx k r → (H →L[ℂ] H)) (c : ℂ) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (h : IsKFinCoefH σ f) :
    IsKFinCoefH σ (fun x => c • f x) := by
  obtain ⟨P, Q, hQ, hP, hf⟩ := h
  refine ⟨P, c • Q, ?_, hP, ?_⟩
  · intro w
    obtain ⟨S, h1, h2, h3⟩ := hQ w
    exact ⟨S, h1, S.smul_mem c h2, h3⟩
  · intro g
    show c • f g = _
    rw [hf g]
    simp only [ContinuousLinearMap.comp_smul]

theorem bcWeight_nonneg (T T' : ℝ) (p : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' p := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

theorem bcWeight_off (hk : 2 ≤ k) (T T' : ℝ) (p : (Fin r → ℂ) × ℂ)
    (h : ¬ ((∀ i, p.1 i ≠ 0) ∧ T * T' < Complex.normSq p.2)) : bcWeight k r T T' p = 0 := by
  unfold bcWeight
  split_ifs with h1
  · by_cases h2 : ∀ i, p.1 i ≠ 0
    · have h3 : Complex.normSq p.2 = T * T' := le_antisymm (not_lt.1 fun h4 => h ⟨h2, h4⟩) h1
      rw [h3, sub_self, zero_pow (by omega), mul_zero]
    · obtain ⟨i, hi⟩ := not_forall.1 h2
      have hi : p.1 i = 0 := not_not.1 hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i), zero_mul]
      rw [hi, norm_zero, zero_pow]
      have := i.2
      unfold Mdim
      omega
  · rfl

def dens (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (p : (Fin r → ℂ) × ℂ) : ℝ :=
  bcWeight k r (Tz k r L.z) (Tz k r L.z') p * hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))

theorem dens_nonneg (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec) (p) : 0 ≤ dens L F μsec p := by
  unfold dens
  exact mul_nonneg (bcWeight_nonneg _ _ _) (hsNormSq_nonneg _)


theorem jNorm2_eq (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec) :
    jNorm2 L F μsec = ∫⁻ p, ENNReal.ofReal (dens L F μsec p) := by
  unfold Formalism.MainNotions.S.ThB.jNorm2 Formalism.QuantumDeterminants.jNormSq dens
  congr 1
  funext p
  congr 1
  try beta_reduce
  rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hsNormSq_nonneg _)]

theorem dens_smul (L : LocBessel k r) (c : ℂ) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec) (p) :
    dens L (fun x => c • F x) μsec p = ‖c‖ ^ 2 * dens L F μsec p := by
  unfold dens
  rw [J_smul, hsNormSq_smul]
  ring


theorem jNorm2_smul (L : LocBessel k r) (c : ℂ) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec) :
    jNorm2 L (fun x => c • F x) μsec = ENNReal.ofReal (‖c‖ ^ 2) * jNorm2 L F μsec := by
  rw [jNorm2_eq, jNorm2_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext p
  rw [dens_smul, ENNReal.ofReal_mul (sq_nonneg _)]

end Loc

def JMeas (D : D7) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H))
    (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    IsSection D.R.k D.R.rS L.z L.z' μsec → IsDSHpk D.R.k D.R.rS L.ε lam' σ → IsKFinCoefH σ f →
    Measurable (dens L f μsec)

def ExFam (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ)
    (f0 : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → Formalism.MainNotions.OnePlaceEstimates.GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec → IsKFinCoefH L.σ f0 → jNorm2 L f0 μsec = 1 →
    ∃ (Hν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Type) (_ : ∀ ν, NormedAddCommGroup (Hν ν))
      (_ : ∀ ν, InnerProductSpace ℂ (Hν ν)) (_ : ∀ ν, CompleteSpace (Hν ν))
      (σν : ∀ ν, Mx D.R.k D.R.rS → (Hν ν →L[ℂ] Hν ν)) (fν : ∀ _ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
        Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)), fν 0 = f0 ∧
      ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
        IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) (σν ν) ∧ IsKFinCoefH (σν ν) (fν ν) ∧
        (jNorm2 L (fν ν) μsec = 1 ∨
          ((∀ q : (Fin D.R.rS → ℂ) × ℂ, Formalism.MainNotions.OnePlaceEstimates.InBig L q → L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
            ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH (σν ν) f' →
              ∀ q : (Fin D.R.rS → ℂ) × ℂ, Formalism.MainNotions.OnePlaceEstimates.InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))



end Formalism.MainNotions.BesselShellMomentBounds

end PieceN92

noncomputable section PieceM93

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

set_option linter.unusedVariables false

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.S.Pv.Frames

def CloudNodeShape (D : D7) (Ch Cg : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b bv : ℝ) (Bf : L.Hs → L.Wp) (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) (w : L.Hs)
    (j : ℕ) : Prop :=
  LocOk0 D Ch Cg L lam0 ka b ka ∧
    Cg * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧ ShapeS L.u lam0 bv ∧
    IsBesselMapSm L.z (psi D.R.k D.R.rS L.z L.c) L.σ L.π Bf ∧
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG ∧ IsHaarOn (Sset D.R.k D.R.rS L.z) μS ∧ IsQuotMeas μG μS νq ∧
    (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) L.σ, l2SG νq (fun g => Bf (L.σ g v)) = (‖v‖₊ : ENNReal) ^ 2) ∧
    IsCayleyU D.R.k D.R.rS L.ε P ∧ w ∈ shell L P j ∧ w ≠ 0

def H1 (D : D7) (C2 b ka : ℝ) : ℝ :=
  b ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * (1 + 1 / ka) ^ (2 * D.R.rS + 2)

def la (D : D7) (L : LocBessel D.R.k D.R.rS) (a : Fin (D.R.rS + 1)) (g : Mx D.R.k D.R.rS) : ℝ :=
  lA D.R.k D.R.rS L.z g a

def ShellMomentBound (D : D7) (Ch Cg Cq C1 C2 : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (Bf : L.Hs → L.Wp)
    (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) (w : L.Hs) (j : ℕ),
    CloudNodeShape D Ch Cg L lam0 ka b bv Bf μG μS νq P w j →
    ∀ q : ℕ, l1 L.lam lam0 + (q : ℝ) ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0 →
      (j : ℝ) + 2 * q ≤ bv / (C1 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2) →
      Emom L Bf νq w (fun g => ENNReal.ofReal (la D L 0 g ^ (2 * q))) ≤ ENNReal.ofReal (H1 D C2 b ka ^ (2 * q))

def ShellEnergyBound (D : D7) (Ch Cg Cq C1 : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (Bf : L.Hs → L.Wp)
    (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) (w : L.Hs) (j : ℕ),
    CloudNodeShape D Ch Cg L lam0 ka b bv Bf μG μS νq P w j →
    l1 L.lam lam0 ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0 →
    ∀ (q : ℕ) (a : ℕ) (ha : a < D.R.rS),
      Emom L Bf νq w (fun g => ENNReal.ofReal ((la D L ⟨a + 1, by omega⟩ g / la D L ⟨a, by omega⟩ g) ^ (2 * q))) ≤
        ENNReal.ofReal ((C1 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 * (b + j + q) / ka) ^ (2 * q))

def ShellLowestCoordinateBound (D : D7) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS), ∀ g ∈ UH (Hpk D.R.k D.R.rS),
    Tz D.R.k D.R.rS L.z ≤ la D L (Fin.last D.R.rS) g ^ 2

def ShellTailBound (D : D7) (Ch Cg Cq C1 C2 : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (Bf : L.Hs → L.Wp)
    (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) (w : L.Hs) (j : ℕ),
    CloudNodeShape D Ch Cg L lam0 ka b bv Bf μG μS νq P w j →
    ∀ q : ℕ, l1 L.lam lam0 + (((2 * D.R.rS + 2) * q : ℕ) : ℝ) ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0 →
      (((2 * D.R.rS + 2) * q + j : ℕ) : ℝ) ≤ bv / (C1 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 4) →
      (∀ a : Fin (D.R.rS + 1),
        Emom L Bf νq w (fun g => ENNReal.ofReal (la D L a g ^ (2 * q))) ≤ ENNReal.ofReal (H1 D C2 b ka ^ (2 * q)) ∧
        Emom L Bf νq w (fun g => ENNReal.ofReal ((la D L a g)⁻¹ ^ (2 * q))) ≤
          ENNReal.ofReal (H1 D C2 b ka ^ (2 * q))) ∧
      ∀ lam' : ℝ, 0 < lam' →
        Emom L Bf νq w
            (Set.indicator {g | ∃ a : Fin (D.R.rS + 1), lam' * H1 D C2 b ka ≤ max (la D L a g) (la D L a g)⁻¹} 1) ≤
          ENNReal.ofReal (2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) * lam' ^ (-(2 * (q : ℝ))))

def ShellCommonHypotheses (D : D7) (Ch Cg : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b bv : ℝ) (Bf : L.Hs → L.Wp) (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) : Prop :=
  LocOk0 D Ch Cg L lam0 ka b ka ∧
    Cg * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧ ShapeS L.u lam0 bv ∧
    IsBesselMapSm L.z (psi D.R.k D.R.rS L.z L.c) L.σ L.π Bf ∧
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG ∧ IsHaarOn (Sset D.R.k D.R.rS L.z) μS ∧ IsQuotMeas μG μS νq ∧
    (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) L.σ, l2SG νq (fun g => Bf (L.σ g v)) = (‖v‖₊ : ENNReal) ^ 2) ∧
    IsCayleyU D.R.k D.R.rS L.ε P

def LowestKTypeRightInvariant (D : D7) (Ch Cg : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (Bf : L.Hs → L.Wp)
    (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) (w : L.Hs),
    ShellCommonHypotheses D Ch Cg L lam0 ka b bv Bf μG μS νq P →
    w ∈ lowKSub L.ε L.lam (fun g => L.σ (P⁻¹ * g * P)) → w ≠ 0 →
    ∃ w0 ∈ shell L P 0, w0 ≠ 0 ∧ ∀ Φ : (Fin (D.R.rS + 1) → ℝ) → ENNReal, Measurable Φ →
      Emom L Bf νq w (fun g => Φ (fun a => la D L a g)) = Emom L Bf νq w0 (fun g => Φ (fun a => la D L a g))



section Geometry

variable {k r : ℕ}

local notation "NN" => 2 * r + k + 1

def yv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a : Fin (r + 1)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
  WithLp.toLp 2 (g⁻¹ *ᵥ fvec k r z a)

def thetaH (k r : ℕ) : EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
  Matrix.toEuclideanLin (Hpk k r)

theorem Hpk_sq' (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  exact (hpkFacts k r).2.1
theorem Hpk_herm' (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  exact (hpkFacts k r).1

theorem thetaH_isTheta (k r : ℕ) : Formalism.HermitianLatticeCounting.ExpansionTerms.IsSelfAdjointInvolution (thetaH k r) := by
  constructor
  · intro x
    show WithLp.toLp 2 (Hpk k r *ᵥ (Hpk k r *ᵥ WithLp.ofLp x)) = x
    rw [mulVec_mulVec, Hpk_sq', one_mulVec]
  · intro x y
    have h : (Matrix.toEuclideanLin (Hpk k r)).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (Hpk_herm' k r)
    exact h x y

theorem form_eq_herm (k r : ℕ) (u v : Fin (2 * r + k + 1) → ℂ) :
    Formalism.HermitianLatticeCounting.ExpansionTerms.majorantHermitianForm (thetaH k r) (WithLp.toLp 2 u) (WithLp.toLp 2 v) = herm (Hpk k r) u v := by
  show inner ℂ (WithLp.toLp 2 (Hpk k r *ᵥ v) : EuclideanSpace ℂ (Fin (2 * r + k + 1))) (WithLp.toLp 2 u) = _
  rw [EuclideanSpace.inner_toLp_toLp, ggHerm_swap _ (Hpk_herm' k r), herm, star_dotProduct, star_star, dotProduct_comm]

theorem eucl_eq_norm {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucl, Complex.normSq_eq_norm_sq]

theorem len_le_lA (z : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a : Fin (r + 1)) : Formalism.HermitianLatticeCounting.ExpansionTerms.majorantDistance (yv k r z g) a ≤ lA k r z g a := by
  unfold lA
  apply le_csInf
  · exact ⟨_, 0, Submodule.zero_mem _, rfl⟩
  · rintro t ⟨y, hy, rfl⟩
    have hmem : (WithLp.toLp 2 (g⁻¹ *ᵥ y) : EuclideanSpace ℂ (Fin (2 * r + k + 1))) ∈
        (Submodule.span ℂ (yv k r z g '' {b | b < a}) : Set (EuclideanSpace ℂ (Fin (2 * r + k + 1)))) := by
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        apply Submodule.subset_span
        refine ⟨⟨b.1.val, by have := b.1.isLt; omega⟩, ?_, ?_⟩
        · show (⟨b.1.val, _⟩ : Fin (r + 1)) < a
          exact b.2
        · simp only [yv, fvec]
          rw [dif_pos b.1.isLt]
      | zero => simp only [mulVec_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ c hx
    have := Metric.infDist_le_dist_of_mem (x := yv k r z g a) hmem
    refine le_trans this (le_of_eq ?_)
    rw [dist_eq_norm, eucl_eq_norm, mulVec_sub]
    rfl

theorem herm_fvec (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z a) (fvec k r z b) =
      if a = Fin.last r ∧ b = Fin.last r then -((Tz k r z : ℝ) : ℂ) else 0 := by
  have hsw := fun u v => ggHerm_swap (Hpk k r) (Hpk_herm' k r) u v
  have hze : ∀ c : Fin r, herm (Hpk k r) z (bvec (eI k r c)) = 0 := by
    intro c
    rw [bvec, ggHerm_bvec_right, ggHpk_mulVec_Wb k r z hz, hz _ (Or.inl c.isLt), mul_zero]
  by_cases ha : (a : ℕ) < r
  · have ha' : a ≠ Fin.last r := by
      intro h; rw [h] at ha; simp at ha
    rw [if_neg (fun h => ha' h.1)]
    by_cases hb : (b : ℕ) < r
    · simp only [fvec, dif_pos ha, dif_pos hb]
      rw [bvec, bvec, ggHerm_bvec_right]
      simp [mulVec_single, ggHpk_ee]
    · simp only [fvec, dif_pos ha, dif_neg hb]
      rw [hsw, hze, star_zero]
  · have ha' : a = Fin.last r := by
      apply Fin.ext; have := a.isLt; simp only [Fin.val_last]; omega
    by_cases hb : (b : ℕ) < r
    · have hb' : b ≠ Fin.last r := by
        intro h; rw [h] at hb; simp at hb
      rw [if_neg (fun h => hb' h.2)]
      simp only [fvec, dif_neg ha, dif_pos hb]
      exact hze _
    · have hb' : b = Fin.last r := by
        apply Fin.ext; have := b.isLt; simp only [Fin.val_last]; omega
      rw [if_pos ⟨ha', hb'⟩]
      simp only [fvec, dif_neg ha, dif_neg hb, Tz]
      have him : (herm (Hpk k r) z z).im = 0 := by
        have := hsw z z
        exact Complex.conj_eq_iff_im.mp this.symm
      apply Complex.ext <;> simp [him]

theorem T_le_lA_sq (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r)) :
    Tz k r z ≤ lA k r z g (Fin.last r) ^ 2 := by
  have hdet : IsUnit (Hpk k r).det := by
    have := congrArg Matrix.det (Hpk_sq' k r)
    rw [det_mul, det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  have hginv : g⁻¹ ∈ UH (Hpk k r) := ((unitary_group_holds _ (Hpk k r) hdet).2.2 g hg).2
  have hcore := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.majorant_lower_bound (EuclideanSpace ℂ (Fin (2 * r + k + 1))) (thetaH k r)
    (thetaH_isTheta k r) r (yv k r z g) (Tz k r z) (by
      intro a b
      rw [yv, yv, form_eq_herm, ggHerm_unitary _ _ hginv, herm_fvec z hz])
  refine le_trans hcore ?_
  have h0 : 0 ≤ Formalism.HermitianLatticeCounting.ExpansionTerms.majorantDistance (yv k r z g) (Fin.last r) := Metric.infDist_nonneg
  exact pow_le_pow_left₀ h0 (len_le_lA z g _) 2

end Geometry

theorem majorant_ge_lowest_coordinate_sq (D : D7) : ShellLowestCoordinateBound D := by
  intro L g hg
  exact T_le_lA_sq L.z L.hz.1 g hg

section Meas

variable {k r : ℕ}

theorem Hpk_det_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  exact isUnit_iff_exists_inv.mpr ⟨_, by rw [← Matrix.det_mul, Hpk_sq', Matrix.det_one]⟩

theorem lA_nonneg (z : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a : Fin (r + 1)) : 0 ≤ lA k r z g a :=
  le_trans Metric.infDist_nonneg (len_le_lA z g a)

theorem lA_pos (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r)) (a : Fin (r + 1)) :
    0 < lA k r z g a := by
  by_cases ha : (a : ℕ) < r
  · refine lt_of_lt_of_le ?_ (len_le_lA z g a)
    have hgu : IsUnit g.det := ((unitary_group_holds _ (Hpk k r) (Hpk_det_unit k r)).2.2 g hg).1
    have hcl : IsClosed (Submodule.span ℂ (yv k r z g '' {b | b < a}) :
        Set (EuclideanSpace ℂ (Fin (2 * r + k + 1)))) := Submodule.closed_of_finiteDimensional _
    refine (hcl.notMem_iff_infDist_pos ⟨0, Submodule.zero_mem _⟩).mp ?_
    intro hmem
    have key : ∀ x ∈ Submodule.span ℂ (yv k r z g '' {b | b < a}),
        (g *ᵥ WithLp.ofLp x) (eI k r ⟨a, ha⟩) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, rfl⟩ := hx
        have hb' : (b : ℕ) < a := hb
        have hbr : (b : ℕ) < r := by omega
        show (g *ᵥ (g⁻¹ *ᵥ fvec k r z b)) _ = 0
        rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hgu, one_mulVec]
        simp only [fvec, dif_pos hbr, bvec]
        rw [Pi.single_apply, if_neg]
        intro h
        have := congrArg Fin.val h
        simp only [eI] at this
        omega
      | zero => simp
      | add x y _ _ hx hy =>
        show (g *ᵥ (WithLp.ofLp x + WithLp.ofLp y)) _ = 0
        rw [mulVec_add, Pi.add_apply, hx, hy, add_zero]
      | smul c x _ hx =>
        show (g *ᵥ (c • WithLp.ofLp x)) _ = 0
        rw [mulVec_smul, Pi.smul_apply, hx, smul_zero]
    have h1 := key _ hmem
    have h2 : (g *ᵥ WithLp.ofLp (yv k r z g a)) (eI k r ⟨a, ha⟩) = 1 := by
      show (g *ᵥ (g⁻¹ *ᵥ fvec k r z a)) _ = 1
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hgu, one_mulVec]
      simp only [fvec, dif_pos ha, bvec]
      rw [Pi.single_apply, if_pos rfl]
    rw [h1] at h2
    exact zero_ne_one h2
  · have ha' : a = Fin.last r := by
      apply Fin.ext; have := a.isLt; simp only [Fin.val_last]; omega
    subst ha'
    have h := T_le_lA_sq z hz g hg
    have h0 := lA_nonneg z g (Fin.last r)
    rcases h0.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1] at h; norm_num at h; linarith

theorem continuous_eucl {N : ℕ} : Continuous (eucl : (Fin N → ℂ) → ℝ) := by
  unfold eucl
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ (fun i _ => Complex.continuous_normSq.comp (continuous_apply i)))

theorem measurable_lA (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    Measurable (fun x : Mt k r => lA k r z (Matrix.of x) a) := by
  apply measurable_of_Iio
  intro c
  set S := Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} => bvec (eI k r b.1)) with hS
  set U : Set (Mt k r) := {x | (Matrix.of x).det ≠ 0} with hU
  have hdetc : Continuous (fun x : Mt k r => (Matrix.of x).det) :=
    Continuous.matrix_det (continuous_id : Continuous fun x : Mt k r => (x : Matrix _ _ ℂ))
  have hUo : IsOpen U := isOpen_ne_fun hdetc continuous_const
  have hset : (fun x : Mt k r => lA k r z (Matrix.of x) a) ⁻¹' Set.Iio c =
      (⋃ y ∈ S, U ∩ (fun x : Mt k r => eucl ((Matrix.of x)⁻¹ *ᵥ (fvec k r z a - y))) ⁻¹' Set.Iio c) ∪
        (Uᶜ ∩ {x | 0 < c}) := by
    ext x
    have hlt : lA k r z (Matrix.of x) a < c ↔ ∃ y ∈ S, eucl ((Matrix.of x)⁻¹ *ᵥ (fvec k r z a - y)) < c := by
      unfold lA
      rw [csInf_lt_iff]
      · constructor
        · rintro ⟨t, ⟨y, hy, rfl⟩, ht⟩; exact ⟨y, hy, ht⟩
        · rintro ⟨y, hy, ht⟩; exact ⟨_, ⟨y, hy, rfl⟩, ht⟩
      · refine ⟨0, ?_⟩
        rintro t ⟨y, hy, rfl⟩
        exact Real.sqrt_nonneg _
      · exact ⟨_, 0, Submodule.zero_mem _, rfl⟩
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_ofPred_eq, exists_prop]
    rw [hlt]
    by_cases hx : x ∈ U
    · simp [hx]
    · have hx' : ¬ IsUnit (Matrix.of x).det := by
        intro h; exact hx h.ne_zero
      have hinv : (Matrix.of x)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hx'
      simp only [hx, false_and, and_false, exists_false, not_false_eq_true, true_and, false_or, hinv, zero_mulVec]
      have h0 : eucl (0 : Fin (2 * r + k + 1) → ℂ) = 0 := by simp [eucl]
      rw [h0]
      constructor
      · rintro ⟨_, _, h⟩; exact h
      · intro h; exact ⟨0, Submodule.zero_mem _, h⟩
  rw [hset]
  refine MeasurableSet.union (IsOpen.measurableSet ?_) (hUo.measurableSet.compl.inter (MeasurableSet.const _))
  refine isOpen_biUnion fun y _ => ?_
  refine ContinuousOn.isOpen_inter_preimage ?_ hUo isOpen_Iio
  refine continuous_eucl.comp_continuousOn ?_
  have hinv : ContinuousOn (fun x : Mt k r => (Matrix.of x)⁻¹) U := by
    have h1 : ∀ x : Mt k r, (Matrix.of x)⁻¹ = ((Matrix.of x).det)⁻¹ • (Matrix.of x).adjugate := by
      intro x; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp only [h1]
    refine ContinuousOn.smul (hdetc.continuousOn.inv₀ fun x hx => hx) ?_
    exact (Continuous.matrix_adjugate (continuous_id : Continuous fun x : Mt k r => (x : Matrix _ _ ℂ))).continuousOn
  exact (Continuous.matrix_mulVec (continuous_id : Continuous fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M)
    continuous_const).comp_continuousOn hinv

theorem measurableSet_UH (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x)ᴴ * Hpk k r * Matrix.of x) := by
    have hid : Continuous fun x : Mt k r => (x : Matrix _ _ ℂ) := continuous_id
    exact (hid.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hid
  exact (isClosed_eq hc continuous_const).measurableSet

theorem Sset_sub_UH (z : Fin (2 * r + k + 1) → ℂ) {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ Sset k r z) : s ∈ UH (Hpk k r) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact (unitary_group_holds _ (Hpk k r) (Hpk_det_unit k r)).2.1 h hh.1 m hm.1

theorem quot_conc (z : Fin (2 * r + k + 1) → ℂ) (μG μS νq : Measure (Mt k r))
    (hG : IsHaarOn (UH (Hpk k r)) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS νq) :
    νq {x | Matrix.of x ∉ UH (Hpk k r)} = 0 := by
  set A : Set (Mt k r) := {x | Matrix.of x ∉ UH (Hpk k r)} with hA
  have hAm : MeasurableSet A := (measurableSet_UH k r).compl
  have h := hq (A.indicator 1) (measurable_one.indicator hAm)
  rw [lintegral_indicator_one hAm, hG.2.2.1] at h
  have hc : μS Set.univ ≠ 0 := by
    intro h0; exact hS.2.1 (Measure.measure_univ_eq_zero.mp h0)
  have hle : ∫⁻ x, A.indicator (fun _ => μS Set.univ) x ∂νq ≤
      ∫⁻ x, (∫⁻ s, A.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have : ∫⁻ s, A.indicator (1 : Mt k r → ENNReal) (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS =
          ∫⁻ s, 1 ∂μS := by
        refine lintegral_congr_ae ?_
        have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
          rw [ae_iff]; exact hS.2.2.1
        filter_upwards [hae] with s hs
        have hsU := Sset_sub_UH z hs
        rw [Set.indicator_of_mem]
        · rfl
        · show ¬ ((Matrix.of s * Matrix.of x) ∈ UH (Hpk k r))
          intro hsx
          apply hx
          have e1 : (Matrix.of s * Matrix.of x)ᴴ * Hpk k r * (Matrix.of s * Matrix.of x) = Hpk k r := hsx
          have e2 : (Matrix.of s)ᴴ * Hpk k r * Matrix.of s = Hpk k r := hsU
          show (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r
          calc (Matrix.of x)ᴴ * Hpk k r * Matrix.of x
              = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Hpk k r * Matrix.of s) * Matrix.of x := by rw [e2]
            _ = (Matrix.of s * Matrix.of x)ᴴ * Hpk k r * (Matrix.of s * Matrix.of x) := by
                rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
            _ = Hpk k r := e1
      rw [this, lintegral_one]
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [← h, lintegral_indicator_const hAm] at hle
  have : μS Set.univ * νq A = 0 := le_antisymm hle (zero_le)
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hc
  · exact h1

end Meas

section Arith

theorem R_le (b C1 Ch ka n t : ℝ) (hb : 2 ≤ b) (hC1 : 1 ≤ C1) (hn1 : 1 ≤ n) (hn : n ≤ b) (hka : 0 < ka)
    (hkinv : ka⁻¹ ≤ b ^ Ch) (ht0 : 0 ≤ t) (ht : t ≤ b) :
    C1 * n ^ 2 * (b + t) / ka ≤ b ^ (Real.logb 2 C1 + 4 + |Ch|) := by
  have hb0 : (0:ℝ) < b := by linarith
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hL : 0 ≤ Real.logb 2 C1 := Real.logb_nonneg one_lt_two hC1
  have hC1b : C1 ≤ b ^ Real.logb 2 C1 := by
    calc C1 = (2:ℝ) ^ Real.logb 2 C1 := (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ b ^ Real.logb 2 C1 := Real.rpow_le_rpow (by norm_num) hb hL
  have hn2 : n ^ 2 ≤ b ^ (2:ℝ) := by
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (by linarith) hn 2
  have hbt : b + t ≤ b ^ (2:ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hka' : 1 / ka ≤ b ^ |Ch| := by
    rw [one_div]
    exact hkinv.trans (Real.rpow_le_rpow_of_exponent_le hb1 (le_abs_self Ch))
  have p1 : 0 ≤ b ^ Real.logb 2 C1 := Real.rpow_nonneg hb0.le _
  have p2 : 0 ≤ b ^ (2:ℝ) := Real.rpow_nonneg hb0.le _
  have h1 : C1 * n ^ 2 ≤ b ^ Real.logb 2 C1 * b ^ (2:ℝ) := mul_le_mul hC1b hn2 (sq_nonneg n) p1
  have h2 : C1 * n ^ 2 * (b + t) ≤ b ^ Real.logb 2 C1 * b ^ (2:ℝ) * b ^ (2:ℝ) :=
    mul_le_mul h1 hbt (by linarith) (mul_nonneg p1 p2)
  have h3 : C1 * n ^ 2 * (b + t) * (1 / ka) ≤ b ^ Real.logb 2 C1 * b ^ (2:ℝ) * b ^ (2:ℝ) * b ^ |Ch| :=
    mul_le_mul h2 hka' (le_of_lt (one_div_pos.mpr hka)) (mul_nonneg (mul_nonneg p1 p2) p2)
  calc C1 * n ^ 2 * (b + t) / ka = C1 * n ^ 2 * (b + t) * (1 / ka) := by ring
    _ ≤ b ^ Real.logb 2 C1 * b ^ (2:ℝ) * b ^ (2:ℝ) * b ^ |Ch| := h3
    _ = b ^ (Real.logb 2 C1 + 4 + |Ch|) := by
        rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
        congr 1
        ring

theorem H_le (b CardSubmodulesOfIndexLePow C2 E ka X : ℝ) (m r : ℕ) (hrm : r ≤ m) (hb : 1 ≤ b) (hka : 0 < ka) (hE : 0 ≤ E)
    (hC2 : CardSubmodulesOfIndexLePow + E ≤ C2) (hX : X ≤ b ^ E) :
    b ^ (CardSubmodulesOfIndexLePow * (m : ℝ)) * (1 + 1 / ka) ^ m * (max 1 X) ^ r ≤ b ^ (C2 * (m : ℝ)) * (1 + 1 / ka) ^ m := by
  have hb0 : (0:ℝ) < b := by linarith
  have hbE : 1 ≤ b ^ E := Real.one_le_rpow hb hE
  have hmax : max 1 X ≤ b ^ E := max_le hbE hX
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have h1 : (max 1 X) ^ r ≤ b ^ (E * (m:ℝ)) := by
    calc (max 1 X) ^ r ≤ (b ^ E) ^ r := pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax r
      _ = b ^ (E * (r:ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
      _ ≤ b ^ (E * (m:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_left (by exact_mod_cast hrm) hE)
  have h2 : b ^ (CardSubmodulesOfIndexLePow * (m:ℝ)) * b ^ (E * (m:ℝ)) ≤ b ^ (C2 * (m:ℝ)) := by
    rw [← Real.rpow_add hb0]
    apply Real.rpow_le_rpow_of_exponent_le hb
    nlinarith
  have hk : 0 ≤ (1 + 1 / ka) ^ m := pow_nonneg (by have := one_div_pos.mpr hka; linarith) _
  have hA : 0 ≤ b ^ (CardSubmodulesOfIndexLePow * (m:ℝ)) := Real.rpow_nonneg hb0.le _
  calc b ^ (CardSubmodulesOfIndexLePow * (m:ℝ)) * (1 + 1 / ka) ^ m * (max 1 X) ^ r
      ≤ b ^ (CardSubmodulesOfIndexLePow * (m:ℝ)) * (1 + 1 / ka) ^ m * b ^ (E * (m:ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hA hk)
    _ = (b ^ (CardSubmodulesOfIndexLePow * (m:ℝ)) * b ^ (E * (m:ℝ))) * (1 + 1 / ka) ^ m := by ring
    _ ≤ b ^ (C2 * (m:ℝ)) * (1 + 1 / ka) ^ m := mul_le_mul_of_nonneg_right h2 hk

theorem lam_lt_u {k n : ℕ} (hkn : k ≤ n) (u : Fin k → ℝ) (lam : Fin n → ℝ) (h : InterlaceS hkn u lam) (hk : 0 < k) :
    ∀ i : Fin k, lam ⟨k - 1, by omega⟩ < u i := by
  have hnode : ∀ i : Fin k, lam ⟨k - 1, by omega⟩ < u i := by
    obtain ⟨h1, h2⟩ := h
    have step : ∀ (i : ℕ) (hi : i + 1 < k), u ⟨i + 1, hi⟩ < u ⟨i, by omega⟩ :=
      fun i hi => (h1 i hi).2.trans (h1 i hi).1
    have key : ∀ d : ℕ, ∀ (i : ℕ) (hi : i < k), i + d = k - 1 → u ⟨k - 1, by omega⟩ ≤ u ⟨i, hi⟩ := by
      intro d
      induction d with
      | zero =>
        intro i hi hd
        simp only [add_zero] at hd
        subst hd
        exact le_rfl
      | succ d ih =>
        intro i hi hd
        have hi1 : i + 1 < k := by omega
        exact (ih (i + 1) hi1 (by omega)).trans (step i hi1).le
    intro i
    have hi' := i.2
    exact (h2 hk).trans_le (key (k - 1 - i.val) i.val i.2 (by omega))
  exact hnode

theorem sizes (D : D7) (Ch Cg : ℝ) (hCg : 1 ≤ Cg) (L : LocBessel D.R.k D.R.rS)
    (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (hLoc : LocOk0 D Ch Cg L lam0 ka b ka)
    (hbv : Cg * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv) (hSh : ShapeS L.u lam0 bv) :
    (2 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ∧ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ≤ bv ∧ bv ≤ b ∧ 0 < ka ∧
      ka⁻¹ ≤ b ^ Ch ∧ 1 ≤ Tz D.R.k D.R.rS L.z := by
  obtain ⟨hk1, -, -, -, -, hStd, -, -⟩ := hLoc
  obtain ⟨-, hI, -, hka, -, hkinv, hT, -, -, -, hlam, -⟩ := hStd
  have hk0 : 0 < D.R.k := hk1
  have hkn : D.R.k ≤ 2 * D.R.rS + D.R.k + 1 := by omega
  have hnode := lam_lt_u hkn L.u lam0 hI hk0
  have hnc : ¬ IsCloud L.u lam0 ⟨D.R.k - 1, by omega⟩ := fun hc => by
    obtain ⟨i, hi⟩ := hc.2
    exact lt_asymm hi (hnode i)
  have h2 := ((hSh ⟨D.R.k - 1, by omega⟩).2 hnc).2
  have h3 := hlam ⟨D.R.k - 1, by omega⟩
  have h4 := neg_abs_le (lam0 ⟨D.R.k - 1, by omega⟩)
  have hbvb : bv ≤ b := by linarith
  have hn1 : (1:ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * D.R.rS + D.R.k + 1 by omega)
  have hn7 : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 := by
    calc ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 := pow_le_pow_right₀ hn1 (by norm_num)
  have hnbv : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ≤ bv := by
    have : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ Cg * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      le_mul_of_one_le_left (by positivity) hCg
    linarith
  rw [div_self hka.ne', one_pow, mul_one] at hT
  refine ⟨?_, hnbv, hbvb, hka, hkinv, hT⟩
  exact_mod_cast (show 2 ≤ 2 * D.R.rS + D.R.k + 1 by omega)

end Arith

def ShellSmooth (D : D7) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (P : Mx D.R.k D.R.rS) (j : ℕ), IsCayleyU D.R.k D.R.rS L.ε P →
    ∀ w ∈ shell L P j, w ∈ smoothVecs (k := D.R.k) (r := D.R.rS) L.σ

def PhMeas (D : D7) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (Bf : L.Hs → L.Wp) (w : L.Hs),
    IsBesselMapSm L.z (psi D.R.k D.R.rS L.z L.c) L.σ L.π Bf → w ∈ smoothVecs (k := D.R.k) (r := D.R.rS) L.σ →
    Measurable (Set.indicator {x : Mt D.R.k D.R.rS | Matrix.of x ∈ UH (Hpk D.R.k D.R.rS)}
      (fun x => ‖Bf (L.σ (Matrix.of x) w)‖))

theorem aem_of_meas {k r : ℕ} (L : LocBessel k r) (Bf : L.Hs → L.Wp) (νq : Measure (Mt k r)) (w : L.Hs)
    (hconc : νq {x | Matrix.of x ∉ UH (Hpk k r)} = 0)
    (hM : Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} (fun x => ‖Bf (L.σ (Matrix.of x) w)‖))) :
    AEMeasurable (fun x : Mt k r => (‖Bf (L.σ (Matrix.of x) w)‖₊ : ENNReal)) νq := by
  have hae : (Set.indicator {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}
      (fun x => ‖Bf (L.σ (Matrix.of x) w)‖)) =ᵐ[νq] (fun x => ‖Bf (L.σ (Matrix.of x) w)‖) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null ?_ hconc
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro hmem
    exact hx (Set.indicator_of_mem (show x ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} from hmem) _)
  have hm : AEMeasurable (fun x => ‖Bf (L.σ (Matrix.of x) w)‖) νq := hM.aemeasurable.congr hae
  refine (ENNReal.measurable_ofReal.comp_aemeasurable hm).congr ?_
  exact Filter.Eventually.of_forall (fun x => by
    show ENNReal.ofReal ‖Bf (L.σ (Matrix.of x) w)‖ = (‖Bf (L.σ (Matrix.of x) w)‖₊ : ENNReal)
    rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal])

def muE {k r : ℕ} (L : LocBessel k r) (Bf : L.Hs → L.Wp) (νq : Measure (Mt k r)) (w : L.Hs) : Measure (Mt k r) :=
  νq.withDensity fun x => (ENNReal.ofReal (‖w‖ ^ 2))⁻¹ * (‖Bf (L.σ (Matrix.of x) w)‖₊ : ENNReal) ^ 2

theorem Emom_eq {k r : ℕ} (L : LocBessel k r) (Bf : L.Hs → L.Wp) (νq : Measure (Mt k r)) (w : L.Hs) (hw : w ≠ 0)
    (hconc : νq {x | Matrix.of x ∉ UH (Hpk k r)} = 0)
    (hPm : AEMeasurable (fun x : Mt k r => (‖Bf (L.σ (Matrix.of x) w)‖₊ : ENNReal)) νq)
    (X : Mx k r → ENNReal) (X' : Mt k r → ENNReal) (hX' : Measurable X')
    (hXX : ∀ x : Mt k r, Matrix.of x ∈ UH (Hpk k r) → X (Matrix.of x) = X' x) :
    Emom L Bf νq w X = ∫⁻ x, X' x ∂(muE L Bf νq w) := by
  have hpos : (0:ℝ) < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw) 2
  have hne : (ENNReal.ofReal (‖w‖ ^ 2))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hpos).ne'
  unfold muE Formalism.MainNotions.S.ThB.Emom
  rw [lintegral_withDensity_eq_lintegral_mul₀ ((hPm.pow_const 2).const_mul _) hX'.aemeasurable]
  simp only [Pi.mul_apply, mul_assoc]
  rw [lintegral_const_mul' _ _ hne]
  congr 1
  apply lintegral_congr_ae
  have hae : ∀ᵐ x ∂νq, Matrix.of x ∈ UH (Hpk k r) := by
    rw [ae_iff]
    exact hconc
  filter_upwards [hae] with x hx
  rw [hXX x hx]
  exact mul_comm _ _

theorem muE_prob {k r : ℕ} (L : LocBessel k r) (Bf : L.Hs → L.Wp) (νq : Measure (Mt k r)) (w : L.Hs) (hw : w ≠ 0)
    (hnorm : l2SG νq (fun g => Bf (L.σ g w)) = (‖w‖₊ : ENNReal) ^ 2) : IsProbabilityMeasure (muE L Bf νq w) := by
  have hpos : (0:ℝ) < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw) 2
  have hne : (ENNReal.ofReal (‖w‖ ^ 2))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hpos).ne'
  have h : ∫⁻ x, (‖Bf (L.σ (Matrix.of x) w)‖₊ : ENNReal) ^ 2 ∂νq = (‖w‖₊ : ENNReal) ^ 2 := hnorm
  constructor
  unfold muE
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_const_mul' _ _ hne, h,
    ENNReal.ofReal_pow (norm_nonneg _), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
  exact ENNReal.inv_mul_cancel (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hw)))
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)

open Classical in

theorem shell_tail_bound_of_moment_energy (D : D7) (Ch Cg Cq C1 CardSubmodulesOfIndexLePow C2 : ℝ) (hCg : 1 ≤ Cg) (hC1 : 1 ≤ C1) (constant_log_relation : 0 ≤ CardSubmodulesOfIndexLePow)
    (hC2 : CardSubmodulesOfIndexLePow + (Real.logb 2 C1 + 4 + |Ch|) ≤ C2) (hSm : ShellSmooth D) (hMe : PhMeas D)
    (ha : ShellMomentBound D Ch Cg Cq C1 CardSubmodulesOfIndexLePow) (hb : ShellEnergyBound D Ch Cg Cq C1) : ShellTailBound D Ch Cg Cq C1 C2 := by
  intro L lam0 ka b bv Bf μG μS νq P w j H q hq1 hq2
  obtain ⟨hLoc, hbv, hShape, hBes, hG, hS, hQ, hnorm, hCay, hw, hw0⟩ := id H
  obtain ⟨hn2, hnbv, hbvb, hka, hkinv, hT⟩ := sizes D Ch Cg hCg L lam0 ka b bv hLoc hbv hShape
  have hconc := quot_conc L.z μG μS νq hG hS hQ
  have hwsm := hSm L P j hCay w hw
  have hPm := aem_of_meas L Bf νq w hconc (hMe L Bf w hBes hwsm)
  have : IsProbabilityMeasure (muE L Bf νq w) := muE_prob L Bf νq w hw0 (hnorm w hwsm)
  have hEq := Emom_eq L Bf νq w hw0 hconc hPm
  set n : ℝ := ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) with hn
  set T : ℝ := Tz D.R.k D.R.rS L.z with hTdef
  have hb2 : 2 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hbv0 : 0 ≤ bv := by linarith
  have hn1 : 1 ≤ n := by linarith

  let l' : Fin (D.R.rS + 1) → Mt D.R.k D.R.rS → ℝ := fun a x =>
    if Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) then la D L a (Matrix.of x) else T
  have hl' : ∀ a x, Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) → l' a x = la D L a (Matrix.of x) := by
    intro a x hx; simp only [l', if_pos hx]
  have hl'm : ∀ a, Measurable (l' a) := fun a =>
    Measurable.ite (measurableSet_UH _ _) (measurable_lA L.z a) measurable_const
  have hl'p : ∀ a x, 0 < l' a x := by
    intro a x
    by_cases hx : Matrix.of x ∈ UH (Hpk D.R.k D.R.rS)
    · rw [hl' a x hx]; exact lA_pos L.z L.hz.1 L.hz.2 _ hx a
    · simp only [l', if_neg hx]; linarith

  set H0 : ℝ := H1 D CardSubmodulesOfIndexLePow b ka with hH0
  set R : ℝ := C1 * n ^ 2 * (b + ((j : ℝ) + (((D.R.rS + 1) * q : ℕ) : ℝ))) / ka with hR
  have hK1 : 1 ≤ (1 + 1 / ka) ^ (2 * D.R.rS + 2) := one_le_pow₀ (by have : 0 < 1 / ka := by positivity
                                                                    linarith)
  have hH0one : 1 ≤ H0 := by
    rw [hH0, H1]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hb1 (by positivity)) hK1
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hC1n4 : 1 ≤ C1 * n ^ 4 := one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hn1)
  have hmq : (((2 * D.R.rS + 2) * q + j : ℕ) : ℝ) ≤ bv := le_trans hq2 (div_le_self hbv0 hC1n4)
  have ht : (j : ℝ) + (((D.R.rS + 1) * q : ℕ) : ℝ) ≤ b := by
    have : j + (D.R.rS + 1) * q ≤ (2 * D.R.rS + 2) * q + j := by nlinarith
    have h' : (j : ℝ) + (((D.R.rS + 1) * q : ℕ) : ℝ) ≤ (((2 * D.R.rS + 2) * q + j : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hRle : R ≤ b ^ (Real.logb 2 C1 + 4 + |Ch|) :=
    R_le b C1 Ch ka n _ hb2 hC1 hn1 (by linarith) hka hkinv (by positivity) ht
  have hE0 : 0 ≤ Real.logb 2 C1 + 4 + |Ch| := by
    have := Real.logb_nonneg (b := 2) (by norm_num) hC1
    positivity
  have hHle : H0 * max 1 R ^ D.R.rS ≤ H1 D C2 b ka := by
    rw [hH0, H1, H1]
    exact H_le b CardSubmodulesOfIndexLePow C2 _ ka R (2 * D.R.rS + 2) D.R.rS (by omega) hb1 hka hE0 hC2 hRle
  have hHpos : 0 < H0 * max 1 R ^ D.R.rS := by positivity

  have hA : ∀ q' ≤ (D.R.rS + 1) * q, ∫⁻ x, ENNReal.ofReal (l' 0 x ^ (2 * q')) ∂(muE L Bf νq w) ≤
      ENNReal.ofReal (H0 ^ (2 * q')) := by
    intro q' hq'
    rw [← hEq (fun g => ENNReal.ofReal (la D L 0 g ^ (2 * q'))) _ ((hl'm 0).pow_const _).ennreal_ofReal
      (fun x hx => by rw [hl' 0 x hx])]
    have hq'2 : 2 * q' ≤ (2 * D.R.rS + 2) * q := by nlinarith
    refine ha L lam0 ka b bv Bf μG μS νq P w j H q' ?_ ?_
    · have : (q' : ℝ) ≤ (((2 * D.R.rS + 2) * q : ℕ) : ℝ) := by
        have : q' ≤ (2 * D.R.rS + 2) * q := by omega
        exact_mod_cast this
      linarith
    · have h1 : (j : ℝ) + 2 * q' ≤ (((2 * D.R.rS + 2) * q + j : ℕ) : ℝ) := by
        have : j + 2 * q' ≤ (2 * D.R.rS + 2) * q + j := by omega
        exact_mod_cast this
      have h2 : bv / (C1 * n ^ 4) ≤ bv / (C1 * n ^ 2) := by
        apply div_le_div_of_nonneg_left hbv0 (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by norm_num)) (by linarith)
      linarith
  have hB : ∀ c : Fin D.R.rS, ∀ q' ≤ (D.R.rS + 1) * q,
      ∫⁻ x, ENNReal.ofReal ((l' c.succ x / l' c.castSucc x) ^ (2 * q')) ∂(muE L Bf νq w) ≤
        ENNReal.ofReal (R ^ (2 * q')) := by
    intro c q' hq'
    rw [← hEq (fun g => ENNReal.ofReal ((la D L c.succ g / la D L c.castSucc g) ^ (2 * q')))
      (fun x => ENNReal.ofReal ((l' c.succ x / l' c.castSucc x) ^ (2 * q')))
      (((hl'm c.succ).div (hl'm c.castSucc)).pow_const _).ennreal_ofReal
      (fun x hx => by rw [hl' _ x hx, hl' _ x hx])]
    refine le_trans (hb L lam0 ka b bv Bf μG μS νq P w j H
      (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) hq1) q' c.val c.isLt) ?_
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by positivity)
    rw [hR]
    have : (q' : ℝ) ≤ (((D.R.rS + 1) * q : ℕ) : ℝ) := by exact_mod_cast hq'
    apply div_le_div_of_nonneg_right _ hka.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hC : ∀ x, T ≤ l' (Fin.last D.R.rS) x ^ 2 := by
    intro x
    by_cases hx : Matrix.of x ∈ UH (Hpk D.R.k D.R.rS)
    · rw [hl' _ x hx]; exact majorant_ge_lowest_coordinate_sq D L _ hx
    · simp only [l', if_neg hx]; nlinarith
  have core := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.corollary_consequence (Mt D.R.k D.R.rS) (muE L Bf νq w) D.R.rS q l' H0 R T hl'm hl'p hH0one hR0 hT
    hA hB hC
  have hmono : ENNReal.ofReal ((H0 * max 1 R ^ D.R.rS) ^ (2 * q)) ≤ ENNReal.ofReal (H1 D C2 b ka ^ (2 * q)) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hHpos.le hHle _)
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [hEq (fun g => ENNReal.ofReal (la D L a g ^ (2 * q))) _ ((hl'm a).pow_const _).ennreal_ofReal
      (fun x hx => by rw [hl' a x hx])]
    exact le_trans (core.1 a).1 hmono
  · rw [hEq (fun g => ENNReal.ofReal ((la D L a g)⁻¹ ^ (2 * q))) (fun x => ENNReal.ofReal ((l' a x)⁻¹ ^ (2 * q)))
      ((hl'm a).inv.pow_const _).ennreal_ofReal (fun x hx => by rw [hl' a x hx])]
    exact le_trans (core.1 a).2 hmono
  · intro lam' hlam'
    have hSm' : MeasurableSet {x : Mt D.R.k D.R.rS | ∃ a : Fin (D.R.rS + 1),
        lam' * H1 D C2 b ka ≤ max (l' a x) (l' a x)⁻¹} := by
      have : {x : Mt D.R.k D.R.rS | ∃ a : Fin (D.R.rS + 1), lam' * H1 D C2 b ka ≤ max (l' a x) (l' a x)⁻¹} =
          ⋃ a : Fin (D.R.rS + 1), {x | lam' * H1 D C2 b ka ≤ max (l' a x) (l' a x)⁻¹} := by
        ext x; simp
      rw [this]
      exact MeasurableSet.iUnion fun a => measurableSet_le measurable_const ((hl'm a).max (hl'm a).inv)
    rw [hEq _ (Set.indicator {x : Mt D.R.k D.R.rS | ∃ a : Fin (D.R.rS + 1),
        lam' * H1 D C2 b ka ≤ max (l' a x) (l' a x)⁻¹} 1) (measurable_one.indicator hSm') (by
      intro x hx
      simp only [Set.indicator, Set.mem_ofPred_eq, hl' _ x hx, Pi.one_apply])]
    rw [lintegral_indicator_one hSm']
    refine le_trans (measure_mono ?_) (le_trans (core.2 lam' hlam') ?_)
    · rintro x ⟨a, hax⟩
      exact ⟨a, le_trans (mul_le_mul_of_nonneg_left hHle hlam'.le) hax⟩
    · apply ENNReal.ofReal_le_ofReal
      have e1 : lam' ^ (-(2 * (q : ℝ))) = (lam' ^ (2 * q))⁻¹ := by
        rw [Real.rpow_neg hlam'.le]
        congr 1
        have : (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ) := by push_cast; ring
        rw [this, Real.rpow_natCast]
      rw [e1, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      push_cast
      have : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
      linarith



def ShellEnergyOneStep (D : D7) (Ch Cg Cq Cs : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (Bf : L.Hs → L.Wp)
    (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS),
    ShellCommonHypotheses D Ch Cg L lam0 ka b bv Bf μG μS νq P →
    l1 L.lam lam0 ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0 →
    ∃ (ι : Type) (_ : Fintype ι) (Eop : ι → L.Hs → L.Hs),
      (∀ i j w, w ∈ shell L P j → Eop i w ∈ shell L P (j + 2)) ∧
      (∀ (j : ℕ) w, w ∈ shell L P j →
        ∑ i, ‖Eop i w‖ ^ 2 ≤ (Cs * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 * (b + j)) ^ 2 * ‖w‖ ^ 2) ∧
      ∀ (a : ℕ) (ha : a < D.R.rS) (j : ℕ) w, w ∈ shell L P j → ∀ g ∈ UH (Hpk D.R.k D.R.rS),
        (ka * la D L ⟨a + 1, by omega⟩ g / la D L ⟨a, by omega⟩ g) ^ 2 * ‖Bf (L.σ g w)‖ ^ 2 ≤
          ∑ i, ‖Bf (L.σ g (Eop i w))‖ ^ 2

theorem ofReal_norm_sq {E : Type*} [NormedAddCommGroup E] (a : E) :
    ENNReal.ofReal (‖a‖ ^ 2) = (‖a‖₊ : ENNReal) ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]


def shellMomentSupremum (D : D7) (Ch Cg : ℝ) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (u : Fin D.R.k → ℝ) (ka b bv : ℝ) (q : ℕ)
    (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (j : ℕ) : ENNReal :=
  ⨆ (L : LocBessel D.R.k D.R.rS) (Bf : L.Hs → L.Wp) (μG : Measure (Mt D.R.k D.R.rS)) (μS : Measure (Mt D.R.k D.R.rS))
    (νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) (w : L.Hs)
    (_ : L.lam = μ ∧ L.u = u ∧ CloudNodeShape D Ch Cg L lam0 ka b bv Bf μG μS νq P w j),
    Emom L Bf νq w (fun g => ENNReal.ofReal (la D L 0 g ^ (2 * q)))

def ShellMomentOneStep (D : D7) (Ch Cg Cq C1 C2 : ℝ) : Prop :=
  ∀ (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (u : Fin D.R.k → ℝ) (ka b bv : ℝ) (q : ℕ)
    (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (j : ℕ),
    l1 μ lam0 + 1 ≤ q0 Cq (2 * D.R.rS + 2) (epsSH D.R) u lam0 →
    (j : ℝ) + 2 ≤ bv / (C1 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2) →
    shellMomentSupremum D Ch Cg lam0 u ka b bv (q + 1) μ j ≤
      ENNReal.ofReal (H1 D C2 b ka ^ 2) * ⨆ s, shellMomentSupremum D Ch Cg lam0 u ka b bv q (μ - Pi.single s 1) (j + 2)

def parAfter {n : ℕ} (μ : Fin n → ℝ) : List (Fin n) → (Fin n → ℝ)
  | [] => μ
  | s :: l => parAfter μ l - Pi.single s 1








end Formalism.MainNotions.BesselShellMomentBounds

end PieceM93

section PieceZ

namespace Formalism.MainNotions.BesselShellMomentBounds

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.S.Pv.Frames

structure BesselShellOpenHypotheses (D : D7) (Ch Aw Cu Cg Cq Cg' C1 CardSubmodulesOfIndexLePow Cs Cb Cgf Cf : ℝ) (A : ℕ) : Prop where
  bp : TheoremBPrimePointwise D Ch Cg Cb
  ubp : UniformityTheoremBPrime D Ch Cu Cg Cg' Cb
  p90 : FormalDegreeRatioAlt D
  p90d : FormalDegreeRatioDual D
  p90P : PieriNormPairing D Ch Cg Cq
  p91 : BesselLeadingMinorBound D Ch Cg Cq Cb
  conjugateExpansionNearLambda : BesselConjugatesEveryCell D Ch Cg Cq Cb
  p92c : BesselIterationNearParameter D Ch Cg Cq Cb
  fr : FrameBesselBound D Cgf Cf
  one1 : OnePlace D Ch Cg 0 (fun _ _ _ _ => True) A (Cb - 6) 4 0
  one3 : OnePlace D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) A (Cb - 6) 5
    (Aw * ((D.R.rS : ℝ) + 1) ^ 2)
  oneUnitaryFirstPlace : OnePlace D Ch Cg (Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)
    (fun _ _ _ X => (∀ v, RngU D Cu Cg' (X.L v).lam (lamSH D.R (D.hc v))) ∧
      ∀ v, jNorm2 (X.L v) (X.f v) (X.μsec v) ≠ 0) A (Cb - 6) 4 0
  oneUnitaryThirdPlace : OnePlace D Ch Cg (Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)
    (fun _ _ _ X => ((∀ v, RngU D Cu Cg' (X.L v).lam (lamSH D.R (D.hc v))) ∧
      ∀ v, jNorm2 (X.L v) (X.f v) (X.μsec v) ≠ 0) ∧
      ∀ v, AllGaps (lamSH D.R (D.hc v)) (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) A (Cb - 6) 5
    (Aw * ((D.R.rS : ℝ) + 1) ^ 2)
  exFam : ExFam D Ch Cg Cq
  jMeas : JMeas D
  shell : ShellSmooth D
  phMeas : PhMeas D
  lowK : LowestKTypeRightInvariant D Ch Cg
  shellMomentStep : ShellMomentOneStep D Ch Cg Cq C1 CardSubmodulesOfIndexLePow
  shellEnergyOneStep : ShellEnergyOneStep D Ch Cg Cq Cs


end Formalism.MainNotions.BesselShellMomentBounds

end PieceZ
