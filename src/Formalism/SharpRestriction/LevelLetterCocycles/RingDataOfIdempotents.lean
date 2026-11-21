import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.ChainWithExtensionOfSplit
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero

section
noncomputable section

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open Matrix Polynomial Formalism.RepresentationBoundsCohomology.ringDataObjects

section GlobalTheory

variable (r t : ℕ)

def blkG (a : Fin (r + t)) : Fin (t + 1) :=
  if _h : (a : ℕ) < r then 0 else ⟨(a : ℕ) - r + 1, by have := a.2; omega⟩

theorem blkG_castAdd (a : Fin r) : blkG r t (Fin.castAdd t a) = 0 := by
  rw [blkG, dif_pos (by simp)]

theorem blkG_natAdd (c : Fin t) : blkG r t (Fin.natAdd r c) = c.succ := by
  rw [blkG, dif_neg (by simp only [Fin.coe_natAdd]; omega)]
  ext
  simp

variable (K : Type) [CommRing K]

def eG : (Fin (r + t) → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)) :=
  (LinearEquiv.funCongrLeft K K finSumFinEquiv).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) K K)

theorem eG_apply (u : Fin (r + t) → K) :
    eG r t K u = (fun a => u (Fin.castAdd t a), fun c => u (Fin.natAdd r c)) := rfl

variable {r t K}

theorem eG_mulVec (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (hM : ∀ a b, blkG r t a ≠ blkG r t b → M a b = 0) (u : Fin (r + t) → K) :
    eG r t K (M *ᵥ u) = ((M.submatrix (Fin.castAdd t) (Fin.castAdd t)) *ᵥ (eG r t K u).1,
      fun c => M (Fin.natAdd r c) (Fin.natAdd r c) * (eG r t K u).2 c) := by
  simp only [eG_apply]
  ext a
  · simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [Fin.sum_univ_add]
    have h0 : ∀ c : Fin t, M (Fin.castAdd t a) (Fin.natAdd r c) = 0 := fun c =>
      hM _ _ (by rw [blkG_castAdd, blkG_natAdd]; exact (Fin.succ_ne_zero c).symm)
    simp [h0]
  · simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_add]
    have h1 : ∀ b : Fin r, M (Fin.natAdd r a) (Fin.castAdd t b) = 0 := fun b =>
      hM _ _ (by rw [blkG_castAdd, blkG_natAdd]; exact Fin.succ_ne_zero a)
    have h2 : ∀ c : Fin t, c ≠ a → M (Fin.natAdd r a) (Fin.natAdd r c) = 0 := fun c hc =>
      hM _ _ (by rw [blkG_natAdd, blkG_natAdd]; exact fun h => hc (Fin.succ_injective _ h).symm)
    simp only [h1, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single a (fun c _ hc => by rw [h2 c hc, zero_mul]) (by simp)]

end GlobalTheory

section Pts

variable {O Y : Type} [CommRing O] [IsDomain O] (t : ℕ) (P : Y → O[X])

end Pts

section EE

variable {A : Type} [CommRing A] {d : Type} [Fintype d] [DecidableEq d]

end EE

section Gen2

variable {r t : ℕ} {A : Type} [CommRing A]

theorem blkG_inj {a b : Fin (r + t)} (h : blkG r t a = blkG r t b) (ha : blkG r t a ≠ 0) : a = b := by
  unfold blkG at h ha
  by_cases h1 : (a : ℕ) < r
  · rw [dif_pos h1] at ha
    exact absurd rfl ha
  · by_cases h2 : (b : ℕ) < r
    · rw [dif_pos h2, dif_neg h1] at h
      exact absurd (congrArg Fin.val h) (by simp)
    · rw [dif_neg h1, dif_neg h2] at h
      have h3 : (a : ℕ) - r + 1 = (b : ℕ) - r + 1 := congrArg Fin.val h
      exact Fin.ext (by omega)

theorem diag_conj (M : Matrix (Fin (r + t)) (Fin (r + t)) A)
    (hM : ∀ a b, blkG r t a ≠ blkG r t b → M a b = 0) :
    (Matrix.diagonal fun a => if blkG r t a = 0 then (0 : A) else 1) * M *
        (Matrix.diagonal fun a => if blkG r t a = 0 then (0 : A) else 1) =
      Matrix.diagonal fun a => if blkG r t a = 0 then 0 else M a a := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    split_ifs <;> simp_all
  · rw [if_neg hab]
    by_cases ha : blkG r t a = 0
    · simp [ha]
    · by_cases hb : blkG r t b = 0
      · simp [hb]
      · have hne : blkG r t a ≠ blkG r t b := fun h => hab (blkG_inj h ha)
        simp [hM a b hne]

end Gen2

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
end

section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
  Formalism.MainNotions.N.Inst Formalism.MainNotions.LargeLevelLemmas.Br

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

abbrev blk (R : Ranks) : Fin R.nV → Fin (R.t + 1) := blkG R.r R.t

def repX : GE N →* (N.X i → MatN N i) := MonoidHom.pi fun x => rO N i r x

theorem repX_apply (γ : GE N) (x : N.X i) : repX N r γ x = rO N i r x γ := rfl

def NormAt : Prop :=
  (∀ g a b, blk R a ≠ blk R b → rO N i r π g a b = 0) ∧
  (∀ g (c : Fin R.t), rO N i r π g (Fin.natAdd R.r c) (Fin.natAdd R.r c) =
    ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i)) ∧
  (∀ g (a b : Fin R.r), rO N i r π g (Fin.castAdd R.t a) (Fin.castAdd R.t b) = rhoO N i ρ π g a b)

theorem repX_mem (γ : GE N) : repX N r γ ∈ tSpan (N.T i) (repX N r) := by
  refine ⟨{γ}, fun _ => 1, fun _ => one_mem _, ?_⟩
  simp

theorem e_of_bd (M : MatN N i) (hM : ∀ a b, blk R a ≠ blk R b → M a b = 0)
    (B : Matrix (Fin R.r) (Fin R.r) (N.O i))
    (hB : ∀ a b, M (Fin.castAdd R.t a) (Fin.castAdd R.t b) = B a b) (χ : Fin R.t → N.O i)
    (hχ : ∀ c, M (Fin.natAdd R.r c) (Fin.natAdd R.r c) = χ c) (u : Fin R.nV → KK N i) :
    eG R.r R.t (KK N i) ((M.map (toK N i)).mulVec u) =
      ((B.map (toK N i)).mulVec (eG R.r R.t (KK N i) u).1,
        fun c => toK N i (χ c) * (eG R.r R.t (KK N i) u).2 c) := by
  refine (eG_mulVec (M.map (toK N i)) (fun a b h => by
    show toK N i (M a b) = 0
    rw [hM a b h, map_zero]) u).trans ?_
  congr 1
  · congr 2
    ext a b
    show toK N i (M (Fin.castAdd R.t a) (Fin.castAdd R.t b)) = toK N i (B a b)
    rw [hB]
  · funext c
    show toK N i (M (Fin.natAdd R.r c) (Fin.natAdd R.r c)) * _ = _
    rw [hχ]

section Mk

variable (g0 : GE N) (eB e₁ X0 : N.X i → MatN N i)

abbrev Pf : N.X i → Polynomial (N.O i) := fun x => blockPoly (eB x) (X0 x)

def mk51 (hfin : Finite (SplitPts R.t (Pf N eB X0))) (π' : SplitPts R.t (Pf N eB X0)) :
    IdempotentChoiceData N i where
  eB := eB
  e1 := e₁
  g0 := g0
  X0 := X0
  X' := SplitPts R.t (Pf N eB X0)
  finX' := @Fintype.ofFinite _ hfin
  decX' := Classical.decEq _
  p := fun y => y.1.1
  T' := splitT (N.T i) R.t (Pf N eB X0)
  rr := fun c y => if h : 1 ≤ c ∧ c ≤ R.t then y.1.2 ⟨c - 1, by omega⟩ else 0
  π' := π'
  e := eG R.r R.t (KK N i)
  ψρ := fun a => (a π').submatrix (Fin.castAdd R.t) (Fin.castAdd R.t)
  ψχ := fun c a => a π' (Fin.natAdd R.r c) (Fin.natAdd R.r c)

variable (hfin : Finite (SplitPts R.t (Pf N eB X0))) (π' : SplitPts R.t (Pf N eB X0))

end Mk

theorem blockPoly_eq {A : Type} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] (e a : Matrix d d A) :
    blockPoly e a = Matrix.det ((Polynomial.X : Polynomial A) • e.map (Polynomial.C (R := A)) -
      a.map (Polynomial.C (R := A)) + 1 - e.map (Polynomial.C (R := A))) := by
  rw [blockPoly]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem e_of_diag (β : Fin R.nV → N.O i) (u : Fin R.nV → KK N i) :
    eG R.r R.t (KK N i) (((Matrix.diagonal fun a => if blk R a = 0 then 0 else β a : MatN N i).map
        (toK N i)).mulVec u) =
      (0, fun c => toK N i (β (Fin.natAdd R.r c)) * (eG R.r R.t (KK N i) u).2 c) := by
  refine (eG_mulVec _ (fun a b h => ?_) u).trans ?_
  · have hab : a ≠ b := fun hab => h (by rw [hab])
    show toK N i (if a = b then (if blk R a = 0 then (0 : N.O i) else β a) else 0) = 0
    rw [if_neg hab, map_zero]
  · congr 1
    · have h0 : ∀ a b : Fin R.r, ((Matrix.diagonal (fun a => if blk R a = 0 then (0 : N.O i) else β a)).map (toK N i)) (Fin.castAdd R.t a) (Fin.castAdd R.t b) = 0 := by
        intro a b
        show toK N i (if Fin.castAdd R.t a = Fin.castAdd R.t b then
          (if blk R (Fin.castAdd R.t a) = 0 then (0 : N.O i) else β (Fin.castAdd R.t a)) else 0) = 0
        have hblk : blk R (Fin.castAdd R.t a) = 0 := by simp [blkG]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl, if_pos hblk, map_zero]
        · rw [if_neg (fun h => hab (Fin.castAdd_injective _ _ h)), map_zero]
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      exact Finset.sum_eq_zero fun b _ => by
        rw [mul_eq_zero]
        left
        exact h0 a b
    · funext c
      have hblk : blk R (Fin.natAdd R.r c) ≠ 0 := by simp [blkG, Fin.ext_iff]
      show toK N i (if Fin.natAdd R.r c = Fin.natAdd R.r c then
        (if blk R (Fin.natAdd R.r c) = 0 then (0 : N.O i) else β (Fin.natAdd R.r c)) else 0) * _ = _
      rw [if_pos rfl, if_neg hblk]

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
end

section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

theorem card_blk (r t : ℕ) (c : Fin (t + 1)) (hc : c ≠ 0) :
    Fintype.card {a : Fin (r + t) // blkG r t a = c} = 1 := by
  rw [Fintype.card_eq_one_iff]
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc
    · exact h
  have hct := c.isLt
  refine ⟨⟨⟨r + ((c : ℕ) - 1), by omega⟩, ?_⟩, ?_⟩
  · unfold blkG
    rw [dif_neg (by simp)]
    exact Fin.ext (by simp; omega)
  · rintro ⟨a, ha⟩
    apply Subtype.ext
    unfold blkG at ha
    split_ifs at ha with h
    · exact absurd ha.symm hc
    · have h2 := congrArg Fin.val ha
      simp at h2
      exact Fin.ext (by simp; omega)

theorem exists_natAdd (r t : ℕ) (a : Fin (r + t)) (ha : blkG r t a ≠ 0) :
    ∃ c : Fin t, a = Fin.natAdd r c := by
  unfold blkG at ha
  split_ifs at ha with h
  · exact absurd rfl ha
  · exact ⟨⟨(a : ℕ) - r, by have := a.2; omega⟩, Fin.ext (by simp; omega)⟩

theorem primHyp_of (hN : NormAt N r ρ π)
    (hG1 : ∀ (γ : GE N) (k : ℕ), (fun x : N.X i => ((rO N i r x γ).charpolyRev).coeff k) ∈ N.T i) :
    PrimHyp (N.O i) (N.T i) (repX N r) π (blk R) (chiU N i 1) (epsU N i) := by
  obtain ⟨hbd, hχ, -⟩ := hN
  refine ⟨N.T_local i, N.T_sep i, hG1, hbd, fun c hc => card_blk R.r R.t c hc, fun g a ha => ?_⟩
  obtain ⟨c, rfl⟩ := exists_natAdd R.r R.t a ha
  have h1 : ((blk R (Fin.natAdd R.r c) : Fin (R.t + 1)) : ℕ) - 1 = (c : ℕ) := by
    rw [show blk R (Fin.natAdd R.r c) = c.succ from blkG_natAdd R.r R.t c]
    simp
  rw [h1]
  refine (hχ g c).trans ?_
  have h2 := N.chi_def i ((c : ℕ) + 1) (by omega) (by have := c.2; omega)
  have h3 : chiU N i ((c : ℕ) + 1) g = chiU N i 1 g * ((epsU N i g)⁻¹ ^ (c : ℕ)) := by
    show N.chi i ((c : ℕ) + 1) g = _
    rw [h2, MonoidHom.mul_apply]
    congr 1
    have h4 : (-(((((c : ℕ) + 1 : ℕ) : ℤ)) - 1)) = -((c : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h4, _root_.zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, inv_pow]
    rfl
  rw [h3]
  simp

def InertiaElementIdempotentChoice : Prop :=
  ∃ g0 : GE N, (∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
    (∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])) ∧
    ∃ eB e₁ s : N.X i → MatN N i, IdemHyp (N.O i) (N.T i) (repX N r) π (blk R) eB e₁ ∧
      DistinctEigenvalueCornerPerturbation (N.O i) (N.T i) (repX N r) π R.t g0 eB s

end Formalism.MainNotions.N.RepresentationBoundsCohomology

namespace Formalism.MainNotions.LargeLevelLemmas

open Formalism.MainNotions.N Formalism.MainNotions.N.RepresentationBoundsCohomology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* Matrix.GeneralLinearGroup (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* Matrix.GeneralLinearGroup (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

end Formalism.MainNotions.LargeLevelLemmas

end
end

section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG

def blockZeroEquiv (r t : ℕ) : Fin r ≃ {a : Fin (r + t) // blkG r t a = 0} where
  toFun a := ⟨Fin.castAdd t a, blkG_castAdd r t a⟩
  invFun y := ⟨(y.1 : ℕ), by
    have h := y.2
    unfold blkG at h
    split_ifs at h with h1
    · exact h1
    · exact absurd h (by simp [Fin.ext_iff])⟩
  left_inv a := by
    ext
    rfl
  right_inv y := by
    apply Subtype.ext
    ext
    rfl

theorem absIrr_block {k G : Type} [Field k] {r t : ℕ} (M : G → Matrix (Fin (r + t)) (Fin (r + t)) k)
    (ρb : G → Matrix (Fin r) (Fin r) k)
    (h : ∀ g a b, M g (Fin.castAdd t a) (Fin.castAdd t b) = ρb g a b)
    (hs : Submodule.span k (Set.range ρb) = ⊤) :
    AbsIrr (fun g => (M g).toSquareBlock (blkG r t) 0) := by
  apply absIrr_of_span
  intro a b
  let L := Matrix.reindexLinearEquiv k k (blockZeroEquiv r t) (blockZeroEquiv r t)
  have hL : ∀ g, L (ρb g) = (M g).toSquareBlock (blkG r t) 0 := by
    intro g
    ext x y
    obtain ⟨x', rfl⟩ := (blockZeroEquiv r t).surjective x
    obtain ⟨y', rfl⟩ := (blockZeroEquiv r t).surjective y
    simp only [L, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]
    exact (h g x' y').symm
  have h1 : L.symm (Matrix.single a b (1 : k)) ∈ Submodule.span k (Set.range ρb) := by
    rw [hs]
    exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := L.toLinearMap) h1
  rw [Submodule.map_span] at h2
  have h3 : L.toLinearMap (L.symm (Matrix.single a b (1 : k))) = Matrix.single a b (1 : k) :=
    L.apply_symm_apply _
  rw [h3] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, (hL g).symm⟩

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

theorem one_le_letterBlockLength (R : Ranks) : 1 ≤ R.t := by
  have h := R.rank_add_five_le
  omega

theorem absIrr_of_res (hN : NormAt N r ρ π)
    (hres : Submodule.span (kk N i)
      (Set.range (mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π))) = ⊤) :
    AbsIrr (fun g => ((repX N r g π).toSquareBlock (blk R) 0).map (IsLocalRing.residue (N.O i))) :=
  absIrr_block (r := R.r) (t := R.t) (fun g => (rO N i r π g).map (IsLocalRing.residue (N.O i)))
    (fun g => mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π) g)
    (fun g a b => congrArg (IsLocalRing.residue (N.O i)) (hN.2.2 g a b)) hres

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
end
