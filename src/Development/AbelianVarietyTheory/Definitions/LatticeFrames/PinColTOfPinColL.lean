import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.LiveModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}


def Reached {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) : ∀ j, Ch₀ j → Prop
  | 0, _ => True
  | j + 1, β => j + 1 = B.R.m ∨ ∃ (hj : j + 1 ≤ B.R.m) (α : Ch₀ j), ∃ z, A.xi j hj α β z ≠ 0







variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))

def movedLev : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (levG _ R.βX (datXP R P t)).comap (MulAut.conj g.bT⁻¹).toMonoidHom

def withTop (ε : ℂ) : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a) :=
  { k with eT := fun _ _ _ => Finsupp.single g.bT ε, cP := ε * (volLev g.volT (movedLev R g P t) : ℂ) }

theorem pinTopL_withTop (h : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))) (ε : ℂ) :
    PinTopL R g P (t := t) (withTop R g P t k ε) (movedLev R g P t) ε :=
  ⟨h, fun h => by
    show (MulAut.conj g.bT⁻¹) h ∈ levG _ R.βX (datXP R P t) ↔ _
    rw [MulAut.conj_apply, inv_inv]; rfl, fun _ _ _ => rfl, rfl⟩




section Emb
open GlobalTheory.MixModel
variable {D : D7}

theorem gram_pos {E : Type} [Field E] [NumberField E] [StarRing E] (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (n : ℕ) :
    (Examples₂.posSpace hs n).gram = 1 := by
  funext i j
  refine (Examples₂.stdSpace_gram_apply hs n (fun _ => false) n 0 i j).trans ?_
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact (if_pos rfl).trans (by simp [Examples₂.sgn])
  · rw [Matrix.one_apply_ne h]; exact if_neg h

theorem rk_top (D : D7) : D.sp.X'.rank + 1 = (D.sp.X D.R.m).rank := by
  have h1 := rankP D
  have h2 := rankN D D.R.m le_rfl
  have h3 : 0 < D.R.N D.R.m := by
    have := D.R.two_le_m
    have h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m := by ring
    simp only [Ranks.N]; omega
  omega

def topDec (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1) :
    OrthDec (D.sp.X D.R.m) D.sp.X' (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1) where
  iA := Matrix.of fun b a => if (a : ℕ) = b then 1 else 0
  iB := Matrix.of fun b _ => if D.sp.X'.rank = b then 1 else 0
  isoA := by
    have := rk_top D
    rw [hG, hG', Matrix.mul_one]
    funext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i, by omega⟩ : Fin (D.sp.X D.R.m).rank)]
    · simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
    · intro b _ hb
      have : ¬ (i : ℕ) = b := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  isoB := by
    have := rk_top D
    rw [hG, Matrix.mul_one]
    funext i j
    have h : (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1).gram i j = 1 := by
      rw [gram_pos, Subsingleton.elim (α := Fin 1) i j, Matrix.one_apply_eq]
    rw [h, Matrix.mul_apply, Finset.sum_eq_single (⟨D.sp.X'.rank, by omega⟩ : Fin (D.sp.X D.R.m).rank)]
    · simp
    · intro b _ hb
      have : ¬ D.sp.X'.rank = b := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  orth := by
    rw [hG, Matrix.mul_one]
    funext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := j.2
    by_cases hb : D.sp.X'.rank = b
    · have : ¬ (j : ℕ) = b := by omega
      simp [this]
    · simp [hb]
  rank_add := rk_top D

theorem iXm_eq (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
    D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b) (b a) : iXm D b a = if (a : ℕ) = b then 1 else 0 := by
  have h0 := rk_top D
  have h1 := rankP D
  have ha := a.2
  have e : ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm (Pi.single a 1)) =
      D.sp.X'.frame (Fin.cast h1.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k
    simp [Finsupp.single_apply, Pi.single_apply, Fin.ext_iff, eq_comm]
  rw [iXm, LinearMap.toMatrix'_apply, iXc]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e, hi _ ⟨a, by omega⟩ rfl]
  simp [Finsupp.single_apply, Fin.ext_iff]

theorem isEmbTop_topDec (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1)
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b)
    (c : D.host.E) : IsEmbTop (D := D) (fun j => if j.1 + 1 = D.R.N D.R.m then c else 0)
      ((topDec hG hG').emb.comp (MonoidHom.inl _ _)) := by
  intro h
  have h0 := rk_top D
  have h1 := rankP D
  have h2 := rankN D D.R.m le_rfl
  have eA : (iXm D).map (incA D) = ((topDec hG hG').jA).reindex (finCongr h2) (finCongr h1) := by
    ext b a
    simp [iXm_eq hi, OrthDec.jA, rat, topDec]
  constructor
  · rw [eA]
    have := (topDec hG hG').emb_jA h 1
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix M _ _) this
  · have := (topDec hG hG').emb_jB h 1
    rw [mt_one, Matrix.mul_one] at this
    funext b
    have e := congrFun (congrFun this (Fin.cast h2.symm b)) (0 : Fin 1)
    have ez : (fun a : Fin (D.R.N D.R.m) => incA D (if a.1 + 1 = D.R.N D.R.m then c else 0)) =
        fun a => (topDec hG hG').jB (Fin.cast h2.symm a) (0 : Fin 1) * incA D c := by
      funext a
      have : (a.1 + 1 = D.R.N D.R.m) ↔ D.sp.X'.rank = a := by omega
      show _ = incA D (if D.sp.X'.rank = a then 1 else 0) * incA D c
      rw [← map_mul]
      by_cases ha : D.sp.X'.rank = a
      · rw [if_pos ha, if_pos (this.2 ha), one_mul]
      · rw [if_neg ha, if_neg (fun h => ha (this.1 h)), zero_mul]
    have ez' := congrFun ez b
    rw [ez, ez', ← e]
    refine Eq.trans ?_ (congrArg (· * incA D c) Matrix.mul_apply).symm
    refine Eq.trans ?_ (Finset.sum_mul _ _ _).symm
    refine Fintype.sum_equiv (finCongr h2.symm) _ _ fun x => ?_
    exact (mul_assoc _ _ _).symm
end Emb

theorem exists_emb (hI : I.Ok) (hP : TC.Pins B X) :
    ∃ (Lz : HSp (I.rec7 l Z)) (oT : ∀ n, n = (I.rec7 l Z).R.m → GlobalTheory.MixModel.OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' Lz),
      IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) := by
  obtain ⟨hs, h1, h2, -⟩ := hI.spaces
  have key : ∀ S : HSp (I.rec7 l Z), ∀ n, S = Examples₂.posSpace hs n → S.gram = 1 := by rintro _ n rfl; exact gram_pos hs n
  have gen : ∀ (D : D7) (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1)
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b) (c : D.host.E),
      ∃ (Lz : HSp D) (oT : ∀ n, n = D.R.m → GlobalTheory.MixModel.OrthDec (D.sp.X n) D.sp.X' Lz),
        IsEmbTop (D := D) (fun j => if j.1 + 1 = D.R.N D.R.m then c else 0) ((oT D.R.m rfl).emb.comp (MonoidHom.inl _ _)) :=
    fun D hG hG' hi c => ⟨_, fun n h => Eq.rec (motive := fun n _ => GlobalTheory.MixModel.OrthDec (D.sp.X n) _ _) (topDec hG hG') h.symm,
      isEmbTop_topDec hG hG' hi c⟩
  exact gen (I.rec7 l Z) (key _ _ (h1 _)) (key _ _ h2) hP.iX _

@[reducible] def reTop {D : D7} (g : GlobalTheory.Fam.Geo D) (Lz : HSp D) (oT : ∀ n, n = D.R.m → GlobalTheory.MixModel.OrthDec (D.sp.X n) D.sp.X' Lz) :
    GlobalTheory.Fam.Geo D := { g with Lz := Lz, oT := oT }

set_option maxHeartbeats 1000000 in

theorem exists_pinTopL (hI : I.Ok) (hP : TC.Pins B X) {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL]
    (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T)
    (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a)) (ε : ℂ) :
    ∃ Lz oT, PinTopL R (reTop g Lz oT) P (t := t) (withTop R (reTop g Lz oT) P t k ε) (movedLev R (reTop g Lz oT) P t) ε := by
  obtain ⟨Lz, oT, h⟩ := exists_emb (l := l) (Z := Z) (u := u) hI hP
  exact ⟨Lz, oT, pinTopL_withTop R (reTop g Lz oT) P t k h ε⟩

end GlobalTheory.AdForm.LiveModel
