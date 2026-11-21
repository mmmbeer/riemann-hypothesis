import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TieModel

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar



example : ¬ SameOn (fun _ : Fin 1 → ℚ => (0 : ℚ)) (fun _ : Fin 2 → ℚ => (0 : ℚ)) := fun h => absurd h.1 (by decide)

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
  (P : LevFam X.E X.K R.r Pr.vGs)

def frm (y : Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) :
    (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).Forms :=
  (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
    (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y)


theorem isFormOf_unique {V : Type} {y : V} {x x' : MtildeV W Ch sel mu P} (h : IsFormOf W Ch sel mu hX P x y)
    (h' : IsFormOf W Ch sel mu hX P x' y) : x = x' := by
  obtain ⟨F, hF, e, rfl⟩ := h
  obtain ⟨F', hF', e', rfl⟩ := h'
  have := ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)).injective (eq_of_heq (e.trans e'.symm))
  subst this
  rfl



end Forms

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)







end Cols

section Core

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}




end Core

section Standard

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links

theorem exists_matEq {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (hG : V.gram = 1) (h : Bridge.Gf V) :
    ∃ x : UAd D.sp.cm n, R3.MatEq (R3.matIn V 1 h) (x : GL (Fin n) _) := by
  obtain ⟨_, g, rfl⟩ := h
  refine ⟨⟨_, GlobalTheory.Mem.ColAd.finN_mem hn hG g⟩, ?_⟩
  subst hn
  refine ⟨rfl, fun i j i' j' a b => ?_⟩
  obtain rfl := Fin.ext a
  obtain rfl := Fin.ext b
  unfold R3.matIn
  rw [mul_one]
  rfl

theorem gram_X' {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) : B.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := w.ok.spaces
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

set_option maxHeartbeats 2000000 in

theorem rx_std_read {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} (x : RXs t) :
    ∃ c : VV B.LL B.wts.sgTrue → t.r.z.R.cX.W, ∀ (h : Bridge.Gf (w.st Z).toD7.sp.X'), ∃ y : UAd B.sp.cm (B.R.N B.R.m - 1),
      ∀ (s : R3.TupU w.I (R3.usedOf w.I T Wt)) (φ : (mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel s.1).EqFun),
        t.r.z.R.B.jR s ((mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel s.1).res (mtildeKOk _ _ _ _ t.hX) φ) h =
          c (φ.1 (decoPt (F := B.fields.F) (E := B.fields.E) B.sp.cm _ ∅ (rowSG (B.primes w.px) w.I.sel s.1) (QuotientGroup.mk y))) := by
  obtain ⟨c, -, hc, -⟩ := x.std.1
  refine ⟨c, fun h => ?_⟩
  have hr : (w.st Z).toD7.sp.X'.rank = B.R.N B.R.m - 1 := by rw [(w.st Z).toD7.sp.X'_rank, rank_X'_eq]; rfl
  obtain ⟨y, hy⟩ := exists_matEq (D := (w.st Z).toD7) _ hr (gram_X' w) h
  refine ⟨y, fun s φ => hc B.sp.cm s (⟨mtildeKOk _ _ _ _ t.hX⟩, φ) h y ?_⟩
  rw [t.r.z.lev.beta.2]
  exact hy

theorem gram_V {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ B.R.m) :
    (B.sp.V j).gram = 1 := by
  obtain ⟨hs, -, -, -, -, h5⟩ := w.ok.spaces
  have hn : B.sp.Vneg j = false := B.V_pos j h1 h2
  rw [h5 j]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn, hn]

theorem rank_V {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : ℕ) : (B.sp.V j).rank = B.R.nV := by
  obtain ⟨hs, -, -, -, -, h5⟩ := w.ok.spaces
  rw [h5 j]
  rfl

set_option maxHeartbeats 2000000 in

theorem rx_std_readL {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} (x : RXs t) (i : Fin (w.st Z).toD7.R.m) :
    ∃ c : VV B.LL (B.wts.lamV ((i : ℕ) + 1)) → (t.r.z.R.cV i).W, ∀ (h : Bridge.Gf (Vc (w.st Z).toD7 i)), ∃ y : UAd B.sp.cm B.R.nV,
      ∀ (s : R3.TupU w.I (R3.usedOf w.I T Wt))
        (φ : (mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel s.1 ((i : ℕ) + 1)).EqFun),
        t.r.z.R.B.jL i s ((mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel s.1 ((i : ℕ) + 1)).res (mtKOk _ _ _ _ t.hX _) φ) h =
          c (φ.1 (decoPt (F := B.fields.F) (E := B.fields.E) B.sp.cm _ ∅ (rowSG (B.primes w.px) w.I.sel s.1) (QuotientGroup.mk y))) := by
  obtain ⟨c, -, hc, -⟩ := x.std.2 i
  refine ⟨c, fun h => ?_⟩
  obtain ⟨y, hy⟩ := exists_matEq (D := (w.st Z).toD7) _ (rank_V w _) (gram_V w _ (Nat.succ_pos _) i.2) h
  refine ⟨y, fun s φ => hc B.sp.cm s (⟨mtKOk _ _ _ _ t.hX _⟩, φ) h y ?_⟩
  rw [t.r.z.lev.beta.1 i]
  exact hy

end Standard

end GlobalTheory.Mem.Top.Bl.TieModel

end
