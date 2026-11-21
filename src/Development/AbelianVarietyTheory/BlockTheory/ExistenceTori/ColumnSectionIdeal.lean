import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslationFrames

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

abbrev MulIso (L : LB A.left) (N : ℕ) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])

abbrev FrameAt (L : LB A.left) (k : ℤ) {T : Over S} (x : T ⟶ A) : Type :=
  LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k))

theorem comp_mulA {T : Over S} (x : T ⟶ A) (N : ℕ) : x ≫ mulA A N = x ^ N := by
  induction N with
  | zero => simp [mulA, MonObj.comp_one]
  | succ n ih =>
    have ih' : x ≫ 𝟙 A ^ n = x ^ n := ih
    simp only [mulA, pow_succ, MonObj.comp_mul, ih', Category.comp_id]

theorem mulIsoT_le (L : LB A.left) (N : ℕ) (T : Over S) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, (snd T A ^ N).left] j ≤
      (snd T A).left ⁻¹ᵁ LB.wchart L ![𝟙 A.left, (mulA A N).left] j := by
  intro y hy
  have h0 : (snd T A).left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have h1 : (snd T A ^ N).left.base y ∈ (L.U (j 1) : Set A.left) := Set.mem_iInter.1 hy 1
  have e : (snd T A).left ≫ (mulA A N).left = (snd T A ^ N).left := by
    rw [← Over.comp_left, comp_mulA]
  rw [← e] at h1
  refine Set.mem_iInter.2 fun i => ?_
  fin_cases i
  · exact h0
  · exact h1

def mulIsoT (L : LB A.left) (N : ℕ) (α : MulIso A L N) (T : Over S) :
    LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]) where
  s := fun j => res (mulIsoT_le A L N T j) (pullU (snd T A).left _ (α.s j))

theorem one_left (T : Over S) : (1 : T ⟶ A).left = T.hom ≫ eSec A := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem originFrame_le (L : LB A.left) (T : Over S) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => (1 : T ⟶ A).left) j ≤
      LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) j :=
  le_of_eq (by rw [one_left])

def originFrame (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (T : Over S) :
    FrameAt A L k (1 : T ⟶ A) where
  s := fun j => res (originFrame_le A L T j) ((rigT A L rig T k).s j)

end GlobalTheory.IndefiniteRowSideFullHecke.TranslationFrames
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnSectionIdeal

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Row (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

abbrev Pol (Dw : Datum H) {l : Level H} (c : Coeff l) (n : ℕ) : Type :=
  MvPolynomial (Letter (E →+* ℂ) Dw.mult n) c.F

def intRing {l : Level H} (c : Coeff l) : Subring c.F := (algebraMap (𝓞 c.F) c.F).range

def Hset (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Pol Dw c n) :=
  HaO Dw.mult n c.F (intRing c) ComplexEmbedding.conjugate (fun τ => τ (H.rt : E) = H.rt0) (fun τ i => a (τ, i))

def HLat (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Submodule (𝓞 c.F) (Pol Dw c n) where
  carrier := Hset Dw c a n
  zero_mem' := ⟨⟨Submodule.zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩,
    fun _ => by simp⟩
  add_mem' := by
    classical
    rintro P Q ⟨⟨hP1, hP2, hP3⟩, hP4⟩ ⟨⟨hQ1, hQ2, hQ3⟩, hQ4⟩
    refine ⟨⟨Submodule.add_mem _ hP1 hQ1, fun σ i i' h t => ?_, fun m hm => ?_⟩, fun m => ?_⟩
    · rw [map_add, hP2 σ i i' h t, hQ2 σ i i' h t]
    · rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hP3 m h
      · exact hQ3 m h
    · rw [MvPolynomial.coeff_add]; exact Subring.add_mem _ (hP4 m) (hQ4 m)
  smul_mem' := by
    rintro r P ⟨⟨hP1, hP2, hP3⟩, hP4⟩
    have e : r • P = (algebraMap (𝓞 c.F) c.F r) • P := (algebraMap_smul _ r P).symm
    suffices hs : (algebraMap (𝓞 c.F) c.F r) • P ∈ Hset Dw c a n from
      (congrArg (fun Q => Q ∈ Hset Dw c a n) e).mpr hs
    refine ⟨⟨Submodule.smul_mem _ _ hP1, fun σ i i' h t => ?_, fun m hm => ?_⟩, fun m => ?_⟩
    · rw [map_smul, hP2 σ i i' h t]
    · exact hP3 m (MvPolynomial.support_smul hm)
    · rw [MvPolynomial.coeff_smul]; exact Subring.mul_mem _ ⟨r, rfl⟩ (hP4 m)

def admitted (l : Level H) (N : ℕ) : Prop := Odd N ∧ l.M ∣ N

open Classical in

def transIdeal (l : Level H) (N : ℕ) : Ideal (𝓞 E) :=
  ∏ 𝔓 ∈ (UniqueFactorizationMonoid.normalizedFactors l.Mb).toFinset,
    𝔓 ^ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(N : 𝓞 E)})).count 𝔓

variable {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

abbrev SecAt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ) : Type :=
  LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk y.x))

abbrev Jet : Type 1 :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ), SecAt Xo c y k → (Row Dw → ℕ) → S

variable {Xo c}

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnSectionIdeal
end
end
