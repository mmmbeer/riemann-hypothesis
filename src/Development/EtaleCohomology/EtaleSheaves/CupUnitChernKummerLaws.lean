import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

section
def LateralTheory.E.EtaleChapterEEight : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2 → GlobalTheory.EtC.D3 → GlobalTheory.EtC.E1 → GlobalTheory.EtC.E2 → GlobalTheory.EtC.E3 → GlobalTheory.EtC.E4 → GlobalTheory.EtC.E6 → GlobalTheory.EtC.E8
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

structure Base : Prop where
  (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6nat : DivisorNaturality) (a6ring : DivisorRingCompatibility) (a6supp : DivisorSupportCondition) (a6add : DivisorAdditivity)
  (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) (b1 : B1) (b2 : B2) (b3 : B3) (b4 : B4) (b5 : B5) (b7 : B7)
  (c1 : C1) (c2 : C2) (c3 : C3) (c4 : C4) (c5 : C5) (d1 : D1) (d2 : D2) (d3 : D3)
  (e1 : E1) (e2 : E2) (e3 : E3) (e4 : E4) (e6 : E6)

def PD (q : ℕ) (X : Scheme.{0}) (d : ℕ) : Prop :=
  ∃ tr : Ht q (sch.obj X) (2 * d) d ≃+ ZMod q, ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = tr ((cup q a b).cast (by ring) (by ring))

def CupUnitChernKummerLaws : Prop := DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity

def EtaleKunneth : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (r : Y ⟶ Spec (CommRingCat.of k)) [QuasiCompact p] [QuasiSeparated p]
    [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ) (b : ∀ s, Ht q (sch.obj Y) (deg s) j),
  (∀ m : ℤ, Function.Bijective fun c : {s // deg s = m} → ZMod q =>
    ∑ s : {s // deg s = m}, c s • ((b s.1).cast s.2 rfl : Ht q (sch.obj Y) m j)) →
  ∀ n i : ℤ, Function.Bijective fun a : ∀ s, Ht q (sch.obj X) (n - deg s) i =>
    ∑ s, ((cup q (pull _ (sch.map (pullback.fst p r)) _ _ (a s)) (pull _ (sch.map (pullback.snd p r)) _ _ (b s))).cast
      (by ring) rfl : Ht q (sch.obj (pullback p r)) n (i + j))

def LeafSupp : Prop := Base → ∀ (q : ℕ) [NeZero q] {X Z : Scheme.{0}} [IsNoetherian X] (ι : Z ⟶ X) [IsClosedImmersion ι],
  IsUnit (q : Γ(X, ⊤)) → ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → ∀ {n m i j : ℤ} (a : Ht q (sch.obj X) n i)
  (b : Ht q (sch.obj X) m j), pull _ (sch.map U.ι) _ _ a = 0 → pull _ (sch.map ι) _ _ b = 0 → cup q a b = 0

def LeafDiag : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ δ : Ht q (sch.obj (pullback p p)) (2 * d) d,
    (∀ W : (pullback p p).Opens, (W : Set ↥(pullback p p)) = (Set.range (pullback.diagonal p))ᶜ →
      pull _ (sch.map W.ι) _ _ δ = 0) ∧
    ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ p = 𝟙 _) (U : X.Opens), (U : Set X) = (Set.range x)ᶜ →
      ∀ c : Ht q (sch.obj X) (2 * d) d, pull _ (sch.map U.ι) _ _ c = 0 →
        ∃ m : ℤ, c = m • pull _ (sch.map (pullback.lift (p ≫ x) (𝟙 X) (by simp [hx]))) _ _ δ

def EtaleExcise : Prop := Base → ∀ (q : ℕ) [NeZero q] {X' X Z : Scheme.{0}} [IsNoetherian X] (f : X' ⟶ X) [IsProper f]
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsUnit (q : Γ(X, ⊤)) → ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → IsIso (f ∣_ U) →
  ∀ n i : ℤ, Function.Bijective (HK.pull (ZMod q)
    (mappingCone.map ((chains _).map (sch.map (pullback.fst f ι))) ((chains _).map (sch.map ι))
      ((chains _).map (sch.map (pullback.snd f ι))) ((chains _).map (sch.map f))
      (by simp only [← Functor.map_comp, pullback.condition])) (tw q i) n)

def EtalePrime : Prop := Base → ∀ (q : ℕ), q.Prime → ∀ (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  PD q X d

def LeafStep : Prop := Base → ∀ (a b : ℕ) [NeZero a] [NeZero b] (k : Type) [Field k] [IsAlgClosed k], IsUnit ((a * b : ℕ) : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  PD a X d → PD b X d → PD (a * b) X d

theorem pd_one (X : Scheme.{0}) (d : ℕ) : PD 1 X d := by
  have hs : ∀ n i : ℤ, Subsingleton (Ht 1 (sch.obj X) n i) := fun n i => Module.subsingleton (ZMod 1) _
  have := hs (2 * d) d
  let _ : Unique (Ht 1 (sch.obj X) (2 * d) d) := uniqueOfSubsingleton 0
  refine ⟨AddEquiv.ofUnique, fun n i φ => ⟨0, fun b => Subsingleton.elim _ _, fun y _ => (hs n i).elim _ _⟩⟩

theorem goal_of (hA : CupUnitChernKummerLaws) (hP : EtalePrime) (hS : LeafStep) : LateralTheory.E.EtaleChapterEEight := by
  intro a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 b1 b2 b3 b4 b5 b7 c1 c2 c3 c4 c5 d1 d2 d3 e1 e2 e3 e4 e6
  have B : Base := ⟨a1, a2, a3, a4, a5, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7,
    c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3, e4, e6⟩
  intro q hq k _ _ hu X _ p _ d _
  change PD q X d
  have hq0 := hq.out
  clear hq
  induction q using Nat.recOnMul with
  | zero => exact absurd rfl hq0
  | one => exact pd_one X d
  | prime l hl => exact hP B l hl k hu p d
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hq0
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hq0
    have : NeZero a := ⟨ha0⟩
    have : NeZero b := ⟨hb0⟩
    have hu' : IsUnit ((a : k) * (b : k)) := by simpa using hu
    exact hS B a b k hu p d (ha (isUnit_of_mul_isUnit_left hu') ha0) (hb (isUnit_of_mul_isUnit_right hu') hb0)

end LateralTheory.E.E8

end
end
