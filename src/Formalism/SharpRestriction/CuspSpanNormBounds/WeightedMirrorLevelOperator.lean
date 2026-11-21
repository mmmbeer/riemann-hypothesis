import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

section
open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.TopsChoicePartA

open Formalism.QuantumDeterminants

abbrev Mat (k0 r : ℕ) := Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ

abbrev Vec (k0 r : ℕ) := Fin (2 * r + (k0 + 1) + 1) → ℂ

structure Lev where
  k0 : ℕ
  r : ℕ
  z : Vec k0 r
  z' : Vec k0 r
  Wp : Type
  Wq : Type
  [nWp : NormedAddCommGroup Wp]
  [iWp : InnerProductSpace ℂ Wp]
  [fWp : FiniteDimensional ℂ Wp]
  [nWq : NormedAddCommGroup Wq]
  [iWq : InnerProductSpace ℂ Wq]
  [fWq : FiniteDimensional ℂ Wq]
  π : Mat k0 r → (Wp →L[ℂ] Wp)
  π' : Mat k0 r → (Wq →L[ℂ] Wq)
  μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ

attribute [instance] Lev.nWp Lev.iWp Lev.fWp Lev.nWq Lev.iWq Lev.fWq

namespace Lev

abbrev Hom (L : Lev) := L.Wq →L[ℂ] L.Wp

abbrev PF (L : Lev) := (Fin (L.r + 1) → ℂ) → L.Hom

abbrev POp (L : Lev) := Op (L.r + 1) L.Hom

abbrev GF (L : Lev) := Mat L.k0 L.r → L.Hom

def T (L : Lev) : ℝ := Tz (L.k0 + 1) L.r L.z
def T' (L : Lev) : ℝ := Tz (L.k0 + 1) L.r L.z'

def HC (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) : Prop :=
  Formalism.MainNotions.S.IsHCTypeW (L.k0 + 1) L.r L.z u L.π ∧ Formalism.MainNotions.S.IsHCTypeW (L.k0 + 1) L.r L.z' u' L.π' ∧
    ∀ i, ∃ m : ℤ, u i - u' i = m

def Std (L : Lev) : Prop :=
  inWb (L.k0 + 1) L.r L.z ∧ inWb (L.k0 + 1) L.r L.z' ∧ 0 < L.T ∧ 0 < L.T' ∧
    IsSection (L.k0 + 1) L.r L.z L.z' L.μsec

def xv (L : Lev) : Vec L.k0 L.r := if h : 0 < L.r then bvec (eI (L.k0 + 1) L.r ⟨0, h⟩) else L.z
def xv' (L : Lev) : Vec L.k0 L.r := if h : 0 < L.r then bvec (eI (L.k0 + 1) L.r ⟨0, h⟩) else L.z'

def flat (L : Lev) (v : Vec L.k0 L.r) : Vec L.k0 L.r := fun j => herm (Hpk (L.k0 + 1) L.r) (bvec j) v

def yv (L : Lev) (g : Mat L.k0 L.r) : Vec L.k0 L.r := g⁻¹ *ᵥ L.xv

def QQ (L : Lev) (Y : ℂ) : Fin 2 → Fin 2 → (L.GF → L.GF) :=
  QQop (m := 2 * L.r + L.k0) (EabH (Hpk (L.k0 + 1) L.r)) (((2 * L.r + L.k0 + 1 : ℕ) : ℂ) / 2) Y
    (fun g => L.yv g) (fun g => L.flat (L.yv g)) L.xv' (L.flat L.xv')

def Cap (L : Lev) (Y : ℂ) : L.GF → L.GF :=
  capelliH (Hpk (L.k0 + 1) L.r) (Y + ((2 * L.r + L.k0 + 1 : ℕ) : ℂ) / 2)

def KKop (L : Lev) : Set L.GF :=
  EqF (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' ∩ {J | ∃ ε : ℝ, 0 < ε ∧ J ∈ KKeps (L.k0 + 1) L.r L.z L.z' ε}

def B (L : Lev) (J : L.GF) : L.PF := Btr (L.k0 + 1) L.r L.z L.z' L.μsec J

def Img (L : Lev) : Set L.PF := {φ | ∃ J ∈ L.KKop, φ = L.B J}

def Rad (L : Lev) (Θ : L.GF → L.GF) (R : L.POp) : Prop :=
  HasRadialPart (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' L.μsec L.KKop Θ R

def BD (L : Lev) : Set (Fin (L.r + 1) → ℂ) := BDom (L.k0 + 1) L.r L.z L.z'

def IsRadQQ (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) : Prop :=
  ∀ (Y : ℂ) (a b : Fin 2), L.Rad (L.QQ Y a b) (R Y a b) ∧ LocalOn L.BD (R Y a b) ∧
    ∀ U : Set (Fin (L.r + 1) → ℂ), IsOpen U → U ⊆ L.BD → LocalOn U (R Y a b)

end Lev

section OpMat

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def scalOp (s : ℂ) : Op m E := fun f => s • f

def idOp : Op m E := fun f => f

def zeroOp : Op m E := fun _ => 0

def omMul {ι κ ν : Type*} [Fintype κ] (M : Matrix ι κ (Op m E)) (N : Matrix κ ν (Op m E)) :
    Matrix ι ν (Op m E) :=
  fun a b f => ∑ c, M a c (N c b f)

def omApply {ι κ : Type*} [Fintype κ] (M : Matrix ι κ (Op m E)) (x : κ → (Fin m → ℂ) → E) :
    ι → (Fin m → ℂ) → E :=
  fun a => ∑ b, M a b (x b)

def smat {ι κ : Type*} (S : Matrix ι κ ℂ) : Matrix ι κ (Op m E) := fun a b => scalOp (S a b)

def oneOM {ι : Type*} [DecidableEq ι] : Matrix ι ι (Op m E) := fun a b => if a = b then idOp else zeroOp

def EqOn' {ι κ : Type*} (S : Set ((Fin m → ℂ) → E)) (D : Set (Fin m → ℂ)) (M N : Matrix ι κ (Op m E)) : Prop :=
  ∀ a b, ∀ φ ∈ S, ∀ x ∈ D, M a b φ x = N a b φ x

def t1 {A : Type*} [Zero A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  fun ik jl => if ik.2 = jl.2 then M ik.1 jl.1 else 0

def t2 {A : Type*} [Zero A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  fun ik jl => if ik.1 = jl.1 then M ik.2 jl.2 else 0

end OpMat

def Pflip : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ik jl => if ik.1 = jl.2 ∧ ik.2 = jl.1 then 1 else 0

def Rh (D : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ik jl => ((if ik = jl then D else 0) - Pflip ik jl) / (D - 1)

def J2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

def Us (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; -s, 1]

def UsInv (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; s, 1]

abbrev Letter := Bool × ℝ

abbrev Word := List Letter

abbrev AuxiliarySlotStates (n : ℕ) := Fin n → Fin 2

def e1s (n : ℕ) : AuxiliarySlotStates n := fun _ => 0

structure Mod (m : ℕ) (E : Type*) (n : ℕ) where
  RR : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) (Op m E)
  TT : ℂ → Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)
  q : ℂ → ℂ

section Words

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def modStart (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op m E)) (q : ℂ → ℂ) : Mod m E 0 where
  RR := oneOM
  TT := fun Y a b => Q Y a.1 b.1
  q := q

def stepPlus {n : ℕ} (Ya : ℝ) (M : Mod m E n) : Mod m E (n + 1) where
  RR := fun α β f => ∑ γ : AuxiliarySlotStates n, M.RR (Fin.tail α) γ (M.TT (Ya : ℂ) (α 0, γ) (β 0, Fin.tail β) f)
  TT := fun Y a b f => ∑ ρ : Fin 2,
    M.TT Y (a.1, Fin.tail a.2) (ρ, Fin.tail b.2) (Rh (Y - (Ya : ℂ)) (ρ, a.2 0) (b.1, b.2 0) • f)
  q := fun Y => M.q Y * ((Y - (Ya : ℂ)) + 1) / (Y - (Ya : ℂ))

def stepMinus {n : ℕ} (Yb : ℝ) (M : Mod m E n) : Mod m E (n + 1) where
  RR := fun α β f => ∑ γ : AuxiliarySlotStates n, M.RR (Fin.tail α) γ (M.TT (Yb : ℂ) (β 0, γ) (α 0, Fin.tail β) f)
  TT := fun Y a b f => ∑ ρ : Fin 2,
    Rh ((Yb : ℂ) - Y) (a.1, b.2 0) (ρ, a.2 0) • M.TT Y (ρ, Fin.tail a.2) (b.1, Fin.tail b.2) f
  q := fun Y => M.q Y * ((Yb : ℂ) - Y) / (((Yb : ℂ) - Y) - 1)

def step {n : ℕ} (l : Letter) (M : Mod m E n) : Mod m E (n + 1) :=
  if l.1 then stepPlus l.2 M else stepMinus l.2 M

def wordMod (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op m E)) (q : ℂ → ℂ) : (w : Word) → Mod m E w.length
  | [] => modStart Q q
  | l :: w => step l (wordMod Q q w)

end Words

def Generic (w : Word) : Prop := w.Pairwise (fun a b => a.2 ≠ b.2 ∧ a.2 - b.2 ≠ 1 ∧ b.2 - a.2 ≠ 1)

def OffPoles (w : Word) (Y : ℂ) : Prop :=
  ∀ l ∈ w, Y ≠ (l.2 : ℂ) ∧ Y ≠ (l.2 : ℂ) + 1 ∧ Y ≠ (l.2 : ℂ) - 1

def Admissible (I : Set ℝ) (w : Word) : Prop :=
  (∀ l ∈ w, l.2 ∈ I) ∧ w.Pairwise (fun a b => 2 < |a.2 - b.2|)

def Interlace {k0 : ℕ} (u : Fin (k0 + 1) → ℝ) (ρ : Fin k0 → ℝ) : Prop :=
  ∀ j : Fin k0, ρ j < u j.castSucc ∧ u j.succ < ρ j

section Vectors

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def vLetter (c : Fin m) (l : Letter) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  if l.1 then Tmat c (l.2 : ℂ) else TmatV c (l.2 : ℂ)

def vLetterStar (c : Fin m) (l : Letter) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  if l.1 then TmatStar c (l.2 : ℂ) else (Tmat c (l.2 : ℂ)).transpose

def bT (c : Fin m) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op m E)
  | [] => oneOM
  | l :: w => fun α β f => vLetter c l (α 0) (β 0) (bT c w (Fin.tail α) (Fin.tail β) f)

def bTstar (c : Fin m) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op m E)
  | [] => oneOM
  | l :: w => fun α β f => bTstar c w (Fin.tail α) (Fin.tail β) (vLetterStar c l (α 0) (β 0) f)

end Vectors

namespace Lev

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def betaB (L : Lev) (φ ψ : L.PF) : ℂ :=
  ∫ x : Fin (L.r + 1) → ℂ, (((∏ a : Fin L.r, Complex.normSq (cOf x a))⁻¹ : ℝ) : ℂ) *
    Formalism.MainNotions.S.hsInner (φ x) (ψ x)

def form (L : Lev) {ι : Type*} [Fintype ι] (M : Matrix ι ι L.POp) (x y : ι → L.PF) : ℂ :=
  ∑ a, L.betaB (omApply M x a) (y a)

def HermOn (L : Lev) {ι : Type*} [Fintype ι] (S : Set L.PF) (M : Matrix ι ι L.POp) : Prop :=
  ∀ x y : ι → L.PF, (∀ a, x a ∈ S) → (∀ a, y a ∈ S) →
    L.form M x y = ∑ a, L.betaB (x a) (omApply M y a)

def PosOn (L : Lev) {ι : Type*} [Fintype ι] (S : Set L.PF) (M : Matrix ι ι L.POp) : Prop :=
  ∀ x : ι → L.PF, (∀ a, x a ∈ S) → (L.form M x x).im = 0 ∧ 0 ≤ (L.form M x x).re

def matNorm {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖

def Eword (L : Lev) (w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1))) (F : L.GF) :
    L.GF :=
  w.foldr (fun ab f => EabH (Hpk (L.k0 + 1) L.r) ab.1 ab.2 f) F

def CC (L : Lev) (A : ℝ) (mm : ℕ) (F : L.GF) : Prop :=
  (∃ U : Set (Mat L.k0 L.r), IsOpen U ∧ UH (Hpk (L.k0 + 1) L.r) ⊆ U ∧ ContDiffOn ℝ (mm : ℕ∞) F U) ∧
    ∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ mm →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), ‖L.Eword w F g‖ ≤ C * (1 + matNorm g) ^ (-A)

structure Haar (L : Lev) where
  μW : Measure (Mt (L.k0 + 1) L.r)
  μN : Measure (Mt (L.k0 + 1) L.r)
  μW' : Measure (Mt (L.k0 + 1) L.r)

def Haar.Ok {L : Lev} (h : L.Haar) : Prop :=
  Formalism.MainNotions.S.IsHaarOn (UWset (L.k0 + 1) L.r L.z) h.μW ∧ Formalism.MainNotions.S.IsHaarOn (Nset (L.k0 + 1) L.r) h.μN ∧
    Formalism.MainNotions.S.IsHaarOn (UWset (L.k0 + 1) L.r L.z') h.μW'

def KK (L : Lev) (h : L.Haar) (A : ℝ) (mm : ℕ) : Set L.GF :=
  {J | ∃ F : L.GF, L.CC A mm F ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ tsupport F, ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g) ∧
    J = besselJ (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' h.μW h.μN h.μW' F}

def ImgK (L : Lev) (h : L.Haar) (A : ℝ) (mm : ℕ) : Set L.PF :=
  {φ | ∃ J ∈ L.KK h A mm, ContDiffOn ℝ ∞ (L.B J) L.BD ∧ φ = L.B J}

end Lev

def liftVectorLevel {k0 r : ℕ} (v : Vec k0 r) : Vec k0 (r + 1) :=
  fun p => liftVec (k0 + 1) 1 r v (Fin.cast (by omega) p)

def ι1 {k0 r : ℕ} (g : Mat k0 r) : Mat k0 (r + 1) :=
  fun p q => ιLev (k0 + 1) 1 r g (Fin.cast (by omega) p) (Fin.cast (by omega) q)

def Lev.up (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp))
    (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq)) : Lev where
  k0 := L.k0
  r := L.r + 1
  z := liftVectorLevel L.z
  z' := liftVectorLevel L.z'
  Wp := L.Wp
  Wq := L.Wq
  π := pb
  π' := pb'
  μsec := L.μsec

def Lev.Compat (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp))
    (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq)) : Prop :=
  ∀ g : Mat L.k0 L.r, L.π g = pb (ι1 g) ∧ L.π' g = pb' (ι1 g)

def liftOM {ι κ : Type*} {m : ℕ} {E : Type*} (M : Matrix ι κ (Op m E)) : Matrix ι κ (Op (m + 1) E) :=
  fun a b => liftOp (M a b)

def fs {m : ℕ} (s : ℂ) (x : Fin (m + 1) → ℂ) : ℂ := Complex.exp (s * x 0 - star s * star (x 0))

def fsC (s c : ℂ) : ℂ := Complex.exp (s * c - star s * star c)

def UUs (s : ℂ) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) ℂ
  | [] => 1
  | l :: w => fun α β => (if l.1 then Us s else Us (star s)) (α 0) (β 0) * UUs s w (Fin.tail α) (Fin.tail β)

def UUsInv (s : ℂ) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) ℂ
  | [] => 1
  | l :: w => fun α β =>
      (if l.1 then UsInv s else UsInv (star s)) (α 0) (β 0) * UUsInv s w (Fin.tail α) (Fin.tail β)

section Waves

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def Vop (s : ℂ) (w : Word) : Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E) :=
  fun α β φ x => (fs s x * UUsInv s w α β) • φ x

def VopStar (s : ℂ) (w : Word) : Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E) :=
  fun α β φ x => (star (fs s x) * star (UUsInv s w β α)) • φ x

def VopInv (s : ℂ) (w : Word) : Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E) :=
  fun α β φ x => ((fs s x)⁻¹ * UUs s w α β) • φ x

def actOnPositions {n : ℕ} (M : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) (Op m E)) : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.1 = b.1 then M a.2 b.2 else 0

def onPosition0 {n : ℕ} (S : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.2 = b.2 then scalOp (S a.1 b.1) else 0

def one_le_card_tops {n : ℕ} (M : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)) :
    Matrix (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.2.1 = b.2.1 then M (a.1, a.2.2) (b.1, b.2.2) else 0

def tensorSecondPosition {n : ℕ} (M : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)) :
    Matrix (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.1 = b.1 then M (a.2.1, a.2.2) (b.2.1, b.2.2) else 0

def Rh12 {n : ℕ} (D : ℂ) : Matrix (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.2.2 = b.2.2 then scalOp (Rh D (a.1, a.2.1) (b.1, b.2.1)) else 0

def tr0 {n : ℕ} (M : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)) :
    Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => M (b.1, a.2) (a.1, b.2)

def JRR {n : ℕ} (M : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) (Op m E)) : Matrix (AuxiliarySlotStates (n + 1)) (AuxiliarySlotStates (n + 1)) (Op m E) :=
  fun α β f => J2 (α 0) (β 0) • M (Fin.tail α) (Fin.tail β) f

def capProd (sg : ℂ) (t11 : ℂ → Op m E) : Word → Op m E
  | [] => idOp
  | l :: w => fun φ => capProd sg t11 w (sg • t11 (l.2 : ℂ) φ)

end Waves

namespace Lev

def UUset (L : Lev) (g : Mat L.k0 L.r) : Set (Mat L.k0 L.r) :=
  {h | h ∈ UWset (L.k0 + 1) L.r L.z' ∧ h *ᵥ (g⁻¹ *ᵥ L.z) = g⁻¹ *ᵥ L.z}

def blockU (L : Lev) (h : Matrix (Fin L.k0) (Fin L.k0) ℂ) : Mat L.k0 L.r :=
  fun i j =>
    if hi : L.r ≤ i.val ∧ i.val < L.r + L.k0 then
      (if hj : L.r ≤ j.val ∧ j.val < L.r + L.k0 then h ⟨i.val - L.r, by omega⟩ ⟨j.val - L.r, by omega⟩ else 0)
    else (if i = j then 1 else 0)

def IsFrameU (L : Lev) (g f : Mat L.k0 L.r) : Prop :=
  f ∈ UH (Hpk (L.k0 + 1) L.r) ∧
    (∀ a : Fin L.r, f *ᵥ bvec (eI (L.k0 + 1) L.r a) = bvec (eI (L.k0 + 1) L.r a) ∧
      f *ᵥ bvec (esI (L.k0 + 1) L.r a) = bvec (esI (L.k0 + 1) L.r a)) ∧
    ∀ j : Fin L.k0,
      herm (Hpk (L.k0 + 1) L.r) (f *ᵥ bvec (wI (L.k0 + 1) L.r j.castSucc.castSucc)) (g⁻¹ *ᵥ L.z) = 0 ∧
      herm (Hpk (L.k0 + 1) L.r) (f *ᵥ bvec (wI (L.k0 + 1) L.r j.castSucc.castSucc)) L.z' = 0

open Classical in

def frameU (L : Lev) (g : Mat L.k0 L.r) : Mat L.k0 L.r :=
  if h : ∃ f, L.IsFrameU g f then Classical.choose h else 1

def isoSub (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : Submodule ℂ L.Wq :=
  sSup {S | Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos L.k0)
    (fun h => L.π' (L.frameU g * L.blockU h * (L.frameU g)⁻¹)) (lowK (Formalism.MainNotions.S.allPos L.k0) ρ) S}

def HomU (L : Lev) (g : Mat L.k0 L.r) : Set L.Hom :=
  {T | ∀ h ∈ L.UUset g, (L.π (g * h * g⁻¹)).comp T = T.comp (L.π' h)}

def lineSet (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : Set L.Hom :=
  {T | T ∈ L.HomU g ∧ ∀ v ∈ (L.isoSub g ρ)ᗮ, T v = 0}

def IsHSProj (L : Lev) (P : L.Hom →L[ℂ] L.Hom) (S : Set L.Hom) : Prop :=
  P.comp P = P ∧ (∀ A B, Formalism.MainNotions.S.hsInner (P A) B = Formalism.MainNotions.S.hsInner A (P B)) ∧
    (∀ A, P A ∈ S) ∧ ∀ A ∈ S, P A = A

open Classical in

def lineP (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : L.Hom →L[ℂ] L.Hom :=
  if h : ∃ P, L.IsHSProj P (L.lineSet g ρ) then Classical.choose h else 0

def pt (L : Lev) (x : Fin (L.r + 1) → ℂ) : Mat L.k0 L.r := bigCell (L.k0 + 1) L.r (cOf x) (L.μsec (zOf x))

def GGx (L : Lev) (x : Fin (L.r + 1) → ℂ) : ℝ := Complex.normSq (zOf x) - L.T * L.T'

end Lev

noncomputable def sCut {k0 : ℕ} (u u' : Fin (k0 + 1) → ℝ) (I : Set ℝ) : ℝ := by
  classical
  exact if h : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ρ : Fin k0 → ℝ, Interlace u ρ → Interlace u' ρ →
      ∀ Y ∈ I, 0 < s * (xPoly ρ (Y : ℂ)).re then Classical.choose h else 1

def castOp {E : Type*} {a b : ℕ} (h : a = b) (R : Op a E) : Op b E := h ▸ R

def liftK {m : ℕ} {E : Type*} : (i : ℕ) → Op m E → Op (m + i) E
  | 0, R => R
  | i + 1, R => liftOp (liftK i R)

def Lev.down (Lt : Lev) (i r' : ℕ) (h : i + r' = Lt.r) : Lev where
  k0 := Lt.k0
  r := r'
  z := fun p => Lt.z ⟨p.val + i, by omega⟩
  z' := fun p => Lt.z' ⟨p.val + i, by omega⟩
  Wp := Lt.Wp
  Wq := Lt.Wq
  π := fun g => Lt.π (fun p q => ιLev (Lt.k0 + 1) i r' g (Fin.cast (by omega) p) (Fin.cast (by omega) q))
  π' := fun g => Lt.π' (fun p q => ιLev (Lt.k0 + 1) i r' g (Fin.cast (by omega) p) (Fin.cast (by omega) q))
  μsec := Lt.μsec

def Lev.liftDown (Lt : Lev) (i r' : ℕ) (h : i + r' = Lt.r) (R : (Lt.down i r' h).POp) : Lt.POp :=
  castOp (by show r' + 1 + i = Lt.r + 1; omega) (liftK i R)

section Prods

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Tprod (Y : ℂ) : (i : ℕ) → i ≤ m → Matrix (Fin 2) (Fin 2) (Op (m + 1) E)
  | 0, _ => oneOM
  | i + 1, h => omMul (Tmat (⟨i, by omega⟩ : Fin (m + 1)) Y) (Tprod Y i (by omega))

def TprodStar (Y : ℂ) : (i : ℕ) → i ≤ m → Matrix (Fin 2) (Fin 2) (Op (m + 1) E)
  | 0, _ => oneOM
  | i + 1, h => omMul (TprodStar Y i (by omega)) (TmatStar (⟨i, by omega⟩ : Fin (m + 1)) Y)

def bTprod (w : Word) : (i : ℕ) → i ≤ m → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E)
  | 0, _ => oneOM
  | i + 1, h => omMul (bT (⟨i, by omega⟩ : Fin (m + 1)) w) (bTprod w i (by omega))

def uw (w : Word) (i : ℕ) (h : i ≤ m) : AuxiliarySlotStates w.length → Op (m + 1) E :=
  fun β => bTprod w i h β (e1s _)

end Prods

namespace Lev

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Dom (L : Lev) : Set (Fin (L.r + 1) → ℂ) := {p | 0 < L.GGx p ∧ zOf p ≠ 0}

def IsDiffZ (L : Lev) (O : L.POp) : Prop :=
  ∃ (N : ℕ) (a : Fin N → Fin N → (Fin (L.r + 1) → ℂ) → (L.Hom →L[ℂ] L.Hom)),
    (∀ i j, ContDiffOn ℝ ∞ (a i j) L.Dom) ∧
    ∀ φ : L.PF, ∀ p ∈ L.Dom, O φ p =
      ∑ i : Fin N, ∑ j : Fin N, a i j p ((wirt (Fin.last L.r))^[i] ((wirtBar (Fin.last L.r))^[j] φ) p)

def IsTriDiff (L : Lev) {n : ℕ} (F : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) L.POp) : Prop :=
  (∀ α β, L.IsDiffZ (F α β)) ∧
    (∃ e : AuxiliarySlotStates n ≃ Fin (Fintype.card (AuxiliarySlotStates n)), ∀ α β, e α < e β → ∀ φ : L.PF, ∀ p ∈ L.Dom, F α β φ p = 0) ∧
    ∀ α, ∃ a : (Fin (L.r + 1) → ℂ) → (L.Hom →L[ℂ] L.Hom),
      (∀ p ∈ L.Dom, IsUnit (a p)) ∧ ∀ φ : L.PF, ∀ p ∈ L.Dom, F α α φ p = a p (φ p)

def dw (L : Lev) {n : ℕ} (N : ℕ) (c : AuxiliarySlotStates n → (Fin L.k0 → ℝ) → ℝ) (α : AuxiliarySlotStates n)
    (p : Fin (L.r + 1) → ℂ) (A : L.Hom) : L.Hom :=
  ((Complex.normSq (zOf p) / L.GGx p) ^ N : ℝ) • ∑ᶠ ρ : Fin L.k0 → ℝ, ((c α ρ : ℝ) : ℂ) • L.lineP (L.pt p) ρ A

def act (L : Lev) (h n h' n' : Mat L.k0 L.r) (F : L.GF) : L.GF := fun g =>
  (psi (L.k0 + 1) L.r L.z cStd n * star (psi (L.k0 + 1) L.r L.z' cStd n')) •
    ((L.π h).comp ((F (h⁻¹ * n⁻¹ * g * n' * h')).comp (L.π' h'⁻¹)))

def IsInv (L : Lev) (Θ : L.GF → L.GF) : Prop :=
  ∀ h ∈ UWset (L.k0 + 1) L.r L.z, ∀ n ∈ Nset (L.k0 + 1) L.r, ∀ h' ∈ UWset (L.k0 + 1) L.r L.z',
    ∀ n' ∈ Nset (L.k0 + 1) L.r, ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F →
      ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), Θ (L.act h n h' n' F) g = L.act h n h' n' (Θ F) g

def EwordV (L : Lev) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1))) (a : Mat L.k0 L.r → V) :
    Mat L.k0 L.r → V :=
  w.foldr (fun ab f => EabH (Hpk (L.k0 + 1) L.r) ab.1 ab.2 f) a

def AA (L : Lev) : Set (L.GF → L.GF) :=
  {Θ | L.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)))
    (a : Fin N → Mat L.k0 L.r → (L.Hom →L[ℂ] L.Hom)),
    (∀ j, ∃ U : Set (Mat L.k0 L.r), IsOpen U ∧
      UH (Hpk (L.k0 + 1) L.r) ∩ {g | 0 < Gf (L.k0 + 1) L.r L.z L.z' g} ⊆ U ∧ ContDiffOn ℝ ∞ (a j) U) ∧
    (∀ j, ∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), ∀ ε : ℝ, 0 < ε →
      ∃ (C : ℝ) (d : ℕ), ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
        ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g → ‖L.EwordV w (a j) g‖ ≤ C * (1 + matNorm g) ^ d) ∧
    ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
      0 < Gf (L.k0 + 1) L.r L.z L.z' g → Θ F g = ∑ j, a j g (L.Eword (ws j) F g)}

def wmod (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) (sg : ℝ) (u u' : Fin (L.k0 + 1) → ℝ)
    (w : Word) : Mod (L.r + 1) L.Hom w.length :=
  wordMod (fun Y a b => fun φ => ((sg : ℝ) : ℂ) • R Y a b φ) (fun Y => qPoly L.T L.T' u u' Y) w

end Lev

def Big (C : ℝ) (L : Lev) (N : ℕ) (A : ℝ) (mm : ℕ) : Prop :=
  C * ((L.r : ℝ) + 1) ^ 4 * ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) ≤ A ∧
  C * ((L.r : ℝ) + 1) ^ 4 * ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) ≤ (mm : ℝ)

def HypC (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ) : Prop :=
  L.Std ∧ L.HC u u' ∧ Formalism.MainNotions.S.IsCutS u u' I ∧ ∃ ρ : Fin L.k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ

namespace Lev

def IsPolyCoef (L : Lev) (a : Mat L.k0 L.r → ℂ) : Prop :=
  ∃ P : MvPolynomial ((Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)) ⊕
      (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1))) ℂ,
    ∀ g, a g = MvPolynomial.eval (Sum.elim (fun ij => g ij.1 ij.2) (fun ij => star (g ij.1 ij.2))) P

def AApoly (L : Lev) : Set (L.GF → L.GF) :=
  {Θ | L.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)))
    (a : Fin N → Mat L.k0 L.r → ℂ), (∀ j, L.IsPolyCoef (a j)) ∧
    ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
      Θ F g = ∑ j, a j g • L.Eword (ws j) F g}

end Lev

def blockK {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j => if hi : i.val < k then (if hj : j.val < k then h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
    else (if i = j then 1 else 0)

def isoK {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ → (H →L[ℂ] H)) (u : Fin k → ℝ) : Submodule ℂ H :=
  sSup {S | Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos k) (fun h => σ (blockK h)) (lowK (Formalism.MainNotions.S.allPos k) u) S}

def lJ (L : Lev) (h : L.Haar) (F : L.GF) : L.GF :=
  besselJ (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' h.μW h.μN h.μW' F

def lbeta (L : Lev) (h : L.Haar) (F F' : L.GF) : ℂ := L.betaB (L.B (lJ L h F)) (L.B (lJ L h F'))

def SuppGe (L : Lev) (ε : ℝ) (F : L.GF) : Prop := ∀ g ∈ tsupport F, ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g

section Deg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def AAdeg (L : Lev) (ε Dg : ℝ) (d : ℕ) (Θ : L.GF → L.GF) : Prop :=
  ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)))
    (a : Fin N → Mat L.k0 L.r → (L.Hom →L[ℂ] L.Hom)),
    (∀ j, (ws j).length ≤ d) ∧
    (∀ j, ∃ U : Set (Mat L.k0 L.r), IsOpen U ∧
      UH (Hpk (L.k0 + 1) L.r) ∩ {g | 0 < Gf (L.k0 + 1) L.r L.z L.z' g} ⊆ U ∧ ContDiffOn ℝ ∞ (a j) U) ∧
    (∀ j, ∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ d + 5 →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g →
        ‖L.EwordV w (a j) g‖ ≤ C * (1 + Lev.matNorm g) ^ Dg) ∧
    ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
      0 < Gf (L.k0 + 1) L.r L.z L.z' g → Θ F g = ∑ j, a j g (L.Eword (ws j) F g)

end Deg

def LemmaBCont (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm →
    ∀ h : L.Haar, h.Ok → ∃ C : ℝ, ∀ (F F' : L.GF) (ν ν' : ℝ), L.CC A mm F → L.CC A mm F' →
      (∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ mm →
        ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), (1 + Lev.matNorm g) ^ A * ‖L.Eword w F g‖ ≤ ν) →
      (∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ mm →
        ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), (1 + Lev.matNorm g) ^ A * ‖L.Eword w F' g‖ ≤ ν') →
      ‖lbeta L h F F'‖ ≤ C * ν * ν'

def LemmaBAdj (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ μG : Measure (Mt (L.k0 + 1) L.r), Formalism.MainNotions.S.IsHaarOn (UH (Hpk (L.k0 + 1) L.r)) μG →
    ∀ Θ Θs : L.GF → L.GF, Θ ∈ L.AA → Θs ∈ L.AA →
      (∀ F F' : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → SmoothOnH (Hpk (L.k0 + 1) L.r) F' →
        HasCompactSupport F → HasCompactSupport F' → (∃ ε : ℝ, 0 < ε ∧ SuppGe L ε F ∧ SuppGe L ε F') →
        ∫ x, Formalism.MainNotions.S.hsInner (Θ F (Matrix.of x)) (F' (Matrix.of x)) ∂μG =
          ∫ x, Formalism.MainNotions.S.hsInner (F (Matrix.of x)) (Θs F' (Matrix.of x)) ∂μG) →
    ∀ (ε Dg : ℝ) (d : ℕ), 0 < ε → 0 ≤ Dg → AAdeg L ε Dg d Θ → AAdeg L ε Dg d Θs →
    ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm → ∀ h : L.Haar, h.Ok →
      ∀ F F' : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → SmoothOnH (Hpk (L.k0 + 1) L.r) F' →
        L.CC (A + Dg) (mm + d) F → L.CC (A + Dg) (mm + d) F' → SuppGe L ε F → SuppGe L ε F' →
        lbeta L h (Θ F) F' = lbeta L h F (Θs F')

def LemmaBRad (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ Θ : L.GF → L.GF, Θ ∈ L.AA →
    ∀ (ε Dg : ℝ) (d : ℕ), 0 < ε → 0 ≤ Dg → AAdeg L ε Dg d Θ →
    ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm → ∀ h : L.Haar, h.Ok →
      ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → L.CC (A + Dg) (mm + d) F → SuppGe L ε F →
        ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), 0 < Gf (L.k0 + 1) L.r L.z L.z' g →
          (∀ l, Dmin (L.k0 + 1) L.r L.z L.z' g l ≠ 0) →
          ∀ J' : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) J' →
            (∃ U : Set (Mat L.k0 L.r), IsOpen U ∧ g ∈ U ∧
              ∀ g' ∈ U, g' ∈ UH (Hpk (L.k0 + 1) L.r) → J' g' = lJ L h F g') →
            lJ L h (Θ F) g = Θ J' g

def LemmaBInt (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm →
    ∀ h : L.Haar, h.Ok → ∀ F F' : L.GF, L.CC A mm F → L.CC A mm F' →
      MeasureTheory.Integrable (fun x : Fin (L.r + 1) → ℂ => (((∏ a : Fin L.r, Complex.normSq (cOf x a))⁻¹ : ℝ) : ℂ) *
        Formalism.MainNotions.S.hsInner (L.B (lJ L h F) x) (L.B (lJ L h F') x))


def LemmaBThreeClauses (CB : ℝ) : Prop := LemmaBCont CB ∧ LemmaBAdj CB ∧ LemmaBRad CB

def LemmaB (CB : ℝ) : Prop := LemmaBCont CB ∧ LemmaBAdj CB ∧ LemmaBRad CB ∧ LemmaBInt CB

end Formalism.MainNotions.S.TopsChoicePartA
end
end

section
noncomputable section

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Dr {r : ℕ} (x : Fin (r + 1) → ℂ) : ℂ := ∏ a : Fin r, cOf x a

def Dr1 {r : ℕ} (x : Fin (r + 1) → ℂ) : ℂ := Dr x * zOf x

def GG {r : ℕ} (T T' : ℝ) (x : Fin (r + 1) → ℂ) : ℂ := ((Complex.normSq (zOf x) - T * T' : ℝ) : ℂ)

def Gfn {r : ℕ} (T T' : ℝ) (x : Fin (r + 1) → ℂ) : ℂ :=
  ((Complex.normSq (Dr x) : ℝ) : ℂ) * GG T T' x

def mulF {m : ℕ} (f : (Fin m → ℂ) → ℂ) : Op m E := fun φ x => f x • φ x

def mulE {m : ℕ} (e : (Fin m → ℂ) → E →L[ℂ] E) : Op m E := fun φ x => e x (φ x)

def one {m : ℕ} : Op m E := fun φ => φ

def vecT {m : ℕ} (M : Matrix (Fin 2) (Fin 2) (Op m E)) (v : Fin 2 → Op m E) : Fin 2 → Op m E :=
  fun a => ∑ b : Fin 2, M a b ∘ v b

def vv {r : ℕ} (Y : ℂ) : (i : ℕ) → i ≤ r → Fin 2 → Op (r + 1) E
  | 0, _ => ![one, 0]
  | i + 1, h => vecT (Tmat (⟨i, by omega⟩ : Fin (r + 1)) Y) (vv Y i (by omega))

def vvV {r : ℕ} (Y : ℂ) : (i : ℕ) → i ≤ r → Fin 2 → Op (r + 1) E
  | 0, _ => ![one, 0]
  | i + 1, h => vecT (TmatV (⟨i, by omega⟩ : Fin (r + 1)) Y) (vvV Y i (by omega))

def Ar (r : ℕ) (Y : ℂ) : Op (r + 1) E := vv Y r le_rfl 0

def Br (r : ℕ) (Y : ℂ) : Op (r + 1) E := vv Y r le_rfl 1

def ArV (r : ℕ) (Y : ℂ) : Op (r + 1) E := vvV Y r le_rfl 0

def BrV (r : ℕ) (Y : ℂ) : Op (r + 1) E := vvV Y r le_rfl 1

def Ahat (r : ℕ) (Y : ℂ) : Op (r + 1) E := mulF Dr ∘ Ar r Y

def AhatV (r : ℕ) (Y : ℂ) : Op (r + 1) E := mulF (fun x => star (Dr x)) ∘ ArV r Y

def Rhat (r : ℕ) (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => star (Dr x)) ∘ (Q Y 1 0 ∘ Ar r Y + Q Y 1 1 ∘ Br r Y)

def dZ (r : ℕ) : Op (r + 1) E := wirt (Fin.last r)

def dZb (r : ℕ) : Op (r + 1) E := wirtBar (Fin.last r)

def nabla (r : ℕ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E := dZ r + mulE h

def l0 (r : ℕ) (T T' : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  -nabla r h - mulF (fun x => (Y + 1 / 2) * star (zOf x) / GG T T' x)

def m0 (r : ℕ) (T T' : ℝ) (hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  dZb r - mulE hs - mulF (fun x => (Y - 1 / 2) * zOf x / GG T T' x)

section Lines

variable {k0 : ℕ} {Rho : Type*}

def xInvFib {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, (xPoly (ρp ρ) Y)⁻¹ • P ρ x

def shInv {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (l : Fin k0)
    (Y : ℂ) : (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, (Y + (ρp ρ l : ℂ))⁻¹ • P ρ x

def tauInv {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => (GG T T' x)⁻¹) ∘ mulE (xInvFib ρp P Y)

def lOp {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (Y : ℂ) : Op (r + 1) E :=
  tauInv T T' ρp P Y ∘ Q Y 1 0

def mOp {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (Y : ℂ) : Op (r + 1) E :=
  tauInv T T' ρp P Y ∘ Q Y 0 1

def lDec {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    Op (r + 1) E :=
  l0 r T T' h Y + mulF (fun x => (GG T T' x)⁻¹) ∘ ∑ l : Fin k0, mulE (shInv ρp P l Y) ∘ mulE (SS l)

end Lines

def SSnat {r : ℕ} (s : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E :=
  mulF (fun x => star (Dr x) / Dr x) ∘ mulE s

def R0 (r : ℕ) (T T' : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => star (Dr x) * GG T T' x) ∘ (l0 r T T' h Y ∘ Ar r Y + Br r Y)

def weightedMirrorLevelOperator (r : ℕ) (T T' : ℝ) (hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => Dr x * GG T T' x) ∘ (m0 r T T' hs Y ∘ ArV r Y + BrV r Y)

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

structure Base (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where

  k0 : ℕ
  T : ℝ
  T' : ℝ
  u : Fin (k0 + 1) → ℝ
  u' : Fin (k0 + 1) → ℝ
  I : Set ℝ

  sgn : ℂ

  hs : E → E → ℂ

  fadj : (E →L[ℂ] E) → (E →L[ℂ] E)

  Rho : Type

  IsType : Rho → Prop

  rhoP : Rho → Fin k0 → ℝ

structure Ctx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Base E) (r : ℕ) where

  Dom : Set (Fin (r + 1) → ℂ)

  cls : Set ((Fin (r + 1) → ℂ) → E)

  clsF : Set ((Fin (r + 1) → ℂ) → E)

  beta : ((Fin (r + 1) → ℂ) → E) → ((Fin (r + 1) → ℂ) → E) → ℂ

  P : B.Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E

  Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)

  AA : Set (Op (r + 1) E)

  RR : (w : List (Bool × ℝ)) → Matrix (Fin w.length → Fin 2) (Fin w.length → Fin 2) (Op (r + 1) E)

  TT : (w : List (Bool × ℝ)) → ℂ →
    Matrix (Fin 2) (Fin 2) (Matrix (Fin w.length → Fin 2) (Fin w.length → Fin 2) (Op (r + 1) E))

  qw : List (Bool × ℝ) → ℂ → ℂ

  uw : (w : List (Bool × ℝ)) → (Fin w.length → Fin 2) → Op (r + 1) E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Ctx

variable {B : Base E} {r : ℕ} (C : Ctx B r)

def OpEq (A A' : Op (r + 1) E) : Prop := ∀ φ ∈ C.cls, ∀ x ∈ C.Dom, A φ x = A' φ x

def IsAdj (A A' : Op (r + 1) E) : Prop := ∀ φ ∈ C.clsF, ∀ ψ ∈ C.clsF, C.beta (A φ) ψ = C.beta φ (A' ψ)

def gg (C : Ctx B r) (x : Fin (r + 1) → ℂ) : ℂ := GG B.T B.T' x

def fstar (C : Ctx B r) (e : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => B.fadj (e x)

abbrev AM (C : Ctx B r) (n : ℕ) := Matrix (Fin n → Fin 2) (Fin n → Fin 2) (Op (r + 1) E)

abbrev FM (C : Ctx B r) (n : ℕ) := Matrix (Fin n → Fin 2) (Fin n → Fin 2) ((Fin (r + 1) → ℂ) → E →L[ℂ] E)

def amul (C : Ctx B r) {n : ℕ} (M N : C.AM n) : C.AM n := fun s t => ∑ v, M s v ∘ N v t

def aapp (C : Ctx B r) {n : ℕ} (M : C.AM n) (φ : (Fin n → Fin 2) → (Fin (r + 1) → ℂ) → E) :
    (Fin n → Fin 2) → (Fin (r + 1) → ℂ) → E := fun s => ∑ t, M s t (φ t)

def adiag (C : Ctx B r) {n : ℕ} (f : (Fin n → Fin 2) → Op (r + 1) E) : C.AM n := fun s t => if s = t then f s else 0

def ascal (C : Ctx B r) {n : ℕ} (A : Op (r + 1) E) : C.AM n := C.adiag (fun _ => A)

def alm (C : Ctx B r) {n : ℕ} (A : Op (r + 1) E) (M : C.AM n) : C.AM n := fun s t => A ∘ M s t

def ablk (C : Ctx B r) {n : ℕ} (B : Fin 2 → Fin 2 → C.AM n) : C.AM (n + 1) :=
  fun s t => B (s 0) (t 0) (Fin.tail s) (Fin.tail t)

def toAM (C : Ctx B r) {n : ℕ} (M : C.FM n) : C.AM n := fun s t => mulE (M s t)

def fmul (C : Ctx B r) {n : ℕ} (M N : C.FM n) : C.FM n := fun s t x => ∑ v, (M s v x).comp (N v t x)

def fblk (C : Ctx B r) {n : ℕ} (B : Fin 2 → Fin 2 → C.FM n) : C.FM (n + 1) :=
  fun s t => B (s 0) (t 0) (Fin.tail s) (Fin.tail t)

def fscal (C : Ctx B r) {n : ℕ} (f : (Fin (r + 1) → ℂ) → ℂ) : C.FM n :=
  fun s t x => if s = t then f x • ContinuousLinearMap.id ℂ E else 0

def fdiag {n : ℕ} (a : (Fin n → Fin 2) → B.Rho → ℂ) : C.FM n :=
  fun s t x => if s = t then ∑ᶠ ρ, a s ρ • C.P ρ x else 0

def fadjM (C : Ctx B r) {n : ℕ} (M : C.FM n) : C.FM n := fun s t x => B.fadj (M t s x)

def xw (C : Ctx B r) : (w : List (Bool × ℝ)) → ℂ → (Fin w.length → Fin 2) → B.Rho → ℂ
  | [], Y, _, ρ => B.sgn * xPoly (B.rhoP ρ) Y
  | (true, ya) :: w, Y, s, ρ =>
      (if s 0 = 0 then (Y - ya) / (Y - ya - 1) else 1) * xw C w Y (Fin.tail s) ρ
  | (false, yb) :: w, Y, s, ρ =>
      (if s 0 = 0 then ((yb : ℂ) - Y) / ((yb : ℂ) - Y - 1) else 1) * xw C w Y (Fin.tail s) ρ

def cw : (w : List (Bool × ℝ)) → (Fin w.length → Fin 2) → B.Rho → ℂ
  | [], _, _ => 1
  | (true, ya) :: w, s, ρ =>
      cw w (Fin.tail s) ρ *
        (if s 0 = 0 then C.qw w ya / C.xw w ((ya : ℂ) + 1) (Fin.tail s) ρ else C.xw w ya (Fin.tail s) ρ)
  | (false, yb) :: w, s, ρ =>
      cw w (Fin.tail s) ρ *
        (if s 0 = 0 then C.qw w ((yb : ℂ) - 1) / C.xw w ((yb : ℂ) - 1) (Fin.tail s) ρ
          else C.xw w yb (Fin.tail s) ρ)

def xM (w : List (Bool × ℝ)) (Y : ℂ) : C.FM w.length := C.fdiag (C.xw w Y)

def xMinv (w : List (Bool × ℝ)) (Y : ℂ) : C.FM w.length := C.fdiag (fun s ρ => (C.xw w Y s ρ)⁻¹)

def ee (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    (w : List (Bool × ℝ)) → ℂ → C.FM w.length
  | [], Y => fun s t x => if s = t then
      (zOf x / star (zOf x)) • ∑ l, (shInv B.rhoP C.P l Y x).comp (SS l x) else 0
  | (true, ya) :: w, Y =>
      C.fblk ![![ee SS w Y - ((Y - ya)⁻¹ • (ee SS w Y - ee SS w ya)) +
          C.fscal (fun x => ((B.T * B.T' : ℝ) : ℂ) / star (zOf x)),
        C.fscal (fun _ => -(Y - ya)⁻¹)],
        ![0, C.fmul (C.xMinv w ya) (C.fmul (ee SS w Y) (C.xM w ya))]]
  | (false, yb) :: w, Y =>
      C.fblk ![![ee SS w Y, 0],
        ![(-(C.qw w ((yb : ℂ) - 1) / ((yb : ℂ) - Y - 1))) •
            C.fmul (C.xMinv w yb) (C.xMinv w ((yb : ℂ) - 1)),
          C.fmul (C.xMinv w yb) (C.fmul (ee SS w Y) (C.xM w yb)) - ((Y - yb)⁻¹ • (ee SS w Y - ee SS w yb)) +
            C.fscal (fun x => ((B.T * B.T' : ℝ) : ℂ) / star (zOf x))]]

def dM (w : List (Bool × ℝ)) : C.AM w.length :=
  C.alm (mulF (fun x => ((Complex.normSq (zOf x) : ℂ) / C.gg x) ^ w.length)) (C.toAM (C.fdiag (C.cw w)))

def dMinv (w : List (Bool × ℝ)) : C.AM w.length :=
  C.alm (mulF (fun x => ((Complex.normSq (zOf x) : ℂ) / C.gg x) ^ w.length)⁻¹)
    (C.toAM (C.fdiag (fun s ρ => (C.cw w s ρ)⁻¹)))

def lfr (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (w : List (Bool × ℝ)) (Y : ℂ) : C.AM w.length :=
  C.ascal (l0 r B.T B.T' h Y) +
    C.alm (mulF (fun x => star (zOf x) / (zOf x * C.gg x))) (C.toAM (C.ee SS w Y))

def mfr (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (w : List (Bool × ℝ)) (Yb : ℂ) : C.AM w.length :=
  C.amul (C.dMinv w) (C.amul
    (C.ascal (n := w.length) (m0 r B.T B.T' (C.fstar h) Yb) +
      (Matrix.of fun s t => mulE (C.fadjM (C.ee SS w (Yb - 1)) s t) ∘ mulF (fun x => zOf x / (star (zOf x) * C.gg x)) :
        C.AM w.length))
    (C.dM w))

def F (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    (w : List (Bool × ℝ)) → C.AM w.length
  | [] => C.ascal one
  | (true, ya) :: w =>
      C.ablk ![![C.alm (mulF (fun x => (zOf x)⁻¹)) (F h SS w), 0],
        ![C.alm (mulF (fun x => (star (zOf x))⁻¹ * C.gg x)) (C.amul (C.lfr h SS w ya) (F h SS w)),
          C.alm (mulF (fun x => (star (zOf x))⁻¹ * C.gg x)) (F h SS w)]]
  | (false, yb) :: w =>
      C.ablk ![![C.alm (mulF (fun x => (star (zOf x))⁻¹)) (F h SS w), 0],
        ![C.alm (mulF (fun x => (zOf x)⁻¹ * C.gg x)) (C.amul (C.mfr h SS w yb) (F h SS w)),
          C.alm (mulF (fun x => (zOf x)⁻¹ * C.gg x)) (F h SS w)]]

def form {n : ℕ} (M : C.AM n) (φ ψ : (Fin n → Fin 2) → (Fin (r + 1) → ℂ) → E) : ℂ :=
  ∑ s, ∑ t, C.beta (M s t (φ t)) (ψ s)

def bsum {n : ℕ} (φ ψ : (Fin n → Fin 2) → (Fin (r + 1) → ℂ) → E) : ℂ := ∑ s, C.beta (φ s) (ψ s)

def IsPlus (w : List (Bool × ℝ)) : Prop := ∀ a ∈ w, a.1 = true

def pts (w : List (Bool × ℝ)) : List ℝ := w.map Prod.snd

end Ctx

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev GOp (n : ℕ) (E : Type*) := (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E

structure GCtx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) where

  nV : ℕ

  Eop : Fin nV → Fin nV → GOp nV E

  H : Matrix (Fin nV) (Fin nV) ℂ

  eIdx : Fin r → Fin nV

  Rad : GOp nV E → Op (r + 1) E → Prop

  PolyInv : Set (GOp nV E)

namespace GCtx

variable {r : ℕ} (Γ : GCtx E r)

def form (v w : Fin Γ.nV → ℂ) : ℂ := ∑ i, ∑ j, star (w i) * Γ.H i j * v j

def cminor (n : ℕ) (hn : n ≤ r) (u : ℂ) : GOp Γ.nV E := fun f g =>
  ∑ b : Fin n → Fin Γ.nV, if StrictMono b then
    (Matrix.det (Matrix.of fun (a j : Fin n) =>
      Γ.form (g.mulVec (Pi.single (b j) 1)) (Pi.single (Γ.eIdx ⟨a, by omega⟩) 1))) •
      qminorOp Γ.Eop (fun a : Fin n => Γ.eIdx ⟨a, by omega⟩) b u f g
  else 0

end GCtx

def DnVn {r : ℕ} (n : ℕ) (hn : n ≤ r) (Y : ℂ) (i : Fin 2) : Op (r + 1) E :=
  mulF (fun x => ∏ a : Fin n, cOf x ⟨a, by omega⟩) ∘ vv Y n hn i

def NoPoleRho (B : Base E) (Y : ℂ) : Prop := ∀ ρ : B.Rho, B.IsType ρ → ∀ l : Fin B.k0, Y + (B.rhoP ρ l : ℂ) ≠ 0

namespace Ctx

variable {B : Base E} {r : ℕ} (C : Ctx B r)

def RhatV (Y : ℂ) : Op (r + 1) E :=
  mulF Dr ∘ (C.Q Y 0 1 ∘ ArV r Y + C.Q Y 1 1 ∘ BrV r Y)

inductive IsEeP (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    ((Fin (r + 1) → ℂ) → E →L[ℂ] E) → Prop
  | const (a : ℂ) : IsEeP SS (fun _ => a • ContinuousLinearMap.id ℂ E)
  | cst (a : B.Rho → ℂ) : IsEeP SS (fun x => ∑ᶠ ρ, a ρ • C.P ρ x)
  | tt : IsEeP SS (fun x => (((B.T * B.T' : ℝ) : ℂ) * star (Dr x) / star (Dr1 x)) • ContinuousLinearMap.id ℂ E)
  | ttc : IsEeP SS (fun x => (((B.T * B.T' : ℝ) : ℂ) * Dr x / Dr1 x) • ContinuousLinearMap.id ℂ E)
  | ss (l : Fin B.k0) :
      IsEeP SS (fun x => (Dr1 x / star (Dr1 x) * (star (Dr x) / Dr x)) • SS l x)
  | ssa (l : Fin B.k0) :
      IsEeP SS (fun x => (star (Dr1 x) / Dr1 x * (Dr x / star (Dr x))) • B.fadj (SS l x))
  | add {e f} : IsEeP SS e → IsEeP SS f → IsEeP SS (e + f)
  | mul {e f} : IsEeP SS e → IsEeP SS f → IsEeP SS (fun x => (e x).comp (f x))
  | congr {e f} : IsEeP SS e → (∀ x ∈ C.Dom, f x = e x) → IsEeP SS f

inductive IsBdd (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    ((Fin (r + 1) → ℂ) → E →L[ℂ] E) → Prop
  | one : IsBdd SS (fun _ => ContinuousLinearMap.id ℂ E)
  | f1 : IsBdd SS (fun x => (Dr x / Dr1 x) • ContinuousLinearMap.id ℂ E)
  | f2 : IsBdd SS (fun x => (Dr1 x / star (Dr1 x)) • ContinuousLinearMap.id ℂ E)
  | f1c : IsBdd SS (fun x => (star (Dr x) / star (Dr1 x)) • ContinuousLinearMap.id ℂ E)
  | f2c : IsBdd SS (fun x => (star (Dr1 x) / Dr1 x) • ContinuousLinearMap.id ℂ E)
  | f3 : IsBdd SS (fun x => (Gfn B.T B.T' x / ((Complex.normSq (Dr1 x) : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ E)
  | pr (ρ : B.Rho) : IsBdd SS (C.P ρ)
  | sn (l : Fin B.k0) : IsBdd SS (fun x => (star (Dr x) / Dr x) • SS l x)
  | sna (l : Fin B.k0) : IsBdd SS (fun x => (Dr x / star (Dr x)) • B.fadj (SS l x))
  | smul (a : ℂ) {e} : IsBdd SS e → IsBdd SS (a • e)
  | add {e f} : IsBdd SS e → IsBdd SS f → IsBdd SS (e + f)
  | mul {e f} : IsBdd SS e → IsBdd SS f → IsBdd SS (fun x => (e x).comp (f x))
  | congr {e f} : IsBdd SS e → (∀ x ∈ C.Dom, f x = e x) → IsBdd SS f

inductive IsEePM (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (b : Bool) : (n : ℕ) → C.FM n → Prop
  | scal {n} (c : ℂ) : IsEePM SS b n (C.fscal (fun _ => c))
  | cst {n} (a : (Fin n → Fin 2) → B.Rho → ℂ) : IsEePM SS b n (C.fdiag a)
  | cstOff {n} (s0 t0 : Fin n → Fin 2) (a : B.Rho → ℂ) :
      IsEePM SS b n (fun s t x => if s = s0 ∧ t = t0 then ∑ᶠ ρ, a ρ • C.P ρ x else 0)
  | tt {n} : b = true → IsEePM SS b n (C.fscal (fun x => ((B.T * B.T' : ℝ) : ℂ) / star (zOf x)))
  | ss {n} (l : Fin B.k0) :
      IsEePM SS b n (fun s t x => if s = t then (zOf x / star (zOf x)) • SS l x else 0)
  | add {n M N} : IsEePM SS b n M → IsEePM SS b n N → IsEePM SS b n (M + N)
  | mul {n M N} : IsEePM SS b n M → IsEePM SS b n N → IsEePM SS b n (C.fmul M N)
  | blk {n} (K : Fin 2 → Fin 2 → C.FM n) : (∀ i j, IsEePM SS b n (K i j)) → IsEePM SS b (n + 1) (C.fblk K)
  | congr {n M N} : IsEePM SS b n M → (∀ s t, ∀ x ∈ C.Dom, N s t x = M s t x) → IsEePM SS b n N

inductive IsFac (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    ℂ → Op (r + 1) E → Prop
  | lA (Y : ℂ) : IsFac h SS Y (mulF (fun x => (Dr1 x)⁻¹) ∘ Ahat r Y)
  | lR (Y : ℂ) : IsFac h SS Y (mulF (fun x => (star (Dr1 x))⁻¹) ∘ R0 r B.T B.T' h Y)
  | lAv (Y : ℂ) : IsFac h SS Y (mulF (fun x => (star (Dr1 x))⁻¹) ∘ AhatV r Y)
  | lRv (Y : ℂ) : IsFac h SS Y (mulF (fun x => (Dr1 x)⁻¹) ∘ weightedMirrorLevelOperator r B.T B.T' (C.fstar h) Y)
  | ee (Y : ℂ) {e} : C.IsEeP SS e → IsFac h SS Y (mulE e)
  | wG (Y : ℂ) (s : ℤ) : s = 1 ∨ s = -1 → IsFac h SS Y (mulF (fun x => Gfn B.T B.T' x ^ s))
  | wD (Y : ℂ) (s : ℤ) : s = 1 ∨ s = -1 → IsFac h SS Y (mulF (fun x => Dr1 x ^ s))
  | wDb (Y : ℂ) (s : ℤ) : s = 1 ∨ s = -1 → IsFac h SS Y (mulF (fun x => star (Dr1 x) ^ s))

def blk4 (i : Fin 4) (Y : ℂ) : Op (r + 1) E :=
  match i with
  | 0 => Ahat r Y
  | 1 => Rhat r C.Q Y
  | 2 => AhatV r Y
  | 3 => C.RhatV Y

def compL (C : Ctx B r) : List (Op (r + 1) E) → Op (r + 1) E
  | [] => one
  | A :: l => A ∘ compL C l

def PiL (x : Fin (r + 1) → ℂ) : E →L[ℂ] E := ∑ᶠ ρ, C.P ρ x

def IsFrameDatum (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  (∀ Y : ℂ, NoPoleRho B Y → C.OpEq (lOp B.T B.T' B.rhoP C.P C.Q Y) (lDec B.T B.T' B.rhoP C.P h SS Y)) ∧
  (∀ x ∈ C.Dom, ∀ e : E, dZ r (fun y => C.PiL y e) x + h x (C.PiL x e) = C.PiL x (h x e)) ∧
  (∀ x ∈ C.Dom, ∀ e : E, h x (e - C.PiL x e) - C.PiL x (h x (e - C.PiL x e)) = 0) ∧
  (∀ l, ∀ x ∈ C.Dom, SS l x = (C.PiL x).comp ((SS l x).comp (C.PiL x)))

end Ctx

namespace Ctx

section Shape

variable {B : Base E} {r : ℕ} {C : Ctx B r} {SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E} {b : Bool}

theorem IsEePM.smul {n : ℕ} (c : ℂ) {M : C.FM n} (h : IsEePM C SS b n M) : IsEePM C SS b n (c • M) := by
  have e : c • M = C.fmul (C.fscal (fun _ => c)) M := by
    funext s t x
    simp only [Ctx.fmul, Ctx.fscal, Matrix.smul_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single s]
    · simp
    · intro v _ hv
      simp [Ne.symm hv]
    · simp
  rw [e]
  exact IsEePM.mul (IsEePM.scal c) h

theorem IsEePM.zero {n : ℕ} : IsEePM C SS b n (0 : C.FM n) := by
  have e : (0 : C.FM n) = C.fscal (fun _ => (0 : ℂ)) := by
    funext s t x
    simp [Ctx.fscal]
  rw [e]
  exact IsEePM.scal 0

theorem IsEePM.sub {n : ℕ} {M N : C.FM n} (h : IsEePM C SS b n M) (h' : IsEePM C SS b n N) :
    IsEePM C SS b n (M - N) := by
  have e : M - N = M + (-1 : ℂ) • N := by simp [sub_eq_add_neg]
  rw [e]
  exact IsEePM.add h (IsEePM.smul _ h')

theorem IsEePM.sum {n : ℕ} {ι : Type*} (s : Finset ι) (M : ι → C.FM n) (h : ∀ i ∈ s, IsEePM C SS b n (M i)) :
    IsEePM C SS b n (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsEePM.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsEePM.add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))



theorem ee_nil_eq (Y : ℂ) :
    C.ee SS [] Y = ∑ l : Fin B.k0, C.fmul (C.fdiag (fun _ ρ => (Y + (B.rhoP ρ l : ℂ))⁻¹))
      (fun s t x => if s = t then (zOf x / star (zOf x)) • SS l x else 0) := by
  funext s t x
  have sub : ∀ a c : Fin ([] : List (Bool × ℝ)).length → Fin 2, a = c := fun a c => funext fun i => absurd i.2 (by simp)
  have hst : s = t := sub _ _
  subst hst
  simp only [Ctx.ee, Ctx.fmul, Ctx.fdiag, shInv, if_true, Matrix.sum_apply, Finset.sum_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single s]
  · simp
  · intro v _ hv
    exact absurd (sub _ _) hv
  · intro hs
    exact absurd (Finset.mem_univ s) hs

theorem ee_nil_mem (Y : ℂ) : IsEePM C SS b 0 (C.ee SS [] Y) := by
  rw [ee_nil_eq]
  exact IsEePM.sum _ _ fun l _ => IsEePM.mul (IsEePM.cst _) (IsEePM.ss l)

theorem ee_mem : ∀ (w : List (Bool × ℝ)) (Y : ℂ), IsEePM C SS true w.length (C.ee SS w Y)
  | [], Y => ee_nil_mem Y
  | (true, ya) :: w, Y => by
      rw [Ctx.ee]
      refine IsEePM.blk _ fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact IsEePM.add (IsEePM.sub (ee_mem w Y) (IsEePM.smul _ (IsEePM.sub (ee_mem w Y) (ee_mem w ya))))
          (IsEePM.tt rfl)
      · exact IsEePM.scal _
      · exact IsEePM.zero
      · exact IsEePM.mul (IsEePM.cst _) (IsEePM.mul (ee_mem w Y) (IsEePM.cst _))
  | (false, yb) :: w, Y => by
      rw [Ctx.ee]
      refine IsEePM.blk _ fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact ee_mem w Y
      · exact IsEePM.zero
      · exact IsEePM.smul _ (IsEePM.mul (IsEePM.cst _) (IsEePM.cst _))
      · exact IsEePM.add (IsEePM.sub (IsEePM.mul (IsEePM.cst _) (IsEePM.mul (ee_mem w Y) (IsEePM.cst _)))
          (IsEePM.smul _ (IsEePM.sub (ee_mem w Y) (ee_mem w yb)))) (IsEePM.tt rfl)

theorem IsEePM.of_eq {n : ℕ} {M N : C.FM n} (h : IsEePM C SS b n M) (e : M = N) : IsEePM C SS b n N := e ▸ h


end Shape

end Ctx

def gw {B : Base E} {r : ℕ} (Cr : Ctx B 0) (C0 : Ctx B r) (lift : Op 1 E → Op (r + 1) E)
    (h : (Fin 1 → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin 1 → ℂ) → E →L[ℂ] E) (w : List (Bool × ℝ)) :
    (Fin w.length → Fin 2) → Op (r + 1) E :=
  fun v => ∑ t, lift (Cr.F h SS w v t) ∘ C0.uw w t

def prW (k : ℕ) (zb : Fin (k + 1) → ℂ) (v : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  v - (herm (Hb k) v zb / herm (Hb k) zb zb) • zb

def omF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ • prW k (wbPart k r z) (Matrix.mulVec μ (wbPart k r z'))

def omF' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  star (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩) • prW k (wbPart k r z') (Matrix.mulVec μ⁻¹ (wbPart k r z))

def bordDet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  Matrix.det (Matrix.of fun (a b : Fin (r + 1)) =>
    herm (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) (if a = Fin.last r then w else fvec k r z a))

def omG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  prW k (wbPart k r z) (fun j => Hb k j j * bordDet k r z z' g (bvec (wI k r j)))

def omG' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  omG k r z' z (Hpk k r * g.conjTranspose * Hpk k r)

def evG {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) : ℂ :=
  MvPolynomial.eval (Sum.elim (fun ij => g ij.1 ij.2) (fun ij => star (g ij.1 ij.2))) p

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants
open Formalism.MainNotions.S.TopsChoicePartA

def hsAdj (L : Lev) (a : L.Hom →L[ℂ] L.Hom) : L.Hom →L[ℂ] L.Hom := by
  classical
  exact if h : ∃ b : L.Hom →L[ℂ] L.Hom, ∀ X Y, Formalism.MainNotions.S.hsInner (a X) Y = Formalism.MainNotions.S.hsInner X (b Y)
    then Classical.choose h else 0

def baseOf (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ) : Base L.Hom where
  k0 := L.k0
  T := L.T
  T' := L.T'
  u := u
  u' := u'
  I := I
  sgn := ((sCut u u' I : ℝ) : ℂ)
  hs := Formalism.MainNotions.S.hsInner
  fadj := hsAdj L
  Rho := Fin L.k0 → ℝ
  IsType := fun ρ => Interlace u ρ ∧ Interlace u' ρ ∧ ∀ j, ∃ m : ℤ, ρ j = m + ((L.k0 : ℝ) - 1) / 2
  rhoP := id

def ctxR (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r)
    (R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp)
    (clsF : Set (Lt.down Lt.r 0 hr).PF) : Ctx (baseOf Lt u u' I) 0 where
  Dom := (Lt.down Lt.r 0 hr).BD
  cls := (Lt.down Lt.r 0 hr).Img
  clsF := clsF
  beta := (Lt.down Lt.r 0 hr).betaB
  P := fun ρ x => (Lt.down Lt.r 0 hr).lineP ((Lt.down Lt.r 0 hr).pt x) ρ
  Q := R
  AA := {O | ∃ Θ ∈ (Lt.down Lt.r 0 hr).AA, (Lt.down Lt.r 0 hr).Rad Θ O}
  RR := fun w => ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).RR
  TT := fun w Y a b s t => ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).TT Y (a, s) (b, t)
  qw := fun w => ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).q
  uw := fun w => uw (m := 0) w 0 le_rfl

def ctx0 (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r)
    (R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp) : Ctx (baseOf Lt u u' I) Lt.r where
  Dom := Lt.BD
  cls := Lt.Img
  clsF := Lt.Img
  beta := Lt.betaB
  P := fun ρ x => Lt.lineP (Lt.pt x) ρ
  Q := fun Y a b => Lt.liftDown Lt.r 0 hr (R Y a b)
  AA := {O | ∃ Θ ∈ Lt.AA, Lt.Rad Θ O}
  RR := fun w s t => Lt.liftDown Lt.r 0 hr (((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).RR s t)
  TT := fun w Y a b s t =>
    Lt.liftDown Lt.r 0 hr (((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).TT Y (a, s) (b, t))
  qw := fun w => ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).q
  uw := fun w => uw (m := Lt.r) w Lt.r le_rfl

def gctxOf (L : Lev) : GCtx L.Hom L.r where
  nV := 2 * L.r + (L.k0 + 1) + 1
  Eop := EabH (Hpk (L.k0 + 1) L.r)
  H := Hpk (L.k0 + 1) L.r
  eIdx := eI (L.k0 + 1) L.r
  Rad := L.Rad
  PolyInv := L.AApoly

def pullZ {r : ℕ} {X : Type*} (e : (Fin 1 → ℂ) → X) : (Fin (r + 1) → ℂ) → X := fun x => e (fun _ => zOf x)

end Formalism.MainNotions.S.LevR
end
end
end
end
end
