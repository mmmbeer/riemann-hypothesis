import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec

section
noncomputable section

open PowerSeries

namespace GlobalTheory.NB

namespace Fr

variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)

def pt (k : ℕ) (τ : Fin R.e) : O⟦X⟧ := (R.φ ^ k) (X - C (R.ϖ τ))

def cst {r : ℕ} (a : Fin r → O) : Fin r → R.EE := fun k => algebraMap O R.EE (a k)

def γv {r : ℕ} : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) := R.γE.toLinearMap.compLeft (Fin r)

variable [IsDomain O]

def toD (_R : Fr l O) {r : ℕ} (a : Fin r → O) : Fin r → FractionRing O :=
  fun k => algebraMap O (FractionRing O) (a k)

end Fr

def winU (b S η : ℕ) : Set ℤ := Set.Icc (b : ℤ) (b + S) ∪ Set.Icc (-(η : ℤ)) η

def winD (b S η : ℕ) : Set ℤ := Set.Icc (-((b : ℤ) + S)) (-(b : ℤ)) ∪ Set.Icc (-(η : ℤ)) η

def win (up : Bool) (b S η : ℕ) : Set ℤ := if up then winU b S η else winD b S η

namespace Fr

variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)

end Fr

namespace Sys

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)

def IsFrame (i : ZMod n) (ρ k : ℕ) (H : Matrix (Fin r) (Fin r) O⟦X⟧) : Prop :=
  (∀ a b, X ∣ (H - (l : O⟦X⟧) ^ k • (1 : Matrix (Fin r) (Fin r) O⟦X⟧)) a b) ∧
    ∀ a b, X ^ ρ ∣ (S.G i * H.map R.γ - H) a b

def Coord (c' : ZMod n) (m : ℕ) (f : O⟦X⟧) (x g : Fin r → R.EE) : Prop :=
  ∃ (ρ k y : ℕ) (H : Matrix (Fin r) (Fin r) O⟦X⟧), S.IsFrame c' ρ k H ∧
    InMul f (R.N0 r) (((R.φ ^ m) X) ^ ρ • g) ∧
    InMul f (S.P c' m) ((l ^ y : ℕ) • ((l ^ k : ℕ) • x - ∑ j, g j • S.φit c' m (fun a => R.ι (H a j))))

variable [IsDomain O]

def FilArc (c' : ZMod n) (m s : ℕ) (τ : Fin R.e) (u : ℤ) :
    Submodule (FractionRing O) (Fin r → FractionRing O) :=
  (S.Fil (c' + ((m - s : ℕ) : ZMod n)) τ u).comap (S.φ0it c' (m - s)).mulVecLin

def Lat (c : ZMod n) (j : ℕ) : Submodule O (Fin r → FractionRing O) :=
  (D0 O r).map ((S.φ0it c j).mulVecLin.restrictScalars O)

end Sys

namespace Hom

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' : ℕ} {S : Sys R n r} {S' : Sys R n r'}
  (F : Hom S S')

def F0 (i : ZMod n) : Matrix (Fin r') (Fin r) O := (F.F i).map constantCoeff

def Good : Prop := F.Onto ∧ ∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a)

end Hom

end GlobalTheory.NB
end
end

section
noncomputable section

open PowerSeries

namespace GlobalTheory.NB

variable {l : ℕ} {O : Type} [CommRing O] [IsDomain O] {R : Fr l O} {n r₁ r : ℕ}

structure Typed {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Fin R.e → Bool)
    (b : ZMod n → Fin R.e → ℕ) (Sn η m h : ℕ) : Prop where
  good : F.Good
  jumps : ∀ i τ, S₁.JumpsIn i τ (win (up i τ) (b i τ) Sn η)
  size : ∀ i τ, η < b i τ
  le_h : ∀ i τ, b i τ + Sn ≤ h
  low : ∀ i τ, S.count i τ (-(η : ℤ)) η ≤ m

def lamC (l H : ℕ) : ℝ := Real.logb l (2 * H) + 1

def aC (l H : ℕ) : ℕ := ⌊(H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + lamC l H⌋₊

def secondSignatureConstant (l H : ℕ) : ℕ := 2 * H / (l - 1) ^ 2 + 1

def cDC (l H : ℕ) : ℕ := (H + 1) / (l - 1) + 1

def MC (l h : ℕ) : ℕ := h / (l - 1) + 1

def sigC (l h η : ℕ) : ℕ := (MC l h + η) / (l - 1) + 1

structure CHyp {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (b : ZMod n → ℕ) (Sn η m h : ℕ) :
    Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  even : Even n
  typed : Typed F (fun i _ => decide (Odd i.val)) (fun i _ => b i) Sn η m h
  big : ∀ i, 2 * ((h + η : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + lamC l (h + η)) + η + 1 ≤ b i
  half : ∀ i, h ≤ 2 * b i
  kills : ∀ i, F.Kills i (R.E ^ aC l (h + η))

def SgB (l h w Sn η : ℕ) : ℝ := (h : ℝ) / (l : ℝ) ^ 2 + (w + Sn + η : ℝ) / l + Real.logb l (2 * h) + 1

def Band (l : ℕ) {n : ℕ} (sz : ZMod n → ℕ) (b w h Sn η : ℕ) (Cb : ℝ) : Prop :=
  ∃ i, sz i ≤ w ∧ (b ≤ sz (i + 1) ∨ b ≤ sz (i - 1)) ∧
    |(l * sz i : ℝ) - b| ≤ Cb * (l * η + l * Sn + (b : ℝ) / l + sz i + l * Real.logb l (2 * h))

def MB (l h : ℕ) : ℕ := 2 * h / (l - 1) + 1

def rrB (l h w Sn η : ℕ) : ℕ :=
  ⌊2 * (w + Sn + η : ℝ) / l + 2 * h / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * h) + 3⌋₊

structure BHyp {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Bool)
    (sz : ZMod n → ℕ) (b w Sn η m h : ℕ) (A ρ : ZMod n → ℕ) : Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  typed : Typed F (fun i _ => up i) (fun i _ => sz i) Sn η m h
  w_pos : 1 ≤ w
  small : 20 * w ≤ b ∧ 20 * η ≤ b ∧ 20 * Sn ≤ b
  thick_or : ∀ i, (b ≤ sz i ∧ sz i ≤ b + η) ∨ sz i ≤ w
  some_thin : ∃ i, sz i ≤ w
  h_def : ((∃ i, b ≤ sz i) → h = b + η + Sn) ∧ ((∀ i, sz i ≤ w) → h = w + Sn)
  killX : ∀ i, F.Kills i (X ^ A i)
  killL : ∀ i, F.Kills i ((l : O⟦X⟧) ^ ρ i)
  killCut : ∀ i, sz (i + 1) ≤ w → F.Kills i ((l : O⟦X⟧) ^ rrB l h w Sn η)
  A_le : ∀ i, (A i : ℝ) ≤ (h + η : ℝ) / (l - 1) + 1
  a_le : ∀ i, (A i + ρ i : ℝ) ≤ (h + η : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l (2 * h)
  A_next : ∀ i, (A i : ℝ) ≤ (sz (i + 1) + Sn + η : ℝ) / l + 5 / 2 * SgB l h w Sn η
  A_cut : ∀ i, sz (i + 2) ≤ w → (A i : ℝ) ≤ (sz (i + 1) + Sn + η : ℝ) / l + 2 * SgB l h w Sn η

structure TypedOnto {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S)
    (up : ZMod n → Fin R.e → Bool) (b : ZMod n → Fin R.e → ℕ) (Sn η m h : ℕ) : Prop where
  onto : F.Onto
  jumps : ∀ i τ, S₁.JumpsIn i τ (win (up i τ) (b i τ) Sn η)
  size : ∀ i τ, η < b i τ
  le_h : ∀ i τ, b i τ + Sn ≤ h
  low : ∀ i τ, S.count i τ (-(η : ℤ)) η ≤ m

structure CSet {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (b : ZMod n → ℕ) (Sn η m h : ℕ) :
    Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  n_pos : 0 < n
  even : Even n
  typed : TypedOnto F (fun i _ => decide (Odd i.val)) (fun i _ => b i) Sn η m h
  big : ∀ i, 2 * ((h + η : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + lamC l (h + η)) + η + 1 ≤ b i
  half : ∀ i, h ≤ 2 * b i

structure BSet {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Bool)
    (sz : ZMod n → ℕ) (b w Sn η m h : ℕ) : Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  n_pos : 0 < n
  typed : TypedOnto F (fun i _ => up i) (fun i _ => sz i) Sn η m h
  w_pos : 1 ≤ w
  small : 20 * w ≤ b ∧ 20 * η ≤ b ∧ 20 * Sn ≤ b
  thick_or : ∀ i, (b ≤ sz i ∧ sz i ≤ b + η) ∨ sz i ≤ w
  some_thin : ∃ i, sz i ≤ w
  h_def : ((∃ i, b ≤ sz i) → h = b + η + Sn) ∧ ((∀ i, sz i ≤ w) → h = w + Sn)

def AltWord {n : ℕ} (up : ZMod n → Bool) (sz : ZMod n → ℕ) (b : ℕ) : Prop :=
  (∀ i, up (i + 1) = !up i) ∧ ∀ i, ¬ (b ≤ sz i ∧ b ≤ sz (i + 1) ∧ b ≤ sz (i + 2))

def OneWord {n : ℕ} (up : ZMod n → Bool) (sz : ZMod n → ℕ) (b ρ : ℕ) : Prop :=
  (∀ i j, up i = up j) ∧ 1 ≤ ρ ∧ ∀ i, ∃ k < ρ, sz (i + (k : ZMod n)) < b

def cW (l H : ℕ) : ℕ := ⌈1 + Real.logb l (H + 1)⌉₊

def eW (l H : ℕ) : ℕ := ⌈(H : ℝ) * l / ((l : ℝ) - 1) ^ 2⌉₊ + cW l H

def CokBound {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (Hw : ZMod n → ℕ) (H : ℕ) : Prop :=
  ∃ s : ZMod n → ℕ, (∀ i, s i ≤ H) ∧
    (∀ i, (s (i - 1) : ℝ) ≤ Hw i + cW l H + 3 + (s i : ℝ) / (l - 1)) ∧
    (∀ i, F.Kills i (X ^ ⌈(s i : ℝ) / (l - 1)⌉₊)) ∧
    ∀ i, F.Kills i ((l : O⟦X⟧) ^ (⌊(s i : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ + cW l H))

def CutBounds {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (sz : ZMod n → ℕ)
    (w Sn η h : ℕ) (A ρ : ZMod n → ℕ) : Prop :=
  (∀ i, F.Kills i (X ^ A i)) ∧ (∀ i, F.Kills i ((l : O⟦X⟧) ^ ρ i)) ∧
  (∀ i, sz (i + 1) ≤ w → F.Kills i ((l : O⟦X⟧) ^ rrB l h w Sn η)) ∧
  (∀ i, (A i : ℝ) ≤ (h + η : ℝ) / (l - 1) + 1) ∧
  (∀ i, (A i + ρ i : ℝ) ≤
    (h + η : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l (2 * h)) ∧
  (∀ i, (A i : ℝ) ≤ (sz (i + 1) + Sn + η : ℝ) / l + 5 / 2 * SgB l h w Sn η) ∧
  ∀ i, sz (i + 2) ≤ w → (A i : ℝ) ≤ (sz (i + 1) + Sn + η : ℝ) / l + 2 * SgB l h w Sn η

section Rel

variable {S₁ : Sys R n r₁} {S : Sys R n r} {F : Hom S₁ S}

omit [IsDomain O] in

theorem Hom.Kills.of_dvd {i : ZMod n} {f g : O⟦X⟧} (h : F.Kills i f) (hfg : f ∣ g) :
    F.Kills i g := by
  obtain ⟨c, rfl⟩ := hfg
  intro y hy
  obtain ⟨x, hx, e⟩ := h (c • y) (Submodule.smul_mem _ _ hy)
  exact ⟨x, hx, by rw [e, smul_smul]⟩

omit [IsDomain O] in

theorem Hom.Kills.pow_le {i : ZMod n} {f : O⟦X⟧} {a a' : ℕ} (h : F.Kills i (f ^ a)) (ha : a ≤ a') :
    F.Kills i (f ^ a') := h.of_dvd (pow_dvd_pow f ha)

theorem typed_iff {up : ZMod n → Fin R.e → Bool} {b : ZMod n → Fin R.e → ℕ} {Sn η m h : ℕ} :
    Typed F up b Sn η m h ↔
      TypedOnto F up b Sn η m h ∧ ∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a) :=
  ⟨fun H => ⟨⟨H.good.1, H.jumps, H.size, H.le_h, H.low⟩, H.good.2⟩,
    fun H => ⟨⟨H.1.onto, H.2⟩, H.1.jumps, H.1.size, H.1.le_h, H.1.low⟩⟩




omit [IsDomain O] in

theorem CokBound.of_kills_one (h : ∀ i, F.Kills i 1) (Hw : ZMod n → ℕ) (H : ℕ) :
    CokBound F Hw H :=
  ⟨fun _ => 0, fun _ => Nat.zero_le _, fun _ => by simp only [Nat.cast_zero, zero_div]; positivity,
    fun i => (h i).of_dvd (one_dvd _), fun i => (h i).of_dvd (one_dvd _)⟩

end Rel

example : AltWord (n := 2) (fun i => decide (i = 1)) (fun i => if i = 1 then 20 else 1) 20 := by
  unfold AltWord; decide

example : OneWord (n := 3) (fun _ => true) (fun i => if i = 0 then 1 else 20) 20 3 ∧
    ¬ OneWord (n := 3) (fun _ => true) (fun i => if i = 0 then 1 else 20) 20 2 := by
  unfold OneWord; decide

example (up : ZMod 3 → Bool) (sz : ZMod 3 → ℕ) (b : ℕ) : ¬ AltWord up sz b := by
  rintro ⟨h, -⟩
  have h0 : up 1 = !up 0 := h 0
  have h1 : up 2 = !up 1 := h 1
  have h2 : up 0 = !up 2 := h 2
  revert h0 h1 h2
  cases up 0 <;> cases up 1 <;> cases up 2 <;> simp

example : cW 11 10 = 2 := by
  unfold cW
  have : Real.logb ((11 : ℕ) : ℝ) (((10 : ℕ) : ℝ) + 1) = 1 := by
    norm_num
  rw [this]; norm_num

example : secondSignatureConstant 11 100 = 3 ∧ cDC 11 100 = 11 ∧ MC 11 100 = 11 ∧ sigC 11 100 0 = 2 ∧
    MB 11 100 = 21 := by decide

end GlobalTheory.NB
end
end
