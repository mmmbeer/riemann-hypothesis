import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot38
open Formalism.BasicNotions.V1 IsLocalRing MvPowerSeries Filter
open scoped Classical

open MvPowerSeries IsLocalRing Filter

section Graded

variable {O : Type} [CommRing O] {a rk : ℕ} (wt : Fin a → (Fin rk → ℤ))

def monoWt (m : Fin a →₀ ℕ) : Fin rk → ℤ := m.sum fun i e => (e : ℤ) • wt i

theorem monoWt_add (m m' : Fin a →₀ ℕ) : monoWt wt (m + m') = monoWt wt m + monoWt wt m' := by
  unfold monoWt
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i e e'; push_cast; exact add_smul _ _ _

theorem monoWt_zero : monoWt wt (0 : Fin a →₀ ℕ) = 0 := by simp [monoWt]

theorem monoWt_single (i : Fin a) : monoWt wt (Finsupp.single i 1) = wt i := by
  simp [monoWt]

variable (O) in

def Pj (j : Fin rk → ℤ) : Submodule O (MvPowerSeries (Fin a) O) where
  carrier := {f | ∀ m, coeff m f ≠ 0 → monoWt wt m = j}
  add_mem' {f g} hf hg m h := by
    rw [map_add] at h
    by_cases h1 : coeff m f = 0
    · rw [h1, zero_add] at h; exact hg m h
    · exact hf m h1
  zero_mem' m h := by simp at h
  smul_mem' c f hf m h := by
    rw [map_smul, smul_eq_mul] at h
    exact hf m (right_ne_zero_of_mul h)

theorem Pj_mul {i j : Fin rk → ℤ} {f g : MvPowerSeries (Fin a) O} (hf : f ∈ Pj O wt i)
    (hg : g ∈ Pj O wt j) : f * g ∈ Pj O wt (i + j) := by
  intro m hm
  classical
  rw [coeff_mul] at hm
  obtain ⟨⟨p, q⟩, hpq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hpq' : p + q = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
  rw [← hpq', monoWt_add, hf p (left_ne_zero_of_mul hne), hg q (right_ne_zero_of_mul hne)]

theorem one_mem_degree_zero : (1 : MvPowerSeries (Fin a) O) ∈ Pj O wt 0 := by
  classical
  intro m hm
  rw [coeff_one] at hm
  split_ifs at hm with h
  · rw [h, monoWt_zero]
  · exact absurd rfl hm

theorem algebraMap_mem_degree_zero (c : O) : algebraMap O (MvPowerSeries (Fin a) O) c ∈ Pj O wt 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (Pj O wt 0).smul_mem c (one_mem_degree_zero wt)

theorem X_mem_Pj (i : Fin a) : (X i : MvPowerSeries (Fin a) O) ∈ Pj O wt (wt i) := by
  classical
  intro m hm
  rw [coeff_X] at hm
  split_ifs at hm with h
  · rw [h, monoWt_single]
  · exact absurd rfl hm

variable (O) in

def Psub : Subalgebra O (MvPowerSeries (Fin a) O) where
  carrier := ((⨆ j, Pj O wt j : Submodule O (MvPowerSeries (Fin a) O)) : Set _)
  mul_mem' {x y} hx hy := by
    simp only [SetLike.mem_coe] at hx hy ⊢
    refine Submodule.iSup_induction _ (motive := fun x => x * y ∈ ⨆ j, Pj O wt j) hx ?_ ?_ ?_
    · intro i x hx
      refine Submodule.iSup_induction _ (motive := fun y => x * y ∈ ⨆ j, Pj O wt j) hy ?_ ?_ ?_
      · intro j y hy; exact Submodule.mem_iSup_of_mem (i + j) (Pj_mul wt hx hy)
      · simp
      · intro y y' h h'; rw [mul_add]; exact Submodule.add_mem _ h h'
    · simp
    · intro x x' h h'; rw [add_mul]; exact Submodule.add_mem _ h h'
  add_mem' hx hy := Submodule.add_mem _ hx hy
  algebraMap_mem' c := Submodule.mem_iSup_of_mem 0 (algebraMap_mem_degree_zero wt c)

variable (O) in

def P0sub : Subalgebra O (MvPowerSeries (Fin a) O) where
  carrier := (Pj O wt 0 : Set _)
  mul_mem' {x y} hx hy := by
    have := Pj_mul wt hx hy; rwa [add_zero] at this
  add_mem' hx hy := Submodule.add_mem _ hx hy
  algebraMap_mem' c := algebraMap_mem_degree_zero wt c

theorem degree_zero_le_graded : P0sub O wt ≤ Psub O wt := fun _ hx => Submodule.mem_iSup_of_mem 0 hx

theorem Pj_le_P (j : Fin rk → ℤ) {x : MvPowerSeries (Fin a) O} (hx : x ∈ Pj O wt j) :
    x ∈ Psub O wt :=
  Submodule.mem_iSup_of_mem j hx

def comp (j : Fin rk → ℤ) (f : MvPowerSeries (Fin a) O) : MvPowerSeries (Fin a) O :=
  fun m => if monoWt wt m = j then coeff m f else 0

def IsHomog (Jh : Ideal (MvPowerSeries (Fin a) O)) : Prop :=
  ∀ f ∈ Jh, ∀ j, comp wt j f ∈ Jh

def IsClosedAdic [IsLocalRing O] (Jh : Ideal (MvPowerSeries (Fin a) O)) : Prop :=
  ∀ f, (∀ N : ℕ, f ∈ Jh ⊔ maximalIdeal (MvPowerSeries (Fin a) O) ^ N) → f ∈ Jh

def Jsub (Jh : Ideal (MvPowerSeries (Fin a) O)) : Submodule O (MvPowerSeries (Fin a) O) :=
  ⨆ j, Jh.restrictScalars O ⊓ Pj O wt j

abbrev mk (Jh : Ideal (MvPowerSeries (Fin a) O)) :
    MvPowerSeries (Fin a) O →ₐ[O] MvPowerSeries (Fin a) O ⧸ Jh :=
  Ideal.Quotient.mkₐ O Jh

variable (Jh : Ideal (MvPowerSeries (Fin a) O))

def Aj (j : Fin rk → ℤ) : Submodule O (MvPowerSeries (Fin a) O ⧸ Jh) :=
  (Pj O wt j).map (mk Jh).toLinearMap

def Asub : Subalgebra O (MvPowerSeries (Fin a) O ⧸ Jh) := (Psub O wt).map (mk Jh)

def A0sub : Subalgebra O (MvPowerSeries (Fin a) O ⧸ Jh) := (P0sub O wt).map (mk Jh)

theorem base_subalgebra_le : A0sub wt Jh ≤ Asub wt Jh := Subalgebra.map_mono (degree_zero_le_graded wt)

theorem Aj_le_A {j : Fin rk → ℤ} {y : MvPowerSeries (Fin a) O ⧸ Jh} (hy : y ∈ Aj wt Jh j) :
    y ∈ Asub wt Jh := by
  obtain ⟨f, hf, rfl⟩ := hy
  exact ⟨f, Pj_le_P wt j hf, rfl⟩

theorem mkX_mem_A (i : Fin a) : mk Jh (X i) ∈ Asub wt Jh :=
  ⟨X i, Pj_le_P wt (wt i) (X_mem_Pj wt i), rfl⟩

def mhat [IsLocalRing O] : Ideal (MvPowerSeries (Fin a) O ⧸ Jh) :=
  (maximalIdeal (MvPowerSeries (Fin a) O)).map (Ideal.Quotient.mk Jh)

def m0 [IsLocalRing O] : Ideal (A0sub wt Jh) := (mhat Jh).comap (A0sub wt Jh).val

end Graded

section Coh

variable {k : Type} [Field k] {n : ℕ}

def dC {H : Type} [Group H] (act : H → Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k)
    (m : ℕ) : ((Fin m → H) → Matrix (Fin n) (Fin n) k) →ₗ[k]
      ((Fin (m + 1) → H) → Matrix (Fin n) (Fin n) k) where
  toFun c x := act (x 0) (c fun i => x i.succ) + Finset.univ.sum fun j : Fin (m + 1) =>
    (-1 : k) ^ ((j : ℕ) + 1) • c (Fin.contractNth j (· * ·) x)
  map_add' c c' := by
    ext x
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r c := by
    funext x
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

def IsCoch {H : Type} [TopologicalSpace H] {m : ℕ} (N : Submodule k (Matrix (Fin n) (Fin n) k))
    (c : (Fin m → H) → Matrix (Fin n) (Fin n) k) : Prop :=
  IsLocallyConstant c ∧ ∀ x, c x ∈ N

def CochSub {H : Type} [TopologicalSpace H] (m : ℕ) (N : Submodule k (Matrix (Fin n) (Fin n) k)) :
    Submodule k ((Fin m → H) → Matrix (Fin n) (Fin n) k) where
  carrier := {c | IsCoch N c}
  add_mem' {c c'} hc hc' := ⟨hc.1.add hc'.1, fun x => N.add_mem (hc.2 x) (hc'.2 x)⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => N.zero_mem⟩
  smul_mem' a c hc := ⟨hc.1.comp (a • ·), fun x => N.smul_mem a (hc.2 x)⟩

end Coh

section Fib

variable (P : LiftProb)

abbrev kk : Type := ResidueField P.O

abbrev MM : Type := Matrix (Fin P.kind.n) (Fin P.kind.n) (kk P)

abbrev FA (m : ℕ) : Type :=
  ((Fin m → P.Gam) → MM P) × (∀ q, (Fin m → P.Gq q) → MM P) × (∀ v, (Fin m → P.Gv v) → MM P)

abbrev FB (m : ℕ) : Type := (∀ q, (Fin m → P.Gq q) → MM P) × (∀ v, (Fin m → P.Gv v) → MM P)

variable {P}

def resL (H : Subgroup P.Gam) (m : ℕ) : ((Fin m → P.Gam) → MM P) →ₗ[kk P] ((Fin m → H) → MM P) :=
  LinearMap.funLeft (kk P) (MM P) fun x i => (x i : P.Gam)

variable (act : P.Gam → MM P →ₗ[kk P] MM P)

def pG (m : ℕ) : FA P m →ₗ[kk P] ((Fin m → P.Gam) → MM P) := LinearMap.fst _ _ _
def pQ (m : ℕ) (q : P.qPl) : FA P m →ₗ[kk P] ((Fin m → P.Gq q) → MM P) :=
  (LinearMap.proj (R := kk P) (φ := fun q : P.qPl => (Fin m → P.Gq q) → MM P) q).comp
    ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))
def pV (m : ℕ) (v : P.lPl) : FA P m →ₗ[kk P] ((Fin m → P.Gv v) → MM P) :=
  (LinearMap.proj (R := kk P) (φ := fun v : P.lPl => (Fin m → P.Gv v) → MM P) v).comp
    ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))
def qQ (m : ℕ) (q : P.qPl) : FB P m →ₗ[kk P] ((Fin m → P.Gq q) → MM P) :=
  (LinearMap.proj (R := kk P) (φ := fun q : P.qPl => (Fin m → P.Gq q) → MM P) q).comp
    (LinearMap.fst _ _ _)
def qV (m : ℕ) (v : P.lPl) : FB P m →ₗ[kk P] ((Fin m → P.Gv v) → MM P) :=
  (LinearMap.proj (R := kk P) (φ := fun v : P.lPl => (Fin m → P.Gv v) → MM P) v).comp
    (LinearMap.snd _ _ _)

def dA (m : ℕ) : FA P m →ₗ[kk P] FA P (m + 1) :=
  LinearMap.prod ((dC act m).comp (pG m)) (LinearMap.prod
    (LinearMap.pi fun q => (dC (fun h : P.Gq q => act h) m).comp (pQ m q))
    (LinearMap.pi fun v => (dC (fun h : P.Gv v => act h) m).comp (pV m v)))

def dB (m : ℕ) : FB P m →ₗ[kk P] FB P (m + 1) :=
  LinearMap.prod
    (LinearMap.pi fun q => (dC (fun h : P.Gq q => act h) m).comp (qQ m q))
    (LinearMap.pi fun v => (dC (fun h : P.Gv v => act h) m).comp (qV m v))

variable {act}

def fAB (m : ℕ) : FA P m →ₗ[kk P] FB P m :=
  LinearMap.prod
    (LinearMap.pi fun q => (resL (P.Gq q) m).comp (pG m) - pQ m q)
    (LinearMap.pi fun v => (resL (P.Gv v) m).comp (pG m) - pV m v)

variable (act)

def d0 : FA P 0 →ₗ[kk P] FA P 1 × FB P 0 := LinearMap.prod (dA act 0) (fAB 0)

def dS (m : ℕ) : FA P (m + 1) × FB P m →ₗ[kk P] FA P (m + 2) × FB P (m + 1) :=
  LinearMap.prod ((dA act (m + 1)).comp (LinearMap.fst _ _ _))
    ((fAB (m + 1)).comp (LinearMap.fst _ _ _) - (dB act m).comp (LinearMap.snd _ _ _))

def NqSet (q : P.qPl) : Set P.Gam := {g | g ∈ P.Iq q ∧ g ∈ P.GF ∧ P.rbar g = 1}

variable (N : Submodule (kk P) (MM P)) (localization₂ : ∀ v (m : ℕ), ((Fin m → P.Gv v) → MM P) → Prop)

def AdmA (m : ℕ) : Set (FA P m) :=
  {x | IsCoch N x.1 ∧ (∀ q, IsCoch N (x.2.1 q) ∧ ∀ y z : Fin m → P.Gq q,
      (∀ i, ((y i : P.Gam))⁻¹ * (z i : P.Gam) ∈ NqSet q) → x.2.1 q y = x.2.1 q z) ∧
    ∀ v, IsCoch N (x.2.2 v) ∧ localization₂ v m (x.2.2 v)}

def AdmB (m : ℕ) : Set (FB P m) := {y | (∀ q, IsCoch N (y.1 q)) ∧ ∀ v, IsCoch N (y.2 v)}

def Z0 : Set (FA P 0) := {x | x ∈ AdmA N localization₂ 0 ∧ d0 act x = 0}

def Zs (m : ℕ) : Set (FA P (m + 1) × FB P m) :=
  {x | x.1 ∈ AdmA N localization₂ (m + 1) ∧ x.2 ∈ AdmB N m ∧ dS act m x = 0}

def Bd : (m : ℕ) → Set (FA P (m + 1) × FB P m)
  | 0 => d0 act '' AdmA N localization₂ 0
  | m + 1 => dS act m '' {x | x.1 ∈ AdmA N localization₂ (m + 1) ∧ x.2 ∈ AdmB N m}

def ZsS (m : ℕ) : Submodule (kk P) (FA P (m + 1) × FB P m) := Submodule.span (kk P) (Zs act N localization₂ m)

abbrev HS (m : ℕ) : Type :=
  ZsS act N localization₂ m ⧸ (Submodule.span (kk P) (Bd act N localization₂ m)).comap (ZsS act N localization₂ m).subtype

def hFib : ℕ → ℕ
  | 0 => Module.finrank (kk P) (Submodule.span (kk P) (Z0 act N localization₂))
  | m + 1 => Module.finrank (kk P) (HS act N localization₂ m)

def FinFib : Prop :=
  FiniteDimensional (kk P) (Submodule.span (kk P) (Z0 act N localization₂)) ∧
    ∀ m, FiniteDimensional (kk P) (HS act N localization₂ m)

end Fib

section Numbers

variable (P : LiftProb)

def wtSub {V : Type} (w : Fin P.kind.n → Fin P.kind.n → V) (j : V) : Submodule (kk P) (MM P) where
  carrier := {X | ∀ a b, X a b ≠ 0 → w a b = j}
  add_mem' {X Y} hX hY a b h := by
    by_cases h1 : X a b = 0
    · exact hY a b (by simpa [h1] using h)
    · exact hX a b h1
  zero_mem' a b h := absurd rfl h
  smul_mem' c X hX a b h := hX a b (right_ne_zero_of_mul h)

def gW (j : Wt P.rk) : Submodule (kk P) (MM P) :=
  gLie (kk P) P.kind ⊓ wtSub P (fun a b => P.dg a - P.dg b) j

def bSub (F : MM P) : Submodule (kk P) (MM P) where
  carrier := {X | X ∈ gLie (kk P) P.kind ∧ ∀ i j, j < i → (F⁻¹ * X * F) i j = 0}
  add_mem' {X Y} hX hY := ⟨(gLie _ _).add_mem hX.1 hY.1, fun i j h => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX.2 i j h, hY.2 i j h, add_zero]⟩
  zero_mem' := ⟨(gLie _ _).zero_mem, fun i j _ => by simp⟩
  smul_mem' c X hX := ⟨(gLie _ _).smul_mem c hX.1, fun i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX.2 i j h, smul_zero]⟩

def nSub (F : MM P) : Submodule (kk P) (MM P) where
  carrier := {X | X ∈ gLie (kk P) P.kind ∧ ∀ i j, j ≤ i → (F⁻¹ * X * F) i j = 0}
  add_mem' {X Y} hX hY := ⟨(gLie _ _).add_mem hX.1 hY.1, fun i j h => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX.2 i j h, hY.2 i j h, add_zero]⟩
  zero_mem' := ⟨(gLie _ _).zero_mem, fun i j _ => by simp⟩
  smul_mem' c X hX := ⟨(gLie _ _).smul_mem c hX.1, fun i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX.2 i j h, smul_zero]⟩

def torP (F X : MM P) (i : Fin P.kind.n) : kk P := (F⁻¹ * X * F) i i

def locZ : ∀ v (m : ℕ), ((Fin m → P.Gv v) → MM P) → Prop := fun _ _ c => c = 0

def locB (F : P.lPl → MM P) : ∀ v (m : ℕ), ((Fin m → P.Gv v) → MM P) → Prop :=
  fun v _ c => ∀ x, c x ∈ bSub P (F v)

def locM (F : P.lPl → MM P) (M : P.lPl → Subgroup P.Gam) :
    ∀ v (m : ℕ), ((Fin m → P.Gv v) → MM P) → Prop :=
  fun v m c => match m with
    | 0 => ∀ x, c x ∈ bSub P (F v)
    | 1 => (∀ x, c x ∈ bSub P (F v)) ∧
        (∀ g h : P.Gv v, ∀ i, torP P (F v) (c fun _ => g * h) i =
          torP P (F v) (c fun _ => g) i + torP P (F v) (c fun _ => h) i) ∧
        ∀ g : P.Gv v, (g : P.Gam) ∈ M v → ∀ i, torP P (F v) (c fun _ => g) i = 0
    | _ + 2 => ∀ x, c x ∈ nSub P (F v)

def gWx (rx : ℕ) (resx : Wt P.rk →+ Wt rx) (j : Wt rx) : Submodule (kk P) (MM P) :=
  gLie (kk P) P.kind ⊓ wtSub P (fun a b => resx (P.dg a - P.dg b)) j

def hc (i : ℕ) (j : Wt P.rk) : ℕ :=
  hFib (adAct P.GF P.rbar) (gW P j) (locZ P) i

def h0tw (j : Wt P.rk) : ℕ :=
  Module.finrank (kk P) (invSub (fun g => ((P.cyc g : kk P)) • adAct P.GF P.rbar g) (gW P j))

def h0R (v : P.rPl) (j : Wt P.rk) : ℕ :=
  Module.finrank (kk P) ↥(gW P j ⊓ LinearMap.ker (adAct P.GF P.rbar (P.cv v) - LinearMap.id))

def hC (rc : P.Gam → MM P) (F : P.lPl → MM P) (i : ℕ) : ℕ :=
  hFib (adAct P.GF rc) (gLie (kk P) P.kind) (locB P F) i

def h0dC (rc : P.Gam → MM P) : ℕ :=
  Module.finrank (kk P) (invSub (fun g => ((P.cyc g : kk P)) • adAct P.GF rc g) (gLie (kk P) P.kind))

def h0inf (rc : P.Gam → MM P) : ℕ :=
  ∑ v, Module.finrank (kk P)
    ↥(gLie (kk P) P.kind ⊓ LinearMap.ker (adAct P.GF rc (P.cv v) - LinearMap.id))

def hCj (rc : P.Gam → MM P) (F : P.lPl → MM P) (rx : ℕ) (resx : Wt P.rk →+ Wt rx) (i : ℕ)
    (j : Wt rx) : ℕ :=
  hFib (adAct P.GF rc) (gWx P rx resx j) (locB P F) i

def hCjM (rc : P.Gam → MM P) (F : P.lPl → MM P) (M : P.lPl → Subgroup P.Gam) (rx : ℕ)
    (resx : Wt P.rk →+ Wt rx) (i : ℕ) (j : Wt rx) : ℕ :=
  hFib (adAct P.GF rc) (gWx P rx resx j) (locM P F M) i

def dimb : GGKind → ℕ
  | .typeThree => 6
  | .typeTwo => 3
  | .GSp4 => 6

end Numbers

class IsCoeff (O : Type) [CommRing O] (l : ℕ) : Prop where
  prime : l.Prime
  odd : l ≠ 2
  dom : IsDomain O
  dvr : IsDiscreteValuationRing O
  complete : IsAdicComplete (maximalIdeal O) O
  char0 : CharZero O
  finRes : Finite (ResidueField O)
  charRes : CharP (ResidueField O) l

def GradedQuotientFiniteness {O : Type} [CommRing O] [IsLocalRing O] {a rk : ℕ} (wt : Fin a → Wt rk)
    (Jh : Ideal (MvPowerSeries (Fin a) O)) : Prop :=

  ((m0 wt Jh).IsMaximal ∧ (∀ I : Ideal (A0sub wt Jh), I.IsMaximal → I = m0 wt Jh) ∧
    IsNoetherianRing (A0sub wt Jh) ∧ IsAdicComplete (m0 wt Jh) (A0sub wt Jh)) ∧

  (∃ s : Finset (MvPowerSeries (Fin a) O ⧸ Jh), ((s : Set (MvPowerSeries (Fin a) O ⧸ Jh)) ⊆ (Asub wt Jh : Set _)) ∧
    ∀ x ∈ Asub wt Jh, x ∈ Algebra.adjoin (A0sub wt Jh) (s : Set _)) ∧

  (∀ j, ∃ s : Finset (MvPowerSeries (Fin a) O ⧸ Jh), ((s : Set (MvPowerSeries (Fin a) O ⧸ Jh)) ⊆ (Aj wt Jh j : Set _)) ∧
    ∀ x ∈ Aj wt Jh j, x ∈ Submodule.span (A0sub wt Jh) (s : Set _)) ∧

  Jh = Ideal.span (Jsub wt Jh : Set (MvPowerSeries (Fin a) O)) ∧

  (∀ j, ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧ ∀ M, ∀ x ∈ Aj wt Jh j, x ∈ mhat Jh ^ M →
    x ∈ (m0 wt Jh ^ n M) • Submodule.span (A0sub wt Jh) (Aj wt Jh j : Set _)) ∧

  (∀ f ∈ Psub O wt, f ∈ Jh → f ∈ Jsub wt Jh) ∧

  (IsDomain (MvPowerSeries (Fin a) O ⧸ Jh) → IsDomain (Asub wt Jh)) ∧

  (∃ N : Submodule (A0sub wt Jh) (MvPowerSeries (Fin a) O ⧸ Jh),
    Disjoint (Submodule.span (A0sub wt Jh) (A0sub wt Jh : Set _)) N ∧
    Submodule.span (A0sub wt Jh) (A0sub wt Jh : Set _) ⊔ N =
      Submodule.span (A0sub wt Jh) (Asub wt Jh : Set _)) ∧

  (∀ p : PrimeSpectrum (A0sub wt Jh), ∃ q : PrimeSpectrum (Asub wt Jh),
    q.asIdeal.comap (Subalgebra.inclusion (base_subalgebra_le wt Jh)) = p.asIdeal)

def FiniteTypeRingPart : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ) [IsCoeff O l] [IsLocalRing O] (a rk : ℕ) (wt : Fin a → Wt rk)
    (Jh : Ideal (MvPowerSeries (Fin a) O)), Jh ≠ ⊤ → IsClosedAdic Jh → IsHomog wt Jh → GradedQuotientFiniteness wt Jh

def PointsLemmaAnyRank : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ) [IsCoeff O l] [IsLocalRing O] (a rk : ℕ) (wt : Fin a → Wt rk)
    (Jh : Ideal (MvPowerSeries (Fin a) O)), Jh ≠ ⊤ → IsClosedAdic Jh → IsHomog wt Jh →
  ∀ (kap : Type) [NontriviallyNormedField kap] [IsUltrametricDist kap] [CompleteSpace kap]
    (xi : Asub wt Jh →+* kap),
    (∀ x : A0sub wt Jh, ‖xi (Subalgebra.inclusion (base_subalgebra_le wt Jh) x)‖ ≤ 1) →
    (∀ x ∈ m0 wt Jh, ‖xi (Subalgebra.inclusion (base_subalgebra_le wt Jh) x)‖ < 1) →
  ∃ (kap' : Type) (_ : NontriviallyNormedField kap') (_ : IsUltrametricDist kap')
    (_ : CompleteSpace kap') (_ : NormedAlgebra kap kap') (_ : FiniteDimensional kap kap')
    (t : Fin rk → kap'ˣ),
    (∀ i, ‖tpow t (wt i) * algebraMap kap kap' (xi ⟨mk Jh (X i), mkX_mem_A wt Jh i⟩)‖ < 1) ∧
    ∃ φ : (MvPowerSeries (Fin a) O ⧸ Jh) →+* kap', (∀ y, ‖φ y‖ ≤ 1) ∧
      (∀ y ∈ mhat Jh, ‖φ y‖ < 1) ∧
      ∀ j y (hy : y ∈ Aj wt Jh j), φ y = tpow t j * algebraMap kap kap' (xi ⟨y, Aj_le_A wt Jh hy⟩)

section Prob

variable (P : LiftProb)

def Split : Prop := ∀ v, P.Gv v ≤ P.GF

def Uq (g : P.Gam) : Prop := ∃ q, g ∈ P.Iq q ∧ g ∈ P.GF ∧ P.rbar g = 1

abbrev IsLift (r0 : P.Gam → MM P) {C : Type} [CommRing C] [IsLocalRing C] [Algebra P.O C]
    [IsLocalHom (algebraMap P.O C)] (r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C) : Prop :=
  IsLiftG P.kind P.GF P.chi (Uq P) r0 r

def Normalised {C : Type} [CommRing C] [Algebra P.O C]
    (r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C) : Prop :=
  ∀ i, nEqG (P.nx i) (P.npos i) (P.ncst i) r = 0

variable {P}

def EigenA (Q : AQuot P) (j : Wt P.rk) (y : Q.Ahat.C) : Prop :=
  ∀ x, Q.q x = y → MvPowerSeries.map Q.q.toRingHom (P.coBox x) =
    (tpowT P.rk Q.Ahat.C j : TA P.rk Q.Ahat.C) * MvPowerSeries.C y

def IsGrPres {B : Type} [CommRing B] [Algebra P.O B] (eig : Wt P.rk → B → Prop) {a : ℕ}
    (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] B) : Prop :=
  IsClosedAdic Jh ∧ IsHomog wt Jh ∧ ∀ i, eig (wt i) (e (mk Jh (X i)))

variable (P)

def resMap (v : P.lPl) : (P.RV v).C →ₐ[P.O] P.Rbox.C :=
  (P.univV v P.Rbox (fun g => P.uBox g) (by
    obtain ⟨h1, h2, h3, h4, h5, _⟩ := P.uBox_lift
    refine ⟨fun g => h1 g, fun g h => ?_, fun hk g => h3 hk g, fun N g0 => ?_, fun g => h5 g,
      fun _ h => h.elim⟩
    · simp only [Subgroup.coe_mul, Subgroup.mem_comap, Subgroup.coe_subtype, MonoidHom.coe_comp,
        Function.comp_apply]
      exact h2 g h
    · exact (continuous_subtype_val.tendsto g0).eventually (h4 N g0)
  )).exists.choose

def liftZP_unit : Prop :=
  (∃ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] P.Rbox.C), IsGrPres (IsEigen P.coBox) wt Jh e) ∧
  (∀ v, ∃ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] (P.RV v).C), IsGrPres (IsEigen (P.coV v)) wt Jh e) ∧
  ∀ Q : AQuot P, ∃ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] Q.Ahat.C), IsGrPres (EigenA Q) wt Jh e ∧
    (∀ g ∈ P.GF, ∀ i j, Q.q (P.uBox g i j) ∈
      (Aj wt Jh (P.dg i - P.dg j)).map e.toLinearEquiv.toLinearMap) ∧

    (∀ g ∉ P.GF, ∀ i j, Q.q (P.uBox g i j) ∈
      (Aj wt Jh (P.dg i + P.dg j)).map e.toLinearEquiv.toLinearMap) ∧
    maximalIdeal Q.Ahat.C ≤
      Ideal.span {y | ∃ g i j, ∃ c : P.O, y = Q.q (P.uBox g i j) - algebraMap P.O Q.Ahat.C c ∧
        y ∈ maximalIdeal Q.Ahat.C} ⊔ maximalIdeal Q.Ahat.C ^ 2 ⊔
      (maximalIdeal P.O).map (algebraMap P.O Q.Ahat.C)

def UniversalLiftFiniteType : Prop :=
  ∀ (Q : AQuot P) (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] Q.Ahat.C), IsGrPres (EigenA Q) wt Jh e →
    (∀ g i j, e.symm (Q.q (P.uBox g i j)) ∈ Asub wt Jh) ∧
    ∀ i j (N : ℕ) (g0 : P.Gam), ∀ᶠ g in nhds g0,
      e.symm (Q.q (P.uBox g i j)) - e.symm (Q.q (P.uBox g0 i j)) ∈
        (m0 wt Jh ^ N) • Submodule.span (A0sub wt Jh) (Asub wt Jh : Set _)

def IsUpper {A : Type} [CommRing A] {n : ℕ} (x : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ i j, j < i → x i j = 0

def IsResFl (rc : P.Gam → MM P) (F : P.lPl → MM P) : Prop :=
  (∀ g, IsUnit (rc g).det) ∧
  (∀ g h, rc (g * h) = rc g * (if g ∈ P.GF then rc h else
    residue P.O (P.chi h : P.O) • ((rc h)⁻¹).transpose)) ∧
  (P.kind = .GSp4 → ∀ g, P.kind.Sympl (rc g) (residue P.O (P.chi g : P.O))) ∧
  IsLocallyConstant rc ∧ (∀ g, Uq P g → rc g = 1) ∧
  ∀ v, P.kind.InG (F v) ∧ ∀ g : P.Gv v, (g : P.Gam) ∈ P.GF → IsUpper ((F v)⁻¹ * rc g * F v)

def IsPair (rc : P.Gam → MM P) (F : P.lPl → MM P) {C : TR P.O}
    (r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C)
    (gs : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) : Prop :=
  IsLift P rc r ∧ ∀ v, P.kind.InG (gs v) ∧
    (∃ b, P.kind.InG b ∧ IsUpper b ∧ resMat (gs v) = (F v).map kToRes * b) ∧
    ∀ g : P.Gv v, (g : P.Gam) ∈ P.GF → IsUpper ((gs v)⁻¹ * r g * gs v)

def PairConj {C : Type} [CommRing C] [IsLocalRing C]
    (r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C)
    (gs : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) C)
    (r' : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C)
    (gs' : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) C) : Prop :=
  ∃ γ, IsKerEl P.kind γ ∧ ConjG P.GF γ r r' ∧ ∀ v, ∃ b, P.kind.InG b ∧ IsUpper b ∧ gs' v = γ * gs v * b

def IsUnivPair (Ex : ∀ {C : TR P.O}, (P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) →
      (P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) → Prop)
    (rc : P.Gam → MM P) (F : P.lPl → MM P) (Rx : TR P.O)
    (ur : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) Rx.C)
    (ugs : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) Rx.C) : Prop :=
  IsPair P rc F ur ugs ∧ Ex ur ugs ∧ Normalised P ur ∧
  ∀ (C : TR P.O), IsArtinianRing C.C →
  ∀ (r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) gs,
    IsPair P rc F r gs → Ex r gs → Normalised P r →
    ∃! φ : Rx.C →ₐ[P.O] C.C, (∀ g, (ur g).map φ = r g) ∧
      ∀ v, ∃ b, P.kind.InG b ∧ IsUpper b ∧ gs v = (ugs v).map φ * b

def kerAbL (v : P.lPl) : Subgroup P.Gam :=
  (⨅ (n : ℕ) (φ : ContinuousMonoidHom (P.Gv v) (Multiplicative (ZMod (P.l ^ n)))),
    (φ : P.Gv v →* Multiplicative (ZMod (P.l ^ n))).ker).map (P.Gv v).subtype

def IsMuPre (v : P.lPl) (M : Subgroup P.Gam) : Prop :=
  kerAbL P v ≤ M ∧ M ≤ P.Gv v ∧ (kerAbL P v).relIndex M ≠ 0 ∧
    ∀ g ∈ P.Gv v, g ^ P.l ∈ M → g ∈ M

def ExM (M : P.lPl → Subgroup P.Gam) {C : TR P.O}
    (r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C)
    (gs : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) : Prop :=
  ∀ v, ∀ g : P.Gv v, (g : P.Gam) ∈ M v → (g : P.Gam) ∈ P.GF → ∀ i,
    ((gs v)⁻¹ * r g * gs v) i i ^ Nat.card (kk P) = ((gs v)⁻¹ * r g * gs v) i i

def ptRep {Q : AQuot P} {a : ℕ} {wt : Fin a → Wt P.rk} {Jh : Ideal (MvPowerSeries (Fin a) P.O)}
    {e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] Q.Ahat.C}
    (hent : ∀ g i j, e.symm (Q.q (P.uBox g i j)) ∈ Asub wt Jh) (c : Asub wt Jh →ₐ[P.O] ResidueField P.O) :
    P.Gam → MM P :=
  fun g => Matrix.of fun i j => c ⟨_, hent g i j⟩

def FixesX (rx : ℕ) (resx : Wt P.rk →+ Wt rx) (rc : P.Gam → MM P) (F : P.lPl → MM P) : Prop :=
  (∀ g i j, rc g i j ≠ 0 →
    (if g ∈ P.GF then resx (P.dg i - P.dg j) else resx (P.dg i + P.dg j)) = 0) ∧
  ∀ v i j, j < i → ∀ w : Wt rx,
    ∑ a ∈ Finset.univ.filter (fun a => resx (P.dg a) = w), (F v)⁻¹ i a * F v a j = 0

def NullconePointCompletion : Prop :=
  ∀ (Q : AQuot P), RingHom.ker Q.q = nIdeal P →
  ∀ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] Q.Ahat.C), IsGrPres (EigenA Q) wt Jh e →
  ∀ (hent : ∀ g i j, e.symm (Q.q (P.uBox g i j)) ∈ Asub wt Jh)
    (c : Asub wt Jh →ₐ[P.O] ResidueField P.O),
    (∀ x ∈ m0 wt Jh, c (Subalgebra.inclusion (base_subalgebra_le wt Jh) x) = 0) →
  ∀ (C : TR P.O), IsArtinianRing C.C →
    (∀ f : Asub wt Jh →ₐ[P.O] C.C, (∀ x, residue C.C (f x) = kToRes (c x)) →
      (∃ N : ℕ, ∀ x ∈ RingHom.ker c ^ N, f x = 0) →
      IsLift P (ptRep P hent c) (fun g => Matrix.of fun i j => f ⟨_, hent g i j⟩) ∧
      Normalised P (fun g => Matrix.of fun i j => f ⟨_, hent g i j⟩)) ∧
    (∀ r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C,
      IsLift P (ptRep P hent c) r → Normalised P r →
      ∃! f : Asub wt Jh →ₐ[P.O] C.C, ((∀ x, residue C.C (f x) = kToRes (c x)) ∧
        ∃ N : ℕ, ∀ x ∈ RingHom.ker c ^ N, f x = 0) ∧ ∀ g i j, r g i j = f ⟨_, hent g i j⟩)

def StableFlagPairsCompletion (Ex : ∀ {C : TR P.O}, (P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) →
      (P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) → Prop) : Prop :=
  ∀ (Q : AQuot P), RingHom.ker Q.q = nIdeal P →
  ∀ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] Q.Ahat.C), IsGrPres (EigenA Q) wt Jh e →
  ∀ (hent : ∀ g i j, e.symm (Q.q (P.uBox g i j)) ∈ Asub wt Jh)
    (c : Asub wt Jh →ₐ[P.O] ResidueField P.O),
    (∀ x ∈ m0 wt Jh, c (Subalgebra.inclusion (base_subalgebra_le wt Jh) x) = 0) →
  ∀ (F : P.lPl → MM P), IsResFl P (ptRep P hent c) F →
  ∃ (Rx : TR P.O) (ur : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) Rx.C)
    (ugs : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) Rx.C) (ι : Asub wt Jh →ₐ[P.O] Rx.C),
    (∀ x, residue Rx.C (ι x) = kToRes (c x)) ∧ (∀ g i j, ur g i j = ι ⟨_, hent g i j⟩) ∧
    IsUnivPair P Ex (ptRep P hent c) F Rx ur ugs

def RelPres {S R : Type} [CommRing S] [CommRing R] (ι : S →+* R) (eigS : Wt P.rk → S → Prop)
    (eigR : Wt P.rk → R → Prop) (aw bw : Wt P.rk → ℕ) : Prop :=
  ∃ (a b : ℕ) (wz : Fin a → Wt P.rk) (wf : Fin b → Wt P.rk) (f : Fin b → MvPowerSeries (Fin a) S)
    (e : (MvPowerSeries (Fin a) S ⧸ Ideal.span (Set.range f)) ≃+* R),
    (∀ x, e (Ideal.Quotient.mk _ (MvPowerSeries.C x)) = ι x) ∧
    (∀ i, eigR (wz i) (e (Ideal.Quotient.mk _ (X i)))) ∧
    (∀ k m, eigS (wf k - monoWt wz m) (coeff m (f k))) ∧
    ∀ j, Fintype.card {i // wz i = j} = aw j ∧ Fintype.card {k // wf k = j} = bw j

def RelativePresentation : Prop :=
  RelPres P P.frl.toRingHom (IsEigen P.coRl) (IsEigen P.coFr) (hc P 1) (hc P 2) ∧

  (Fintype.card P.lPl = 1 → ∀ v, RelPres P (resMap P v).toRingHom
    (IsEigen (P.coV v)) (IsEigen P.coBox) (hc P 1) (hc P 2)) ∧
  ∀ j : Wt P.rk, ((j ≠ 0 ∧ h0tw P (-j) = 0) ∨ (j = 0 ∧ h0tw P 0 = 0)) →
    (hc P 1 j : ℤ) - hc P 2 j = -∑ v, (h0R P v j : ℤ)

def PairRep (rc : P.Gam → MM P) (F : P.lPl → MM P) : Prop :=
  ∃ (f : Fin (hC P rc F 2) → MvPowerSeries (Fin (hC P rc F 1)) P.O) (R : TR P.O)
    (_ : (MvPowerSeries (Fin (hC P rc F 1)) P.O ⧸ Ideal.span (Set.range f)) ≃ₐ[P.O] R.C)
    (ur : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) R.C)
    (ugs : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) R.C),
    IsPair P rc F ur ugs ∧
    ∀ (C : TR P.O) (r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) gs, IsPair P rc F r gs →
      ∃! φ : R.C →ₐ[P.O] C.C, PairConj P (fun g => (ur g).map φ) (fun v => (ugs v).map φ) r gs

def FlagPairsPresentation : Prop :=
  ∀ (rc : P.Gam → MM P) (F : P.lPl → MM P), IsResFl P rc F →
    (hC P rc F 0 = 0 → PairRep P rc F) ∧
    (hC P rc F 0 = 0 → h0dC P rc = 0 →
      (hC P rc F 1 : ℤ) - hC P rc F 2 = P.degF * dimb P.kind - h0inf P rc)

def Fixes (h : Matrix (Fin P.kind.n) (Fin P.kind.n) P.O) (rc : P.Gam → MM P) (F : P.lPl → MM P) :
    Prop :=
  P.kind.InG h ∧ ConjG P.GF (h.map (residue P.O)) rc rc ∧
  ∀ v, ∃ b, P.kind.InG b ∧ IsUpper b ∧ h.map (residue P.O) * F v = F v * b

def FiniteGroupPresentation : Prop :=
  ∀ (rc : P.Gam → MM P) (F : P.lPl → MM P), IsResFl P rc F → hC P rc F 0 = 0 →
  ∀ (H : Subgroup (GL (Fin P.kind.n) P.O)) [Fintype H], ¬ P.l ∣ Fintype.card H →
    (∀ h ∈ H, Fixes P (h : Matrix (Fin P.kind.n) (Fin P.kind.n) P.O) rc F) →
    ∃ (f : Fin (hC P rc F 2) → MvPowerSeries (Fin (hC P rc F 1)) P.O) (R : TR P.O)
      (e : (MvPowerSeries (Fin (hC P rc F 1)) P.O ⧸ Ideal.span (Set.range f)) ≃ₐ[P.O] R.C)
      (ur : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) R.C)
      (ugs : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) R.C)
      (σ : H →* (MvPowerSeries (Fin (hC P rc F 1)) P.O ≃ₐ[P.O] MvPowerSeries (Fin (hC P rc F 1)) P.O)),
      IsPair P rc F ur ugs ∧
      (∀ (C : TR P.O) (r : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) gs, IsPair P rc F r gs →
        ∃! φ : R.C →ₐ[P.O] C.C, PairConj P (fun g => (ur g).map φ) (fun v => (ugs v).map φ) r gs) ∧
      (∀ h i, σ h (X i) ∈ Submodule.span P.O (Set.range fun k => (X k : MvPowerSeries _ P.O))) ∧
      (∀ h k, σ h (f k) ∈ Submodule.span P.O (Set.range f)) ∧
      ∀ h : H, ∃ τ : R.C ≃ₐ[P.O] R.C, (∀ x, τ (e (Ideal.Quotient.mk _ x)) =
          e (Ideal.Quotient.mk _ (σ h x))) ∧
        ∃ r', ConjG P.GF ((((h : GL (Fin P.kind.n) P.O) : Matrix (Fin P.kind.n) (Fin P.kind.n) P.O)).map
            (algebraMap P.O R.C)) ur r' ∧
          PairConj P (fun g => (ur g).map τ.toAlgHom) (fun v => (ugs v).map τ) r'
            (fun v => (((h : GL (Fin P.kind.n) P.O) : Matrix (Fin P.kind.n) (Fin P.kind.n) P.O)).map
              (algebraMap P.O R.C) * ugs v)

def TorusPairsGeneral (Ex : ∀ {C : TR P.O}, (P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) →
      (P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) C.C) → Prop)
    (hN : (P.Gam → MM P) → (P.lPl → MM P) → ∀ rx : ℕ, (Wt P.rk →+ Wt rx) → ℕ → Wt rx → ℕ) : Prop :=
  ∀ (Q : AQuot P), RingHom.ker Q.q = nIdeal P →
  ∀ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] Q.Ahat.C), IsGrPres (EigenA Q) wt Jh e →
  ∀ (hent : ∀ g i j, e.symm (Q.q (P.uBox g i j)) ∈ Asub wt Jh)
    (c : Asub wt Jh →ₐ[P.O] ResidueField P.O),
    (∀ x ∈ m0 wt Jh, c (Subalgebra.inclusion (base_subalgebra_le wt Jh) x) = 0) →
  ∀ (F : P.lPl → MM P) (Rx : TR P.O)
    (ur : P.Gam → Matrix (Fin P.kind.n) (Fin P.kind.n) Rx.C)
    (ugs : P.lPl → Matrix (Fin P.kind.n) (Fin P.kind.n) Rx.C),
    IsResFl P (ptRep P hent c) F → IsUnivPair P Ex (ptRep P hent c) F Rx ur ugs →
  ∀ (rx : ℕ) (resx : Wt P.rk →+ Wt rx) (coX : Rx.C →ₐ[P.O] TA rx Rx.C),
    Function.Surjective resx → FixesX P rx resx (ptRep P hent c) F → (∀ x, constantCoeff (coX x) = x) →
    ConjG P.GF (diagTT (fun i => resx (P.dg i)) Rx.C) (fun g => (ur g).map MvPowerSeries.C)
      (fun g => (ur g).map coX) →
    (∀ v, ∃ b, P.kind.InG b ∧ IsUpper b ∧ (ugs v).map coX =
      diagTT (fun i => resx (P.dg i)) Rx.C * (ugs v).map MvPowerSeries.C * b) →
    (∃ (a b : ℕ) (wZ : Fin a → Wt rx) (wf : Fin b → Wt rx) (f : Fin b → MvPowerSeries (Fin a) P.O)
      (e : (MvPowerSeries (Fin a) P.O ⧸ Ideal.span (Set.range f)) ≃ₐ[P.O] Rx.C),
      (∀ i, IsEigen coX (wZ i) (e (Ideal.Quotient.mk _ (X i)))) ∧ (∀ k, f k ∈ Pj P.O wZ (wf k)) ∧
      ∀ j, (Fintype.card {k // wf k = j} = hN (ptRep P hent c) F rx resx 2 j) ∧
        ((Fintype.card {i // wZ i = j} : ℤ) = if j = 0 then
          (hN (ptRep P hent c) F rx resx 1 0 : ℤ) + P.rk - hN (ptRep P hent c) F rx resx 0 0
          else (hN (ptRep P hent c) F rx resx 1 j : ℤ) - hN (ptRep P hent c) F rx resx 0 j)) ∧

    ∀ (μc : Wt P.rk →+ ℤ) (coM : Rx.C →ₐ[P.O] TA 1 Rx.C) (y : Rx.C) (yt : P.O) (sg : ℤ),
      P.rk = rx + 1 → Function.Bijective (fun w => (resx w, μc w)) →
      (∀ x, constantCoeff (coM x) = x) →
      ConjG P.GF (diagTT (fun i _ => μc (P.dg i)) Rx.C) (fun g => (ur g).map MvPowerSeries.C)
        (fun g => (ur g).map coM) →
      (sg = 1 ∨ sg = -1) → IsEigen coM (fun _ => sg) y → IsEigen coX 0 y → IsUnit y →
      y - algebraMap P.O Rx.C yt ∈ maximalIdeal Rx.C →
      Nonempty (MvPowerSeries (Fin 1) (Rx.C ⧸ Ideal.span {y - algebraMap P.O Rx.C yt}) ≃ₐ[P.O] Rx.C) ∧
      ∃ (a b : ℕ) (wZ : Fin a → Wt rx) (wf : Fin b → Wt rx) (f : Fin b → MvPowerSeries (Fin a) P.O)
        (e' : (MvPowerSeries (Fin a) P.O ⧸ Ideal.span (Set.range f)) ≃ₐ[P.O]
          (Rx.C ⧸ Ideal.span {y - algebraMap P.O Rx.C yt})),

        (∀ i, ∃ z : Rx.C, IsEigen coX (wZ i) z ∧
          e' (Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mk _ z) ∧
        (∀ k, f k ∈ Pj P.O wZ (wf k)) ∧
        ∀ j, (Fintype.card {k // wf k = j} = hN (ptRep P hent c) F rx resx 2 j) ∧
          ((Fintype.card {i // wZ i = j} : ℤ) + if j = 0 then 1 else 0) = if j = 0 then
          (hN (ptRep P hent c) F rx resx 1 0 : ℤ) + P.rk - hN (ptRep P hent c) F rx resx 0 0
          else (hN (ptRep P hent c) F rx resx 1 j : ℤ) - hN (ptRep P hent c) F rx resx 0 j

def TorusPairs : Prop := TorusPairsGeneral P (fun _ _ => True) (hCj P)

def TorusPairsMultiplierVariant : Prop :=
  ∀ M : P.lPl → Subgroup P.Gam, (∀ v, IsMuPre P v (M v)) →

    (∀ v, ∀ g ∈ M v, (P.chi g : P.O) ^ Nat.card (kk P) = (P.chi g : P.O)) →
    TorusPairsGeneral P (ExM P M) (fun rc F => hCjM P rc F M)

end Prob

section Lit

def litGordan : Prop :=
  ∀ (a rk : ℕ) (wt : Fin a → Wt rk),
    (∃ s : Finset (Fin a →₀ ℕ), (∀ m ∈ s, monoWt wt m = 0) ∧
      ∀ m, monoWt wt m = 0 → m ∈ AddSubmonoid.closure (s : Set (Fin a →₀ ℕ))) ∧
    ∀ j, ∃ s : Finset (Fin a →₀ ℕ), (∀ m ∈ s, monoWt wt m = j) ∧
      ∀ m, monoWt wt m = j → ∃ m₀ ∈ s, ∃ m', monoWt wt m' = 0 ∧ m = m₀ + m'

def litFarkas : Prop :=
  ∀ (a r : ℕ) (w : Fin a → Fin r → ℚ) (c : Fin a → ℚ),
    (∃ τ : Fin r → ℚ, ∀ i, 0 < c i + ∑ s, w i s * τ s) ∨
    (∃ n : Fin a → ℚ, (∀ i, 0 ≤ n i) ∧ n ≠ 0 ∧ ∑ i, n i • w i = 0 ∧ ∑ i, n i * c i ≤ 0)

variable (P : LiftProb)

def litFinA : Prop := ∀ j, FinFib (adAct P.GF P.rbar) (gW P j) (locZ P)

def litFinC : Prop :=
  ∀ rc F, IsResFl P rc F → FinFib (adAct P.GF rc) (gLie (kk P) P.kind) (locB P F) ∧
    (∀ rx resx, FixesX P rx resx rc F → ∀ j, FinFib (adAct P.GF rc) (gWx P rx resx j) (locB P F)) ∧
    ∀ M, (∀ v, IsMuPre P v (M v)) → ∀ rx resx, FixesX P rx resx rc F →
      ∀ j, FinFib (adAct P.GF rc) (gWx P rx resx j) (locM P F M)

def litTateA : Prop := ∀ j, (hc P 0 j : ℤ) - hc P 1 j + hc P 2 j - hc P 3 j = ∑ v, (h0R P v j : ℤ)

def litTateC : Prop :=
  ∀ rc F, IsResFl P rc F →
    (hC P rc F 0 : ℤ) - hC P rc F 1 + hC P rc F 2 - hC P rc F 3 = h0inf P rc - P.degF * dimb P.kind

def litPTA : Prop := ∀ j, hc P 3 j = h0tw P (-j)

def litPTC : Prop := ∀ rc F, IsResFl P rc F → hC P rc F 3 ≤ h0dC P rc

def IsRes (rc : P.Gam → MM P) : Prop :=
  (∀ g, IsUnit (rc g).det) ∧
  (∀ g h, rc (g * h) = rc g * (if g ∈ P.GF then rc h else
    residue P.O (P.chi h : P.O) • ((rc h)⁻¹).transpose)) ∧
  (P.kind = .GSp4 → ∀ g, P.kind.Sympl (rc g) (residue P.O (P.chi g : P.O))) ∧
  IsLocallyConstant rc ∧ (∀ g, Uq P g → rc g = 1)

variable {P}

section Grp

variable {H : Type} [Group H] [TopologicalSpace H] (ι : H →* P.Gam) (S : Set P.Gam)
  (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P))

def CochG (m : ℕ) : Submodule (kk P) ((Fin m → H) → MM P) where
  carrier := {c | IsCoch N c ∧ ∀ y z : Fin m → H, (∀ i, (ι (y i))⁻¹ * ι (z i) ∈ S) → c y = c z}
  add_mem' {c c'} hc hc' := ⟨(CochSub m N).add_mem hc.1 hc'.1, fun y z h => by
    simp only [Pi.add_apply]; rw [hc.2 y z h, hc'.2 y z h]⟩
  zero_mem' := ⟨(CochSub m N).zero_mem, fun _ _ _ => rfl⟩
  smul_mem' a c hc := ⟨(CochSub m N).smul_mem a hc.1, fun y z h => by
    simp only [Pi.smul_apply]; rw [hc.2 y z h]⟩

def ZG (m : ℕ) : Submodule (kk P) ((Fin m → H) → MM P) :=
  CochG ι S N m ⊓ LinearMap.ker (dC (fun h : H => act (ι h)) m)

def BG : (m : ℕ) → Submodule (kk P) ((Fin m → H) → MM P)
  | 0 => ⊥
  | m + 1 => (CochG ι S N m).map (dC (fun h : H => act (ι h)) m)

abbrev HG (m : ℕ) : Type := ZG ι S act N m ⧸ (BG ι S act N m).comap (ZG ι S act N m).subtype

def hG (m : ℕ) : ℕ := Module.finrank (kk P) (HG ι S act N m)

def FinCd (d : ℕ) : Prop :=
  (∀ m, FiniteDimensional (kk P) (HG ι S act N m)) ∧ ∀ m, d < m → hG ι S act N m = 0

def chiG : ℤ := (hG ι S act N 0 : ℤ) - hG ι S act N 1 + hG ι S act N 2

def StabG : Prop := ∀ h : H, ∀ X ∈ N, act (ι h) X ∈ N

end Grp

def resAll (m : ℕ) : ((Fin m → P.Gam) → MM P) →ₗ[kk P] FB P m :=
  LinearMap.prod (LinearMap.pi fun q => resL (P.Gq q) m) (LinearMap.pi fun v => resL (P.Gv v) m)

def ZlocS (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P)) :
    Submodule (kk P) (FB P 2) :=
  Submodule.span (kk P) {y | y ∈ AdmB N 2 ∧ dB act 2 y = 0}

def BlocS (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P)) :
    Submodule (kk P) (FB P 2) :=
  Submodule.span (kk P) ({y | ∃ a, IsCoch N a ∧ dC act 2 a = 0 ∧ y = resAll 2 a} ∪ dB act 1 '' AdmB N 1)

def cokPT (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P)) : ℕ :=
  Module.finrank (kk P) (ZlocS act N ⧸ (BlocS act N).comap (ZlocS act N).subtype)

variable (P)

def tateFin : Prop :=
  ∀ rc, IsRes P rc → ∀ N : Submodule (kk P) (MM P),
    (StabG (MonoidHom.id P.Gam) (adAct P.GF rc) N →
      FinCd (MonoidHom.id P.Gam) {1} (adAct P.GF rc) N 2) ∧
    (∀ v, StabG (P.Gv v).subtype (adAct P.GF rc) N →
      FinCd (P.Gv v).subtype {1} (adAct P.GF rc) N 2) ∧
    ∀ q, StabG (P.Gq q).subtype (adAct P.GF rc) N → FinCd (P.Gq q).subtype {1} (adAct P.GF rc) N 2

def tateGlobal : Prop :=
  ∀ rc, IsRes P rc → ∀ N : Submodule (kk P) (MM P), StabG (MonoidHom.id P.Gam) (adAct P.GF rc) N →
    chiG (MonoidHom.id P.Gam) {1} (adAct P.GF rc) N =
      (∑ v, (Module.finrank (kk P) ↥(N ⊓ LinearMap.ker (adAct P.GF rc (P.cv v) - LinearMap.id)) : ℤ)) -
        P.degF * Module.finrank (kk P) N

def tateLocal : Prop :=
  ∀ rc, IsRes P rc → ∀ N : Submodule (kk P) (MM P),
    (∀ v, StabG (P.Gv v).subtype (adAct P.GF rc) N →
      chiG (P.Gv v).subtype {1} (adAct P.GF rc) N = -((P.dv v : ℤ) * Module.finrank (kk P) N)) ∧
    ∀ q, StabG (P.Gq q).subtype (adAct P.GF rc) N → chiG (P.Gq q).subtype {1} (adAct P.GF rc) N = 0

def unrLocal : Prop :=
  ∀ rc, IsRes P rc → ∀ N : Submodule (kk P) (MM P),
    ∀ q, StabG (P.Gq q).subtype (adAct P.GF rc) N →
      FinCd (P.Gq q).subtype (NqSet q) (adAct P.GF rc) N 1 ∧
      hG (P.Gq q).subtype (NqSet q) (adAct P.GF rc) N 1 = hG (P.Gq q).subtype (NqSet q) (adAct P.GF rc) N 0

def poitouTate : Prop :=
  (∀ j, cokPT (adAct P.GF P.rbar) (gW P j) = h0tw P (-j)) ∧
  ∀ rc, IsRes P rc → cokPT (adAct P.GF rc) (gLie (kk P) P.kind) = h0dC P rc

def LitG : Prop :=
  tateFin P ∧ tateGlobal P ∧ tateLocal P ∧ unrLocal P ∧ poitouTate P

end Lit

def lit1 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := litGordan
def lit2 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := litFarkas

def Conclusion1 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := ∀ P : LiftProb, liftZP_unit P

def Conclusion2 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := FiniteTypeRingPart ∧ ∀ P : LiftProb, UniversalLiftFiniteType P

def PointsLemma (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := PointsLemmaAnyRank

def Conclusion4 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop :=
  ∀ P : LiftProb, NullconePointCompletion P ∧ StableFlagPairsCompletion P (fun _ _ => True) ∧
    ∀ M : P.lPl → Subgroup P.Gam, (∀ v, IsMuPre P v (M v)) → StableFlagPairsCompletion P (ExM P M)

def RelativePresentationLiterature (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop :=
  ∀ P : LiftProb, litFinA P → litTateA P → litPTA P → RelativePresentation P

def PairsWithFiniteGroup (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop :=
  ∀ P : LiftProb, Split P → litFinC P → litTateC P → litPTC P → FlagPairsPresentation P ∧ FiniteGroupPresentation P

def TorusPairsWithVariant (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop :=
  ∀ P : LiftProb, Split P → litFinC P → TorusPairs P ∧ TorusPairsMultiplierVariant P

def FibreComplexFiniteness (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop :=
  ∀ P : LiftProb, LitG P →
    (litFinA P ∧ litTateA P ∧ litPTA P) ∧ (Split P → litFinC P ∧ litTateC P ∧ litPTC P)

def Conclusion5 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop :=
  RelativePresentationLiterature D V ∧ PairsWithFiniteGroup D V ∧ TorusPairsWithVariant D V ∧ FibreComplexFiniteness D V

def Conclusion₂ (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop :=
  Conclusion1 D V ∧ Conclusion2 D V ∧ PointsLemma D V ∧ Conclusion4 D V ∧ Conclusion5 D V

def Stmt (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := Conclusion₂ D V

def Lit (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := lit1 D V ∧ lit2 D V

def LiftingLemmasStatement (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := Lit D V → Conclusion₂ D V

def OrbitValuationBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), Formalism.BasicNotions.VData (Fm.D x i)) : Prop :=
  ∀ x (i : Fm.Ix x), Conclusion₂ (Fm.D x i) (VF x i)

def LitF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), Formalism.BasicNotions.VData (Fm.D x i)) : Prop :=
  ∀ x (i : Fm.Ix x), Lit (Fm.D x i) (VF x i)

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), Formalism.BasicNotions.VData (Fm.D x i)) : Prop :=
  OrbitValuationBound Fm VF

def FamilyLiftingStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), Formalism.BasicNotions.VData (Fm.D x i)) :
    Prop :=
  LitF Fm VF → OrbitValuationBound Fm VF

end Formalism.MainNotions.UnusedSlot38
end
end

section
noncomputable section

open MvPowerSeries

namespace Formalism.MainNotions.GradedPowerSeriesLemmas

section Graded

variable (O : Type) [CommRing O] {a : ℕ} (wt : Fin a → ℤ)

def W : Fin a → Formalism.BasicNotions.V1.Wt 1 := fun v _ => wt v

def cj (j : ℤ) : Formalism.BasicNotions.V1.Wt 1 := fun _ => j

abbrev Pring : Subalgebra O (MvPowerSeries (Fin a) O) := Formalism.MainNotions.UnusedSlot38.Psub O (W wt)

abbrev PT : Type := ↥(Pring O wt)

variable {O wt}

def IsHom (j : ℤ) (f : PT O wt) : Prop :=
  (f : MvPowerSeries (Fin a) O) ∈ Formalism.MainNotions.UnusedSlot38.Pj O (W wt) (cj j)

def PjP (j : ℤ) : Submodule O (PT O wt) :=
  (Formalism.MainNotions.UnusedSlot38.Pj O (W wt) (cj j)).comap (Pring O wt).val.toLinearMap

def comp (j : ℤ) (f : MvPowerSeries (Fin a) O) : MvPowerSeries (Fin a) O :=
  Formalism.MainNotions.UnusedSlot38.comp (W wt) (cj j) f

theorem X_mem (v : Fin a) : (X v : MvPowerSeries (Fin a) O) ∈ Pring O wt :=
  Formalism.MainNotions.UnusedSlot38.Pj_le_P (W wt) (W wt v) (Formalism.MainNotions.UnusedSlot38.X_mem_Pj (W wt) v)

def Xv (v : Fin a) : PT O wt := ⟨X v, X_mem v⟩

def cc : PT O wt →+* O := (constantCoeff (σ := Fin a) (R := O)).comp (Pring O wt).val.toRingHom

variable (𝔓 : Ideal (PT O wt))

abbrev AT : Type := PT O wt ⧸ 𝔓

def mkA : PT O wt →ₐ[O] AT 𝔓 := Ideal.Quotient.mkₐ O 𝔓

def Aj (j : ℤ) : Submodule O (AT 𝔓) := (PjP (O := O) (wt := wt) j).map (mkA 𝔓).toLinearMap

def mA : Ideal (AT 𝔓) := Ideal.map (mkA 𝔓) (RingHom.ker (cc (O := O) (wt := wt)))

def Wj (j : ℤ) : Submodule O (mA 𝔓).Cotangent :=
  Submodule.span O {c | ∃ g : mA 𝔓, (g : AT 𝔓) ∈ Aj 𝔓 j ∧ c = (mA 𝔓).toCotangent g}

def dSet {ι : Type} (F : ι → PT O wt) : Set (mA 𝔓).Cotangent :=
  {c | ∃ i, ∃ g : mA 𝔓, (g : AT 𝔓) = mkA 𝔓 (F i) ∧ c = (mA 𝔓).toCotangent g}

def SpansRat {M : Type} [AddCommGroup M] [Module O M] (s : Set M) (W : Submodule O M) : Prop :=
  Submodule.span O s ≤ W ∧ ∀ w ∈ W, ∃ c : O, c ≠ 0 ∧ c • w ∈ Submodule.span O s

def LinIndepRat {ι : Type} [Fintype ι] (F : ι → PT O wt) : Prop :=
  ∀ (g : ι → mA 𝔓), (∀ i, (g i : AT 𝔓) = mkA 𝔓 (F i)) →
    ∀ c : ι → O, (∃ t : O, t ≠ 0 ∧ t • ∑ i, c i • (mA 𝔓).toCotangent (g i) = 0) → ∀ i, c i = 0

abbrev Tors : Submodule O (mA 𝔓).Cotangent := Submodule.torsion O (mA 𝔓).Cotangent

def PiLat : Submodule O ((mA 𝔓).Cotangent ⧸ Tors 𝔓) :=
  Submodule.span O {q | ∃ g : mA 𝔓, (g : AT 𝔓) ∈ Aj 𝔓 (-1) ∧ q = (Tors 𝔓).mkQ ((mA 𝔓).toCotangent g)}

def spanF {ι : Type} (F : ι → PT O wt) : Submodule O ((mA 𝔓).Cotangent ⧸ Tors 𝔓) :=
  Submodule.span O {q | ∃ i, ∃ g : mA 𝔓, (g : AT 𝔓) = mkA 𝔓 (F i) ∧
    q = (Tors 𝔓).mkQ ((mA 𝔓).toCotangent g)}

def VPrime {ι : Type} (F : ι → PT O wt) : ℕ∞ :=
  Module.length O (↥(PiLat 𝔓) ⧸ (spanF 𝔓 F).comap (PiLat 𝔓).subtype)

variable {r s r' s' m : ℕ}
  (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
  (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt)

def IS : Ideal (PT O wt) :=
  𝔓 ⊔ Ideal.span (Set.range F ∪ Set.range G ∪ Set.range E1 ∪ Set.range E2 ∪ Set.range Z)

abbrev ST : Type := PT O wt ⧸ IS 𝔓 F G E1 E2 Z

def mkS : PT O wt →ₐ[O] ST 𝔓 F G E1 E2 Z := Ideal.Quotient.mkₐ O _

def Sj (j : ℤ) : Submodule O (ST 𝔓 F G E1 E2 Z) :=
  (PjP (O := O) (wt := wt) j).map (mkS 𝔓 F G E1 E2 Z).toLinearMap

end Graded

section Points

variable {O : Type} [CommRing O] [IsDomain O] {a : ℕ} {wt : Fin a → ℤ}

abbrev Ebar (O : Type) [CommRing O] [IsDomain O] : Type := AlgebraicClosure (FractionRing O)

variable {R : Type} [CommRing R] [Algebra O R] (mk : PT O wt →ₐ[O] R)

def Fixed (ξ : R →ₐ[O] Ebar O) : Prop :=
  ∀ (t : (Ebar O)ˣ) (j : ℤ) (f : PT O wt), IsHom j f → ξ (mk f) = (t : Ebar O) ^ j * ξ (mk f)

def SameOrbit (ξ ξ' : R →ₐ[O] Ebar O) : Prop :=
  ∃ t : (Ebar O)ˣ, ∀ (j : ℤ) (f : PT O wt), IsHom j f → ξ' (mk f) = (t : Ebar O) ^ j * ξ (mk f)

def IsNotBasePoint (ξ : R →ₐ[O] Ebar O) : Prop :=
  ∃ f : PT O wt, ξ (mk f) ≠ algebraMap O (Ebar O) (cc f)

def NegZero (ξ : R →ₐ[O] Ebar O) : Prop := ∀ v, wt v < 0 → ξ (mk (Xv v)) = 0

def PosZero (ξ : R →ₐ[O] Ebar O) : Prop := ∀ v, 0 < wt v → ξ (mk (Xv v)) = 0

def NegNZ (ξ : R →ₐ[O] Ebar O) : Prop := ∃ v, wt v < 0 ∧ ξ (mk (Xv v)) ≠ 0

def PosNZ (ξ : R →ₐ[O] Ebar O) : Prop := ∃ v, 0 < wt v ∧ ξ (mk (Xv v)) ≠ 0

def SameD (ξ ξ₁ : R →ₐ[O] Ebar O) : Prop := ∀ v, wt v = 0 → ξ (mk (Xv v)) = ξ₁ (mk (Xv v))

def Both (ξ : R →ₐ[O] Ebar O) : Prop := NegNZ mk ξ ∧ PosNZ mk ξ

def xiE (ξ : R →ₐ[O] Ebar O) : TensorProduct O (Ebar O) R →ₐ[Ebar O] Ebar O :=
  Algebra.TensorProduct.lift (AlgHom.id (Ebar O) (Ebar O)) ξ (fun _ _ => Commute.all _ _)

variable [IsDiscreteValuationRing O]

def vE (x : Ebar O) : ℚ :=
  (((IsDiscreteValuationRing.addVal O) ((minpoly O x).coeff 0)).toNat : ℚ) /
    ((minpoly O x).natDegree : ℚ)

end Points

section Hyp

variable {O : Type} [CommRing O] [IsDomain O] {a : ℕ} {wt : Fin a → ℤ}
  (𝔓 : Ideal (PT O wt)) {r s r' s' m : ℕ}
  (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
  (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt)

def DataM : Prop :=
  (∀ v, -2 ≤ wt v ∧ wt v ≤ 2) ∧
  (∀ f ∈ 𝔓, ∀ j, ∃ g ∈ 𝔓, (g : MvPowerSeries (Fin a) O) = comp (wt := wt) j f) ∧
  𝔓.IsPrime ∧ Module.Flat O (AT 𝔓) ∧
  (∀ f ∈ 𝔓, cc f = 0) ∧
  (∀ i, IsHom (-1) (F i)) ∧ (∀ i, IsHom (-2) (G i)) ∧ (∀ i, IsHom 1 (E1 i)) ∧
  (∀ i, IsHom 2 (E2 i)) ∧ (∀ i, IsHom 0 (Z i) ∧ cc (Z i) = 0)

def M1 (rp sp l : ℕ) : Prop :=
  (∃ _ : (Ideal.map (algebraMap (AT 𝔓) (Localization.Away (algebraMap O (AT 𝔓) (l : O))))
      (mA 𝔓)).IsPrime,
    IsRegularLocalRing (Localization.AtPrime (Ideal.map (algebraMap (AT 𝔓)
      (Localization.Away (algebraMap O (AT 𝔓) (l : O)))) (mA 𝔓)))) ∧
  1 ≤ r ∧
  Module.finrank O (Wj 𝔓 (-1)) = r ∧ Module.finrank O (Wj 𝔓 (-2)) = s ∧
  Module.finrank O (Wj 𝔓 1) = rp + 1 ∧ Module.finrank O (Wj 𝔓 2) = sp + 1 ∧
  Module.finrank O (Wj 𝔓 0) = m ∧
  SpansRat (dSet 𝔓 F) (Wj 𝔓 (-1)) ∧
  SpansRat (dSet 𝔓 G) (Wj 𝔓 (-2)) ∧ LinIndepRat 𝔓 G ∧
  SpansRat (dSet 𝔓 Z) (Wj 𝔓 0) ∧ LinIndepRat 𝔓 Z

def M2 : Prop := Module.Finite O (Sj 𝔓 F G E1 E2 Z 0)

def M3 : Prop :=
  ∀ x₁ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, Fixed (mkS 𝔓 F G E1 E2 Z) x₁ →
    IsNotBasePoint (mkS 𝔓 F G E1 E2 Z) x₁ →
    (¬ ∃ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, NegZero (mkS 𝔓 F G E1 E2 Z) ξ ∧
        PosNZ (mkS 𝔓 F G E1 E2 Z) ξ ∧ SameD (mkS 𝔓 F G E1 E2 Z) ξ x₁) ∨
    (¬ ∃ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, PosZero (mkS 𝔓 F G E1 E2 Z) ξ ∧
        NegNZ (mkS 𝔓 F G E1 E2 Z) ξ ∧ SameD (mkS 𝔓 F G E1 E2 Z) ξ x₁)

def M4 : Prop :=
  ∀ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, Both (mkS 𝔓 F G E1 E2 Z) ξ →
    IsRegularLocalRing
      (@Localization.AtPrime _ _ (RingHom.ker (xiE ξ).toRingHom) (RingHom.ker_isPrime _)) ∧
    ringKrullDim
      (@Localization.AtPrime _ _ (RingHom.ker (xiE ξ).toRingHom) (RingHom.ker_isPrime _)) = 1

def M5 (a₀ : PT O wt) : Prop :=
  IsHom 0 a₀ ∧ cc a₀ = 0 ∧
  ∀ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, Both (mkS 𝔓 F G E1 E2 Z) ξ →
    ξ (mkS 𝔓 F G E1 E2 Z a₀) ≠ 0

def IsDerS {M : Type} [AddCommGroup M] [Module O M] (D : ST 𝔓 F G E1 E2 Z →ₗ[O] M) : Prop :=
  ∀ f g : PT O wt, D (mkS 𝔓 F G E1 E2 Z (f * g)) =
    cc f • D (mkS 𝔓 F G E1 E2 Z g) + cc g • D (mkS 𝔓 F G E1 E2 Z f)

def IsDerA (D : AT 𝔓 →ₗ[O] O) : Prop :=
  ∀ f g : PT O wt, D (mkA 𝔓 (f * g)) = cc f * D (mkA 𝔓 g) + cc g * D (mkA 𝔓 f)

end Hyp

section Bridge

variable {O : Type} [CommRing O] {a : ℕ} (wt : Fin a → ℤ) (Jh : Ideal (MvPowerSeries (Fin a) O))

def PofJ : Ideal (PT O wt) := Jh.comap (Pring O wt).val

def toA : PT O wt →ₐ[O] Formalism.MainNotions.UnusedSlot38.Asub (W wt) Jh :=
  ((Formalism.MainNotions.UnusedSlot38.mk Jh).comp (Pring O wt).val).codRestrict _ (fun f => ⟨f, f.2, rfl⟩)

theorem ker_toA : RingHom.ker (toA wt Jh) = PofJ wt Jh := by
  ext f
  rw [RingHom.mem_ker, Subtype.ext_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

end Bridge

def IsOl (O : Type) [CommRing O] (l : ℕ) : Prop := Formalism.MainNotions.UnusedSlot38.IsCoeff O l ∧ Irreducible (l : O)

def LemmaM : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), IsOl O l →
  ∀ (a : ℕ) (wt : Fin a → ℤ) (𝔓 : Ideal (PT O wt)) (r s r' s' m : ℕ)
    (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
    (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt) (a₀ : PT O wt),
  DataM 𝔓 F G E1 E2 Z → M1 𝔓 F G Z r' s' l → M2 𝔓 F G E1 E2 Z → M3 𝔓 F G E1 E2 Z →
  M4 𝔓 F G E1 E2 Z → M5 𝔓 F G E1 E2 Z a₀ →
  ∃ T : Finset (ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O),
    (∀ τ ∈ T, Both (mkS 𝔓 F G E1 E2 Z) τ) ∧
    (∀ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, Both (mkS 𝔓 F G E1 E2 Z) ξ →
      ∃! τ, τ ∈ T ∧ SameOrbit (mkS 𝔓 F G E1 E2 Z) τ ξ) ∧
    ∃ V' : ℕ, VPrime 𝔓 F = V' ∧ (V' : ℚ) ≤ 2 * ∑ τ ∈ T, vE (τ (mkS 𝔓 F G E1 E2 Z a₀))

def LemmaM' : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), IsOl O l →
  ∀ (a : ℕ) (wt : Fin a → ℤ) (𝔓 : Ideal (PT O wt)) (r s r' s' m : ℕ)
    (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
    (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt),
  DataM 𝔓 F G E1 E2 Z →
  ∀ (MM : Type) [AddCommGroup MM] [Module O MM] [Finite MM] (k₀ : ℕ), 1 ≤ k₀ →
  ∀ φ : MM →+ (ST 𝔓 F G E1 E2 Z →ₗ[O] O ⧸ Ideal.span {(l : O) ^ k₀}),
    Function.Injective φ →
    (∀ x : MM, IsDerS 𝔓 F G E1 E2 Z (φ x) ∧
      (∀ j : ℤ, j ≠ -1 → ∀ f, IsHom j f → φ x (mkS 𝔓 F G E1 E2 Z f) = 0) ∧
      ∃ Dt : AT 𝔓 →ₗ[O] O, IsDerA 𝔓 Dt ∧
        (∀ j : ℤ, j ≠ -1 → ∀ f, IsHom j f → Dt (mkA 𝔓 f) = 0) ∧
        ∀ f : PT O wt, Ideal.Quotient.mk _ (Dt (mkA 𝔓 f)) = φ x (mkS 𝔓 F G E1 E2 Z f)) →
    Module.length O MM ≤ VPrime 𝔓 F

def LemmaM'fg : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), IsOl O l →
  ∀ (a : ℕ) (wt : Fin a → ℤ) (𝔓 : Ideal (PT O wt)) (r s r' s' m : ℕ)
    (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
    (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt),
  DataM 𝔓 F G E1 E2 Z →
  ∀ (MM : Type) [AddCommGroup MM] [Module O MM] [Module.Finite O MM] (k₀ : ℕ), 1 ≤ k₀ →
  ∀ φ : MM →+ (ST 𝔓 F G E1 E2 Z →ₗ[O] O ⧸ Ideal.span {(l : O) ^ k₀}),
    Function.Injective φ →
    (∀ x : MM, IsDerS 𝔓 F G E1 E2 Z (φ x) ∧
      (∀ j : ℤ, j ≠ -1 → ∀ f, IsHom j f → φ x (mkS 𝔓 F G E1 E2 Z f) = 0) ∧
      ∃ Dt : AT 𝔓 →ₗ[O] O, IsDerA 𝔓 Dt ∧
        (∀ j : ℤ, j ≠ -1 → ∀ f, IsHom j f → Dt (mkA 𝔓 f) = 0) ∧
        ∀ f : PT O wt, Ideal.Quotient.mk _ (Dt (mkA 𝔓 f)) = φ x (mkS 𝔓 F G E1 E2 Z f)) →
    IsFiniteLength O MM ∧ Module.length O MM ≤ VPrime 𝔓 F

set_option linter.unusedVariables false in

def adm1 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := Formalism.MainNotions.UnusedSlot38.FiniteTypeRingPart

def admitted (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := adm1 D V

set_option linter.unusedVariables false in

def Conclusion1 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := LemmaM
set_option linter.unusedVariables false in

def Conclusion2 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := LemmaM'
set_option linter.unusedVariables false in

def LemmaMPrimeFinitelyGenerated (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := LemmaM'fg

def Conclusion₂ (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := Conclusion1 D V ∧ Conclusion2 D V

def Stmt (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := admitted D V → Conclusion₂ D V

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), Formalism.BasicNotions.VData (Fm.D x i))

def OrbitValuationBound : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion₂ (Fm.D x i) (VF x i)

def AdmF : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, admitted (Fm.D x i) (VF x i)

def KudlaFamilyStatement : Prop := AdmF Fm VF → OrbitValuationBound Fm VF

end Family

end Formalism.MainNotions.GradedPowerSeriesLemmas
end
end
