import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermCompatId

section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section Kos
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
  {κ : Type} [LinearOrder κ]

def KE {M : Type} [AddCommGroup M] [Module ℂ M] (C : Cx ℂ M) (d : ℤ) : Prop := ∀ m < d, C.Z m ≤ C.B m

def sm (M : Submodule ℂ E) (T : Set S) : Submodule ℂ E := ⨆ r ∈ T, M.map (act r)

def Stab (R : Subalgebra ℂ S) (M : Submodule ℂ E) : Prop := ∀ r ∈ R, ∀ m ∈ M, act r m ∈ M

def Reg (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) : Prop :=
  ∀ k : Fin d, ∀ m ∈ M, act (f k) m ∈ sm act M (f '' {j | j < k}) → m ∈ sm act M (f '' {j | j < k})

def kos (M : Submodule ℂ E) (r : κ → S) : Cx ℂ (Finset κ → E) := acx (fun _ => M) fun l => act (r l)

def kosT (M : Submodule ℂ E) (u : κ → Sˣ) (z : κ → S) : Cx ℂ (Finset κ → E) :=
  acx (fun L => M.map (act ((∏ l ∈ L, u l : Sˣ) : S))) fun l => act (z l)

def unsc (u : κ → Sˣ) (c : Finset κ → E) : Finset κ → E := fun L => act (((∏ l ∈ L, u l)⁻¹ : Sˣ) : S) (c L)

def detC {p : ℕ} (ρ : κ → Fin p → S) (s : Finset κ) : S :=
  if h : s.card = p then (Matrix.of fun a b => ρ (s.orderEmbOfFin h a) b).det else 0

end Kos

section Idx
variable {β κ κ' E : Type} [LinearOrder β] [LinearOrder κ] [LinearOrder κ']

def col (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) : Finset κ → E := fun L => c (uni b L)

def resK (e : κ' ↪o κ) (c : Finset (β ⊕ₗ κ) → E) : Finset (β ⊕ₗ κ') → E := fun s => c (uni (lft s) ((rgt s).map e.toEmbedding))

def top (c : Finset (β ⊕ₗ κ) → E) : Finset β → E := fun b => c (uni b ∅)

def inlE : β ↪o β ⊕ₗ κ := OrderEmbedding.ofStrictMono _ Sum.Lex.inl_strictMono
def inrE : κ ↪o β ⊕ₗ κ := OrderEmbedding.ofStrictMono _ Sum.Lex.inr_strictMono

def img {d : ℕ} (e : Fin d ↪o κ) : Finset κ := Finset.univ.map e.toEmbedding

def pk {d : ℕ} (I : Finset (Fin (d + 1))) : Fin (d + 1) := if h : I.Nonempty then I.min' h else 0

abbrev Two (d : ℕ) : Type := Fin (d + 1) ⊕ₗ Fin (d + 1)

abbrev Mi (d : ℕ) : Type := Fin (d + 1) ×ₗ Fin (d + 1)

def dj {d : ℕ} (j : Fin (d + 1)) : Fin d ↪o Mi d :=
  OrderEmbedding.ofStrictMono (fun l => toLex (j.succAbove l, j)) fun _ _ h =>
    Prod.Lex.left _ _ (Fin.strictMono_succAbove j h)

end Idx

structure Sys (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] where
  act : S →ₐ[ℂ] Module.End ℂ E
  X : Fin (d + 1) → Sˣ
  Y : Fin (d + 1) → Sˣ
  R : Finset (Fin (d + 1)) → Finset (Fin (d + 1)) → Subalgebra ℂ S
  M : Finset (Fin (d + 1)) → Finset (Fin (d + 1)) → Submodule ℂ E

namespace Sys
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  {κ : Type} [LinearOrder κ]

structure Good : Prop where
  monoR : ∀ I I' J J', I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' → T.R I J ≤ T.R I' J'
  monoM : ∀ I I' J J', I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' → T.M I J ≤ T.M I' J'
  stab : ∀ I J, I.Nonempty → J.Nonempty → Stab T.act (T.R I J) (T.M I J)
  memX : ∀ I J, J.Nonempty → ∀ i ∈ I, ∀ a, ((T.X a * (T.X i)⁻¹ : Sˣ) : S) ∈ T.R I J
  memY : ∀ I J, I.Nonempty → ∀ j ∈ J, ∀ a, ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) ∈ T.R I J

def u (n : κ → ℕ × ℕ) (i j : Fin (d + 1)) (l : κ) : Sˣ := T.X i ^ (n l).1 * T.Y j ^ (n l).2

def r (n : κ → ℕ × ℕ) (z : κ → S) (i j : Fin (d + 1)) (l : κ) : S := z l * ((T.u n i j l)⁻¹ : Sˣ)

def admitted (n : κ → ℕ × ℕ) (z : κ → S) : Prop := ∀ i j l, T.r n z i j l ∈ T.R {i} {j}

def colCx (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) : Cx ℂ (Finset κ → E) :=
  kosT T.act (T.M I J) (T.u n (pk I) (pk J)) z

def wt (z : κ → S) : Two d ⊕ₗ κ → Module.End ℂ E := fun t => Sum.elim (fun _ => 1) (fun l => T.act (z l)) (ofLex t)

def cx (n : κ → ℕ × ℕ) (z : κ → S) : Cx ℂ (Finset (Two d ⊕ₗ κ) → E) :=
  acx (fun s => mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s, T.u n (pk I) (pk J) l : Sˣ) : S))) (lft s)) (T.wt z)

def mix : Cx ℂ (Finset (Two d) → E) := acx (mixF T.M) fun _ => 1

def mu (l : Mi d) : S := T.X (ofLex l).1 * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1

def rowMu : Fin (d + 1) ⊕ₗ Mi d → Fin (d + 1) → S := fun t => Sum.elim (fun i => Pi.single i 1)
  (fun l m => (if m = (ofLex l).1 then (T.X m * T.Y (ofLex l).2 : S) else 0) -
    if m = (ofLex l).2 then (T.X m * T.Y (ofLex l).1 : S) else 0) (ofLex t)

def rowT : Fin (d + 1) ⊕ₗ Fin d → Fin (d + 1) → S := fun t => Sum.elim (fun i => Pi.single i 1)
  (fun l => Pi.single l.succ (T.X l.succ : S)) (ofLex t)

def mj (p : ℕ) (θ : Finset (Fin (d + 1) ⊕ₗ κ) → S) (b : Finset (Fin (d + 1)) → E) : Finset (Two d ⊕ₗ κ) → E := fun s =>
  ((-1 : ℤ) ^ ((p + 1) * (rgt s).card)) • T.act (θ (uni (lft (lft s)) (rgt s))) (b (rgt (lft s)))

end Sys

def n11 {κ : Type} : κ → ℕ × ℕ := fun _ => (1, 1)

def app {κ κ' A : Type} (f : κ → A) (g : κ' → A) : κ ⊕ₗ κ' → A := fun t => Sum.elim f g (ofLex t)

def rcup {d : ℕ} {κ E E' E'' : Type} [LinearOrder κ] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup E''] [Module ℂ E''] (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'') (p : ℕ) (c : Finset (Two d ⊕ₗ κ) → E)
    (x : Finset (Fin (d + 1)) → E') : Finset (Two d ⊕ₗ κ) → E'' := fun s =>
  ((-1 : ℤ) ^ (p * ((rgt (lft s)).card + (rgt s).card))) • ∑ i ∈ lft (lft s),
    μ (c (uni (uni ((lft (lft s)).filter (· ≤ i)) (rgt (lft s))) (rgt s))) (x ((lft (lft s)).filter (i ≤ ·)))

section Inst
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

abbrev xv : Fin (d + 1) → F := fun i => x i

def sysZ (a : ℕ) : Sys d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K) where
  act := actZ K
  X i := Units.map ((Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap F K) : F →+* K ⊗[ℂ] K) : F →* K ⊗[ℂ] K) (x i)
  Y i := Units.map (((Algebra.TensorProduct.includeRight : K →ₐ[ℂ] K ⊗[ℂ] K).toRingHom.comp (algebraMap F K) : F →+* K ⊗[ℂ] K) :
    F →* K ⊗[ℂ] K) (x i)
  R I J := (Algebra.TensorProduct.map (rB ℂ K (xv x) I).val (rB ℂ K (xv x) J).val).range
  M := MZ F K (xv x) a

def sysP (a : ℕ) : Sys d (F ⊗[ℂ] K) (F ⊗[ℂ] DR ℂ K) where
  act := (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ F) (Algebra.lsmul ℂ ℂ (DR ℂ K)))
  X i := Units.map ((Algebra.TensorProduct.includeLeftRingHom : F →+* F ⊗[ℂ] K) : F →* F ⊗[ℂ] K) (x i)
  Y i := Units.map (((Algebra.TensorProduct.includeRight : K →ₐ[ℂ] F ⊗[ℂ] K).toRingHom.comp (algebraMap F K) : F →+* F ⊗[ℂ] K) :
    F →* F ⊗[ℂ] K) (x i)
  R I J := (Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rB ℂ K (xv x) J).val).range
  M I J := Submodule.map₂ (TensorProduct.mk ℂ _ _) (omA ℂ (xv x) I) (omB ℂ K (rB ℂ K (xv x) J) a)

variable (F) in

def muP (τ : DR ℂ K →ₗ[K] K) : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K →ₗ[ℂ] F ⊗[ℂ] DR ℂ K :=
  LinearMap.flip (LinearMap.rTensorHom (DR ℂ K) ∘ₗ (LinearMap.mul ℂ (DR ℂ K)).flip.compr₂
    ((Algebra.trace F K).restrictScalars ℂ ∘ₗ τ.restrictScalars ℂ))

variable (F) in

def mulP : F ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  TensorProduct.lift ((Algebra.lsmul ℂ ℂ (DR ℂ K)).toLinearMap ∘ₗ (Algebra.linearMap F K).restrictScalars ℂ)

def Acts (τ : DR ℂ K →ₗ[K] K) (a : ℕ) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (c : K) : Prop :=
  ∀ w ∈ ⋀[K]^a Ω[K⁄ℂ], mulP F K (muP F K τ m w) = c • w

def kap (L : Finset (Mi d)) : K :=
  Algebra.TensorProduct.lmul' ℂ (detC (sysZ K x 0).rowMu (uni {0} L))

variable {K} {K' : Type} [Field K'] [Algebra ℂ K'] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
  [IsScalarTower ℂ F K']

def sysY (j2 : K →ₐ[ℂ] K') (a : ℕ) : Sys d K' (DR ℂ K') where
  act := Algebra.lsmul ℂ ℂ (DR ℂ K')
  X i := Units.map (algebraMap F K' : F →* K') (x i)
  Y i := Units.map ((j2.toRingHom.comp (algebraMap F K) : F →+* K') : F →* K') (x i)
  R := RY (xv x) j2
  M I J := omB ℂ K' (RY (xv x) j2 I J) a

def gS (j2 : K →ₐ[ℂ] K') : K ⊗[ℂ] K →ₐ[ℂ] K' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ K K') j2

end Inst

section Loc
variable {L : Type} [Field L] [Algebra ℂ L]

def loc (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) : Subalgebra ℂ L where
  carrier := {v | ∃ b : B, e b ≠ 0 ∧ (b : L) * v ∈ B}
  mul_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', by simp [hb, hb'], ?_⟩
    have := B.mul_mem h h'
    rwa [show (b : L) * v * (b' * v') = ((b * b' : B) : L) * (v * v') by push_cast; ring] at this
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', by simp [hb, hb'], ?_⟩
    have := B.add_mem (B.mul_mem b'.2 h) (B.mul_mem b.2 h')
    rwa [show (b' : L) * (b * v) + b * (b' * v') = ((b * b' : B) : L) * (v + v') by push_cast; ring] at this
  algebraMap_mem' c := ⟨1, by simp, by simpa using B.algebraMap_mem c⟩

variable {F : Type} [Field F] [Algebra ℂ F] [Algebra F L] {d : ℕ} (x : Fin (d + 1) → Fˣ)

variable (L) in

def tt (j : Fin d) : L := algebraMap F L ((x j.succ : F) / x 0)

variable (L) in

def dtS (S : Finset (Fin d)) : DR ℂ L :=
  ExteriorAlgebra.ιMulti L S.card fun a => D ℂ L (tt L x (S.orderEmbOfFin rfl a))

end Loc

end UpperTheory.Gal.productCup_of_system

end
end

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.WH
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

def WOk {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E] (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) : Prop :=
  (∀ i j, Commute (w i) (w j)) ∧ ∀ s i, i ∉ s → ∀ m ∈ A s, w i m ∈ A (insert i s)

def wOn {σ E : Type} [DecidableEq σ] [AddCommGroup E] [Module ℂ E] (Q : Finset σ) (w : σ → Module.End ℂ E) : σ → Module.End ℂ E :=
  fun i => if i ∈ Q then w i else 0

def Lev {σ E : Type} [DecidableEq σ] [Zero E] (Q : Finset σ) (P : ℤ → Prop) (c : Finset σ → E) : Prop :=
  ∀ s, ¬ P ((s ∩ Q).card : ℤ) → c s = 0

def QEx {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E] (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (Q : Finset σ) (d : ℤ) : Prop :=
  ∀ (n m : ℤ), m < d → ∀ c ∈ (acx A w).C n, Lev Q (· = m) c → wd (wOn Q w) c = 0 →
    ∃ y ∈ (acx A w).C (n - 1), Lev Q (· = m - 1) y ∧ wd (wOn Q w) y = c

def colA {β κ E : Type} [LinearOrder β] [LinearOrder κ] [AddCommGroup E] [Module ℂ E] (A : Finset (β ⊕ₗ κ) → Submodule ℂ E)
    (w : β ⊕ₗ κ → Module.End ℂ E) (b : Finset β) : Cx ℂ (Finset κ → E) := acx (fun L => A (uni b L)) fun l => w (inrE l)

def InSp {S κ : Type} [CommRing S] [Algebra ℂ S] [Fintype κ] (R : Subalgebra ℂ S) (r : κ → S) (g : S) : Prop :=
  ∃ a : κ → S, (∀ l, a l ∈ R) ∧ g = ∑ l, a l * r l

def WdBasic : Prop := ∀ (σ E : Type) [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E] (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E),
  ((∀ i j, Commute (w i) (w j)) → ∀ c, wd w (wd w c) = 0) ∧ (WOk A w → (acx A w).IsCx) ∧
  (∀ w' : σ → Module.End ℂ E, wd (w + w') = wd w + wd w') ∧
  (∀ w' : σ → Module.End ℂ E, (∀ i j, Commute (w i) (w' j)) → (∀ i, w i = 0 ∨ w' i = 0) →
    ∀ c, wd w (wd w' c) + wd w' (wd w c) = 0) ∧
  (∀ c, wd (fun _ : σ => (1 : Module.End ℂ E)) c = deltaL ℂ σ E c) ∧
  ∀ (σ' : Type) [LinearOrder σ'] (e : σ' ↪o σ) (c : Finset σ → E) (s : Finset σ'),
    wd (fun i => w (e i)) (fun t => c (t.map e.toEmbedding)) s = wd w c (s.map e.toEmbedding)

def WdUni : Prop := ∀ (β κ E : Type) [LinearOrder β] [LinearOrder κ] [AddCommGroup E] [Module ℂ E]
  (w : β ⊕ₗ κ → Module.End ℂ E) (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ),
  wd w c (uni b L) = wd (fun i => w (inlE i)) (fun b' => c (uni b' L)) b +
      ((-1 : ℤ) ^ b.card) • wd (fun l => w (inrE l)) (fun L' => c (uni b L')) L ∧
    lft (uni b L) = b ∧ rgt (uni b L) = L ∧ (uni b L).card = b.card + L.card ∧ ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s

def Det : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] (p : ℕ) (ρ : κ → Fin p → S) (f : Fin p → S) (m : E),
  wd (fun l => act (∑ b, ρ l b * f b)) (fun s => act (detC ρ s) m) = 0

def Htpy : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S), Stab act R M →
  ∀ (n : ℤ), ∀ c ∈ (kos act M r).Z n, ∀ g, InSp R r g → (fun L => act g (c L)) ∈ (kos act M r).B n

def KoszulExactBelowLengthOfWeaklyRegular : Prop := ∀ (d : ℕ) (R N : Type) [CommRing R] [Algebra ℂ R] [AddCommGroup N] [Module R N] [Module ℂ N]
  [IsScalarTower ℂ R N] (κ : Type) [LinearOrder κ] [Fintype κ] (r : κ → R) (f : List R), f.length = d → RingTheory.Sequence.IsWeaklyRegular N f →
  (∀ g ∈ f, InSp ⊤ r g) → KE (kos (Algebra.lsmul ℂ ℂ N) ⊤ r) d

def K1 : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S) (d : ℕ) (f : Fin d → S),
  Stab act R M → (∀ l, r l ∈ R) → Reg act M f → (∀ j, InSp R r (f j)) → KE (kos act M r) d

def RS : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (M : Submodule ℂ E) (u : κ → Sˣ) (r z : κ → S), (∀ l, r l = z l * ((u l)⁻¹ : Sˣ)) →
  ∀ (n : ℤ) (c : Finset κ → E), (c ∈ (kosT act M u z).C n ↔ unsc act u c ∈ (kos act M r).C n) ∧
    (c ∈ (kosT act M u z).Z n ↔ unsc act u c ∈ (kos act M r).Z n) ∧ (c ∈ (kosT act M u z).B n ↔ unsc act u c ∈ (kos act M r).B n) ∧
    unsc act u⁻¹ (unsc act u c) = c ∧ unsc act u (unsc act u⁻¹ c) = c

def FiltrationBoundaryCriterion : Prop := ∀ (σ E : Type) [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E] (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (Q : Finset σ) (d n : ℤ), WOk A w → QEx A w Q d → ∀ c ∈ (acx A w).Z n, Lev Q (· ≤ d) c →
  (∃ y ∈ (acx A w).C (n - 1), Lev Q (· = d - 1) y ∧ ∀ s, ((s ∩ Q).card : ℤ) = d → wd (wOn Q w) y s = c s) → c ∈ (acx A w).B n

def FiltrationCocycleLiftCriterion : Prop := ∀ (σ E : Type) [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E] (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (Q : Finset σ) (d n : ℤ), WOk A w → QEx A w Q d → ∀ c0 ∈ (acx A w).C n, Lev Q (· = d) c0 →
  wd (wOn Q w) c0 = 0 → (∃ y ∈ (acx A w).C n, Lev Q (· = d - 1) y ∧ wd (wOn Q w) y = wd (wOn Qᶜ w) c0) →
  ∃ c ∈ (acx A w).Z n, Lev Q (· < d) (c - c0)

def ColQEx : Prop := ∀ (β κ E : Type) [LinearOrder β] [Fintype β] [LinearOrder κ] [Fintype κ] [AddCommGroup E] [Module ℂ E]
  (A : Finset (β ⊕ₗ κ) → Submodule ℂ E) (w : β ⊕ₗ κ → Module.End ℂ E) (d : ℤ), (∀ b, KE (colA A w b) d) → QEx A w (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) d

def L1 : Prop := ∀ (β κ E : Type) [LinearOrder β] [Fintype β] [LinearOrder κ] [Fintype κ] [AddCommGroup E] [Module ℂ E]
  (A : Finset (β ⊕ₗ κ) → Submodule ℂ E) (w : β ⊕ₗ κ → Module.End ℂ E) (d n : ℤ), WOk A w → (∀ b, KE (colA A w b) d) → ∀ c ∈ (acx A w).Z n,
  (∀ b L, d < (L.card : ℤ) → c (uni b L) = 0) → (∀ b, (b.card : ℤ) = n - d → col c b ∈ (colA A w b).B d) → c ∈ (acx A w).B n

def L2 : Prop := ∀ (β κ E : Type) [LinearOrder β] [Fintype β] [LinearOrder κ] [Fintype κ] [AddCommGroup E] [Module ℂ E]
  (A : Finset (β ⊕ₗ κ) → Submodule ℂ E) (w : β ⊕ₗ κ → Module.End ℂ E) (d n : ℤ), WOk A w → (∀ b, KE (colA A w b) d) → ∀ c0 : Finset β → Finset κ → E,
  (∀ b, (b.card : ℤ) = n - d → c0 b ∈ (colA A w b).Z d) →
  (∀ b, (b.card : ℤ) = n - d + 1 → (fun L => wd (fun i => w (inlE i)) (fun b' => c0 b' L) b) ∈ (colA A w b).B d) →
  ∃ c ∈ (acx A w).Z n, (∀ b, (b.card : ℤ) = n - d → col c b = c0 b) ∧ ∀ b L, d < (L.card : ℤ) → c (uni b L) = 0

def SubQEx : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (M : Submodule ℂ E) (r : κ → S) (d : ℕ) (e : Fin d ↪o κ),
  KE (kos act M fun j => r (e j)) d → QEx (fun _ => M) (fun l => act (r l)) (img e) d

def KoszulBoundaryOfComponentMemIdeal : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S) (d : ℕ) (e : Fin d ↪o κ),
  Stab act R M → (∀ l, r l ∈ R) → KE (kos act M fun j => r (e j)) d → ∀ c ∈ (kos act M r).Z d,
  c (img e) ∈ sm act M (Set.range fun j => r (e j)) → c ∈ (kos act M r).B d

def KoszulCocycleExistsWithPrescribedComponent : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S) (d : ℕ) (e : Fin d ↪o κ),
  Stab act R M → (∀ l, r l ∈ R) → KE (kos act M fun j => r (e j)) d → ∀ m ∈ M,
  (∀ l, act (r l) m ∈ sm act M (Set.range fun j => r (e j))) → ∃ c ∈ (kos act M r).Z d, c (img e) = m

def KSub : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S), Stab act R M → (∀ l, r l ∈ R) →
  (∀ (d : ℕ) (e : Fin d ↪o κ), KE (kos act M fun j => r (e j)) d → KE (kos act M r) d) ∧
  ∀ n : ℤ, ∀ c ∈ (kos act M r).B n, ∀ L, c L ∈ sm act M (Set.range r)

def K3 : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S) (d : ℕ) (e e' : Fin d ↪o κ)
  (N : Matrix (Fin d) (Fin d) S), Stab act R M → (∀ l, r l ∈ R) → (∀ a j, N a j ∈ R) → (∀ a, r (e' a) = ∑ j, N a j * r (e j)) →
  (∀ a j, e' a ≠ e j) →
  KE (kos act M fun j => r (e j)) d → ∀ c ∈ (kos act M r).Z d,
  c (img e') - act N.det (c (img e)) ∈ sm act M (Set.range fun j => r (e j))

def LocD : Prop := ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [LinearOrder κ] [Fintype κ] (R : Subalgebra ℂ S) (M M' : Submodule ℂ E) (r : κ → S) (v : Sˣ) (a b : S) (l0 : κ) (d : ℤ),
  Stab act R M → (∀ l, r l ∈ R) → a ∈ R → b ∈ R → r l0 = 1 - a * b → M ≤ M' → (∀ m ∈ M', ∃ N : ℕ, act (a ^ N) m ∈ M) →
  (∀ m ∈ M', act v m ∈ M' ∧ act (v⁻¹ : Sˣ) m ∈ M') →
  (KE (kos act M' fun l => r l * v) d → KE (kos act M r) d) ∧
  ∀ m ∈ M, m ∈ sm act M' (Set.range fun l => r l * v) → m ∈ sm act M (Set.range r)

def SysOk : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S), T.Good → T.admitted n z →
  WOk (fun s : Finset (Two d ⊕ₗ κ) =>
    mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s, T.u n (pk I) (pk J) l : Sˣ) : S))) (lft s)) (T.wt z) ∧
  (∀ I J, ∀ i ∈ I, ∀ j ∈ J, (∀ l, T.r n z i j l ∈ T.R I J) ∧ T.colCx n z I J = kosT T.act (T.M I J) (T.u n i j) z) ∧
  ∀ I I' J J', I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' → ∀ m, (T.colCx n z I J).Z m ≤ (T.colCx n z I' J').Z m

def CechKoszulSystemBoundaryCriterion : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S) (N : ℤ), T.Good → T.admitted n z →
  (∀ I J, I.Nonempty → J.Nonempty → KE (T.colCx n z I J) d) → ∀ c ∈ (T.cx n z).Z N,
  (∀ b L, d < L.card → c (uni b L) = 0) →
  (∀ I J, I.Nonempty → J.Nonempty → ((I.card + J.card : ℕ) : ℤ) = N - d → col c (uni I J) ∈ (T.colCx n z I J).B d) →
  c ∈ (T.cx n z).B N

def CechKoszulSystemCocycleGluing : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S), T.Good → T.admitted n z →
  (∀ I J, I.Nonempty → J.Nonempty → KE (T.colCx n z I J) d) → ∀ c0 : Fin (d + 1) → Fin (d + 1) → Finset κ → E,
  (∀ i j, c0 i j ∈ (T.colCx n z {i} {j}).Z d) → (∀ i i' j, c0 i j - c0 i' j ∈ (T.colCx n z {i, i'} {j}).B d) →
  (∀ i j j', c0 i j - c0 i j' ∈ (T.colCx n z {i} {j, j'}).B d) →
  ∃ c ∈ (T.cx n z).Z (d + 2), ∀ i j, col c (uni {i} {j}) = c0 i j

def SysBasic : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S) (N : ℤ),
  (∀ c ∈ (T.cx n z).C N, ∀ I J L, (I = ∅ ∨ J = ∅ ∨ ((I.card + J.card + L.card : ℕ) : ℤ) ≠ N) → c (uni (uni I J) L) = 0) ∧
  (∀ c, c ∈ (T.cx n z).C N ↔ ∀ I J, col c (uni I J) ∈ (if I.Nonempty ∧ J.Nonempty then (T.colCx n z I J).C (N - I.card - J.card)
    else ⊥)) ∧
  (∀ c ∈ (T.cx n z).Z N, top c ∈ T.mix.Z N) ∧ (∀ c ∈ (T.cx n z).B N, top c ∈ T.mix.B N) ∧
  (∀ c ∈ (T.cx n z).Z N, ∀ I J, I.Nonempty → J.Nonempty → (∀ I' J' L, I'.card + J'.card < I.card + J.card →
    c (uni (uni I' J') L) = 0) → col c (uni I J) ∈ (T.colCx n z I J).Z (N - I.card - J.card)) ∧
  ∀ (κ' : Type) [LinearOrder κ'] [Fintype κ'] (e : κ' ↪o κ), ∀ c ∈ (T.cx n z).Z N,
    resK e c ∈ (T.cx (fun l => n (e l)) fun l => z (e l)).Z N

def MJ : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (κ : Type) [LinearOrder κ] [Fintype κ] (z : κ → S) (p : ℕ) (θ : Finset (Fin (d + 1) ⊕ₗ κ) → S) (b : Finset (Fin (d + 1)) → E),
  wd (fun t => (Algebra.lmul ℂ S) (app (fun _ => 1) z t)) θ = 0 → deltaL ℂ _ _ b = 0 → (∀ J, J.card ≠ p + 1 → b J = 0) →
  wd (T.wt z) (T.mj p θ b) = 0

def RCup : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (S' E' E'' : Type) [CommRing S'] [Algebra ℂ S'] [AddCommGroup E'] [Module ℂ E'] [AddCommGroup E'']
  [Module ℂ E''] (T' : Sys d S' E'') (κ : Type) [LinearOrder κ] [Fintype κ] (z : κ → S) (z' : κ → S') (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'') (p : ℕ)
  (c : Finset (Two d ⊕ₗ κ) → E) (x : Finset (Fin (d + 1)) → E'), (∀ l m y, μ (T.act (z l) m) y = T'.act (z' l) (μ m y)) →
  wd (T.wt z) c = 0 → (∀ J L, c (uni (uni ∅ J) L) = 0) → deltaL ℂ _ _ x = 0 → (∀ I, I.card ≠ p + 1 → x I = 0) →
  wd (T'.wt z') (rcup μ p c x) = 0

def ThMu : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E),
  wd (fun t => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu t)) (detC T.rowMu) = 0 ∧ (∀ L, detC T.rowMu (uni ∅ L) = 0) ∧
  detC T.rowMu (uni Finset.univ ∅) = 1 ∧
  detC T.rowMu (uni {0} (img (dj 0))) = (∏ l : Fin d, (T.X l.succ : S)) * (T.Y 0 : S) ^ d

def ThMuLat : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E), T.Good → T.admitted n11 T.mu ∧ ∀ I J L, I.Nonempty → ∀ j ∈ J, ∃ s ∈ T.R I J,
  detC T.rowMu (uni I L) = s * (∏ m ∈ Iᶜ, (T.X m : S)) * (T.Y j : S) ^ L.card

def ThT : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E),
  wd (fun t => (Algebra.lmul ℂ S) (app (fun _ => 1) (fun l : Fin d => (T.X l.succ : S)) t)) (detC T.rowT) = 0 ∧
  detC T.rowT (uni Finset.univ ∅) = 1 ∧ detC T.rowT (uni {0} Finset.univ) = ∏ l : Fin d, (T.X l.succ : S) ∧
  ∀ I L, detC T.rowT (uni I L) = 0 ∨ (0 ∈ I ∧ I.card + L.card = d + 1 ∧ ∃ ε : ℤˣ, detC T.rowT (uni I L) = ε • ∏ m ∈ Iᶜ, (T.X m : S))

def MuSpan : Prop := ∀ (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E), T.Good → ∀ I J, ∀ i ∈ I, ∀ j ∈ J, ∀ l,
  InSp (T.R I J) (fun a => T.r n11 T.mu i j (dj j a)) (T.r n11 T.mu i j l)

def EdgeRel : Prop := ∀ (ι E : Type) [LinearOrder ι] [Fintype ι] [AddCommGroup E] [Module ℂ E] (G : Finset ι → Submodule ℂ E) (p : ℕ),
  (∀ s t, s.Nonempty → s ⊆ t → G s ≤ G t) → ∀ α ∈ (cech G).Z p,
  edge2 α - ((-1 : ℤ) ^ p) • edge1 α ∈ (acx (mixF fun I J : Finset ι => G (I ∪ J)) fun _ => 1).B (p + 2)

def KunDec : Prop := ∀ (ι E E' : Type) [LinearOrder ι] [Fintype ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  (A : Finset ι → Submodule ℂ E) (B : Finset ι → Submodule ℂ E') (d : ℕ), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) →
  (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) →
  ∀ t ∈ (acx (mixF fun I J => Submodule.map₂ (TensorProduct.mk ℂ E E') (A I) (B J)) fun _ => 1).Z (d + 2),
  ∃ (m : ℕ) (p : Fin m → ℕ) (a : Fin m → Finset ι → E) (b : Fin m → Finset ι → E'),
    (∀ k, p k ≤ d ∧ a k ∈ (cech A).Z (d - p k) ∧ b k ∈ (cech B).Z (p k)) ∧
    t - ∑ k, join (TensorProduct.mk ℂ E E') (a k) (b k) ∈
      (acx (mixF fun I J => Submodule.map₂ (TensorProduct.mk ℂ E E') (A I) (B J)) fun _ => 1).B (d + 2)

def TrLin : Prop := ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (φ : ι → V →ₗ[ℂ] ℂ) (v : ι → V),
  (∀ y, y = ∑ k, φ k y • v k) → FiniteDimensional ℂ V ∧ ∀ u : V →ₗ[ℂ] V, LinearMap.trace ℂ V u = ∑ k, φ k (u (v k))

def LCupRel : Prop := ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (E E' E'' : Type) [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] [AddCommGroup E''] [Module ℂ E''] (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'')
  (A : Finset ι → Submodule ℂ E) (G : Finset (ι ⊕ₗ ι) → Submodule ℂ E') (H : Finset ι → Finset ι → Submodule ℂ E'') (q p : ℕ),
  (∀ I J I' s, J.Nonempty → I'.Nonempty → s.Nonempty → I' ⊆ I → s ⊆ uni I J → ∀ y ∈ A I', ∀ y' ∈ G s, μ y y' ∈ H I J) →
  ∀ a ∈ (cech A).Z q, ∀ γ ∈ (cech G).Z p,
  join μ a (fun J => γ (uni ∅ J)) - ((-1 : ℤ) ^ p) • edge1 (cupE μ a fun I => γ (uni I ∅)) ∈
    (acx (mixF H) fun _ => 1).B (q + p + 2) ∧ deltaL ℂ _ _ (cupE μ a fun I => γ (uni I ∅)) = 0

def EdgeInj : Prop := ∀ (ι E : Type) [LinearOrder ι] [Fintype ι] [AddCommGroup E] [Module ℂ E]
  (G : Finset (ι ⊕ₗ ι) → Submodule ℂ E) (d : ℕ), ∀ x ∈ (cech fun I => G (uni I ∅)).Z d,
  edge1 x ∈ (acx (mixF fun I J => G (uni I J)) fun _ => 1).B (d + 2) →
  ∃ γ ∈ (cech G).Z d, (∀ J, γ (uni ∅ J) = 0) ∧ ∀ I, γ (uni I ∅) = x I

end UpperTheory.Gal.productCup_of_system

end
end
