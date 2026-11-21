import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Pairings

variable {S : Scheme.{0}} {A B G G' : Over S} [GrpObj A] [GrpObj B] [GrpObj G] [GrpObj G']

def lamPull (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) : LB (A ⊗ B).left :=
  cubeLB G ![fst A B ≫ f₁, snd A B ≫ f₂] L

def LamEq (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') : Prop :=
  LBIso (lamPull L f₁ f₂) (lamPull L' g₁ g₂)

def WeilEqAt (k : ℕ) (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') :
    Prop :=
  ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B), x ^ k = 1 → y ^ k = 1 → ∀ c : Γ(T.left, ⊤)ˣ,
    Out.WeilIs G L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs G' L' k (x ≫ g₁) (y ≫ g₂) c

def WeilEq (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') : Prop :=
  ∀ k : ℕ, 0 < k → WeilEqAt k L f₁ f₂ L' g₁ g₂

end Pairings

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Zw (H : Host E) : Subalgebra ℤ (𝓞 E) := Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))

def wz (H : Host E) : Zw H := ⟨H.w0, Algebra.self_mem_adjoin_singleton ℤ H.w0⟩

structure CMCurve (H : Host E) (R : Type) [CommRing R] (ω : R) where

  P : Out.PolAV (Sp R)
  dim : P.g = 1

  act : OAct (Zw H) P.A

  v : epsR R ⟶ P.A
  basis : IsLieBasis (G := P.A) ![v]
  eigen : (v ≫ act.act (wz H)).left = spMap (epsScaleR ω) ≫ v.left

variable {H : Host E}

structure IsPrincipal {S : Scheme.{0}} (t : SAB H S) : Prop where
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L

def SigAt (H : Host E) (p q : ℕ) {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G)
    {k : Type} [Field k] (x : Sp k ⟶ S) (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → LieMult act x τ p) ∧ (τ H.rt ≠ ρ → LieMult act x τ q)

def HasSig (H : Host E) (p q : ℕ) {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (act : OAct (𝓞 E) G)
    (ρ : R) : Prop :=
  ρ ^ 2 = -(H.d : R) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k), SigAt H p q act (spMap β) (β ρ)

def herm (D : Datum H) (x y : D.La) : Zw H :=
  ((D.EF (H.w0 • x) y - D.EF x y : ℤ) : Zw H) + ((D.EF x y : ℤ) : Zw H) * wz H

open Classical in

def posSign (D : Datum H) : ℤˣ := if (0 < H.rt0.im ↔ D.q = 0) then 1 else -1

structure IsTensorMap {R : Type} [CommRing R] {ω : R} (C : CMCurve H R ω) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (h : La → La → Zw H) (t : SAB H (Sp R)) (φ : La → (C.P.A ⟶ t.G)) : Prop where
  hom : ∀ x, IsMonHom (φ x)
  add : ∀ x y, φ (x + y) = φ x * φ y
  lin : ∀ (a : 𝓞 E) x, φ (a • x) = φ x ≫ t.act.act a
  bal : ∀ (b : Zw H) x, φ ((b : 𝓞 E) • x) = C.act.act b ≫ φ x

  onto : ∀ (T : Over (Sp R)) (y : T ⟶ t.G), ∃ (n : ℕ) (x : Fin n → La) (c : Fin n → (T ⟶ C.P.A)),
    y = (List.ofFn fun i => c i ≫ φ (x i)).prod

  inj : ∀ (T : Over (Sp R)) (n : ℕ) (x : Fin n → La) (c : Fin n → (T ⟶ C.P.A)),
    (List.ofFn fun i => c i ≫ φ (x i)).prod = 1 →
      ∀ ℓ : La →ₗ[Zw H] Zw H, (List.ofFn fun i => c i ≫ C.act.act (ℓ (x i))).prod = 1

  pol : ∀ x y, LamEq t.PP.L (φ x) (φ y) C.P.L (C.act.act (h x y)) (𝟙 C.P.A)

example (D : Datum H) {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {k : Type} [Field k]
    (x : Sp k ⟶ S) (ρ : k) : SigAt H D.p D.q act x ρ ↔ DetCond D act x ρ := Iff.rfl

example (D : Datum H) (x : D.La) : herm D x x = ((D.EF (H.w0 • x) x : ℤ) : Zw H) := by
  simp [herm, D.alt]

theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have hr : H.bar H.rt = -H.rt := by
    have h2 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h3 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [← H.bar_eq, h] at h3
      have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
      have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun a : 𝓞 E => φ (a : E)) H.rt_sq
        simpa using this
      have h5 := congrArg Complex.re h4
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      simp [sq, him] at h5
      nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
    · exact h
  have h2 : (2 : 𝓞 E) * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [hr, sub_eq_add_neg, map_ofNat] using this
  have : (2 : 𝓞 E) * (H.bar H.w0 - (1 - H.w0)) = 0 := by linear_combination h2 + H.two_weight_eq_one_add_root
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left two_ne_zero)

end GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms
end
end

section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} [Field K] [NumberField K]

structure GenFib (t : SAB H (Sp (𝓞 K))) where

  tK : SAB H (Sp K)

  m : SABMap tK t (spMap (algebraMap (𝓞 K) K))

  g : ℕ

  v : Fin g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v

namespace GenFib

variable {t t' : SAB H (Sp (𝓞 K))} (F : GenFib t) (F' : GenFib t')

def IsVec (c : Fin F.g → K) (x : Sp (DualNumber K) ⟶ t.G.left) : Prop :=
  ∃ w : epsR K ⟶ F.tK.G, IsLieComb c F.v w ∧ x = w.left ≫ F.m.φ

def IsIntegralVec (c : Fin F.g → K) : Prop :=
  ∃ w : epsR (𝓞 K) ⟶ t.G, IsTangent w ∧ F.IsVec c (spMap (Chart.dualMapR (algebraMap (𝓞 K) K)) ≫ w.left)

def lieLat : Submodule (𝓞 K) (Fin F.g → K) := Submodule.span (𝓞 K) {c | F.IsIntegralVec c}

def IsDiff (f : t.G ⟶ t'.G) (D : (Fin F.g → K) →ₗ[K] (Fin F'.g → K)) : Prop :=
  ∀ c x, F.IsVec c x → F'.IsVec (D c) (x ≫ f.left)

def IsEigenVec (τ : E →+* K) (c : Fin F.g → K) : Prop :=
  ∀ (a : 𝓞 E) x, F.IsVec c x → F.IsVec (τ (a : E) • c) (x ≫ (t.act.act a).left)

def eigenSp (τ : E →+* K) : Submodule K (Fin F.g → K) := Submodule.span K {c | F.IsEigenVec τ c}

def eigenLat (τ : E →+* K) : Submodule (𝓞 K) (Fin F.g → K) :=
  F.lieLat ⊓ (F.eigenSp τ).restrictScalars (𝓞 K)

structure CxFib (σ : K →+* ℂ) where

  A : Over (Sp ℂ)
  [grp : GrpObj A]

  φ : A.left ⟶ F.tK.G.left
  cart : IsGrpPullback A F.tK.G (spMap σ) φ

  u : HolUnif A (F.tK.PP.L.pull φ) F.g

  Hm : Matrix (Fin F.g) (Fin F.g) ℂ

  χ : u.Λ → ℂ
  ah : u.IsAH Hm χ

  vC : Fin F.g → (epsR ℂ ⟶ A)
  vC_base : ∀ i, (vC i).left ≫ φ = spMap (Chart.dualMapR σ) ≫ (F.v i).left

  W : Fin F.g → (Fin F.g → ℂ)
  diff : ∀ i, u.IsDiff (W i) (vC i)

attribute [instance] CxFib.grp

variable {F} in

def CxFib.vec {σ : K →+* ℂ} (C : F.CxFib σ) (c : Fin F.g → K) : Fin F.g → ℂ := ∑ i, σ (c i) • C.W i

variable {F} in

def CxFib.piH {σ : K →+* ℂ} (C : F.CxFib σ) (x y : Fin F.g → K) : ℂ :=
  (Real.pi : ℂ) * hermForm C.Hm (C.vec x) (C.vec y)

end GenFib

section Sum

variable {S : Scheme.{0}}

def sumPow {A B : Over S} [GrpObj B] {n : ℕ} (f : Fin n → (A ⟶ B)) : (∏ᶜ fun _ : Fin n => A) ⟶ B :=
  (List.ofFn fun i => Pi.π (fun _ : Fin n => A) i ≫ f i).prod

def sumMap {A A' B : Over S} [GrpObj B] {p q : ℕ} (f : Fin p → (A ⟶ B)) (f' : Fin q → (A' ⟶ B)) :
    (∏ᶜ fun _ : Fin p => A) ⊗ (∏ᶜ fun _ : Fin q => A') ⟶ B :=
  (fst _ _ ≫ sumPow f) * (snd _ _ ≫ sumPow f')

def IsFinFlatSurj {X Y : Over S} (f : X ⟶ Y) : Prop := IsFinite f.left ∧ Flat f.left ∧ Surjective f.left

def IsLinHom {t t' : SAB H S} (f : t.G ⟶ t'.G) : Prop :=
  IsMonHom f ∧ ∀ a : 𝓞 E, t.act.act a ≫ f = f ≫ t'.act.act a

def PolId {t t' : SAB H S} (f : t.G ⟶ t'.G) (h : 𝓞 E) : Prop :=
  WeilEq t'.PP.L f f t.PP.L (t.act.act h) (𝟙 t.G)

end Sum

structure CMObj (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (p q : ℕ) where

  A : SAB H (Sp (𝓞 K))

  A' : SAB H (Sp (𝓞 K))

  B : SAB H (Sp (𝓞 K))
  prinA : IsPrincipal A
  prinA' : IsPrincipal A'
  prinB : IsPrincipal B
  sigA : HasSig H 1 0 A.act ρ
  sigA' : HasSig H 0 1 A'.act ρ
  sigB : HasSig H p q B.act ρ

  ph : Fin p → (A.G ⟶ B.G)

  ph' : Fin q → (A'.G ⟶ B.G)
  lin : ∀ i, IsLinHom (ph i)
  lin' : ∀ j, IsLinHom (ph' j)
  isog : IsFinFlatSurj (sumMap ph ph')

  h : Fin p → 𝓞 E

  h' : Fin q → 𝓞 E
  pol : ∀ i, PolId (ph i) (h i)
  pol' : ∀ j, PolId (ph' j) (h' j)

namespace CMObj

variable {ρ : 𝓞 K} {p q : ℕ} (X : CMObj H K ρ p q)

def line (F : GenFib X.A) (τ : E →+* K) : Submodule (𝓞 K) (Fin F.g → K) := F.eigenLat τ

def Bdd (La : ℝ) : Prop :=
  ∀ τ : E →+* ℂ, (∀ i, ‖τ (X.h i : E)‖ ≤ La ^ 2) ∧ ∀ j, ‖τ (X.h' j : E)‖ ≤ La ^ 2

end CMObj

def SplitsE (E K : Type) [Field E] [NumberField E] [Field K] : Prop := Nat.card (E →+* K) = Module.finrank ℚ E

example {t : SAB H (Sp (𝓞 K))} (F : GenFib t) : F.IsDiff F (𝟙 t.G) LinearMap.id := by
  intro c x hx
  simpa using hx

example {t t' t'' : SAB H (Sp (𝓞 K))} (F : GenFib t) (F' : GenFib t') (F'' : GenFib t'') (f : t.G ⟶ t'.G)
    (f' : t'.G ⟶ t''.G) (D D') (h : F.IsDiff F' f D) (h' : F'.IsDiff F'' f' D') :
    F.IsDiff F'' (f ≫ f') (D' ∘ₗ D) := by
  intro c x hx
  simpa using h' _ _ (h c x hx)

example {S : Scheme.{0}} (t : SAB H S) : IsLinHom (𝟙 t.G) ∧ PolId (𝟙 t.G) 1 := by
  refine ⟨⟨inferInstance, by simp⟩, ?_⟩
  intro k _ T x y _ _ c
  rw [t.act.one]

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres
end
end
