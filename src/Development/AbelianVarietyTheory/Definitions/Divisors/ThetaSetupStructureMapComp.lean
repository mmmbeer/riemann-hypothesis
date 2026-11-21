import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

section
noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.Poinc

structure FPre {O : Type} [CommRing O] (bar : O → O) (q p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsLocalRing A] where

  Y : Type

  ev : Y → A →+* PadicAlgCl p
  ev_le : ∀ y h, ‖ev y h‖ ≤ 1
  ev_lt : ∀ y, ∀ h ∈ maximalIdeal A, ‖ev y h‖ < 1

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  β : ∀ y, LinearMap.BilinForm ℤ (X y)
  bal : ∀ y, β y ∈ balForms bar (X y)
  pos : ∀ y x, x ≠ 0 → 0 < β y x x

  sc : Y → ℝ
  sc_pos : ∀ y, 0 < sc y

attribute [instance] FPre.add FPre.mod FPre.fin FPre.proj FPre.freeZ FPre.finZ

namespace FPre

variable {O : Type} [CommRing O] {bar : O → O} {q p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : FPre bar q p A) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)

def abelian₂ : Prop :=
  ∃ C : ℝ, ∀ y x, x ≠ 0 → ∃ h ∈ maximalIdeal A, Real.exp (-(C * (Φ.sc y * Φ.β y x x))) ≤ ‖Φ.ev y h‖

def IsTerms {Q : Type} (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) : Prop :=
  (∀ y μ c, ‖t y μ c‖ ≤ Real.exp (-(Φ.sc y * qW W (Φ.β y) μ))) ∧
    ∀ y μ, ∃ c, ‖t y μ c‖ = Real.exp (-(Φ.sc y * qW W (Φ.β y) μ))

def OrbitSums (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) {Q : Type}
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) : Prop :=
  ∀ (m : ℕ) (a : Fin m × Fin s → Φ.X y₀) (c : Fin m → Q) (e : ℕ), ∃ f : A, ∀ y,
    ∃ h ∈ maximalIdeal A, ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Fin m × Fin s → Φ.X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
      (∀ μ ∈ orbit O N₁ N (k y) a, μ ∉ S → Real.exp (-(Φ.sc y * ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ))) < ε) ∧
      ‖Φ.ev y f - ∑ μ ∈ S, ∏ i, t y (fun u => μ (i, u)) (c i)‖ ≤ max ε (‖Φ.ev y h‖ ^ e)

def Four (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type)
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod O N (k y)) ∧ Φ.IsTerms W t ∧
      Φ.OrbitSums W N₁ N y₀ k t

def Approx (φ : InvFun O) (d : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (e : ℕ), ∃ f : A, ‖Φ.ev y₀ f‖ = Real.exp (-(Φ.sc y₀ * (d * φ.evalZ (Φ.β y₀)))) ∧
    ∀ y, ‖Φ.ev y f‖ ≤ Real.exp (-(Φ.sc y * (d * φ.evalZ (Φ.β y)))) ∨ ∃ h ∈ maximalIdeal A, ‖Φ.ev y f‖ ≤ ‖Φ.ev y h‖ ^ e

def ClassSums (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) {Q : Type}
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) (B : Type) [CommRing B] [Algebra A B] (𝔷 : Ideal B) : Prop :=
  ∃ (ev' : Φ.Y → B →+* PadicAlgCl p) (f : (Fin s → Φ.X y₀) → Q → B),
    (∀ y a, ev' y (algebraMap A B a) = Φ.ev y a) ∧ (∀ y b, ‖ev' y b‖ ≤ 1) ∧ (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) ∧
    (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧
    (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin s → Φ.X y), ∀ S : Finset (Fin s → Φ.X y),
      (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) →
        ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧
    ∀ σ : B ≃ₐ[A] B, 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (c : O) x, CongMod N (γ (c • x)) (c • γ x)) ∧
      (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod N₁ (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ

end FPre

end GlobalTheory.Poinc
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc

variable {g n : ℕ}

structure Setup (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {Z : Scheme.{0}} (i : F.X ⟶ Z) where

  o₁ : Type

  Ω₁ : Type
  [ring : CommRing o₁]
  [field : Field Ω₁]
  [alg : Algebra o₁ Ω₁]
  [ar : ArithBase o₁ Ω₁]

  S : ThetaSys o₁ Ω₁

  ρ : S.Real
  big : S.Big

  u : Sp S.R ⟶ F.X
  sharp : SharpOver F W ρ.P u
  gen : ∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X

  M : RatModel o₁ Ω₁
  normal : IsNormalScheme M.Z

  π : M.Z ⟶ Z
  fin : IsFinite π
  comp : M.pt ≫ π = spMap S.R.val.toRingHom ≫ u ≫ i

  one_le : 1 ≤ g

  three_le : 3 ≤ n

  odd : Odd n

  z : Z ⟶ Sp (cycAway n)

  proj : IsProjOver z

  normalZ : IsNormalScheme Z

  imm : IsOpenImmersion i

  thetaSetup_structureMap_comp : i ≫ z = F.s

  dense : Dense (Set.range i)

  e8 : IsE8 W

  thetaInt : ThetaInt F W i

  κ : cycAway n →+* o₁

  base : spMap S.R.val.toRingHom ≫ u ≫ F.s = spMap ((algebraMap o₁ Ω₁).comp κ)

attribute [instance] Setup.ring Setup.field Setup.alg Setup.ar

structure CTrait {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i)
    (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) where

  y : Sp (OO p) ⟶ X₁.M.Z
  cen : y (cPt p) = z₁

  T : Trait F

  ι : FractionRing T.V →+* PadicAlgCl p
  int : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))
  comm : gPt p ≫ y ≫ X₁.π = spMap ι ≫ T.y ≫ i

variable {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

namespace Setup

variable (X₁ : Setup F W i)

theorem isThetaCompact : IsThetaCompact F X₁.z i :=
  ⟨X₁.proj, X₁.normalZ, X₁.imm, X₁.thetaSetup_structureMap_comp, X₁.dense, W, X₁.e8, X₁.thetaInt⟩

theorem div : X₁.M.HasDiv X₁.S.th :=
  X₁.thetaInt X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.sharp X₁.gen X₁.M X₁.π X₁.normal X₁.comp

include X₁ in

theorem posW : PosW W := X₁.e8.1

include X₁ in

theorem diag_pos (a : Fin 8) : 0 < W a a := by
  have := X₁.e8.1.diag_pos (i := a)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
  have h2 : (0 : ℤ) < W a a + W a a := by exact_mod_cast this
  omega

theorem isProper_compactificationMap : IsProper X₁.z := ((isProjOver_iff_isProper_and_exists_isAmpleLB X₁.z).1 X₁.proj).1

theorem s_comp : X₁.M.s ≫ spMap X₁.κ = X₁.π ≫ X₁.z := by
  refine ext_of_isDominant X₁.M.pt ?_
  rw [← Category.assoc, X₁.M.pt_s, ← Category.assoc, X₁.comp, Category.assoc, Category.assoc, X₁.thetaSetup_structureMap_comp, X₁.base]
  exact (Spec.map_comp (CommRingCat.ofHom X₁.κ) (CommRingCat.ofHom (algebraMap X₁.o₁ X₁.Ω₁))).symm

theorem projM : IsProjOver X₁.M.s := by
  haveI := X₁.fin
  obtain ⟨h1, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB X₁.z).1 X₁.proj
  haveI : IsProper (X₁.M.s ≫ spMap X₁.κ) := by rw [s_comp]; infer_instance
  haveI : IsProper X₁.M.s := IsProper.of_comp X₁.M.s (spMap X₁.κ)
  exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, _, hL.pull_of_isFinite X₁.π⟩

theorem isUnit_level : IsUnit (n : X₁.o₁) := by
  have hn : (n : ℂ) ≠ 0 := by have := X₁.three_le; exact_mod_cast (by omega : n ≠ 0)
  have h : IsUnit (n : cycAway n) :=
    IsUnit.of_mul_eq_one ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ (Subtype.ext (by simp [hn]))
  simpa using h.map X₁.κ

end Setup

def CTrait.sc {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : ℝ :=
  -Real.log ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖

def CTrait.val {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁)
    (a : X₁.M.Z.presheaf.stalk z₁) : PadicAlgCl p :=
  X₁.M.val (gPt p ≫ c.y) (X₁.M.stalkHom z₁ a)

namespace CTrait

variable {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

theorem point_eq {c c' : CTrait X₁ p z₁} (h : c.y = c'.y) : spMap c.ι ≫ c.T.y = spMap c'.ι ≫ c'.T.y := by
  haveI := X₁.imm
  rw [← cancel_mono i, Category.assoc, Category.assoc, ← c.comm, ← c'.comm, h]

def valInt (c : CTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* OO p :=
  (RatModel.valLoc c.y z₁ (specializes_of_eq c.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem val_eq_valInt (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : c.val a = (c.valInt a : PadicAlgCl p) :=
  RatModel.val_spMap_comp (OO p).subtype c.y (specializes_of_eq c.cen) (X₁.M.stalkEquiv z₁ a)

theorem norm_val_le (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖c.val a‖ ≤ 1 := by
  rw [val_eq_valInt]
  have h : Valued.v (c.valInt a : PadicAlgCl p) ≤ 1 := (c.valInt a).2
  exact_mod_cast h


theorem norm_uniformiser_pos (c : CTrait X₁ p z₁) : 0 < ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ :=
  norm_pos_iff.2 ((map_ne_zero c.ι).2 fun h =>
    c.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h))

theorem scale_pos (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have h1 := c.norm_uniformiser_pos
  set x := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hx
  have h0 : x ≠ 0 := fun h => by simp [h] at h1
  have h2 : ‖c.ι x‖ < 1 := by
    by_contra h
    have : ‖c.ι x⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨v, hv⟩ := (c.int _).1 this
    refine c.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing c.T.V) ?_))
    rw [map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]
  exact neg_pos.2 (Real.log_neg h1 h2)

theorem exp_neg_sc_mul (c : CTrait X₁ p z₁) (a : ℕ) :
    Real.exp (-(c.sc * a)) = ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ ^ a := by
  rw [CTrait.sc, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log c.norm_uniformiser_pos]

example (c : CTrait X₁ p z₁) : c.val 1 = 1 := by simp [val_eq_valInt]

example (c : CTrait X₁ p z₁) : c.val 0 = 0 := by simp [val_eq_valInt]

end CTrait

def FPre.Matches {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)) :
    Prop :=
  ∀ c : CTrait X₁ p z₁, ∃ y : Φ.Y, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X,
    ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)

def ApproxAt (X₁ : Setup F W i) (φ : InvFun ℤ) (d : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c₀ : CTrait X₁ p z₁) (e : ℕ), ∃ f : X₁.M.Z.presheaf.stalk z₁,
    ‖c₀.val f‖ = Real.exp (-(c₀.sc * (d * φ.evalZ c₀.T.β))) ∧ ∀ c : CTrait X₁ p z₁,
      ‖c.val f‖ ≤ Real.exp (-(c.sc * (d * φ.evalZ c.T.β))) ∨
        ∃ h ∈ IsLocalRing.maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖c.val f‖ ≤ ‖c.val h‖ ^ e

example (X₁ : Setup F W i) (φ : InvFun ℤ) : ApproxAt X₁ φ 0 := fun p _ z₁ c₀ e =>
  ⟨1, by simp [CTrait.val_eq_valInt], fun c => Or.inl (by simp [CTrait.val_eq_valInt])⟩

example : IsEmpty (Setup F 0 i) := ⟨fun X₁ => by simpa using X₁.diag_pos 0⟩

end GlobalTheory.Poinc
end
end
