import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ThetaWeightHeightConstants
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TotallyPositiveExponents

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree

open Formalism.BasicNotions NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents
open scoped TensorProduct ComplexOrder

def Kfld (D : D7) : IntermediateField ℚ D.what₂.LL :=
  IntermediateField.adjoin ℚ (Set.range D.what₂.OtoLL)

def KK (D : D7) : Type := ↥(Kfld D)

instance (D : D7) : Field (KK D) := inferInstanceAs (Field ↥(Kfld D))
instance (D : D7) : NumberField (KK D) := inferInstanceAs (NumberField ↥(Kfld D))

def incl (D : D7) : KK D →+* D.what₂.LL := (Kfld D).val.toRingHom

abbrev OO (D : D7) : Type := 𝓞 (KK D)

abbrev Place (D : D7) : Type := HeightOneSpectrum (OO D)

abbrev Emb (D : D7) : Type := KK D →+* ℂ

def emb0 (D : D7) : Emb D := D.what₂.embLL.comp (incl D)

instance (D : D7) : Algebra (KK D) ℂ := (emb0 D).toAlgebra


def nK (D : D7) : ℕ := Module.finrank ℚ (KK D)



open Classical in

def vK {D : D7} (l : Place D) (a : KK D) : WithTop ℝ :=
  if a = 0 then ⊤ else (((vAdd l a : ℤ) : ℝ) : WithTop ℝ)

theorem vK_nonneg {D : D7} (l : Place D) (a : OO D) : 0 ≤ vK l (a : KK D) := by
  unfold vK
  split_ifs with h
  · exact le_top
  · have h1 : l.valuation (KK D) (a : KK D) ≤ 1 := l.valuation_le_one a
    have h0 : l.valuation (KK D) (a : KK D) ≠ 0 := by simpa using h
    have : WithZero.log (l.valuation (KK D) (a : KK D)) ≤ 0 := by
      rw [← WithZero.log_one, WithZero.log_le_log h0 one_ne_zero]; exact h1
    have h2 : (0 : ℤ) ≤ vAdd l (a : KK D) := by unfold vAdd; omega
    exact_mod_cast h2

abbrev Wsp (D : D7) (j : Lift D.R) : @HSpace D.host.E _ _ D.host.cmStar :=
  letI := D.host.cmStar; D.sp.W j.1

abbrev WV (D : D7) (j : Lift D.R) : Type := letI := D.host.cmStar; (Wsp D j).V

def hW (D : D7) (j : Lift D.R) (x y : WV D j) : D.host.E := letI := D.host.cmStar; (Wsp D j).hD x y

structure CuspGeom (D : D7) (j : Lift D.R) where
  lat : letI := D.host.cmStar; Submodule (𝓞 D.host.E) (WV D j)
  lat_lat : letI := D.host.cmStar; Submodule.IsLattice D.host.E lat
  lat_unimod : letI := D.host.cmStar; Formalism.HermitianLatticesTheory.IsUnimodular (Wsp D j).hT lat
  frame : letI := D.host.cmStar; V D.host (rho j) →ₗ[D.host.E] WV D j
  frame_inj : Function.Injective frame
  frame_iso : ∀ u u', hW D j (frame u) (frame u') = 0

namespace CuspGeom

variable {D : D7} {j : Lift D.R} (c : CuspGeom D j)

def N : Submodule (𝓞 D.host.E) (V D.host (rho j)) :=
  letI := D.host.cmStar; c.lat.comap (c.frame.restrictScalars (𝓞 D.host.E))

def X : Submodule (𝓞 D.host.E) (V D.host (rho j)) := charLattice c.N

def Conj (c c' : CuspGeom D j) : Prop :=
  letI := D.host.cmStar
  ∃ γ : WV D j ≃ₗ[D.host.E] WV D j, (∀ x y, hW D j (γ x) (γ y) = hW D j x y) ∧
    (∀ x, γ x ∈ c'.lat ↔ x ∈ c.lat) ∧
    ∀ x, γ x ∈ LinearMap.range c'.frame ↔ x ∈ LinearMap.range c.frame

theorem Conj.refl : c.Conj c := by
  letI := D.host.cmStar
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

def killed (c₁ : ℝ) : Set (expGroup c.X) := {χ | IsShallow c.X c₁ (χ : Herm D.host (rho j))}


end CuspGeom

def zeroWt (D : D7) (j : Lift D.R) : ThetaWeight D j where
  plus := 0
  minus := 0
  plus_anti _ := antitone_const
  minus_anti _ := antitone_const
  n := 0

structure FormsRecord (D : D7) where

  Cusp : (j : Lift D.R) → ThetaWeight D j → Type
  [acg : ∀ j G, AddCommGroup (Cusp j G)]
  [modK : ∀ j G, Module (KK D) (Cusp j G)]
  [fd : ∀ j G, FiniteDimensional (KK D) (Cusp j G)]

  mul : ∀ {j} {G G' : ThetaWeight D j}, Cusp j G →ₗ[KK D] Cusp j G' →ₗ[KK D] Cusp j (G.add G')
  mul_comm : ∀ {j} {G G' : ThetaWeight D j} (f : Cusp j G) (g : Cusp j G'), HEq (mul f g) (mul g f)
  mul_assoc : ∀ {j} {G G' G'' : ThetaWeight D j} (f : Cusp j G) (g : Cusp j G') (h : Cusp j G''),
    HEq (mul (mul f g) h) (mul f (mul g h))

  one : ∀ j, rho j = 0 → Cusp j (zeroWt D j)
  one_mul : ∀ j (h : rho j = 0) (G : ThetaWeight D j) (f : Cusp j G), HEq (mul (one j h) f) f

  Pt : Lift D.R → Type
  place : ∀ {j}, Pt j → Place D

  vAt : ∀ {j} {G : ThetaWeight D j}, Pt j → Cusp j G → WithTop ℝ
  vAt_smul : ∀ {j} {G : ThetaWeight D j} (y : Pt j) (a : KK D) (f : Cusp j G),
    vAt y (a • f) = vK (place y) a + vAt y f
  vAt_add : ∀ {j} {G : ThetaWeight D j} (y : Pt j) (f g : Cusp j G),
    min (vAt y f) (vAt y g) ≤ vAt y (f + g)
  vAt_mul : ∀ {j} {G G' : ThetaWeight D j} (y : Pt j) (f : Cusp j G) (g : Cusp j G'),
    vAt y (mul f g) = vAt y f + vAt y g

  vAt_discrete : ∀ {j} (y : Pt j), ∃ e : ℕ, 0 < e ∧ ∀ (G : ThetaWeight D j) (f : Cusp j G) (t : ℝ),
    vAt y f = (t : WithTop ℝ) → ∃ z : ℤ, e * t = z

  sup : ∀ {j} {G : ThetaWeight D j}, Emb D → Cusp j G → ℝ
  sup_smul : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (a : KK D) (f : Cusp j G),
    sup σ (a • f) = ‖σ a‖ * sup σ f
  sup_add : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f g : Cusp j G), sup σ (f + g) ≤ sup σ f + sup σ g
  sup_mul : ∀ {j} {G G' : ThetaWeight D j} (σ : Emb D) (f : Cusp j G) (g : Cusp j G'),
    sup σ (mul f g) ≤ sup σ f * sup σ g
  sup_mul_self : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f : Cusp j G), sup σ (mul f f) = sup σ f ^ 2
  sup_conj : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f : Cusp j G),
    sup (ComplexEmbedding.conjugate σ) f = sup σ f

  ip : ∀ {j} {G : ThetaWeight D j}, Emb D → Cusp j G → Cusp j G → ℂ
  ip_add : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f f' g : Cusp j G),
    ip σ (f + f') g = ip σ f g + ip σ f' g
  ip_smul : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (a : KK D) (f g : Cusp j G),
    ip σ (a • f) g = σ a * ip σ f g
  ip_symm : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f g : Cusp j G),
    ip σ g f = starRingEnd ℂ (ip σ f g)

  ip_posDef : ∀ {j} {G : ThetaWeight D j} (σ : Emb D), ∃ (n : ℕ) (b : Module.Basis (Fin n) (KK D) (Cusp j G)),
    (Matrix.of fun i k => ip σ (b i) (b k)).PosDef
  ip_conj : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f g : Cusp j G),
    ip (ComplexEmbedding.conjugate σ) f g = starRingEnd ℂ (ip σ f g)

  l2_norm_le_sup_norm : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f : Cusp j G), √(ip σ f f).re ≤ sup σ f
  l2_norm_mul : ∀ {j} {G G' : ThetaWeight D j} (σ : Emb D) (f : Cusp j G) (g : Cusp j G'),
    √(ip σ (mul f g) (mul f g)).re ≤ sup σ f * √(ip σ g g).re

  MaxCusp : Lift D.R → Type
  geom : ∀ {j}, MaxCusp j → CuspGeom D j
  geom_cover : ∀ j, 0 < rho j → ∀ c : CuspGeom D j, ∃ a : MaxCusp j, c.Conj (geom a)
  no_cusp : ∀ j, rho j = 0 → IsEmpty (MaxCusp j)

  Coef : ∀ {j} (a : MaxCusp j), ThetaWeight D j → expGroup (geom a).X → Type
  [coefAcg : ∀ {j} (a : MaxCusp j) G χ, AddCommGroup (Coef a G χ)]
  [coefMod : ∀ {j} (a : MaxCusp j) G χ, Module ℂ (Coef a G χ)]

  fj : ∀ {j} (a : MaxCusp j) (G : ThetaWeight D j) (χ : expGroup (geom a).X),
    (ℂ ⊗[KK D] Cusp j G) →ₗ[ℂ] Coef a G χ

attribute [instance] FormsRecord.acg FormsRecord.modK FormsRecord.fd FormsRecord.coefAcg FormsRecord.coefMod

namespace FormsRecord

variable {D : D7} (Φ : FormsRecord D) {j : Lift D.R}

instance modO (G : ThetaWeight D j) : Module (OO D) (Φ.Cusp j G) :=
  Module.compHom _ (algebraMap (OO D) (KK D))

instance tower (G : ThetaWeight D j) : IsScalarTower (OO D) (KK D) (Φ.Cusp j G) :=
  ⟨fun a b f => by
    change (a • b) • f = (algebraMap (OO D) (KK D) a) • (b • f)
    rw [Algebra.smul_def, mul_smul]⟩

abbrev Forms (j : Lift D.R) : Type := DirectSum (ThetaWeight D j) (Φ.Cusp j)

abbrev CuspC (G : ThetaWeight D j) : Type := ℂ ⊗[KK D] Φ.Cusp j G

def l2 {G : ThetaWeight D j} (σ : Emb D) (f : Φ.Cusp j G) : ℝ := √(Φ.ip σ f f).re

theorem vAt_zero {G : ThetaWeight D j} (y : Φ.Pt j) : Φ.vAt y (0 : Φ.Cusp j G) = ⊤ := by
  have := Φ.vAt_smul y 0 (0 : Φ.Cusp j G)
  simpa [vK] using this

def integralOn (G : ThetaWeight D j) (S : Set (Φ.Pt j)) : Submodule (OO D) (Φ.Cusp j G) where
  carrier := {f | ∀ y ∈ S, 0 ≤ Φ.vAt y f}
  add_mem' := fun {f g} hf hg y hy => le_trans (le_min (hf y hy) (hg y hy)) (Φ.vAt_add y f g)
  zero_mem' := fun y _ => by rw [vAt_zero]; exact le_top
  smul_mem' := fun a f hf y hy => by
    change 0 ≤ Φ.vAt y ((a : KK D) • f)
    rw [Φ.vAt_smul]
    exact add_nonneg (vK_nonneg _ a) (hf y hy)

def M (G : ThetaWeight D j) : Submodule (OO D) (Φ.Cusp j G) := Φ.integralOn G Set.univ

end FormsRecord

namespace FormsRecord

variable {D : D7} (Φ : FormsRecord D) {j : Lift D.R}

def fjK (a : Φ.MaxCusp j) (G : ThetaWeight D j) (χ : expGroup (Φ.geom a).X) (f : Φ.Cusp j G) :
    Φ.Coef a G χ := Φ.fj a G χ (1 ⊗ₜ f)

def PositiveExponents : Prop := ∀ (j : Lift D.R) (a : Φ.MaxCusp j) (G : ThetaWeight D j)
  (χ : expGroup (Φ.geom a).X) (F : Φ.CuspC G), Φ.fj a G χ F ≠ 0 → TotPos (χ : Herm D.host (rho j))

def deepC (G : ThetaWeight D j) (c₁ : ℝ) : Submodule ℂ (Φ.CuspC G) :=
  ⨅ (a : Φ.MaxCusp j) (χ ∈ (Φ.geom a).killed c₁), LinearMap.ker (Φ.fj a G χ)

def deepK (G : ThetaWeight D j) (c₁ : ℝ) : Submodule (KK D) (Φ.Cusp j G) :=
  ((Φ.deepC G c₁).restrictScalars (KK D)).comap (TensorProduct.mk (KK D) ℂ (Φ.Cusp j G) 1)


def deepKRec (G : ThetaWeight D j) (T : ℕ) (c : ℝ) : Submodule (KK D) (Φ.Cusp j G) :=
  Φ.deepK G (cOne D j T c)

def Descent : Prop := ∀ (j : Lift D.R) (G : ThetaWeight D j) (c₁ : ℝ),
  Φ.deepC G c₁ = (Φ.deepK G c₁).baseChange ℂ

end FormsRecord

theorem vK_mul {D : D7} (l : Place D) (a b : KK D) : vK l (a * b) = vK l a + vK l b := by
  unfold vK
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Examples₂.PlacesToy.vAdd_mul l ha hb]
  push_cast; rfl

theorem vK_add {D : D7} (l : Place D) (a b : KK D) : min (vK l a) (vK l b) ≤ vK l (a + b) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  by_cases hab : a + b = 0
  · simp [vK, hab]
  have := Examples₂.PlacesToy.vAdd_add l ha hb hab
  simp only [vK, if_neg ha, if_neg hb, if_neg hab]
  rcases min_le_iff.1 this with h | h
  · exact min_le_of_left_le (by exact_mod_cast h)
  · exact min_le_of_right_le (by exact_mod_cast h)

open Classical in

def lineRecord (D : D7) : FormsRecord D where
  Cusp _ _ := KK D
  mul := LinearMap.mul (KK D) (KK D)
  mul_comm f g := heq_of_eq (_root_.mul_comm f g)
  mul_assoc f g h := heq_of_eq (_root_.mul_assoc f g h)
  one _ _ := 1
  one_mul _ _ _ f := heq_of_eq (_root_.one_mul f)
  Pt _ := Place D
  place y := y
  vAt y f := vK y f
  vAt_smul y a f := vK_mul y a f
  vAt_add y f g := vK_add y f g
  vAt_mul y f g := vK_mul y f g
  vAt_discrete y := ⟨1, one_pos, fun _ f t h => by
    unfold vK at h
    split_ifs at h
    · exact absurd h (by simp)
    · exact ⟨vAdd y f, by rw [← WithTop.coe_injective h]; simp⟩⟩
  sup σ f := ‖σ f‖
  sup_smul σ a f := by simp
  sup_add σ f g := by rw [map_add]; exact norm_add_le _ _
  sup_mul σ f g := by simp
  sup_mul_self σ f := by simp [sq]
  sup_conj σ f := by simp
  ip σ f g := σ f * starRingEnd ℂ (σ g)
  ip_add σ f f' g := by simp [add_mul]
  ip_smul σ a f g := by simp [_root_.mul_assoc]
  ip_symm σ f g := by simp [_root_.mul_comm]
  ip_posDef σ := ⟨1, Module.Basis.singleton _ _, by
    convert Matrix.PosDef.one (n := Fin 1) (R := ℂ)
    ext i k; simp [Matrix.one_apply, Subsingleton.elim i k]⟩
  ip_conj σ f g := by simp
  l2_norm_le_sup_norm σ f := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  l2_norm_mul σ f g := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.ofReal_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    simp
  MaxCusp j := {_c : CuspGeom D j // 0 < rho j}
  geom a := a.1
  geom_cover _ h c := ⟨⟨c, h⟩, CuspGeom.Conj.refl c⟩
  no_cusp _ h := ⟨fun a => by have := a.2; omega⟩
  Coef _ _ _ := ℂ ⊗[KK D] KK D
  fj _ _ χ := if TotPos χ.1 then LinearMap.id else 0

example (D : D7) (j : Lift D.R) (G : ThetaWeight D j) :
    (∃ f ∈ (lineRecord D).M G, f ≠ 0) ∧ (lineRecord D).PositiveExponents := by
  refine ⟨⟨show (lineRecord D).Cusp j G from (1 : KK D), fun y _ => ?_,
    show (1 : KK D) ≠ 0 from one_ne_zero⟩, fun j a G χ F h => ?_⟩
  · change Place D at y
    change 0 ≤ vK y (1 : KK D)
    simpa using vK_nonneg (D := D) y 1
  · by_contra hn
    exact h (by simp only [lineRecord]; rw [if_neg hn]; rfl)

end GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree

end
