import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev LevGrp (Dw : Datum H) (l : Level H) : Type := LevQ Dw l ≃ₗ[𝓞 E] LevQ Dw l

section Act

variable {Xo : Moduli Dw l} {c : Coeff l}

def FrAlong {ρ : Xo.X ⟶ Xo.X} (m : SABMap Xo.univ.t Xo.univ.t ρ) {k : Type} [CommRing k] [Algebra c.F k]
    (y y' : FrPt Xo c k) : Prop :=
  y.x ≫ ρ = y'.x ∧ (∀ τ i, y.u τ i ≫ m.φ = y'.u τ i) ∧
  ∃ (w₀ : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull m.φ)) (pm : Gx y.x ⟶ Gx y'.x)
    (t : LB.Sec (LB.LinComb (Xo.univ.t.PP.L.pull m.φ) (K := Fin 1)
      (fun _ => (snd (Over.mk y.x) Xo.univ.t.G).left) (fun _ => 1))),
    w₀.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit) (fun _ => eSec Xo.univ.t.G) (fun _ => 1))
      Xo.univ.t.PP.rig (m.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig) ∧
    pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ m.φ ∧
    pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
    SecMaps (LB.linCombIso w₀ (K := Fin 1) (fun _ => (snd (Over.mk y.x) Xo.univ.t.G).left) (fun _ => 1))
      y.s t ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
      (h : (LB.LinComb (Xo.univ.t.PP.L.pull m.φ) (K := Fin 1)
        (fun _ => (snd (Over.mk y.x) Xo.univ.t.G).left) (fun _ => 1)).U (fun _ _ => i 0) ≤
          pm ⁻¹ᵁ (PPx y'.x).U i),
      (pm.appLE _ _ h).hom (y'.s.f i) = t.f (fun _ _ => i 0)

def IsLevelAct (κ : LevGrp Dw l) (f f' : Rul Xo c) : Prop :=
  ∃ (ρ : Xo.X ≅ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t ρ.hom), ρ.hom ≫ Xo.s = Xo.s ∧
    (∀ a a' : Dw.La, (Submodule.Quotient.mk a' : LevQ Dw l) = κ (Submodule.Quotient.mk a) →
      (Xo.univ.eta a').left ≫ m.φ = ρ.hom ≫ (Xo.univ.eta a).left) ∧
    (∀ a : Dw.La, (Xo.univ.etaA a).left ≫ m.φ = ρ.hom ≫ (Xo.univ.etaA a).left) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k),
      ∃ y' : FrPt Xo c k, FrAlong m y y' ∧ evR Xo c f' y = evR Xo c f y'

end Act

section Placed

variable (c : Coeff l) {n : ℕ}

def push (γ : Matrix (Fin n) (Fin n) E) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  MvPolynomial.aeval fun m : LtN Dw n => letB c m.1 m.2.1 fun a => IsCMField.complexConj E (γ a m.2.2)

def archChar (dd : (E →+* ℂ) → ℤ) (γ : Matrix (Fin n) (Fin n) E) : c.F :=
  ∏ τ : E →+* ℂ, embF c τ γ.det ^ dd τ

def cocyc (dd : (E →+* ℂ) → ℤ) {J : Subgroup (UA E n)} (lam : J →* c.Fˣ) (γ : Matrix (Fin n) (Fin n) E) (k : J) : c.F :=
  archChar c dd γ * ((lam k : c.Fˣ) : c.F)

def IsPlaced (dd : (E →+* ℂ) → ℤ) {J : Subgroup (UA E n)} (lam : J →* c.Fˣ)
    {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (f : UA E n → T) : Prop :=
  ∀ (γ₀ : Matrix (Fin n) (Fin n) E) (γ : UA E n), γ.1 = γ₀.map (diagE E) → ∀ (h : UA E n) (k : J),
    io (f (γ * h * (k : UA E n))) = cocyc c dd lam γ₀ k • push c γ₀ (io (f h))

variable {c} {Xo : Moduli Dw l}

end Placed

section Row

variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
  {G : Type} [Group G] (Γ : Subgroup G) (dict : G → Σ k, Frame ((U σ).X k).Ψ r) (mu : G → ℂ) (xi : ℝ)

def jConst (a : (E →+* ℂ) × ℕ → ℕ) (cc : (U σ).Comp → ℂ) (f : Rul Xo c) (g : G) : ℂ :=
  cc (dict g).1 * ((lieFac Dw xi a : ℝ) : ℂ) * (mu g * rdU (U σ) f (dict g).1 (dict g).2)

variable (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ}
  {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
  {Tup : Type} (d : Tup → DeltaDat Xo c n) {ι : Tup → Type} [∀ t, Fintype (ι t)] (vol : Tup → ℚ)
  (J : Tup → Subgroup (UA E n)) (h : ∀ t, ι t → UA E n) (N : ∀ t, ι t → ℕ) (ep : Tup → UA E n → ℂ)
  (cξ : Tup → Rul Xo c) (φ : Tup → (Fin n → ConjQ Dw l) → c.F) (φδ : ∀ t, (Fin n → LaJ Xo c (d t)) → c.F)

def EqAt (cc : (U σ).Comp → ℂ) (ph : ℂ) (z : LevGrp Dw l) (ζ : ℂ) (t : Tup) (x : ι t → T) (θ : G → ℂ) : Prop :=
  (∃ F ∈ cusp Xo c U a n, ∃ F' ∈ cusp Xo c U a n,
    IsClassSumRuleDown Xo c (d t) (vol t) (J t) (h t) (N t) (ep t) (cξ t) (φ t) (φδ t) io x F ∧ IsLevelAct z F F') ∧
  ∀ F ∈ cusp Xo c U a n, ∀ F' ∈ cusp Xo c U a n,
    IsClassSumRuleDown Xo c (d t) (vol t) (J t) (h t) (N t) (ep t) (cξ t) (φ t) (φδ t) io x F → IsLevelAct z F F' →
      ∀ g, ph * θ g = ζ * jConst U σ dict mu xi a cc F' g

variable (dd : (E →+* ℂ) → ℤ) (lam : ∀ t, J t →* c.Fˣ) (thAd : Tup → (UA E n → T) → G → ℂ)

variable (q₁ : ℕ) (S : Tup → Finset (Plc E))

end Row

theorem push_one (c : Coeff l) (n : ℕ) :
    push (Dw := Dw) c (1 : Matrix (Fin n) (Fin n) E) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, i, j⟩
  simp only [push, letB, MvPolynomial.aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb]
  · simp

example (c : Coeff l) {n : ℕ} (dd : (E →+* ℂ) → ℤ) {J : Subgroup (UA E n)} (lam : J →* c.Fˣ)
    (io : c.F →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) : IsPlaced c dd lam io (0 : UA E n → c.F) := by
  intro γ₀ γ _ h k
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter
