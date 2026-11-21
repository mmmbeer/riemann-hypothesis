import Mathlib
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.MemWmPerp

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

namespace RowPar

variable {R : Ranks} (S : RowPar R)

def lamWQ (i : Fin R.r) : ℚ := S.aPlus R.m (i.1 + 1) + (R.nV : ℚ) / 2 - S.eAt (R.m - 1)

def lamW : DomWeight R.r := ofQ S.lamWQ

end RowPar

namespace Wts

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

def lamW (τ : X.Tau) : DomWeight R.r := (W.row τ).lamW

end Wts

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def wmVal (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : CoefPk X R.r (DecoSet X.E R.r ∅ SG) :=
  roundPk X W.lamW fun d => d.1.N

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

variable (R) in

def wmTyQ (Q : Finset (HeightOneSpectrum (𝓞 X.E))) : LevFam X.E X.K R.r Q := fun _ => ⟨⊤, 1⟩

def wmTy (P : LevFam X.E X.K R.r Pr.vGs) : LevFam X.E X.K R.r (rowSG Pr sel mu) :=
  P.inv.glue (wmTyQ R (QE sel (mu : Chr X.F X.E X.K)))

@[reducible] def wmGSD (P : LevFam X.E X.K R.r Pr.vGs) : GSD X.K :=
  formGSD (wmVal W (rowSG Pr sel mu)) (wmTy sel mu P).inv

@[reducible] def wmKGSD : GSD X.K := wmGSD W sel mu (rKg X Pr R)

@[reducible] def WmCSD (P : LevFam X.E X.K R.r Pr.vGs) (h : (wmGSD W sel mu P).Ok) : CSD X.K := (wmGSD W sel mu P).toCSD h

theorem unipotentHat_normalizes_W (a : G0 X.E Pr.vGs R.r) (w : rowSG Pr sel mu) :
    ((wmTy sel mu (rKg X Pr R)).inv w).NormBy (unipotentGroupBlockEmbedding Pr sel mu (le_refl R.r) a w) := by
  generalize unipotentGroupBlockEmbedding Pr sel mu (le_refl R.r) a w = b
  by_cases hw : w.1 ∈ Pr.vGs
  · have e : (wmTy sel mu (rKg X Pr R)).inv w = ⟨⊥, 1⟩ := by
      unfold LevFam.inv Lev.inv wmTy LevFam.glue
      rw [dif_pos hw]
      show ({ H := ⊥, lam := (1⁻¹)⁻¹ } : Lev (𝓞 X.E ⧸ (w : HeightOneSpectrum (𝓞 X.E)).asIdeal) X.K R.r) = ⟨⊥, 1⟩
      congr 1
    rw [e]
    intro h
    refine ⟨h, ?_, rfl⟩
    rw [Subgroup.mem_bot.mp h.2, mul_one, one_mul]
  · have e : (wmTy sel mu (rKg X Pr R)).inv w = ⟨⊤, 1⟩ := by
      unfold LevFam.inv Lev.inv wmTy LevFam.glue
      rw [dif_neg hw]
      show ({ H := ⊤, lam := 1⁻¹ } : Lev (𝓞 X.E ⧸ (w : HeightOneSpectrum (𝓞 X.E)).asIdeal) X.K R.r) = ⟨⊤, 1⟩
      congr 1
    rw [e]
    intro h
    refine ⟨⟨b⁻¹ * h.1 * b, Subgroup.mem_top _⟩, ?_, rfl⟩
    show b⁻¹ * h.1 = b⁻¹ * h.1 * b * b⁻¹
    rw [mul_inv_cancel_right]

def unipotentRightActionFormsW : Representation X.K (G0 X.E Pr.vGs R.r) (wmKGSD W sel mu).EqFun :=
  trRep _ _ (unipotentGroupBlockEmbedding Pr sel mu (le_refl R.r)) (unipotentHat_normalizes_W sel mu)

end Forms

section Data

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def wmIntAt (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (N' : Submodule (𝓞 E) (Sp E a)) (N : Submodule (𝓞 E) (Sp E b))
    (x : Sp E a →ₗ[E] Sp E b) : Prop :=
  ∀ y ∈ localization₂ P.asIdeal N', x y ∈ localization₂ P.asIdeal N

def WmSchw {K : Type} [Zero K] (S : Finset (HeightOneSpectrum (𝓞 E))) {a b : ℕ} (Φ : (Sp E a →ₗ[E] Sp E b) → K) : Prop :=
  ∃ (A' B' : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) (Sp E a)) (A B : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) (Sp E b)),
    (∀ P ∈ S, Submodule.IsLattice E (A' P) ∧ Submodule.IsLattice E (A P) ∧ Submodule.IsLattice E (B' P) ∧
      Submodule.IsLattice E (B P)) ∧
    (∀ x y, (∀ P ∈ S, wmIntAt P (A' P) (A P) y) → Φ (x + y) = Φ x) ∧
    (∀ x, Φ x ≠ 0 → ∀ P ∈ S, wmIntAt P (B' P) (B P) x)

variable {SG : Finset (HeightOneSpectrum (𝓞 E))}

def wmIsRed {a b : ℕ} (d' : DecoSet E a ∅ SG) (d : DecoSet E b ∅ SG) (w : SG) (x : Sp E a →ₗ[E] Sp E b)
    (M : Matrix (Fin b) (Fin a) (𝓞 E ⧸ w.1.asIdeal)) : Prop :=
  ∀ y ∈ d'.1.at w.1, x y ∈ d.1.at w.1 ∧ d.1.be w (x y) = M.mulVec (d'.1.be w y)

open Classical in

def lemU {κ K : Type} [CommRing κ] [Field K] {r n : ℕ} (h : r ≤ n) (l : Lev κ K r) (s : κˣ →* Kˣ)
    (M : Matrix (Fin n) (Fin r) κ) : K :=
  if H : ∃ k : ↥l.H, (∀ i j, M (Fin.castLE h i) j = (k.1 : Matrix (Fin r) (Fin r) κ) i j) ∧
      ∀ (i : Fin n) (j : Fin r), r ≤ i.1 → M i j = 0
  then ((l.lam H.choose : Kˣ) : K) * (((s (Matrix.GeneralLinearGroup.det H.choose.1))⁻¹ : Kˣ) : K)
  else 0

open Classical in

def wmPhi {K : Type} [Field K] {a b : ℕ} (loc : ∀ w : SG, Matrix (Fin b) (Fin a) (𝓞 E ⧸ w.1.asIdeal) → K)
    (d' : DecoSet E a ∅ SG) (d : DecoSet E b ∅ SG) (x : Sp E a →ₗ[E] Sp E b) : K :=
  ∏ w : SG, if h : ∃ M, wmIsRed d' d w x M then loc w h.choose else 0

end Data

section Dist

variable (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (V V' : Type) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

abbrev WmTh : Type :=
  Finset (HeightOneSpectrum (𝓞 E)) → DecoSet E a ∅ SG → DecoSet E b ∅ SG →
    ((Sp E a →ₗ[E] Sp E b) → K) →ₗ[K] (V →ₗ[K] V')

variable {E K a b SG V V'}

open Classical in

structure WmTh.Ok (th : WmTh E K a b SG V V') (rho : UF E b →* Module.End K V) (rho' : UF E a →* Module.End K V')
    (sV sW : ∀ w : SG, (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (aV aW : HeightOneSpectrum (𝓞 E) → K) : Prop where

  rat : ∀ S d' d Φ (γ' : UF E a) (γ : UF E b), WmSchw S Φ →
    th S (((γ', 1) : UF E a × GLG E a SG) • d') (((γ, 1) : UF E b × GLG E b SG) • d)
        (fun x => Φ (γ.1.symm.toLinearMap ∘ₗ x ∘ₗ γ'.1.toLinearMap)) =
      rho' γ' ∘ₗ th S d' d Φ ∘ₗ rho γ⁻¹

  lev : ∀ S d' d Φ (κ' : GLG E a SG) (κ : GLG E b SG), WmSchw S Φ →
    th S (((1 : UF E a), κ') • d') (((1 : UF E b), κ) • d) Φ =
      (∏ w : SG, (((sV w (Matrix.GeneralLinearGroup.det (κ' w)))⁻¹ : Kˣ) : K) *
        ((sW w (Matrix.GeneralLinearGroup.det (κ w)) : Kˣ) : K)) • th S d' d Φ

  vac : ∀ S d' d Φ (P : HeightOneSpectrum (𝓞 E)), conjPrime₂ P ≠ P → P ∉ S → conjPrime₂ P ∉ S → P ∉ SG → conjPrime₂ P ∉ SG →
    WmSchw S Φ →
    th S d' d Φ = th (insert P S) d' d (fun x => if wmIntAt P d'.1.N d.1.N x then Φ x else 0)

  nbV : ∀ S d' d d₁ Φ (P : HeightOneSpectrum (𝓞 E)) (i : ℕ), conjPrime₂ P ≠ P → P ∈ S → conjPrime₂ P ∉ S → P ∉ SG → conjPrime₂ P ∉ SG →
    WmSchw S Φ → d₁ ∈ d.heckeSet P.asIdeal i → th S d' d Φ = aV P ^ i • th S d' d₁ Φ

  nbW : ∀ S d' d'₁ d Φ (P : HeightOneSpectrum (𝓞 E)) (i : ℕ), conjPrime₂ P ≠ P → P ∈ S → conjPrime₂ P ∉ S → P ∉ SG → conjPrime₂ P ∉ SG →
    WmSchw S Φ → d'₁ ∈ d'.heckeSet P.asIdeal i → th S d'₁ d Φ = aW P ^ i • th S d' d Φ

end Dist

section Theta

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in

def wmLoc (Ch : Chars X Pr R.m) (P : LevFam X.E X.K R.r Pr.vGs) :
    ∀ w : rowSG Pr sel mu, Matrix (Fin R.nV) (Fin R.r) (𝓞 X.E ⧸ w.1.asIdeal) → X.K := fun w =>
  if h : w.1 ∈ Pr.vGs then lemU (r_le_nV R) (P ⟨w.1, h⟩).inv (chiAt Ch ⟨w.1, h⟩ (R.m - 1))⁻¹
  else lemU (r_le_nV R) (⟨⊤, 1⟩ : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K R.r) (resChar (mu : Chr X.F X.E X.K) w.1)

open Classical in

def wmUnitChar : ∀ w : rowSG Pr sel mu, (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* X.Kˣ := fun w =>
  if h : w.1 ∈ Pr.vGs then (chiAt Ch ⟨w.1, h⟩ (R.m - 1))⁻¹ else resChar (mu : Chr X.F X.E X.K) w.1

abbrev ThM (P : LevFam X.E X.K R.r Pr.vGs) : Type :=
  WmTh X.E X.K R.r R.nV (rowSG Pr sel mu) (mtGSD W Ch sel mu P R.m).V (wmGSD W sel mu P).V

def wmKer (P : LevFam X.E X.K R.r Pr.vGs) (th : ThM W Ch sel mu P) (d : (mtGSD W Ch sel mu P R.m).D)
    (d' : (wmGSD W sel mu P).D) : (mtGSD W Ch sel mu P R.m).V →ₗ[X.K] (wmGSD W sel mu P).V :=
  th (rowSG Pr sel mu) d' d (wmPhi (wmLoc sel mu Ch P) d' d)

def GSD.wmCls {K : Type} [Field K] [NumberField K] [StarRing K] (S S' : GSD K) (h : S.Ok) (k : S.D → S'.D → (S.V →ₗ[K] S'.V)) :
    S.EqFun →ₗ[K] (S'.D → S'.V) where
  toFun φ d' := letI := h.fintypeCl
    ∑ c, (((S.toCSD h).wt c : K))⁻¹ • k (S.outSec.rep c) d' ((φ : S.D → S.V) (S.outSec.rep c))
  map_add' φ ψ := by
    funext d'
    simp only [Submodule.coe_add, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext d'
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_comm]

def thetaP (P : LevFam X.E X.K R.r Pr.vGs) (th : ThM W Ch sel mu P) (h : (mtGSD W Ch sel mu P R.m).Ok) :
    (mtGSD W Ch sel mu P R.m).EqFun →ₗ[X.K] ((wmGSD W sel mu P).D → (wmGSD W sel mu P).V) :=
  GSD.wmCls (mtGSD W Ch sel mu P R.m) (wmGSD W sel mu P) h (wmKer W Ch sel mu P th)

end Theta

section Z

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def mtPts : DecoPts (mtKGSD W Ch sel mu R.m) X.E R.nV ∅ (rowSG Pr sel mu) where
  pts := Equiv.refl _
  hom := FormG.incl _
  pts_smul := fun _ _ => rfl

end Z

section NbFun

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]

def nbFun (P : Ideal (𝓞 E)) (i : ℕ) : (DecoSet E n ST SG → V) →ₗ[K] (DecoSet E n ST SG → V) where
  toFun ψ d := ∑ d₁ ∈ d.heckeNb P i, ψ d₁
  map_add' ψ ψ' := by
    funext d
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext d
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

end NbFun

section Rel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Rel

end Formalism.L2.Col
