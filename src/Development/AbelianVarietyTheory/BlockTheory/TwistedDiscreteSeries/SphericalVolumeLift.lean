import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift

open scoped ComplexConjugate InnerProductSpace Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.AutMult GlobalTheory.Cont
open GlobalTheory.Mem.Th (CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev FinPl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

abbrev RealMat (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

section Vectors

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : RealMat S) (sT : RealMat T)

def IsFockVec (Φ : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T Φ ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N →
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) Φ = 0

def IsSphOff (LS : Lat S) (LT : Lat T) (Sf : Finset (FinPl D)) (Φ : WO S T → ℂ) : Prop :=
  IsLatVac (heisO ψ S T) (latO S T LS LT fun v => v ∉ Sf) Φ

def IsCoef {X : Type} (x : X → WO S T → ℂ) (Φ : WO S T → ℂ) (c : X → ℂ) : Prop :=
  ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧
    ∀ p, c p = ∫ w in 𝓕, x p w * conj (Φ w) ∂μ

end Vectors

section Kernel

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
  (sA : RealMat A) (sB : RealMat B)

def IsKernelPair (o : Bool) (P : (WO B A → ℂ) → Prop) (Q : (WO A B → ℂ) → Prop) (K₁ K₂ : GA D A → GA D B → ℂ)
    (c : GA D A → ℂ) : Prop :=
  match o with
  | true => ∃ (om : GA D B × GA D A →* Module.End ℂ (WO B A → ℂ)) (Φ₁ Φ₂ : WO B A → ℂ),
      IsWeilDatumO ψ B A χB χA om ∧ IsFockVec ψ θ B A sB sA Φ₁ ∧ IsFockVec ψ θ B A sB sA Φ₂ ∧ P Φ₁ ∧ P Φ₂ ∧
      (∀ g h, K₁ g h = thetaKO om h g Φ₁) ∧ (∀ g h, K₂ g h = thetaKO om h g Φ₂) ∧
      IsCoef B A (fun g : GA D A => om (1, g) Φ₁) Φ₂ c
  | false => ∃ (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (Φ₁ Φ₂ : WO A B → ℂ),
      IsWeilDatumO ψ A B χA χB om ∧ IsFockVec ψ θ A B sA sB Φ₁ ∧ IsFockVec ψ θ A B sA sB Φ₂ ∧ Q Φ₁ ∧ Q Φ₂ ∧
      (∀ g h, K₁ g h = conj (thetaKO om g h Φ₁)) ∧ (∀ g h, K₂ g h = conj (thetaKO om g h Φ₂)) ∧
      IsCoef A B (fun g : GA D A => om (g, 1) Φ₁) Φ₂ fun g => conj (c g)

variable {A B}

def lift (m : Measure (GA D A)) (K : GA D A → GA D B → ℂ) (f : GA D A → ℂ) : GA D B → ℂ :=
  fun h => petersson A m (fun g => K g h) f

def LiftConv (m : Measure (GA D A)) (ν : Measure (GA D B)) (K : GA D A → GA D B → ℂ) (f : GA D A → ℂ) : Prop :=
  (∀ h, Integrable (AutomorphicL2Unitary.descend (GQ A) fun g => K g h * conj (f g)) (autMeasure A m)) ∧ MemL2Quotient (GQ B) ν (lift m K f)

variable (B) in

def volQ (ν : Measure (GA D B)) : ℝ := (autMeasure B ν).real Set.univ

variable (A B) in

def HidaSetting (t : ℕ) (cA : CptF A) : Prop :=
  1 ≤ A.rank ∧ 1 ≤ t ∧ B.rank = A.rank + t ∧ IsInfFam θ ∧ HSpace.SigOK A ∧ IsCartanFrame A cA ∧
    (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) ∧ (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧
    ∀ τ, cA τ * sA τ = Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 * cA τ

end Kernel

def Convergent (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (o : Bool) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ)
    (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ),
    HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t →
    IsKernelPair ψ θ A B χA χB sA sB o (fun _ => True) (fun _ => True) K₁ K₂ c →
    m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA →
    LiftConv m ν K₁ f₁ ∧ LiftConv m ν K₂ f₂ ∧
      Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧
      petersson B ν (lift m K₁ f₁) (lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m

section Local

variable (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D))

def hgtW (w : InfinitePlace D.host.F) (g : Gw A w) : ℝ :=
  Doubling.hgtArch D.sp.cm.sig (Doubling.dblSp A).gram w (Formalism.UG.bc (compInf _ _ w) a)
    (Doubling.ioH _ D.sp.cm.sig (Doubling.gram_hdbl A) (g, 1))

def hgtV (v : FinPl D) (g : Gv A v) : ℝ :=
  Doubling.hgtFin D.sp.cm.sig (Doubling.dblSp A).gram L v (Doubling.ioH _ D.sp.cm.sig (Doubling.gram_hdbl A) (g, 1))

variable {Hs : Formalism.MainNotions.SchurIrreducible.Pl D.host.F → Type} [∀ v, NormedAddCommGroup (Hs v)] [∀ v, InnerProductSpace ℂ (Hs v)]
  (δ : ∀ v, GPl D.sp.cm.sig A.gram v →* (Hs v →L[ℂ] Hs v)) (x y : ∀ v, Hs v) (s₀ s : ℂ)

variable (Sf : Finset (FinPl D)) (ca : ∀ w, Gw A w → ℂ) (cf : ∀ v, Gv A v → ℂ) (ma : ∀ w, Measure (Gw A w))
  (mf : ∀ v, Measure (Gv A v))

end Local

example {A B : HSp D} (m : Measure (GA D A)) (K : GA D A → GA D B → ℂ) (f : GA D A → ℂ) (z : ℂ) (h : GA D B) :
    lift m K (z • f) h = conj z * lift m K f h := by
  simp only [lift, petersson, pet, AutomorphicL2Unitary.descend, Pi.smul_apply, smul_eq_mul, map_mul, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun q => by ring)

example {A B : HSp D} {t : ℕ} (hb : B.rank = A.rank + t) (ht : A.rank < t) : wittIndex B < t := by
  have := two_mul_wittIndex_le B
  omega

example {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : RealMat S} {sT : RealMat T} {LS : Lat S}
    {LT : Lat T} {Φ : WO S T → ℂ} (h : IsVacO ψ θ S T sS sT LS LT Φ) :
    IsFockVec ψ θ S T sS sT Φ ∧ IsSphOff ψ S T LS LT ∅ Φ := by
  refine ⟨⟨h.2.theta, 1, fun l hl => ?_⟩, by simpa [IsSphOff] using h.2.lat⟩
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
  exact h.2.fock p.1 p.2

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift

end
