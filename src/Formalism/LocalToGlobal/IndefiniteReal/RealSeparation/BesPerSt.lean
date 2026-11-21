import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scalar

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def PsiRat (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  ∀ x : D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D x)) = 1

def IsEmbHom (ι : A.V →ₗ[D.host.E] B.V) (s : GA D A →* GA D B) : Prop :=
  ∀ h, EmbRel B A ι (s h) h

def IsQuotPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ

def IsNPair (d : BesDat A B ι) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) : Prop :=
  μN.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B d.e) 𝓕N μN ∧ μN 𝓕N = 1

def besIntd (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (φ : GA D A → ℂ)
    (F : GA D B → ℂ) (h : GA D A) (n : NFlag B d.e) : ℂ :=
  φ h * F ((n : GA D B) * s h * (d.y : GA D B)) * star (besChar ψ d (n : GA D B))

def IsBesPer (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) (φ : GA D A → ℂ) (F : GA D B → ℂ)
    (b : ℂ) : Prop :=
  (∀ h, IntegrableOn (besIntd ψ d s φ F h) 𝓕N μN) ∧
    IntegrableOn (fun h => ∫ n in 𝓕N, besIntd ψ d s φ F h n ∂μN) 𝓕 μ ∧
    b = ∫ h in 𝓕, ∫ n in 𝓕N, besIntd ψ d s φ F h n ∂μN ∂μ

def BesStd (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) : Prop :=
  Continuous ψ ∧ PsiRat ψ ∧ HSpace.IsIsomEmb A B ι ∧ IsAniso A ∧ IsEmbHom ι s ∧ IsQuotPair A μ 𝓕 ∧
    IsNPair d μN 𝓕N

end Scalar

section Vec

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def rTrLin (V : HSp D) (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SobContN {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Lie : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (N : ℕ) (ℓ : H →ₗ[ℂ] ℂ) : Prop :=
  ∃ (L : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ X ∈ l, X ∈ Lie) ∧
    ∀ w, SmoothVec Lie σ w → ‖ℓ w‖ ≤ C * (L.map fun l => ‖l.foldr (dRep σ) w‖).sum

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  {Vt : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
  {S : D.what₂.Tau → SPar}

open Classical in

def IsColMap (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ))
    (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) : Prop :=
  (∀ v, IsAutFun A (Φ v)) ∧
    ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∀ v : ∀ τ, Vt τ,
      Φ (Function.update v τ (π τ h (v τ))) = rTr A (atTau θ A τ h) (Φ v)

open Classical in

def IsBesForm (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (M : DSModel B S) (N : ℕ)
    (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)) : Prop :=
  (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∀ (v : ∀ τ, Vt τ) (x : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ (infMat D.sp.cm.sig B.gram (θ τ) (s (atTau θ A τ h))) (x τ) →
      ℓ (Function.update v τ (π τ h (v τ))) (Function.update x τ w) = ℓ v x) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ), atTau θ B τ g ∈ NFlag B d.e →
      ∀ (v : ∀ τ, Vt τ) (x : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (x τ) →
      ℓ v (Function.update x τ w) = besChar ψ d (atTau θ B τ g) * ℓ v x) ∧
    ∀ τ (v : ∀ τ, Vt τ) (x : M.Vec), ∃ L : M.H τ →ₗ[ℂ] ℂ, SobContN (lieAt B τ) (M.rep τ) N L ∧
      ∀ w : M.sm τ, L w = ℓ v (Function.update x τ w)

open Classical in

def UnifSob (M : DSModel B S) (N : ℕ) (T : MMap M) : Prop :=
  ∀ Ω : Set (GA D B), IsCompact Ω → ∀ τ (x : M.Vec),
    ∃ (L : List (List (Matrix (Fin B.rank) (Fin B.rank) ℂ))) (C : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ X ∈ l, X ∈ lieAt B τ) ∧
      ∀ g ∈ Ω, ∀ w : M.sm τ, ‖T (Function.update x τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum

end Vec

end Formalism.IndefR.Mi

end
