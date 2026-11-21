import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.LocalUnitNormIndex.LocalUnitNormIndex

section
noncomputable section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Lbc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def fixT (N : ℕ) (θ : MulAut (GL (Fin N) k)) : Subgroup (Tor k N) :=
  (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id _)).comap (Tor k N).subtype

variable (k) in

def orbSet (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (t δ : GL (Fin N) k) :
    Set (Tor k N ⧸ (fixT k N θ ⊔ J.subgroupOf (Tor k N))) :=
  {q | ∃ s : Tor k N, (s : Tor k N ⧸ (fixT k N θ ⊔ J.subgroupOf (Tor k N))) = q ∧
    ∃ κ ∈ J ⊓ Tor k N, (s : GL (Fin N) k)⁻¹ * δ * θ s = t * κ}

variable (k) in

def V2 : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k),
    admitted k N J θ l → GoodT k N J θ l t →
    ∀ [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
      [MeasurableMul₂ (GL (Fin N) k)] [MeasurableInv (GL (Fin N) k)]
      (μG : Measure (GL (Fin N) k)) [μG.IsHaarMeasure] [SFinite μG],
    ∀ δ ∈ Tor k N, IncrV k N (tnorm θ l δ) →
    ∀ (μδ : Measure (twCent θ.toMonoidHom δ)) [μδ.IsHaarMeasure],
      twOrbIntegral θ.toMonoidHom μG δ μδ (Set.indicator (dcos J t) 1) =
        ((orbSet k N J θ t δ).encard : ℝ≥0∞) * μG J / μδ {x | (x : GL (Fin N) k) ∈ J}

variable (k) in

def TwistClassVanishing : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k),
    admitted k N J θ l → GoodT k N J θ l t →
    ∀ [MeasurableSpace (GL (Fin N) k)] (μG : Measure (GL (Fin N) k)) (δ : GL (Fin N) k)
      (μδ : Measure (twCent θ.toMonoidHom δ)),
      (¬ ∃ g : GL (Fin N) k, ∃ κ ∈ J ⊓ Tor k N, twConj θ.toMonoidHom g δ = t * κ) →
      twOrbIntegral θ.toMonoidHom μG δ μδ (Set.indicator (dcos J t) 1) = 0

def sigmaAut {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℕ) (σ : E ≃ₐ[F] E) :
    MulAut (GL (Fin n) E) where
  toFun := sigmaGL σ
  invFun := sigmaGL σ.symm
  left_inv g := by ext i j; simp [sigmaGL_val]
  right_inv g := by ext i j; simp [sigmaGL_val]
  map_mul' := map_mul _

end PositivityTheory.Lbc

end
end

section
noncomputable section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Lbc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def TwCentTor : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ),
    admitted k N J θ l → ∀ δ ∈ Tor k N, IncrV k N (tnorm θ l δ) →
    ∀ g : GL (Fin N) k, g ∈ twCent θ.toMonoidHom δ ↔ (g ∈ Tor k N ∧ θ g = g)

def TwClassUnique : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (δ δ₀ : GL (Fin n) E), IsTwRegSemisimple σ δ →
      (∃ h : GL (Fin n) E, normGL σ δ = h * normGL σ δ₀ * h⁻¹) → TwConjugate (sigmaGL σ) δ₀ δ

end PositivityTheory.Lbc

end
end
