import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.UnitaryGroupLocal
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP

section
noncomputable section

namespace Formalism.L2.SG.Pf.Lem3Mass

open Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds Filter Topology

section Alg

variable {R : Type} [CommRing R] [StarRing R] {m : ℕ}

def Mult (c : R) (N : ℕ) : Set (Matrix (Fin m) (Fin m) R) := {X | ∃ W, X = c ^ N • W}

variable {c : R}

end Alg

section Top

variable {R : Type} [CommRing R] [StarRing R] [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R]
  [CompactSpace R] [T2Space R] {m : ℕ}

instance compactSpace_matR : CompactSpace (Matrix (Fin m) (Fin m) R) :=
  inferInstanceAs (CompactSpace (Fin m → Fin m → R))

instance t2SpaceMatrix : T2Space (Matrix (Fin m) (Fin m) R) := inferInstanceAs (T2Space (Fin m → Fin m → R))

end Top

end Formalism.L2.SG.Pf.Lem3Mass
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.Lem3Mass

open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnitaryGroupLocal
open NumberField IsDedekindDomain Topology Matrix Filter Formalism.HermitianLatticeCounting.LatticeSumBounds

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

def IntM {m : ℕ} (X : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i k, X i k ∈ Formalism.MainNotions.UnitaryGroupLocal.oE v

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (x : E ⊗[F] v.adicCompletion F) :
    PI.UnitaryApproxDefs.sigR σ _ (PI.UnitaryApproxDefs.sigR σ _ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e r => simp [PI.UnitaryApproxDefs.sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

def starO (hσ : ∀ e, σ (σ e) = e) : StarRing (Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v) where
  star x := ⟨PI.UnitaryApproxDefs.sigR σ _ x, Formalism.MainNotions.UnitaryGroupLocal.sigR_mem v σ x.2⟩
  star_involutive x := Subtype.ext (sigR_sigR v σ hσ x)
  star_mul x y := Subtype.ext (by
    show PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)
        ((x : E ⊗[F] v.adicCompletion F) * (y : E ⊗[F] v.adicCompletion F)) =
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (y : E ⊗[F] v.adicCompletion F) *
        PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (x : E ⊗[F] v.adicCompletion F)
    rw [map_mul, mul_comm])
  star_add x y := Subtype.ext (map_add _ _ _)

variable {m : ℕ}

def up : Matrix (Fin m) (Fin m) (Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v) →+*
    Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F) :=
  (Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v).subtype.mapMatrix

def down (X : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) (hX : IntM v X) :
    Matrix (Fin m) (Fin m) (Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v) := fun i k => ⟨X i k, hX i k⟩

end Formalism.L2.SG.Pf.Lem3Mass
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.Lem3Mass

open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnitaryGroupLocal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

section Trace

variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)

def trF (y : E) : F :=
  Classical.choose (hfix (y + σ y) (by rw [map_add, hσ, add_comm]))

theorem trF_spec (y : E) : algebraMap F E (trF σ hσ hfix y) = y + σ y :=
  Classical.choose_spec (hfix (y + σ y) (by rw [map_add, hσ, add_comm]))

theorem trF_add (y z : E) : trF σ hσ hfix (y + z) = trF σ hσ hfix y + trF σ hσ hfix z := by
  apply (algebraMap F E).injective
  rw [map_add, trF_spec, trF_spec, trF_spec, map_add]
  abel

theorem trF_smul (c : F) (y : E) : trF σ hσ hfix (c • y) = c * trF σ hσ hfix y := by
  apply (algebraMap F E).injective
  rw [map_mul, trF_spec, trF_spec, Algebra.smul_def, map_mul, AlgHom.commutes, mul_add]

def trA : E ⊗[F] v.adicCompletion F →ₗ[F] v.adicCompletion F :=
  TensorProduct.lift (LinearMap.mk₂ F (fun (e : E) (r : v.adicCompletion F) => trF σ hσ hfix e • r)
    (fun e e' r => by rw [trF_add, add_smul])
    (fun c e r => by rw [trF_smul, mul_smul])
    (fun e r r' => by rw [smul_add])
    (fun c e r => by rw [smul_comm]))

end Trace

section D1

variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)

theorem coe_algebraMap_int (t : 𝓞 F) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E (t : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]

end D1

end Formalism.L2.SG.Pf.Lem3Mass
end
end
