import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.BlockTheory.EvidentLattices.LatticeLetterSources
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq

section
open CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM
open GlobalTheory

namespace GlobalTheory

end GlobalTheory
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)
open GlobalTheory.SecTransport GlobalTheory.SecTieEx

namespace GlobalTheory.FramedCMPointCompare

section Bundles

variable {X X' Y : Scheme.{0}}

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l}

section Letters

variable [StarRing (𝓞 E)] {nΨ n' : ℕ}

def srcEquiv (o : LamObj c nΨ n') :
    (Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g) ≃ IndefiniteRowSideFullHecke.LatticeLetterSources.FinalTheorems o :=
  Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)

def lettersEquiv (o : LamObj c nΨ n') : LamLetters o ≃ IndefiniteRowSideFullHecke.LatticeLetterSources.LamLetters o where
  toFun L := ⟨L.m, L.e, fun k => srcEquiv o (L.src k), L.U, L.ℓ⟩
  invFun L := ⟨L.m, L.e, fun k => (srcEquiv o).symm (L.src k), L.U, L.ℓ⟩
  left_inv L := by simp only [Equiv.symm_apply_apply]
  right_inv L := by simp only [Equiv.apply_symm_apply]

variable {o : LamObj c nΨ n'}


end Letters

section Data

variable {Dw : Datum H} {Xo : Moduli Dw l}

def embEquiv {F : Type} [Field F] (σ₀ : F →+* ℂ) (K : Type) [Field K] [Algebra F K] :
    (K →ₐ[F] CAt σ₀) ≃ {σ : K →+* ℂ // σ.comp (algebraMap F K) = σ₀} where
  toFun σ := ⟨σ.toRingHom, RingHom.ext fun a => σ.commutes a⟩
  invFun σ := ⟨σ.1, fun a => RingHom.congr_fun σ.2 a⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Data

variable {D : D7}

theorem fdeg_host (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

end GlobalTheory.FramedCMPointCompare
end
end
