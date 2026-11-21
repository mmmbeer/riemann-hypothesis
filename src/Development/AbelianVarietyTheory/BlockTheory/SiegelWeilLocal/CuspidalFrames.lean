import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open MeasureTheory NumberField
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames

open Formalism.MainNotions.S GlobalTheory.Count

def IsCuspidalFrame (B : RowsAut) (Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) : Prop :=
  (∀ i, T i ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
    (∀ i, T i ∈ B.I.HomS B.σs B.μf B.fund B.R) ∧
    (∀ i u, ‖T i u‖ = ‖u‖) ∧
    (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧
    Submodule.span ℂ (Set.range T) = B.I.eHom B.σs B.μf B.fund B.R B.Re ∧
    (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) ∧
    (∀ i u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T i u) = T i u) ∧
    Orthonormal ℂ (fun i => T i (B.tens B.w)) ∧
    Submodule.span ℂ (Set.range fun i => T i (B.tens B.w)) = LinearMap.range Rφ.toLinearMap

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames
