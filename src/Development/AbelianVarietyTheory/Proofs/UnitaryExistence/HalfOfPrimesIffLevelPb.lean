import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients

noncomputable section

namespace GlobalTheory.ParAtCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

theorem isHalf_of_level (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.IsHalf D l.Mb :=
  ⟨l.fromK, hl.1 ▸ l.prod, l.coprime⟩

theorem levelAt_Mb (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.levelAt D l.Mb (isHalf_of_level D l hl) = l := by
  obtain ⟨M, h3, hodd, Mb, hK, hp, hc, A, hA⟩ := l
  obtain ⟨h1, h2⟩ := hl
  dsimp only at h1 h2
  subst h1 h2
  rfl

theorem levelAt_spec (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : HalfLevelCoefficients.IsHalf D Mb) :
    (HalfLevelCoefficients.levelAt D Mb h).M = D.host.g 0 * D.host.g 1 ∧ (HalfLevelCoefficients.levelAt D Mb h).A = 1 :=
  ⟨rfl, rfl⟩

def levelEquivHalf (D : D7) :
    {l : Level (hostOfRecord D) // l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1} ≃
      {Mb : Ideal (𝓞 D.host.E) // HalfLevelCoefficients.IsHalf D Mb} where
  toFun l := ⟨l.1.Mb, isHalf_of_level D l.1 l.2⟩
  invFun Mb := ⟨HalfLevelCoefficients.levelAt D Mb.1 Mb.2, levelAt_spec D Mb.1 Mb.2⟩
  left_inv l := Subtype.ext (levelAt_Mb D l.1 l.2)
  right_inv _ := rfl


theorem levelPb_iff (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) :
    LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb) := by
  constructor
  · rintro ⟨l, hl, hb⟩
    have h := isHalf_of_level D l hl
    rw [hb] at h
    exact h
  · intro h
    exact ⟨HalfLevelCoefficients.levelAt D _ h, levelAt_spec D _ h, rfl⟩

end GlobalTheory.ParAtCompare
