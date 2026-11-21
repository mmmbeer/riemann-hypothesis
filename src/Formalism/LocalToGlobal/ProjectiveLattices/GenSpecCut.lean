import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable (Xo c) in

def GenSpecSt (hG : GenFrEx Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (m : Ideal p.R) [m.IsMaximal],
    ∃ (Z : Comp Xo c) (q : TRing c.F) (yq : FrPt Xo c q.R),
      (∃ (p' : TRing c.F) (lam : p.R →ₐ[c.F] p'.R) (a : q.R →ₐ[c.F] p'.R)
          (μ : p'.R →ₐ[c.F] Localization.AtPrime m) (y' : FrPt Xo c p'.R),
        FrMap lam y y' ∧ FrMap a yq y' ∧ μ.comp lam = locM c.F m) ∧
      ∀ (p₀ : TRing c.F) (φ₀ : p₀.R →ₐ[c.F] Om Z) (y₀ : FrPt Xo c p₀.R), FrMap φ₀ y₀ (genFr hG Z) →
        ∃ (B : TRing c.F) (β : q.R →ₐ[c.F] B.R) (β₀ : p₀.R →ₐ[c.F] B.R) (yB y₀B : FrPt Xo c B.R)
          (tB : Ix Dw → (B.R)ˣ) (Ω : Type) (_ : Field Ω) (_ : Algebra c.F Ω)
          (κ : Om Z →ₐ[c.F] Ω) (γ : B.R →ₐ[c.F] Ω),
          FrMap β yq yB ∧ FrMap β₀ y₀ y₀B ∧ FrBor tB y₀B yB ∧ γ.comp β₀ = κ.comp φ₀ ∧
            Function.Injective (γ.comp β)

theorem evR_of_frMap (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R}
    {w : FrPt Xo c S} (hy : FrMap φ y w) : evR Xo c f w = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hy⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact hW f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec hy


end Gen

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}


end Formalism.L2.Pj
end
end

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def SepXSt : Prop := IsSeparated Xo.s

variable {Xo c}

variable (Xo c) in

def FrGenChartSt (hG : GenFrEx Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (m : Ideal p.R) [m.IsMaximal],
    ∃ (Z : Comp Xo c) (q : TRing c.F) (yq : FrPt Xo c q.R),
      (∃ (p' : TRing c.F) (lam : p.R →ₐ[c.F] p'.R) (a : q.R →ₐ[c.F] p'.R)
          (μ : p'.R →ₐ[c.F] Localization.AtPrime m) (y' : FrPt Xo c p'.R),
        FrMap lam y y' ∧ FrMap a yq y' ∧ μ.comp lam = locM c.F m) ∧
      ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra c.F Ω) (κ : Om Z →ₐ[c.F] Ω) (γ : q.R →ₐ[c.F] Ω)
        (w w₀ : FrPt Xo c Ω) (t : Ix Dw → Ωˣ),
        Function.Injective γ ∧ FrMap γ yq w ∧ FrMap κ (genFr hG Z) w₀ ∧ FrBor t w₀ w

end Formalism.L2.Pj
end
end
