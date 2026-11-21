import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.FrobSerSt

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

section Closed

variable {C : Type} [Field C]

def PsiCurveFBSt : Prop :=
  AllFB fun C _ V _ I _ dd X => X.RankHyp → ∀ _H : ∀ g, X.CartHyp V g, X.AltC → ∀ g,
    ∃ M : JJ I g → JJ I g → C, (∀ q' q, V.Ge 0 (M q' q)) ∧
      ∀ x ∈ X.TySet V g, ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C),
        IsCv V γ → IsCv V lam →
        (∀ i, alongCv γ (X.lg i) =
          ∑ c : I g, X.u g c i • tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inl c))) →
        (∀ q : JJ I g, tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inr q)) =
          lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
            ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
              X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inl c)) else 0) →
        (∀ i, ∀ m < V.l ^ 2, PowerSeries.coeff m (γ i) = 0) →
        (∀ i, V.MM (PowerSeries.coeff (V.l ^ 2) (γ i))) →
        ∀ q, V.MM (PowerSeries.coeff V.l (lam q) ^ V.l -
          ∑ q', PowerSeries.coeff (V.l ^ 2) (lam q') * M q' q)

end Closed

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Geo

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.nmul (Y : FBChart C V O dd) : ℕ → Pt C 1 dd
  | 0 => fun _ => 0
  | k + 1 => addOf Y.B.G.F (Y.nmul k) (pt C dd 0)

def FBChart.u2 (Y : FBChart C V O dd) : PS C 2 dd :=
  FB.expS C (ev (n := 2) ![pt C dd 0, comp1 (Y.nmul V.l) (pt C dd 1)] Y.h - MvPowerSeries.C (V.l : C) * Y.h)

def FBChart.cS (Y : FBChart C V O dd) (j : Fin dd) : PS C 2 dd :=
  ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (Y.sgP (Pi.single j 1)) -
    ev (n := 2) ![pt C dd 0] (Y.sgP (Pi.single j 1)) - ev (n := 2) ![pt C dd 1] (Y.sgP (Pi.single j 1))

end Geo

section Closed

def UnitSeriesFrobenius : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (μ : Fin 2 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((1 : Fin 2), i)) →
      V.MM (MvPowerSeries.coeff μ Y.u2)

end Closed

end Formalism.L2.FormalSeriesBounds
end
end
