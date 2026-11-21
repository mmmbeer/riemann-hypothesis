import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.EtaleLevelHecke

def ModelExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (Model b N)

def ModelProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.CompactB → ∀ M : Model b N, IsProjOver M.s

def EtLevForget : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (E : EtModel b N w0 r) (E' : EtModel b N' w0 r), ∃ π : E'.X ⟶ E.X, π ≫ E.s = E'.s ∧ IsFinite π ∧ Etale π ∧ ∃ m : ObjMap (E'.univ.forget N hd hc) E.univ π, ∀ y, (E'.lv y).left ≫ m.φ = π ≫ (E.lv y).left

def GenCmp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _)

end GlobalTheory.EtaleLevelHecke
