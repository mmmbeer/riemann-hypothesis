import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.UniformizationClosedSplit

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ModelAtPrimeToLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}



theorem hasModel_iff (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) :
    HasModel Xo c T io ↔
      ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β) (b : O →+* T.V),
        Y.N3 ∧ (algebraMap T.V T.Fr).comp b = io.comp β := by
  constructor
  · rintro ⟨O, i, β, b, Y, hb, h3⟩
    exact ⟨O, i, β, Y, b, h3, RingHom.ext hb⟩
  · rintro ⟨O, i, β, Y, b, h3, hb⟩
    exact ⟨O, i, β, b, Y, fun x => RingHom.congr_fun hb x, h3⟩


def HasModelPush (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (b : O →+* T.V) (Y : Model Xo c β),
    (∀ x : O, algebraMap T.V T.Fr (b x) = io (β x)) ∧ Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L

def ModelAtBare (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), Y.N3 ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β

theorem modelAtBare_of_modelAtSt {Xo : Moduli Dw l} {c : Coeff l} {la : HeightOneSpectrum (𝓞 c.F)}
    (h : ModelAtSt Xo c la) : ModelAtBare Xo c la := by
  obtain ⟨O, i, β, Y, h3, -, hb⟩ := h
  exact ⟨O, i, β, Y, h3, hb⟩







variable (Xo : Moduli Dw l) (c : Coeff l)

def ModelAtPush : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModelPush Xo c T io

def ModelOverLevelPush : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ¬ PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModelPush Xo c T io

def UnifAtFin : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
      ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G

def UnifAtInf : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ¬ T.FinRes →
      ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G

theorem unifAt_iff : UnifAt Xo c ↔ UnifAtFin Xo c ∧ UnifAtInf Xo c := by
  constructor
  · intro h
    exact ⟨fun la hla T io e ho _ => h la hla T io e ho, fun la hla T io e ho _ => h la hla T io e ho⟩
  · rintro ⟨h₁, h₂⟩ la hla T io e ho
    by_cases hT : T.FinRes
    · exact h₁ la hla T io e ho hT
    · exact h₂ la hla T io e ho hT

theorem unifOfModel_iff : UnifOfModel Xo c ↔
    ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N3 →
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V), (algebraMap T.V T.Fr).comp b = io.comp β →
        ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1),
          (∃ S : SplitExt (Sp (IsLocalRing.ResidueField T.V)),
            S.IsGt ((Over.pullback (spMap (IsLocalRing.residue T.V))).obj I.G.G)) →
          ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso := by
  constructor
  · intro h O i β Y h3 T io b hb
    exact h T io ((hasModel_iff Xo c T io).2 ⟨O, i, β, Y, b, h3, hb⟩)
  · intro h T io hm
    obtain ⟨O, i, β, Y, b, h3, hb⟩ := (hasModel_iff Xo c T io).1 hm
    exact h O β Y h3 T io b hb

end General

section Instance

variable {D : D7} {T : Top D}


theorem one_le_rank (h : LawsP T) {j : ℕ} (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have h3 := D.R.m_add_three_le_k
  simp only [Ranks.sigW]
  omega

end Instance

def ModelAtAll : Prop :=
  ∀ (D : D7) (T : Top D), LawsP T → ∀ j, InR D j → ∀ la, ModelAtSt (T.Q.Xo j) T.Q.c la

def ModelAtCore : Prop :=
  ∀ (D : D7) (T : Top D), LawsP T → ∀ j, InR D j → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
    ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ModelAtBare (T.Q.Xo j) T.Q.c la

theorem ModelAtAll.core (h : ModelAtAll) : ModelAtCore :=
  fun D T hT j hj la _ => modelAtBare_of_modelAtSt (h D T hT j hj la)









section Full

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem unifOfModel_of (hE : ExtVStatement) (hC : Out.CubePullSt) (Xo : Moduli Dw l) (c : Coeff l) :
    UnifOfModel Xo c :=
  (unifOfModel_iff Xo c).2 fun _ _ _ Y h3 T io b hb y I hS =>
    PullbackSections.unifAtInt_of_model hE hC Y h3 T io b hb y.1 I hS

theorem unifOfModel (Xo : Moduli Dw l) (c : Coeff l) : UnifOfModel Xo c :=
  unifOfModel_of GlobalTheory.ModelUniqueChecks.extV_holds Out.proved_CubePullSt Xo c

end Full



theorem statement_iff : Statement ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
      ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ModelAt Xo c :=
  ⟨fun h E _ _ _ H Dw hr l Xo c => (h E H Dw hr l Xo c).1,
    fun h E _ _ _ H Dw hr l Xo c => ⟨h E H Dw hr l Xo c, unifOfModel Xo c⟩⟩


end GlobalTheory.Proof.ModelAtPrimeToLevel
