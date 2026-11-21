import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace GlobalTheory.Formalism.L2.Col

open _root_.Formalism.BasicNotions _root_.Formalism.L2.Host _root_.Formalism.L2.DIV _root_.Formalism.FrobeniusOrbits

export _root_.Formalism.L2.Col (
  Chars Chars.FromHecke Chars.Ok Chars.Tied Dat Dat.Ok FQ_le_EQ Fields Fields.Core Fields.IsCond Fields.Kq Fields.Ok
  Fields.Ok.core Fields.Ok.f_pos Fields.AbelianUnramifiedExtensionConditions Fields.AbelianUnramifiedExtensionConditions.eight_le_f Fields.AbelianUnramifiedExtensionConditions.f_even Fields.AbelianUnramifiedExtensionConditions.four_dvd_f
  Fields.AbelianUnramifiedExtensionConditions.two_le_f Fields.conjO Fields.embBar Fields.embC Fields.f Fields.sig IsEtaT IsMu0 Primes Primes.Ok
  Primes.PiGCong Primes.PiGCong.g_cong Primes.natCast_dvd_intCast Primes.vG Primes.vGs Primes.vT Primes.vTbar QDat
  QDat.HasBase QDat.Off QDat.Ok QDat.TiedTo QDat.empty RowPar RowPar.aMinusRev RowPar.aPlus RowPar.bAt RowPar.dV
  RowPar.eAt RowPar.lamV RowPar.lamVQ RowPar.of RowPar.pOf RowPar.qOf RowPar.sg RowPar.sgHC RowPar.sgQ RowPar.sgTrue
  RowPar.vb Sizes Sizes.T_big Sizes.T_spread Sizes.T_spread_true Sizes.a_pos Sizes.spread_le_N Sizes.two_spread_lt Wts
  Wts.Ok Wts.aTop Wts.bTop Wts.deg Wts.degTrue Wts.lamN Wts.lamTrue Wts.lamV Wts.nuW Wts.sgTrue Wts.sgW divs embQ fin_EQ
  fin_F1Q fin_FQ fin_adjoin fin_sqQ finite_pow_eq fintypePsi hostFields hostTops map_le_of_normal normal_EQ normal_F1Q
  normal_adjoin normal_of_map_le normal_sqQ normal_sup' ofQ shiftW spread_shiftW two_le_N)

def quadFields (K : Type) [Field K] [NumberField K] [IsCMField K] : Fields where
  F := ℚ
  E := K
  K := K
  starE := IsCMField.starRing K
  starK := IsCMField.starRing K
  Tau := Unit
  emb := fun _ => RingHom.id K


instance isCyclotomicExtension_gauss : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
  CyclotomicField.isCyclotomicExtension 4 ℚ



def Wts.const {X : Fields} (Word : Type) {R : Ranks} (P : X.Tau → HCParam R) (tops : Finset X.Tau) : Wts X Word R :=
  ⟨fun τ => RowPar.of (P τ), fun _ τ => P τ, tops⟩



def QDat.OverOnePrime {X : Fields} (Z : QDat X) (p : ℕ) : Prop :=
  ∀ P ∈ Z.Q, ∀ P' ∈ Z.Q, ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 X.E) ∈ P'.asIdeal →
    P.asIdeal.comap (RingOfIntegers.mapRingHom X.Kq.subtype) = P'.asIdeal.comap (RingOfIntegers.mapRingHom X.Kq.subtype)

example : GlobalTheory.Formalism.L2.Col.Dat = _root_.Formalism.L2.Col.Dat := rfl

example {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) (j : ℕ) (τ : X.Tau) (i : Fin (R.N j)) :
    (W.lamTrue u j τ).w i + (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) = (W.lamN u j τ).w i := by
  simp [Wts.lamTrue, shiftW]

example : (ofQ ![(3 : ℚ), 1]).w 0 = 3 := by
  have h : Antitone ![(3 : ℚ), 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  simp [ofQ, h]

example : divs (1 : ℤ) = ∅ := by
  ext P
  have h : {P : HeightOneSpectrum ℤ | (1 : ℤ) ∈ P.asIdeal} = ∅ :=
    Set.eq_empty_of_forall_notMem fun P hP => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hP)
  simp [divs, h]

end GlobalTheory.Formalism.L2.Col
