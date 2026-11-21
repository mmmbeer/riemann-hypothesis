import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

def P_contr_id : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ) (y : Fin n → ℤ)
    (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0),
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * m = tdiag ϖ y * τ

def P_contr_tw : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ)
    (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0),
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * thL n w m = tdiag ϖ y * τ

def DiagonalConjDistinctValuations : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (v : Fin n → ℤ) (hv : Function.Injective v) (d d' h : GLw n w)
    (hd : (∀ i j : Fin n, i ≠ j → d.val i j = 0) ∧ ∀ i, ordL (d.val i i) = v i)
    (hd' : (∀ i j : Fin n, i ≠ j → d'.val i j = 0) ∧ ∀ i, ordL (d'.val i i) = v i)
    (hh : h⁻¹ * d * h = d'),
    d = d' ∧ ∀ i j : Fin n, i ≠ j → h.val i j = 0

def Hilbert90InertPlace : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w),
    (∀ u : w.adicCompletion E, Valued.v u = 1 → cj w u = u → ∃ z, Valued.v z = 1 ∧ z * cj w z = u) ∧
    (∀ u : w.adicCompletion E, u * cj w u = 1 → ∃ z, Valued.v z = 1 ∧ u * cj w z = z)

def P_iwU_facts : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ),
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧
    IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0}

def TwistedDoubleCosetStrictDiagonal : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ) (y : Fin a → ℤ)
    (hy : StrictAnti y) (δ : GLw a w) (hP : ∃ p : GLw a w, dcos a w (tdiag ϖ y) (p⁻¹ * δ * thL a w p) ≠ 0),
    (∃ p₀, OneCoset (thL a w) (iwGL a w) δ {g | dcos a w (tdiag ϖ y) g ≠ 0} p₀) ∧
      CentOK (thL a w) (GlobalTheory.LFun.KGL w a) (iwGL a w) δ ∧ HasVals (nrmL a w δ).val.charpoly (nv y)

def UnitaryHeckeSingleCoset : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ : UL n w)
    (hP : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0),
    (∃ p₀, OneCoset (MonoidHom.id (UL n w)) (iwU n w b) γ {g | fU n w b ϖ l g ≠ 0} p₀) ∧
      CentOK (MonoidHom.id (UL n w)) (KL n w) (iwU n w b) γ ∧ HasVals γ.1.val.charpoly (wexp n l)

def P_asmReg : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)),
    RegAt2 a (n - a) w (phiX n w b ϖ x a)

end PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
