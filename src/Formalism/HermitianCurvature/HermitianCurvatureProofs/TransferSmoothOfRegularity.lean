import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSmoothCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBesselEigen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFFName
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

noncomputable section

def ClassEigenC : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : NumberField.InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    100 ≤ Cc → JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∀ v : Fin S.f,
      Q.CkLev S.G.k S.G.r 0 (2 * S.G.r + S.G.k + 1) (Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z')
          (B.JF (T v).base (f v)) ∧
        ∀ (Y : ℝ), ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z',
          Q.CV S.G.k S.G.r (Y : ℂ) (B.JF (T v).base (f v)) g = ((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v) g

theorem class_eigenvalue_constant : ClassEigenC := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hCc hB v
  obtain ⟨_, _, _, hbuilt, _, _, _, _, _, hCk, hk2, hA, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, heig⟩ := hv v
  have hpos : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
  have hA' : 100 * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ := by
    calc 100 * ((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)
        = 100 * (((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)) := by ring
      _ ≤ Cc * (((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)) :=
          mul_le_mul_of_nonneg_right hCc hpos
      _ = Cc * ((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by ring
      _ ≤ A₀ := hA
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    Formalism.FourierDecayAlt.P.CutMP.thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA'
  have hW := Formalism.FourierDecayAlt.P.jacquet_derivative_formula S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) hThr (hCC _)
  refine ⟨hW.1, ?_⟩
  intro Y g hg
  have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
  have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) (f v) :=
    Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (hCk v)
  rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ p ∂(T v).base.μSS,
      JF.xiP (T v).base p • Q.CV S.G.k S.G.r (Y : ℂ) (B.rho (T v).base p (f v)) g =
        ((S.P v Y : ℝ) : ℂ) • (JF.xiP (T v).base p • B.rho (T v).base p (f v) g) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS (T v).base] with p hp
    rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ (T v).base (Y : ℂ) (f v) p hp hCkn _ hgG]
    have hs := Formalism.FourierDecayAlt.P.B7.sgs_mem (T v).base hp hgG
    simp only [B.rho]
    rw [heig Y _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

theorem mem_om_of_mem_omP {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    {g : B.Mat S.G.k S.G.r} (hgG : g ∈ B.GV S.G.k S.G.r) (hg : g ∈ OmP S T v) :
    g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := by
  refine ⟨hgG, ?_, hg.1⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l.val with h0 | hpos
  · have hl0 : l = 0 := Fin.ext h0
    subst hl0
    unfold Dmin
    have : IsEmpty (Fin ((0 : Fin (S.G.r + 2)) : ℕ)) := ⟨fun i => absurd i.isLt (by simp)⟩
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · have := hg.2 ⟨l.val - 1, by omega⟩
    have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (S.G.r + 2)) = l := Fin.ext (by simp; omega)
    simpa [e] using this

end

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

section
open Formalism.FourierDecayAlt MeasureTheory NumberField

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

noncomputable section

section cls

variable {r : ℕ} {TT : ℝ}

def smM (m : ℕ∞) : WithTop ℕ∞ := ((m : ℕ∞) : WithTop ℕ∞)

def smSubM (r : ℕ) (TT : ℝ) (m : ℕ∞) : Subalgebra ℂ (MA.Qp r TT → ℂ) where
  carrier := {f | ContDiffOn ℝ (smM m) (MA.ext f) (MA.Qset r TT)}
  mul_mem' {f g} hf hg := (hf.mul hg).congr fun x hx => by simp [MA.ext, hx]
  add_mem' {f g} hf hg := (hf.add hg).congr fun x hx => by simp [MA.ext, hx]
  algebraMap_mem' z := (contDiffOn_const (c := z)).congr fun x hx => by simp [MA.ext, hx]




end cls

section jets

variable {r : ℕ} {TT : ℝ}

def JetEq (m : ℕ∞) (q : MA.Qp r TT) (f g : MA.Qp r TT → ℂ) : Prop :=
  ∀ k : ℕ, (k : ℕ∞) ≤ m → iteratedFDeriv ℝ k (MA.ext f) q.1 = iteratedFDeriv ℝ k (MA.ext g) q.1

open scoped Classical in

def actJ (m : ℕ∞) (a : (MA.anQ r TT).Op) (u : MA.Qp r TT → ℂ) : MA.Qp r TT → ℂ :=
  fun q => if h : ∃ g : MA.SmQ r TT, JetEq m q g.1 u then (show MA.SmQ r TT from a (Classical.choose h)).1 q else 0

end jets

section ord

variable {r : ℕ} {TT : ℝ}

inductive Fac (r : ℕ) (TT : ℝ) : Type
  | mul (f : MA.SmQ r TT) : Fac r TT
  | eul (v : M.Var r) : Fac r TT

def Fac.op : Fac r TT → (MA.anQ r TT).Op
  | .mul f => (MA.anQ r TT).mulOp f
  | .eul v => MA.eulerQ v

def Fac.ord : Fac r TT → ℕ
  | .mul _ => 0
  | .eul _ => 1

def OpOrd (r : ℕ) (TT : ℝ) (d : ℕ) : Submodule ℂ (MA.anQ r TT).Op :=
  Submodule.span ℂ {a | ∃ l : List (Fac r TT), (l.map Fac.ord).sum ≤ d ∧ a = (l.map Fac.op).prod}

end ord

def JetLocal : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (d : ℕ) (a : (MA.anQ r TT).Op), a ∈ OpOrd r TT d → ∀ m : ℕ∞, (d : ℕ∞) ≤ m →
    ∀ (q : MA.Qp r TT) (g g' : MA.SmQ r TT), JetEq m q g.1 g'.1 →
      (show MA.SmQ r TT from a g).1 q = (show MA.SmQ r TT from a g').1 q

def JetAgree : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (d : ℕ) (a : (MA.anQ r TT).Op), a ∈ OpOrd r TT d → ∀ m : ℕ∞, (d : ℕ∞) ≤ m →
    ∀ g : MA.SmQ r TT, actJ m a g.1 = (show MA.SmQ r TT from a g).1

section En

variable (P : M.Par) (m : ℕ∞)

end En


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FFlM {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (m : ℕ∞) (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (i : Fin (r + 1)) (Dm : Set (Q.Mx k r)) : Set (Q.Mx k r → (Wq →L[ℂ] Wp)) :=
  {J | (∀ g₀ ∈ Q.Glev k r i ∩ Dm, ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ (smM m) F U ∧ ∀ g ∈ U, g ∈ Q.Glev k r i → J g = F g) ∧
    Q.LeftEq k r z i Dm J ∧ Q.RightEq k r z' i Dm J ∧
    ∀ g ∈ Q.Glev k r i ∩ Dm, ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      J (h * g * h') = (π h).comp ((J g).comp (π' h'))}


section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def trJF (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    M.Ty (D.parOf S v) → MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ :=
  fun ρ q => ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
    inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1)))

end place

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section thr

theorem thr_of_budget {k r m N : ℕ} {A₀ : ℝ}
    (hm : 6 * ((r : ℝ) + 1) * m + 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A₀)
    (hA : 10 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    JF.TransportedAlt k r A₀ m := by
  unfold JF.TransportedAlt
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hn] at hm ⊢
  rw [lt_div_iff₀ (by positivity)]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, mul_zero, sub_zero] at hm ⊢
    have hn1 : (1 : ℝ) ≤ 2 * (r : ℝ) + k + 1 := by linarith
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
    have hP : 1 ≤ ((r : ℝ) + 1) ^ 3 * (2 * (r : ℝ) + k + 1) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr1) hn1
    have h3 : ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * (2 * (r : ℝ) + k + 1) ^ 3 := by
      calc ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 = ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 * 1 := by ring
        _ ≤ ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 * (((r : ℝ) + 1) ^ 3 * (2 * (r : ℝ) + k + 1)) :=
            mul_le_mul_of_nonneg_left hP (by positivity)
        _ = ((r : ℝ) + 1) ^ 4 * (2 * (r : ℝ) + k + 1) ^ 3 := by ring
    have hN : 0 ≤ ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2) := by positivity
    have hpos2 : 0 < ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by positivity
    nlinarith [h3, hN, hpos2, hA]
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
    nlinarith [hm, hm1]

end thr

section jf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jf_mem_FFlM [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hT : JF.TransportedAlt k r A m) (hF : B.InCC A m F) :
    B.JF D F ∈ FFlM (m : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem
    D.haarN.conc (fun n₀ h => D.haarN.left n₀ h)
  have hW := Formalism.FourierDecayAlt.P.bessel_words_of_domain Formalism.FourierDecayAlt.P.bessel_integral_domain
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, he⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one D.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one D.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem
      D.haarN.conc D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
      (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

end jf

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellw

variable {d : ℕ}

def pdc : List (Fin d) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | i :: w, u => fun x => fderiv ℝ (pdc w u) x (Pi.single i 1)

structure SOp (d : ℕ) where
  ord : ℕ
  a : (k : Fin (ord + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ

def SOp.app (P : SOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x

def SOp.tr (P : SOp d) (φ : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d,
    (-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x

def SOp.symb (P : SOp d) (x ξ : Fin d → ℝ) : ℂ :=
  ∑ w : Fin P.ord → Fin d, (∏ i, (ξ (w i) : ℂ)) * P.a (Fin.last P.ord) w x

end ellw

def EllRegW : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : ι → SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ j k w, ContDiffOn ℝ ∞ ((P j).a k w) U) → ContinuousOn u U →
    (∀ j (φ : (Fin d → ℝ) → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, u x * (P j).tr φ x = 0) →
    (∀ x ∈ U, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∃ j, (P j).symb x ξ ≠ 0) →
    ContDiffOn ℝ ∞ u U

def GRegJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.CV k r (Y : ℂ) J g = c • J g) →
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') J

theorem transfer_smooth_of_regularity (hR : GRegJ) : JfSmoothBuilt := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hce := JfS.class_eigenvalue_constant 100 E Wp Wq S T f χ ν' m₀ top A₀ le_rfl hB v
  obtain ⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, hCC, _⟩ := hv v
  have hpos : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
  have hA' : 100 * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ := hA
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    Formalism.FourierDecayAlt.P.CutMP.thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA'
  have hF := Gr.jf_mem_FFlM (T v).base A₀ (2 * S.G.r + S.G.k + 1) (f v) hThr (hCC _)
  obtain ⟨_, _, _, _, _, hTy, hTy'⟩ := hplace
  have hS := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ _ (B.JF (T v).base (f v)) hTy hTy' hF
    (fun Y => ⟨_, hce.2 Y⟩)
  have hsub : ∀ g, g ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v →
      g ∈ Q.Glev S.G.k S.G.r 0 ∩ Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun g hg => ⟨hg.1, (JfS.mem_om_of_mem_omP S T v hg.1.1 hg.2).2⟩
  obtain ⟨_, hL, hRt, hU⟩ := hF
  refine ⟨fun g₀ hg₀ => hS g₀ (hsub g₀ hg₀), fun g hg n hn => hL g (hsub g hg) n hn,
    fun g hg n hn => hRt g (hsub g hg) n hn, fun g hg h hh h' hh' => hU g (hsub g hg) h hh h' hh'⟩


end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
