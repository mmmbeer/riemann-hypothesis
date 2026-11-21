import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunDepth.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

section General

variable (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) [StarRing (𝓞 D.host.E)]
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

def retie (O : OnObj S P oc) (ι : Bs.J → ℕ) : OnObj S P oc :=
  { O with
    E := fun v j => EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) (depOf T EX Tp hK) v (ι j)
    σ := fun _ j => sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
    nnK := fun j => nnKAt (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
    T := Tp.TO
    g1 := D.host.g 0
    g2 := D.host.g 1
    q1 := D.host.q
    dd := D.host.d
    sm := D.host.small
    k := D.R.k
    m := D.R.m
    f := D.R.f
    x := L.sc.x
    eps := L.sc.eps
    Sc := L.Sc
    eta := L.etaSz
    bp := L.sc.b'
    X2 := L.sc.X'' D.R.n
    vd := vd2 D
    wt := fun _ => 2 * (D.R.f : ℝ) * L.sc.b
    th := fun l => Formalism.UnitaryBoundIntegral.thl D.R.k l
    ad := fun _ => 0
    DF := ((Finset.univ.sup fun j : Bs.J => WeightAlgebra.DF (lR Tp hK (ι j)) : ℕ) : ℝ) }


variable {T EX Tp hK} {O : OnObj S P oc} {ι : Bs.J → ℕ}



theorem b_eq (h : RunTie T EX Tp hK O ι) : O.b = L.sc.b := by
  unfold OnObj.b OnObj.xe Scale.b Scale.L
  rw [h.x_eq, h.eps_eq]


theorem th_zero (h : RunTie T EX Tp hK O ι) : O.th 0 = 0 ∧ O.th 1 = 0 := by
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have h1 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ ((3 : ℝ) / 2) := Real.one_le_rpow hk (by norm_num)
  constructor
  · rw [h.th_eq, Formalism.UnitaryBoundIntegral.thl]
    convert Real.sSup_empty
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, -, h3, hlt, -⟩
    rw [Nat.cast_zero, zero_pow (by omega)] at hlt
    linarith
  · rw [h.th_eq, Formalism.UnitaryBoundIntegral.thl]
    convert Real.sSup_empty
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, -, -, hlt, -⟩
    rw [Nat.cast_one, one_pow] at hlt
    linarith


end General








def intMap (T : Core D) : 𝓞 T.Q.c.F →+* 𝓞 D.what₂.LL :=
  (D.what₂.OtoLL.comp T.Q.eO.toRingHom).codRestrict (integralClosure ℤ D.what₂.LL) fun x =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) x).map (D.what₂.OtoLL.comp T.Q.eO.toRingHom).toIntAlgHom

def hostMap (D : D7) : 𝓞 D.host.E →+* D.what₂.LL := D.embE.comp (algebraMap (𝓞 D.host.E) D.host.E)





end GlobalTheory.RunDepth.Model
