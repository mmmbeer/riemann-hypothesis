import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

variable {C : Type} [Field C]

def IntS (V : VF C) {σ : Type} (F : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, V.Ge 0 (MvPowerSeries.coeff μ F)

def TInv (V : VF C) : Prop :=
  ∀ (d : ℕ) (I₁ J₁ : Type) [Fintype I₁] [Fintype J₁] (X₁ : Cart V d I₁ J₁) (S : Sys X₁),
    (∀ c s x, V.Ge 0 (S.al c s x)) → ∀ t : I₁ → MvPowerSeries I₁ C, S.IsT t →
    ∃ Φ : I₁ → MvPowerSeries I₁ C, (∀ x, IntS V (Φ x)) ∧
      (∀ x, MvPowerSeries.constantCoeff (Φ x) = 0) ∧
      ∀ x, MvPowerSeries.subst t (Φ x) = (MvPowerSeries.X x : MvPowerSeries I₁ C)

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

def tyS (l : ℕ) (a : ℕ → C) : PowerSeries C :=
  PowerSeries.mk fun n => ∑ s ∈ Finset.range (n + 1), if l ^ s = n then a s else 0

def IsCv (V : VF C) {σ : Type} (γ : σ → PowerSeries C) : Prop :=
  ∀ i, PowerSeries.constantCoeff (γ i) = 0 ∧ ∀ n, V.Ge 0 (PowerSeries.coeff n (γ i))

def alongCv {σ : Type} (γ : σ → PowerSeries C) (f : MvPowerSeries σ C) : PowerSeries C :=
  MvPowerSeries.subst γ f

abbrev JJ (I : Fin 2 → Type) : Fin 2 → Type := fun g => I (1 - g)

structure RawChart (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) (κ : Type) where

  lg : κ → MvPowerSeries κ C
  ex : κ → MvPowerSeries κ C

  h : MvPowerSeries (Fin 2 × κ) C

  k : ℕ

  u : ∀ g, I g → κ → C
  ty : ∀ g, I g → ZMod d

  n : ℕ
  j : ℕ
  j' : ℕ
  big : Fin 2 → ZMod d → Prop

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

instance (g : Fin 2) : Fintype (JJ I g) := inferInstanceAs (Fintype (I (1 - g)))

def sg (v : κ → C) : MvPowerSeries κ C :=
  fun μ => -∑ i, v i * MvPowerSeries.coeff
    (μ.mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) X.h

def sg1 (w v : κ → C) : C := ∑ x, w x * MvPowerSeries.coeff (Finsupp.single x 1) (X.sg v)

def tyC (g : Fin 2) : I g ⊕ JJ I g → ZMod d := Sum.elim (X.ty g) (X.ty (1 - g))

def TySet (V : VF C) (g : Fin 2) : Set (ℕ → I g ⊕ JJ I g → C) :=
  {x | ∃ (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C), IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) ∧
    ∀ q : JJ I g, tyS V.l (fun s => x s (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0}

structure CartHyp (V : VF C) (g : Fin 2) : Prop where

  zero : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g

  add : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g
  neg : ∀ x, x ∈ X.TySet V g → -x ∈ X.TySet V g

  teich : ∀ c, V.Ge 0 c → ∀ x ∈ X.TySet V g, teich V.l c x ∈ X.TySet V g

  Vm : ∀ x ∈ X.TySet V g, Vpow 1 x ∈ X.TySet V g

  Fm : ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g

  sumV : ∀ y : ℕ → ℕ → I g ⊕ JJ I g → C, (∀ s, y s ∈ X.TySet V g) → sumV y ∈ X.TySet V g

  t2 : ∀ x ∈ X.TySet V g, ∀ s, (∀ i < s, x i = 0) → ∀ n, V.Ge 0 (x s n)

  t3 : ∀ ζ : JJ I g → C, (∀ q, V.Ge 0 (ζ q)) → const0 (Sum.elim 0 ζ) ∈ X.TySet V g

  t4 : ∀ (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) → (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

variable {X}

def cart {V : VF C} {g : Fin 2} (H : X.CartHyp V g) : Cart V d (I g) (JJ I g) where
  ty := X.tyC g
  Ty :=
    { carrier := X.TySet V g
      zero_mem' := H.zero
      add_mem' := fun {x y} hx hy => H.add x y hx hy
      neg_mem' := fun {x} hx => H.neg x hx }
  teich_mem := H.teich
  V_mem := H.Vm
  F_mem := H.Fm
  sumV_mem := H.sumV
  t2 := H.t2
  t3 := H.t3
  t4 := H.t4

variable (X)

def pairK (g : Fin 2) (q : JJ I g) (c : I (1 - g)) : C := if q = c then -(X.k : C) else 0

def expPt (g : Fin 2) (x : κ) : MvPowerSeries (WV I) C :=
  MvPowerSeries.subst (fun i : κ => ∑ c : I g, X.u g c i • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C))
    (X.ex x)

def hRow : MvPowerSeries (WV I) C :=
  (X.k : C) • MvPowerSeries.subst (fun p : Fin 2 × κ => X.expPt p.1 p.2) X.h

def OnLf (g : Fin 2) (a a' : ZMod d) (w : WV I) : Prop :=
  (w.1 = g ∧ X.ty w.1 w.2 = a) ∨ (w.1 = 1 - g ∧ X.ty w.1 w.2 = a')

def hLf (g : Fin 2) (a a' : ZMod d) : MvPowerSeries (WV I) C :=
  fun μ => if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0

theorem onLf_swap (a a' : ZMod d) (w : WV I) : X.OnLf 1 a' a w ↔ X.OnLf 0 a a' w := by
  unfold OnLf
  simp only [sub_self, sub_zero]
  exact or_comm

theorem hLf_swap (a a' : ZMod d) : X.hLf 1 a' a = X.hLf 0 a a' := by
  unfold hLf
  funext μ
  exact if_congr (by simp only [onLf_swap]) rfl rfl

theorem hLf_leaf (g : Fin 2) (a a' : ZMod d) (μ : WV I →₀ ℕ)
    (h : MvPowerSeries.coeff μ (X.hLf g a a') ≠ 0) : ∀ w ∈ μ.support, X.OnLf g a a' w := by
  by_contra hn
  apply h
  show (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0) = 0
  rw [if_neg hn]

structure RankHyp : Prop where
  big_compl : ∀ g a, X.big (1 - g) a ↔ ¬ X.big g a
  rk_big : ∀ g a, X.big g a → (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.n + X.j
  rk_small : ∀ g a, ¬ X.big g a → (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.j'

def AltC : Prop := Even d ∧ ∀ a : ZMod d, (X.big 0 a ↔ Even a.val)

def AxesSt : Prop :=
  ∀ (μ : WV I →₀ ℕ), ((∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1)) →
    MvPowerSeries.coeff μ X.hRow = 0

section Geo

variable {X} {V : VF C} (H : ∀ g, X.CartHyp V g)

def IntegralGermIndependentOfSystem : Prop :=
  ∀ (S S₂ : ∀ g, Sys (cart (H g))) (t t₂ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g, (S g).IsT (t g)) → (∀ g, (S₂ g).IsT (t₂ g)) → IntGerm V t = IntGerm V t₂

def CEqSt : Prop :=
  X.AltC → ∀ g a a', Odd (a' - a).val →
    ∀ (S : ∀ g, Sys (cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ k : I (1 - g), X.ty (1 - g) k = a' →
      ∃ K ∈ IntGerm V t,
        dVar (⟨1 - g, k⟩ : WV I) (X.hLf g a a') -
            toLeaf (fun g => cart (H g)) g a a' (∑ q : JJ I g, X.pairK g q k • upG g ((S g).ze (t g) q)) =
          toLeaf (fun g => cart (H g)) g a a' K

def RankMaximalCondition : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (cart (H g)).Good a w x →
    (∀ q, V.MM ((cart (H g)).c0' x q)) → ∀ c, V.MM (w c)

def IndependenceBoundCondition : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∀ (N : ℕ) (w : Fin N → I g → C) (x : Fin N → ℕ → I g ⊕ JJ I g → C),
    (∀ ν, (cart (H g)).Good a (w ν) (x ν)) → (∀ ν c, V.MM ((cart (H g)).V2 (x ν) c)) →
    IndepMod V w → N ≤ X.j'

def CHSt : Prop :=
  ∀ g a, X.big g a → ∀ w : Fin X.n → I g → C, IsSat V w →
    (∀ c x, X.ty g x ≠ a → w c x = 0) →
    ∃ y : Fin X.n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧
      (∀ (S : ∀ g, Sys (cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
        ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
          IntGerm V t) ∧
      (X.AltC →
        V.v (Matrix.of fun ρ c : Fin X.n => ∑ x, y ρ x * w c x).det ≤
          (((X.n : ℝ) * gam V.l + ((X.j : ℝ) + X.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, X.big g a) →
        V.v (Matrix.of fun ρ c : Fin X.n => ∑ x, y ρ x * w c x).det ≤
          ((((X.j : ℝ) + X.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))

end Geo

structure Hyps (V : VF C) : Prop where
  charZero : CharZero C
  algClosed : IsAlgClosed C
  l_odd : V.l ≠ 2
  k_unit : V.v (X.k : C) = 0
  cartH : ∀ g, X.CartHyp V g
  rank : X.RankHyp
  axes : X.AxesSt
  G0 : IntegralGermIndependentOfSystem cartH
  CEq : CEqSt cartH
  R1 : IndependenceBoundCondition cartH
  R2 : RankMaximalCondition cartH
  CH : CHSt cartH

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace RawChart

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  (X : RawChart C d I κ) {V : VF C}

theorem pairK_int (g : Fin 2) (q : JJ I g) (c : I (1 - g)) : V.Ge 0 (X.pairK g q c) := by
  unfold pairK
  split_ifs
  · exact (VF.ge_natCast X.k).neg
  · exact VF.Ge.zero 0

theorem k_ne_zero (hk : V.v (X.k : C) = 0) : (X.k : C) ≠ 0 := by
  intro h
  rw [h, V.v.map_zero] at hk
  exact WithTop.top_ne_zero hk

theorem k_inv_int (hk : V.v (X.k : C) = 0) : V.Ge 0 ((X.k : C)⁻¹) := by
  have h1 : V.v ((X.k : C) * (X.k : C)⁻¹) = 0 := by
    rw [mul_inv_cancel₀ (X.k_ne_zero hk), V.v.map_one]
  rw [V.v.map_mul, hk, zero_add] at h1
  unfold VF.Ge
  rw [h1]
  rfl

theorem pairK_onto (hk : V.v (X.k : C) = 0) (g : Fin 2) :
    ∃ s : I (1 - g) → JJ I g → C, (∀ c q, V.Ge 0 (s c q)) ∧
      ∀ q q' : JJ I g, ∑ c, X.pairK g q c * s c q' = if q = q' then 1 else 0 := by
  refine ⟨fun c q => if c = q then -(X.k : C)⁻¹ else 0, ?_, ?_⟩
  · intro c q
    dsimp only
    split_ifs
    · exact (X.k_inv_int hk).neg
    · exact VF.Ge.zero 0
  · intro q q'
    have hk0 := X.k_ne_zero hk
    simp only [pairK, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs
    · field_simp
    · simp

theorem rk_fil (H : X.RankHyp) (g : Fin 2) (a : ZMod d) :
    (Finset.univ.filter fun q : I (1 - g) => X.ty (1 - g) q = a).card + 0 +
      (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.n + X.j + X.j' := by
  by_cases hb : X.big g a
  · have h1 : ¬ X.big (1 - g) a := fun h => (H.big_compl g a).1 h hb
    rw [H.rk_big g a hb, H.rk_small (1 - g) a h1]
    omega
  · have h1 : X.big (1 - g) a := (H.big_compl g a).2 hb
    rw [H.rk_small g a hb, H.rk_big (1 - g) a h1]
    omega

theorem hLf_axes (H : X.AxesSt) (g : Fin 2) (a a' : ZMod d) (μ : WV I →₀ ℕ)
    (h : (∀ w ∈ μ.support, w.1 = g) ∨ (∀ w ∈ μ.support, w.1 = 1 - g)) :
    MvPowerSeries.coeff μ (X.hLf g a a') = 0 := by
  have h2 : (∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1) := by
    fin_cases g
    · exact h
    · exact h.symm
  show (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0) = 0
  rw [H μ h2]
  simp

def rowData [NeZero d] (H : X.Hyps V) : RowData C V d I (JJ I) where
  charZero := H.charZero
  algClosed := H.algClosed
  l_odd := H.l_odd
  G := fun g => cart (H.cartH g)
  n := X.n
  j := X.j
  j' := X.j'
  rh := 0
  r := X.n + X.j + X.j'
  r_eq := rfl
  big := X.big
  big_compl := H.rank.big_compl
  rk_big := H.rank.rk_big
  rk_small := H.rank.rk_small
  rk_fil := X.rk_fil H.rank
  pair := X.pairK
  pair_int := X.pairK_int
  pair_type := by
    intro g q c h
    unfold pairK
    rw [if_neg]
    rintro rfl
    exact h rfl
  pair_onto := X.pairK_onto H.k_unit
  R2 := H.R2
  R1 := fun hA g a hb N w x h1 h2 h3 => by simpa using H.R1 hA g a hb N w x h1 h2 h3
  G0 := H.G0
  hL := X.hLf
  hL_leaf := X.hLf_leaf
  hL_swap := X.hLf_swap
  hL_axes := X.hLf_axes H.axes
  C_eq := H.CEq
  CH := H.CH

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

def un1 {dd : ℕ} (f : PS C 1 dd) : MvPowerSeries (Fin dd) C :=
  fun μ => MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f

def linAct {dd : ℕ} (φ : Pt C 1 dd) (v : Fin dd → C) : Fin dd → C :=
  fun i => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i) * v j

structure FBChart (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) where
  algClosed : IsAlgClosed C

  cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)
  l_odd : V.l ≠ 2
  B : FB C dd O
  h : PS C 2 dd
  gauge : B.IsCanonGauge C h
  intF : ∀ i, IntS V (B.G.F i)
  intAct : ∀ a i, IntS V (B.A.act a i)
  intPh1 : IntS V B.ph1
  intPh2 : IntS V B.ph2
  intSy : IntS V B.sy
  intAd : ∀ a, IntS V (B.ad a)

  lg : Pt C 1 dd
  lg_lin : ∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)
  lg_add : ∀ i, ev (n := 2) ![addOf B.G.F (pt C dd 0) (pt C dd 1)] (lg i) =
    ev (n := 2) ![pt C dd 0] (lg i) + ev (n := 2) ![pt C dd 1] (lg i)

  ex : Pt C 1 dd
  ex_const : ∀ i, MvPowerSeries.constantCoeff (ex i) = 0
  lg_ex : comp1 lg ex = pt C dd 0

  ex_lg : comp1 ex lg = pt C dd 0
  w0 : O

  halfIntegralGenerator_add_conj_eq_one : w0 + star w0 = 1
  k : ℕ
  k_unit : V.v (k : C) = 0

structure PairData {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] where

  em : Fin 2 → ZMod d → (O →+* C)
  em_int : ∀ g a x, V.Ge 0 (em g a x)
  em_conj : ∀ a x, em 1 a x = em 0 a (star x)

  em_frob : ∀ g a x, V.MM (em g (a + 1) x - em g a x ^ V.l)

  em_sep : ∀ p p' : Fin 2 × ZMod d, p ≠ p' → ∃ x, V.v (em p.1 p.2 x - em p'.1 p'.2 x) = 0

  em_unr : ∀ g, ∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em g a ε - 1)) ∧
    ∀ x : O, (∀ a, V.MM (em g a x)) → ∃ y, ε * x = (V.l : O) * y
  u : ∀ g, I g → Fin dd → C
  ty : ∀ g, I g → ZMod d
  u_int : ∀ g c i, V.Ge 0 (u g c i)
  u_eig : ∀ g c x, linAct (Y.B.A.act x) (u g c) = em g (ty g c) x • u g c

  u_sat : ∀ g, ∃ w : Fin dd → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
    ∀ c c' : I g, ∑ x, u g c x * w x c' = if c = c' then 1 else 0

  u_full : ∀ g a (v : Fin dd → C), (∀ x, linAct (Y.B.A.act x) v = em g a x • v) →
    ∃ b : I g → C, (∀ c, ty g c ≠ a → b c = 0) ∧ v = ∑ c, b c • u g c
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Fin 2 → ZMod d → Prop

namespace FBChart

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]

def raw (Y : FBChart C V O dd) (p : PairData Y d I) : RawChart C d I (Fin dd) where
  lg := fun i => un1 (Y.lg i)
  ex := fun i => un1 (Y.ex i)
  h := Y.h
  k := Y.k
  u := p.u
  ty := p.ty
  n := p.n
  j := p.j
  j' := p.j'
  big := p.big

end FBChart

section Closed

def AllFB (Φ : ∀ (C : Type) [Field C] (_V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin dd) → Prop) : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    Φ C V d I dd (Y.raw p)

def CartFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => ∀ g, X.CartHyp V g

def AxesFBSt : Prop := AllFB fun _ _ _ _ _ _ _ X => X.AxesSt

def IntegralGermIndependentAllCharts : Prop := AllFB fun _ _ V _ _ _ _ X => ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H

def CEqFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.CEqSt H

def IndependenceBoundAllCharts : Prop :=
  AllFB fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H

end Closed

section Steps

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.sgP (Y : FBChart C V O dd) (v : Fin dd → C) : PS C 1 dd :=
  -∑ i, MvPowerSeries.C (v i) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) Y.h)

def GermISt (Y : FBChart C V O dd) : Prop :=
  ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    IntS V (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (Y.sgP v) -
      ev (n := 2) ![pt C dd 0] (Y.sgP v) - ev (n := 2) ![pt C dd 1] (Y.sgP v))

def GermIISt (Y : FBChart C V O dd) : Prop :=
  ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    IntS V ((∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 1, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) *
          MvPowerSeries.pderiv C ((1 : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd 0] (Y.sgP v))

def ActCv (Y : FBChart C V O dd) (a : ℕ → O) : Prop :=
  ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (MvPowerSeries.coeff μ (Y.B.A.act (a (n + 1)) i) -
    MvPowerSeries.coeff μ (Y.B.A.act (a n) i))

def EndomorphismLimitIntegral (Y : FBChart C V O dd) : Prop :=
  ∀ a : ℕ → O, ActCv Y a → ActCv Y (fun n => star (a n)) →
    ∃ e eb : Pt C 1 dd, (∀ i, IntS V (e i)) ∧ (∀ i, IntS V (eb i)) ∧
      (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (a n) i))) ∧
      (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (eb i) - MvPowerSeries.coeff μ (Y.B.A.act (star (a n)) i))) ∧
      comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
        addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)) ∧
      IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h))

end Steps

section Record

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d] {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]

theorem FBChart.hyps (hCart : CartFBSt) (hAx : AxesFBSt) (hG0 : IntegralGermIndependentAllCharts) (hC : CEqFBSt) (hR1 : IndependenceBoundAllCharts)
    (Y : FBChart C V O dd) (p : PairData Y d I) (hrk : (Y.raw p).RankHyp)
    (hR2 : RawChart.RankMaximalCondition (hCart C V O dd Y d I p)) (hCH : RawChart.CHSt (hCart C V O dd Y d I p)) :
    (Y.raw p).Hyps V where
  charZero := inferInstance
  algClosed := Y.algClosed
  l_odd := Y.l_odd
  k_unit := Y.k_unit
  cartH := hCart C V O dd Y d I p
  rank := hrk
  axes := hAx C V O dd Y d I p
  G0 := hG0 C V O dd Y d I p _
  CEq := hC C V O dd Y d I p hrk _
  R1 := hR1 C V O dd Y d I p hrk _ hR2
  R2 := hR2
  CH := hCH

end Record

end Formalism.L2.FormalSeriesBounds
end
end
