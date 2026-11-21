import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.MainNotions.CartierLocalBounds

open Formalism.BasicNotions

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def gam (l : ℕ) : ℝ := (l : ℝ) / ((l : ℝ) ^ 2 - 1)

def expE (l i : ℕ) : ℕ := 1 + l * ∑ t ∈ Finset.range ((i - 1) / 2), (l ^ 2) ^ t

def rad1 (l i : ℕ) : ℝ := rho l + ((l : ℝ) ^ i)⁻¹ / 2

def rad2 (l : ℕ) : ℝ := rho l + 1 / 2

def dlt (l i : ℕ) : ℝ := ((l : ℝ) ^ i)⁻¹ / 8

def vLe {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (b : ℝ) : Prop := (l : ℝ) ^ (-b) ≤ ‖x‖

def vGe {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (b : ℝ) : Prop := ‖x‖ ≤ (l : ℝ) ^ (-b)

section Jets

variable {C : Type} [Field C]

abbrev PVar (n0 : ℕ) := (Fin n0 × Fin n0) ⊕ (Fin n0 × Fin n0)

def detL (C : Type) [Field C] (n0 : ℕ) : MvPolynomial (PVar n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inl (b, c)))

def detR (C : Type) [Field C] (n0 : ℕ) : MvPolynomial (PVar n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inr (b, c)))

def mfact {σ : Type} (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial

def jetAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ m ∈ P.support, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m g

def mvExp {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun m => ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C)

def LamOf (C : Type) [Field C] (l i n0 : ℕ) (h : MvPowerSeries (PVar n0) C) (y : ℕ) : C :=
  jetAt0 (detL C n0 ^ (l ^ i * y) * detR C n0 ^ y) (mvExp h)

def dL {ι ι' : Type} [Fintype ι] (μ : (ι ⊕ ι') →₀ ℕ) : ℕ := ∑ c : ι, μ (Sum.inl c)

def dR {ι ι' : Type} [Fintype ι'] (μ : (ι ⊕ ι') →₀ ℕ) : ℕ := ∑ b : ι', μ (Sum.inr b)

def diffOp {σ : Type} (P Q : MvPolynomial σ C) : MvPolynomial σ C :=
  ∑ m ∈ P.support, ∑ a ∈ Q.support,
    if m ≤ a then
      MvPolynomial.monomial (a - m)
        (MvPolynomial.coeff m P * MvPolynomial.coeff a Q * ((mfact a : C) / (mfact (a - m) : C)))
    else 0

end Jets

def WeightGe {l : ℕ} [Fact l.Prime] (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (h1 : MvPowerSeries (ι ⊕ ι') ℂ_[l]) : Prop :=
  ∀ μ, vGe (MvPowerSeries.coeff μ h1)
    (1 / ((l : ℝ) - 1) - ((dL μ : ℝ) * (rad1 l i - dlt l i) + (dR μ : ℝ) * (rad2 l - dlt l i)))

def hP (l : ℕ) [Fact l.Prime] (i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) ℂ_[l]) :
    MvPowerSeries (PVar n0) ℂ_[l] :=
  -(((l : ℂ_[l]) ^ expE l i)⁻¹) • (∑ b : Fin n0, ∑ c : Fin n0,
      MvPowerSeries.X (Sum.inl (b, c)) ^ (l ^ i) * MvPowerSeries.X (Sum.inr (b, c))) + h1

def ThmP : Prop :=
  ∃ C0 : ℝ, ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ i : ℕ, Odd i → ∀ n n0 : ℕ, 1 ≤ n → n0 ≤ n →
    ∀ h1 : MvPowerSeries (PVar n0) ℂ_[l], MvPowerSeries.constantCoeff h1 = 0 → WeightGe i h1 →
    ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧
      (y : ℝ) < Y0 + C0 * (n : ℝ) ^ 2 * ((i : ℝ) + Real.log ((n : ℝ) + 1)) ∧
      vLe (LamOf ℂ_[l] l i n0 (hP l i n0 h1) y)
        ((n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1))

def CayleyId : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 s : ℕ),
    diffOp (detL C n0) (detL C n0 ^ (s + 1)) =
      ((∏ a ∈ Finset.range n0, ((s : C) + 1 + a))) • detL C n0 ^ s

def LPDual : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → Even d → ∀ Ds : ZMod d → ℝ, (∀ a, 0 ≤ Ds a) →
    IsGreatest {y : ℝ | ∃ sg : ZMod d → ℝ, (∀ a, 0 ≤ sg a ∧ sg a ≤ 1) ∧
        (∀ a (i : ℕ), Odd i → i < d → 1 ≤ (l : ℝ) ^ i * sg a + sg (a + (i : ZMod d))) ∧
        y = ∑ a, Ds a * (gam l - sg a)}
      (lpF l d Ds)

theorem fin_two_eq_one_sub (g g' : Fin 2) (h : g' ≠ g) : g' = 1 - g := by
  fin_cases g <;> fin_cases g' <;> simp_all

structure LocD (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d] where

  five_le_l : 5 ≤ l

  d_even : Even d

  r : ℕ
  j : ℕ
  j' : ℕ
  rh : ℕ
  rh_le : rh ≤ j'

  rh_le_big : rh + j' ≤ r
  jj_le : j + j' ≤ r

  big : Fin 2 → ZMod d → Prop

  rk : Fin 2 → ZMod d → ℕ
  rk_big : ∀ g a, big g a → rk g a = r - j'
  rk_small : ∀ g a, ¬ big g a → rk g a = j'

  U : ∀ g a, Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])
  U_summand : ∀ g a, big g a → ∃ Q : Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l]), IsCompl (U g a) Q
  U_basis : ∀ g a, big g a → Nonempty (Module.Basis (Fin (r - j' - j)) 𝓞_ℂ_[l] (U g a))

  Chart : Type

  tan : Chart → ∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])

  chart_tan : ∀ b : (∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])),
    ∃ χ : Chart, tan χ = b

  alC : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk g a) → ℂ_[l]
  alC_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → alC χ g b c s a = 0

  alC_zero : ∀ χ g b c k, alC χ g b c 0 b k = ((tan χ g b c k : 𝓞_ℂ_[l]) : ℂ_[l])

  beP : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk (1 - g) a) → ℂ_[l]
  beP_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → beP χ g b c s a = 0

  beP_zero : ∀ χ g b c a, beP χ g b c 0 a = 0

  chart_mod : ∀ (χ : Chart)
    (x : ∀ g : Fin 2, ℕ → (Σ b : ZMod d, Fin (rk g b)) → (Σ b : ZMod d, Fin (rk g b)) → 𝓞_ℂ_[l]),
    (∀ g (s : ℕ) c b, b.1 ≠ c.1 + (s : ZMod d) → x g s c b = 0) →
    (∀ g, IsUnit (Matrix.of (x g 0)).det) →
    ∃ χ' : Chart,
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, alC χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * alC χ g b.1 b.2 (n - s) a k) ∧
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, beP χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * beP χ g b.1 b.2 (n - s) a k)

  tL : Chart → ∀ (g : Fin 2) (a : ZMod d), (Σ b : ZMod d, Fin (rk g b)) → MvPowerSeries (Fin (rk g a)) ℂ_[l]
  tL_const : ∀ χ g a x, MvPowerSeries.constantCoeff (tL χ g a x) = 0

  tL_log_same : ∀ χ g a (k : Fin (rk g a)) (μ : Fin (rk g a) →₀ ℕ),
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) =
      if μ = Finsupp.single k 1 then 1 else 0

  tL_log_other : ∀ χ g a a' (k : Fin (rk g a')) (μ : Fin (rk g a) →₀ ℕ), a' ≠ a →
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a' k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) = 0

  hL : ∀ (g : Fin 2) (a a' : ZMod d), MvPowerSeries (Fin (rk g a) ⊕ Fin (rk (1 - g) a')) ℂ_[l]

  Tt : Fin 2 → Type
  [instTt : ∀ g, AddCommGroup (Tt g)]
  [modTt : ∀ g, Module ℤ_[l] (Tt g)]
  Tt_free : ∀ g, Module.Free ℤ_[l] (Tt g)
  Tt_rank : ∀ g, Module.finrank ℤ_[l] (Tt g) = d * (r - rh)

  alHT : ∀ g, Tt g → ∀ a, (Fin (rk g a) → 𝓞_ℂ_[l]) →ₗ[𝓞_ℂ_[l]] 𝓞_ℂ_[l]

  chiG : Chart → ∀ g, Tt g → MvPowerSeries (Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l]

  chiG_leaf : ∀ χ g (t : Tt g) a,
    MvPowerSeries.subst (fun x => tL χ g a x)
        (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) (chiG χ g t)) =
      mvExp (∑ k : Fin (rk g a), ((alHT g t a (Pi.single k 1) : 𝓞_ℂ_[l]) : ℂ_[l]) •
        (MvPowerSeries.X k : MvPowerSeries (Fin (rk g a)) ℂ_[l]))

  ev : Chart → ∀ N : ℕ,
    MvPolynomial (Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (rk g a)) 𝓞_ℂ_[l] →
    MvPowerSeries (Fin N × Σ g : Fin 2, Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l] → ℂ_[l]

attribute [instance] LocD.instTt LocD.modTt

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def nn : ℕ := Λ.r - Λ.j' - Λ.j

def mm : ℕ := Λ.j + Λ.j'

def Alternating : Prop := ∀ a : ZMod d, (Λ.big 0 a ↔ Even a.val) ∧ (Λ.big 1 a ↔ ¬ Even a.val)

def AllBig : Prop := ∀ a : ZMod d, Λ.big 0 a

def bg (_Λ : LocD l d) (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

abbrev CoG (g : Fin 2) := Σ b : ZMod d, Fin (Λ.rk g b)

def zeP (χ : Λ.Chart) (g : Fin 2) (a a' : ZMod d) (b : Fin (Λ.rk (1 - g) a')) :
    MvPowerSeries (Fin (Λ.rk g a)) ℂ_[l] :=
  fun μ => -(∑ s ∈ Finset.range (μ.degree + 1), ∑ x : Λ.CoG g, ∑ k : Fin (Λ.rk (1 - g) a'),
    ((Λ.tan χ (1 - g) a' b k : 𝓞_ℂ_[l]) : ℂ_[l]) * Λ.beP χ g x.1 x.2 s a' k *
      MvPowerSeries.coeff μ (Λ.tL χ g a x ^ (l ^ s)))

end LocD

def hPull {l : ℕ} [Fact l.Prime] {N N' : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (H : MvPowerSeries (Fin N ⊕ Fin N') ℂ_[l]) (v : ι → Fin N → ℂ_[l]) (v' : ι' → Fin N' → ℂ_[l]) :
    MvPowerSeries (ι ⊕ ι') ℂ_[l] :=
  MvPowerSeries.subst
    (Sum.elim (fun k => ∑ c : ι, v c k • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') ℂ_[l]))
      (fun k => ∑ b : ι', v' b k • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') ℂ_[l]))) H

def embL {C : Type} [CommRing C] {ι ι' : Type} (f : MvPowerSeries ι C) : MvPowerSeries (ι ⊕ ι') C :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (Sum.inl k) : MvPowerSeries (ι ⊕ ι') C)) f

def embR {C : Type} [CommRing C] {ι ι' : Type} (f : MvPowerSeries ι' C) : MvPowerSeries (ι ⊕ ι') C :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (Sum.inr k) : MvPowerSeries (ι ⊕ ι') C)) f

def hRows {C : Type} [CommRing C] (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) :
    MvPowerSeries (PVar n0) C :=
  ∑ ρ : Fin n0, MvPowerSeries.subst
    (Sum.elim (fun c => (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar n0) C))
      (fun b => MvPowerSeries.X (Sum.inr (ρ, b)))) H

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def hM (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) (i : ℕ) {n0 N' : ℕ} (e : Fin n0 → Fin (Λ.rk g a))
    (v' : Fin N' → Fin (Λ.rk (1 - g) (a + (i : ZMod d))) → 𝓞_ℂ_[l]) :
    MvPowerSeries (Fin n0 ⊕ Fin N') ℂ_[l] :=
  hPull (Λ.hL g a (a + (i : ZMod d))) (fun c k => ((Λ.tan χ g a (e c) k : 𝓞_ℂ_[l]) : ℂ_[l]))
    (fun b k => ((v' b k : 𝓞_ℂ_[l]) : ℂ_[l]))

def mainM (_Λ : LocD l d) (i : ℕ) {n0 N' : ℕ} (Φ : Fin N' → Fin n0 → ℂ_[l]) :
    MvPowerSeries (Fin n0 ⊕ Fin N') ℂ_[l] :=
  ((l : ℂ_[l]) ^ expE l i)⁻¹ • ∑ b : Fin N', ∑ c : Fin n0,
    Φ b c • (MvPowerSeries.X (Sum.inl c) ^ (l ^ i) * MvPowerSeries.X (Sum.inr b))

def MConcl (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) (i n0 : ℕ) (e : Fin n0 ↪ Fin (Λ.rk g a))
    (v' : Fin Λ.nn → Fin (Λ.rk (1 - g) (a + (i : ZMod d))) → 𝓞_ℂ_[l])
    (Φ : Fin Λ.nn → Fin n0 → ℂ_[l]) : Prop :=
  ((Λ.nn : ℤ) - ((i : ℤ) + 3) * Λ.mm ≤ n0 ∧ n0 ≤ Λ.nn) ∧
  Submodule.span 𝓞_ℂ_[l] (Set.range (fun c => Λ.tan χ g a (e c))) ≤ Λ.U g a ∧
  (∃ Q : Submodule 𝓞_ℂ_[l] (Fin (Λ.rk g a) → 𝓞_ℂ_[l]), Q ≤ Λ.U g a ∧
    Disjoint (Submodule.span 𝓞_ℂ_[l] (Set.range (fun c => Λ.tan χ g a (e c)))) Q ∧
    Submodule.span 𝓞_ℂ_[l] (Set.range (fun c => Λ.tan χ g a (e c))) ⊔ Q = Λ.U g a) ∧
  LinearIndependent 𝓞_ℂ_[l] v' ∧
  Submodule.span 𝓞_ℂ_[l] (Set.range v') = Λ.U (1 - g) (a + (i : ZMod d)) ∧
  (∀ c a'' k, Λ.alC χ g a (e c) 1 a'' k = 0) ∧
  (∀ b c, ‖Φ b c‖ ≤ 1) ∧
  (∀ (b : Fin Λ.nn) (c : Fin n0), b.val < n0 → Φ b c = if b.val = c.val then -1 else 0) ∧
  WeightGe i (Λ.hM χ g a i e v' - Λ.mainM i Φ) ∧
  (∀ μ, dR μ = 0 → MvPowerSeries.coeff μ (Λ.hM χ g a i e v' - Λ.mainM i Φ) = 0) ∧
  (i = 1 → ∀ μ, dL μ < l ^ 2 → dR μ < l →
    ‖MvPowerSeries.coeff μ (Λ.hM χ g a i e v' - Λ.mainM i Φ)‖ ≤ 1)

def LemmaMAt : Prop :=
  Λ.Alternating → ∀ (g : Fin 2) (a : ZMod d), Λ.big g a → ∀ i : ℕ, Odd i → i < d →
    ∃ (χ : Λ.Chart) (n0 : ℕ) (e : Fin n0 ↪ Fin (Λ.rk g a))
      (v' : Fin Λ.nn → Fin (Λ.rk (1 - g) (a + (i : ZMod d))) → 𝓞_ℂ_[l])
      (Φ : Fin Λ.nn → Fin n0 → ℂ_[l]), Λ.MConcl χ g a i n0 e v' Φ

def UBAt : Prop :=
  Λ.Alternating → ∀ (g : Fin 2) (a : ZMod d), Λ.big g a →
    ∀ (χ : Λ.Chart) (n0 : ℕ) (e : Fin n0 ↪ Fin (Λ.rk g a))
      (v' : Fin Λ.nn → Fin (Λ.rk (1 - g) (a + ((1 : ℕ) : ZMod d))) → 𝓞_ℂ_[l])
      (Φ : Fin Λ.nn → Fin n0 → ℂ_[l]), Λ.MConcl χ g a 1 n0 e v' Φ →
      ∀ (hn : n0 ≤ Λ.nn) (y : ℕ), y + Λ.nn ≤ l - 1 →
        ‖LamOf ℂ_[l] l 1 n0
          (hRows n0 (Λ.hM χ g a 1 e (fun b => v' (Fin.castLE hn b)))) y‖ = 1

def htDet (g : Fin 2) (a : ZMod d) (bas : Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U g a))
    (t : Fin Λ.nn → Λ.Tt g) : ℂ_[l] :=
  (((Matrix.of fun k c : Fin Λ.nn => Λ.alHT g (t k) a (bas c : Fin (Λ.rk g a) → 𝓞_ℂ_[l])).det :
    𝓞_ℂ_[l]) : ℂ_[l])

def CHAt : Prop :=
  (Λ.Alternating → ∀ (g : Fin 2) (a : ZMod d), Λ.big g a →
    ∀ bas : Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U g a), ∃ t : Fin Λ.nn → Λ.Tt g,
      vLe (Λ.htDet g a bas t) ((Λ.nn : ℝ) * gam l + (Λ.mm : ℝ) / ((l : ℝ) - 1))) ∧
  (Λ.AllBig → ∀ a : ZMod d,
    ∀ bas : Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U 0 a), ∃ t : Fin Λ.nn → Λ.Tt 0,
      vLe (Λ.htDet 0 a bas t) ((Λ.mm : ℝ) / ((l : ℝ) - 1)))

abbrev LV (N : ℕ) := Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (Λ.rk g a)

abbrev CV (N : ℕ) := Fin N × Σ g : Fin 2, Λ.CoG g

def detBlock (N : ℕ) (a : ZMod d) (S : Fin Λ.nn ↪ Fin N)
    (bas : Fin Λ.nn → Fin (Λ.rk (Λ.bg a) a) → 𝓞_ℂ_[l]) : MvPolynomial (Λ.LV N) 𝓞_ℂ_[l] :=
  Matrix.det (Matrix.of fun k c : Fin Λ.nn =>
    ∑ κ : Fin (Λ.rk (Λ.bg a) a), MvPolynomial.C (bas c κ) * MvPolynomial.X (S k, ⟨Λ.bg a, a, κ⟩))

def DetProd (N : ℕ) (W : ZMod d → ℕ) : Set (MvPolynomial (Λ.LV N) 𝓞_ℂ_[l]) :=
  {P | ∃ (B : ℕ) (blk : Fin B → ZMod d) (S : Fin B → (Fin Λ.nn ↪ Fin N)) (ex : Fin B → ℕ)
      (bas : ∀ a, Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U (Λ.bg a) a)),
    (∀ a, ∑ β ∈ Finset.univ.filter (fun β => blk β = a), ex β = W a) ∧
    (∀ β β', β ≠ β' → blk β = blk β' → Disjoint (Set.range (S β)) (Set.range (S β'))) ∧
    P = ∏ β, (Λ.detBlock N (blk β) (S β)
      (fun c => (bas (blk β) c : Fin (Λ.rk (Λ.bg (blk β)) (blk β)) → 𝓞_ℂ_[l]))) ^ (ex β)}

end LocD

def thl (l k : ℕ) : ℝ :=
  ((l : ℝ) ^ sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i})⁻¹

def addl (C : ℝ) (l k n d : ℕ) (l1 : ℝ) : ℝ :=
  if (l : ℝ) < (k : ℝ) ^ ((1 : ℝ) / 2) then C * d * (n : ℝ) ^ 3 * (k : ℝ) ^ 3 * Real.log k
  else if (l : ℝ) < l1 then C * d * (n : ℝ) ^ 3 * l * Real.log ((n : ℝ) * l) else 0

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def ContentAt (C : ℝ) : Prop :=
  Λ.Alternating → 0 < Λ.mm →
  ∀ (T Dp l1 : ℝ) (w : ZMod d → ℝ) (W : ZMod d → ℕ) (tha : ZMod d → ℝ),
    1 ≤ T → 1 ≤ Dp → Dp * ((Λ.nn : ℝ) + 1) / Λ.mm ≤ T → (Dp + 4) / T ≤ 1 / 2 →
    (∀ a, 0 < w a) → (∀ a, T * W a = w a * (1 - tha a)) →
    (∀ a, 0 ≤ tha a ∧ tha a ≤ (Dp + 4) / T) →
    ((Λ.nn : ℝ) + 1) ^ ((3 : ℝ) / 2) < l1 → 2 * (Λ.nn : ℝ) + 2 < l1 →
    ∃ N : ℕ, (N : ℝ) ≤ C * Λ.r * d * (1 + ((Finset.univ.sup W : ℕ) : ℝ) / l1 ^ 2) ∧
      ∃ P ∈ Λ.DetProd N W, ∃ (χ : Λ.Chart) (g : MvPowerSeries (Λ.CV N) 𝓞_ℂ_[l]),
        vLe (Λ.ev χ N P g)
          ((lpF l d (fun a => (Λ.nn : ℝ) * w a) +
            C * Real.log ((Λ.nn : ℝ) + 1) * Λ.mm * (∑ a, w a) / l +
            C * ((Λ.nn : ℝ) + 1) * thl l (Λ.nn + 1) * (∑ a, w a) +
            T * addl C l (Λ.nn + 1) Λ.nn d l1) / T)

def CartierFrobeniusFormLocal : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2), ∃ (c : ℕ → Λ.CoG g → Λ.CoG g → 𝓞_ℂ_[l])
      (c' : ℕ → Λ.CoG g → ∀ a : ZMod d, Fin (Λ.rk (1 - g) a) → 𝓞_ℂ_[l]),
    ∀ (x : Λ.CoG g) (i : ℕ) (a : ZMod d),
      (∀ k, (l : ℂ_[l]) * Λ.alC χ g x.1 x.2 (i + 1) a k =
        ∑ s ∈ Finset.range (i + 1), ∑ y : Λ.CoG g,
          ((c s x y : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (i - s)) * Λ.alC χ g y.1 y.2 (i - s) a k) ∧
      (∀ k, (l : ℂ_[l]) * Λ.beP χ g x.1 x.2 (i + 1) a k =
        (∑ s ∈ Finset.range (i + 1), ∑ y : Λ.CoG g,
          ((c s x y : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (i - s)) * Λ.beP χ g y.1 y.2 (i - s) a k) +
          ((c' i x a k : 𝓞_ℂ_[l]) : ℂ_[l]))

def LieLeafVanishingLocal : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → Λ.big g a →
    Λ.big (1 - g) (a + (i : ZMod d)) →
    (∀ μ, (dL μ = 0 ∨ dR μ = 0) → MvPowerSeries.coeff μ (Λ.hL g a (a + (i : ZMod d))) = 0) ∧
    ∃ K' : Fin (Λ.rk (1 - g) (a + (i : ZMod d))) →
        MvPowerSeries (Λ.CoG g ⊕ Λ.CoG (1 - g)) 𝓞_ℂ_[l],
      ∀ b, (∑ k : Fin (Λ.rk (1 - g) (a + (i : ZMod d))),
          ((Λ.tan χ (1 - g) (a + (i : ZMod d)) b k : 𝓞_ℂ_[l]) : ℂ_[l]) •
            MvPowerSeries.pderiv ℂ_[l] (Sum.inr k) (Λ.hL g a (a + (i : ZMod d)))) =
        MvPowerSeries.subst
            (Sum.elim (fun x => embL (Λ.tL χ g a x))
              (fun x => embR (Λ.tL χ (1 - g) (a + (i : ZMod d)) x)))
            (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) (K' b)) +
          embL (Λ.zeP χ g a (a + (i : ZMod d)) b)

def GoodC (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) {N : ℕ} (e : Fin N ↪ Fin (Λ.rk g a)) : Prop :=
  ∀ c a'' k, Λ.alC χ g a (e c) 1 a'' k = 0

def RankOneLocalSpread : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2) (a : ZMod d), Λ.big g a → Λ.big g (a + 2) →
    ∀ (N : ℕ) (e : Fin N ↪ Fin (Λ.rk g a)), Λ.GoodC χ g a e →
      ∃ (N' : ℕ) (ρ : Fin N' ↪ Fin N) (κ : Fin N' ↪ Fin (Λ.rk g (a + 2))), N ≤ N' + Λ.j' ∧
        ‖(Matrix.of fun s t : Fin N' =>
          (l : ℂ_[l]) * Λ.alC χ g a (e (ρ s)) 2 (a + 2) (κ t)).det‖ = 1

def RankTwoLocalSpread : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2) (a : ZMod d), Λ.big g a →
    ∀ (N : ℕ) (e : Fin N ↪ Fin (Λ.rk g a)), Λ.GoodC χ g a e →
      ∃ (N' : ℕ) (ρ : Fin N' ↪ Fin N) (κ : Fin N' ↪ Fin (Λ.rk (1 - g) (a + 1))), N ≤ N' + Λ.rh ∧
        ‖(Matrix.of fun s t : Fin N' =>
          (l : ℂ_[l]) * Λ.beP χ g a (e (ρ s)) 1 (a + 1) (κ t)).det‖ = 1

def FrobeniusNormedRingLocal : Prop :=
  ∀ g : Fin 2, ∃ (A : Type) (_ : CommRing A) (φ : A ≃+* A) (θ : A →+* 𝓞_ℂ_[l]) (μ ξ : A)
      (n1 nb : A → ℝ),
    IsDomain A ∧ Function.Surjective θ ∧ RingHom.ker θ = Ideal.span {ξ} ∧ μ = ξ * φ.symm μ ∧
    (∀ x y, n1 (x * y) = n1 x * n1 y) ∧ (∀ x y, nb (x * y) = nb x * nb y) ∧
    (∀ x, ‖((θ x : 𝓞_ℂ_[l]) : ℂ_[l])‖ ≤ n1 x) ∧ (∀ x, nb x ≤ n1 x) ∧ (∀ x, 0 ≤ nb x) ∧
    (∀ x, n1 x ≤ 1) ∧
    n1 (φ.symm μ) = (l : ℝ) ^ (-(1 / ((l : ℝ) - 1))) ∧
    nb (φ.symm μ) = (l : ℝ) ^ (-(1 / ((l : ℝ) - 1))) ∧
    ‖((θ (φ.symm μ) : 𝓞_ℂ_[l]) : ℂ_[l])‖ = (l : ℝ) ^ (-(1 / ((l : ℝ) - 1))) ∧
    nb ξ = (l : ℝ)⁻¹ ∧ (∀ x, nb (φ x) = nb x ^ l) ∧
    ∃ (M : ZMod d → Type) (_ : ∀ a, AddCommGroup (M a)) (_ : ∀ a, Module A (M a))
      (φM : ∀ a, M a →+ M (a + 1))
      (π : ∀ a, M a →+ ((Fin (Λ.rk g a) → 𝓞_ℂ_[l]) →ₗ[𝓞_ℂ_[l]] 𝓞_ℂ_[l]))
      (lam : ∀ a, M a →+ (Fin (Λ.r - Λ.rh - Λ.rk g a) → 𝓞_ℂ_[l]))
      (mT : Λ.Tt g → ∀ a, M a) (u : (𝓞_ℂ_[l])ˣ) (tb : Fin (Λ.r - Λ.rh) → Λ.Tt g),
      (∀ a, Module.Free A (M a) ∧ Module.Finite A (M a) ∧ Module.finrank A (M a) = Λ.r - Λ.rh) ∧
      (∀ a (c : A) (x : M a), φM a (c • x) = φ c • φM a x) ∧
      (∀ a, Function.Injective (φM a)) ∧
      (∀ a (x : M (a + 1)), φ ξ • x ∈ Submodule.span A (Set.range (φM a))) ∧
      (∀ a (x : M a), ∃ y, φM a (ξ • x) = φ ξ • y) ∧
      (∀ a (c : A) (x : M a), (∃ y, φM a x = φ ξ • y) → π a (c • x) = θ c • π a x) ∧
      (∀ a f, ∃ x : M a, (∃ y, φM a x = φ ξ • y) ∧ π a x = f) ∧
      (∀ a (x : M a), (∃ y, φM a x = φ ξ • y) → (π a x = 0 ↔ ∃ y, x = ξ • y)) ∧
      (∀ a (c : A) (x : M a), lam a (c • x) = θ c • lam a x) ∧
      (∀ a, Function.Surjective (lam a)) ∧
      (∀ a (x : M a), lam a x = 0 ↔ ∃ y, φM a x = φ ξ • y) ∧
      (∀ t t', mT (t + t') = mT t + mT t') ∧ Function.Injective mT ∧
      (∀ m : ∀ a, M a, (∀ a, φM a (m a) = φ ξ • m (a + 1)) ↔ ∃ t, mT t = m) ∧
      (∀ t a, π a (mT t a) = (u : 𝓞_ℂ_[l]) • Λ.alHT g t a) ∧
      (∀ a (x : M a), μ • x ∈ Submodule.span A (Set.range (fun t => mT t a))) ∧
      (∀ a, LinearIndependent A (fun i => mT (tb i) a) ∧
        ∀ t, mT t a ∈ Submodule.span A (Set.range (fun i => mT (tb i) a)))

abbrev LfV (N : ℕ) (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d) :=
  Σ ρ : Fin N, (Fin (Λ.rk (gρ ρ) (aρ ρ)) ⊕ Fin (Λ.rk (1 - gρ ρ) (a'ρ ρ)))

def OnLeaves {N : ℕ} (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d)
    (P : MvPolynomial (Λ.LV N) 𝓞_ℂ_[l]) : Prop :=
  ∀ μ ∈ P.support, ∀ x : Λ.LV N, μ x ≠ 0 →
    (x.2.1 = gρ x.1 ∧ x.2.2.1 = aρ x.1) ∨ (x.2.1 = 1 - gρ x.1 ∧ x.2.2.1 = a'ρ x.1)

def letterMap {N : ℕ} (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d) (x : Λ.LV N) :
    MvPolynomial (Λ.LfV N gρ aρ a'ρ) ℂ_[l] :=
  if h : x.2.1 = gρ x.1 ∧ x.2.2.1 = aρ x.1 then
    MvPolynomial.X ⟨x.1, Sum.inl (Fin.cast (by rw [← h.1, ← h.2]) x.2.2.2)⟩
  else if h' : x.2.1 = 1 - gρ x.1 ∧ x.2.2.1 = a'ρ x.1 then
    MvPolynomial.X ⟨x.1, Sum.inr (Fin.cast (by rw [← h'.1, ← h'.2]) x.2.2.2)⟩
  else 0

def coordMap (χ : Λ.Chart) {N : ℕ} (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d) (x : Λ.CV N) :
    MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l] :=
  if h : x.2.1 = gρ x.1 then
    MvPowerSeries.subst (fun k : Fin (Λ.rk x.2.1 (aρ x.1)) =>
        (MvPowerSeries.X ⟨x.1, Sum.inl (Fin.cast (by rw [h]) k)⟩ :
          MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l]))
      (Λ.tL χ x.2.1 (aρ x.1) x.2.2)
  else
    MvPowerSeries.subst (fun k : Fin (Λ.rk x.2.1 (a'ρ x.1)) =>
        (MvPowerSeries.X ⟨x.1, Sum.inr (Fin.cast (by rw [fin_two_eq_one_sub _ _ h]) k)⟩ :
          MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l]))
      (Λ.tL χ x.2.1 (a'ρ x.1) x.2.2)

def leafH {N : ℕ} (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d) :
    MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l] :=
  ∑ ρ : Fin N, MvPowerSeries.subst
    (Sum.elim (fun k => (MvPowerSeries.X ⟨ρ, Sum.inl k⟩ : MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l]))
      (fun k => MvPowerSeries.X ⟨ρ, Sum.inr k⟩)) (Λ.hL (gρ ρ) (aρ ρ) (a'ρ ρ))

def LeafRuleLocal : Prop :=
  ∀ (χ : Λ.Chart) (N : ℕ) (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d),
    (∀ ρ, Λ.big (gρ ρ) (aρ ρ) ∧ Λ.big (1 - gρ ρ) (a'ρ ρ) ∧ Odd (a'ρ ρ - aρ ρ).val) →
    ∀ (P : MvPolynomial (Λ.LV N) 𝓞_ℂ_[l]) (g : MvPowerSeries (Λ.CV N) 𝓞_ℂ_[l]),
      Λ.OnLeaves gρ aρ a'ρ P →
      Λ.ev χ N P g =
        jetAt0 (MvPolynomial.aeval (Λ.letterMap gρ aρ a'ρ)
            (MvPolynomial.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) P))
          (MvPowerSeries.subst (Λ.coordMap χ gρ aρ a'ρ)
              (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) g) *
            mvExp (Λ.leafH gρ aρ a'ρ))

def AdmLoc : Prop := Λ.CartierFrobeniusFormLocal ∧ Λ.RankOneLocalSpread ∧ Λ.LieLeafVanishingLocal ∧ Λ.RankTwoLocalSpread ∧ Λ.FrobeniusNormedRingLocal ∧ Λ.LeafRuleLocal

end LocD

def RealisationStatementAll : Prop :=
  CayleyId → LPDual →
    ThmP ∧ ∃ C : ℝ, ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (Λ : LocD l d), Λ.AdmLoc →
      Λ.LemmaMAt ∧ Λ.UBAt ∧ Λ.CHAt ∧ Λ.ContentAt C

def PtCl (D : Formalism.BasicNotions.D7) (Y : ModuliIntegralCharts.Prov D) (w : Y.Dat) (l : ℕ) [Fact l.Prime] : Type :=
  Σ y : (Y.loc w l).Pt (Y.loc w l).YY,
    {e : ((Y.loc w l).fld y).C ≃+* ℂ_[l] // ∀ x, ‖e x‖ = ‖x‖}

structure Loc (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) where

  dat : ℕ → Y.Dat
  dat_rk : ∀ j, 1 ≤ j → j < D.R.m → Y.rk (dat j) = D.R.r
  dat_jj : ∀ j, 1 ≤ j → j < D.R.m → Y.jj (dat j) = D.R.k + j - 1

  Pt : D.jet.Sit → Type

  la : ∀ i, Pt i → X.PlP (D.jet.loc i).l

  ty : ∀ i, Pt i → ZMod (D.jet.loc i).d → DV.Emb D (D.jet.loc i).l
  ty_succ : ∀ i y a, ty i y (a + 1) = DV.phiPow D 1 (ty i y a)
  ty_inj : ∀ i y, Function.Injective (ty i y)

  ptE : ∀ i, D.jet.jOf i < D.R.m → Pt i ≃ PtCl D Y (dat (D.jet.jOf i)) (D.jet.loc i).l

  loc : ∀ i, Pt i → LocD (D.jet.loc i).l (D.jet.loc i).d

  loc_r : ∀ i y, (loc i y).r = D.R.r
  loc_j : ∀ i y, (loc i y).j = D.jet.jOf i
  loc_j' : ∀ i y, (loc i y).j' = D.R.m - D.jet.jOf i

  loc_big : ∀ i y a,
    ((loc i y).big 0 a ↔ ty i y a ∈ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y))) ∧
    ((loc i y).big 1 a ↔ ty i y a ∉ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y)))

  loc_alt : ∀ i y, (loc i y).Alternating

  loc_rh : ∀ i (h : D.jet.jOf i < D.R.m) (y : Pt i),
    Module.finrank ℤ ((Y.loc (dat (D.jet.jOf i)) (D.jet.loc i).l).Ylat (ptE i h y).1) =
      2 * D.R.f * (loc i y).rh

variable (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) (Lc : Loc D X Y)

def adm1 : Prop := ∀ i y, (Lc.loc i y).CartierFrobeniusFormLocal ∧ (Lc.loc i y).RankOneLocalSpread

def adm2 : Prop := ∀ i y, (Lc.loc i y).LieLeafVanishingLocal

def adm3 : Prop := ∀ i y, (Lc.loc i y).RankTwoLocalSpread

def ArchimedeanSignatureMatching : Prop := CayleyId

def adm5 : Prop := ∀ i y, (Lc.loc i y).FrobeniusNormedRingLocal

def adm6 : Prop := ∀ i y, (Lc.loc i y).LeafRuleLocal

def adm7 : Prop := LPDual

def admitted : Prop :=
  adm1 D X Y Lc ∧ adm2 D X Y Lc ∧ adm3 D X Y Lc ∧ ArchimedeanSignatureMatching ∧ adm5 D X Y Lc ∧ adm6 D X Y Lc ∧ adm7

def Conclusion1 : Prop := ∀ i y, (Lc.loc i y).LemmaMAt

def Conclusion2 : Prop := ThmP

def PointsLemma : Prop := ∀ i y, (Lc.loc i y).UBAt

def Conclusion4 : Prop := ∀ i y, (Lc.loc i y).CHAt

def Conclusion5 (C : ℝ) : Prop := ∀ i y, (Lc.loc i y).ContentAt C

def Stmt (C : ℝ) : Prop :=
  admitted D X Y Lc → Conclusion1 D X Y Lc ∧ Conclusion2 ∧ PointsLemma D X Y Lc ∧ Conclusion4 D X Y Lc ∧ Conclusion5 D X Y Lc C

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (YF x hx i))

def AdmF : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i)

def Conclusion1Family : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion1 (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i)

def Conclusion3Family : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PointsLemma (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i)

def SlopeLemmaFamily : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4 (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i)

def SlopeLossFamily (C : ℝ) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion5 (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i) C

def ShareFamilyAtConstant (C : ℝ) : Prop :=
  AdmF Fm YF LF → Conclusion1Family Fm YF LF ∧ ThmP ∧ Conclusion3Family Fm YF LF ∧ SlopeLemmaFamily Fm YF LF ∧ SlopeLossFamily Fm YF LF C

def KudlaFamilyStatement (_CH : ℝ) : Prop :=
  AdmF Fm YF LF → Conclusion1Family Fm YF LF ∧ ThmP ∧ Conclusion3Family Fm YF LF ∧ SlopeLemmaFamily Fm YF LF ∧
    ∃ C : ℝ, SlopeLossFamily Fm YF LF C

end Family

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ C : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ =>
    ∀ (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
      (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (YF x hx i)),
      ShareFamilyAtConstant Fm YF LF C)




end Formalism.MainNotions.CartierLocalBounds
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.PDVN

variable (D : Formalism.BasicNotions.D7)

def IsConjPl (P P' : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  Formalism.BasicNotions.IsConjPl D.host P P'

def QOk (i : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.QOk D.ntw i Q

def SOk (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) (s : ℤ) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SOk D.ntw i lam s


def kMap (i : D.ntw.Tw) (k : ℕ) : FractionRing (D.ntw.O i) →+* FractionRing (D.ntw.Ok i k) :=
  Formalism.MainNotions.BlochKatoReduction.Gen.kMap D.ntw i k

def thEval (i : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (lam : D.ntw.abelian₂ i) (k : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) : FractionRing (D.ntw.Ok i k) :=
  Formalism.MainNotions.BlochKatoReduction.Gen.thEval D.ntw i Q lam k ψ

def IntAfter (i : D.ntw.Tw) (n : ℕ) (x : FractionRing (D.ntw.O i)) : Prop :=
  ∃ y : D.ntw.O i, algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) y =
    ((D.ntw.l i : ℕ) : FractionRing (D.ntw.O i)) ^ n * x

def ThetaDenominatorWith (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk D i Q →
    ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → ∀ δ, ∃ y : D.ntw.O i, algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) y =
      ((D.ntw.l i : ℕ) : FractionRing (D.ntw.O i)) ^ (N0 i) * D.ntw.th i Q lam δ

def ThetaDenominatorExists : Prop := ∃ N0 : D.ntw.Tw → ℕ, ThetaDenominatorWith D N0

structure Loc where

  cE : ∀ i, D.ntw.abelian₂ i → ℕ

  kap : ∀ i, D.ntw.abelian₂ i → ℕ

  ffP : Finset ℕ

  a0 : ℕ → ℕ
  a0_mem_one_two : ∀ p ∈ ffP, a0 p = 1 ∨ a0 p = 2

  g_mem : ∀ k, D.host.g k ∈ ffP
  pde_mem : D.host.pde ∈ ffP ∧ D.host.pde' ∈ ffP

variable {D} in

def Loc.wt (X : Loc D) (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) : ℝ :=
  (X.kap i lam : ℝ) + (D.ntw.s2 i lam : ℝ) * (D.R.f : ℝ)

def ThetaDenominatorValues (X : Loc D) (C : ℝ) : Prop :=
  ∃ n : ∀ i, D.ntw.abelian₂ i → ℕ,
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ≠ 2 →
      (∀ P ∈ placesOver D.host.E (D.ntw.l i), P.asIdeal.ramificationIdx ℤ = 1) →
      D.ntw.l i ∉ X.ffP → n i lam = 0) ∧
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ∣ D.host.condN →
      (n i lam : ℝ) ≤ X.wt i lam * (2 + C * Formalism.MainNotions.ExistsIdealDenominator.vdd D (D.ntw.l i))) ∧
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ∈ X.ffP → (n i lam : ℝ) ≤ C * (X.a0 (D.ntw.l i) : ℝ) * X.wt i lam) ∧
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk D i Q →
      ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → ∀ δ, IntAfter D i (X.cE i lam + n i lam) (D.ntw.th i Q lam δ)

variable {D} in
theorem IntAfter.mono {i : D.ntw.Tw} {a b : ℕ} (h : a ≤ b) {x : FractionRing (D.ntw.O i)}
    (hx : IntAfter D i a x) : IntAfter D i b x := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨((D.ntw.l i : ℕ) : D.ntw.O i) ^ (b - a) * y, ?_⟩
  rw [map_mul, map_pow, hy, map_natCast, ← mul_assoc, ← pow_add, Nat.sub_add_cancel h]


def familyThetaDenominatorValues {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i)) (C : ℝ) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaDenominatorValues (Fm.D x i) (XF x hx i) C

def eq' {K : Type} [Field K] (Y qms : K) (q : ℕ) : K :=
  Formalism.MainNotions.BlochKatoReduction.Gen.eq' Y qms q

open Classical in

def CharacterTwistTheta : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk D i Q →
    ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → ∀ (P Pb : HeightOneSpectrum (𝓞 D.host.E)) (_hP : P ∈ Q) (_hPb : Pb ∈ Q),
      P ≠ Pb → IsConjPl D P Pb → ∀ (k : ℕ) (ψ : D.ntw.RCG i ((Q.erase P).erase Pb) →* (D.ntw.Ok i k)ˣ)
      (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsFrob (D.nd.plOm.1 P) (normV P) σ →
        thEval D i Q lam k (ψ.comp (D.ntw.res i Q ((Q.erase P).erase Pb)
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))) =
          eq' (kMap D i k (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.Xv i lam P)) *
                algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k))
                  ((ψ (D.ntw.art i ((Q.erase P).erase Pb) σ) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
              (((normV P : ℕ) : FractionRing (D.ntw.Ok i k)) ^ (-s)) (normV P) *
            thEval D i ((Q.erase P).erase Pb) lam k ψ

def OrdRule {σ B : Type} (lx : σ → B) (rk : B → ℕ) (o : List σ) : Prop :=
  o.Pairwise fun u u' => lx u ≠ lx u' → rk (lx u) < rk (lx u')

def oW (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (a : 𝓞 E) : (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) :=
  LinearMap.baseChange ℂ_[l] (DistribSMul.toAddMonoidHom Λ a).toIntLinearMap

structure PtTie {l : ℕ} [Fact l.Prime] (E : Type) [Field E] [NumberField E] {Λ σ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Y : Formalism.MainNotions.ExistsIdealDenominator.PtGeo l Λ σ) {Bx Ex : Type} (lx : σ → Bx) (le : σ → Ex)
    (slx : Bx → (𝓞 E →+* ℂ_[l])) where

  HA : Type
  [acgHA : AddCommGroup HA]
  [modHA : Module ℂ_[l] HA]
  LA : Type
  [acgLA : AddCommGroup LA]
  [modLA : Module ℂ_[l] LA]
  pr : HA →ₗ[ℂ_[l]] LA
  pr_surj : Function.Surjective pr

  oH : 𝓞 E →+* Module.End ℂ_[l] HA
  oL : 𝓞 E →+* Module.End ℂ_[l] LA
  pr_o : ∀ a h, pr (oH a h) = oL a (pr h)

  bx : Module.Basis Bx ℂ_[l] LA
  bx_eig : ∀ a x, oL a (bx x) = slx x a • bx x

  sle : Ex → (𝓞 E →+* ℂ_[l])
  be : Module.Basis Ex ℂ_[l] (ℂ_[l] ⊗[ℤ] Λ)
  be_eig : ∀ a e, oW l E Λ a (be e) = sle e a • be e

  th : 𝓞 E →+* 𝓞 E
  mu : HA →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] Y.H
  mu_bal : ∀ a h w, mu (oH a h) w = mu h (oW l E Λ (th a) w)

  fil : Y.Fil = Submodule.span ℂ_[l] {v | ∃ h w, pr h = 0 ∧ v = mu h w}

  letters : ∀ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id → ∃ b : Module.Basis σ ℂ_[l] (Y.H ⧸ Y.Fil),
    ∀ u, b u = Y.Fil.mkQ (mu (sA (bx (lx u))) (be (le u)))

  all_pairs : ∀ x e, slx x = (sle e).comp th → ∃ u, lx u = x ∧ le u = e

  EL_eq : Y.EL = {L | ∃ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id ∧ (∀ a, sA ∘ₗ oL a = oH a ∘ₗ sA) ∧
    ∀ u, L u = mu (sA (bx (lx u))) (be (le u))}

attribute [instance] PtTie.acgHA PtTie.modHA PtTie.acgLA PtTie.modLA

variable {D} in

structure ValRule (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) where

  Bx : D.ntw.Tw → ℕ → Type
  Ex : D.ntw.Tw → ℕ → Type
  lx : ∀ i j, D.nth.Let i j → Bx i j
  le : ∀ i j, D.nth.Let i j → Ex i j

  slx : ∀ i j, Bx i j → (𝓞 D.host.E →+* ℂ_[D.ntw.l i])

  rk : ∀ i j, Bx i j → ℕ
  rk_inj : ∀ i j, Function.Injective (rk i j)

  ord : ∀ i j, OrdRule (lx i j) (rk i j) (X.ord i j)

  pt : ∀ i j y, PtTie D.host.E (X.pt i j y) (lx i j) (le i j) (slx i j)

variable {D} in

def ValRuled (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop := Nonempty (ValRule X)


variable {D} in

theorem valRuled_of_noPts (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) (h : ∀ i j, IsEmpty (D.nth.Pt i j))
    (e : ∀ i : D.ntw.Tw, 𝓞 D.host.E →+* ℂ_[D.ntw.l i]) : ValRuled X := by
  refine ⟨{
    Bx := fun _ _ => Unit
    Ex := fun _ _ => Unit
    lx := fun _ _ _ => ()
    le := fun _ _ _ => ()
    slx := fun i _ _ => e i
    rk := fun _ _ _ => 0
    rk_inj := fun _ _ _ _ _ => rfl
    ord := fun i j => ?_
    pt := fun i j y => (h i j).elim y }⟩
  unfold OrdRule
  exact List.pairwise_of_forall fun _ _ hne => (hne rfl).elim

variable {D} in

def LiftsIndependence (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j y, ∀ P ∈ D.nth.Harm i j, ∀ L ∈ (X.pt i j y).EL, ∀ L' ∈ (X.pt i j y).EL, ∀ g ∈ (X.pt i j y).Bas,
    (X.pt i j y).PN (X.ord i j) (X.pt i j y).nabD L (P.map (Formalism.MainNotions.ExistsIdealDenominator.iO i)) g =
      (X.pt i j y).PN (X.ord i j) ((X.pt i j y).nab 1) L' (P.map (Formalism.MainNotions.ExistsIdealDenominator.iO i)) g

variable {D} in

def LiftsIndependenceRuled (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop := ValRuled X → LiftsIndependence X

variable {D} in

def EigenLiftScaling (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j y, ∃ L ∈ (X.pt i j y).EL, ∃ U : D.nth.Let i j → (X.pt i j y).H, (∀ u, U u ∈ (X.pt i j y).HO) ∧
    ∀ u, L u - U u ∈ (X.pt i j y).Fil ∧
      ∀ d : ℂ_[D.ntw.l i], ‖d‖ ≤ (D.ntw.l i : ℝ) ^ (-(Formalism.MainNotions.ExistsIdealDenominator.vdd D (D.ntw.l i))) →
        d • (L u - U u) ∈ (X.pt i j y).HO

variable {D} in

def ValueFunctionFormula (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j b (d : D.nexp.Dat i j b) (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))),
    D.nth.datP i j b d ∈ D.nth.Harm i j →
    (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal)) →
    ∀ Ψ : ↥QP → D.nth.Lt i j → Formalism.MainNotions.ExistsIdealDenominator.KK i,
    (∀ (q : ↥QP) P', Formalism.MainNotions.ExistsIdealDenominator.ConjPl D q.1 P' → Formalism.MainNotions.ExistsIdealDenominator.PerI (q.1.asIdeal * P'.asIdeal) (Ψ q)) →
    (fun y => D.nth.thV i j (fun x => D.nth.datPhi i j b d x * ∏ q : ↥QP, Ψ q x) (D.nth.datP i j b d) y)
      ∈ X.FQ i j b QP

variable {D} in

def ValueFunctionRuled (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop := ValRuled X → ValueFunctionFormula X

def eG (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b

def eO (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.eO D.nexp i j b

def AO (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.AO D.nexp i j b

def Fm0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.Fm0 D.nexp i j b

def V0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.V0 D.nexp i j b

def HkIdx (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host) : Prop :=
  Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P

def hkO (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.hkO D.nexp i j b k P

def T3 (i : D.ntw.Tw) (j : ℕ) (b : Bool) (B : Submodule (D.ntw.O i) (D.nexp.Fm i j b)) : Prop :=
  Formalism.MainNotions.IntegralHeckeForms.T3 D.nexp i j b B

def M0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.Mall D.nexp i j b

def Mj (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  M0 D i j b ⊓ (V0 D i j b).restrictScalars (D.ntw.O i)

def ConjugationNormInvariance : Prop :=
  (∀ (i : D.ntw.Tw) (b : Bool), ∃ c : MonoidAlgebra (D.ntw.O i) (G0g D.nd),
    MonoidAlgebra.map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).toAddMonoidHom c =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (D.ntw.O i)) • D.nexp.eAlg i b) ∧
  ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, (M0 D i j b).map (AO D i j b) ≤ Mj D i j b

variable {D} in

def KeyTwoSidedBound (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j, ∃ C : ℝ, ∀ y, (D.ntw.l i : ℝ) ^ (-C) ≤ ‖(X.pt i j y).key‖ ∧ ‖(X.pt i j y).key‖ ≤ (D.ntw.l i : ℝ) ^ C

variable {D} in

def KeyUpperBound (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j, ∃ C : ℝ, ∀ y, ‖(X.pt i j y).key‖ ≤ (D.ntw.l i : ℝ) ^ C

variable {D} in
theorem keyUpper_of_twoSided (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) (h : KeyTwoSidedBound X) : KeyUpperBound X :=
  fun i j => let ⟨C, hC⟩ := h i j; ⟨C, fun y => (hC y).2⟩

variable {D} in

def ExistsUnitClasses (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j, ∃ (n : ℕ) (cp : D.nth.Pt i j → Fin n) (u : Fin n → (D.ntw.O i)ˣ) (tr : D.nth.Pt i j → ℂ_[D.ntw.l i]),
    (∀ y, (X.pt i j y).key = Formalism.MainNotions.ExistsIdealDenominator.iO i (u (cp y) : D.ntw.O i) * tr y) ∧
    (∀ s ∈ Formalism.MainNotions.ExistsIdealDenominator.GalF i (D.nth.MaximalUnramifiedExtension i), ∀ y, tr (X.actG i j s y) = s (tr y) ∧ cp (X.actG i j s y) = cp y) ∧
    (∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → ∀ (k : D.nth.Kq i j P) y, cp (D.nth.actK i j P k y) = cp y) ∧
    ∀ b (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i) →
      ∀ F ∈ X.FQ i j b QP, ∀ c, (fun y => if cp y = c then F y else 0) ∈ X.FQ i j b QP

def inL (w : D.what₂.places.Pl) (y : ℝ) : ℝ := y / (D.what₂.places.ramIdx w : ℝ)

theorem ramIdx_conj (w : D.what₂.places.Pl) :
    D.what₂.places.ramIdx (D.what₂.places.conj w) = D.what₂.places.ramIdx w := by
  have hnat : ∀ (w' : D.what₂.places.Pl) (n : ℕ), 0 ≤ D.what₂.places.val w' (n : D.what₂.LL) := by
    intro w' n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact le_trans (le_min ih (by rw [AddValuation.map_one])) (AddValuation.map_add _ _ _)
  have hint : ∀ (w' : D.what₂.places.Pl) (z : ℤ), 0 ≤ D.what₂.places.val w' (z : D.what₂.LL) := by
    intro w' z
    rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
    · simpa using hnat w' n
    · rw [Int.cast_neg, AddValuation.map_neg]
      simpa using hnat w' n
  have hstar : ∀ n : ℕ, D.what₂.places.val (D.what₂.places.conj w) (n : D.what₂.LL) =
      D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    rw [D.conj_val, star_natCast]
  have hres : D.what₂.places.resChar (D.what₂.places.conj w) = D.what₂.places.resChar w := by
    by_contra hne
    have hcop : Nat.Coprime (D.what₂.places.resChar (D.what₂.places.conj w)) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime _) (D.what₂.places.resChar_prime _)).2 hne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL) +
        (b : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hab
    have hq : 0 < D.what₂.places.val w ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL) := by
      rw [← hstar, D.what₂.places.val_resChar]
      exact_mod_cast D.what₂.places.ramIdx_pos _
    have hp : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
      rw [D.what₂.places.val_resChar]
      exact_mod_cast D.what₂.places.ramIdx_pos _
    have ha : 0 < D.what₂.places.val w ((a : D.what₂.LL) *
        ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]
      exact lt_of_lt_of_le hq (le_add_of_nonneg_left (hint w a))
    have hb : 0 < D.what₂.places.val w ((b : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]
      exact lt_of_lt_of_le hp (le_add_of_nonneg_left (hint w b))
    have hadd := AddValuation.map_add (D.what₂.places.val w) ((a : D.what₂.LL) *
        ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL))
      ((b : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL))
    rw [h1, AddValuation.map_one] at hadd
    exact absurd hadd (not_le.2 (lt_min ha hb))
  have hv := D.what₂.places.val_resChar (D.what₂.places.conj w)
  rw [hres, hstar, D.what₂.places.val_resChar] at hv
  exact_mod_cast hv.symm

def wJ (j : ℕ) : ℝ := ∑ ρ : D.what₂.Tau, DV.wSz D j ρ

def wMax : ℝ := (SizeData₂.lifts D).fold max 0 (wJ D)

def onL (L : SizeData₂ D) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) : ℝ :=
  ∑ j ∈ SizeData₂.lifts D,
    ((inL D w (D.what₂.Ij μ j w : ℝ) +
      inL D (D.what₂.places.conj w) (D.what₂.Ij μ j (D.what₂.places.conj w) : ℝ)) / (D.what₂.D0 : ℝ) - 2 * L.F j w)

def onRj (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ) (j : ℕ) (w : D.what₂.places.Pl) : ℝ :=
  fl j (D.what₂.places.resChar w) + (r j w + r j (D.what₂.places.conj w)) / (D.what₂.D0 : ℝ)

def onR (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ) (w : D.what₂.places.Pl) : ℝ :=
  (∑ j ∈ SizeData₂.lifts D, onRj D fl r j w) + 2 / ((D.what₂.places.resChar w : ℝ) ^ 2)

def onBound (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (D.R.m : ℝ) * (L.sc.L * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * wMax D +
    (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * Real.log L.sc.x)

def onBoundJ (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (L.sc.L * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * wMax D +
    (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * Real.log L.sc.x)

theorem onBound_eq (L : SizeData₂ D) (C : ℝ) : onBound D L C = (D.R.m : ℝ) * onBoundJ D L C := by
  simp only [onBound, onBoundJ]
  ring

def ONTw (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∃ (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ), (∀ j l, 0 ≤ fl j l) ∧ (∀ j w, 0 ≤ r j w) ∧
    (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → onL D L (D.what₂.muAt w) w ≤ onR D fl r w) ∧
    ∀ T : Finset D.what₂.places.Pl, ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (onR D fl r w) ≤ onBound D L C

variable {D} in

theorem ONTw.sum_le {L : SizeData₂ D} {C : ℝ} (h : ONTw D L C) (T : Finset D.what₂.places.Pl)
    (hT : ∀ w ∈ T, D.what₂.muAt w ≠ D.what₂.mu0) :
    ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (onL D L (D.what₂.muAt w) w) ≤ onBound D L C := by
  obtain ⟨fl, r, _, _, hle, hsum⟩ := h
  refine le_trans (Finset.sum_le_sum fun w hw => ?_) (hsum T)
  have h0 : 0 ≤ SizeData₂.lwP w := by
    unfold SizeData₂.lwP Formalism.BasicNotions.lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ h0
  unfold DV.ur
  exact mul_le_mul_of_nonneg_left (hle w (hT w hw)) (Nat.cast_nonneg _)

def ONTwJ (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∃ (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ), (∀ j l, 0 ≤ fl j l) ∧ (∀ j w, 0 ≤ r j w) ∧
    (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → onL D L (D.what₂.muAt w) w ≤ onR D fl r w) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ T : Finset D.what₂.places.Pl,
      ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (onRj D fl r j w) ≤ onBoundJ D L C) ∧
    ∀ T : Finset D.what₂.places.Pl,
      ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (2 / ((D.what₂.places.resChar w : ℝ) ^ 2)) ≤ C

variable {D} in

theorem ONTwJ.toONTw {L : SizeData₂ D} {C : ℝ} (h : ONTwJ D L C) (hC : C ≤ onBound D L C) : ONTw D L (2 * C) := by
  obtain ⟨fl, r, hfl, hr, hle, hJ, h2⟩ := h
  refine ⟨fl, r, hfl, hr, hle, fun T => ?_⟩
  have key : ∀ w, SizeData₂.lwP w * DV.ur D w (onR D fl r w) =
      (∑ j ∈ SizeData₂.lifts D, SizeData₂.lwP w * DV.ur D w (onRj D fl r j w)) +
        SizeData₂.lwP w * DV.ur D w (2 / ((D.what₂.places.resChar w : ℝ) ^ 2)) := by
    intro w
    simp only [onR, DV.ur, mul_add, Finset.mul_sum]
  simp only [key, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have hs : ∑ j ∈ SizeData₂.lifts D, ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (onRj D fl r j w) ≤
      ∑ _j ∈ SizeData₂.lifts D, onBoundJ D L C :=
    Finset.sum_le_sum fun j hj => hJ j hj T
  have hcard : ∑ _j ∈ SizeData₂.lifts D, onBoundJ D L C = onBound D L C := by
    rw [Finset.sum_const, nsmul_eq_mul, onBound_eq]
    simp [SizeData₂.lifts]
  have h2' := h2 T
  have hB : onBound D L (2 * C) = 2 * onBound D L C := by
    simp only [onBound]
    ring
  rw [hB]
  linarith

structure ThetaDenominatorData where

  dat : ∀ i j b, Set (D.nexp.Dat i j b)

def TraceLatticeInclusion (E : Formalism.MainNotions.IntegralHeckeForms.XD D) (T : ThetaDenominatorData D) : Prop := Formalism.MainNotions.IntegralHeckeForms.ThSub D.nexp E T.dat

def DomON (L : SizeData₂ D) (nW : ℕ) (CP : ℝ) : Prop := ∀ j ∈ SizeData₂.lifts D, WeightAlgebra.DomAt D L j nW CP

def SizeConditionTwenty (L : SizeData₂ D) : Prop :=
  10 ^ 4 * zBase L * ((D.R.r + D.R.t : ℕ) : ℝ) ≤ L.sc.b


def OntoIndices (L : SizeData₂ D) (P : ParameterChoice' D L) (PT : ParamsT D L P) (CH : NChoice D) (I : Formalism.MainNotions.TwIn D) (T : ThetaDenominatorData D) (C : ℝ) :
    Prop :=
  DomON D L PT.nWn PT.CP → Formalism.MainNotions.TwConjAt D CH → TraceLatticeInclusion D I.E T → Formalism.MainNotions.TwGoodAt D CH I → ONTw D L C

def OntoIndicesByLift (L : SizeData₂ D) (P : ParameterChoice' D L) (PT : ParamsT D L P) (CH : NChoice D) (I : Formalism.MainNotions.TwIn D) (T : ThetaDenominatorData D) (C : ℝ) :
    Prop :=
  DomON D L PT.nWn PT.CP → Formalism.MainNotions.TwConjAt D CH → TraceLatticeInclusion D I.E T → Formalism.MainNotions.TwGoodAt D CH I → ONTwJ D L C

def OffG (w : D.what₂.places.Pl) : Prop := ∀ i0 : Fin 2, ¬ LiftErrorLocal.Over D i0 w

def GGAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  ∀ B1 B2 : Submodule (D.ntw.O (CH.twI w)) (D.nexp.Fm (CH.twI w) j b),
    B1.FG → B2 ≤ B1 → LiftErrorLocal.spK B2 = LiftErrorLocal.spK B1 → LiftErrorLocal.GStab B1 → LiftErrorLocal.GStab B2 →
    LiftErrorLocal.delq D * LiftErrorLocal.lenQ (D.ntw.l (CH.twI w)) (LiftErrorLocal.psiPart B1) (LiftErrorLocal.psiPart B2) ≤
      LiftErrorLocal.lenQ (D.ntw.l (CH.twI w)) B1 B2 + (LiftErrorLocal.rkK B1 : ℝ) * LiftErrorLocal.vU D (CH.twI w)

def SHAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  (LiftErrorLocal.rkK (D.nexp.Bsup (CH.twI w) j b) : ℝ) / LiftErrorLocal.delq D ≤
                 2 * (Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) : ℝ) ∧
    Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.V0 D.nexp (CH.twI w) j b) = D.what₂.D0 ∧
    (Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) : ℝ) ≤ 2 * D.what₂.D0 ∧
    (D.nexp.Bsup (CH.twI w) j b).map (IntegralHeckeForms.AO D.nexp (CH.twI w) j b) ≤ D.nexp.Bsup (CH.twI w) j b

def SHbAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  LiftErrorLocal.rkK (IntegralHeckeForms.Mall D.nexp (CH.twI w) j b) =
                 Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) ∧
    LiftErrorLocal.rkK (LiftErrorLocal.Mj D (CH.twI w) j b) = D.what₂.D0

def ShareAtTypePrimes (CH : NChoice D) : Prop := ∀ (i0 : Fin 2) w, LiftErrorLocal.Over D i0 w → TwistedAt D w → SHAt D CH w

section Run

variable {D} {CH : NChoice D} (X : LiftErrorLocal.Loc D CH)

def UAt (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (CH.twI w) j b (CH.k' w) (CH.Q w) (X.psiW w b) ≤ LiftErrorLocal.twistV0Submodule D CH w j b ∧
    (D.what₂.Ij (D.what₂.muTw w) j (LiftErrorLocal.plS CH w b) : ℝ) ≤
      (D.what₂.places.ramIdx (LiftErrorLocal.plS CH w b) : ℝ) * X.IsgTw w j b

def LKAt (w : D.what₂.places.Pl) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool),
  (D.nexp.Bsup (CH.twI w) j b).FG ∧ LiftErrorLocal.GStab (D.nexp.Bsup (CH.twI w) j b) ∧
    X.ThN w j h1 h2 b ≤ D.nexp.Bsup (CH.twI w) j b

def DepAt (L : SizeData₂ D) (T : ThetaDenominatorData D) (er : ℕ → ℕ → ℝ) (w : D.what₂.places.Pl) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool), ∃ c : D.ntw.O (CH.twI w), c ≠ 0 ∧
    (∀ x ∈ LiftErrorLocal.psiPart (LiftErrorLocal.GSpan (X.ThN w j h1 h2 b)),
      ∃ z ∈ IntegralHeckeForms.Th D.nexp (CH.twI w) j b (T.dat (CH.twI w) j b),
        ((Nat.card D.nexp.U : ℕ) : D.ntw.O (CH.twI w)) • x = c • z) ∧
    ((X.W j h1 h2).eLa X.TO (X.run j).nus (X.laK (LiftErrorLocal.plS CH w b)) : ℝ) /
        (eWL X.B.KO (X.laK (LiftErrorLocal.plS CH w b)) : ℝ) -
      LiftErrorLocal.vDv (D.ntw.O (CH.twI w)) (D.ntw.l (CH.twI w)) c ≤ L.F j w + er j (D.what₂.places.resChar w)

def WBAt : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
  ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
    s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def DomRun (L : SizeData₂ D) (CP : ℝ) : Prop := ∀ j (_h1 : 1 ≤ j) (_h2 : j ≤ D.R.m), WeightAlgebra.DomAt D L j (X.run j).nW CP

def AdmRun (L : SizeData₂ D) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  DomRun X L H.C1 → LiftErrorLocal.ArchimedeanSignatureMatching D L X H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D X CRd ∧ WBAt X ∧ LiftErrorLocal.adm11 D L X H C2 A2 CR CT CRd

end Run

structure ONObj (CH : NChoice D) (Xd : DivX D) where
  X : LiftErrorLocal.Loc D CH
  X' : LiftErrorLocal.Loc D CH

  I_eq : X'.I = X.I
  c6 : CartierLocalBounds.Loc D Xd X.P6
  c6' : CartierLocalBounds.Loc D Xd X'.P6
  T : ThetaDenominatorData D

def TwistedPlacesCover : Prop := Formalism.MainNotions.N.LocsCoverTw D

section AdmON

variable {D} (L : SizeData₂ D) {CH : NChoice D} {Xd : DivX D} (O : ONObj D CH Xd)

def admA (CA : ℝ) : Prop := LiftErrorLocal.ConjugationNormInvariance D L O.X CA

def unitBoundAtTwistedPlaces : Prop := ∀ w, TwistedAt D w → UAt O.X w

def OffTypePrimeConditions : Prop := ∀ w, OffG D w → TwistedAt D w → GGAt D CH w ∧ SHAt D CH w ∧ SHbAt D CH w ∧
  (D.what₂.places.resChar w ≠ D.host.pde → LKAt O.X w) ∧ (D.what₂.places.resChar w = D.host.pde → LKAt O.X' w)

def OrbitContentCond (C6 : ℝ) : Prop := CartierLocalBounds.Conclusion5 D Xd O.X.P6 O.c6 C6 ∧ CartierLocalBounds.Conclusion5 D Xd O.X'.P6 O.c6' C6

def DepthFromContent (C6 Cd : ℝ) : Prop := OrbitContentCond O C6 →
  ∃ er : ℕ → ℕ → ℝ, (∀ j l, 0 ≤ er j l) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ, ∑ l ∈ S, Real.log (l : ℝ) * er j l ≤ onBoundJ D L Cd) ∧
    (∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w ≠ D.host.pde → DepAt O.X L O.T er w) ∧
    ∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w = D.host.pde → DepAt O.X' L O.T er w

def TypePrimeSizeConds (Cs : ℝ) : Prop :=
  1 ≤ Real.log L.sc.x ∧
    ((O.X.TO : ℝ) + (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2) * (Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ)) ≤
      onBoundJ D L Cs

def AdmON (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 Cd Cs CA : ℝ) : Prop :=
  L.FDef ∧ AdmRun O.X L H C2 A2 CR CT CRd ∧ AdmRun O.X' L H C2 A2 CR CT CRd ∧ admA L O CA ∧ unitBoundAtTwistedPlaces O ∧
    OffTypePrimeConditions O ∧ OrbitContentCond O C6 ∧ DepthFromContent L O C6 Cd ∧ TypePrimeSizeConds L O Cs ∧ TwistedPlacesCover D ∧ ShareAtTypePrimes D CH

end AdmON

abbrev ONObjF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Type 1 :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ONObj (Fm.D x i) (Fm.ex x hx i).nch (Fm.X x i)

section FamON

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (OF : ONObjF Fm)

def AdmONF (H : WeightAlgebra.KHyp) (C2 A2 CR CRd C6 Cd Cs CA : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    AdmON (Fm.L x i) (OF x hx i) H C2 A2 CR (Fm.Ct + 1) CRd C6 Cd Cs CA

def familyOntoIndicesWith (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    OntoIndices (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) (Fm.ex x hx i).nch (OF x hx i).X.I (OF x hx i).T C ∧
      OntoIndicesByLift (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) (Fm.ex x hx i).nch (OF x hx i).X.I (OF x hx i).T C

variable {Fm OF} in

theorem familyOntoIndicesWith.concl {C : ℝ} (h : familyOntoIndicesWith Fm OF C)
    (hg : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      DomON (Fm.D x i) (Fm.L x i) (Fm.parT x hx i).nWn (Fm.parT x hx i).CP ∧ Formalism.MainNotions.TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧ TraceLatticeInclusion (Fm.D x i) (OF x hx i).X.I.E (OF x hx i).T ∧
        Formalism.MainNotions.TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch (OF x hx i).X.I) :
    ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ONTw (Fm.D x i) (Fm.L x i) C ∧ ONTwJ (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨x0, h0⟩ := h
  obtain ⟨x1, h1⟩ := hg
  refine ⟨max x0 x1, fun x hx hxm i => ?_⟩
  obtain ⟨a, b, c, d⟩ := h1 x hx (le_trans (le_max_right _ _) hxm) i
  obtain ⟨p, q⟩ := h0 x hx (le_trans (le_max_left _ _) hxm) i
  exact ⟨p a b c d, q a b c d⟩

end FamON

def FamilyOntoIndicesOfAdmissible (H : WeightAlgebra.KHyp) (C2 A2 CR CRd C6 Cd Cs CA C : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (OF : ONObjF Fm) (_CH : ℝ) :
    Prop :=
  AdmONF Fm OF H C2 A2 CR CRd C6 Cd Cs CA → familyOntoIndicesWith Fm OF C

end Formalism.MainNotions.PDVN

end
end
