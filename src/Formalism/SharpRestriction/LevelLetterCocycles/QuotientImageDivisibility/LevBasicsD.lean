import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open PowerSeries

section EvF

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (m : ℕ)

def Zp : Polynomial O := (1 + Polynomial.X) ^ (p ^ m) - 1

def Zs : PowerSeries O := (1 + PowerSeries.X) ^ (p ^ m) - 1

theorem Zs_coe : ((Zp (O := O) p m : Polynomial O) : PowerSeries O) = Zs p m := by
  simp [Zp, Zs]

theorem X_add_one_monic : (Polynomial.X + 1 : Polynomial O).Monic := by
  simpa using Polynomial.monic_X_add_C (1 : O)

theorem pow_natDegree' : ((1 + Polynomial.X : Polynomial O) ^ (p ^ m)).natDegree = p ^ m := by
  have h1 : (1 + Polynomial.X : Polynomial O).Monic := by rw [add_comm]; exact X_add_one_monic
  have h2 : (1 + Polynomial.X : Polynomial O).natDegree = 1 := by
    rw [add_comm]; simpa using Polynomial.natDegree_X_add_C (1 : O)
  rw [h1.natDegree_pow, h2, mul_one]

theorem Zp_monic : (Zp (O := O) p m).Monic := by
  have h1 : (1 + Polynomial.X : Polynomial O).Monic := by rw [add_comm]; exact X_add_one_monic
  have hpm : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  have h2 := h1.pow (p ^ m)
  unfold Zp
  apply h2.sub_of_left
  rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree h2.ne_zero, pow_natDegree']
  first
  | exact_mod_cast hpm
  | exact WithBot.coe_lt_coe.mpr hpm

private theorem algHom_coe_polynomial_eq_of_X_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (φ ψ : PowerSeries A →ₐ[A] B) (h : φ PowerSeries.X = ψ PowerSeries.X) (r : Polynomial A) :
    φ (r : PowerSeries A) = ψ (r : PowerSeries A) := by
  first
  | (have e := Polynomial.algHom_ext (f := φ.comp (Polynomial.coeToPowerSeries.algHom A))
        (g := ψ.comp (Polynomial.coeToPowerSeries.algHom A)) (by simpa using h)
     simpa using AlgHom.congr_fun e r)
  | (have hC : ∀ a : A, φ ((Polynomial.C a : Polynomial A) : PowerSeries A) =
          ψ ((Polynomial.C a : Polynomial A) : PowerSeries A) := by
        intro a
        have e : ((Polynomial.C a : Polynomial A) : PowerSeries A) = algebraMap A (PowerSeries A) a := by
          first
          | rw [Polynomial.coe_C, PowerSeries.algebraMap_eq]
          | simp [PowerSeries.algebraMap_eq]
        rw [e, AlgHom.commutes, AlgHom.commutes]
     refine Polynomial.induction_on r (fun a => hC a) (fun p q hp hq => ?_) (fun n a _ => ?_)
     · rw [Polynomial.coe_add, map_add, map_add, hp, hq]
     · rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_mul, map_pow,
         map_pow, h, hC])

theorem Zp_natDegree : (Zp (O := O) p m).natDegree = p ^ m := by
  have hpm : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  unfold Zp
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, pow_natDegree']
  rw [Polynomial.natDegree_one, pow_natDegree']; exact hpm

variable (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
include hlm

theorem Zs_res : PowerSeries.map (IsLocalRing.residue O) (Zs p m) = PowerSeries.X ^ (p ^ m) := by
  have hpp : p.Prime := Fact.out
  have hp : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    have h := (IsLocalRing.residue_eq_zero_iff ((p : ℕ) : O)).mpr hlm
    simpa using h
  haveI hk : CharP (IsLocalRing.ResidueField O) p := by
    first
    | exact (CharP.charP_iff_prime_eq_zero hpp).mpr hp
    | exact CharP.charP_of_prime_eq_zero hpp hp
    | (have h1 : ringChar (IsLocalRing.ResidueField O) ∣ p := ringChar.dvd hp
       rcases (Nat.dvd_prime hpp).mp h1 with h2 | h2
       · exact absurd h2 CharP.ringChar_ne_one
       · exact ringChar.of_eq h2)
  haveI : CharP (PowerSeries (IsLocalRing.ResidueField O)) p := by
    first
    | infer_instance
    | exact charP_of_injective_algebraMap' (IsLocalRing.ResidueField O) p
  simp only [Zs, map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
  first
  | (rw [add_pow_char_pow]; simp)
  | (rw [add_pow_expChar_pow]; simp)

theorem Zs_res_ne : PowerSeries.map (IsLocalRing.residue O) (Zs p m) ≠ 0 := by
  rw [Zs_res p m hlm]; exact pow_ne_zero _ PowerSeries.X_ne_zero

theorem Zs_order : (PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (Zs p m)).order.toNat =
    p ^ m := by
  have h : (PowerSeries.map (IsLocalRing.residue O) (Zs p m)).order.toNat = p ^ m := by
    first
    | rw [Zs_res p m hlm, PowerSeries.order_X_pow, ENat.toNat_coe]
    | simp [Zs_res p m hlm]
  exact h

variable {F : Type} [CommRing F] [Algebra O F]

def evP (x : F) (f : PowerSeries O) : F := Polynomial.aeval x (f %ʷ Zs p m)

omit hlm in
theorem evalWeierstrassMod_def (x : F) (f : PowerSeries O) : evP p m x f = Polynomial.aeval x (f %ʷ Zs p m) := rfl

theorem evalWeierstrassMod_eq_aeval_of_eq {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (f q : PowerSeries O)
    (r : Polynomial O) (h : f = Zs p m * q + (r : PowerSeries O)) :
    evP p m x f = Polynomial.aeval x r := by
  have hne := Zs_res_ne p m hlm
  have hW := f.isWeierstrassDivision_weierstrassDiv_weierstrassMod hne
  have hP := Zp_monic (O := O) p m
  have hord : (PowerSeries.map (IsLocalRing.residue O) (Zs p m)).order.toNat = p ^ m := by
    first
    | rw [Zs_res p m hlm, PowerSeries.order_X_pow, ENat.toNat_coe]
    | simp [Zs_res p m hlm]
  rw [evalWeierstrassMod_def]
  generalize hq0 : f /ʷ Zs p m = q0 at hW
  generalize hr0 : f %ʷ Zs p m = r0 at hW ⊢
  have h2 := hW.eq_mul_add
  have e1 : ((r0 - r : Polynomial O) : PowerSeries O) = Zs p m * (q - q0) := by
    rw [Polynomial.coe_sub]; linear_combination h - h2
  have hdiv : (((r0 - r) %ₘ Zp p m + Zp p m * ((r0 - r) /ₘ Zp p m) : Polynomial O) :
      PowerSeries O) = ((r0 - r : Polynomial O) : PowerSeries O) := by
    first
    | rw [Polynomial.modByMonic_add_div _ _ hP]
    | rw [Polynomial.modByMonic_add_div (r0 - r) (Zp p m)]
    | rw [Polynomial.modByMonic_add_div (r0 - r) hP]
  rw [Polynomial.coe_add, Polynomial.coe_mul, Zs_coe] at hdiv
  have H1 : PowerSeries.IsWeierstrassDivision (((r0 - r) %ₘ Zp p m : Polynomial O) : PowerSeries O)
      (Zs p m) (q - q0 - (((r0 - r) /ₘ Zp p m : Polynomial O) : PowerSeries O)) 0 := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · rw [Polynomial.coe_zero, add_zero]; linear_combination hdiv + e1
  have H2 : PowerSeries.IsWeierstrassDivision (((r0 - r) %ₘ Zp p m : Polynomial O) : PowerSeries O)
      (Zs p m) 0 ((r0 - r) %ₘ Zp p m) := by
    refine ⟨?_, ?_⟩
    · first
      | rw [Zs_order p m hlm]
      | rw [hord]
      calc ((r0 - r) %ₘ Zp p m).degree < (Zp (O := O) p m).degree :=
            Polynomial.degree_modByMonic_lt _ hP
        _ = ((p ^ m : ℕ) : WithBot ℕ) := by
            rw [Polynomial.degree_eq_natDegree hP.ne_zero, Zp_natDegree]
    · rw [mul_zero, zero_add]
  have hb : (r0 - r) %ₘ Zp p m = 0 := by
    first
    | exact (PowerSeries.IsWeierstrassDivision.elim hne H1 H2).2.symm
    | exact (H1.elim hne H2).2.symm
    | exact (H2.eq_weierstrassDiv_weierstrassMod hne).2.trans (H1.eq_weierstrassDiv_weierstrassMod hne).2.symm
  have hdvd : Zp p m ∣ r0 - r := (Polynomial.modByMonic_eq_zero_iff_dvd hP).mp hb
  have h3 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hx
  rw [map_sub, sub_eq_zero] at h3
  exact h3

def evR {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) : PowerSeries O →ₐ[O] F where
  toFun := evP p m x
  map_one' := by
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx 1 0 1 (by simp)]; simp
  map_mul' f g := by
    obtain ⟨qf, hf⟩ : ∃ q, f = Zs p m * q + ((f %ʷ Zs p m : Polynomial O) : PowerSeries O) :=
      ⟨_, (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add⟩
    obtain ⟨qg, hg⟩ : ∃ q, g = Zs p m * q + ((g %ʷ Zs p m : Polynomial O) : PowerSeries O) :=
      ⟨_, (g.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add⟩
    have key : f * g = Zs p m * (qf * (Zs p m * qg + ((g %ʷ Zs p m : Polynomial O) : PowerSeries O)) +
        ((f %ʷ Zs p m : Polynomial O) : PowerSeries O) * qg) +
        (((f %ʷ Zs p m) * (g %ʷ Zs p m) : Polynomial O) : PowerSeries O) := by
      calc f * g = (Zs p m * qf + ((f %ʷ Zs p m : Polynomial O) : PowerSeries O)) *
            (Zs p m * qg + ((g %ʷ Zs p m : Polynomial O) : PowerSeries O)) := by rw [← hf, ← hg]
        _ = _ := by rw [Polynomial.coe_mul]; ring
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx (f * g) _ _ key, map_mul]
    rfl
  map_zero' := by
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx 0 0 0 (by simp)]; simp
  map_add' f g := by
    have hf := (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add
    have hg := (g.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx (f + g) (f /ʷ Zs p m + g /ʷ Zs p m) ((f %ʷ Zs p m) + (g %ʷ Zs p m)) ?_,
      map_add]
    · rfl
    · conv_lhs => rw [hf, hg]
      rw [Polynomial.coe_add]
      ring
  commutes' o := by
    show evP p m x (algebraMap O (PowerSeries O) o) = algebraMap O F o
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx _ 0 (Polynomial.C o) (by simp [PowerSeries.algebraMap_eq])]
    simp

theorem evR_apply {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (f : PowerSeries O) :
    evR p m hlm hx f = evP p m x f := rfl

theorem evR_coe {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (r : Polynomial O) :
    evR p m hlm hx (r : PowerSeries O) = Polynomial.aeval x r := by
  rw [evR_apply]
  exact evalWeierstrassMod_eq_aeval_of_eq p m hlm hx _ 0 r (by rw [mul_zero, zero_add])

theorem evR_X {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) :
    evR p m hlm hx PowerSeries.X = x := by
  have h := evR_coe p m hlm hx (Polynomial.X : Polynomial O)
  rwa [Polynomial.coe_X, Polynomial.aeval_X] at h

theorem evR_Zs {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) :
    evR p m hlm hx (Zs p m) = 0 := by
  have h := evR_coe p m hlm hx (Zp (O := O) p m)
  rwa [Zs_coe, hx] at h

theorem evR_subst {x y : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0)
    (hy : Polynomial.aeval y (Zp (O := O) p m) = 0) (u : PowerSeries O)
    (hu : PowerSeries.constantCoeff u = 0) (huy : evR p m hlm hx u = y) (f : PowerSeries O) :
    evR p m hlm hx (PowerSeries.subst u f) = evR p m hlm hy f := by
  have hu' : PowerSeries.HasSubst u := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hu
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hu
  obtain ⟨ψ, hψ⟩ : ∃ ψ : PowerSeries O →ₐ[O] F,
      ∀ g, evR p m hlm hx (PowerSeries.subst u g) = ψ g :=
    ⟨(evR p m hlm hx).comp (PowerSeries.substAlgHom hu'), fun g => by
      first
      | rfl
      | rw [AlgHom.comp_apply, PowerSeries.coe_substAlgHom]
      | simp [PowerSeries.coe_substAlgHom]⟩
  have hX : ψ PowerSeries.X = evR p m hlm hy PowerSeries.X := by
    rw [← hψ, PowerSeries.subst_X hu', huy, evR_X]
  have hpoly := algHom_coe_polynomial_eq_of_X_eq ψ (evR p m hlm hy) hX
  have hS : ψ (Zs p m) = 0 := by
    rw [← Zs_coe, hpoly, evR_coe, hy]
  obtain ⟨q, r, hf⟩ : ∃ (q : PowerSeries O) (r : Polynomial O),
      f = Zs p m * q + (r : PowerSeries O) :=
    ⟨_, _, (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod
      (Zs_res_ne p m hlm)).eq_mul_add⟩
  rw [hψ, hf, map_add, map_add, map_mul, map_mul, hS, evR_Zs p m hlm hy, hpoly]
  simp

end EvF

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def GenUnitsC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (s : ℕ) (u : ℤ_[l]ˣ),
    ((u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) → ((u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) →
      Subgroup.closure (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) = ⊤

section Parts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevBasics (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  inj : Function.Injective (algebraMap O F)
  hp : ((PD.p : ℕ) : F) ≠ 0
  root : ∃ ζ : F, IsPrimitiveRoot ζ (PD.p ^ (s + 1))
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ (ζ : Rs F PD.p s) (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ : Rs F PD.p s, ev ζ (letE a) = 1
  ev_π : ∀ ζ : Rs F PD.p s, ev ζ letπ = (ζ : F) - 1
  ev_ps : ∀ ζ : Rs F PD.p s, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ : Rs F PD.p s, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g (ζ : Rs F PD.p s) x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤

end Parts

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
  {F : Type} [Field F] [Algebra O F]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem root_Zp {y : F} (hy : (1 + y) ^ (p ^ m) = 1) : Polynomial.aeval y (Zp (O := O) p m) = 0 := by
  simp only [Zp, map_sub, map_pow, map_add, map_one, Polynomial.aeval_X, hy, sub_self]

theorem evR_congr {x x' : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0)
    (hx' : Polynomial.aeval x' (Zp (O := O) p m) = 0) (h : x = x') (f : PowerSeries O) :
    evR p m hlm hx f = evR p m hlm hx' f := by
  subst h
  rfl

theorem evR_eq_cc {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (hx0 : x = 0)
    (f : PowerSeries O) : evR p m hlm hx f = algebraMap O F (PowerSeries.constantCoeff f) := by
  subst hx0
  obtain ⟨q, hq⟩ : ∃ q, f = Zs p m * q + ((f %ʷ Zs p m : Polynomial O) : PowerSeries O) :=
    ⟨_, (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add⟩
  show evP p m 0 f = _
  rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx f q _ hq]
  conv_rhs => rw [hq]
  rw [← Polynomial.coeff_zero_eq_aeval_zero']
  simp [Zs]

theorem evR_onePow {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (k : ℕ) :
    evR p m hlm hx ((1 + PowerSeries.X) ^ k) = (1 + x) ^ k := by
  have hX : evR p m hlm hx PowerSeries.X = x := by
    show evP p m x PowerSeries.X = x
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx PowerSeries.X 0 Polynomial.X (by simp)]
    simp
  rw [map_pow, map_add, map_one, hX]

end SlopeTestRemainingChoices

theorem exists_prim {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (N : ℕ) (hN : 0 < N) :
    ∃ ζ : F, IsPrimitiveRoot ζ N := by
  haveI : NeZero (N : F) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N F) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 hN).ne')
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Con

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F]

theorem rs_root (s : ℕ) (ζ : Rs F PD.p s) :
    Polynomial.aeval ((ζ : F) - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
  root_Zp PD.p (s + 1) (by rw [add_sub_cancel]; exact rs_pow_N F PD.p s ζ)

def evAt (a : ZMod n) (s : ℕ) (ζ : Rs F PD.p s) : LetA O n →+* F :=
  (evR PD.p (s + 1) hlm (rs_root F s ζ)).toRingHom.comp
    (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)

theorem evAt_apply (a : ZMod n) (s : ℕ) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ x = evR PD.p (s + 1) hlm (rs_root F s ζ) (x a) := rfl

theorem ev_qp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [CharZero F] (s : ℕ) {y : F}
    (hy : Polynomial.aeval y (Zp (O := O) PD.p (s + 1)) = 0) :
    (evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) = 0) ↔
      (y ≠ 0 ∧ (1 + y) ^ PD.p = 1) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Formalism.MainNotions.N.Pv.LocalLengthBound.eat_qp] at hw
  have hq0 : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    have := congrFun hw 0
    simpa [LocWach.q, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀] using this
  have hwu : evR PD.p (s + 1) hlm hy ((w : LetA O n) 0) ≠ 0 := by
    have hu : IsUnit ((w : LetA O n) 0) := (w.isUnit.map (Pi.evalMonoidHom (fun _ => PowerSeries O) 0))
    exact (hu.map (evR PD.p (s + 1) hlm hy)).ne_zero

  have hXq : PowerSeries.X * W.q₀ = (1 + PowerSeries.X) ^ PD.p - 1 := by
    rw [← W.φ₀_X, Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W]
  have hev : y * evR PD.p (s + 1) hlm hy W.q₀ = (1 + y) ^ PD.p - 1 := by
    have := congrArg (evR PD.p (s + 1) hlm hy) hXq
    rwa [map_mul, evR_X, map_sub, evR_onePow, map_one] at this
  have hsplit : evR PD.p (s + 1) hlm hy W.q₀ = evR PD.p (s + 1) hlm hy ((w : LetA O n) 0) *
      evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    rw [hq0, map_mul]
  constructor
  · intro h0
    have hq : evR PD.p (s + 1) hlm hy W.q₀ = 0 := by rw [hsplit, h0, mul_zero]
    refine ⟨fun hy0 => ?_, ?_⟩
    ·
      have hcc := evR_eq_cc PD.p (s + 1) hlm hy hy0 W.q₀
      have hc : PowerSeries.constantCoeff W.q₀ = ((PD.p : ℕ) : O) := by
        have := congrArg (PowerSeries.coeff 1) hXq
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
        rw [this]
        have e : ((1 + PowerSeries.X) ^ PD.p - 1 : PowerSeries O) =
            (((1 + Polynomial.X) ^ PD.p - 1 : Polynomial O) : PowerSeries O) := by
          simp [Polynomial.coe_pow]
        rw [e, Polynomial.coeff_coe, Polynomial.coeff_sub, Polynomial.coeff_one, add_comm,
          Polynomial.coeff_X_add_one_pow]
        simp
      rw [hq, hc, map_natCast] at hcc
      exact (Nat.cast_ne_zero.2 (hpF.out.ne_zero)) hcc.symm
    · have := hev
      rw [hq, mul_zero] at this
      exact (sub_eq_zero.1 this.symm)
  · rintro ⟨hy0, hyp⟩
    have hq : evR PD.p (s + 1) hlm hy W.q₀ = 0 := by
      have := hev
      rw [hyp, sub_self] at this
      exact (mul_eq_zero.1 this).resolve_left hy0
    rw [hsplit] at hq
    exact (mul_eq_zero.1 hq).resolve_left hwu

end Con

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Bs

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
  {F : Type} [Field F] [Algebra O F] [Algebra ℤ_[p] O] [IsDomain O] [CharZero O]

theorem evR_bs (s : ℕ) {x : F} (hx : Polynomial.aeval x (Zp (O := O) p (s + 1)) = 0) (ζ : F)
    (hxζ : x = ζ - 1) (z : ℤ_[p]) :
    evR p (s + 1) hlm hx (PowerSeries.binomialSeries O z) =
      ζ ^ (PadicInt.toZModPow (s + 1) z).val := by
  set A := (PadicInt.toZModPow (s + 1) z).val with hA
  have hker : z - (A : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ (s + 1)} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hA,
      ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hker
  have hz : z = (A : ℤ_[p]) + (((p ^ (s + 1) : ℕ)) : ℤ_[p]) * w := by
    push_cast; linear_combination -hw
  have hN : 1 ≤ p ^ (s + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  rw [hz, PowerSeries.binomialSeries_add, PowerSeries.binomialSeries_nat,
    ← Formalism.MainNotions.UnusedSlot80.LG.subst_bs (p ^ (s + 1)) hN w, map_mul, evR_onePow,
    show 1 + x = ζ by rw [hxζ]; ring]
  have h0 : Polynomial.aeval (0 : F) (Zp (O := O) p (s + 1)) = 0 := root_Zp p (s + 1) (by simp)
  have hsub := evR_subst p (s + 1) hlm hx h0 ((1 + PowerSeries.X) ^ (p ^ (s + 1)) - 1)
    (by simp) (evR_Zs p (s + 1) hlm hx) (PowerSeries.binomialSeries O w)
  rw [hsub, evR_eq_cc p (s + 1) hlm h0 rfl, PowerSeries.binomialSeries_constantCoeff, map_one, mul_one]

end Bs

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    [IsDomain O] [CharZero O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F]

theorem evAt_ps (a : ZMod n) (s t : ℕ) (ζ : Rs F PD.p s) :
    ∃ hy : Polynomial.aeval ((ζ : F) ^ (PD.p ^ t) - 1) (Zp (O := O) PD.p (s + 1)) = 0,
      evAt hlm F a s ζ (ps W t) =
        evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have hy : Polynomial.aeval ((ζ : F) ^ (PD.p ^ t) - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  refine ⟨hy, ?_⟩
  have hφ := Formalism.MainNotions.UnusedSlot80.LG.phi_pow_X W.φ₀ PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W) t
  have h0 : PowerSeries.constantCoeff ((W.φ₀ ^ t) PowerSeries.X) = 0 := by rw [hφ]; simp
  rw [evAt_apply, Formalism.MainNotions.UnusedSlot80.LG.ps_apply W t a, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst _ h0, hφ]
  refine evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hy _ (by simp) ?_ _
  rw [map_sub, evR_onePow, map_one, add_sub_cancel]

theorem evAt_ps_iff (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [CharZero F] (a : ZMod n) (s t : ℕ)
    (ζ : Rs F PD.p s) : evAt hlm F a s ζ (ps W t) = 0 ↔ t = s := by
  obtain ⟨hy, he⟩ := evAt_ps W hlm F a s t ζ
  rw [he, ev_qp W hlm F hR s hy, add_sub_cancel]
  have hζ : IsPrimitiveRoot (ζ : F) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hp1 : 1 < PD.p := hpF.out.one_lt
  constructor
  · rintro ⟨hne, hpow⟩
    by_contra hts
    rcases Nat.lt_or_gt_of_ne hts with h | h
    ·
      have hprim := hζ.pow_of_dvd (pow_ne_zero t hpF.out.ne_zero)
        (pow_dvd_pow PD.p (by omega : t ≤ s + 1))
      rw [Nat.pow_div (by omega) hpF.out.pos] at hprim
      have hd := hprim.dvd_of_pow_eq_one PD.p hpow
      have h1 := Nat.le_of_dvd hpF.out.pos hd
      have h2 : PD.p ^ 2 ≤ PD.p ^ (s + 1 - t) := Nat.pow_le_pow_right hpF.out.pos (by omega)
      have h3 : PD.p < PD.p ^ 2 := by nlinarith
      omega
    ·
      apply hne
      rw [sub_eq_zero]
      obtain ⟨k, hk⟩ : PD.p ^ (s + 1) ∣ PD.p ^ t := pow_dvd_pow PD.p (by omega)
      rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  · rintro rfl
    have hprim := hζ.pow_of_dvd (pow_ne_zero t hpF.out.ne_zero)
      (pow_dvd_pow PD.p (by omega : t ≤ t + 1))
    rw [Nat.pow_div (by omega) hpF.out.pos, show t + 1 - t = 1 by omega, pow_one] at hprim
    exact ⟨sub_ne_zero.2 (hprim.ne_one hp1), hprim.pow_eq_one⟩

end Main

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Fin

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    [IsDomain O] [CharZero O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F] [Algebra ℤ_[PD.p] O]

theorem evAt_γ (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O)) (a : ZMod n) (s : ℕ)
    (g : W.Gam) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ (W.γA g x) = evAt hlm F a s (powR F PD.p s (redU PD.p s (z g)) ζ) x := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have h0 := (W.γ₀_X g).1
  have h1 : PowerSeries.coeff 1 (W.γ₀ g PowerSeries.X) = algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) := by
    rw [(W.γ₀_X g).2, hz g]
  have hbs := Formalism.MainNotions.UnusedSlot80.LG.aut_eq_bs W.φ₀ (W.γ₀ g) PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W)
    (fun a => W.γ₀_comm g a) h0 (z g : ℤ_[PD.p]) h1
  set A := (PadicInt.toZModPow (s + 1) (z g : ℤ_[PD.p])).val with hA
  have hyA : Polynomial.aeval ((ζ : F) ^ A - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  rw [evAt_apply, evAt_apply]
  have e1 : (W.γA g x) a = W.γ₀ g (x a) := rfl
  have huy : evR PD.p (s + 1) hlm (rs_root F s ζ) (W.γ₀ g PowerSeries.X) = (ζ : F) ^ A - 1 := by
    have e : W.γ₀ g PowerSeries.X = PowerSeries.binomialSeries O (z g : ℤ_[PD.p]) - 1 := by
      rw [← hbs]; ring
    rw [e, map_sub, evR_bs PD.p hlm s (rs_root F s ζ) (ζ : F) rfl, map_one]
  rw [e1, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst (W.γ₀ g) h0,
    evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hyA _ h0 huy]
  exact evR_congr PD.p (s + 1) hlm hyA _ rfl _

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in

theorem gen_of (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert (redU PD.p s (z W.gam))
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ := by
  obtain ⟨z0, hz0, hv⟩ := hγz
  have hzg : z W.gam = z0 := Units.ext (hZinj (by rw [hz, hz0]))
  have hne : (z0 : ℤ_[PD.p]) - 1 ≠ 0 := by
    intro h; rw [h, PadicInt.valuation_zero] at hv; exact zero_ne_one hv
  have hu1 : (z0 : ℤ_[PD.p]) - 1 ∈ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p])} := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by rw [hv])
    rwa [pow_one] at this
  have hu2 : (z0 : ℤ_[PD.p]) - 1 ∉ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p]) ^ 2} := by
    intro h
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 2).1 h
    rw [hv] at this; omega
  have htop := hGen PD.p hp2 s z0 hu1 hu2

  have hl2 := hpF.out.two_le
  obtain ⟨H, hH⟩ : ∃ H : Subgroup W.Gam, (H : Set W.Gam) = ↑W.DelF := ⟨
    { carrier := ↑W.DelF
      mul_mem' := by
        intro a b ha hb
        simp only [Finset.mem_coe, W.DelF_def] at ha hb ⊢
        obtain ⟨k, hk, hak⟩ := ha
        obtain ⟨k', hk', hbk⟩ := hb
        exact ⟨k * k', Nat.mul_pos hk hk', by
          rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbk, one_pow]⟩
      one_mem' := by
        simp only [Finset.mem_coe, W.DelF_def]
        exact ⟨1, one_pos, one_pow _⟩
      inv_mem' := by
        intro a ha
        simp only [Finset.mem_coe, W.DelF_def] at ha ⊢
        obtain ⟨k, hk, hak⟩ := ha
        exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩ }, rfl⟩
  have memH : ∀ x, x ∈ H ↔ x ∈ W.DelF := fun x => by
    rw [← SetLike.mem_coe, hH, Finset.mem_coe]
  have hHcard : Nat.card H = PD.p - 1 := by
    rw [← hcard, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight memH)
  have hexp : ∀ δ ∈ W.DelF, δ ^ (PD.p - 1) = 1 := by
    intro δ hδ
    have h : (⟨δ, (memH δ).mpr hδ⟩ : H) ^ (PD.p - 1) = 1 := by
      rw [← hHcard]
      exact pow_card_eq_one'
    have h2 := congrArg (fun y : H => (y : W.Gam)) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2

  have hzΔ : ∀ δ : ↥W.DelF, (z δ) ^ (PD.p - 1) = 1 := by
    intro δ
    apply Units.ext
    apply hZinj
    rw [Units.val_pow_eq_pow_val, map_pow, hz, ← Units.val_pow_eq_pow_val, ← map_pow,
      hexp δ δ.2, map_one]
    simp
  let zΔ : ↥W.DelF → DeltaT PD.p := fun δ => ⟨z δ, hzΔ δ⟩
  have hinj : Function.Injective zΔ := by
    intro δ δ' h
    have h1 : z δ = z δ' := congrArg Subtype.val h
    have h2 : W.χΓ δ = W.χΓ δ' := Units.ext (by rw [← hz, ← hz, h1])
    exact Subtype.ext (W.χΓ_inj h2)
  haveI : NeZero (PD.p - 1) := ⟨by omega⟩
  let e : DeltaT PD.p ≃ ↥(rootsOfUnity (PD.p - 1) ℤ_[PD.p]) :=
    Equiv.subtypeEquivRight fun x => (mem_rootsOfUnity (PD.p - 1) x).symm
  haveI : Finite (DeltaT PD.p) := Finite.of_equiv _ e.symm
  have hle : Nat.card (DeltaT PD.p) ≤ Nat.card ↥W.DelF := by
    rw [Nat.card_congr e, Nat.card_eq_finsetCard, hcard]
    exact card_rootsOfUnity ℤ_[PD.p] (PD.p - 1)
  have hsurj := (hinj.bijective_of_nat_card_le hle).2
  rw [eq_top_iff, ← htop]
  apply Subgroup.closure_mono
  intro u hu
  rcases Set.mem_insert_iff.1 hu with rfl | ⟨d, rfl⟩
  · exact Set.mem_insert_iff.2 (Or.inl (by rw [hzg]))
  · obtain ⟨δ, hδ⟩ := hsurj d
    refine Set.mem_insert_of_mem _ ⟨δ, δ.2, ?_⟩
    show redU PD.p s (z δ) = redU PD.p s d.1
    rw [← hδ]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in
theorem gen_of' (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert ((fun g => redU PD.p s (z g)) W.gam)
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ :=
  gen_of W z hz hZinj hγz hcard hp2 hGen s

def levBasics_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [IsAlgClosed F] [CharZero F]
    (hinjF : Function.Injective (algebraMap O F))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hχ : ∀ g : W.Gam, ∃ z : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z : ℤ_[PD.p]) = (W.χΓ g : O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (a : ZMod n) (s : ℕ) :
    LevBasics W a s where
  F := F
  fF := inferInstance
  algOF := inferInstance
  inj := hinjF
  hp := Nat.cast_ne_zero.2 hpF.out.ne_zero
  root := exists_prim _ (pow_pos hpF.out.pos _)
  ev := evAt hlm F a s
  ev_O ζ x := by
    rw [evAt_apply]
    exact (evR PD.p (s + 1) hlm (rs_root F s ζ)).commutes x
  ev_letE ζ := by
    rw [evAt_apply]
    simp [letE]
  ev_π ζ := by
    rw [evAt_apply]
    exact evR_X PD.p (s + 1) hlm (rs_root F s ζ)
  ev_ps ζ := (evAt_ps_iff W hlm F hR a s s ζ).2 rfl
  ev_pt t ht ζ := fun h => ht ((evAt_ps_iff W hlm F hR a s t ζ).1 h)
  σ g := redU PD.p s (Classical.choose (hχ g))
  ev_γ g ζ x := evAt_γ W hlm F (fun g => Classical.choose (hχ g))
    (fun g => Classical.choose_spec (hχ g)) a s g ζ x
  gen := gen_of' W (fun g => Classical.choose (hχ g)) (fun g => Classical.choose_spec (hχ g))
    hZinj hγz hcard hp2 hGen s

end Fin

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def castZp {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) : ℤ_[a] →+* ℤ_[b] := by
  subst e; exact RingHom.id _

theorem castZp_symm {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) (x : ℤ_[b]) :
    castZp e (castZp e.symm x) = x := by
  subst e; rfl

theorem castZp_val {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) (x : ℤ_[a]) :
    (castZp e x).valuation = x.valuation := by
  subst e; rfl

theorem castZp_inj {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) :
    Function.Injective (castZp e) := by
  subst e; exact fun x y h => h

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end
