import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ReadingAllLemmas

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll.Model

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X}









variable (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

theorem bsup_eq (i : X.Tw) (j : ℕ) (b : Bool) : Y.Bsup i j b = Submodule.span (X.O i) (Ball T i j b 1) :=
  T.Bsup_def i j b

theorem norm_l (i : X.Tw) : ‖((X.l i : ℕ) : ℂ_[X.l i])‖ = ((X.l i : ℝ))⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[X.l i] (PadicComplex (X.l i))), norm_algebraMap', Padic.norm_p]

theorem smul_l_pow (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b) :
    ((X.l i : X.O i) ^ c) • f = ((X.l i : FractionRing (X.O i)) ^ c) • f := by
  rw [← algebraMap_smul (FractionRing (X.O i))]
  simp

theorem l_pow_smul_mem (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (B : ℝ) (f : Y.Fm i j b)
    (hf : f ∈ Ball T i j b ((X.l i : ℝ) ^ c * B)) : ((X.l i : X.O i) ^ c) • f ∈ Ball T i j b B := by
  have hl : (0 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.pos
  rw [smul_l_pow]
  refine ⟨T.FmUr_smul i j b _ _ (pow_mem (natCast_mem _ _) _) hf.1, fun y => ?_⟩
  rw [T.ev_smul, norm_mul, map_pow, map_natCast, norm_pow, norm_l, inv_pow]
  rw [inv_mul_le_iff₀ (by positivity)]
  exact hf.2 y

theorem l_pow_smul_span (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b)
    (hf : f ∈ Submodule.span (X.O i) (Ball T i j b ((X.l i : ℝ) ^ c))) :
    ((X.l i : X.O i) ^ c) • f ∈ Y.Bsup i j b := by
  rw [bsup_eq T]
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (l_pow_smul_mem T i j b c 1 x (by simpa using hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx




theorem span_bsup_of_supBdd (h : SupBdd T) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) : Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b)) = ⊤ := by
  rw [eq_top_iff, ← T.FmUr_span i j b, Submodule.span_le]
  intro f hf
  obtain ⟨B, hB⟩ := h i hi j hj b f hf
  have hl : (1 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.one_lt
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt B hl
  have h1 : f ∈ Ball T i j b ((X.l i : ℝ) ^ c) := ⟨hB.1, fun y => (hB.2 y).trans hc.le⟩
  have h2 := l_pow_smul_span T i j b c f (Submodule.subset_span h1)
  rw [smul_l_pow] at h2
  have hne : ((X.l i : FractionRing (X.O i))) ≠ 0 := by
    intro h0
    have := congrArg (T.iC i) h0
    rw [map_natCast, map_zero] at this
    exact (X.lPrime i).out.ne_zero (by exact_mod_cast this)
  have h3 := (Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b))).smul_mem
    (((X.l i : FractionRing (X.O i)) ^ c)⁻¹) (Submodule.subset_span h2)
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul] at h3



theorem l_ne_zero (T : NTh D.R D.host D.what₂ D.LL0 N X Y) (i : X.Tw) : ((X.l i : FractionRing (X.O i))) ≠ 0 := by
  intro h0
  have := congrArg (T.iC i) h0
  rw [map_natCast, map_zero] at this
  exact (X.lPrime i).out.ne_zero (by exact_mod_cast this)



end GlobalTheory.TwAll.Model

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw.Model

open GlobalTheory.TwAll GlobalTheory.TwAll.Model

variable (D : D7)






instance finG : Finite (G0g D.nd) := by
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  infer_instance

abbrev Pt (j : ℕ) : Type := {_g : G0g D.nd // j ∈ Finset.Icc 1 D.R.m}

instance finPt (j : ℕ) : Fintype (Pt D j) := Fintype.ofFinite _

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

@[reducible] def tw : @NTw D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd :=
  { D.ntw with
    B := fun i j _ => Pt D j → D.ntw.O i
    acgB := fun _ _ _ => inferInstance
    modB := fun _ _ _ => inferInstance
    freeB := fun _ _ _ => inferInstance
    finB := fun _ _ _ => inferInstance
    Theta := fun _ _ _ => ⊤
    ThetaPsi := fun _ _ _ _ _ _ => ⊤
    ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_top _).symm
    hk := fun _ _ _ _ _ => 1
    hk_zero := fun _ _ _ _ => rfl
    hEig := fun _ _ _ _ => 1 }

def transl (i : D.ntw.Tw) (j : ℕ) : G0g D.nd →* ((Pt D j → KK D i) ≃ₗ[KK D i] (Pt D j → KK D i)) where
  toFun g :=
    { toFun := fun f y => f ⟨y.1 * g, y.2⟩
      invFun := fun f y => f ⟨y.1 * g⁻¹, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun f => by funext y; simp
      right_inv := fun f => by funext y; simp }
  map_one' := by ext f y; simp
  map_mul' g h := by ext f y; simp [mul_assoc]

def intF (i : D.ntw.Tw) (j : ℕ) : (Pt D j → D.ntw.O i) →ₗ[D.ntw.O i] (Pt D j → KK D i) :=
  (Algebra.linearMap (D.ntw.O i) (KK D i)).compLeft _

variable (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)

@[reducible] def ex : @NExp D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D) :=
  { D.nexp with
    Fm := fun i j _ => Pt D j → KK D i
    acgFm := fun _ _ _ => inferInstance
    modFmK := fun _ _ _ => inferInstance
    modFmO := fun _ _ _ => inferInstance
    towFm := fun _ _ _ => inferInstance
    fdFm := fun _ _ _ => inferInstance
    actG := fun i j _ => transl D i j
    U := ⊥
    psiU := fun _ _ => 1
    Bsup := fun i j _ => LinearMap.range (intF D i j)
    Dat := fun i j _ => Pt D j → KK D i
    th := fun _ _ _ a => a
    lev := fun _ _ _ _ => ∅
    thPsi := fun i _ _ k _ _ a => {(1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] a}
    thPsi_one := fun _ _ _ _ _ => rfl
    thU := fun i _ _ Q M a => (s i M • a) ⊗ₜ[D.ntw.O i]
      AddMonoidAlgebra.single (0 : DelQM D.host (D.ntw.l i) Q M) (1 : D.ntw.O i)
    twPsi := fun i j _ k _ => TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i k) (Pt D j → KK D i) 1
    twPsi_one := fun _ _ _ _ _ => rfl
    twDel := fun _ _ _ _ _ => 0
    thP := fun _ _ _ _ _ _ => 0
    hkF := fun i j _ => A i j
    embB := fun i j _ => intF D i j
    embB_inj := fun i j _ f g h => by
      funext y
      exact IsFractionRing.injective (D.ntw.O i) (KK D i) (congrFun h y)
    eH := fun _ _ _ => 1
    eH_idem := fun _ _ _ => mul_one _ }

theorem mem_intF (i : D.ntw.Tw) (j : ℕ) (f : Pt D j → KK D i) :
    f ∈ LinearMap.range (intF D i j) ↔ ∀ y, f y ∈ (algebraMap (D.ntw.O i) (KK D i)).range := by
  constructor
  · rintro ⟨g, rfl⟩ y
    exact ⟨g y, rfl⟩
  · intro h
    choose g hg using h
    exact ⟨g, funext hg⟩

open Classical in

@[reducible] def th : @NTh D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D) (ex D A s) :=
  { D.nth with
    Pt := fun _ j => Pt D j
    ev := fun i j _ => (D.nth.iC i).toAddMonoidHom.compLeft _
    ev_smul := fun i j _ a f y => map_mul (D.nth.iC i) a (f y)
    ev_inj := fun i j _ f g h => by
      funext y
      exact (D.nth.iC i).injective (congrFun h y)
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => (add_zero _).symm
    thV_smul := fun _ _ _ _ _ _ => (mul_zero _).symm
    thV_addP := fun _ _ _ _ _ _ => (add_zero _).symm
    thV_smulP := fun _ _ _ _ _ _ => (mul_zero _).symm
    datPhi := fun _ _ _ _ _ => 0
    datP := fun _ _ _ _ => 0
    recDet := fun _ _ _ => 1
    Kq := fun _ _ _ => PUnit
    grpKq := fun _ _ _ => inferInstance
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun _ j _ _ => Pt D j
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun _ _ _ _ c _ => c
    hkU := fun i j _ k P c y => D.nth.iC i (A i j k P (Pi.single c 1) y)
    hk_ev := fun i j _ k P _ _ _ _ f y => by
      change D.nth.iC i (A i j k P f y) = ∑ c, D.nth.iC i (A i j k P (Pi.single c 1) y) * D.nth.iC i (f c)
      simp_rw [← map_mul, ← map_sum]
      congr 1
      conv_lhs => rw [pi_eq_sum_univ' f]
      simp [map_sum, mul_comm]
    MaximalUnramifiedExtension := fun _ => ⊤
    FmUr := fun _ _ _ => ⊤
    FmUr_smul := fun _ _ _ _ _ _ _ => trivial
    FmUr_span := fun _ _ _ => by simp
    Bsup_def := fun i j _ => by
      have : {f : Pt D j → KK D i | f ∈ (⊤ : AddSubgroup (Pt D j → KK D i)) ∧ ∀ y, ‖D.nth.iC i (f y)‖ ≤ 1} =
          (LinearMap.range (intF D i j) : Set _) := by
        ext f
        simp only [AddSubgroup.mem_top, true_and, Set.mem_setOf_eq, SetLike.mem_coe, mem_intF, D.nth.iC_int]
      change LinearMap.range (intF D i j) = Submodule.span _
        {f : Pt D j → KK D i | f ∈ (⊤ : AddSubgroup (Pt D j → KK D i)) ∧ ∀ y, ‖D.nth.iC i (f y)‖ ≤ 1}
      rw [this, Submodule.span_eq] }

@[reducible] def rec : D7 := { D with ntw := tw D, nexp := ex D A s, nth := th D A s }


def dat : XD (rec D A s) where
  Dat0 := fun _ _ _ => Set.univ
  theta_base_equivariant := fun i j b a _ u => by
    have hu : (u : G0g D.nd) = 1 := Subgroup.mem_bot.1 u.2
    rw [hu]
    funext y
    simp [transl]

theorem inNonzeroPlaces_recursive_iff (i : D.ntw.Tw) : (rec D A s).ntw.NonzeroIndexPlace i ↔ D.ntw.NonzeroIndexPlace i := Iff.rfl



theorem supG : SupG (rec D A s) := fun i _ j _ _ g f hf =>
  (mem_intF D i j _).2 fun y => (mem_intF D i j f).1 hf ⟨y.1 * g, y.2⟩

theorem exists_pow (i : D.ntw.Tw) (j : ℕ) (f : Pt D j → KK D i) :
    ∃ c : ℕ, ((D.ntw.l i : D.ntw.O i) ^ c) • f ∈ LinearMap.range (intF D i j) := by
  have hl : (1 : ℝ) < D.ntw.l i := by exact_mod_cast (D.ntw.lPrime i).out.one_lt
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt (∑ y, ‖D.nth.iC i (f y)‖) hl
  refine ⟨c, l_pow_smul_span (D := rec D (fun _ _ _ _ => 1) (fun _ _ => 1)) (th D (fun _ _ _ _ => 1) (fun _ _ => 1))
    i j true c f (Submodule.subset_span ⟨trivial, fun y => ?_⟩)⟩
  exact (Finset.single_le_sum (f := fun y => ‖D.nth.iC i (f y)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ y)).trans hc.le

theorem supFull : SupFull (rec D A s) := fun i hi j hj b =>
  ⟨by
    change (LinearMap.range (intF D i j)).FG
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top,
   span_bsup_of_supBdd (D := rec D A s) (th D A s) (fun i _ j _ b f _ =>
    ⟨∑ y, ‖D.nth.iC i (f y)‖, trivial, fun y => Finset.single_le_sum (f := fun y => ‖D.nth.iC i (f y)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ y)⟩) i hi j hj b⟩



abbrev scal (t : ∀ i : D.ntw.Tw, ℕ → KK D i) :
    ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i) :=
  fun i _ k _ => t i k • LinearMap.id









open Classical in

def unitOp (i : D.ntw.Tw) (j : ℕ) (g₁ g₀ : G0g D.nd) : Module.End (KK D i) (Pt D j → KK D i) where
  toFun f y := if y.1 = g₁ then f ⟨g₀, y.2⟩ else 0
  map_add' f f' := by funext y; by_cases h : y.1 = g₁ <;> simp [h]
  map_smul' a f := by funext y; by_cases h : y.1 = g₁ <;> simp [h]



end GlobalTheory.SupLaw.Model

end
end
