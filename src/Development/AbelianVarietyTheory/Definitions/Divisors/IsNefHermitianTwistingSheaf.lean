import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.VolBr.Model

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem ratVal_add {σ : k →+* ℂ} {y : CxPts p σ} {f g : X.functionField} (hf : RegAt (under y) f)
    (hg : RegAt (under y) g) : ratVal (f + g) y = ratVal f y + ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]

theorem ratVal_intCast_mul {σ : k →+* ℂ} {y : CxPts p σ} {f : X.functionField} (hf : RegAt (under y) f) (n : ℤ) :
    RegAt (under y) ((n : X.functionField) * f) ∧ ratVal ((n : X.functionField) * f) y = n * ratVal f y := by
  have h : (n : X.functionField) = fnOf ⊤ (Opens.mem_top _) (n : Γ(X, ⊤)) := (map_intCast _ n).symm
  have hr : RegAt (under y) (n : X.functionField) := ⟨n, map_intCast _ n⟩
  refine ⟨hr.mul hf, ?_⟩
  rw [ratVal_mul hr hf, h, ratVal_fnOf mem_ptsIn_top, ev_eq mem_ptsIn_top, map_intCast]


theorem div_eq {B : LB X} {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) {i j : B.ι}
    (h : genericPoint X ∈ B.U i ⊓ B.U j) :
    (r i : X.functionField) / r j = fnOf _ h (B.g i j : Γ(X, B.U i ⊓ B.U j)) := by
  rw [hr i j h, mul_div_cancel_right₀ _ (r j).ne_zero]


section Two

variable (A : HermLB p) (u : A.B.Sec) (hu : genericPoint X ∈ nonzeroLocus u)

abbrev dbl : Pair p := ⟨A, A, ratOfSec u hu, ratOfSec u hu, isRatSec_ratOfSec u hu, isRatSec_ratOfSec u hu⟩

variable {A u hu}

end Two

omit [IsIntegral X] in

theorem isNef_of_small {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (hs : L.SemiPos D) (hf : ArInt.NefFib L)
    (hg : ∀ x : X, ∃ u ∈ L.smallSec, x ∈ nonzeroLocus u) : L.IsNef D where
  semiPos := hs
  vertical := hf
  horizontal Z i _ _ _ hc hd := by
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
    obtain ⟨u, hu, ha⟩ := hg (i (genericPoint Z))
    have hgen : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
      rw [GlobalTheory.nonzeroLocus_secPull]; exact ha
    have h0 : ∀ σ (y : CxPts (i ≫ p) σ), y ∈ ptsIn _ σ (nonzeroLocus (GlobalTheory.secPull u i)) := fun σ y => by
      refine mem_ptsIn.2 ?_
      have key : ∀ y : Sp ℂ ⟶ Z, y (IsLocalRing.closedPoint ℂ) = genericPoint Z := fun y =>
        GlobalTheory.HtSelfInter.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
      rw [key]
      exact hgen
    refine ⟨_, isRatSec_ratOfSec _ hgen, ?_⟩
    rw [HermLB.curveDeg_sec i u hgen h0]
    refine sub_nonneg.2 (le_trans (b := 0) ?_ ?_)
    · refine finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun σ =>
        finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun y => ?_
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (Weight.nsq_nonneg _ _ _) (hu σ _)) zero_le_two
    · exact finsum_nonneg fun z =>
        mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)

local instance isIntegral_line : IsIntegral (PSpace ℤ 1) := isIntegral_of_isDomain ℤ 1

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem gen_mem_coord (a : Fin 2) : genericPoint (PSpace ℤ 1) ∈ nonzeroLocus (coord ℤ 1 a) := by
  let η : ProjectiveSpectrum (grading ℤ 1) := ⟨⊥, Ideal.isPrime_bot, fun h =>
    MvPolynomial.X_ne_zero _ (h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem ℤ 1 0)))⟩
  rw [nonzeroLocus_coord]
  exact gen_mem (x := η) fun h => MvPolynomial.X_ne_zero a h

section IntValues

open IntExample

theorem exists_int_of_regAt {f : (Sp ℤ).functionField} (h : ∀ x, RegAt x f) : ∃ n : ℤ, f = n := by
  obtain ⟨a, ha⟩ := exists_fnOf_eq (U := ⊤) trivial fun x _ => h x
  obtain ⟨n, rfl⟩ := ArithBase.surjective_intCast (𝟙 (Sp ℤ)) a
  exact ⟨n, ha.symm.trans (map_intCast _ n)⟩

theorem ratVal_int {σ : k →+* ℂ} (y : CxPts p σ) (n : ℤ) : ratVal (n : X.functionField) y = n := by
  have := (ratVal_intCast_mul (y := y) (unitAt_one _).regAt n).2
  have e := ratVal_nat y 1
  rw [Nat.cast_one, Nat.cast_one] at e
  rwa [mul_one, e, mul_one] at this

def intPt : CxPts (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) :=
  ⟨Spec.map (CommRingCat.ofHom (Int.castRingHom ℂ)), Category.comp_id _⟩

theorem rep_iff (a b : ℤ) (t : ℝ) : pair.Rep a b (ArithBase.trivShift t) ↔ t = b * Real.log 3 := by
  refine ⟨fun ⟨ρ, _, hu, hn⟩ => ?_, fun h => h ▸ rep a b⟩
  have := charZero_functionField
  have hu' (x) : UnitAt x (ρ PUnit.unit : (Sp ℤ).functionField) := by
    have := hu x PUnit.unit PUnit.unit PUnit.unit trivial trivial trivial
    erw [loc_eq] at this
    rwa [div_one] at this
  obtain ⟨m, hm⟩ := exists_int_of_regAt fun x => (hu' x).regAt
  obtain ⟨m', hm'⟩ := exists_int_of_regAt fun x => (hu' x).inv.regAt
  have h1 : m * m' = 1 := by
    have : ((m * m' : ℤ) : (Sp ℤ).functionField) = (1 : ℤ) := by
      push_cast; rw [← hm, ← hm', mul_inv_cancel₀ (Units.ne_zero _)]
    exact Int.cast_injective this
  have h := hn _ intPt PUnit.unit PUnit.unit PUnit.unit mem_ptsIn_top mem_ptsIn_top mem_ptsIn_top
  erw [loc_eq] at h
  rw [div_one] at h
  erw [hm] at h
  rw [ratVal_int] at h
  change _ - (0 + 2 * t) / 2 = -(a * (0 + 2 * (0 : ℝ)) + b * (0 + 2 * Real.log 3)) / 2 at h
  have h0 : Real.log ‖(m : ℂ)‖ = 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with rfl | rfl <;> simp
  rw [h0] at h
  linarith


end IntValues



end GlobalTheory.VolBr.Model
