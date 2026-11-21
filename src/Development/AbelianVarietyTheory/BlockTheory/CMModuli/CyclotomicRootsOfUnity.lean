import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def IsIntegersOf (V C : Type) [CommRing V] [NormedField C] [Algebra V C] : Prop :=
  Function.Injective (algebraMap V C) ∧ ∀ x : C, (∃ a : V, algebraMap V C a = x) ↔ ‖x‖ ≤ 1

example (p : ℕ) [Fact p.Prime] : IsIntegersOf ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val_injective, fun x => ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩⟩

def primeToPart (p n : ℕ) : ℕ := n / p ^ n.factorization p

example : primeToPart 3 45 = 5 := by
  have h : (45 : ℕ).factorization 3 = 2 := by
    rw [show (45 : ℕ) = 3 ^ 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow (by norm_num), Nat.Prime.factorization (by norm_num)]
    simp
  rw [primeToPart, h]
  norm_num

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def AbelianLocusLevels (p : ℕ) (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧
    (∀ a : D.La, primeToPart p l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → Y.Extends U (Y.oF.eta a)) ∧
    (∀ a : D.La, (∃ b : D.La, primeToPart p l.A • a = l.A • b) → Y.Extends U (Y.oF.etaA a))

def HasGoodReduction (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K]
    (y : Sp K ⟶ Xo.XF c) : Prop :=
  ∃ (B : Over (Sp V)) (_ : GrpObj B) (L : LB B.left),
    IsAbelianScheme B ∧ L.IsLB ∧ ReciprocityTheory.ChartRestriction.G.Out.RelAmple B L ∧
    ∃ (Ay : Over (Sp K)) (_ : GrpObj Ay) (φ : Ay.left ⟶ Y.oF.t.G.left) (ψ : Ay.left ⟶ B.left),
      IsGrpPullback Ay Y.oF.t.G y φ ∧ IsGrpPullback Ay B (spMap (algebraMap V K)) ψ ∧
      LBIso (Y.oF.t.PP.L.pull φ) (L.pull ψ)

def GoodPointsExtend (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (γ : O →+* V) (y : Sp K ⟶ Xo.XF c),
    y ≫ pullback.snd _ _ ≫ spMap β = spMap (algebraMap V K) ≫ spMap γ →
    HasGoodReduction Y V K y →
    ∃ yt : Sp V ⟶ Y.X, yt ≫ Y.s = spMap γ ∧ spMap (algebraMap V K) ≫ yt = y ≫ Y.j ∧
      Set.range yt ⊆ abLocus Y.t.G

structure OneModel (p : ℕ) (Y : Model Xo c β) : Prop where

  acts : Y.LevelActs

  descends : l.A = 1 → Y.Descends

  push : PushInvertible Y.t.G Y.t.PP.L

  abLevels : AbelianLocusLevels p Y

  extDVR : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K],
    GoodPointsExtend Y V K

  extInt : ∀ (V C : Type) [CommRing V] [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra V C], ‖(p : C)‖ < 1 → IsIntegersOf V C → GoodPointsExtend Y V C

end GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels
end
end

section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels

def LiesOver (W : ValuationSubring ℂ) (p : ℕ) : Prop := (p : ℂ) ∈ W.nonunits

example (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, LiesOver W p := by
  have hI : Ideal.span {((p : ℕ) : (⊥ : Subring ℂ))} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    obtain ⟨⟨x, hx⟩, h1⟩ := h.exists_right_inv
    obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hx
    have h2 : ((p : ℤ) : ℂ) * (m : ℂ) = 1 := by simpa using congrArg Subtype.val h1
    have h3 : (p : ℤ) * m = 1 := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ 1 := ⟨m, h3.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast h4))
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨W, hW ⟨_, Ideal.subset_span rfl, by simp⟩⟩

abbrev locRing (W : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) : ValuationSubring F :=
  W.comap F.val.toRingHom

abbrev locIncl (W : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) : locRing W F →+* F :=
  (locRing W F).subtype

theorem inv_natCast_mem {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime) (hW : LiesOver W p) {d : ℕ}
    (hd : ¬ p ∣ d) : (d : ℂ)⁻¹ ∈ W := by
  by_contra h
  have hdn : (d : ℂ) ∈ W.nonunits := (W.mem_nonunits_iff_or).mpr (Or.inr h)
  have hc : IsCoprime (p : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : ℂ) * p + (b : ℂ) * d = 1 := by exact_mod_cast hab
  have hv : ∀ (m : ℤ) (x : ℂ), W.valuation x < 1 → W.valuation ((m : ℂ) * x) < 1 := fun m x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((W.valuation_le_one_iff _).mpr (intCast_mem W m))) hx
  have := Valuation.map_add_lt W.valuation (hv a _ (W.mem_nonunits_iff.mp hW)) (hv b _ (W.mem_nonunits_iff.mp hdn))
  rw [h1, map_one] at this
  exact lt_irrefl _ this

theorem zeta_mem_valuationSubring (W : ValuationSubring ℂ) {M : ℕ} (hM : M ≠ 0) : zeta M ∈ W := by
  have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
  rw [← W.valuation_le_one_iff]
  have h2 : W.valuation (zeta M) ^ M = 1 := by rw [← map_pow, h1, map_one]
  exact ((pow_eq_one_iff_of_nonneg zero_le' hM).mp h2).le

theorem cycloLocal_le {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime) (hW : LiesOver W p) {M : ℕ} (hM : M ≠ 0)
    {F : IntermediateField ℚ ℂ} (hF : zeta M ∈ F) : cycloLocal p M ≤ W.toSubring ⊓ F.toSubfield.toSubring := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨q, hq, rfl⟩ | hx)
  · refine ⟨?_, SubfieldClass.ratCast_mem F q⟩
    change (q : ℂ) ∈ W
    rw [Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem W _) (inv_natCast_mem hp hW hq)
  · obtain rfl : x = zeta M := hx
    exact ⟨zeta_mem_valuationSubring W hM, hF⟩

theorem zeta_mem_of_dvd {F : IntermediateField ℚ ℂ} {a N : ℕ} (hN : N ≠ 0) (h : a ∣ N) (hF : zeta N ∈ F) :
    zeta a ∈ F := by
  obtain ⟨k, rfl⟩ := h
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hN)
  have : zeta a = zeta (a * k) ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [this]
  exact pow_mem hF k

theorem zeta_lcm_mem {F : IntermediateField ℚ ℂ} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h₁ : zeta a ∈ F)
    (h₂ : zeta b ∈ F) : zeta (Nat.lcm a b) ∈ F := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hl : ((Nat.lcm a b : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero ha hb)
  have e1 : ((Nat.gcd a b : ℕ) : ℂ) * (Nat.lcm a b : ℕ) = a * b := by exact_mod_cast Nat.gcd_mul_lcm a b
  have e2 : ((Nat.gcd a b : ℕ) : ℂ) = a * (Nat.gcdA a b : ℂ) + b * (Nat.gcdB a b : ℂ) := by
    exact_mod_cast Nat.gcd_eq_gcd_ab a b
  have : zeta (Nat.lcm a b) = zeta a ^ Nat.gcdB a b * zeta b ^ Nat.gcdA a b := by
    rw [zeta, zeta, zeta, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    field_simp
    linear_combination (-1 : ℂ) * e1 + (Nat.lcm a b : ℂ) * e2
  rw [this]
  exact mul_mem (zpow_mem h₁ _) (zpow_mem h₂ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Idx (H : Host E) (p : ℕ) : Type := Σ l : {l : Level H // l.GoodAt p}, Coeff l.1

abbrev Idx.l {p : ℕ} (i : Idx H p) : Level H := i.1.1

abbrev Idx.F {p : ℕ} (i : Idx H p) : IntermediateField ℚ ℂ := i.2.F

def Idx.Le {p : ℕ} (i j : Idx H p) : Prop := i.l.Dvd j.l ∧ i.F ≤ j.F

theorem Idx.Le.refl {p : ℕ} (i : Idx H p) : i.Le i := ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl⟩

theorem Idx.Le.trans {p : ℕ} {i j k : Idx H p} (h : i.Le j) (h' : j.Le k) : i.Le k :=
  ⟨⟨h.1.1.trans h'.1.1, h'.1.2.1.trans h.1.2.1, h.1.2.2.trans h'.1.2.2⟩, h.2.trans h'.2⟩

def addLevel (l : Level H) {N : ℕ} (hN : N ≠ 0) : Level H :=
  { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos (Nat.pos_of_ne_zero hN) }

theorem zeta_mem_sup (F : IntermediateField ℚ ℂ) (N : ℕ) :
    zeta N ∈ F ⊔ IntermediateField.adjoin ℚ {zeta N} :=
  (le_sup_right : _ ≤ F ⊔ _) (IntermediateField.subset_adjoin _ _ rfl)

def addCoeff {l : Level H} (c : Coeff l) {N : ℕ} (hN : N ≠ 0) : Coeff (addLevel l hN) :=
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hz : zeta (addLevel l hN).M' ∈ c.F ⊔ IntermediateField.adjoin ℚ {zeta N} := by
    have : (addLevel l hN).M' = Nat.lcm l.M' N := (Nat.lcm_assoc _ _ _).symm
    rw [this]
    exact zeta_lcm_mem hM' hN ((le_sup_left : c.F ≤ _) c.zeta_mem) (zeta_mem_sup _ _)
  { F := c.F ⊔ IntermediateField.adjoin ℚ {zeta N}
    fin := by
      have := c.fin
      have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta N}) :=
        IntermediateField.adjoin.finiteDimensional
          (((Complex.isPrimitiveRoot_exp N hN).isIntegral (Nat.pos_of_ne_zero hN)).tower_top)
      infer_instance
    conj := fun τ a => (le_sup_left : c.F ≤ _) (c.conj τ a)
    zeta_mem := hz
    le := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x (rfl | hx)
      · exact (le_sup_left : c.F ≤ _) (c.le (IntermediateField.subset_adjoin _ _ (by simp)))
      · obtain rfl : x = _ := hx
        exact zeta_mem_of_dvd
          (Nat.lcm_ne_zero (by have := l.three_le; change l.M ≠ 0; omega) (addLevel l hN).A_pos.ne')
          (Nat.dvd_lcm_right _ _) hz }

def Idx.add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : Idx H p :=
  ⟨⟨addLevel i.l hN, i.1.2⟩, addCoeff i.2 hN⟩

theorem Idx.le_add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : i.Le (i.add hN) :=
  ⟨⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩, le_sup_left⟩

def abOpen {S : Scheme.{0}} (G : Over S) : S.Opens := ⟨interior (abLocus G), isOpen_interior⟩

def IsBirational {X Z : Scheme.{0}} (h : X ⟶ Z) : Prop :=
  ∃ V : Z.Opens, Dense (V : Set Z) ∧ Dense ((h ⁻¹ᵁ V : X.Opens) : Set X) ∧ IsIso (h ∣_ V)

example (X : Scheme.{0}) : IsBirational (𝟙 X) :=
  ⟨⊤, dense_univ, dense_univ, inferInstance⟩

def genus (D : Datum H) : ℕ := Module.finrank ℚ E / 2 * (D.p + D.q)

section Compare

variable {D : Datum H} {l l₁ : Level H} {Xo : Moduli D l} {Xo₁ : Moduli D l₁} {c : Coeff l} {c₁ : Coeff l₁}
  {O O₁ : Type} [CommRing O] [CommRing O₁] {β : O →+* c.F} {β₁ : O₁ →+* c₁.F}

end Compare

abbrev Models {D : Datum H} (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (W : ValuationSubring ℂ) : Type 1 :=
  ∀ i : Idx H p, Model (Xo i.l) i.2 (locIncl W i.F)

end GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity
end
end
