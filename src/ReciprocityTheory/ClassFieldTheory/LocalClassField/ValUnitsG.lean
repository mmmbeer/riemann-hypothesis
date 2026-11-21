import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem fK_dvd (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : fK p K ∣ fK p L := by
  have hK := finDim_of_le p hL h
  obtain ⟨f, -, hf, -⟩ := qK_le_pow_finrank p K hK hL h
  rw [qK_eq_pow_fK p L hL, qK_eq_pow_fK p K hK, ← pow_mul] at hf
  exact ⟨f, Nat.pow_right_injective (Fact.out : p.Prime).two_le hf⟩

theorem fK_eq_mul (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : fK p L = fLK p K L * fK p K :=
  (Nat.div_mul_cancel (fK_dvd p hL h)).symm

theorem qK_eq_pow_fLK (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : qK p L = qK p K ^ fLK p K L := by
  rw [qK_eq_pow_fK p L hL, qK_eq_pow_fK p K (finDim_of_le p hL h), ← pow_mul, fK_eq_mul p hL h, mul_comm]

theorem eLK_mul_fLK_eq_degLK (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    eLK p K L * fLK p K L = degLK p K L := by
  have hK := finDim_of_le p hL h
  have h1 := finrank_eq_degLK_mul h hL
  rw [← eK_mul_fK p L hL, ← eK_mul_fK p K hK, eK_eq_mul p hL h, fK_eq_mul p hL h] at h1
  have h2 : (eLK p K L * fLK p K L) * (eK p K * fK p K) = degLK p K L * (eK p K * fK p K) := by
    rw [← h1]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (eK_pos p K hK) (fK_pos p K hK)) h2

theorem eK_Kur (hK : FiniteDimensional ℚ_[p] K) : eK p (MaximalUnramifiedExtension p K) = eK p K :=
  eK_eq_of_norm p le_Kur fun x hx => by
    obtain ⟨n, hn, hxn⟩ := (mem_Kur_iff hK x).1 hx
    exact norm_Kn p K hK hn hxn

def toLayer [(subG p K L).Normal] (x : multOf p L) : (layer p K L).V :=
  ⟨x.1, fun σ => Units.ext (σ.2 _ x.2)⟩

theorem toLayer_val [(subG p K L).Normal] (x : multOf p L) : (toLayer p x : (layer p K L).V).1 = x.1 := rfl

theorem vLayerMap_spec (h : K ≤ L) [(subG p K L).Normal] (x : (layer p K L).V) :
    (vLayerMap p K L x : ℝ) = eK p L * vbar p x.1 := by
  have hex : ∃ f : (layer p K L).V →+ ℤ, ∀ x, (f x : ℝ) = eK p L * vbar p x.1 :=
    ⟨(vOn p L).comp
      { toFun := fun x => ⟨x.1, layer_val_mem h x⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }, fun x => vOn_spec p L _⟩
  unfold vLayerMap
  rw [dif_pos hex]
  exact hex.choose_spec x

theorem vLayerMap_toLayer (h : K ≤ L) [(subG p K L).Normal] (x : multOf p L) :
    vLayerMap p K L (toLayer p x) = vOn p L x := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p h, vOn_spec, toLayer_val]

theorem vLayerMap_surjective (he : 0 < eK p L) (h : K ≤ L) [(subG p K L).Normal] :
    Function.Surjective (vLayerMap p K L) := fun n => by
  obtain ⟨x, hx⟩ := vOn_surjective_of_pos p L he n
  exact ⟨toLayer p x, by rw [vLayerMap_toLayer p h, hx]⟩

theorem layerUIncl_injective [(subG p K L).Normal] : Function.Injective (layerUIncl p K L).u := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (layer p K L).V => z.1) hxy

theorem vLayerMap_eq_zero_iff (he : 0 < eK p L) (h : K ≤ L) [(subG p K L).Normal]
    (x : (layer p K L).V) : vLayerMap p K L x = 0 ↔ x ∈ LinearMap.range (layerUIncl p K L).u := by
  have he' : (eK p L : ℝ) ≠ 0 := by positivity
  rw [← Int.cast_inj (α := ℝ), vLayerMap_spec p h, Int.cast_zero, mul_eq_zero, or_iff_right he']
  constructor
  · intro hx
    exact ⟨⟨⟨x.1, hx⟩, fun g => Subtype.ext (x.2 g)⟩, Subtype.ext rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.1.2

theorem vLayer_surjective (he : 0 < eK p L) (h : K ≤ L) [(subG p K L).Normal] :
    Function.Surjective (vLayer p K L).u := vLayerMap_surjective p he h

theorem ker_vLayer (he : 0 < eK p L) (h : K ≤ L) [(subG p K L).Normal] :
    LinearMap.ker (vLayer p K L).u = LinearMap.range (layerUIncl p K L).u := by
  ext x
  rw [LinearMap.mem_ker]
  exact vLayerMap_eq_zero_iff p he h x

theorem vLayerMap_of_mem (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal]
    (x : (layer p K L).V) (hx : x.1 ∈ multOf p K) :
    vLayerMap p K L x = eLK p K L * vOn p K ⟨x.1, hx⟩ := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p h, Int.cast_mul, vOn_spec, eK_eq_mul p hL h]
  push_cast
  ring

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem rpow_neg_div_nonneg (i : ℕ) : 0 ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

theorem rpow_neg_div_lt_one (he : 0 < eK p K) {i : ℕ} (hi : 0 < i) : (p : ℝ) ^ (- (i : ℝ) / eK p K) < 1 := by
  have he' : (0 : ℝ) < eK p K := by positivity
  have hi' : (0 : ℝ) < i := by positivity
  exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_p_real p) (div_neg_of_neg_of_pos (by linarith) he')

def UKi (i : ℕ) : Subgroup Kˣ where
  carrier := {x | x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K)}
  one_mem' := ⟨(UK p K).one_mem, by
    show ‖(((1 : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    simp only [Units.val_one, OneMemClass.coe_one, sub_self, norm_zero]
    exact rpow_neg_div_nonneg p K i⟩
  mul_mem' := fun {x y} hx hy => ⟨(UK p K).mul_mem hx.1 hy.1, by
    have hx1 : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx.1
    have h : (((x * y : Kˣ) : K) : PadicAlgCl p) - 1 =
        ((x : K) : PadicAlgCl p) * (((y : K) : PadicAlgCl p) - 1) + (((x : K) : PadicAlgCl p) - 1) := by
      rw [Units.val_mul, MulMemClass.coe_mul]; ring
    show ‖(((x * y : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    rw [h]
    refine (PadicAlgCl.isNonarchimedean p _ _).trans (max_le ?_ hx.2)
    rw [norm_mul, hx1, one_mul]; exact hy.2⟩
  inv_mem' := fun {x} hx => ⟨(UK p K).inv_mem hx.1, by
    have hx1 : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx.1
    have hx0 := coe_units_ne_zero x
    have h : (((x⁻¹ : Kˣ) : K) : PadicAlgCl p) - 1 =
        - ((((x : K) : PadicAlgCl p) - 1) * ((x : K) : PadicAlgCl p)⁻¹) := by
      rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      field_simp
      ring
    show ‖(((x⁻¹ : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    rw [h, norm_neg, norm_mul, norm_inv, hx1, inv_one, mul_one]; exact hx.2⟩

theorem mem_UKi_iff (i : ℕ) (x : Kˣ) :
    x ∈ UKi p K i ↔ x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) := Iff.rfl

theorem norm_pow_uniformiser (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) :
    ‖((π : K) : PadicAlgCl p)‖ ^ i = (p : ℝ) ^ (- (i : ℝ) / eK p K) := by
  have h := norm_eq_rpow_vK p K hK (π ^ i)
  rw [vK_pow, hπ, mul_one, Int.cast_natCast, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, norm_pow] at h
  exact h

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def redK : OK p K →+* resK p K :=
  (resMap p K).codRestrict (resK p K) fun x => (mem_resK_iff p K _).2 ⟨toObar p K x, (x : K).2, rfl⟩

theorem redK_eq_iff (a b : OK p K) :
    redK p K a = redK p K b ↔ ‖((a : K) : PadicAlgCl p) - ((b : K) : PadicAlgCl p)‖ < 1 := by
  rw [Subtype.ext_iff]
  show IsLocalRing.residue (Obar p) (toObar p K a) = IsLocalRing.residue (Obar p) (toObar p K b) ↔ _
  rw [residue_eq_iff]
  rfl

theorem redK_surjective : Function.Surjective (redK p K) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff p K c).1 hc
  exact ⟨⟨⟨x, hx⟩, x.2⟩, Subtype.ext rfl⟩

def UKtoOK : UK p K →* OK p K where
  toFun x := ⟨((x : Kˣ) : K), (mem_OK_iff p K _).2 (le_of_eq x.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {K}

def gradFun (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) (x : UKi p K i) : OK p K :=
  ⟨(((x : Kˣ) : K) - 1) / (π : K) ^ i, by
    rw [mem_OK_iff]
    show ‖((((x : Kˣ) : K) : PadicAlgCl p) - 1) / ((π : K) : PadicAlgCl p) ^ i‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one (pow_pos (norm_units_pos π) i), norm_pow_uniformiser p K hK hπ i]
    exact x.2.2⟩

theorem gradFun_val (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) (x : UKi p K i) :
    ((gradFun p hK hπ i x : K) : PadicAlgCl p) =
      ((((x : Kˣ) : K) : PadicAlgCl p) - 1) / ((π : K) : PadicAlgCl p) ^ i := rfl

variable (K)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
