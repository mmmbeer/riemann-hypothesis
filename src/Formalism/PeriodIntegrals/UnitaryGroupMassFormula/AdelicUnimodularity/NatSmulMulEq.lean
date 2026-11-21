import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Lemmata.GeneralBFactThirdMore.Key
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.KCountable

section
noncomputable section

namespace PI.WAU

open scoped TensorProduct

variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

def coord : E ⊗[F] B →ₗ[F] (ι → B) :=
  TensorProduct.lift (LinearMap.mk₂ F (fun (e : E) (a : B) => fun k => b.repr e k • a)
    (fun e₁ e₂ a => by funext k; simp [add_smul])
    (fun c e a => by funext k; simp [smul_smul])
    (fun e a₁ a₂ => by funext k; simp [smul_add])
    (fun c e a => by funext k; simp [smul_comm c]))

theorem coord_tmul (e : E) (a : B) : coord b (e ⊗ₜ[F] a) = fun k => b.repr e k • a := by
  simp [coord]

def emb (c : ι → B) : E ⊗[F] B := ∑ i, b i ⊗ₜ[F] c i

theorem coord_emb (c : ι → B) : coord b (emb b c) = c := by
  funext k
  simp only [emb, map_sum, coord_tmul, Finset.sum_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

theorem emb_coord (x : E ⊗[F] B) : emb b (coord b x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [emb]
  | tmul e a =>
    simp only [emb, coord_tmul]
    conv_rhs => rw [← b.sum_repr e]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    have : emb b (coord b (x + y)) = emb b (coord b x) + emb b (coord b y) := by
      simp [emb, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [this, hx, hy]

theorem coord_injective : Function.Injective (coord b : E ⊗[F] B → ι → B) :=
  Function.LeftInverse.injective (emb_coord b)

theorem coord_mul (x y : E ⊗[F] B) :
    coord b (x * y) = fun k => ∑ i, ∑ j, b.repr (b i * b j) k • (coord b x i * coord b y j) := by
  conv_lhs => rw [← emb_coord b x, ← emb_coord b y]
  simp only [emb, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum, coord_tmul]
  funext k
  simp [Finset.sum_apply]

theorem coord_smul (c : F) (x : E ⊗[F] B) : coord b (c • x) = c • coord b x := map_smul _ _ _

theorem coord_incl (e : E) :
    coord b (Algebra.TensorProduct.includeLeftRingHom (R := F) (B := B) e) = fun k => algebraMap F B (b.repr e k) := by
  funext k
  simp [Algebra.TensorProduct.includeLeftRingHom_apply, coord_tmul, Algebra.algebraMap_eq_smul_one]

theorem coord_map (σ : E →ₐ[F] E) (x : E ⊗[F] B) :
    coord b (Algebra.TensorProduct.map σ (AlgHom.id F B) x) =
      fun k => ∑ i, b.repr (σ (b i)) k • coord b x i := by
  conv_lhs => rw [← emb_coord b x]
  simp only [emb, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, coord_tmul]
  funext k
  simp [Finset.sum_apply]

section Topology

variable [TopologicalSpace B] [IsTopologicalRing B]

theorem cont_smul {X : Type*} [TopologicalSpace X] (c : F) {h : X → B} (hh : Continuous h) :
    Continuous (fun x => c • h x) := by
  simp_rw [Algebra.smul_def]
  exact continuous_const.mul hh

def CtsA {X : Type*} [TopologicalSpace X] (f : X → E ⊗[F] B) : Prop :=
  Continuous (fun x => coord b (f x))

variable {b}
variable {X : Type*} [TopologicalSpace X]

theorem ctsA_const (y : E ⊗[F] B) : CtsA b (fun _ : X => y) := continuous_const

theorem ctsA_emb {g : X → ι → B} (hg : Continuous g) : CtsA b (fun x => emb b (g x)) := by
  simpa [CtsA, coord_emb] using hg

theorem ctsA_sum {κ : Type*} (s : Finset κ) {f : κ → X → E ⊗[F] B} (hf : ∀ i ∈ s, CtsA b (f i)) :
    CtsA b (fun x => ∑ i ∈ s, f i x) := by
  unfold CtsA
  simp only [map_sum]
  exact continuous_finset_sum _ hf

theorem ctsA_mul {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : CtsA b (fun x => f x * g x) := by
  unfold CtsA
  simp only [coord_mul]
  refine continuous_pi fun k => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact cont_smul _ (((continuous_apply i).comp hf).mul ((continuous_apply j).comp hg))

theorem ctsA_map (σ : E →ₐ[F] E) {f : X → E ⊗[F] B} (hf : CtsA b f) :
    CtsA b (fun x => Algebra.TensorProduct.map σ (AlgHom.id F B) (f x)) := by
  unfold CtsA
  simp only [coord_map]
  exact continuous_pi fun k => continuous_finset_sum _ fun i _ => cont_smul _ ((continuous_apply i).comp hf)

end Topology

end PI.WAU
end
end

section
noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct

theorem exists_den {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, (m : K) * x = algebraMap (𝓞 K) K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hN0 : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hs0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
  refine ⟨Ideal.absNorm (Ideal.span {s}), Nat.pos_of_ne_zero hN0, t * a, ?_⟩
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  have : ((Ideal.absNorm (Ideal.span {s}) : ℕ) : K) = algebraMap (𝓞 K) K t * algebraMap (𝓞 K) K s := by
    rw [← map_mul, ht, map_natCast]
  rw [this, map_mul]
  field_simp

variable {F : Type} [Field F] [NumberField F]

def IntF (f : F) : Prop := algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ Ohat F

theorem ohat_mul {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a * c ∈ Ohat F := by
  intro v
  exact mul_mem (ha v) (hc v)

theorem ohat_add {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a + c ∈ Ohat F := by
  intro v
  exact add_mem (ha v) (hc v)

theorem ohat_neg {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) : -a ∈ Ohat F := by
  intro v
  exact neg_mem (ha v)

theorem ohat_zero : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F := by
  intro v
  exact (v.adicCompletionIntegers F).zero_mem

theorem ohat_one : (1 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F := by
  intro v
  exact (v.adicCompletionIntegers F).one_mem

theorem ohat_sum {κ : Type*} (s : Finset κ) {f : κ → FiniteAdeleRing (𝓞 F) F} (hf : ∀ i ∈ s, f i ∈ Ohat F) :
    ∑ i ∈ s, f i ∈ Ohat F := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ohat_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact ohat_add (hf j (Finset.mem_insert_self j s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem ohat_nsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℕ) : m • a ∈ Ohat F := by
  induction m with
  | zero => rw [zero_nsmul]; exact ohat_zero
  | succ n ih => rw [succ_nsmul]; exact ohat_add ih ha

theorem ohat_zsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℤ) : m • a ∈ Ohat F := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [natCast_zsmul]; exact ohat_nsmul ha n
  · rw [neg_zsmul, natCast_zsmul]; exact ohat_neg (ohat_nsmul ha n)

theorem intF_of_int (a : 𝓞 F) : IntF (algebraMap (𝓞 F) F a) := by
  unfold IntF Ohat
  intro v
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a

theorem exists_den_fin {κ : Type} [Fintype κ] (f : κ → F) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IntF ((m : F) * f i) := by
  classical
  choose m hm a ha using fun i => exists_den (f i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have key : ((∏ j, m j : ℕ) : F) * f i = algebraMap (𝓞 F) F ((c : 𝓞 F) * a i) := by
    rw [hc, Nat.cast_mul, map_mul, ← ha i, map_natCast]; ring
  rw [key]
  exact intF_of_int _

section Coord

variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

local notation "Af" => FiniteAdeleRing (𝓞 F) F

def IntC (x : E ⊗[F] Af) : Prop := ∀ k, coord b x k ∈ Ohat F

variable {b}

theorem intC_add {x y : E ⊗[F] Af} (hx : IntC b x) (hy : IntC b y) : IntC b (x + y) := by
  intro k
  rw [map_add]
  exact ohat_add (hx k) (hy k)


theorem intC_sum {κ : Type*} (s : Finset κ) {f : κ → E ⊗[F] Af} (hf : ∀ i ∈ s, IntC b (f i)) :
    IntC b (∑ i ∈ s, f i) := by
  intro k
  rw [map_sum, Finset.sum_apply]
  exact ohat_sum s fun i hi => hf i hi k

theorem smul_eq_algebraMap_mul (c : F) (a : Af) : c • a = algebraMap F Af c * a :=
  Algebra.smul_def c a

theorem exists_den_mul (b : Module.Basis ι F E) :
    ∃ m : ℕ, 0 < m ∧ ∀ x y : E ⊗[F] Af, IntC b x → IntC b y → IntC b (m • (x * y)) := by
  obtain ⟨m, hm, h⟩ := exists_den_fin (fun p : ι × ι × ι => b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨m, hm, fun x y hx hy k => ?_⟩
  rw [map_nsmul, coord_mul]
  simp only [Pi.smul_apply, Finset.smul_sum]
  refine ohat_sum _ fun i _ => ohat_sum _ fun j _ => ?_
  rw [smul_eq_algebraMap_mul, nsmul_eq_mul, ← mul_assoc]
  have h1 : (m : Af) * algebraMap F Af (b.repr (b i * b j) k) = algebraMap F Af ((m : F) * b.repr (b i * b j) k) := by
    simp
  rw [h1]
  exact ohat_mul (h (i, j, k)) (ohat_mul (hx i) (hy j))


end Coord

end PI.WAU
end
end

section
noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

abbrev inclV (w : Fin n → E) : Fin n → E ⊗[F] Af := fun i => Formalism.UG.inclE (F := F) Af (w i)

theorem inclV_mem {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E} (hw : w ∈ L) :
    inclV (F := F) w ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

theorem one_tmul_mem_intAf {c : Af} (hc : c ∈ Ohat F) : ((1 : E) ⊗ₜ[F] c) ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

theorem exists_nat_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • w ∈ L := by
  first | exact Bl.general_b_fact_third'.goal1 .. | (apply Bl.general_b_fact_third'.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third'.goal1 <;> assumption)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_lower (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Fin n → E ⊗[F] Af, (∀ j, IntC b (y j)) → d • y ∈ lamAf (F := F) L := by
  classical
  choose m hm hmL using fun p : Fin n × ι => exists_nat_smul_mem L hL (Pi.single p.1 (b p.2))
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun y hy => ?_⟩
  have key : ∀ (j : Fin n) (k : ι) (c : Af), c ∈ Ohat F →
      (∏ p, m p) • Pi.single j (b k ⊗ₜ[F] c) ∈ lamAf (F := F) L := by
    intro j k c hc
    obtain ⟨q, hq⟩ : m (j, k) ∣ ∏ p, m p := Finset.dvd_prod_of_mem m (Finset.mem_univ (j, k))
    have hw : (∏ p, m p) • (Pi.single j (b k) : Fin n → E) ∈ L := by
      rw [hq, mul_comm, mul_smul]; exact nsmul_mem (hmL (j, k)) q
    have heq : (∏ p, m p) • (Pi.single j (b k ⊗ₜ[F] c) : Fin n → E ⊗[F] Af) =
        (⟨(1 : E) ⊗ₜ[F] c, one_tmul_mem_intAf hc⟩ : IntAf F E) •
          inclV (F := F) ((∏ p, m p) • (Pi.single j (b k) : Fin n → E)) := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one]
        rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.smul_tmul']
        simp only [inclV, Pi.smul_apply, Pi.single_eq_same, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      · simp [Pi.single_eq_of_ne hij, Subring.smul_def, Formalism.UG.inclE, inclV]
    rw [heq]
    exact Submodule.smul_mem _ _ (inclV_mem hw)
  have hy' : y = ∑ j, ∑ k, (Pi.single j (b k ⊗ₜ[F] coord b (y j) k) : Fin n → E ⊗[F] Af) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := emb_coord b (y j)
    simp only [emb] at h1
    conv_lhs => rw [← h1]
    exact map_sum (AddMonoidHom.single (fun _ : Fin n => E ⊗[F] Af) j) _ _
  rw [hy', Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Finset.smul_sum]
  exact Submodule.sum_mem _ fun k _ => key j k _ (hy j k)

end PI.WAU
end
end

section
noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

def ohatL (L : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → E ⊗[F] Af) :=
  AddSubgroup.closure {y | ∃ c ∈ Ohat F, ∃ l ∈ L, y = ((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) Af (l i)}

theorem smul_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {a : E ⊗[F] Af} (ha : a ∈ IntAf F E) :
    ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L := by
  let T : Subring (E ⊗[F] Af) :=
    { carrier := {a | ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L}
      mul_mem' := fun {a c} ha hc y hy => by rw [mul_smul]; exact ha _ (hc y hy)
      one_mem' := fun y hy => by rw [one_smul]; exact hy
      add_mem' := fun {a c} ha hc y hy => by rw [add_smul]; exact add_mem (ha y hy) (hc y hy)
      zero_mem' := fun y _ => by rw [zero_smul]; exact zero_mem _
      neg_mem' := fun {a} ha y hy => by rw [neg_smul]; exact neg_mem (ha y hy) }
  have hle : IntAf F E ≤ T := by
    apply Subring.closure_le.mpr
    rintro a (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨c', hc'⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := hx
      refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c, hc, o • l, L.smul_mem o hl, ?_⟩
        funext i
        show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Af)) * (((1 : E) ⊗ₜ[F] c) * ((l i) ⊗ₜ[F] (1 : Af))) =
          ((1 : E) ⊗ₜ[F] c) * (((o • l) i) ⊗ₜ[F] (1 : Af))
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Pi.smul_apply, Algebra.smul_def]
        simp only [one_mul, mul_one]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
    · refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c' * c, ohat_mul hc' hc, l, hl, ?_⟩
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
  exact hle ha

theorem lamAf_le_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {y : Fin n → E ⊗[F] Af}
    (hy : y ∈ lamAf (F := F) L) : y ∈ ohatL (F := F) L := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨1, ohat_one, (l : Fin n → E), l.2, ?_⟩
    rw [← Algebra.TensorProduct.one_def, one_smul]
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul a x _ hx => exact smul_ohatL L a.2 x hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem intC_zero {b : Module.Basis ι F E} : IntC b (0 : E ⊗[F] Af) := by
  intro k
  simp only [map_zero, Pi.zero_apply]
  exact ohat_zero

theorem intC_neg {b : Module.Basis ι F E} {x : E ⊗[F] Af} (hx : IntC b x) : IntC b (-x) := by
  intro k
  simp only [map_neg, Pi.neg_apply]
  exact ohat_neg (hx k)

theorem exists_upper (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ y ∈ lamAf (F := F) L, ∀ j, IntC b (D • y j) := by
  obtain ⟨T, hT⟩ := (hfg.restrictScalars (R := ℤ))
  obtain ⟨D, hD, hDint⟩ := exists_den_fin (fun x : T × Fin n × ι =>
    b.repr ((x.1 : Fin n → E) x.2.1) x.2.2)
  have hQ : ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
    intro l hl
    have hl' : l ∈ Submodule.span ℤ (T : Set (Fin n → E)) := by rw [hT]; exact hl
    clear hl
    induction hl' using Submodule.span_induction with
    | mem x hx => intro j k; exact hDint ⟨⟨x, hx⟩, j, k⟩
    | zero =>
      intro j k
      unfold IntF
      simp only [Pi.zero_apply, map_zero, Finsupp.coe_zero, mul_zero]
      exact ohat_zero
    | add x z _ _ hx hz =>
      intro j k
      have h1 := hx j k
      have h2 := hz j k
      unfold IntF at h1 h2 ⊢
      rw [Pi.add_apply, map_add, Finsupp.add_apply, mul_add, map_add]
      exact ohat_add h1 h2
    | smul a x _ hx =>
      intro j k
      have h1 := hx j k
      unfold IntF at h1 ⊢
      rw [Pi.smul_apply, map_zsmul, Finsupp.smul_apply, mul_smul_comm, map_zsmul]
      exact ohat_zsmul h1 a
  refine ⟨D, hD, fun y hy j => ?_⟩
  have hy' := lamAf_le_ohatL L hy
  clear hy
  unfold ohatL at hy'
  induction hy' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, l, hl, rfl⟩ := hz
    intro k
    rw [map_nsmul, Pi.smul_apply]
    have ew : ((((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) Af (l i)) j) =
        (l j) ⊗ₜ[F] c := by
      simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    rw [ew]
    simp only [coord, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul, Algebra.smul_def]
    exact ohat_mul (hQ l hl j k) hc
  | zero => rw [Pi.zero_apply, smul_zero]; exact intC_zero
  | add u w _ _ hu hw => rw [Pi.add_apply, smul_add]; exact intC_add hu hw
  | neg u _ hu => rw [Pi.neg_apply, smul_neg]; exact intC_neg hu

end PI.WAU
end
end

section
noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {B : Type} [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

theorem emb_add (c c' : ι → B) : emb b (c + c') = emb b c + emb b c' := by
  apply coord_injective b; rw [map_add, coord_emb, coord_emb, coord_emb]

theorem emb_zero : emb b (0 : ι → B) = 0 := by
  apply coord_injective b; rw [map_zero, coord_emb]

theorem emb_neg (c : ι → B) : emb b (-c) = -emb b c := by
  apply coord_injective b; rw [map_neg, coord_emb, coord_emb]

theorem emb_sub (c c' : ι → B) : emb b (c - c') = emb b c - emb b c' := by
  apply coord_injective b; rw [map_sub, coord_emb, coord_emb, coord_emb]

theorem emb_nsmul (N : ℕ) (c : ι → B) : emb b (N • c) = N • emb b c := by
  apply coord_injective b; rw [map_nsmul, coord_emb, coord_emb]

theorem isClosed_eqA [TopologicalSpace B] [IsTopologicalRing B] [T2Space B] {X : Type*} [TopologicalSpace X]
    {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : IsClosed {p | f p = g p} := by
  have : {p | f p = g p} = {p | coord b (f p) = coord b (g p)} := by
    ext p; exact (coord_injective b).eq_iff.symm
  rw [this]; exact isClosed_eq hf hg

end General

namespace Cpt

variable (I : AutInst)

abbrev ιb : Type := Fin (Module.finrank I.F I.E)

abbrev bs : Module.Basis (ιb I) I.F I.E := Module.finBasis I.F I.E

abbrev Co : Type := Fin I.n → Fin I.n → ιb I → Af I.F

def matOf (P : Co I) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun i j => emb (bs I) (P i j)

theorem mulVec_mem_Lf (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ l ∈ I.L, M *ᵥ inclV (F := I.F) l ∈ I.Lf) : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨l, hl⟩, rfl⟩ := hx; exact hM l hl
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hx

theorem isClosed_LfC (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf) :
    IsClosed {w : Fin I.n → ιb I → Af I.F | (fun j => emb (bs I) (w j)) ∈ I.Lf} := by
  let S : AddSubgroup (Fin I.n → ιb I → Af I.F) :=
    { carrier := {w | (fun j => emb (bs I) (w j)) ∈ I.Lf}
      add_mem' := fun {w w'} hw hw' => by
        have : (fun j => emb (bs I) ((w + w') j)) = (fun j => emb (bs I) (w j)) + fun j => emb (bs I) (w' j) := by
          funext j; simp [emb_add]
        show (fun j => emb (bs I) ((w + w') j)) ∈ I.Lf
        rw [this]; exact I.Lf.add_mem hw hw'
      zero_mem' := by
        show (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) ∈ I.Lf
        have : (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) = 0 := by
          funext j; simp [emb_zero]
        rw [this]; exact I.Lf.zero_mem
      neg_mem' := fun {w} hw => by
        have : (fun j => emb (bs I) ((-w) j)) = -fun j => emb (bs I) (w j) := by
          funext j; simp [emb_neg]
        show (fun j => emb (bs I) ((-w) j)) ∈ I.Lf
        rw [this]; exact I.Lf.neg_mem hw }
  have hnhds : (S : Set (Fin I.n → ιb I → Af I.F)) ∈ 𝓝 0 := by
    let U := {w : Fin I.n → ιb I → Af I.F | ∀ j k, algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k ∈ Ohat I.F}
    have hU : IsOpen U := by
      have : U = ⋂ j, ⋂ k, (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) ⁻¹' Ohat I.F := by
        ext w; simp [U]
      rw [this]
      refine isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have hc : Continuous (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) :=
        continuous_const.mul ((continuous_apply k).comp (continuous_apply j))
      exact hc.isOpen_preimage _ isOpen_Ohat
    have h0 : (0 : Fin I.n → ιb I → Af I.F) ∈ U := fun j k => by simpa using ohat_zero
    refine Filter.mem_of_superset (hU.mem_nhds h0) fun w hw => ?_
    have hd0 : (d : I.F) ≠ 0 := by exact_mod_cast hd.ne'
    have := hlow (fun j => emb (bs I) (fun k => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k))
      (fun j k => by rw [coord_emb]; exact hw j k)
    show (fun j => emb (bs I) (w j)) ∈ I.Lf
    convert this using 1
    funext j
    rw [Pi.smul_apply, ← emb_nsmul]
    congr 1; funext k
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul,
      mul_inv_cancel₀ hd0, map_one, one_mul]
  exact AddSubgroup.isClosed_of_isOpen S (S.isOpen_of_mem_nhds hnhds)

end Cpt

end PI.WAU
end
end

section
noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

def Cset (N : ℕ) : Set (Co I × Co I) :=
  {p | (∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N) ∧
    matOf I p.1 * matOf I p.2 = 1 ∧ matOf I p.2 * matOf I p.1 = 1 ∧
    Formalism.UG.cT (sg I) (matOf I p.1) * Jf I * matOf I p.1 = Jf I ∧
    (∀ l ∈ I.L, matOf I p.1 *ᵥ inclV (F := I.F) l ∈ I.Lf) ∧
    (∀ l ∈ I.L, matOf I p.2 *ᵥ inclV (F := I.F) l ∈ I.Lf)}

theorem ctsA_fst (i j : Fin I.n) : CtsA (bs I) (fun p : Co I × Co I => matOf I p.1 i j) :=
  ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))

theorem ctsA_snd (i j : Fin I.n) : CtsA (bs I) (fun p : Co I × Co I => matOf I p.2 i j) :=
  ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

theorem ctsA_mulE {f g : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (hg : ∀ i j, CtsA (bs I) (fun p => g p i j)) (i j : Fin I.n) :
    CtsA (bs I) (fun p => (f p * g p) i j) := by
  simp only [Matrix.mul_apply]
  exact ctsA_sum _ fun l _ => ctsA_mul (hf i l) (hg l j)

theorem ctsA_constE (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (i j : Fin I.n) :
    CtsA (bs I) (fun _ : Co I × Co I => M i j) := ctsA_const _

theorem ctsA_cTE {f : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (i j : Fin I.n) :
    CtsA (bs I) (fun p => Formalism.UG.cT (sg I) (f p) i j) := by
  show CtsA (bs I) (fun p => Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (f p j i))
  exact ctsA_map _ (hf j i)

theorem isClosed_matEq {f g : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (hg : ∀ i j, CtsA (bs I) (fun p => g p i j)) :
    IsClosed {p | f p = g p} := by
  have : {p | f p = g p} = ⋂ i, ⋂ j, {p | f p i j = g p i j} := by
    ext p; simp [← Matrix.ext_iff]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eqA (bs I) (hf i j) (hg i j)

theorem isClosed_lat (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    {f : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) :
    IsClosed {p | ∀ l ∈ I.L, f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by
  have : {p | ∀ l ∈ I.L, f p *ᵥ inclV (F := I.F) l ∈ I.Lf} =
      ⋂ l ∈ I.L, {p | f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by
    ext; simp
  rw [this]
  refine isClosed_biInter fun l _ => ?_
  have hc : Continuous (fun p => fun j => coord (bs I) ((f p *ᵥ inclV (F := I.F) l) j)) := by
    refine continuous_pi fun j => ?_
    have : CtsA (bs I) (fun p => (f p *ᵥ inclV (F := I.F) l) j) := by
      simp only [Matrix.mulVec, dotProduct]
      exact ctsA_sum _ fun k _ => ctsA_mul (hf j k) (ctsA_const _)
    exact this
  have := (isClosed_LfC I d hd hlow).preimage hc
  convert this using 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, emb_coord]

theorem isCompact_Cset (N d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf) :
    IsCompact (Cset I N) := by
  have hbox : IsCompact {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} := by
    have : {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} =
        (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) ×ˢ
          (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) := by
      ext p
      simp only [Set.mem_prod, Set.mem_univ_pi, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨fun i j k => (h i j k).1, fun i j k => (h i j k).2⟩,
        fun h i j k => ⟨h.1 i j k, h.2 i j k⟩⟩
    rw [this]
    have h3 := isCompact_univ_pi fun _ : Fin I.n => isCompact_univ_pi fun _ : Fin I.n =>
      isCompact_univ_pi fun _ : ιb I => isCompact_Bx I N
    exact h3.prod h3
  have hf := ctsA_fst I
  have hs := ctsA_snd I
  have hc1 := isClosed_matEq I (ctsA_mulE I hf hs) (ctsA_constE I 1)
  have hc2 := isClosed_matEq I (ctsA_mulE I hs hf) (ctsA_constE I 1)
  have hc3 := isClosed_matEq I (ctsA_mulE I (ctsA_mulE I (ctsA_cTE I hf) (ctsA_constE I (Jf I))) hf)
    (ctsA_constE I (Jf I))
  have hc4 := isClosed_lat I d hd hlow hf
  have hc5 := isClosed_lat I d hd hlow hs
  exact hbox.inter_right (hc1.inter (hc2.inter (hc3.inter (hc4.inter hc5))))

def psi (N : ℕ) (p : Cset I N) : I.Gf :=
  ⟨⟨matOf I p.1.1, matOf I p.1.2, p.2.2.1, p.2.2.2.1⟩, p.2.2.2.2.1⟩

theorem psi_mem (N : ℕ) (p : Cset I N) : psi I N p ∈ I.Kset := by
  intro y
  have h1 := mulVec_mem_Lf I _ p.2.2.2.2.2.1
  have h2 := mulVec_mem_Lf I _ p.2.2.2.2.2.2
  show y ∈ I.Lf ↔ matOf I p.1.1 *ᵥ y ∈ I.Lf
  constructor
  · exact h1 y
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, p.2.2.2.1, Matrix.one_mulVec] at this

end Cpt

end PI.WAU
end
end

section
noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

private theorem intC_smul_entry_of_preserves_Lf (d D D1 : ℕ)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hg : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F,
      v ∈ I.Lf ↔ (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf)
    (i j : Fin I.n) :
    IntC (bs I) ((D * (d * D1)) • (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j) := by
  classical
  have hy : ∀ j', IntC (bs I)
      ((Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F) j') := by
    intro j'
    by_cases h : j' = j
    · rw [h, Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne h]
      intro k
      simp only [map_zero, Pi.zero_apply]
      exact (Formalism.UG.intAd I.F).zero_mem
  have hL := (hg _).mp (hlow _ hy)
  have hI := hup _ hL i
  have hs : ((g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ
      (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F)) i =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j * (D1 • (1 : I.E ⊗[I.F] Af I.F)) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : D • ((g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ
      (d • (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F))) i =
      (D * (d * D1)) • (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j := by
    rw [Matrix.mulVec_smul, Pi.smul_apply, hs]
    simp only [nsmul_eq_mul, Nat.cast_mul, mul_one]
    ring
  rwa [key] at hI

private theorem coord_mem_Bx_of_intC_nsmul (N : ℕ) (hN : 0 < N) (z : I.E ⊗[I.F] Af I.F)
    (hz : IntC (bs I) (N • z)) (k : ιb I) : coord (bs I) z k ∈ Bx I N := by
  simp only [Bx, Set.mem_image]
  refine ⟨N • coord (bs I) z k, ?_, ?_⟩
  · have := hz k
    rwa [map_nsmul, Pi.smul_apply] at this
  · have hN' : (N : I.F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)) N, ← map_mul,
      inv_mul_cancel₀ hN', map_one, one_mul]

theorem mem_range_psi (d D D1 : ℕ) (hN : 0 < D * (d * D1))
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    {x : I.Gf} (hx : x ∈ I.Kset) : ∃ p, psi I (D * (d * D1)) p = x := by
  classical
  have h0 : (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf := hx
  have h0i : ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹) ∈ Formalism.UG.stabGL I.Lf := inv_mem h0
  have hx' : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, v ∈ I.Lf ↔
      ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v
        ∈ I.Lf := h0
  have hxi' : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, v ∈ I.Lf ↔
      (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf := h0i
  have hm1 : matOf I (fun i j => coord (bs I) (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)) =
      ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) := by
    funext i j; simp only [matOf, emb_coord]
  have hm2 : matOf I (fun i j => coord (bs I)
      ((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)) =
      (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) := by
    funext i j; simp only [matOf, emb_coord]
  refine ⟨⟨(fun i j => coord (bs I) (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j), fun i j => coord (bs I)
      ((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)), ?_⟩, ?_⟩
  · simp only [Cset, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j k
      exact ⟨coord_mem_Bx_of_intC_nsmul I _ hN _ (intC_smul_entry_of_preserves_Lf I d D D1 hlow hup h1 _ hx' i j) k,
        coord_mem_Bx_of_intC_nsmul I _ hN _ (intC_smul_entry_of_preserves_Lf I d D D1 hlow hup h1 _ hxi' i j) k⟩
    · rw [hm1, hm2]; exact Units.mul_inv _
    · rw [hm1, hm2]; exact Units.inv_mul _
    · rw [hm1]; exact x.2
    · intro l hl
      rw [hm1]
      exact (hx' _).mp (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
    · intro l hl
      rw [hm2]
      exact (hxi' _).mp (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
  · exact Subtype.ext (Units.ext hm1)

theorem nat_smul_mul_eq (g d D m : ℕ) (a y : I.E ⊗[I.F] Af I.F) :
    ((g * d * D * m) • a) * y = (g * d) • (m • (a * (D • y))) := by
  simp only [nsmul_eq_mul, Nat.cast_mul]
  ring

theorem continuous_psi (N d D m : ℕ) (hd : 0 < d) (hD : 0 < D) (hm : 0 < m)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j))
    (hmul : ∀ x y : I.E ⊗[I.F] Af I.F, IntC (bs I) x → IntC (bs I) y → IntC (bs I) (m • (x * y))) :
    Continuous (psi I N) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  intro U hU
  have hV : (fun z => psi I N p * z) ⁻¹' U ∈ 𝓝 (1 : I.Gf) := by
    have := (continuous_mul_left (psi I N p)).tendsto 1
    rw [mul_one] at this
    exact this hU
  obtain ⟨g, hg1, hsub⟩ := I.topf_basis _ hV
  have hN1' : ((g * d * D * m : ℕ) : I.F) ≠ 0 := by
    have : 0 < g * d * D * m := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hg1 hd) hD) hm
    exact_mod_cast this.ne'
  let c : I.F := ((g * d * D * m : ℕ) : I.F)⁻¹
  let W : Set (Cset I N) := {p' | ∀ i j k, algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k) ∈ Ohat I.F}
  have hW : W ∈ 𝓝 p := by
    have hWo : IsOpen W := by
      have : W = ⋂ i, ⋂ j, ⋂ k, (fun p' : Cset I N => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)) ⁻¹'
          Ohat I.F := by
        ext; simp [W]
      rw [this]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have h0 : Continuous (fun p' : Cset I N => p'.1.1 i j k) := by fun_prop
      have hc : Continuous (fun p' : Cset I N => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)) :=
        continuous_const.mul (h0.sub continuous_const)
      exact hc.isOpen_preimage _ isOpen_Ohat
    exact hWo.mem_nhds (fun i j k => by simpa using ohat_zero)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hW fun p' hp' => ?_
  have hQM : matOf I p.1.2 * matOf I p.1.1 = 1 := p.2.2.2.1
  let x := (psi I N p)⁻¹ * psi I N p'
  have hxK : x ∈ I.Kset :=
    (Formalism.UG.stabGL I.Lf).mul_mem ((Formalism.UG.stabGL I.Lf).inv_mem (psi_mem I N p)) (psi_mem I N p')
  have hfx : I.fmat x = matOf I p.1.2 * matOf I p'.1.1 := rfl
  have hcond : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat x - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    let u : Co I := fun i j k => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)
    have hu : ∀ i j k, u i j k ∈ Ohat I.F := hp'
    have hδ : ∀ i j, matOf I p'.1.1 i j - matOf I p.1.1 i j = (g * d * D * m) • emb (bs I) (u i j) := by
      intro i j
      simp only [matOf]
      rw [← emb_sub, ← emb_nsmul]
      congr 1; funext k
      simp only [u, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, c]
      rw [← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hN1', map_one,
        one_mul]
    let w : Fin I.n → I.E ⊗[I.F] Af I.F := fun i => ∑ j, m • (emb (bs I) (u i j) * (D • y j))
    have hw : ∀ i, IntC (bs I) (w i) := fun i => intC_sum _ fun j _ =>
      hmul _ _ (fun k => by rw [coord_emb]; exact hu i j k) (hup y hy j)
    have hdw := hlow w hw
    have hmv : (matOf I p'.1.1 - matOf I p.1.1) *ᵥ y = (g * d) • w := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, hδ, nat_smul_mul_eq I, Pi.smul_apply,
        Finset.smul_sum, w]
    refine ⟨matOf I p.1.2 *ᵥ (d • w), mulVec_mem_Lf I _ p.2.2.2.2.2.2 _ hdw, ?_⟩
    rw [hfx, ← hQM, ← Matrix.mul_sub, ← Matrix.mulVec_mulVec, hmv, mul_smul, Matrix.mulVec_smul,
      Nat.cast_smul_eq_nsmul]
  have hx := hsub ⟨hxK, hcond⟩
  show psi I N p' ∈ U
  have : psi I N p * x = psi I N p' := mul_inv_cancel_left _ _
  rw [← this]; exact hx

theorem isCompact_Kset : IsCompact I.Kset := by
  obtain ⟨d, hd, hlow⟩ := exists_lower (bs I) I.L I.L_span
  obtain ⟨D, hD, hup⟩ := exists_upper (bs I) I.L I.L_fg
  obtain ⟨m, hm, hmul⟩ := exists_den_mul (bs I)
  obtain ⟨D1, hD1, h1F⟩ := exists_den_fin (fun k : ιb I => (bs I).repr 1 k)
  have h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)) := by
    intro k
    rw [map_nsmul, ← map_one (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (A := I.E) (B := Af I.F)),
      coord_incl, Pi.smul_apply, nsmul_eq_mul, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul]
    exact h1F k
  have hN : 0 < D * (d * D1) := Nat.mul_pos hD (Nat.mul_pos hd hD1)
  haveI : CompactSpace (Cset I (D * (d * D1))) :=
    isCompact_iff_compactSpace.mp (isCompact_Cset I _ d hd hlow)
  have : I.Kset = Set.range (psi I (D * (d * D1))) := by
    ext x
    constructor
    · intro hx; exact mem_range_psi I d D D1 hN hlow hup h1 hx
    · rintro ⟨p, rfl⟩; exact psi_mem I _ p
  rw [this]
  exact isCompact_range (continuous_psi I _ d D m hd hD hm hlow hup hmul)

end Cpt

end PI.WAU
end
end
