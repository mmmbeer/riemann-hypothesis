import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwaStmt

section
noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology

variable {F : Type} [Field F] [NumberField F]

theorem val_algebraMap_F (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (v.adicCompletion F) t) = v.valuation F t := by
  rw [algebraMap_adicCompletion]
  simp [valuedAdicCompletion_eq_valuation']

theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  have hnhds : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
    mem_closure_iff_nhds.mp ((denseRange_algebraMap (K := F) (v := v)) x) _ hnhds
  simp only [Set.mem_ofPred_eq] at hy
  have hk : v.valuation F k ≤ 1 := by
    rw [← val_algebraMap_F]
    calc Valued.v (algebraMap F (v.adicCompletion F) k)
        = Valued.v ((algebraMap F (v.adicCompletion F) k - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap F (v.adicCompletion F) k - x)) (Valued.v x) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk 1
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) k -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
    rw [← map_sub, val_algebraMap_F, ← Valuation.map_neg, neg_sub]
    simpa using ha
  calc Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      = Valued.v ((x - algebraMap F (v.adicCompletion F) k) + (algebraMap F (v.adicCompletion F) k -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := by
      refine max_lt ?_ h2
      rw [← Valuation.map_neg, neg_sub]; exact hy

def toOv (v : HeightOneSpectrum (𝓞 F)) : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict _ (fun a => by
    show Valued.v (_ : v.adicCompletion F) ≤ 1
    simp only [RingHom.comp_apply]
    rw [val_algebraMap_F, valuation_of_algebraMap]
    exact intValuation_le_one v a)

theorem toOv_coe (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    ((toOv v a : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

theorem isUnit_integer_iff (v : HeightOneSpectrum (𝓞 F)) (x : Valued.integer (v.adicCompletion F)) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
  (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one

theorem finite_residue (v : HeightOneSpectrum (𝓞 F)) :
    Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))) := by
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
    (IsLocalRing.residue _).comp (toOv v)
  have hker : ∀ a ∈ v.asIdeal, φ a = 0 := by
    intro a ha
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, isUnit_integer_iff, toOv_coe, val_algebraMap_F, valuation_of_algebraMap]
    exact ((intValuation_lt_one_iff_mem v a).mpr ha).ne
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  refine Finite.of_surjective ψ ?_
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_int_near v (x : v.adicCompletion F) x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  simp only [ψ, Ideal.Quotient.lift_mk, φ, RingHom.comp_apply]
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_integer_iff]
  push_cast [toOv_coe]
  exact ha.ne

theorem compactSpace_integer (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residue v⟩
  · exact (Valued.isClosed_integer (R := v.adicCompletion F)).completeSpace_coe
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))

theorem isCompact_Ov (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this

instance compactSpace_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

def Ohat (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem isOpen_Ohat : IsOpen (Ohat F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

instance compactSpace_Ov' (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

theorem isCompact_Ohat : IsCompact (Ohat F) := by
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have : Ohat F = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨x, rfl⟩ v
      exact (x v).2
  rw [this]
  exact isCompact_range hc

instance t2Space_finiteAdeleRing_alt : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

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

end Topology

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

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

theorem ohat_add {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a + c ∈ Ohat F :=
  fun v => by
    show a v + c v ∈ _
    exact add_mem (ha v) (hc v)

theorem ohat_zero : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F :=
  fun v => by
    show (0 : v.adicCompletion F) ∈ _
    exact zero_mem _

theorem ohat_nsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℕ) : m • a ∈ Ohat F := by
  induction m with
  | zero => simpa using ohat_zero
  | succ m ih => rw [succ_nsmul]; exact ohat_add ih ha

section Coord

variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

local notation "Af" => FiniteAdeleRing (𝓞 F) F

def IntC (x : E ⊗[F] Af) : Prop := ∀ k, coord b x k ∈ Ohat F

variable {b}

end Coord

end PI.IwaMeasEx.Wau

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Wau

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
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simpa using L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, h1, hx⟩ := hx
    obtain ⟨m2, h2, hy⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos h1 h2, ?_⟩
    have : (m1 * m2) • (x + y) = m2 • (m1 • x) + m1 • (m2 • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m2 m1]
    rw [this]
    exact L.add_mem (nsmul_mem hx m2) (nsmul_mem hy m1)
  | smul e x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨t, ht, a, ha⟩ := exists_den e
    refine ⟨t * m, Nat.mul_pos ht hm, ?_⟩
    have : (t * m) • (e • x) = a • (m • x) := by
      rw [← algebraMap_smul E a (m • x), ← ha, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, smul_smul]
      congr 1
      push_cast; ring
    rw [this]
    exact L.smul_mem a hx

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

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem intC_zero {b : Module.Basis ι F E} : IntC b (0 : E ⊗[F] Af) := fun k => by
  rw [map_zero]; exact ohat_zero

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {B : Type} [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

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

end Cpt

end PI.IwaMeasEx.Wau

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

theorem mem_Bx {N : ℕ} (hN : 0 < N) {a : Af I.F} (ha : N • a ∈ Ohat I.F) : a ∈ Bx I N := by
  refine ⟨N • a, ha, ?_⟩
  have hN0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
  simp only
  rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, inv_mul_cancel₀ hN0,
    map_one, one_mul]

def Cset (N : ℕ) : Set (Co I × Co I) :=
  {p | (∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N) ∧
    matOf I p.1 * matOf I p.2 = 1 ∧ matOf I p.2 * matOf I p.1 = 1 ∧
    Formalism.UG.cT (sg I) (matOf I p.1) * Jf I * matOf I p.1 = Jf I ∧
    (∀ l ∈ I.L, matOf I p.1 *ᵥ inclV (F := I.F) l ∈ I.Lf) ∧
    (∀ l ∈ I.L, matOf I p.2 *ᵥ inclV (F := I.F) l ∈ I.Lf)}

def psi (N : ℕ) (p : Cset I N) : I.Gf :=
  ⟨⟨matOf I p.1.1, matOf I p.1.2, p.2.2.1, p.2.2.2.1⟩, p.2.2.2.2.1⟩

end Cpt

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

end Cpt

end PI.IwaMeasEx.Wau

end
end
