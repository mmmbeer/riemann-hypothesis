import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocallyCompactSpaceOfIsClosed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankGroupCohomologyFunRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.JmMulJm

section
noncomputable section

open GlobalTheory.Mt.Adelic

namespace GlobalTheory.HkPart

section Fix

variable {E G V : Type} [Field E] [Group G] [AddCommGroup V] [Module E V]

def fix (π : Representation E G V) (K : Subgroup G) : Submodule E V :=
  Representation.invariants (π.comp K.subtype)

variable (π : Representation E G V) {K : Subgroup G}

theorem mem_fix {v : V} : v ∈ fix π K ↔ ∀ k ∈ K, π k v = v :=
  by rw [fix, Representation.mem_invariants]; exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩

theorem apply_eq_of_coset {v : V} (hv : v ∈ fix π K) {x y : G} (h : (x : G ⧸ K) = y) :
    π x v = π y v := by
  rw [QuotientGroup.eq] at h
  rw [show y = x * (x⁻¹ * y) by group, map_mul, Module.End.mul_apply, (mem_fix π).1 hv _ h]

theorem sum_mem_fix {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) {v : V} (hv : v ∈ fix π K) :
    (∑ i, π (z i) v) ∈ fix π K := by
  rw [mem_fix]
  intro k hk
  let F : G ⧸ K → V := fun y => π y.out v
  have hF : ∀ x : G, π x v = F (x : G ⧸ K) := fun x =>
    apply_eq_of_coset π hv (QuotientGroup.out_eq' (x : G ⧸ K)).symm
  rw [map_sum]
  calc ∑ i, π k (π (z i) v) = ∑ i, F ((k * z i : G) : G ⧸ K) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Module.End.mul_apply, ← map_mul, hF]
    _ = ∑ i, F ((z i : G) : G ⧸ K) := sum_heckeFam hz F hk
    _ = ∑ i, π (z i) v := Finset.sum_congr rfl fun i _ => (hF _).symm

def op {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) : Module.End E (fix π K) :=
  (∑ i, π (z i)).restrict fun v hv => by
    rw [LinearMap.sum_apply]; exact sum_mem_fix π hz hv

theorem coe_op {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) (v : fix π K) :
    ((op π hz v : fix π K) : V) = ∑ i, π (z i) v := by
  simp [op, LinearMap.restrict_apply]

theorem isHeckeFam_one (K : Subgroup G) : IsHeckeFam K (fun _ : Fin 1 => (1 : G)) := by
  intro k hk
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [mul_one]
  exact QuotientGroup.eq.2 (by simpa using hk)

theorem op_one : op π (isHeckeFam_one K) = LinearMap.id := by
  ext v
  simp [coe_op]

end Fix

section Part

variable {E G V M M' M'' : Type} [Field E] [Group G] [AddCommGroup V] [Module E V]
  [AddCommGroup M] [Module E M] [AddCommGroup M'] [Module E M'] [AddCommGroup M''] [Module E M'']

variable (E) in

abbrev HeckeRel (K : Subgroup G) (M : Type) [AddCommGroup M] [Module E M] : Type :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G), IsHeckeFam K z → Module.End E M → Prop

def HeckeRel.ofFun {K : Subgroup G} (t : ∀ {n : ℕ} (z : Fin n → G), IsHeckeFam K z → Module.End E M) :
    HeckeRel E K M :=
  fun _ z hz T => T = t z hz

def part (π : Representation E G V) (K : Subgroup G) (R : HeckeRel E K M) :
    Submodule E (fix π K →ₗ[E] M) where
  carrier := {φ | ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M),
    R z hz T → φ ∘ₗ op π hz = T ∘ₗ φ}
  add_mem' {a b} ha hb n z hz T hT := by
    rw [LinearMap.add_comp, LinearMap.comp_add, ha z hz T hT, hb z hz T hT]
  zero_mem' n z hz T hT := by simp
  smul_mem' c a ha n z hz T hT := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ha z hz T hT]

variable {π : Representation E G V} {K : Subgroup G} {R : HeckeRel E K M}

theorem mem_part {φ : fix π K →ₗ[E] M} : φ ∈ part π K R ↔
    ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M), R z hz T → φ ∘ₗ op π hz = T ∘ₗ φ :=
  Iff.rfl

theorem mem_part_iff_apply {φ : fix π K →ₗ[E] M} : φ ∈ part π K R ↔
    ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M), R z hz T →
      ∀ v, φ (op π hz v) = T (φ v) := by
  refine ⟨fun h n z hz T hT v => LinearMap.congr_fun (h z hz T hT) v, fun h n z hz T hT => ?_⟩
  ext v
  exact h z hz T hT v

theorem part_apply_op (φ : part π K R) {n : ℕ} {z : Fin n → G} {hz : IsHeckeFam K z} {T : Module.End E M}
    (hT : R z hz T) (v : fix π K) : (φ : fix π K →ₗ[E] M) (op π hz v) = T ((φ : fix π K →ₗ[E] M) v) :=
  mem_part_iff_apply.1 φ.2 z hz T hT v


def Intertw (R : HeckeRel E K M) (R' : HeckeRel E K M') (f : M →ₗ[E] M') : Prop :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T' : Module.End E M'), R' z hz T' →
    ∃ T, R z hz T ∧ f ∘ₗ T = T' ∘ₗ f

theorem Intertw.comp {R : HeckeRel E K M} {R' : HeckeRel E K M'} {R'' : HeckeRel E K M''} {f : M →ₗ[E] M'}
    {g : M' →ₗ[E] M''} (hf : Intertw R R' f) (hg : Intertw R' R'' g) : Intertw R R'' (g ∘ₗ f) := by
  intro n z hz T'' hT''
  obtain ⟨T', hT', e'⟩ := hg z hz T'' hT''
  obtain ⟨T, hT, e⟩ := hf z hz T' hT'
  refine ⟨T, hT, ?_⟩
  rw [LinearMap.comp_assoc, e, ← LinearMap.comp_assoc, e', LinearMap.comp_assoc]

variable (π) in

def map {R : HeckeRel E K M} {R' : HeckeRel E K M'} (f : M →ₗ[E] M') (hf : Intertw R R' f) :
    part π K R →ₗ[E] part π K R' where
  toFun φ := ⟨f ∘ₗ (φ : fix π K →ₗ[E] M), fun _ z hz T' hT' => by
    obtain ⟨T, hT, e⟩ := hf z hz T' hT'
    rw [LinearMap.comp_assoc, mem_part.1 φ.2 z hz T hT, ← LinearMap.comp_assoc, e, LinearMap.comp_assoc]⟩
  map_add' a b := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' c a := Subtype.ext (LinearMap.comp_smul _ _ _)

@[simp] theorem coe_map {R' : HeckeRel E K M'} (f : M →ₗ[E] M') (hf : Intertw R R' f) (φ : part π K R) :
    ((map π f hf φ : part π K R') : fix π K →ₗ[E] M') = f ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

def Commutes (R : HeckeRel E K M) (f : Module.End E M) : Prop :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M), R z hz T → f ∘ₗ T = T ∘ₗ f

theorem Commutes.intertw {f : Module.End E M} (hf : Commutes R f) : Intertw R R f :=
  fun _ z hz T hT => ⟨T, hT, hf z hz T hT⟩

variable (π) in

def endo (f : Module.End E M) (hf : Commutes R f) : Module.End E (part π K R) :=
  map π f hf.intertw

@[simp] theorem coe_endo (f : Module.End E M) (hf : Commutes R f) (φ : part π K R) :
    ((endo π f hf φ : part π K R) : fix π K →ₗ[E] M) = f ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

variable (π) in

def partRep {Γ : Type} [Group Γ] (ρ : Representation E Γ M) (hρ : ∀ γ, Commutes R (ρ γ)) :
    Representation E Γ (part π K R) where
  toFun γ := endo π (ρ γ) (hρ γ)
  map_one' := by
    ext φ : 1
    exact Subtype.ext (by ext v; simp)
  map_mul' a b := by
    ext φ : 1
    exact Subtype.ext (by simp [LinearMap.comp_assoc]; rfl)

@[simp] theorem coe_partRep {Γ : Type} [Group Γ] (ρ : Representation E Γ M) (hρ : ∀ γ, Commutes R (ρ γ)) (γ : Γ)
    (φ : part π K R) :
    ((partRep π ρ hρ γ φ : part π K R) : fix π K →ₗ[E] M) = ρ γ ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

instance [FiniteDimensional E (fix π K)] [FiniteDimensional E M] : FiniteDimensional E (part π K R) :=
  inferInstance

end Part

section Pi

variable {E G V ι : Type} [Field E] [Group G] [AddCommGroup V] [Module E V] [DecidableEq ι]
  {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module E (M i)] {K : Subgroup G}

def piRel (R : ∀ i, HeckeRel E K (M i)) : HeckeRel E K (∀ i, M i) :=
  fun _ z hz T => ∃ Ts : ∀ i, Module.End E (M i), (∀ i, R i z hz (Ts i)) ∧
    T = LinearMap.pi fun i => Ts i ∘ₗ LinearMap.proj i

variable (π : Representation E G V) (R : ∀ i, HeckeRel E K (M i))

def partPi (hR : ∀ i {n : ℕ} (z : Fin n → G) (hz : IsHeckeFam K z), ∃ T, R i z hz T) :
    part π K (piRel R) ≃ₗ[E] ∀ i, part π K (R i) where
  toFun φ i := ⟨LinearMap.proj i ∘ₗ (φ : fix π K →ₗ[E] ∀ i, M i), by
    rw [mem_part_iff_apply]
    intro n z hz T hT v
    classical
    let Ts : ∀ j, Module.End E (M j) := Function.update (fun j => (hR j z hz).choose) i T
    have hTs : ∀ j, R j z hz (Ts j) := by
      intro j
      by_cases h : j = i
      · subst h; simpa [Ts] using hT
      · simpa [Ts, h] using (hR j z hz).choose_spec
    have := part_apply_op φ (T := LinearMap.pi fun j => Ts j ∘ₗ LinearMap.proj j) ⟨Ts, hTs, rfl⟩ v
    have := congrFun this i
    simpa [Ts] using this⟩
  invFun ψ := ⟨LinearMap.pi fun i => ((ψ i : part π K (R i)) : fix π K →ₗ[E] M i), by
    rw [mem_part_iff_apply]
    rintro n z hz T ⟨Ts, hTs, rfl⟩ v
    funext i
    simpa using part_apply_op (ψ i) (hTs i) v⟩
  map_add' a b := by ext i : 1; exact Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' c a := by ext i : 1; exact Subtype.ext (LinearMap.comp_smul _ _ _)
  left_inv φ := by
    apply Subtype.ext
    ext v i
    rfl
  right_inv ψ := by
    funext i
    apply Subtype.ext
    ext v
    rfl

end Pi

section Transport

variable {E' E : Type} [Field E'] [Field E]

def Tr (_ι : E' ≃+* E) (V : Type) : Type := V

variable (ι : E' ≃+* E) {V : Type} [AddCommGroup V] [Module E V]

instance : AddCommGroup (Tr ι V) := inferInstanceAs (AddCommGroup V)

instance : Module E' (Tr ι V) := Module.compHom V (ι : E' →+* E)

def Tr.of : V ≃+ Tr ι V := AddEquiv.refl V

variable {G : Type} [Group G]

def trRep (π : Representation E G V) : Representation E' G (Tr ι V) where
  toFun g :=
    { toFun := fun v => Tr.of ι (π g ((Tr.of ι).symm v))
      map_add' := fun v w => (π g).map_add v w
      map_smul' := fun c v => (π g).map_smul (ι c) v }
  map_one' := by ext v; simp [Tr.of]; rfl
  map_mul' a b := by
    ext v
    change Tr.of ι (π (a * b) _) = Tr.of ι (π a (π b _))
    rw [map_mul]; rfl

end Transport

section Inhabitant

variable {E G M : Type} [Field E] [Group G] [AddCommGroup M] [Module E M] (K : Subgroup G)

variable (E) in

def mulRel (M : Type) [AddCommGroup M] [Module E M] : HeckeRel E K M :=
  fun n _ _ T => T = (n : E) • LinearMap.id

variable (E) in

def zeroRel (M : Type) [AddCommGroup M] [Module E M] : HeckeRel E K M :=
  fun _ _ _ T => T = 0

theorem fix_trivial : fix (Representation.trivial E G E) K = ⊤ :=
  eq_top_iff.2 fun v _ => (mem_fix _).2 fun _ _ => rfl

theorem op_trivial {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) :
    op (Representation.trivial E G E) hz = (n : E) • LinearMap.id := by
  ext v
  simp [coe_op, Finset.sum_const, Finset.card_univ]

theorem part_trivial_mulRel : part (Representation.trivial E G E) K (mulRel E K M) = ⊤ := by
  refine eq_top_iff.2 fun φ _ => mem_part.2 fun n z hz T hT => ?_
  rw [op_trivial, show T = (n : E) • LinearMap.id from hT]
  ext v
  simp

theorem finrank_part_trivial_mulRel :
    Module.finrank E (part (Representation.trivial E G E) K (mulRel E K E)) = 1 := by
  rw [part_trivial_mulRel, finrank_top, Module.finrank_linearMap, fix_trivial, finrank_top,
    Module.finrank_self, one_mul]

theorem part_zeroRel {V : Type} [AddCommGroup V] [Module E V] (π : Representation E G V) :
    part π K (zeroRel E K M) = ⊥ := by
  refine eq_bot_iff.2 fun φ hφ => ?_
  have h := mem_part.1 hφ (fun _ : Fin 1 => (1 : G)) (isHeckeFam_one K) 0 rfl
  rw [op_one, LinearMap.comp_id, LinearMap.zero_comp] at h
  exact (Submodule.mem_bot E).2 h

example (v : fix (Representation.trivial ℚ G ℚ) K) : op (Representation.trivial ℚ G ℚ) (isHeckeFam_one K) v = v := by
  rw [op_one]; rfl

example : FiniteDimensional ℚ (part (Representation.trivial ℚ G ℚ) K (mulRel ℚ K ℚ)) := inferInstance

example : Module.finrank ℚ (part (Representation.trivial ℚ G ℚ) K (mulRel ℚ K ℚ)) = 1 :=
  finrank_part_trivial_mulRel K

example : part (Representation.trivial ℚ G ℚ) K (zeroRel ℚ K ℚ) = ⊥ := part_zeroRel K _

end Inhabitant

end GlobalTheory.HkPart
end
end

section
noncomputable section

open NumberField Matrix GlobalTheory.LKTrip GlobalTheory.Mt.Adelic ReciprocityTheory.ChartRestriction.DS GlobalTheory.Kg
open scoped TensorProduct Matrix.Norms.L2Operator

namespace GlobalTheory.HTBetti

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

abbrev Gf : Type := G.GAf × G.GQp

def toF : G.GQ →* Gf G := G.toAf.prod (ubc ℚ_[p])

abbrev coh (Kf : Subgroup (Gf G)) {d : ℕ} (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) : Type :=
  groupCohomology (Rep.of (funRepY (toF G) Kf ξ₀)) q

def hecke {Kf : Subgroup (Gf G)} {n : ℕ} {z : Fin n → Gf G} (hz : IsHeckeFam Kf z) {d : ℕ}
    (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) : Module.End ℂ (coh G Kf ξ₀ q) :=
  heckeCoh (ρf := toF G) hz ξ₀ q

def heckeRel (Kf : Subgroup (Gf G)) {d : ℕ} (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) :
    GlobalTheory.HkPart.HeckeRel ℂ Kf (coh G Kf ξ₀ q) :=
  GlobalTheory.HkPart.HeckeRel.ofFun fun z hz => hecke G hz ξ₀ q

abbrev piPart {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (Gf G) V) (Kf : Subgroup (Gf G))
    {d : ℕ} (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) :
    Submodule ℂ (GlobalTheory.HkPart.fix π Kf →ₗ[ℂ] coh G Kf ξ₀ q) :=
  GlobalTheory.HkPart.part π Kf (heckeRel G Kf ξ₀ q)


section Classes

variable (Kf : Subgroup (Gf G))

abbrev act : MulAction G.GQ (Gf G ⧸ Kf) := yAct (toF G) Kf

abbrev Classes : Type := letI := act G Kf; MulAction.orbitRel.Quotient G.GQ (Gf G ⧸ Kf)

def pt (c : Classes G Kf) : Gf G ⧸ Kf := letI := act G Kf; Quotient.out c

def gam (y : Gf G ⧸ Kf) : Subgroup G.GQ := letI := act G Kf; MulAction.stabilizer G.GQ y


theorem pt_cover : letI := act G Kf; ∀ y : Gf G ⧸ Kf, ∃ c : Classes G Kf, ∃ g : G.GQ, g • pt G Kf c = y := by
  letI := act G Kf
  intro y
  refine ⟨Quotient.mk'' y, ?_⟩
  have h : pt G Kf (Quotient.mk'' y) ∈ MulAction.orbit G.GQ y :=
    MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk'' y : Classes G Kf)))
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

theorem pt_disjoint : letI := act G Kf;
    ∀ (i j : Classes G Kf) (g : G.GQ), g • pt G Kf i = pt G Kf j → i = j := by
  letI := act G Kf
  intro i j g h
  rw [← Quotient.out_eq i, ← Quotient.out_eq j]
  apply Quotient.sound
  refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g⁻¹, ?_⟩)
  change g⁻¹ • pt G Kf j = pt G Kf i
  rw [← h, inv_smul_smul]

def cohEquivPi {d : ℕ} (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) :
    coh G Kf ξ₀ q ≃ₗ[ℂ] ∀ c : Classes G Kf,
      groupCohomology (Rep.of (GlobalTheory.BorelCoh.matVecRep (ξ₀.comp (gam G Kf (pt G Kf c)).subtype))) q :=
  letI := act G Kf
  GlobalTheory.BorelCoh.Shapiro.cohEquiv ξ₀ (pt G Kf) (pt_cover G Kf) (pt_disjoint G Kf) q

end Classes

section UJpm

variable {T : Type} [Fintype T] {n : ℕ}

def UJpm (ε : T → Fin n → Bool) : Subgroup (MatT T n)ˣ where
  carrier := {g | ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ τ, (g.val τ)ᴴ * Jm (ε τ) * g.val τ = (s : ℂ) • Jm (ε τ)}
  one_mem' := ⟨1, Or.inl rfl, fun τ => by simp⟩
  mul_mem' := by
    rintro g h ⟨s, hs, hg⟩ ⟨t, ht, hh⟩
    refine ⟨s * t, ?_, fun τ => ?_⟩
    · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
    · simp only [Units.val_mul, Pi.mul_apply, Matrix.conjTranspose_mul]
      calc (h.val τ)ᴴ * (g.val τ)ᴴ * Jm (ε τ) * (g.val τ * h.val τ)
          = (h.val τ)ᴴ * ((g.val τ)ᴴ * Jm (ε τ) * g.val τ) * h.val τ := by simp only [Matrix.mul_assoc]
        _ = ((s * t : ℝ) : ℂ) • Jm (ε τ) := by
          rw [hg τ, Matrix.mul_smul, Matrix.smul_mul, hh τ, smul_smul]
          push_cast; ring_nf
  inv_mem' := by
    rintro g ⟨s, hs, hg⟩
    refine ⟨s, hs, fun τ => ?_⟩
    have h1 : g.val τ * (g⁻¹).val τ = 1 := by
      rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]
    have hss : (s : ℂ) * s = 1 := by rcases hs with rfl | rfl <;> norm_num
    calc ((g⁻¹).val τ)ᴴ * Jm (ε τ) * (g⁻¹).val τ
        = (s : ℂ) • (((g⁻¹).val τ)ᴴ * ((s : ℂ) • Jm (ε τ)) * (g⁻¹).val τ) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hss, one_smul]
      _ = (s : ℂ) • ((g.val τ * (g⁻¹).val τ)ᴴ * Jm (ε τ) * (g.val τ * (g⁻¹).val τ)) := by
          rw [← hg τ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (s : ℂ) • Jm (ε τ) := by rw [h1]; simp


end UJpm

section Frame

def eps (v : InfinitePlace G.F) : Fin G.n → Bool := fun i => decide (0 < (G.gram_herm v).eigenvalues i)

theorem Jm_eps (v : InfinitePlace G.F) :
    Jm (eps G v) = diagonal (GlobalTheory.HermCongruence.signVec (G.gram_herm v)) := by
  unfold Jm eps GlobalTheory.HermCongruence.signVec
  congr 1
  funext i
  by_cases h : 0 < (G.gram_herm v).eigenvalues i <;> simp [h]


def frame (v : InfinitePlace G.F) : GL (Fin G.n) ℂ :=
  (GlobalTheory.HermCongruence.exists_congr_signVec (G.gram_herm v) (G.gram_det v)).choose

theorem frame_spec (v : InfinitePlace G.F) :
    ((frame G v : Matrix (Fin G.n) (Fin G.n) ℂ))ᴴ * G.gram v * (frame G v : Matrix (Fin G.n) (Fin G.n) ℂ) =
      Jm (eps G v) := by
  rw [Jm_eps]
  exact (GlobalTheory.HermCongruence.exists_congr_signVec (G.gram_herm v) (G.gram_det v)).choose_spec

def conjGL {m : ℕ} (P : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ →ₐ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun X := ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * X * P
  map_one' := by
    rw [Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  map_mul' X Y := by
    have h : ((P : Matrix (Fin m) (Fin m) ℂ) * ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * (X * Y) * P =
      ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * X * P * (((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * Y * P)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P : Matrix (Fin m) (Fin m) ℂ), h, Matrix.one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    show ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * algebraMap ℝ (Matrix (Fin m) (Fin m) ℂ) r * P = _
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]

theorem conjGL_apply {m : ℕ} (P : GL (Fin m) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    conjGL P X = ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * X * P := rfl

theorem conjGL_sim {m : ℕ} (P : GL (Fin m) ℂ) (h X : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (hX : Xᴴ * h * X = c • h) :
    (conjGL P X)ᴴ * ((P : Matrix (Fin m) (Fin m) ℂ)ᴴ * h * P) * conjGL P X =
      c • ((P : Matrix (Fin m) (Fin m) ℂ)ᴴ * h * P) := by
  have h1 : (((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ))ᴴ * (P : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.conjTranspose_one]
  have h2 : (P : Matrix (Fin m) (Fin m) ℂ) * ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [conjGL_apply]
  calc _ = (P : Matrix (Fin m) (Fin m) ℂ)ᴴ * Xᴴ *
        ((((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ))ᴴ * (P : Matrix (Fin m) (Fin m) ℂ)ᴴ) * h *
        ((P : Matrix (Fin m) (Fin m) ℂ) * ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) * X * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P : Matrix (Fin m) (Fin m) ℂ)ᴴ * (Xᴴ * h * X) * P := by
        rw [h1, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hX, Matrix.mul_smul, Matrix.smul_mul]

def mat : ℝ ⊗[ℚ] G.C →ₐ[ℝ] MatT (InfinitePlace G.F) G.n :=
  Pi.algHom ℝ _ fun v => (conjGL (frame G v)).comp (G.psiR v)

theorem mat_apply (x : ℝ ⊗[ℚ] G.C) (v : InfinitePlace G.F) : mat G x v = conjGL (frame G v) (G.psiR v x) := rfl

theorem psiR_star (v : InfinitePlace G.F) (x : ℝ ⊗[ℚ] G.C) :
    G.psiR v (starT G.star ℝ x).unop = (G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    rw [starT_tmul, HTGroup.psiR_tmul, HTGroup.psiR_tmul, G.psi_star, Matrix.conjTranspose_smul, star_trivial,
      Matrix.mul_smul, Matrix.smul_mul]
  | add x y hx hy =>
    simp only [map_add, MulOpposite.unop_add, hx, hy, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem psiR_sim (g : G.GR) (v : InfinitePlace G.F) :
    (G.psiR v ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C))ᴴ * G.gram v *
        G.psiR v ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C) =
      ((((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ) : ℂ) • G.gram v := by
  set x : ℝ ⊗[ℚ] G.C := ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C)
  set c : ℝ := (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ)
  have hx : x * (starT G.star ℝ x).unop = algebraMap ℝ (ℝ ⊗[ℚ] G.C) c := g.2
  have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Units.ne_zero _)
  have hdet : IsUnit (G.gram v).det := (G.gram_det v).isUnit
  have h1 := congrArg (G.psiR v) hx
  rw [map_mul, psiR_star, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    RCLike.real_smul_eq_coe_smul (K := ℂ)] at h1
  have h2 : (G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v * G.psiR v x = (c : ℂ) • 1 :=
    (mul_eq_smul_one_comm hc).1 h1
  calc (G.psiR v x)ᴴ * G.gram v * G.psiR v x
      = G.gram v * ((G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v * G.psiR v x) := by
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    _ = _ := by rw [h2, Matrix.mul_smul, Matrix.mul_one]

end Frame

section Norm

def invSqrtAbs : ℝˣ →* ℝˣ where
  toFun c := Units.mk0 (Real.sqrt |(c : ℝ)|)⁻¹ (inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 c.ne_zero)).ne')
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp [abs_mul, Real.sqrt_mul (abs_nonneg _), mul_inv, mul_comm]

theorem invSqrtAbs_sq (c : ℝˣ) : ((invSqrtAbs c : ℝˣ) : ℝ) * (invSqrtAbs c : ℝˣ) * c = SignType.sign (c : ℝ) := by
  have hc := c.ne_zero
  have hpos : 0 < |(c : ℝ)| := abs_pos.2 hc
  show (Real.sqrt |(c : ℝ)|)⁻¹ * (Real.sqrt |(c : ℝ)|)⁻¹ * c = _
  rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  rcases lt_or_gt_of_ne hc with h | h
  · rw [abs_of_neg h, sign_neg h]; field_simp; simp
  · rw [abs_of_pos h, sign_pos h]; field_simp; simp

def normR : G.GR →* (ℝ ⊗[ℚ] G.C)ˣ where
  toFun g := Units.map (algebraMap ℝ (ℝ ⊗[ℚ] G.C) : ℝ →* ℝ ⊗[ℚ] G.C) (invSqrtAbs (uSimR ℝ g)) *
    (g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1
  map_one' := by simp
  map_mul' g h := by
    ext
    simp only [map_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Subgroup.coe_mul, Prod.fst_mul]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, Algebra.commutes]

theorem normR_val (g : G.GR) : ((normR G g : (ℝ ⊗[ℚ] G.C)ˣ) : ℝ ⊗[ℚ] G.C) =
    algebraMap ℝ (ℝ ⊗[ℚ] G.C) ((invSqrtAbs (uSimR ℝ g) : ℝˣ) : ℝ) * ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C) := rfl

theorem mat_normR_sim (g : G.GR) (v : InfinitePlace G.F) :
    (mat G (normR G g : ℝ ⊗[ℚ] G.C) v)ᴴ * Jm (eps G v) * mat G (normR G g : ℝ ⊗[ℚ] G.C) v =
      (((SignType.sign (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ) : ℝ)) : ℂ) • Jm (eps G v) := by
  set t : ℝ := ((invSqrtAbs (uSimR ℝ g) : ℝˣ) : ℝ)
  set c : ℝˣ := (g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2
  have hY := conjGL_sim (frame G v) (G.gram v) _ _ (psiR_sim G g v)
  rw [frame_spec] at hY
  have hM : mat G (normR G g : ℝ ⊗[ℚ] G.C) v = (t : ℂ) • conjGL (frame G v)
      (G.psiR v ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C)) := by
    rw [normR_val, map_mul, AlgHom.commutes, Pi.mul_apply, mat_apply]
    rw [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hs' : t * t * (c : ℝ) = (SignType.sign (c : ℝ) : ℝ) := invSqrtAbs_sq (uSimR ℝ g)
  have hst : star (t : ℂ) = t := Complex.conj_ofReal t
  rw [hM, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [hY, smul_smul, smul_smul, hst]
  congr 1
  exact_mod_cast hs'

def realPointsToUnitaryGroup : G.GR →* UJpm (eps G) :=
  ((Units.map (mat G).toMonoidHom).comp (normR G)).codRestrict _ fun g =>
    ⟨SignType.sign (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ), by
      rcases lt_or_gt_of_ne (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ).ne_zero) with h | h
      · right; rw [sign_neg h]; rfl
      · left; rw [sign_pos h]; rfl,
     fun v => mat_normR_sim G g v⟩


def PosSim : Prop := ∀ g : G.GR, 0 < (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ)

def toUJ (h : PosSim G) : G.GR →* UJfam (eps G) :=
  ((Units.map (mat G).toMonoidHom).comp (normR G)).codRestrict _ fun g v => by
    have := mat_normR_sim G g v
    rw [sign_pos (h g)] at this
    simpa using this


end Norm

def Aniso : Prop := ∀ x : G.C, (G.star x).unop * x = 0 → x = 0

theorem aniso_of_division (h : ∀ x : G.C, x ≠ 0 → IsUnit x) : Aniso G := by
  intro x hx
  by_contra hne
  obtain ⟨u, rfl⟩ := h x hne
  have h0 : (G.star (u : G.C)).unop = 0 := by
    have := congrArg (· * ((u⁻¹ : G.Cˣ) : G.C)) hx
    simpa [mul_assoc] using this
  apply hne
  rw [← G.star_star (u : G.C), h0]
  simp

section Inhabitant

variable (Kf : Subgroup (Gf G))

abbrev xiTriv : G.GQ →* Matrix (Fin 1) (Fin 1) ℂ := 1

theorem const_mem_invariants :
    (fun _ _ => (1 : ℂ) : Gf G ⧸ Kf → Fin 1 → ℂ) ∈ (funRepY (toF G) Kf (xiTriv G)).invariants := by
  intro γ
  funext y i
  induction y using QuotientGroup.induction_on with
  | H x => rw [funRepY_apply]; simp

instance nontrivial_coh_zero : Nontrivial (coh G Kf (xiTriv G) 0) := by
  haveI : Nontrivial (funRepY (toF G) Kf (xiTriv G)).invariants :=
    ⟨⟨⟨_, const_mem_invariants G Kf⟩, 0, fun h => by
      have := congrFun (congrFun (congrArg Subtype.val h) (QuotientGroup.mk 1)) 0
      simp at this⟩⟩
  exact (groupCohomology.H0Iso _).toLinearEquiv.toEquiv.nontrivial

end Inhabitant

section Examples

open GlobalTheory.LKTrip.Example

example (v : InfinitePlace QI) : eps (ex 1 one_ne_zero) v ⟨0, Nat.one_pos⟩ = true := by
  unfold eps
  have h := eig_Hc 1 v.embedding ⟨0, Nat.one_pos⟩
  change decide (0 < (isHermitian_gramAt (herm_Hc 1) v.embedding).eigenvalues ⟨0, Nat.one_pos⟩) = true
  rw [h]; norm_num

example (v : InfinitePlace QI) : eps (ex (-1) (by norm_num)) v ⟨0, Nat.one_pos⟩ = false := by
  unfold eps
  have h := eig_Hc (-1) v.embedding ⟨0, Nat.one_pos⟩
  change decide (0 < (isHermitian_gramAt (herm_Hc (-1)) v.embedding).eigenvalues ⟨0, Nat.one_pos⟩) = false
  rw [h]; norm_num

example (c : ℚ) (hc : c ≠ 0) : Aniso (ex c hc) := by
  refine aniso_of_division _ fun x hx => ?_
  let y : Matrix (Fin 1) (Fin 1) QI := x
  have h : IsUnit y := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
    refine (Ne.isUnit fun h0 => hx ?_)
    show y = 0
    ext i j
    fin_cases i; fin_cases j
    exact h0
  exact h

example : Nontrivial (coh (ex 1 one_ne_zero) ⊤ (xiTriv _) 0) := inferInstance

example (Kf : Subgroup (Gf (ex 1 one_ne_zero))) :
    piPart (ex 1 one_ne_zero) (Representation.trivial ℂ _ ℂ) Kf (xiTriv _) 0 ≤ ⊤ := le_top

end Examples

end GlobalTheory.HTBetti
end
end
