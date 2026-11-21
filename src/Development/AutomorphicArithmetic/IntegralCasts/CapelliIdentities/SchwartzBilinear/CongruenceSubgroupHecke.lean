import Mathlib

namespace UpperTheory.Reformulated.B.P6.CongruenceSubgroupHecke

open scoped DivisionSemiring Semifield Field AddCommGroup DivInvMonoid Group Set DFunLike RingHom Semiring LinearMap MonoidHom MulOneClass Monoid MulZeroOneClass Module.End Membership SetLike Subgroup Units Subtype HSMul SMulZeroClass AddZero AddZeroClass AddMonoid SubNegMonoid AddGroup DistribSMul DistribMulAction Module HAdd AddCommMonoid OfNat Zero Submodule AddSubmonoid AddSubsemigroup One Ring CommRing NonAssocRing NonAssocCommRing Subring DivisionRing NonAssocSemiring Valuation ValuativeRel CommSemiring Classical Ideal Singleton HPow SubmonoidClass Matrix Fin Matrix.GeneralLinearGroup Algebra SubsemiringClass HasQuotient Ideal.Quotient Complex MulZeroClass Pi EquivLike MulEquiv ZPow LE PartialOrder ConditionallyCompletePartialOrderSup ConditionallyCompletePartialOrder ConditionallyCompleteLattice ConditionallyCompleteLinearOrder Int HMul

noncomputable def GlobalTheory.PRep.IsSmooth :
    {k G V : Type} → [inst_h0 : Field k] → [inst_h1 : Group G] → [inst_h2 : AddCommGroup V] → [inst_h3 : _root_.Module k V] → [inst_h4 : TopologicalSpace G] → Representation k G V → Prop :=
  fun {k G V : Type} {inst_f0 : Field k} {inst_f1 : Group G} {inst_f2 : AddCommGroup V} {inst_f3 : _root_.Module k V} {inst_f4 : TopologicalSpace G} (ρ : Representation k G V) ↦ ∀ (v : V), IsOpen (X := G) {g : G | DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h5 : V) ↦ V) (DFunLike.coe (β := fun (x_h6 : G) ↦ V →ₗ[k] V) ρ g : V →ₗ[k] V) v = v}

theorem GlobalTheory.PRep.eig_obl_1 :
    ∀ {k G V : Type} [inst_h0 : Field k] [inst_h1 : Group G] [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V}, Membership.mem (γ := Set V) {v : V | ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h4 : V) ↦ V) (DFunLike.coe (β := fun (x_h5 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) v = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h6 : ↥H) ↦ kˣ) χ h)) v} a → Membership.mem (γ := Set V) {v : V | ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h7 : V) ↦ V) (DFunLike.coe (β := fun (x_h8 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) v = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h9 : ↥H) ↦ kˣ) χ h)) v} b → ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h10 : V) ↦ V) (DFunLike.coe (β := fun (x_h11 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) (a + b) = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h12 : ↥H) ↦ kˣ) χ h)) (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  simp only [Set.mem_setOf_eq] at ha hb
  rw [map_add, ha h, hb h, smul_add]

theorem GlobalTheory.PRep.eig_obl_2 :
    ∀ {k G V : Type} [inst_h0 : Field k] [inst_h1 : Group G] [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h4 : V) ↦ V) (DFunLike.coe (β := fun (x_h5 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) (OfNat.ofNat (nat_lit 0)) = HSMul.hSMul (α := k) (β := V) (Units.val (DFunLike.coe (β := fun (x_h6 : ↥H) ↦ kˣ) χ h)) (OfNat.ofNat (nat_lit 0)) := by
  intro k G V _ _ _ _ ρ H χ h
  simp

theorem GlobalTheory.PRep.eig_obl_3 :
    ∀ {k G V : Type} [inst_h0 : Field k] [inst_h1 : Group G] [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V}, Membership.mem (γ := Set V) {v : V | ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h4 : V) ↦ V) (DFunLike.coe (β := fun (x_h5 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) v = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h6 : ↥H) ↦ kˣ) χ h)) v} v → ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h7 : V) ↦ V) (DFunLike.coe (β := fun (x_h8 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) (c • v) = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h9 : ↥H) ↦ kˣ) χ h)) (c • v) := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  simp only [Set.mem_setOf_eq] at hv
  rw [map_smul, hv h, smul_comm]

noncomputable def GlobalTheory.PRep.eig :
    {k G V : Type} → [inst_h0 : Field k] → [inst_h1 : Group G] → [inst_h2 : AddCommGroup V] → [inst_h3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
  fun {k G V : Type} {inst_h0 : Field k} {inst_h1 : Group G} {inst_h2 : AddCommGroup V} {inst_h3 : _root_.Module k V} (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦ { carrier := {v : V | ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h4 : V) ↦ V) (DFunLike.coe (β := fun (x_h5 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) v = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h6 : ↥H) ↦ kˣ) χ h)) v}, add_mem' := @GlobalTheory.PRep.eig_obl_1 k G V inst_h0 inst_h1 inst_h2 inst_h3 ρ H χ, zero_mem' := GlobalTheory.PRep.eig_obl_2 ρ H χ, smul_mem' := GlobalTheory.PRep.eig_obl_3 ρ H χ }

noncomputable def GlobalTheory.PRep.fixed :
    {k G V : Type} → [inst_h0 : Field k] → [inst_h1 : Group G] → [inst_h2 : AddCommGroup V] → [inst_h3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
  fun {k G V : Type} {inst_f5 : Field k} {inst_f6 : Group G} {inst_f7 : AddCommGroup V} {inst_f8 : _root_.Module k V} (ρ : Representation k G V) (H : Subgroup G) ↦ GlobalTheory.PRep.eig ρ H (OfNat.ofNat (nat_lit 1))

theorem Zls.unif_obl_1 :
    ∀ (k : Type) [inst_h0 : Field k] [inst_h1 : ValuativeRel k] [inst_h2 : TopologicalSpace k] [inst_h3 : IsNonarchimedeanLocalField k], ∃ (ϖ : ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))), Irreducible ϖ := by
  intro k _ _ _ _
  exact IsDiscreteValuationRing.exists_irreducible _

noncomputable def Zls.unif :
    (k : Type) → [inst_h0 : Field k] → [inst_h1 : ValuativeRel k] → [inst_h2 : TopologicalSpace k] → [inst_h3 : IsNonarchimedeanLocalField k] → ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)) :=
  fun (k : Type) {inst_f9 : Field k} {inst_f10 : ValuativeRel k} {inst_f11 : TopologicalSpace k} {inst_f12 : IsNonarchimedeanLocalField k} ↦ Classical.choose (p := Irreducible) (Zls.unif_obl_1 k)

noncomputable def Zls.Km :
    (k : Type) → [inst_h0 : Field k] → [inst_h1 : ValuativeRel k] → [inst_h2 : TopologicalSpace k] → [inst_h3 : IsNonarchimedeanLocalField k] → (N : ℕ) → ℕ → Subgroup (GL (Fin N) k) :=
  fun (k : Type) {inst_f13 : Field k} {inst_f14 : ValuativeRel k} {inst_f15 : TopologicalSpace k} {inst_f16 : IsNonarchimedeanLocalField k} (N m : ℕ) ↦ Subgroup.map (G := GL (Fin N) ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) (Matrix.GeneralLinearGroup.map (Algebra.algebraMap (↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) k)) (MonoidHom.ker (M := GL (Fin N) (HasQuotient.Quotient ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)) (B := Ideal ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) (Ideal.span {HPow.hPow (α := ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) (Zls.unif k) m}))) (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {HPow.hPow (α := ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) (Zls.unif k) m}))))

theorem Zls.unifU_obl_2 :
    ∀ (k : Type) [inst_h0 : Field k] [inst_h1 : ValuativeRel k] [inst_h2 : TopologicalSpace k] [inst_h3 : IsNonarchimedeanLocalField k], Ne (α := k) (DFunLike.coe (F := ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)) →+* k) (β := fun (x_h4 : ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) ↦ k) (Algebra.algebraMap (↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) k) (Zls.unif k) : k) (OfNat.ofNat (nat_lit 0) : k) := by
  intro k _ _ _ _ h
  apply (Classical.choose_spec (Zls.unif_obl_1 k)).ne_zero
  exact Subtype.ext h

noncomputable def Zls.unifU :
    (k : Type) → [inst_h0 : Field k] → [inst_h1 : ValuativeRel k] → [inst_h2 : TopologicalSpace k] → [inst_h3 : IsNonarchimedeanLocalField k] → kˣ :=
  fun (k : Type) {inst_f23 : Field k} {inst_f24 : ValuativeRel k} {inst_f25 : TopologicalSpace k} {inst_f26 : IsNonarchimedeanLocalField k} ↦ Units.mk0 (DFunLike.coe (F := ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)) →+* k) (β := fun (x_h4 : ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) ↦ k) (Algebra.algebraMap (↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))) k) (Zls.unif k)) (Zls.unifU_obl_2 k)

end UpperTheory.Reformulated.B.P6.CongruenceSubgroupHecke
