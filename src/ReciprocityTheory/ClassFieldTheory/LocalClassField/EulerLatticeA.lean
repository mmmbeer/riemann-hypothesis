import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Euler

open _root_.Neutral.B1

noncomputable section

section Q

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

def qEd (p d : ℕ) (rho : Representation R G M) : ℚ :=
  ((Nat.card (H0 rho) : ℚ) * (Nat.card (H2 rho) : ℚ) * (p : ℚ) ^ (d * padicValNat p (Nat.card M))) /
    (Nat.card (H1 rho) : ℚ)

def fnRep (rho : Representation R G M) (U : Subgroup G) : Representation R G (G ⧸ U → M) where
  toFun g :=
    { toFun := fun F x => rho g (F (g⁻¹ • x))
      map_add' := fun F F' => funext fun x => map_add (rho g) _ _
      map_smul' := fun c F => funext fun x => map_smul (rho g) _ _ }
  map_one' := LinearMap.ext fun F => funext fun x => by
    show rho 1 (F ((1 : G)⁻¹ • x)) = F x
    rw [inv_one, one_smul, map_one]; rfl
  map_mul' g h := LinearMap.ext fun F => funext fun x => by
    show rho (g * h) (F ((g * h)⁻¹ • x)) = rho g (rho h (F (h⁻¹ • g⁻¹ • x)))
    rw [mul_inv_rev, mul_smul, map_mul]; rfl

def intRep (rho : Representation R G M) : Representation ℤ G M where
  toFun g := (rho g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun m => by
    show rho 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show rho (g * h) m = rho g (rho h m)
    rw [map_mul]; rfl

end Q

section ZG

variable (G : Type) [Group G]

abbrev ZG : Type := MonoidAlgebra ℤ G

variable {G} (l : ℕ) (D A : Type) [AddCommGroup D] [Module (ZG G) D] [AddCommGroup A] [Module (ZG G) A]

def mulL : A →ₗ[ZG G] A := l • LinearMap.id

variable (G) in

def fixG : Type := {d : D // ∀ g : G, MonoidAlgebra.of ℤ G g • d = d}

end ZG

section Hom

variable (N : Type) [Group N] [TopologicalSpace N] (M : Type) [AddCommGroup M] [TopologicalSpace M]
  [IsTopologicalAddGroup M]

def homSub : AddSubgroup (N → M) where
  carrier := {f | Continuous f ∧ ∀ a b, f (a * b) = f a + f b}
  zero_mem' := ⟨continuous_const, fun _ _ => (add_zero (0 : M)).symm⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun a b => by
    show f (a * b) + f' (a * b) = f a + f' a + (f b + f' b)
    rw [hf.2, hf'.2]; abel⟩
  neg_mem' := fun {f} hf => ⟨hf.1.neg, fun a b => by
    show - f (a * b) = - f a + - f b
    rw [hf.2]; abel⟩

end Hom

section OL

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def OLadd : AddSubgroup (PadicAlgCl p) where
  carrier := {x | x ∈ L ∧ ‖x‖ ≤ 1}
  zero_mem' := ⟨L.zero_mem, by simp⟩
  add_mem' := fun {x y} hx hy => ⟨L.add_mem hx.1 hy.1,
    (PadicAlgCl.isNonarchimedean p x y).trans (max_le hx.2 hy.2)⟩
  neg_mem' := fun {x} hx => ⟨L.neg_mem hx.1, by rw [norm_neg]; exact hx.2⟩

variable {p K L}

def integerRingGaloisAction (hKL : K ≤ L) [hN : (subG p K L).Normal] : Representation ℤ (GK p K) (OLadd p L) where
  toFun σ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => ⟨σ x.1, (subG_normal_iff hKL).1 hN σ x.1 x.2.1, by rw [norm_map_GK]; exact x.2.2⟩
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }
  map_one' := rfl
  map_mul' _ _ := rfl

end OL

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Euler
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Euler

open _root_.Neutral.B1 Function

noncomputable section

section aux

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def OLaddEquiv : OLadd p K ≃+ OK p K where
  toFun x := ⟨⟨x.1, x.2.1⟩, (mem_OK_iff p K _).2 x.2.2⟩
  invFun y := ⟨y.1.1, y.1.2, (mem_OK_iff p K _).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem map_range_OLaddEquiv (z : ℤ) :
    (zmultiplesHom (OLadd p K →+ OLadd p K) (AddMonoidHom.id _) z).range.map (OLaddEquiv p K : OLadd p K →+ OK p K) =
      (Ideal.span {(z : OK p K)}).toAddSubgroup := by
  ext y
  rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨OLaddEquiv p K x, ?_⟩
    have : (zmultiplesHom (OLadd p K →+ OLadd p K) (AddMonoidHom.id _) z) x = z • x := rfl
    rw [this]
    show _ = OLaddEquiv p K (z • x)
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨(OLaddEquiv p K).symm a, rfl⟩, ?_⟩
    have : (zmultiplesHom (OLadd p K →+ OLadd p K) (AddMonoidHom.id _) z) ((OLaddEquiv p K).symm a) =
      z • (OLaddEquiv p K).symm a := rfl
    rw [this]
    show OLaddEquiv p K (z • (OLaddEquiv p K).symm a) = _
    rw [map_zsmul, zsmul_eq_mul, mul_comm, AddEquiv.apply_symm_apply]

def quotOLaddEquiv (z : ℤ) :
    (OLadd p K ⧸ (zmultiplesHom (OLadd p K →+ OLadd p K) (AddMonoidHom.id _) z).range) ≃
      (OK p K ⧸ Ideal.span {(z : OK p K)}) :=
  (QuotientAddGroup.congr _ _ (OLaddEquiv p K) (map_range_OLaddEquiv p K z)).toEquiv

attribute [local instance] zpAlgOK

theorem card_OK_quot_natCast (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : n ≠ 0) :
    Nat.card (OK p K ⧸ Ideal.span {(n : OK p K)}) = (p ^ padicValNat p n) ^ Module.finrank ℚ_[p] K := by
  have := isScalarTower_zp_OK p K
  have := isIntegralClosure_OK p K
  have := isTorsionFree_zp_K p K
  have : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  have : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  have hr := IsIntegralClosure.rank ℤ_[p] ℚ_[p] K (OK p K)
  have hn' : (n : OK p K) = algebraMap ℤ_[p] (OK p K) (n : ℕ) := (map_natCast _ _).symm
  rw [hn', ReciprocityTheory.Neutral.Cmp.card_quot_span_algebraMap (Module.finBasis ℤ_[p] (OK p K)),
    ReciprocityTheory.Neutral.Cmp.card_quot_natCast_padicInt p hn, Fintype.card_fin, hr]

end aux

attribute [local instance] zpAlgOK

variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Euler
end
