import Development.EtaleCohomology.WeilConjectures.FermatCount

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et Polynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.CurveCut

section Defs
variable (k : Type) [Field k]

abbrev Kb : Type := AlgebraicClosure (RatFunc k)

abbrev Gal : Type := Kb k ≃ₐ[RatFunc k] Kb k

abbrev OK : Type := integralClosure k[X] (Kb k)

def geo : Subgroup (Gal k) where
  carrier := {g | ∀ x : Kb k, IsAlgebraic k x → g x = x}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x hx := by rw [AlgEquiv.mul_apply, hb x hx, ha x hx]
  inv_mem' {a} ha x hx := a.symm_apply_eq.2 (ha x hx).symm

instance geo_normal : (geo k).Normal := ⟨fun g hg σ x hx => by
  have h : IsAlgebraic k (σ.symm x) := hx.algHom (σ.symm.toAlgHom.restrictScalars k)
  change σ (g (σ.symm x)) = x
  rw [hg _ h, σ.apply_symm_apply]⟩

variable {k}

def Inert (h : k[X]) (g : Gal k) : Prop := ∃ P : Ideal (OK k), P.IsPrime ∧ algebraMap k[X] (OK k) h ∉ P ∧
  ∀ s s' : OK k, (s' : Kb k) = g s → s' - s ∈ P

def ram (h : k[X]) : Subgroup (Gal k) := Subgroup.normalClosure {g | Inert h g}

instance ram_normal (h : k[X]) : (ram h).Normal := Subgroup.normalClosure_normal

def pt {h : k[X]} {k' : Type} [Field k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k') : k' :=
  φ (algebraMap k[X] (Localization.Away h) X)

def gen {h : k[X]} (h0 : h ≠ 0) : Localization.Away h →+* RatFunc k :=
  IsLocalization.Away.lift h (g := algebraMap k[X] (RatFunc k)) (IsUnit.mk0 _ (by simpa using h0))

variable (l : ℕ) [Fact l.Prime] {V : Type 1} [AddCommGroup V] [Module ℚ_[l] V]

def Eig (T : V →ₗ[ℚ_[l]] V) (α : AlgebraicClosure ℚ_[l]) : Prop :=
  Module.End.HasEigenvalue (T.baseChange (AlgebraicClosure ℚ_[l])) α

variable {l}

def Z1 (h : k[X]) (ρ : Representation ℚ_[l] (Gal k) V) : Submodule ℚ_[l] (geo k → V) where
  carrier := {c | (∀ μ : Module.Dual ℚ_[l] V, Continuous fun g => μ (c g)) ∧
    (∀ g g', c (g * g') = c g + ρ g (c g')) ∧ ∀ g, g.1 ∈ ram h → c g = 0}
  zero_mem' := ⟨fun μ => by simpa using continuous_const, by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨fun μ => by simp only [Pi.add_apply, map_add]; exact (ha.1 μ).add (hb.1 μ),
    fun g g' => by simp only [Pi.add_apply, ha.2.1, hb.2.1, map_add]; abel,
    fun g hg => by simp [ha.2.2 g hg, hb.2.2 g hg]⟩
  smul_mem' r a ha := ⟨fun μ => by simpa using ha.1 (r • μ),
    fun g g' => by simp only [Pi.smul_apply, ha.2.1, map_smul, smul_add], fun g hg => by simp [ha.2.2 g hg]⟩

def cj (σ : Gal k) (g : geo k) : geo k := ⟨σ⁻¹ * g * σ, (geo_normal k).conj_mem' _ g.2 σ⟩

theorem cj_mul (σ : Gal k) (g g' : geo k) : cj σ (g * g') = cj σ g * cj σ g' := Subtype.ext (by simp [cj, mul_assoc])

theorem rho_cj (ρ : Representation ℚ_[l] (Gal k) V) (σ : Gal k) (g : geo k) (v : V) :
    ρ σ (ρ (cj σ g) v) = ρ g (ρ σ v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]; simp [cj, mul_assoc]

def actZ (h : k[X]) (ρ : Representation ℚ_[l] (Gal k) V) (σ : Gal k) : Z1 h ρ →ₗ[ℚ_[l]] Z1 h ρ where
  toFun c := ⟨fun g => ρ σ (c.1 (cj σ g)),
    fun μ => (c.2.1 (μ.comp (ρ σ))).comp (Continuous.subtype_mk (by fun_prop) _),
    fun g g' => by beta_reduce; rw [cj_mul, c.2.2.1, map_add, rho_cj],
    fun g hg => by beta_reduce; rw [c.2.2.2 (cj σ g) ((ram_normal h).conj_mem' _ hg σ), map_zero]⟩
  map_add' a b := Subtype.ext (funext fun g => map_add (ρ σ) _ _)
  map_smul' r a := Subtype.ext (funext fun g => map_smul (ρ σ) _ _)

def B1 (h : k[X]) (ρ : Representation ℚ_[l] (Gal k) V) : Submodule ℚ_[l] (Z1 h ρ) where
  carrier := {c | ∃ v, ∀ g, c.1 g = ρ g v - v}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨v + w, fun g => by change a.1 g + b.1 g = _; rw [hv, hw, map_add]; abel⟩
  smul_mem' := by
    rintro r a ⟨v, hv⟩
    exact ⟨r • v, fun g => by change r • a.1 g = _; rw [hv, map_smul, smul_sub]⟩

variable (l) in

def genRep {h : k[X]} (h0 : h ≠ 0) {X : Scheme.{0}} (f : X ⟶ Sp (Localization.Away h)) (n : ℤ) :
    Representation ℚ_[l] (Gal k) (HX l (Kb k) (fibre f (gen h0)) n) := galHQ l (Kb k) (fibre f (gen h0)) n 0

end Defs

end LateralTheory.EWeil.CurveCut

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.ContinCut

universe u v

def Chev : Prop := ∀ (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
  (K : ℕ → Submodule ℤ_[l] M), Antitone K → (∀ x, (∀ k, x ∈ K k) → x = 0) →
  ∀ N : ℕ, ∃ k, ∀ y ∈ K k, ∃ z : M, y = (l : ℤ_[l]) ^ N • z

def AbsCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (ρ : Representation ℤ_[l] G M)
  (K : ℕ → Submodule ℤ_[l] M), Antitone K → (∀ x, (∀ k, x ∈ K k) → x = 0) →
  (∀ (x : M) (k : ℕ), IsOpen {g : G | ρ g x - x ∈ K k}) →
  ∀ (φ : M →ₗ[ℤ_[l]] ℚ_[l]) (x : M), Continuous fun g => φ (ρ g x)

def Stab : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K], (l : K) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp K), IsProper p → ∀ (n : ℤ) (x : Hl l (sch.obj (geom (AlgebraicClosure K) p)) n 0)
    (k : ℕ), IsOpen {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
      (galHl l (AlgebraicClosure K) p n 0 σ x).1 k = x.1 k}

def evk (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) : Hl l E n i →ₗ[ℤ_[l]] HtL l k E n i :=
  (LinearMap.proj (R := ℤ_[l]) (φ := fun k => HtL l k E n i) k).comp (HlSub l E n i).subtype

theorem evk_apply (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) (x : Hl l E n i) : evk l E n i k x = x.1 k := rfl

theorem evk_anti (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) : Antitone fun k => LinearMap.ker (evk l E n i k) := by
  intro a b hab x hx
  simp only [LinearMap.mem_ker, evk_apply] at hx ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact hx
  | succ d ih =>
    apply ih (Nat.le_add_right _ _)
    have h2 : red (l ^ (a + d + 1)) (l ^ (a + d)) E n i (x.1 (a + d + 1)) = x.1 (a + d) := x.2 (a + d)
    have h3 : (x.1 (a + d + 1) : Ht (l ^ (a + d + 1)) E n i) = 0 := hx
    rw [← h2, h3]; exact map_zero (red (l ^ (a + d + 1)) (l ^ (a + d)) E n i)

end LateralTheory.EWeil.ContinCut
end
end
