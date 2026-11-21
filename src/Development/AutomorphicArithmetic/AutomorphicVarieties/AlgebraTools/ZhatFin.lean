import Mathlib

section
noncomputable section

namespace UpperTheory.V.AlgebraTools

structure Cx (A : Type) [CommRing A] where
  X : ℕ → Type
  [grp : ∀ n, AddCommGroup (X n)]
  [mod : ∀ n, Module A (X n)]
  d : ∀ n, X n →ₗ[A] X (n + 1)
  dd : ∀ n x, d (n + 1) (d n x) = 0

attribute [instance] Cx.grp Cx.mod

namespace Cx

variable {A : Type} [CommRing A]

def Z (K : Cx A) (n : ℕ) : Submodule A (K.X n) := LinearMap.ker (K.d n)

def B (K : Cx A) : ∀ n : ℕ, Submodule A (K.X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (K.d n)


abbrev H (K : Cx A) (n : ℕ) : Type := K.Z n ⧸ (K.B n).comap (K.Z n).subtype

abbrev cls (K : Cx A) {n : ℕ} (z : K.Z n) : K.H n := Submodule.Quotient.mk z

structure Hom (K L : Cx A) where
  f : ∀ n, K.X n →ₗ[A] L.X n
  comm : ∀ n x, f (n + 1) (K.d n x) = L.d n (f n x)

namespace Hom

variable {K L N : Cx A}

def id (K : Cx A) : Hom K K where
  f _ := LinearMap.id
  comm _ _ := rfl

def comp (ψ : Hom L N) (φ : Hom K L) : Hom K N where
  f n := ψ.f n ∘ₗ φ.f n
  comm n x := (congrArg (ψ.f (n + 1)) (φ.comm n x)).trans (ψ.comm n _)

def smul (a : A) (φ : Hom K L) : Hom K L where
  f n := a • φ.f n
  comm n x := by rw [LinearMap.smul_apply, LinearMap.smul_apply, φ.comm, map_smul]

def sub (φ ψ : Hom K L) : Hom K L where
  f n := φ.f n - ψ.f n
  comm n x := by rw [LinearMap.sub_apply, LinearMap.sub_apply, φ.comm, ψ.comm, map_sub]

def Z (φ : Hom K L) (n : ℕ) : K.Z n →ₗ[A] L.Z n :=
  (φ.f n).restrict fun x hx => by
    have h0 : K.d n x = 0 := hx
    exact (φ.comm n x).symm.trans (by rw [h0, map_zero])

theorem map_B (φ : Hom K L) (n : ℕ) : ∀ x ∈ K.B n, φ.f n x ∈ L.B n := by
  rcases n with _ | n
  · intro x hx
    rw [(Submodule.mem_bot A).1 hx, map_zero]
    exact zero_mem _
  · rintro _ ⟨y, rfl⟩
    exact ⟨φ.f n y, (φ.comm n y).symm⟩

def H (φ : Hom K L) (n : ℕ) : K.H n →ₗ[A] L.H n :=
  Submodule.mapQ _ _ (φ.Z n) fun z hz => φ.map_B n z.1 hz

end Hom

def prod (K L : Cx A) : Cx A where
  X n := K.X n × L.X n
  d n := (K.d n).prodMap (L.d n)
  dd n x := Prod.ext (K.dd n x.1) (L.dd n x.2)

def pi {ι : Type} (K : ι → Cx A) : Cx A where
  X n := ∀ i, (K i).X n
  d n := LinearMap.pi fun i => (K i).d n ∘ₗ LinearMap.proj i
  dd n x := funext fun i => (K i).dd n (x i)

def up (L : Cx A) : ℕ → Type
  | 0 => PUnit
  | n + 1 => L.X n

instance upGrp (L : Cx A) : ∀ n, AddCommGroup (L.up n)
  | 0 => inferInstanceAs (AddCommGroup PUnit)
  | n + 1 => L.grp n

instance upMod (L : Cx A) : ∀ n, Module A (L.up n)
  | 0 => inferInstanceAs (Module A PUnit)
  | n + 1 => L.mod n

def upD (L : Cx A) : ∀ n, L.up n →ₗ[A] L.X n
  | 0 => 0
  | n + 1 => L.d n

theorem d_upD (L : Cx A) (n : ℕ) (y : L.up n) : L.d n (L.upD n y) = 0 := by
  rcases n with _ | n
  · exact map_zero _
  · exact L.dd n y

variable {K L N : Cx A}

def fib (φ : Hom K L) : Cx A where
  X n := K.X n × L.up n
  d n := (K.d n ∘ₗ LinearMap.fst A _ _).prod
    (show K.X n × L.up n →ₗ[A] L.X n from φ.f n ∘ₗ LinearMap.fst A _ _ - L.upD n ∘ₗ LinearMap.snd A _ _)
  dd n x := Prod.ext (K.dd n x.1) <| by
    change φ.f (n + 1) (K.d n x.1) - L.d n (φ.f n x.1 - L.upD n x.2) = 0
    rw [map_sub, L.d_upD, φ.comm, sub_zero, sub_self]

theorem fib_d (φ : Hom K L) (n : ℕ) (x : K.X n) (y : L.up n) :
    (fib φ).d n (x, y) = (K.d n x, show L.X n from φ.f n x - L.upD n y) := rfl

def fibFst (φ : Hom K L) : Hom (fib φ) K where
  f _ := LinearMap.fst A _ _
  comm _ _ := rfl

def upMap {L L' : Cx A} (β : Hom L L') : ∀ n, L.up n →ₗ[A] L'.up n
  | 0 => 0
  | n + 1 => β.f n

theorem upD_upMap {L L' : Cx A} (β : Hom L L') (n : ℕ) (y : L.up n) :
    L'.upD n (upMap β n y) = β.f n (L.upD n y) := by
  rcases n with _ | n
  · exact (map_zero _).symm
  · exact (β.comm n y).symm

def fibMap {K L K' L' : Cx A} {φ : Hom K L} {φ' : Hom K' L'} (α : Hom K K') (β : Hom L L')
    (h : ∀ n x, φ'.f n (α.f n x) = β.f n (φ.f n x)) : Hom (fib φ) (fib φ') where
  f n := (α.f n).prodMap (upMap β n)
  comm n x := Prod.ext (α.comm n x.1) <| by
    change β.f n (φ.f n x.1 - L.upD n x.2) = φ'.f n (α.f n x.1) - L'.upD n (upMap β n x.2)
    rw [h, upD_upMap, map_sub]

def fibIn (φ : Hom K L) (n : ℕ) : L.Z n →ₗ[A] (fib φ).H (n + 1) :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict ((fib φ).Z (n + 1))
    (LinearMap.inr A (K.X (n + 1)) (L.X n) ∘ₗ (L.Z n).subtype) fun y =>
      Prod.ext (map_zero (K.d (n + 1))) <| by
        have hy : L.d n y.1 = 0 := y.2
        change φ.f (n + 1) 0 - L.d n y.1 = 0
        rw [hy, map_zero, sub_zero]

structure SES (i : Hom K L) (p : Hom L N) : Prop where
  inj : ∀ n, Function.Injective (i.f n)
  ex : ∀ n, Function.Exact (i.f n) (p.f n)
  surj : ∀ n, Function.Surjective (p.f n)

def single (M : Type) [AddCommGroup M] [Module A M] : Cx A where
  X n := match n with | 0 => M | _ + 1 => PUnit
  grp n := match n with | 0 => ‹AddCommGroup M› | _ + 1 => inferInstanceAs (AddCommGroup PUnit)
  mod n := match n with | 0 => ‹Module A M› | _ + 1 => (inferInstance : Module A PUnit)
  d _ := 0
  dd _ _ := rfl

instance instInhabited : Inhabited (Cx A) := ⟨single PUnit⟩

end Cx

section Cochains

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

def dInh (ρ : Representation A G M) (n : ℕ) : ((Fin n → G) → M) →ₗ[A] ((Fin (n + 1) → G) → M) :=
  (inhomogeneousCochains.d (k := A) (G := G) (Rep.of ρ) n).hom

theorem dInh_apply (ρ : Representation A G M) (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → G) :
    dInh ρ n f g = ρ (g 0) (f fun i => g i.succ) +
      ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := rfl

theorem dInh_dInh (ρ : Representation A G M) (n : ℕ) (f : (Fin n → G) → M) :
    dInh ρ (n + 1) (dInh ρ n f) = 0 :=
  LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (groupCohomology.inhomogeneousCochains.d_comp_d (A := Rep.of ρ) (n := n))) f

variable [TopologicalSpace G] [TopologicalSpace M]

def ContAct (ρ : Representation A G M) : Prop := Continuous fun q : G × M => ρ q.1 q.2

theorem continuous_contractNth {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
    (j : Fin (n + 1)) : Continuous fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g :=
  continuous_pi fun k => by
    unfold Fin.contractNth
    split_ifs <;> fun_prop

variable [IsTopologicalAddGroup M] [ContinuousConstSMul A M]

variable (A G M) in
omit [Group G] in

def contC (n : ℕ) : Submodule A ((Fin n → G) → M) where
  carrier := {f | Continuous f}
  add_mem' hf hg := Continuous.add hf hg
  zero_mem' := continuous_const
  smul_mem' a _ hf := Continuous.const_smul hf a

theorem continuous_dInh [IsTopologicalGroup G] {ρ : Representation A G M} (hρ : ContAct ρ) (n : ℕ)
    {f : (Fin n → G) → M} (hf : Continuous f) : Continuous (dInh ρ n f) := by
  have h1 : Continuous fun g : Fin (n + 1) → G => ρ (g 0) (f fun i => g i.succ) :=
    Continuous.comp (f := fun g : Fin (n + 1) → G => (g 0, f fun i => g i.succ)) hρ (by fun_prop)
  exact h1.add (continuous_finset_sum _ fun j _ => (hf.comp (continuous_contractNth j)).const_smul _)

def contCx [IsTopologicalGroup G] (ρ : Representation A G M) (hρ : ContAct ρ) : Cx A where
  X n := contC A G M n
  d n := (dInh ρ n).restrict fun _ hf => continuous_dInh hρ n hf
  dd n f := Subtype.ext (dInh_dInh ρ n f.1)

def contMap {G' M' : Type} [Group G'] [AddCommGroup M'] [Module A M'] [TopologicalSpace G']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul A M']
    [IsTopologicalGroup G] [IsTopologicalGroup G'] {ρ : Representation A G M} (hρ : ContAct ρ)
    {ρ' : Representation A G' M'} (hρ' : ContAct ρ') (φ : G' →* G) (hφ : Continuous φ)
    (u : M →ₗ[A] M') (hu : Continuous u) (h : ∀ g m, u (ρ (φ g) m) = ρ' g (u m)) :
    Cx.Hom (contCx ρ hρ) (contCx ρ' hρ') where
  f n :=
    { toFun := fun f => ⟨fun g => u (f.1 fun i => φ (g i)),
        hu.comp (Continuous.comp f.2 (continuous_pi fun i => hφ.comp (continuous_apply i)))⟩
      map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add u _ _)
      map_smul' := fun _ _ => Subtype.ext (funext fun _ => map_smul u _ _) }
  comm n f := Subtype.ext <| funext fun g => by
    have hc : ∀ j : Fin (n + 1), Fin.contractNth j (· * ·) (fun i => φ (g i)) =
        fun i => φ (Fin.contractNth j (· * ·) g i) := fun j =>
      (Fin.comp_contractNth (· * ·) (· * ·) (map_mul φ) j g).symm
    change u (dInh ρ n f.1 fun i => φ (g i)) = dInh ρ' n (fun g => u (f.1 fun i => φ (g i))) g
    simp only [dInh_apply, map_add, map_sum, map_smul, h, hc]

def crossed (ρ : Representation A G M) : Submodule A (G → M) where
  carrier := {z | Continuous z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)}
  add_mem' := fun ⟨c, e⟩ ⟨c', e'⟩ => ⟨c.add c', fun g h => by
    simp only [Pi.add_apply, e, e', map_add]; abel⟩
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := fun a _ ⟨c, e⟩ => ⟨c.const_smul a, fun g h => by
    simp only [Pi.smul_apply, e, map_smul, smul_add]⟩

end Cochains

end UpperTheory.V.AlgebraTools

end
end

section
noncomputable section

namespace UpperTheory.V.AlgebraTools.Cx

variable {A : Type} [CommRing A]

structure Sel (A : Type) [CommRing A] (ι : Type) : Type 1 where
  G : Cx A
  L : ι → Cx A
  P : ι → Cx A
  res : ∀ i, Hom G (L i)
  inc : ∀ i, Hom (P i) (L i)

namespace Sel

variable {ι : Type} (S : Sel A ι)

def dif : Hom (prod S.G (pi S.P)) (pi S.L) where
  f n := LinearMap.pi fun i => ((S.res i).f n).comp (LinearMap.fst A (S.G.X n) (∀ i, (S.P i).X n)) -
    ((S.inc i).f n).comp ((LinearMap.proj i).comp (LinearMap.snd A (S.G.X n) (∀ i, (S.P i).X n)))
  comm n x := funext fun i => by
    show (S.res i).f (n + 1) (S.G.d n x.1) - (S.inc i).f (n + 1) ((S.P i).d n (x.2 i)) =
      (S.L i).d n ((S.res i).f n x.1 - (S.inc i).f n (x.2 i))
    rw [map_sub, Hom.comm, Hom.comm]

def cx : Cx A := fib S.dif

def grp (n : ℕ) : Submodule A (S.G.H n) :=
  ⨅ i, (LinearMap.range ((S.inc i).H n)).comap ((S.res i).H n)

structure Map (S T : Sel A ι) where
  g : Hom S.G T.G
  l : ∀ i, Hom (S.L i) (T.L i)
  p : ∀ i, Hom (S.P i) (T.P i)
  res : ∀ i n x, (T.res i).f n (g.f n x) = (l i).f n ((S.res i).f n x)
  inc : ∀ i n x, (T.inc i).f n ((p i).f n x) = (l i).f n ((S.inc i).f n x)

end Sel

def Hom.prodMap {K L K' L' : Cx A} (φ : Hom K K') (ψ : Hom L L') : Hom (prod K L) (prod K' L') :=
  ⟨fun n => (φ.f n).prodMap (ψ.f n), fun n x => Prod.ext (φ.comm n x.1) (ψ.comm n x.2)⟩

def Hom.piMap {ι : Type} {K L : ι → Cx A} (φ : ∀ i, Hom (K i) (L i)) : Hom (pi K) (pi L) :=
  ⟨fun n => LinearMap.pi fun i => ((φ i).f n).comp (LinearMap.proj i), fun n x => funext fun i => (φ i).comm n (x i)⟩

def Sel.Map.cx {ι : Type} {S T : Sel A ι} (m : Sel.Map S T) : Hom S.cx T.cx :=
  fibMap (m.g.prodMap (Hom.piMap m.p)) (Hom.piMap m.l) fun n x => funext fun i => by
    show (T.res i).f n (m.g.f n x.1) - (T.inc i).f n ((m.p i).f n (x.2 i)) =
      (m.l i).f n ((S.res i).f n x.1 - (S.inc i).f n (x.2 i))
    rw [map_sub, m.res, m.inc]

def Sel.Map.mul {ι : Type} (S : Sel A ι) (a : A) : Sel.Map S S where
  g := (Hom.id _).smul a
  l _ := (Hom.id _).smul a
  p _ := (Hom.id _).smul a
  res _ _ _ := map_smul _ _ _
  inc _ _ _ := map_smul _ _ _

section Two

variable (P Q : Type) [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

def twoX : ℕ → Type
  | 0 => P
  | 1 => Q
  | _ + 2 => PUnit

instance twoGrp : ∀ n, AddCommGroup (twoX P Q n)
  | 0 => inferInstanceAs (AddCommGroup P)
  | 1 => inferInstanceAs (AddCommGroup Q)
  | _ + 2 => inferInstanceAs (AddCommGroup PUnit)

instance twoMod : ∀ n, Module A (twoX P Q n)
  | 0 => inferInstanceAs (Module A P)
  | 1 => inferInstanceAs (Module A Q)
  | _ + 2 => inferInstanceAs (Module A PUnit)

variable {P Q}

def twoD (f : P →ₗ[A] Q) : ∀ n, twoX P Q n →ₗ[A] twoX P Q (n + 1)
  | 0 => f
  | _ + 1 => 0

def two (f : P →ₗ[A] Q) : Cx A where
  X := twoX P Q
  d := twoD f
  dd _ _ := rfl

def Hom.ofTwo (f : P →ₗ[A] Q) (L : Cx A) (u : P →ₗ[A] L.X 0) (v : Q →ₗ[A] L.X 1) (h : ∀ x, v (f x) = L.d 0 (u x))
    (h' : ∀ y, L.d 1 (v y) = 0) : Hom (two f) L where
  f
    | 0 => u
    | 1 => v
    | _ + 2 => 0
  comm
    | 0, x => h x
    | 1, y => (h' y).symm
    | _ + 2, _ => (map_zero _).symm

end Two

def chi (K : Cx A) (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, (-1) ^ n * ((Module.length A (K.H n)).toNat : ℤ)

instance (ι : Type) : Inhabited (Sel A ι) :=
  ⟨⟨default, fun _ => default, fun _ => default, fun _ => Hom.id _, fun _ => Hom.id _⟩⟩

end UpperTheory.V.AlgebraTools.Cx

end
end

section
open UpperTheory.V.AlgebraTools UpperTheory.V.AlgebraTools.Cx

theorem UpperTheory.V.AlgebraTools.zhatFin :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Type) [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul A M] (ρ : Representation A G M) [CompactSpace G] [Finite M] [DiscreteTopology M] (I : Subgroup G) [I.Normal] (φ : G), ContAct ρ →
      Dense ((I ⊔ Subgroup.zpowers φ : Subgroup G) : Set G) →
      (∀ k : ℕ, 0 < k → ∃ χ : G →* Multiplicative (ZMod k), IsOpen (χ.ker : Set G) ∧ I ≤ χ.ker ∧ χ φ = Multiplicative.ofAdd 1) →
      ∀ m, (∀ u ∈ I, ρ u m = m) → ∃! z : crossed ρ, (∀ u ∈ I, z.1 u = 0) ∧ z.1 φ = m := by
  intro A _ G _ _ _ M _ _ _ _ _ ρ _ _ _ I hI φ hρ hd hχ m hm
  have hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by rw [map_mul]; rfl
  have hinv : ∀ g x, ρ g⁻¹ (ρ g x) = x := fun g x => by rw [← hmul, inv_mul_cancel, map_one]; rfl
  have hinv' : ∀ g x, ρ g (ρ g⁻¹ x) = x := fun g x => by rw [← hmul, mul_inv_cancel, map_one]; rfl
  have hall : ∀ S : Subgroup G, IsClosed (S : Set G) → I ≤ S → φ ∈ S → ∀ g, g ∈ S := by
    intro S hS h1 h2 g
    have h3 : I ⊔ Subgroup.zpowers φ ≤ S := sup_le h1 ((Subgroup.zpowers_le).2 h2)
    exact hS.closure_subset_iff.2 (show ((I ⊔ Subgroup.zpowers φ : Subgroup G) : Set G) ⊆ S from h3) (hd g)
  apply existsUnique_of_exists_of_unique
  · let T : Equiv.Perm M :=
      { toFun := fun x => m + ρ φ x
        invFun := fun x => ρ φ⁻¹ (x - m)
        left_inv := fun x => by simp only [add_sub_cancel_left, hinv]
        right_inv := fun x => by simp only [hinv', add_sub_cancel] }
    have hT : ∀ x, T x = m + ρ φ x := fun _ => rfl
    have hk : 0 < orderOf T := orderOf_pos T
    obtain ⟨χ, hχo, hχI, hχφ⟩ := hχ (orderOf T) hk
    haveI : NeZero (orderOf T) := ⟨hk.ne'⟩
    let Θ : G → Equiv.Perm M := fun g => T ^ (Multiplicative.toAdd (χ g)).val
    have hΘmul : ∀ g h x, Θ (g * h) x = Θ g (Θ h x) := fun g h x => by
      have : Θ (g * h) = Θ g * Θ h := by
        simp only [Θ, map_mul, toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add]
      rw [this]; rfl
    have hΘI : ∀ u ∈ I, ∀ x, Θ u x = x := fun u hu x => by
      have : χ u = 1 := hχI hu
      simp [Θ, this]
    have hΘφ : ∀ x, Θ φ x = m + ρ φ x := fun x => by
      have : Θ φ = T := by
        have e : (1 : ZMod (orderOf T)) = ((1 : ℕ) : ZMod (orderOf T)) := Nat.cast_one.symm
        simp only [Θ, hχφ, toAdd_ofAdd]
        rw [e, ZMod.val_natCast, pow_mod_orderOf, pow_one]
      rw [this, hT]
    have hlc : IsLocallyConstant χ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have ho : IsOpen {h : G | g⁻¹ * h ∈ χ.ker} := hχo.preimage (continuous_const.mul continuous_id)
      filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ χ.ker by simp)] with h hh
      have : χ (g⁻¹ * h) = 1 := hh
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have hΘc : ∀ x, Continuous fun g => Θ g x := fun x =>
      (hlc.comp fun a => (T ^ (Multiplicative.toAdd a).val) x).continuous
    have hTF : ∀ (n : ℕ) x, (∀ u ∈ I, ρ u x = x) → ∀ u ∈ I, ρ u ((T ^ n) x) = (T ^ n) x := by
      intro n x hx
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        intro u hu
        rw [pow_succ', Equiv.Perm.mul_apply, hT, map_add, hm u hu, ← hmul]
        have : u * φ = φ * (φ⁻¹ * u * φ⁻¹⁻¹) := by group
        rw [this, hmul, ih _ (hI.conj_mem u hu φ⁻¹)]
    have hΘF : ∀ g x, (∀ u ∈ I, ρ u x = x) → ∀ u ∈ I, ρ u (Θ g x) = Θ g x := fun g x hx => hTF _ x hx
    have h0 : ∀ u ∈ I, ρ u (0 : M) = 0 := fun u _ => map_zero _
    let S : Subgroup G :=
      { carrier := {g | ∀ x, (∀ u ∈ I, ρ u x = x) → Θ g x = Θ g 0 + ρ g x}
        one_mem' := fun x _ => by simp [hΘI 1 I.one_mem]
        mul_mem' := fun {g h} hg hh x hx => by
          rw [hΘmul, hΘmul, hg _ (hΘF h x hx), hg _ (hΘF h 0 h0), hh x hx, map_add, hmul, add_assoc]
        inv_mem' := fun {g} hg x hx => by
          have e1 := hg _ (hΘF g⁻¹ x hx)
          have e2 := hg _ (hΘF g⁻¹ 0 h0)
          rw [← hΘmul, mul_inv_cancel, hΘI 1 I.one_mem] at e1 e2
          have e3 : x = ρ g (Θ g⁻¹ x - Θ g⁻¹ 0) := by
            rw [map_sub, eq_sub_iff_add_eq, ← add_right_inj (Θ g 0), ← e1, add_left_comm, ← e2, add_zero]
          have e4 := congrArg (ρ g⁻¹) e3
          rw [hinv] at e4
          rw [e4, add_sub_cancel] }
    have hSc : IsClosed (S : Set G) := by
      have : (S : Set G) = ⋂ x, ⋂ _ : (∀ u ∈ I, ρ u x = x), {g | Θ g x = Θ g 0 + ρ g x} := by
        ext g; simp only [Set.mem_iInter]; rfl
      rw [this]
      refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq (hΘc x) ((hΘc 0).add ?_)
      exact Continuous.comp hρ (continuous_id.prodMk continuous_const)
    have hS := hall S hSc (fun u hu x hx => by rw [hΘI u hu, hΘI u hu, hx u hu, zero_add])
      (fun x _ => by rw [hΘφ, hΘφ, map_zero, add_zero])
    refine ⟨⟨fun g => Θ g 0, hΘc 0, fun g h => ?_⟩, fun u hu => hΘI u hu 0, ?_⟩
    · show Θ (g * h) 0 = Θ g 0 + ρ g (Θ h 0)
      rw [hΘmul]
      exact hS g _ (hΘF h 0 h0)
    · show Θ φ 0 = m
      rw [hΘφ, map_zero, add_zero]
  · rintro ⟨y, hyc, hy⟩ ⟨z, hzc, hz⟩ ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
    simp only at hy1 hy2 hz1 hz2
    let S : Subgroup G :=
      { carrier := {g | y g = z g}
        one_mem' := (hy1 1 I.one_mem).trans (hz1 1 I.one_mem).symm
        mul_mem' := fun {g h} (hg : y g = z g) (hh : y h = z h) => by
          show y (g * h) = z (g * h)
          rw [hy, hz, hg, hh]
        inv_mem' := fun {g} (hg : y g = z g) => by
          show y g⁻¹ = z g⁻¹
          have e1 := hy g⁻¹ g
          have e2 := hz g⁻¹ g
          rw [inv_mul_cancel] at e1 e2
          rw [hy1 1 I.one_mem, hg] at e1
          rw [hz1 1 I.one_mem] at e2
          exact add_right_cancel (e1.symm.trans e2) }
    have hS := hall S (isClosed_eq hyc hzc) (fun u hu => (hy1 u hu).trans (hz1 u hu).symm) (hy2.trans hz2.symm)
    exact Subtype.ext (funext hS)
end
