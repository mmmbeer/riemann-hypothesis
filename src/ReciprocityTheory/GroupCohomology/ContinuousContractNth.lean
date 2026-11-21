import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
import Mathlib

section
namespace ReciprocityTheory.Coh

noncomputable section

universe u

variable {R : Type u} [CommRing R]

structure Cx (R : Type u) [CommRing R] where
  X : ℕ → Type u
  [acg : ∀ n, AddCommGroup (X n)]
  [mod : ∀ n, Module R (X n)]
  d : ∀ n, X n →ₗ[R] X (n + 1)
  dd : ∀ n x, d (n + 1) (d n x) = 0

attribute [instance] Cx.acg Cx.mod

namespace Cx

def Z (A : Cx R) (n : ℕ) : Submodule R (A.X n) := LinearMap.ker (A.d n)

def B (A : Cx R) : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (A.d n)

abbrev H (A : Cx R) (n : ℕ) := A.Z n ⧸ (A.B n).comap (A.Z n).subtype

def cls (A : Cx R) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) : A.H n := Submodule.Quotient.mk ⟨x, hx⟩

structure Hom (A B : Cx R) where
  f : ∀ n, A.X n →ₗ[R] B.X n
  comm : ∀ n x, f (n + 1) (A.d n x) = B.d n (f n x)

variable {A B C : Cx R}

def Hom.id (A : Cx R) : Hom A A := ⟨fun _ => LinearMap.id, fun _ _ => rfl⟩

def Hom.comp (ψ : Hom B C) (φ : Hom A B) : Hom A C :=
  ⟨fun n => (ψ.f n).comp (φ.f n), fun n x => by simp [φ.comm, ψ.comm]⟩

def Hom.Z (φ : Hom A B) (n : ℕ) : A.Z n →ₗ[R] B.Z n :=
  (φ.f n).restrict fun x hx => by
    have hx' : A.d n x = 0 := hx
    show B.d n (φ.f n x) = 0
    rw [← φ.comm, hx', map_zero]

def Hom.H (φ : Hom A B) (n : ℕ) : A.H n →ₗ[R] B.H n :=
  Submodule.mapQ _ _ (φ.Z n) fun x hx => by
    cases n with
    | zero =>
      have hx' : x.1 = 0 := hx
      show φ.f 0 x.1 ∈ (⊥ : Submodule R _)
      rw [hx', map_zero]; exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy⟩ := hx
      refine ⟨φ.f n y, ?_⟩
      show B.d n (φ.f n y) = φ.f (n + 1) x.1
      rw [← φ.comm, hy]; rfl

def Hom.QuasiIso (φ : Hom A B) : Prop := ∀ n, Function.Bijective (φ.H n)

structure SES (i : Hom A B) (p : Hom B C) : Prop where
  inj : ∀ n, Function.Injective (i.f n)
  exact : ∀ n, Function.Exact (i.f n) (p.f n)
  surj : ∀ n, Function.Surjective (p.f n)

def IsConn (i : Hom A B) (p : Hom B C) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) : Prop :=
  ∀ n (b : B.X n) (a : A.X (n + 1)) (hc : C.d n (p.f n b) = 0) (ha : A.d (n + 1) a = 0),
    B.d n b = i.f (n + 1) a → δ n (C.cls n (p.f n b) hc) = A.cls (n + 1) a ha

structure LES (i : Hom A B) (p : Hom B C) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) : Prop where
  inj : Function.Injective (i.H 0)
  exB : ∀ n, Function.Exact (i.H n) (p.H n)
  exC : ∀ n, Function.Exact (p.H n) (δ n)
  exA : ∀ n, Function.Exact (δ n) (i.H (n + 1))

def up (B : Cx R) : Cx R where
  X n := match n with | 0 => PUnit | n + 1 => B.X n
  acg n := match n with | 0 => inferInstance | _ + 1 => inferInstance
  mod n := match n with | 0 => inferInstance | _ + 1 => inferInstance
  d n := match n with | 0 => 0 | n + 1 => -B.d n
  dd n x := match n with
    | 0 => by show -B.d 0 0 = 0; simp
    | n + 1 => by show -B.d (n + 1) (-B.d n x) = 0; simp [B.dd]

def fib (φ : Hom A B) : Cx R where
  X n := A.X n × B.up.X n
  d n := LinearMap.prod ((A.d n).comp (LinearMap.fst R _ _))
    ((show A.X n →ₗ[R] B.up.X (n + 1) from φ.f n).coprod (B.up.d n))
  dd n x := by
    refine Prod.ext (A.dd n x.1) ?_
    have h := B.up.dd n x.2
    show φ.f (n + 1) (A.d n x.1) + -B.d n (φ.f n x.1 + (show B.X n from B.up.d n x.2)) = 0
    have h' : -B.d n (show B.X n from B.up.d n x.2) = 0 := h
    rw [map_add, neg_add, h', φ.comm]; simp

def prod (A B : Cx R) : Cx R where
  X n := A.X n × B.X n
  d n := (A.d n).prodMap (B.d n)
  dd n x := Prod.ext (A.dd n x.1) (B.dd n x.2)

def pi {ι : Type u} (A : ι → Cx R) : Cx R where
  X n := ∀ v, (A v).X n
  d n := LinearMap.pi fun v => ((A v).d n).comp (LinearMap.proj v)
  dd n x := funext fun v => (A v).dd n (x v)

def FinLen (A : Cx R) (N : ℕ) : Prop :=
  (∀ n, IsFiniteLength R (A.H n)) ∧ ∀ n, N < n → Subsingleton (A.H n)

def chi (A : Cx R) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1) ^ n * ((Module.length R (A.H n)).toNat : ℤ)

structure IsTowerLim (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m)) :
    Prop where
  surj : ∀ m n, Function.Surjective ((τ m).f n)
  compat : ∀ m n x, (τ m).f n ((π (m + 1)).f n x) = (π m).f n x
  ext : ∀ n (x : L.X n), (∀ m, (π m).f n x = 0) → x = 0
  lift : ∀ n (y : ∀ m, (A m).X n), (∀ m, (τ m).f n (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).f n x = y m

end Cx

end

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal

noncomputable section

universe u

variable {R : Type u} [CommRing R]

structure TRep (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] where
  V : Type u
  [acg : AddCommGroup V]
  [mod : Module R V]
  [top : TopologicalSpace V]
  [tag : IsTopologicalAddGroup V]
  [ccs : ContinuousConstSMul R V]
  rho : Representation R G V
  cont : ContAction rho

attribute [instance] TRep.acg TRep.mod TRep.top TRep.tag TRep.ccs

variable {G G' G'' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [Group G''] [TopologicalSpace G''] [IsTopologicalGroup G'']

theorem dn_dn {M : Type u} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R G M) (n : ℕ) (f : (Fin n → G) → M) :
    dn rho (n + 1) (dn rho n f) = 0 := by
  have h := groupCohomology.inhomogeneousCochains.d_comp_d (Rep.of rho) (n := n)
  exact congrArg (fun φ => φ.hom f) h

theorem continuous_contractNth (n : ℕ) (j : Fin (n + 1)) :
    Continuous fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g := by
  refine continuous_pi fun k => ?_
  unfold Fin.contractNth
  split_ifs <;> fun_prop

theorem continuous_dn (M : TRep R G) (n : ℕ) {f : (Fin n → G) → M.V} (hf : Continuous f) :
    Continuous (dn M.rho n f) := by
  have h1 : Continuous fun g : Fin (n + 1) → G => M.rho (g 0) (f fun i => g i.succ) :=
    M.cont.comp (f := fun g : Fin (n + 1) → G => (g 0, f fun i => g i.succ))
      ((continuous_apply 0).prodMk (hf.comp (continuous_pi fun i => continuous_apply _)))
  exact h1.add (continuous_finsetSum _ fun j _ => (hf.comp (continuous_contractNth n j)).const_smul _)

namespace TRep

def coch (M : TRep R G) : Cx R where
  X n := Cn M.rho n
  d n := (dn M.rho n).restrict fun _ hf => continuous_dn M n hf
  dd n x := Subtype.ext (dn_dn M.rho n x.1)

abbrev H (M : TRep R G) (n : ℕ) := M.coch.H n

def res (M : TRep R G) (φ : G' →* G) (hφ : Continuous φ) : TRep R G' where
  V := M.V
  rho := M.rho.comp φ
  cont := M.cont.comp (f := fun p : G' × M.V => (φ p.1, p.2))
    ((hφ.comp continuous_fst).prodMk continuous_snd)

abbrev resSub (M : TRep R G) (U : Subgroup G) : TRep R U := M.res U.subtype continuous_subtype_val

end TRep

structure Pair (M : TRep R G) (M' : TRep R G') where
  φ : G' →* G
  u : M.V →ₗ[R] M'.V
  φ_cont : Continuous φ
  u_cont : Continuous u
  equiv : ∀ g m, u (M.rho (φ g) m) = M'.rho g (u m)

theorem contractNth_map (φ : G' →* G) (n : ℕ) (j : Fin (n + 1)) (g : Fin (n + 1) → G') :
    (fun i => φ (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) fun i => φ (g i) := by
  funext k
  unfold Fin.contractNth
  split_ifs <;> simp

def Pair.hom {M : TRep R G} {M' : TRep R G'} (P : Pair M M') : Cx.Hom M.coch M'.coch where
  f n :=
    { toFun := fun f => ⟨fun g => P.u (f.1 fun i => P.φ (g i)),
        P.u_cont.comp (Continuous.comp f.2 (continuous_pi fun i => P.φ_cont.comp (continuous_apply i)))⟩
      map_add' := fun f f' => Subtype.ext (funext fun g => map_add P.u _ _)
      map_smul' := fun r f => Subtype.ext (funext fun g => map_smul P.u _ _) }
  comm n f := by
    refine Subtype.ext (funext fun g => ?_)
    show P.u (dn M.rho n f.1 fun i => P.φ (g i)) = dn M'.rho n (fun g => P.u (f.1 fun i => P.φ (g i))) g
    simp only [dn_apply, map_add, map_sum, map_smul, P.equiv, contractNth_map]

def Pair.ofMap {M M' : TRep R G} (u : M.V →ₗ[R] M'.V) (hu : Continuous u)
    (he : ∀ g m, u (M.rho g m) = M'.rho g (u m)) : Pair M M' :=
  ⟨MonoidHom.id G, u, continuous_id, hu, he⟩

def Pair.res (M : TRep R G) (φ : G' →* G) (hφ : Continuous φ) : Pair M (M.res φ hφ) :=
  ⟨φ, LinearMap.id, hφ, continuous_id, fun _ _ => rfl⟩

structure admitted {A B C : TRep R G} (i : Pair A B) (p : Pair B C) : Prop where
  i_id : i.φ = MonoidHom.id G
  p_id : p.φ = MonoidHom.id G
  emb : Topology.IsEmbedding i.u
  exact : Function.Exact i.u p.u
  sec : ∃ s : C.V → B.V, Continuous s ∧ ∀ c, p.u (s c) = c

def IsInvRep (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M) : Prop :=
  P.φ = QuotientGroup.mk' N ∧ Topology.IsEmbedding P.u ∧
    ∀ m, m ∈ LinearMap.range P.u ↔ ∀ g ∈ N, M.rho g m = m

def rep (U : Subgroup G) (x : G) : G := (Quotient.mk (QuotientGroup.rightRel U) x).out

theorem mul_rep_inv_mem (U : Subgroup G) (x : G) : x * (rep U x)⁻¹ ∈ U :=
  QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel U) x)))

def retr (U : Subgroup G) (x : G) : U := ⟨x * (rep U x)⁻¹, mul_rep_inv_mem U x⟩

def corFun (M : TRep R G) (U : Subgroup G) (n : ℕ) (f : (Fin n → U) → M.V) (g : Fin n → G) : M.V :=
  ∑ᶠ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹
    (f fun i => (retr U (c.out * Fin.partialProd g i.castSucc))⁻¹ * retr U (c.out * Fin.partialProd g i.succ))

def IsCor (M : TRep R G) (U : Subgroup G) (cor : Cx.Hom (M.resSub U).coch M.coch) : Prop :=
  ∀ n f, (cor.f n f).1 = corFun M U n f.1

structure Pairing (M N P : TRep R G) where
  β : M.V →ₗ[R] N.V →ₗ[R] P.V
  cont : Continuous fun x : M.V × N.V => β x.1 x.2
  equiv : ∀ g m n, β (M.rho g m) (N.rho g n) = P.rho g (β m n)

def cupFun {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (f : (Fin p → G) → M.V)
    (f' : (Fin q → G) → N.V) (g : Fin (p + q) → G) : P.V :=
  b.β (f fun i => g (Fin.castAdd q i))
    (N.rho (List.ofFn fun i => g (Fin.castAdd q i)).prod (f' fun j => g (Fin.natAdd p j)))

def IsCup {M N P : TRep R G} (b : Pairing M N P)
    (cup : ∀ p q, M.H p →ₗ[R] N.H q →ₗ[R] P.H (p + q)) : Prop :=
  ∀ p q (x : M.coch.X p) (y : N.coch.X q) (hx : M.coch.d p x = 0) (hy : N.coch.d q y = 0),
    ∃ (z : P.coch.X (p + q)) (hz : P.coch.d (p + q) z = 0), z.1 = cupFun b p q x.1 y.1 ∧
      cup p q (M.coch.cls p x hx) (N.coch.cls q y hy) = P.coch.cls (p + q) z hz

def TRep.cast (M : TRep R G) {n m : ℕ} (h : n = m) : M.H n ≃ₗ[R] M.H m := h ▸ LinearEquiv.refl R _

def IsCoind (U : Subgroup G) (M : TRep R U) (C : TRep R G) (ev : Pair C M) : Prop :=
  ev.φ = U.subtype ∧ ∃ j : C.V → C(G, M.V), Topology.IsEmbedding j ∧
    (∀ c g, j c g = ev.u (C.rho g c)) ∧
    ∀ f : C(G, M.V), (∀ (x : U) g, f (x * g) = M.rho x (f g)) → f ∈ Set.range j

structure SelData (M : TRep R G) (ι : Type u) where
  D : ι → Type u
  [grp : ∀ v, Group (D v)]
  [top : ∀ v, TopologicalSpace (D v)]
  [tgrp : ∀ v, IsTopologicalGroup (D v)]
  φ : ∀ v, D v →* G
  φ_cont : ∀ v, Continuous (φ v)
  U : ι → Cx R
  j : ∀ v, Cx.Hom (U v) (M.res (φ v) (φ_cont v)).coch

attribute [instance] SelData.grp SelData.top SelData.tgrp

namespace SelData

variable {M : TRep R G} {ι : Type u} (S : SelData M ι)

abbrev loc (v : ι) : Cx R := (M.res (S.φ v) (S.φ_cont v)).coch

abbrev locHom (v : ι) : Cx.Hom M.coch (S.loc v) := (Pair.res M (S.φ v) (S.φ_cont v)).hom

def diff : Cx.Hom (Cx.prod M.coch (Cx.pi S.U)) (Cx.pi S.loc) where
  f n := LinearMap.pi fun v => ((S.locHom v).f n).comp (LinearMap.fst R _ _) -
    ((S.j v).f n).comp ((LinearMap.proj v).comp (LinearMap.snd R _ _))
  comm n x := funext fun v => by
    show (S.locHom v).f (n + 1) (M.coch.d n x.1) - (S.j v).f (n + 1) ((S.U v).d n (x.2 v)) =
      (S.loc v).d n ((S.locHom v).f n x.1 - (S.j v).f n (x.2 v))
    rw [map_sub, (S.locHom v).comm, (S.j v).comm]

def cx : Cx R := Cx.fib S.diff

def sel (n : ℕ) : Submodule R (M.H n) :=
  ⨅ v, (LinearMap.range ((S.j v).H n)).comap ((S.locHom v).H n)

end SelData

end

end ReciprocityTheory.Coh
end
