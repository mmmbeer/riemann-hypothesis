import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphic
import BuildAid.ForwardExisting

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartCobd

open GlobalTheory.CatCoh GlobalTheory.AnPer.Charts

theorem tsze_mul_of_fst {A : Type} [CommRing A] {n : ℕ} (x y : TrivSqZeroExt A (Fin n → A)) (hx : x.fst = 0)
    (hy : y.fst = 0) : x * y = 0 := by
  ext : 1 <;> simp [hx, hy]

theorem comap_fst_nil {A : Type} [CommRing A] {n : ℕ} (J : Ideal A) (hJ : IsNilpotent J) :
    IsNilpotent (J.comap (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom) := by
  obtain ⟨N, hN⟩ := hJ
  refine ⟨N * 2, ?_⟩
  have h1 : (J.comap (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom) ^ N ≤
      RingHom.ker (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom := by
    refine (Ideal.le_comap_pow _ N).trans ?_
    rw [hN, Ideal.zero_eq_bot]
    exact le_of_eq rfl
  rw [pow_mul, Ideal.zero_eq_bot, eq_bot_iff]
  refine (Ideal.pow_right_mono h1 2).trans ?_
  rw [pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  exact tsze_mul_of_fst a b ha hb

section Gen

variable {R : Type} [CommRing R] [Algebra ℂ R] {O O' : Type} [CommRing O] [Algebra ℂ O] [CommRing O'] [Algebra ℂ O']

theorem map_alg (φ : O →ₐ[ℂ] O') (r : R) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ (algebraMap R (R ⊗[ℂ] O) r) = algebraMap R (R ⊗[ℂ] O') r := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem map_mem (φ : O →ₐ[ℂ] O') (M : Ideal R) (c : R ⊗[ℂ] O) (hc : c ∈ M.map (algebraMap R (R ⊗[ℂ] O))) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ c ∈ M.map (algebraMap R (R ⊗[ℂ] O')) := by
  have e : (Algebra.TensorProduct.map (AlgHom.id ℂ R) φ).toRingHom.comp (algebraMap R (R ⊗[ℂ] O)) =
      algebraMap R (R ⊗[ℂ] O') := RingHom.ext (map_alg φ)
  have := Ideal.mem_map_of_mem (Algebra.TensorProduct.map (AlgHom.id ℂ R) φ).toRingHom hc
  rwa [Ideal.map_map, e] at this

theorem map_right (φ : O →ₐ[ℂ] O') (x : O) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (φ x) := by
  simp

theorem map_nil {A : Type} [CommRing A] (f : R →+* A) (M : Ideal R) (h : IsNilpotent M) : IsNilpotent (M.map f) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩

theorem lTensor_alg (D : Derivation ℂ O O) (r : R) :
    LinearMap.lTensor R D.toLinearMap (algebraMap R (R ⊗[ℂ] O) r) = 0 := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem lTensor_right (D : Derivation ℂ O O) (x : O) :
    LinearMap.lTensor R D.toLinearMap (Algebra.TensorProduct.includeRight (R := ℂ) (A := R) x) =
      Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (D x) := by
  simp

theorem right_alg (c : ℂ) : Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (algebraMap ℂ O c) =
    algebraMap R (R ⊗[ℂ] O) (algebraMap ℂ R c) := by
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem tensor_subsingleton [Subsingleton O] (x y : R ⊗[ℂ] O) : x = y := Subsingleton.elim _ _

theorem fst_inl_inr {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)).fst = x := by simp

theorem eq_zero_of_inl_inr {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A)
    (h : (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)) = TrivSqZeroExt.inl x) : v = 0 := by
  simpa using congrArg TrivSqZeroExt.snd h

theorem inl_add_zero {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A) (h : ∀ a, v a = 0) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)) = TrivSqZeroExt.inl x := by
  rw [show v = 0 from funext h]; simp

end Gen

variable {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R]
  {et : Hol F₀.V →+* R} {M : Ideal R}

theorem right_cst (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) (k : K₀.K) (f : Hol F₀.V) :
    Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (K₀.cst k f) = algebraMap R (R ⊗[ℂ] Hol (K₀.W k)) (et f) := by
  by_cases hW : ∃ p, p ∈ K₀.W k
  · obtain ⟨p, hp⟩ := hW
    have e : K₀.cst k f = algebraMap ℂ (Hol (K₀.W k)) (f.fn p.1) := Hol.ext_fn fun p' hp' ↦ by
      rw [K₀.fn_cst k f hp', Hol.fn_algebraMap _ hp', Subsingleton.elim p'.1 p.1]
    rw [e, hev f p.1 (K₀.base k p hp)]
    exact right_alg _
  · haveI : Subsingleton (Hol (K₀.W k)) := ⟨fun a b ↦ Hol.ext_fn fun p hp ↦ (hW ⟨p, hp⟩).elim⟩
    exact tensor_subsingleton _ _

@[reducible] def objS (hM : IsNilpotent M) (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) (k : K₀.K) :
    K₀.DObj et M where
  T :=
    { k := k
      C := R ⊗[ℂ] Hol (K₀.W k)
      alg := ((algebraMap R (R ⊗[ℂ] Hol (K₀.W k))).comp et).toAlgebra
      J := M.map (algebraMap R (R ⊗[ℂ] Hol (K₀.W k)))
      nil := map_nil _ M hM
      ρ := (Algebra.TensorProduct.includeRight (R := ℂ) (A := R)).toRingHom
      ρ_cst := right_cst K₀ hev k }
  alg := Algebra.TensorProduct.leftAlgebra
  compat _ := rfl
  mem _ hd := Ideal.mem_map_of_mem _ hd

def homS (hM : IsNilpotent M) (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) {l : Λ} {k k' : K₀.K}
    (h : K₀.le l k' k) : objS K₀ hM hev k ⟶ objS K₀ hM hev k' :=
  ⟨{ φ := letI := (objS K₀ hM hev k).T.alg; letI := (objS K₀ hM hev k').T.alg
      { (Algebra.TensorProduct.map (AlgHom.id ℂ R) (shA h)).toRingHom with commutes' := fun f ↦ map_alg (shA h) (et f) }
     deg := l
     le := h
     mem := map_mem (shA h) M
     close := by
       have e : (Algebra.TensorProduct.map (AlgHom.id ℂ R) (shA h)).toRingHom.comp (objS K₀ hM hev k).T.ρ =
           (objS K₀ hM hev k').T.ρ.comp (sh h) := RingHom.ext fun x ↦ map_right (R := R) (shA h) x
       exact Eq.mpr (congrArg (Close _ _) e) Relation.ReflTransGen.refl },
   map_alg (shA h)⟩

variable {K₀}

@[reducible] def jetD (S : K₀.DObj et M) : K₀.DObj et M where
  T :=
    { k := S.T.k
      C := TrivSqZeroExt S.T.C (Fin g → S.T.C)
      alg := ((TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp (algebraMap (Hol F₀.V) S.T.C)).toAlgebra
      J := S.T.J.comap (TrivSqZeroExt.fstHom ℤ S.T.C (Fin g → S.T.C)).toRingHom
      nil := comap_fst_nil _ S.T.nil
      ρ := (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp S.T.ρ
      ρ_cst := fun f ↦ congrArg (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)) (S.T.ρ_cst f) }
  alg := ((TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp (algebraMap R S.T.C)).toAlgebra
  compat f := congrArg (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)) (S.compat f)
  mem d hd := S.mem d hd

def jetHom (S : K₀.DObj et M) (ψ : S.T.C →+* TrivSqZeroExt S.T.C (Fin g → S.T.C)) (D : S.T.C → Fin g → S.T.C)
    (hψ : ∀ x, ψ x = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)) (hR : ∀ r a, D (algebraMap R S.T.C r) a = 0)
    (hc : Close (jetD S).T.J (jetD S).T.ρ (ψ.comp S.T.ρ)) : S ⟶ jetD S :=
  ⟨{ φ := letI := (jetD S).T.alg
      { ψ with commutes' := fun f ↦ (hψ _).trans (inl_add_zero _ _ fun a ↦ by rw [S.compat]; exact hR _ a) }
     deg := 0
     le := K₀.le_refl _
     mem := fun c hc ↦ by
       change (ψ c).fst ∈ S.T.J
       rw [hψ, fst_inl_inr]; exact hc
     close := Eq.mpr (congrArg (fun ρ ↦ Close (jetD S).T.J ρ (ψ.comp S.T.ρ))
       (RingHom.ext fun x ↦ congrArg (jetD S).T.ρ (sh_refl (K₀.le_refl _) x))) hc },
   fun d ↦ (hψ _).trans (inl_add_zero _ _ (hR d))⟩

theorem killed {q : Λ →+ R} (s : ∀ S : K₀.DObj et M, S.T.C)
    (key : ∀ {S S' : K₀.DObj et M} (f : S ⟶ S'), s S' - f.1.φ (s S) = algebraMap R S'.T.C (q f.1.deg))
    (S : K₀.DObj et M) (ψ : S.T.C →+* TrivSqZeroExt S.T.C (Fin g → S.T.C)) (D : S.T.C → Fin g → S.T.C)
    (hψ : ∀ x, ψ x = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)) (hR : ∀ r a, D (algebraMap R S.T.C r) a = 0)
    (hD : ∀ h a, D (S.T.ρ h) a = S.T.ρ (dw a h)) : D (s S) = 0 := by
  have e0 := key (jetHom S (TrivSqZeroExt.inlHom _ _) (fun _ ↦ 0) (fun x ↦ (inl_add_zero x _ fun _ ↦ rfl).symm)
    (fun _ _ ↦ rfl) Relation.ReflTransGen.refl)
  have e1 := key (jetHom S ψ D hψ hR (Relation.ReflTransGen.single
    ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ S.T.J.zero_mem, fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _,
      fun h ↦ (hψ _).trans (by
        rw [show D (S.T.ρ h) = fun a ↦ S.T.ρ (dw a h) from funext (hD h)]
        exact tsze_expand _ _)⟩))
  have e2 : ψ (s S) = TrivSqZeroExt.inl (s S) := sub_right_injective (e1.trans e0.symm)
  exact eq_zero_of_inl_inr _ _ ((hψ _).symm.trans e2)

theorem coboundary_on_charts : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →+* R) (M : Ideal R), IsNilpotent M → (∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ (q : Λ →+ R), K₀.perClD et M q = 0 → ∃ G : ∀ k, R ⊗[ℂ] Hol (K₀.W k), (∀ k a, LinearMap.lTensor R (dw a).toLinearMap (G k) = 0) ∧ ∀ l k k' (h : K₀.le l k' k), G k' - Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) (G k) = q l ⊗ₜ[ℂ] 1 := by
  intro g Λ _ F₀ K₀ R _ _ et M hM hev q hq
  obtain ⟨s, hs⟩ := CatCoh.H1.mk_eq_zero.1 hq
  have key : ∀ {S S' : K₀.DObj et M} (f : S ⟶ S'),
      @HSub.hSub S'.T.C S'.T.C S'.T.C _ (s S') (f.1.φ (s S)) = algebraMap R S'.T.C (q f.1.deg) :=
    fun f ↦ congrFun (congrFun (congrFun hs _) _) f
  refine ⟨fun k ↦ s (objS K₀ hM hev k), fun k a ↦ ?_, fun l k k' h ↦ key (homS K₀ hM hev h)⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SqZeroMove.sqZeroMove (TrivSqZeroExt.inlHom (R ⊗[ℂ] Hol (K₀.W k)) (Fin g → R ⊗[ℂ] Hol (K₀.W k)))
    (fun a ↦ TrivSqZeroExt.inr (Pi.single a 1)) (fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _)
  exact congrFun (killed s key (objS K₀ hM hev k) ψ (fun x a ↦ LinearMap.lTensor R (dw a).toLinearMap x)
    (fun x ↦ (hψ x).trans (tsze_expand _ _).symm) (fun r a ↦ lTensor_alg _ r) (fun h a ↦ lTensor_right _ h)) a

end GlobalTheory.ChartCobd
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
  {R : Type} [CommRing R] (et : Hol F.V →+* R) (M : Ideal R)

def perZDLin : (Λ →+ R) →ₗ[R] GlobalTheory.CatCoh.Z1 (K.OD et M) where
  toFun := K.perZD et M
  map_add' q q' := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦ map_add (algebraMap R S'.T.C) (q f.1.deg) (q' f.1.deg))
  map_smul' r q := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦
    (map_mul (algebraMap R S'.T.C) r (q f.1.deg)).trans (Algebra.smul_def (A := S'.T.C) r _).symm)

end GlobalTheory.AnPer.Charts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AnPer.perClD_relation_unique : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : _root_.GlobalTheory.AnPer.Fam Empty g Λ} (K₀ : _root_.GlobalTheory.AnPer.Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : _root_.GlobalTheory.AnPer.Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : _root_.GlobalTheory.AnPer.Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  intro g Λ _ F₀ K₀ R _ _ et M hrich hV hnil het io S d q q' hrel l
  let q'' : Λ →+ R := q' - ∑ i ∈ S, d i • q i
  have hq'' : ∀ m, q'' m = q' m - ∑ i ∈ S, d i * q i m := by
    intro m
    simp [q'', AddMonoidHom.finset_sum_apply, smul_eq_mul]
  have hcl : K₀.perClD et M q'' = 0 := by
    have hc : ∀ p : Λ →+ R, K₀.perClD et M p =
        _root_.GlobalTheory.CatCoh.H1.mk _
          (K₀.perZDLin et M p) := fun p => rfl
    simp only [hc] at hrel ⊢
    simp only [q'', map_sub, map_sum, map_smul, hrel, sub_self]
  obtain ⟨G, hG0, hGsh⟩ := _root_.GlobalTheory.ChartCobd.coboundary_on_charts K₀ et M hnil het q'' hcl
  have hzero : q'' l = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let Φ : ∀ k, R ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol (K₀.W k) →ₗ[ℂ]
        _root_.GlobalTheory.AnPer.Hol (K₀.W k) :=
      fun k => (TensorProduct.lid ℂ _).toLinearMap ∘ₗ LinearMap.rTensor _ φ
    have hΦ : ∀ k r h, Φ k (r ⊗ₜ h) = φ r • h := by
      intro k r h
      simp [Φ]
    have hΦd : ∀ k a y, _root_.GlobalTheory.AnPer.dw a (Φ k y) =
        Φ k (LinearMap.lTensor R (_root_.GlobalTheory.AnPer.dw a).toLinearMap y) := by
      intro k a y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r h => simp [hΦ]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hΦs : ∀ {m k k'} (h : K₀.le m k' k) y,
        Φ k' (Algebra.TensorProduct.map (AlgHom.id ℂ R)
          (_root_.GlobalTheory.AnPer.Charts.shA h) y) =
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k y) := by
      intro m k k' h y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b =>
        simp [hΦ, ← _root_.GlobalTheory.AnPer.Charts.shA_apply]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hfsh : ∀ m k k' (h : K₀.le m k' k),
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k (G k)) =
          Φ k' (G k') + K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) := by
      intro m k k' h
      have h1 := congrArg (Φ k') (hGsh m k k' h)
      rw [map_sub, hΦs, hΦ] at h1
      have h2 : K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) =
          -(φ (q'' m) • 1) := by
        unfold _root_.GlobalTheory.AnPer.Charts.cst
        simp [Algebra.algebraMap_eq_smul_one]
      rw [h2, ← h1]
      abel
    obtain ⟨Gf, -, -, hper, hconst⟩ := _root_.GlobalTheory.AnPer.Charts.glue K₀
      hrich (fun k => Φ k (G k)) (by
        intro k k' h
        simp [hfsh 0 k k' h])
    have hc := hconst (fun k a => by rw [hΦd, hG0, map_zero])
    let p : _root_.GlobalTheory.AnPer.Tot Empty g := ((0 : Empty → ℂ), (0 : Fin g → ℂ))
    have hp := hper l (algebraMap ℂ _ (-(φ (q'' l)))) (fun k k' h => hfsh l k k' h) p (hV _)
    have e : Gf (F₀.shift l p) = Gf p := by
      calc Gf (F₀.shift l p) =
          Gf ((F₀.shift l p).1, (F₀.shift l p).2) := rfl
        _ = Gf ((F₀.shift l p).1, 0) := hc _ (hV _) _
        _ = Gf (p.1, 0) := by rw [Subsingleton.elim (F₀.shift l p).1 p.1]
        _ = Gf p := rfl
    have hfn : (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol F₀.V)
        (-(φ (q'' l)))).fn p.1 = -(φ (q'' l)) := by
      unfold _root_.GlobalTheory.AnPer.Hol.fn
      simp [hV]
    rw [e, hfn] at hp
    linear_combination hp
  rw [← sub_eq_zero, ← hq'' l]
  exact hzero
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClass_linear_relation_unique_of_nilpotent : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  atlas_forward_decl GlobalTheory.AnPer.perClD_relation_unique
end
