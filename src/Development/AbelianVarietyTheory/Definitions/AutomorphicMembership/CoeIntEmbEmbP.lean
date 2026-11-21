import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Alg

variable {S : Type} [CommRing S] {ρ V : Type}

def apolar (P : MvPolynomial V S) (f : MvPowerSeries V S) : S :=
  ∑ m ∈ P.support, P.coeff m * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f)

theorem apolar_monomial (m : V →₀ ℕ) (c : S) (f : MvPowerSeries V S) :
    apolar (MvPolynomial.monomial m c) f = c * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f) := by
  classical
  rw [apolar, Finset.sum_subset (MvPolynomial.support_monomial_subset) fun x _ hx => by
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul], Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

example : apolar (MvPolynomial.monomial (Finsupp.single () 2) (1 : ℚ))
    (MvPowerSeries.monomial (Finsupp.single () 2) 1) = 2 := by
  rw [apolar_monomial, MvPowerSeries.coeff_monomial_same, Finsupp.prod_single_index (by simp)]
  norm_num [Nat.factorial]

def jetAt (c : ρ → V) (m : ℕ) : Jet S ρ m →ₐ[S] Jet S V m :=
  jetMap (fun r => MvPolynomial.X (c r)) fun r => X_mem_orig (c r)

def serAt (c : ρ → V) (g : MvPowerSeries ρ S) : MvPowerSeries V S :=
  MvPowerSeries.subst (fun r => (MvPowerSeries.X (c r) : MvPowerSeries V S)) g

end Alg

section Exp

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

structure IsExp (u : ρ → (Sp (DualNumber S) ⟶ G.left)) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) : Prop where
  zero : ∀ m, homAt x0 (jetAug : Jet S ρ m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ≫ x (m + 1) = x m
  law : ∀ m, homAt x0 (jetSum (Finset.univ : Finset (Fin 2))) ≫ x m =
    (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) * (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)
  act : ∀ m (c : O), x m ≫ a.act c = homAt x0 (jetScale fun r => ch r c) ≫ x m
  tan : ∀ r, (homAt x0 (jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left = u r

variable (bar : O → O) (L : LB G.left) (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => eSec G) fun _ => 1))

abbrev Fr (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) : Type :=
  ∀ m, LB.Gen (LB.LinComb L (K := PUnit) (fun _ => (x m).left) fun _ => 1)

structure IsHoriz (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m y J, Good L y J →
    val (e (m + 1)) (homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m)).left y J = val (e m) (𝟙 _) y J
  zero : ∀ y J, Good L y J → val (e 0) (homAt x0 (jetAug : Jet S ρ 0 →ₐ[S] S)).left y J = val rig x0 y J
  coc : ∀ c : O, ∃ β : LB.Gen (LB.LinComb L (K := Fin 4)
      ![(a.act (1 + c * bar c)).left, (a.act c).left, 𝟙 _, (a.act (c * bar c)).left] ![1, -2, -1, -1]), β.IsGen ∧
    (∀ y J, Good L y J → val β (eSec G) y J = (val rig (𝟙 _) y J ^ 3)⁻¹) ∧
    ∀ m y J, Good L y J → val (e m) (homAt x0 (jetScale fun r => ch r (1 + c * bar c))).left y J =
      val β (x m).left y J * val (e m) (homAt x0 (jetScale fun r => ch r c)).left y J ^ 2 * val (e m) (𝟙 _) y J *
        val (e m) (homAt x0 (jetScale fun r => ch r (c * bar c))).left y J

variable (G) in

abbrev Pw (n : ℕ) : Over X := Over.mk x0 ⊗ powObj G n

variable (G) in

abbrev pr {n : ℕ} (b : Fin n) : (Pw G x0 n).left ⟶ G.left := (snd _ _ ≫ powPr G b).left

abbrev SecPw (n k : ℕ) : Type := LB.Sec (LB.LinComb L (pr G x0 (n := n)) fun _ => (k : ℤ))

def pwPt {n : ℕ} (col : Fin n → ρ → V) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (m : ℕ) :
    overAt x0 (Jet S V m) ⟶ Pw G x0 n :=
  lift (Over.homMk (spMap (algebraMap S (Jet S V m))) rfl)
    ((powIsLimit G n).lift (Fan.mk _ fun b => homAt x0 (jetAt (col b) m) ≫ x m))

def IsGermPw {n k : ℕ} (col : Fin n → ρ → V) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x)
    (s : SecPw x0 L n k) (f : MvPowerSeries V S) : Prop :=
  ∀ m y J, Good L y J → sval s (pwPt x0 col x m).left y J =
    gs (𝟙 _) y ⊤ (toΓ _ (psJet m f)) * ∏ b, (val (e m) (homAt x0 (jetAt (col b) m)).left y J ^ k).val

def IsVal (u : ρ → (Sp (DualNumber S) ⟶ G.left)) {n k : ℕ} (col : Fin n → ρ → V) (P : MvPolynomial V S)
    (s : SecPw x0 L n k) (v : S) : Prop :=
  ∃ (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) (f : MvPowerSeries V S),
    IsExp a x0 ch u x ∧ IsHoriz a x0 ch bar L rig x e ∧ IsGermPw x0 L col x e s f ∧ v = apolar P f

def IsBoxSum {n k N : ℕ} (s : SecPw x0 L n k) (c : Fin N → S) (σ : Fin N → Fin n → H0 L k) : Prop :=
  ∀ y J, Good L y J → sval s (𝟙 _) y J =
    ∑ i, gs (fst (Over.mk x0) (powObj G n)).left y ⊤ (toΓ S (c i)) * ∏ b, sval (σ i b) (pr G x0 b) y J

end Exp

section Gt

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} (Y : Ray oa)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ Sp R) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

def IsTermGerm {k : ℕ} (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ Y.H) (e : Fr x0 D.toPre.P.L fun m => x m ≫ Y.q)
    {α : D.toPre.X} (σ : D.toPre.SecB k α) (g : MvPowerSeries ρ S) : Prop :=
  ∀ m y J, Good D.toPre.P.L y J → sval σ (x m ≫ Y.q).left y J * (val ((Y.Φ _ (x m)).s α) (𝟙 _) y J).val =
    gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (e m) (𝟙 _) y J ^ k).val

def IsValGt [TopologicalSpace S] (u : ρ → (Sp (DualNumber S) ⟶ Y.H.left)) {n k : ℕ} (col : Fin n → ρ → V)
    (P : MvPolynomial V S) (s : SecPw x0 U.LG.L n k) (v : S) : Prop :=
  ∃ (N : ℕ) (c : Fin N → S) (σ : Fin N → Fin n → H0 U.LG.L k) (F : Fin N → Fin n → ∀ α, D.toPre.SecB k α)
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ Y.H) (e : Fr x0 D.toPre.P.L fun m => x m ≫ Y.q)
    (g : Fin N → Fin n → D.toPre.X → MvPowerSeries ρ S),
    IsBoxSum x0 U.LG.L s c σ ∧ (∀ i b l, U.ExpandsAt l k (σ i b) (F i b)) ∧ IsExp Y.act x0 ch u x ∧
    IsHoriz (Ray.actB oa) x0 ch star D.toPre.P.L D.toPre.rig (fun m => x m ≫ Y.q) e ∧
    (∀ i b α, IsTermGerm Y x0 x e (F i b α) (g i b α)) ∧
    HasSum (fun χ : Fin n → D.toPre.X =>
      apolar P (∑ i, MvPowerSeries.C (c i) * ∏ b, serAt (col b) (g i b (χ b)))) v

end Gt

end GlobalTheory.RayEv
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.DeRham GlobalTheory.Cris
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv



section Contr

variable {O C Λ J : Type} [CommRing O] [Field C] [Algebra O C] [CommRing Λ] [DecidableEq J] {σ : J → Λ →+* C}
  (h : IsSplitting σ) {M M' : Type*} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']

def eigDefect (ρ : Λ →+* Module.End O M) (i : J) (x : M) : C ⊗[O] M :=
  proj h (baseChangeAction C ρ) i (1 ⊗ₜ x) - 1 ⊗ₜ x

def contr (ρ : Λ →+* Module.End O M) (ψ : LinearMap.BilinForm O M) (i : J) (x x' : M) : C :=
  ψ.baseChange C (eigDefect h ρ i x) (1 ⊗ₜ x')

theorem eigDefect_map {ρ : Λ →+* Module.End O M} {ρ' : Λ →+* Module.End O M'} {f : M →ₗ[O] M'}
    (hf : IsEquivariant ρ ρ' f) (i : J) (x : M) :
    f.baseChange C (eigDefect h ρ i x) = eigDefect h ρ' i (f x) := by
  have e : IsEquivariant (baseChangeAction C ρ) (baseChangeAction C ρ') (f.baseChange C) := fun a z => by
    induction z with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul c m => exact congrArg (c ⊗ₜ[O] ·) (hf a m)
  rw [eigDefect, map_sub, e.proj h]
  rfl

theorem contr_comp {ρ : Λ →+* Module.End O M} {ρ' : Λ →+* Module.End O M'} {f : M →ₗ[O] M'}
    (hf : IsEquivariant ρ ρ' f) (ψ : LinearMap.BilinForm O M') (i : J) (x x' : M) :
    contr h ρ (ψ.compl₁₂ f f) i x x' = contr h ρ' ψ i (f x) (f x') := by
  rw [contr, contr, ← eigDefect_map h hf]
  induction eigDefect h ρ i x with
  | zero => simp
  | add z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw]
  | tmul c m => simp [LinearMap.BilinForm.baseChange_tmul]


example {ρ : Λ →+* Module.End O M} (ψ : LinearMap.BilinForm O M) {i j : J} (hij : j ≠ i) {x : M}
    (hx : (1 : C) ⊗ₜ[O] x ∈ eigenSub (baseChangeAction C ρ) (σ j)) (x' : M) :
    contr h ρ ψ i x x' = -algebraMap O C (ψ x x') := by
  rw [contr, eigDefect, proj_of_mem_ne h hij hx, zero_sub, map_neg, LinearMap.neg_apply,
    LinearMap.BilinForm.baseChange_tmul, _root_.mul_one, Algebra.algebraMap_eq_smul_one]

end Contr

section Nat

variable {O Λ : Type} [CommRing O] [CommRing Λ] {G B : Over (Sp O)} [GrpObj G] [IsCommMonObj G] [GrpObj B]
  [IsCommMonObj B] {a : OAct Λ G} {b : OAct Λ B}

variable (b) in

structure PolSplit (L : LB B.left) : Type 1 where

  ψ : LinearMap.BilinForm O (HdR B)
  pol : IsPolForm (dp0 O) (𝟙 _) B L ψ

  s : Lie b →ₗ[O] HdR B
  lift : ∀ v, IsLieImage (s v) v.hom
  lag : ∀ v w, ψ (s v) (s w) = 0

variable {q : G ⟶ B} (hq : IsLinearHom a b q)

def NatLie (_hq : IsLinearHom a b q) : Submodule O (Lie a × HdR B) where
  carrier := {z | IsLieImage z.2 (z.1.hom ≫ q)}
  add_mem' {z w} hz hw := by
    haveI := _hq.isMonHom
    have := IsLieImage.add hz hw
    rwa [← MonObj.mul_comp] at this
  zero_mem' := by
    haveI := _hq.isMonHom
    change IsLieImage 0 ((1 : epsR O ⟶ G) ≫ q)
    rw [MonObj.one_comp]
    exact isLieImage_one_iff.2 (zero_mem _)
  smul_mem' r z hz := by
    have := IsLieImage.smul hz r
    rwa [← Category.assoc] at this

def natToB : NatLie hq →ₗ[O] HdR B := LinearMap.snd O _ _ ∘ₗ (NatLie hq).subtype

def natToLie : NatLie hq →ₗ[O] Lie a := LinearMap.fst O _ _ ∘ₗ (NatLie hq).subtype

def natEnd (c : Λ) : Module.End O (NatLie hq) :=
  ((DistribSMul.toLinearMap O (Lie a) c).prodMap (DeRham.act (dp0 O) (𝟙 _) b c)).restrict fun z hz => by
    haveI := b.hom c
    have := IsLieImage.push hz (b.act c)
    rwa [Category.assoc, ← hq.comm, ← Category.assoc] at this

def natAct : Λ →+* Module.End O (NatLie hq) where
  toFun := natEnd hq
  map_one' := LinearMap.ext fun z => Subtype.ext (Prod.ext (one_smul Λ z.1.1)
    (LinearMap.congr_fun (map_one (DeRham.act (dp0 O) (𝟙 _) b)) z.1.2))
  map_mul' c c' := LinearMap.ext fun z => Subtype.ext (Prod.ext (mul_smul c c' z.1.1)
    (LinearMap.congr_fun (map_mul (DeRham.act (dp0 O) (𝟙 _) b) c c') z.1.2))
  map_zero' := LinearMap.ext fun z => Subtype.ext (Prod.ext (zero_smul Λ z.1.1)
    (LinearMap.congr_fun (map_zero (DeRham.act (dp0 O) (𝟙 _) b)) z.1.2))
  map_add' c c' := LinearMap.ext fun z => Subtype.ext (Prod.ext (add_smul c c' z.1.1)
    (LinearMap.congr_fun (map_add (DeRham.act (dp0 O) (𝟙 _) b) c c') z.1.2))


variable {L : LB B.left} (sp : PolSplit b L)

def natForm : LinearMap.BilinForm O (NatLie hq) := sp.ψ.compl₁₂ (natToB hq) (natToB hq)

def natLift (v : Lie a) : NatLie hq :=
  ⟨(v, sp.s (Lie.mapLinear hq v)), sp.lift (Lie.mapLinear hq v)⟩


variable {C J : Type} [Field C] [Algebra O C] [DecidableEq J] {σ : J → Λ →+* C} (h : IsSplitting σ)

def kapAb (i : J) (u u' : Lie b) : C := contr h (DeRham.act (dp0 O) (𝟙 _) b) sp.ψ i (sp.s u) (sp.s u')

def kapExt (i : J) (u u' : Lie a) : C :=
  contr h (natAct hq) (natForm hq sp) i (natLift hq sp u) (natLift hq sp u')


example (b : OAct Λ (𝟙_ (Over (Sp O)))) (L : LB (𝟙_ (Over (Sp O))).left) (hL : ∀ i j, L.g i j = 1) :
    Nonempty (PolSplit b L) :=
  ⟨⟨0, isPolForm_zero L hL, 0, fun v => toUnit_unique 1 v.hom ▸ isLieImage_one_iff.2 (zero_mem _), fun _ _ => rfl⟩⟩

end Nat

end GlobalTheory.RayEv
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.DeRham GlobalTheory.Cris
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv


section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p}
  {P : PointsOfFlagModel.PtC Y C}

variable (C) in

theorem integers : (NormedField.valuation (K := ↥C.S)).Integers ↥(intO ↥C.S) :=
  ⟨Subtype.val_injective, fun x => x.2, fun {r} hr => ⟨⟨r, hr⟩, rfl⟩⟩

variable (P) in

def embP (τ : E →+* ℂ) : E →+* ↥C.S := P.fK.comp (embF c τ)

abbrev intEmb (φ : E →+* ↥C.S) : 𝓞 E →+* ↥(intO ↥C.S) := HTLat.embO (integers C) φ


variable (A : DatAt Y P)

def ray : letI := H.starRing; Ray A.U.oD := letI := H.starRing; Classical.choice inferInstance

abbrev actGt := letI := H.starRing; (ray A).act

abbrev actAb := letI := H.starRing; Ray.actB A.U.oD

abbrev actT := letI := H.starRing; torAct A.U.D.toPre (𝓞 E)

def LieGt (τ : E →+* ℂ) : Type := LieEig A.f (actGt A) (intEmb (embP P τ))

instance (τ : E →+* ℂ) : AddCommGroup (LieGt A τ) :=
  inferInstanceAs (AddCommGroup (LieEig A.f (actGt A) (intEmb (embP P τ))))

instance (τ : E →+* ℂ) : Module ↥(intO ↥C.S) (LieGt A τ) :=
  inferInstanceAs (Module ↥(intO ↥C.S) (LieEig A.f (actGt A) (intEmb (embP P τ))))

def LieB (τ : E →+* ℂ) : Type := LieEig A.f (actAb A) (intEmb (embP P τ))

instance (τ : E →+* ℂ) : AddCommGroup (LieB A τ) :=
  inferInstanceAs (AddCommGroup (LieEig A.f (actAb A) (intEmb (embP P τ))))

instance (τ : E →+* ℂ) : Module ↥(intO ↥C.S) (LieB A τ) :=
  inferInstanceAs (Module ↥(intO ↥C.S) (LieEig A.f (actAb A) (intEmb (embP P τ))))

def LieT (τ : E →+* ℂ) : Type := LieEig A.f (actT A) (intEmb (embP P τ))

instance (τ : E →+* ℂ) : AddCommGroup (LieT A τ) :=
  inferInstanceAs (AddCommGroup (LieEig A.f (actT A) (intEmb (embP P τ))))

instance (τ : E →+* ℂ) : Module ↥(intO ↥C.S) (LieT A τ) :=
  inferInstanceAs (Module ↥(intO ↥C.S) (LieEig A.f (actT A) (intEmb (embP P τ))))

theorem q_lin : letI := H.starRing; IsLinearHom (actGt A) (actAb A) (ray A).q := letI := H.starRing; (ray A).q_linear

theorem i_lin : letI := H.starRing; IsLinearHom (actT A) (actGt A) (ray A).i := letI := H.starRing; (ray A).i_linear

def resB (τ : E →+* ℂ) : LieGt A τ →ₗ[↥(intO ↥C.S)] LieB A τ := eigMap A.f (q_lin A) _

def incT (τ : E →+* ℂ) : LieT A τ →ₗ[↥(intO ↥C.S)] LieGt A τ := eigMap A.f (i_lin A) _

abbrev Split : Type 1 := PolSplit ((actAb A).pullback (spMap A.f))
  (A.U.D.toPre.P.L.pull (pullback.fst A.U.D.toPre.P.A.hom (spMap A.f)))

open Classical in

def kapB (τ : E →+* ℂ) (u u' : LieB A τ) : ↥C.S :=
  if h : Nonempty (Split A) then kapAb h.some (HTLat.isSplitting_embO (integers C)) (embP P τ) u.1 u'.1 else 0

open Classical in

def kapGt (τ : E →+* ℂ) (u u' : LieGt A τ) : ↥C.S :=
  if h : Nonempty (Split A) then
    kapExt (isLinearHom_pull A.f (q_lin A)) h.some (HTLat.isSplitting_embO (integers C)) (embP P τ) u.1 u'.1
  else 0

open Classical in

theorem kapB_of (h : Nonempty (Split A)) (τ : E →+* ℂ) (u u' : LieB A τ) :
    kapB A τ u u' = kapAb h.some (HTLat.isSplitting_embO (integers C)) (embP P τ) u.1 u'.1 := dif_pos h

open Classical in

theorem kapGt_of (h : Nonempty (Split A)) (τ : E →+* ℂ) (u u' : LieGt A τ) : kapGt A τ u u' =
    kapExt (isLinearHom_pull A.f (q_lin A)) h.some (HTLat.isSplitting_embO (integers C)) (embP P τ) u.1 u'.1 :=
  dif_pos h

variable {T : Type} (emb : T × Bool → E →+* ℂ)

structure HarmAt : Type where

  a : ℕ

  b : ℕ

  n : ℕ

  u : ∀ t, Fin a → LieGt A (emb (t, false))

  w : ∀ t, Fin b → LieGt A (emb (t, true))

  P : Harm.Poly ↥C.S T a b (Fin n)
  harm : Harm.IsHarmonic P

abbrev xC : Sp ↥C.S ⟶ Sp A.R := spMap ((intO ↥C.S).subtype.comp A.f)

structure SecAt : Type where

  k : ℕ
  pos : 0 < k

  s : ∀ n, SecPw (xC A) A.U.U.LG.L n k

def SecAt.zero (k : ℕ) (hk : 0 < k) : SecAt A :=
  ⟨k, hk, fun _ => ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩⟩

def HarmAt.pow (u : ∀ t, LieGt A (emb (t, false))) (n : ℕ) (t : T) (k : Fin n) (m : ℕ) : HarmAt A emb :=
  ⟨1, 0, n, fun t _ => u t, fun _ => Fin.elim0, MvPolynomial.X (Harm.xVar t 0 k) ^ m, fun _ _ b => b.elim0⟩

example (u : ∀ t, LieGt A (emb (t, false))) (w : ∀ t, LieGt A (emb (t, true))) (t : T) : HarmAt A emb :=
  ⟨1, 1, 2, fun t _ => u t, fun t _ => w t,
    MvPolynomial.X (Harm.xVar t 0 0) * MvPolynomial.X (Harm.yVar t 0 1), fun t' a b => by
      classical
      simp [Harm.laplacian_apply, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite (MvPolynomial.pderiv _)]⟩

variable {A emb}

namespace HarmAt

variable (Q : HarmAt A emb)

abbrev Row : Type := T × (Fin Q.a ⊕ Fin Q.b)

def vec : Q.Row → LieAt A.f (actGt A)
  | (t, .inl i) => (Q.u t i).1
  | (t, .inr j) => (Q.w t j).1

def chr (r : Q.Row) : 𝓞 E →+* ↥C.S := (embP P (emb (r.1, r.2.isRight))).comp (algebraMap (𝓞 E) E)

def col (k : Fin Q.n) (r : Q.Row) : Harm.Var T Q.a Q.b (Fin Q.n) := (r.1, r.2, k)

variable [Fintype T] [DecidableEq T]

def IsValA (s : SecAt A) (v : ↥C.S) : Prop :=
  letI := H.starRing
  ∃ u : Q.Row → (Over.mk ((epsR ↥(intO ↥C.S)).hom ≫ spMap A.f) ⟶ A.t.G),
    (∀ r, FormalPoint.IsPointOf A.U.U.toUnifPre ((ray A).Φ _ (tanPt A.f (Q.vec r))) (u r)) ∧
    IsVal A.t.act (xC A) Q.chr H.bar A.U.U.LG.L A.U.U.LG.rig
      (fun r => spMap (dualMap (intO ↥C.S).subtype) ≫ (u r).left) Q.col Q.P (s.s Q.n) v

def IsValG (s : SecAt A) (v : ↥C.S) : Prop :=
  letI := H.starRing
  IsValGt A.U.U.toUnifPre (ray A) (xC A) Q.chr
    (fun r => spMap (dualMap (intO ↥C.S).subtype) ≫ (tanPt A.f (Q.vec r)).left) Q.col Q.P (s.s Q.n) v

open Classical in

def evA (s : SecAt A) : ↥C.S := if h : ∃! v, Q.IsValA s v then h.choose else 0

open Classical in

def evGt (s : SecAt A) : ↥C.S := if h : ∃! v, Q.IsValG s v then h.choose else 1



end HarmAt

variable (A)



end Point

end GlobalTheory.RayEv
end
end
