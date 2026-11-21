import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LocallyExactCech
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace UpperTheory.Et

variable {R : Type} [CommRing R]

abbrev toPC {τ : GrothendieckTopology Scheme.{0}} (I : CochainComplex (Sheaf τ (ModuleCat.{1} (ULift.{1} R))) ℤ) : PC R :=
  ((sheafToPresheaf τ _).mapHomologicalComplex _).obj I

abbrev etC (F : GlobalTheory.EtC.Shv R) : PC R := toPC (GlobalTheory.EtC.res R F)

def etι (F : GlobalTheory.EtC.Shv R) : F.obj ⟶ (etC F).X 0 := (GlobalTheory.EtC.resι R F).hom

abbrev prC (G : GlobalTheory.Et.Shv R) : PC R := toPC (injectiveResolution G).cochainComplex

def prι (G : GlobalTheory.Et.Shv R) : G.obj ⟶ (prC G).X 0 :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ (injectiveResolution G).ι'.f 0).hom

def prGen (R : Type) [CommRing R] (X : Scheme.{0}) : sec ((GlobalTheory.Et.freeOn R).obj X).obj X :=
  ap (toSheafify Scheme.proetaleTopology
    (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))).obj (uliftYoneda.{1}.obj X)))
    (ModuleCat.freeMk (ULift.up (𝟙 X)))

section Cont
variable (R) (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T]

def cPre : PMod R where
  obj U := ModuleCat.of (ULift.{1} R) (ULift.{1} C(U.unop, T))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ⟨g.down.comp f.unop.base.hom⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def cSh : GlobalTheory.Et.Shv R := (presheafToSheaf _ _).obj (cPre R T)

def cSec {U : Scheme.{0}} (g : C(U, T)) : sec (cSh R T).obj U :=
  ap (toSheafify Scheme.proetaleTopology (cPre R T)) (ULift.up g)

variable {R T} {T' : Type} [AddCommGroup T'] [Module R T'] [TopologicalSpace T'] [IsTopologicalAddGroup T']
  [ContinuousConstSMul R T']

def cPreMap (u : T →L[R] T') : cPre R T ⟶ cPre R T' where
  app U := ModuleCat.ofHom
    { toFun := fun g => ⟨(⟨u, u.continuous⟩ : C(T, T')).comp g.down⟩
      map_add' := fun a b => congrArg ULift.up (ContinuousMap.ext fun x => map_add u _ _)
      map_smul' := fun r a => congrArg ULift.up (ContinuousMap.ext fun x => map_smul u r.down _) }
  naturality _ _ _ := rfl

def cMap (u : T →L[R] T') : cSh R T ⟶ cSh R T' := (presheafToSheaf _ _).map (cPreMap u)

end Cont

section Adic
variable (l : ℕ) [Fact l.Prime]

def ZL (k : ℕ) : Type := ZMod (l ^ k)

instance (k : ℕ) : CommRing (ZL l k) := inferInstanceAs (CommRing (ZMod (l ^ k)))
instance (k : ℕ) : Algebra ℤ_[l] (ZL l k) := (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)).toAlgebra
instance (k : ℕ) : TopologicalSpace (ZL l k) := ⊥
instance (k : ℕ) : DiscreteTopology (ZL l k) := ⟨rfl⟩

def ZL.red (k : ℕ) : ZL l (k + 1) →L[ℤ_[l]] ZL l k where
  toFun := (ZMod.castHom (pow_dvd_pow l k.le_succ) (ZMod (l ^ k)) : ZMod (l ^ (k + 1)) →+* ZMod (l ^ k))
  map_add' := map_add _
  map_smul' r x := by
    change ZMod.castHom (pow_dvd_pow l k.le_succ) (ZMod (l ^ k)) (PadicInt.toZModPow (k + 1) r * (show ZMod (l ^ (k + 1)) from x)) =
      PadicInt.toZModPow k r * ZMod.castHom (pow_dvd_pow l k.le_succ) (ZMod (l ^ k)) (show ZMod (l ^ (k + 1)) from x)
    rw [map_mul, ZMod.castHom_apply, PadicInt.cast_toZModPow k (k + 1) k.le_succ]
  cont := continuous_of_discreteTopology

end Adic

def EtaleProperBaseChange : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], IsUnit (l : k) → ∀ n : ℕ,
  ∃ e : ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of k)), IsProper p →
    (GlobalTheory.Et.H ℤ_[l] n X ≃ₗ[ℤ_[l]] GlobalTheory.EtC.Hl l (GlobalTheory.EtC.sch.obj X) n 0),
  ∀ {Y X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (p' : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ X) h h'
    (x : GlobalTheory.Et.H ℤ_[l] n X),
    e Y p' h' (GlobalTheory.Et.pull ℤ_[l] n f x) = GlobalTheory.EtC.pullHl l (GlobalTheory.EtC.sch.map f) n 0 (e X p h x)

end UpperTheory.Et

end
