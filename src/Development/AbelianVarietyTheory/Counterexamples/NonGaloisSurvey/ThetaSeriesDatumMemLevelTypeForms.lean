import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.FullRankTest

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem charZero_K (i : X.Tw) : CharZero (FractionRing (X.O i)) :=
  (RingHom.charZero_iff ((IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
      (L := FractionRing (X.O i)) (X.O_inj i)).comp (X.emb0 i)).injective).1 inferInstance

theorem AO_apply (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • eG Y i j b x := by
  show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _
  rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), algebraMap_smul]

theorem thetaSeriesDatum_mem_levelTypeForms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (a : Y.Dat i j b) (ha : a ∈ E.Dat0 i j b) :
    Y.th i j b a ∈ Fm0 Y i j b := by
  simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u
  have := E.theta_base_equivariant i j b a ha u
  simp [this]

theorem theta_le_integral_forms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) {Sg : Set (Y.Dat i j b)} (h : Sg ⊆ E.Dat0 i j b) :
    Th Y i j b Sg ≤ (Fm0 Y i j b).restrictScalars (X.O i) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact thetaSeriesDatum_mem_levelTypeForms Y E i j b a (h ha)

theorem clause_two (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) {Sg : Set (Y.Dat i j b)} (h : Sg ⊆ E.Dat0 i j b) :
    ∀ x ∈ (Th Y i j b Sg).map (AO Y i j b), x ∈ V0 Y i j b := by
  rintro _ ⟨y, hy, rfl⟩
  rw [AO_apply]
  exact Submodule.smul_mem _ _ ⟨y, theta_le_integral_forms Y E i j b h hy, rfl⟩



def reSeries (Dt : ∀ (_ : X.Tw) (_ : ℕ) (_ : Bool), Type) (t : ∀ i j b, Dt i j b → Y.Fm i j b) :
    NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    Dat := Dt
    th := t
    lev := fun _ _ _ _ => ∅
    thPsi := fun i j b k _ _ d => {(1 : X.Ok i k) ⊗ₜ[X.O i] t i j b d}
    thPsi_one := fun _ _ _ _ _ => rfl
    thU := fun _ _ _ _ _ _ => 0 }

def junk : NExp D.R D.host D.what₂ D.LL0 N X :=
  reSeries Y (fun i j b => ↥(Fm0 Y i j b)) fun _ _ _ x => x.1

def junkDat : ExpDat (junk Y) where
  Dat0 _ _ _ := Set.univ
  theta_base_equivariant i j b a _ u := by
    have h := a.2
    simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker] at h
    have h' := h u
    rw [LinearMap.sub_apply, sub_eq_zero] at h'
    exact h'

theorem descent {O O' V : Type} [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O'] [Algebra O O']
    (hinj : Function.Injective (algebraMap O O')) [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (x : V) (c : O') (hc : c ≠ 0)
    (h : c • ((1 : O') ⊗ₜ[O] x) ∈ T.baseChange O') :
    x ∈ Submodule.span (FractionRing O) (T : Set V) := by
  by_contra hx
  obtain ⟨l, hl1, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  let ι : FractionRing O →+* FractionRing O' :=
    IsFractionRing.map (A := O) (B := O') (K := FractionRing O) (L := FractionRing O') hinj
  have hι : ∀ a : O, ι (algebraMap O (FractionRing O) a) = algebraMap O' (FractionRing O') (algebraMap O O' a) :=
    fun a => by simp [ι, IsFractionRing.map]
  let m : V →ₗ[O] FractionRing O' :=
    { toFun := fun v => ι (l v)
      map_add' := fun v w => by simp
      map_smul' := fun a v => by
        rw [← algebraMap_smul (FractionRing O) a v, map_smul, smul_eq_mul, map_mul, hι, RingHom.id_apply,
          ← algebraMap_smul O' a, Algebra.smul_def] }
  let M : O' ⊗[O] V →ₗ[O'] FractionRing O' := m.liftBaseChange O'
  have hT : T.baseChange O' ≤ LinearMap.ker M := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have : l v = 0 := by
      have : l v ∈ (Submodule.span (FractionRing O) (T : Set V)).map l := ⟨v, Submodule.subset_span hv, rfl⟩
      rwa [hl0, Submodule.mem_bot] at this
    show M ((1 : O') ⊗ₜ[O] v) = 0
    simp [M, m, this]
  have h0 := hT h
  rw [LinearMap.mem_ker, map_smul] at h0
  have h1 : M ((1 : O') ⊗ₜ[O] x) = ι (l x) := by simp [M, m]
  rw [h1, Algebra.smul_def, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hc ((IsFractionRing.injective O' (FractionRing O')) (by simpa using h0))
  · exact hl1 (ι.injective (by simpa using h0))

end GlobalTheory.FullRankTest

end
