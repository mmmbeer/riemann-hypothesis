import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {fc : DefSub A → DefFace Bs}

structure RefInputs (X : CxData A) (cr : Crd A fc) : Prop where

  M_lat : ∀ j, Submodule.IsLattice K (X.M false j)

  T_lat : ∀ j, Submodule.IsLattice K ((lv (fc X.zs) false).Tl j Bs.μ0)

  form_nondeg : ∀ j, ((lv (fc X.zs) false).HT j Bs.μ0).det ≠ 0

  w_inj : ∀ j, Function.Injective (X.w0C false j)

  theta_inj : ∀ j, Function.Injective (X.tC cr false j Bs.μ0)

  theta_range : ∀ j, LinearMap.range (X.tC cr false j Bs.μ0) = LinearMap.range (X.w0C false j)

  theta_rat : ∀ j, IsRat Bs.v0.embedding (X.liftMatC cr false j Bs.μ0)

def retuple (X : CxData A) (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup) (Tw : Finset (HeightOneSpectrum (𝓞 K))) : CxData A :=
  { X with μ := μ, Tw := Tw }

def TwistChoice (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (tw : HeightOneSpectrum (𝓞 K) → Bs.Tup) : Prop :=
  (∀ w, X.W1 cr N w → tw w ≠ Bs.μ0) ∧ ∀ w, X.W1 cr N w → tw (conjPl w) = tw w

def FiveSet (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ j, (X.data cr false).Iw j Bs.μ0 w ≠ 0 ∨ (X.data cr false).Iw j Bs.μ0 (conjPl w) ≠ 0 ∨
    jw ((lv (fc X.zs) false).HT j Bs.μ0) w ((lv (fc X.zs) false).Tl j Bs.μ0) ≠ 0 ∨ N.F0 w j ≠ 0 ∨ N.F0 (conjPl w) j ≠ 0



namespace Examples₂

variable (K) (v0 : InfinitePlace K)

def base : DefBase K := ⟨⊤, v0, Bool, false, Unit, inferInstance, Unit, inferInstance⟩

def stdLat : Submodule (𝓞 K) (Fin 1 → K) := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin 1)))

omit [StarRing K] in
theorem stdLat_isLattice : Submodule.IsLattice K (stdLat K) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin 1)).span_eq]
    exact Submodule.span_mono Submodule.subset_span

def amb : DefAmb (base K v0) :=
  ⟨fun _ => K, fun _ => inferInstance, fun _ => inferInstance, fun _ => Unit, fun _ _ => 1, fun _ => ⊤,
    fun _ _ => K, fun _ _ => inferInstance, fun _ _ => inferInstance, fun _ _ => Unit, fun _ _ _ => 1, fun _ _ => ⊤⟩

def side : DefSide (base K v0) :=
  ⟨fun _ => 1, fun _ => 1, fun _ => stdLat K, fun _ => 1, fun _ => 1, fun _ _ => 1, fun _ _ => ⊤,
    fun _ _ => 1, fun _ _ => 2, fun _ _ _ => 1, fun _ _ => stdLat K, fun _ _ _ => ⊤⟩

def face : DefSub (amb K v0) → DefFace (base K v0) := fun _ =>
  ⟨side K v0, side K v0, ⟨Empty, fun _ => 0, fun u => u.elim, fun u => u.elim⟩,
    ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊤⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

def crd : Crd (amb K v0) (face K v0) where
  toR _ b _ := match b with
    | false => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
    | true => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
  toL _ b _ _ := match b with
    | false => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
    | true => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)

def cx : CxData (amb K v0) where
  FC _ := ℂ
  jR _ := v0.embedding.toSemilinearMap
  EE := ℂ
  Θ _ := LinearMap.id
  EEp _ := ⊤
  EEl _ := ⊤
  FLC _ _ := ℂ
  jL _ _ := v0.embedding.toSemilinearMap
  W _ := ℂ
  θ' _ _ := LinearMap.id
  Wp _ _ := ⊤
  dW _ _ := 1
  WC _ _ _ := ℂ
  bW _ _ _ _ := 1
  eW _ _ := LinearMap.id
  M _ _ := stdLat K
  nP _ := 1
  μ _ := false
  Tw := ∅
  κ _ := 1
  lam _ _ _ _ := 1
  err0 _ _ := 0



theorem tC_eq (j : Unit) : (cx K v0).tC (crd K v0) false j false = lin (fun _ : Fin 1 => (1 : ℂ)) := by
  change lin (fun k : Fin 1 => v0.embedding ((Pi.single k (1 : K) : Fin 1 → K) 0)) = _
  congr 1
  funext k
  fin_cases k
  simp


end Examples₂

end GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample
