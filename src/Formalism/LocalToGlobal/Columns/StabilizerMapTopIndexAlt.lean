import Formalism.LocalToGlobal.Columns.RecChainYUnfPol
import Mathlib
import Formalism.LocalToGlobal.Columns.GFamEv
import Formalism.LocalToGlobal.Columns.FiniteDimensionalForms
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.LocalToGlobal.Columns.DecoratedFrameDiagonalTwistDecoration
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
import Formalism.LocalToGlobal.Columns.WithTopLevGTop
import Formalism.LocalToGlobal.Columns.StabMapRLInjective

section
noncomputable section

namespace Formalism.L2.Col

structure GFamS (K : Type) [Field K] [NumberField K] [StarRing K] extends GFam K where

  sec : ∀ b, (toGFam.mem b).Sec

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

namespace GFamS

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFamS K)

@[reducible] def toCSD (h : F.Ok) : CSD K := F.toCSDOf h F.sec

abbrev outSec : ∀ b, (F.mem b).Sec := fun b => (F.sec b)

abbrev rep (c : F.Cl) : F.D c.1 := (F.sec c.1).rep c.2

def valAt (φ : F.Forms) (c : F.Cl) : F.V := ((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) (F.rep c)

def res (h : F.Ok) : F.Forms ≃ₗ[K] (F.toCSD h).Forms := F.resOf h F.outSec

def gramV : Matrix F.ιV F.ιV K := Matrix.of fun i j => F.pair (F.bV i) (F.bV j)

def pairAt (v : InfinitePlace K) (x y : F.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (F.bV.repr x i)) * v.embedding (F.gramV i j) * v.embedding (F.bV.repr y j)

def ipAt (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) : ℂ :=
  letI : Fintype F.Cl := h.fintypeCl
  ∑ c : F.Cl, (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ * F.pairAt v (F.valAt φ c) (F.valAt ψ c)

structure Rat : Prop where
  pair_rat : ∀ i j, F.gramV i j ∈ cmMax K
  act_rat : ∀ (b : F.β) (g : F.G b) i j, F.bV.repr (F.ρ b g (F.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef

def Free : Prop := ∀ b, (F.mem b).Free

abbrev hDim (h : F.Ok) : ℕ := (F.toCSD h).dim

def hB (h : F.Ok) : Basis (Fin (F.hDim h)) K F.Forms := (F.toCSD h).basis.map (F.res h).symm

abbrev hGram (h : F.Ok) : Matrix (Fin (F.hDim h)) (Fin (F.hDim h)) K := (F.toCSD h).H

def PosH (h : F.Ok) : Prop := ∀ v : InfinitePlace K, ((F.hGram h).map v.embedding).PosDef

@[reducible] def toH (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : HLat K where
  V := F.Forms
  ι := Fin (F.hDim h)
  b := F.hB h
  X := stdFrame (F.hGram h)
  L := L

abbrev hCoord (h : F.Ok) : F.Forms ≃ₗ[K] (Fin (F.hDim h) → K) := F.coordOf h F.outSec

def toHc (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : HLat K :=
  toHLat (stdFrame (F.hGram h)) (L.map ((F.hCoord h).toLinearMap.restrictScalars (𝓞 K)))

def subZ (h : F.Ok) (U : Submodule K F.Forms) : Submodule K (Fin (F.hDim h) → K) :=
  U.map (F.hCoord h).toLinearMap

def subEq (h : F.Ok) (U : Submodule K F.Forms) : U ≃ₗ[K] F.subZ h U := (F.hCoord h).submoduleMap U

abbrev subD (h : F.Ok) (U : Submodule K F.Forms) : ℕ := subDim (F.subZ h U)

def subB (h : F.Ok) (U : Submodule K F.Forms) : Basis (Fin (F.subD h U)) K U :=
  (subBasis (F.subZ h U)).map (F.subEq h U).symm

def subMat (h : F.Ok) (U : Submodule K F.Forms) : Matrix (Fin (F.hDim h)) (Fin (F.subD h U)) K :=
  subE (F.subZ h U)

@[reducible] def subH (h : F.Ok) (U : Submodule K F.Forms) (L : Submodule (𝓞 K) U) : HLat K where
  V := U
  ι := Fin (F.subD h U)
  b := F.subB h U
  X := restrFrame (F.subMat h U) (F.hGram h)
  L := L

theorem wt_eq_card (h : F.Ok) (c : F.Cl) :
    (F.toCSD h).wt c = Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) :=
  (F.mem c.1).wt_eq (h c.1) (F.sec c.1) c.2

variable {F} in
theorem Rat.mem (R : F.Rat) (b : F.β) : (F.mem b).Rat := ⟨R.pair_rat, R.act_rat b, R.pos⟩

theorem Rat.of_mem [Nonempty F.β] (R : ∀ b, (F.mem b).Rat) : F.Rat :=
  ⟨(R (Classical.arbitrary F.β)).pair_rat, fun b => (R b).act_rat, (R (Classical.arbitrary F.β)).pos⟩

variable {F} in
theorem Rat.toCSDOf (R : F.Rat) (h : F.Ok) (s : ∀ b, (F.mem b).Sec) : (F.toCSDOf h s).Rat where
  pair_rat := R.pair_rat
  act_rat := fun c γ i j => R.act_rat c.1 (γ : F.G c.1) i j
  pos := R.pos

theorem hB_equivFun (h : F.Ok) (φ : F.Forms) : (F.hB h).equivFun φ = F.hCoord h φ := by
  funext i
  simp [hB, GFam.coordOf, res]

theorem hB_apply (h : F.Ok) (i : Fin (F.hDim h)) : F.res h (F.hB h i) = (F.toCSD h).basis i := by
  simp [hB]

theorem subB_equivFun (h : F.Ok) (U : Submodule K F.Forms) (x : U) :
    (F.subMat h U).mulVec ((F.subB h U).equivFun x) = F.hCoord h (x : F.Forms) := by
  unfold subMat
  rw [subE_mulVec]
  have : (F.subB h U).equivFun x = (subBasis (F.subZ h U)).equivFun (F.subEq h U x) := by
    funext i
    simp [subB]
  rw [this, LinearEquiv.symm_apply_apply]
  rfl

theorem subMat_injective (h : F.Ok) (U : Submodule K F.Forms) : Function.Injective (F.subMat h U).mulVec :=
  (subspace_image_spec K _ (F.subZ h U)).1

variable {F}

theorem PosH.frameOK {h : F.Ok} (hp : F.PosH h) (L : Submodule (𝓞 K) F.Forms) : FrameOK (F.toH h L) :=
  fun v => (frameOfSpec _ _ (hp v)).1

theorem PosH.met {h : F.Ok} (hp : F.PosH h) (v : InfinitePlace K) :
    metOf (stdFrame (F.hGram h) v) = (F.hGram h).map v.embedding := (frameOfSpec _ _ (hp v)).2

theorem PosH.sub_maj {h : F.Ok} (hp : F.PosH h) (U : Submodule K F.Forms) (v : InfinitePlace K) (x y : U) :
    majAt (F.subB h U) (restrFrame (F.subMat h U) (F.hGram h)) v x y =
      majAt (F.hB h) (stdFrame (F.hGram h)) v (x : F.Forms) (y : F.Forms) := by
  rw [thl_majAt_coord (F.subB h U), thl_majAt_coord (F.hB h),
    (restrFrameSpec K _ _ (F.hGram h) hp (F.subMat h U) (F.subMat_injective h U) v).2.2,
    subB_equivFun, subB_equivFun, hB_equivFun, hB_equivFun]

theorem PosH.sub_norm {h : F.Ok} (hp : F.PosH h) (U : Submodule K F.Forms) (v : InfinitePlace K) (x : U) :
    normAt (F.subB h U) (restrFrame (F.subMat h U) (F.hGram h)) v x =
      normAt (F.hB h) (stdFrame (F.hGram h)) v (x : F.Forms) := by
  rw [normAt_eq_sqrt, normAt_eq_sqrt, hp.sub_maj]

variable (F)

def isoHc (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (F.toH h L) (F.toHc h L) where
  e := F.hCoord h
  map_L := rfl
  norm := fun v x => by
    show normAt (Pi.basisFun K (Fin (F.hDim h))) (stdFrame (F.hGram h)) v (F.hCoord h x) =
      normAt (F.hB h) (stdFrame (F.hGram h)) v x
    rw [thl_normAt_coord (F.hB h), hB_equivFun]

variable {F}

theorem PosH.good {h : F.Ok} (hp : F.PosH h) {L : Submodule (𝓞 K) F.Forms} (hL : Submodule.IsLattice K L) :
    (F.toH h L).Good := ⟨hp.frameOK L, hL.fg, hL.span_eq_top⟩

theorem PosH.iso_sub {h : F.Ok} (hp : F.PosH h) (L : Submodule (𝓞 K) F.Forms) (U : Submodule K F.Forms) :
    ∃ I : Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (F.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))) (sub (F.toH h L) U),
      ∀ x : U, (I.e x : U) = x := by
  obtain ⟨I, hI⟩ := embIso' (F.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))) (F.toH h L) U.subtype U
    (hp.frameOK L) (Submodule.injective_subtype U) (Submodule.range_subtype U) (fun v x => hp.sub_norm U v x) rfl
  exact ⟨I, fun x => Subtype.ext (hI x)⟩

variable (F)

theorem pairAt_add_left (v : InfinitePlace K) (x x' y : F.V) :
    F.pairAt v (x + x') y = F.pairAt v x y + F.pairAt v x' y := by
  simp only [pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (v : InfinitePlace K) (x y y' : F.V) :
    F.pairAt v x (y + y') = F.pairAt v x y + F.pairAt v x y' := by
  simp only [pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (v : InfinitePlace K) (a : K) (x y : F.V) :
    F.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * F.pairAt v x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (v : InfinitePlace K) (a : K) (x y : F.V) :
    F.pairAt v x (a • y) = v.embedding a * F.pairAt v x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem valAt_add (φ ψ : F.Forms) (c : F.Cl) : F.valAt (φ + ψ) c = F.valAt φ c + F.valAt ψ c := rfl

theorem valAt_smul (a : K) (φ : F.Forms) (c : F.Cl) : F.valAt (a • φ) c = a • F.valAt φ c := rfl

theorem isSesq_ipAt (h : F.Ok) : IsSesq (fun v (φ ψ : F.Forms) => F.ipAt h v φ ψ) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [ipAt, valAt_add, pairAt_add_left, mul_add, Finset.sum_add_distrib]
  · simp only [ipAt, valAt_add, pairAt_add_right, mul_add, Finset.sum_add_distrib]
  · simp only [ipAt, valAt_smul, pairAt_smul_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · simp only [ipAt, valAt_smul, pairAt_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

def evRep (h : F.Ok) : F.Forms →ₗ[K] (F.Cl → F.V) := (F.toCSD h).Forms.subtype ∘ₗ (F.res h).toLinearMap

theorem evRep_apply (h : F.Ok) (φ : F.Forms) (c : F.Cl) : F.evRep h φ c = F.valAt φ c := rfl

theorem evRep_injective (h : F.Ok) : Function.Injective (F.evRep h) :=
  (Submodule.injective_subtype _).comp (F.res h).injective

theorem posAt_ipAt (h : F.Ok) (hpos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K F.Forms) :
    PosAt b (fun v (φ ψ : F.Forms) => F.ipAt h v φ ψ) := by
  classical
  intro v
  let _ : Fintype F.Cl := h.fintypeCl
  let P : F.Cl → Matrix F.ιV ι ℂ := fun c => Matrix.of fun i a => v.embedding (F.bV.repr (F.evRep h (b a) c) i)
  have hgram : gramOf b (fun (φ ψ : F.Forms) => F.ipAt h v φ ψ) =
      ∑ c, (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ • ((P c)ᴴ * F.gramV.map v.embedding * P c) := by
    ext a a'
    simp only [gramOf, Matrix.of_apply, ipAt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp only [pairAt, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, P, Matrix.of_apply,
      Matrix.map_apply, evRep_apply]
    rw [Finset.sum_comm]
    rfl
  rw [hgram]
  refine thl_posDef_sum _ (fun c => ?_) _ (hpos v) P fun x hx => ?_
  · have : (0 : ℝ) < (((F.toCSD h).wt c : ℕ) : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (F.toCSD h).wt_pos c)
    have h2 : ((((F.toCSD h).wt c : ℕ) : ℝ)⁻¹ : ℂ) = (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ := by push_cast; rfl
    rw [← h2]
    exact_mod_cast this
  · let Bb : Basis (Σ _ : F.Cl, F.ιV) K (F.Cl → F.V) := Pi.basis fun _ => F.bV
    obtain ⟨g, hg⟩ := (F.evRep h).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (F.evRep_injective h))
    have h1 : (LinearMap.toMatrix Bb b g).map v.embedding * (LinearMap.toMatrix b Bb (F.evRep h)).map v.embedding = 1 := by
      rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
      simp
    have h2 : (LinearMap.toMatrix b Bb (F.evRep h)).map v.embedding *ᵥ x = 0 := by
      funext ⟨c, i⟩
      have := congrFun (hx c) i
      simpa [Matrix.mulVec, dotProduct, P, LinearMap.toMatrix_apply, Bb, Pi.basis_repr] using this
    have h3 := congrArg ((LinearMap.toMatrix Bb b g).map v.embedding).mulVec h2
    simpa [Matrix.mulVec_mulVec, h1] using h3

theorem pairAt_of_rat (v : InfinitePlace K) (x y : F.V) (hx : ∀ i, F.bV.repr x i ∈ cmMax K) :
    v.embedding (F.pair x y) = F.pairAt v x y := by
  conv_lhs => rw [← F.bV.sum_repr x, ← F.bV.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, pairAt,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : v.embedding ((starRingEnd K) (F.bV.repr x i)) = starRingEnd ℂ (v.embedding (F.bV.repr x i)) :=
    hx i v.embedding
  rw [h1, RingHom.id_apply]
  simp only [gramV, Matrix.of_apply]
  ring

theorem gram_ipAt (h : F.Ok) (hr : (F.toCSD h).HasRatBasis) (v : InfinitePlace K) :
    gramOf (F.hB h) (fun (φ ψ : F.Forms) => F.ipAt h v φ ψ) = (F.hGram h).map v.embedding := by
  ext a a'
  simp only [gramOf, Matrix.of_apply, ipAt, Matrix.map_apply, CSD.H, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have e : ∀ a, F.valAt (F.hB h a) c = ((F.toCSD h).basis a : F.Cl → F.V) c := by
    intro a
    rw [← F.hB_apply h a]
    rfl
  rw [e, e]
  exact (F.pairAt_of_rat v _ _ fun i => (F.toCSD h).basis_rat hr a c i).symm

variable {F}

theorem Rat.posH (R : F.Rat) (h : F.Ok) : F.PosH h := by
  intro v
  rw [← F.gram_ipAt h (csd_hasRatBasis _ (R.toCSDOf h F.outSec)) v]
  exact F.posAt_ipAt h R.pos (F.hB h) v

theorem Rat.maj_eq (R : F.Rat) (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) :
    majAt (F.hB h) (stdFrame (F.hGram h)) v φ ψ = F.ipAt h v φ ψ := by
  rw [sesq_eq_sum (isSesq_maj (F.hB h) (stdFrame (F.hGram h))) (F.hB h) v φ ψ,
    sesq_eq_sum (F.isSesq_ipAt h) (F.hB h) v φ ψ, gramOf_maj,
    F.gram_ipAt h (csd_hasRatBasis _ (R.toCSDOf h F.outSec)) v]
  have := (R.posH h).met v
  unfold metOf at this
  rw [this]

end GFamS

namespace GFamS

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFamS K)

def intOf (N : ∀ b, F.D b → Submodule (𝓞 K) F.V) : Submodule (𝓞 K) F.Forms :=
  Submodule.pi Set.univ fun b => (F.mem b).intOf (N b)

@[reducible] def withDel (N : ∀ b, F.D b → Submodule (𝓞 K) F.V) : GFamS K :=
  { toGFam := { F.toGFam with Del := N }, sec := fun b => { rep := (F.sec b).rep, spec := (F.sec b).spec } }

end GFamS

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

namespace GFamS

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev Pt (F : GFamS K) : Type := Σ b, F.D b

def cls (F : GFamS K) (p : F.Pt) : F.Cl := ⟨p.1, (F.mem p.1).cls p.2⟩

def repPt (F : GFamS K) (c : F.Cl) : F.Pt := ⟨c.1, F.rep c⟩


structure Ev (F : GFamS K) (σ : K →+* ℂ) where

  Y : Type

  ev : F.V →ₛₗ[σ] (Y → ℂ)
  li : LinearIndependent ℂ fun i => ev (F.bV i)

  ip : (Y → ℂ) →ₗ⋆[ℂ] (Y → ℂ) →ₗ[ℂ] ℂ
  ip_ev : ∀ x y, ip (ev x) (ev y) = σ (F.pair x y)

  tr : ∀ b, F.G b →* ((Y → ℂ) ≃ₗ[ℂ] (Y → ℂ))
  tr_ev : ∀ b g x, tr b g (ev x) = ev (F.ρ b g x)

namespace Ev

variable {F : GFamS K} {σ : K →+* ℂ} (E : F.Ev σ)

@[reducible] def mem (b : F.β) : (F.mem b).Ev σ where
  Y := E.Y
  ev := E.ev
  li := E.li
  ip := E.ip
  ip_ev := E.ip_ev
  tr := E.tr b
  tr_ev := E.tr_ev b

theorem mem_Y (b : F.β) : (E.mem b).Y = E.Y := rfl

@[reducible] def ofMem {b₀ : F.β} (E₀ : (F.mem b₀).Ev σ) (tr : ∀ b, F.G b →* ((E₀.Y → ℂ) ≃ₗ[ℂ] (E₀.Y → ℂ)))
    (tr_ev : ∀ b g x, tr b g (E₀.ev x) = E₀.ev (F.ρ b g x)) : F.Ev σ where
  Y := E₀.Y
  ev := E₀.ev
  li := E₀.li
  ip := E₀.ip
  ip_ev := E₀.ip_ev
  tr := tr
  tr_ev := tr_ev

def evCl : (F.Cl → F.V) →ₛₗ[σ] (F.Cl → E.Y → ℂ) where
  toFun f := fun c => E.ev (f c)
  map_add' f g := by funext c; exact map_add E.ev _ _
  map_smul' a f := by funext c; exact LinearMap.map_smulₛₗ E.ev _ _

def emb : F.Forms →ₛₗ[σ] (F.Cl → E.Y → ℂ) where
  toFun φ := fun c => E.ev (F.valAt φ c)
  map_add' φ ψ := by funext c; exact map_add E.ev _ _
  map_smul' a φ := by funext c; exact LinearMap.map_smulₛₗ E.ev _ _

theorem emb_apply (φ : F.Forms) (c : F.Cl) :
    E.emb φ c = E.ev (((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) ((F.sec c.1).rep c.2)) := rfl

theorem emb_valAt (φ : F.Forms) (c : F.Cl) : E.emb φ c = E.ev (F.valAt φ c) := rfl

def part (b : F.β) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] ((F.mem b).Cl → E.Y → ℂ) :=
  LinearMap.pi fun c => LinearMap.proj (⟨b, c⟩ : F.Cl)

def trPt (p : F.Pt) : (E.Y → ℂ) ≃ₗ[ℂ] (E.Y → ℂ) := E.tr p.1 ((F.sec p.1).mv p.2)

def atPt (p : F.Pt) (Φ : F.Cl → E.Y → ℂ) : E.Y → ℂ := E.trPt p (Φ (F.cls p))

theorem atPt_emb (φ : F.Forms) (p : F.Pt) :
    E.atPt p (E.emb φ) = E.ev (((φ p.1 : (F.mem p.1).EqFun) : F.D p.1 → F.V) p.2) := by
  unfold atPt trPt
  rw [emb_apply, E.tr_ev]
  show E.ev (F.ρ p.1 ((F.sec p.1).mv p.2) (((φ p.1 : (F.mem p.1).EqFun) : F.D p.1 → F.V) ((F.sec p.1).rep ((F.mem p.1).cls p.2)))) = _
  rw [← (φ p.1).2, (F.sec p.1).mv_smul]

theorem atPt_eq (hf : F.Free) (Φ : F.Cl → E.Y → ℂ) (b : F.β) (d : F.D b) (c : (F.mem b).Cl) (g : F.G b)
    (h : g • (F.sec b).rep c = d) : E.atPt ⟨b, d⟩ Φ = E.tr b g (Φ ⟨b, c⟩) := by
  have hc : (F.mem b).cls d = c := by rw [← h, (F.mem b).cls_smul, (F.sec b).spec]
  subst hc
  have h1 : (F.sec b).mv d = g := by
    have h2 : (g⁻¹ * (F.sec b).mv d) • (F.sec b).rep ((F.mem b).cls d) = (F.sec b).rep ((F.mem b).cls d) := by
      rw [mul_smul, (F.sec b).mv_smul]
      conv_lhs => rw [← h]
      rw [inv_smul_smul]
    have h3 := hf b _ _ h2
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  show E.tr b ((F.sec b).mv d) (Φ ⟨b, (F.mem b).cls d⟩) = _
  rw [h1]

def opOn (δ : F.Pt → F.Pt) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (F.Cl → E.Y → ℂ) where
  toFun Φ := fun c => E.atPt (δ (F.repPt c)) Φ
  map_add' Φ Ψ := by funext c; exact map_add (E.trPt _) _ _
  map_smul' a Φ := by funext c; exact map_smul (E.trPt _) _ _


theorem opOn_id (hf : F.Free) : E.opOn (fun p => p) = LinearMap.id := by
  ext Φ c : 2
  obtain ⟨b, c⟩ := c
  show E.atPt ⟨b, (F.sec b).rep c⟩ Φ = Φ ⟨b, c⟩
  rw [E.atPt_eq hf Φ b _ c 1 (one_smul _ _), map_one]
  rfl

theorem opOn_comp (hf : F.Free) (δ δ' : F.Pt → F.Pt)
    (hδ' : ∀ (b : F.β) (g : F.G b) (d : F.D b), ∃ g' : F.G (δ' ⟨b, d⟩).1,
      δ' ⟨b, g • d⟩ = ⟨(δ' ⟨b, d⟩).1, g' • (δ' ⟨b, d⟩).2⟩ ∧ E.tr _ g' = E.tr b g) :
    E.opOn δ ∘ₗ E.opOn δ' = E.opOn fun p => δ' (δ p) := by
  ext Φ c : 2
  show E.trPt (δ (F.repPt c)) (E.atPt (δ' (F.repPt (F.cls (δ (F.repPt c))))) Φ) = E.atPt (δ' (δ (F.repPt c))) Φ
  generalize δ (F.repPt c) = p
  obtain ⟨b, d⟩ := p
  obtain ⟨g', h1, h2⟩ := hδ' b ((F.sec b).mv d) ((F.sec b).rep ((F.mem b).cls d))
  rw [(F.sec b).mv_smul d] at h1
  rw [h1]
  show E.tr b ((F.sec b).mv d) (E.atPt (δ' ⟨b, (F.sec b).rep ((F.mem b).cls d)⟩) Φ) = _
  generalize δ' ⟨b, (F.sec b).rep ((F.mem b).cls d)⟩ = q at g' h2
  obtain ⟨b', d'⟩ := q
  rw [E.atPt_eq hf Φ b' (g' • d') ((F.mem b').cls d') (g' * (F.sec b').mv d')
    (by rw [mul_smul, (F.sec b').mv_smul]), map_mul, h2]
  rfl

def opOnC (δ : ∀ b, F.D b → F.D b) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (F.Cl → E.Y → ℂ) := E.opOn fun p => ⟨p.1, δ p.1 p.2⟩





def lin : (F.ιV → ℂ) →ₗ[ℂ] (E.Y → ℂ) := Fintype.linearCombination ℂ fun i => E.ev (F.bV i)

theorem ev_eq_lin (x : F.V) : E.ev x = E.lin fun i => σ (F.bV.repr x i) := by
  conv_lhs => rw [← F.bV.sum_repr x]
  rw [map_sum, lin, Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ E.ev _ _

theorem lin_ker : LinearMap.ker E.lin = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact E.li.fintypeLinearCombination_injective

def gram : Matrix F.ιV F.ιV ℂ := Matrix.of fun i j => E.ip (E.ev (F.bV i)) (E.ev (F.bV j))

def ipB : (E.Y → ℂ) →ₗ[ℂ] (F.ιV → ℂ) := LinearMap.pi fun j => E.ip (E.ev (F.bV j))

open Classical in

def co : (E.Y → ℂ) →ₗ[ℂ] (F.ιV → ℂ) :=
  if IsUnit E.gram.det then Matrix.toLin' E.gram⁻¹ ∘ₗ E.ipB
  else (E.lin.exists_leftInverse_of_injective E.lin_ker).choose

def extend {M : Type} [AddCommGroup M] [Module ℂ M] (ℓ : F.V →ₛₗ[σ] M) : (E.Y → ℂ) →ₗ[ℂ] M :=
  (Fintype.linearCombination ℂ fun i => ℓ (F.bV i)) ∘ₗ E.co

def sharp (ℓ : F.V →ₛₗ[σ] ℂ) : E.Y → ℂ :=
  ∑ j, starRingEnd ℂ (∑ i, ℓ (F.bV i) * E.gram⁻¹ i j) • E.ev (F.bV j)

theorem ipB_lin (z : F.ιV → ℂ) : E.ipB (E.lin z) = E.gram *ᵥ z := by
  funext j
  simp only [ipB, LinearMap.pi_apply, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smul, smul_eq_mul,
    Matrix.mulVec, dotProduct, gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem co_lin (z : F.ιV → ℂ) : E.co (E.lin z) = z := by
  unfold co
  split_ifs with hG
  · rw [LinearMap.comp_apply, ipB_lin, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG,
      Matrix.one_mulVec]
  · exact LinearMap.congr_fun (E.lin.exists_leftInverse_of_injective E.lin_ker).choose_spec z

theorem extend_ev {M : Type} [AddCommGroup M] [Module ℂ M] (ℓ : F.V →ₛₗ[σ] M) (x : F.V) : E.extend ℓ (E.ev x) = ℓ x := by
  rw [extend, LinearMap.comp_apply, ev_eq_lin, co_lin, Fintype.linearCombination_apply]
  conv_rhs => rw [← F.bV.sum_repr x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (LinearMap.map_smulₛₗ ℓ _ _).symm

def ipCl (h : F.Ok) : (F.Cl → E.Y → ℂ) →ₗ⋆[ℂ] (F.Cl → E.Y → ℂ) →ₗ[ℂ] ℂ :=
  letI := h.fintypeCl
  ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ •
    ((E.ip.comp (LinearMap.proj c)).compl₂ (LinearMap.proj c))

theorem ipCl_apply (h : F.Ok) (Φ Ψ : F.Cl → E.Y → ℂ) :
    E.ipCl h Φ Ψ = (letI := h.fintypeCl
      ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ * E.ip (Φ c) (Ψ c)) := by
  unfold ipCl
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    smul_eq_mul]

def Fi : Submodule ℂ (F.Cl → E.Y → ℂ) := Submodule.span ℂ (Set.range E.emb)

def evAt {ι : Type} (pts : ι → F.Pt) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (ι → E.Y → ℂ) :=
  LinearMap.pi fun i => (E.trPt (pts i)).toLinearMap ∘ₗ LinearMap.proj (F.cls (pts i))

def perCl (h : F.Ok) {ι : Type} [Fintype ι] (ℓ : F.Cl → ι → (F.V →ₛₗ[σ] ℂ)) :
    (F.Cl → E.Y → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ :=
  letI := h.fintypeCl
  LinearMap.mk₂ ℂ (fun Φ z => ∑ c : F.Cl,
      ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ * ∑ a, z a * E.extend (ℓ c a) (Φ c))
    (fun Φ Φ' z => by simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun a Φ z => by
      simp only [Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      ring)
    (fun Φ z z' => by simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib])
    (fun a Φ z => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      ring)



theorem norm_eq (h : F.Ok) (R : F.Rat) (hσ : ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) (φ : F.Forms) :
    (majAt (F.hB h) (stdFrame (F.hGram h)) (InfinitePlace.mk σ) φ φ).re =
      (letI := h.fintypeCl
       ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ *
        E.ip (E.emb φ c) (E.emb φ c)).re := by
  let _ := h.fintypeCl
  rw [R.maj_eq h]
  unfold ipAt
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [F.wt_eq_card h c, emb_valAt, E.ip_ev]
  rcases (F.mem c.1).pairAt_mk σ hσ with hp | hp
  · exact congrArg (fun z : ℂ => (((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ * z).re) (hp _ _)
  · have e : F.pairAt (InfinitePlace.mk σ) (F.valAt φ c) (F.valAt φ c) = starRingEnd ℂ (σ (F.pair (F.valAt φ c) (F.valAt φ c))) := hp _ _
    rw [e, ← Complex.conj_re]
    congr 1
    simp only [map_mul, map_inv₀, map_natCast, Complex.conj_conj]

theorem norm_ipCl (h : F.Ok) (R : F.Rat) (hσ : ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) (φ : F.Forms) :
    (majAt (F.hB h) (stdFrame (F.hGram h)) (InfinitePlace.mk σ) φ φ).re = (E.ipCl h (E.emb φ) (E.emb φ)).re := by
  rw [ipCl_apply]
  exact E.norm_eq h R hσ φ

end Ev

end GFamS

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Fam

variable {X : Fields} {R : Ranks}

abbrev FamStabS (F : GFamS X.K) (c : F.Cl) : Type := MulAction.stabilizer (F.G c.1) ((F.sec c.1).rep c.2)

def recChainFS (hc : X.Tau → HCParam R) (F : ℕ → GFamS X.K) (hF : ∀ j, (F j).Ok) (σ₀ : X.K →+* ℂ)
    (D : ℕ) (hD : 0 < D) (hdvd : ∀ j, j ≤ R.m → ∀ c : (F j).Cl, Nat.card (FamStabS (F j) c) ∣ D)
    (A : ChainArgF R (fun i => (F i).toGFam) σ₀) : ColumnChain R X.Tau hc where
  cls := fun i => (F i).Cl
  clsFin := fun i => (hF i).fintypeCl
  stab := fun i c => FamStabS (F i) c
  stabGrp := fun _ _ => inferInstance
  stabFin := fun i c => (hF i c.1).fin_stab _
  DGam := D
  DGam_pos := hD
  dvd_DGam := hdvd
  Y := fun i => FrS X σ₀ (R.N i)
  de := fun _ y τ => deFr y τ
  de_ne := fun _ y τ => (y.2 τ).ne_zero
  rhoDet := A.rhoDet
  rhoDet' := A.rhoDet'
  rho_norm := A.rho_norm
  rho'_norm := A.rho'_norm
  unf := A.unf
  sSharp := sSharpH hc
  sSharp_eq := fun i h τ => by
    obtain ⟨a, ha⟩ := (rec_sInt R (hc τ) ⟨i, h⟩).2
    have e : (RowPar.of (hc τ)).eAt i = (hc τ).e ⟨i, h⟩ := by
      unfold RowPar.eAt
      rw [dif_pos h]
      rfl
    unfold sSharpH
    rw [e]
    simp only at ha
    rw [ha, Int.floor_intCast]
  sDiv := sDivH hc
  sDiv_eq := fun i h τ => by
    obtain ⟨a, ha⟩ := (rec_sInt R (hc τ) ⟨i, h⟩).1
    have e : (RowPar.of (hc τ)).eAt i = (hc τ).e ⟨i, h⟩ := by
      unfold RowPar.eAt
      rw [dif_pos h]
      rfl
    unfold sDivH
    rw [e]
    simp only at ha
    rw [ha, Int.floor_intCast]

end Fam

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker Formalism.L2.Col

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev SecY (u : Pr.Word) (m2 : ℕ) : Type := ∀ j b, ((Formalism.L2.Col.chFY W sel mu cst L u m2 j).mem b).Sec

@[reducible] def chFY (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) (j : ℕ) : GFamS X.K :=
  { toGFam := Formalism.L2.Col.chFY W sel mu cst L u m2 j, sec := sec j }

variable {W sel mu cst L}

def ptYc {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} {j : ℕ} (c : (chFY W sel mu cst L u m2 sec j).Cl) : ChPt (R := R) sel mu u j :=
  (((chFY W sel mu cst L u m2 sec j).sec c.1).rep c.2).1.1

def ybY {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} {j : ℕ} (c : (chFY W sel mu cst L u m2 sec j).Cl) : Set (Sp X.E (R.N j)) :=
  (((chFY W sel mu cst L u m2 sec j).sec c.1).rep c.2).1.2

def XiY {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl)
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if i < m2 then XiEntry Ch sel mu cst L i c.1 c'.1 (ptYc c) (ptYc c') x
  else if i = m2 then XiCpl1 Ch sel mu cst L i c.1 (ptYc c) (ptYc c') (ybY c') x
  else if i = m2 + 1 then XiTop Ch sel mu cst i (ptYc c) (ybY c) (ptYc c') x
  else 0

def thY (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl) :
    VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ :=
  Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (ptYc c).deco.1.N (ptYc c').deco.1.N (XiY Ch i c c')

def rhoY (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) : ℂ :=
  σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c).deco.1.N (frsF sel mu (ptYc c))) *
    (Am.chiF (R.N i) (R.N (i + 1)) (ptYc c).deco.1.N (stdLat X.E (R.N (i + 1))))⁻¹

def rhoY' (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl) : ℂ :=
  (σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c').deco.1.N (frsF sel mu (ptYc c'))))⁻¹ *
    (Am.chiF (R.N i) (R.N (i + 1)) (stdLat X.E (R.N i)) (ptYc c').deco.1.N)⁻¹

def RhoYUnit (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) : Prop :=
  (∀ i, i < R.m → ∀ c : (chFY W sel mu cst L u m2 sec i).Cl, ‖rhoY Ch σ₀ Am i c‖ = 1) ∧
    ∀ i, i < R.m → ∀ c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl, ‖rhoY' Ch σ₀ Am i c'‖ = 1

def ChainArgF.ofChKer (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2 sec) :
    ChainArgF R (fun i => (chFY W sel mu cst L u m2 sec i).toGFam) σ₀ where
  rhoDet := rhoY Ch σ₀ Am
  rhoDet' := rhoY' Ch σ₀ Am
  rho_norm := hU.1
  rho'_norm := hU.2
  unf i c c' := unfTh σ₀ Am.cD (thY Ch Am i c c')

variable {Ch}

end Charts

end Formalism.L2.Col.Sc
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Pairs

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 j : ℕ}

variable (W cst L u m2 j) in

abbrev PtY (b : L.β j) : Type := (cplAt W sel mu cst L u m2 j b).Pts

@[reducible] def ptYAct (b : L.β j) : MulAction ((chFY W sel mu cst L u m2 j).mem b).G (PtY W cst L u m2 j b) := ((chFY W sel mu cst L u m2 j).mem b).actD

attribute [local instance] ptYAct

def PtY.deco {b : L.β j} (x : PtY W cst L u m2 j b) : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs := x.1.1.deco

theorem sameOn_QE {d d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs} (h : DecoSet.SameOn (rowSG Pr sel mu) d d') :
    DecoSet.SameOn (QE sel (mu : Chr X.F X.E X.K)) d d' := by
  classical
  exact fun P hP => h P (Finset.mem_union_right _ hP)

theorem cplAt_ys_mv (b : L.β j) (p : ChPt (R := R) sel mu u j) {d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs}
    (h : DecoSet.SameOn (rowSG Pr sel mu) p.deco d') :
    (cplAt W sel mu cst L u m2 j b).ys (p.mv d') = (cplAt W sel mu cst L u m2 j b).ys p := by
  classical
  show (if j = m2 + 1 then ybSet sel mu cst (p.mv d').deco.1.N else {Set.univ}) = if j = m2 + 1 then ybSet sel mu cst p.deco.1.N else {Set.univ}
  rw [DecoF.mv_deco (sameOn_QE h)]
  split_ifs
  · exact ybSet_sameAt sel mu cst h
  · rfl

def PtY.repl {b : L.β j} (x : PtY W cst L u m2 j b) (d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs)
    (h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : PtY W cst L u m2 j b :=
  ⟨(x.1.1.mv d', x.1.2), by rw [cplAt_ys_mv b x.1.1 h]; exact x.2⟩

open Classical in

def PtY.mv {b : L.β j} (x : PtY W cst L u m2 j b) (d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) : PtY W cst L u m2 j b :=
  if h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d' then x.repl d' h else x

theorem PtY.mv_pos {b : L.β j} {x : PtY W cst L u m2 j b} {d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs}
    (h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : x.mv d' = x.repl d' h := dif_pos h

theorem PtY.mv_neg {b : L.β j} {x : PtY W cst L u m2 j b} {d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs}
    (h : ¬ DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : x.mv d' = x := dif_neg h

theorem PtY.mv_deco {b : L.β j} {x : PtY W cst L u m2 j b} {d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs}
    (h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : (x.mv d').deco = d' := by
  rw [PtY.mv_pos h]
  exact DecoF.mv_deco (sameOn_QE h)

def grpDeco {b : L.β j} (g : ((chFY W sel mu cst L u m2 j).mem b).G) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs := (g.1, g.2.1.1)

theorem PtY.mv_smul {b : L.β j} (g : ((chFY W sel mu cst L u m2 j).mem b).G) (x : PtY W cst L u m2 j b)
    (d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    PtY.mv (((chFY W sel mu cst L u m2 j).mem b).actD.toSMul.smul g x) (grpDeco g • d') =
      ((chFY W sel mu cst L u m2 j).mem b).actD.toSMul.smul g (x.mv d') := by
  by_cases h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d'
  · rw [PtY.mv_pos h, PtY.mv_pos (show DecoSet.SameOn (rowSG Pr sel mu)
      (PtY.deco (((chFY W sel mu cst L u m2 j).mem b).actD.toSMul.smul g x)) (grpDeco g • d') from h.smul _)]
    apply Subtype.ext
    apply Prod.ext
    · exact DecoF.mv_smul (FrmG.incl (L.levG j b) (L.levQ j b) g) x.1.1 d'
    · rfl
  · rw [PtY.mv_neg h, PtY.mv_neg (fun h' : DecoSet.SameOn (rowSG Pr sel mu)
      (PtY.deco (((chFY W sel mu cst L u m2 j).mem b).actD.toSMul.smul g x)) (grpDeco g • d') => h (DecoSet.SameOn.of_smul _ h'))]

def PtY.dia1 {b : L.β j} (P : {P // P ∈ Pr.vT u}) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (x : PtY W cst L u m2 j b) : PtY W cst L u m2 j b :=
  ⟨(x.1.1.dia1 P a, x.1.2), x.2⟩

def PtY.upL {b : L.β j} (x : PtY W cst L u m2 j b) (P : {P // P ∈ Pr.vT u}) (q : 𝓞 X.E) (y : x.deco.lv P) : PtY W cst L u m2 j b :=
  x.mv (x.deco.upL P q y)

def OffBad (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mu : Tup X.F X.E X.K S) (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  conjPrime₂ P ≠ P ∧ ∀ P' ∈ rowSG Pr sel mu, P' ≠ P ∧ P' ≠ conjPrime₂ P

def classRepresentativePair (c : (chFY W sel mu cst L u m2 j).Cl) : PtY W cst L u m2 j c.1 := ((chFY W sel mu cst L u m2 j).mem c.1).outSec.rep c.2

def clsY (b : L.β j) (x : PtY W cst L u m2 j b) : (chFY W sel mu cst L u m2 j).Cl := ⟨b, ((chFY W sel mu cst L u m2 j).mem b).cls x⟩

end Pairs

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Zero

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 : ℕ}

attribute [local instance] ptYAct

variable (Λ L) in

structure Step0Hyp : Prop where
  uniq : ∀ b b' : L.β 0, b = b'
  levG : ∀ b, L.levG 0 b = Λ 0
  levQ : ∀ b, L.levQ 0 b = LevQFam.top X.E X.K (R.N 0) (QE sel (mu : Chr X.F X.E X.K))

theorem mem_grp_of_eq {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))} {Λ₁ Λ₂ : LevFam E K n SG}
    (h : Λ₁ = Λ₂) {g : GLG E n SG} (hg : g ∈ Λ₁.grp) : g ∈ Λ₂.grp := h ▸ hg

theorem frame_move {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)}
    {f f' γ : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (hf' : ∀ x, f' x ∈ localization₂ P.asIdeal N' ↔ x ∈ stdAt E n P)
    (hN : localization₂ P.asIdeal N = localization₂ P.asIdeal (gmap γ N')) : f⁻¹ * γ * f' ∈ GLint E n P := by
  intro x
  show f.symm (γ (f' x)) ∈ stdAt E n P ↔ x ∈ stdAt E n P
  rw [← hf, LinearEquiv.apply_symm_apply, hN, mem_localization_gmap, LinearEquiv.symm_apply_apply, hf']

def levelZeroClassMap (c : (chFY W sel mu cst L u m2 0).Cl) : StCl W Λ u 0 := (stepGSD W Λ u 0).cls (classRepresentativePair c).deco

variable (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))

variable (W Λ cst L u m2) in

def e0LY : (StCl W Λ u 0 → FrS X σ₀ (R.N 0) → ℂ) →ₗ[ℂ] ((chFY W sel mu cst L u m2 0).Cl → FrS X σ₀ (R.N 0) → ℂ) where
  toFun F c := (stepEv W Λ σ₀ hσ u 0).atPt (classRepresentativePair c).deco F
  map_add' F G := by
    funext c
    exact map_add ((stepEv W Λ σ₀ hσ u 0).trPt (classRepresentativePair c).deco) _ _
  map_smul' t F := by
    funext c
    exact map_smul ((stepEv W Λ σ₀ hσ u 0).trPt (classRepresentativePair c).deco) t _

end Zero

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

def frameOfY {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet X.E n (Pr.vT u) Pr.vGs) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  Classical.choose (exists_frameD P d.2.lat)

theorem frameOfY_spec {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet X.E n (Pr.vT u) Pr.vGs) :
    ∀ x, frameOfY u P d x ∈ localization₂ P.asIdeal d.1.N ↔ x ∈ stdAt X.E n P :=
  Classical.choose_spec (exists_frameD P d.2.lat)

variable (hm : R.m = m2 + 2)

def topIdx : (L₀.withTop m2 Λt Θt).β R.m := ChIdx.top L₀ m2 Λt Θt (by omega)

def tilPtY (d : DecoSet X.E (R.N R.m - 1) ∅ SG') : PtY W cst (L₀.withTop m2 Λt Θt) u m2 R.m (topIdx L₀ m2 Λt Θt hm) :=
  ⟨(⟨(tilR hSG u d, fun P => frameOfY u P.1 (tilR hSG u d)), fun P x => frameOfY_spec u P.1 (tilR hSG u d) x⟩, Set.univ), by
    classical
    show Set.univ ∈ (if R.m = m2 + 1 then ybSet sel mu cst (tilR hSG u d).1.N else {Set.univ})
    rw [if_neg (by omega)]
    rfl⟩


def tilY (c : (ptGSD W ΛM).Cl) : (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).Cl :=
  clsY (topIdx L₀ m2 Λt Θt hm) (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))

def TopLevQ : Prop :=
  ∀ (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G), s • d = d →
    ∀ (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (h : (frameOfY u P.1 (tilR hSG u d))⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * frameOfY u P.1 (tilR hSG u d) ∈ GLint X.E (R.N R.m) P.1),
      (⟨_, h⟩ : ↥(GLint X.E (R.N R.m) P.1)) ∈ (Θt R.m P).H

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm}

theorem localization_tilR_fixed (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) {d : DecoSet X.E (R.N R.m - 1) ∅ SG'} {s : (ptGSD W ΛM).G}
    (hs : s • d = d) (P : HeightOneSpectrum (𝓞 X.E)) :
    localization₂ P.asIdeal (tilR hSG u d).1.N = localization₂ P.asIdeal (gmap (extR R hSG (s.1, s.2.1)).1.1 (tilR hSG u d).1.N) := by
  have hsd : Deco.act s.1.1 s.2.1 d.1 = d.1 := by
    have h0 := congrArg Subtype.val hs
    exact h0
  have key : ∀ {N : ℕ} (hN : N = R.N R.m - 1 + 1),
      Deco.act (extUH hN s.1).1 (extGH hN s.2.1) (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 =
        (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 := by
    intro N hN
    subst hN
    have hok : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok := d.2.til (conj_piT_notMem hPr u) hpi
    have e : (DecoSet.tilH (ST := Pr.vT u) (rfl : R.N R.m - 1 + 1 = R.N R.m - 1 + 1) (Pr.piT u) d).1 =
        d.1.til (ST := Pr.vT u) (Pr.piT u) := by
      show (DecoSet.til (ST := Pr.vT u) (Pr.piT u) d).1 = _
      unfold DecoSet.til
      rw [dif_pos hok]
    rw [e]
    show Deco.act (extE s.1.1) (extG s.2.1) _ = _
    rw [← Deco.til_act, hsd]
  have hN : gmap (extR R hSG (s.1, s.2.1)).1.1 (tilR hSG u d).1.N = (tilR hSG u d).1.N :=
    congrArg Deco.N (key (N_m_succ R))
  rw [hN]

def extYg (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).G :=
  ((extR R hSG (s.1, s.2.1)).1, ⟨(extR R hSG (s.1, s.2.1)).2, hL s.2⟩,
    ⟨fun P => ⟨(frameOfY u P.1 (tilR hSG u d))⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * frameOfY u P.1 (tilR hSG u d),
      frame_move (frameOfY_spec u P.1 _) (frameOfY_spec u P.1 _) (localization_tilR_fixed hPr hpi hs P.1)⟩,
      fun P _ => hQ d s hs P _⟩)


theorem extYg_smul (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs • tilPtY W cst L₀ u m2 Λt Θt hSG hm d =
      tilPtY W cst L₀ u m2 Λt Θt hSG hm d := by
  have hsd : Deco.act s.1.1 s.2.1 d.1 = d.1 := by
    have h0 := congrArg Subtype.val hs
    exact h0
  have key : ∀ {N : ℕ} (hN : N = R.N R.m - 1 + 1),
      Deco.act (extUH hN s.1).1 (extGH hN s.2.1) (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 =
        (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 := by
    intro N hN
    subst hN
    have hok : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok := d.2.til (conj_piT_notMem hPr u) hpi
    have e : (DecoSet.tilH (ST := Pr.vT u) (rfl : R.N R.m - 1 + 1 = R.N R.m - 1 + 1) (Pr.piT u) d).1 =
        d.1.til (ST := Pr.vT u) (Pr.piT u) := by
      show (DecoSet.til (ST := Pr.vT u) (Pr.piT u) d).1 = _
      unfold DecoSet.til
      rw [dif_pos hok]
    rw [e]
    show Deco.act (extE s.1.1) (extG s.2.1) _ = _
    rw [← Deco.til_act, hsd]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      show (Deco.act (extUH (N_m_succ R) s.1).1 (extGH (N_m_succ R) s.2.1)
          (DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1).res hSG =
        ((DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1).res hSG
      rw [key]
    · funext P
      show (extR R hSG (s.1, s.2.1)).1.1 * frameOfY u P.1 (tilR hSG u d) *
          ((frameOfY u P.1 (tilR hSG u d))⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * frameOfY u P.1 (tilR hSG u d))⁻¹ = frameOfY u P.1 (tilR hSG u d)
      group
  · have hmem := (extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs •
      tilPtY W cst L₀ u m2 Λt Θt hSG hm d).2
    classical
    change _ ∈ (if R.m = m2 + 1 then ybSet sel mu cst _ else {Set.univ}) at hmem
    rw [if_neg (by omega)] at hmem
    exact hmem

def stabilizerMapMaximalIndex (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      MulAction.stabilizer ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).G
        (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.rep
          (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
            (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))) where
  toFun s := ⟨(((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))⁻¹ *
      extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
      ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)), by
    have h1 := ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.mv_smul
      (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))
    refine MulAction.mem_stabilizer_iff.2 ?_
    show (_ * _ * _) • ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.rep
      (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))) = _
    rw [mul_smul, mul_smul, h1, extYg_smul, inv_smul_eq_iff, h1]⟩
  map_one' := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ 1 _ * _ = 1
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) 1 (one_smul _ _) = 1 := by
      have e1 : (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)) = 1 := map_one (extR R hSG)
      apply Prod.ext
      · show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1 = 1
        rw [e1]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).2 = 1
          rw [e1]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * ((extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1.1) * frameOfY u P.1 _ = 1
          rw [e1]
          have e2 : ((1 : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs).1 : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) = 1 := rfl
          rw [e2]
          group
    rw [e, mul_one, inv_mul_cancel]
  map_mul' s t := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ (s.1 * t.1) _ * _ =
      (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) * _) *
        (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) * _)
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) (s.1 * t.1) (MulAction.mem_stabilizer_iff.1 (s * t).2) =
        extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
          extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) := by
      have em : extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1) = extR R hSG (s.1.1, s.1.2.1) * extR R hSG (t.1.1, t.1.2.1) :=
        map_mul (extR R hSG) (s.1.1, s.1.2.1) (t.1.1, t.1.2.1)
      apply Prod.ext
      · show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1 = (extR R hSG (s.1.1, s.1.2.1)).1 * (extR R hSG (t.1.1, t.1.2.1)).1
        rw [em]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).2 = (extR R hSG (s.1.1, s.1.2.1)).2 * (extR R hSG (t.1.1, t.1.2.1)).2
          rw [em]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1.1 * frameOfY u P.1 _ =
            ((frameOfY u P.1 _)⁻¹ * (extR R hSG (s.1.1, s.1.2.1)).1.1 * frameOfY u P.1 _) *
              ((frameOfY u P.1 _)⁻¹ * (extR R hSG (t.1.1, t.1.2.1)).1.1 * frameOfY u P.1 _)
          rw [em]
          show _ * ((extR R hSG (s.1.1, s.1.2.1)).1.1 * (extR R hSG (t.1.1, t.1.2.1)).1.1) * _ = _
          group
    rw [e]
    group

def stabMapY (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      FamStab (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m) (tilY W cst L₀ u m2 Λt Θt hSG ΛM hm c) :=
  stabilizerMapMaximalIndex (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ c


end Top

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 : ℕ}
  {Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} {hSG : Pr.vGs ⊆ SG'} {ΛM : LevFam X.E X.K (R.N R.m - 1) SG'} {hm : R.m = m2 + 2}
  (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

attribute [local instance] ptYAct

def stabilizerMapMaximalIndex (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      MulAction.stabilizer ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).G
        (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
          (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
            (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))) where
  toFun s := ⟨(((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))⁻¹ *
      extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
      ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)), by
    have h1 := ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv_smul
      (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))
    refine MulAction.mem_stabilizer_iff.2 ?_
    show (_ * _ * _) • ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
      (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))) = _
    rw [mul_smul, mul_smul, h1, extYg_smul, inv_smul_eq_iff, h1]⟩
  map_one' := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ 1 _ * _ = 1
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) 1 (one_smul _ _) = 1 := by
      have e1 : (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)) = 1 := map_one (extR R hSG)
      apply Prod.ext
      · show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1 = 1
        rw [e1]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).2 = 1
          rw [e1]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * ((extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1.1) * frameOfY u P.1 _ = 1
          rw [e1]
          have e2 : ((1 : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs).1 : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) = 1 := rfl
          rw [e2]
          group
    rw [e, mul_one, inv_mul_cancel]
  map_mul' s t := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ (s.1 * t.1) _ * _ =
      (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) * _) *
        (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) * _)
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) (s.1 * t.1) (MulAction.mem_stabilizer_iff.1 (s * t).2) =
        extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
          extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) := by
      have em : extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1) = extR R hSG (s.1.1, s.1.2.1) * extR R hSG (t.1.1, t.1.2.1) :=
        map_mul (extR R hSG) (s.1.1, s.1.2.1) (t.1.1, t.1.2.1)
      apply Prod.ext
      · show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1 = (extR R hSG (s.1.1, s.1.2.1)).1 * (extR R hSG (t.1.1, t.1.2.1)).1
        rw [em]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).2 = (extR R hSG (s.1.1, s.1.2.1)).2 * (extR R hSG (t.1.1, t.1.2.1)).2
          rw [em]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1.1 * frameOfY u P.1 _ =
            ((frameOfY u P.1 _)⁻¹ * (extR R hSG (s.1.1, s.1.2.1)).1.1 * frameOfY u P.1 _) *
              ((frameOfY u P.1 _)⁻¹ * (extR R hSG (t.1.1, t.1.2.1)).1.1 * frameOfY u P.1 _)
          rw [em]
          show _ * ((extR R hSG (s.1.1, s.1.2.1)).1.1 * (extR R hSG (t.1.1, t.1.2.1)).1.1) * _ = _
          group
    rw [e]
    group

def stabMapY (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      FamStabS (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m) (tilY W cst L₀ u m2 Λt Θt hSG ΛM hm c) :=
  stabilizerMapMaximalIndex (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) sec hPr hpi hL hQ c

end Top

end Formalism.L2.Col.Sc
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col Formalism.L2.Col.Sc

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

variable (sel mu) in

structure TopFr where
  fr : ∀ (_P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (_d : DecoSet X.E (R.N R.m - 1) ∅ SG'), Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)
  spec : ∀ P d x, fr P d x ∈ localization₂ P.1.asIdeal (tilR hSG u d).1.N ↔ x ∈ stdAt X.E (R.N R.m) P.1

variable (hm : R.m = m2 + 2) (F : TopFr sel mu u hSG)

def tilPtY (d : DecoSet X.E (R.N R.m - 1) ∅ SG') : PtY W cst (L₀.withTop m2 Λt Θt) u m2 R.m (topIdx L₀ m2 Λt Θt hm) :=
  ⟨(⟨(tilR hSG u d, fun P => F.fr P d), fun P x => F.spec P d x⟩, Set.univ), by
    classical
    show Set.univ ∈ (if R.m = m2 + 1 then ybSet sel mu cst (tilR hSG u d).1.N else {Set.univ})
    rw [if_neg (by omega)]
    rfl⟩


def tilY (c : (ptGSD W ΛM).Cl) : (Formalism.L2.Col.chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).Cl :=
  clsY (topIdx L₀ m2 Λt Θt hm) (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c))

def TopLevQ : Prop :=
  ∀ (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G), s • d = d →
    ∀ (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (h : (F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d ∈ GLint X.E (R.N R.m) P.1),
      (⟨_, h⟩ : ↥(GLint X.E (R.N R.m) P.1)) ∈ (Θt R.m P).H

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm F}

def extYg (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    ((Formalism.L2.Col.chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).G :=
  ((extR R hSG (s.1, s.2.1)).1, ⟨(extR R hSG (s.1, s.2.1)).2, hL s.2⟩,
    ⟨fun P => ⟨(F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d,
      frame_move (F.spec P _) (F.spec P _) (localization_tilR_fixed hPr hpi hs P.1)⟩,
      fun P _ => hQ d s hs P _⟩)


theorem extYg_smul (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs • tilPtY W cst L₀ u m2 Λt Θt hSG hm F d =
      tilPtY W cst L₀ u m2 Λt Θt hSG hm F d := by
  have hsd : Deco.act s.1.1 s.2.1 d.1 = d.1 := by
    have h0 := congrArg Subtype.val hs
    exact h0
  have key : ∀ {N : ℕ} (hN : N = R.N R.m - 1 + 1),
      Deco.act (extUH hN s.1).1 (extGH hN s.2.1) (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 =
        (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 := by
    intro N hN
    subst hN
    have hok : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok := d.2.til (conj_piT_notMem hPr u) hpi
    have e : (DecoSet.tilH (ST := Pr.vT u) (rfl : R.N R.m - 1 + 1 = R.N R.m - 1 + 1) (Pr.piT u) d).1 =
        d.1.til (ST := Pr.vT u) (Pr.piT u) := by
      show (DecoSet.til (ST := Pr.vT u) (Pr.piT u) d).1 = _
      unfold DecoSet.til
      rw [dif_pos hok]
    rw [e]
    show Deco.act (extE s.1.1) (extG s.2.1) _ = _
    rw [← Deco.til_act, hsd]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      show (Deco.act (extUH (N_m_succ R) s.1).1 (extGH (N_m_succ R) s.2.1)
          (DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1).res hSG =
        ((DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1).res hSG
      rw [key]
    · funext P
      show (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d *
          ((F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d)⁻¹ = F.fr P d
      group
  · have hmem := (extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs •
      tilPtY W cst L₀ u m2 Λt Θt hSG hm F d).2
    classical
    change _ ∈ (if R.m = m2 + 1 then ybSet sel mu cst _ else {Set.univ}) at hmem
    rw [if_neg (by omega)] at hmem
    exact hmem

variable (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

def stabilizerMapMaximalIndex (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      MulAction.stabilizer ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).G
        (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
          (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
            (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c)))) where
  toFun s := ⟨(((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c)))⁻¹ *
      extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
      ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c)), by
    have h1 := ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv_smul
      (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c))
    refine MulAction.mem_stabilizer_iff.2 ?_
    show (_ * _ * _) • ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
      (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c))) = _
    rw [mul_smul, mul_smul, h1, extYg_smul, inv_smul_eq_iff, h1]⟩
  map_one' := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ 1 _ * _ = 1
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) 1 (one_smul _ _) = 1 := by
      have e1 : (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)) = 1 := map_one (extR R hSG)
      apply Prod.ext
      · show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1 = 1
        rw [e1]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).2 = 1
          rw [e1]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (F.fr P _)⁻¹ * ((extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1.1) * F.fr P _ = 1
          rw [e1]
          have e2 : ((1 : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs).1 : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) = 1 := rfl
          rw [e2]
          group
    rw [e, mul_one, inv_mul_cancel]
  map_mul' s t := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ (s.1 * t.1) _ * _ =
      (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) * _) *
        (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) * _)
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) (s.1 * t.1) (MulAction.mem_stabilizer_iff.1 (s * t).2) =
        extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
          extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) := by
      have em : extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1) = extR R hSG (s.1.1, s.1.2.1) * extR R hSG (t.1.1, t.1.2.1) :=
        map_mul (extR R hSG) (s.1.1, s.1.2.1) (t.1.1, t.1.2.1)
      apply Prod.ext
      · show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1 = (extR R hSG (s.1.1, s.1.2.1)).1 * (extR R hSG (t.1.1, t.1.2.1)).1
        rw [em]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).2 = (extR R hSG (s.1.1, s.1.2.1)).2 * (extR R hSG (t.1.1, t.1.2.1)).2
          rw [em]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (F.fr P _)⁻¹ * (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1.1 * F.fr P _ =
            ((F.fr P _)⁻¹ * (extR R hSG (s.1.1, s.1.2.1)).1.1 * F.fr P _) *
              ((F.fr P _)⁻¹ * (extR R hSG (t.1.1, t.1.2.1)).1.1 * F.fr P _)
          rw [em]
          show _ * ((extR R hSG (s.1.1, s.1.2.1)).1.1 * (extR R hSG (t.1.1, t.1.2.1)).1.1) * _ = _
          group
    rw [e]
    group

def stabMapY (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      FamStabS (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m) (tilY W cst L₀ u m2 Λt Θt hSG ΛM hm F c) :=
  stabilizerMapMaximalIndex (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) sec hPr hpi hL hQ c


end Top

end Formalism.L2.Col.Sc.Fr
end
end
