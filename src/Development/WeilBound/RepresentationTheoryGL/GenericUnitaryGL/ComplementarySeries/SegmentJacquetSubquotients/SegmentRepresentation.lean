import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.IsSubquotientJacMultiProdOfSub
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import Development.WeilBound.CoreStatements.PublishedTheorems.SegmentRepresentations.IsIrreduciblePiTensorSegTerm
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PosMkIff
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjProd
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.PiLocalization₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  have hρ := PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hfl : HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hT' : T ≠ ⊥ := fun h => hT (by rw [h]; rfl)
  obtain ⟨S, hS, hle⟩ := GlobalTheory.CompanionTheory.JacExp.exists_atom_le hfl hT'
  exact ⟨S, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hS, hle⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem isSubquotient_jac_of_le {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    {S T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))} (hST : S.toSubmodule ≤ T.toSubmodule)
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) T)
    (IsSubquotient.of_injective ⟨Submodule.inclusion hST, fun _ => rfl⟩ (Submodule.inclusion_injective hST)))

end PositivityTheory.Pf1.SegRepC.PiLocalization₂

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published

namespace PositivityTheory.Pf1.SegRepC.Uniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_unique_irred_sub {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ)
    (h1 : jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1) :
    ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        S'.toRepresentation.IsIrreducible → S' = S) ∧
      jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) S.toRepresentation) = 1 := by
  have hρ := PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hsπ : IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _
  have := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp (consecBlocks l d) hρ hsρ
  have hfl : HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hone : ∀ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), IsAtom T →
      1 ≤ jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) T.toRepresentation) :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac_atom _ hρ
  have hjm : jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) ≤ 1 := h1.le
  have hsoc : ∃ τ : IrrRep (GL (Fin (l * d)) k), IsSocle τ.ρ (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_forall_isAtom (π := multiProd (consecBlocks l d) (segTerm σ.ρ l)) (consecBlocks l d) hρ hsπ hfl hone hjm
  obtain ⟨τ, hτ, f, hf, hS⟩ := hsoc
  have hat : IsAtom f.range := isAtom_range hτ f hf
  have hatom : ∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible → IsAtom S' := fun S' hS' => by
    let g : S'.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨S'.toSubmodule.subtype, fun _ => rfl⟩
    have hr : g.range = S' := Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)
    have h := isAtom_range hS' g Subtype.val_injective
    rwa [hr] at h
  refine ⟨f.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat,
    fun S' hS' => hS S' (hatom S' hS'), le_antisymm ?_ ?_⟩
  · let ι : f.range.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨f.range.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (jacMap (consecBlocks l d) ι) :=
      GlobalTheory.JacInj.jacMap_injective k _ _ _ (consecBlocks l d) _ _ f.range.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)) ι hsπ
        Subtype.val_injective
    exact (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hρ (jacMap (consecBlocks l d) ι) hinj).trans hjm
  · exact hone _ hat

end PositivityTheory.Pf1.SegRepC.Uniq

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrEasy

theorem isSmooth_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _

private theorem isSmooth_segTerm_segment_jacquet_subquotients {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth ((isSmoothChar_absPow _).comp _ continuous_glDet)

theorem hasFiniteLength_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := by
  have h := GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k l (l * d)
    (fun _ => d)
    (fun a => ⟨σ.V, segTerm σ.ρ l a, isSmooth_segTerm_segment_jacquet_subquotients σ a, isIrreducible_twist σ.irr _⟩)
    (consecBlocks l d)
  exact h

theorem isSmooth_sub {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth S.toRepresentation := by
  intro v
  have h := hπ (v : V)
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hg
    exact congrArg Subtype.val hg
  · intro hg
    exact Subtype.ext hg

end SrEasy

open SrEasy

private theorem exists_irreducible_subrep_le_of_ne_bot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hwf : WellFoundedLT (Subrepresentation ρ))
    (T : Subrepresentation ρ) (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation ρ, S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  obtain ⟨S, ⟨hS0, hST⟩, hmin⟩ := hwf.wf.has_min
    {S : Subrepresentation ρ | S.toSubmodule ≠ ⊥ ∧ S.toSubmodule ≤ T.toSubmodule} ⟨T, hT, le_rfl⟩
  refine ⟨S, ?_, hST⟩
  let img : Subrepresentation S.toRepresentation → Subrepresentation ρ := fun U =>
    ⟨U.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨S.toRepresentation g w, U.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hne : (⊥ : Subrepresentation S.toRepresentation) ≠ ⊤ := by
    intro h
    apply hS0
    rw [eq_bot_iff]
    intro v hv
    have h1 : (⟨v, hv⟩ : S.toSubmodule) ∈ (⊤ : Subrepresentation S.toRepresentation).toSubmodule :=
      show _ ∈ (⊤ : Submodule ℂ S.toSubmodule) from Submodule.mem_top
    rw [← h] at h1
    have h0 : (⟨v, hv⟩ : S.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 h1
    have h2 : v = 0 := congrArg Subtype.val h0
    rw [h2]
    exact Submodule.zero_mem _
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun U => ?_ }
  by_cases hU : U.toSubmodule = ⊥
  · left
    exact Subrepresentation.ext hU
  · right
    have himg0 : (img U).toSubmodule ≠ ⊥ := by
      intro h
      apply hU
      apply Submodule.map_injective_of_injective S.toSubmodule.injective_subtype
      rw [Submodule.map_bot]
      exact h
    have himgS : img U ≤ S := by
      rintro _ ⟨w, _, rfl⟩
      exact w.2
    have heq : img U = S := by
      by_contra hne'
      exact hmin (img U) ⟨himg0, le_trans himgS hST⟩ (lt_of_le_of_ne himgS hne')
    apply Subrepresentation.ext
    apply eq_top_iff.2
    intro w _
    have hw : (w : V) ∈ (img U).toSubmodule := by
      rw [heq]
      exact w.2
    obtain ⟨u, hu, hu'⟩ := hw
    have : u = w := Subtype.ext hu'
    rw [← this]
    exact hu

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  have hfl := hasFiniteLength_prod (l := l) σ
  rw [hasFiniteLength_iff_wellFounded] at hfl
  exact exists_irreducible_subrep_le_of_ne_bot hfl.2 T hT

set_option synthInstance.maxHeartbeats 400000 in

theorem isIrreducible_segTensor {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ 2)).IsIrreducible :=
  PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2

private theorem hasFiniteLength_subrepresentation {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : HasFiniteLength π) (S : Subrepresentation π) :
    HasFiniteLength S.toRepresentation :=
  GlobalTheory.ProdLength.hasFiniteLength_of_injective
    (LinearMap.intertwiningMap_of_isIntertwiningMap S.toRepresentation π S.toSubmodule.subtype
      (fun _ _ => rfl))
    (fun a b h => Subtype.ext h) hπ

set_option synthInstance.maxHeartbeats 400000 in

theorem hasFiniteLength_jac_sub {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))) :
    HasFiniteLength (jac (consecBlocks 2 d) S.toRepresentation) := by
  exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks 2 d) _ S.toRepresentation
    (isSmooth_sub (isSmooth_prod σ) S) (hasFiniteLength_subrepresentation (hasFiniteLength_prod σ) S)

end PositivityTheory.RgGu.SRC

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel Matrix

namespace PositivityTheory.Pf1.SegRepC.Twist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_ne_zero_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hi : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  have := hi
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
  exact exists_ne (0 : ρ.asModule)

theorem exists_nabs_ne_one : ∃ x : kˣ, nabs k x ≠ 1 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  exact ⟨ϖ, fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)⟩

theorem not_equiv_segTerm {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (l : ℕ) {a b : Fin l}
    (hab : a ≠ b) : IsEmpty ((segTerm σ.ρ l a).Equiv (segTerm σ.ρ l b)) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨x, hx⟩ := exists_nabs_ne_one (k := k)
  let z : GL (Fin d) k := GeneralLinearGroup.scalar (Fin d) x
  have hz : ∀ g : GL (Fin d) k, z * g = g * z := fun g => by
    ext i j
    simp [z, GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hdet : GeneralLinearGroup.det z = x ^ d := by
    ext
    simp [z, GeneralLinearGroup.scalar]
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id σ.ρ σ.smooth σ.irr (σ.ρ z) fun g y => by
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]
  have hcz : ∀ y, σ.ρ z y = c • y := fun y => by
    rw [hc]; rfl
  obtain ⟨v, hv⟩ := exists_ne_zero_irr σ.ρ σ.irr
  have hc0 : c ≠ 0 := fun e => hv (by
    have h2 : σ.ρ z⁻¹ (σ.ρ z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hcz, e, zero_smul, map_zero] at h2
    exact h2.symm)
  have hφv : φ.toLinearEquiv v ≠ 0 := fun e => hv (φ.toLinearEquiv.map_eq_zero_iff.1 e)
  have h3 : φ.toLinearEquiv ((segTerm σ.ρ l a) z v) = (segTerm σ.ρ l b) z (φ.toLinearEquiv v) :=
    Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap z v
  simp only [segTerm, twist_apply, detChar_apply, hdet, map_smul, hcz, smul_smul] at h3
  have h4 := mul_right_cancel₀ hc0 (smul_left_injective ℂ hφv h3)
  rw [val_absPow, val_absPow, Complex.cpow_natCast, Complex.cpow_natCast] at h4
  have h5 : nabs k (x ^ d) ^ (a : ℕ) = nabs k (x ^ d) ^ (b : ℕ) := by exact_mod_cast h4
  have hpos : 0 < nabs k (x ^ d) := nabs_pos' k _
  have hne : nabs k (x ^ d) ≠ 1 := by
    have hpow : nabs k (x ^ d) = nabs k x ^ d := by simp [nabs]
    rw [hpow]
    exact fun e => hx ((pow_eq_one_iff_of_nonneg (nabs_pos' k x).le hd.ne').1 e)
  exact hab (Fin.ext (pow_right_injective₀ hpos hne h5))

end PositivityTheory.Pf1.SegRepC.Twist

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel GlobalTheory.LocGL

namespace PositivityTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrMult

theorem irrAdm : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem isSmooth_segTerm' {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isIrreducible_segTerm' {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _

def cl {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL k :=
  IrrGL.of (segTerm σ.ρ l a) (isSmooth_segTerm' σ a) (isIrreducible_segTerm' σ a)

theorem cl_injective {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) : Function.Injective (cl σ l) := by
  intro a b h
  by_contra hab
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h
  exact (PositivityTheory.Pf1.SegRepC.Twist.not_equiv_segTerm hd σ l hab).false φ

theorem cl_cusp {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) (a : Fin l) :
    (cl σ l a).IsCusp := by
  have h0 : (IrrGL.of σ.ρ σ.smooth σ.irr).IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf _ _ _) hσ⟩
  have h1 := h0.nu ((a : ℕ) : ℂ)
  have e : (IrrGL.of σ.ρ σ.smooth σ.irr).nu ((a : ℕ) : ℂ) = cl σ l a := by
    unfold IrrGL.nu cl segTerm
    rw [IrrGL.tw_of]
  rwa [e] at h1

def jacEquivOf {α : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] {N : ℕ} (e : (Σ a, m a) ≃ Fin N) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : π.Equiv τ) : (jac e π).Equiv (jac e τ) :=
  equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap,
      fun q => Submodule.Quotient.induction_on _ q fun v => by
        show (Submodule.Quotient.mk (φ.symm (φ v)) : _) = _
        rw [φ.symm_apply_apply],
      fun q => Submodule.Quotient.induction_on _ q fun v => by
        show (Submodule.Quotient.mk (φ (φ.symm v)) : _) = _
        rw [φ.apply_symm_apply]⟩)

def cl' {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL k := ⟨d, (cl σ l a).2⟩

end SrMult

open SrMult in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem jhMult_jac_multiProd (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) :
    jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1 := by
  classical
  have hx : ∑ a, (cl' σ l a).1 = l * d := by
    simp [cl', mul_comm]
  have hinj : Function.Injective (cl' σ l) := fun a b h => cl_injective hd σ h
  have hc : ∀ a, (cl' σ l a).IsCusp := fun a => cl_cusp hd σ hσ a
  have key := GlobalTheory.T.jacquet_multiplicity_cuspidal_product irrAdm (cl' σ l) (cl' σ l) hx hx hc hc
  have hset : {e : Fin l ≃ Fin l | ∀ a, cl' σ l a = cl' σ l (e a)} = {Equiv.refl _} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      ext a
      exact congrArg Fin.val (hinj (h a)).symm
    · rintro rfl a
      rfl
  rw [hset, Set.ncard_singleton] at key
  have h1 : jhMult (piTensor fun a => (cl' σ l a).rep)
      (jac (stdBlocks (fun _ : Fin l => d) hx)
        (multiProd (stdBlocks (fun _ : Fin l => d) hx) fun a => (cl' σ l a).rep)) = 1 := by
    have h := key
    exact_mod_cast h
  have hblk0 : ∀ h : ∑ _a : Fin l, d = l * d, stdBlocks (fun _ : Fin l => d) h = consecBlocks l d := by
    intro h
    ext ⟨a, i⟩
    rw [stdBlocks_val, consecBlocks_val]
    simp [mul_comm, add_comm]
  rw [hblk0 hx] at h1
  calc jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
      = jhMult (piTensor fun a => (cl' σ l a).rep)
          (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) :=
        jhMult_congr_left (piTensorEquiv fun a => IrrGL.equivOf (segTerm σ.ρ l a) (isSmooth_segTerm' σ a)
          (isIrreducible_segTerm' σ a)) _
    _ = jhMult (piTensor fun a => (cl' σ l a).rep)
          (jac (consecBlocks l d) (multiProd (consecBlocks l d) fun a => (cl' σ l a).rep)) :=
        jhMult_congr_right _ (jacEquivOf (consecBlocks l d)
          (multiProdEquiv (consecBlocks l d) fun a => IrrGL.equivOf (segTerm σ.ρ l a) (isSmooth_segTerm' σ a)
            (isIrreducible_segTerm' σ a)))
    _ = 1 := h1

end PositivityTheory.RgGu.SRC

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.MultOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagSM (l d : ℕ) : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d) :=
  ⟨fun i j => if i = j then d else 0, fun i => by simp, fun j => by simp⟩

theorem isSmooth_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isIrreducible_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _


theorem isIrreducible_piTensor_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ l)).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => isIrreducible_segTerm σ a)
    fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (isSmooth_segTerm σ a)
      (isIrreducible_segTerm σ a) φ hφ

theorem hasFiniteLength_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    HasFiniteLength (segTerm σ.ρ l a) :=
  (⟨_, segTerm σ.ρ l a, isSmooth_segTerm σ a, isIrreducible_segTerm σ a⟩ :
    IrrRep (GL (Fin d) k)).hasFiniteLength


theorem exists_other {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    {i j : Fin l} (h : b.1 i j < d) : ∃ j', j' ≠ j ∧ 0 < b.1 i j' := by
  by_contra hc
  push Not at hc
  have h2 := b.2.1 i
  simp only [Fintype.card_fin] at h2
  rw [Finset.sum_eq_single j (fun j' _ hj' => Nat.le_zero.1 (hc j' hj')) (by simp)] at h2
  omega


end PositivityTheory.Pf1.SegRepC.MultOne

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.Perm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_zero_or_d {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i))) :
    ∀ i j, b.1 i j = 0 ∨ b.1 i j = d := by
  intro i j
  by_contra hne
  push_neg at hne
  obtain ⟨h0, hdj⟩ := hne
  have hcusp : IsCuspidal (segTerm σ.ρ l i) :=
    GlobalTheory.LocGL.isCuspidal_twist hσ (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hsum := b.2.1 i
  simp only [Fintype.card_fin] at hsum
  obtain ⟨j', hj'ne, hj'0⟩ : ∃ j', j' ≠ j ∧ b.1 i j' ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hdj
    rw [Finset.sum_eq_single j (fun j' _ hj' => hall j' hj') (by simp)] at hsum
    exact hsum
  have hpos : 0 < b.1 i j := Nat.pos_of_ne_zero h0
  have hpos' : 0 < b.1 i j' := Nat.pos_of_ne_zero hj'0
  have hbot : unipRad k (f i) ≠ ⊥ := by
    rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
    rcases lt_or_gt_of_ne hj'ne with h | h
    · exact ⟨f i ⟨j', ⟨0, hpos'⟩⟩, f i ⟨j, ⟨0, hpos⟩⟩, by rw [blk_apply, blk_apply]; exact h⟩
    · exact ⟨f i ⟨j, ⟨0, hpos⟩⟩, f i ⟨j', ⟨0, hpos'⟩⟩, by rw [blk_apply, blk_apply]; exact h⟩
  have hsub := hcusp.2 l (b.1 i) (f i) hbot
  obtain ⟨S, g, hg⟩ := hs i
  have hnt : ∀ j, Nontrivial (s i j).V := by
    intro j
    haveI := (s i j).irr
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (bot_ne_top : (⊥ : Subrepresentation (s i j).ρ) ≠ ⊤)
    ext x
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  haveI := GlobalTheory.ProdSupport.nontrivial_piTensor (fun j => (s i j).V) hnt
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (PiTensorProduct ℂ fun j => (s i j).V)
  obtain ⟨x', rfl⟩ := hg x
  obtain ⟨y', rfl⟩ := hg y
  apply hxy
  have : x' = y' := Subtype.ext (Subsingleton.elim _ _)
  rw [this]

open GlobalTheory.LocGL in

theorem row_of_eq {d r : ℕ} (c : Fin r → ℕ) (j₀ : Fin r) (h0 : ∀ j, j ≠ j₀ → c j = 0) (hcd : c j₀ = d)
    (f : (Σ j, Fin (c j)) ≃ Fin d) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin d) k) V) (hτs : IsSmooth τ) (hτ : τ.IsIrreducible)
    (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (hs : IsSubquotient (piTensor fun j => (s j).ρ) (jac f τ)) :
    IrrGL.of (s j₀).ρ (s j₀).smooth (s j₀).irr = IrrGL.of τ hτs hτ := by
  subst hcd
  have h1 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (s j).ρ) (fun j => (s j).irr) j₀
  have h2 := h1.trans (SupportUnique.isSubquotient_comp hs
    (MonoidHom.mulSingle (fun j => GL (Fin (c j)) k) j₀))
  have h3 := h2.trans (SupportUnique.isSubquotient_jac_single j₀ h0 f τ)
  obtain ⟨φ⟩ := SupportUnique.nonempty_equiv_of_isSubquotient (s j₀).irr hτ h3
  exact IrrGL.of_eq_of.2 ⟨φ.symm⟩

open GlobalTheory.LocGL in

theorem col_of_eq {d r : ℕ} (c : Fin r → ℕ) (i₀ : Fin r) (h0 : ∀ i, i ≠ i₀ → c i = 0)
    (g : (Σ i, Fin (c i)) ≃ Fin d) (t : ∀ i, IrrRep (GL (Fin (c i)) k)) {V : Type} [AddCommGroup V]
    [Module ℂ V] (τ : Representation ℂ (GL (Fin d) k) V) (hτs : IsSmooth τ) (hτ : τ.IsIrreducible)
    (h : IrrGL.of (t i₀).ρ (t i₀).smooth (t i₀).irr = IrrGL.of τ hτs hτ) :
    Nonempty ((multiProd g fun i => (t i).ρ).Equiv τ) := by
  have hcd : c i₀ = d := congrArg Sigma.fst h
  subst hcd
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h
  obtain ⟨ψ⟩ := GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single c i₀ h0 t g
  exact ⟨ψ.trans φ⟩

theorem eq_of_eq_d {d l : ℕ} (hd : 0 < d) (c : Fin l → ℕ) (hsum : ∑ j, c j = d) {j j' : Fin l}
    (hj : c j = d) (hj' : c j' = d) : j = j' := by
  classical
  by_contra hne
  have h := Finset.sum_le_sum_of_subset (f := c) (Finset.subset_univ {j, j'})
  rw [Finset.sum_pair hne, hsum, hj, hj'] at h
  omega

theorem exists_eq_d {d l : ℕ} (hd : 0 < d) (c : Fin l → ℕ) (hsum : ∑ j, c j = d)
    (h01 : ∀ j, c j = 0 ∨ c j = d) : ∃ j, c j = d := by
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := c) (by omega)
  exact ⟨j, (h01 j).resolve_left hj⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_perm_of_cell {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (h01 : ∀ i j, b.1 i j = 0 ∨ b.1 i j = d)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (piTensor fun j => multiProd (g j) fun i => (s i j).ρ)) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  classical
  have hr : ∀ i, ∑ j, b.1 i j = d := fun i => by simpa using b.2.1 i
  have hc : ∀ j, ∑ i, b.1 i j = d := fun j => by simpa using b.2.2 j
  choose v hv using fun j => exists_eq_d hd (fun i => b.1 i j) (hc j) (fun i => h01 i j)
  have hvinj : Function.Injective v := fun j j' e =>
    eq_of_eq_d hd (b.1 (v j)) (hr (v j)) (hv j) (e ▸ hv j')
  let w : Equiv.Perm (Fin l) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hvinj)
  refine ⟨w, ?_⟩
  have hE : ∀ j, Nonempty ((multiProd (g j) fun i => (s i j).ρ).Equiv (segTerm σ.ρ l (v j))) := by
    intro j
    refine col_of_eq (fun i => b.1 i j) (v j) (fun i hi => ?_) (g j) (fun i => s i j) _
      (MultOne.isSmooth_segTerm σ _) (MultOne.isIrreducible_segTerm σ _) ?_
    · exact (h01 i j).resolve_right fun h => hi (eq_of_eq_d hd (fun i => b.1 i j) (hc j) h (hv j))
    · exact row_of_eq (b.1 (v j)) j
        (fun j' hj' => (h01 (v j) j').resolve_right fun h => hj' (eq_of_eq_d hd _ (hr (v j)) h (hv j)))
        (hv j) (f (v j)) _ _ _ (s (v j)) (hs (v j))
  let E := GlobalTheory.LocGL.piTensorEquiv fun j => (hE j).some
  have hT : (piTensor fun j => segTerm σ.ρ l (v j)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => MultOne.isIrreducible_segTerm σ _)
      fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (MultOne.isSmooth_segTerm σ _)
        (MultOne.isIrreducible_segTerm σ _) φ hφ
  have h' := h.trans (IsSubquotient.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hπ hT h'
  exact ⟨φ.symm⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_perm_of_isSubquotient_jac (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  obtain ⟨b, f, g, s, hs, hπs⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (consecBlocks l d) (consecBlocks l d) (MultOne.isSmooth_segTerm σ)
    (MultOne.hasFiniteLength_segTerm σ) hπ h
  exact exists_perm_of_cell hd σ hσ b (entries_zero_or_d hd σ hσ b f s hs) f g s hs π hπ hπs

end PositivityTheory.Pf1.SegRepC.Perm

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrPerm

theorem sq_right {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem sq_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

theorem equiv_parInd_jac {β : Type} [Fintype β] [LinearOrder β] (c : β → ℕ) (j₀ : β)
    (h0 : ∀ j, j ≠ j₀ → c j = 0) (f : (Σ j, Fin (c j)) ≃ Fin (c j₀)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (c j₀)) k) V) (hρ : IsSmooth ρ) :
    Nonempty (ρ.Equiv (parInd f (jac f ρ))) := by
  have hU : ∀ u ∈ unipRad k f, u = 1 := fun u hu => GlobalTheory.OneBlockCell.eq_one_of_mem_unipRad_single f j₀ h0 hu
  have hK : twKer ρ (unipRad k f) 1 = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    rw [hU n n.2]
    simp
  let L : V ≃ₗ[ℂ] Jacquet ρ (unipRad k f) := (Submodule.quotEquivOfEqBot _ hK).symm
  have hP : ∀ g : GL (Fin (c j₀)) k, g ∈ parab k f := fun g => GlobalTheory.OneBlockCell.mem_parab_of_single f j₀ h0 g
  refine GlobalTheory.CompanionTheory.WordProd.OneBlockProd.nonempty_equiv_parInd f hρ hP
    (GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single j₀ h0) L (fun p v => ?_)
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k f p
  rw [hU u hu, mul_one] at hp
  have hd : deltaHalf k (fun j => Fin (c j)) (leviProj k f p) = 1 :=
    GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single j₀ h0 _
  show (twist (jacU f ρ) (deltaHalf k fun j => Fin (c j))⁻¹) (leviProj k f p)
    (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ p v)
  rw [twist_apply, MonoidHom.inv_apply, hd, inv_one, Units.val_one, one_smul]
  simp only [jacU, jacquet, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply]
  rw [← hp]

theorem row_class {β : Type} [Fintype β] [LinearOrder β] {N : ℕ} (c : β → ℕ) (j₀ : β) (hN : c j₀ = N)
    (h0 : ∀ j, j ≠ j₀ → c j = 0) (f : (Σ j, Fin (c j)) ≃ Fin N) (ρ : IrrRep (GL (Fin N) k))
    (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (hs : IsSubquotient (piTensor fun j => (s j).ρ) (jac f ρ.ρ)) :
    (⟨c j₀, (s j₀).cl⟩ : IrrGL k) = ⟨N, ρ.cl⟩ := by
  subst hN
  obtain ⟨e1⟩ := GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single c j₀ h0 s f
  obtain ⟨e2⟩ := equiv_parInd_jac c j₀ h0 f ρ.ρ ρ.smooth
  have h3 : IsSubquotient (multiProd f fun j => (s j).ρ) (parInd f (jac f ρ.ρ)) :=
    GlobalTheory.ParIndSubquot.parInd_isSubquotient k β (Fin (c j₀)) (fun j => Fin (c j)) f _ _ _ _
      (isSmooth_jac f ρ.smooth) hs
  have h4 : IsSubquotient (s j₀).ρ ρ.ρ := sq_right (sq_left e1 h3) e2.symm
  obtain ⟨φ⟩ := h4.nonempty_equiv (s j₀).irr ρ.irr
  exact congrArg (Sigma.mk (c j₀)) (IrrRep.cl_eq_iff.2 ⟨φ.symm⟩)

theorem col_class {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (b : α → ℕ) (i₀ : α) (hN : b i₀ = N)
    (h0 : ∀ i, i ≠ i₀ → b i = 0) (σ : ∀ i, IrrRep (GL (Fin (b i)) k)) (g : (Σ i, Fin (b i)) ≃ Fin N) :
    ∃ τ : IrrRep (GL (Fin N) k), Nonempty ((multiProd g fun i => (σ i).ρ).Equiv τ.ρ) ∧
      (⟨N, τ.cl⟩ : IrrGL k) = ⟨b i₀, (σ i₀).cl⟩ := by
  subst hN
  exact ⟨σ i₀, GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single b i₀ h0 σ g, rfl⟩

def segIrr {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrRep (GL (Fin d) k) :=
  ⟨σ.V, segTerm σ.ρ l a, PositivityTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ a,
    PositivityTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ a⟩

theorem exists_perm_of_cell {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k))
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (h01 : ∀ i j, b.1 i j = 0 ∨ b.1 i j = d)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (piTensor fun j => multiProd (g j) fun i => (s i j).ρ)) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  classical
  have hr : ∀ i, ∑ j, b.1 i j = d := fun i => by simpa using b.2.1 i
  have hc : ∀ j, ∑ i, b.1 i j = d := fun j => by simpa using b.2.2 j
  have two : ∀ (F : Fin l → ℕ), ∑ j, F j = d → ∀ j j', F j = d → F j' = d → j = j' := by
    intro F hF j j' h1 h2
    by_contra hne
    have : F j + F j' ≤ ∑ x, F x := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    omega
  have one : ∀ (F : Fin l → ℕ), (∀ j, F j = 0 ∨ F j = d) → ∑ j, F j = d → ∃ j, F j = d := by
    intro F h0 hF
    by_contra hne
    push Not at hne
    have : ∑ j, F j = 0 := Finset.sum_eq_zero fun j _ => (h0 j).resolve_right (hne j)
    omega
  have zero : ∀ (F : Fin l → ℕ), (∀ j, F j = 0 ∨ F j = d) → ∑ j, F j = d → ∀ j, F j = d →
      ∀ j', j' ≠ j → F j' = 0 := fun F h0 hF j hj j' hj' =>
    (h0 j').resolve_right fun e => hj' (two F hF j' j e hj)
  choose q hq using fun j => one (fun i => b.1 i j) (fun i => h01 i j) (hc j)
  have qinj : Function.Injective q := fun j j' e =>
    two (fun x => b.1 (q j) x) (hr (q j)) j j' (hq j) (e ▸ hq j')
  let w : Equiv.Perm (Fin l) := Equiv.ofBijective q (Finite.injective_iff_bijective.1 qinj)
  have hcol : ∀ j, Nonempty ((multiProd (g j) fun i => (s i j).ρ).Equiv (segTerm σ.ρ l (w j))) := by
    intro j
    obtain ⟨τ, ⟨E⟩, hτ⟩ := col_class (fun i => b.1 i j) (q j) (hq j)
      (zero (fun i => b.1 i j) (fun i => h01 i j) (hc j) (q j) (hq j)) (fun i => s i j) (g j)
    have hrow := row_class (fun x => b.1 (q j) x) j (hq j)
      (zero (fun x => b.1 (q j) x) (fun x => h01 (q j) x) (hr (q j)) j (hq j)) (f (q j))
      (segIrr σ l (q j)) (s (q j)) (hs (q j))
    have e := hτ.trans hrow
    have e' : τ.cl = (segIrr σ l (q j)).cl := eq_of_heq (Sigma.mk.inj_iff.1 e).2
    obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 e'
    exact ⟨E.trans φ⟩
  have hT : (piTensor fun a => segTerm σ.ρ l (w a)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _
      (fun a => PositivityTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ (w a))
      fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (PositivityTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ (w a))
        (PositivityTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ (w a)) φ hφ
  have h2 : IsSubquotient π (piTensor fun a => segTerm σ.ρ l (w a)) :=
    sq_right h (GlobalTheory.LocGL.piTensorEquiv fun j => (hcol j).some)
  obtain ⟨φ⟩ := h2.nonempty_equiv hπ hT
  exact ⟨w, ⟨φ.symm⟩⟩

end SrPerm

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_perm_of_isSubquotient_jac (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  obtain ⟨b, f, g, s, hs, hπs⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (consecBlocks l d) (consecBlocks l d) (PositivityTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ)
    (PositivityTheory.Pf1.SegRepC.MultOne.hasFiniteLength_segTerm σ) hπ h
  exact SrPerm.exists_perm_of_cell hd σ b (PositivityTheory.Pf1.SegRepC.Perm.entries_zero_or_d hd σ hσ b f s hs) f g s hs
    π hπ hπs

set_option synthInstance.maxHeartbeats 400000 in

theorem constituents_jac_sub (hG : GeometricLemma) {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) X)
    (hρ : ρ.IsIrreducible) (hs : IsSubquotient ρ (jac (consecBlocks 2 d) S.toRepresentation)) :
    Nonempty (ρ.Equiv (piTensor (segTerm σ.ρ 2))) ∨
      Nonempty (ρ.Equiv (PositivityTheory.Pf1.SegRepC.SegTwo.revTensor σ)) := by
  obtain ⟨w, ⟨φ⟩⟩ := exists_perm_of_isSubquotient_jac hG hd (by decide) σ hσ ρ hρ
    (PositivityTheory.Pf1.SegRepC.Lift.isSubquotient_jac_multiProd_of_sub σ S hs)
  have hne : w 1 ≠ w 0 := fun e => absurd (w.injective e) (by decide)
  rcases Fin.exists_fin_two.1 ⟨w 0, rfl⟩ with h0 | h0
  · have h1 : w 1 = 1 := by
      rw [h0] at hne
      rcases Fin.exists_fin_two.1 ⟨w 1, rfl⟩ with h | h
      · exact absurd h hne
      · exact h
    have e : (fun a => segTerm σ.ρ 2 (w a)) = segTerm σ.ρ 2 := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [e] at φ
    exact Or.inl ⟨φ⟩
  · have h1 : w 1 = 0 := by
      rw [h0] at hne
      rcases Fin.exists_fin_two.1 ⟨w 1, rfl⟩ with h | h
      · exact h
      · exact absurd h hne
    have e : (fun a => segTerm σ.ρ 2 (w a)) = fun a : Fin 2 => segTerm σ.ρ 2 a.rev := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [e] at φ
    exact Or.inr ⟨φ⟩

end PositivityTheory.RgGu.SRC

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel Zc
open PositivityTheory.Pf1.SegRepC.SegTwo

namespace PositivityTheory.RgGu.SRC

namespace SrRev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem transfer {N : ℕ} {v w : Fin 2 → IrrGL k} (h : v = w) (hv : ∑ a, (v a).1 = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ (GL (Fin N) k) W} (f : ω.IntertwiningMap (prodIrr v hv)) :
    ∃ (hw : ∑ a, (w a).1 = N) (f' : ω.IntertwiningMap (prodIrr w hw)),
      (Function.Injective f → Function.Injective f') ∧ (Function.Surjective f' → Function.Surjective f) := by
  subst h
  exact ⟨hv, f, id, id⟩

theorem jmc {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst e
  rfl

end SrRev

open SrRev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem jhMult_rev_jac_sub (hG : GeometricLemma) (hR : RhoNuRhoReducible) {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)))
    (hS : S.toRepresentation.IsIrreducible)
    (h1 : jhMult (piTensor (segTerm σ.ρ 2)) (jac (consecBlocks 2 d) S.toRepresentation) = 1) :
    jhMult (revTensor σ) (jac (consecBlocks 2 d) S.toRepresentation) = 0 := by
  by_contra h2
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  let x : IrrGL k := IrrGL.of σ.ρ σ.smooth σ.irr
  have hx : x.IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) hσ⟩
  let u : Fin 2 → IrrGL k := fun a => x.nu ((a : ℕ) : ℂ)
  have hu1 : ∀ a, (u a).1 = d := fun _ => rfl
  have hu : ∑ a, (u a).1 = 2 * d := by simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hu' : ∑ a, (u (Fin.rev a)).1 = 2 * d := by
    simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have he : stdBlocks (fun a => (u a).1) hu = consecBlocks 2 d := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (Eq.trans ?_ (consecBlocks_val 2 d a j).symm)
    rw [stdBlocks_val]
    fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]
  have he' : stdBlocks (fun a => (u (Fin.rev a)).1) hu' = consecBlocks 2 d := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (Eq.trans ?_ (consecBlocks_val 2 d a j).symm)
    rw [stdBlocks_val]
    fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]
  let φ : ∀ a, (segTerm σ.ρ 2 a).Equiv (u a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (x.twEquiv _ (isSmoothChar_absPow _))
  have Φ : (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).Equiv (prodIrr u hu) := by
    unfold prodIrr
    rw [he]
    exact multiProdEquiv (consecBlocks 2 d) φ
  let ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let f : S.toRepresentation.IntertwiningMap (prodIrr u hu) := Φ.toIntertwiningMap.comp ι
  have hf : Function.Injective f := Φ.toLinearEquiv.injective.comp Subtype.val_injective
  have j1 : 1 ≤ jm u hu S.toRepresentation := by
    have : jm u hu S.toRepresentation = 1 := by
      unfold jm
      rw [he]
      exact (jhMult_congr_left (piTensorEquiv φ) _).symm.trans h1
    rw [this]
  have j2 : 1 ≤ jm (fun a => u (Fin.rev a)) hu' S.toRepresentation := by
    have : jm (fun a => u (Fin.rev a)) hu' S.toRepresentation ≠ 0 := by
      unfold jm
      rw [he']
      exact fun h => h2 ((jhMult_congr_left (piTensorEquiv fun a => φ (Fin.rev a)) _).trans h)
    exact Order.one_le_iff_ne_zero.2 this
  have hux : u = ![x, x.nu 1] := by
    funext a
    fin_cases a
    · simp [u]
    · simp [u]
  have hux' : (fun a => u (Fin.rev a)) = ![x.nu 1, x] := by
    funext a
    fin_cases a
    · simp [u]
    · simp [u]
  obtain ⟨hw, f', hf', hs'⟩ := transfer hux hu f
  have hw' : ∑ a, (![x.nu 1, x] a).1 = 2 * d := by rw [← hux']; exact hu'
  have hnx : x ≠ x.nu 1 := by
    intro h
    have h0 : x.nu ((0 : ℕ) : ℂ) = x.nu ((1 : ℕ) : ℂ) := by simpa using h
    exact absurd ((GlobalTheory.LocGL.IrrGL.nu_natCast_inj hd).1 h0) (by decide)
  have hsurj := GlobalTheory.CompanionTheory.CuspPairSub.surjective_of_jm hA hx (hx.nu 1) hnx hw hw' f' (hf' hf)
    (by rw [← jmc hux hu hw]; exact j1) (by rw [← jmc hux' hu' hw']; exact j2)
  have hsf := hs' hsurj
  have hι : Function.Surjective ι := by
    intro v
    obtain ⟨w, hw⟩ := hsf (Φ v)
    exact ⟨w, Φ.toLinearEquiv.injective hw⟩
  have htop : S = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨w, rfl⟩ := hι v
    exact w.2
  subst htop
  exact hR k d hd σ hσ (GlobalTheory.Parabolic.isIrreducible_of_equiv (topEquiv _) hS)

end PositivityTheory.RgGu.SRC

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel
open PositivityTheory.Pf1.SegRepC PositivityTheory.Pf1.SegRepC.SegTwo

namespace PositivityTheory.RgGu.SRC

set_option synthInstance.maxHeartbeats 400000 in

def StageP : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GeometricLemma → PositivityTheory.Pf1.SegRepC.SegTwo → ∀ {d l : ℕ}, 0 < d → 0 < l → ∀ (σ : IrrRep (GL (Fin d) k)),
    IsCuspidal σ.ρ → ∀ (i : ℕ) (hi : i + 1 < l),
    ∃ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), T.toSubmodule ≠ ⊥ ∧
      ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X),
        π.IsIrreducible → IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) →
        ∀ (w : Equiv.Perm (Fin l)), π.Equiv (piTensor fun a => segTerm σ.ρ l (w a)) →
        w.symm ⟨i, by omega⟩ < w.symm ⟨i + 1, hi⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem segTwo_of (hG : GeometricLemma) (hR : RhoNuRhoReducible) : PositivityTheory.Pf1.SegRepC.SegTwo := by
  intro k _ _ _ _ d hd σ hσ
  have h2 : (0 : ℕ) < 2 := by decide
  obtain ⟨S, hS, hU, h1⟩ := Uniq.exists_unique_irred_sub hd h2 σ hσ (SRC.jhMult_jac_multiProd hG hd h2 σ hσ)
  refine ⟨S, hS, hU, ?_⟩
  refine GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one _ _ (SRC.isIrreducible_segTensor hd σ) (SRC.hasFiniteLength_jac_sub hd σ hσ S) h1 fun X _ _ ρ hρ hs => ?_
  rcases SRC.constituents_jac_sub hG hd σ hσ S ρ hρ hs with h | h'
  · exact h
  · obtain ⟨φ⟩ := h'
    exfalso
    refine jhMult_ne_zero_iff.2 ?_ (SRC.jhMult_rev_jac_sub hG hR hd σ hσ S hS h1)
    exact (IsSubquotient.of_surjective φ.toIntertwiningMap fun w => ⟨φ.symm w, φ.apply_symm_apply w⟩).trans hs

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem segRep_of (hT : StageP) (hG : GeometricLemma) (h2 : PositivityTheory.Pf1.SegRepC.SegTwo) : SegmentRepresentation := by
  intro k _ _ _ _ d l hd hl σ hσ
  obtain ⟨S, hS, huniq, h1⟩ := Uniq.exists_unique_irred_sub hd hl σ hσ (SRC.jhMult_jac_multiProd hG hd hl σ hσ)
  refine ⟨S, hS, huniq, ?_⟩
  have hfl : HasFiniteLength (jac (consecBlocks l d) S.toRepresentation) :=
    GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks l d) _ S.toRepresentation
      (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (Lift.isSmooth_multiProd_segTerm σ l) S) (hasFiniteLength_of_isIrreducible hS)
  refine GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one _ _
    (PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l) hfl h1 fun X _ _ π hπ h => ?_
  obtain ⟨w, ⟨φ⟩⟩ := SRC.exists_perm_of_isSubquotient_jac hG hd hl σ hσ π hπ (Lift.isSubquotient_jac_multiProd_of_sub σ S h)
  obtain rfl : w = 1 := Lift.perm_eq_one_of_lt_succ w fun i hi => by
    obtain ⟨T, hT0, hTw⟩ := hT k hG h2 hd hl σ hσ i hi
    obtain ⟨S', hS', hle⟩ := SRC.exists_irred_le hd hl σ hσ T hT0
    obtain rfl := huniq S' hS'
    exact hTw π hπ (PiLocalization₂.isSubquotient_jac_of_le σ hle h) w φ
  exact ⟨φ⟩

end PositivityTheory.RgGu.SRC

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel PositivityTheory.Pf1.SegRepC

namespace PositivityTheory.RgGu.SRC

namespace StageC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev cls {d : ℕ} (σ : IrrRep (GL (Fin d) k)) : IrrGL k := IrrGL.of σ.ρ σ.smooth σ.irr

theorem segTerm_smooth {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_absPow _).detChar

theorem segTerm_irr {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : (segTerm σ.ρ l a).IsIrreducible :=
  isIrreducible_twist σ.irr _

abbrev tcl {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL k :=
  IrrGL.of (segTerm σ.ρ l a) (segTerm_smooth σ l a) (segTerm_irr σ l a)

theorem tcl_eq {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : tcl σ l a = (cls σ).nu ((a : ℕ) : ℂ) :=
  (IrrGL.tw_of σ.ρ σ.smooth σ.irr _ _).symm

theorem blocks_eq (l d : ℕ) (h : ∑ _a : Fin l, d = l * d) : stdBlocks (fun _ : Fin l => d) h = consecBlocks l d := by
  ext ⟨a, j⟩
  rw [stdBlocks_val, consecBlocks_val]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem consec_equiv {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (h : ∑ a, (tcl σ l a).1 = l * d) :
    Nonempty ((multiProd (consecBlocks l d) (segTerm σ.ρ l)).Equiv (prodIrr (tcl σ l) h)) := by
  have he : stdBlocks (fun a => (tcl σ l a).1) h = consecBlocks l d := blocks_eq l d h
  unfold prodIrr
  rw [he]
  exact ⟨multiProdEquiv (consecBlocks l d) fun a => IrrGL.equivOf _ _ _⟩

theorem prod₂_map_injective_right (r t : ℕ) {U W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U)
    (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W')
    (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ ρ'), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f)
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom), GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem inj_comp {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₃ : Representation ℂ G V₃} (f : ρ₂.IntertwiningMap ρ₃) (g : ρ₁.IntertwiningMap ρ₂)
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (f.comp g) :=
  fun _ _ h => hg (hf h)

theorem inj_equiv {G V₁ V₂ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} (φ : ρ₁.Equiv ρ₂) :
    Function.Injective φ.toIntertwiningMap :=
  φ.toLinearEquiv.injective

theorem sum_const_fin (n d : ℕ) : ∑ _a : Fin n, d = n * d := by simp

section Emb

variable {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃}

def Emb (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) : Prop :=
  ∃ F : ρ₁.IntertwiningMap ρ₂, Function.Injective F

theorem Emb.trans (h : Emb ρ₁ ρ₂) (h' : Emb ρ₂ ρ₃) : Emb ρ₁ ρ₃ := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  exact ⟨g.comp f, inj_comp _ _ hg hf⟩

theorem Emb.of (e : Nonempty (ρ₁.Equiv ρ₂)) : Emb ρ₁ ρ₂ := ⟨e.some.toIntertwiningMap, inj_equiv _⟩

theorem Emb.of' (e : Nonempty (ρ₂.Equiv ρ₁)) : Emb ρ₁ ρ₂ := ⟨e.some.symm.toIntertwiningMap, inj_equiv _⟩

theorem Emb.sub (S : Subrepresentation ρ₁) : Emb S.toRepresentation ρ₁ :=
  ⟨⟨S.toSubmodule.subtype, fun _ => rfl⟩, Subtype.val_injective⟩

theorem Emb.range (h : Emb ρ₁ ρ₂) [Nontrivial V₁] :
    ∃ T : Subrepresentation ρ₂, T.toSubmodule ≠ ⊥ ∧ IsSubquotient T.toRepresentation ρ₁ := by
  obtain ⟨F, hF⟩ := h
  let T : Subrepresentation ρ₂ :=
    ⟨LinearMap.range F.toLinearMap, by
      rintro g _ ⟨v, rfl⟩
      exact ⟨_, F.isIntertwining _ _ g v⟩⟩
  let toT : ρ₁.IntertwiningMap T.toRepresentation :=
    ⟨LinearMap.codRestrict T.toSubmodule F.toLinearMap (fun v => ⟨v, rfl⟩), fun g => by
      ext v
      exact F.isIntertwining _ _ g v⟩
  refine ⟨T, fun hT => ?_, IsSubquotient.of_surjective toT ?_⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
    have hmem : F v ∈ T.toSubmodule := ⟨v, rfl⟩
    rw [hT, Submodule.mem_bot] at hmem
    exact hv (hF (hmem.trans (map_zero F).symm))
  · rintro ⟨_, v, rfl⟩
    exact ⟨v, rfl⟩

end Emb

theorem sum_app {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) :
    ∑ a, (Fin.append x y a).1 = ∑ a, (x a).1 + ∑ a, (y a).1 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

section Two

variable {r t : ℕ} {U U' W W' Y Y' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y']
  [Module ℂ Y']

set_option synthInstance.maxHeartbeats 400000 in
theorem embR (σ : Representation ℂ (GL (Fin r) k) U) (ρ : Representation ℂ (GL (Fin t) k) W)
    (ρ' : Representation ℂ (GL (Fin t) k) W') (P : Representation ℂ (GL (Fin (r + t)) k) Y)
    (P' : Representation ℂ (GL (Fin (r + t)) k) Y') (h : Emb ρ ρ') (e : Nonempty ((prod₂ σ ρ).Equiv P))
    (e' : Nonempty ((prod₂ σ ρ').Equiv P')) : Emb P P' := by
  obtain ⟨f, hf⟩ := h
  have h3 : Emb (prod₂ σ ρ) (prod₂ σ ρ') := prod₂_map_injective_right r t σ ρ ρ' f hf
  exact ((Emb.of' e).trans h3).trans (Emb.of e')

set_option synthInstance.maxHeartbeats 400000 in
theorem embL (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U')
    (ρ : Representation ℂ (GL (Fin t) k) W) (P : Representation ℂ (GL (Fin (r + t)) k) Y)
    (P' : Representation ℂ (GL (Fin (r + t)) k) Y') (h : Emb σ σ') (e : Nonempty ((prod₂ σ ρ).Equiv P))
    (e' : Nonempty ((prod₂ σ' ρ).Equiv P')) : Emb P P' := by
  obtain ⟨f, hf⟩ := h
  have h3 : Emb (prod₂ σ ρ) (prod₂ σ' ρ) := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k r t _ _ _ σ σ' ρ f hf
  exact ((Emb.of' e).trans h3).trans (Emb.of e')

end Two

set_option synthInstance.maxHeartbeats 400000 in
theorem emb_right {p q q' r t : ℕ} (A : Fin p → IrrGL k) (y : Fin q → IrrGL k) (y' : Fin q' → IrrGL k)
    (hA : ∑ a, (A a).1 = r) (hy : ∑ a, (y a).1 = t) (hy' : ∑ a, (y' a).1 = t) (h : Emb (prodIrr y hy) (prodIrr y' hy'))
    (h1 : ∑ a, (Fin.append A y a).1 = r + t) (h2 : ∑ a, (Fin.append A y' a).1 = r + t) :
    Emb (prodIrr (Fin.append A y) h1) (prodIrr (Fin.append A y') h2) :=
  embR (prodIrr A hA) (prodIrr y hy) (prodIrr y' hy') _ _ h (GlobalTheory.T.product_irreducible_append_equiv k p q r t A y hA hy h1)
    (GlobalTheory.T.product_irreducible_append_equiv k p q' r t A y' hA hy' h2)

set_option synthInstance.maxHeartbeats 400000 in
theorem emb_left {p p' q r t : ℕ} (y : Fin p → IrrGL k) (y' : Fin p' → IrrGL k) (B : Fin q → IrrGL k)
    (hy : ∑ a, (y a).1 = r) (hy' : ∑ a, (y' a).1 = r) (hB : ∑ a, (B a).1 = t) (h : Emb (prodIrr y hy) (prodIrr y' hy'))
    (h1 : ∑ a, (Fin.append y B a).1 = r + t) (h2 : ∑ a, (Fin.append y' B a).1 = r + t) :
    Emb (prodIrr (Fin.append y B) h1) (prodIrr (Fin.append y' B) h2) :=
  embL (prodIrr y hy) (prodIrr y' hy') (prodIrr B hB) _ _ h (GlobalTheory.T.product_irreducible_append_equiv k p q r t y B hy hB h1)
    (GlobalTheory.T.product_irreducible_append_equiv k p' q r t y' B hy' hB h2)

set_option synthInstance.maxHeartbeats 400000 in
theorem comb {n c N : ℕ} (xx : Fin n → IrrGL k) (hdx : ∑ a, (xx a).1 = N) (iz : Fin n) (z : IrrGL k) (hz : xx iz = z)
    (pr : Fin 2 → IrrGL k) (hs : ∑ j, (pr j).1 = z.1) (d : ℕ) (hsd : ∀ j, (pr j).1 = d) (hsc : ∀ j, (pr j).IsCusp)
    (hu : Nonempty ((jac (stdBlocks (fun j => (pr j).1) hs) z.rep).Equiv (piTensor fun j => (pr j).rep)))
    (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N) (hyc : ∀ a, (y a).IsCusp) (hjm : 1 ≤ Zc.jm y hy (prodIrr xx hdx)) :
    ∃ f : Fin 2 ↪o Fin c, ∀ j, y (f j) = pr j := by
  subst hz
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  obtain ⟨b, hb, s', hrow, hcol⟩ := GlobalTheory.CompanionTheory.Shuffle2.exists_cell_data hA xx hdx y hy hyc hjm
  choose a ha haw using hcol
  have key : ∀ r j, b r j ≠ 0 → IrrGL.of (s' r j).ρ (s' r j).smooth (s' r j).irr = y j := by
    intro r j hj
    obtain rfl : a j = r := by_contra fun hne => hj (ha j r (Ne.symm hne))
    exact haw j
  obtain ⟨f, -, hf⟩ := GlobalTheory.CompanionTheory.Shuffle2.exists_row hA (xx iz) pr hs d hsd hsc hu (b iz) (hb iz)
    (s' iz) (hrow iz) y hyc (key iz)
  exact ⟨f, hf⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem classMain {i q N : ℕ} (t : Fin (i + 2 + q) → IrrGL k) (ht : ∑ a, (t a).1 = N) (pr : Fin 2 → IrrGL k)
    (hpr : ∀ j, pr j = t (Fin.castAdd q (Fin.natAdd i j))) (z : IrrGL k) (hs : ∑ j, (pr j).1 = z.1)
    (he : Emb z.rep (prodIrr pr hs)) :
    ∃ (n : ℕ) (xx : Fin n → IrrGL k) (hdx : ∑ a, (xx a).1 = N) (iz : Fin n), xx iz = z ∧
      Emb (prodIrr xx hdx) (prodIrr t ht) := by
  obtain ⟨A, hA⟩ : ∃ A : Fin i → IrrGL k, ∀ a, A a = t (Fin.castAdd q (Fin.castAdd 2 a)) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin q → IrrGL k, ∀ b, B b = t (Fin.natAdd (i + 2) b) := ⟨_, fun _ => rfl⟩
  have hfun : Fin.append (Fin.append A pr) B = t := by
    funext a
    refine Fin.addCases (fun u => ?_) (fun b => ?_) a
    · rw [Fin.append_left]
      refine Fin.addCases (fun v => ?_) (fun j => ?_) u
      · rw [Fin.append_left, hA]
      · rw [Fin.append_right, hpr]
    · rw [Fin.append_right, hB]
  clear hA hB hpr
  subst hfun
  have hzs : ∑ _a : Fin 1, z.1 = z.1 := by simp
  have h1 : ∑ a, (Fin.append A (fun _ : Fin 1 => z) a).1 = ∑ a, (A a).1 + z.1 := by rw [sum_app, hzs]
  have h2 : ∑ a, (Fin.append A pr a).1 = ∑ a, (A a).1 + z.1 := by rw [sum_app, hs]
  have hN : ∑ a, (A a).1 + z.1 + ∑ a, (B a).1 = N := by rw [← ht, sum_app, h2]
  subst hN
  have h3 : ∑ a, (Fin.append (Fin.append A (fun _ : Fin 1 => z)) B a).1 = ∑ a, (A a).1 + z.1 + ∑ a, (B a).1 := by
    rw [sum_app, h1]
  have e0 : Emb (prodIrr (fun _ : Fin 1 => z) hzs) (prodIrr pr hs) :=
    (Emb.of' (nonempty_equiv_prodIrr_one z hzs)).trans he
  refine ⟨_, _, h3, Fin.castAdd q (Fin.natAdd i (0 : Fin 1)), by rw [Fin.append_left, Fin.append_right], ?_⟩
  exact emb_left _ _ B h1 h2 rfl (emb_right A _ pr rfl hzs hs e0 h1 h2) h3 ht

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_alt_ter {d : ℕ} (σ : IrrRep (GL (Fin d) k)) {U : Type} [AddCommGroup U] [Module ℂ U]
    (τ : Representation ℂ (GL (Fin (2 * d)) k) U) (hsS : IsSmooth τ) (hiS : τ.IsIrreducible)
    (hs : ∑ j, (tcl σ 2 j).1 = 2 * d) (a2 : Emb τ (prodIrr (tcl σ 2) hs))
    (eS : (jac (consecBlocks 2 d) τ).Equiv (piTensor (segTerm σ.ρ 2))) :
    ∃ (z : IrrGL k) (hs : ∑ j, (tcl σ 2 j).1 = z.1), Emb z.rep (prodIrr (tcl σ 2) hs) ∧
      Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) z.rep).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
  have a1 : Emb (IrrGL.of τ hsS hiS).rep τ := Emb.of' ⟨IrrGL.equivOf τ hsS hiS⟩
  have he2 : stdBlocks (fun j => (tcl σ 2 j).1) hs = consecBlocks 2 d := blocks_eq 2 d hs
  have e1 : (piTensor (segTerm σ.ρ 2)).Equiv (piTensor fun a => (tcl σ 2 a).rep) :=
    piTensorEquiv fun a => IrrGL.equivOf _ _ _
  have a3 : Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) τ).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
    rw [he2]
    exact ⟨eS.trans e1⟩
  exact ⟨IrrGL.of τ hsS hiS, hs, a1.trans a2,
    ⟨(SrMult.jacEquivOf (stdBlocks (fun j => (tcl σ 2 j).1) hs) (IrrGL.equivOf τ hsS hiS).symm).trans a3.some⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_unit_one_add_generator (h2 : PositivityTheory.Pf1.SegRepC.SegTwo) {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) :
    ∃ (z : IrrGL k) (hs : ∑ j, (tcl σ 2 j).1 = z.1), Emb z.rep (prodIrr (tcl σ 2) hs) ∧
      Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) z.rep).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
  obtain ⟨S, hiS, -, ⟨eS⟩⟩ := h2 k d hd σ hσ
  have hs : ∑ j, (tcl σ 2 j).1 = 2 * d := sum_const_fin 2 d
  exact exists_alt_ter σ S.toRepresentation (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) S) hiS hs
    ((Emb.sub S).trans (Emb.of (consec_equiv σ 2 hs))) eS

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem one_le_jm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) {U X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X]
    [Module ℂ X] (τ : Representation ℂ (GL (Fin (l * d)) k) U) (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hsub : IsSubquotient π (jac (consecBlocks l d) τ)) (w : Equiv.Perm (Fin l))
    (φ : π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) (hy : ∑ a, (tcl σ l (w a)).1 = l * d) :
    1 ≤ Zc.jm (fun a => tcl σ l (w a)) hy τ := by
  have hey : stdBlocks (fun a => (tcl σ l (w a)).1) hy = consecBlocks l d := blocks_eq _ d hy
  refine ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 ?_)
  show IsSubquotient (piTensor fun a => (tcl σ l (w a)).rep) (jac (stdBlocks (fun a => (tcl σ l (w a)).1) hy) τ)
  rw [hey]
  have e1 : (piTensor fun a => segTerm σ.ρ l (w a)).Equiv (piTensor fun a => (tcl σ l (w a)).rep) :=
    piTensorEquiv fun a => IrrGL.equivOf _ _ _
  exact (GlobalTheory.JacStages.isSubquotient_of_equiv (e1.symm.trans φ.symm)).trans hsub

end StageC

open StageC in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem stageP : StageP := by
  intro k _ _ _ _ _ h2 d l hd _ σ hσ i hi
  obtain ⟨q, rfl⟩ : ∃ q, l = i + 2 + q := ⟨l - (i + 2), by omega⟩
  have hx : (cls σ).IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) hσ⟩
  obtain ⟨σ', hσ'c, hcls'⟩ : ∃ σ' : IrrRep (GL (Fin d) k), IsCuspidal σ'.ρ ∧ cls σ' = (cls σ).nu ((i : ℕ) : ℂ) :=
    ⟨((cls σ).nu ((i : ℕ) : ℂ)).2.rep, (hx.nu _).2, IrrGL.of_rep _⟩
  have hpr : ∀ j : Fin 2, tcl σ' 2 j = tcl σ (i + 2 + q) (Fin.castAdd q (Fin.natAdd i j)) := by
    intro j
    rw [tcl_eq, tcl_eq, hcls', IrrGL.nu_nu]
    congr 1
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    push_cast
    ring
  obtain ⟨z, hs, hz, hu⟩ := exists_unit_one_add_generator h2 hd σ' hσ'c
  have ht : ∑ a, (tcl σ (i + 2 + q) a).1 = (i + 2 + q) * d := sum_const_fin (i + 2 + q) d
  obtain ⟨n, xx, hdx, iz, hxz, he⟩ := classMain (tcl σ (i + 2 + q)) ht (tcl σ' 2) hpr z hs hz
  haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr xx hdx
  obtain ⟨T, hT, hTs⟩ := (he.trans (Emb.of' (consec_equiv σ (i + 2 + q) ht))).range
  refine ⟨T, hT, ?_⟩
  intro X _ _ π _ hsub w φ
  have hy : ∑ a, (tcl σ (i + 2 + q) (w a)).1 = (i + 2 + q) * d := sum_const_fin (i + 2 + q) d
  have hjm := (one_le_jm σ T.toRepresentation π hsub w φ hy).trans
    (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient _ hy _ _ (isSmooth_prodIrr xx hdx) hTs)
  have hsc : ∀ j, (tcl σ' 2 j).IsCusp := fun j => by
    rw [tcl_eq, hcls']
    exact (hx.nu _).nu _
  obtain ⟨f, hf⟩ := comb xx hdx iz z hxz (tcl σ' 2) hs d (fun _ => rfl) hsc hu _ hy
    (fun a => by rw [tcl_eq]; exact hx.nu _) hjm
  have hval : ∀ j : Fin 2, ((w (f j) : Fin (i + 2 + q)) : ℕ) = i + j := by
    intro j
    have h3 : tcl σ (i + 2 + q) (w (f j)) = tcl σ (i + 2 + q) (Fin.castAdd q (Fin.natAdd i j)) := (hf j).trans (hpr j)
    rw [tcl_eq, tcl_eq] at h3
    exact (IrrGL.nu_natCast_inj hx.1).1 h3
  have e0 : w.symm ⟨i, by omega⟩ = f 0 := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simpa using (hval 0).symm)
  have e1 : w.symm ⟨i + 1, hi⟩ = f 1 := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simpa using (hval 1).symm)
  rw [e0, e1]
  exact f.strictMono (by decide)

end PositivityTheory.RgGu.SRC

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.Published

namespace PositivityTheory.RgGu.NR

namespace RedC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irr_congr {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (x' a).1 = N, ((prodIrr x hd).IsIrreducible ↔ (prodIrr x' hd').IsIrreducible) := by
  subst e
  exact ⟨hd, Iff.rfl⟩

theorem irr_tw {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (s : ℂ)
    (hi : (prodIrr x hd).IsIrreducible) : (prodIrr (fun a => (x a).nu s) hd).IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv (prodIrrTwistEquiv x hd (absPow k s) (isSmoothChar_absPow s))
    (isIrreducible_twist hi _)

end RedC

open RedC in
set_option maxHeartbeats 800000 in
theorem redCl_ofC (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : SomeRed k) (h2 : CuspUnit k) (h3 : GlobalTheory.BZSeg.CuspPairIrr k) : RedCl k := by
  intro y hy N hd hirr
  obtain ⟨ρ, z, hρ, hu, rfl⟩ := h2 y hy
  obtain ⟨s, hs0, hs⟩ := h1 ρ hρ hu
  have hpos : 0 < ρ.1 := hρ.1
  have hs2 : s = 1 / 2 := by
    by_contra hne
    have hd0 : ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 = ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 := rfl
    refine hs _ hd0 (h3 _ _ _ hd0 (hρ.nu _) (hρ.nu _) ?_ ?_)
    · intro e
      rw [IrrGL.nu_nu, show -(s : ℂ) + 1 = ((-s + 1 : ℝ) : ℂ) by push_cast; ring] at e
      have := (IrrGL.nu_ofReal_inj hpos).1 e
      exact hne (by linarith)
    · intro e
      rw [IrrGL.nu_nu, show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
        show (s : ℂ) + 1 = ((s + 1 : ℝ) : ℂ) by push_cast; ring] at e
      have := (IrrGL.nu_ofReal_inj hpos).1 e
      linarith
  set t : ℂ := -((z : ℂ) + 1 / 2) with ht
  have key : (fun a => (![ρ.nu (z : ℂ), (ρ.nu (z : ℂ)).nu 1] a).nu t) = ![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] := by
    funext a
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [IrrGL.nu_nu, hs2, ht]
      congr 1
      push_cast
      ring
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [IrrGL.nu_nu, IrrGL.nu_nu, hs2, ht]
      congr 1
      push_cast
      ring
  obtain ⟨hd', hiff⟩ := irr_congr key hd
  exact hs N hd' (hiff.1 (irr_tw _ hd t hirr))

theorem rhoNuRho_ofC (h : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    RedCl k) : PositivityTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := by
  intro k _ _ _ _ d hd σ hσ hirr
  set y : IrrGL k := IrrGL.of σ.ρ σ.smooth σ.irr with hy
  have hyc : y.IsCusp := IrrGL.isCusp_of.2 ⟨hd, hσ⟩
  let x : Fin 2 → IrrGL k := fun a => y.nu ((a : ℕ) : ℂ)
  have hx1 : ∀ a, (x a).1 = d := fun _ => rfl
  have hdx : ∑ a, (x a).1 = 2 * d := by
    simp only [hx1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  let φ : ∀ a : Fin 2, (segTerm σ.ρ 2 a).Equiv (x a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (y.twEquiv _ _)
  have E1 := multiProdEquiv (consecBlocks 2 d) φ
  have hdd : ∑ _a : Fin 2, d = 2 * d := by simp
  have hE : consecBlocks 2 d = stdBlocks (fun _ : Fin 2 => d) hdd := by
    ext ⟨a, i⟩
    rw [consecBlocks_val, stdBlocks_val]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h3 : (prodIrr x hdx).IsIrreducible := by
    have h4 := GlobalTheory.Parabolic.isIrreducible_of_equiv E1 hirr
    rw [hE] at h4
    exact h4
  have e : x = ![y, y.nu 1] := by
    funext a
    fin_cases a
    · simp [x]
    · simp [x]
  obtain ⟨hd', hiff⟩ := RedC.irr_congr e hdx
  exact h k y hyc (2 * d) hd' (hiff.1 h3)

end PositivityTheory.RgGu.NR
end
end

section
namespace PositivityTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem redClC : RedCl k :=
  redCl_ofC k (someRed_of k (complementary_of signature) (compact k) (boundB k) (herm_ofB k (conjProd k) (conjDual k))
    (prodModel k)) (cuspUnit k) (cuspPairIrr k)

theorem rhoNuRhoReducibleC : PositivityTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := rhoNuRho_ofC fun k _ _ _ _ => redClC k

end PositivityTheory.RgGu.NR
end

section
namespace PositivityTheory.RgGu

theorem segmentRepresentation : GlobalTheory.Published.SegmentRepresentation :=
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness PositivityTheory.Geo.geometricLemmaFiltration
  SRC.segRep_of SRC.stageP hG (SRC.segTwo_of hG NR.rhoNuRhoReducibleC)

end PositivityTheory.RgGu
end
