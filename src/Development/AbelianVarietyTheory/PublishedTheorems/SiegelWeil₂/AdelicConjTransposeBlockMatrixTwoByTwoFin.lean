import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundedCommutantVacua

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero GlobalTheory.ThetaMean GlobalTheory.SiegelFormula.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelWeilMiddle.Model

variable {D : D7}

abbrev iso9 (D : D7) : HSp D := Examples₂.lorentzSpace (E := D.host.E) Examples₂.star_isIntegral

theorem wittIndex_eq_one (D : D7) : Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) = 1 := by
  have h1 : Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) ≤ 1 :=
    (GlobalTheory.WittSignature.wittIdx_le_signature D.host.E (iso9 D) (Examples₂.lorentzSpace_signature_ok _) D.host.φ₀
      (D.sp.cm.cmUnram.2.1 D.host.φ₀)).2
  let v : Fin (8 + 1) → D.host.E := Pi.single 0 1 + Pi.single 8 1
  have hv : v ≠ 0 := fun h => by simpa [v] using congrFun h 0
  have h0 : Examples₂.diagForm (E := D.host.E) (8 + 1) Examples₂.negLast v v = 0 := by
    simp [Examples₂.diagForm_apply, v, Fin.sum_univ_succ, Examples₂.sgn, Examples₂.negLast, Pi.single_apply]
  have h2 : 1 ≤ Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) := le_csSup (bddAbove_witt _)
    ⟨Submodule.span D.host.E {(v : (iso9 D).V)}, finrank_span_singleton hv, by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
      change Examples₂.diagForm (E := D.host.E) (8 + 1) Examples₂.negLast (a • v) (b • v) = 0
      simp [h0]⟩
  omega

theorem range_inhabited (D : D7) :
    (∃ A B : HSp D, 0 < Formalism.MainNotions.SchurIrreducible.wittIdx B ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧
      A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) ∧
    (∃ A B : HSp D, B.rank = 2 * A.rank ∧ A.rank < B.rank ∧ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) :=
  ⟨⟨pos D 5, iso9 D, by rw [wittIndex_eq_one]; decide, show 5 < 8 + 1 by decide, show 8 + 1 ≤ 2 * 5 by decide,
    by rw [wittIndex_eq_one]; exact show 5 + 1 < 8 + 1 by decide⟩,
   ⟨pos D 1, pos D 2, rfl, show 1 < 2 by decide, by rw [wittIdx_pos]; exact show 1 + 0 < 2 by decide⟩⟩


theorem hypotheses_inhabited (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)),
      0 < Formalism.MainNotions.SchurIrreducible.wittIdx B ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank ∧
        IsWeilDatumO ψ (dblSp A) B 1 χB ω ∧ IsMaj A a ∧ IsCovolOne (ratL B A) μ 𝓨 ∧ ν.IsHaarMeasure ∧
        (∃ f, IsThetaFunO ψ (dblSp A) B f ∧ f ≠ 0) ∧ ∃ f, IsThetaFunO ψ (dblSp A) B f ∧ IsKFinVec ω (Khat A a) f := by
  obtain ⟨A, B, h0, h1, h2, h3⟩ := (range_inhabited D).1
  obtain ⟨m, ψ, χ, ω, f, μ, 𝓨, hm, hω, hf, hf0, hμ⟩ := data_exist H A B
  obtain ⟨a, ha⟩ := exists_isMaj A
  exact ⟨ψ, A, B, χ, ω, a, μ, 𝓨, m, h0, h1, h2, h3, hω, ha, hμ, hm, ⟨f, hf, hf0⟩,
    0, GlobalTheory.ThetaMean.Model.zero_vec ψ _ B ω _⟩




theorem weilPair : GlobalTheory.Published.WeilRepresentationUnitaryPair := fun D ψ S T χS χT hψ h1 h2 h3 h4 =>
  GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT
    ((GlobalTheory.WeilParts.exists_isEtaTilde_unramified D).imp fun _ h => h) h1 h2 h3 h4

theorem all_hypotheses_inhabited (D : D7) (A B : HSp D) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (χB : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (θ : InfFam D) (sS : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.RealMat (dblSp A)) (sB : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.RealMat B)
      (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)) (f : WO (dblSp A) B → ℂ),
      IsWeilDatumO ψ (dblSp A) B 1 χB ω ∧ IsMaj A a ∧ HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) ∧ IsInfFam θ ∧
        (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) ∧ (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧
        (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
          sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) ∧
        IsCovolOne (ratL B A) μ 𝓨 ∧ ν.IsHaarMeasure ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ (dblSp A) B sS sB f ∧ f ≠ 0 := by
  obtain ⟨m, ψ, χ, ω, -, μ, 𝓨, hm, hω, -, -, hμ⟩ := data_exist weilPair A B
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨a, ha, hfr⟩ := GlobalTheory.Core.Rk.MajFrame.exists_maj_cart D θ A (s A) hθ (hs A)
  obtain ⟨h1, h2⟩ := GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl D θ A (s A) a hθ (hs A) hfr
  obtain ⟨f, hf, f0⟩ := GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua.exists_isVac_ne_zero hω.std hθ h1 (hs B)
  refine ⟨ψ, χ, ω, a, θ, _, s B, μ, 𝓨, m, f, hω, ha, GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha, hθ, h1, hs B, h2, hμ, hm,
    ⟨hf.1, 1, fun l hl => ?_⟩, f0⟩
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
  exact hf.2 p.1 p.2

end GlobalTheory.SiegelWeilMiddle.Model

end
end

section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem submatrix_fromBlocks_mul {R : Type} [CommRing R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' = blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_injective {R : Type} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R} (h : blk4 a b c d = blk4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have := congrArg (fun M => Matrix.submatrix M finSumFinEquiv finSumFinEquiv) h
  simpa [blk4, Matrix.fromBlocks_inj] using this

theorem adelicConjTranspose_blockMatrixTwoByTwoFin (a b c d : Mx D n n) :
    adj (blk4 a b c d : Mx D (n + n) (n + n)) = blk4 (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem JR_Jst : (JR (AF D.host.F) (Jst D n) : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  ext i j
  simp only [JR, Jst, blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem exists_mat (M N : Mx D (n + n) (n + n)) (h1 : M * N = 1) (h2 : N * M = 1)
    (h : adj M * blk4 0 1 (-1) 0 * M = blk4 0 1 (-1) 0) : ∃ g : G D n, mat g = M :=
  ⟨⟨⟨M, N, h1, h2⟩, by
    change adj M * JR (AF D.host.F) (Jst D n) * M = JR (AF D.host.F) (Jst D n)
    rw [JR_Jst]; exact h⟩, rfl⟩

theorem exists_levi (a : GL (Fin n) (AE D)) : ∃ g : G D n, mat g = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  have h1 : (adj a.1 : Mx D n n) * adj (a⁻¹).1 = 1 := by rw [← adj_mul]; simp [adj_one]
  have h2 : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by rw [← adj_mul]; simp [adj_one]
  refine exists_mat _ (blk4 (a⁻¹).1 0 0 (adj a.1)) ?_ ?_ ?_
  · simp [submatrix_fromBlocks_mul, h2, block_matrix_one, -Matrix.coe_units_inv]
  · simp [submatrix_fromBlocks_mul, h1, block_matrix_one, -Matrix.coe_units_inv]
  · simp [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, h1, adj_zero, adj_adj, -Matrix.coe_units_inv]

theorem exists_unip (b : Mx D n n) : (∃ g : G D n, mat g = blk4 1 b 0 1) ↔ adj b = b := by
  constructor
  · rintro ⟨g, hg⟩
    have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
    rw [JR_Jst, hg] at h
    simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_one, adj_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, mul_neg,
      neg_mul] at h
    exact (neg_add_eq_zero.1 (blockMatrixTwoByTwoFin_injective h).2.2.2).symm
  · intro hb
    refine exists_mat _ (blk4 1 (-b) 0 1) ?_ ?_ ?_
    · simp [submatrix_fromBlocks_mul, block_matrix_one]
    · simp [submatrix_fromBlocks_mul, block_matrix_one]
    · simp [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_zero, adj_one, hb]

theorem exists_weyl : ∃ g : G D n, mat g = blk4 0 1 (-1) 0 := by
  refine exists_mat _ (blk4 0 (-1) 1 0) ?_ ?_ ?_
  · simp [submatrix_fromBlocks_mul, block_matrix_one]
  · simp [submatrix_fromBlocks_mul, block_matrix_one]
  · simp [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_zero, adj_one, adj_neg]



theorem lower_eq_zero {p : G D n} (hp : p ∈ P D n) (i j : Fin n) :
    mat p (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  have h := (hp (Pi.single (finSumFinEquiv (.inl j)) 1)).1 (by
    ext k
    have : (finSumFinEquiv (Sum.inr k : Fin n ⊕ Fin n)) ≠ finSumFinEquiv (.inl j) := by
      rw [Ne, finSumFinEquiv.apply_eq_iff_eq]; simp
    simp only [LinearMap.funLeft_apply, Pi.single_eq_of_ne this, Pi.zero_apply])
  have h2 := congrFun h i
  simp only [LinearMap.funLeft_apply, Matrix.mulVec_single_one, Pi.zero_apply] at h2
  exact h2

theorem blkA_mul {p q : G D n} (hq : q ∈ P D n) : blkA (mat (p * q)) = blkA (mat p) * blkA (mat q) := by
  ext i j
  have e : mat (p * q) = mat p * mat q := rfl
  simp only [e, blkA, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [lower_eq_zero hq, mul_zero, Finset.sum_const_zero, add_zero]

theorem blkA_one : blkA (mat (1 : G D n)) = 1 := by
  have e : mat (1 : G D n) = 1 := rfl
  rw [e, blkA, Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

def levi : P D n →* GL (Fin n) (AE D) :=
  MonoidHom.toHomUnits ⟨⟨fun p => blkA (mat p.1), blkA_one⟩, fun p q => blkA_mul q.2⟩

theorem continuous_mat : Continuous (mat : G D n → Mx D (n + n) (n + n)) :=
  Units.continuous_val.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous

theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE D) → (AE D)ˣ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  rw [Units.continuous_iff]
  refine ⟨Units.continuous_val.matrix_det, (Units.continuous_coe_inv.matrix_det).congr fun g => ?_⟩
  rw [← map_inv]; rfl

theorem isCompact_K : IsCompact (K D n : Set (G D n)) :=
  haveI : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  isCompact_levelAll (isCMExt_host D) _ _ _

theorem isClosed_P : IsClosed (P D n : Set (G D n)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : (P D n : Set (G D n)) = ⋂ x ∈ upperHalf D n, ({g | (mat g).mulVec x ∈ upperHalf D n} ∩
      {g | (mat g⁻¹).mulVec x ∈ upperHalf D n}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe]
    refine ⟨fun h x hx => ⟨(h x).1 hx, ((P D n).inv_mem h x).1 hx⟩, fun h x => ⟨fun hx => (h x hx).1, fun hx => ?_⟩⟩
    have := (h _ hx).2
    change (mat g⁻¹).mulVec ((mat g).mulVec x) ∈ _ at this
    rwa [Matrix.mulVec_mulVec, show mat g⁻¹ * mat g = mat (g⁻¹ * g) from rfl, inv_mul_cancel,
      show mat (1 : G D n) = 1 from rfl, Matrix.one_mulVec] at this
  have hU : IsClosed (upperHalf D n : Set (Fin (n + n) → AE D)) :=
    isClosed_eq (f := fun (x : Fin (n + n) → AE D) (i : Fin n) => x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)))
      (g := fun _ => 0) (continuous_pi fun i => continuous_apply _) continuous_const
  rw [this]
  exact isClosed_biInter fun x _ => (hU.preimage (continuous_mat.matrix_mulVec continuous_const)).inter
    (hU.preimage ((continuous_mat.comp continuous_inv).matrix_mulVec continuous_const))

end GlobalTheory.StdUnn.Model

end
end
