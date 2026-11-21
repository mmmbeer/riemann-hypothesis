import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.VanishOrdL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocPublishedOfLitCoh
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsExtra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUpperTriangularConjIntegralCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedOfLevelAwayInertiaCharacters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterPowPredEqOneOfKillsPrimeRoots
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement

section
open Formalism.MainNotions.N

namespace GlobalTheory.ConjugateIrreducibility

private theorem isIrrSub_of_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H H' : Subgroup Γ)
    (hHH : ∀ s ∈ H, s ∈ H') (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (hconj : ∀ s : Γ, (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹)
    (hne : (⊤ : Submodule k (Fin n → k)) ≠ ⊥)
    (hmin : ∀ W : Submodule k (Fin n → k), W ≤ ⊤ → IsInv (MonoidHom.comp r (Subgroup.subtype H)) W →
      W = ⊥ ∨ W = ⊤) :
    IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hinv => ?_⟩

  let W₀ : Submodule k (Fin n → k) := W.comap (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v, v ∈ W₀ ↔ (g : Matrix (Fin n) (Fin n) k).mulVec v ∈ W := fun v => by
    simp [W₀, Matrix.toLin'_apply]
  have hinv₀ : IsInv (MonoidHom.comp r (Subgroup.subtype H)) W₀ := by
    intro s v hv
    rw [hmem] at hv ⊢
    have key : (g : Matrix (Fin n) (Fin n) k).mulVec ((r s.1 : Matrix (Fin n) (Fin n) k).mulVec v) =
        (r' s.1 : Matrix (Fin n) (Fin n) k).mulVec ((g : Matrix (Fin n) (Fin n) k).mulVec v) := by
      simp [hconj, Matrix.mulVec_mulVec, mul_assoc]
    have h1 := hinv ⟨s, hHH s s.2⟩ _ hv
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢
    rw [key]
    exact h1
  have hback : ∀ w, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w ∈ W₀ ↔ w ∈ W := fun w => by
    rw [hmem, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rcases hmin W₀ le_top hinv₀ with h0 | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 := (hback w).mpr hw
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg (Matrix.mulVec (g : Matrix (Fin n) (Fin n) k)) h1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [h2]
    exact Submodule.zero_mem _
  · right
    rw [eq_top_iff]
    intro w _
    exact (hback w).mp (htop ▸ Submodule.mem_top)

theorem main {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H H' : Subgroup Γ) (hHH : ∀ s ∈ H, s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (hconj : ∀ s : Γ, (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹)
    (hirr : IsIrrSub (MonoidHom.comp r (Subgroup.subtype H)) ⊤) :
    IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  obtain ⟨hne, -, hmin⟩ := hirr
  exact isIrrSub_of_conj H H' hHH r r' g hconj hne hmin

theorem target : ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (H H' : Subgroup Γ), (∀ s ∈ H, s ∈ H') → ∀ (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k), (∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹) → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r (Subgroup.subtype H)) ⊤ → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  intro Γ k _ _ n H H' hHH r r' g hconj hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  exact isIrrSub_of_conj H H' hHH r r' g hconj hne hmin

end GlobalTheory.ConjugateIrreducibility
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.IrrConj

theorem isIrrSub_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (H H' : Subgroup Γ) (hH : ∀ s, s ∈ H → s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsIrrSub (r.comp H.subtype) ⊤) : IsIrrSub (r'.comp H'.subtype) ⊤ := by
  first
  | exact @_root_.GlobalTheory.ConjugateIrreducibility.target
  | exact _root_.GlobalTheory.ConjugateIrreducibility.target
  | (apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateIrreducibility.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateIrreducibility.target ..)

theorem dt_eq_of_repIso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    (W W' : R2 Ω l) (g : GL (Fin 2) (Qbar l)) (hg : ∀ s, W' s = g * W s * g⁻¹) (s : G ℚ Ω) :
    dt W' s = dt W s := by
  simp only [dt, MonoidHom.comp_apply, hg s, map_mul, map_inv]
  rw [mul_comm (Matrix.GeneralLinearGroup.det g), mul_assoc, mul_inv_cancel, mul_one]

theorem irr_of_repIso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l),
    RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  intro Ω _ _ l _ W W' ⟨g, hg⟩ h
  refine isIrrSub_conj (H0g W) (H0g W') ?_ W W' g hg h
  intro s hs
  simp only [H0g, Subgroup.mem_inf, MonoidHom.mem_ker] at hs ⊢
  exact ⟨hs.1, by rw [dt_eq_of_repIso W W' g hg]; exact hs.2⟩

end GlobalTheory.IrrConj
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_restriction_of_iso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l), RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  atlas_forward_decl GlobalTheory.IrrConj.irr_of_repIso
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfEx

theorem up2 {k : Type} [Field k] (X Y Z : Matrix (Fin 2) (Fin 2) k) (hX : X 1 0 = 0) (hY : Y 1 0 = 0) (hZ : Z 1 0 = 0) :
    (X * Y * Z) 1 0 = 0 ∧ (X * Y * Z) 0 0 = X 0 0 * Y 0 0 * Z 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hX, hY, hZ]

theorem inv_up {k : Type} [Field k] (B : GL (Fin 2) k) (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧
    (B : Matrix (Fin 2) (Fin 2) k) 0 0 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
  have key : ∀ i j, ∑ x, (B : Matrix (Fin 2) (Fin 2) k) i x * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) x j =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j => by
    rw [← Matrix.mul_apply, B.mul_inv]
  have e10 := key 1 0
  have e11 := key 1 1
  have e00 := key 0 0
  rw [Fin.sum_univ_two, hB, zero_mul, zero_add] at e10 e11
  rw [Fin.sum_univ_two] at e00
  rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e10
  rw [Matrix.one_apply_eq] at e11 e00
  have hN : ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rcases mul_eq_zero.1 e10 with h | h
    · rw [h, zero_mul] at e11
      exact absurd e11 zero_ne_one
    · exact h
  refine ⟨hN, ?_⟩
  rw [hN, mul_zero, add_zero] at e00
  exact e00

end GlobalTheory.NfEx

end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SrcConj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem tw_conj (r r' : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : GL (Fin n) k)
    (h : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) : tw r' χ s = g * tw r χ s * g⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, tw_val, tw_val, h s, Units.val_mul, Units.val_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem isSSRep_conj (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (h : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsSSRep r) : IsSSRep r' := by
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ?_ ?_ hr
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · intro s
    rw [h s, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

theorem att_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k' : ℕ}
    (f : Newform k') (V V' : G ℚ Ω →* GL (Fin 2) (Qbar l)) (g : GL (Fin 2) (Qbar l))
    (h : ∀ s, V' s = g * V s * g⁻¹) (hV : f.Att ι V) : f.Att ι V' := by
  refine ⟨isSSRep_conj V V' g h hV.1, hV.2.mono fun w hw A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hw A hA
  refine ⟨fun s hs => by rw [h s, hI s hs, mul_one, mul_inv_cancel], fun σ hσ => ?_⟩
  rw [← hF σ hσ, h σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end GlobalTheory.Ord2.SrcConj

end
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfSrc

theorem upper_triangular_conj_lower_right_entry_eq {k : Type} [Field k] (B : GL (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k)
    (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (hX : X 1 0 = 0) :
    ((B : Matrix (Fin 2) (Fin 2) k) * X * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = X 1 1 := by
  have hinv := GlobalTheory.NfEx.inv_up B hB
  have h1 : ((B⁻¹ * B : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by simp
  have a11 := congrFun (congrFun h1 1) 1
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv.1, zero_mul, zero_add, Matrix.one_apply_eq] at a11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hB, hX, zero_mul, zero_add, mul_zero]
  calc _ = X 1 1 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1 * (B : Matrix (Fin 2) (Fin 2) k) 1 1 := by ring
    _ = _ := by rw [mul_assoc, a11, mul_one]

end GlobalTheory.NfSrc

theorem GlobalTheory.Ord2.exists_nf_srcUr : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → SrcL ι e W → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l) (g : Newform (2 * e + 1)), RepIso W W' ∧ Nf e S A W' ∧ SrcUr ι e A W' g := by
  intro l _ Ω _ _ _ ι e W hl he hW hS
  obtain ⟨⟨g0, χ, A, κ, hM0, ha0, hχ, hatt, hA, hfl, hin⟩, hne⟩ := hS
  obtain ⟨g, hg⟩ := hfl
  obtain ⟨M, hM, hMa⟩ := hW.away
  obtain ⟨S, hSa, hSu⟩ := GlobalTheory.T.unramified_of_levelAway_inertia_characters l Ω W M hM hMa
  let r : G ℚ Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj g).toMonoidHom.comp W
  have hrc : Continuous r := by
    show Continuous fun s => g * W s * g⁻¹
    exact (continuous_const.mul hW.cont).mul continuous_const
  obtain ⟨E, hE, hEm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l (G ℚ Ω) 2 r
    (fun i j => ((Units.continuous_val.comp hrc).matrix_elem i j))
  obtain ⟨B, hB10, hBint⟩ := GlobalTheory.T.exists_upperTriangular_conj_integral_compact l (G ℚ Ω) E r hE hrc hEm
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coefficientRing_finiteExtension_padic l E hE
  let h : GL (Fin 2) (Qbar l) := B * g
  let W' : R2 Ω l := (MulAut.conj h).toMonoidHom.comp W
  have hh : ∀ s, W' s = h * W s * h⁻¹ := fun s => rfl
  have hW' : ∀ s, W' s = B * r s * B⁻¹ := fun s => by
    show h * W s * h⁻¹ = B * (g * W s * g⁻¹) * B⁻¹
    simp only [h, mul_inv_rev]; group
  have hiso : RepIso W W' := ⟨h, hh⟩
  have hdt : dt W' = dt W := by
    ext s
    rw [GlobalTheory.Ord2.TwDet.dt_coe, GlobalTheory.Ord2.TwDet.dt_conj W h s]
    rfl
  have hdet : ∀ s, (dt W' s : Qbar l) = (mat W' s).det := fun s => rfl
  have hker : ∀ s, W' s = 1 ↔ W s = 1 := fun s => by
    show h * W s * h⁻¹ = 1 ↔ W s = 1
    constructor
    · intro hh; rw [mul_inv_eq_one, mul_eq_left] at hh; exact hh
    · intro hh; rw [hh]; simp
  have hinv := GlobalTheory.NfEx.inv_up B hB10
  have hup : ∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) A), mat W' s 1 0 = 0 ∧ mat W' s 0 0 = (κ 0 ⟨s, hs⟩ : Qbar l) ∧
      mat W' s 1 1 = (κ 1 ⟨s, hs⟩ : Qbar l) := by
    intro s hs
    have h1 := (hg ⟨s, hs⟩).1 1 0 (by decide)
    have h2 := (hg ⟨s, hs⟩).2 0
    have h3 := (hg ⟨s, hs⟩).2 1
    have := GlobalTheory.NfEx.up2 (B : Matrix (Fin 2) (Fin 2) (Qbar l)) ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
      ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1 hinv.1
    have e1 : mat W' s = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      simp only [mat, hW', Units.val_mul]
    refine ⟨by rw [e1]; exact this.1, ?_, ?_⟩
    · rw [e1, this.2, ← h2]
      change _ = ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0
      calc _ = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 := by ring
        _ = _ := by rw [hinv.2, one_mul]
    · rw [e1, GlobalTheory.NfSrc.upper_triangular_conj_lower_right_entry_eq B ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1]
      exact h3

  have hline : ∀ (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) A),
      mat W' s 0 0 = eps l s ^ e * (χ s : Qbar l) := by
    intro s hs
    have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
    obtain ⟨u10, u00, u11⟩ := hup s hd
    have hi := hin ⟨s, hd⟩ hs
    have hD : (dt W s : Qbar l) = mat W' s 0 0 * mat W' s 1 1 := by
      rw [← hdt, hdet, Matrix.det_fin_two, u10, mul_zero, sub_zero]
    have hdne : (dt W s : Qbar l) ≠ 0 := Units.ne_zero _
    simp only [zpow_natCast] at hi
    rw [← u11] at hi
    simp only [eps]
    calc mat W' s 0 0 = mat W' s 0 0 * (mat W' s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ e * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l))) := by
          rw [hi, mul_one]
      _ = (mat W' s 0 0 * mat W' s 1 1) * (dt W s : Qbar l)⁻¹ * ((cycBar ℚ Ω l s : Qbar l) ^ e * (χ s : Qbar l)) := by ring
      _ = _ := by rw [← hD, mul_inv_cancel₀ hdne, one_mul]
  refine ⟨S, A, W', g0, hiso, ?_, ?_⟩
  · refine
      { l_odd := hl
        e_pos := he
        cont := ?_
        int := ⟨c, fun s i j => (hc _).2 ⟨?_, ?_⟩⟩
        above := hSa
        unr := ?_
        det2 := by rw [hdt]; exact hW.det2
        odd := by rw [hdt]; exact hW.odd
        irr := GlobalTheory.T.irreducible_restriction_of_iso Ω l W W' hiso hW.irr
        atL := hA
        upper := fun s hs => (hup s hs).1
        wt := ?_
        ne := ?_ }
    · show Continuous fun s => h * W s * h⁻¹
      exact (continuous_const.mul hW.cont).mul continuous_const
    · have := (hBint s i j).1; simpa only [mat, hW'] using this
    · have := (hBint s i j).2; simpa only [mat, hW'] using this
    · intro w hw B' hB' s hs
      exact (hker s).2 (hSu w hw B' hB' hs)
    · refine ⟨l - 1, ?_, fun s hs => ?_⟩
      · have := (Fact.out : l.Prime).two_le; omega
      · rw [hline s hs, mul_pow, ← pow_mul]
        have hχ1 := GlobalTheory.T.character_pow_pred_eq_one_of_killsPrimeRoots Ω l _ χ s hχ
        rw [← Units.val_pow_eq_pow_val (χ s), hχ1, Units.val_one, mul_one]
    · obtain ⟨s, hs⟩ := hne A κ hA ⟨g, hg⟩
      refine ⟨s, s.2, ?_⟩
      rw [(hup s s.2).2.1]
      intro hh
      exact hs (Units.ext hh)
  · refine ⟨hM0, ha0, χ, hχ, ?_, ?_⟩
    · rw [hdt]
      exact SrcConj.att_conj ι g0 _ _ h (SrcConj.tw_conj W W' _ h hh) hatt
    · intro s hs
      have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
      rw [(hup s hd).2.2, hdt]
      exact hin ⟨s, hd⟩ hs

end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ordinary_normal_form_unramified_source : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → SrcL ι e W → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l) (g : Newform (2 * e + 1)), RepIso W W' ∧ Nf e S A W' ∧ SrcUr ι e A W' g := by
  atlas_forward_decl GlobalTheory.Ord2.exists_nf_srcUr
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem repIso_symm_srcL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W W' : R2 Ω l}
    (h : RepIso W W') : RepIso W' W := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, fun s => ?_⟩
  rw [hg s]
  group

theorem vanishOrdL_of_zetaUr : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ZetaUr → VanishOrdL := by
  intro hC hZ l _ hl Ω _ _ _ ι e he W hW hS
  obtain ⟨S, A, W', g, hiso, hnf, hsrc⟩ := GlobalTheory.T.exists_ordinary_normal_form_unramified_source l Ω ι e W hl he hW hS
  have hes : ES W' A := hZ l Ω ι e S A W' g hnf hsrc
  have hv : BlochKatoSelmerVanishes l (Loc.colRep W') := GlobalTheory.Ord2.es_vanish hC l Ω e S A W' hnf hes
  exact UpperTheory.V.X.Kato.conj l ℚ Ω 2 W' W (repIso_symm_srcL hiso) hv

end GlobalTheory.Ord2
end
