import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRUpLoc
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesRationalFormZero
import Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem adms_int (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal)
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy : y ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)) (p q : Fin n) :
    ((((L.fr i v hv)⁻¹ * bc (G.phi i v hv) y * L.fr i v hv : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q) ∈ v.adicCompletionIntegers F := by
  classical
  set fr := L.fr i v hv
  set w : Fin n → v.adicCompletion F := (fr : Matrix (Fin n) (Fin n) _) *ᵥ Pi.single q 1 with hw
  have hw' : ∀ b, (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) b ∈
      v.adicCompletionIntegers F := by
    intro b
    rw [hw, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    by_cases h : b = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  obtain ⟨y0, hy0, hy0w⟩ := (L.fr_lat i v hv w).2 hw'
  have hyy : (y : Matrix (Fin n) (Fin n) _) *ᵥ y0 ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := (hy y0).1 hy0
  have h1 := (L.fr_lat i v hv (fun b => G.phi i v hv (((y : Matrix (Fin n) (Fin n) _) *ᵥ y0) b))).1 ⟨_, hyy, fun b => rfl⟩ p
  have e1 : (fun b => G.phi i v hv (((y : Matrix (Fin n) (Fin n) _) *ᵥ y0) b)) =
      ((bc (G.phi i v hv) y : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w := by
    have e2 : w = fun b => G.phi i v hv (y0 b) := funext fun b => (hy0w b).symm
    rw [e2]
    funext b
    exact (RingHom.map_mulVec (G.phi i v hv) (y : Matrix (Fin n) (Fin n) _) y0 b)
  rw [e1, mulVec_mulVec, hw, mulVec_mulVec] at h1
  have e3 : (((fr⁻¹ * bc (G.phi i v hv) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
      (Pi.single q (1 : v.adicCompletion F) : Fin n → v.adicCompletion F)) p = (((fr⁻¹ * bc (G.phi i v hv) y * fr : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) _) p q) := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [← e3]
  simpa only [Units.val_mul, Matrix.mul_assoc] using h1

end Loc

section AdmsGL

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

set_option maxHeartbeats 1000000 in

theorem adms_gl (v : HeightOneSpectrum (𝓞 F)) (M : GL (Fin n) (v.adicCompletion F))
    (hA : ∀ p q, (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q ∈ v.adicCompletionIntegers F)
    (hB : ∀ p q, ((M⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q ∈
      v.adicCompletionIntegers F)
    (hU : ∀ p q : Fin n, (q < p → redM F v (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q = 0) ∧
      redM F v (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p p = 1) :
    M ∈ iwU F n v := by
  classical
  let A : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := fun p q => ⟨_, hA p q⟩
  let B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := fun p q => ⟨_, hB p q⟩
  have hinj : ∀ P Q : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F),
      P.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
        Q.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) → P = Q := by
    intro P Q h
    funext p q
    exact Subtype.ext (congrFun (congrFun h p) q)
  have hAmap : A.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
      (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    funext p q; rfl
  have hBmap : B.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
      ((M⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    funext p q; rfl
  have hAB : A * B = 1 := by
    apply hinj
    rw [Matrix.map_mul, hAmap, hBmap, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : B * A = 1 := by
    apply hinj
    rw [Matrix.map_mul, hAmap, hBmap, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  let g0 : GL (Fin n) (v.adicCompletionIntegers F) := ⟨A, B, hAB, hBA⟩
  refine Subgroup.mem_map.2 ⟨g0, ?_, Units.ext hAmap⟩
  apply Subgroup.subset_closure
  intro p q
  have hred : ∀ p' q', ((redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g0 :
      GL (Fin n) ((v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) :
      Matrix (Fin n) (Fin n) ((v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) p' q' =
      (redM F v (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p' q' :
        (v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) := by
    intro p' q'
    simp only [redM]
    rw [dif_pos (hA p' q')]
    rfl
  exact ⟨fun hqp => by rw [hred]; exact (hU p q).1 hqp, by rw [hred]; exact (hU p p).2⟩

end AdmsGL

section Loc2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

set_option maxHeartbeats 1000000 in

theorem adms_iwU (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) (ha : n ≤ a) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ S.Uloc v) :
    (L.fr i v hv)⁻¹ * bc (G.phi i v hv) x * L.fr i v hv ∈ iwU F n v := by
  have hlev := S.Uloc_lev v hx
  have hI := (L.mem i v hv x hlev).1 hx
  have hst : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := hlev.2
  have hinv : ((L.fr i v hv)⁻¹ * bc (G.phi i v hv) x * L.fr i v hv)⁻¹ =
      (L.fr i v hv)⁻¹ * bc (G.phi i v hv) x⁻¹ * L.fr i v hv := by
    rw [map_inv]; group
  refine adms_gl v _ (adms_int S G L i v hv x hst)
    (by rw [hinv]; exact adms_int S G L i v hv x⁻¹ ((stabGL _).inv_mem hst)) fun p q => ?_
  refine ⟨fun hqp => hI.1 p q ?_, hI.2.1 p (lt_of_lt_of_le p.2 ha)⟩
  simp only [blkOf, if_pos (lt_of_lt_of_le q.2 ha), if_pos (lt_of_lt_of_le p.2 ha)]
  exact hqp

end Loc2

section Tied

variable {D : D7} {u : D.what₂.Word}

theorem rank_zero_le_admissible_bound : D.R.N 0 ≤ aOf D.R 0 := by
  have := D.R.two_le_m
  unfold aOf Ranks.N
  rw [if_pos (by omega)]
  simp

set_option maxHeartbeats 2000000 in

theorem adms_core (Tf : FormsTied D u) (x : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (γ : GL (Fin (D.R.N 0)) D.host.E) (hγJ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hγ : x.1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * x.1 ∈
      (Tf.cls 0 (Nat.zero_le _)).lev.U) : γ = 1 := by
  let _ := D.host.cmStar
  set S := (Tf.cls 0 (Nat.zero_le _)).lev with hSdef
  choose vv hvv using fun i : Fin 2 => Formalism.L2.G.Triv.exists_place (F := D.host.F) (D.host.g i) (D.host.g_prime i)
  have hτ : ∀ τ : D.host.E →+* ℂ, τ.comp (sigD D : D.host.E →+* D.host.E) = (starRingEnd ℂ).comp τ :=
    fun τ => Formalism.L2.G.sig_conj D.sp.cm τ
  have hH : IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := by
    have h := Formalism.L2.G.gram_herm D.sp.cm (D.sp.X 0)
    unfold IsHerm cT at h ⊢
    funext p q
    have h1 := congrFun (congrFun h ((finCongr (rankN D 0 (Nat.zero_le _))).symm p))
      ((finCongr (rankN D 0 (Nat.zero_le _))).symm q)
    simpa [gramN, sigD, Matrix.reindex_apply] using h1
  have hdet : IsUnit (gramN D 0 (Nat.zero_le _)).det := by
    have h := Formalism.L2.G.gram_det_unit D.sp.cm (D.sp.X 0)
    show IsUnit ((D.sp.X 0).gram.reindex _ _).det
    rw [Matrix.det_reindex_self]; exact h
  have hdef : IsTotDef (sigD D) (gramN D 0 (Nat.zero_le _)) :=
    Formalism.L2.G.Triv.totDef_reindex _ _ _
      (Formalism.L2.G.gram_totDef D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (D.sp.X_def 0 (Nat.zero_le _)))
  exact Formalism.L2.G.Triv.gen_triv (sigD D) (gramN D 0 (Nat.zero_le _)) hτ hH hdet hdef S.Lb S.Lb_fin S.Lb_span S.U
    (fun x hx v => (S.Uloc_lev v (((S.U_eq x).1 hx).2 v)).2) D.host.g D.host.g_prime D.host.g_ne vv hvv
    (fun i => Tf.gl.phi i (vv i) (hvv i)) (fun i => (Tf.glev 0 (Nat.zero_le _)).fr i (vv i) (hvv i))
    (fun i z hz => adms_iwU S Tf.gl (Tf.glev 0 (Nat.zero_le _)) rank_zero_le_admissible_bound i (vv i) (hvv i) _ (((S.U_eq z).1 hz).2 (vv i)))
    x γ hγJ hγ

set_option maxHeartbeats 2000000 in

theorem adms_triv (Tf : FormsTied D u) (c : (D.mem u).C.cls 0)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
      (Tf.cls 0 (Nat.zero_le _)).lev.U.map (MulAut.conj ((Tf.cls 0 (Nat.zero_le _)).y c).1).toMonoidHom) :
    γ = 1 := by
  obtain ⟨κ, hκ, he⟩ := Subgroup.mem_map.1 hγ
  have hγ' : (((Tf.cls 0 (Nat.zero_le _)).y c : UPts (sigD D) (gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _)⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * ((Tf.cls 0 (Nat.zero_le _)).y c).1 ∈
        (Tf.cls 0 (Nat.zero_le _)).lev.U := by
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
    exact hκ
  exact Subtype.ext (adms_core Tf _ γ.1 γ.2 hγ')

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem upn_isTr_inv (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (s : (D.mem u).C.Y i) :
    IsTr (atInf (embT D) γ.1.1)
      ((Tf.val i hi).eY ((Tf.val i hi).eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
        ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)).inv_mem γ.2) ((Tf.val i hi).eY s))))
      ((Tf.val i hi).eY s) := by
  intro τ
  rw [Equiv.apply_symm_apply]
  show ((Tf.val i hi).eY s).1 τ = atInf (embT D) (γ.1 : Matrix _ _ D.host.E) τ *
    (atInf (embT D) ((γ.1⁻¹ : GL _ D.host.E) : Matrix _ _ D.host.E) τ * ((Tf.val i hi).eY s).1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

set_option maxHeartbeats 4000000 in

theorem upNat_of_tied (Tf : FormsTied D u) : UpNat Tf := by
  intro i hi v c z hz
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := Tf.upN i hi v c z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun h => ?_⟩
  funext s
  rw [h6 h s _ (upn_isTr_inv Tf i hi γ s), Units.val_inv_eq_inv_val]
  rfl

set_option maxHeartbeats 4000000 in

theorem dnNat_of_tied (Tf : FormsTied D u) : DnNat Tf := by
  intro i hi v c g hg0
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5⟩ := Tf.dnN i hi v c g hg0
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun h => ?_⟩
  funext s
  rw [h5 h s _ (upn_isTr_inv Tf i hi γ s), Units.val_inv_eq_inv_val]
  rfl




end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem translate_mem_span_adelic (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U) {h : Frames (gramC J emb) → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range g)) :
    (fun y => (S.chi κ : ℂ) * h (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) ∈
      Submodule.span ℂ (Set.range g) := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨z, rfl⟩ := hh
    have hb : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
      Formalism.UG.Final.RatPtsLe F E (Fin n) σ J (FiniteAdeleRing (𝓞 F) F) ⟨γ, hγ, rfl⟩
    have hk : κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := ((S.U_eq κ.1).1 κ.2).1
    let z' : UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
      ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * z.1 * κ.1, mul_mem (mul_mem hb z.2) hk⟩
    apply Submodule.subset_span
    refine ⟨z', ?_⟩
    funext y
    exact adelic_value_translate S emb hc hg γ hγ z z' κ rfl y
  | zero =>
    have e : (fun y => (S.chi κ : ℂ) * (0 : Frames (gramC J emb) → ℂ)
        (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) = 0 := by funext y; simp
    rw [e]; exact zero_mem _
  | add a b _ _ ha hb =>
    have e : (fun y => (S.chi κ : ℂ) * (a + b) (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) =
        (fun y => (S.chi κ : ℂ) * a (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) +
        (fun y => (S.chi κ : ℂ) * b (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) := by
      funext y; simp [mul_add]
    rw [e]; exact add_mem ha hb
  | smul r a _ ha =>
    have e : (fun y => (S.chi κ : ℂ) * (r • a) (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) =
        r • (fun y => (S.chi κ : ℂ) * a (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) := by
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact Submodule.smul_mem _ r ha

set_option maxHeartbeats 1000000 in

theorem adelic_function_extends_from_classes (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (lam : ι → DomWeight n)
    {C : Type} [Fintype C] (y : C → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : ∀ c, RndStabTriv S (y c))
    (hdis : ∀ (c c' : C) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 = (y c').1 * κ.1 → c = c')
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdForms S emb lam)
    (Fc : C → Frames (gramC J emb) → ℂ) (hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g)) :
    ∃ G ∈ AdForms S emb lam, ∀ c, G (y c) = Fc c := by
  classical
  have hgA := (Submodule.mem_inf.1 hg).1
  have hgV : ∀ z, g z ∈ ValC (gramC J emb) lam := fun z => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) z trivial
  have hspan : Submodule.span ℂ (Set.range g) ≤ ValC (gramC J emb) lam :=
    Submodule.span_le.2 (by rintro _ ⟨z, rfl⟩; exact hgV z)
  let G := ∑ c, rndFillG S emb hc (y c) (Fc c)
  refine ⟨G, Submodule.mem_inf.2 ⟨Submodule.sum_mem _ fun c _ => rnd_fill_mem S emb hc (y c) (hs c) (Fc c), ?_⟩, ?_⟩
  · refine Submodule.mem_pi.2 fun x _ => ?_
    show (∑ c, rndFillG S emb hc (y c) (Fc c)) x ∈ _
    rw [Finset.sum_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
        x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * (y c).1 * p.2.1
    · have e : rndFillG S emb hc (y c) (Fc c) x = fun yy => (S.chi (Classical.choose hx).2 : ℂ) *
          Fc c (frameTranslate emb hc (Classical.choose hx).1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem (Classical.choose hx).1.2) yy) := by
        funext yy; unfold rndFillG; rw [dif_pos hx]
      rw [e]
      exact hspan (translate_mem_span_adelic S emb hc hgA _ (Classical.choose hx).1.2 _ (hF c))
    · have e : rndFillG S emb hc (y c) (Fc c) x = 0 := by
        funext yy; unfold rndFillG; rw [dif_neg hx]; rfl
      rw [e]; exact zero_mem _
  · intro c
    show (∑ c', rndFillG S emb hc (y c') (Fc c')) (y c) = Fc c
    rw [Finset.sum_apply, Finset.sum_eq_single c]
    · exact rnd_fill_at S emb hc (y c) (hs c) (Fc c)
    · intro c' _ hne
      funext yy
      unfold rndFillG
      rw [dif_neg]
      · rfl
      rintro ⟨p, hp⟩
      apply hne
      refine hdis c' c p.1.1 p.1.2 p.2⁻¹ ?_
      rw [hp, InvMemClass.coe_inv]; group
    · intro h; exact absurd (Finset.mem_univ c) h

end Gen

section Tied

variable {D : D7} {u : D.what₂.Word}

theorem trivial_stabiliser_level_zero (Tf : FormsTied D u) (x0 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    RndStabTriv (Tf.cls 0 (Nat.zero_le _)).lev x0 := by
  intro δ hδ κ h
  apply adms_core Tf x0 δ hδ
  have e : x0.1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * x0.1 = κ.1 := by
    rw [mul_assoc, h]; group
  rw [e]; exact κ.2

theorem class_rep_unique_of_translate (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : (Tf.cls i hi).lev.U)
    (h : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((Tf.cls i hi).y c).1 =
      ((Tf.cls i hi).y c').1 * κ.1) : c = c' :=
  (Tf.cls i hi).y_bij.1 (rnd_cls _ γ hγ _ _ κ h)

set_option maxHeartbeats 4000000 in

theorem U_op_preserves_forms_level_zero (Tf : FormsTied D u) (v : (D.mem u).A.vT) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (hφ : φ ∈ (D.fm u).Fi 0) : Formalism.MainNotions.product_first_zeroth_parts.Uop D u 0 v φ ∈ (D.fm u).Fi 0 := by
  classical
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function Tf 0 (Nat.zero_le _) φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  have key : ∀ c (x : (D.fm u).lv 0 v c), (D.fm u).fv 0 v c x = 1 →
      ∃ p : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        (D.fm u).upT 0 v c x (φ ((D.fm u).up 0 v c x)) = fun s => g p ((Tf.val 0 (Nat.zero_le _)).eY s) := by
    intro c x hx
    obtain ⟨z, rfl⟩ := (Tf.lv 0 (Nat.zero_le _)).pr_surj v c x
    obtain ⟨γ, η, κ, -, hrel, -, -, -, htr⟩ := upNat_of_tied Tf 0 (Nat.zero_le _) v c z hx
    refine ⟨(Tf.cls 0 (Nat.zero_le _)).y c * η, ?_⟩
    rw [htr, hgφ]
    exact natTr_adFun Tf 0 (Nat.zero_le _) hgA _ _ η γ κ hrel
  choose pp hpp using key
  let Fc : (D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ := fun c =>
    ∑ x ∈ Finset.univ.filter (fun x : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c x = 1),
      if hx : (D.fm u).fv 0 v c x = 1 then g (pp c x hx) else 0
  have hU : ∀ c, Formalism.MainNotions.product_first_zeroth_parts.Uop D u 0 v φ c = fun s => Fc c ((Tf.val 0 (Nat.zero_le _)).eY s) := by
    intro c
    funext s
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Uop, Formalism.BasicNotions.LT.Uop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply, Fc]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx1 := (Finset.mem_filter.1 hx).2
    rw [dif_pos hx1]
    exact congrFun (hpp c x hx1) s
  have hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g) := by
    intro c
    refine Submodule.sum_mem _ fun x _ => ?_
    split_ifs
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact zero_mem _
  obtain ⟨G, hG, hGc⟩ := adelic_function_extends_from_classes (Tf.cls 0 (Nat.zero_le _)).lev (embT D) (fun τ x => embedding_conj_compat D τ x) (lamT u 0)
    (Tf.cls 0 (Nat.zero_le _)).y (fun c => trivial_stabiliser_level_zero Tf _) (fun c c' γ hγ κ h => class_rep_unique_of_translate Tf 0 (Nat.zero_le _) c c' γ hγ κ h)
    hg Fc hF
  refine ((Tf.val 0 (Nat.zero_le _)).Fi _).2 ⟨G, hG, ?_⟩
  funext c z
  show G ((Tf.cls 0 (Nat.zero_le _)).y c) z = _
  rw [hGc, hU]
  simp

set_option maxHeartbeats 4000000 in

theorem D_op_preserves_forms_level_zero (Tf : FormsTied D u) (v : (D.mem u).A.vT) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (hφ : φ ∈ (D.fm u).Fi 0) : Formalism.MainNotions.product_first_zeroth_parts.Dop D u 0 v φ ∈ (D.fm u).Fi 0 := by
  classical
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function Tf 0 (Nat.zero_le _) φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  have key : ∀ c (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), x ((D.fm u).te 0 v c) = 1 →
      ∃ p : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        (D.fm u).dnT 0 v c x (φ ((D.fm u).dn 0 v c x)) = fun s => g p ((Tf.val 0 (Nat.zero_le _)).eY s) := by
    intro c x hx
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, LinearMap.zero_apply] at hx; exact zero_ne_one hx
    obtain ⟨γ, η, κ, -, hrel, -, -, htr⟩ := dnNat_of_tied Tf 0 (Nat.zero_le _) v c x hx0
    refine ⟨(Tf.cls 0 (Nat.zero_le _)).y c * η, ?_⟩
    rw [htr, hgφ]
    exact natTr_adFun Tf 0 (Nat.zero_le _) hgA _ _ η γ κ hrel
  choose pp hpp using key
  let Fc : (D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ := fun c =>
    ∑ x ∈ Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ((D.fm u).te 0 v c) = 1),
      if hx : x ((D.fm u).te 0 v c) = 1 then g (pp c x hx) else 0
  have hU : ∀ c, Formalism.MainNotions.product_first_zeroth_parts.Dop D u 0 v φ c = fun s => Fc c ((Tf.val 0 (Nat.zero_le _)).eY s) := by
    intro c
    funext s
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Dop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply, Fc]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx1 := (Finset.mem_filter.1 hx).2
    rw [dif_pos hx1]
    exact congrFun (hpp c x hx1) s
  have hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g) := by
    intro c
    refine Submodule.sum_mem _ fun x _ => ?_
    split_ifs
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact zero_mem _
  obtain ⟨G, hG, hGc⟩ := adelic_function_extends_from_classes (Tf.cls 0 (Nat.zero_le _)).lev (embT D) (fun τ x => embedding_conj_compat D τ x) (lamT u 0)
    (Tf.cls 0 (Nat.zero_le _)).y (fun c => trivial_stabiliser_level_zero Tf _) (fun c c' γ hγ κ h => class_rep_unique_of_translate Tf 0 (Nat.zero_le _) c c' γ hγ κ h)
    hg Fc hF
  refine ((Tf.val 0 (Nat.zero_le _)).Fi _).2 ⟨G, hG, ?_⟩
  funext c z
  show G ((Tf.cls 0 (Nat.zero_le _)).y c) z = _
  rw [hGc, hU]
  simp

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

section UnramifiedDiagonal

variable (D : D7) (u : D.what₂.Word)

def DiamondCommutesLevelZero : Prop :=
  ∀ v v' (a : ((D.mem u).A.Fv v')ˣ), ∀ φ ∈ (D.fm u).Fi 0,
    dia D u 0 v' a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v' a φ) ∧
    dia D u 0 v' a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v' a φ)

def TraceDiamondInvariantLevelZero : Prop :=
  ∀ v (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi 0, trp D u 0 v (dia D u 0 v a φ) = trp D u 0 v φ

def DUFormulaLevelZero : Prop :=
  ∀ v, ∀ φ ∈ (D.fm u).Fi 0, Dop D u 0 v (Uop D u 0 v φ) =
    ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ - ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 2) • Nm D u 0 v φ
      + ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 2) • trp D u 0 v φ

variable {D u}

theorem norm_commutes_hecke_level_zero (hc : DiamondCommutesLevelZero D u) (v v' : (D.mem u).A.vT) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    Nm D u 0 v' (Uop D u 0 v φ) = Uop D u 0 v (Nm D u 0 v' φ) ∧
    Nm D u 0 v' (Dop D u 0 v φ) = Dop D u 0 v (Nm D u 0 v' φ) := by
  simp only [norm_eq_sum_diamond, map_sum]
  exact ⟨Finset.sum_congr rfl fun a _ => (hc v v' a φ hφ).1, Finset.sum_congr rfl fun a _ => (hc v v' a φ hφ).2⟩

theorem trace_zero_of_norm_zero_level_zero (ht : TraceDiamondInvariantLevelZero D u) (v : (D.mem u).A.vT) (φ : Fn D u 0)
    (hφ : φ ∈ (D.fm u).Fi 0) (hN : Nm D u 0 v φ = 0) : trp D u 0 v φ = 0 := by
  have h1 : ∑ a : ((D.mem u).A.Fv v)ˣ, trp D u 0 v (dia D u 0 v a φ) = trp D u 0 v (Nm D u 0 v φ) := by
    rw [norm_eq_sum_diamond, map_sum]
  rw [hN, map_zero, Finset.sum_congr rfl (fun a _ => ht v a φ hφ), Finset.sum_const,
    Finset.card_univ] at h1
  have hc : (Fintype.card ((D.mem u).A.Fv v)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left hc



end UnramifiedDiagonal

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end
