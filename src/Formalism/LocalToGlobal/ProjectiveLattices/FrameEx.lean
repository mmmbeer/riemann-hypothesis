import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

section Per

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Classical in

def bdiag (X : Data E r) (b : Frame X.Ψ r) (τ : E →+* ℂ) (i : ℕ) : ℂ :=
  if h : τ ∈ X.Ψ then (if hi : X.p0 + i < r then b ⟨τ, h⟩ ⟨X.p0 + i, hi⟩ ⟨X.p0 + i, hi⟩ else 1)
  else if h' : conjEmb τ ∈ X.Ψ then
    (if hj : X.p0 - 1 - i < r then (b ⟨conjEmb τ, h'⟩ ⟨X.p0 - 1 - i, hj⟩ ⟨X.p0 - 1 - i, hj⟩)⁻¹ else 1)
  else 1

def bdet (X : Data E r) (b : Frame X.Ψ r) : ℂ :=
  ∏ τ : X.Ψ, ∏ j : Fin r, b τ j j ^ (if X.p0 ≤ (j : ℕ) then (1 : ℤ) else -1)

end Per

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
  (M : ModelsOf F r)

abbrev PerAt : Prop :=
  ∀ k, ∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (pmOf e M k x)

def lieOf (hP : PerAt e F M) (k : Fin F.n) (x : (M.X k).dom) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left :=
  (derivAt_exists (hP k x.1 x.2) (eb e τ i)).choose

theorem lieOf_spec (hP : PerAt e F M) (k : Fin F.n) (x : (M.X k).dom) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    IsDerivAt0 (fun z => (F.ex k (pmOf e M k x.1) z).left) (eb e τ i) (lieOf e F M hP k x τ i) :=
    (derivAt_exists (hP k x.1 x.2) (eb e τ i)).choose_spec

def LieEig : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ τ (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), IsTanAt (S := CAt σ) (F.u i P) v → IsEigAt c τ v →
      ∃ a : Fin (Dw.mult τ) → ℂ, IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, a j • eb e τ j) v

def UnitGen (k : Fin F.n) (Pm : (F.Di k).La →+ (Fin g → ℂ)) (x : Frame (M.X k).Ψ r) (y : FrPt Xo c (CAt σ)) :
    Prop :=
  (∀ τ' i', ‖dmin (M.X k).Gm x τ' i'‖ = 1) →
    ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
      (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
      Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
      (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
      (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
        fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
          (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
      (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
          (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
      (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
          Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
      (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
        pt ≫ gxFst y.x = (F.ex k Pm z).left →
        pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
        ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
      MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
      (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
        (MeasureTheory.volume Fd).toReal = 1

abbrev GenSec : Type :=
  ∀ k (x : (M.X k).dom), LB.Sec (PPx (S := CAt σ) (F.u k (pmOf e M k x.1)))

abbrev IsGenSec (s : GenSec e F M) : Prop :=
  ∀ k (x : (M.X k).dom) (s' : LB.Sec (PPx (S := CAt σ) (F.u k (pmOf e M k x.1)))),
    ∃! a : CAt σ, ∀ i, s'.f i = scal (S := CAt σ) (F.u k (pmOf e M k x.1)) a i * (s k x).f i

variable {e F M} in

theorem lieOf_basis (hTE : ExpTan e F) (hEL : ExpLin e F) (hLE : LieEig e F) (hP : PerAt e F M)
    (k : Fin F.n) (x : (M.X k).dom) :
    (∀ τ i, IsTanAt (S := CAt σ) (F.u k (pmOf e M k x.1)) (lieOf e F M hP k x τ i)) ∧
    (∀ τ i, IsEigAt c τ (lieOf e F M hP k x τ i)) ∧
    ∀ τ (w : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), IsTanAt (S := CAt σ) (F.u k (pmOf e M k x.1)) w →
      IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → CAt σ,
        IsCombAt (S := CAt σ) (F.u k (pmOf e M k x.1)) (lieOf e F M hP k x τ) a w := by
  have hPx := hP k x.1 x.2
  refine ⟨fun τ i => (hTE k _ hPx _ _ (lieOf_spec e F M hP k x τ i)).1, fun τ i => ?_, fun τ w hw he => ?_⟩
  · have := (hTE k _ hPx _ _ (lieOf_spec e F M hP k x τ i)).2 (e.symm ⟨τ, i⟩) rfl
    simpa using this
  · obtain ⟨a, ha⟩ := hLE k _ hPx τ w hw he
    refine ⟨a, hEL k _ hPx _ _ _ a w (fun j => lieOf_spec e F M hP k x τ j) ha, fun a' ha' => ?_⟩
    have h2 := derivAt_of_comb hEL hPx (fun j => lieOf_spec e F M hP k x τ j) ha'
    have hs := derivAt_unique hTE hPx ha h2
    funext j
    have := congrFun hs (e.symm ⟨τ, j⟩)
    have h1 := sum_eb_apply e τ a j
    have h3 := sum_eb_apply e τ (a' : Fin (Dw.mult τ) → ℂ) j
    exact (h1.symm.trans (this.trans h3)).symm

def unOf (hTE : ExpTan e F) (hEL : ExpLin e F) (hLE : LieEig e F) (hP : PerAt e F M) (s : GenSec e F M)
    (hs : IsGenSec e F M s) : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ) :=
  fun k x =>
  { x := F.u k (pmOf e M k x.1)
    x_over := F.over_σ k _ (hP k x.1 x.2)
    u := lieOf e F M hP k x
    tan := (lieOf_basis hTE hEL hLE hP k x).1
    eig := (lieOf_basis hTE hEL hLE hP k x).2.1
    basis := (lieOf_basis hTE hEL hLE hP k x).2.2
    s := s k x
    gen := hs k x }

def GenAt (hTE : ExpTan e F) (hEL : ExpLin e F) (hLE : LieEig e F) (hP : PerAt e F M) : Prop :=
  ∃ (s : GenSec e F M) (hs : IsGenSec e F M s),
    (∀ k (x : (M.X k).dom), UnitGen e F M k (pmOf e M k x.1) x.1 (unOf e F M hTE hEL hLE hP s hs k x)) ∧
    (∀ k (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom),
      ∃ t0 : (CAt σ)ˣ, toC (t0 : CAt σ) ^ 2 = bdet (M.X k) b ∧
        SClause (t0 : CAt σ) (unOf e F M hTE hEL hLE hP s hs k x) (unOf e F M hTE hEL hLE hP s hs k ⟨_, h⟩)) ∧
    (∀ k, ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom),
      ∃ t0 : (CAt σ)ˣ, toC (t0 : CAt σ) ^ 2 = 1 ∧
        SClause (t0 : CAt σ) (unOf e F M hTE hEL hLE hP s hs k x) (unOf e F M hTE hEL hLE hP s hs k ⟨_, h⟩)) ∧
    ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k,
      DifferentiableOn ℂ (rdU (unfOf e F M (unOf e F M hTE hEL hLE hP s hs)) f k) (M.X k).dom

def PerBor : Prop :=
  ∀ k, ∀ x ∈ (M.X k).dom, ∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom →
    ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, pmOf e M k (rmul x b) a = h (pmOf e M k x a)) ∧
      ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → ℂ, cf i = bdiag (M.X k) b (relab c σ τ) i ∧
        (∀ j, i < j → cf j = 0) ∧ h.symm (eb e τ i) = ∑ j, cf j • eb e τ j

def PerGam : Prop :=
  ∀ k, ∀ γ ∈ (M.X k).Γ, ∀ x, lact γ x ∈ (M.X k).dom →
    ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La, (∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ e', gam a = a + l.M • e') ∧
      (∀ a, ∃ e', gam a = a + l.A • e') ∧ ∀ a, pmOf e M k (lact γ x) (gam a) = pmOf e M k x a

end Fam

section Red

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}
  (hTE : ExpTan e F) (hEL : ExpLin e F) (hLE : LieEig e F) (hP : PerAt e F M) (s : GenSec e F M)
  (hs : IsGenSec e F M s)

end Red

section Row

variable {D : D7}

end Row

section Gam

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ ((G.map τ) *ᵥ star w) := by
  first
    | rfl
    | (unfold hermC; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]; done)

theorem star_mulVec_fx (Γ : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    star (Γ *ᵥ w) = (Γ.map (starRingEnd ℂ)) *ᵥ star w := by
  funext i
  first
    | (simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul', Matrix.map_apply]; rfl)
    | simp [Matrix.mulVec, dotProduct, star_sum]

theorem mulVec_dot (Γ : Matrix (Fin r) (Fin r) ℂ) (u y : Fin r → ℂ) : (Γ *ᵥ u) ⬝ᵥ y = u ⬝ᵥ (Γᵀ *ᵥ y) := by
  first
    | rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    | (simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
       rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

theorem hermC_unitary (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Γ : Matrix (Fin r) (Fin r) ℂ)
    (hu : Γᵀ * G.map τ * Γ.map (starRingEnd ℂ) = G.map τ) (u w : Fin r → ℂ) :
    hermC τ G (Γ *ᵥ u) (Γ *ᵥ w) = hermC τ G u w := by
  rw [hermC_dot, hermC_dot, star_mulVec_fx, mulVec_dot, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]

theorem ustab_mapC {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} {γ : GL (Fin r) E}
    (hγ : IsUStab G Λ γ) (τ : E →+* ℂ) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ * ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) =
      G.map τ := by
  have hcc : ∀ a : E, τ (cc a) = starRingEnd ℂ (τ a) := by
    intro a
    first
      | (unfold cc; exact NumberField.IsCMField.complexEmbedding_complexConj E τ a)
      | exact NumberField.IsCMField.complexEmbedding_complexConj E τ a
      | (simp only [cc]; exact NumberField.IsCMField.complexEmbedding_complexConj E τ a)
  have h := congrArg (fun A : Matrix (Fin r) (Fin r) E => A.map τ) (ustab_mat hγ)
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h
  have hf : (⇑τ ∘ cc) = (starRingEnd ℂ) ∘ ⇑τ := funext hcc
  rw [Matrix.map_map, ← hf]
  exact h

theorem emb_mulVec (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    Data.emb τ (A *ᵥ v) = (A.map τ) *ᵥ Data.emb τ v := by
  funext i
  first
    | simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
    | (unfold Data.emb; simp [Matrix.mulVec, dotProduct]; done)

theorem det_map_ne (τ : E →+* ℂ) (γ : GL (Fin r) E) : ((γ : Matrix (Fin r) (Fin r) E).map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).2 (Matrix.isUnits_det_units γ).ne_zero

theorem perFr_lact_fx (X : Data E r) (x : Frame X.Ψ r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = perFr X x v τ i := by
  have hu : ∀ t : E →+* ℂ, IsUnit (((γ : Matrix (Fin r) (Fin r) E).map t).det) :=
    fun t => isUnit_iff_ne_zero.2 (det_map_ne t γ)
  have hinv : ∀ t : E →+* ℂ, ((γ : Matrix (Fin r) (Fin r) E).map t)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map t = 1 :=
    fun t => Matrix.nonsing_inv_mul _ (hu t)
  have hm : ∀ t : ↥X.Ψ, mat (lact γ x) t = ((γ : Matrix (Fin r) (Fin r) E).map (t : E →+* ℂ)) * mat x t :=
    fun t => rfl
  have hcol : ∀ (A B : Matrix (Fin r) (Fin r) ℂ) (j : Fin r), col (A * B) j = A *ᵥ col B j := by
    intro A B j
    funext k
    first
      | simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      | rfl
  unfold perFr
  rw [emb_mulVec, emb_mulVec]
  simp only [hm]
  split_ifs with h1 h2 h3 h4
  · simp only [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.mul_one]
  · rfl
  · rw [hcol]
    exact hermC_unitary _ _ _ (ustab_mapC hγ _) _ _
  · rfl
  · rfl

end Gam

section GamL

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}

def gamL (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) : X.Λ ≃ₗ[𝓞 E] X.Λ where
  toFun v := ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ v, (hγ.2 v).1 v.2⟩
  invFun v := ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, by
    refine (hγ.2 _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact v.2⟩
  map_add' u v := by ext1; simp [Matrix.mulVec_add]
  map_smul' a v := by
    ext1
    simp only [SetLike.val_smul, RingHom.id_apply]
    first
      | exact Matrix.mulVec_smul _ _ _
      | simp [Matrix.mulVec_smul]
  left_inv v := by
    ext1
    simp only
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    ext1
    simp only
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem gamL_coe (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) (v : X.Λ) :
    ((gamL X hγ v : X.Λ) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ v := rfl

variable (e F M) in

theorem perGam_of (hMB : ModelBase M) : PerGam e F M := by
  intro k γ hγ x _
  obtain ⟨hU, hMc, hAc⟩ := (hMB.gam k γ).1 hγ
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans ((gamL (M.X k) hU).trans (M.φ k).symm)
  have hg : ∀ a, ((M.φ k (gam a) : (M.X k).Λ) : Fin r → E) =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := fun a => by
    simp [gam, gamL_coe]
  refine ⟨gam, fun a b => ?_, fun a ha => ?_, fun a => ?_, fun a => ?_⟩
  · have e1 := hMB.ef k (gam a) (gam b)
    have e2 := hMB.ef k a b
    rw [hg, hg, hU.1] at e1
    exact_mod_cast e1.trans e2.symm
  · obtain ⟨b, hb⟩ := hMc a ha
    refine ⟨b, (M.φ k).injective (Subtype.ext ?_)⟩
    rw [hg, hb, map_add, map_nsmul]
    rfl
  · obtain ⟨b, hb⟩ := hAc a
    refine ⟨b, (M.φ k).injective (Subtype.ext ?_)⟩
    rw [hg, hb, map_add, map_nsmul]
    rfl
  · funext j
    simp only [pmOf, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [hg]
    exact perFr_lact_fx (M.X k) x hU _ _ _

end GamL

end Formalism.L2.Pj
