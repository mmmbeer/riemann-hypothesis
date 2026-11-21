import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumFibreEqSumOrbits
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormMapOfFinOrder
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

section
noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure MemOn (F : GFam K) where

  G : Type
  [grpG : Group G]

  D : Type
  [actD : MulAction G D]

  ρ : G →* Module.End K F.V

  Nab : D → Submodule (𝓞 K) F.V

  Del : D → Submodule (𝓞 K) F.V

attribute [instance] MemOn.grpG MemOn.actD

@[reducible] def MemOn.gsd {F : GFam K} (M : MemOn F) : GSD K where
  G := M.G
  D := M.D
  V := F.V
  ιV := F.ιV
  bV := F.bV
  pair := F.pair
  ρ := M.ρ
  Nab := M.Nab
  Del := M.Del

@[reducible] def MemOn.self (F : GFam K) (b : F.β) : MemOn F where
  G := F.G b
  D := F.D b
  ρ := F.ρ b
  Nab := F.Nab b
  Del := F.Del b

@[reducible] def MemOn.pairs (F : GFam K) (b : F.β) (Y : Cpl (F.mem b)) : MemOn F where
  G := F.G b
  D := Y.Pts
  actD := (cplGSD (F.mem b) Y).actD
  ρ := F.ρ b
  Nab d := F.Nab b d.1.1
  Del d := F.Del b d.1.1

example (F : GFam K) (b : F.β) : (MemOn.self F b).gsd = F.mem b := rfl

example (F : GFam K) (b : F.β) (Y : Cpl (F.mem b)) : (MemOn.pairs F b Y).gsd = cplGSD (F.mem b) Y := rfl

inductive SpIdx (β : ℕ → Type) (n m i : ℕ) : Type
  | mat (b : β i) (h : i ≤ n) : SpIdx β n m i
  | cpl (h : i = n + 1) : SpIdx β n m i
  | top (h : i = m) : SpIdx β n m i

namespace SpIdx

variable {β : ℕ → Type} {n m i : ℕ}

instance [Finite (β i)] : Finite (SpIdx β n m i) :=
  Finite.of_injective (fun b : SpIdx β n m i => match b with
    | .mat b _ => (Sum.inl b : β i ⊕ Bool)
    | .cpl _ => Sum.inr false
    | .top _ => Sum.inr true) (by
      rintro (⟨a, _⟩ | _ | _) (⟨b, _⟩ | _ | _) h <;> simp_all)

instance [Finite (β i)] : Fintype (SpIdx β n m i) := Fintype.ofFinite _

instance : DecidableEq (SpIdx β n m i) := Classical.decEq _

def lowEquiv (hm : n < m) (hi : i ≤ n) : β i ≃ SpIdx β n m i where
  toFun b := .mat b hi
  invFun b := match b with
    | .mat b _ => b
    | .cpl h => absurd h (by omega)
    | .top h => absurd h (by omega)
  left_inv _ := rfl
  right_inv b := match b with
    | .mat _ _ => rfl
    | .cpl h => absurd h (by omega)
    | .top h => absurd h (by omega)


theorem eq_top (hm : n + 1 < m) (h : i = m) (b : SpIdx β n m i) : b = .top h := by
  rcases b with ⟨_, h'⟩ | h' | _
  · omega
  · omega
  · rfl

theorem isEmpty_of_lt (hm : n + 1 < m) (h : m < i) : IsEmpty (SpIdx β n m i) :=
  ⟨fun b => by rcases b with ⟨_, h'⟩ | h' | h' <;> omega⟩

end SpIdx

section Splice

variable (F : ℕ → GFam K) (n m : ℕ) (C : MemOn (F (n + 1))) (T : MemOn (F m))

@[reducible] def spMem : ∀ (i : ℕ) (_ : SpIdx (fun j => (F j).β) n m i), MemOn (F i)
  | i, .mat b _ => MemOn.self (F i) b
  | _, .cpl rfl => C
  | _, .top rfl => T

@[reducible] def spFam (i : ℕ) : GFam K where
  β := SpIdx (fun j => (F j).β) n m i
  V := (F i).V
  ιV := (F i).ιV
  bV := (F i).bV
  pair := (F i).pair
  G b := (spMem F n m C T i b).G
  D b := (spMem F n m C T i b).D
  ρ b := (spMem F n m C T i b).ρ
  Nab b := (spMem F n m C T i b).Nab
  Del b := (spMem F n m C T i b).Del




variable {F n m C T}

theorem spFam_ok (hF : ∀ i, i ≤ n → (F i).Ok) (hC : C.gsd.Ok) (hT : T.gsd.Ok) (i : ℕ) : (spFam F n m C T i).Ok := by
  rintro (⟨b, h⟩ | rfl | rfl)
  · exact hF i h b
  · exact hC
  · exact hT

def spEntry (kk : KerFam F) (k1 : ∀ al : (F n).β, ClsKer ((F n).mem al) C.gsd) (k2 : ClsKer C.gsd T.gsd)
    (i j : ℕ) (e : j = i + 1) : ∀ (b : (spFam F n m C T i).β) (b' : (spFam F n m C T j).β),
      ClsKer ((spFam F n m C T i).mem b) ((spFam F n m C T j).mem b')
  | .mat al _, .mat be _ => (match j, e, be with | _, rfl, be => kk i al be : ClsKer ((F i).mem al) ((F j).mem be))
  | .mat al _, .cpl h' =>
    (match i, j, (Nat.succ.inj (h'.symm.trans e) : n = i), h', al with | _, _, rfl, rfl, al => k1 al :
      ClsKer ((F i).mem al) ((spFam F n m C T j).mem (.cpl h')))
  | .cpl h, .top h' =>
    (match i, j, h, h' with | _, _, rfl, rfl => k2 :
      ClsKer ((spFam F n m C T i).mem (.cpl h)) ((spFam F n m C T j).mem (.top h')))
  | .mat _ _, .top _ => zeroKer _ _
  | .cpl _, .mat _ _ => zeroKer _ _
  | .cpl _, .cpl _ => zeroKer _ _
  | .top _, _ => zeroKer _ _

variable (kk : KerFam F) (k1 : ∀ al : (F n).β, ClsKer ((F n).mem al) C.gsd) (k2 : ClsKer C.gsd T.gsd)

def spKer : KerFam (spFam F n m C T) := fun i b b' => spEntry kk k1 k2 i (i + 1) rfl b b'




variable (n m C T) in

def spIn (i : ℕ) : (F i).Forms →ₗ[K] (spFam F n m C T i).Forms :=
  LinearMap.pi fun b => match b with
    | .mat al _ => LinearMap.proj al
    | .cpl _ => 0
    | .top _ => 0


variable {hS : ∀ i, (spFam F n m C T i).Ok}




end Splice


end GlobalTheory.GO
end
end

section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Aut

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def autU (N : Submodule (𝓞 E) (Sp E n)) : Subgroup (UF E n) where
  carrier := {γ | ∀ x, γ.1 x ∈ N ↔ x ∈ N}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b.1 x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹.1 x)
    rw [show a.1 (a⁻¹.1 x) = x from LinearEquiv.apply_symm_apply a.1 x] at h
    exact h.symm

theorem mem_autU {N : Submodule (𝓞 E) (Sp E n)} {γ : UF E n} : γ ∈ autU N ↔ gmap γ.1 N = N := by
  constructor
  · intro h
    ext x
    rw [mem_gmap, ← h (γ.1.symm x), LinearEquiv.apply_symm_apply]
  · intro h x
    conv_lhs => rw [← h, mem_gmap, LinearEquiv.symm_apply_apply]

end Aut

section Stab

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem card_dvd_card_autU (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q)
    (H : Subgroup (FrmG Λ Θ)) (hH : ∀ g ∈ H, g • p = p) : Nat.card H ∣ Nat.card (autU p.deco.1.N) := by
  let f : H →* autU p.deco.1.N :=
    { toFun := fun g => ⟨g.1.1, mem_autU.2 (congrArg (fun q : DecoF X.E n ST SG Q => q.deco.1.N) (hH g.1 g.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Subgroup.card_dvd_of_injective f fun a b hab => ?_
  have h1 : a.1.1 = b.1.1 := congrArg Subtype.val hab
  have ha : FrmG.incl Λ Θ a.1 • p = p := hH a.1 a.2
  have hb : FrmG.incl Λ Θ b.1 • p = p := hH b.1 b.2
  have h2 := DecoSet.stab_fst_injective p.deco (a := ((FrmG.incl Λ Θ a.1).1, (FrmG.incl Λ Θ a.1).2.1))
    (b := ((FrmG.incl Λ Θ b.1).1, (FrmG.incl Λ Θ b.1).2.1)) (congrArg DecoF.deco ha) (congrArg DecoF.deco hb) h1
  exact Subtype.ext (FramedForms.incl_injective Λ Θ (FramedForms.stab_inj p ha hb h1 (Prod.mk.inj h2).2))

end Stab

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (Λ : LevFam X.E X.K (R.N R.m) Pr.vGs) (Θ : LevQFam X.E X.K (R.N R.m) (QE sel (mu : Chr X.F X.E X.K)))

@[reducible] def frmMem : MemOn (chF W sel mu L u R.m) where
  G := FrmG Λ Θ
  D := ChPt (R := R) sel mu u R.m
  actD := frmAct Λ Θ
  ρ := frmRho (colValF W sel mu u R.m) Λ Θ
  Nab := (colValF W sel mu u R.m).Nab
  Del := (colValF W sel mu u R.m).Del


@[reducible] def cplMem : MemOn (chF W sel mu L u (m2 + 1)) :=
  MemOn.pairs (chF W sel mu L u (m2 + 1)) b (ybCpl W sel mu cst L u m2 b hY)


@[reducible] def levFam : ℕ → GFam X.K :=
  spFam (chF W sel mu L u) m2 R.m (cplMem W sel mu cst L u m2 b hY) (frmMem W sel mu L u Λ Θ)

variable {W sel mu cst L u m2 b hY Λ Θ}

def levPt : ∀ (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β),
    (levFam W sel mu cst L u m2 b hY Λ Θ i).D β → ChPt (R := R) sel mu u i
  | _, .mat _ _ => fun p => p
  | _, .cpl rfl => fun p => p.1.1
  | _, .top rfl => fun p => p

def levG : ∀ (i : ℕ) (_ : (levFam W sel mu cst L u m2 b hY Λ Θ i).β), LevFam X.E X.K (R.N i) Pr.vGs
  | i, .mat al _ => L.levG i al
  | _, .cpl rfl => L.levG (m2 + 1) b
  | _, .top rfl => Λ

def levQ : ∀ (i : ℕ) (_ : (levFam W sel mu cst L u m2 b hY Λ Θ i).β), LevQFam X.E X.K (R.N i) (QE sel (mu : Chr X.F X.E X.K))
  | i, .mat al _ => L.levQ i al
  | _, .cpl rfl => L.levQ (m2 + 1) b
  | _, .top rfl => Θ

def levGrp : ∀ (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β),
    (levFam W sel mu cst L u m2 b hY Λ Θ i).G β ≃* FrmG (levG i β) (levQ i β)
  | _, .mat _ _ => MulEquiv.refl _
  | _, .cpl rfl => MulEquiv.refl _
  | _, .top rfl => MulEquiv.refl _

theorem levPt_smul (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (g : (levFam W sel mu cst L u m2 b hY Λ Θ i).G β)
    (d : (levFam W sel mu cst L u m2 b hY Λ Θ i).D β) : levPt i β (g • d) = levGrp i β g • levPt i β d := by
  rcases β with _ | rfl | rfl <;> rfl




theorem card_stab_dvd_autU (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (d : (levFam W sel mu cst L u m2 b hY Λ Θ i).D β) :
    Nat.card (MulAction.stabilizer ((levFam W sel mu cst L u m2 b hY Λ Θ i).G β) d) ∣ Nat.card (autU (levPt i β d).deco.1.N) := by
  have h := card_dvd_card_autU (levG i β) (levQ i β) (levPt i β d)
    ((MulAction.stabilizer ((levFam W sel mu cst L u m2 b hY Λ Θ i).G β) d).map (levGrp i β).toMonoidHom) (by
      rintro _ ⟨g, hg, rfl⟩
      exact (levPt_smul i β g d).symm.trans (congrArg (levPt i β) hg))
  rwa [Subgroup.card_map_of_injective (levGrp i β).injective] at h

theorem levFam_ok (hF : ∀ j, (chF W sel mu L u j).Ok) (hT : (frmGSD (colValF W sel mu u R.m) Λ Θ).Ok) (i : ℕ) :
    (levFam W sel mu cst L u m2 b hY Λ Θ i).Ok :=
  spFam_ok (fun j _ => hF j) (cplGSD_ok _ (hF (m2 + 1) b)) hT i

end Fam

end GlobalTheory.GO
end
end

section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.TopStep

section Aut

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem card_autU (N : Submodule (𝓞 E) (Sp E n)) : Nat.card (autU N) = Nat.card (Mem.Col2.autO N) :=
  Nat.card_congr
    { toFun := fun γ => ⟨γ.1.1, γ.1.2, mem_autLat.2 (mem_autU.1 γ.2)⟩
      invFun := fun γ => ⟨⟨γ.1, γ.2.1⟩, mem_autU.2 (mem_autLat.1 γ.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_autU_dvd_tilN (N : Submodule (𝓞 E) (Sp E n)) : Nat.card (autU N) ∣ Nat.card (autU (tilN N)) := by
  let f : autU N →* autU (tilN N) :=
    ((extUH rfl).comp (autU N).subtype).codRestrict _ fun γ => mem_autU.2 (by
      have h := tilN_gmap γ.1.1 N
      rw [mem_autU.1 γ.2] at h
      exact h.symm)
  refine Subgroup.card_dvd_of_injective f fun a b hab => Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
  have h : extE a.1.1 = extE b.1.1 := congrArg (fun z : autU (tilN N) => z.1.1) hab
  have h1 := initL_extE a.1.1 (incl E n x)
  rw [h, initL_extE] at h1
  have h2 : initL E n (incl E n x) = x := by
    funext i
    simp [initL, incl, LinearMap.funLeft_apply]
  rw [h2] at h1
  exact h1.symm

theorem exists_card_autU_dvd {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (k : ℕ) :
    ∃ N' : Submodule (𝓞 E) (Sp E (n + k)), IsSdLat N' ∧ Nat.card (autU N) ∣ Nat.card (autU N') := by
  induction k with
  | zero => exact ⟨N, hN, dvd_rfl⟩
  | succ k ih =>
    obtain ⟨N', h1, h2⟩ := ih
    exact ⟨tilN N', ⟨tilN_lattice h1.1, tilN_unimodular h1.2⟩, h2.trans (card_autU_dvd_tilN N')⟩

theorem card_autU_dvd_DGam (hE : PosStar E) (R : Ranks) (hm : 1 ≤ R.m) {i : ℕ} (hi : i ≤ R.m) {N : Submodule (𝓞 E) (Sp E (R.N i))}
    (hN : IsSdLat N) : Nat.card (autU N) ∣ Mem.Col2.DGam E R := by
  have hle : R.N i ≤ R.N R.m := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨N', h1, h2⟩ := exists_card_autU_dvd hN k
  refine h2.trans ?_
  rw [card_autU]
  exact Mem.Col2.dvd_DGam hE R (hk ▸ Mem.Col2.N_mem_gamRanks R hm le_rfl) h1.1 h1.2

end Aut

section Rho

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ : X.K →+* ℂ)
  (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ)

def muInvPt (i : ℕ) {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) : X.K :=
  muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) p.deco.1.N (frsF sel mu p)

def rhoPt (i : ℕ) {u : Pr.Word} (p : ChPt (R := R) sel mu u i) : ℂ :=
  σ (muInvPt Ch sel mu cst i p) * chi (R.N i) p.deco.1.N ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ))

def rhoPt' (i : ℕ) {u : Pr.Word} (p : ChPt (R := R) sel mu u (i + 1)) : ℂ :=
  (σ (muInvPt Ch sel mu cst i p))⁻¹ * chi (R.N (i + 1)) p.deco.1.N ^ (((R.N i / 2 : ℕ) : ℤ))

def RhoUnit : Prop :=
  (∀ i, i < R.m → ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
    ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) N fr)‖ = 1) ∧
  ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → ‖chi n N‖ = 1

def ChiSplit (A : Amb X) : Prop :=
  ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    A.chiF a b N N' = chi a N ^ (((b / 2 : ℕ) : ℤ)) * chi b N' ^ (-((a / 2 : ℕ) : ℤ))

variable {Ch sel mu cst σ chi}

theorem RhoUnit.norm_rhoPt (h : RhoUnit Ch sel mu cst σ chi) {i : ℕ} (hi : i < R.m) {u : Pr.Word} (p : ChPt (R := R) sel mu u i) :
    ‖rhoPt Ch sel mu cst σ chi i p‖ = 1 := by
  rw [rhoPt, norm_mul, norm_zpow, muInvPt, h.1 i hi, h.2 _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩, one_zpow, one_mul]

theorem RhoUnit.norm_rhoPt' (h : RhoUnit Ch sel mu cst σ chi) {i : ℕ} (hi : i < R.m) {u : Pr.Word} (p : ChPt (R := R) sel mu u (i + 1)) :
    ‖rhoPt' Ch sel mu cst σ chi i p‖ = 1 := by
  rw [rhoPt', norm_mul, norm_inv, norm_zpow, muInvPt, h.1 i hi, h.2 _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩, one_zpow, inv_one, one_mul]

theorem rhoUnit_of {D : D7} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    (ht : Ch.Tied s.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) (hG : G.σ₀ = s.σ₀) (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) :
    RhoUnit Ch sel mu cst s.σ₀ (chiLat s χ) :=
  ⟨fun _ hi _ N fr => hG ▸ norm_muInvDet hX hPr hsel hS (hG ▸ ht) hL hi N fr, fun _ _ hN => norm_chiLat hX hs hχ hN⟩

end Rho

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (P : LevFam X.E X.K R.r Pr.vGs) (c : TopDepth R cst.M)

@[reducible] def twFam : ℕ → GFam X.K := levFam W sel mu cst L u m2 b hY (topLevG Ch P) (topLevQ R sel mu c.pos)

def TwEquiv : Prop :=
  MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) ∧ Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY ∧
    TopEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P c

variable {W Ch sel mu cst L A u m2 b hY P c}

theorem TwEquiv.kerEquivC (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hX : X.Ok) (hPr : Pr.Ok) (hm : R.m = m2 + 2) (hc : cst.Ok)
    (H : TilOk Pr sel mu u) : KerEquivC W Ch sel mu cst L A u m2 b hY P :=
  ⟨h.1, h.2.1, h.2.2.cp2Equiv hX hPr hm hc H (tameFr_chTh W Ch sel mu cst A u m2)⟩

def twistedKernelPointCoset (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (al : L.β m2) :
    ClsKer ((chF W sel mu L u m2).mem al) (cplMem W sel mu cst L u m2 b hY).gsd :=
  cplKer1 (topCpl h.2.1 h.2.2 al)

def twistedKernelCosetPoint (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) :
    ClsKer (cplMem W sel mu cst L u m2 b hY).gsd (frmMem W sel mu L u (topLevG Ch P) (topLevQ R sel mu c.pos)).gsd where
  k d p' := topDegreeKTwo W Ch sel mu cst (chTh W Ch sel mu cst A u m2) d.1.1 d.1.2 p'
  equiv g g₁ d p' := h.2.2 g g₁ d.1.1 d.1.2 p'

def twKer (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) : KerFam (twFam W Ch sel mu cst L u m2 b hY P c) :=
  spKer (matFam h.1) (twistedKernelPointCoset h) (twistedKernelCosetPoint h)

def twXi (i j : ℕ) (e : j = i + 1) : ∀ (β : (twFam W Ch sel mu cst L u m2 b hY P c i).β) (β' : (twFam W Ch sel mu cst L u m2 b hY P c j).β),
    (twFam W Ch sel mu cst L u m2 b hY P c i).D β → (twFam W Ch sel mu cst L u m2 b hY P c j).D β' → HomE X.E (R.N i) (R.N j) → X.K
  | .mat al _, .mat be _ =>
    (match j, e, be with | _, rfl, be => XiEntry Ch sel mu cst L i al be :
      ChPt (R := R) sel mu u i → ChPt (R := R) sel mu u j → HomE X.E (R.N i) (R.N j) → X.K)
  | .mat al _, .cpl h' =>
    (match i, j, (Nat.succ.inj (h'.symm.trans e) : m2 = i), h', al with
      | _, _, rfl, rfl, al => fun p₀ d => XiCpl1 Ch sel mu cst L m2 al p₀ d.1.1 d.1.2 :
      ChPt (R := R) sel mu u i → (twFam W Ch sel mu cst L u m2 b hY P c j).D (.cpl h') → HomE X.E (R.N i) (R.N j) → X.K)
  | .cpl h, .top h' =>
    (match i, j, h, h' with | _, _, rfl, rfl => fun d p' => XiTop Ch sel mu cst m2 d.1.1 d.1.2 p' :
      (twFam W Ch sel mu cst L u m2 b hY P c i).D (.cpl h) → (twFam W Ch sel mu cst L u m2 b hY P c j).D (.top h') →
        HomE X.E (R.N i) (R.N j) → X.K)
  | .mat _ _, .top _ => fun _ _ _ => 0
  | .cpl _, .mat _ _ => fun _ _ _ => 0
  | .cpl _, .cpl _ => fun _ _ _ => 0
  | .top _, _ => fun _ _ _ => 0

def twRep (i : ℕ) (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) : ChPt (R := R) sel mu u i :=
  levPt i x.1 (((twFam W Ch sel mu cst L u m2 b hY P c i).mem x.1).outSec.rep x.2)

def twSrc (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ) (hX : X.Ok) (hm : R.m = m2 + 2) (hF : ∀ j, (chF W sel mu L u j).Ok)
    (hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hρ : RhoUnit Ch sel mu cst A.σ₀ chi) : ChSrc X R where
  F := twFam W Ch sel mu cst L u m2 b hY P c
  ok := levFam_ok hF (topGSD_ok W Ch sel mu hX P u c)
  lam := W.lamTrue u
  eV _ := LinearEquiv.refl _ _
  kk := twKer hK
  rho i x := rhoPt Ch sel mu cst A.σ₀ chi i (twRep i x)
  rho' i x := rhoPt' Ch sel mu cst A.σ₀ chi i (twRep (i + 1) x)
  rho_norm _ hi _ := hρ.norm_rhoPt hi _
  rho'_norm _ hi _ := hρ.norm_rhoPt' hi _
  DG := Mem.Col2.DGam X.E R
  DG_pos := Mem.Col2.DGam_pos (posStar_of_ok hX) R
  dvd i hi x := (card_stab_dvd_autU i x.1 _).trans
    (card_autU_dvd_DGam (posStar_of_ok hX) R (by omega) hi ⟨(twRep i x).deco.2.lat, (twRep i x).deco.2.uni⟩)

section Laws

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi}

end Laws

variable (b hY P c) in

def twStart {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) :
    MfV W Ch u →ₗ[X.K] (twFam W Ch sel mu cst L u m2 b hY P c 0).Forms :=
  spIn m2 R.m _ _ 0 ∘ₗ startC hL u

section Col

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi} {G : ChGlob X R.m}

end Col

example : Nonempty (twFam W Ch sel mu cst L u m2 b hY P c R.m).Cl :=
  (inferInstance : Nonempty (TopPt R sel mu u)).elim fun p => ⟨⟨.top rfl, Quotient.mk _ p⟩⟩

example : Nonempty (twFam W Ch sel mu cst L u m2 b hY P c (m2 + 1)).Cl :=
  haveI : NeZero (R.N (m2 + 1)) := ⟨(R.N_pos _).ne'⟩
  open Classical in ⟨⟨.cpl rfl, Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG Pr sel mu) (stdLat X.E (R.N (m2 + 1)))
    fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)}), 0, zero_mem _, rfl⟩⟩⟩

example (hm : R.m = m2 + 2) (i : ℕ) (hi : R.m < i) : IsEmpty (twFam W Ch sel mu cst L u m2 b hY P c i).Cl :=
  ⟨fun x => (SpIdx.isEmpty_of_lt (by omega) hi).false x.1⟩

example (σ : X.K →+* ℂ) (z : ℂ) (i : ℕ) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (h : muInvPt Ch sel mu cst i p = 1) (h' : muInvPt Ch sel mu cst i p' = 1) :
    rhoPt Ch sel mu cst σ (fun _ _ => z) i p = (z ^ (R.N (i + 1) / 2))⁻¹ ∧ rhoPt' Ch sel mu cst σ (fun _ _ => z) i p' = z ^ (R.N i / 2) := by
  simp only [rhoPt, rhoPt', h, h', map_one, one_mul, inv_one, zpow_neg, zpow_natCast, and_self]

end Chain

end GlobalTheory.GO
end
end
