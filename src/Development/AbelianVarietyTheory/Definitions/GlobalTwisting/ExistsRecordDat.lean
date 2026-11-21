import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulMemSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes

section
noncomputable section

namespace GlobalTheory.LvT.Built.Model

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

section Split

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def offY (y : Ys X n) : Setoid (PtY ST SG Q y) where
  r p q := SameOff ST p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2
  iseqv := ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
    fun h => ⟨fun w hw => (h.1 w hw).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩,
    fun h h' => ⟨fun w hw => (h.1 w hw).trans (h'.1 w hw), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩⟩

theorem off_mv (y : Ys X n) (p : PtY ST SG Q y) (d : DecoSet X.E n ST SG) (h1 : SameOff ST p.1.1.deco.1.N d.1.N)
    (h2 : p.1.1.deco.1.be = d.1.be) : (offY y).r p (p.mv d) := by
  classical
  by_cases h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  · rw [show p.mv d = ⟨(⟨(d, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ from dif_pos h]
    exact ⟨h1, h2, rfl, rfl⟩
  · rw [show p.mv d = p from dif_neg h]

theorem ok_repl {d : Deco X.E n ST SG} (hd : d.Ok) {e : Deco X.E n ST ∅} (he : e.Ok)
    (hG : ∀ w : SG, localization₂ w.1.asIdeal d.N = localization₂ w.1.asIdeal e.N) : Deco.Ok (⟨e.N, e.f, d.be⟩ : Deco X.E n ST SG) := by
  let d0 : Deco X.E n ∅ SG := ⟨d.N, fun P => absurd P.2 (Finset.notMem_empty _), d.be⟩
  have h0 : d0.Ok := ⟨hd.lat, hd.uni, fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _),
    fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _), hd.be_add, hd.be_smul, hd.be_off,
    hd.be_surj, hd.be_ker⟩
  have h1 := GlobalTheory.GO.decoration_admissible_of_localization_eq h0 he.lat he.uni (fun P => absurd P.2 (Finset.notMem_empty _)) hG
  exact ⟨he.lat, he.uni, he.f_add, he.f_smul, he.f_off, he.f_ne, h1.be_add, h1.be_smul, h1.be_off, h1.be_surj, h1.be_ker⟩

theorem exists_uf (γ : GL (Fin n) X.E) (h : (γ : Matrix (Fin n) (Fin n) X.E)ᴴ * (γ : Matrix (Fin n) (Fin n) X.E) = 1) :
    ∃ g : UF X.E n, ufGL X.E n g = γ := by
  refine ⟨⟨(Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv, fun x y => ?_⟩, ?_⟩
  · show hStd X.E n (γ.1 *ᵥ x) (γ.1 *ᵥ y) = hStd X.E n x y
    have e : ∀ a b : Fin n → X.E, hStd X.E n a b = star a ⬝ᵥ b := fun _ _ => rfl
    rw [e, e, star_mulVec, dotProduct_mulVec, vecMul_vecMul, h, vecMul_one]
  · apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, LevLaws.ufGL_mulVec]
    rfl

def splitY (T : ℕ) (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG)
    (Θ : β → LevQFam X.E X.K n Q) (pref : DecoF X.E n ST SG Q → Prop) (hP : ∀ P : ST, MoveHyp ST SG P)
    (hQ : ∀ (P : ST) (w : Q), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1)
    (hy : ∀ N N', SameOff ST N N' → y.ys N = y.ys N')
    (h1 : ∀ P ∈ ST, (T : 𝓞 X.E) ∈ P.asIdeal) (h2 : ∀ P ∈ ST, (T : 𝓞 X.E) ∉ P.asIdeal ^ 2) :
    Split (tdatY ST T y β Λ Θ pref) T where
  off _ := offY y
  off_act b g d d' h := by
    refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
    · ext x
      change x ∈ localization₂ w.asIdeal (gmap g.1.1 d.1.1.deco.1.N) ↔ x ∈ localization₂ w.asIdeal (gmap g.1.1 d'.1.1.deco.1.N)
      rw [mem_localization_gmap, mem_localization_gmap, h.1 w hw]
    · change (d.1.1.deco.1.act g.1.1 g.2.1.1).be = (d'.1.1.deco.1.act g.1.1 g.2.1.1).be
      simp only [Deco.act, h.2.1]
    · funext P
      change g.1.1 * d.1.1.fr P * _ = g.1.1 * d'.1.1.fr P * _
      rw [h.2.2.1]
    · change (fun v => g.1.1 v) '' d.1.2 = (fun v => g.1.1 v) '' d'.1.2
      rw [h.2.2.2]
  off_lat _ _ _ h := h.1
  ext b d d' h e := by
    have eN : d.1.1.deco.1.N = d'.1.1.deco.1.N := (congrArg Deco.N e :)
    have ef : d.1.1.deco.1.f = d'.1.1.deco.1.f := (congrArg Deco.f e :)
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (Subtype.ext (Deco.ext eN ef h.2.1)) h.2.2.1)) h.2.2.2)
  surj b d e he hs := by
    refine ⟨⟨(⟨(⟨_, ok_repl d.1.1.deco.2 he fun w => hs _ fun P hP' => (hP ⟨P, hP'⟩).sg w⟩, d.1.1.fr), fun P x => ?_⟩, d.1.2), ?_⟩,
      ⟨hs, rfl, rfl, rfl⟩, Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))⟩
    · have := hs P.1 fun P' hP' => hQ ⟨P', hP'⟩ P
      change _ ∈ localization₂ P.1.asIdeal e.N ↔ _
      rw [← this]
      exact d.1.1.2 P x
    · change d.1.2 ∈ y.ys e.N
      rw [← hy _ _ hs]
      exact d.2
  off_up b d P x hx hf := by
    have e := DecoSet.up_val d.1.1.deco P (hP P) (h1 _ P.2) (h2 _ P.2) hx hf
    refine off_mv y d _ (fun w hw => ?_) (by rw [e]; rfl)
    rw [e]
    exact ((upN_spec d.1.1.deco.2.lat d.1.1.deco.2.uni P.1 (hP P).ne hx).2.2.1 w (hw _ P.2).1 (hw _ P.2).2).localization_eq.symm
  off_dn b d P g _ := by
    show (offY y).r d (d.mv (d.1.1.deco.dn P g))
    unfold DecoSet.dn
    split_ifs with h
    · exact off_mv y d _ (fun w hw =>
        ((d.1.1.deco.2.dnN_spec P (hP P).ne).2.2.1 w (hw _ P.2).1 (hw _ P.2).2).localization_eq.symm) rfl
    · exact off_mv y d _ (fun _ _ => rfl) rfl
  off_dia b d P a := off_mv y d _ (fun _ _ => rfl) rfl
  dia_deco b d P P' a h := by
    classical
    show (d.mv (DecoSet.dia1 P a d.1.1.deco)).1.1.deco.1.f P' = d.1.1.deco.1.f P'
    unfold DecoSet.dia1
    rw [LevLaws.mv_dia]
    funext x
    show ((Pi.mulSingle P a : DiaG X.E ST) P').1 * _ = _
    rw [Pi.mulSingle_eq_of_ne h, Units.val_one, one_mul]
  gam_surj b γ h := by
    obtain ⟨g, hg⟩ := exists_uf γ h
    exact ⟨(g, 1), hg⟩
  T_mem := h1
  T_nsq := h2
  nonconj P hP' Q' hQ' := (hP ⟨P, hP'⟩).st ⟨Q', hQ'⟩

end Split

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem localization_eq_of_sameOff (hPr : Pr.Ok) (u : Pr.Word) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) {n : ℕ}
    {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : SameOff (Pr.vT u) N N') (w : rowSG Pr sel mu) :
    localization₂ w.1.asIdeal N = localization₂ w.1.asIdeal N' := by
  classical
  have h2 : (Pr.T u : 𝓞 X.E) ∉ w.1.asIdeal := (Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)
  exact h w.1 fun P hP => ne_of_T_notMem hPr u ⟨P, hP⟩ h2

def splitAt (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)
    (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (j : ℕ) :
    Split (tdatAt sel mu cst L Tp u j) (Pr.T u) :=
  splitY _ _ _ _ _ _ (moveHyp_of_ok hPr u) (fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2))
    (fun N N' h => by
      have h1 := localization_eq_of_sameOff sel mu hPr u hQ h
      unfold ysAt
      split_ifs
      · show ybSet sel mu cst N = ybSet sel mu cst N'
        simp only [ybSet, locLat, h1]
      · rfl)
    (fun P hP => (T_unif hX hPr u ⟨P, hP⟩).1) (fun P hP => (T_unif hX hPr u ⟨P, hP⟩).2)


end Chain

section Side

variable {D : D7} {u : D.what₂.Word} {B : Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}



end Side

namespace KerInh


section K
variable {D : D7} {u : D.what₂.Word} (B : Dat D u)

def id1 {ι R : Type} [CommRing R] {n : ℕ} : ι × Fin n × Fin n → R := fun x => (1 : Matrix (Fin n) (Fin n) R) x.2.1 x.2.2

def I' : ChainIn B.E D.what₂.LL D.what₂.Tau D.R :=
  { B.I with
    rho := fun _ _ => 1
    rho' := fun _ _ => 1
    jet := fun i _ _ => LinearMap.smulRight (MvPolynomial.aeval (R := ℂ) (id1 (R := ℂ))).toLinearMap
      (MvPolynomial.map D.what₂.embLL (extV D.what₂.LL (B.lam (i+1))).1) }

def B' : Dat D u where
  E := B.E
  emb := B.emb
  fok := B.fok
  I := I' B
  J := ⟨B.J.T, B.J.ST, B.J.A, B.J.psi, B.J.duStar, B.J.Dstar, B.J.GamP⟩
  Q := ⟨B.Q.S', B.Q.b0, B.Q.til, B.Q.ext, B.Q.sg, B.Q.tz, B.Q.H⟩
  Z := ⟨B.Z.1, B.Z.2, B.Z.3, B.Z.4, B.Z.5, B.Z.6⟩
  hI := ⟨B.hI.1, fun _ _ _ => norm_one, fun _ _ _ => norm_one, B.hI.4, B.hI.5⟩
  hJ := ⟨B.hJ.1, B.hJ.2, B.hJ.3, B.hJ.4, B.hJ.5, B.hJ.6, B.hJ.7, B.hJ.8, B.hJ.9, B.hJ.10⟩
  hQ := ⟨B.hQ.1, B.hQ.2, B.hQ.3, B.hQ.4, B.hQ.5, B.hQ.6, B.hQ.7, B.hQ.8, B.hQ.9, B.hQ.10, B.hQ.11⟩
  l := ⟨B.l.1, B.l.2, B.l.3, B.l.4⟩
  lf := ⟨B.lf.1, B.lf.2, B.lf.3, B.lf.4, B.lf.5, B.lf.6, B.lf.7, B.lf.8, B.lf.9, B.lf.10, B.lf.11⟩
  hT := ⟨B.hT.1, B.hT.2, B.hT.3⟩

def k0 (i : ℕ) : B.V i →ₗ[D.what₂.LL] B.V (i+1) :=
  LinearMap.smulRight ((MvPolynomial.aeval (R := D.what₂.LL) (id1 (R := D.what₂.LL))).toLinearMap ∘ₗ (Formalism.L2.DIV.VV _ _).subtype) (extV _ _)

def kk (i : ℕ) : B.Ker i := fun b b' d d' =>
  (B.I.S (i+1)).rho B.emb (B.lam (i+1)) b' ((B.I.S (i+1)).mv b' d') ∘ₗ k0 B i ∘ₗ (B.I.S i).rho B.emb (B.lam i) b ((B.I.S i).mv b d)⁻¹

theorem gen {G G' K V V' : Type} [Group G] [Group G'] [Field K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']
    (ρ : G →* Module.End K V) (ρ' : G' →* Module.End K V') (k : V →ₗ[K] V') (g a : G) (g' a' : G') :
    ρ' (g' * a') ∘ₗ k ∘ₗ ρ (g * a)⁻¹ = ρ' g' ∘ₗ (ρ' a' ∘ₗ k ∘ₗ ρ a⁻¹) ∘ₗ ρ g⁻¹ := by
  rw [_root_.mul_inv_rev, map_mul, map_mul]
  rfl

theorem eval_extremal {R : Type} [CommRing R] {n : ℕ} (lam : DomWeight n) :
    MvPolynomial.eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0) (extremal R n lam) = 1 := by
  unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  have h : ∀ (k : ℕ) (h1 h2 : k ≤ n),
      (MvPolynomial.eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0)).mapMatrix
        (Matrix.of fun p q : Fin k => (MvPolynomial.X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [Matrix.one_apply, Fin.ext_iff]
  rw [h, Matrix.det_one, one_pow]

theorem ext_one (i : ℕ) : MvPolynomial.aeval (id1 (R := D.what₂.LL)) (extV D.what₂.LL (B.lam i)).1 = 1 := by
  rw [MvPolynomial.aeval_eq_eval]
  show MvPolynomial.eval _ (∏ τ, _) = 1
  rw [map_prod]
  refine Finset.prod_eq_one fun t _ => ?_
  unfold Formalism.GradedWeylDivisibility.blockEmb
  rw [MvPolynomial.eval_rename]
  exact eval_extremal (B.lam i t)

end K

end KerInh

end GlobalTheory.LvT.Built.Model
end
end

section
noncomputable section

namespace GlobalTheory.LvT.Built.Inh

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2
open Formalism.MainNotions.product_first_zeroth_parts (Ow)

theorem val_tauAt {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) (hX : X.AbelianUnramifiedExtensionConditions) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (P : Pr.vT u) (s : Bool) (hs : s = true ↔ seenC Pr u w) (x : X.E) :
    X.emb (tauAt hPr u w P) (if s then x else star x) ∈ GlobalTheory.LvT.Inh.valO w ↔ P.1.valuation X.E x ≤ 1 := by
  rw [GlobalTheory.LvT.Inh.mem_valO_of_below (X.emb (tauAt hPr u w P)) w (pullW (tauAt hPr u w P) w) (fun _ => Iff.rfl), GlobalTheory.LvT.Inh.mem_valO]
  by_cases h : s = true
  · rw [if_pos h, show pullW _ w = P.1 from seesP_tauAt hPr u hX (hs.1 h) P]
  · rw [if_neg h, show pullW _ w = conjPrime₂ P.1 from seesPbar_tauAt hPr u hX hw (mt hs.2 h) P,
      GlobalTheory.CharVal.valuation_conjP, star_star]

structure NonDeg {D : D7} {u : D.what₂.Word} (A : Dat D u) : Prop where
  sees : A.Sees
  T_eq : A.J.T = (D.mem u).A.T
  cl : ∀ i, Nonempty (A.I.S i).Cl
  split : ∀ i, Nonempty (Split (A.J.A i) A.J.T)
  forms : A.ch.fm.Fi 0 ≠ ⊥

local instance starHost (B : Base) : StarRing B.host.E := B.fields.starE

variable (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W) (G : GJStage B C)
  (u : B.Word)

def ofOk (I : ChainIn B.fields.E B.fields.K B.fields.Tau B.R) (J : AtIn I) (Q : PerIn I)
    (Z : FmIn J (assemble B C W V S N G).what₂.places) (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (hT : Q.Over J) :
    Dat (assemble B C W V S N G) u where
  E := B.fields.E
  sE := B.fields.starE
  emb := B.fields.emb
  fok := base_fOk B
  I := I
  J := J
  Q := Q
  Z := Z
  hI := hI
  hJ := hJ
  hQ := hQ
  l := (laws_all I J _ _ _ (base_fOk B) hI hJ Q hQ (assemble B C W V S N G).what₂.places).1
  lf := (laws_all I J _ _ _ (base_fOk B) hI hJ Q hQ (assemble B C W V S N G).what₂.places).2
  hT := hT

theorem sees_ofOk (X : PreX B.toPre) (I : ChainIn B.fields.E B.fields.K B.fields.Tau B.R) (J : AtIn I) (Q : PerIn I)
    (Z : FmIn J (assemble B C W V S N G).what₂.places) (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (hT : Q.Over J)
    (eT : J.T = B.T u) (eS : ∀ P ∈ J.ST, P ∈ (B.primes X).vT u)
    (eZ : ∀ w (P : J.ST), Z.tauOf w P = tauAt (GlobalTheory.BasePrimes.primes_ok B X).1 u w ⟨P.1, eS P.1 P.2⟩)
    (eF : ∀ w, Z.seenP w = true ↔ seenC (B.primes X) u w) :
    (ofOk B C W V S N G u I J Q Z hI hJ hQ hT).Sees := by
  intro w hw P x
  have h1 := GlobalTheory.LvT.Inh.resChar_mem_plEq (assemble B C W V S N G) w
  rw [show (assemble B C W V S N G).what₂.places.resChar w = B.T u from hw.trans eT] at h1
  refine (GlobalTheory.LvT.Inh.mem_Ow_iff_valO (assemble B C W V S N G) w _).trans ?_
  have h2 := val_tauAt (GlobalTheory.BasePrimes.primes_ok B X).1 u (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 h1 ⟨P.1, eS P.1 P.2⟩ _ (eF w) x
  exact (iff_of_eq (congrArg (fun τ => B.fields.emb τ (if Z.seenP w then x else star x) ∈ GlobalTheory.LvT.Inh.valO w) (eZ w P))).trans h2

end GlobalTheory.LvT.Built.Inh
end
end
