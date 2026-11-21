import Formalism.LocalToGlobal.HermitianForms.PrkSmul
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas

section
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

def sgHC (R : Ranks) (h : HCParam R) (i : ℕ) : ℚ :=
  ((R.m : ℚ) * ((R.t : ℚ) + 1)) / 2 +
  if h1 : i < R.k - 1 then h.v ⟨i, h1⟩
  else if h2 : (i - (R.k - 1)) / (R.t + 1) < R.m then
    (if (i - (R.k - 1)) % (R.t + 1) = 0 then -h.b ⟨_, h2⟩
     else -h.e ⟨_, h2⟩ + ((R.t : ℚ) - 1) / 2 - ((((i - (R.k - 1)) % (R.t + 1) : ℕ) : ℚ) - 1))
  else 0

variable (D : D7)

theorem rankP : letI := D.host.cmStar; D.sp.X'.rank = D.R.N D.R.m - 1 := by
  letI := D.host.cmStar
  have h := D.sp.X'_rank
  have h2 := D.R.m_add_three_le_k
  rw [h]; unfold Ranks.rankX' Ranks.r Ranks.N; rw [Nat.mul_add, Nat.mul_one]; omega

def gramP : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E :=
  letI := D.host.cmStar
  D.sp.X'.gram.reindex (finCongr (rankP D)) (finCongr (rankP D))

def iXc : (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E) :=
  letI := D.host.cmStar
  ((((D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm) :
      (D.sp.X D.R.m).V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E)) :
      (D.sp.X D.R.m).V →ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E)).comp D.sp.iX').comp
    ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm :
      (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] D.sp.X'.V)

def zc : Fin (D.R.N D.R.m) → D.host.E :=
  letI := D.host.cmStar
  ((D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm)) D.sp.z

def iXm : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) D.host.E := LinearMap.toMatrix' (iXc D)

def IsExt (z0 : Fin (D.R.N D.R.m) → D.host.E) {R : Type} [CommRing R] (φ : D.host.E →+* R)
    (g' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R)
    (g : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R) : Prop :=
  g * (iXm D).map φ = (iXm D).map φ * g' ∧ g *ᵥ (fun a => φ (z0 a)) = fun a => φ (z0 a)

abbrev FrP : Type := Frames (gramC (gramP D) (embT D))

variable {D}

set_option maxHeartbeats 1000000 in

structure ClsPTied (u : D.what₂.Word) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f (badG D)
  y : (D.fm u).clsP → UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  lat : (D.fm u).clsP → Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)
  y_lat : ∀ c (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb
  lat_fin : ∀ c, Module.Finite (𝓞 D.host.E) (lat c)
  stabI : ∀ c, (D.fm u).stabilizer₂ c →* UJ (sigD D : D.host.E →+* D.host.E) (gramP D)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

def sgT (u : D.what₂.Word) : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => shW ((D.fm u).sg τ) ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)

set_option maxHeartbeats 1000000 in

structure ValPTied (u : D.what₂.Word) (K : ClsPTied u) where

  sg : ∀ τ (i : Fin (D.R.N D.R.m - 1)),
    (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i

  eW : (D.mem u).P.Wrow ≃ₗ[ℂ] ((D.fm u).clsP → FrP D → ℂ)
  ptC : ∀ z, z ∈ (D.fm u).ptC ↔ eW z ∈ FiC K.lev (embT D) (sgT u) K.y

  ipP : ∀ (o : FrP D), o.IsON → ∀ (z z' : (D.mem u).P.Wrow)
    (P Q : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
    (∀ c, P c ∈ CSpan (D.fm u).sg) → (∀ c, Q c ∈ CSpan (D.fm u).sg) →
    (∀ c, eW z c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) (P c)) →
    (∀ c, eW z' c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) (Q c)) →
    (D.fm u).ipP z z' = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll (D.fm u).sg (Q c) (P c)
  rat : ∀ z, (∃ x, (D.fm u).ptEmb x = z) ↔
    z ∈ (D.fm u).ptC ∧ ∀ c, ∃ P ∈ RatSpan D (D.fm u).sg, eW z c = fnOf _ (shiftOf (sgT u)) 1 P

  lat : ∀ x : (D.fm u).ptLat.V, x ∈ (D.fm u).ptLat.L ↔
    ∀ (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (K.lat c : Set _) B →
      ∃ P ∈ IntSpan D w (D.fm u).sg, eW ((D.fm u).ptEmb x) c =
        fnOf _ (shiftOf (sgT u)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N D.R.m - 1)) D.host.E).1) P

set_option maxHeartbeats 1000000 in

structure TilTied (u : D.what₂.Word) (A : AtTTied u) (K : ClsPTied u) (P : LvTied u A D.R.m le_rfl) where
  z0 : Fin (D.R.N D.R.m) → D.host.E
  lastCoordinateUniformizerVector_spans_orthogonal_line : ∃ a : D.host.E, z0 = a • zc D
  hermitianForm_lastCoordinateUniformizerVector_self : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)
  ga : (D.fm u).clsP → UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
  til_lat : ∀ c, mulLat (ga c).1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) =
    (K.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}
  til_fv : ∀ v c (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c))) (r : 𝓞 D.host.E),
    (r : D.host.E) = hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 ((ga c).1.1 *ᵥ x.1) →
    (D.fm u).fv D.R.m v ((D.fm u).til c) (P.pr v _ x) = A.res v r

set_option maxHeartbeats 4000000 in

def TilBaseLat {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    (Tl : TilTied u A K P) (Km : ClsTied u D.R.m le_rfl) : Prop :=
  Km.lev.Lb = K.lev.Lb.map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {Tl.z0}

set_option maxHeartbeats 4000000 in

def TilBaseFv {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    (Tl : TilTied u A K P) (Km : ClsTied u D.R.m le_rfl)
    (fMe : ∀ v, Km.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) : Prop :=
  ∀ v (t : latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
      (Submodule.span (𝓞 D.host.E)
        (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) Km.lev.Lb)))
    (x : Fin (D.R.N D.R.m) → D.host.E) (r : 𝓞 D.host.E),
    t.1 = (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (x a)) →
    (r : D.host.E) = hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) Tl.z0 x →
    fMe v (Km.lev.fT (A.eV v).1 (A.eV v).2 t) = A.res v r

set_option maxHeartbeats 4000000 in

structure TilAd {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    (Tl : TilTied u A K P) (Km : ClsTied u D.R.m le_rfl) where
  ka : (D.fm u).clsP → Km.lev.U
  til_ad : ∀ c (g : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsExt D Tl.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K.y c).1.1 g.1 →
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tl.ga c).1 * (Km.y ((D.fm u).til c)).1 =
      g * (ka c).1

set_option maxHeartbeats 4000000 in

def FrExt {u : D.what₂.Word} (z0 : Fin (D.R.N D.R.m) → D.host.E) {K : ClsPTied u} {Km : ClsTied u D.R.m le_rfl}
    {G : GLoc D.host.F D.host.E (sigD D) D.host.g} {a t nb sk fc a' t' nb' sk' fc' : ℕ} {zl zl' : Bool}
    (Lm : GLev Km.lev G a t nb sk fc zl) (Lp : GLev K.lev G a' t' nb' sk' fc' zl') : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal),
    (∀ (x : Fin (D.R.N D.R.m)) (b : Fin (D.R.N D.R.m - 1)) (b' : Fin (D.R.N D.R.m)), (b : ℕ) = b' →
      (Lm.fr i v h).1 x b' =
        ((iXm D).map ((G.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))) * (Lp.fr i v h).1) x b) ∧
    ∀ (x l : Fin (D.R.N D.R.m)), (l : ℕ) + 1 = D.R.N D.R.m →
      (Lm.fr i v h).1 x l = G.phi i v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) (z0 x))

end Formalism.L2.Forms
end
end

section
namespace Formalism.L2.Forms
open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem AdFun_transport (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (g) (hg : g ∈ AdFun S emb) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x'.1 = x.1 * κ.1)
    (y y' : Frames (gramC J emb)) (hy : IsTr (atInf emb γ) y' y) :
    g x y = ((S.chi κ)⁻¹ : ℂˣ) * g x' y' := by
  have h2 : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x'.1 * (κ⁻¹ : S.U).1 := by
    rw [h]; simp
  have := hg γ hγ x' x κ⁻¹ h2 y y' hy
  rw [this, map_inv]

end Formalism.L2.Forms
end

section
namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 4000000 in
theorem UpTie.explicit {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : UpTie P K W)
    (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (hz : (D.fm u).fv i v c (P.pr v c z) = 1) :
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : K.lev.U), ∀ g ∈ AdFun K.lev (embT D), ∀ s s',
      IsTr (atInf (embT D) γ.1.1) (W.eY s') (W.eY s) →
      (D.fm u).upT i v c (P.pr v c z) (fun s => g (K.y ((D.fm u).up i v c (P.pr v c z))) (W.eY s)) s =
        (((K.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * g (K.y ((D.fm u).up i v c (P.pr v c z))) (W.eY s') := by
  obtain ⟨γ, η, κ, _, heq, _, _, _, htr⟩ := h v c z hz
  refine ⟨γ, κ, fun g hg s s' hs => ?_⟩
  rw [htr g hg]
  exact AdFun_transport K.lev (embT D) g hg γ.1 γ.2 (K.y c * η) _ κ heq _ _ hs

set_option maxHeartbeats 4000000 in
theorem DnTie.explicit {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : DnTie P K W)
    (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (hg0 : g ≠ 0) :
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : K.lev.U), ∀ f ∈ AdFun K.lev (embT D), ∀ s s',
      IsTr (atInf (embT D) γ.1.1) (W.eY s') (W.eY s) →
      (D.fm u).dnT i v c g (fun s => f (K.y ((D.fm u).dn i v c g)) (W.eY s)) s =
        (((K.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * f (K.y ((D.fm u).dn i v c g)) (W.eY s') := by
  obtain ⟨γ, η, κ, _, heq, _, _, htr⟩ := h v c g hg0
  refine ⟨γ, κ, fun f hf s s' hs => ?_⟩
  rw [htr f hf]
  exact AdFun_transport K.lev (embT D) f hf γ.1 γ.2 (K.y c * η) _ κ heq _ _ hs

set_option maxHeartbeats 4000000 in

theorem UpNatTie.upTie {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : UpNatTie P K W) :
    UpTie P K W := by
  intro v c z hz
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h v c z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g hg => ?_⟩
  funext s
  obtain ⟨y', hy'⟩ := exists_isTr' (embT D) γ.1 (W.eY s)
  have hs : IsTr (atInf (embT D) γ.1.1) (W.eY (W.eY.symm y')) (W.eY s) := by
    rw [Equiv.apply_symm_apply]; exact hy'
  rw [h6 _ s _ hs]
  exact (AdFun_transport K.lev (embT D) g hg γ.1 γ.2 (K.y c * η) _ κ h2 _ _ hs).symm

set_option maxHeartbeats 4000000 in

theorem DnNatTie.dnTie {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : DnNatTie P K W) :
    DnTie P K W := by
  intro v c g hg0
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5⟩ := h v c g hg0
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun f hf => ?_⟩
  funext s
  obtain ⟨y', hy'⟩ := exists_isTr' (embT D) γ.1 (W.eY s)
  have hs : IsTr (atInf (embT D) γ.1.1) (W.eY (W.eY.symm y')) (W.eY s) := by
    rw [Equiv.apply_symm_apply]; exact hy'
  rw [h5 _ s _ hs]
  exact (AdFun_transport K.lev (embT D) f hf γ.1 γ.2 (K.y c * η) _ κ h2 _ _ hs).symm

end Formalism.L2.Forms
end

section
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7}

def EvzTie {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    {Tl : TilTied u A K P} {Km : ClsTied u D.R.m le_rfl}
    (Ta : TilAd Tl Km) (W : ValTied u A.eV D.R.m le_rfl Km)
    (eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)) : Prop :=
  ∀ (φ : (D.mem u).C.cls D.R.m → (D.mem u).C.Y D.R.m → ℂ) c s s',
    IsTr (atInf (embT D) (Tl.ga c).1.1) (W.eY s') (W.eY s) →
    eWz ((D.mem u).P.evz φ) c s = (((Km.lev.chi (Ta.ka c))⁻¹ : ℂˣ) : ℂ) * φ ((D.fm u).til c) s'

open Classical in

def BwTie {u : D.what₂.Word} (A : AtTTied u) {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u A.eV i hi K) : Prop :=
  ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (D.fm u).seenP w = true →
    ∀ v (x : ((D.fm u).lat i).V), x ∈ (D.fm u).Bw i w v ↔
    ∀ (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B → IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B' →
      ∃ P ∈ IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i x c z =
        fnOf _ (shiftOf (lamT u i))
          (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ
            else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ) P (W.eY z)

def PerTie (u : D.what₂.Word) (jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow) : Prop :=
  (∀ z ∈ (D.fm u).ptC, ∃ F, jM F = z) ∧ (∀ F, jM F ∈ (D.fm u).ptC) ∧
    ∀ w F, (D.mem u).P.period w F = (D.fm u).ipP (jM F) w

def subP {ι : Type} {n : ℕ} (o : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  MvPolynomial.aeval fun x => ∑ a', MvPolynomial.C (o x.1 x.2.1 a') * MvPolynomial.X (x.1, a', x.2.2)

def embS (D : D7) (s : D.what₂.LL →+* ℂ) : D.what₂.Tau → D.host.E →+* ℂ :=
  fun τ => s.comp (D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

def NormTie {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u eV i hi K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : ((D.fm u).lat i).V)
    (Pc : (D.mem u).C.cls i → MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) D.what₂.LL),
    (∀ c z, (D.fm u).emb i x c z =
      fnOf _ (shiftOf (lamT u i)) 1 (MvPolynomial.map D.what₂.embLL (Pc c)) (W.eY z)) →
    ∀ o : Frames (gramC (gramN D i hi) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk s) x x).re =
        ∑ c, ((D.mem u).C.wt i c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u i) τ)) *
          (nfAll ((D.fm u).lam i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def NormPTie {u : D.what₂.Word} {K : ClsPTied u} (W : ValPTied u K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : (D.fm u).ptLat.V)
    (Pc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW ((D.fm u).ptEmb x) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (nfAll (D.fm u).sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def aOf (R : Ranks) (i : ℕ) : ℕ := if i < R.m then R.k + i else R.r

def skipOf (R : Ranks) (i : ℕ) : ℕ := if i + 1 < R.m then R.k else R.N i

def fcOf (R : Ranks) (i : ℕ) : ℕ := if R.m ≤ i + 1 then R.k else R.N i

theorem fcOf_lt {R : Ranks} {i : ℕ} (h : i + 1 < R.m) : fcOf R i = R.N i := if_neg (Nat.not_le.2 h)


set_option maxHeartbeats 1000000 in

structure FormsTied (D : D7) (u : D.what₂.Word) where
  atT : AtTTied u
  cls : ∀ i hi, ClsTied u i hi
  val : ∀ i hi, ValTied u atT.eV i hi (cls i hi)

  gl : GLoc D.host.F D.host.E (sigD D) D.host.g
  gl_K : ∀ i, (gl.piG i : D.host.E) ∈ D.host.K

  glev : ∀ i hi, GLev (cls i hi).lev gl (aOf D.R i) D.R.t i (skipOf D.R i) (fcOf D.R i) (decide (i = D.R.m))
  lv : ∀ i hi, LvTied u atT i hi
  fMe : ∀ i hi v, (cls i hi).lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fv : ∀ i hi, FvTie (lv i hi) (cls i hi) (fMe i hi)

  upN : ∀ i hi, UpNatTie (lv i hi) (cls i hi) (val i hi)
  dnN : ∀ i hi, DnNatTie (lv i hi) (cls i hi) (val i hi)
  norm : ∀ i hi, NormTie (val i hi)
  bw : ∀ i hi, BwTie atT (val i hi)
  clsP : ClsPTied u
  valP : ValPTied u clsP
  normP : NormPTie valP

  glevP : GLev clsP.lev gl D.R.r D.R.t D.R.m (D.R.N D.R.m) (fcOf D.R D.R.m) false
  til : TilTied u atT clsP (lv D.R.m le_rfl)
  tilLat : TilBaseLat til (cls D.R.m le_rfl)
  tilFv : TilBaseFv til (cls D.R.m le_rfl) (fMe D.R.m le_rfl)
  tilAd : TilAd til (cls D.R.m le_rfl)
  frExt : FrExt til.z0 (glev D.R.m le_rfl) glevP
  eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)
  evz : EvzTie tilAd (val D.R.m le_rfl) eWz
  jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow
  per : PerTie u jM

  DGam : (D.mem u).C.DGam = (D.mem D.u₀).C.DGam

theorem FormsTied.up {u : D.what₂.Word} (T : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) :
    UpTie (T.lv i hi) (T.cls i hi) (T.val i hi) := (T.upN i hi).upTie

theorem FormsTied.dn {u : D.what₂.Word} (T : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) :
    DnTie (T.lv i hi) (T.cls i hi) (T.val i hi) := (T.dnN i hi).dnTie

theorem Mu0_iff {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :
    φ ∈ (D.mem u).A.Mu0 ↔
      (fun c z => φ c (W.eY.symm z)) ∈ FiC K.lev (embT D) ((D.fm u).lam 0) K.y := by
  rw [← (D.fm u).Fi_zero, ← lamT_zero]; exact W.Fi φ

theorem rhoT_eq {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia K.lev (eV v).1 (eV v).2 k δ) (g) (hg : g ∈ AdFun K.lev (embT D)) :
    (D.mem u).A.rhoT v a (fun c s => g (K.y c) (W.eY s)) = fun c s => g (K.y c * δ) (W.eY s) := by
  funext c
  rw [(D.fm u).rhoT_dil]
  exact W.dilT v a k hk c δ hδ g hg

end Formalism.L2.Forms
end
end
