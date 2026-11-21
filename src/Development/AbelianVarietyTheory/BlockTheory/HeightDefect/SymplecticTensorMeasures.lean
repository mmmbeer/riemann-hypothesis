import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev cE (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem cE_cE (x : D.host.E) : cE D (cE D x) = x := star_star x

theorem cA_inc (x : D.host.E) : cA D (incA D x) = incA D (cE D x) := by
  simp [cA, incA, sigR, inclR]

theorem cA_cA (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have : D.sp.cm.sig (D.sp.cm.sig e) = e := star_star e
    simp [cA, sigR, this]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem conj_map_mem_unitaryGroup {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (P g : GL (Fin n) R)
    (hP : Formalism.UG.cT c P.val * J * P.val = J.map c) (hg : g ∈ Formalism.UG.UJ c J) :
    (MulAut.conj P).toMonoidHom.comp (Matrix.GeneralLinearGroup.map c) g ∈ Formalism.UG.UJ c J := by
  have hg' : Formalism.UG.cT c g.val * J * g.val = J := hg
  have hc := congrArg (fun M => M.map c) hg'
  simp only [Matrix.map_mul] at hc
  have e : (Formalism.UG.cT c g.val).map c = Formalism.UG.cT c (g.val.map c) := rfl
  rw [e] at hc
  have hAB : P.val * (P⁻¹).val = 1 := P.mul_inv
  show Formalism.UG.cT c (P.val * g.val.map c * (P⁻¹).val) * J * (P.val * g.val.map c * (P⁻¹).val) = J
  generalize (P⁻¹).val = B at *
  generalize P.val = A at *
  generalize g.val.map c = G at *
  calc Formalism.UG.cT c (A * G * B) * J * (A * G * B)
      = Formalism.UG.cT c B * (Formalism.UG.cT c G * (Formalism.UG.cT c A * J * A) * G) * B := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT c B * (Formalism.UG.cT c A * J * A) * B := by rw [hP, hc]
    _ = Formalism.UG.cT c (A * B) * J * (A * B) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hAB, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

structure ConjIsom (V : HSp D) where
  P : GL (Fin V.rank) D.host.E
  iso : Formalism.UG.cT (cE D) P.val * V.gram * P.val = V.gram.map (cE D)

namespace ConjIsom

variable {V : HSp D} (s : ConjIsom V)

def toFun (x : Fin V.rank → D.host.E) : Fin V.rank → D.host.E :=
  s.P.val.mulVec fun i => cE D (x i)

def PA : GL (Fin V.rank) (AE D) := Matrix.GeneralLinearGroup.map (incA D) s.P

def autGL : GL (Fin V.rank) (AE D) →* GL (Fin V.rank) (AE D) :=
  (MulAut.conj s.PA).toMonoidHom.comp (Matrix.GeneralLinearGroup.map (cA D))

theorem isoA : Formalism.UG.cT (cA D) s.PA.val * V.gram.map (incA D) *
    s.PA.val = (V.gram.map (incA D)).map (cA D) := by
  have h := congrArg (fun M => M.map (incA D)) s.iso
  simp only [Matrix.map_mul] at h
  have e1 : (Formalism.UG.cT (cE D) s.P.val).map (incA D) =
      Formalism.UG.cT (cA D) s.PA.val := by
    ext i j
    exact (cA_inc _).symm
  have e2 : (V.gram.map (cE D)).map (incA D) = (V.gram.map (incA D)).map (cA D) := by
    ext i j
    exact (cA_inc _).symm
  rw [e1, e2] at h
  exact h

theorem autGL_mem (g : GL (Fin V.rank) (AE D)) (hg : g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) :
    s.autGL g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
  conj_map_mem_unitaryGroup (cA D) (V.gram.map (incA D)) s.PA g s.isoA hg

def aut : GA D V →* GA D V :=
  (s.autGL.comp (matHom V)).codRestrict (HR (AF D.host.F) D.sp.cm.sig V.gram) fun g => s.autGL_mem _ g.2


end ConjIsom

theorem gram_herm (V : HSp D) : Formalism.UG.cT (cE D) V.gram = V.gram := by
  funext i j
  exact V.herm.eq (V.frame j) (V.frame i)

def ConjIsom.ofOrth (V : HSp D) (Q : GL (Fin V.rank) D.host.E)
    (hQ : ∀ i j, i ≠ j → (Formalism.UG.cT (cE D) Q.val * V.gram *
      Q.val) i j = 0) : ConjIsom V where
  P := Q * (Matrix.GeneralLinearGroup.map (cE D) Q)⁻¹
  iso := by
    set q : Matrix (Fin V.rank) (Fin V.rank) D.host.E := Q.val with hq
    set R : GL (Fin V.rank) D.host.E := Matrix.GeneralLinearGroup.map (cE D) Q with hR
    set b : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (R⁻¹).val with hb
    have hab : q.map (cE D) * b = 1 := R.mul_inv
    set d := Formalism.UG.cT (cE D) q * V.gram * q with hd
    have hcc : ∀ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.UG.cT (cE D) (Formalism.UG.cT (cE D) M) = M := by
      intro M; funext i j; exact cE_cE _
    have hdh : Formalism.UG.cT (cE D) d = d := by
      rw [hd, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcc, gram_herm, Matrix.mul_assoc]
    have hdc : d.map (cE D) = d := by
      funext i j
      by_cases h : i = j
      · subst h; exact congrFun (congrFun hdh i) i
      · show cE D (d i j) = d i j
        rw [hQ i j h, map_zero]
    have hd2 : d = Formalism.UG.cT (cE D) (q.map (cE D)) * V.gram.map (cE D) * q.map (cE D) := by
      rw [← hdc, hd, Matrix.map_mul, Matrix.map_mul]; rfl
    show Formalism.UG.cT (cE D) (q * b) * V.gram * (q * b) = _
    calc Formalism.UG.cT (cE D) (q * b) * V.gram * (q * b) = Formalism.UG.cT (cE D) b * d * b := by
          rw [Formalism.UG.cT_mul, hd]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT (cE D) (q.map (cE D) * b) * V.gram.map (cE D) * (q.map (cE D) * b) := by
          rw [hd2, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = V.gram.map (cE D) := by rw [hab, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

def basConj {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} (K : KfinTied Wl) (V : HSp D) (hV : V.SigOK) :
    ConjIsom V :=
  ConjIsom.ofOrth V (Matrix.nonsingInvUnit (K.bas V) (K.bas_unit V hV)) (K.bas_orth V hV)

theorem basConj_fix {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} (K : KfinTied Wl) (V : HSp D) (hV : V.SigOK) :
    (basConj K V hV).P.val * (K.bas V).map (cE D) = K.bas V := by
  set Q := Matrix.nonsingInvUnit (K.bas V) (K.bas_unit V hV)
  have h : (basConj K V hV).P * Matrix.GeneralLinearGroup.map (cE D) Q = Q := inv_mul_cancel_right Q _
  exact congrArg Units.val h

def hTens (V W : HSp D) (x y : WA V W) : AE D :=
  ∑ i, ∑ j, ∑ k, ∑ l, cA D (y i j) * incA D (V.gram i k) * incA D (W.gram j l) * x k l

def toHom {V W : HSp D} (s : ConjIsom V) (t : ConjIsom W) (y : WA V W) : WA V W :=
  if V.rank ≤ W.rank then HMul.hMul (cM s.PA.val) y else HMul.hMul y (cM t.PA.val).transpose

def pairAut {V W : HSp D} (s : ConjIsom V) (t : ConjIsom W) : GA D V × GA D W →* GA D V × GA D W :=
  if V.rank ≤ W.rank then s.aut.prodMap (MonoidHom.id _) else (MonoidHom.id _).prodMap t.aut

def omTens {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {V W : HSp D} (s : ConjIsom V) (t : ConjIsom W)
    (χ χ' : X.Chr) : GA D V × GA D W →* Module.End ℂ (X.Sch V W) :=
  (Wl.om V W χ χ').comp (pairAut s t)

def IsFinK (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (g : GA D V) : Prop :=
  ∃ f ∈ GfC V, ∃ k, IsKinf θ V A k ∧ g = f * k

def htFin (V : HSp D) (g : GA D V) : ℕ :=
  ((latHat D.host.F D.host.E (L0c D V)).comap
    (Matrix.mulVecLin (finMat D.sp.cm.sig V.gram g)).toAddMonoidHom).relIndex (latHat D.host.F D.host.E (L0c D V))

def htStd (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) : ℝ :=
  (htFin V g : ℝ) * (1 + ∑ τ, ∑ i, ∑ j, ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖)

def IsHeckeCharF (D : D7) (χ : (AF D.host.F)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ a : D.host.Fˣ, χ (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1

def realFac (r : ℕ → ℕ → NNReal) (V : HSp D) : NNReal :=
  ∏ τ : D.what₂.Tau, r (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2

variable {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T}

structure KfinLocalWeilDatum (K : KfinTied Wl) (L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X) where

  eG : ∀ V, L.G V ≃* GA D V

  eG_meas : ∀ V (S : Set (L.G V)), MeasurableSet S ↔ MeasurableSet (eG V '' S)

  gF : ∀ V g, g ∈ L.GF V ↔ eG V g ∈ GQ V

  gK : AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → ∀ g, g ∈ L.Gk V ↔ IsFinK θ V (K.cpt V) (eG V g)

  rc : ℕ → ℕ → NNReal
  rc_pos : ∀ p q, 0 < rc p q

  meas : ∀ V : HSp D, V.SigOK →
    AllSome (IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2)) fun μ =>
      Measure.map (eG V) (L.μG V) = realFac rc V • μ

  eF : L.ChrF →* ((AF D.host.F)ˣ →* Circle)
  eF_inj : Function.Injective eF
  eF_range : Set.range eF = {χ | IsHeckeCharF D χ}

  res : ∀ χ a, eF (L.res χ) a = T.eChr χ (idF D a)

  eta : IsEta D (eF L.eta)

  thF : ∀ V W : HSp D, V.rank ≠ W.rank → ∀ Φ, L.thF V W Φ = Wl.evS V W Φ 0

  om : ∀ (V W : HSp D) (hV : V.SigOK) (hW : W.SigOK) χ χ', V.rank ≠ W.rank →
    ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → ∀ g h,
      L.om V W χ χ' (g, h) = omTens Wl (basConj K V hV) (basConj K W hW) χ χ' (eG V g, eG W h)

structure LocWTied (K : KfinTied Wl) (L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X) extends KfinLocalWeilDatum K L where

  cc : ∀ χ x, T.eChr (L.cc χ) x = T.eChr χ (Units.map (cA D).toMonoidHom x)

  ht : AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, ∃ (C : ℝ) (N : ℕ), ∀ g,
    L.ht V g ≤ C * htStd θ V (eG V g) ^ N ∧ htStd θ V (eG V g) ≤ C * L.ht V g ^ N

  sR : L.sR = true

def AutProps (D : D7) : Prop :=
  ∀ (V : HSp D) (s : ConjIsom V), IsHomeomorph s.aut ∧ ∀ g, (s.aut g ∈ GQ V ↔ g ∈ GQ V) ∧ (s.aut g ∈ GfC V ↔ g ∈ GfC V) ∧
    (s.aut g ∈ GinfC V ↔ g ∈ GinfC V) ∧ (mt V (s.aut g)).det = cA D (mt V g).det

end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures

end
