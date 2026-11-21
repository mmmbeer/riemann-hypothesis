import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.IsLowPairZero
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSc

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDualParamAt {S : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (τ : D.what₂.Tau) (α : ℚ) {r s : ℕ}
    (lam' : Ix r s → ℚ) : Prop :=
  ∃ e : Fin S.rank ≃ Ix r s, ∀ a, (M.ε τ a = true ↔ (e a).isLeft = true) ∧ M.lam τ a = (α : ℝ) + (lam' (e a) : ℝ)

open Classical in

def ARvO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T' : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (χS χT : (AE D)ˣ →* Circle)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)),
    Formalism.IndefR.Fock.Sk.PairSetup ψ θ S T' sS sT BS BT pS pT → IsWeilDatumO ψ S T' χS χT om' →
    ∀ (τ : D.what₂.Tau) (αT : ℚ), HasInfExp D χT τ αT →
    ∀ {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (t i : ℕ) (al be ga de : List ℚ),
      ((HypA t al be ga de ∧ HypG t al be ga de ∧ IsDualParamAt M τ αT (lamA' t al be ga de)) ∨
        (HypA t al be ga de ∧ HypGm t al be ga de ∧ IsDualParamAt M τ αT (lamM' t al be ga de))) →
      1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → T'.SigOK →
      T'.sig (tauE D τ) = (al.length + be.length - i, ga.length + de.length - i) →
      (¬ (∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2) ∨ ¬ (∃ a, lamA al be ga de a = -(((t : ℚ) + 1) / 2))) →
      ∀ f₀ : WO S T' → ℂ, IsThetaFunO ψ S T' f₀ →
        (∀ τ', IsFockVacAt (heisO ψ S T') θ τ' (cplxO (sS τ') (sT τ')) f₀) →
      ∀ B : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ),
        IsLowPair θ M om' (pureTensorO ψ θ S T' sS sT BS BT f₀) B →
        (∀ v, IsLinearMap ℂ (fun φ => B φ v)) →
        (∀ φ τ' (v : M.Vec) (w w' : M.sm τ') (c : ℂ),
          B φ (Function.update v τ' (c • w + w')) = c • B φ (Function.update v τ' w) + B φ (Function.update v τ' w')) →
        (∀ φ τ' (v : M.Vec) (g' : GA D T'), ∃ ℓ : M.H τ' →ₗ[ℂ] ℂ, Sobolev₂ (lieAt S τ') (M.rep τ') ℓ ∧
          ∀ w : M.sm τ', ℓ w = B φ (Function.update v τ' w) g') →
        B = 0

end Formalism.IndefR.Tow

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def KAt {k : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ) :=
  {g | g ∈ Formalism.QuantumDeterminants.UH G ∧ g * s = s * g}

def KFinAt {S : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (τ : D.what₂.Tau)
    (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) (w : M.H τ) : Prop :=
  ∃ W : Submodule ℂ (M.H τ), FiniteDimensional ℂ W ∧ w ∈ W ∧
    ∀ g ∈ KAt (gramAt D S τ) s, ∀ x ∈ W, M.rep τ g x ∈ W

def DSTiesSq (X : ProvA) : Prop :=
  ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → ∃ e ε lamS c σ χ E, Formalism.MainNotions.J.DSTieAt X p q lam e ε lamS c σ χ E ∧
    ∃ m : ℤ, (m : ℝ) = 2 * c ∧ ∀ g, χ g = (((X.grp p q).sq g : ℂˣ) : ℂ) ^ (-m)

open Classical in

def GlobalThetaOrthogonality (D : D7) : Prop :=
  ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.AdmA X → ProvisionCompatibility D X → DSTiesSq X →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T' : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (χS χT : (AE D)ˣ →* Circle)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)),
    Formalism.IndefR.Fock.Sk.PairSetup ψ θ S T' sS sT BS BT pS pT → IsWeilDatumO ψ S T' χS χT om' →
    ∀ (τ : D.what₂.Tau) (αT : ℚ), HasInfExp D χT τ αT →
    ∀ {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) {p q r s : ℕ} (lam' : Ix r s → ℚ),
      IsParam lam' → GapGt lam' (((r + s : ℕ) : ℝ) ^ 3) → IsDualParamAt M τ αT lam' → T'.SigOK →
      T'.sig (tauE D τ) = (p, q) →
      ∀ f₀ : WO S T' → ℂ, IsThetaFunO ψ S T' f₀ →
        (∀ τ', IsFockVacAt (heisO ψ S T') θ τ' (cplxO (sS τ') (sT τ')) f₀) →
      ∀ B : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ),
        IsLowPair θ M om' (pureTensorO ψ θ S T' sS sT BS BT f₀) B →
        (∀ v, IsLinearMap ℂ (fun φ => B φ v)) →
        (∀ φ τ' (v : M.Vec) (w w' : M.sm τ') (c : ℂ),
          B φ (Function.update v τ' (c • w + w')) = c • B φ (Function.update v τ' w) + B φ (Function.update v τ' w')) →
        ∀ φ (v : M.Vec) (g' : GA D T'), KFinAt M τ (sS τ) (v τ : M.H τ) → B φ v g' ≠ 0 →
          ∃ (MM : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam').HK.V),
            IsIntw (X.fock p q r s) MM (X.ds r s lam').HK f ∧ f ≠ 0

open Classical in

def ArvOKF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T' : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (χS χT : (AE D)ˣ →* Circle)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)),
    Formalism.IndefR.Fock.Sk.PairSetup ψ θ S T' sS sT BS BT pS pT → IsWeilDatumO ψ S T' χS χT om' →
    ∀ (τ : D.what₂.Tau) (αT : ℚ), HasInfExp D χT τ αT →
    ∀ {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (t i : ℕ) (al be ga de : List ℚ),
      ((HypA t al be ga de ∧ HypG t al be ga de ∧ IsDualParamAt M τ αT (lamA' t al be ga de)) ∨
        (HypA t al be ga de ∧ HypGm t al be ga de ∧ IsDualParamAt M τ αT (lamM' t al be ga de))) →
      1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → T'.SigOK →
      T'.sig (tauE D τ) = (al.length + be.length - i, ga.length + de.length - i) →
      (¬ (∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2) ∨ ¬ (∃ a, lamA al be ga de a = -(((t : ℚ) + 1) / 2))) →
      ∀ f₀ : WO S T' → ℂ, IsThetaFunO ψ S T' f₀ →
        (∀ τ', IsFockVacAt (heisO ψ S T') θ τ' (cplxO (sS τ') (sT τ')) f₀) →
      ∀ B : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ),
        IsLowPair θ M om' (pureTensorO ψ θ S T' sS sT BS BT f₀) B →
        (∀ v, IsLinearMap ℂ (fun φ => B φ v)) →
        (∀ φ τ' (v : M.Vec) (w w' : M.sm τ') (c : ℂ),
          B φ (Function.update v τ' (c • w + w')) = c • B φ (Function.update v τ' w) + B φ (Function.update v τ' w')) →
        ∀ φ (v : M.Vec) (g' : GA D T'), KFinAt M τ (sS τ) (v τ : M.H τ) → B φ v g' = 0

end Formalism.IndefR.Tow

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

def lieG {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | Xᴴ * G + G * X = 0}

def IsGRep {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  π 1 = 1 ∧ (∀ a ∈ Formalism.QuantumDeterminants.UH G, ∀ b ∈ Formalism.QuantumDeterminants.UH G, π (a * b) = (π a).comp (π b)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ v : H, ‖π g v‖ = ‖v‖) ∧ ∀ v : H, ContinuousOn (fun g => π g v) (Formalism.QuantumDeterminants.UH G)

def dL {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H) : H :=
  l.foldr (dRep π) w

def oneProd {n d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (List.ofFn fun i => NormedSpace.exp (t i • Y i)).prod

def KFinG {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (G s : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ w ∈ W ∧ ∀ g ∈ KAt G s, ∀ x ∈ W, π g x ∈ W

def evP {n : ℕ} (q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) (k : Fin n → Fin n → ℂ) : ℂ :=
  MvPolynomial.eval (Sum.elim (fun ij => k ij.1 ij.2) (fun ij => starRingEnd ℂ (k ij.1 ij.2))) q

def IsHaarK {n : ℕ} (G s : Matrix (Fin n) (Fin n) ℂ) (μ : Measure (Fin n → Fin n → ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ k ∂μ, Matrix.of k ∈ KAt G s) ∧
    (∀ k₀ ∈ KAt G s, μ.map (fun k => Matrix.of.symm (k₀ * Matrix.of k)) = μ) ∧
    ∀ U : Set (Fin n → Fin n → ℂ), IsOpen U → (∃ k ∈ U, Matrix.of k ∈ KAt G s) → 0 < μ U

def SobRepM (D : D7) : Prop :=
  ∀ {S : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (τ : D.what₂.Tau),
    CompleteSpace (M.H τ) ∧ IsGRep (gramAt D S τ) (M.rep τ)

def SmoothLin : Prop :=
  ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G : Matrix (Fin n) (Fin n) ℂ)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsGRep G π →
    SmoothVec (lieG G) π 0 ∧
    ∀ (c : ℂ) (u v : H), SmoothVec (lieG G) π u → SmoothVec (lieG G) π v → SmoothVec (lieG G) π (c • u + v)

def FoldLin : Prop :=
  ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G : Matrix (Fin n) (Fin n) ℂ)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsGRep G π →
    ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ (c : ℝ) (u v : H),
      SmoothVec (lieG G) π u → SmoothVec (lieG G) π v → dL π l (c • u + v) = c • dL π l u + dL π l v

def SobChart : Prop :=
  ∀ {n : ℕ} (G s : Matrix (Fin n) (Fin n) ℂ), IsCartanInv G s →
    ∃ (d : ℕ) (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieG G) ∧
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ g ∈ Formalism.QuantumDeterminants.UH G, (∀ i j, ‖g i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ) →
        ∃ t : Fin d → ℝ, (∀ i, |t i| < ε) ∧ g = oneProd Y t

def FoldCont : Prop :=
  ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G : Matrix (Fin n) (Fin n) ℂ)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsGRep G π →
    ∀ w : H, SmoothVec (lieG G) π w → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) →
      ∀ (d : ℕ) (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieG G) →
        Continuous fun t : Fin d → ℝ => dL π l (π (oneProd Y t) w)

def Cont1 : Prop :=
  ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G s : Matrix (Fin n) (Fin n) ℂ)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsCartanInv G s → IsGRep G π →
    ∀ w : H, SmoothVec (lieG G) π w → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) →
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ g ∈ Formalism.QuantumDeterminants.UH G,
        (∀ i j, ‖g i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ) → ‖dL π l (π g w) - dL π l w‖ < ε

def FoldBddK : Prop :=
  ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G s : Matrix (Fin n) (Fin n) ℂ)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsCartanInv G s → IsGRep G π →
    ∀ w : H, SmoothVec (lieG G) π w → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) →
      ∃ B : ℝ, ∀ k ∈ KAt G s, ‖dL π l (π k w)‖ ≤ B

def HaarExists : Prop :=
  ∀ {n : ℕ} (G s : Matrix (Fin n) (Fin n) ℂ), IsCartanInv G s → ∃ μ, IsHaarK G s μ

def PolyKernel : Prop :=
  ∀ {n : ℕ} (G s : Matrix (Fin n) (Fin n) ℂ), IsCartanInv G s → ∀ μ, IsHaarK G s μ →
    ∀ U ∈ 𝓝 (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)), ∀ η > (0 : ℝ),
      ∃ q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Integrable (evP q) μ ∧
        ∫ k, evP q k ∂μ = 1 ∧ ∫ k, ‖evP q k‖ ∂μ ≤ 1 ∧ ∫ k in Uᶜ, ‖evP q k‖ ∂μ < η

def AvgSmooth : Prop :=
  ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G s : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsCartanInv G s → IsGRep G π →
    ∀ μ, IsHaarK G s μ → ∀ p : (Fin n → Fin n → ℂ) → ℂ, Continuous p →
      ∀ w : H, SmoothVec (lieG G) π w →
        SmoothVec (lieG G) π (∫ k, p k • π (Matrix.of k) w ∂μ) ∧
        ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) →
          Integrable (fun k => p k • dL π l (π (Matrix.of k) w)) μ ∧
          dL π l (∫ k, p k • π (Matrix.of k) w ∂μ) = ∫ k, p k • dL π l (π (Matrix.of k) w) ∂μ

def AvgKFin : Prop :=
  ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G s : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsCartanInv G s → IsGRep G π →
    ∀ μ, IsHaarK G s μ → ∀ (q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) (w : H),
      KFinG G s π (∫ k, evP q k • π (Matrix.of k) w ∂μ)

def SobApprox : Prop :=
  ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G s : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsCartanInv G s → IsGRep G π →
    ∀ w : H, SmoothVec (lieG G) π w → ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieG G) →
      ∀ ε > (0 : ℝ), ∃ v : H, SmoothVec (lieG G) π v ∧ KFinG G s π v ∧ ∀ l ∈ S, ‖dL π l v - dL π l w‖ < ε

end Formalism.IndefR.Tow.SobPf

end
end
