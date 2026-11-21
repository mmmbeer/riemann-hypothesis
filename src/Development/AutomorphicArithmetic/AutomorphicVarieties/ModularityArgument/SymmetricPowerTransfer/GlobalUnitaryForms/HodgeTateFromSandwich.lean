import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Defs

variable {K : Type} [Field K]

def jstd (τ : K) : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix (QuadraticAlgebra.basis (-1) τ)

def Cu (O : Type) [CommRing O] [Algebra O K] (τ : K) : Subgroup (Etau K τ)ˣ :=
  (Units.map ((integralClosure O (Etau K τ)).val : integralClosure O (Etau K τ) →* Etau K τ)).range

def scalE (τ : K) : Subgroup (Etau K τ)ˣ := (Units.map (algebraMap K (Etau K τ) : K →* Etau K τ)).range

open Classical in

def toUnit {R : Type} [Monoid R] (x : R) : Rˣ := if h : IsUnit x then h.unit else 1

variable {F : Type} [Field F] [NumberField F]

abbrev TA (τ : F) : Type := RP (fun v : Pl F => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ)

def IsDiagT (τ : F) (φ : (Etau F τ)ˣ →* TA τ) : Prop := ∀ z v, ((φ z).1 v : Etau (Kv v) (cv v τ)) = emap (cv v) τ z

open Classical in

def ms (τ : F) : ℂ :=
  if h : ∃ φ, IsDiagT τ φ then mass h.choose (scalE τ) ((rpg _ _).box fun v => Cint (Ov v) (cv v τ)) else 0

variable {Δ : F} (D : Dat Δ)

def Dat.Good (t : Dat.Par F) (τ : F) : Prop := (∀ σ : F →+* ℝ, σ (τ ^ 2 - 4) < 0) ∧ ∀ v ∈ D.Sg, Ind (D.S v).H (cv v τ) (t v)

def Dat.nS (τ : F) : ℂ := ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), gOrb (Ov v) (jstd (cv v τ)) 1 (toUnit QuadraticAlgebra.omega)

def Dat.nK (τ : F) : ℂ := ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), gOrb (Ov v) (jstd (cv v τ)) (D.χ v) (toUnit (1 + QuadraticAlgebra.omega))

def Dat.sumS (ch : F → ℂ) (t : Dat.Par F) : ℂ := ∑ᶠ τ, one (D.Good t τ) * (ch τ * ms τ * D.nS τ)

def Dat.sumK (ch : F → ℂ) (t : Dat.Par F) : ℂ := ∑ᶠ τ, one (D.Good t τ) * (ch τ * ms τ * D.nK τ)

def Dat.Off (x : DA Δ) : Prop := ∀ v ∈ D.Sg, x.1 v = 1

end Defs

def BaseG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (U3 Δ) V) (Θ : V →ₗ[ℂ] V) (ch : F → ℂ), (∀ γ v, Θ (W γ v) = W (theta Δ γ) (Θ v)) →
    (∀ δ τ, HasTau δ τ → LinearMap.trace ℂ V (W δ ∘ₗ Θ) = ch τ) →
    ∃ (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), D.IsBG ch B s ∧ B.W = W ∧ s.Θ = Θ

def BaseS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (SU Δ) V) (ch : F → ℂ), (∀ (γ : SU Δ) τ, HasTr (γ : DX Δ) τ → LinearMap.trace ℂ V (W γ) = ch τ) →
    ∀ x : DA Δ, ∃ B : Base (SU Δ) (SA Δ) V, D.IsBS ch x B ∧ B.W = W

def BaseK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (DX Δ) V) (ch : F → ℂ),
    (∀ z s, IsScal z s → ∀ v, W s v = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ • v) →
    (∀ (g : DX Δ) τ, (mt g).trace = algebraMap F _ (2 + τ) → (mt g).det = algebraMap F _ (2 + τ) → LinearMap.trace ℂ V (W g) = ch τ) →
    ∃ B : Base (DX Δ) (DA Δ) V, D.IsBK ch B ∧ B.W = W

def FinG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), D.IsBG ch B s → B.Fin ∧ ∀ t, D.Cone t → s.IsTest (D.FG t)

def FinS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (x : DA Δ) (B : Base (SU Δ) (SA Δ) V), D.IsBS ch x B → B.Fin ∧ ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FSx t x)

def FinK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (B : Base (DX Δ) (DA Δ) V), D.IsBK ch B → B.Fin ∧ ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FK t)

def SideG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ c e : ℝ, 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw),
    D.IsBG ch B s → ∀ t, D.Cone t → LinearMap.trace ℂ B.Forms (s.R (D.FG t)) = c * (D.sumS ch t + e * D.sumK ch t)

def SideK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Base (DX Δ) (DA Δ) V),
    D.IsBK ch B → ∀ t, D.Cone t → LinearMap.trace ℂ B.Forms ((Base.Tw.one B).R (D.FK t)) = c * D.sumK ch t

def Recip : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d x : F), d ≠ 0 → x ≠ 0 →
    {v : Pl F | hs (cv v d) (cv v x) ≠ 1}.Finite ∧ (∏ᶠ v : Pl F, hs (cv v d) (cv v x)) = ∏ σ : F →+* ℝ, hs (σ d) (σ x)

def SymbolEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d : F), d ≠ 0 → ∀ y : ∀ v : Pl F, (Kv v)ˣ, {v | hs (cv v d) (y v : Kv v) ≠ 1}.Finite →
    (∏ᶠ v : Pl F, hs (cv v d) (y v : Kv v)) = 1 →
    ∃ x : F, x ≠ 0 ∧ (∀ σ : F →+* ℝ, 0 < σ x) ∧ ∀ v, hs (cv v d) (cv v x) = hs (cv v d) (y v : Kv v)

def HsMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (d x y : Kv v), d ≠ 0 → x ≠ 0 → y ≠ 0 → hs d (x * y) = hs d x * hs d y

def HsHasse : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d x : F), d ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, hs (σ d) (σ x) = 1) →
    (∀ v : Pl F, hs (cv v d) (cv v x) = 1) → hs d x = 1

end UpperTheory.V.Z.Sym.Glob
end
end

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Shortcuts

variable {I : Type} (Gv : I → Type) [∀ v, Group (Gv v)] (K : ∀ v, Subgroup (Gv v))

instance rpGroup : Group (RP Gv K) := inferInstance
instance rpDivInvMonoid : DivInvMonoid (RP Gv K) := inferInstance
instance rpMonoid : Monoid (RP Gv K) := inferInstance
instance rpMulOneClass : MulOneClass (RP Gv K) := inferInstance
instance rpMulOne : MulOne (RP Gv K) := inferInstance
instance rpSemigroup : Semigroup (RP Gv K) := inferInstance
instance rpMul : Mul (RP Gv K) := inferInstance
instance rpOne : One (RP Gv K) := inferInstance
instance rpInv : Inv (RP Gv K) := inferInstance

end Shortcuts

section Defs

variable {K K' : Type} [Field K] [Field K']

def elmap (f : K →+* K') {Δ τ : K} (x : EL Δ τ) : EL (f Δ) (f τ) := ⟨lmap f Δ x.re, lmap f Δ x.im⟩

def negU (Δ : K) : U3 Δ := ⟨-1, by simp, by simp⟩

variable {F : Type} [Field F] [NumberField F]

def TPos (x : F) : Prop := ∀ σ : F →+* ℝ, 0 < σ x

def IsCM (τ : F) : Prop := ∀ σ : F →+* ℝ, σ (τ ^ 2 - 4) < 0

def PosF {Δ τ : F} (c : F) (m : EL Δ τ) : Prop := ∀ x : Sp Δ τ, x ≠ 0 → TPos (herm c m x x).re

variable {Δ : F}

def IsIotaG (ι : U3 Δ →* GA Δ) : Prop :=
  ∀ γ v, (((ι γ).1 v : U3 (cv v Δ)) : Matrix (Fin 3) (Fin 3) _) = (γ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map (lmap (cv v) Δ)

def IsIotaD (ι : DX Δ →* DA Δ) : Prop := ∀ γ v, mt ((ι γ).1 v) = (mt γ).map (lmap (cv v) Δ)

variable (D : Dat Δ)

def Dat.admitted (t : Dat.Par F) (τ : F) : Prop := ∀ v ∈ D.Sg, Ind (D.S v).H (cv v τ) (t v)

def Dat.Spl (τ : F) : Prop := ∀ v ∈ D.Sg, IsSquare (cv v τ ^ 2 - 4)

def Dat.Ev (x : F) : Prop := ∀ v ∉ D.Sg, EvenVal (Ov v) (cv v x)

def Dat.Sel (y : F) : Set (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) := {c | TPos (c.out : F) ∧ D.Ev ((c.out : F) * y)}

def Dat.nL {τ : F} (c : F) (d m : EL Δ τ) : ℂ :=
  ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), lcount (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)

end Defs

def IotaEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F), (∃ ι : U3 Δ →* GA Δ, IsIotaG ι) ∧ (∃ ι : DX Δ →* DA Δ, IsIotaD ι) ∧
    ∀ τ : F, ∃ φ, IsDiagT τ φ

def MassFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (τ : F), IsCM τ → ∀ φ, IsDiagT τ φ →
    (φ.range ⊔ (rpg _ _).box fun v => Cint (Ov v) (cv v τ)).index ≠ 0 ∧
    (scalE τ).relIndex (((rpg _ _).box fun v => Cint (Ov v) (cv v τ)).comap φ) ≠ 0

def ChiVal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ v (x : (Kv v)ˣ) (x₀ : Ov v), algebraMap (Ov v) (Kv v) x₀ = x →
    (D.χ v x : ℂ) = hs (cv v Δ) (x : Kv v) / (Nat.card (Ov v ⧸ Ideal.span {x₀}) : ℂ)

def ChiProd : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ z : Fˣ,
    (∏ᶠ v, (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ)) = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹

def SelCard : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → (D.Sel 1).Finite ∧ (D.Sel 1).Nonempty ∧
    ∀ y : F, TPos y → (D.Sel y).Finite ∧ (D.Sel y).ncard = (D.Sel 1).ncard

def EmbAlg : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K), Δ ≠ 0 → τ ^ 2 - 4 ≠ 0 → ∀ γ : DX Δ, HasTr γ τ →
    (∃ j, IsEmb τ γ j) ∧ (∀ j, IsEmb τ γ j → Function.Injective j ∧ (∀ x, x ∈ j.range ↔ x * γ = γ * x) ∧ (ZD Δ).comap j = scalE τ) ∧
    ∀ γ' : DX Δ, HasTr γ' τ → ∃ x, γ' = x⁻¹ * γ * x

def EmbEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ τ : F, (IsCM τ → ∃ γ : DX Δ, HasTr γ τ) ∧ ∀ γ : DX Δ, HasTr γ τ → τ ^ 2 - 4 ≠ 0 → IsCM τ

def LocD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) j, HasTr γ τ → IsEmb τ γ j → ∀ χ : Kˣ →* ℂˣ, Unr O χ →
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + QuadraticAlgebra.omega →
    orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fun g => one (g ∈ KD Δ O)) γ =
      gOrb O (jstd τ) 1 (toUnit QuadraticAlgebra.omega) ∧
    orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fZD O χ) (j z) = gOrb O (jstd τ) χ (toUnit (1 + QuadraticAlgebra.omega))

def StabLe : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K] (Δ τ : K), Δ ≠ 0 → τ ^ 2 - 4 ≠ 0 →
    (∀ (γ : DX Δ) j, HasTr γ τ → IsEmb τ γ j → ∀ y s, y⁻¹ * j s * y ∈ ZD Δ ⊔ KD Δ O → s ∈ Cint O τ) ∧
    ∀ (c : K) (d m : EL Δ τ) δ ι P, IsDat c d m → Models c d m δ ι P → ∀ y s, y⁻¹ * ι s * y ∈ KU O Δ → s ∈ Cint O τ

def GqS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaD ι → ∀ t, D.Cone t → ∀ τ, IsCM τ → ∀ (γ : DX Δ) j, HasTr γ τ → IsEmb τ γ j →
    gqOn (ι.comp j) (scalE τ) D.UZ (fun y => D.FS t (y.out⁻¹ * ι γ * y.out)) =
      (∏ v ∈ D.Sg, ((D.S v).cS : ℂ)) * (one (D.admitted t τ) * (ms τ * D.nS τ))

def GqK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaD ι → ∀ t, D.Cone t → ∀ τ, IsCM τ → ∀ (γ : DX Δ) j, HasTr γ τ → IsEmb τ γ j →
    ∀ z : (Etau F τ)ˣ, (z : Etau F τ) = 1 + QuadraticAlgebra.omega →
    gqOn (ι.comp j) (scalE τ) D.UZ (fun y => D.FK t (y.out⁻¹ * ι (j z) * y.out)) =
      (∏ v ∈ D.Sg, ((D.S v).cK : ℂ)) * (one (D.admitted t τ) * (ms τ * D.nK τ))

def Fibre : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaD ι → ∀ x₀, D.Off x₀ → ∃ (n : ℕ) (x : Fin (n + 1) → DA Δ) (c : ℝ), x 0 = x₀ ∧ (∀ i, D.Off (x i)) ∧ 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Fin (n + 1) → Base (SU Δ) (SA Δ) V),
    (∀ i, D.IsBS ch (x i) (B i)) → ∀ t, D.Cone t → ∀ (I : Type) (τ : I → F) (γ : I → DX Δ) (j : ∀ i, (Etau F (τ i))ˣ →* DX Δ),
    Function.Injective τ → (∀ i, τ i ^ 2 - 4 ≠ 0 ∧ HasTr (γ i) (τ i) ∧ IsEmb (τ i) (γ i) (j i)) →
    (∀ (g : DX Δ) s, HasTr g s → D.admitted t s → ∃ i, τ i = s) →
    ∑ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R (D.FSx t (x i))) =
      c * ∑ᶠ i, ch (τ i) * gqOn (ι.comp (j i)) (scalE (τ i)) D.UZ fun y => D.FS t (y.out⁻¹ * ι (γ i) * y.out)

def TauEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ δ : U3 Δ, ∃ τ, HasTau δ τ ∧ (τ ^ 2 - 4 ≠ 0 → IsCM τ)

def ModelFacts : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Δ τ c : K) (d m : EL Δ τ) δ ι P, Δ ≠ 0 → IsDat c d m → Models c d m δ ι P →
    HasTau δ τ ∧ ι.ker = scalE τ ∧ negU Δ ∉ ι.range ∧ ∀ x, x⁻¹ * δ * theta Δ x = δ ↔ x ∈ ι.range ∨ negU Δ * x ∈ ι.range

def ClassG : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K) (d m : EL Δ τ), Δ ≠ 0 → IsDat 1 d m → ∀ δ : U3 Δ, HasTau δ τ →
    ∃ (c t : Kˣ), ∃ ι P, Models (c : K) d ((t : K) • m) δ ι P

def ConjG : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K) (d m : EL Δ τ), Δ ≠ 0 → IsDat 1 d m → ∀ (c c' t t' : Kˣ) δ δ' ι ι' P P',
    Models (c : K) d ((t : K) • m) δ ι P → Models (c' : K) d ((t' : K) • m) δ' ι' P' →
    ((∃ x, δ' = x⁻¹ * δ * theta Δ x) ↔ IsSquare (c' / c) ∧ t' / t ∈ NE τ)

def ExG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (τ c : F) (d m : EL Δ τ), IsDat c d m → PosF c m → D.Ev (c * (2 - τ)) → ∃ δ ι P, Models c d m δ ι P

def ModelMap : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (Δ τ c : K) (d m : EL Δ τ), IsDat c d m →
    IsDat (f c) (elmap f d) (elmap f m) ∧ ∀ δ ι P, Models c d m δ ι P → ∀ δ' : U3 (f Δ),
      (δ' : Matrix (Fin 3) (Fin 3) _) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (lmap f Δ) →
      ∃ ι' P', Models (f c) (elmap f d) (elmap f m) δ' ι' P' ∧ ∀ (z : (Etau K τ)ˣ) (z' : (Etau K' (f τ))ˣ),
        (z' : Etau K' (f τ)) = emap f τ z → (ι' z' : Matrix (Fin 3) (Fin 3) _) = (ι z : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (lmap f Δ)

def GqG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaG ι → ∀ θ : GA Δ →* GA Δ, (∀ g v, (θ g).1 v = theta _ (g.1 v)) → ∀ t, D.Cone t →
    ∀ (τ c : F) (d m : EL Δ τ) δ i P, IsCM τ → IsDat c d m → Models c d m δ i P →
    gqOn (ι.comp i) (scalE τ) D.UG (fun y => D.FG t (y.out⁻¹ * ι δ * θ y.out)) =
      (∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (one (D.admitted t τ) * (ms τ * D.nL c d m))

def GenPl : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (τ c : F) (d m : EL Δ τ), IsDat c d m →
    ∀ᶠ v : Pl F in Filter.cofinite, ∀ t : (Kv v)ˣ,
      lcount (Ov v) (cv v c) (elmap (cv v) d) ((t : Kv v) • elmap (cv v) m) = one (t ∈ NE (cv v τ))

def NormD : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ x : F, TPos x → ∃ g : DX Δ, (mt g).det = algebraMap F _ x

def WeakD : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaD ι → ∀ g : DA Δ,
    ∃ γ, ∃ u ∈ D.U2, D.Off (ι γ * g * u)

def SumT : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (τ c : F) (d m : EL Δ τ), IsCM τ → D.Spl τ → IsDat c d m →
    {t : Fˣ ⧸ NE τ | TPos (t.out : F) ∧ D.nL c d ((t.out : F) • m) ≠ 0}.Finite ∧
    ∑ᶠ t : Fˣ ⧸ NE τ, one (TPos (t.out : F)) * D.nL c d ((t.out : F) • m) =
      1 / 2 * ((∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), stabSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) +
        ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m))

def BasePt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ e : ℝ, ∀ τ : F, IsCM τ → D.Spl τ → (∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) →
    ∃ d m : EL Δ τ, IsDat 1 d m ∧ PosF 1 m ∧ ∀ c : F, TPos c → D.Ev (c * (2 - τ)) →
      (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) = e * D.nK τ

def DatEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ τ : F, IsCM τ → (∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) → ∃ d m : EL Δ τ, IsDat 1 d m ∧ PosF 1 m

def PosLaw : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (τ : F) (d m : EL Δ τ), PosF 1 m → ∀ c t : F, (TPos c → TPos t → PosF c (t • m)) ∧
    ∀ δ ι P, Models c d (t • m) δ ι P → TPos c ∧ TPos t

def ClassRep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaD ι → ∃ Y : Finset (DA Δ), (∀ y ∈ Y, D.Off y) ∧
    ∀ g : DA Δ, ∃ γ, ∃ s ∈ SA Δ, ∃ y ∈ Y, ∃ u ∈ D.U2, g = ι γ * s * y * u

def QuaternionStableSideTraceIdentity : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ x₀, D.Off x₀ → ∃ (n : ℕ) (x : Fin (n + 1) → DA Δ) (c : ℝ), x 0 = x₀ ∧
    (∀ i, D.Off (x i)) ∧ 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Fin (n + 1) → Base (SU Δ) (SA Δ) V),
    (∀ i, D.IsBS ch (x i) (B i)) → ∀ t, D.Cone t →
    ∑ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R (D.FSx t (x i))) = c * D.sumS ch t

def TFId0 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ x₀, D.Off x₀ → ∃ (n : ℕ) (x : Fin (n + 1) → DA Δ) (a b : ℝ), x 0 = x₀ ∧
    (∀ i, D.Off (x i)) ∧ 0 < a ∧
    ∀ (VG VS VK : Type) [AddCommGroup VG] [Module ℂ VG] [FiniteDimensional ℂ VG] [AddCommGroup VS] [Module ℂ VS]
      [FiniteDimensional ℂ VS] [AddCommGroup VK] [Module ℂ VK] [FiniteDimensional ℂ VK] (ch : F → ℂ)
      (BG : Base (U3 Δ) (GA Δ) VG) (s : BG.Tw) (BS : Fin (n + 1) → Base (SU Δ) (SA Δ) VS) (BK : Base (DX Δ) (DA Δ) VK),
    D.IsBG ch BG s → (∀ i, D.IsBS ch (x i) (BS i)) → D.IsBK ch BK → ∀ t, D.Cone t →
    LinearMap.trace ℂ BG.Forms (s.R (D.FG t)) =
      a * ∑ i, LinearMap.trace ℂ (BS i).Forms ((Base.Tw.one (BS i)).R (D.FSx t (x i))) +
      b * LinearMap.trace ℂ BK.Forms ((Base.Tw.one BK).R (D.FK t))

end UpperTheory.V.Z.Sym.Glob
end
end
