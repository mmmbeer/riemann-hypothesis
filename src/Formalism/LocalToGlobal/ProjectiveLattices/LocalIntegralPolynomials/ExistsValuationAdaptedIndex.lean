import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import ReciprocityTheory.SemistableReduction.AlgAll

section
noncomputable section

namespace Formalism.L2.Pj.LocAlg

open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

def GenAt (K : Type) {Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ} (jc : Fin (N + 1))
    (x : Fin N → Ω) (V : ValuationSubring (OmS Ω D N)) : Prop :=
  ∃ ht : ∀ p, sImg jc x p ∈ V,
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω (OmS Ω D N))
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω (OmS Ω D N))) (algebraMap K Ω)
    letI : Algebra (IsLocalRing.ResidueField
        ((V.comap (algebraMap Ω (OmS Ω D N))).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
      ((algebraMap _ (IsLocalRing.ResidueField V)).comp
        (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω (OmS Ω D N)))))).toAlgebra
    AlgebraicIndependent
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω (OmS Ω D N))).comap (algebraMap K Ω)))
      (fun p => IsLocalRing.residue V ⟨sImg jc x p, ht p⟩)

def LocStructSt : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D N : ℕ) (jc : Fin (N + 1)) (x : Fin N → Ω),
    Algebra.trdeg K Ω = D →
    ∀ (Z : Type) [Fintype Z] (v : Z → Valuation (OmS Ω D N) (WithZero (Multiplicative ℤ))),
      (∀ ζ, GenAt K jc x (v ζ).valuationSubring) →
      (∀ ζ, ∃ a : OmS Ω D N,
        v ζ a = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      ∀ g : OmS Ω D N, (∀ ζ, v ζ g ≤ 1) →
      ∃ f d : MvPolynomial (TVar D N) Ω,
        (∀ ζ e, v ζ (algebraMap Ω (OmS Ω D N) (f.coeff e)) ≤ 1) ∧
        (∀ ζ e, v ζ (algebraMap Ω (OmS Ω D N) (d.coeff e)) ≤ 1) ∧
        (∀ ζ, v ζ (aeval (sImg jc x) d) = 1) ∧
        aeval (sImg jc x) f = aeval (sImg jc x) d * g

end Formalism.L2.Pj.LocAlg
end
end

section
noncomputable section

namespace Formalism.L2.Pj.LocAlg

open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

variable {Ω : Type} [Field Ω] {D N : ℕ}

def yv (jc : Fin (N + 1)) (x : Fin N → Ω) : Fin (N + 1) → Ω :=
  Fin.insertNth (α := fun _ => Ω) jc 1 x

theorem yv_self (jc : Fin (N + 1)) (x : Fin N → Ω) : yv jc x jc = 1 := by
  unfold yv
  exact Fin.insertNth_apply_same (α := fun _ => Ω) jc 1 x



theorem sImg_succAbove (jc : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    sImg jc x (i, jc.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) jc _ _ k


def tj (jc j0 : Fin (N + 1)) (x : Fin N → Ω) : SVar D N → OmS Ω D N :=
  Sum.elim (fun _ => sImg jc x (0, j0)) (fun p => sImg jc x (p.1, j0.succAbove p.2))

def qj (jc j0 : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) : MvPolynomial (SVar D N) Ω :=
  Fin.insertNth (α := fun _ => MvPolynomial (SVar D N) Ω) j0
    (if p.1 = 0 then X (Sum.inl ())
      else -∑ k, C (yv jc x (j0.succAbove k) / yv jc x j0) * X (Sum.inr (p.1, k)))
    (fun k => X (Sum.inr (p.1, k))) p.2

variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}


def intPoly (σ : Type) (W : Subring Ω) : Subring (MvPolynomial σ Ω) where
  carrier := {P | ∀ e, P.coeff e ∈ W}
  mul_mem' := by
    intro P Q hP hQ e
    classical
    rw [coeff_mul]
    exact sum_mem fun d _ => W.mul_mem (hP _) (hQ _)
  one_mem' := by
    intro e
    classical
    rw [coeff_one]
    split_ifs
    exacts [W.one_mem, W.zero_mem]
  add_mem' := by
    intro P Q hP hQ e
    rw [coeff_add]
    exact W.add_mem (hP e) (hQ e)
  zero_mem' := by
    intro e
    rw [coeff_zero]
    exact W.zero_mem
  neg_mem' := by
    intro P hP e
    rw [coeff_neg]
    exact W.neg_mem (hP e)

theorem C_mem_intPoly {σ : Type} {W : Subring Ω} {a : Ω} (ha : a ∈ W) : (C a : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_C]
  split_ifs
  exacts [ha, W.zero_mem]

theorem X_mem_intPoly {σ : Type} {W : Subring Ω} (s : σ) : (X s : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_X']
  split_ifs
  exacts [W.one_mem, W.zero_mem]



end Formalism.L2.Pj.LocAlg
end
end
