import Formalism.LocalToGlobal.UnitaryNorms.CharExHost

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

section Gen

variable (L : Type) [Field L] [NumberField L]

theorem mulSupport_ord_finite (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (x : Ideles L) :
    (Function.mulSupport fun v => c v ^ ordAt L v x).Finite := by
  refine (Filter.eventually_cofinite.mp (ordAt_eventually L x)).subset fun v hv h0 => hv ?_
  show c v ^ ordAt L v x = 1
  rw [h0, zpow_zero]

def unrQ (c : HeightOneSpectrum (𝓞 L) → ℂˣ) : Ideles L →* ℂˣ where
  toFun x := ∏ᶠ v, c v ^ ordAt L v x
  map_one' := by simp only [ordAt_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [ordAt_mul, zpow_add]
    exact finprod_mul_distrib (mulSupport_ord_finite L c x) (mulSupport_ord_finite L c y)

variable {L}



open Classical in

def InfChar {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Prop :=
  ∃ Φ : Ideles L →* ℂˣ, Continuous Φ ∧ (∀ x, ‖((Φ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ v x, Φ (localIdele L v x) = 1) ∧
    (∀ k : Lˣ, ((Φ (diagUnits L k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧
    ∀ (S : Finset (InfinitePlace L)) (k : Lˣ), ((Φ (∏ w ∈ S, infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
      ∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (φ i) ∈ S), (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i

end Gen

variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

open Classical in

def EtaInfCheck : Prop := ∀ (w : InfinitePlace H.F) (k : H.Fˣ),
  (∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (embPsi H i) ∈ aboveInf (L := H.E) H.F w),
    (embPsi H i ((upF H.F k : H.Eˣ) : H.E) / ((‖embPsi H i ((upF H.F k : H.Eˣ) : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) =
    ((etaInf H.F w k : ℂˣ) : ℂ)

end CharEx

end Formalism.L2.Host
