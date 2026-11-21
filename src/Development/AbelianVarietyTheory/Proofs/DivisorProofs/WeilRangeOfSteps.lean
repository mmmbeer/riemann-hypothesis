import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WeilRangeOfAll

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWWeil

open GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

abbrev unipN (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E) : Subgroup (UA σ J₂) :=
  unipOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype

abbrev ratN (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E) : Subgroup (unipN σ J₂) :=
  (ratU σ J₂).comap (unipN σ J₂).subtype

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type}

end GlobalTheory.SWWeil

namespace GlobalTheory.SWWeil
open GlobalTheory.SWLit GlobalTheory.SWACase

end GlobalTheory.SWWeil
