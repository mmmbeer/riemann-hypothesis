import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes

noncomputable section

namespace GlobalTheory.HeightCounting.ReadingModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain

def ofFrame {D : D7} (F : TwFrame D) : TwFrameC D :=
  ⟨F.K0, F.eO0, F.j0, F.Lw, F.eO, F.eOk, F.iCq, F.S0x⟩

def toFrame {D : D7} (F : TwFrameC D) : TwFrame D :=
  ⟨F.K0, F.eO0, F.j0, F.Lw, F.eO, F.eOk, F.iCq, F.S0x⟩





section
variable {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd}



variable (hE : IsEmpty D.nd.Loc) (F : TwF T) (S : RingSpec D cf b0 b1 Sx T)
  (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
  (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex)

def withRings : D7 := setTw D (T.ntw hE F (TwL.empty T)) ex h0 th S.br S.br_ind

def chiData : NChiData (withRings hE F S ex h0 th) :=
  ⟨S.mu0H, S.etaH, S.delH, fun a => hE.elim a, fun _ a => PEmpty.elim a, S.embO⟩


def frameC : TwFrameC (withRings hE F S ex h0 th) :=
  ⟨S.K0, S.eO0, S.j0, S.Lw, S.eO, S.eOk, S.iCq, fun _ => Sx⟩


end

end GlobalTheory.HeightCounting.ReadingModel

end
