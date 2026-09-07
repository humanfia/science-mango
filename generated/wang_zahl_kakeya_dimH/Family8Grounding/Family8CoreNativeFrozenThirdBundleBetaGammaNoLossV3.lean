import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8SectionEightBetaGammaLosslessBridgeV2

/-!
# Lossless beta-to-gamma transport of a same-object frozen third bundle, V3

V1 and V2 are failed drafts and are not imported.  The assembly, selected
set, count, average, and loss are unchanged; only the exponent is transported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CoreNativeFrozenThirdBundleBetaGammaNoLossV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8CoreNativeFrozenThirdBundleV1
open Family8SectionEightBetaGammaLosslessBridgeV2
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

variable {iota kappa : Type} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {G : ConvexFamily kappa}

/-- Transport a literal frozen third bundle from beta to gamma without
changing any of its data or paying any additional loss.  The returned
bundle's standard projections are therefore definitionally the required
`thirdCount`, `thirdAverage`, `thirdLoss`, and gamma-valued `hThird` fields. -/
def CoreNativeFrozenThirdBundle.toGammaOfFourthCardScale
    {Q : ConvexFactorization F G} {Y : Shading F}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {middleScale : NNReal} {loss : ENNReal} {beta gamma : Real}
    (X : CoreNativeFrozenThirdBundle Q Y A middleScale loss beta)
    (hmiddle : 0 < middleScale) (hbetaGamma : beta <= gamma)
    (hfourth :
      ((middleScale : ENNReal) ^ (4 : Nat)) *
          (((middleScale : ENNReal) ^ (2 : Nat)) *
            (Fintype.card kappa : ENNReal)) <= 1) :
    CoreNativeFrozenThirdBundle Q Y A middleScale loss gamma := by
  have hselectedCard : 0 < X.selected.card :=
    Finset.card_pos.mpr X.selected_nonempty
  have hselectedLe : X.selected.card <= Fintype.card kappa := by
    simpa only [Finset.card_univ] using Finset.card_le_univ X.selected
  have hcard : 0 < Fintype.card kappa := lt_of_lt_of_le hselectedCard hselectedLe
  refine
    { selected := X.selected
      selected_nonempty := X.selected_nonempty
      bound := ?_ }
  calc
    A.frozenCoarse.averageMultiplicity <=
        loss * sectionEightScaleCountFrostmanFactor
          middleScale 1 (Fintype.card kappa) beta := X.bound
    _ <= loss * sectionEightScaleCountFrostmanFactor
          middleScale 1 (Fintype.card kappa) gamma :=
      mul_le_mul' le_rfl
        (sectionEight_to_one_beta_le_gamma_of_fourth_cardScale
          hmiddle hcard hbetaGamma hfourth)

#print axioms CoreNativeFrozenThirdBundle.toGammaOfFourthCardScale

end
end Family8CoreNativeFrozenThirdBundleBetaGammaNoLossV3
