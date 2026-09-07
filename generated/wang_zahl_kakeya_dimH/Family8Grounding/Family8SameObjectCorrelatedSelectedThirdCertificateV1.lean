import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
import Family8Grounding.Family8SectionEightBetaGammaLosslessBridgeV2
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1
import Mathlib.Tactic

/-!
# Same-object correlated selected-third certificate

This is an interface record, not a producer or a closure theorem.  Its
parameters freeze one literal scale cover `U`, shading `Y`, factorization,
frozen assembly `A`, and card-scale mass `X`.  The record retains the source
Katz--Tao coefficient only in its correlated form with `X`; it never exports
the unsupported standalone power bound used by the old G1/G2 gates.

All analytic and selection obligations remain explicit fields.  The lemmas
below are only monotonicity/reassociation and the already verified Section-8
card-scale algebra.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SameObjectCorrelatedSelectedThirdCertificateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8SectionEightBetaGammaLosslessBridgeV2
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta scale rho : NNReal}
  {iota kappa : Type}
  [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]
  {fine : UniformTubeFamily scale iota}
  {G : ConvexFamily kappa}

/-- A producer-facing certificate retaining all data needed to use a selected
third factor without separating its Katz--Tao coefficient from the matching
card-scale mass.  Dependence on `U`, `Y`, `Q`, and `A` makes object identity a
type-level fact rather than an equality reconstructed downstream. -/
structure SameObjectCorrelatedSelectedThirdCertificate
    (U : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal)
    (outputEta : Real) where
  actualThirdAverage : ENNReal
  actualThirdAverage_eq :
    actualThirdAverage = A.frozenCoarse.averageMultiplicity
  actualThirdAverage_le_coefficient :
    actualThirdAverage <=
      selectorLoss * (CKT * volume (unitBallBody : Set Space))
  activeCoarseCard_eq : Fintype.card kappa = U.coarseCard
  activeCoarseCard_pos : 0 < Fintype.card kappa
  cardScaleMass_eq :
    X = (Fintype.card kappa : ENNReal) * (rho : ENNReal) ^ (2 : Nat)
  coefficient_mul_volume_le_cardScale :
    CKT * volume (unitBallBody : Set Space) <=
      128 * (delta : ENNReal) ^ (-outputEta) * X
  fourth_cardScaleMass_le_one :
    (rho : ENNReal) ^ (4 : Nat) * X <= 1
  sourceMass_retained :
    sourceMass <= massRetentionLoss * shadingMassOn Y U.activeFine
  sourceDensity_retained :
    densityRetentionLoss * sourceDensity <= Y.shadingDensity

namespace SameObjectCorrelatedSelectedThirdCertificate

/-- Keep the source coefficient correlated with `X` when bounding the actual
selected-third average. -/
theorem actualThirdAverage_le_correlatedCardScale
    {U : StickyScaleCover fine rho}
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal}
    {outputEta : Real}
    (Z : SameObjectCorrelatedSelectedThirdCertificate (delta := delta) U Y Q A
      X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta) :
    Z.actualThirdAverage <=
      selectorLoss *
        (128 * (delta : ENNReal) ^ (-outputEta) * X) := by
  exact Z.actualThirdAverage_le_coefficient.trans
    (mul_le_mul' le_rfl Z.coefficient_mul_volume_le_cardScale)

/-- Pure full-product consumer.  The correlated `X` term is consumed only
inside the supplied product budget; no standalone bound for `CKT` is
derived. -/
theorem prefix_mul_actualThirdAverage_le_of_correlatedBudget
    {U : StickyScaleCover fine rho}
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss outerPrefix target : ENNReal}
    {outputEta : Real}
    (Z : SameObjectCorrelatedSelectedThirdCertificate (delta := delta) U Y Q A
      X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta)
    (hbudget :
      outerPrefix *
          (selectorLoss *
            (128 * (delta : ENNReal) ^ (-outputEta) * X)) <= target) :
    outerPrefix * Z.actualThirdAverage <= target := by
  exact (mul_le_mul' le_rfl
    Z.actualThirdAverage_le_correlatedCardScale).trans hbudget

/-- The certificate's fourth-card-scale field supplies the existing
lossless beta-to-gamma Section-8 comparison for the exact coarse index type
of `A`.  This has no `gamma > 2/3` hypothesis. -/
theorem sectionEightFactor_beta_le_gamma
    {U : StickyScaleCover fine rho}
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal}
    {outputEta beta gamma : Real}
    (Z : SameObjectCorrelatedSelectedThirdCertificate (delta := delta) U Y Q A
      X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta)
    (hrho : 0 < rho) (hbetaGamma : beta <= gamma) :
    sectionEightScaleCountFrostmanFactor
        rho 1 (Fintype.card kappa) beta <=
      sectionEightScaleCountFrostmanFactor
        rho 1 (Fintype.card kappa) gamma := by
  apply sectionEight_to_one_beta_le_gamma_of_fourth_cardScale
    hrho Z.activeCoarseCard_pos hbetaGamma
  have hmass :
      ((rho : ENNReal) ^ (2 : Nat)) *
          (Fintype.card kappa : ENNReal) = X := by
    rw [mul_comm, ← Z.cardScaleMass_eq]
  simpa only [hmass] using Z.fourth_cardScaleMass_le_one

#print axioms SameObjectCorrelatedSelectedThirdCertificate
#print axioms actualThirdAverage_le_correlatedCardScale
#print axioms prefix_mul_actualThirdAverage_le_of_correlatedBudget
#print axioms sectionEightFactor_beta_le_gamma

end SameObjectCorrelatedSelectedThirdCertificate
end
end Family8SameObjectCorrelatedSelectedThirdCertificateV1
