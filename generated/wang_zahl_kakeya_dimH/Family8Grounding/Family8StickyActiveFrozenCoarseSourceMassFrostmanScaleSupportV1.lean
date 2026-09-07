import Family8Grounding.Family8FrozenCoarseB2FrostmanActualDatumV1
import Family8Grounding.Family8FrozenCoarseSameDataDensityBudgetV2
import Family8Grounding.Family8FrozenCoarseB2CardScaleBaseBudgetV6
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveFrozenCoarseSourceMassFrostmanScaleSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8FrozenCoarseSameDataDensityBudgetV2
open Family8FrozenCoarseB2CardScaleBaseBudgetV6
open Family8StickyActiveRestrictedCoarseKatzTaoV1

noncomputable section

/-!
# Same-data frozen Frostman endpoint from scale and B2 support

Unlike the admissibility-specialized connector, this theorem applies to an
arbitrary existing sticky cover and its literal `P/A`.  The raw coarse family
only needs the scale and the actual radius-two support consumed by B2
normalization.  Thus a tau-active interval cover can use support inherited
from its original global cover without manufacturing an inadmissible
intermediate datum.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_normalized_activeFrozenCoarse_of_sourceMass_scaleSupport
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho)
    (P : CoarseTubePartition
      (activeFineRestrictedFamily S)
      (activeFineRestrictedScaleCover S).coarse)
    (Y : Shading (activeFineRestrictedFamily S).bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    (hrhoPos : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hB2 : forall k,
      ((activeFineRestrictedScaleCover S).coarse.tubes k).carrier ⊆
        Metric.closedBall (0 : Space) 2)
    {conflictThreshold : Nat}
    (hconflict : forall k,
      (normalizedConflictIndices (frozenCoarseActualDatum P Y A) k).card <=
        conflictThreshold)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C)
    (hdelta0 : rho / 8 <= delta0)
    {sourceFloor baseFloor XUpper : ENNReal}
    (hsource0 :
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass ≠ 0)
    (hsourceLower : sourceFloor <=
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass)
    (hXUpper : (activeCoarseCardScaleMass S : ENNReal) <= XUpper)
    (hdensityScalar :
      ((((rho / 8 : NNReal) : ENNReal) ^ eta *
            ((conflictThreshold + 1 : Nat) : ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((P.branchingLoss * P.branching : Nat) : ENNReal)) *
            (8 * XUpper)) <= sourceFloor)
    (hbaseLower :
      baseFloor <= (activeCoarseCardScaleMass S : ENNReal))
    (hbaseScalar :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          (baseFloor / 128)) :
    exists selected :
        Finset (Fin (activeFineRestrictedScaleCover S).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        ((conflictThreshold + 1 : Nat) : ENNReal) *
          frostmanMultiplicityRHS (rho / 8)
            (restrictActualTubeDatum
              (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
                (frozenCoarseActualDatum P Y A))
              selected).actualFamilyVolume epsilon beta := by
  classical
  letI : Nonempty
      (Fin (activeFineRestrictedScaleCover S).coarseCard) := by
    obtain ⟨k, _hk⟩ := P.coarse_nonempty
    exact ⟨k⟩
  have hdensityBudget :
      ((rho / 8 : NNReal) : ENNReal) ^ eta <=
        (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
          (frozenCoarseActualDatum P Y A)).shading.shadingDensity /
            ((conflictThreshold + 1 : Nat) : ENNReal) :=
    activeFrozenCoarse_normalizedDensityBudget_of_sourceMass
      S P Y A hrhoPos hrhoHalf (by omega) hsource0 hsourceLower hXUpper
        hdensityScalar
  have hbaseBudget :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
            ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) :=
    activeFrozenCoarse_baseBudget_of_cardScaleMassLower
      S hbaseLower hbaseScalar
  exact exists_normalized_frozenCoarse_averageMultiplicity_le_frostmanRHS
    hF P Y A hrhoPos hrhoHalf hB2 hconflict
      (activeFineRestrictedScaleCover_coarse_isKatzTao S hKT)
      hdelta0 hdensityBudget hbaseBudget

#print axioms
  exists_normalized_activeFrozenCoarse_of_sourceMass_scaleSupport

end
end Family8StickyActiveFrozenCoarseSourceMassFrostmanScaleSupportV1
