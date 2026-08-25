import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainSelectedIdentityDirectNormalizerProducerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchySelectedSourceDirectTerminalWZConsumerV1

noncomputable section

/-!
# Direct normalizer for the identity all-radius cover

The canonical identity cover never merges parent indices.  Consequently its
upper endpoint fiber and its fiber at every intermediate radius are literally
the same indexed convex family.  The actual reverse-normalizer ratio is
therefore `x / x`, and is at most one even in the zero case.

This gives a direct arbitrary-radius Sticky endpoint.  It does not use
selected ancestor coordinates, hierarchy sibling rigidity, collision-cell
geometry, or random-motion/WZ certificates.  The local interval geometry and
the discrete endpoint bounds remain the independent analytic inputs required
by the existing arbitrary-radius theorem.
-/

universe u

variable {delta : NNReal} {depth : Nat}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  (fine : UniformTubeFamily delta iota)
  (T : FiniteScaleSequence delta depth)

/-! ## Generic identity-cover loss -/

/-- For the identity cover, one literal reverse-fiber ratio is at most one.
The active branch reduces definitionally to `x / x`; `div_self_le_one` also
covers `x = 0`.  The inactive branch is zero. -/
theorem actualReverseFiberMassRatio_identity_le_one
    (m : Fin depth) (rho : NNReal)
    (hTauRho : T.tau m <= rho) (hRhoTheta : rho <= T.theta m)
    (k : Fin (Fintype.card iota)) :
    actualReverseFiberMassRatio (identityRadiusCoherentCover fine) T
      m rho hTauRho hRhoTheta k <= 1 := by
  unfold actualReverseFiberMassRatio
  split_ifs
  · have hfiber :
        (upperEndpointCover (identityRadiusCoherentCover fine) T m).fiberFamily
            ((rhoToUpperCover (identityRadiusCoherentCover fine) T m rho
              hTauRho hRhoTheta).parent k) =
          (lowerScaleCover (identityRadiusCoherentCover fine) T m rho
            hTauRho hRhoTheta).fiberFamily k := by
        rfl
    rw [hfiber]
    let x : ENNReal :=
      familyVolume
        ((lowerScaleCover (identityRadiusCoherentCover fine) T m rho
          hTauRho hRhoTheta).fiberFamily k)
    change x / x <= 1
    by_cases hx : x = 0
    · simp [hx]
    · have hxtop : x ≠ ⊤ := by
        dsimp only [x]
        exact familyVolume_ne_top
          ((lowerScaleCover (identityRadiusCoherentCover fine) T m rho
            hTauRho hRhoTheta).fiberFamily k)
      exact (ENNReal.div_le_iff hx hxtop).2 (by simp)
  · exact (show (0 : ENNReal) <= 1 from bot_le)

/-- The exact worst reverse normalizer of every identity all-radius cover is
bounded by one, uniformly in the family and in the finite scale sequence. -/
theorem actualReverseParentNormalizerLoss_identity_le_one :
    actualReverseParentNormalizerLoss (identityRadiusCoherentCover fine) T <=
      1 := by
  unfold actualReverseParentNormalizerLoss
  refine iSup_le fun m => ?_
  refine iSup_le fun rho => ?_
  refine iSup_le fun hTauRho => ?_
  refine iSup_le fun hRhoTheta => ?_
  refine iSup_le fun k => ?_
  exact actualReverseFiberMassRatio_identity_le_one fine T
    m rho hTauRho hRhoTheta k

/-! ## Direct arbitrary-radius endpoint -/

/-- The arbitrary-radius theorem for an identity cover has no reverse
normalizer loss: the output Frostman constant is exactly the supplied
endpoint constant rather than an additional hierarchy-dependent multiple. -/
theorem isStickyAtEveryScale_of_identityDirectNormalizer
    {epsilon : Real}
    (hdepth : 0 < depth) (hdelta : 0 < delta)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry (identityRadiusCoherentCover fine) T
      epsilon massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds (identityRadiusCoherentCover fine) T
      epsilon frostmanError katzTaoError) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
      frostmanError (katzTaoLoss * katzTaoError) := by
  have hsticky :=
    isStickyAtEveryScale_of_actualReverseParentNormalizerLoss
      (C := identityRadiusCoherentCover fine) (S := T)
      hdepth hdelta D B
  exact hsticky.mono
    (by
      calc
        actualReverseParentNormalizerLoss
              (identityRadiusCoherentCover fine) T * frostmanError <=
            1 * frostmanError := by
              gcongr
              exact actualReverseParentNormalizerLoss_identity_le_one fine T
        _ = frostmanError := one_mul frostmanError)
    le_rfl

/-! ## Genuine selected-hierarchy specialization -/

variable {nominalRadius : Nat -> NNReal} {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  (R : SelectedTerminalSourceChartBucketGeometry (H := H))

/-- Selected level zero is merely a specialization of the generic identity
cover bound.  In particular no ancestor-injectivity assumption is present. -/
theorem selectedIdentity_actualReverseParentNormalizerLoss_le_one
    (S : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth) :
    actualReverseParentNormalizerLoss (selectedIdentityCoherentCover R) S <=
      1 :=
  actualReverseParentNormalizerLoss_identity_le_one
    ((selectedHierarchy R).effectiveFamily 0) S

/-- Direct selected arbitrary-radius Sticky endpoint.  Its only inputs are
the scalar positivity needed by the generic analytic theorem, the finite
scale sequence, local interval geometry, and discrete endpoint estimates.
It has no `SelectedAncestorInjective`, random-motion, WZ, collision-cell, or
cover-to-hierarchy coordinate input. -/
theorem isStickyAtEveryScale_of_selectedIdentityDirectNormalizer
    {epsilon : Real}
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    (S : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry (selectedIdentityCoherentCover R) S
      epsilon massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds (selectedIdentityCoherentCover R) S
      epsilon frostmanError katzTaoError) :
    (selectedIdentityCoherentCover R).base.IsStickyAtEveryScale
      frostmanError (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_identityDirectNormalizer
    ((selectedHierarchy R).effectiveFamily 0) S hdepth
      (selectedHierarchy_effectiveRadius_zero_pos (S := R) hdelta) D B

#print axioms actualReverseFiberMassRatio_identity_le_one
#print axioms actualReverseParentNormalizerLoss_identity_le_one
#print axioms isStickyAtEveryScale_of_identityDirectNormalizer
#print axioms selectedIdentity_actualReverseParentNormalizerLoss_le_one
#print axioms isStickyAtEveryScale_of_selectedIdentityDirectNormalizer

end
end FamilyStickyScaleChainSelectedIdentityDirectNormalizerProducerV1
