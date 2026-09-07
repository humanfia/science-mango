import Family8Grounding.Family8Family7ActivePatternOccurrenceWeightV1
import Family8Grounding.Family8Family7PatternFirstEqualShareFiberMassLiftV2
import Family8Grounding.Family8ShadingAwareProjectedPhysicalLowerBucketV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7ActivePatternLowerBucketFiberMassConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7ActivePatternOccurrenceWeightV1
open Family8Family7ActivePatternOccurrenceWeightV1.ActivePatternOccurrenceData
open Family8Family7PatternFirstEqualShareFiberMassLiftV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u

/-!
# Lower-bucket pattern weights lift to literal 3D shading mass

When the physical pattern is definitionally the quantitative lower-fibre
bucket, no pointwise fibre-floor callback is needed.  Exact-pattern
propagation supplies active membership throughout each event, and lower
bucket membership itself supplies the fibre inequality consumed by the
equal-share Tonelli lift.
-/

theorem fibreFloor_mul_activePatternOccurrenceWeight_le_ballShadingMass
    {iota : Type u} [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set (Real × Real)) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (fibreFloor : ENNReal)
    (N : CanonicalNormNonconcentrationData iota)
    (localShading : FiniteProjectedShading (Real × Real) iota)
    (source : Set (Real × Real))
    (P : ActivePatternOccurrenceData N
      (shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI fibreFloor)
      localShading source)
    (ball : Finset iota) :
    fibreFloor * (∑ i ∈ ball, P.occurrenceWeight i) ≤
      ∑ i ∈ ball,
        volume ((shadingWindowRestriction Y f hf X hX I hI).carrier i) := by
  classical
  let labels : Finset P.PatternIndex := Finset.univ
  let event : P.PatternIndex → Set (Real × Real) := fun p =>
    activePatternEvent
      (shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI fibreFloor)
      source p.1
  let fiber : P.PatternIndex → Finset iota := P.occurrenceFiber
  have hfiber : ∀ p, p ∈ labels → (fiber p).Nonempty := by
    intro p _hp
    exact P.occurrenceFiber_nonempty p
  have hmeasurable : ∀ p, p ∈ labels → MeasurableSet (event p) := by
    intro p _hp
    exact P.measurableSet_activePatternEvent p.1
  have hdisjoint : Set.PairwiseDisjoint (labels : Set P.PatternIndex) event := by
    simpa only [labels, event, Finset.coe_univ] using
      P.patternEvents_pairwiseDisjoint
  have hfloor : ∀ p, p ∈ labels → ∀ i, i ∈ fiber p → ∀ q,
      q ∈ event p →
        fibreFloor ≤ shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i q := by
    intro p _hp i hi q hq
    apply shadingFiberMass_lower_of_mem_activeAtPoint
      Y active f hf X hX I hI fibreFloor
    exact P.occurrence_mem_physicalAt_of_mem_event p hi hq
  have hlift := fibreFloor_mul_equalShareWeight_le_ballShadingMass
    labels event fiber hfiber hmeasurable hdisjoint
      (shadingWindowRestriction Y f hf X hX I hI) f hf fibreFloor
        hfloor ball
  have hweight : ∀ i,
      patternFirstEqualShareTubeWeight labels event fiber i =
        P.occurrenceWeight i := by
    intro i
    rfl
  simpa only [hweight] using hlift

#print axioms
  fibreFloor_mul_activePatternOccurrenceWeight_le_ballShadingMass

end

end Family8Family7ActivePatternLowerBucketFiberMassConnectorV1
