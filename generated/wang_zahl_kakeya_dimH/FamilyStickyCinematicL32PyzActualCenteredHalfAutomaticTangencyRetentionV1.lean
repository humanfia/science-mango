import FamilyStickyCinematicL32PyzActualCenteredHalfTangencyCeilingCleanV1
import FamilyStickyCinematicL32ActualProjectedCenteredHalfStoredCriticalContainmentV1
import FamilyStickyCinematicL32FiniteNormCriticalBallV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32PyzActualCenteredHalfAutomaticTangencyRetentionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfStoredCriticalContainmentV1
open FamilyStickyCinematicL32PyzActualCenteredHalfTangencyCeilingCleanV1

noncomputable section

/-!
# Exact tangency retention with the automatic `36 * t` ceiling

The stored centered-half critical ball is literally contained in the
retained family.  The actual localized geometry supplies the full
`36 * globalScale` comparison ceiling, so the weighted-cardinality estimate
has no free `hfull` premise.
-/

theorem centeredHalfLocalized_weighted_card_le_retained_thirtySix
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (hparameter : ∀ z, z ∈ Icc outerA outerB → |z| ≤ 1)
    (hfun : ∀ z, z ∈ Icc outerA outerB → |f z| ≤ 2)
    (hfun1 : ∀ z, z ∈ Icc outerA outerB → |f1 z| ≤ 2)
    (globalScale : Real) (globalCenter : Tube radius)
    (exponent threshold : Real) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty)
    (hradius : 0 < radius)
    (hradiusCeiling : (radius : Real) ≤ 36 * globalScale)
    (hexponent : 0 ≤ exponent)
    (hscaleUpper :
      actualProjectedCenteredHalfLocalizedTangencyScale fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) exponent q ≤ threshold) :
    let localized := finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)
    let tangencyScale := finiteCriticalMaximizerScale localized
      (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
        hOuter hf hf1 (physical.activeAtPoint q))
      (radius : Real) (36 * globalScale) exponent hlocalized
    let retained := actualProjectedCenteredHalfRetainedTubeFamily fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      (36 * globalScale) exponent threshold q
    (localized.card : Real) * (36 * globalScale) ^ (-exponent) ≤
      (retained.card : Real) * tangencyScale ^ (-exponent) := by
  dsimp only
  let localized : Finset (Tube radius) :=
    finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)
  let distance : Tube radius → Tube radius → Real :=
    actualProjectedCenteredHalfTangencyDistance f f1 f2
      outerA outerB hOuter hf hf1 (physical.activeAtPoint q)
  let center := finiteCriticalMaximizerCenter localized distance
    (radius : Real) (36 * globalScale) exponent hlocalized
  have hcenterMem : center ∈ localized :=
    finiteCriticalMaximizerCenter_mem localized distance
      (radius : Real) (36 * globalScale) exponent hlocalized
  have hweighted := finiteNormCriticalBall_weighted_card_retention
    localized distance hlocalized (testCenter := center)
      (fun T _hT => by
        dsimp only [distance]
        rw [actualProjectedCenteredHalfTangencyDistance_self]
        exact_mod_cast hradius.le)
      (by exact_mod_cast hradius) hradiusCeiling hexponent hcenterMem
      (by
        dsimp only [localized, distance, center] at hcenterMem ⊢
        exact actualProjectedCenteredHalfLocalizedFamily_full_tangencyCeiling
          fine physical.ambient (physical.activeAtPoint q) f f1 f2
          outerA outerB hOuter hf hf1 hparameter hfun hfun1 globalScale
          globalCenter _ hcenterMem)
  have hcard :
      (finiteNormCriticalBall localized distance (radius : Real)
        (36 * globalScale) exponent hlocalized).card ≤
      (actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) exponent threshold q).card := by
    apply Finset.card_le_card
    simpa only [localized, distance] using
      (centeredHalfTangencyCriticalBall_subset_retained fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) exponent threshold q hlocalized hscaleUpper)
  have hradiusNonneg : (0 : Real) ≤ (radius : Real) := by
    exact_mod_cast hradius.le
  have hscaleNonneg : 0 ≤ finiteCriticalMaximizerScale localized distance
      (radius : Real) (36 * globalScale) exponent hlocalized :=
    hradiusNonneg.trans
      (finiteCriticalMaximizerScale_bounds localized distance hlocalized
        hradiusCeiling).1
  have hpow : 0 ≤ finiteCriticalMaximizerScale localized distance
      (radius : Real) (36 * globalScale) exponent hlocalized ^ (-exponent) :=
    Real.rpow_nonneg hscaleNonneg _
  exact hweighted.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpow)

end
end FamilyStickyCinematicL32PyzActualCenteredHalfAutomaticTangencyRetentionV1
