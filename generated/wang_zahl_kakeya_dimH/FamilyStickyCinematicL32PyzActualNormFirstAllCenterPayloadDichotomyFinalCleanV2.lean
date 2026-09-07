import FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
import FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
import FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
open FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Actual norm-first all-centre rich-payload dichotomy

The primitive extremal data produce all distinctness and coefficient-cap
facts.  The norm selector then retains the exact measurable partition, and
the two later dyadic selections are performed only in its positive cells.
The result is either an actual high-degree selected payload or a low-degree
payload in every positive cell.
-/

theorem exists_actualNormFirst_allCenterPayload_high_or_all_low
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    {Y : Shading S.family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      extremalEpsilon extremalSigma)
    (bucket : Int)
    (hbucket : ∀ i, i ∈ ambient →
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket)
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hsourcePos : 0 < volume
      ((actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand lower upper))
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity) :
    let physical := actualProjectedNormFirstSixteenthPhysicalShading
      S.family ambient physicalBase hphysicalBase f hfContinuous outerA outerB
    let normScale := actualProjectedAmbientNormScale S.family physical 16
      normExponent
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (radius : Real))
        (dyadicCeilBucket 16),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      let globalScale := dyadicCeilUpper normLabel
      volume (physical.multiplicityBand lower upper) /
          (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
            ENNReal) ≤ volume E_norm ∧
      0 < volume E_norm ∧ E_norm.Nonempty ∧ MeasurableSet E_norm ∧
      E_norm ⊆ physical.multiplicityBand lower upper ∧
      0 < globalScale ∧ (radius : Real) ≤ globalScale ∧
      (∀ x ∈ E_norm,
        globalScale / 2 < normScale x ∧ normScale x ≤ globalScale) ∧
      ∃ fallback : FiniteMetricMember
          (activeTubeImage S.family physical.ambient),
        let centers := finiteMetricCoverCenters
          (activeTubeImage S.family physical.ambient)
          projectedTubePairCoefficientDistance globalScale
          (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
        let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
          (fun i x ↦ x ∈ physical.carrier i)
          (activeTubeImage S.family physical.ambient) fallback
          (actualProjectedAmbientCriticalFamily S.family physical.ambient)
          projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
          globalScale
          (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
        let cell := fun center ↦ measurableLabelCell E_norm label center
        ∃ hcellData : ∀ center, center ∈ centers →
          MeasurableSet (cell center) ∧ cell center ⊆ E_norm ∧
          ∀ x, x ∈ cell center →
            let active := physical.activeAtPoint x
            let localFamily := actualProjectedAmbientCriticalFamily S.family
              physical.ambient active
            ∃ hlocalFamily : localFamily.Nonempty,
              let localBall := finiteNormCriticalBall localFamily
                projectedTubePairCoefficientDistance (radius : Real) 16
                normExponent hlocalFamily
              let localized := finiteIncidenceNormLocalizedFamilyValue
                (actualProjectedAmbientCriticalFamily S.family
                  physical.ambient)
                projectedTubePairCoefficientDistance globalScale center active
              localBall ⊆ localized ∧ localBall.card ≤ localized.card,
          volume E_norm = ∑ center ∈ centers, volume (cell center) ∧
          (∀ x ∈ E_norm, label x ∈ centers) ∧
          let hcellMeasurable := fun center hcenter ↦
            (hcellData center hcenter).1
          ((∃ center, ∃ hcenter : center ∈ centers,
              0 < volume (cell center) ∧
              ∃ payload : ActualPositiveCenterCanonicalPayload volume
                  (cell center) (hcellMeasurable center hcenter) S.family
                  physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
                  center tangencyExponent,
                24 * logCount ≤ pyzE2DegreeLower payload.finalLabel) ∨
            (∀ center, ∀ hcenter : center ∈ centers,
              0 < volume (cell center) →
              ∃ payload : ActualPositiveCenterCanonicalPayload volume
                  (cell center) (hcellMeasurable center hcenter) S.family
                  physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
                  center tangencyExponent,
                pyzE2DegreeLower payload.finalLabel < 24 * logCount)) := by
  dsimp only
  let physical := actualProjectedNormFirstSixteenthPhysicalShading S.family
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  obtain ⟨hambientPairwise, hbandPairwise, hactiveCap⟩ :=
    actualNormFirst_public_inputs_of_extremal_bucket S ambient hambient
      physicalBase hphysicalBase f hfContinuous outerA outerB G bucket hbucket
      hloss
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormNonempty,
      hnormMeasurable, hnormSubset, hglobalScale, hradiusGlobalScale,
      hnormBin, fallback, hpartition, hlabelRange, hcellData⟩ :=
    exists_actualProjectedNormFirst_allCenterCells volume S.family physical
      16 normExponent hradius hradiusSixteen hsourcePos hmultiplicity hlower
      hbandPairwise hactiveCap
  let normScale := actualProjectedAmbientNormScale S.family physical 16
    normExponent
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand lower upper) normScale normLabel
  let globalScale := dyadicCeilUpper normLabel
  let centers := finiteMetricCoverCenters
    (activeTubeImage S.family physical.ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
  let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
    (fun i x ↦ x ∈ physical.carrier i)
    (activeTubeImage S.family physical.ambient) fallback
    (actualProjectedAmbientCriticalFamily S.family physical.ambient)
    projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
    globalScale (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
  let cell := fun center ↦ measurableLabelCell E_norm label center
  have hcellMeasurable : ∀ center, center ∈ centers →
      MeasurableSet (cell center) := fun center hcenter ↦
    (hcellData center hcenter).1
  have hradiusTangency : (radius : Real) ≤ 36 * globalScale := by
    have hscale36 : globalScale ≤ 36 * globalScale := by nlinarith
    exact hradiusGlobalScale.trans hscale36
  have hlocalized : ∀ center, center ∈ centers → ∀ x, x ∈ cell center →
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily S.family physical.ambient)
        projectedTubePairCoefficientDistance globalScale center
        (physical.activeAtPoint x)).Nonempty := by
    intro center hcenter x hx
    obtain ⟨hlocalFamily, hballSubset, _hcard⟩ :=
      (hcellData center hcenter).2.2 x hx
    have hballNonempty := finiteNormCriticalBall_nonempty
      (exponent := normExponent) (actualProjectedAmbientCriticalFamily S.family physical.ambient
        (physical.activeAtPoint x))
      projectedTubePairCoefficientDistance hlocalFamily
      (fun T _hT ↦ by
        rw [projectedTubePairCoefficientDistance_self]
        exact_mod_cast hradius.le)
      hradiusSixteen
    exact hballNonempty.mono hballSubset
  have hdichotomy := actualAllCenter_canonicalPayload_high_or_all_low
    volume S.family physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
    centers cell tangencyExponent logCount hradius hradiusTangency
    hcellMeasurable hlocalized
  refine ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormNonempty,
    hnormMeasurable, hnormSubset, hglobalScale, hradiusGlobalScale,
    hnormBin, fallback, hcellData, ?_, ?_, ?_⟩
  · simpa only [physical, normScale, E_norm, globalScale, centers, label,
      cell] using hpartition
  · simpa only [physical, normScale, E_norm, globalScale, centers, label,
      cell] using hlabelRange
  · simpa only [physical, normScale, E_norm, globalScale, centers, label,
      cell, hcellMeasurable] using hdichotomy


/-- Any finite predicate split carries at least half of the total ENNReal
weight on one side.  The proof is valid when the total weight is infinite;
it performs no `toReal` conversion and assumes no finiteness. -/
theorem half_sum_le_filter_or_filter_not
    {alpha : Type*} [DecidableEq alpha]
    (items : Finset alpha) (weight : alpha -> ENNReal) (p : alpha -> Prop)
    [DecidablePred p] :
    (∑ a ∈ items, weight a) / 2 <=
        ∑ a ∈ items.filter p, weight a ∨
      (∑ a ∈ items, weight a) / 2 <=
        ∑ a ∈ items.filter (fun a => ¬ p a), weight a := by
  let high := ∑ a ∈ items.filter p, weight a
  let low := ∑ a ∈ items.filter (fun a => ¬ p a), weight a
  have hsplit : (∑ a ∈ items, weight a) = high + low := by
    simpa only [high, low] using
      (Finset.sum_filter_add_sum_filter_not items p weight).symm
  rw [hsplit]
  have hsumMax : high + low <= max high low * 2 := by
    calc
      high + low <= max high low + max high low :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = max high low * 2 := by ring
  have hhalfMax : (high + low) / 2 <= max high low :=
    ENNReal.div_le_of_le_mul hsumMax
  by_cases hlowHigh : low <= high
  · exact Or.inl (by simpa [max_eq_left hlowHigh] using hhalfMax)
  · have hhighLow : high <= low := le_of_not_ge hlowHigh
    exact Or.inr (by simpa [max_eq_right hhighLow] using hhalfMax)


/-- Choose a genuine canonical payload in every positive centre cell, split
those cells by the actual selected degree, and retain an exact mass
partition.  One side carries at least half of the supplied source mass.
Zero-mass cells are discarded only after proving that they contribute zero. -/
theorem exists_actualAllCenter_payloadAt_mass_high_or_low
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real)
    (centers : Finset (Tube radius)) (cell : Tube radius -> Set point)
    (tangencyExponent : Real) (logCount : Nat)
    (hradius : 0 < radius)
    (hradiusTangency : (radius : Real) <= 36 * globalScale)
    (hcellMeasurable : forall center, center ∈ centers ->
      MeasurableSet (cell center))
    (hlocalized : forall center, center ∈ centers ->
      forall x, x ∈ cell center ->
        (finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily fine physical.ambient)
          projectedTubePairCoefficientDistance globalScale center
          (physical.activeAtPoint x)).Nonempty)
    (sourceMass : ENNReal)
    (hsourceMass : sourceMass =
      ∑ center ∈ centers, mu (cell center)) :
    let positiveCenters := centers.filter fun center =>
      0 < mu (cell center)
    let PositiveCenter := {center // center ∈ positiveCenters}
    exists payloadAt : forall center : PositiveCenter,
      ActualPositiveCenterCanonicalPayload mu (cell center.1)
        (hcellMeasurable center.1
          ((Finset.mem_filter.mp center.2).1)) fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale center.1 tangencyExponent,
      let isHigh := fun center : PositiveCenter =>
        24 * logCount <= pyzE2DegreeLower (payloadAt center).finalLabel
      let high := (Finset.univ : Finset PositiveCenter).filter isHigh
      let low := (Finset.univ : Finset PositiveCenter).filter fun center =>
        ¬ isHigh center
      sourceMass =
          (∑ center ∈ high, mu (cell center.1)) +
            ∑ center ∈ low, mu (cell center.1) ∧
        (sourceMass / 2 <=
            ∑ center ∈ high, mu (cell center.1) ∨
          sourceMass / 2 <=
            ∑ center ∈ low, mu (cell center.1)) ∧
        (forall center, center ∈ high ->
          24 * logCount <=
            pyzE2DegreeLower (payloadAt center).finalLabel) ∧
        (forall center, center ∈ low ->
          pyzE2DegreeLower (payloadAt center).finalLabel <
            24 * logCount) := by
  classical
  let positiveCenters := centers.filter fun center =>
    0 < mu (cell center)
  let PositiveCenter := {center // center ∈ positiveCenters}
  let Payload : PositiveCenter -> Type _ := fun center =>
    ActualPositiveCenterCanonicalPayload mu (cell center.1)
      (hcellMeasurable center.1
        ((Finset.mem_filter.mp center.2).1)) fine physical f f1 f2
      outerA outerB hOuter hf hf1 globalScale center.1 tangencyExponent
  have hpayload : forall center : PositiveCenter,
      Nonempty (Payload center) := by
    intro center
    exact exists_actualPositiveCenterCanonicalPayload mu (cell center.1)
      (hcellMeasurable center.1
        ((Finset.mem_filter.mp center.2).1))
      ((Finset.mem_filter.mp center.2).2) fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale center.1 tangencyExponent hradius
      hradiusTangency
      (hlocalized center.1 ((Finset.mem_filter.mp center.2).1))
  let payloadAt : forall center : PositiveCenter, Payload center :=
    fun center => Classical.choice (hpayload center)
  refine ⟨payloadAt, ?_⟩
  let isHigh := fun center : PositiveCenter =>
    24 * logCount <= pyzE2DegreeLower (payloadAt center).finalLabel
  let high := (Finset.univ : Finset PositiveCenter).filter isHigh
  let low := (Finset.univ : Finset PositiveCenter).filter fun center =>
    ¬ isHigh center
  have hpositiveSum :
      (∑ center : PositiveCenter, mu (cell center.1)) =
        ∑ center ∈ centers, mu (cell center) := by
    calc
      (∑ center : PositiveCenter, mu (cell center.1)) =
          ∑ center ∈ positiveCenters, mu (cell center) := by
            simpa only [PositiveCenter, Finset.univ_eq_attach] using
              Finset.sum_attach positiveCenters
                (fun center => mu (cell center))
      _ = ∑ center ∈ centers, mu (cell center) := by
        apply Finset.sum_subset
        · intro center hcenter
          exact (Finset.mem_filter.mp hcenter).1
        · intro center hcenter hnot
          have hnpos : ¬ 0 < mu (cell center) := by
            intro hpos
            exact hnot (Finset.mem_filter.mpr ⟨hcenter, hpos⟩)
          exact le_antisymm (not_lt.mp hnpos) bot_le
  have htotal : sourceMass =
      ∑ center : PositiveCenter, mu (cell center.1) :=
    hsourceMass.trans hpositiveSum.symm
  have hsplit :
      (∑ center : PositiveCenter, mu (cell center.1)) =
        (∑ center ∈ high, mu (cell center.1)) +
          ∑ center ∈ low, mu (cell center.1) := by
    simpa only [high, low, isHigh] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset PositiveCenter) isHigh
          (fun center => mu (cell center.1))).symm
  have hhalf := half_sum_le_filter_or_filter_not
    (Finset.univ : Finset PositiveCenter)
    (fun center => mu (cell center.1)) isHigh
  rw [← htotal] at hhalf
  refine ⟨htotal.trans hsplit, hhalf, ?_, ?_⟩
  · intro center hcenter
    exact (Finset.mem_filter.mp hcenter).2
  · intro center hcenter
    exact lt_of_not_ge (Finset.mem_filter.mp hcenter).2


/-- Sum local same-witness bounds over a half-mass high family.  A strictly
positive natural degree gap is enough to discard the degree factor; no
cancellation in ENNReal is used. -/
theorem half_sourceMass_le_sum_rhs_of_degreeGap
    {alpha : Type*} [DecidableEq alpha]
    (high : Finset alpha) (weight rhs : alpha -> ENNReal)
    (degreeGap : alpha -> Nat) (sourceMass : ENNReal)
    (hhalf : sourceMass / 2 <= ∑ a ∈ high, weight a)
    (hgap : forall a, a ∈ high -> 1 <= degreeGap a)
    (hlocal : forall a, a ∈ high ->
      weight a * (degreeGap a : ENNReal) <= rhs a) :
    sourceMass / 2 <= ∑ a ∈ high, rhs a := by
  apply hhalf.trans
  apply Finset.sum_le_sum
  intro a ha
  calc
    weight a = weight a * 1 := by rw [mul_one]
    _ <= weight a * (degreeGap a : ENNReal) := by
      gcongr
      exact_mod_cast hgap a ha
    _ <= rhs a := hlocal a ha

#print axioms half_sourceMass_le_sum_rhs_of_degreeGap

#print axioms exists_actualAllCenter_payloadAt_mass_high_or_low

#print axioms half_sum_le_filter_or_filter_not

#print axioms exists_actualNormFirst_allCenterPayload_high_or_all_low

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
