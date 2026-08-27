import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualCoarseFiberIndexRandomSamplingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualCoarseFiberIndexRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Sampling the actual Y1 coarse fibres in the shared global norm family

The point sources of the fine rectangles vary, but all actual Y1 incidences
lie in the same global coefficient `3B`.  The two endpoints below construct
that global canonical family and discharge fibre provenance automatically.

For arbitrary `mu` and `nu`, lower cardinality of the two restricted coarse
balls is genuinely additional quantitative data.  With no such input the
common-fibre centre witnesses give the sharp automatic conclusion `mu = nu =
1`; this is the version recorded here.
-/

/-- Index-valued actual sampler with automatic shared-global provenance and
the strongest unconditional local richness, namely one retained centre in
each restricted ball. -/
theorem exists_actualCenteredHalfY1_globalNorm_index_sample_one_rich
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle) (left right : iota)
    (ballRadius : Real) (hballRadius : 0 <= ballRadius)
    (hleftFiber : forall R, R ∈ rectangles ->
      left ∈ D.coarseCurveIndexFiber keep R)
    (hrightFiber : forall R, R ∈ rectangles ->
      right ∈ D.coarseCurveIndexFiber keep R) :
    exists N : CanonicalNormNonconcentrationData iota,
      N.family =
          actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
        ((rectangles.card : Nat) : Real) / 8 <=
            ((twoSidedZeroColorSurvivors 1 1
              (fun R : rectangles =>
                ambientSubtypeRestriction N.family
                  (D.coarseCurveMetricBall keep R.1
                    projectedTubePairCoefficientDistance ballRadius
                    (fine.tubes left)))
              (fun R : rectangles =>
                ambientSubtypeRestriction N.family
                  (D.coarseCurveMetricBall keep R.1
                    projectedTubePairCoefficientDistance ballRadius
                    (fine.tubes right))) omega).card : Real) ∧
          twoSidedZeroColorLoad 1 1 omega <=
            7 * ((N.family.card : Real) / (1 : Real) +
              (N.family.card : Real) / (1 : Real)) := by
  have hgoodActual :
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent threshold fineT coarseDelta coarseT).goodPairs.Nonempty := by
    simpa only [← hD] using hgood
  have hfamilies :=
    actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT hgoodActual
  let N := actualGlobalNormIndexData fine physical globalScale globalCenter
    exponent hfamilies.1 hradius hradiusSixteen hexponent
  refine ⟨N, rfl, ?_⟩
  have hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseCurveIndexFiber keep R ⊆ N.family := by
    intro R hR
    rw [hD]
    exact actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT keep R
  have hDf : D.fine = fine := by
    rw [hD]
    rfl
  have hleftCard : forall R, R ∈ rectangles ->
      1 <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius
        (fine.tubes left)).card := by
    intro R hR
    apply Finset.one_le_card.mpr
    refine ⟨left, (D.mem_coarseCurveMetricBall_iff keep).mpr
      ⟨hleftFiber R hR, ?_⟩⟩
    rw [hDf, projectedTubePairCoefficientDistance_self]
    exact hballRadius
  have hrightCard : forall R, R ∈ rectangles ->
      1 <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius
        (fine.tubes right)).card := by
    intro R hR
    apply Finset.one_le_card.mpr
    refine ⟨right, (D.mem_coarseCurveMetricBall_iff keep).mpr
      ⟨hrightFiber R hR, ?_⟩⟩
    rw [hDf, projectedTubePairCoefficientDistance_self]
    exact hballRadius
  simpa only [Nat.cast_one] using
    (exists_actualCoarseFiberIndex_sample_with_eighth_survival_and_sevenfold_load
      N D keep rectangles projectedTubePairCoefficientDistance
        (fine.tubes left) (fine.tubes right) ballRadius 1 1 hfiberSubset
        hleftCard hrightCard)

/-- Tube-valued counterpart.  Its ambient canonical family is exactly the
shared global `3B` tube family, and no point anchor or fibre inclusion is an
input. -/
theorem exists_actualCenteredHalfY1_globalNorm_tube_sample_one_rich
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle) (left right : Tube radius)
    (ballRadius : Real) (hballRadius : 0 <= ballRadius)
    (hleftFiber : forall R, R ∈ rectangles ->
      left ∈ D.coarseTubeFiber keep R)
    (hrightFiber : forall R, R ∈ rectangles ->
      right ∈ D.coarseTubeFiber keep R) :
    exists N : CanonicalNormNonconcentrationData (Tube radius),
      N.family =
          actualGlobalNormTubeFamily fine physical globalScale globalCenter ∧
      exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
        ((rectangles.card : Nat) : Real) / 8 <=
            ((twoSidedZeroColorSurvivors 1 1
              (fun R : rectangles =>
                ambientSubtypeRestriction N.family
                  (D.coarseTubeMetricBall keep R.1 N.distance ballRadius left))
              (fun R : rectangles =>
                ambientSubtypeRestriction N.family
                  (D.coarseTubeMetricBall keep R.1 N.distance ballRadius right))
              omega).card : Real) ∧
          twoSidedZeroColorLoad 1 1 omega <=
            7 * ((N.family.card : Real) / (1 : Real) +
              (N.family.card : Real) / (1 : Real)) := by
  have hgoodActual :
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent threshold fineT coarseDelta coarseT).goodPairs.Nonempty := by
    simpa only [← hD] using hgood
  have hfamilies :=
    actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT hgoodActual
  let N := actualGlobalNormTubeData fine physical globalScale globalCenter
    exponent hfamilies.2 hradius hradiusSixteen hexponent
  refine ⟨N, rfl, ?_⟩
  have hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseTubeFiber keep R ⊆ N.family := by
    intro R hR
    rw [hD]
    exact actualCenteredHalfY1_coarseTubeFiber_subset_globalNormTubeFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT keep R
  have hleftCard : forall R, R ∈ rectangles ->
      1 <= (D.coarseTubeMetricBall keep R N.distance ballRadius left).card := by
    intro R hR
    apply Finset.one_le_card.mpr
    refine ⟨left, (D.mem_coarseTubeMetricBall_iff keep).mpr
      ⟨hleftFiber R hR, ?_⟩⟩
    change projectedTubePairCoefficientDistance left left <= ballRadius
    rw [projectedTubePairCoefficientDistance_self]
    exact hballRadius
  have hrightCard : forall R, R ∈ rectangles ->
      1 <= (D.coarseTubeMetricBall keep R N.distance ballRadius right).card := by
    intro R hR
    apply Finset.one_le_card.mpr
    refine ⟨right, (D.mem_coarseTubeMetricBall_iff keep).mpr
      ⟨hrightFiber R hR, ?_⟩⟩
    change projectedTubePairCoefficientDistance right right <= ballRadius
    rw [projectedTubePairCoefficientDistance_self]
    exact hballRadius
  simpa only [Nat.cast_one] using
    (exists_actualCoarseFiberTube_sample_with_eighth_survival_and_sevenfold_load
      N D keep rectangles left right ballRadius 1 1 hfiberSubset hleftCard
        hrightCard)

/-! ## Extracting genuine endpoint pairs from survivor hit events -/

/-- The literal subtype of rectangles whose two neighbour families are hit
by the same sampled outcome. -/
abbrev TwoSidedZeroColorSurvivor
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l)) :=
  {R // R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega}

/-- A genuine left neighbour witnessing the left hit of one survivor.  The
subtype stores both neighbour membership and the literal zero-colour event. -/
noncomputable def survivorLeftHitWitness
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l))
    (R : TwoSidedZeroColorSurvivor k l leftNeighbors rightNeighbors omega) :
    {a // a ∈ leftNeighbors R.1 ∧ omega.1 a = 0} := by
  have hsurvivor :=
    (mem_twoSidedZeroColorSurvivors_iff k l leftNeighbors rightNeighbors
      omega R.1).mp R.2
  let hex :=
    (mem_zeroColorHitEvent_iff k (leftNeighbors R.1) omega.1).mp hsurvivor.1
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩

/-- The corresponding genuine right hit witness. -/
noncomputable def survivorRightHitWitness
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l))
    (R : TwoSidedZeroColorSurvivor k l leftNeighbors rightNeighbors omega) :
    {b // b ∈ rightNeighbors R.1 ∧ omega.2 b = 0} := by
  have hsurvivor :=
    (mem_twoSidedZeroColorSurvivors_iff k l leftNeighbors rightNeighbors
      omega R.1).mp R.2
  let hex :=
    (mem_zeroColorHitEvent_iff l (rightNeighbors R.1) omega.2).mp hsurvivor.2
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩

theorem survivorLeftHitWitness_mem_neighbors
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l))
    (R : TwoSidedZeroColorSurvivor k l leftNeighbors rightNeighbors omega) :
    (survivorLeftHitWitness k l leftNeighbors rightNeighbors omega R).1 ∈
      leftNeighbors R.1 :=
  (survivorLeftHitWitness k l leftNeighbors rightNeighbors omega R).2.1

theorem survivorRightHitWitness_mem_neighbors
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l))
    (R : TwoSidedZeroColorSurvivor k l leftNeighbors rightNeighbors omega) :
    (survivorRightHitWitness k l leftNeighbors rightNeighbors omega R).1 ∈
      rightNeighbors R.1 :=
  (survivorRightHitWitness k l leftNeighbors rightNeighbors omega R).2.1

/-- The actual-tube family formed by choosing one genuine hit on each side
of every surviving rectangle. -/
noncomputable def survivorRetainedPairTubeFamily
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    {radius : NNReal}
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l))
    (leftTube : alpha -> Tube radius) (rightTube : beta -> Tube radius) :
    Finset (Tube radius) :=
  retainedPairTubeFamily
    (Finset.univ : Finset
      (TwoSidedZeroColorSurvivor k l leftNeighbors rightNeighbors omega))
    (fun R => leftTube
      (survivorLeftHitWitness k l leftNeighbors rightNeighbors omega R).1)
    (fun R => rightTube
      (survivorRightHitWitness k l leftNeighbors rightNeighbors omega R).1)

/-- Elementary union bound for a retained endpoint family whose two maps
land in specified finite samples. -/
theorem retainedPairTubeFamily_card_le_of_mem
    {gamma : Type*} [DecidableEq gamma]
    {radius : NNReal} (fiber : Finset gamma)
    (T U : gamma -> Tube radius)
    (leftFamily rightFamily : Finset (Tube radius))
    (hleft : forall i, i ∈ fiber -> T i ∈ leftFamily)
    (hright : forall i, i ∈ fiber -> U i ∈ rightFamily) :
    (retainedPairTubeFamily fiber T U).card <=
      leftFamily.card + rightFamily.card := by
  have hleftImage : fiber.image T ⊆ leftFamily := by
    intro V hV
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
    exact hleft i hi
  have hrightImage : fiber.image U ⊆ rightFamily := by
    intro V hV
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
    exact hright i hi
  calc
    (retainedPairTubeFamily fiber T U).card <=
        (fiber.image T).card + (fiber.image U).card := by
      exact Finset.card_union_le _ _
    _ <= leftFamily.card + rightFamily.card :=
      Nat.add_le_add (Finset.card_le_card hleftImage)
        (Finset.card_le_card hrightImage)

/-- The chosen endpoint family never uses more distinct actual tubes than
the total number of sampled left and right coordinates. -/
theorem survivorRetainedPairTubeFamily_card_le_two_samples
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    {radius : NNReal}
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l))
    (leftTube : alpha -> Tube radius) (rightTube : beta -> Tube radius) :
    (survivorRetainedPairTubeFamily k l leftNeighbors rightNeighbors omega
      leftTube rightTube).card <=
        (zeroColorSample k omega.1).card +
          (zeroColorSample l omega.2).card := by
  let fiber : Finset
      (TwoSidedZeroColorSurvivor k l leftNeighbors rightNeighbors omega) :=
    Finset.univ
  let T := fun R :
      TwoSidedZeroColorSurvivor k l leftNeighbors rightNeighbors omega =>
    leftTube
      (survivorLeftHitWitness k l leftNeighbors rightNeighbors omega R).1
  let U := fun R :
      TwoSidedZeroColorSurvivor k l leftNeighbors rightNeighbors omega =>
    rightTube
      (survivorRightHitWitness k l leftNeighbors rightNeighbors omega R).1
  let leftFamily := (zeroColorSample k omega.1).image leftTube
  let rightFamily := (zeroColorSample l omega.2).image rightTube
  have hleft : forall R, R ∈ fiber -> T R ∈ leftFamily := by
    intro R _hR
    apply Finset.mem_image.mpr
    refine ⟨(survivorLeftHitWitness k l leftNeighbors rightNeighbors
      omega R).1, ?_, rfl⟩
    simp only [zeroColorSample, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (survivorLeftHitWitness k l leftNeighbors rightNeighbors
      omega R).2.2
  have hright : forall R, R ∈ fiber -> U R ∈ rightFamily := by
    intro R _hR
    apply Finset.mem_image.mpr
    refine ⟨(survivorRightHitWitness k l leftNeighbors rightNeighbors
      omega R).1, ?_, rfl⟩
    simp only [zeroColorSample, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (survivorRightHitWitness k l leftNeighbors rightNeighbors
      omega R).2.2
  calc
    (survivorRetainedPairTubeFamily k l leftNeighbors rightNeighbors omega
        leftTube rightTube).card = (retainedPairTubeFamily fiber T U).card := by
      rfl
    _ <= leftFamily.card + rightFamily.card :=
      retainedPairTubeFamily_card_le_of_mem fiber T U leftFamily rightFamily
        hleft hright
    _ <= (zeroColorSample k omega.1).card +
        (zeroColorSample l omega.2).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le

/-- Real-valued form used directly by the sevenfold-load estimate. -/
theorem survivorRetainedPairTubeFamily_card_cast_le_load
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    {radius : NNReal}
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l))
    (leftTube : alpha -> Tube radius) (rightTube : beta -> Tube radius) :
    ((survivorRetainedPairTubeFamily k l leftNeighbors rightNeighbors omega
      leftTube rightTube).card : Real) <= twoSidedZeroColorLoad k l omega := by
  unfold twoSidedZeroColorLoad
  exact_mod_cast survivorRetainedPairTubeFamily_card_le_two_samples k l
    leftNeighbors rightNeighbors omega leftTube rightTube

/-! ## G-prime separated centres followed by one-rich sampling -/

/-- The downstream package produced after a positive G-prime separated-pair
lower bound: two genuine centres over a common coarse rectangle, their
canonical separated balls, and a same-outcome singleton-rectangle sample
whose retained actual-tube family is controlled by the sevenfold load. -/
noncomputable def ActualSeparatedSingletonSamplingOutcome
    {point : Type*} [MeasurableSpace point]
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    {fineLabel : Type*} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (lowerBound : Nat) : Prop :=
  exists left, left ∈ N.family ∧
    exists right, right ∈ N.family ∧
      canonicalTenRadiusSeparated N ballRadius left right ∧
      D.CoarseGoodPair keep left right ∧
      0 < D.coarseCrossIncidenceCount keep left right ∧
      lowerBound <=
        (richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N ballRadius)
            (D.CoarseGoodPair keep)).card *
          D.coarseCrossIncidenceCount keep left right ∧
      FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
        (finiteFamilyMetricBall N.family N.distance ballRadius left)
        (finiteFamilyMetricBall N.family N.distance ballRadius right) ∧
      ((finiteFamilyMetricBall N.family N.distance ballRadius left).card :
          Real) <=
        (ballRadius / N.criticalScale) ^ N.exponent *
          ((N.criticalBall.card : Nat) : Real) ∧
      ((finiteFamilyMetricBall N.family N.distance ballRadius right).card :
          Real) <=
        (ballRadius / N.criticalScale) ^ N.exponent *
          ((N.criticalBall.card : Nat) : Real) ∧
      exists R, R ∈ D.coarseRectangleFamily ∧
        left ∈ D.coarseCurveIndexFiber keep R ∧
        right ∈ D.coarseCurveIndexFiber keep R ∧
        let rectangles : Finset C2GraphRectangle := {R}
        let leftNeighbors := fun S : rectangles =>
          ambientSubtypeRestriction N.family
            (D.coarseCurveMetricBall keep S.1
              projectedTubePairCoefficientDistance ballRadius
              (D.fine.tubes left))
        let rightNeighbors := fun S : rectangles =>
          ambientSubtypeRestriction N.family
            (D.coarseCurveMetricBall keep S.1
              projectedTubePairCoefficientDistance ballRadius
              (D.fine.tubes right))
        exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
          ((rectangles.card : Nat) : Real) / 8 <=
              ((twoSidedZeroColorSurvivors 1 1 leftNeighbors rightNeighbors
                omega).card : Real) ∧
            twoSidedZeroColorLoad 1 1 omega <=
              7 * ((N.family.card : Real) / (1 : Real) +
                (N.family.card : Real) / (1 : Real)) ∧
            ((survivorRetainedPairTubeFamily 1 1 leftNeighbors rightNeighbors
              omega (fun i : N.family => D.fine.tubes i.1)
                (fun i : N.family => D.fine.tubes i.1)).card : Real) <=
              twoSidedZeroColorLoad 1 1 omega

/-- Closest actual assembly endpoint.  The shared-global family removes all
provenance assumptions.  The sole remaining quantitative premise is exposed
after bucket selection: one full degree block must remain after the rich/poor
rectangle subtraction.  That premise is exactly what makes the generated
separated-pair lower bound positive; no stronger mu/nu input is requested. -/
theorem exists_actualCenteredHalfY1_globalNorm_GPrime_separated_singleton_sample_one_rich
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent) (ballRadius : Real)
    (hradiusBall : (radius : Real) <= ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= 16) :
    exists N : CanonicalNormNonconcentrationData iota,
      N.family =
          actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      ∃ bucket ∈ Finset.range (coarseDegreeBucketLoss D),
        0 < comparableBase bucket ∧
        D.goodPairs.card <= coarseDegreeBucketLoss D *
          (D.retainedGoodPairs
            (coarseDegreeBucketKeep D bucket)).card ∧
        let keep := coarseDegreeBucketKeep D bucket
        let lowerBound :=
          canonicalCoarseSeparatedPairProducedLower
            (automaticCanonicalRichness N ballRadius)
            (automaticCanonicalNearCap N ballRadius)
            (automaticRichRetainedMassLower D
              (automaticCanonicalRichness N ballRadius)
              (2 * comparableBase bucket))
            (2 * comparableBase bucket)
        lowerBound <=
            canonicalCoarseRichSeparatedPairCountTotal N D keep ballRadius ∧
          (2 * comparableBase bucket <=
              automaticRichRetainedMassLower D
                (automaticCanonicalRichness N ballRadius)
                (2 * comparableBase bucket) ->
            ActualSeparatedSingletonSamplingOutcome N D keep ballRadius
              lowerBound) := by
  have hgoodActual :
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent threshold fineT coarseDelta coarseT).goodPairs.Nonempty := by
    simpa only [← hD] using hgood
  have hfamilies :=
    actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT hgoodActual
  let N := actualGlobalNormIndexData fine physical globalScale globalCenter
    exponent hfamilies.1 hradius hradiusSixteen hexponent
  have hsymm : forall i j, N.distance i j = N.distance j i := by
    intro i j
    exact actualGlobalNormIndexData_distance_comm fine physical globalScale
      globalCenter exponent hfamilies.1 hradius hradiusSixteen hexponent i j
  have htriangle : forall i center j,
      N.distance i j <= N.distance i center + N.distance center j := by
    intro i center j
    exact projectedTubePairCoefficientDistance_triangle
      (fine.tubes i) (fine.tubes center) (fine.tubes j)
  have hballNonneg : 0 <= ballRadius :=
    (show (0 : Real) <= (radius : Real) from by positivity).trans hradiusBall
  have hnearRadiusLower : N.delta <= 10 * ballRadius := by
    change (radius : Real) <= 10 * ballRadius
    nlinarith
  have hballUpper : ballRadius <= N.ceiling := by
    change ballRadius <= 16
    nlinarith
  obtain ⟨bucket, hbucket, hbasePos, hselection, hproducedIf⟩ :=
    exists_actualGPrime_bucket_separatedPairLower N D ballRadius hgood hsymm
      hnearRadiusLower hnearRadiusUpper
  have hfiberSubset : forall R,
      R ∈ richCoarseRectangleFamily D
        (coarseDegreeBucketKeep D bucket)
        (automaticCanonicalRichness N ballRadius) ->
      D.coarseCurveIndexFiber (coarseDegreeBucketKeep D bucket) R ⊆
        N.family := by
    intro R _hR
    change D.coarseCurveIndexFiber (coarseDegreeBucketKeep D bucket) R ⊆
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    simpa only [hD] using
      (actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
        base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
        hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
        coarseDelta coarseT (coarseDegreeBucketKeep D bucket) R)
  have hproduced := hproducedIf hfiberSubset
  refine ⟨N, rfl, bucket, hbucket, hbasePos, hselection, hproduced, ?_⟩
  intro hmassBlock
  let keep := coarseDegreeBucketKeep D bucket
  let lowerBound :=
    canonicalCoarseSeparatedPairProducedLower
      (automaticCanonicalRichness N ballRadius)
      (automaticCanonicalNearCap N ballRadius)
      (automaticRichRetainedMassLower D
        (automaticCanonicalRichness N ballRadius)
        (2 * comparableBase bucket))
      (2 * comparableBase bucket)
  have hlowerPos : 0 < lowerBound := by
    exact automatic_bucket_separatedPairLower_pos N D ballRadius bucket
      hbasePos hmassBlock
  obtain ⟨left, hleft, right, hright, hseparated, hcoarseGood,
      hcrossPositive, hrichLower, hwitness, hcrossSeparated,
      hleftUpper, hrightUpper⟩ :=
    exists_canonical_coarse_richSeparated_ballPair N D keep hsymm htriangle
      hradiusBall hballUpper hlowerPos hproduced
  obtain ⟨R, hR, ⟨leftFine, hleftFine⟩, ⟨rightFine, hrightFine⟩⟩ :=
    hwitness
  have hleftFiber : left ∈ D.coarseCurveIndexFiber keep R :=
    (D.mem_coarseCurveIndexFiber_iff keep).mpr ⟨leftFine, hleftFine⟩
  have hrightFiber : right ∈ D.coarseCurveIndexFiber keep R :=
    (D.mem_coarseCurveIndexFiber_iff keep).mpr ⟨rightFine, hrightFine⟩
  refine ⟨left, hleft, right, hright, hseparated, hcoarseGood,
    hcrossPositive, hrichLower, hcrossSeparated, hleftUpper, hrightUpper,
    R, hR, hleftFiber, hrightFiber, ?_⟩
  dsimp only
  have hsingletonFiber : forall S, S ∈ ({R} : Finset C2GraphRectangle) ->
      D.coarseCurveIndexFiber keep S ⊆ N.family := by
    intro S hS
    have hSR : S = R := Finset.mem_singleton.mp hS
    subst S
    change D.coarseCurveIndexFiber keep R ⊆
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    rw [hD]
    exact actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT keep R
  have hleftCard : forall S, S ∈ ({R} : Finset C2GraphRectangle) ->
      1 <= (D.coarseCurveMetricBall keep S
        projectedTubePairCoefficientDistance ballRadius
        (D.fine.tubes left)).card := by
    intro S hS
    have hSR : S = R := Finset.mem_singleton.mp hS
    subst S
    apply Finset.one_le_card.mpr
    refine ⟨left, (D.mem_coarseCurveMetricBall_iff keep).mpr
      ⟨hleftFiber, ?_⟩⟩
    rw [projectedTubePairCoefficientDistance_self]
    exact hballNonneg
  have hrightCard : forall S, S ∈ ({R} : Finset C2GraphRectangle) ->
      1 <= (D.coarseCurveMetricBall keep S
        projectedTubePairCoefficientDistance ballRadius
        (D.fine.tubes right)).card := by
    intro S hS
    have hSR : S = R := Finset.mem_singleton.mp hS
    subst S
    apply Finset.one_le_card.mpr
    refine ⟨right, (D.mem_coarseCurveMetricBall_iff keep).mpr
      ⟨hrightFiber, ?_⟩⟩
    rw [projectedTubePairCoefficientDistance_self]
    exact hballNonneg
  obtain ⟨omega, hsurvival, hload⟩ :=
    exists_actualCoarseFiberIndex_sample_with_eighth_survival_and_sevenfold_load
      N D keep ({R} : Finset C2GraphRectangle)
        projectedTubePairCoefficientDistance (D.fine.tubes left)
        (D.fine.tubes right) ballRadius 1 1 hsingletonFiber hleftCard
        hrightCard
  refine ⟨omega, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_one] using hsurvival
  · simpa only [Nat.cast_one] using hload
  · exact survivorRetainedPairTubeFamily_card_cast_le_load 1 1
      (fun S : ({R} : Finset C2GraphRectangle) =>
        ambientSubtypeRestriction N.family
          (D.coarseCurveMetricBall keep S.1
            projectedTubePairCoefficientDistance ballRadius
            (D.fine.tubes left)))
      (fun S : ({R} : Finset C2GraphRectangle) =>
        ambientSubtypeRestriction N.family
          (D.coarseCurveMetricBall keep S.1
            projectedTubePairCoefficientDistance ballRadius
            (D.fine.tubes right)))
      omega (fun i : N.family => D.fine.tubes i.1)
        (fun i : N.family => D.fine.tubes i.1)

/-! ## Paper-level arbitrary mu/nu endpoints -/

/-- Shared-global index sampler with arbitrary positive sampling moduli.
The local cardinality lower bounds are retained as the exact quantitative
inputs of PYZ Proposition 4.1.  The same outcome also controls the actual
retained endpoint-tube family by its sevenfold load. -/
theorem exists_actualCenteredHalfY1_globalNorm_index_sample_mu_nu
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (hleftCard : forall R, R ∈ rectangles ->
      mu <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius left).card)
    (hrightCard : forall R, R ∈ rectangles ->
      nu <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius right).card) :
    exists N : CanonicalNormNonconcentrationData iota,
      N.family =
          actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      exists omega : (N.family -> Fin mu) × (N.family -> Fin nu),
        ((rectangles.card : Nat) : Real) / 8 <=
            ((twoSidedZeroColorSurvivors mu nu
              (fun R : rectangles =>
                ambientSubtypeRestriction N.family
                  (D.coarseCurveMetricBall keep R.1
                    projectedTubePairCoefficientDistance ballRadius left))
              (fun R : rectangles =>
                ambientSubtypeRestriction N.family
                  (D.coarseCurveMetricBall keep R.1
                    projectedTubePairCoefficientDistance ballRadius right))
              omega).card : Real) ∧
          twoSidedZeroColorLoad mu nu omega <=
            7 * ((N.family.card : Real) / (mu : Real) +
              (N.family.card : Real) / (nu : Real)) ∧
          ((survivorRetainedPairTubeFamily mu nu
            (fun R : rectangles =>
              ambientSubtypeRestriction N.family
                (D.coarseCurveMetricBall keep R.1
                  projectedTubePairCoefficientDistance ballRadius left))
            (fun R : rectangles =>
              ambientSubtypeRestriction N.family
                (D.coarseCurveMetricBall keep R.1
                  projectedTubePairCoefficientDistance ballRadius right))
            omega (fun i : N.family => D.fine.tubes i.1)
              (fun i : N.family => D.fine.tubes i.1)).card : Real) <=
            twoSidedZeroColorLoad mu nu omega := by
  have hgoodActual :
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent threshold fineT coarseDelta coarseT).goodPairs.Nonempty := by
    simpa only [← hD] using hgood
  have hfamilies :=
    actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT hgoodActual
  let N := actualGlobalNormIndexData fine physical globalScale globalCenter
    exponent hfamilies.1 hradius hradiusSixteen hexponent
  have hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseCurveIndexFiber keep R ⊆ N.family := by
    intro R _hR
    rw [hD]
    exact actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT keep R
  obtain ⟨omega, hsurvival, hload⟩ :=
    exists_actualCoarseFiberIndex_sample_with_eighth_survival_and_sevenfold_load
      N D keep rectangles projectedTubePairCoefficientDistance left right
        ballRadius mu nu hfiberSubset hleftCard hrightCard
  refine ⟨N, rfl, omega, hsurvival, hload, ?_⟩
  exact survivorRetainedPairTubeFamily_card_cast_le_load mu nu
    (fun R : rectangles =>
      ambientSubtypeRestriction N.family
        (D.coarseCurveMetricBall keep R.1 projectedTubePairCoefficientDistance
          ballRadius left))
    (fun R : rectangles =>
      ambientSubtypeRestriction N.family
        (D.coarseCurveMetricBall keep R.1 projectedTubePairCoefficientDistance
          ballRadius right))
    omega (fun i : N.family => D.fine.tubes i.1)
      (fun i : N.family => D.fine.tubes i.1)

/-! The tube-valued arbitrary-mu/nu counterpart. -/

/-- Tube-valued arbitrary-mu/nu endpoint over the shared global coefficient
family, with the same outcome controlling the retained actual-tube family. -/
theorem exists_actualCenteredHalfY1_globalNorm_tube_sample_mu_nu
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (hleftCard : forall R, R ∈ rectangles ->
      mu <= (D.coarseTubeMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius left).card)
    (hrightCard : forall R, R ∈ rectangles ->
      nu <= (D.coarseTubeMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius right).card) :
    exists N : CanonicalNormNonconcentrationData (Tube radius),
      N.family =
          actualGlobalNormTubeFamily fine physical globalScale globalCenter ∧
      exists omega : (N.family -> Fin mu) × (N.family -> Fin nu),
        ((rectangles.card : Nat) : Real) / 8 <=
            ((twoSidedZeroColorSurvivors mu nu
              (fun R : rectangles =>
                ambientSubtypeRestriction N.family
                  (D.coarseTubeMetricBall keep R.1 N.distance
                    ballRadius left))
              (fun R : rectangles =>
                ambientSubtypeRestriction N.family
                  (D.coarseTubeMetricBall keep R.1 N.distance
                    ballRadius right)) omega).card : Real) ∧
          twoSidedZeroColorLoad mu nu omega <=
            7 * ((N.family.card : Real) / (mu : Real) +
              (N.family.card : Real) / (nu : Real)) ∧
          ((survivorRetainedPairTubeFamily mu nu
            (fun R : rectangles =>
              ambientSubtypeRestriction N.family
                (D.coarseTubeMetricBall keep R.1 N.distance ballRadius left))
            (fun R : rectangles =>
              ambientSubtypeRestriction N.family
                (D.coarseTubeMetricBall keep R.1 N.distance ballRadius right))
            omega (fun T : N.family => T.1)
              (fun T : N.family => T.1)).card : Real) <=
            twoSidedZeroColorLoad mu nu omega := by
  have hgoodActual :
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent threshold fineT coarseDelta coarseT).goodPairs.Nonempty := by
    simpa only [← hD] using hgood
  have hfamilies :=
    actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT hgoodActual
  let N := actualGlobalNormTubeData fine physical globalScale globalCenter
    exponent hfamilies.2 hradius hradiusSixteen hexponent
  have hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseTubeFiber keep R ⊆ N.family := by
    intro R _hR
    rw [hD]
    exact actualCenteredHalfY1_coarseTubeFiber_subset_globalNormTubeFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT keep R
  obtain ⟨omega, hsurvival, hload⟩ :=
    exists_actualCoarseFiberTube_sample_with_eighth_survival_and_sevenfold_load
      N D keep rectangles left right ballRadius mu nu hfiberSubset hleftCard
        hrightCard
  refine ⟨N, rfl, omega, hsurvival, hload, ?_⟩
  exact survivorRetainedPairTubeFamily_card_cast_le_load mu nu
    (fun R : rectangles =>
      ambientSubtypeRestriction N.family
        (D.coarseTubeMetricBall keep R.1 N.distance ballRadius left))
    (fun R : rectangles =>
      ambientSubtypeRestriction N.family
        (D.coarseTubeMetricBall keep R.1 N.distance ballRadius right))
    omega (fun T : N.family => T.1) (fun T : N.family => T.1)

#print axioms exists_actualCenteredHalfY1_globalNorm_index_sample_one_rich
#print axioms exists_actualCenteredHalfY1_globalNorm_tube_sample_one_rich
#print axioms survivorLeftHitWitness
#print axioms survivorRightHitWitness
#print axioms survivorLeftHitWitness_mem_neighbors
#print axioms survivorRightHitWitness_mem_neighbors
#print axioms survivorRetainedPairTubeFamily
#print axioms survivorRetainedPairTubeFamily_card_le_two_samples
#print axioms survivorRetainedPairTubeFamily_card_cast_le_load
#print axioms ActualSeparatedSingletonSamplingOutcome
#print axioms exists_actualCenteredHalfY1_globalNorm_GPrime_separated_singleton_sample_one_rich
#print axioms exists_actualCenteredHalfY1_globalNorm_index_sample_mu_nu
#print axioms exists_actualCenteredHalfY1_globalNorm_tube_sample_mu_nu

end

end FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
