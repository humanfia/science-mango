import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRandomSamplingLensAssemblyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingLensAssemblyV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Actual shared-global sampling to the paper-shaped lens bound

This connector stays entirely on the sampling lane.  Its callback is not an
unstructured inequality in an arbitrary real curve count: for every outcome
it must bound the surviving rectangles using the literal actual-tube family
chosen from the two genuine zero-colour hit witnesses.
-/

/-- The index-valued neighbour family used by actual shared-global sampling,
retyped into the canonical global `3B` ambient subtype. -/
noncomputable def actualSharedGlobalCoarseCurveNeighbors
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (ballRadius : Real) (center : Tube radius) :
    rectangles ->
      Finset (actualGlobalNormIndexFamily fine physical globalScale
        globalCenter) :=
  fun R =>
    ambientSubtypeRestriction
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter)
      (D.coarseCurveMetricBall keep R.1
        projectedTubePairCoefficientDistance ballRadius center)

/-- The exact actual-tube family used by the one-hit lens callback for one
sampling outcome. -/
noncomputable def actualSharedGlobalSurvivorRetainedTubeFamily
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu)) : Finset (Tube radius) :=
  survivorRetainedPairTubeFamily mu nu
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left)
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right)
    omega
    (fun i : actualGlobalNormIndexFamily fine physical globalScale
        globalCenter => D.fine.tubes i.1)
    (fun i : actualGlobalNormIndexFamily fine physical globalScale
        globalCenter => D.fine.tubes i.1)

/-- One-outcome actual lens certificate.  Its curve parameter is definitionally
the cardinality of the retained survivor tube family, so the callback cannot
silently substitute an unrelated load or ambient family. -/
def ActualSharedGlobalSurvivorLensCertificate
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (depth : Real)
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu)) : Prop :=
  ((twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right)
      omega).card : Real) <=
    sampledLensBound depth
      (actualSharedGlobalSurvivorRetainedTubeFamily fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega).card

/-- The selected left endpoint of every survivor is a genuine member of its
literal actual coarse-curve metric ball. -/
theorem actualSharedGlobal_survivorLeftHit_mem_coarseCurveMetricBall
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (S : TwoSidedZeroColorSurvivor mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega) :
    (survivorLeftHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega S).1.1 ∈
      D.coarseCurveMetricBall keep S.1.1
        projectedTubePairCoefficientDistance ballRadius left := by
  have hmem := survivorLeftHitWitness_mem_neighbors mu nu
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left)
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right) omega S
  exact (mem_ambientSubtypeRestriction_iff
    (actualGlobalNormIndexFamily fine physical globalScale globalCenter)
    (D.coarseCurveMetricBall keep S.1.1
      projectedTubePairCoefficientDistance ballRadius left) _).mp hmem

/-- Right-hand genuine-hit counterpart. -/
theorem actualSharedGlobal_survivorRightHit_mem_coarseCurveMetricBall
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (S : TwoSidedZeroColorSurvivor mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega) :
    (survivorRightHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega S).1.1 ∈
      D.coarseCurveMetricBall keep S.1.1
        projectedTubePairCoefficientDistance ballRadius right := by
  have hmem := survivorRightHitWitness_mem_neighbors mu nu
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left)
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right) omega S
  exact (mem_ambientSubtypeRestriction_iff
    (actualGlobalNormIndexFamily fine physical globalScale globalCenter)
    (D.coarseCurveMetricBall keep S.1.1
      projectedTubePairCoefficientDistance ballRadius right) _).mp hmem

/-- A retained-family certificate promotes to the load-valued callback needed
by the abstract finite lens assembly. -/
theorem ActualSharedGlobalSurvivorLensCertificate.card_le_sampledLensBound_load
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (depth : Real) (hdepth : 0 <= depth)
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (C : ActualSharedGlobalSurvivorLensCertificate fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu depth omega) :
    ((twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega).card : Real) <=
      sampledLensBound depth (twoSidedZeroColorLoad mu nu omega) := by
  have hfamilyLoad :
      ((actualSharedGlobalSurvivorRetainedTubeFamily fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega).card :
          Real) <= twoSidedZeroColorLoad mu nu omega := by
    exact survivorRetainedPairTubeFamily_card_cast_le_load mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right)
      omega
      (fun i : actualGlobalNormIndexFamily fine physical globalScale
          globalCenter => D.fine.tubes i.1)
      (fun i : actualGlobalNormIndexFamily fine physical globalScale
          globalCenter => D.fine.tubes i.1)
  exact C.trans (sampledLensBound_mono_curveCount hdepth
    (Nat.cast_nonneg _) hfamilyLoad)

/-- Highest paper-shaped actual endpoint on the sampling lane.  All global
family provenance is automatic.  The only quantitative inputs are precisely
the paper's local `mu`/`nu` neighbour lower bounds, and the only geometric
callback is the one-hit lens certificate on the literal retained survivor
tube family. -/
theorem actualCenteredHalfY1_rectangleCard_le_sharedGlobal_sampledLensPaperShape_mu_nu
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
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (hleftCard : forall R, R ∈ rectangles ->
      mu <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius left).card)
    (hrightCard : forall R, R ∈ rectangles ->
      nu <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius right).card)
    (depth : Real) (hdepth : 0 <= depth)
    (hsampledLens : forall omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu),
      ActualSharedGlobalSurvivorLensCertificate fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu depth
          omega) :
    let ambient :=
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    let load := 7 * ((ambient.card : Real) / (mu : Real) +
      (ambient.card : Real) / (nu : Real))
    ((rectangles.card : Nat) : Real) <=
      8 * (316 + 48 * depth) * load * Real.sqrt load := by
  dsimp only
  let ambient :=
    actualGlobalNormIndexFamily fine physical globalScale globalCenter
  let leftNeighbors :=
    actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left
  let rightNeighbors :=
    actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right
  have hfiberSubset : forall R,
      D.coarseCurveIndexFiber keep R ⊆ ambient := by
    intro R
    change D.coarseCurveIndexFiber keep R ⊆
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    rw [hD]
    exact actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT keep R
  have hleftSubset : forall S : rectangles,
      D.coarseCurveMetricBall keep S.1 projectedTubePairCoefficientDistance
        ballRadius left ⊆ ambient := by
    intro S i hi
    exact hfiberSubset S.1 ((D.mem_coarseCurveMetricBall_iff keep).mp hi).1
  have hrightSubset : forall S : rectangles,
      D.coarseCurveMetricBall keep S.1 projectedTubePairCoefficientDistance
        ballRadius right ⊆ ambient := by
    intro S i hi
    exact hfiberSubset S.1 ((D.mem_coarseCurveMetricBall_iff keep).mp hi).1
  have hleftRestricted : forall S : rectangles,
      mu <= (leftNeighbors S).card := by
    intro S
    change mu <= (ambientSubtypeRestriction ambient
      (D.coarseCurveMetricBall keep S.1 projectedTubePairCoefficientDistance
        ballRadius left)).card
    rw [ambientSubtypeRestriction_card_eq ambient _ (hleftSubset S)]
    exact hleftCard S.1 S.2
  have hrightRestricted : forall S : rectangles,
      nu <= (rightNeighbors S).card := by
    intro S
    change nu <= (ambientSubtypeRestriction ambient
      (D.coarseCurveMetricBall keep S.1 projectedTubePairCoefficientDistance
        ballRadius right)).card
    rw [ambientSubtypeRestriction_card_eq ambient _ (hrightSubset S)]
    exact hrightCard S.1 S.2
  have hsampledLensLoad : forall omega :
      (ambient -> Fin mu) × (ambient -> Fin nu),
      ((twoSidedZeroColorSurvivors mu nu leftNeighbors rightNeighbors
          omega).card : Real) <=
        sampledLensBound depth (twoSidedZeroColorLoad mu nu omega) := by
    intro omega
    exact (hsampledLens omega).card_le_sampledLensBound_load fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
      depth hdepth omega
  simpa only [Fintype.card_coe] using
    (rectangleCard_le_sampledLensPaperShape_of_twoSidedSampling_automaticBudget
      mu nu leftNeighbors rightNeighbors hleftRestricted hrightRestricted
        depth hdepth hsampledLensLoad)

#print axioms actualSharedGlobalCoarseCurveNeighbors
#print axioms actualSharedGlobalSurvivorRetainedTubeFamily
#print axioms ActualSharedGlobalSurvivorLensCertificate
#print axioms actualSharedGlobal_survivorLeftHit_mem_coarseCurveMetricBall
#print axioms actualSharedGlobal_survivorRightHit_mem_coarseCurveMetricBall
#print axioms ActualSharedGlobalSurvivorLensCertificate.card_le_sampledLensBound_load
#print axioms actualCenteredHalfY1_rectangleCard_le_sharedGlobal_sampledLensPaperShape_mu_nu

end

end FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
