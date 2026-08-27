import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1

open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

universe u v

/-!
# Actual centered-half E2 to same-fine separated balls

This connector discharges the only geometric provenance premise left by the
generic fine-label mass producer. Every active incidence at a selected fine
source point is a genuine good pair in the actual centered-half Y1 data, and
the existing global-norm theorem puts that pair in the canonical family.
-/

/-- Every active tube at one actual selected fine source point lies in the
common global norm family. -/
theorem actualCenteredHalfY1_activeAtFine_subset_globalNormIndexFamily
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
    (r : fineLabel) (hr : r ∈ fineLabels) :
    let D := actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT
    D.shading.activeAtPoint (D.pointAt r) ⊆
      actualGlobalNormIndexFamily fine physical globalScale globalCenter := by
  dsimp only
  intro i hi
  have hiData := (FiniteProjectedShading.mem_activeAtPoint _ _ _).mp hi
  have hgood :
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine
        physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
        globalScale globalCenter ceiling exponent threshold fineT coarseDelta
        coarseT).GoodPair i r := by
    exact ⟨hiData.1, hr, hiData.2⟩
  exact (actualCenteredHalfY1_goodPair_mem_globalNormFamilies
    base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
    hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
    coarseDelta coarseT i r hgood).1

/-- Fully actual specialization of the E2 fine-label mass selector. It has no
coarse-degree retention predicate and no extra active-fibre inclusion premise:
both are generated from the actual centered-half source. -/
theorem exists_actualCenteredHalfY1_fineSeparatedBallPair_of_E2
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
    (N : CanonicalNormNonconcentrationData iota)
    (hNfamily : N.family =
      actualGlobalNormIndexFamily fine physical globalScale globalCenter)
    (label : Int) (ballRadius : Real)
    (hfineLabels : D.fineLabels.Nonempty)
    (hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈
        projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hroom :
      automaticCanonicalNearCap N ballRadius <
        pyzE2DegreeLower label)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    Nonempty (ActualGPrimeFineSeparatedBallPairOutcome
      N D (fun _ _ => True) ballRadius (pyzE2DegreeLower label)) := by
  subst D
  apply exists_actualGPrimeFineSeparatedBallPairOutcome_of_E2
    N (actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    label ballRadius hfineLabels hcell hactive
  · intro r hr
    rw [hNfamily]
    exact actualCenteredHalfY1_activeAtFine_subset_globalNormIndexFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT r hr
  · exact hroom
  · exact hsymm
  · exact htriangle
  · exact hnearRadiusLower
  · exact hnearRadiusUpper
  · exact hballRadiusLower
  · exact hballRadiusUpper

#print axioms actualCenteredHalfY1_activeAtFine_subset_globalNormIndexFamily
#print axioms exists_actualCenteredHalfY1_fineSeparatedBallPair_of_E2

end

end FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
