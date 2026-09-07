import Family8Grounding.Family8SameSelectedQFibreCrossingDestinationV1
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Mathlib.Tactic

/-!
# Value-only transport to the literal q-fibre destination

The grounded stage argument factors into an independent scalar threshold
comparison and a concentration-value comparison.  This file supplies only
the latter.  It never mentions a stage inequality or a current-stage
barrier.

First we prove that the canonical Frostman constant is exactly invariant
when a finite family and its ambient body are transported by one affine
equivalence.  We then state the earliest honest hierarchy seam for the
q-fibre successor: an exact equivalence between the two literal raw-fibre
index types, equality of each destination body with the common affine image
of its source body, and the analogous ambient-parent equality.  Those
geometric fields imply equality, hence the required inequality, of the two
literal `actualCrossingValue`s.

The correspondence is intentionally not manufactured from carrier nesting.
The existing faithful cover proves containment and parent realization, but
not the body equalities required below.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SameSelectedQFibreCrossingValueTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8PaperFactorFiniteRunV2
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SameSelectedQFibreCrossingDestinationV1
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8SelectedParentAffineShadingTransportV4
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

universe u v

/-! ## Exact affine invariance of the canonical Frostman scalar -/

/-- Concentration of an affine-image family inside an arbitrary target body
is the source concentration inside its affine preimage. -/
theorem concentration_affineImageFamily_eq_preimage
    {index : Type u} [Fintype index]
    (e : Space ≃ᵃ[Real] Space) (F : ConvexFamily index)
    (K : ConvexBody Space) :
    concentration (affineImageFamily e F) K =
      concentration F (affinePreimageConvexBody e K) := by
  rw [concentration_eq_containedMass_div,
    concentration_eq_containedMass_div,
    containedMass_affineImageFamily,
    volume_eq_affineJacobian_mul_preimage]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos e).ne'
  · exact affineJacobian_ne_top e

/-- Supremal concentration is unchanged by a common affine equivalence. -/
theorem maximalConcentration_affineImageFamily
    {index : Type u} [Fintype index]
    (e : Space ≃ᵃ[Real] Space) (F : ConvexFamily index) :
    maximalConcentration (affineImageFamily e F) =
      maximalConcentration F := by
  apply le_antisymm
  · apply iSup_le
    intro K
    rw [concentration_affineImageFamily_eq_preimage]
    exact concentration_le_maximalConcentration F
      (affinePreimageConvexBody e K)
  · apply iSup_le
    intro K
    have himage := concentration_le_maximalConcentration
      (affineImageFamily e F) (affineImageConvexBody e K)
    rw [concentration_affineImageFamily_eq_preimage,
      affinePreimageConvexBody_affineImageConvexBody] at himage
    exact himage

/-- The canonical parent-normalized Frostman scalar is exactly affine
invariant when both the finite family and its ambient body are transported
by the same equivalence. -/
theorem canonicalFrostmanConstant_affineImage_eq
    {index : Type u} [Fintype index]
    (e : Space ≃ᵃ[Real] Space) (F : ConvexFamily index)
    (K : ConvexBody Space) :
    canonicalFrostmanConstant (affineImageFamily e F)
        (affineImageConvexBody e K) =
      canonicalFrostmanConstant F K := by
  unfold canonicalFrostmanConstant
  rw [maximalConcentration_affineImageFamily,
    volume_affineImageConvexBody, containedMass_affineImageFamily,
    affinePreimageConvexBody_affineImageConvexBody]
  calc
    maximalConcentration F *
          (affineJacobian e * volume (K : Set Space)) /
        (affineJacobian e * containedMass F K) =
      affineJacobian e *
          (maximalConcentration F * volume (K : Set Space)) /
        (affineJacobian e * containedMass F K) := by
          congr 1
          ac_rfl
    _ = maximalConcentration F * volume (K : Set Space) /
        containedMass F K := by
      apply ENNReal.mul_div_mul_left
      · exact (affineJacobian_pos e).ne'
      · exact affineJacobian_ne_top e

/-- Combine affine transport with an exact finite reindexing and literal
body equalities. -/
theorem canonicalFrostmanConstant_eq_of_affineBodyEquiv
    {sourceIndex : Type u} {targetIndex : Type v}
    [Fintype sourceIndex] [Fintype targetIndex]
    (indexEquiv : sourceIndex ≃ targetIndex)
    (e : Space ≃ᵃ[Real] Space)
    (sourceFamily : ConvexFamily sourceIndex)
    (targetFamily : ConvexFamily targetIndex)
    (sourceAmbient targetAmbient : ConvexBody Space)
    (hfamily : forall i,
      affineImageConvexBody e (sourceFamily i) =
        targetFamily (indexEquiv i))
    (hambient : affineImageConvexBody e sourceAmbient = targetAmbient) :
    canonicalFrostmanConstant sourceFamily sourceAmbient =
      canonicalFrostmanConstant targetFamily targetAmbient := by
  calc
    canonicalFrostmanConstant sourceFamily sourceAmbient =
        canonicalFrostmanConstant (affineImageFamily e sourceFamily)
          (affineImageConvexBody e sourceAmbient) :=
      (canonicalFrostmanConstant_affineImage_eq
        e sourceFamily sourceAmbient).symm
    _ = canonicalFrostmanConstant targetFamily
          (affineImageConvexBody e sourceAmbient) := by
      apply canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
        indexEquiv (affineImageFamily e sourceFamily) targetFamily
      intro i
      simpa only [affineImageFamily_apply] using hfamily i
    _ = canonicalFrostmanConstant targetFamily targetAmbient := by
      rw [hambient]

/-! ## The exact raw-fibre hierarchy seam -/

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}
  {Wsrc : FirstParentwiseNormalizedCrossingWitness
    D hD C S epsilon hepsilon eta N}
  {step : SameObjectCrossingPaperStep Wsrc}

/-- The literal source raw interval cover of the selected crossing. -/
abbrev sourceRawCrossingCover :=
  paperBufferedIntervalCover
    D hD C S epsilon hepsilon Wsrc.m Wsrc.rho Wsrc.buffered

/-- The literal raw interval cover on the definitionally same q-fresh
destination datum and faithful q-fresh hierarchy. -/
abbrev destinationRawCrossingCover
    (Y : SameSelectedQFibreCrossingDestination step) :=
  paperBufferedIntervalCover
    step.integrated.dualChild.qFibreChildDatum
    step.integrated.dualChild.qFibreChild_admissible
    Y.faithful.readiness.qFreshCover Y.destinationScales
    Y.destinationEpsilon Y.destinationEpsilon_nonneg
    Y.destination.m Y.destination.rho Y.destination.buffered

/-- Earliest honest geometry required to transport the crossing value.

The index equivalence is between the two exact active fibres named by the
source and destination crossing witnesses.  The body fields use one common
affine equivalence for every indexed member and for the ambient parent.
There is no numerical crossing-value inequality in this certificate. -/
structure QFibreRawCrossingAffineCorrespondence
    (Y : SameSelectedQFibreCrossingDestination step) where
  affineEquiv : Space ≃ᵃ[Real] Space
  fibreIndexEquiv :
    {i // i ∈ (sourceRawCrossingCover (Wsrc := Wsrc)).fiber Wsrc.q.1} ≃
      {j // j ∈ (destinationRawCrossingCover Y).fiber Y.destination.q.1}
  fibreBody_eq : forall i,
    affineImageConvexBody affineEquiv
        ((sourceRawCrossingCover (Wsrc := Wsrc)).fiberFamily Wsrc.q.1 i) =
      (destinationRawCrossingCover Y).fiberFamily Y.destination.q.1
        (fibreIndexEquiv i)
  ambientBody_eq :
    affineImageConvexBody affineEquiv
        ((sourceRawCrossingCover (Wsrc := Wsrc)).activeCoarseFamily Wsrc.q) =
      (destinationRawCrossingCover Y).activeCoarseFamily Y.destination.q

namespace QFibreRawCrossingAffineCorrespondence

variable {Y : SameSelectedQFibreCrossingDestination step}

/-- Exact equality of the two literal crossing values. -/
theorem crossingValue_eq
    (H : QFibreRawCrossingAffineCorrespondence Y) :
    actualCrossingValue Wsrc = actualCrossingValue Y.destination := by
  unfold actualCrossingValue parentNormalizedFiberCFAt
  exact canonicalFrostmanConstant_eq_of_affineBodyEquiv
    H.fibreIndexEquiv H.affineEquiv
    ((sourceRawCrossingCover (Wsrc := Wsrc)).fiberFamily Wsrc.q.1)
    ((destinationRawCrossingCover Y).fiberFamily Y.destination.q.1)
    ((sourceRawCrossingCover (Wsrc := Wsrc)).activeCoarseFamily Wsrc.q)
    ((destinationRawCrossingCover Y).activeCoarseFamily Y.destination.q)
    H.fibreBody_eq H.ambientBody_eq

/-- Value-only inequality consumed by the independent scalar-threshold
connector. -/
theorem crossingValue_le
    (H : QFibreRawCrossingAffineCorrespondence Y) :
    actualCrossingValue Wsrc <= actualCrossingValue Y.destination :=
  H.crossingValue_eq.le

end QFibreRawCrossingAffineCorrespondence

#print axioms concentration_affineImageFamily_eq_preimage
#print axioms maximalConcentration_affineImageFamily
#print axioms canonicalFrostmanConstant_affineImage_eq
#print axioms canonicalFrostmanConstant_eq_of_affineBodyEquiv
#print axioms QFibreRawCrossingAffineCorrespondence
#print axioms QFibreRawCrossingAffineCorrespondence.crossingValue_eq
#print axioms QFibreRawCrossingAffineCorrespondence.crossingValue_le

end
end Family8SameSelectedQFibreCrossingValueTransportV1
