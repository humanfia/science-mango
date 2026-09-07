import Family8Grounding.Family8Family7CoordinateToVerticalFamilyV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8Family7CoordinateToVerticalTubeTransportV1
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Family8Grounding.Family8StickyActiveCoarseB2SupportV5
import Mathlib.Tactic

/-!
# B2 support for the active lower family at a FirstCrossing interval, V7

V4 used an explicit index transport whose membership proof retained a hidden
cast and is not imported.  This successor keeps the literal buffered-lower
index shared by the source-to-`tau` cover.
The active fine indices of the buffered interval are literally the active
coarse indices of the source-to-`tau` cover.  Thus the sticky-parent B2
support theorem applies before the Family7 coordinate permutation, and the
permutation preserves the same centered ball exactly.  V1 had a namespace
spelling error and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal

namespace Family8Family7FirstCrossingBufferedLowerActiveB2SupportV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8StickyActiveCoarseB2SupportV5
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

/-- Every active lower-family tube of a buffered interval is supported in
`B(0,2)` once its lower scale is at most `1/16`. -/
theorem bufferedLowerFamily_activeFine_carrier_subset_closedBall_two
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho)
    (htauSixteenth : S.tau m ≤ (1 / 16 : NNReal))
    (i : bufferedLowerIndex D C S m)
    (hi : i ∈ (bufferedIntervalCover
      D hD C S epsilon hepsilon m rho hbuffered).activeFine) :
    ((bufferedLowerFamily D C S m).tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 2 := by
  have hiSource := hi
  rw [bufferedIntervalCover_activeFine] at hiSource
  let k : {k // k ∈ (sourceTauCover D C S m).activeCoarse} :=
    ⟨i, hiSource⟩
  have hsupport :=
    activeCoarseFamily_body_subset_closedBall_two
      D hD (sourceTauCover D C S m) htauSixteenth k
  simpa only [k, sourceTauCover, bufferedLowerFamily,
    StickyScaleCover.activeCoarseFamily,
    UniformTubeFamily.bodyFamily, Tube.coe_body] using hsupport

/-- The same pointwise B2 support survives the exact Family7 coordinate
permutation. -/
theorem coordinateToVertical_bufferedLowerFamily_activeFine_carrier_subset_closedBall_two
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho)
    (htauSixteenth : S.tau m ≤ (1 / 16 : NNReal))
    (axis : Fin 3)
    (i : bufferedLowerIndex D C S m)
    (hi : i ∈ (bufferedIntervalCover
      D hD C S epsilon hepsilon m rho hbuffered).activeFine) :
    (((coordinateToVerticalFamily axis
      (bufferedLowerFamily D C S m)).tubes i).carrier) ⊆
        Metric.closedBall (0 : Space) 2 := by
  have hB2 := bufferedLowerFamily_activeFine_carrier_subset_closedBall_two
    D hD C S epsilon hepsilon m rho hbuffered htauSixteenth i hi
  intro _x hx
  rw [coordinateToVerticalFamily_tubes,
    rigidTube_coordinateToVertical_carrier] at hx
  obtain ⟨x, hxTube, rfl⟩ := hx
  have hxBall := hB2 hxTube
  rw [Metric.mem_closedBall] at hxBall ⊢
  calc
    dist (coordinateToVerticalRigidMotion axis x) 0 =
        dist (coordinateToVerticalRigidMotion axis x)
          (coordinateToVerticalRigidMotion axis 0) := by
      rw [coordinateToVerticalRigidMotion_zero]
    _ = dist x 0 :=
      (coordinateToVerticalRigidMotion axis).isometry.dist_eq x 0
    _ ≤ 2 := hxBall

/-- Any literal subtype of the interval's active lower indices inherits the
coordinate-family B2 support needed by the scale-support normalizer. -/
theorem coordinateToVertical_bufferedLowerFamily_restrictTo_carrier_subset_closedBall_two
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho)
    (htauSixteenth : S.tau m ≤ (1 / 16 : NNReal))
    (axis : Fin 3)
    (selected : Finset (bufferedLowerIndex D C S m))
    (hselected : selected ⊆ (bufferedIntervalCover
      D hD C S epsilon hepsilon m rho hbuffered).activeFine) :
    ∀ i,
      (((coordinateToVerticalFamily axis
        (bufferedLowerFamily D C S m)).restrictTo selected).tubes i).carrier ⊆
          Metric.closedBall (0 : Space) 2 := by
  intro i
  change (((coordinateToVerticalFamily axis
    (bufferedLowerFamily D C S m)).tubes i.1).carrier) ⊆ _
  exact
    coordinateToVertical_bufferedLowerFamily_activeFine_carrier_subset_closedBall_two
      D hD C S epsilon hepsilon m rho hbuffered htauSixteenth
        axis i.1 (hselected i.2)

#print axioms
  bufferedLowerFamily_activeFine_carrier_subset_closedBall_two
#print axioms
  coordinateToVertical_bufferedLowerFamily_activeFine_carrier_subset_closedBall_two
#print axioms
  coordinateToVertical_bufferedLowerFamily_restrictTo_carrier_subset_closedBall_two

end
end Family8Family7FirstCrossingBufferedLowerActiveB2SupportV7
