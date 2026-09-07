import Family8Grounding.Family8ContractedJohnEighthProxyAxisGapCoreV1
import Family8Grounding.Family8ContractedJohnEighthProxySelectedAncestorCenterGapV1
import Family8Grounding.Family8StickyActiveCoarseB2SupportV5
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8EighthNormalizedSelectedAncestorAxisGapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CommonPointTubePackingV1
open Family8ContractedJohnEighthProxyAxisGapCoreV1
open Family8ContractedJohnEighthProxySelectedAncestorCenterGapV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8StickyActiveCoarseB2SupportV5
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-!
# Eighth-normalized selected-ancestor axis gap

The active-parent route uses the literal same normalization on the child and
its source ancestor: both are obtained by `eighthNormalizedTube`.  Source
carrier nesting puts the source midpoints within `3 * sigma` and the source
directions within `6 * sigma`, up to sign.  Eighth dilation changes the first
bound to `3 * sigma / 8` and leaves the unit directions unchanged.  Hence the
complete normalized child axis lies in the `27 * sigma / 8` thickening of the
normalized ancestor axis.

The final statement uses a genuine buffered tube with the literal normalized
ancestor axis.  Its only extra premise is the scalar comparison between this
proved axis gap and the chosen buffer.
-/

/-- The common-point midpoint of the eighth-normalized tube is the literal
eighth dilation of the source midpoint. -/
theorem tubeAxisMidpoint_eighthNormalizedTube
    {r : NNReal} (T : Tube r) :
    Family8CommonPointTubePackingV1.tubeAxisMidpoint
        (eighthNormalizedTube T) =
      eighthDilationPoint
        (Family8CommonPointTubePackingV1.tubeAxisMidpoint T) := by
  unfold Family8CommonPointTubePackingV1.tubeAxisMidpoint
    eighthNormalizedTube eighthNormalizedAxis eighthDilationPoint
    Family8FiniteRandomRigidMotionB2NormalizationCoreV1.tubeAxisMidpoint
  simp only
  module

/-- Literal eighth normalization scales the source midpoint gap by `1/8`. -/
theorem dist_eighthNormalizedTube_midpoint_le_three_eighths
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma)
    (hTU : T.carrier ⊆ U.carrier) :
    dist (Family8CommonPointTubePackingV1.tubeAxisMidpoint
          (eighthNormalizedTube T))
        (Family8CommonPointTubePackingV1.tubeAxisMidpoint
          (eighthNormalizedTube U)) <=
      3 * (sigma : Real) / 8 := by
  have hsource :
      dist (Family8CommonPointTubePackingV1.tubeAxisMidpoint T)
          (Family8CommonPointTubePackingV1.tubeAxisMidpoint U) <=
        3 * (sigma : Real) :=
    dist_tubeAxisMidpoint_le_three_mul_of_axis_subset_carrier
      T U (T.axis_subset_carrier.trans hTU)
  rw [tubeAxisMidpoint_eighthNormalizedTube,
    tubeAxisMidpoint_eighthNormalizedTube, dist_eighthDilationPoint]
  calc
    (1 / 8 : Real) *
        dist (Family8CommonPointTubePackingV1.tubeAxisMidpoint T)
          (Family8CommonPointTubePackingV1.tubeAxisMidpoint U) <=
        (1 / 8 : Real) * (3 * (sigma : Real)) := by
      gcongr
    _ = 3 * (sigma : Real) / 8 := by ring

/-- Eighth normalization keeps source directions literally unchanged, so the
source common-segment estimate transports without loss. -/
theorem eighthNormalizedTube_unorientedDirectionClose_of_carrier_subset
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma)
    (hTU : T.carrier ⊆ U.carrier) :
    UnorientedDirectionClose
      (eighthNormalizedTube T).axis
      (eighthNormalizedTube U).axis
      (6 * (sigma : Real)) := by
  have hsource : UnorientedDirectionClose T.axis U.axis
      (6 * (sigma : Real)) :=
    UnorientedDirectionClose.symm
      (Tube.unorientedDirectionClose_of_commonSegment
        U T.axis (T.axis_subset_carrier.trans hTU))
  unfold UnorientedDirectionClose at hsource ⊢
  simpa only [eighthNormalizedTube_axis,
    eighthNormalizedAxis_direction] using hsource

/-- The canonical nonnegative axis gap for a literal eighth-normalized source
ancestor at scale `sigma`. -/
def eighthNormalizedSelectedAncestorAxisGap (sigma : NNReal) : NNReal :=
  (27 * sigma) / 8

@[simp]
theorem coe_eighthNormalizedSelectedAncestorAxisGap (sigma : NNReal) :
    (eighthNormalizedSelectedAncestorAxisGap sigma : Real) =
      27 * (sigma : Real) / 8 := by
  simp only [eighthNormalizedSelectedAncestorAxisGap,
    NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]

/-- Source carrier nesting alone produces the explicit normalized-axis
thickening; no normalized-axis inclusion is assumed. -/
theorem eighthNormalizedTube_axis_subset_selectedAncestorGap
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma)
    (hTU : T.carrier ⊆ U.carrier) :
    (eighthNormalizedTube T).axis.carrier ⊆
      Metric.cthickening
        (eighthNormalizedSelectedAncestorAxisGap sigma : Real)
        (eighthNormalizedTube U).axis.carrier := by
  apply
    Family8ContractedJohnEighthProxyAxisGapCoreV1.Tube.axis_carrier_subset_cthickening_of_midpoint_unorientedDirectionClose
      (eighthNormalizedTube T) (eighthNormalizedTube U)
      (dist_eighthNormalizedTube_midpoint_le_three_eighths T U hTU)
      (eighthNormalizedTube_unorientedDirectionClose_of_carrier_subset
        T U hTU)
  rw [coe_eighthNormalizedSelectedAncestorAxisGap]
  ring_nf
  exact le_rfl

/-- A genuine containing tube which keeps the literal normalized ancestor
axis and adds only the displayed nonnegative buffer to its radius. -/
def eighthNormalizedContainingTube
    {sigma : NNReal} (U : Tube sigma) (buffer : NNReal) :
    Tube (sigma / 8 + buffer) :=
  (eighthNormalizedTube U).buffer buffer

@[simp]
theorem eighthNormalizedContainingTube_axis
    {sigma : NNReal} (U : Tube sigma) (buffer : NNReal) :
    (eighthNormalizedContainingTube U buffer).axis =
      (eighthNormalizedTube U).axis :=
  rfl

/-- An eighth-normalized child lies in a buffered normalized ancestor once
the explicit axis-gap/radius budget closes. -/
theorem eighthNormalizedTube_subset_containingTube_of_axisGap
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma)
    (axisGap buffer : NNReal)
    (haxis :
      (eighthNormalizedTube T).axis.carrier ⊆
        Metric.cthickening (axisGap : Real)
          (eighthNormalizedTube U).axis.carrier)
    (hbudget : rho / 8 + axisGap <= sigma / 8 + buffer) :
    (eighthNormalizedTube T).carrier ⊆
      (eighthNormalizedContainingTube U buffer).carrier := by
  change
    Metric.cthickening (((rho / 8 : NNReal)) : Real)
        (eighthNormalizedTube T).axis.carrier ⊆
      Metric.cthickening ((((sigma / 8 + buffer : NNReal))) : Real)
        (eighthNormalizedTube U).axis.carrier
  have hthicken := Metric.cthickening_subset_of_subset
    (((rho / 8 : NNReal)) : Real) haxis
  rw [cthickening_cthickening (by positivity) (by positivity)] at hthicken
  exact hthicken.trans
    (Metric.cthickening_mono (by exact_mod_cast hbudget)
      (eighthNormalizedTube U).axis.carrier)

/-- Source nesting and the scalar buffer comparison produce full containment
of the literal eighth-normalized tubes. -/
theorem eighthNormalizedTube_subset_selectedAncestorContainingTube
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma)
    (hRhoSigma : rho <= sigma) (hTU : T.carrier ⊆ U.carrier)
    (buffer : NNReal)
    (haxisGapBuffer :
      eighthNormalizedSelectedAncestorAxisGap sigma <= buffer) :
    (eighthNormalizedTube T).carrier ⊆
      (eighthNormalizedContainingTube U buffer).carrier := by
  apply eighthNormalizedTube_subset_containingTube_of_axisGap
    T U (eighthNormalizedSelectedAncestorAxisGap sigma) buffer
      (eighthNormalizedTube_axis_subset_selectedAncestorGap T U hTU)
  exact add_le_add (by gcongr) haxisGapBuffer

/-- Complete positive ledger for one active-route normalized ancestor step. -/
structure EighthNormalizedSelectedAncestorBufferedStep
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma)
    (buffer : NNReal) : Prop where
  source_scale_le : rho <= sigma
  source_carrier_subset : T.carrier ⊆ U.carrier
  normalized_direction_close :
    UnorientedDirectionClose
      (eighthNormalizedTube T).axis
      (eighthNormalizedTube U).axis
      (6 * (sigma : Real))
  normalized_axis_subset_gap :
    (eighthNormalizedTube T).axis.carrier ⊆
      Metric.cthickening
        (eighthNormalizedSelectedAncestorAxisGap sigma : Real)
        (eighthNormalizedTube U).axis.carrier
  actual_normalized_subset_buffered_parent :
    (eighthNormalizedTube T).carrier ⊆
      (eighthNormalizedContainingTube U buffer).carrier

/-- Producer for the complete active-route ledger.  Its only premise beyond
the source hierarchy is the scalar axis-gap-to-buffer comparison. -/
theorem eighthNormalizedSelectedAncestorBufferedStep_of_source
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma)
    (buffer : NNReal) (hRhoSigma : rho <= sigma)
    (hTU : T.carrier ⊆ U.carrier)
    (haxisGapBuffer :
      eighthNormalizedSelectedAncestorAxisGap sigma <= buffer) :
    EighthNormalizedSelectedAncestorBufferedStep T U buffer where
  source_scale_le := hRhoSigma
  source_carrier_subset := hTU
  normalized_direction_close :=
    eighthNormalizedTube_unorientedDirectionClose_of_carrier_subset T U hTU
  normalized_axis_subset_gap :=
    eighthNormalizedTube_axis_subset_selectedAncestorGap T U hTU
  actual_normalized_subset_buffered_parent :=
    eighthNormalizedTube_subset_selectedAncestorContainingTube
      T U hRhoSigma hTU buffer haxisGapBuffer

#print axioms tubeAxisMidpoint_eighthNormalizedTube
#print axioms dist_eighthNormalizedTube_midpoint_le_three_eighths
#print axioms eighthNormalizedTube_unorientedDirectionClose_of_carrier_subset
#print axioms eighthNormalizedSelectedAncestorAxisGap
#print axioms eighthNormalizedTube_axis_subset_selectedAncestorGap
#print axioms eighthNormalizedContainingTube
#print axioms eighthNormalizedTube_subset_containingTube_of_axisGap
#print axioms eighthNormalizedTube_subset_selectedAncestorContainingTube
#print axioms EighthNormalizedSelectedAncestorBufferedStep
#print axioms eighthNormalizedSelectedAncestorBufferedStep_of_source

end
end Family8EighthNormalizedSelectedAncestorAxisGapV1
