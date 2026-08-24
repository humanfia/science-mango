import FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
import Submission.Kakeya.Uniformity.TubeFamily
import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

/-!
# Measurable two-dimensional projected tube carriers

This is the clean two-dimensional source geometry behind the cinematic
incidence pattern.  Its graph is the literal twisted-projection trace
a + c t + f(t)(b + d t), and its carrier is a vertical neighbourhood over a
measurable parameter domain.  Continuity of f proves every fixed carrier
measurable; no arbitrary point-to-Finset measurability field appears.
-/

open LeanEval.Analysis.WangZahlKakeya

/-- Clean WZ twisted projection pi_f(x,y,z) = (x+f(z)y,z). -/
def projectedTwistedProjection
    (f : Real → Real) (p : Space) : Real × Real :=
  (p 0 + f (p 2) * p 1, p 2)

theorem continuous_projectedTwistedProjection
    (f : Real → Real) (hf : Continuous f) :
    Continuous (projectedTwistedProjection f) := by
  unfold projectedTwistedProjection
  fun_prop

/-- Exact two-dimensional image of one full actual tube carrier. -/
def projectedTubeImageCarrier
    {delta : NNReal} (f : Real → Real) (T : Tube delta) :
    Set (Real × Real) :=
  Set.image (projectedTwistedProjection f) T.carrier

theorem isCompact_projectedTubeImageCarrier
    {delta : NNReal} (f : Real → Real) (hf : Continuous f)
    (T : Tube delta) :
    IsCompact (projectedTubeImageCarrier f T) :=
  T.isCompact_carrier.image (continuous_projectedTwistedProjection f hf)

theorem measurableSet_projectedTubeImageCarrier
    {delta : NNReal} (f : Real → Real) (hf : Continuous f)
    (T : Tube delta) :
    MeasurableSet (projectedTubeImageCarrier f T) :=
  (isCompact_projectedTubeImageCarrier f hf T).measurableSet

/-- Literal first coordinate of the twisted projection of the axis of T. -/
def projectedTubeCinematicTrace
    {delta : NNReal} (f : Real → Real) (T : Tube delta) (t : Real) : Real :=
  projectedTubeGraphA T + projectedTubeGraphC T * t +
    f t * (projectedTubeGraphB T + projectedTubeGraphD T * t)

theorem continuous_projectedTubeCinematicTrace
    {delta : NNReal} (f : Real → Real) (hf : Continuous f)
    (T : Tube delta) :
    Continuous (projectedTubeCinematicTrace f T) := by
  unfold projectedTubeCinematicTrace
  fun_prop

/-- Height of the standard unit-axis parameter. -/
def projectedTubeAxisHeight
    {delta : NNReal} (T : Tube delta) (s : Real) : Real :=
  T.axis.base 2 + s * T.axis.direction 2

/-- Exact provenance: the clean twisted projection of every axis point is the
point on the literal cinematic trace at the same height. -/
theorem projectedTwistedProjection_axisPoint_eq_trace
    {delta : NNReal} (f : Real → Real) (T : Tube delta)
    (hvertical : T.axis.direction 2 ≠ 0) (s : Real) :
    projectedTwistedProjection f
        (T.axis.base + s • T.axis.direction) =
      (projectedTubeCinematicTrace f T (projectedTubeAxisHeight T s),
        projectedTubeAxisHeight T s) := by
  apply Prod.ext
  · simp [projectedTwistedProjection, projectedTubeCinematicTrace,
      projectedTubeAxisHeight, projectedTubeGraphA, projectedTubeGraphB,
      projectedTubeGraphC, projectedTubeGraphD]
    field_simp
    ring
  · simp [projectedTwistedProjection, projectedTubeAxisHeight]

/-- The projected delta-carrier in coordinate order (value, parameter). -/
def projectedTubeVerticalCarrier
    {delta : NNReal} (f : Real → Real) (I : Set Real) (R : Real)
    (T : Tube delta) : Set (Real × Real) :=
  {q | q.2 ∈ I ∧
    |q.1 - projectedTubeCinematicTrace f T q.2| ≤ R}

theorem mem_projectedTubeVerticalCarrier
    {delta : NNReal} (f : Real → Real) (I : Set Real) (R : Real)
    (T : Tube delta) (q : Real × Real) :
    q ∈ projectedTubeVerticalCarrier f I R T ↔
      q.2 ∈ I ∧ |q.1 - projectedTubeCinematicTrace f T q.2| ≤ R :=
  Iff.rfl

theorem measurableSet_projectedTubeVerticalCarrier
    {delta : NNReal} (f : Real → Real) (hf : Continuous f)
    (I : Set Real) (hI : MeasurableSet I) (R : Real)
    (T : Tube delta) :
    MeasurableSet (projectedTubeVerticalCarrier f I R T) := by
  have hbase : MeasurableSet {q : Real × Real | q.2 ∈ I} :=
    measurable_snd hI
  have htrace : Measurable (fun q : Real × Real =>
      projectedTubeCinematicTrace f T q.2) :=
    (continuous_projectedTubeCinematicTrace f hf T).measurable.comp
      measurable_snd
  have herror : Measurable (fun q : Real × Real =>
      |q.1 - projectedTubeCinematicTrace f T q.2|) :=
    (measurable_fst.sub htrace).abs
  exact hbase.inter (measurableSet_le herror measurable_const)

/-- The exact projected images of a finite full actual tube family form a
measurable projected shading. -/
noncomputable def finiteProjectedTubeImageShading
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (ambient : Finset iota)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hf : Continuous f) :
    FiniteProjectedShading (Real × Real) iota where
  ambient := ambient
  base := base
  carrier := fun i => projectedTubeImageCarrier f (fine.tubes i)
  measurable_base := hbase
  measurable_carrier := by
    intro i _hi
    exact measurableSet_projectedTubeImageCarrier f hf (fine.tubes i)

/-- A finite actual tube family gives the projected-shading structure used by
the continuum multiplicity and critical-scale certificate. -/
noncomputable def finiteProjectedTubeShading
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (ambient : Finset iota)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hf : Continuous f)
    (I : Set Real) (hI : MeasurableSet I) (R : Real) :
    FiniteProjectedShading (Real × Real) iota where
  ambient := ambient
  base := base
  carrier := fun i => projectedTubeVerticalCarrier f I R (fine.tubes i)
  measurable_base := hbase
  measurable_carrier := by
    intro i _hi
    exact measurableSet_projectedTubeVerticalCarrier f hf I hI R
      (fine.tubes i)

/-- Its active family is definitionally the literal projected-incidence
filter. -/
theorem activeAtPoint_finiteProjectedTubeShading
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (ambient : Finset iota)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hf : Continuous f)
    (I : Set Real) (hI : MeasurableSet I) (R : Real)
    (q : Real × Real) :
    (finiteProjectedTubeShading fine ambient base hbase f hf I hI R).activeAtPoint q =
      finiteIncidenceActiveAtPoint ambient
        (fun i q => q ∈ projectedTubeVerticalCarrier f I R (fine.tubes i)) q :=
  rfl

#print axioms projectedTwistedProjection
#print axioms continuous_projectedTwistedProjection
#print axioms projectedTubeImageCarrier
#print axioms measurableSet_projectedTubeImageCarrier
#print axioms finiteProjectedTubeImageShading
#print axioms projectedTubeCinematicTrace
#print axioms continuous_projectedTubeCinematicTrace
#print axioms projectedTubeAxisHeight
#print axioms projectedTwistedProjection_axisPoint_eq_trace
#print axioms projectedTubeVerticalCarrier
#print axioms measurableSet_projectedTubeVerticalCarrier
#print axioms finiteProjectedTubeShading
#print axioms activeAtPoint_finiteProjectedTubeShading

end

end FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
