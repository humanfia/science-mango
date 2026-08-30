import ArchonPhysics.LocalNonzeroJacobianQuantitativePatch
import ArchonPhysics.ParametricJacobianLinearSmallBall

/-!
# Local parametric Jacobian-to-small-ball pipeline

This module composes local inverse-function regularity with the quantitative
area formula and the bounded-environment slab estimate.  Once an actual
augmented spectral chart supplies a continuous true derivative field and one
invertible base derivative, the theorem below returns a concrete local patch
whose mismatch marginal obeys a linear small-ball bound.
-/

namespace ArchonPhysics.LocalParametricJacobianSmallBallPipeline

open ArchonPhysics
open ArchonPhysics.LocalNonzeroJacobianQuantitativePatch
open ArchonPhysics.ParametricJacobianLinearSmallBall
open ArchonPhysics.ParametricLiftedMismatchSmallBall
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

variable {Environment : Type*} [NormedAddCommGroup Environment]
  [NormedSpace Real Environment] [CompleteSpace Environment]
  [FiniteDimensional Real Environment] [MeasurableSpace Environment]
  [BorelSpace Environment]

local instance massTripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Complete local route from one regular augmented Jacobian point to a
linear mismatch small-ball estimate with all environment coordinates kept. -/
theorem exists_localPatch_parametricMismatch_smallBall
    (nu : Measure Environment) [Measure.IsAddHaarMeasure nu]
    {point : MassTriple × Environment}
    {chart : MassTriple × Environment → MassTriple × Environment}
    (hchart : Measurable chart)
    {baseDerivative : (MassTriple × Environment) →L[Real]
      (MassTriple × Environment)}
    (hstrict : HasStrictFDerivAt chart baseDerivative point)
    (hinvertible : baseDerivative.IsInvertible)
    (derivativeField : MassTriple × Environment →
      (MassTriple × Environment) →L[Real]
        (MassTriple × Environment))
    (hfieldAt : derivativeField point = baseDerivative)
    (hfieldContinuous : ContinuousAt derivativeField point)
    {regularity neighborhood : Set (MassTriple × Environment)}
    (hregularity : regularity ∈ nhds point)
    (hneighborhood : neighborhood ∈ nhds point)
    (hderivative : ∀ nearby ∈ regularity,
      HasFDerivAt chart (derivativeField nearby) nearby)
    (ceiling : Real) {environmentPatch : Set Environment}
    (henvironmentPatch : MeasurableSet environmentPatch)
    (himageNeighborhood : chart '' neighborhood ⊆
      parametricLiftedCylinder ceiling environmentPatch) :
    ∃ patch : Set (MassTriple × Environment), ∃ detLower : Real,
      IsOpen patch ∧ point ∈ patch ∧
      patch ⊆ regularity ∧ patch ⊆ neighborhood ∧
      0 < detLower ∧
      (∀ delta : Real, 0 ≤ delta →
        Measure.map parametricMismatch
            (Measure.map chart
              (((volume : Measure MassTriple).prod nu).restrict patch))
            (absoluteMismatchSublevel delta) ≤
          (ENNReal.ofReal detLower)⁻¹ *
              (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
            ENNReal.ofReal (2 * delta) * nu environmentPatch) := by
  obtain ⟨patch, detLower, hpatchOpen, hpointPatch, hpatchRegular,
      hpatchNeighborhood, hdetLower, hinjective, _himageOpen,
      hderivativeWithin, hdet⟩ :=
    exists_open_injective_detLower_patch hstrict hinvertible derivativeField
      hfieldAt hfieldContinuous hregularity hneighborhood hderivative
  refine ⟨patch, detLower, hpatchOpen, hpointPatch, hpatchRegular,
    hpatchNeighborhood, hdetLower, ?_⟩
  intro delta hdelta
  apply map_restrict_parametricMismatch_smallBall_le_of_detLower
    nu hpatchOpen.measurableSet chart hchart derivativeField hderivativeWithin
      hinjective hdetLower hdet ceiling henvironmentPatch
  · intro imagePoint himagePoint
    obtain ⟨sourcePoint, hsourcePoint, rfl⟩ := himagePoint
    exact himageNeighborhood ⟨sourcePoint, hpatchNeighborhood hsourcePoint, rfl⟩
  · exact hdelta

end

end ArchonPhysics.LocalParametricJacobianSmallBallPipeline
