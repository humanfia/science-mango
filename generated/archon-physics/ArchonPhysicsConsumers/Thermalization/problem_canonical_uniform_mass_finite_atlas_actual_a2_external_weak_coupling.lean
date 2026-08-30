import ArchonPhysics.CanonicalUniformMassFiniteAtlasActualA2ExternalWeakCoupling

/-!
# Consumer: fixed canonical finite atlas implies the actual external-g A2 limit

The model-specific finite-atlas reduction remains an explicit hypothesis.
This file checks both the general compact-certificate family and its
canonical monotone-chart specialization.
-/

namespace ArchonPhysicsConsumers.Thermalization
namespace CanonicalUniformMassFiniteAtlasActualA2ExternalWeakCoupling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.CanonicalUniformMassFiniteAtlasActualA2ExternalWeakCoupling
open ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open ArchonPhysics.WeightedMismatchFiniteChartKineticClosure
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
variable (ensemble : IIDMassPhaseEnsemble Omega)
variable {N : Nat} [NeZero N]
variable (channel : IteratedA2MismatchChannel)
variable (kappa : Real)
variable (radius : Omega -> Lattice.Site N -> Real)
variable (observed : Lattice.Site N)
variable (term : IteratedQuadraticSecondPicardCharacterTerm N)
variable (ChartIndex : Type*) [Fintype ChartIndex]

section GeneralCompactAtlas

variable (chartMismatch : ChartIndex -> Real -> Real)
variable (chartWeight : ChartIndex -> Real -> Complex)
variable (chartCertificate : forall index : ChartIndex,
  WeightedMismatchCompactIntervalFourierCertificate
    RandomEnsemble.massCoordinateLaw
      (chartMismatch index) (chartWeight index))
variable (hreduction :
  ActualA2StaticCanonicalFiniteAtlasReduction ensemble channel kappa radius
    observed term ChartIndex chartMismatch chartWeight)

/-- The finite family of compact certificates becomes the actual
finite-chart certificate. -/
example :
    ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term ChartIndex :=
  actualA2FiniteChartCertificateOfCompactAtlas ensemble channel kappa radius
    observed term ChartIndex chartMismatch chartWeight chartCertificate
      hreduction

/-- The total actual variation cost is exactly the finite chartwise sum. -/
example :
    (actualA2FiniteChartCertificateOfCompactAtlas ensemble channel kappa radius
      observed term ChartIndex chartMismatch chartWeight chartCertificate
        hreduction).variationCost =
      Finset.univ.sum fun index : ChartIndex =>
        (chartCertificate index).variationCost :=
  variationCost_actualA2FiniteChartCertificateOfCompactAtlas ensemble channel
    kappa radius observed term ChartIndex chartMismatch chartWeight
      chartCertificate hreduction

/-- The standard external-g limit follows with no extra analytic premise. -/
example :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualA2ExternalAccumulation_of_compactAtlas ensemble channel kappa
    radius observed term ChartIndex chartMismatch chartWeight
      chartCertificate hreduction

end GeneralCompactAtlas

section MonotoneAtlas

variable (data : ChartIndex -> IncreasingUniformMassC2ChartData)
variable (fibreWeight fibreWeightDeriv : ChartIndex -> Real -> Complex)
variable (hfibreWeight : forall index mass,
  HasDerivAt (fibreWeight index) (fibreWeightDeriv index mass) mass)
variable (hfibreWeightDerivContinuous : forall index,
  Continuous (fibreWeightDeriv index))
variable (hmonotoneReduction :
  ActualA2StaticCanonicalMonotoneAtlasReduction ensemble channel kappa radius
    observed term ChartIndex data fibreWeight)

/-- Applying the single-chart constructor chartwise produces the actual
finite-chart certificate. -/
example :
    ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term ChartIndex :=
  actualA2FiniteChartCertificateOfMonotoneAtlas ensemble channel kappa radius
    observed term ChartIndex data fibreWeight fibreWeightDeriv hfibreWeight
      hfibreWeightDerivContinuous hmonotoneReduction

/-- The specialization preserves the exact sum of canonical variation
costs. -/
example :
    (actualA2FiniteChartCertificateOfMonotoneAtlas ensemble channel kappa
      radius observed term ChartIndex data fibreWeight fibreWeightDeriv
        hfibreWeight hfibreWeightDerivContinuous
          hmonotoneReduction).variationCost =
      Finset.univ.sum fun index : ChartIndex =>
        (compactIntervalCertificate (data index) (fibreWeight index)
          (fibreWeightDeriv index) (hfibreWeight index)
            (hfibreWeightDerivContinuous index)).variationCost :=
  variationCost_actualA2FiniteChartCertificateOfMonotoneAtlas ensemble channel
    kappa radius observed term ChartIndex data fibreWeight fibreWeightDeriv
      hfibreWeight hfibreWeightDerivContinuous hmonotoneReduction

/-- Fixed finite monotone atlases close the standard external-g limit. -/
example :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualA2ExternalAccumulation_of_monotoneAtlas ensemble channel kappa
    radius observed term ChartIndex data fibreWeight fibreWeightDeriv
      hfibreWeight hfibreWeightDerivContinuous hmonotoneReduction

end MonotoneAtlas

#print axioms compactMismatchChartOfCertificate
#print axioms actualA2FiniteChartCertificateOfCompactAtlas
#print axioms variationCost_actualA2FiniteChartCertificateOfCompactAtlas
#print axioms tendsto_actualA2ExternalAccumulation_of_compactAtlas
#print axioms actualA2FiniteChartCertificateOfMonotoneAtlas
#print axioms variationCost_actualA2FiniteChartCertificateOfMonotoneAtlas
#print axioms tendsto_actualA2ExternalAccumulation_of_monotoneAtlas

end

end CanonicalUniformMassFiniteAtlasActualA2ExternalWeakCoupling
end ArchonPhysicsConsumers.Thermalization
