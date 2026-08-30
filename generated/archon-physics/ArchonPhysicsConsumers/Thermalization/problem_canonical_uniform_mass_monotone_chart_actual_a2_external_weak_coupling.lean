import ArchonPhysics.CanonicalUniformMassMonotoneChartActualA2ExternalWeakCoupling

/-!
# Consumer: canonical fibre reduction implies the actual external-g A2 limit

This consumer keeps the model-specific fibre equality as an explicit
hypothesis and checks that it produces both the actual compact certificate
and the standard external weak-coupling limit.
-/

namespace ArchonPhysicsConsumers.Thermalization
namespace CanonicalUniformMassMonotoneChartActualA2ExternalWeakCoupling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.CanonicalUniformMassMonotoneChartActualA2ExternalWeakCoupling
open ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
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
variable (data : IncreasingUniformMassC2ChartData)
variable (fibreWeight fibreWeightDeriv : Real -> Complex)
variable (hfibreWeight : forall mass : Real,
  HasDerivAt fibreWeight (fibreWeightDeriv mass) mass)
variable (hfibreWeightDerivContinuous : Continuous fibreWeightDeriv)
variable (hreduction :
  ActualIteratedA2StaticCanonicalUniformMassFibreReduction
    ensemble channel kappa radius observed term data.chart fibreWeight)

/-- The transparent fibre equality is sufficient to manufacture the actual
compact-interval certificate. -/
example :
    ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term :=
  actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
    ensemble channel kappa radius observed term data fibreWeight
      fibreWeightDeriv hfibreWeight hfibreWeightDerivContinuous hreduction

/-- Copying the certificate preserves the exact endpoint variation cost. -/
example :
    (actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
      ensemble channel kappa radius observed term data fibreWeight
        fibreWeightDeriv hfibreWeight hfibreWeightDerivContinuous
          hreduction).variationCost =
      (compactIntervalCertificate data fibreWeight fibreWeightDeriv
        hfibreWeight hfibreWeightDerivContinuous).variationCost :=
  variationCost_actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
    ensemble channel kappa radius observed term data fibreWeight
      fibreWeightDeriv hfibreWeight hfibreWeightDerivContinuous hreduction

/-- No further A2 regularity premise is needed after the fibre reduction:
the existing compact-certificate theorem closes the external-g limit. -/
example :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualA2ExternalAccumulation_of_canonicalMassFibreReduction
    ensemble channel kappa radius observed term data fibreWeight
      fibreWeightDeriv hfibreWeight hfibreWeightDerivContinuous hreduction

#print axioms
  actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
#print axioms
  variationCost_actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
#print axioms
  tendsto_actualA2ExternalAccumulation_of_canonicalMassFibreReduction

end

end CanonicalUniformMassMonotoneChartActualA2ExternalWeakCoupling
end ArchonPhysicsConsumers.Thermalization
