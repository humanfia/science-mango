import ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate

/-! Consumer for the fixed-volume unweighted-law AC to weighted `L1` bridge. -/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeakCouplingQualitativeFourierKineticScale
open ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate
open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

example {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) (hmismatch : Measurable mismatch)
    (hweightMeasurable : Measurable weight) (hweight : Integrable weight measure)
    (hunweighted : Measure.map mismatch measure ≪ volume) :
    WeightedMismatchL1FourierCertificate measure mismatch weight :=
  weightedMismatchL1FourierCertificate_of_map_absolutelyContinuous
    measure mismatch weight hmismatch hweightMeasurable hweight hunweighted

example {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) (hmismatch : Measurable mismatch)
    (hweightMeasurable : Measurable weight) (hweight : Integrable weight measure)
    (constant : ENNReal)
    (hunweighted : Measure.map mismatch measure <=
      constant • (volume : Measure Real)) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  (weightedMismatchL1FourierCertificate_of_map_le_smul_volume
    measure mismatch weight hmismatch hweightMeasurable hweight constant
      hunweighted).tendsto_kineticAccumulation

#print axioms integrable_weightedMismatchRNDensity
#print axioms integral_test_mul_real_eq_integral_realWeightedMismatchRNDensity
#print axioms
  weightedMismatchL1FourierCertificate_of_map_absolutelyContinuous
#print axioms weightedMismatchL1FourierCertificate_of_map_le_smul_volume

end

end ArchonPhysicsConsumers.Thermalization
