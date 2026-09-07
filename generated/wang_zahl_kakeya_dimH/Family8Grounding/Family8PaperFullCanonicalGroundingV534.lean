import Family8Grounding.Family8PaperFullCanonicalGroundingV533
import Family8Grounding.Family8ParameterOutputEtaLongCoreOnlyMainLemmaV1
import Family8Grounding.Family8EndpointIdentityDirectNoKTMiddleGammaReducedDSOComposerV1
import Family8Grounding.Family8EndpointIdentityHighGammaLongCoreDSOV1
import Family8Grounding.Family8DividingScaleOutputTargetMonotonicityV1
import Family8Grounding.Family8EndpointIdentityFrozenComparableDensityGateV3
import Family8Grounding.Family8EndpointIdentityLongCoreSourceKatzTaoOuterScaleCountV1
import Family8Grounding.Family8ActiveFineParallelClusterKatzTaoV1

/-!
# Full canonical grounding interface checkpoint V534

This checkpoint gathers the newly validated LongCore interfaces without
claiming that their remaining premises have been discharged.

* The arbitrary-parameter wrapper reduces the actual Family8 top target to
  one `NormalizedLongIntervalCoreWitness -> DividingScaleOutput` producer;
  FirstCrossing is eliminated on the same chosen ladder.
* The gamma-reduced composer removes G3 and internalizes G4/G5, but still
  exposes the genuine G1 density and G2 base-scale callbacks.
* The high-gamma module constructs a `DividingScaleOutput` from the singleton
  endpoint fibre after explicit small-scale, exponent, G1, and G2 premises.
  Its canonical wrapper supplies only the strict high-gamma gain.
* Target-loss monotonicity permits a DSO proved with a smaller effective loss
  to be lifted to the requested loss.  It does not by itself strengthen the
  Frostman theorem supplied to the producer.
* The actual frozen-comparable density helper removes assembly dependence
  from G1, leaving an honest scalar power comparison.
* The source-Katz--Tao outer comparison and active parallel-cluster Katz--Tao
  theorem remain numerical/local inputs; neither is yet connected to an
  actual-average DSO consumer.

Consequently this is an aggregation and audit checkpoint, not an
unconditional LongCore, Family8, or submission theorem.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV534

#print axioms
  Family8ParameterOutputEtaLongCoreOnlyMainLemmaV1.mainLemmaOne_of_parameter_outputEta_longCoreOnlyDSO
#print axioms
  Family8EndpointIdentityDirectNoKTMiddleGammaReducedDSOComposerV1.nonempty_longCoreThreeScaleDSOData_of_direct_noKT_middle_gammaReduced
#print axioms
  Family8EndpointIdentityHighGammaLongCoreDSOV1.dividingScaleOutput_of_endpointIdentity_canonicalHighGamma_longCore
#print axioms
  Family8DividingScaleOutputTargetMonotonicityV1.dividingScaleOutput_mono_targetEpsilon
#print axioms
  Family8EndpointIdentityFrozenComparableDensityGateV3.target_le_density_div_actualFrozenLoss_mul_branching
#print axioms
  Family8EndpointIdentityLongCoreSourceKatzTaoOuterScaleCountV1.longIntervalKatzTaoRHSENNReal_le_endpointIdentity_outerScaleCountFactor_of_sourceKatzTaoHypotheses
#print axioms
  Family8ActiveFineParallelClusterKatzTaoV1.isKatzTao_activeSubtype_of_epsilonExtremal_clusterBound

end Family8PaperFullCanonicalGroundingV534
