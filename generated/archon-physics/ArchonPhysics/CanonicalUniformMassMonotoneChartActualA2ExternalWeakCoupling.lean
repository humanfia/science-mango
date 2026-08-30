import ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate
import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling

/-!
# Canonical uniform-mass fibre reduction for the actual external-g A2 limit

This module isolates the exact model-specific premise needed to use a
one-coordinate canonical mass chart for an actual iterated-A2 channel.  The
premise is only an equality of weighted expectations for every time.  Given
that equality and the smooth monotone-chart data, the canonical compact
Fourier certificate is copied to the actual channel and the existing
external weak-coupling limit is applied.

No fibre reduction or nonlinear eigenfrequency chart is constructed here.
Those remain explicit inputs.
-/

namespace ArchonPhysics.CanonicalUniformMassMonotoneChartActualA2ExternalWeakCoupling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter MeasureTheory Set

noncomputable section

/-- Transparent fibre-reduction premise for one actual static A2 channel.

It says exactly that, after integrating every other random input into a
one-dimensional complex fibre weight, the actual channel expectation equals
the canonical uniform single-mass expectation for every time.  It does not
assert that such a chart or fibre weight has already been derived. -/
abbrev ActualIteratedA2StaticCanonicalUniformMassFibreReduction
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (chart : Real -> Real) (fibreWeight : Real -> Complex) : Prop :=
  forall time : Real,
    actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
        radius observed term time =
      weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
        chart fibreWeight time

/-- Copy a canonical monotone-chart certificate to the actual static A2
channel using only the displayed fibre-reduction equality. -/
def actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (data : IncreasingUniformMassC2ChartData)
    (fibreWeight fibreWeightDeriv : Real -> Complex)
    (hfibreWeight : forall mass : Real,
      HasDerivAt fibreWeight (fibreWeightDeriv mass) mass)
    (hfibreWeightDerivContinuous : Continuous fibreWeightDeriv)
    (hreduction :
      ActualIteratedA2StaticCanonicalUniformMassFibreReduction
        ensemble channel kappa radius observed term data.chart fibreWeight) :
    ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term := by
  let canonicalCertificate :=
    compactIntervalCertificate data fibreWeight fibreWeightDeriv
      hfibreWeight hfibreWeightDerivContinuous
  refine
    { lower := canonicalCertificate.lower
      upper := canonicalCertificate.upper
      lower_le_upper := canonicalCertificate.lower_le_upper
      density := canonicalCertificate.density
      densityDeriv := canonicalCertificate.densityDeriv
      expectation_eq := ?_
      density_hasDeriv := canonicalCertificate.density_hasDeriv
      densityDeriv_intervalIntegrable :=
        canonicalCertificate.densityDeriv_intervalIntegrable }
  intro time
  change
    actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
        radius observed term time =
      weightedMismatchIntervalOscillatoryIntegral
        canonicalCertificate.density canonicalCertificate.lower
          canonicalCertificate.upper time
  exact (hreduction time).trans (canonicalCertificate.expectation_eq time)

/-- The copied actual certificate has exactly the canonical chart variation
cost; the fibre-reduction proof contributes no hidden analytic constant. -/
theorem variationCost_actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (data : IncreasingUniformMassC2ChartData)
    (fibreWeight fibreWeightDeriv : Real -> Complex)
    (hfibreWeight : forall mass : Real,
      HasDerivAt fibreWeight (fibreWeightDeriv mass) mass)
    (hfibreWeightDerivContinuous : Continuous fibreWeightDeriv)
    (hreduction :
      ActualIteratedA2StaticCanonicalUniformMassFibreReduction
        ensemble channel kappa radius observed term data.chart fibreWeight) :
    (actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
      ensemble channel kappa radius observed term data fibreWeight
        fibreWeightDeriv hfibreWeight hfibreWeightDerivContinuous
          hreduction).variationCost =
      (compactIntervalCertificate data fibreWeight fibreWeightDeriv
        hfibreWeight hfibreWeightDerivContinuous).variationCost :=
  rfl

/-- The standard external-g actual A2 accumulation tends to zero once the
fibre reduction and the concrete canonical monotone chart are supplied. -/
theorem
    tendsto_actualA2ExternalAccumulation_of_canonicalMassFibreReduction
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (data : IncreasingUniformMassC2ChartData)
    (fibreWeight fibreWeightDeriv : Real -> Complex)
    (hfibreWeight : forall mass : Real,
      HasDerivAt fibreWeight (fibreWeightDeriv mass) mass)
    (hfibreWeightDerivContinuous : Continuous fibreWeightDeriv)
    (hreduction :
      ActualIteratedA2StaticCanonicalUniformMassFibreReduction
        ensemble channel kappa radius observed term data.chart fibreWeight) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualIteratedA2StaticExternalWeakCouplingAccumulation_compact
    ensemble channel kappa radius observed term
      (actualCompactIntervalCertificateOfCanonicalUniformMassFibreReduction
        ensemble channel kappa radius observed term data fibreWeight
          fibreWeightDeriv hfibreWeight hfibreWeightDerivContinuous hreduction)

end

end ArchonPhysics.CanonicalUniformMassMonotoneChartActualA2ExternalWeakCoupling
