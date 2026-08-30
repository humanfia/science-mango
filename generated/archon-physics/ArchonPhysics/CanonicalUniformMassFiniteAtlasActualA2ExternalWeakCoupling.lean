import ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate
import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling

/-!
# Canonical finite compact atlases for the actual external-g A2 limit

A single mass coordinate need not give one globally monotone spectral chart.
This module assembles a fixed finite atlas.  Each chart is supplied by an
existing compact-interval Fourier certificate.  A transparent reduction
premise states that the actual fixed-kappa A2 expectation is the finite sum
of the corresponding canonical uniform-mass expectations.

The reduction premise, the existence of a finite spectral cover, and any
uniform-in-volume control of the summed costs remain model-specific inputs.
-/

namespace ArchonPhysics
namespace CanonicalUniformMassFiniteAtlasActualA2ExternalWeakCoupling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open ArchonPhysics.WeightedMismatchFiniteChartKineticClosure
open Filter MeasureTheory Set

noncomputable section

/-! ## A compact certificate as one atlas chart -/

/-- Forget only the ambient expectation representation and retain the
compact C1 interval data needed by a finite atlas. -/
def compactMismatchChartOfCertificate
    {Sample : Type*} [MeasurableSpace Sample]
    {measure : Measure Sample} {mismatch : Sample -> Real}
    {weight : Sample -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    CompactMismatchFourierChart where
  lower := certificate.lower
  upper := certificate.upper
  lower_le_upper := certificate.lower_le_upper
  density := certificate.density
  densityDeriv := certificate.densityDeriv
  density_hasDeriv := certificate.density_hasDeriv
  densityDeriv_intervalIntegrable :=
    certificate.densityDeriv_intervalIntegrable

@[simp] theorem oscillation_compactMismatchChartOfCertificate
    {Sample : Type*} [MeasurableSpace Sample]
    {measure : Measure Sample} {mismatch : Sample -> Real}
    {weight : Sample -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) (time : Real) :
    (compactMismatchChartOfCertificate certificate).oscillation time =
      weightedMismatchIntervalOscillatoryIntegral certificate.density
        certificate.lower certificate.upper time :=
  rfl

@[simp] theorem variationCost_compactMismatchChartOfCertificate
    {Sample : Type*} [MeasurableSpace Sample]
    {measure : Measure Sample} {mismatch : Sample -> Real}
    {weight : Sample -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    (compactMismatchChartOfCertificate certificate).variationCost =
      certificate.variationCost :=
  rfl

/-! ## General canonical compact-certificate atlas -/

/-- Transparent fixed-atlas reduction premise.

For every time, the actual static A2 expectation must equal the finite sum
of canonical uniform single-mass expectations represented by the supplied
chart mismatches and weights.  No disintegration or cover theorem is hidden
inside this abbreviation. -/
abbrev ActualA2StaticCanonicalFiniteAtlasReduction
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (chartMismatch : ChartIndex -> Real -> Real)
    (chartWeight : ChartIndex -> Real -> Complex) : Prop :=
  forall time : Real,
    actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
        radius observed term time =
      Finset.univ.sum fun index : ChartIndex =>
        weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
          (chartMismatch index) (chartWeight index) time

/-- A finite family of canonical compact certificates, plus the transparent
reduction equality, gives the actual finite-chart certificate. -/
def actualA2FiniteChartCertificateOfCompactAtlas
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (chartMismatch : ChartIndex -> Real -> Real)
    (chartWeight : ChartIndex -> Real -> Complex)
    (chartCertificate : forall index : ChartIndex,
      WeightedMismatchCompactIntervalFourierCertificate
        RandomEnsemble.massCoordinateLaw
          (chartMismatch index) (chartWeight index))
    (hreduction :
      ActualA2StaticCanonicalFiniteAtlasReduction ensemble channel kappa
        radius observed term ChartIndex chartMismatch chartWeight) :
    ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term ChartIndex := by
  classical
  refine
    { chart := fun index =>
        compactMismatchChartOfCertificate (chartCertificate index)
      expectation_eq := ?_ }
  intro time
  change
    actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
        radius observed term time =
      Finset.univ.sum fun index : ChartIndex =>
        (compactMismatchChartOfCertificate
          (chartCertificate index)).oscillation time
  calc
    actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
          radius observed term time =
        Finset.univ.sum fun index : ChartIndex =>
          weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
            (chartMismatch index) (chartWeight index) time :=
      hreduction time
    _ = Finset.univ.sum fun index : ChartIndex =>
        (compactMismatchChartOfCertificate
          (chartCertificate index)).oscillation time := by
      apply Finset.sum_congr rfl
      intro index _hindex
      exact (chartCertificate index).expectation_eq time

/-- The assembled actual variation cost is exactly the sum of the supplied
compact-certificate costs. -/
theorem variationCost_actualA2FiniteChartCertificateOfCompactAtlas
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (chartMismatch : ChartIndex -> Real -> Real)
    (chartWeight : ChartIndex -> Real -> Complex)
    (chartCertificate : forall index : ChartIndex,
      WeightedMismatchCompactIntervalFourierCertificate
        RandomEnsemble.massCoordinateLaw
          (chartMismatch index) (chartWeight index))
    (hreduction :
      ActualA2StaticCanonicalFiniteAtlasReduction ensemble channel kappa
        radius observed term ChartIndex chartMismatch chartWeight) :
    (actualA2FiniteChartCertificateOfCompactAtlas ensemble channel kappa radius
      observed term ChartIndex chartMismatch chartWeight chartCertificate
        hreduction).variationCost =
      Finset.univ.sum fun index : ChartIndex =>
        (chartCertificate index).variationCost := by
  classical
  rfl

/-- Standard external-g convergence for the fixed finite compact atlas. -/
theorem tendsto_actualA2ExternalAccumulation_of_compactAtlas
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (chartMismatch : ChartIndex -> Real -> Real)
    (chartWeight : ChartIndex -> Real -> Complex)
    (chartCertificate : forall index : ChartIndex,
      WeightedMismatchCompactIntervalFourierCertificate
        RandomEnsemble.massCoordinateLaw
          (chartMismatch index) (chartWeight index))
    (hreduction :
      ActualA2StaticCanonicalFiniteAtlasReduction ensemble channel kappa
        radius observed term ChartIndex chartMismatch chartWeight) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualIteratedA2StaticExternalWeakCouplingAccumulation_finiteChart
    ensemble channel kappa radius observed term ChartIndex
      (actualA2FiniteChartCertificateOfCompactAtlas ensemble channel kappa
        radius observed term ChartIndex chartMismatch chartWeight
          chartCertificate hreduction)

/-! ## Monotone-chart specialization -/

/-- The same reduction premise specialized to a fixed family of canonical
uniform-mass monotone charts. -/
abbrev ActualA2StaticCanonicalMonotoneAtlasReduction
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (data : ChartIndex -> IncreasingUniformMassC2ChartData)
    (fibreWeight : ChartIndex -> Real -> Complex) : Prop :=
  ActualA2StaticCanonicalFiniteAtlasReduction ensemble channel kappa radius
    observed term ChartIndex (fun index => (data index).chart) fibreWeight

/-- Build the actual finite atlas by applying the monotone-chart constructor
independently to every fixed chart. -/
def actualA2FiniteChartCertificateOfMonotoneAtlas
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (data : ChartIndex -> IncreasingUniformMassC2ChartData)
    (fibreWeight fibreWeightDeriv : ChartIndex -> Real -> Complex)
    (hfibreWeight : forall index mass,
      HasDerivAt (fibreWeight index) (fibreWeightDeriv index mass) mass)
    (hfibreWeightDerivContinuous : forall index,
      Continuous (fibreWeightDeriv index))
    (hreduction :
      ActualA2StaticCanonicalMonotoneAtlasReduction ensemble channel kappa
        radius observed term ChartIndex data fibreWeight) :
    ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term ChartIndex :=
  actualA2FiniteChartCertificateOfCompactAtlas ensemble channel kappa radius
    observed term ChartIndex (fun index => (data index).chart) fibreWeight
      (fun index =>
        compactIntervalCertificate (data index) (fibreWeight index)
          (fibreWeightDeriv index) (hfibreWeight index)
            (hfibreWeightDerivContinuous index))
      hreduction

/-- Exact summed variation cost for the monotone-atlas specialization. -/
theorem variationCost_actualA2FiniteChartCertificateOfMonotoneAtlas
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (data : ChartIndex -> IncreasingUniformMassC2ChartData)
    (fibreWeight fibreWeightDeriv : ChartIndex -> Real -> Complex)
    (hfibreWeight : forall index mass,
      HasDerivAt (fibreWeight index) (fibreWeightDeriv index mass) mass)
    (hfibreWeightDerivContinuous : forall index,
      Continuous (fibreWeightDeriv index))
    (hreduction :
      ActualA2StaticCanonicalMonotoneAtlasReduction ensemble channel kappa
        radius observed term ChartIndex data fibreWeight) :
    (actualA2FiniteChartCertificateOfMonotoneAtlas ensemble channel kappa
      radius observed term ChartIndex data fibreWeight fibreWeightDeriv
        hfibreWeight hfibreWeightDerivContinuous hreduction).variationCost =
      Finset.univ.sum fun index : ChartIndex =>
        (compactIntervalCertificate (data index) (fibreWeight index)
          (fibreWeightDeriv index) (hfibreWeight index)
            (hfibreWeightDerivContinuous index)).variationCost := by
  classical
  rfl

/-- Standard external-g convergence for the fixed finite monotone atlas. -/
theorem tendsto_actualA2ExternalAccumulation_of_monotoneAtlas
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (data : ChartIndex -> IncreasingUniformMassC2ChartData)
    (fibreWeight fibreWeightDeriv : ChartIndex -> Real -> Complex)
    (hfibreWeight : forall index mass,
      HasDerivAt (fibreWeight index) (fibreWeightDeriv index mass) mass)
    (hfibreWeightDerivContinuous : forall index,
      Continuous (fibreWeightDeriv index))
    (hreduction :
      ActualA2StaticCanonicalMonotoneAtlasReduction ensemble channel kappa
        radius observed term ChartIndex data fibreWeight) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualA2ExternalAccumulation_of_compactAtlas ensemble channel kappa
    radius observed term ChartIndex (fun index => (data index).chart)
      fibreWeight
      (fun index =>
        compactIntervalCertificate (data index) (fibreWeight index)
          (fibreWeightDeriv index) (hfibreWeight index)
            (hfibreWeightDerivContinuous index))
      hreduction

end

end CanonicalUniformMassFiniteAtlasActualA2ExternalWeakCoupling
end ArchonPhysics
