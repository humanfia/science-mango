import ArchonPhysics.MeasurableOrderedHarmonicEnergy

/-!
# Random-mass measurable physical harmonic-mode energies

This module inserts the physical mass weights into the globally measurable
ordered-projector observable.  Positions and canonical momenta are converted
to `X = sqrt(M) q` and `Y = M^(-1/2) p` before mode energies are evaluated.
Thus no measurable eigenbasis and no unweighted-momentum shortcut enters the
random observable.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassMeasurableHarmonicEnergy

open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.ReducedModeTransform
open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Physical mass-weighted position as a random Euclidean configuration. -/
def massWeightedPositionSample
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (position : Omega → HilbertConfiguration N) (omega : Omega) :
    WeightedConfiguration N :=
  sqrtMassTransform (massSample omega) (position omega)

/-- Physical mass-weighted momentum as a random Euclidean configuration. -/
def massWeightedMomentumSample
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (momentum : Omega → HilbertConfiguration N) (omega : Omega) :
    WeightedConfiguration N :=
  inverseSqrtMassTransform (massSample omega) (momentum omega)

theorem measurable_massWeightedPositionSample
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (position : Omega → HilbertConfiguration N)
    (hmass : ∀ i, Measurable fun omega => (massSample omega).mass i)
    (hposition : Measurable position) :
    Measurable (massWeightedPositionSample massSample position) := by
  rw [show massWeightedPositionSample massSample position =
      fun omega => WithLp.toLp 2 (fun i =>
        Real.sqrt ((massSample omega).mass i) *
          WithLp.ofLp (position omega) i) by
    funext omega
    ext i
    exact sqrtMassTransform_apply (massSample omega) (position omega) i]
  apply (WithLp.measurable_toLp 2 _).comp
  exact measurable_pi_lambda _ fun i => (hmass i).sqrt.mul
    ((measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 _).comp hposition))

theorem measurable_massWeightedMomentumSample
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (momentum : Omega → HilbertConfiguration N)
    (hmass : ∀ i, Measurable fun omega => (massSample omega).mass i)
    (hmomentum : Measurable momentum) :
    Measurable (massWeightedMomentumSample massSample momentum) := by
  rw [show massWeightedMomentumSample massSample momentum =
      fun omega => WithLp.toLp 2 (fun i =>
        (Real.sqrt ((massSample omega).mass i))⁻¹ *
          WithLp.ofLp (momentum omega) i) by
    funext omega
    ext i
    exact inverseSqrtMassTransform_apply
      (massSample omega) (momentum omega) i]
  apply (WithLp.measurable_toLp 2 _).comp
  exact measurable_pi_lambda _ fun i => (hmass i).sqrt.inv.mul
    ((measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 _).comp hmomentum))

/-- Globally defined physical energy of one ordered random-mass mode. -/
def harmonicOrderedPhysicalModeEnergy
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (position momentum : Omega → HilbertConfiguration N)
    (omega : Omega) (k : Fin (Fintype.card (Lattice.Site N))) : Real :=
  orderedHarmonicModeEnergy
    (harmonicHermitianSample massSample omega) k
    (massWeightedPositionSample massSample position omega)
    (massWeightedMomentumSample massSample momentum omega)

/-- Every fixed ordered physical mode energy is globally measurable. -/
theorem measurable_harmonicOrderedPhysicalModeEnergy
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (position momentum : Omega → HilbertConfiguration N)
    (hmass : ∀ i, Measurable fun omega => (massSample omega).mass i)
    (hposition : Measurable position) (hmomentum : Measurable momentum)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun omega =>
      harmonicOrderedPhysicalModeEnergy massSample position momentum omega k := by
  exact measurable_orderedHarmonicModeEnergy
    (harmonicHermitianSample massSample)
    (measurable_harmonicHermitianSample massSample hmass)
    (fun omega => WithLp.ofLp
      (massWeightedPositionSample massSample position omega))
    (fun omega => WithLp.ofLp
      (massWeightedMomentumSample massSample momentum omega))
    ((WithLp.measurable_ofLp 2 _).comp
      (measurable_massWeightedPositionSample massSample position hmass hposition))
    ((WithLp.measurable_ofLp 2 _).comp
      (measurable_massWeightedMomentumSample massSample momentum hmass hmomentum)) k

omit [MeasurableSpace Omega] in
/-- Positivity follows from positive semidefiniteness of the harmonic matrix. -/
theorem harmonicOrderedPhysicalModeEnergy_nonneg
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (position momentum : Omega → HilbertConfiguration N)
    (omega : Omega) (k : Fin (Fintype.card (Lattice.Site N))) :
    0 ≤ harmonicOrderedPhysicalModeEnergy
      massSample position momentum omega k := by
  apply orderedHarmonicModeEnergy_nonneg
  exact harmonicOrderedEigenvalue_nonneg massSample omega k

omit [MeasurableSpace Omega] in
/-- On a simple spectrum, the physical ordered mode energies exactly sum to
the mass-weighted harmonic energy. -/
theorem sum_harmonicOrderedPhysicalModeEnergy_of_simple
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (position momentum : Omega → HilbertConfiguration N)
    (omega : Omega)
    (hsimple : OrderedSingleModeProjector.SimpleOrderedSpectrum
      (harmonicHermitianSample massSample omega)) :
    (∑ k : Fin (Fintype.card (Lattice.Site N)),
      harmonicOrderedPhysicalModeEnergy massSample position momentum omega k) =
      (SpectralBandEnergyObservable.coordinateEnergy
          (massWeightedMomentumSample massSample momentum omega) +
        (massWeightedPositionSample massSample position omega : Lattice.Configuration N) ⬝ᵥ
          (OrderedSingleModeProjector.matrixVal
              (harmonicHermitianSample massSample omega) *ᵥ
            (massWeightedPositionSample massSample position omega :
              Lattice.Configuration N))) / 2 := by
  exact sum_orderedHarmonicModeEnergy
    (harmonicHermitianSample massSample omega) hsimple
    (massWeightedPositionSample massSample position omega)
    (massWeightedMomentumSample massSample momentum omega)

/-- For every iid ensemble with at least two sites, the exact physical modal
energy sum holds almost surely. -/
theorem sum_harmonicOrderedPhysicalModeEnergy_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (position momentum : Omega → HilbertConfiguration N) :
    ∀ᵐ omega ∂ensemble.probability,
      (∑ k : Fin (Fintype.card (Lattice.Site N)),
        harmonicOrderedPhysicalModeEnergy
          (ensemble.restrictPositiveMass (N := N))
          position momentum omega k) =
        (SpectralBandEnergyObservable.coordinateEnergy
            (massWeightedMomentumSample
              (ensemble.restrictPositiveMass (N := N)) momentum omega) +
          (massWeightedPositionSample
              (ensemble.restrictPositiveMass (N := N)) position omega :
                Lattice.Configuration N) ⬝ᵥ
            (OrderedSingleModeProjector.matrixVal
                (harmonicHermitianSample
                  (ensemble.restrictPositiveMass (N := N)) omega) *ᵥ
              (massWeightedPositionSample
                (ensemble.restrictPositiveMass (N := N)) position omega :
                  Lattice.Configuration N))) / 2 := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  exact sum_harmonicOrderedPhysicalModeEnergy_of_simple
    (ensemble.restrictPositiveMass (N := N)) position momentum omega hsimple

/-- Canonical iid `[4/5,6/5]` specialization: every fixed physical ordered
mode energy is globally measurable. -/
theorem canonical_measurable_harmonicOrderedPhysicalModeEnergy
    {N : Nat} [NeZero N]
    (position momentum : RandomEnsemble.SampleSpace → HilbertConfiguration N)
    (hposition : Measurable position) (hmomentum : Measurable momentum)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun omega =>
      harmonicOrderedPhysicalModeEnergy
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        position momentum omega k := by
  exact measurable_harmonicOrderedPhysicalModeEnergy
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    position momentum
    (measurable_restrictPositiveMass_coordinate canonicalIIDMassPhaseEnsemble)
    hposition hmomentum k

end

end ArchonPhysics.RandomMassMeasurableHarmonicEnergy
