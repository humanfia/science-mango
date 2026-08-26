import ArchonPhysics.MeasurableOrderedEigenframe
import ArchonPhysics.RandomMassPositiveCollisionData

/-!
# Explicit measurable signed eigenframe for iid random masses

This module specializes the finite first-positive-pivot construction to the
mass-weighted harmonic matrix of an iid positive-mass chain.  The signed frame
is globally defined and measurable, including at the null exceptional set of
degenerate spectra.  Full rank-one, normalization, eigenvector, and physical
collision-frame identities are asserted only almost surely, using the proved
random-mass simple-spectrum event.

No phase-distribution, empirical-limit, kinetic, or thermalization conclusion
is asserted.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassMeasurableOrderedEigenframe

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- One fixed ordered signed harmonic eigenvector as a globally totalized
random variable. -/
def orderedEigenvectorSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (k : OrderedModeIndex N)
    (omega : Omega) : Lattice.Configuration N :=
  signedOrderedEigenvector
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)) omega) k

/-- Euclidean wrapper of one ordered signed harmonic eigenvector. -/
def orderedEigenvectorLpSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (k : OrderedModeIndex N)
    (omega : Omega) : EuclideanSpace Real (Lattice.Site N) :=
  signedOrderedEigenvectorLp
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)) omega) k

/-- The complete ordered signed frame. -/
def orderedEigenframeSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    OrderedModeIndex N → Lattice.Configuration N := fun k =>
  orderedEigenvectorSample ensemble k omega

/-- Every fixed signed eigenvector is globally measurable, not merely on the
almost-sure simple-spectrum event. -/
theorem measurable_orderedEigenvectorSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (k : OrderedModeIndex N) :
    Measurable (orderedEigenvectorSample ensemble k) := by
  exact measurable_signedOrderedEigenvector
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)))
    (measurable_harmonicHermitianSample _
      (measurable_restrictPositiveMass_coordinate ensemble)) k

/-- Every fixed Euclidean signed eigenvector is globally measurable. -/
theorem measurable_orderedEigenvectorLpSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (k : OrderedModeIndex N) :
    Measurable (orderedEigenvectorLpSample ensemble k) := by
  exact measurable_signedOrderedEigenvectorLp
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)))
    (measurable_harmonicHermitianSample _
      (measurable_restrictPositiveMass_coordinate ensemble)) k

/-- The complete frame is globally measurable in both ordered-mode and site
coordinates. -/
theorem measurable_orderedEigenframeSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] :
    Measurable (orderedEigenframeSample (N := N) ensemble) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_orderedEigenvectorSample ensemble k

/-- Almost surely, every explicitly signed vector has the exact ordered
rank-one projector as its outer product. -/
theorem orderedEigenvector_outerProduct_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      ∀ k : OrderedModeIndex N,
        Matrix.vecMulVec (orderedEigenvectorSample ensemble k omega)
            (orderedEigenvectorSample ensemble k omega) =
          orderedModeProjector
            (harmonicHermitianSample
              (ensemble.restrictPositiveMass (N := N)) omega) k := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  intro k
  exact signedOrderedEigenvector_outerProduct _ hsimple k

/-- Almost surely every Euclidean signed vector has norm one. -/
theorem orderedEigenvectorLp_norm_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      ∀ k : OrderedModeIndex N,
        ‖orderedEigenvectorLpSample ensemble k omega‖ = 1 := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  intro k
  exact signedOrderedEigenvectorLp_norm _ hsimple k

/-- Almost surely every signed vector is an eigenvector for the corresponding
ordered eigenvalue. -/
theorem orderedEigenvector_eigenvector_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      ∀ k : OrderedModeIndex N,
        matrixVal
            (harmonicHermitianSample
              (ensemble.restrictPositiveMass (N := N)) omega) *ᵥ
            orderedEigenvectorSample ensemble k omega =
          orderedEigenvalue
              (harmonicHermitianSample
                (ensemble.restrictPositiveMass (N := N)) omega) k •
            orderedEigenvectorSample ensemble k omega := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  intro k
  exact signedOrderedEigenvector_eigenvector _ hsimple k

/-- Almost surely the explicit frame satisfies the existing sign-invariant
physical collision-frame contract. -/
theorem isPhysicalOrderedEigenframe_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      IsPhysicalOrderedEigenframe
        (ensemble.restrictPositiveMass (N := N) omega)
        (orderedEigenframeSample ensemble omega) := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  intro k
  have houter := signedOrderedEigenvector_outerProduct
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)) omega) hsimple k
  simpa [orderedEigenframeSample, orderedEigenvectorSample,
    MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian,
    harmonicHermitianSample] using houter.symm

/-- The existing positive marked empirical collision measure may therefore
be represented almost surely in this explicit measurable signed frame. -/
theorem positiveMarkedEmpiricalMeasure_eq_signedFrame_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (sign : Fin 3 → ModalPhaseMismatch.InteractionSign) :
    ∀ᵐ omega ∂ensemble.probability,
      positiveMarkedEmpiricalMeasure
          (ensemble.restrictPositiveMass (N := N) omega) sign =
        framePositiveMarkedEmpiricalMeasure
          (ensemble.restrictPositiveMass (N := N) omega) sign
          (orderedEigenframeSample ensemble omega) := by
  filter_upwards [isPhysicalOrderedEigenframe_ae ensemble hN] with omega hframe
  exact positiveMarkedEmpiricalMeasure_eq_frame _ sign _ hframe

/-- Canonical iid Uniform `[4/5,6/5]` frame measurability. -/
theorem measurable_canonicalOrderedEigenframeSample
    {N : Nat} [NeZero N] :
    Measurable
      (orderedEigenframeSample (N := N) canonicalIIDMassPhaseEnsemble) :=
  measurable_orderedEigenframeSample canonicalIIDMassPhaseEnsemble

/-- Canonical iid Uniform `[4/5,6/5]` physical-frame identification. -/
theorem canonical_isPhysicalOrderedEigenframe_ae
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      IsPhysicalOrderedEigenframe
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
        (orderedEigenframeSample canonicalIIDMassPhaseEnsemble omega) :=
  isPhysicalOrderedEigenframe_ae canonicalIIDMassPhaseEnsemble hN

end

end ArchonPhysics.RandomMassMeasurableOrderedEigenframe
