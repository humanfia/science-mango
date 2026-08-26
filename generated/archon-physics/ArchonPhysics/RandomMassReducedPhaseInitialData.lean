import ArchonPhysics.GlobalReducedParametricFlowAdapter
import ArchonPhysics.RandomMassMeasurableHarmonicEnergy
import ArchonPhysics.RandomMassPhaseInitialData

/-!
# Reduced physical random initial data and the common parametric embedding

The reconstructed mass-weighted initial state has zero coefficient in the
fixed final translation mode.  On a simple spectrum, orthonormality of the
explicit signed frame therefore makes both reconstructed vectors orthogonal
to the translation line.  After undoing the mass weights, this is exactly the
mass-weighted position gauge and zero-total-canonical-momentum constraint.

Consequently each simple realization supplies a genuine point of the
mass-dependent reduced phase space, while the same physical data is globally
packaged as one measurable point in the common parametric phase space.  This
is the adapter required by the canonical global-flow construction.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassReducedPhaseInitialData

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedHarmonicSpectrum
open ArchonPhysics.SignedEigenframeModeAssembly
open scoped BigOperators

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The signed final eigenvector lies in the physical translation line. -/
theorem signedLastEigenvector_mem_translationSpan
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    signedOrderedEigenvector (harmonicHermitian m)
        (lastOrderedIndex (ι := Lattice.Site N)) ∈
      Real ∙ translationMode m := by
  have heigen := signedOrderedEigenvector_eigenvector
    (harmonicHermitian m) hsimple
      (lastOrderedIndex (ι := Lattice.Site N))
  rw [harmonic_lastOrderedEigenvalue_eq_zero m, zero_smul] at heigen
  have hker : signedOrderedEigenvector (harmonicHermitian m)
      (lastOrderedIndex (ι := Lattice.Site N)) ∈
        LinearMap.ker (harmonicLinearMap m) := by
    rw [LinearMap.mem_ker]
    change matrixVal (harmonicHermitian m) *ᵥ
      signedOrderedEigenvector (harmonicHermitian m)
        (lastOrderedIndex (ι := Lattice.Site N)) = 0
    exact heigen
  rw [harmonicLinearMap_ker_eq_span] at hker
  exact hker

/-- If the last scalar coefficient is zero, the signed-frame reconstruction
is orthogonal to the physical translation vector. -/
theorem translationMode_dot_signedFrameReconstruction_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (coefficient : OrderedModeIndex N → Real)
    (hlast : coefficient (lastOrderedIndex (ι := Lattice.Site N)) = 0) :
    translationMode m ⬝ᵥ
        signedFrameReconstruction (harmonicHermitian m) coefficient = 0 := by
  let z := lastOrderedIndex (ι := Lattice.Site N)
  let v := signedOrderedEigenvector (harmonicHermitian m) z
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_singleton.mp
      (signedLastEigenvector_mem_translationSpan m hsimple))
  have hcne : c ≠ 0 := by
    intro hc0
    subst c
    have hvzero : v = 0 := by simpa [v, z] using hc.symm
    have hnorm := signedOrderedEigenvector_dot_self
      (harmonicHermitian m) hsimple z
    change v ⬝ᵥ v = 1 at hnorm
    rw [hvzero] at hnorm
    simp at hnorm
  have hvorth := signedOrderedEigenvector_dot_reconstruction
    (harmonicHermitian m) hsimple coefficient z
  rw [hlast] at hvorth
  have hscaled : c * (translationMode m ⬝ᵥ
      signedFrameReconstruction (harmonicHermitian m) coefficient) = 0 := by
    rw [← smul_eq_mul, ← smul_dotProduct, hc]
    simpa [v, z] using hvorth
  exact (mul_eq_zero.mp hscaled).resolve_left hcne

/-- The final modal position coefficient vanishes identically. -/
@[simp] theorem initialModePositionCoefficient_last
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega) :
    initialModePositionCoefficient ensemble a omega
      (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
  simp [initialModePositionCoefficient, phaseCoordinate]

/-- The final modal momentum coefficient vanishes identically. -/
@[simp] theorem initialModeMomentumCoefficient_last
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega) :
    initialModeMomentumCoefficient ensemble a omega
      (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
  simp [initialModeMomentumCoefficient, phaseMomentum]

/-- On a simple realization, the reconstructed `X` is orthogonal to the
translation vector. -/
theorem translationMode_dot_initialMassWeightedPosition_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    translationMode (ensemble.restrictPositiveMass (N := N) omega) ⬝ᵥ
      initialMassWeightedPosition ensemble a omega = 0 := by
  exact translationMode_dot_signedFrameReconstruction_eq_zero
    (ensemble.restrictPositiveMass (N := N) omega) hsimple _
    (initialModePositionCoefficient_last ensemble a omega)

/-- On a simple realization, the reconstructed `Y` is orthogonal to the
translation vector. -/
theorem translationMode_dot_initialMassWeightedMomentum_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    translationMode (ensemble.restrictPositiveMass (N := N) omega) ⬝ᵥ
      initialMassWeightedMomentum ensemble a omega = 0 := by
  exact translationMode_dot_signedFrameReconstruction_eq_zero
    (ensemble.restrictPositiveMass (N := N) omega) hsimple _
    (initialModeMomentumCoefficient_last ensemble a omega)

/-- The physical initial position satisfies the mass-weighted translation
gauge on every simple realization. -/
theorem initialPhysicalPosition_mem_reducedPositionSpace
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    initialPhysicalPosition ensemble a omega ∈
      ReducedPositionSpace
        (ensemble.restrictPositiveMass (N := N) omega) := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  rw [mem_reducedPositionSpace_iff]
  calc
    (∑ i, m.mass i * initialPhysicalPosition ensemble a omega i) =
        translationMode m ⬝ᵥ
          initialMassWeightedPosition ensemble a omega := by
      unfold dotProduct translationMode
      apply Finset.sum_congr rfl
      intro i _hi
      unfold initialPhysicalPosition
      have hs0 : Real.sqrt (m.mass i) ≠ 0 :=
        Real.sqrt_ne_zero'.2 (m.mass_pos i)
      have hs2 : Real.sqrt (m.mass i) ^ 2 = m.mass i :=
        Real.sq_sqrt (m.mass_pos i).le
      change m.mass i * ((Real.sqrt (m.mass i))⁻¹ *
        initialMassWeightedPosition ensemble a omega i) =
          Real.sqrt (m.mass i) *
            initialMassWeightedPosition ensemble a omega i
      field_simp [hs0]
      rw [hs2]
    _ = 0 := translationMode_dot_initialMassWeightedPosition_eq_zero
      ensemble a omega (by simpa [m] using hsimple)

/-- The physical initial canonical momentum has total sum zero on every
simple realization. -/
theorem initialPhysicalMomentum_mem_reducedMomentumSpace
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    initialPhysicalMomentum ensemble a omega ∈ ReducedMomentumSpace N := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  rw [mem_reducedMomentumSpace_iff]
  calc
    (∑ i, initialPhysicalMomentum ensemble a omega i) =
        translationMode m ⬝ᵥ
          initialMassWeightedMomentum ensemble a omega := by
      unfold dotProduct translationMode
      apply Finset.sum_congr rfl
      intro i _hi
      unfold initialPhysicalMomentum
      rfl
    _ = 0 := translationMode_dot_initialMassWeightedMomentum_eq_zero
      ensemble a omega (by simpa [m] using hsimple)

/-- The genuine mass-dependent reduced initial point on a simple realization. -/
def reducedInitialStateOfSimple
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    ReducedPhaseSpace (ensemble.restrictPositiveMass (N := N) omega) :=
  (⟨initialPhysicalPosition ensemble a omega,
      initialPhysicalPosition_mem_reducedPositionSpace
        ensemble a omega hsimple⟩,
    ⟨initialPhysicalMomentum ensemble a omega,
      initialPhysicalMomentum_mem_reducedMomentumSpace
        ensemble a omega hsimple⟩)

/-- Globally measurable initial point in the common parameterized phase
space.  It is totalized even on the degenerate null set. -/
def parametricInitialSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (kappa beta g a : Real) (omega : Omega) : ParametricPhaseSpace N :=
  ((WithLp.toLp 2 fun i =>
      ((ensemble.restrictPositiveMass (N := N) omega).mass i)⁻¹,
      (kappa, (beta, g))),
    (initialPhysicalPosition ensemble a omega,
      initialPhysicalMomentum ensemble a omega))

theorem measurable_parametricInitialSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa beta g a : Real) :
    Measurable (parametricInitialSample ensemble (N := N) kappa beta g a) := by
  have hinverseMass : Measurable fun omega =>
      WithLp.toLp 2 (fun i =>
        ((ensemble.restrictPositiveMass (N := N) omega).mass i)⁻¹) := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro i
    exact (RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
      ensemble i).inv
  exact (hinverseMass.prodMk measurable_const).prodMk
    ((measurable_initialPhysicalPosition ensemble a).prodMk
      (measurable_initialPhysicalMomentum ensemble a))

/-- On every simple realization, the common measurable initial point is
exactly the embedding of the genuine reduced initial state. -/
theorem parametricInitialSample_eq_embedReducedPoint
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa beta g a : Real) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    parametricInitialSample ensemble kappa beta g a omega =
      embedReducedPoint (ensemble.restrictPositiveMass (N := N) omega)
        kappa beta g (reducedInitialStateOfSimple ensemble a omega hsimple) := by
  rfl

/-- The physical ordered energies of the globally measurable initial point
equal the frozen target profile on a simple realization. -/
theorem harmonicOrderedPhysicalModeEnergy_initial_eq_target
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)))
    (k : OrderedModeIndex N) :
    harmonicOrderedPhysicalModeEnergy
        (ensemble.restrictPositiveMass (N := N))
        (initialPhysicalPosition ensemble a)
        (initialPhysicalMomentum ensemble a) omega k =
      orderedTargetEnergy N a k := by
  unfold harmonicOrderedPhysicalModeEnergy massWeightedPositionSample
    massWeightedMomentumSample
  rw [sqrtMassTransform_initialPhysicalPosition,
    inverseSqrtMassTransform_initialPhysicalMomentum]
  exact orderedHarmonicModeEnergy_initial_eq_target
    ensemble hN ha0 ha1 omega
      (by simpa [harmonicHermitianSample, harmonicHermitian] using hsimple) k

/-- The exact physical modal profile and total harmonic energy one hold
almost surely. -/
theorem harmonicOrderedPhysicalModeEnergy_initial_eq_target_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) :
    ∀ᵐ omega ∂ensemble.probability,
      (∀ k : OrderedModeIndex N,
        harmonicOrderedPhysicalModeEnergy
            (ensemble.restrictPositiveMass (N := N))
            (initialPhysicalPosition ensemble a)
            (initialPhysicalMomentum ensemble a) omega k =
          orderedTargetEnergy N a k) ∧
      (∑ k : OrderedModeIndex N,
        harmonicOrderedPhysicalModeEnergy
            (ensemble.restrictPositiveMass (N := N))
            (initialPhysicalPosition ensemble a)
            (initialPhysicalMomentum ensemble a) omega k) = 1 := by
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
    (N := N) ensemble (by omega)] with omega hsimple
  have hall : ∀ k : OrderedModeIndex N,
      harmonicOrderedPhysicalModeEnergy
          (ensemble.restrictPositiveMass (N := N))
          (initialPhysicalPosition ensemble a)
          (initialPhysicalMomentum ensemble a) omega k =
        orderedTargetEnergy N a k := fun k =>
    harmonicOrderedPhysicalModeEnergy_initial_eq_target
      ensemble hN ha0 ha1 omega
        (by simpa [harmonicHermitianSample, harmonicHermitian] using hsimple) k
  refine ⟨hall, ?_⟩
  simp_rw [hall]
  exact sum_orderedTargetEnergy_eq_one hN a

end

end ArchonPhysics.RandomMassReducedPhaseInitialData
