import ArchonPhysics.PhyslibFPUTFirstPicardDecomposition

/-!
# Canonical free reference determined by physical Physlib initial data

The first-Picard free orbit takes a radial function and a phase torus as
parameters.  This file constructs those parameters from an actual physical
initial position `q₀` and canonical momentum `p₀`.

For one positive-frequency mode set

`z = Q + i P / omega`, `radius = ‖z‖`,

and take the torus phase whose first Fourier character is
`exp (arg z * i)`.  The identity `‖z‖ exp (arg z * i) = z` then gives exact
reconstruction of both `Q` and `P`, including the zero-amplitude case.  At
zero frequency the construction still reconstructs position, while momentum
reconstruction requires the explicit condition `P = 0`; this is precisely
the reduced-sector condition that removes translation drift.

Everything is finite-volume deterministic algebra.  No random-phase,
smallness, kinetic, or thermalization assertion is made.
-/

namespace ArchonPhysics.PhyslibInitialModalReference

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Complex polar datum attached to a real harmonic coordinate and momentum.
For positive frequency it is the complex amplitude before multiplication by
`sqrt (omega / 2)`. -/
def modalPolarDatum (omega Q P : Real) : Complex :=
  (Q : Complex) + (P / omega : Real) * Complex.I

/-- Radial coordinate of the real free harmonic orbit. -/
def modalReferenceRadius (omega Q P : Real) : Real :=
  ‖modalPolarDatum omega Q P‖

/-- Unit additive-circle phase determined canonically by the argument of the
modal polar datum.  At zero amplitude, `Complex.arg 0 = 0` selects phase zero.
-/
def modalReferencePhase (omega Q P : Real) : UnitAddCircle :=
  (AddCircle.homeomorphCircle one_ne_zero).symm
    (Circle.exp (Complex.arg (modalPolarDatum omega Q P)))

/-- The first phase character is the unit complex direction selected by the
argument of the modal polar datum. -/
theorem unitPhase_modalReferencePhase (omega Q P : Real) :
    unitPhase (modalReferencePhase omega Q P) =
      (Circle.exp (Complex.arg (modalPolarDatum omega Q P)) : Complex) := by
  unfold unitPhase modalReferencePhase
  rw [fourier_one]
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  exact congrArg Subtype.val
    ((AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply
      (Circle.exp (Complex.arg (modalPolarDatum omega Q P))))

/-- Exact polar reconstruction, valid also when the modal datum is zero. -/
theorem modalReferenceRadius_mul_unitPhase_eq (omega Q P : Real) :
    (modalReferenceRadius omega Q P : Complex) *
        unitPhase (modalReferencePhase omega Q P) =
      modalPolarDatum omega Q P := by
  rw [unitPhase_modalReferencePhase]
  unfold modalReferenceRadius
  change (‖modalPolarDatum omega Q P‖ : Complex) *
      Complex.exp (Complex.arg (modalPolarDatum omega Q P) * Complex.I) = _
  exact Complex.norm_mul_exp_arg_mul_I (modalPolarDatum omega Q P)

/-- The radial/phase data always reconstruct the original real coordinate;
no frequency hypothesis is needed for this position identity. -/
theorem modalReferenceRadius_mul_re_eq_coordinate (omega Q P : Real) :
    modalReferenceRadius omega Q P *
        (unitPhase (modalReferencePhase omega Q P)).re = Q := by
  have h := congrArg Complex.re
    (modalReferenceRadius_mul_unitPhase_eq omega Q P)
  simpa [modalPolarDatum] using h

/-- At nonzero frequency the radial/phase data reconstruct the original
harmonic modal momentum. -/
theorem frequency_mul_modalReferenceRadius_mul_im_eq_momentum
    {omega : Real} (Q P : Real) (homega : omega ≠ 0) :
    omega * modalReferenceRadius omega Q P *
        (unitPhase (modalReferencePhase omega Q P)).im = P := by
  have h := congrArg Complex.im
    (modalReferenceRadius_mul_unitPhase_eq omega Q P)
  simp only [modalPolarDatum, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_add,
    Complex.ofReal_re, mul_one] at h
  have him : modalReferenceRadius omega Q P *
      (unitPhase (modalReferencePhase omega Q P)).im = P / omega := by
    simpa only [add_zero, zero_mul] using h
  calc
    omega * modalReferenceRadius omega Q P *
        (unitPhase (modalReferencePhase omega Q P)).im =
      omega * (modalReferenceRadius omega Q P *
        (unitPhase (modalReferencePhase omega Q P)).im) :=
          mul_assoc _ _ _
    _ = omega * (P / omega) := by rw [him]
    _ = P := by field_simp [homega]

/-- Initial modal position obtained from a physical Physlib position. -/
def physlibInitialModalPosition {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (q₀ : HilbertConfiguration N) :
    WeightedConfiguration N :=
  modalCoordinates m (sqrtMassTransform m q₀)

/-- Initial modal momentum obtained from a physical canonical momentum. -/
def physlibInitialModalMomentum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p₀ : HilbertConfiguration N) :
    WeightedConfiguration N :=
  modalCoordinates m (inverseSqrtMassTransform m p₀)

/-- Canonical radial parameters determined by the physical initial state. -/
def physlibInitialReferenceRadius {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N) : Lattice.Site N → Real :=
  fun k => modalReferenceRadius (modeFrequency m k)
    (physlibInitialModalPosition m q₀ k)
    (physlibInitialModalMomentum m p₀ k)

/-- Canonical phase torus determined by the physical initial state. -/
def physlibInitialReferencePhase {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N) :
    UnitAddTorus (Lattice.Site N) :=
  fun k => modalReferencePhase (modeFrequency m k)
    (physlibInitialModalPosition m q₀ k)
    (physlibInitialModalMomentum m p₀ k)

/-- Modal momentum encoded by radial/phase free-orbit parameters at time
zero.  It is the time derivative of `radius * Re(z exp (-i omega t))` at
zero, written without differentiating through the quotient phase API. -/
def freeReferenceInitialModalMomentum {d : Type*}
    (radius frequency : d → Real) (phase : UnitAddTorus d) (mode : d) : Real :=
  frequency mode * radius mode * (unitPhase (phase mode)).im

/-- The canonical free weighted configuration at time zero is exactly the
actual mass-weighted Physlib modal position.  Thus the Picard reference is no
longer an arbitrary `radius`/`phase` parameter. -/
theorem freeWeightedConfiguration_physlibInitialReference_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N) :
    freeWeightedConfiguration
        (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m) 0
        (physlibInitialReferencePhase m q₀ p₀) =
      physlibInitialModalPosition m q₀ := by
  have hphase :
      physicalFreePhaseEvolution (modeFrequency m) 0
          (physlibInitialReferencePhase m q₀ p₀) =
        physlibInitialReferencePhase m q₀ p₀ := by
    ext k
    simp [physicalFreePhaseEvolution, freeHarmonicPhaseEvolution,
      harmonicPhaseAdvance]
  ext k
  rw [freeWeightedConfiguration_apply]
  unfold freeRealModeCoordinate
  rw [hphase]
  unfold realPhaseModeCoordinate physlibInitialReferenceRadius
    physlibInitialReferencePhase
  exact modalReferenceRadius_mul_re_eq_coordinate
    (modeFrequency m k) (physlibInitialModalPosition m q₀ k)
      (physlibInitialModalMomentum m p₀ k)

/-- Every positive-frequency mode also has exactly the physical initial modal
momentum encoded by the same radial/phase data. -/
theorem freeReferenceInitialModalMomentum_physlibInitialReference_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N) (k : Lattice.Site N)
    (hfrequency : 0 < modeFrequency m k) :
    freeReferenceInitialModalMomentum
        (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m)
        (physlibInitialReferencePhase m q₀ p₀) k =
      physlibInitialModalMomentum m p₀ k := by
  exact frequency_mul_modalReferenceRadius_mul_im_eq_momentum
    (physlibInitialModalPosition m q₀ k)
    (physlibInitialModalMomentum m p₀ k) hfrequency.ne'

/-- Full modal-momentum reconstruction requires only the explicit zero-mode
condition: every zero-frequency translation component of the initial modal
momentum vanishes. -/
theorem freeReferenceInitialModalMomentum_physlibInitialReference
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N)
    (hzero : ∀ k, modeFrequency m k = 0 →
      physlibInitialModalMomentum m p₀ k = 0) :
    (fun k => freeReferenceInitialModalMomentum
        (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m)
        (physlibInitialReferencePhase m q₀ p₀) k) =
      physlibInitialModalMomentum m p₀ := by
  funext k
  by_cases hk : modeFrequency m k = 0
  · simp [freeReferenceInitialModalMomentum, hk, hzero k hk]
  · exact freeReferenceInitialModalMomentum_physlibInitialReference_of_pos
      m q₀ p₀ k (lt_of_le_of_ne (modeFrequency_nonneg m k) (Ne.symm hk))

/-- On every positive-frequency mode, the complex amplitude computed from the
canonical free reference at time zero is exactly the amplitude of the actual
physical initial modal coordinate and momentum. -/
theorem complexModeAmplitude_physlibInitialReference_zero_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N) (k : Lattice.Site N)
    (hfrequency : 0 < modeFrequency m k) :
    complexModeAmplitude (modeFrequency m k)
        (freeWeightedConfiguration
          (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m) 0
          (physlibInitialReferencePhase m q₀ p₀) k)
        (freeReferenceInitialModalMomentum
          (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m)
          (physlibInitialReferencePhase m q₀ p₀) k) =
      complexModeAmplitude (modeFrequency m k)
        (physlibInitialModalPosition m q₀ k)
        (physlibInitialModalMomentum m p₀ k) := by
  have hposition :
      freeWeightedConfiguration
          (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m) 0
          (physlibInitialReferencePhase m q₀ p₀) k =
        physlibInitialModalPosition m q₀ k :=
    congrArg (fun x : WeightedConfiguration N => x k)
      (freeWeightedConfiguration_physlibInitialReference_zero m q₀ p₀)
  rw [hposition,
    freeReferenceInitialModalMomentum_physlibInitialReference_of_pos
      m q₀ p₀ k hfrequency]

end

end ArchonPhysics.PhyslibInitialModalReference
