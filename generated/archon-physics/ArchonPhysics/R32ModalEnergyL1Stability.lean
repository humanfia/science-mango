import ArchonPhysics.FiniteModalEnergyL1Stability
import ArchonPhysics.GlobalRandomMassModalObservable
import ArchonPhysics.RandomMassPositiveCollisionData
import ArchonPhysics.SignedEigenframeModeAssembly

/-!
# R32: `L1` stability of the ordered harmonic modal-energy profile

For a finite family of frequency-weighted phase-space vectors `W`, put

`E_k(W) = (1 / 2) * ‖W_k‖²`.

This file proves the sharp elementary quadratic-difference estimate

`∑ k, |E_k(W) - E_k(W₀)|
  ≤ (1 / 2) ‖W-W₀‖₂ (‖W‖₂ + ‖W₀‖₂)`.

It then specializes `W` to the globally ordered modes of a fixed
positive-mass harmonic chain.  In signed ordered coordinates,

`W_k(q,p) = sqrt(λ_k) Q_k(q) + i P_k(p)`,

so that `E_k(W)` is exactly the basis-free physical ordered harmonic energy
whenever the ordered spectrum is simple.  The final theorem is stated
directly for two points of the mass-dependent reduced physical phase space.

This is a deterministic finite-volume observable estimate.  It assumes no
kinetic approximation, random-phase propagation, or thermalization input.
-/

namespace ArchonPhysics.R32ModalEnergyL1Stability

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.FiniteModalEnergyL1Stability
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.NormalizedL1Stability
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.SignedEigenframeModeAssembly

noncomputable section

/-! ## Abstract finite phase-space estimate -/

variable {Mode : Type} [Fintype Mode]

/-- Harmonic energy profile carried by a finite complex phase-space vector.
The complex real and imaginary parts represent the frequency-weighted
position and momentum coordinates. -/
def harmonicEnergyProfile (W : Mode -> Complex) (k : Mode) : Real :=
  (1 / 2 : Real) * ‖W k‖ ^ 2

/-- Euclidean `L2` size of the complete finite modal phase-space vector. -/
def phaseSpaceL2Norm (W : Mode -> Complex) : Real :=
  amplitudeL2Norm (Mode := Mode) (E := Complex) W

/-- Euclidean `L2` distance between two complete modal phase-space vectors. -/
def phaseSpaceL2Distance (W W0 : Mode -> Complex) : Real :=
  amplitudeL2Distance (Mode := Mode) (E := Complex) W W0

/-- Exact `L1` quadratic-difference bound for the harmonic energy profile. -/
theorem harmonicEnergyProfile_l1_le
    (W W0 : Mode -> Complex) :
    (∑ k, |harmonicEnergyProfile W k - harmonicEnergyProfile W0 k|) <=
      (1 / 2 : Real) * phaseSpaceL2Distance W W0 *
        (phaseSpaceL2Norm W + phaseSpaceL2Norm W0) := by
  have h := modalEnergyL1Distance_le
    (Mode := Mode) (E := Complex) W W0
  have hleft :
      (∑ k, |harmonicEnergyProfile W k - harmonicEnergyProfile W0 k|) =
        (1 / 2 : Real) *
          modalEnergyL1Distance (Mode := Mode) (E := Complex) W W0 := by
    unfold harmonicEnergyProfile modalEnergyL1Distance l1Distance
      modalEnergySpectrum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← mul_sub, abs_mul,
      abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 2)]
  rw [hleft]
  calc
    (1 / 2 : Real) *
        modalEnergyL1Distance (Mode := Mode) (E := Complex) W W0 <=
        (1 / 2 : Real) *
          ((amplitudeL2Norm (Mode := Mode) (E := Complex) W +
              amplitudeL2Norm (Mode := Mode) (E := Complex) W0) *
            amplitudeL2Distance (Mode := Mode) (E := Complex) W W0) := by
      exact mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (1 / 2 : Real) * phaseSpaceL2Distance W W0 *
        (phaseSpaceL2Norm W + phaseSpaceL2Norm W0) := by
      unfold phaseSpaceL2Distance phaseSpaceL2Norm
      ring

/-! ## Ordered harmonic coordinates -/

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- Signed scalar coordinate of a real state in one globally ordered mode. -/
def orderedSignedCoordinate
    (A : HermitianMatrix iota) (k : Fin (Fintype.card iota))
    (x : iota -> Real) : Real :=
  signedOrderedEigenvector A k ⬝ᵥ x

/-- Frequency-weighted phase-space vector of a state expressed in the
globally signed ordered eigenframe. -/
def orderedHarmonicPhaseVector
    (A : HermitianMatrix iota) (position momentum : iota -> Real) :
    Fin (Fintype.card iota) -> Complex :=
  fun k => Complex.mk
    (Real.sqrt (orderedEigenvalue A k) * orderedSignedCoordinate A k position)
    (orderedSignedCoordinate A k momentum)

/-- A simple ordered projector extracts the square of the corresponding
signed scalar coordinate from an arbitrary real state. -/
theorem orderedModeEnergy_eq_orderedSignedCoordinate_sq
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card iota)) (x : iota -> Real) :
    orderedModeEnergy A k x = (orderedSignedCoordinate A k x) ^ 2 := by
  unfold orderedModeEnergy orderedModeProjectedState
    SpectralBandEnergyObservable.coordinateEnergy orderedSignedCoordinate
  rw [← signedOrderedEigenvector_outerProduct A hsimple k,
    Matrix.vecMulVec_mulVec, smul_dotProduct, dotProduct_smul,
    signedOrderedEigenvector_dot_self A hsimple k]
  simp only [op_smul_eq_smul, smul_eq_mul, mul_one, pow_two]

/-- The squared norm of the weighted complex coordinate is twice the
basis-free ordered harmonic energy. -/
theorem norm_sq_orderedHarmonicPhaseVector
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (hA : ∀ k, 0 <= orderedEigenvalue A k)
    (position momentum : iota -> Real)
    (k : Fin (Fintype.card iota)) :
    ‖orderedHarmonicPhaseVector A position momentum k‖ ^ 2 =
      2 * orderedHarmonicModeEnergy A k position momentum := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold orderedHarmonicPhaseVector
  change
    (Real.sqrt (orderedEigenvalue A k) *
        orderedSignedCoordinate A k position) *
        (Real.sqrt (orderedEigenvalue A k) *
          orderedSignedCoordinate A k position) +
      orderedSignedCoordinate A k momentum *
        orderedSignedCoordinate A k momentum = _
  rw [orderedHarmonicModeEnergy, orderedModeEnergy_eq_orderedSignedCoordinate_sq
      A hsimple k momentum,
    orderedModeEnergy_eq_orderedSignedCoordinate_sq A hsimple k position]
  nlinarith [Real.sq_sqrt (hA k)]

/-- Consequently the abstract half-squared-norm profile is exactly the
ordered harmonic energy profile. -/
theorem harmonicEnergyProfile_orderedHarmonicPhaseVector
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (hA : ∀ k, 0 <= orderedEigenvalue A k)
    (position momentum : iota -> Real)
    (k : Fin (Fintype.card iota)) :
    harmonicEnergyProfile (orderedHarmonicPhaseVector A position momentum) k =
      orderedHarmonicModeEnergy A k position momentum := by
  unfold harmonicEnergyProfile
  rw [norm_sq_orderedHarmonicPhaseVector A hsimple hA position momentum k]
  ring

/-- Ordered basis-free harmonic energies inherit the sharp `L1` stability
bound from the frequency-weighted phase-space vector. -/
theorem orderedHarmonicModeEnergy_l1_le
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (hA : ∀ k, 0 <= orderedEigenvalue A k)
    (position momentum position0 momentum0 : iota -> Real) :
    (∑ k, |orderedHarmonicModeEnergy A k position momentum -
        orderedHarmonicModeEnergy A k position0 momentum0|) <=
      (1 / 2 : Real) *
        phaseSpaceL2Distance
          (orderedHarmonicPhaseVector A position momentum)
          (orderedHarmonicPhaseVector A position0 momentum0) *
        (phaseSpaceL2Norm (orderedHarmonicPhaseVector A position momentum) +
          phaseSpaceL2Norm
            (orderedHarmonicPhaseVector A position0 momentum0)) := by
  simpa only [harmonicEnergyProfile_orderedHarmonicPhaseVector
    A hsimple hA] using
      harmonicEnergyProfile_l1_le
        (orderedHarmonicPhaseVector A position momentum)
        (orderedHarmonicPhaseVector A position0 momentum0)

/-! ## Frozen positive-mass chain and reduced physical phase space -/

/-- The actual frequency-weighted ordered modal vector of one point in the
mass-dependent reduced physical phase space. -/
def reducedOrderedHarmonicPhaseVector
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : ReducedPhaseSpace m) : OrderedModeIndex N -> Complex :=
  orderedHarmonicPhaseVector (harmonicHermitian m)
    (sqrtMassTransform m (z.1 :
      CoerciveHamiltonianPhyslib.HilbertConfiguration N))
    (inverseSqrtMassTransform m (z.2 :
      CoerciveHamiltonianPhyslib.HilbertConfiguration N))

/-- Every ordered eigenvalue of the actual positive-mass harmonic matrix is
nonnegative. -/
theorem harmonicHermitian_orderedEigenvalue_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) :
    0 <= orderedEigenvalue (harmonicHermitian m) k := by
  simpa [harmonicOrderedEigenvalue, harmonicHermitianSample,
    harmonicHermitian] using
      (harmonicOrderedEigenvalue_nonneg (fun _ : Unit => m) () k)

/-- The weighted ordered vector represents the repository's physical
reduced-state modal energy exactly. -/
theorem harmonicEnergyProfile_reducedOrderedHarmonicPhaseVector
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z : ReducedPhaseSpace m) (k : OrderedModeIndex N) :
    harmonicEnergyProfile (reducedOrderedHarmonicPhaseVector m z) k =
      reducedPhysicalOrderedModeEnergy m z k := by
  exact harmonicEnergyProfile_orderedHarmonicPhaseVector
    (harmonicHermitian m) hsimple
    (harmonicHermitian_orderedEigenvalue_nonneg m)
    (sqrtMassTransform m (z.1 :
      CoerciveHamiltonianPhyslib.HilbertConfiguration N))
    (inverseSqrtMassTransform m (z.2 :
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)) k

/-- Requested fixed-realization physical statement: the complete ordered
harmonic modal-energy profile is locally Lipschitz in the frequency-weighted
phase-space `L2` metric, with the exact quadratic-difference constant `1/2`.
-/
theorem reducedPhysicalOrderedModeEnergy_l1_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z z0 : ReducedPhaseSpace m) :
    (∑ k : OrderedModeIndex N,
      |reducedPhysicalOrderedModeEnergy m z k -
        reducedPhysicalOrderedModeEnergy m z0 k|) <=
      (1 / 2 : Real) *
        phaseSpaceL2Distance
          (reducedOrderedHarmonicPhaseVector m z)
          (reducedOrderedHarmonicPhaseVector m z0) *
        (phaseSpaceL2Norm (reducedOrderedHarmonicPhaseVector m z) +
          phaseSpaceL2Norm (reducedOrderedHarmonicPhaseVector m z0)) := by
  simpa only [harmonicEnergyProfile_reducedOrderedHarmonicPhaseVector
    m hsimple] using
      harmonicEnergyProfile_l1_le
        (reducedOrderedHarmonicPhaseVector m z)
        (reducedOrderedHarmonicPhaseVector m z0)

#print axioms harmonicEnergyProfile_l1_le
#print axioms reducedPhysicalOrderedModeEnergy_l1_le

end

end ArchonPhysics.R32ModalEnergyL1Stability
