import ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
import ArchonPhysics.PhyslibHamiltonDuhamel

/-!
# Ordered measurable eigenframe versus the Physlib normal-mode basis

For one deterministic positive-mass realization with simple harmonic
spectrum, the globally defined signed ordered eigenvector and Mathlib's
noncomputable Hermitian eigenvector basis span the same one-dimensional
eigenspace.  This module identifies them by an explicit real orientation
coefficient, proves that coefficient is exactly `+1` or `-1`, and transports
the identification to modal coordinates, nonlinear force projections, and
interaction-picture sources.

The results are pointwise deterministic.  No RPA, random-phase, Markov,
small-denominator, recollision, kinetic-limit, or measurability assumption is
introduced.  A later canonical adapter may apply them on the already proved
almost-sure simple-spectrum event.
-/

namespace ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining

open scoped Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform

noncomputable section

variable {N : Nat} [NeZero N]

/-- Physlib's normal-mode index corresponding to an ordered spectral index. -/
def orderedPhyslibModeIndex (k : OrderedModeIndex N) : Lattice.Site N :=
  orderedIndexEquiv k

/-- Dot-product orientation between Physlib's normal mode and the explicit
signed ordered eigenvector. -/
def orderedPhyslibOrientation
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N) : Real :=
  (⇑(normalModeBasis m (orderedPhyslibModeIndex k)) :
      Lattice.Configuration N) ⬝ᵥ
    signedOrderedEigenvector (harmonicHermitian m) k

/-- On a simple spectrum the two basis vectors have exactly the same
rank-one outer product. -/
theorem normalModeBasis_vecMulVec_eq_signedOrderedEigenvector
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    Matrix.vecMulVec
        (⇑(normalModeBasis m (orderedPhyslibModeIndex k)) :
          Lattice.Configuration N)
        (⇑(normalModeBasis m (orderedPhyslibModeIndex k)) :
          Lattice.Configuration N) =
      Matrix.vecMulVec
        (signedOrderedEigenvector (harmonicHermitian m) k)
        (signedOrderedEigenvector (harmonicHermitian m) k) := by
  change Matrix.vecMulVec
      (⇑((harmonicHermitian m).2.eigenvectorBasis (orderedIndexEquiv k)) :
        Lattice.Configuration N)
      (⇑((harmonicHermitian m).2.eigenvectorBasis (orderedIndexEquiv k)) :
        Lattice.Configuration N) = _
  exact
    (orderedModeProjector_eq_vecMulVec
      (harmonicHermitian m) hsimple k).symm.trans
        (signedOrderedEigenvector_outerProduct
          (harmonicHermitian m) hsimple k).symm

/-- A Physlib normal mode has unit Euclidean dot norm. -/
theorem normalModeBasis_dot_self
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N) :
    (⇑(normalModeBasis m (orderedPhyslibModeIndex k)) :
        Lattice.Configuration N) ⬝ᵥ
      (⇑(normalModeBasis m (orderedPhyslibModeIndex k)) :
        Lattice.Configuration N) = 1 := by
  have hinner :=
    (normalModeBasis m).inner_eq_one (orderedPhyslibModeIndex k)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    using hinner

/-- The explicit signed ordered vector is the Physlib normal mode multiplied
by their orientation coefficient. -/
theorem signedOrderedEigenvector_eq_orientation_smul_normalModeBasis
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    signedOrderedEigenvector (harmonicHermitian m) k =
      orderedPhyslibOrientation m k •
        (⇑(normalModeBasis m (orderedPhyslibModeIndex k)) :
          Lattice.Configuration N) := by
  have houter :=
    normalModeBasis_vecMulVec_eq_signedOrderedEigenvector m hsimple k
  have happ := congrArg
    (fun M : Matrix (Lattice.Site N) (Lattice.Site N) Real =>
      M *ᵥ signedOrderedEigenvector (harmonicHermitian m) k) houter
  simpa [Matrix.vecMulVec_mulVec, orderedPhyslibOrientation,
    signedOrderedEigenvector_dot_self (harmonicHermitian m) hsimple k]
      using happ.symm

/-- The orientation coefficient has square one. -/
theorem orderedPhyslibOrientation_sq
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    orderedPhyslibOrientation m k ^ 2 = 1 := by
  have halign :=
    signedOrderedEigenvector_eq_orientation_smul_normalModeBasis
      m hsimple k
  have hnorm := congrArg
    (fun v : Lattice.Configuration N => v ⬝ᵥ v) halign
  rw [signedOrderedEigenvector_dot_self
      (harmonicHermitian m) hsimple k,
    smul_dotProduct, dotProduct_smul,
    normalModeBasis_dot_self m k] at hnorm
  simpa only [smul_eq_mul, mul_one, pow_two] using hnorm.symm

/-- Hence the orientation is literally one of the two real signs. -/
theorem orderedPhyslibOrientation_eq_one_or_neg_one
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    orderedPhyslibOrientation m k = 1 ∨
      orderedPhyslibOrientation m k = -1 :=
  sq_eq_one_iff.mp (orderedPhyslibOrientation_sq m hsimple k)

/-- In particular the orientation has absolute value one. -/
theorem abs_orderedPhyslibOrientation
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    |orderedPhyslibOrientation m k| = 1 := by
  rcases orderedPhyslibOrientation_eq_one_or_neg_one m hsimple k with h | h
  · simp [h]
  · simp [h]

/-- Ordered signed coordinates and reindexed Physlib modal coordinates differ
by precisely the same orientation sign. -/
theorem orderedSignedCoordinate_eq_orientation_mul_modalCoordinates
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) (x : WeightedConfiguration N) :
    orderedSignedCoordinate m k x =
      orderedPhyslibOrientation m k *
        modalCoordinates m x (orderedPhyslibModeIndex k) := by
  rw [orderedSignedCoordinate,
    signedOrderedEigenvector_eq_orientation_smul_normalModeBasis
      m hsimple k,
    smul_dotProduct, modalCoordinates_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    smul_eq_mul]
  rw [dotProduct_comm]

/-- The true physical nonlinear force projected in the signed ordered frame
is the reindexed Physlib tensor force multiplied by the orientation sign. -/
theorem orderedSignedNonlinearForce_eq_orientation_mul_physlibModeTensorForce
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa beta g : Real) (k : OrderedModeIndex N)
    (q : Time -> HilbertConfiguration N) (time : Real) :
    orderedSignedNonlinearForce m kappa beta g k
        (realReparametrize q time) =
      orderedPhyslibOrientation m k *
        physlibModeTensorForce m kappa beta g
          (orderedPhyslibModeIndex k) q time := by
  rw [orderedSignedNonlinearForce,
    orderedSignedCoordinate_eq_orientation_mul_modalCoordinates
      m hsimple k,
    modalCoordinates_transformedNonlinearForce,
    projectedNonlinearBondForce_eq_tensorNonlinearForce]
  rfl

/-- Full interaction-picture source intertwining.  This is the deterministic
source-level bridge from the canonical signed ordered representation to the
actual Physlib normal-mode representation. -/
theorem orderedSignedRotatedSource_eq_orientation_mul_physlibModeRotatedSource
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa beta g : Real) (k : OrderedModeIndex N)
    (q : Time -> HilbertConfiguration N) (time : Real) :
    orderedSignedRotatedSource m kappa beta g k
        (realReparametrize q) time =
      (orderedPhyslibOrientation m k : Complex) *
        physlibModeRotatedSource m kappa beta g
          (orderedPhyslibModeIndex k) q time := by
  unfold orderedSignedRotatedSource physlibModeRotatedSource
  rw [orderedModeFrequency_harmonicHermitian_eq,
    orderedSignedNonlinearForce_eq_orientation_mul_physlibModeTensorForce
      m hsimple kappa beta g k q time]
  simp only [orderedPhyslibModeIndex]
  rw [mul_comm (modeFrequency m (orderedIndexEquiv k)) time]
  unfold forcedModeSource
  push_cast
  ring

end

end ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
