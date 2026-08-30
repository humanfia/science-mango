import ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
import ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

/-!
# Ordered signed amplitudes versus reindexed Physlib amplitudes

The basis orientation relation is transported through the positive-frequency
complex-amplitude transform and the interaction-picture phase rotation.  On
a simple harmonic spectrum, each ordered signed amplitude is exactly the
corresponding Physlib amplitude multiplied by a real sign of absolute value
one.  Finite signed block monomials consequently differ only by the product
of those signs and have identical norms.

These are deterministic identities.  No stochastic closure, RPA, Markov,
small-denominator, recollision, or kinetic hypothesis is used.
-/

namespace ArchonPhysics.RandomMassOrderedPhyslibAmplitudeIntertwining

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform

noncomputable section

variable {N : Nat} [NeZero N]

/-- Complex-amplitude intertwining for arbitrary weighted position and
momentum vectors. -/
theorem complexModeAmplitude_orderedSignedCoordinate_eq_orientation_mul
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N)
    (position momentum : WeightedConfiguration N) :
    complexModeAmplitude
        (orderedModeFrequency (harmonicHermitian m) k)
        (orderedSignedCoordinate m k position)
        (orderedSignedCoordinate m k momentum) =
      (orderedPhyslibOrientation m k : Complex) *
        complexModeAmplitude (modeFrequency m (orderedPhyslibModeIndex k))
          (modalCoordinates m position (orderedPhyslibModeIndex k))
          (modalCoordinates m momentum (orderedPhyslibModeIndex k)) := by
  rw [orderedModeFrequency_harmonicHermitian_eq,
    orderedSignedCoordinate_eq_orientation_mul_modalCoordinates
      m hsimple k position,
    orderedSignedCoordinate_eq_orientation_mul_modalCoordinates
      m hsimple k momentum]
  simp only [orderedPhyslibModeIndex]
  unfold complexModeAmplitude
  push_cast
  ring

/-- Interaction-picture amplitude written directly in the explicit ordered
signed frame along a Physlib trajectory. -/
def orderedSignedInteractionAmplitudeAlongPhyslibPath
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N)
    (p q : Time -> HilbertConfiguration N) (time : Real) : Complex :=
  phaseRenormalize
    (orderedModeFrequency (harmonicHermitian m) k * time)
    (complexModeAmplitude
      (orderedModeFrequency (harmonicHermitian m) k)
      (orderedSignedCoordinate m k
        (massWeightedPosition m (realReparametrize q) time))
      (orderedSignedCoordinate m k
        (massWeightedMomentum m (realReparametrize p) time)))

/-- The corresponding reindexed Physlib interaction-picture amplitude. -/
def reindexedPhyslibInteractionAmplitude
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N)
    (p q : Time -> HilbertConfiguration N) (time : Real) : Complex :=
  phaseRenormalize (modeFrequency m (orderedPhyslibModeIndex k) * time)
    (physlibModeAmplitude m (orderedPhyslibModeIndex k) p q time)

/-- Full interaction-picture amplitude intertwining along any Physlib paths. -/
theorem orderedSignedInteractionAmplitudeAlongPhyslibPath_eq_orientation_mul
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N)
    (p q : Time -> HilbertConfiguration N) (time : Real) :
    orderedSignedInteractionAmplitudeAlongPhyslibPath m k p q time =
      (orderedPhyslibOrientation m k : Complex) *
        reindexedPhyslibInteractionAmplitude m k p q time := by
  unfold orderedSignedInteractionAmplitudeAlongPhyslibPath
    reindexedPhyslibInteractionAmplitude physlibModeAmplitude
    physlibModePosition physlibModeMomentum
  rw [complexModeAmplitude_orderedSignedCoordinate_eq_orientation_mul
    m hsimple k
      (massWeightedPosition m (realReparametrize q) time)
      (massWeightedMomentum m (realReparametrize p) time),
    orderedModeFrequency_harmonicHermitian_eq]
  simp only [orderedPhyslibModeIndex]
  unfold phaseRenormalize
  ring

/-- The phase/conjugate branch retains the same real orientation sign. -/
theorem phaseSignAct_orderedSignedInteractionAmplitude_eq_orientation_mul
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (entry : PhaseSign × OrderedModeIndex N)
    (p q : Time -> HilbertConfiguration N) (time : Real) :
    phaseSignActComplex entry.1
        (orderedSignedInteractionAmplitudeAlongPhyslibPath
          m entry.2 p q time) =
      (orderedPhyslibOrientation m entry.2 : Complex) *
        phaseSignActComplex entry.1
          (reindexedPhyslibInteractionAmplitude
            m entry.2 p q time) := by
  rw [orderedSignedInteractionAmplitudeAlongPhyslibPath_eq_orientation_mul
    m hsimple entry.2 p q time]
  rcases entry with ⟨sign, k⟩
  cases sign <;> simp [phaseSignActComplex]

/-- Orientation multiplication does not change the norm of one interaction
amplitude. -/
theorem norm_orderedSignedInteractionAmplitudeAlongPhyslibPath_eq
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N)
    (p q : Time -> HilbertConfiguration N) (time : Real) :
    ‖orderedSignedInteractionAmplitudeAlongPhyslibPath m k p q time‖ =
      ‖reindexedPhyslibInteractionAmplitude m k p q time‖ := by
  rw [orderedSignedInteractionAmplitudeAlongPhyslibPath_eq_orientation_mul
    m hsimple k p q time, norm_mul]
  simp [abs_orderedPhyslibOrientation m hsimple k]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Product of all orientation signs in one finite signed modal block. -/
def orderedBlockOrientation
    (m : Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) : Complex :=
  ∏ i ∈ block, (orderedPhyslibOrientation m (entry i).2 : Complex)

/-- A finite signed ordered block differs from the reindexed Physlib block
by exactly the product orientation. -/
theorem orderedSignedInteractionBlock_eq_orientation_mul_physlibBlock
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I)
    (p q : Time -> HilbertConfiguration N) (time : Real) :
    (∏ i ∈ block,
      phaseSignActComplex (entry i).1
        (orderedSignedInteractionAmplitudeAlongPhyslibPath
          m (entry i).2 p q time)) =
      orderedBlockOrientation m entry block *
        ∏ i ∈ block,
          phaseSignActComplex (entry i).1
            (reindexedPhyslibInteractionAmplitude
              m (entry i).2 p q time) := by
  simp_rw [phaseSignAct_orderedSignedInteractionAmplitude_eq_orientation_mul
    m hsimple]
  unfold orderedBlockOrientation
  rw [Finset.prod_mul_distrib]

/-- The block orientation itself has norm one. -/
theorem norm_orderedBlockOrientation
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    ‖orderedBlockOrientation m entry block‖ = 1 := by
  unfold orderedBlockOrientation
  rw [norm_prod]
  simp [abs_orderedPhyslibOrientation m hsimple]

/-- Consequently the two finite signed block monomials have identical norm. -/
theorem norm_orderedSignedInteractionBlock_eq_physlibBlock
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I)
    (p q : Time -> HilbertConfiguration N) (time : Real) :
    ‖∏ i ∈ block,
      phaseSignActComplex (entry i).1
        (orderedSignedInteractionAmplitudeAlongPhyslibPath
          m (entry i).2 p q time)‖ =
      ‖∏ i ∈ block,
        phaseSignActComplex (entry i).1
          (reindexedPhyslibInteractionAmplitude
            m (entry i).2 p q time)‖ := by
  rw [orderedSignedInteractionBlock_eq_orientation_mul_physlibBlock
    m hsimple entry block p q time, norm_mul,
    norm_orderedBlockOrientation m hsimple entry block, one_mul]

end

end ArchonPhysics.RandomMassOrderedPhyslibAmplitudeIntertwining
