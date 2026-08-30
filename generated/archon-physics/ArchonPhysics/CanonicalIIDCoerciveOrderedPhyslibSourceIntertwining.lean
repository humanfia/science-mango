import ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
import ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
import ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter

/-!
# Canonical iid source intertwining with actual Physlib trajectories

The canonical measurable flow agrees almost surely, for every real time,
with an embedded genuine reduced Hamiltonian trajectory.  The deterministic
ordered/Physlib basis theorem can therefore be applied to the corresponding
Physlib `Time` path.  This module proves that every canonical ordered source,
and every phase/conjugate signed source, is exactly the orientation sign
times the reindexed actual Physlib source almost surely and for all times.

The orientation has absolute value one and introduces no estimate loss.  No
RPA, Markov, small-denominator, recollision, kinetic, or closure hypothesis
is used.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveOrderedPhyslibSourceIntertwining

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- A reduced real trajectory gives exactly the oriented Physlib source after
the existing canonical `Time` reparametrization. -/
theorem orderedSignedRotatedSource_reducedPath_eq_orientedPhyslib
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (sourceKappa sourceBeta sourceG : Real)
    (z : Real -> ReducedPhaseSpace m)
    (k : OrderedModeIndex N) (time : Real) :
    orderedSignedRotatedSource m sourceKappa sourceBeta sourceG k
        (fun s => ((z s).1 : HilbertConfiguration N)) time =
      (orderedPhyslibOrientation m k : Complex) *
        physlibModeRotatedSource m sourceKappa sourceBeta sourceG
          (orderedPhyslibModeIndex k)
          (physlibPositionPathOfReducedTrajectory z) time := by
  have hpath :
      realReparametrize (physlibPositionPathOfReducedTrajectory z) =
        (fun s => ((z s).1 : HilbertConfiguration N)) := by
    funext s
    exact realReparametrize_physlibPositionPathOfReducedTrajectory z s
  rw [← hpath]
  exact
    orderedSignedRotatedSource_eq_orientation_mul_physlibModeRotatedSource
      m hsimple sourceKappa sourceBeta sourceG k
        (physlibPositionPathOfReducedTrajectory z) time

/-- Pointwise canonical ordered source identification once a reduced-path
matching witness has been supplied. -/
theorem canonicalOrderedPotentialChannelRotatedSource_eq_orientedPhyslib_of_matches_reduced
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (z : Real -> ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatch : forall t,
      canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble flowKappa flowBeta flowG
            hflowBeta a (omega, t) =
        embedReducedPoint (canonicalMass (N := N) omega)
          flowKappa flowBeta flowG (z t))
    (k : OrderedModeIndex N) (time : Real) :
    canonicalOrderedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG k (omega, time) =
      (orderedPhyslibOrientation (canonicalMass (N := N) omega) k : Complex) *
        physlibModeRotatedSource (canonicalMass (N := N) omega)
          sourceKappa sourceBeta sourceG (orderedPhyslibModeIndex k)
          (physlibPositionPathOfReducedTrajectory z) time := by
  have hq :
      (fun s => canonicalFlowPosition (N := N)
        flowKappa flowBeta flowG hflowBeta a (omega, s)) =
      (fun s => ((z s).1 : HilbertConfiguration N)) := by
    funext s
    have hs := congrArg
      (fun x : ParametricPhaseSpace N => x.2.1) (hmatch s)
    simpa [canonicalFlowPosition, embedReducedPoint] using hs
  unfold canonicalOrderedPotentialChannelRotatedSource
  rw [hq]
  exact orderedSignedRotatedSource_reducedPath_eq_orientedPhyslib
    (canonicalMass (N := N) omega) hsimple
      sourceKappa sourceBeta sourceG z k time

/-- Phase and conjugate branches retain the same real orientation sign. -/
theorem canonicalSignedPotentialChannelRotatedSource_eq_orientedPhyslib_of_matches_reduced
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (z : Real -> ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatch : forall t,
      canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble flowKappa flowBeta flowG
            hflowBeta a (omega, t) =
        embedReducedPoint (canonicalMass (N := N) omega)
          flowKappa flowBeta flowG (z t))
    (entry : PhaseSign × OrderedModeIndex N) (time : Real) :
    canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry (omega, time) =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) entry.2 : Complex) *
        phaseSignActComplex entry.1
          (physlibModeRotatedSource (canonicalMass (N := N) omega)
            sourceKappa sourceBeta sourceG
              (orderedPhyslibModeIndex entry.2)
              (physlibPositionPathOfReducedTrajectory z) time) := by
  rw [canonicalSignedPotentialChannelRotatedSource]
  rw [canonicalOrderedPotentialChannelRotatedSource_eq_orientedPhyslib_of_matches_reduced
    flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG omega hsimple z hmatch entry.2 time]
  rcases entry with ⟨sign, k⟩
  cases sign <;> simp [phaseSignActComplex]

/-- For the actual canonical iid ensemble, the complete ordered source
intertwining holds almost surely, simultaneously for every ordered mode and
every real time.  The witness path is a genuine reduced Hamiltonian integral
curve and hence its `Time` reparametrization is an actual Physlib solution. -/
theorem canonicalOrderedPotentialChannelRotatedSource_eq_orientedPhyslib_ae_allTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      exists hsimple : SimpleOrderedSpectrum
          (harmonicHermitian (canonicalMass (N := N) omega)),
        exists z : Real -> ReducedPhaseSpace (canonicalMass (N := N) omega),
          (forall t, HasDerivAt z
            (reducedVectorField (canonicalMass (N := N) omega)
              flowKappa flowBeta flowG (z t)) t) ∧
          (forall t,
            canonicalRandomMassPhaseTrajectory (N := N)
                canonicalIIDMassPhaseEnsemble flowKappa flowBeta flowG
                  hflowBeta a (omega, t) =
              embedReducedPoint (canonicalMass (N := N) omega)
                flowKappa flowBeta flowG (z t)) ∧
          forall k time,
            canonicalOrderedPotentialChannelRotatedSource (N := N)
                flowKappa flowBeta flowG hflowBeta a
                  sourceKappa sourceBeta sourceG k (omega, time) =
              (orderedPhyslibOrientation
                  (canonicalMass (N := N) omega) k : Complex) *
                physlibModeRotatedSource (canonicalMass (N := N) omega)
                  sourceKappa sourceBeta sourceG
                    (orderedPhyslibModeIndex k)
                    (physlibPositionPathOfReducedTrajectory z) time := by
  filter_upwards [canonicalRandomMassPhaseTrajectory_matches_reduced_ae
    (N := N) canonicalIIDMassPhaseEnsemble hN ha0 ha1
      flowKappa flowBeta flowG hflowBeta] with omega homega
  rcases homega with ⟨hsimple, z, _hz0, hz, hmatch, _henergy⟩
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)) := by
    simpa [canonicalMass] using hsimple
  refine ⟨hsimple', z, hz, hmatch, ?_⟩
  intro k time
  exact
    canonicalOrderedPotentialChannelRotatedSource_eq_orientedPhyslib_of_matches_reduced
      flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG omega hsimple' z hmatch k time

/-- Signed version of the almost-sure all-time source bridge. -/
theorem canonicalSignedPotentialChannelRotatedSource_eq_orientedPhyslib_ae_allTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      exists hsimple : SimpleOrderedSpectrum
          (harmonicHermitian (canonicalMass (N := N) omega)),
        exists z : Real -> ReducedPhaseSpace (canonicalMass (N := N) omega),
          (forall t, HasDerivAt z
            (reducedVectorField (canonicalMass (N := N) omega)
              flowKappa flowBeta flowG (z t)) t) ∧
          (forall t,
            canonicalRandomMassPhaseTrajectory (N := N)
                canonicalIIDMassPhaseEnsemble flowKappa flowBeta flowG
                  hflowBeta a (omega, t) =
              embedReducedPoint (canonicalMass (N := N) omega)
                flowKappa flowBeta flowG (z t)) ∧
          forall entry time,
            canonicalSignedPotentialChannelRotatedSource (N := N)
                flowKappa flowBeta flowG hflowBeta a
                  sourceKappa sourceBeta sourceG entry (omega, time) =
              (orderedPhyslibOrientation
                  (canonicalMass (N := N) omega) entry.2 : Complex) *
                phaseSignActComplex entry.1
                  (physlibModeRotatedSource
                    (canonicalMass (N := N) omega)
                    sourceKappa sourceBeta sourceG
                      (orderedPhyslibModeIndex entry.2)
                      (physlibPositionPathOfReducedTrajectory z) time) := by
  filter_upwards [canonicalRandomMassPhaseTrajectory_matches_reduced_ae
    (N := N) canonicalIIDMassPhaseEnsemble hN ha0 ha1
      flowKappa flowBeta flowG hflowBeta] with omega homega
  rcases homega with ⟨hsimple, z, _hz0, hz, hmatch, _henergy⟩
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)) := by
    simpa [canonicalMass] using hsimple
  refine ⟨hsimple', z, hz, hmatch, ?_⟩
  intro entry time
  exact
    canonicalSignedPotentialChannelRotatedSource_eq_orientedPhyslib_of_matches_reduced
      flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG omega hsimple' z hmatch entry time

end

end ArchonPhysics.CanonicalIIDCoerciveOrderedPhyslibSourceIntertwining
