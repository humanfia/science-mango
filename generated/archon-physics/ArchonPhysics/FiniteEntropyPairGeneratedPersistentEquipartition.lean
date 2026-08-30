import ArchonPhysics.FiniteThreeWavePairGeneratedPositivity
import ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition

/-!
# Persistent equipartition after pair-generated positivity

Two-neighbour generation from the positive initial support makes every mode
strictly positive at each positive time.  Shifting the same physical orbit by
an arbitrary positive burn-in therefore supplies the all-time positivity
hypothesis used by finite entropy relaxation.  This removes positivity of the
whole original trajectory as an external premise.

The persistent observable below is evaluated on the time-shifted physical
orbit.  No microscopic-to-kinetic limit or collision-network identification is
claimed here.
-/

namespace ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition

open Set
open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.FiniteThreeWavePairGeneratedPositivity
open ArchonPhysics.PersistentEquipartition
open scoped ENNReal

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Nonempty Mode] [Fintype Triad]

/-- Restrict a global forward kinetic orbit to the future of `burnIn`. -/
def GlobalForwardCertificate.forwardShift
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (burnIn : Real) (hburnIn : 0 <= burnIn) :
    GlobalForwardCertificate model g (flow.trajectory burnIn) where
  trajectory := fun t => flow.trajectory (t + burnIn)
  initial := by simp
  nonnegative := by
    intro t ht i
    exact flow.nonnegative (t + burnIn) (add_nonneg ht hburnIn) i
  equation := by
    intro t ht
    have hbase := flow.equation (t + burnIn) (add_nonneg ht hburnIn)
    have hinner : HasDerivAt (fun s : Real => s + burnIn) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id t).add_const burnIn
    rw [hasDerivAt_pi]
    intro i
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_pi.mp hbase i).comp t hinner
  energy_conserved := by
    intro t ht
    calc
      totalKineticEnergy model.frequency (flow.trajectory (t + burnIn)) =
          totalKineticEnergy model.frequency actionZero :=
        flow.energy_conserved (t + burnIn) (add_nonneg ht hburnIn)
      _ = totalKineticEnergy model.frequency (flow.trajectory burnIn) :=
        (flow.energy_conserved burnIn hburnIn).symm

/-- After any positive burn-in, pair generation supplies strict positivity on
the entire shifted forward orbit. -/
theorem GlobalForwardCertificate.forwardShift_strictlyPositive_of_pairGenerated
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (hg : g ≠ 0)
    (hgenerated : PairGeneratedFromInitialSupport
      model.network model.rate actionZero)
    (burnIn : Real) (hburnIn : 0 < burnIn) :
    forall t, 0 <= t -> forall i,
      0 < (ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.forwardShift
        flow burnIn hburnIn.le).trajectory t i := by
  intro t ht i
  exact ArchonPhysics.FiniteThreeWavePairGeneratedPositivity.GlobalForwardCertificate.strictlyPositive_for_posTime_of_pairGenerated
    flow hg hgenerated (t + burnIn) (add_pos_of_nonneg_of_pos ht hburnIn) i

/-- Pair-generated nonnegative data imply a permanent finite kinetic tail
after any positive burn-in, with no all-time positivity premise on the
unshifted orbit. -/
theorem GlobalForwardCertificate.exists_persistentKineticEquipartitionTail_of_pairGenerated
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (mu : Real) (hmu : 0 < mu) (hmuOne : mu < 1)
    (hg : g ≠ 0)
    (hrigid : FrequencyBalanceRigid model.network model.frequency)
    (hrate : forall a, 0 < model.rate a)
    (henergy : 0 < totalKineticEnergy model.frequency actionZero)
    (hgenerated : PairGeneratedFromInitialSupport
      model.network model.rate actionZero)
    (burnIn : Real) (hburnIn : 0 < burnIn)
    (delta : Real) (hdelta : 0 < delta) :
    exists start : ENNReal, 0 < start ∧ start < ⊤ ∧
      TailPersistsFor
        (strictFiniteDistanceEvent
          (kineticEquipartitionDistance model.collisionData
            (ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.forwardShift
              flow burnIn hburnIn.le).trajectory mu)
          delta)
        start := by
  let shifted :=
    ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.forwardShift
      flow burnIn hburnIn.le
  have hshiftEnergy : 0 < totalKineticEnergy model.frequency
      (flow.trajectory burnIn) := by
    rw [flow.energy_conserved burnIn hburnIn.le]
    exact henergy
  have hshiftPositive : forall t, 0 <= t -> forall i,
      0 < shifted.trajectory t i := by
    exact ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.forwardShift_strictlyPositive_of_pairGenerated
      flow hg hgenerated burnIn hburnIn
  exact ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition.GlobalForwardCertificate.exists_persistentKineticEquipartitionTail_of_structural
    shifted mu hmu hmuOne hg hrigid hrate hshiftEnergy hshiftPositive
      delta hdelta

/-- The matching permanent settling time of the shifted physical orbit is
finite below every positive tolerance. -/
theorem GlobalForwardCertificate.kineticEquipartitionSettlingTime_lt_top_of_pairGenerated
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (mu : Real) (hmu : 0 < mu) (hmuOne : mu < 1)
    (hg : g ≠ 0)
    (hrigid : FrequencyBalanceRigid model.network model.frequency)
    (hrate : forall a, 0 < model.rate a)
    (henergy : 0 < totalKineticEnergy model.frequency actionZero)
    (hgenerated : PairGeneratedFromInitialSupport
      model.network model.rate actionZero)
    (burnIn : Real) (hburnIn : 0 < burnIn)
    (delta : Real) (hdelta : 0 < delta) :
    strictDistanceSettlingTime
        (kineticEquipartitionDistance model.collisionData
          (ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.forwardShift
            flow burnIn hburnIn.le).trajectory mu)
        delta < ⊤ := by
  let shifted :=
    ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.forwardShift
      flow burnIn hburnIn.le
  have hshiftEnergy : 0 < totalKineticEnergy model.frequency
      (flow.trajectory burnIn) := by
    rw [flow.energy_conserved burnIn hburnIn.le]
    exact henergy
  have hshiftPositive : forall t, 0 <= t -> forall i,
      0 < shifted.trajectory t i := by
    exact ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.forwardShift_strictlyPositive_of_pairGenerated
      flow hg hgenerated burnIn hburnIn
  exact ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition.GlobalForwardCertificate.kineticEquipartitionSettlingTime_lt_top_of_structural
    shifted mu hmu hmuOne hg hrigid hrate hshiftEnergy hshiftPositive
      delta hdelta

end

end ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition
