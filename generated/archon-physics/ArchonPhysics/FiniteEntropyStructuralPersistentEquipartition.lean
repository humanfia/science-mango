import ArchonPhysics.FiniteEntropyStructuralF2Certificate
import ArchonPhysics.PersistentEquipartition

/-!
# Persistent kinetic equipartition from finite structural relaxation

The finite structural collision hypotheses already imply convergence of the
late-window kinetic equipartition distance to zero.  This module composes that
result with the persistent-tail interface: below every positive tolerance
there is a positive finite start after which the kinetic distance remains
below the tolerance at every finite future time.

This is a kinetic-level statement.  It does not supply the structural
hypotheses for the frozen random lattice or a microscopic-to-kinetic limit.
-/

namespace ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition

open Filter Set
open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.FiniteEntropyStructuralF2Certificate
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.PersistentEquipartition
open scoped ENNReal

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Nonempty Mode] [Fintype Triad]

/-- Structural finite-network relaxation yields an attained positive finite
start whose entire finite future stays below any positive kinetic
equipartition tolerance. -/
theorem GlobalForwardCertificate.exists_persistentKineticEquipartitionTail_of_structural
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (mu : Real) (hmu : 0 < mu) (hmuOne : mu < 1)
    (hg : g ≠ 0)
    (hrigid : FrequencyBalanceRigid model.network model.frequency)
    (hrate : forall a, 0 < model.rate a)
    (henergy : 0 < totalKineticEnergy model.frequency actionZero)
    (haction : forall t, 0 <= t -> forall i,
      0 < flow.trajectory t i)
    (delta : Real) (hdelta : 0 < delta) :
    exists start : ENNReal, 0 < start ∧ start < ⊤ ∧
      TailPersistsFor
        (strictFiniteDistanceEvent
          (kineticEquipartitionDistance model.collisionData
            flow.trajectory mu)
          delta)
        start := by
  exact exists_ennreal_tail_of_tendsto_zero
    (kineticEquipartitionDistance model.collisionData flow.trajectory mu)
    delta
    (GlobalForwardCertificate.tendsto_kineticEquipartitionDistance_zero_of_structural
      flow mu hmu hmuOne hg hrigid hrate henergy haction)
    hdelta

/-- Under the same explicit structural hypotheses, the permanent kinetic
settling time below every positive tolerance is finite. -/
theorem GlobalForwardCertificate.kineticEquipartitionSettlingTime_lt_top_of_structural
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (mu : Real) (hmu : 0 < mu) (hmuOne : mu < 1)
    (hg : g ≠ 0)
    (hrigid : FrequencyBalanceRigid model.network model.frequency)
    (hrate : forall a, 0 < model.rate a)
    (henergy : 0 < totalKineticEnergy model.frequency actionZero)
    (haction : forall t, 0 <= t -> forall i,
      0 < flow.trajectory t i)
    (delta : Real) (hdelta : 0 < delta) :
    strictDistanceSettlingTime
        (kineticEquipartitionDistance model.collisionData flow.trajectory mu)
        delta < ⊤ := by
  exact strictDistanceSettlingTime_lt_top_of_tendsto_zero
    (kineticEquipartitionDistance model.collisionData flow.trajectory mu)
    delta
    (GlobalForwardCertificate.tendsto_kineticEquipartitionDistance_zero_of_structural
      flow mu hmu hmuOne hg hrigid hrate henergy haction)
    hdelta

end

end ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition
