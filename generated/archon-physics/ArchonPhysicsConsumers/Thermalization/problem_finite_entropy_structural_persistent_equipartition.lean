import ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition

/-!
Consumer replay and trust audit for persistent kinetic equipartition under
the explicit finite structural collision hypotheses.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Filter Set
open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition
open ArchonPhysics.FiniteEntropyStructuralPersistentEquipartition.GlobalForwardCertificate
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.PersistentEquipartition
open scoped ENNReal

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Nonempty Mode] [Fintype Triad]

theorem problem_exists_persistentKineticEquipartitionTail_of_structural
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
        start :=
  exists_persistentKineticEquipartitionTail_of_structural
    flow mu hmu hmuOne hg hrigid hrate henergy haction delta hdelta

theorem problem_kineticEquipartitionSettlingTime_lt_top_of_structural
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
        delta < ⊤ :=
  kineticEquipartitionSettlingTime_lt_top_of_structural
    flow mu hmu hmuOne hg hrigid hrate henergy haction delta hdelta

#print axioms exists_persistentKineticEquipartitionTail_of_structural
#print axioms kineticEquipartitionSettlingTime_lt_top_of_structural
#print axioms problem_exists_persistentKineticEquipartitionTail_of_structural
#print axioms problem_kineticEquipartitionSettlingTime_lt_top_of_structural

end

end ArchonPhysicsConsumers.Thermalization
