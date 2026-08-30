import ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition

/-!
# Consumer: pair-generated positivity and persistent equipartition

This consumer replays the sharp finite-network obstruction, strict positivity
propagation, and the burn-in persistent-equipartition bridge.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Set
open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.FiniteThreeWavePairGeneratedPositivity
open ArchonPhysics.PersistentEquipartition
open scoped ENNReal

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Nonempty Mode] [Fintype Triad]

theorem problem_ordinary_connectivity_and_positive_energy_do_not_force_positivity :
    EveryModeIncident oneTriadNetwork /\
      (forall a, 0 < oneTriadRate a) /\
      (forall a, oneTriadFrequency (oneTriadNetwork.mode₁ a) =
        oneTriadFrequency (oneTriadNetwork.mode₂ a) +
          oneTriadFrequency (oneTriadNetwork.mode₃ a)) /\
      0 < totalKineticEnergy oneTriadFrequency oneSeedAction /\
      collisionVectorField oneTriadNetwork oneTriadRate oneSeedAction = 0 /\
      ¬ (forall i, 0 < oneSeedAction i) :=
  ordinary_connectivity_and_positive_energy_do_not_force_positivity

theorem problem_strictlyPositive_for_posTime_of_pairGenerated
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (hg : g ≠ 0)
    (hgenerated : PairGeneratedFromInitialSupport
      model.network model.rate actionZero) :
    forall t, 0 < t -> forall i, 0 < flow.trajectory t i :=
  ArchonPhysics.FiniteThreeWavePairGeneratedPositivity.GlobalForwardCertificate.strictlyPositive_for_posTime_of_pairGenerated
    flow hg hgenerated

theorem problem_exists_persistentKineticEquipartitionTail_of_pairGenerated
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
        start :=
  ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.exists_persistentKineticEquipartitionTail_of_pairGenerated
    flow mu hmu hmuOne hg hrigid hrate henergy hgenerated burnIn hburnIn
      delta hdelta

theorem problem_kineticEquipartitionSettlingTime_lt_top_of_pairGenerated
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
        delta < ⊤ :=
  ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.kineticEquipartitionSettlingTime_lt_top_of_pairGenerated
    flow mu hmu hmuOne hg hrigid hrate henergy hgenerated burnIn hburnIn
      delta hdelta

#print axioms ordinary_connectivity_and_positive_energy_do_not_force_positivity
#print axioms ArchonPhysics.FiniteThreeWavePairGeneratedPositivity.GlobalForwardCertificate.strictlyPositive_for_posTime_of_pairGenerated
#print axioms ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.exists_persistentKineticEquipartitionTail_of_pairGenerated
#print axioms ArchonPhysics.FiniteEntropyPairGeneratedPersistentEquipartition.GlobalForwardCertificate.kineticEquipartitionSettlingTime_lt_top_of_pairGenerated
#print axioms problem_ordinary_connectivity_and_positive_energy_do_not_force_positivity
#print axioms problem_strictlyPositive_for_posTime_of_pairGenerated
#print axioms problem_exists_persistentKineticEquipartitionTail_of_pairGenerated
#print axioms problem_kineticEquipartitionSettlingTime_lt_top_of_pairGenerated

end

end ArchonPhysicsConsumers.Thermalization
