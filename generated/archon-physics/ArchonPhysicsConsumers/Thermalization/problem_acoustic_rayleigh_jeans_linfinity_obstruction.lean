import ArchonPhysics.AcousticRayleighJeansLInfinityObstruction

namespace ArchonPhysicsConsumers.Thermalization.AcousticRayleighJeansLInfinityObstruction

open Filter MeasureTheory Set
open ArchonPhysics
open ArchonPhysics.AcousticRayleighJeansLInfinityObstruction
open ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory Topology

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

theorem problem_acousticRayleighJeansAction_not_memLp
    (collision : ResonantThreeWaveMeasure Mode)
    {W : Real} (hW : 0 < W)
    (hlower :
      volume.restrict (additiveFrequencyTriangle W) ≪
        (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W))
    {temperature : Real} (htemperature : 0 < temperature) :
    ¬ MemLp
      (rayleighJeansAction temperature collision.frequency) ∞
      (collisionReferenceMeasure collision) :=
  not_memLp_top_rayleighJeansAction_of_childTriangleDominance
    collision hW hlower htemperature

theorem problem_acousticRayleighJeansEquilibria_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (hacoustic : HasAcousticMassAtZero
      (collisionReferenceMeasure collision) collision.frequency) :
    rayleighJeansEquilibriumSet collision = {0} :=
  rayleighJeansEquilibriumSet_eq_singleton_zero_of_hasAcousticMassAtZero
    collision hacoustic

theorem problem_acousticRayleighJeans_no_uniformPositiveRelaxation
    (collision : ResonantThreeWaveMeasure Mode)
    {W : Real} (hW : 0 < W)
    (hlower :
      volume.restrict (additiveFrequencyTriangle W) ≪
        (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W))
    {floor : Real} (hfloor : 0 < floor)
    (trajectory : Real -> CanonicalLInfinity collision)
    (hactionFloor : forall t, 0 <= t ->
      AELowerBound collision floor (trajectory t)) :
    ¬ Tendsto
      (fun t => rayleighJeansDistance collision (trajectory t))
      atTop (nhds 0) :=
  not_tendsto_rayleighJeansDistance_zero_of_childTriangleDominance_uniformPositiveBuffer
    collision hW hlower hfloor trajectory hactionFloor

#print axioms problem_acousticRayleighJeansAction_not_memLp
#print axioms problem_acousticRayleighJeansEquilibria_eq_zero
#print axioms problem_acousticRayleighJeans_no_uniformPositiveRelaxation

end

end ArchonPhysicsConsumers.Thermalization.AcousticRayleighJeansLInfinityObstruction
