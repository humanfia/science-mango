import ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity
import ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation

/-!
# Uniform continuity of dissipation along compact RN collision orbits

A compact canonical `L∞` orbit has a uniform norm radius.  The quadratic RN
collision bound therefore gives a uniform derivative bound and hence a
Lipschitz trajectory on the forward half-line.  Heine--Cantor supplies uniform
continuity of genuine canonical entropy production on the compact state set;
composition removes the time-uniform-continuity hypothesis from Barbalat.
-/

namespace ArchonPhysics.CanonicalLInfinityCompactOrbitDissipationUniformContinuity

open Metric Set
open ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A compact forward RN orbit is Lipschitz in time.  The Lipschitz constant
is generated from a compact norm radius and the genuine quadratic collision
speed bound; no external trajectory modulus is assumed. -/
theorem exists_lipschitzOnWith_trajectory_of_compact_rnCollisionODE
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (states : Set (CanonicalLInfinity collision)) (hstates : IsCompact states)
    (trajectory : Real → CanonicalLInfinity collision)
    (htrajectory : ∀ t, 0 ≤ t → trajectory t ∈ states)
    (htrajectoryODE : ∀ t, 0 ≤ t →
      HasDerivAt trajectory
        (rnCollisionVectorField collision g (trajectory t)) t) :
    ∃ K : NNReal, LipschitzOnWith K trajectory (Ici 0) := by
  obtain ⟨radius, hstatesRadius⟩ :=
    hstates.isBounded.subset_closedBall
      (0 : CanonicalLInfinity collision)
  have hradius : 0 ≤ radius := by
    have hzero := hstatesRadius (htrajectory 0 le_rfl)
    have hnorm : ‖trajectory 0‖ ≤ radius := by
      simpa only [mem_closedBall, dist_zero_right] using hzero
    exact (norm_nonneg _).trans hnorm
  let K := Real.toNNReal (3 * g ^ 2 * radius ^ 2)
  refine ⟨K, ?_⟩
  have hconstant : 0 ≤ 3 * g ^ 2 * radius ^ 2 := by positivity
  apply (convex_Ici 0).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  · intro t ht
    exact (htrajectoryODE t ht).hasDerivWithinAt
  · intro t ht
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hconstant]
    calc
      ‖rnCollisionVectorField collision g (trajectory t)‖ ≤
          3 * g ^ 2 * ‖trajectory t‖ ^ 2 :=
        norm_rnCollisionVectorField_le collision g (trajectory t)
      _ ≤ 3 * g ^ 2 * radius ^ 2 := by
        gcongr
        have hclosed := hstatesRadius (htrajectory t ht)
        simpa only [mem_closedBall, dist_zero_right] using hclosed

/-- Along a compact genuine RN collision orbit, the coupling-scaled canonical
log-entropy production is automatically uniformly continuous in forward
time.  This is the exact missing regularity input for the Barbalat endpoint. -/
theorem uniformContinuousOn_scaled_canonicalLogEntropyProduction_along_compact_rnCollisionODE
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    {repairFloor : Real} (hrepairFloor : 0 < repairFloor)
    (states : Set (CanonicalLInfinity collision)) (hstates : IsCompact states)
    (trajectory : Real → CanonicalLInfinity collision)
    (htrajectory : ∀ t, 0 ≤ t → trajectory t ∈ states)
    (htrajectoryODE : ∀ t, 0 ≤ t →
      HasDerivAt trajectory
        (rnCollisionVectorField collision g (trajectory t)) t) :
    UniformContinuousOn
      (fun t => g ^ 2 * canonicalLogEntropyProduction
        collision repairFloor (trajectory t)) (Ici 0) := by
  obtain ⟨K, htrajectoryLipschitz⟩ :=
    exists_lipschitzOnWith_trajectory_of_compact_rnCollisionODE
      collision g states hstates trajectory htrajectory htrajectoryODE
  have hdissipationContinuous : ContinuousOn
      (fun action : CanonicalLInfinity collision =>
        g ^ 2 * canonicalLogEntropyProduction collision repairFloor action)
      states :=
    (continuous_const.mul
      (continuous_canonicalLogEntropyProduction
        collision hrepairFloor)).continuousOn
  have hdissipationUniform : UniformContinuousOn
      (fun action : CanonicalLInfinity collision =>
        g ^ 2 * canonicalLogEntropyProduction collision repairFloor action)
      states :=
    hstates.uniformContinuousOn_of_continuous hdissipationContinuous
  rw [Metric.uniformContinuousOn_iff]
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hclose⟩ :=
    (Metric.uniformContinuousOn_iff.mp hdissipationUniform)
      epsilon hepsilon
  have hKnonnegative : 0 ≤ (K : Real) := K.coe_nonneg
  have hdenominator : 0 < (K : Real) + 1 := by positivity
  refine ⟨delta / ((K : Real) + 1),
    div_pos hdelta hdenominator, ?_⟩
  intro s hs t ht hst
  apply hclose (trajectory s) (htrajectory s hs)
    (trajectory t) (htrajectory t ht)
  have htrajectoryDistance :=
    htrajectoryLipschitz.dist_le_mul s hs t ht
  calc
    dist (trajectory s) (trajectory t) ≤
        (K : Real) * dist s t := htrajectoryDistance
    _ < delta := by
      rw [lt_div_iff₀ hdenominator] at hst
      nlinarith [show 0 ≤ dist s t from dist_nonneg]

end

end ArchonPhysics.CanonicalLInfinityCompactOrbitDissipationUniformContinuity
