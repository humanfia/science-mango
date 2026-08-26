import ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
import ArchonPhysics.TwoTimeKineticHittingBounds

/-!
# Release-level finite three-wave kinetic family

The enhanced kinetic certificate identifies one robust crossing time and
therefore assumes strict antitonicity of the complete late-window distance.
The first release goal only asks for two positive finite constants.  This
module packages exactly that weaker endpoint: initial separation, continuity
at zero, and relaxation to equipartition produce a robust hitting window and
an exact finite-network F2 certificate.
-/

namespace ArchonPhysics.TwoTimeFiniteThreeWaveKineticFamily

open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.TwoTimeKineticHittingBounds
open Filter

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad] [Nonempty Mode]

/-- Analytic contracts sufficient for the two-sided release law.  Unlike
`AnalyticRelaxationContracts`, this structure has no strict-antitonicity
field. -/
structure ReleaseAnalyticRelaxationContracts
    (model : FiniteCollisionModel Mode Triad)
    (trajectory : Real -> (Mode -> Real))
    (mu delta : Real) : Prop where
  mu_nonnegative : 0 <= mu
  mu_less_one : mu < 1
  threshold_positive : 0 < delta
  threshold_below_initial :
    delta < kineticEquipartitionProfile model.collisionData trajectory mu 0
  distance_continuousAt_zero : ContinuousAt
    (kineticEquipartitionProfile model.collisionData trajectory mu) 0
  relaxationToEquipartition : Tendsto
    (kineticEquipartitionProfile model.collisionData trajectory mu)
    atTop (nhds 0)

/-- The release-level contracts are exactly a two-time relaxation contract
for the physical kinetic observable. -/
theorem ReleaseAnalyticRelaxationContracts.toRelaxationToTwoTimeWindow
    {model : FiniteCollisionModel Mode Triad}
    {trajectory : Real -> (Mode -> Real)} {mu delta : Real}
    (contracts : ReleaseAnalyticRelaxationContracts
      model trajectory mu delta) :
    RelaxationToTwoTimeWindow
      (kineticEquipartitionProfile model.collisionData trajectory mu)
      delta where
  threshold_pos := contracts.threshold_positive
  initial_above := contracts.threshold_below_initial
  continuousAt_zero := contracts.distance_continuousAt_zero
  tendsto_zero := contracts.relaxationToEquipartition

/-- Release contracts produce positive finite lower and upper kinetic times
with the margins required for stable threshold transfer. -/
theorem ReleaseAnalyticRelaxationContracts.exists_robustKineticHittingWindow
    {model : FiniteCollisionModel Mode Triad}
    {trajectory : Real -> (Mode -> Real)} {mu delta : Real}
    (contracts : ReleaseAnalyticRelaxationContracts
      model trajectory mu delta) :
    exists lower upper : Real,
      RobustKineticHittingWindow
        (kineticEquipartitionProfile model.collisionData trajectory mu)
        delta lower upper := by
  exact contracts.toRelaxationToTwoTimeWindow
    |>.exists_robustKineticHittingWindow

/-- Complete finite-network F2 certificate for the first, two-sided release
law.  Global flow is constructed; only actual kernel relaxation remains an
analytic input. -/
structure TwoTimeF2Certificate
    (model : FiniteCollisionModel Mode Triad)
    (actionZero : Mode -> Real) (mu delta : Real) where
  unitFlow : GlobalForwardCertificate model 1 actionZero
  initialEnergy_positive :
    0 < totalKineticEnergy model.frequency actionZero
  relaxation : ReleaseAnalyticRelaxationContracts
    model unitFlow.trajectory mu delta
  lower : Real
  upper : Real
  robust_window : RobustKineticHittingWindow
    (kineticEquipartitionProfile model.collisionData unitFlow.trajectory mu)
    delta lower upper

/-- Every constructed global flow satisfying the weaker release contracts
produces a two-time F2 certificate. -/
theorem exists_twoTimeF2Certificate
    (model : FiniteCollisionModel Mode Triad)
    (actionZero : Mode -> Real)
    (hactionZero : forall i, 0 <= actionZero i)
    (hinitialEnergy : 0 < totalKineticEnergy model.frequency actionZero)
    (mu delta : Real)
    (hcontracts : forall flow : GlobalForwardCertificate
      model 1 actionZero,
      ReleaseAnalyticRelaxationContracts
        model flow.trajectory mu delta) :
    exists _certificate : TwoTimeF2Certificate
      model actionZero mu delta, True := by
  obtain ⟨flow, _⟩ := exists_globalForwardCertificate
    model 1 actionZero hactionZero
  let contracts := hcontracts flow
  obtain ⟨lower, upper, window⟩ :=
    contracts.exists_robustKineticHittingWindow
  exact ⟨⟨flow, hinitialEnergy, contracts, lower, upper, window⟩, trivial⟩

end

end ArchonPhysics.TwoTimeFiniteThreeWaveKineticFamily
