import ArchonPhysics.PhyslibFPUTIndependentHaarCouplingLowerBound

/-!
# Consumer: independent Haar coupling lower bound

This gate checks that literal independent fresh-Haar reinitialization cannot
meet a sixth-order full-state mean-distance budget when a Lipschitz observed
mode retains a fixed nonzero amplitude.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTIndependentHaarCouplingLowerBound

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.PhyslibFPUTIndependentHaarCouplingLowerBound

noncomputable section

#check deterministicAmplitude_le_meanDistance_freshHaar
#check observedAmplitude_le_lipschitz_mul_meanDistance_freshHaar
#check not_meanDistance_le_sixth_of_independent_freshHaar

/-- Consumer-level statement of the independent-reinitialization no-go. -/
theorem independent_freshHaar_excludes_sixth_fullState_meanDistance
    {d X : Type*} [Fintype d] [PseudoMetricSpace X]
    (charge : d -> Int) (hcharge : charge ≠ 0)
    (actualState : X) (referenceState : UnitAddTorus d -> X)
    (observable : X -> Complex) (A : NNReal)
    (hobservable : LipschitzWith A observable)
    (coefficient : Complex)
    (hreferenceObservable : forall phase,
      observable (referenceState phase) =
        coefficient * mFourier charge phase)
    (hstateDistanceIntegrable : Integrable
      (fun phase : UnitAddTorus d =>
        dist actualState (referenceState phase))
      (finitePhaseHaarLaw d))
    (g C r0 : Real)
    (hamplitude : r0 <= ‖observable actualState‖)
    (hseparation : (A : Real) * (C * |g| ^ 6) < r0) :
    ¬ ((∫ phase : UnitAddTorus d,
      dist actualState (referenceState phase)
      ∂finitePhaseHaarLaw d) <= C * |g| ^ 6) :=
  not_meanDistance_le_sixth_of_independent_freshHaar
    charge hcharge actualState referenceState observable A hobservable
      coefficient hreferenceObservable hstateDistanceIntegrable
      g C r0 hamplitude hseparation

#print axioms deterministicAmplitude_le_meanDistance_freshHaar
#print axioms observedAmplitude_le_lipschitz_mul_meanDistance_freshHaar
#print axioms not_meanDistance_le_sixth_of_independent_freshHaar
#print axioms independent_freshHaar_excludes_sixth_fullState_meanDistance

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTIndependentHaarCouplingLowerBound
