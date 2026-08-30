import ArchonPhysics.FiniteDuhamelPhaseAverage

/-!
# Independent Haar reinitialization has a full-state coupling lower bound

The full-state RPA interfaces permit the reference state to be coupled with
the actual state on an arbitrary common probability space.  Such an optimal,
correlated coupling need not conflict with Hamiltonian reversibility.

Literal fresh re-Haarization is different: conditional on a deterministic
actual state, the new phase is independent and Haar.  Every nonzero Fourier
character then has zero mean.  The norm-of-integral inequality shows that the
mean amplitude displacement is at least the norm of the actual amplitude.
After a Lipschitz observation map, this gives a lower bound on the mean
full-state distance.  In particular, that distance cannot be `O(|g|^6)` at
fixed nonzero modal amplitude merely by drawing an independent fresh phase.

This is a no-go statement for the independent product coupling.  It does not
rule out Wasserstein closeness of the two marginal laws under an optimized
correlated coupling, nor does reversibility alone imply such a lower bound.
-/

namespace ArchonPhysics.PhyslibFPUTIndependentHaarCouplingLowerBound

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/- Use the normalized Haar probability law underlying the finite phase
moment API. -/
local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

/-- Conditional on one deterministic complex amplitude, replacing its phase
by an independent nonzero Haar character costs at least the norm of the
deterministic amplitude in mean distance. -/
theorem deterministicAmplitude_le_meanDistance_freshHaar
    {d : Type*} [Fintype d]
    (charge : d -> Int) (hcharge : charge ≠ 0)
    (actual coefficient : Complex) :
    ‖actual‖ <=
      ∫ phase : UnitAddTorus d,
        ‖actual - coefficient * mFourier charge phase‖
        ∂finitePhaseHaarLaw d := by
  have hreference : Integrable
      (fun phase : UnitAddTorus d =>
        coefficient * mFourier charge phase)
      (finitePhaseHaarLaw d) :=
    (integrable_mFourier_finitePhaseHaarLaw charge).const_mul coefficient
  have hactual : Integrable
      (fun _phase : UnitAddTorus d => actual)
      (finitePhaseHaarLaw d) :=
    integrable_const actual
  have hreferenceMean :
      (∫ phase : UnitAddTorus d,
        coefficient * mFourier charge phase
        ∂finitePhaseHaarLaw d) = 0 := by
    rw [integral_const_mul, integral_mFourier_eq_zero hcharge, mul_zero]
  have hactualMean :
      (∫ _phase : UnitAddTorus d, actual ∂finitePhaseHaarLaw d) = actual := by
    simp
  have hmean :
      (∫ phase : UnitAddTorus d,
        actual - coefficient * mFourier charge phase
        ∂finitePhaseHaarLaw d) = actual := by
    rw [integral_sub hactual hreference, hactualMean, hreferenceMean, sub_zero]
  calc
    ‖actual‖ =
        ‖∫ phase : UnitAddTorus d,
          actual - coefficient * mFourier charge phase
          ∂finitePhaseHaarLaw d‖ := by rw [hmean]
    _ <= ∫ phase : UnitAddTorus d,
        ‖actual - coefficient * mFourier charge phase‖
        ∂finitePhaseHaarLaw d :=
      norm_integral_le_integral_norm _

/-- A Lipschitz modal observable transfers the independent-Haar amplitude
lower bound to the full-state metric. -/
theorem observedAmplitude_le_lipschitz_mul_meanDistance_freshHaar
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
      (finitePhaseHaarLaw d)) :
    ‖observable actualState‖ <=
      (A : Real) *
        ∫ phase : UnitAddTorus d,
          dist actualState (referenceState phase)
          ∂finitePhaseHaarLaw d := by
  have hrawDifference : Integrable
      (fun phase : UnitAddTorus d =>
        observable actualState - coefficient * mFourier charge phase)
      (finitePhaseHaarLaw d) := by
    exact (integrable_const (observable actualState)).sub
      ((integrable_mFourier_finitePhaseHaarLaw charge).const_mul coefficient)
  have hobservedDistance : Integrable
      (fun phase : UnitAddTorus d =>
        ‖observable actualState - observable (referenceState phase)‖)
      (finitePhaseHaarLaw d) := by
    apply hrawDifference.norm.congr
    filter_upwards with phase
    rw [hreferenceObservable phase]
  have hpointwise : forall phase : UnitAddTorus d,
      ‖observable actualState - observable (referenceState phase)‖ <=
        (A : Real) * dist actualState (referenceState phase) := by
    intro phase
    simpa only [dist_eq_norm] using
      hobservable.dist_le_mul actualState (referenceState phase)
  calc
    ‖observable actualState‖ <=
        ∫ phase : UnitAddTorus d,
          ‖observable actualState - coefficient * mFourier charge phase‖
          ∂finitePhaseHaarLaw d :=
      deterministicAmplitude_le_meanDistance_freshHaar
        charge hcharge (observable actualState) coefficient
    _ = ∫ phase : UnitAddTorus d,
          ‖observable actualState - observable (referenceState phase)‖
          ∂finitePhaseHaarLaw d := by
      apply integral_congr_ae
      filter_upwards with phase
      rw [hreferenceObservable phase]
    _ <= ∫ phase : UnitAddTorus d,
          (A : Real) * dist actualState (referenceState phase)
          ∂finitePhaseHaarLaw d := by
      exact integral_mono hobservedDistance
        (hstateDistanceIntegrable.const_mul (A : Real)) hpointwise
    _ = (A : Real) *
        ∫ phase : UnitAddTorus d,
          dist actualState (referenceState phase)
          ∂finitePhaseHaarLaw d := by
      rw [integral_const_mul]

/-- Quantitative sixth-order no-go.  If the observed actual amplitude stays
above `r0`, and the proposed sixth-order budget is too small to cover that
amplitude after the observation Lipschitz constant, literal independent Haar
reinitialization cannot satisfy the proposed mean full-state bound. -/
theorem not_meanDistance_le_sixth_of_independent_freshHaar
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
    (hseparation :
      (A : Real) * (C * |g| ^ 6) < r0) :
    ¬ ((∫ phase : UnitAddTorus d,
      dist actualState (referenceState phase)
      ∂finitePhaseHaarLaw d) <= C * |g| ^ 6) := by
  intro hmeanSixth
  have hlower :=
    observedAmplitude_le_lipschitz_mul_meanDistance_freshHaar
      charge hcharge actualState referenceState observable A hobservable
        coefficient hreferenceObservable hstateDistanceIntegrable
  have hupper :
      ‖observable actualState‖ <= (A : Real) * (C * |g| ^ 6) :=
    hlower.trans
      (mul_le_mul_of_nonneg_left hmeanSixth A.coe_nonneg)
  exact (not_le_of_gt hseparation) (hamplitude.trans hupper)

end

end ArchonPhysics.PhyslibFPUTIndependentHaarCouplingLowerBound
