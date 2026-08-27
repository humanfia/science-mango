import ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Closed small-ball lower bounds under finite-measure weak limits

The closed-set half of Portmanteau has the direction needed for positive
on-shell mass.  If finite measures converge weakly and a sequence of lower
bounds converges to `lower`, then an eventual lower bound on a fixed closed
set passes to the limit.

The specialization below accepts the finite-volume estimate in its natural
real form `c * delta - error n <= mu_n {|x| <= delta}`.  It does not assume a
density and it does not turn qualitative positivity into a linear estimate.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.FiniteMeasureClosedSmallBallLowerWeakLimit

open ArchonPhysics
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- Eventual lower bounds on a closed set pass through weak convergence of
finite measures, provided the lower bounds themselves converge. -/
theorem lower_le_measure_closed_of_tendsto_of_eventually_le
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (source : Nat -> FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (closedSet : Set X) (hclosed : IsClosed closedSet)
    (lower : Nat -> ENNReal) (limitLower : ENNReal)
    (hlower : Tendsto lower atTop (nhds limitLower))
    (hbound : ∀ᶠ n in atTop,
      lower n <= (source n : Measure X) closedSet) :
    limitLower <= (target : Measure X) closedSet := by
  have hportmanteau :=
    FiniteMeasure.limsup_measure_closed_le_of_tendsto hlimit hclosed
  have hlowerLimsup :
      atTop.limsup lower <=
        atTop.limsup (fun n => (source n : Measure X) closedSet) :=
    Filter.limsup_le_limsup hbound
  calc
    limitLower = atTop.limsup lower := hlower.limsup_eq.symm
    _ <= atTop.limsup (fun n => (source n : Measure X) closedSet) :=
      hlowerLimsup
    _ <= (target : Measure X) closedSet := hportmanteau

/-- A finite-volume linear lower small-ball bound with a vanishing additive
error passes to the weak limit on every fixed closed mismatch window. -/
theorem finiteMeasure_absoluteMismatchSublevel_ge_of_linearLower_with_vanishingError
    (source : Nat -> FiniteMeasure Real) (target : FiniteMeasure Real)
    (hlimit : Tendsto source atTop (nhds target))
    (constant : Real) (_hconstant : 0 <= constant)
    (error : Nat -> Real) (herror : Tendsto error atTop (nhds 0))
    (hbound : forall n : Nat, forall delta : Real,
      0 < delta -> delta <= 1 ->
      constant * delta - error n <=
        ((source n : Measure Real)
          (absoluteMismatchSublevel delta)).toReal) :
    forall delta : Real, 0 < delta -> delta <= 1 ->
      ENNReal.ofReal (constant * delta) <=
        (target : Measure Real) (absoluteMismatchSublevel delta) := by
  intro delta hdelta hdeltaOne
  have hlowerReal : Tendsto
      (fun n => constant * delta - error n) atTop
      (nhds (constant * delta)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto
          (fun _n : Nat => constant * delta) atTop
          (nhds (constant * delta))).sub herror)
  have hlowerENN : Tendsto
      (fun n => ENNReal.ofReal (constant * delta - error n)) atTop
      (nhds (ENNReal.ofReal (constant * delta))) :=
    ENNReal.tendsto_ofReal hlowerReal
  apply lower_le_measure_closed_of_tendsto_of_eventually_le
    source target hlimit (absoluteMismatchSublevel delta)
    (isClosed_le continuous_abs continuous_const)
    (fun n => ENNReal.ofReal (constant * delta - error n))
    (ENNReal.ofReal (constant * delta)) hlowerENN
  exact Filter.Eventually.of_forall fun n =>
    ENNReal.ofReal_le_of_le_toReal
      (hbound n delta hdelta hdeltaOne)

/-- Real-valued form of the preceding limit lower bound. -/
theorem finiteMeasure_absoluteMismatchSublevel_toReal_ge_of_linearLower_with_vanishingError
    (source : Nat -> FiniteMeasure Real) (target : FiniteMeasure Real)
    (hlimit : Tendsto source atTop (nhds target))
    (constant : Real) (hconstant : 0 <= constant)
    (error : Nat -> Real) (herror : Tendsto error atTop (nhds 0))
    (hbound : forall n : Nat, forall delta : Real,
      0 < delta -> delta <= 1 ->
      constant * delta - error n <=
        ((source n : Measure Real)
          (absoluteMismatchSublevel delta)).toReal)
    (delta : Real) (hdelta : 0 < delta) (hdeltaOne : delta <= 1) :
    constant * delta <=
      ((target : Measure Real)
        (absoluteMismatchSublevel delta)).toReal := by
  have hENN :=
    finiteMeasure_absoluteMismatchSublevel_ge_of_linearLower_with_vanishingError
      source target hlimit constant hconstant error herror hbound
      delta hdelta hdeltaOne
  have hfinite :
      (target : Measure Real) (absoluteMismatchSublevel delta) ≠ ∞ :=
    measure_ne_top _ _
  exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hENN

end

end ArchonPhysics.FiniteMeasureClosedSmallBallLowerWeakLimit
