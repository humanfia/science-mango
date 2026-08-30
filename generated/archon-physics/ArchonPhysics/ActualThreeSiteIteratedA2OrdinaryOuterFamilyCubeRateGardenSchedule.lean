import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
import ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule

/-!
# Actual ordinary-outer-family cube-rate garden schedule

This module inserts the *actual* four-history ordinary outer near-mismatch event
into the cube-rate garden estimate.  At the sextic cutoff `|g|^6`, its ENNReal
and real bad budgets are bounded by `840 * |g|^2`.  The same actual family event
is then used, separately and explicitly, as the quadratic and quartic bad term
in the kinetic-time estimate.

The regular-good garden envelopes remain hypotheses.  Thus the final theorem is
a specialization of the good/bad garden criterion, not a derivation of those
envelopes (or of Hamiltonian RPA) from microscopic dynamics.
-/

namespace ArchonPhysics
namespace ActualThreeSiteIteratedA2OrdinaryOuterFamilyCubeRateGardenSchedule

open Filter MeasureTheory Real
open scoped ENNReal Topology

open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule
open ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate
open ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- The actual ENNReal probability budget of the four ordinary outer histories
at the sextic coupling cutoff. -/
def ordinaryOuterFamilySexticCutoffBadBudgetENNReal (g : Real) : ENNReal :=
  iidMassTripleLaw
    (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
      (sexticCouplingCutoff g))

/-- Real-valued version of the actual four-history bad-event probability. -/
def ordinaryOuterFamilySexticCutoffBadBudget (g : Real) : Real :=
  (ordinaryOuterFamilySexticCutoffBadBudgetENNReal g).toReal

/-- The actual quadratic bad term: the four-history family probability. -/
def ordinaryOuterFamilyQuadraticBadBudget (g : Real) : Real :=
  ordinaryOuterFamilySexticCutoffBadBudget g

/-- The actual quartic bad term: the same four-history family probability. -/
def ordinaryOuterFamilyQuarticBadBudget (g : Real) : Real :=
  ordinaryOuterFamilySexticCutoffBadBudget g

/-- The four-history union has the same sharp cube-rate probability bound as
the underlying absolute mismatch event, including at `g = 0`. -/
theorem ordinaryOuterFamilySexticCutoffBadBudgetENNReal_le
    (g : Real) :
    ordinaryOuterFamilySexticCutoffBadBudgetENNReal g ≤
      840 * ENNReal.ofReal (squareCouplingCutoff g) := by
  by_cases hg : g = 0
  · subst g
    simp [ordinaryOuterFamilySexticCutoffBadBudgetENNReal,
      threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq,
      sexticCouplingCutoff, squareCouplingCutoff,
      iidMassTripleLaw_threeSiteOuterNearMismatchEvent_zero]
  · simpa [ordinaryOuterFamilySexticCutoffBadBudgetENNReal,
      threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq] using
      iidMassTripleLaw_threeSiteOuterNearMismatchEvent_sextic_le hg

theorem ordinaryOuterFamilySexticCutoffBadBudget_nonneg (g : Real) :
    0 ≤ ordinaryOuterFamilySexticCutoffBadBudget g := by
  exact ENNReal.toReal_nonneg

/-- Real-valued actual family budget at the sextic cutoff. -/
theorem ordinaryOuterFamilySexticCutoffBadBudget_le (g : Real) :
    ordinaryOuterFamilySexticCutoffBadBudget g ≤
      840 * squareCouplingCutoff g := by
  have hENN := ordinaryOuterFamilySexticCutoffBadBudgetENNReal_le g
  have hfinite :
      840 * ENNReal.ofReal (squareCouplingCutoff g) ≠ ⊤ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfinite hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by
      unfold squareCouplingCutoff
      positivity)] at hreal
  exact hreal

theorem ordinaryOuterFamilyQuadraticBadBudget_nonneg (g : Real) :
    0 ≤ ordinaryOuterFamilyQuadraticBadBudget g := by
  simpa [ordinaryOuterFamilyQuadraticBadBudget] using
    ordinaryOuterFamilySexticCutoffBadBudget_nonneg g

theorem ordinaryOuterFamilyQuarticBadBudget_nonneg (g : Real) :
    0 ≤ ordinaryOuterFamilyQuarticBadBudget g := by
  simpa [ordinaryOuterFamilyQuarticBadBudget] using
    ordinaryOuterFamilySexticCutoffBadBudget_nonneg g

theorem ordinaryOuterFamilyQuadraticBadBudget_le (g : Real) :
    ordinaryOuterFamilyQuadraticBadBudget g ≤
      840 * squareCouplingCutoff g := by
  simpa [ordinaryOuterFamilyQuadraticBadBudget] using
    ordinaryOuterFamilySexticCutoffBadBudget_le g

theorem ordinaryOuterFamilyQuarticBadBudget_le (g : Real) :
    ordinaryOuterFamilyQuarticBadBudget g ≤
      840 * squareCouplingCutoff g := by
  simpa [ordinaryOuterFamilyQuarticBadBudget] using
    ordinaryOuterFamilySexticCutoffBadBudget_le g

/-- Kinetic-time vanishing with both exceptional terms instantiated by the
actual four-history ordinary outer event at cutoff `|g|^6`.

The two displayed garden inequalities are the transparent regular-good
envelope assumptions that this theorem does not derive. -/
theorem coupling_channel_budget_tendsto_zero_at_kineticTime_actualOrdinaryOuterFamily
    (quadraticOrder quarticOrder : Nat)
    (g quadraticBudget quarticBudget : Nat → Real)
    (kappa beta tau : Real)
    (quadraticGoodCoefficient quarticGoodCoefficient : Real)
    (quadraticGlobal quarticGlobal : Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ n, g n ≠ 0)
    (hquadraticBudget0 : ∀ n, 0 ≤ quadraticBudget n)
    (hquarticBudget0 : ∀ n, 0 ≤ quarticBudget n)
    (hquadraticBudget : ∀ n,
      quadraticBudget n ≤
        cubeRateQuadraticGardenGoodEnvelope quadraticOrder
            quadraticGoodCoefficient (g n) +
          quadraticGlobal * ordinaryOuterFamilyQuadraticBadBudget (g n))
    (hquarticBudget : ∀ n,
      quarticBudget n ≤
        cubeRateQuarticGardenGoodEnvelope quarticOrder
            quarticGoodCoefficient (g n) +
          quarticGlobal * ordinaryOuterFamilyQuarticBadBudget (g n)) :
    Tendsto (fun n =>
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) atTop (nhds 0) := by
  exact
    coupling_channel_budget_tendsto_zero_at_kineticTime_cubeRate
      quadraticOrder quarticOrder g quadraticBudget quarticBudget
      (fun n => ordinaryOuterFamilyQuadraticBadBudget (g n))
      (fun n => ordinaryOuterFamilyQuarticBadBudget (g n))
      kappa beta tau quadraticGoodCoefficient quarticGoodCoefficient
      quadraticGlobal quarticGlobal 840 840 hg hg0
      hquadraticBudget0 hquarticBudget0
      (fun n => ordinaryOuterFamilyQuadraticBadBudget_nonneg (g n))
      (fun n => ordinaryOuterFamilyQuarticBadBudget_nonneg (g n))
      hquadraticBudget hquarticBudget
      (fun n => ordinaryOuterFamilyQuadraticBadBudget_le (g n))
      (fun n => ordinaryOuterFamilyQuarticBadBudget_le (g n))

end

end ActualThreeSiteIteratedA2OrdinaryOuterFamilyCubeRateGardenSchedule
end ArchonPhysics
