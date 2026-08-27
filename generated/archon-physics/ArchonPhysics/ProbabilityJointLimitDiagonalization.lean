import ArchonPhysics.QualitativeJointLimitDiagonalization
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Probability joint-limit diagonalization

Convergence in measure supplies a qualitative tail cutoff for every fixed
positive distance threshold.  For a nonnegative coupling amplification
`amplification`, choose the threshold

`g / (amplification g + 1)`.

At every positive coupling, a volume cutoff can therefore make the real
probability of the corresponding bad event smaller than `g`.  Along every
joint path admitted by those cutoffs, the bad-event probabilities tend to
zero and the amplified distance threshold is bounded by the coupling.  No
rate of convergence in measure is assumed or extracted.
-/

namespace ArchonPhysics.ProbabilityJointLimitDiagonalization

open ArchonPhysics.QualitativeJointLimitDiagonalization
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-- The distance threshold that absorbs an arbitrary nonnegative coupling
amplification. -/
def probabilityDiagonalThreshold
    (amplification : Real -> Real) (g : Real) : Real :=
  g / (amplification g + 1)

/-- Failure of the target approximation at the diagonal distance threshold. -/
def probabilityDiagonalBadEvent
    (X : Nat -> Omega -> E) (target : Omega -> E)
    (amplification : Real -> Real) (N : Nat) (g : Real) : Set Omega :=
  {omega | probabilityDiagonalThreshold amplification g <=
    dist (X N omega) (target omega)}

theorem probabilityDiagonalThreshold_pos
    (amplification : Real -> Real)
    (hamplification : forall g, 0 <= amplification g)
    {g : Real} (hg : 0 < g) :
    0 < probabilityDiagonalThreshold amplification g := by
  unfold probabilityDiagonalThreshold
  exact div_pos hg (by linarith [hamplification g])

/-- The threshold multiplied by its amplification is no larger than the
coupling that selected it. -/
theorem probabilityDiagonalThreshold_mul_amplification_le
    (amplification : Real -> Real)
    (hamplification : forall g, 0 <= amplification g)
    {g : Real} (hg : 0 < g) :
    probabilityDiagonalThreshold amplification g * amplification g <= g := by
  have hdenominator : 0 < amplification g + 1 := by
    linarith [hamplification g]
  calc
    probabilityDiagonalThreshold amplification g * amplification g =
        (g * amplification g) / (amplification g + 1) := by
      unfold probabilityDiagonalThreshold
      ring
    _ <= g := by
      rw [div_le_iff₀ hdenominator]
      nlinarith [hamplification g, hg]

/-- At a fixed positive coupling, convergence in measure makes the real
probability of the diagonal bad event tend to zero with volume. -/
theorem probabilityDiagonalBadEvent_probability_tendsto_zero
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> E) (target : Omega -> E)
    (amplification : Real -> Real)
    (hX : TendstoInMeasure mu X atTop target)
    (hamplification : forall g, 0 <= amplification g)
    {g : Real} (hg : 0 < g) :
    Tendsto
      (fun N => mu.real
        (probabilityDiagonalBadEvent X target amplification N g))
      atTop (nhds 0) := by
  exact (tendstoInMeasure_iff_measureReal_dist.mp hX)
    (probabilityDiagonalThreshold amplification g)
    (probabilityDiagonalThreshold_pos amplification hamplification hg)

/-- A qualitative, coupling-dependent volume cutoff extracted from
convergence in measure.  Its value outside the positive-threshold regime is
irrelevant and is fixed to zero. -/
def probabilityJointSizeCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> E) (target : Omega -> E)
    (amplification : Real -> Real)
    (hX : TendstoInMeasure mu X atTop target) : Real -> Nat :=
  fun g =>
    if hthreshold : 0 < probabilityDiagonalThreshold amplification g then
      vanishingErrorCutoff
        (fun N => mu.real
          (probabilityDiagonalBadEvent X target amplification N g))
        ((tendstoInMeasure_iff_measureReal_dist.mp hX)
          (probabilityDiagonalThreshold amplification g) hthreshold)
        g
    else 0

/-- Above the selected cutoff, the diagonal bad-event probability is
strictly smaller than the positive coupling. -/
theorem probabilityDiagonalBadEvent_probability_lt_of_cutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> E) (target : Omega -> E)
    (amplification : Real -> Real)
    (hX : TendstoInMeasure mu X atTop target)
    (hamplification : forall g, 0 <= amplification g)
    {g : Real} (hg : 0 < g) {N : Nat}
    (hN : probabilityJointSizeCutoff
      mu X target amplification hX g <= N) :
    mu.real (probabilityDiagonalBadEvent X target amplification N g) < g := by
  have hthreshold :
      0 < probabilityDiagonalThreshold amplification g :=
    probabilityDiagonalThreshold_pos amplification hamplification hg
  unfold probabilityJointSizeCutoff at hN
  rw [dif_pos hthreshold] at hN
  exact error_lt_of_vanishingErrorCutoff
    (fun M => mu.real
      (probabilityDiagonalBadEvent X target amplification M g))
    ((tendstoInMeasure_iff_measureReal_dist.mp hX)
      (probabilityDiagonalThreshold amplification g) hthreshold)
    hg hN

/-- Every admitted joint path eventually has bad-event probability at most
its current coupling. -/
theorem eventually_probabilityDiagonalBadEvent_probability_le_coupling
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> E) (target : Omega -> E)
    (amplification : Real -> Real)
    (hX : TendstoInMeasure mu X atTop target)
    (hamplification : forall g, 0 <= amplification g)
    (s : AdmissibleJointLimit
      (probabilityJointSizeCutoff mu X target amplification hX)) :
    ∀ᶠ j in atTop,
      mu.real (probabilityDiagonalBadEvent X target amplification
        (s.systemSize j) (s.coupling j)) <= s.coupling j := by
  filter_upwards [s.eventually_sizeCutoff] with j hj
  exact (probabilityDiagonalBadEvent_probability_lt_of_cutoff
    mu X target amplification hX hamplification
    (s.coupling_pos j) hj).le

/-- The diagonal bad-event probabilities vanish along every admitted joint
path. -/
theorem probabilityDiagonalBadEvent_probability_along_jointLimit_tendsto_zero
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> E) (target : Omega -> E)
    (amplification : Real -> Real)
    (hX : TendstoInMeasure mu X atTop target)
    (hamplification : forall g, 0 <= amplification g)
    (s : AdmissibleJointLimit
      (probabilityJointSizeCutoff mu X target amplification hX)) :
    Tendsto
      (fun j => mu.real
        (probabilityDiagonalBadEvent X target amplification
          (s.systemSize j) (s.coupling j)))
      atTop (nhds 0) := by
  have hcoupling : Tendsto s.coupling atTop (nhds 0) :=
    s.coupling_tendsto_zero.mono_right inf_le_left
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun _j => measureReal_nonneg)
    (eventually_probabilityDiagonalBadEvent_probability_le_coupling
      mu X target amplification hX hamplification s)
    hcoupling

/-- Along every admitted joint path, the threshold-amplification product is
pointwise bounded by the coupling and hence tends to zero. -/
theorem probabilityDiagonalThreshold_mul_amplification_along_jointLimit_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> E) (target : Omega -> E)
    (amplification : Real -> Real)
    (hX : TendstoInMeasure mu X atTop target)
    (hamplification : forall g, 0 <= amplification g)
    (s : AdmissibleJointLimit
      (probabilityJointSizeCutoff mu X target amplification hX))
    (j : Nat) :
    probabilityDiagonalThreshold amplification (s.coupling j) *
        amplification (s.coupling j) <= s.coupling j :=
  probabilityDiagonalThreshold_mul_amplification_le
    amplification hamplification (s.coupling_pos j)

/-- Bundled probability diagonalization: one qualitative cutoff works for
every admitted joint path, without an explicit finite-volume rate. -/
theorem exists_sizeCutoff_for_tendstoInMeasure_jointLimit
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> E) (target : Omega -> E)
    (amplification : Real -> Real)
    (hX : TendstoInMeasure mu X atTop target)
    (hamplification : forall g, 0 <= amplification g) :
    exists sizeCutoff : Real -> Nat,
      forall s : AdmissibleJointLimit sizeCutoff,
        (∀ᶠ j in atTop,
          mu.real (probabilityDiagonalBadEvent X target amplification
            (s.systemSize j) (s.coupling j)) <= s.coupling j) /\
        Tendsto
          (fun j => mu.real
            (probabilityDiagonalBadEvent X target amplification
              (s.systemSize j) (s.coupling j)))
          atTop (nhds 0) /\
        forall j,
          probabilityDiagonalThreshold amplification (s.coupling j) *
              amplification (s.coupling j) <= s.coupling j := by
  refine ⟨probabilityJointSizeCutoff mu X target amplification hX, ?_⟩
  intro s
  exact ⟨eventually_probabilityDiagonalBadEvent_probability_le_coupling
      mu X target amplification hX hamplification s,
    probabilityDiagonalBadEvent_probability_along_jointLimit_tendsto_zero
      mu X target amplification hX hamplification s,
    probabilityDiagonalThreshold_mul_amplification_along_jointLimit_le
      mu X target amplification hX hamplification s⟩

end

end ArchonPhysics.ProbabilityJointLimitDiagonalization
