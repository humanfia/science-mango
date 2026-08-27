import ArchonPhysics.ProbabilityJointLimitDiagonalization

/-!
# Two-scale probability diagonalization

Suppose that, for every fixed integer time scale `t`, random quantities
`X t N` converge in probability as the size `N` tends to infinity to a
deterministic center `Y t`, and that `Y t` converges to `y` as `t` tends to
infinity.  This module constructs one deterministic size cutoff for every
`t`.  Above that cutoff the fixed-time bad-event probability is smaller than
`1 / (t + 1)` at the same distance threshold.

Consequently every path whose time tends to infinity and whose size is
eventually above the selected cutoff converges in probability to `y`.  No
uniform-in-time finite-size estimate or explicit convergence rate is assumed.
-/

namespace ArchonPhysics.TwoScaleProbabilityDiagonalization

open ArchonPhysics.QualitativeJointLimitDiagonalization
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-- The simultaneous distance and bad-event probability tolerance at integer
time scale `t`. -/
def twoScaleProbabilityTolerance (t : Nat) : Real :=
  1 / ((t : Real) + 1)

theorem twoScaleProbabilityTolerance_pos (t : Nat) :
    0 < twoScaleProbabilityTolerance t := by
  unfold twoScaleProbabilityTolerance
  positivity

theorem twoScaleProbabilityTolerance_tendsto_zero :
    Tendsto twoScaleProbabilityTolerance atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Failure of the fixed-time approximation at tolerance `1 / (t + 1)`. -/
def twoScaleProbabilityBadEvent
    (X : Nat -> Nat -> Omega -> E) (Y : Nat -> E)
    (t N : Nat) : Set Omega :=
  {omega | twoScaleProbabilityTolerance t <=
    dist (X t N omega) (Y t)}

/-- A deterministic volume cutoff at every integer time scale.  Fixed-time
convergence in probability guarantees that this cutoff makes the associated
bad-event probability smaller than `1 / (t + 1)`. -/
def twoScaleProbabilitySizeCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Nat -> Omega -> E) (Y : Nat -> E)
    (hX : forall t,
      TendstoInMeasure mu (X t) atTop (fun _omega => Y t)) :
    Nat -> Nat :=
  fun t => vanishingErrorCutoff
    (fun N => mu.real (twoScaleProbabilityBadEvent X Y t N))
    (by
      simpa [twoScaleProbabilityBadEvent] using
        ((tendstoInMeasure_iff_measureReal_dist.mp (hX t))
          (twoScaleProbabilityTolerance t)
          (twoScaleProbabilityTolerance_pos t)))
    (twoScaleProbabilityTolerance t)

/-- Above the selected fixed-time cutoff, the bad-event probability is
strictly smaller than `1 / (t + 1)`. -/
theorem twoScaleProbabilityBadEvent_probability_lt_of_cutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Nat -> Omega -> E) (Y : Nat -> E)
    (hX : forall t,
      TendstoInMeasure mu (X t) atTop (fun _omega => Y t))
    (t : Nat) {N : Nat}
    (hN : twoScaleProbabilitySizeCutoff mu X Y hX t <= N) :
    mu.real (twoScaleProbabilityBadEvent X Y t N) <
      twoScaleProbabilityTolerance t := by
  unfold twoScaleProbabilitySizeCutoff at hN
  exact error_lt_of_vanishingErrorCutoff
    (fun M => mu.real (twoScaleProbabilityBadEvent X Y t M))
    (by
      simpa [twoScaleProbabilityBadEvent] using
        ((tendstoInMeasure_iff_measureReal_dist.mp (hX t))
          (twoScaleProbabilityTolerance t)
          (twoScaleProbabilityTolerance_pos t)))
    (twoScaleProbabilityTolerance_pos t) hN

/-- Any path with diverging integer time and size eventually above the
deterministic cutoff converges in probability to the limiting deterministic
center. -/
theorem tendstoInMeasure_along_twoScaleProbabilitySizeCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Nat -> Omega -> E) (Y : Nat -> E) (y : E)
    (hX : forall t,
      TendstoInMeasure mu (X t) atTop (fun _omega => Y t))
    (hY : Tendsto Y atTop (nhds y))
    (timeIndex sizeIndex : Nat -> Nat)
    (htime : Tendsto timeIndex atTop atTop)
    (hcutoff : ∀ᶠ j in atTop,
      twoScaleProbabilitySizeCutoff mu X Y hX (timeIndex j) <= sizeIndex j) :
    TendstoInMeasure mu
      (fun j omega => X (timeIndex j) (sizeIndex j) omega)
      atTop (fun _omega => y) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  have htolerance : Tendsto
      (fun j => twoScaleProbabilityTolerance (timeIndex j))
      atTop (nhds 0) :=
    twoScaleProbabilityTolerance_tendsto_zero.comp htime
  have hcenter : Tendsto (fun j => dist (Y (timeIndex j)) y)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (hY.comp htime).dist
        (tendsto_const_nhds :
          Tendsto (fun _j : Nat => y) atTop (nhds y))
  have htoleranceClose : ∀ᶠ j in atTop,
      twoScaleProbabilityTolerance (timeIndex j) < epsilon / 2 :=
    htolerance.eventually (Iio_mem_nhds (half_pos hepsilon))
  have hcenterClose : ∀ᶠ j in atTop,
      dist (Y (timeIndex j)) y < epsilon / 2 :=
    hcenter.eventually (Iio_mem_nhds (half_pos hepsilon))
  have htargetLeBad : ∀ᶠ j in atTop,
      mu.real {omega | epsilon <=
          dist (X (timeIndex j) (sizeIndex j) omega) y} <=
        mu.real (twoScaleProbabilityBadEvent X Y
          (timeIndex j) (sizeIndex j)) := by
    filter_upwards [htoleranceClose, hcenterClose] with
        j htoleranceJ hcenterJ
    apply measureReal_mono (h₂ := by finiteness)
    intro omega homega
    change epsilon <=
      dist (X (timeIndex j) (sizeIndex j) omega) y at homega
    change twoScaleProbabilityTolerance (timeIndex j) <=
      dist (X (timeIndex j) (sizeIndex j) omega) (Y (timeIndex j))
    have htriangle := dist_triangle
      (X (timeIndex j) (sizeIndex j) omega) (Y (timeIndex j)) y
    linarith
  have hbadLeTolerance : ∀ᶠ j in atTop,
      mu.real (twoScaleProbabilityBadEvent X Y
          (timeIndex j) (sizeIndex j)) <=
        twoScaleProbabilityTolerance (timeIndex j) := by
    filter_upwards [hcutoff] with j hj
    exact (twoScaleProbabilityBadEvent_probability_lt_of_cutoff
      mu X Y hX (timeIndex j) hj).le
  have htargetLeTolerance : ∀ᶠ j in atTop,
      mu.real {omega | epsilon <=
          dist (X (timeIndex j) (sizeIndex j) omega) y} <=
        twoScaleProbabilityTolerance (timeIndex j) := by
    filter_upwards [htargetLeBad, hbadLeTolerance] with j hj hk
    exact hj.trans hk
  exact squeeze_zero'
    (Eventually.of_forall fun _j => measureReal_nonneg)
    htargetLeTolerance htolerance

/-- Bundled existence form of the two-scale diagonalization theorem. -/
theorem exists_sizeCutoff_for_twoScale_tendstoInMeasure
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Nat -> Nat -> Omega -> E) (Y : Nat -> E) (y : E)
    (hX : forall t,
      TendstoInMeasure mu (X t) atTop (fun _omega => Y t))
    (hY : Tendsto Y atTop (nhds y)) :
    exists sizeCutoff : Nat -> Nat,
      forall timeIndex sizeIndex : Nat -> Nat,
        Tendsto timeIndex atTop atTop ->
        (∀ᶠ j in atTop, sizeCutoff (timeIndex j) <= sizeIndex j) ->
        TendstoInMeasure mu
          (fun j omega => X (timeIndex j) (sizeIndex j) omega)
          atTop (fun _omega => y) := by
  use twoScaleProbabilitySizeCutoff mu X Y hX
  intro timeIndex sizeIndex htime hcutoff
  exact tendstoInMeasure_along_twoScaleProbabilitySizeCutoff
    mu X Y y hX hY timeIndex sizeIndex htime hcutoff

end

end ArchonPhysics.TwoScaleProbabilityDiagonalization
