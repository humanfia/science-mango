import ArchonPhysics.MeasurableOrderedModeCoupling
import ArchonPhysics.QuantitativeEmpiricalResonanceTransfer
import ArchonPhysics.SincSquareMassExact

/-!
# Quantitative transfer for finitely marked resonance data

A collision datum consists of a real phase mismatch and a nonnegative mark
(typically a squared, frequency-normalized interaction vertex).  Its
finite-time collision action is the finite sum of the marks tested against
the normalized squared-sinc resonance peak.

This module lifts the scalar bounded-Lipschitz transfer estimate to those
weighted finite sums.  It also gives a concrete paired-data criterion: the
error is controlled by the total mark error and by the reference-mark-weighted
phase displacement.  At time `T`, these cost respectively `T / (2*pi)` and
`T^2 / pi`.

The joint-limit theorem deliberately retains the model-specific empirical
estimate as a hypothesis.  In particular, no theorem below claims that a
random-mass lattice supplies the required `epsilon_N (T_N + T_N^2) -> 0`
rate.
-/

namespace ArchonPhysics.MarkedEmpiricalResonanceTransfer

open Filter
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.QuantitativeEmpiricalResonanceTransfer
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.UniformCollisionDensityTransfer
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSpectrumContinuity

noncomputable section

/-- A finite marked collision action: each phase mismatch is tested against
the exactly normalized finite-time squared-sinc peak and weighted by its
supplied mark. -/
def markedCollisionAction {I : Type*} [Fintype I]
    (mismatch mark : I -> Real) (T : Real) : Real :=
  ∑ i, mark i * normalizedFiniteTimeResonanceKernel (mismatch i) T

/-- Nonnegative marks give a nonnegative finite-time collision action. -/
theorem markedCollisionAction_nonneg {I : Type*} [Fintype I]
    (mismatch mark : I -> Real) (T : Real)
    (hmark : forall i, 0 <= mark i) :
    0 <= markedCollisionAction mismatch mark T := by
  unfold markedCollisionAction
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hmark i)
      (normalizedFiniteTimeResonanceKernel_nonneg (mismatch i) T)

/-- The finite action is measurable when all mismatch and mark coordinates
are measurable. -/
theorem measurable_markedCollisionAction
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    (mismatch mark : Omega -> I -> Real)
    (hmismatch : forall i, Measurable fun omega => mismatch omega i)
    (hmark : forall i, Measurable fun omega => mark omega i)
    {T : Real} (hT : 0 < T) :
    Measurable fun omega =>
      markedCollisionAction (mismatch omega) (mark omega) T := by
  unfold markedCollisionAction
  apply Finset.measurable_sum
  intro i _hi
  exact (hmark i).mul
    ((continuous_normalizedFiniteTimeResonanceKernel hT).measurable.comp
      (hmismatch i))

/-- Bounded-Lipschitz error for two finite marked sums.  Unlike an ordinary
empirical probability measure, the marks are retained inside the testing
functional.  This is the minimal rate hypothesis needed by the transfer
theorems below. -/
def markedBoundedLipschitzSumError
    {I J : Type*} [Fintype I] [Fintype J]
    (mismatch : I -> Real) (mark : I -> Real)
    (referenceMismatch : J -> Real) (referenceMark : J -> Real)
    (epsilon : Real) : Prop :=
  forall (f : Real -> Real) (height slope : Real),
    0 <= height -> 0 <= slope ->
    (forall x, |f x| <= height) ->
    (forall x y, |f x - f y| <= slope * |x - y|) ->
    |(∑ i, mark i * f (mismatch i)) -
        (∑ j, referenceMark j * f (referenceMismatch j))| <=
      epsilon * (height + slope)

/-- Fixed-time marked transfer.  The exact squared-sinc mass gives the height
cost `T/(2*pi)`, while its elementary phase Lipschitz bound gives the slope
cost `T^2/pi`. -/
theorem abs_markedCollisionAction_sub_le_of_boundedLipschitzError
    {I J : Type*} [Fintype I] [Fintype J]
    (mismatch : I -> Real) (mark : I -> Real)
    (referenceMismatch : J -> Real) (referenceMark : J -> Real)
    {epsilon T : Real} (hT : 0 < T)
    (hBL : markedBoundedLipschitzSumError mismatch mark
      referenceMismatch referenceMark epsilon) :
    |markedCollisionAction mismatch mark T -
        markedCollisionAction referenceMismatch referenceMark T| <=
      epsilon * resonanceKernelBLSize T := by
  unfold markedCollisionAction resonanceKernelBLSize
  exact hBL
    (fun Omega => normalizedFiniteTimeResonanceKernel Omega T)
    (T / (2 * Real.pi)) (T ^ 2 / Real.pi)
    (by positivity) (by positivity)
    (fun Omega =>
      abs_normalizedFiniteTimeResonanceKernel_le_height Omega hT)
    (fun Omega Xi =>
      abs_normalizedFiniteTimeResonanceKernel_sub_le Omega Xi hT)

/-- Total variation of the marks for paired finite data. -/
def pairedMarkError {I : Type*} [Fintype I]
    (mark referenceMark : I -> Real) : Real :=
  ∑ i, |mark i - referenceMark i|

/-- Phase displacement weighted by the nonnegative reference marks. -/
def pairedWeightedMismatchError {I : Type*} [Fintype I]
    (mismatch referenceMismatch referenceMark : I -> Real) : Real :=
  ∑ i, referenceMark i * |mismatch i - referenceMismatch i|

/-- Paired mark and mismatch errors control every bounded Lipschitz test.
This is a deterministic finite-sum inequality, not a stochastic convergence
claim. -/
theorem abs_weightedTestSum_sub_le_pairedErrors
    {I : Type*} [Fintype I]
    (mismatch mark referenceMismatch referenceMark : I -> Real)
    (f : Real -> Real) {height slope : Real}
    (_hheight : 0 <= height) (_hslope : 0 <= slope)
    (hreferenceMark : forall i, 0 <= referenceMark i)
    (hfHeight : forall x, |f x| <= height)
    (hfSlope : forall x y,
      |f x - f y| <= slope * |x - y|) :
    |(∑ i, mark i * f (mismatch i)) -
        (∑ i, referenceMark i * f (referenceMismatch i))| <=
      height * pairedMarkError mark referenceMark +
        slope * pairedWeightedMismatchError mismatch referenceMismatch
          referenceMark := by
  have hpoint : forall i,
      |mark i * f (mismatch i) -
          referenceMark i * f (referenceMismatch i)| <=
        |mark i - referenceMark i| * height +
          referenceMark i * slope * |mismatch i - referenceMismatch i| := by
    intro i
    calc
      |mark i * f (mismatch i) -
          referenceMark i * f (referenceMismatch i)| =
          |(mark i - referenceMark i) * f (mismatch i) +
            referenceMark i *
              (f (mismatch i) - f (referenceMismatch i))| := by
            congr 1
            ring
      _ <= |(mark i - referenceMark i) * f (mismatch i)| +
          |referenceMark i *
            (f (mismatch i) - f (referenceMismatch i))| :=
        abs_add_le _ _
      _ = |mark i - referenceMark i| * |f (mismatch i)| +
          referenceMark i *
            |f (mismatch i) - f (referenceMismatch i)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hreferenceMark i)]
      _ <= |mark i - referenceMark i| * height +
          referenceMark i *
            (slope * |mismatch i - referenceMismatch i|) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hfHeight (mismatch i)) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left
            (hfSlope (mismatch i) (referenceMismatch i))
            (hreferenceMark i))
      _ = |mark i - referenceMark i| * height +
          referenceMark i * slope *
            |mismatch i - referenceMismatch i| := by ring
  calc
    |(∑ i, mark i * f (mismatch i)) -
        (∑ i, referenceMark i * f (referenceMismatch i))| =
        |∑ i, (mark i * f (mismatch i) -
          referenceMark i * f (referenceMismatch i))| := by
      rw [Finset.sum_sub_distrib]
    _ <= ∑ i, |mark i * f (mismatch i) -
        referenceMark i * f (referenceMismatch i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i, (|mark i - referenceMark i| * height +
        referenceMark i * slope *
          |mismatch i - referenceMismatch i|) :=
      Finset.sum_le_sum fun i _hi => hpoint i
    _ = height * pairedMarkError mark referenceMark +
        slope * pairedWeightedMismatchError mismatch referenceMismatch
          referenceMark := by
      simp only [pairedMarkError, pairedWeightedMismatchError,
        Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i _hi
        ring
      · apply Finset.sum_congr rfl
        intro i _hi
        ring

/-- If both paired errors are at most `epsilon`, they furnish the marked
bounded-Lipschitz hypothesis with the same `epsilon`. -/
theorem markedBoundedLipschitzSumError_of_pairedErrors
    {I : Type*} [Fintype I]
    (mismatch mark referenceMismatch referenceMark : I -> Real)
    {epsilon : Real}
    (hreferenceMark : forall i, 0 <= referenceMark i)
    (hmarkError : pairedMarkError mark referenceMark <= epsilon)
    (hmismatchError : pairedWeightedMismatchError mismatch referenceMismatch
      referenceMark <= epsilon) :
    markedBoundedLipschitzSumError mismatch mark
      referenceMismatch referenceMark epsilon := by
  intro f height slope hheight hslope hfHeight hfSlope
  calc
    |(∑ i, mark i * f (mismatch i)) -
        (∑ i, referenceMark i * f (referenceMismatch i))| <=
        height * pairedMarkError mark referenceMark +
          slope * pairedWeightedMismatchError mismatch referenceMismatch
            referenceMark :=
      abs_weightedTestSum_sub_le_pairedErrors mismatch mark
        referenceMismatch referenceMark f hheight hslope hreferenceMark
        hfHeight hfSlope
    _ <= height * epsilon + slope * epsilon :=
      add_le_add
        (mul_le_mul_of_nonneg_left hmarkError hheight)
        (mul_le_mul_of_nonneg_left hmismatchError hslope)
    _ = epsilon * (height + slope) := by ring

/-- Explicit fixed-time estimate from paired errors, with separate height and
slope costs. -/
theorem abs_markedCollisionAction_sub_le_pairedErrors
    {I : Type*} [Fintype I]
    (mismatch mark referenceMismatch referenceMark : I -> Real)
    {T : Real} (hT : 0 < T)
    (hreferenceMark : forall i, 0 <= referenceMark i) :
    |markedCollisionAction mismatch mark T -
        markedCollisionAction referenceMismatch referenceMark T| <=
      (T / (2 * Real.pi)) * pairedMarkError mark referenceMark +
        (T ^ 2 / Real.pi) *
          pairedWeightedMismatchError mismatch referenceMismatch
            referenceMark := by
  exact abs_weightedTestSum_sub_le_pairedErrors mismatch mark
    referenceMismatch referenceMark
    (fun Omega => normalizedFiniteTimeResonanceKernel Omega T)
    (by positivity) (by positivity) hreferenceMark
    (fun Omega =>
      abs_normalizedFiniteTimeResonanceKernel_le_height Omega hT)
    (fun Omega Xi =>
      abs_normalizedFiniteTimeResonanceKernel_sub_le Omega Xi hT)

/-- Joint marked transfer with the exact time-dependent BL size.  The finite
index types may vary with system size. -/
theorem tendsto_markedCollisionAction_sub_zero
    {I J : Nat -> Type*} [forall n, Fintype (I n)]
    [forall n, Fintype (J n)]
    (mismatch : forall n, I n -> Real)
    (mark : forall n, I n -> Real)
    (referenceMismatch : forall n, J n -> Real)
    (referenceMark : forall n, J n -> Real)
    {epsilon time : Nat -> Real}
    (htime : forall n, 0 < time n)
    (hBL : forall n, markedBoundedLipschitzSumError
      (mismatch n) (mark n) (referenceMismatch n) (referenceMark n)
      (epsilon n))
    (hscale : Tendsto
      (fun n => epsilon n * resonanceKernelBLSize (time n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        markedCollisionAction (mismatch n) (mark n) (time n) -
          markedCollisionAction (referenceMismatch n) (referenceMark n)
            (time n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero
    (g := fun n => epsilon n * resonanceKernelBLSize (time n))
  · intro n
    positivity
  · intro n
    rw [Real.norm_eq_abs]
    exact abs_markedCollisionAction_sub_le_of_boundedLipschitzError
      (mismatch n) (mark n) (referenceMismatch n) (referenceMark n)
      (htime n) (hBL n)
  · exact hscale

/-- Convenient joint-scale corollary: it suffices that the model-specific
marked empirical error obeys `epsilon_N (T_N + T_N^2) -> 0`. -/
theorem tendsto_markedCollisionAction_sub_zero_of_error_mul_time_add_sq
    {I J : Nat -> Type*} [forall n, Fintype (I n)]
    [forall n, Fintype (J n)]
    (mismatch : forall n, I n -> Real)
    (mark : forall n, I n -> Real)
    (referenceMismatch : forall n, J n -> Real)
    (referenceMark : forall n, J n -> Real)
    {epsilon time : Nat -> Real}
    (hepsilon : forall n, 0 <= epsilon n)
    (htime : forall n, 0 < time n)
    (hBL : forall n, markedBoundedLipschitzSumError
      (mismatch n) (mark n) (referenceMismatch n) (referenceMark n)
      (epsilon n))
    (hscale : Tendsto
      (fun n => epsilon n * (time n + time n ^ 2))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        markedCollisionAction (mismatch n) (mark n) (time n) -
          markedCollisionAction (referenceMismatch n) (referenceMark n)
            (time n))
      atTop (nhds 0) := by
  apply tendsto_markedCollisionAction_sub_zero mismatch mark
    referenceMismatch referenceMark htime hBL
  apply squeeze_zero
    (g := fun n => epsilon n * (time n + time n ^ 2))
  · intro n
    exact mul_nonneg (hepsilon n)
      (resonanceKernelBLSize_nonneg (htime n).le)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (resonanceKernelBLSize_le_time_add_sq (htime n).le)
      (hepsilon n)
  · exact hscale

/-- Signed mismatch formed from the globally ordered mode frequencies. -/
def orderedPhaseMismatch {iota : Type*} [Fintype iota] [DecidableEq iota]
    {n : Nat} (A : HermitianMatrix iota)
    (sign : Fin n -> InteractionSign)
    (modes : Fin n -> Fin (Fintype.card iota)) : Real :=
  ∑ r, (sign r).coefficient * orderedModeFrequency A (modes r)

/-- Ordered mismatch is measurable for every measurable Hermitian sample. -/
theorem measurable_orderedPhaseMismatch
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota] [DecidableEq iota] {n : Nat}
    (sample : Omega -> HermitianMatrix iota) (hsample : Measurable sample)
    (sign : Fin n -> InteractionSign)
    (modes : Fin n -> Fin (Fintype.card iota)) :
    Measurable fun omega => orderedPhaseMismatch (sample omega) sign modes := by
  unfold orderedPhaseMismatch
  apply Finset.measurable_sum
  intro r _hr
  exact measurable_const.mul
    (measurable_pi_iff.mp
      (measurable_orderedModeFrequencies_unconditional sample hsample)
      (modes r))

/-- Physical specialization using the basis-free squared ordered vertex.
The finite family of tuples is arbitrary; choosing it to be the positive-mode
collision domain is a separate finite combinatorial construction. -/
def harmonicOrderedMarkedCollisionAction
    {N n I : Nat} [NeZero N]
    (m : ArchonPhysics.Lattice.PositiveMassConfig N)
    (sign : Fin n -> InteractionSign)
    (tuples : Fin I -> Fin n ->
      Fin (Fintype.card (ArchonPhysics.Lattice.Site N)))
    (T : Real) : Real :=
  markedCollisionAction
    (fun i => orderedPhaseMismatch (harmonicHermitian m) sign (tuples i))
    (fun i => harmonicOrderedNormalizedInteractionWeight m (tuples i)) T

/-- The projector-based physical marked action is globally measurable for
every measurable mass sample; no measurable eigenframe is chosen. -/
theorem measurable_harmonicOrderedMarkedCollisionAction
    {Omega : Type*} [MeasurableSpace Omega]
    {N n I : Nat} [NeZero N]
    (massSample : Omega -> ArchonPhysics.Lattice.PositiveMassConfig N)
    (hmass : forall i, Measurable fun omega => (massSample omega).mass i)
    (sign : Fin n -> InteractionSign)
    (tuples : Fin I -> Fin n ->
      Fin (Fintype.card (ArchonPhysics.Lattice.Site N)))
    {T : Real} (hT : 0 < T) :
    Measurable fun omega =>
      harmonicOrderedMarkedCollisionAction (massSample omega) sign tuples T := by
  unfold harmonicOrderedMarkedCollisionAction
  apply measurable_markedCollisionAction
  · intro i
    apply measurable_orderedPhaseMismatch
    · apply Measurable.subtype_mk
      exact ArchonPhysics.MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
        massSample hmass
  · intro i
    exact measurable_harmonicOrderedNormalizedInteractionWeight
      massSample hmass (tuples i)
  · exact hT

/-- On simple spectrum, the physical ordered marks are the usual nonnegative
normalized vertex squares, hence their marked action is nonnegative. -/
theorem harmonicOrderedMarkedCollisionAction_nonneg_of_simpleSpectrum
    {N n I : Nat} [NeZero N]
    (m : ArchonPhysics.Lattice.PositiveMassConfig N)
    (hsimple : ArchonPhysics.OrderedSingleModeProjector.SimpleOrderedSpectrum
      (harmonicHermitian m))
    (sign : Fin n -> InteractionSign)
    (tuples : Fin I -> Fin n ->
      Fin (Fintype.card (ArchonPhysics.Lattice.Site N)))
    (T : Real) :
    0 <= harmonicOrderedMarkedCollisionAction m sign tuples T := by
  unfold harmonicOrderedMarkedCollisionAction
  apply markedCollisionAction_nonneg
  intro i
  rw [harmonicOrderedNormalizedInteractionWeight_eq m hsimple]
  exact normalizedInteractionWeight_nonneg m
    (fun r => ArchonPhysics.OrderedSingleModeProjector.orderedIndexEquiv
      (tuples i r))

end

end ArchonPhysics.MarkedEmpiricalResonanceTransfer
