import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Apply
import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0597

/-!
# Limiting velocity in a moving inertial frame

A fixed particle is observed from a laboratory frame `S` and from a family
of collinear inertial frames `S'(v)`.  The horizontal coordinate `v` and the
vertical coordinate `u'` in the supplied graph are dimensional scalar
readouts in metres per second.  The physical velocity itself is represented
by Physlib's `Lorentz.Velocity 1`; its spatial component divided by its time
component is the corresponding dimensionless velocity fraction `u/c`.

The graph calibrates `u'_a = 0.800 c`, has labelled horizontal ticks at
`0`, `0.2 c`, and `0.4 c`, and depicts a decreasing curve.  The governing
law is a Lorentz boost by the dimensionless relative speed `v/c`.  The
requested conclusion is the left-hand limit of the measured velocity as
`v` approaches `c`; that conclusion does not occur in any premise below.
-/

/-! ## Frames and physical velocity readouts -/

/-- The laboratory frame `S` and the collinear moving frame `S'(v)`. -/
inductive InertialFrameLabel where
  | S
  | SPrime (relativeSpeedInMetersPerSecond : ℝ)

/-- The relative speed assigned to each named frame, measured from `S`. -/
def relativeSpeedInMetersPerSecond : InertialFrameLabel → ℝ
  | .S => 0
  | .SPrime v => v

/-!
The longitudinal three-velocity component as a dimensionless fraction of
the vacuum speed of light.  This is a scalar projection of a physical
Physlib four-velocity, not a scalar replacement for that velocity.
-/
def longitudinalVelocityFractionOfC
    (velocity : Lorentz.Velocity 1) : ℝ :=
  (Lorentz.Vector.spatialPart velocity.1) (0 : Fin 1) /
    Lorentz.Vector.timeComponent velocity.1

/-! ## Vocabulary and data from the supplied graph -/

/-- Labels printed along the horizontal `v`-axis. -/
inductive HorizontalAxisTickLabel where
  | zero
  | pointTwoC
  | pointFourC
  deriving DecidableEq, Fintype, Repr

/-- Labels printed along the vertical velocity axis. -/
inductive VerticalAxisLabel where
  | uPrime
  | uPrimeA
  deriving DecidableEq, Fintype, Repr

/-!
Typed data carried by image 597.  The plotted ordinate and tick positions
are dimensional scalar readouts in metres per second.  Their numerical
calibration and physical interpretation are stated separately as evidence.
-/
structure SuppliedVelocityGraph where
  horizontalTickInMetersPerSecond : HorizontalAxisTickLabel → ℝ
  verticalScaleInMetersPerSecond : ℝ
  plottedLongitudinalVelocityInMetersPerSecond : ℝ → ℝ
  verticalAxisLabelShown : VerticalAxisLabel → Bool
  gridShown : Bool

/-!
The independent physical setup.  A single particle has a genuine Physlib
four-velocity in each frame, while `speedOfLightInMetersPerSecond` supplies
the dimensional conversion between fractions of `c` and graph readouts.
-/
structure RelativisticVelocityGraphSetup where
  speedOfLightInMetersPerSecond : ℝ
  particleFourVelocityMeasuredIn :
    InertialFrameLabel → Lorentz.Velocity 1
  figure : SuppliedVelocityGraph

/-- The particle's dimensional longitudinal velocity readout in a frame. -/
def particleLongitudinalVelocityInMetersPerSecond
    (setup : RelativisticVelocityGraphSetup)
    (frame : InertialFrameLabel) : ℝ :=
  setup.speedOfLightInMetersPerSecond *
    longitudinalVelocityFractionOfC
      (setup.particleFourVelocityMeasuredIn frame)

/-! ## Figure evidence, physical domain, and governing law -/

/-!
Quantitative and qualitative evidence read from the supplied graph.  The
curve-to-measurement equality identifies what the graph plots; it does not
assign any unshown limiting value to the curve.
-/
structure MatchesSuppliedVelocityGraph
    (setup : RelativisticVelocityGraphSetup) : Prop where
  zeroTickCalibration :
    setup.figure.horizontalTickInMetersPerSecond .zero = 0
  pointTwoTickCalibration :
    setup.figure.horizontalTickInMetersPerSecond .pointTwoC =
      (1 / 5 : ℝ) * setup.speedOfLightInMetersPerSecond
  pointFourTickCalibration :
    setup.figure.horizontalTickInMetersPerSecond .pointFourC =
      (2 / 5 : ℝ) * setup.speedOfLightInMetersPerSecond
  verticalScaleCalibration :
    setup.figure.verticalScaleInMetersPerSecond =
      (4 / 5 : ℝ) * setup.speedOfLightInMetersPerSecond
  uPrimeLabelIsShown :
    setup.figure.verticalAxisLabelShown .uPrime = true
  uPrimeAScaleLabelIsShown :
    setup.figure.verticalAxisLabelShown .uPrimeA = true
  backgroundGridIsShown :
    setup.figure.gridShown = true
  plottedCurveRepresentsMeasuredVelocity :
    ∀ v ∈ Set.Icc 0
        (setup.figure.horizontalTickInMetersPerSecond .pointFourC),
      setup.figure.plottedLongitudinalVelocityInMetersPerSecond v =
        particleLongitudinalVelocityInMetersPerSecond setup (.SPrime v)
  curveStartsAtVerticalScale :
    setup.figure.plottedLongitudinalVelocityInMetersPerSecond 0 =
      setup.figure.verticalScaleInMetersPerSecond
  displayedCurveIsStrictlyDecreasing :
    StrictAntiOn
      setup.figure.plottedLongitudinalVelocityInMetersPerSecond
      (Set.Icc 0
        (setup.figure.horizontalTickInMetersPerSecond .pointFourC))

/-- Physical positivity of the dimensional vacuum speed of light. -/
structure HasPhysicalSpeedOfLight
    (setup : RelativisticVelocityGraphSetup) : Prop where
  speedOfLightPositive : 0 < setup.speedOfLightInMetersPerSecond

/-!
The governing special-relativistic frame-change law.  For every subluminal
relative speed `v`, the independently stored four-velocity in `S'(v)` is the
Lorentz boost of the four-velocity in `S` by `v/c`.  The desired `v → c`
limit is not included in this law.
-/
structure SatisfiesOneDimensionalLorentzVelocityLaw
    (setup : RelativisticVelocityGraphSetup) : Prop where
  particleFourVelocityTransformsByBoost :
    ∀ (v : ℝ)
      (hSubluminal :
        |v / setup.speedOfLightInMetersPerSecond| < 1),
      (setup.particleFourVelocityMeasuredIn (.SPrime v)).1 =
        LorentzGroup.boost
            (0 : Fin 1)
            (v / setup.speedOfLightInMetersPerSecond)
            hSubluminal •
          (setup.particleFourVelocityMeasuredIn .S).1

/-! ## Displayed choices and dataset metadata -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensional velocity represented by each displayed answer choice. -/
def displayedAnswerVelocityInMetersPerSecond
    (speedOfLightInMetersPerSecond : ℝ) : AnswerChoice → ℝ
  | .A => 0
  | .B => speedOfLightInMetersPerSecond
  | .C => -speedOfLightInMetersPerSecond
  | .D => (4 / 5 : ℝ) * speedOfLightInMetersPerSecond

/-- The source dataset records choice C; this metadata is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-! ## Derived relations and formalization target -/

/-!
At zero relative frame speed, the Lorentz law identifies `S'(0)` with `S`.
Together with the graph's starting ordinate, this determines the particle's
laboratory-frame longitudinal velocity as `0.800 c`.
-/
lemma laboratory_velocity_eq_point_eight_c
    (setup : RelativisticVelocityGraphSetup)
    (hFigure : MatchesSuppliedVelocityGraph setup)
    (hPhysical : HasPhysicalSpeedOfLight setup)
    (hRelativity : SatisfiesOneDimensionalLorentzVelocityLaw setup) :
    particleLongitudinalVelocityInMetersPerSecond setup .S =
      (4 / 5 : ℝ) * setup.speedOfLightInMetersPerSecond := by
  have hZeroTransform :=
    hRelativity.particleFourVelocityTransformsByBoost 0 (by simp)
  simp only [zero_div, LorentzGroup.boost_zero_eq_id, one_smul] at hZeroTransform
  have hZeroVelocity :
      setup.particleFourVelocityMeasuredIn (.SPrime 0) =
        setup.particleFourVelocityMeasuredIn .S :=
    Lorentz.Velocity.ext hZeroTransform
  have hZeroReadout :
      particleLongitudinalVelocityInMetersPerSecond setup (.SPrime 0) =
        particleLongitudinalVelocityInMetersPerSecond setup .S := by
    unfold particleLongitudinalVelocityInMetersPerSecond
    rw [hZeroVelocity]
  have hZeroInDomain :
      (0 : ℝ) ∈ Set.Icc 0
        (setup.figure.horizontalTickInMetersPerSecond .pointFourC) := by
    constructor
    · exact le_rfl
    · rw [hFigure.pointFourTickCalibration]
      nlinarith [hPhysical.speedOfLightPositive]
  rw [← hZeroReadout,
    ← hFigure.plottedCurveRepresentsMeasuredVelocity 0 hZeroInDomain,
    hFigure.curveStartsAtVerticalScale, hFigure.verticalScaleCalibration]

/-!
As the speed of `S'` approaches `c` from below, the particle's longitudinal
velocity measured in `S'` approaches `-c`.  Equivalently, the correct
displayed answer is choice C.

This is the declaration corresponding to
`thm:physics:phyx_mini_0597:target`.
-/
theorem velocity_in_moving_frame_tends_to_negative_c
    (setup : RelativisticVelocityGraphSetup)
    (hFigure : MatchesSuppliedVelocityGraph setup)
    (hPhysical : HasPhysicalSpeedOfLight setup)
    (hRelativity : SatisfiesOneDimensionalLorentzVelocityLaw setup) :
    Filter.Tendsto
      (fun v : ℝ =>
        particleLongitudinalVelocityInMetersPerSecond setup (.SPrime v))
      (nhdsWithin setup.speedOfLightInMetersPerSecond
        (Set.Iio setup.speedOfLightInMetersPerSecond))
      (nhds (-setup.speedOfLightInMetersPerSecond)) := by
  let c := setup.speedOfLightInMetersPerSecond
  let p := (setup.particleFourVelocityMeasuredIn .S).1
  have hcPos : 0 < c := hPhysical.speedOfLightPositive
  have hc : c ≠ 0 := ne_of_gt hcPos
  have hpTimePos : 0 < Lorentz.Vector.timeComponent p :=
    Lorentz.Velocity.timeComponent_pos
      (setup.particleFourVelocityMeasuredIn .S)
  have hpTime : Lorentz.Vector.timeComponent p ≠ 0 := ne_of_gt hpTimePos
  have hLab :=
    laboratory_velocity_eq_point_eight_c setup hFigure hPhysical hRelativity
  have hLabFraction :
      (Lorentz.Vector.spatialPart p) (0 : Fin 1) /
          Lorentz.Vector.timeComponent p = (4 / 5 : ℝ) := by
    unfold particleLongitudinalVelocityInMetersPerSecond
      longitudinalVelocityFractionOfC at hLab
    change c * ((Lorentz.Vector.spatialPart p) (0 : Fin 1) /
      Lorentz.Vector.timeComponent p) = (4 / 5 : ℝ) * c at hLab
    nlinarith
  have hpSpatial :
      (Lorentz.Vector.spatialPart p) (0 : Fin 1) =
        (4 / 5 : ℝ) * Lorentz.Vector.timeComponent p := by
    exact (div_eq_iff hpTime).mp hLabFraction
  let transformedVelocity : ℝ → ℝ := fun v =>
    c * (((4 / 5 : ℝ) - v / c) /
      (1 - (v / c) * (4 / 5 : ℝ)))
  have hFormula :
      ∀ v : ℝ, 0 < v → v < c →
        particleLongitudinalVelocityInMetersPerSecond setup (.SPrime v) =
          transformedVelocity v := by
    intro v hvPos hvLt
    have hβPos : 0 < v / c := div_pos hvPos hcPos
    have hβLt : v / c < 1 := (div_lt_one hcPos).mpr hvLt
    have hβ : |v / c| < 1 := by
      rw [abs_of_pos hβPos]
      exact hβLt
    have hTransform :=
      hRelativity.particleFourVelocityTransformsByBoost v hβ
    unfold particleLongitudinalVelocityInMetersPerSecond
      longitudinalVelocityFractionOfC
    rw [hTransform]
    change c *
        (((LorentzGroup.boost (0 : Fin 1) (v / c) hβ • p)
            (Sum.inr (0 : Fin 1))) /
          ((LorentzGroup.boost (0 : Fin 1) (v / c) hβ • p)
            (Sum.inl (0 : Fin 1)))) =
      transformedVelocity v
    rw [Lorentz.Vector.boost_inr_self_eq,
      Lorentz.Vector.boost_time_eq]
    change c *
        (LorentzGroup.γ (v / c) *
            ((Lorentz.Vector.spatialPart p) (0 : Fin 1) -
              (v / c) * Lorentz.Vector.timeComponent p) /
          (LorentzGroup.γ (v / c) *
            (Lorentz.Vector.timeComponent p -
              (v / c) * (Lorentz.Vector.spatialPart p) (0 : Fin 1)))) =
      transformedVelocity v
    rw [hpSpatial]
    have hOneMinusβPos : 0 < 1 - (v / c) * (4 / 5 : ℝ) := by
      nlinarith
    have hOneMinusSquarePos : 0 < 1 - (v / c) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hβLt)
        (show 0 < 1 + v / c by nlinarith)]
    have hγPos : 0 < LorentzGroup.γ (v / c) := by
      rw [LorentzGroup.γ]
      exact one_div_pos.mpr (Real.sqrt_pos.2 hOneMinusSquarePos)
    dsimp [transformedVelocity]
    field_simp [hc, hpTime, ne_of_gt hOneMinusβPos, ne_of_gt hγPos]
  have hvDivContinuous : ContinuousAt (fun v : ℝ => v / c) c :=
    continuousAt_id.div_const c
  have hNumeratorContinuous :
      ContinuousAt (fun v : ℝ => (4 / 5 : ℝ) - v / c) c :=
    continuousAt_const.sub hvDivContinuous
  have hDenominatorContinuous :
      ContinuousAt (fun v : ℝ => 1 - (v / c) * (4 / 5 : ℝ)) c :=
    continuousAt_const.sub (hvDivContinuous.mul continuousAt_const)
  have hDenominatorAtC :
      (1 - (c / c) * (4 / 5 : ℝ)) ≠ 0 := by
    norm_num [hc]
  have hTransformedContinuous : ContinuousAt transformedVelocity c := by
    dsimp [transformedVelocity]
    exact continuousAt_const.mul
      (hNumeratorContinuous.div hDenominatorContinuous hDenominatorAtC)
  have hTransformedAtC : transformedVelocity c = -c := by
    dsimp [transformedVelocity]
    field_simp [hc]
    ring
  have hTransformedTendsto :
      Filter.Tendsto transformedVelocity
        (nhdsWithin c (Set.Iio c)) (nhds (-c)) := by
    rw [← hTransformedAtC]
    exact hTransformedContinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply hTransformedTendsto.congr'
  filter_upwards [
    eventually_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hcPos)
  ] with v hvLt hvPos
  exact (hFormula v hvPos hvLt).symm

end PhyXMiniProblems.ProblemPhyXMini0597
