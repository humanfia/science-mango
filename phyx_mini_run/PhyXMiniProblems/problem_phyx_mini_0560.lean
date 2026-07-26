import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Relativity.LorentzGroup.Boosts.Apply
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0560

open Dimension

/-!
# Energy seen after a transverse Lorentz boost

A massive particle approaches the origin of the inertial frame `S`.  Its
velocity lies in the `x-y` plane and makes the angle `alpha` with the positive
`y`-axis.  The observer frame `SPrime` is obtained by an `x`-directed boost
chosen so that the particle has no `xPrime` momentum and therefore moves
along the `yPrime` axis.

Mass, speed, and energy are represented by Physlib dimensionful quantities.
The real Lorentz vectors below are coherent numerical readouts of the
energy-momentum four-vector: their temporal coordinate is `E` and their
spatial coordinates are `p c`, all in joules.  Consequently the Lorentz
group can act directly on them using the dimensionless boost fraction `v/c`.

The primary bitmap takes precedence over its auxiliary caption: the bitmap
draws `alpha` from the positive `y`-axis, and the arrow labelled `u` points
from the particle in the first quadrant toward the origin.
-/

/-! ## Dimensionful physical quantities and coherent scalar readouts -/

/-- A nonnegative physical rest mass with mass dimension `M`. -/
abbrev RestMassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- Read a physical rest mass in kilograms. -/
def restMassInKilograms (mass : RestMassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a nonnegative physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact dimensionful vacuum speed of light, read in SI units. -/
def vacuumLightSpeedInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- A speed expressed as the dimensionless fraction `u/c`. -/
def speedFractionOfLight (speed : DimSpeed) : ℝ :=
  speedInMetersPerSecond speed / vacuumLightSpeedInMetersPerSecond

/-- The rest-energy equivalent `m c²`, expressed in joules. -/
def restEnergyEquivalentInJoules (mass : RestMassQuantity) : ℝ :=
  restMassInKilograms mass * vacuumLightSpeedInMetersPerSecond ^ 2

/-! ## Frame, axis, and primary-figure labels -/

/-- The two inertial frames named in the problem. -/
inductive InertialFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Fintype, Repr

/-- The two spatial axes shown in the bitmap and used for the boost. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Coordinate index corresponding to a labelled diagram axis. -/
def DiagramAxis.toFin : DiagramAxis → Fin 2
  | .x => 0
  | .y => 1

/-!
Qualitative and geometric information transcribed from the primary bitmap.
Coordinates here are drawing coordinates only; the bitmap supplies no
quantitative position or distance scale.
-/
structure ParticleApproachFigure where
  axisShown : DiagramAxis → Bool
  axisText : DiagramAxis → String
  particlePoint : EuclideanSpace ℝ (Fin 2)
  velocityArrowTail : EuclideanSpace ℝ (Fin 2)
  velocityArrowHead : EuclideanSpace ℝ (Fin 2)
  particleText : String
  velocityArrowText : String
  frameText : String
  angleText : String
  angleReferenceAxis : DiagramAxis
  alphaRadians : ℝ
  dashedExtensionToOriginShown : Bool
  hasQuantitativePositionScale : Bool

/-!
The independent physical quantities of the scenario.  In particular, the
energy measured in `SPrime` is an unconstrained dimensionful field here; it
is not defined from the requested formula or from an answer choice.
-/
structure TransverseBoostSetup where
  particleRestMass : RestMassQuantity
  particleSpeedInS : DimSpeed
  measuredEnergy : InertialFrameLabel → DimEnergy
  velocityFractionInS : EuclideanSpace ℝ (Fin 2)
  energyMomentumReadout : InertialFrameLabel → Lorentz.Vector 2
  sPrimeBoostFractionAlongX : ℝ
  alphaRadians : ℝ
  figure : ParticleApproachFigure

/-- The component `u_axis/c` of the particle's velocity in `S`. -/
def velocityFractionComponent
    (setup : TransverseBoostSetup) (axis : DiagramAxis) : ℝ :=
  setup.velocityFractionInS axis.toFin

/-- Temporal energy coordinate of the energy-momentum readout, in joules. -/
def energyMomentumTemporalComponent
    (setup : TransverseBoostSetup) (frame : InertialFrameLabel) : ℝ :=
  setup.energyMomentumReadout frame (Sum.inl 0)

/-- Spatial `p_axis c` coordinate of the energy-momentum readout, in joules. -/
def energyMomentumSpatialComponent
    (setup : TransverseBoostSetup)
    (frame : InertialFrameLabel) (axis : DiagramAxis) : ℝ :=
  setup.energyMomentumReadout frame (Sum.inr axis.toFin)

/-! ## Figure evidence and physical-domain assumptions -/

/-!
Facts read from the primary raster and the prose.  The arrow starts at the
particle in the first quadrant and points inward along the same ray.  The
component equations encode an inward velocity making `alpha` with the
positive `y`-axis.  No energy in `SPrime` is fixed here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : TransverseBoostSetup) : Prop where
  xAxisShown : setup.figure.axisShown .x = true
  yAxisShown : setup.figure.axisShown .y = true
  xAxisText : setup.figure.axisText .x = "x"
  yAxisText : setup.figure.axisText .y = "y"
  particleLabel : setup.figure.particleText = "m"
  velocityLabel : setup.figure.velocityArrowText = "u"
  frameLabel : setup.figure.frameText = "S"
  angleLabel : setup.figure.angleText = "α"
  angleMeasuredFromPositiveYAxis : setup.figure.angleReferenceAxis = .y
  figureAngleAgrees : setup.figure.alphaRadians = setup.alphaRadians
  particleInFirstQuadrant :
    0 < setup.figure.particlePoint DiagramAxis.x.toFin ∧
      0 < setup.figure.particlePoint DiagramAxis.y.toFin
  arrowTailAtParticle :
    setup.figure.velocityArrowTail = setup.figure.particlePoint
  arrowPointsAlongRayTowardOrigin :
    ∃ scale : ℝ, 0 < scale ∧ scale < 1 ∧
      setup.figure.velocityArrowHead =
        scale • setup.figure.velocityArrowTail
  dashedExtensionShown : setup.figure.dashedExtensionToOriginShown = true
  noQuantitativePositionScale : setup.figure.hasQuantitativePositionScale = false
  velocityMagnitudeReadout :
    ‖setup.velocityFractionInS‖ = speedFractionOfLight setup.particleSpeedInS
  inwardXVelocityComponent :
    velocityFractionComponent setup .x =
      -(speedFractionOfLight setup.particleSpeedInS) *
        Real.sin setup.alphaRadians
  inwardYVelocityComponent :
    velocityFractionComponent setup .y =
      -(speedFractionOfLight setup.particleSpeedInS) *
        Real.cos setup.alphaRadians

/-!
Positivity, angle range, and subluminal input conditions.  They select the
physical branch but contain no equation for the requested transformed energy.
-/
structure HasPhysicalInputParameters
    (setup : TransverseBoostSetup) : Prop where
  restMassPositive : 0 < restMassInKilograms setup.particleRestMass
  energyInSPositive : 0 < energyInJoules (setup.measuredEnergy .S)
  lightSpeedPositive : 0 < vacuumLightSpeedInMetersPerSecond
  speedFractionNonnegative :
    0 ≤ speedFractionOfLight setup.particleSpeedInS
  speedFractionSubluminal :
    speedFractionOfLight setup.particleSpeedInS < 1
  alphaNonnegative : 0 ≤ setup.alphaRadians
  alphaAtMostRightAngle : setup.alphaRadians ≤ Real.pi / 2

/-!
The defining condition on the observer in `SPrime`.  Its boost is along the
`x` direction and matches the particle's transverse velocity fraction, while
the transformed particle has zero `xPrime` momentum and hence travels along
the `yPrime` axis.  This specifies the observer, not the requested energy.
-/
structure ObserverMakesParticleMoveAlongYPrime
    (setup : TransverseBoostSetup) : Prop where
  boostCancelsTransverseVelocity :
    setup.sPrimeBoostFractionAlongX = velocityFractionComponent setup .x
  transformedXMomentumIsZero :
    energyMomentumSpatialComponent setup .SPrime .x = 0

/-! ## Governing special-relativistic laws -/

/-!
The four-vector readouts use energy coordinates `(E, p_x c, p_y c)`.
Accordingly:

* the temporal coordinate is the measured relativistic energy;
* in `S`, `p_i c = E (u_i/c)`;
* the change from `S` to `SPrime` is Physlib's Lorentz boost;
* the invariant mass shell is `E² - |p c|² = (m c²)²`.

These are general governing laws.  None states the target square-root
formula for the energy in `SPrime`.
-/
structure SatisfiesSpecialRelativisticParticleKinematics
    (setup : TransverseBoostSetup) : Prop where
  temporalComponentIsMeasuredEnergy :
    ∀ frame : InertialFrameLabel,
      energyMomentumTemporalComponent setup frame =
        energyInJoules (setup.measuredEnergy frame)
  spatialMomentumVelocityRelationInS :
    ∀ axis : DiagramAxis,
      energyMomentumSpatialComponent setup .S axis =
        energyMomentumTemporalComponent setup .S *
          velocityFractionComponent setup axis
  boostIsSubluminal : |setup.sPrimeBoostFractionAlongX| < 1
  energyMomentumTransformsByLorentzBoost :
    setup.energyMomentumReadout .SPrime =
      LorentzGroup.boost DiagramAxis.x.toFin
          setup.sPrimeBoostFractionAlongX boostIsSubluminal •
        setup.energyMomentumReadout .S
  invariantMassShell :
    ∀ frame : InertialFrameLabel,
      energyMomentumTemporalComponent setup frame ^ 2 -
          energyMomentumSpatialComponent setup frame .x ^ 2 -
          energyMomentumSpatialComponent setup frame .y ^ 2 =
        restEnergyEquivalentInJoules setup.particleRestMass ^ 2

/-! ## Derived energy and displayed answers -/

/-!
Before inserting the figure's trigonometric component, the transverse boost
changes the energy by `sqrt (1 - (u_x/c)^2)`.
-/
lemma energy_after_transverse_boost
    (setup : TransverseBoostSetup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hObserver : ObserverMakesParticleMoveAlongYPrime setup)
    (hRelativity : SatisfiesSpecialRelativisticParticleKinematics setup) :
    energyInJoules (setup.measuredEnergy .SPrime) =
      energyInJoules (setup.measuredEnergy .S) *
        Real.sqrt (1 - velocityFractionComponent setup .x ^ 2) := by
  let β := velocityFractionComponent setup .x
  have hβ : |β| < 1 := by
    change |velocityFractionComponent setup .x| < 1
    rw [← hObserver.boostCancelsTransverseVelocity]
    exact hRelativity.boostIsSubluminal
  have hq : 0 < 1 - β ^ 2 := by
    rw [abs_lt] at hβ
    nlinarith
  have hsqrt : 0 < Real.sqrt (1 - β ^ 2) := Real.sqrt_pos.2 hq
  have htransform :=
    congrFun hRelativity.energyMomentumTransformsByLorentzBoost (Sum.inl 0)
  rw [Lorentz.Vector.boost_time_eq] at htransform
  change energyMomentumTemporalComponent setup .SPrime =
    LorentzGroup.γ setup.sPrimeBoostFractionAlongX *
      (energyMomentumTemporalComponent setup .S -
        setup.sPrimeBoostFractionAlongX *
          energyMomentumSpatialComponent setup .S .x) at htransform
  rw [hObserver.boostCancelsTransverseVelocity] at htransform
  rw [hRelativity.spatialMomentumVelocityRelationInS .x] at htransform
  rw [hRelativity.temporalComponentIsMeasuredEnergy .SPrime] at htransform
  change _ = LorentzGroup.γ β *
    (energyMomentumTemporalComponent setup .S -
      β * (energyMomentumTemporalComponent setup .S * β)) at htransform
  rw [hRelativity.temporalComponentIsMeasuredEnergy .S] at htransform
  rw [htransform]
  change LorentzGroup.γ β * (_ - β * (_ * β)) = _
  calc
    LorentzGroup.γ β *
          (energyInJoules (setup.measuredEnergy .S) -
            β * (energyInJoules (setup.measuredEnergy .S) * β)) =
        (energyInJoules (setup.measuredEnergy .S) * (1 - β ^ 2)) /
          Real.sqrt (1 - β ^ 2) := by
            rw [LorentzGroup.γ]
            ring
    _ = energyInJoules (setup.measuredEnergy .S) * Real.sqrt (1 - β ^ 2) := by
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      rw [mul_assoc, ← pow_two, Real.sq_sqrt (le_of_lt hq)]

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless multiplier of `E` printed beside each answer label. -/
def displayedEnergyMultiplier
    (setup : TransverseBoostSetup) : AnswerChoice → ℝ
  | .A => Real.sqrt
      (1 + speedFractionOfLight setup.particleSpeedInS ^ 2 *
        Real.sin setup.alphaRadians ^ 2)
  | .B => Real.sqrt
      (2 - speedFractionOfLight setup.particleSpeedInS ^ 2 *
        Real.sin setup.alphaRadians ^ 2)
  | .C => Real.sqrt
      (2 + speedFractionOfLight setup.particleSpeedInS ^ 2 *
        Real.sin setup.alphaRadians ^ 2)
  | .D => Real.sqrt
      (1 - speedFractionOfLight setup.particleSpeedInS ^ 2 *
        Real.sin setup.alphaRadians ^ 2)

/-- The answer label recorded in the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed multiplier agrees with the independently modeled energy. -/
def MatchesDisplayedAnswer
    (setup : TransverseBoostSetup) (choice : AnswerChoice) : Prop :=
  energyInJoules (setup.measuredEnergy .SPrime) =
    energyInJoules (setup.measuredEnergy .S) *
      displayedEnergyMultiplier setup choice

/-!
With `u_x/c = -(u/c) sin alpha`, the energy seen in `SPrime` is

`EPrime = E sqrt (1 - (u²/c²) sin² alpha)`,

which is the expression printed as answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0560:target`.
-/
theorem problem_phyx_mini_0560
    (setup : TransverseBoostSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hObserver : ObserverMakesParticleMoveAlongYPrime setup)
    (hRelativity : SatisfiesSpecialRelativisticParticleKinematics setup) :
    energyInJoules (setup.measuredEnergy .SPrime) =
      energyInJoules (setup.measuredEnergy .S) *
        Real.sqrt
          (1 - speedFractionOfLight setup.particleSpeedInS ^ 2 *
            Real.sin setup.alphaRadians ^ 2) := by
  rw [energy_after_transverse_boost setup hPhysical hObserver hRelativity]
  rw [hFigure.inwardXVelocityComponent]
  congr 2
  ring

/-! The exact result agrees with the source's recorded answer choice D. -/
theorem recorded_answer_D_matches
    (setup : TransverseBoostSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hObserver : ObserverMakesParticleMoveAlongYPrime setup)
    (hRelativity : SatisfiesSpecialRelativisticParticleKinematics setup) :
    MatchesDisplayedAnswer setup recordedDatasetAnswer := by
  simpa [MatchesDisplayedAnswer, recordedDatasetAnswer, displayedEnergyMultiplier] using
    problem_phyx_mini_0560 setup hFigure hPhysical hObserver hRelativity

end PhyXMiniProblems.ProblemPhyXMini0560
