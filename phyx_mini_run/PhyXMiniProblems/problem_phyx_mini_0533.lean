import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Trigonometric
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0533

open Dimension

/-!
# Electron tunneling through a rectangular potential barrier

An electron of kinetic energy `5.00 eV` approaches from the left a rectangular
barrier of height `10.0 eV` and width `0.200 nm`.  The supplied figure labels
the incident energy by `E`, the barrier height by `U`, and the barrier width
by `L`.

Energies, lengths, mass, the reduced Planck constant, and the evanescent decay
constant are represented by unit-independent physical quantities.  Real
numbers occur only at explicit unit-readout boundaries and for dimensionless
probabilities, approximation data, and displayed answer values.

The source's recorded value is the leading exponential attenuation factor,
not the exact transmission coefficient for a finite rectangular barrier.  The
formalization therefore stores the physical tunneling probability and that
semiclassical estimate separately.  An explicit remainder and error bound
relate them, while the exact rectangular-barrier transmission law constrains
the physical probability.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative inverse length, used for the under-barrier decay constant. -/
abbrev InverseLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- The physical dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in nanometres. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Read a physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/--
Read a physical energy in electron volts by comparison with Physlib's
dimensionful `DimEnergy.electronVolt`.
-/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read a physical action in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read an inverse-length quantity in inverse metres. -/
def inverseLengthInInverseMeters
    (inverseLength : InverseLengthQuantity) : ℝ :=
  ((inverseLength UnitChoices.SI).val : ℝ)

/-! ## Physical and figure vocabulary -/

/-- Particle species distinguished in the physical setup. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Regions of the one-dimensional potential shown in the diagram. -/
inductive BarrierRegion where
  | leftOfBarrier
  | insideBarrier
  | rightOfBarrier
  deriving DecidableEq, Repr

/-- Shape of the potential-energy profile. -/
inductive PotentialProfileShape where
  | rectangularBarrier
  | other
  deriving DecidableEq, Repr

/-- Roles assigned to the two plotted axes. -/
inductive PlotAxisRole where
  | position
  | energy
  deriving DecidableEq, Repr

/-- The symbols printed next to quantities in the supplied figure. -/
inductive FigureQuantityLabel where
  | incidentEnergyE
  | barrierWidthL
  | barrierHeightU
  deriving DecidableEq, Repr

/-- The charge mark printed beside the incident particle. -/
inductive ParticleChargeLabel where
  | negativeElementaryCharge
  | other
  deriving DecidableEq, Repr

/-- Horizontal direction of the incident arrow. -/
inductive HorizontalDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/--
Qualitative and labeled information read from image 533.  It records the
rectangular geometry and visible labels, but contains no tunneling probability.
-/
structure RectangularBarrierFigure where
  horizontalAxisRole : PlotAxisRole
  verticalAxisRole : PlotAxisRole
  horizontalAxisMarkedX : Bool
  verticalAxisMarkedEnergy : Bool
  originMarkedZero : Bool
  profileShape : PotentialProfileShape
  barrierInteriorShaded : Bool
  incidentEnergyLineShownLeftOfBarrier : Bool
  incidentEnergyLabel : FigureQuantityLabel
  barrierWidthLabel : FigureQuantityLabel
  barrierHeightLabel : FigureQuantityLabel
  incidentParticleChargeLabel : ParticleChargeLabel
  incidentArrowDirection : HorizontalDirection

/--
Independent physical data for the scattering experiment.  In particular, the
physical probability, the leading semiclassical estimate, and its remainder
are fields rather than definitions from the source's recorded answer.
-/
structure ElectronBarrierSetup where
  particleSpecies : ParticleSpecies
  incidentDirection : HorizontalDirection
  profileShape : PotentialProfileShape
  potentialEnergyAt : BarrierRegion → DimEnergy
  incidentKineticEnergy : DimEnergy
  barrierHeight : DimEnergy
  barrierWidth : LengthQuantity
  particleRestMass : MassQuantity
  reducedPlanckAction : ActionQuantity
  barrierDecayConstant : InverseLengthQuantity
  tunnelingProbability : ℝ
  semiclassicalAttenuationEstimate : ℝ
  approximationRemainder : ℝ
  approximationAbsoluteErrorBound : ℝ
  figure : RectangularBarrierFigure

/-! ## Scenario, source readouts, figure evidence, and governing laws -/

/-- The prose describes an electron incident from the left on the barrier. -/
structure MatchesElectronBarrierScenario
    (setup : ElectronBarrierSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  electronMovesTowardPositiveX : setup.incidentDirection = .positiveX
  potentialIsRectangular : setup.profileShape = .rectangularBarrier

/--
The calibrated numerical data stated in the problem.  These fields constrain
only the incident energy, barrier height, and barrier width.
-/
structure MatchesProblemNumericalReadouts
    (setup : ElectronBarrierSetup) : Prop where
  incidentKineticEnergyElectronVolts :
    energyInElectronVolts setup.incidentKineticEnergy = 5
  barrierHeightElectronVolts :
    energyInElectronVolts setup.barrierHeight = 10
  barrierWidthNanometers :
    lengthInNanometers setup.barrierWidth = (1 / 5 : ℝ)

/--
Primary-raster evidence from image 533: the axes, origin, rectangular orange
profile, shaded barrier, labels `E`, `L`, and `U`, and the `-e` particle
moving to the right.  No probability or answer-choice datum is included.
-/
structure MatchesSuppliedBarrierFigure
    (setup : ElectronBarrierSetup) : Prop where
  horizontalAxisIsPosition : setup.figure.horizontalAxisRole = .position
  verticalAxisIsEnergy : setup.figure.verticalAxisRole = .energy
  xLabelShown : setup.figure.horizontalAxisMarkedX = true
  energyLabelShown : setup.figure.verticalAxisMarkedEnergy = true
  zeroOriginShown : setup.figure.originMarkedZero = true
  rectangularProfileShown :
    setup.figure.profileShape = .rectangularBarrier
  shadedBarrierShown : setup.figure.barrierInteriorShaded = true
  incidentEnergyLineShown :
    setup.figure.incidentEnergyLineShownLeftOfBarrier = true
  energyLineLabeledE :
    setup.figure.incidentEnergyLabel = .incidentEnergyE
  widthLabeledL : setup.figure.barrierWidthLabel = .barrierWidthL
  heightLabeledU : setup.figure.barrierHeightLabel = .barrierHeightU
  electronMarkedMinusE :
    setup.figure.incidentParticleChargeLabel = .negativeElementaryCharge
  arrowPointsTowardBarrier :
    setup.figure.incidentArrowDirection = .positiveX

/--
The rectangular potential is zero outside the barrier and equal to the stated
height inside it.  This is the potential profile visible in the figure, not a
statement about transmission.
-/
structure SatisfiesRectangularPotentialProfile
    (setup : ElectronBarrierSetup) : Prop where
  leftPotentialElectronVolts :
    energyInElectronVolts (setup.potentialEnergyAt .leftOfBarrier) = 0
  barrierPotentialIsHeight :
    energyInElectronVolts (setup.potentialEnergyAt .insideBarrier) =
      energyInElectronVolts setup.barrierHeight
  rightPotentialElectronVolts :
    energyInElectronVolts (setup.potentialEnergyAt .rightOfBarrier) = 0

/--
Standard electron and quantum reference data.  Physlib supplies the coherent
SI value `Constants.ℏ`; the electron rest mass has no matching Physlib
dimensionful constant and is calibrated here explicitly.
-/
structure UsesStandardElectronReferenceData
    (setup : ElectronBarrierSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.particleRestMass = 9.1093837015e-31
  reducedPlanckJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)

/--
Positivity, the classically forbidden inequality `E < U`, the opaque-barrier
regime, and probability bounds select the physical branch.
-/
structure HasPhysicalTunnelingParameters
    (setup : ElectronBarrierSetup) : Prop where
  positiveIncidentEnergy :
    0 < energyInJoules setup.incidentKineticEnergy
  incidentEnergyBelowBarrier :
    energyInJoules setup.incidentKineticEnergy <
      energyInJoules setup.barrierHeight
  positiveBarrierWidth : 0 < lengthInMeters setup.barrierWidth
  positiveElectronMass : 0 < massInKilograms setup.particleRestMass
  positiveReducedPlanckAction :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  positiveDecayConstant :
    0 < inverseLengthInInverseMeters setup.barrierDecayConstant
  opaqueBarrierRegime :
    1 < inverseLengthInInverseMeters setup.barrierDecayConstant *
      lengthInMeters setup.barrierWidth
  probabilityNonnegative : 0 ≤ setup.tunnelingProbability
  probabilityAtMostOne : setup.tunnelingProbability ≤ 1
  approximationErrorBoundNonnegative :
    0 ≤ setup.approximationAbsoluteErrorBound

/--
For a constant barrier with `E < U`, the evanescent decay constant obeys

`κ = sqrt (2 m (U - E)) / ℏ`.

The equality is stated at coherent-SI readouts so that its two sides both have
units of inverse metres.
-/
structure SatisfiesBarrierDecayRelation
    (setup : ElectronBarrierSetup) : Prop where
  decayConstantLaw :
    inverseLengthInInverseMeters setup.barrierDecayConstant =
      Real.sqrt
          (2 * massInKilograms setup.particleRestMass *
            (energyInJoules setup.barrierHeight -
              energyInJoules setup.incidentKineticEnergy)) /
        actionInJouleSeconds setup.reducedPlanckAction

/--
The exact one-dimensional transmission coefficient for a finite rectangular
barrier with `E < U`:

`T = (1 + U^2 sinh^2 (κ L) / (4 E (U - E)))⁻¹`.

All energy occurrences use the same coherent-SI readout, and `κ L` is
dimensionless.  Unlike the bare exponential factor, this relation includes
the interface-matching prefactor.
-/
structure SatisfiesExactRectangularBarrierTransmissionLaw
    (setup : ElectronBarrierSetup) : Prop where
  exactTransmissionProbabilityLaw :
    setup.tunnelingProbability =
      (1 +
        energyInJoules setup.barrierHeight ^ 2 *
            Real.sinh
                (inverseLengthInInverseMeters setup.barrierDecayConstant *
                  lengthInMeters setup.barrierWidth) ^ 2 /
          (4 * energyInJoules setup.incidentKineticEnergy *
            (energyInJoules setup.barrierHeight -
              energyInJoules setup.incidentKineticEnergy)))⁻¹

/--
Finite-parameter contract for the commonly used opaque-barrier estimate.

The leading attenuation estimate is `exp (-2 κ L)`, but the physical
probability is the estimate plus an explicit remainder whose absolute value is
bounded.  Thus the approximation is not asserted as a globally exact law.
No numerical value of the estimate, remainder, or answer choice is assumed.
-/
structure SatisfiesFiniteErrorOpaqueBarrierEstimate
    (setup : ElectronBarrierSetup) : Prop where
  leadingAttenuationEstimateLaw :
    setup.semiclassicalAttenuationEstimate =
      Real.exp
        (-2 * inverseLengthInInverseMeters setup.barrierDecayConstant *
          lengthInMeters setup.barrierWidth)
  probabilityErrorDecomposition :
    setup.tunnelingProbability =
      setup.semiclassicalAttenuationEstimate + setup.approximationRemainder
  remainderControlled :
    |setup.approximationRemainder| ≤
      setup.approximationAbsoluteErrorBound

/-! ## Displayed answers and the requested conclusion -/

/-- Labels of the four probability choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless probability displayed beside each answer label. -/
def displayedTunnelingProbability : AnswerChoice → ℝ
  | .A => 111 / 10000
  | .B => 76 / 10000
  | .C => 225 / 10000
  | .D => 103 / 10000

/-- Agreement with a displayed probability to within `0.0001`. -/
def MatchesDisplayedWithinOneTenThousandth
    (probability : ℝ) (choice : AnswerChoice) : Prop :=
  |probability - displayedTunnelingProbability choice| < (1 / 10000 : ℝ)

/-- A choice is strictly nearer to the physical probability than every other choice. -/
def IsUniqueNearestDisplayedProbability
    (probability : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |probability - displayedTunnelingProbability choice| <
      |probability - displayedTunnelingProbability other|

/--
Substitution into the leading exponential estimate gives approximately
`0.0102313`, so the source's intended estimate agrees with D and is uniquely
nearest to D.  The exact finite rectangular-barrier transmission coefficient
is instead approximately `0.0401006`; it is within `0.0001` of `0.0401` and
within that tolerance of none of the displayed choices.

This formalizes `thm:physics:phyx_mini_0533:target` while making the source's
approximation status explicit.  Neither numerical result nor any selected
answer occurs in a premise.
-/
theorem problem_phyx_mini_0533
    (setup : ElectronBarrierSetup)
    (_scenario : MatchesElectronBarrierScenario setup)
    (_readouts : MatchesProblemNumericalReadouts setup)
    (_figure : MatchesSuppliedBarrierFigure setup)
    (_profile : SatisfiesRectangularPotentialProfile setup)
    (_reference : UsesStandardElectronReferenceData setup)
    (_physical : HasPhysicalTunnelingParameters setup)
    (_decay : SatisfiesBarrierDecayRelation setup)
    (_exactTransmission :
      SatisfiesExactRectangularBarrierTransmissionLaw setup)
    (_finiteErrorEstimate : SatisfiesFiniteErrorOpaqueBarrierEstimate setup) :
    MatchesDisplayedWithinOneTenThousandth
        setup.semiclassicalAttenuationEstimate .D ∧
      IsUniqueNearestDisplayedProbability
        setup.semiclassicalAttenuationEstimate .D ∧
      |setup.tunnelingProbability - (401 / 10000 : ℝ)| <
        (1 / 10000 : ℝ) ∧
      ∀ choice : AnswerChoice,
        ¬ MatchesDisplayedWithinOneTenThousandth
            setup.tunnelingProbability choice := by
  have heV :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hE :
      energyInJoules setup.incidentKineticEnergy =
        5 * 1.602176634e-19 := by
    have h := _readouts.incidentKineticEnergyElectronVolts
    rw [energyInElectronVolts, heV] at h
    norm_num at h ⊢
    linarith
  have hU :
      energyInJoules setup.barrierHeight =
        10 * 1.602176634e-19 := by
    have h := _readouts.barrierHeightElectronVolts
    rw [energyInElectronVolts, heV] at h
    norm_num at h ⊢
    linarith
  have hLengthConversion :
      lengthInNanometers setup.barrierWidth =
        1000000000 * lengthInMeters setup.barrierWidth := by
    have hscale := setup.barrierWidth.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.nanometers}
    have hval := congrArg
      (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) hscale
    norm_num [lengthInNanometers, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.scale,
      LengthUnit.meters, LengthUnit.div_eq_val, NNReal.smul_def] at hval ⊢
    exact hval
  have hL :
      lengthInMeters setup.barrierWidth =
        (1 / 5000000000 : ℝ) := by
    linarith [_readouts.barrierWidthNanometers, hLengthConversion]
  have hM :
      massInKilograms setup.particleRestMass = 9.1093837015e-31 :=
    _reference.electronMassKilograms
  have hh :
      actionInJouleSeconds setup.reducedPlanckAction =
        1.054571817e-34 := by
    rw [_reference.reducedPlanckJouleSeconds]
    norm_num [Constants.ℏ]
  have hk :
      inverseLengthInInverseMeters setup.barrierDecayConstant =
        Real.sqrt
            (2 * 9.1093837015e-31 *
              (10 * 1.602176634e-19 - 5 * 1.602176634e-19)) /
          1.054571817e-34 := by
    rw [_decay.decayConstantLaw, hM, hU, hE, hh]
  have hkLBounds :
      (2291 / 1000 : ℝ) <
          inverseLengthInInverseMeters setup.barrierDecayConstant *
            lengthInMeters setup.barrierWidth ∧
        inverseLengthInInverseMeters setup.barrierDecayConstant *
            lengthInMeters setup.barrierWidth <
          (573 / 250 : ℝ) := by
    rw [hk, hL]
    have hsq := Real.sq_sqrt (show
      (0 : ℝ) ≤ 2 * 9.1093837015e-31 *
        (10 * 1.602176634e-19 - 5 * 1.602176634e-19) by norm_num)
    have hn := Real.sqrt_nonneg
      (2 * 9.1093837015e-31 *
        (10 * 1.602176634e-19 - 5 * 1.602176634e-19))
    norm_num at hsq hn ⊢
    constructor <;> nlinarith
  have hExpLower :
      (1021 / 100000 : ℝ) < Real.exp (-573 / 125 : ℝ) := by
    rw [show (-573 / 125 : ℝ) =
        (5 : ℕ) • (-573 / 625 : ℝ) by norm_num,
      Real.exp_nsmul]
    have h := Real.exp_bound
      (x := (-573 / 625 : ℝ)) (n := 12) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [abs_le] at h
    have he :
        (19989 / 50000 : ℝ) < Real.exp (-573 / 625 : ℝ) := by
      nlinarith [h.1]
    calc
      (1021 / 100000 : ℝ) < (19989 / 50000 : ℝ) ^ 5 := by
        norm_num
      _ < Real.exp (-573 / 625 : ℝ) ^ 5 := by
        gcongr
  have hExpUpper :
      Real.exp (-2291 / 500 : ℝ) < (41 / 4000 : ℝ) := by
    rw [show (-2291 / 500 : ℝ) =
        (5 : ℕ) • (-2291 / 2500 : ℝ) by norm_num,
      Real.exp_nsmul]
    have h := Real.exp_bound
      (x := (-2291 / 2500 : ℝ)) (n := 12) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [abs_le] at h
    have he :
        Real.exp (-2291 / 2500 : ℝ) < (2 / 5 : ℝ) := by
      nlinarith [h.2]
    calc
      Real.exp (-2291 / 2500 : ℝ) ^ 5 < (2 / 5 : ℝ) ^ 5 := by
        gcongr
      _ < (41 / 4000 : ℝ) := by
        norm_num
  have hEstimate :=
    _finiteErrorEstimate.leadingAttenuationEstimateLaw
  have hEstimateLower :
      (1021 / 100000 : ℝ) <
        setup.semiclassicalAttenuationEstimate := by
    calc
      (1021 / 100000 : ℝ) < Real.exp (-573 / 125 : ℝ) :=
        hExpLower
      _ < Real.exp
          (-2 *
            inverseLengthInInverseMeters setup.barrierDecayConstant *
              lengthInMeters setup.barrierWidth) := by
        apply Real.exp_lt_exp.mpr
        nlinarith [hkLBounds.2]
      _ = setup.semiclassicalAttenuationEstimate := hEstimate.symm
  have hEstimateUpper :
      setup.semiclassicalAttenuationEstimate <
        (41 / 4000 : ℝ) := by
    calc
      setup.semiclassicalAttenuationEstimate =
          Real.exp
            (-2 *
              inverseLengthInInverseMeters setup.barrierDecayConstant *
                lengthInMeters setup.barrierWidth) := hEstimate
      _ < Real.exp (-2291 / 500 : ℝ) := by
        apply Real.exp_lt_exp.mpr
        nlinarith [hkLBounds.1]
      _ < (41 / 4000 : ℝ) := hExpUpper
  have hEstimatePos :
      0 < setup.semiclassicalAttenuationEstimate := by
    linarith [hEstimateLower]
  have hSinh :
      Real.sinh
          (inverseLengthInInverseMeters setup.barrierDecayConstant *
            lengthInMeters setup.barrierWidth) ^ 2 =
        (1 - setup.semiclassicalAttenuationEstimate) ^ 2 /
          (4 * setup.semiclassicalAttenuationEstimate) := by
    rw [hEstimate]
    let x :=
      inverseLengthInInverseMeters setup.barrierDecayConstant *
        lengthInMeters setup.barrierWidth
    rw [show
      -2 * inverseLengthInInverseMeters setup.barrierDecayConstant *
          lengthInMeters setup.barrierWidth =
        -2 * x by
      dsimp [x]
      ring]
    change Real.sinh x ^ 2 =
      (1 - Real.exp (-2 * x)) ^ 2 / (4 * Real.exp (-2 * x))
    rw [Real.sinh_eq, show (-2 * x : ℝ) = -(x + x) by ring,
      Real.exp_neg, Real.exp_neg, Real.exp_add]
    have hexp := Real.exp_ne_zero x
    field_simp
    ring
  have hTransmission :=
    _exactTransmission.exactTransmissionProbabilityLaw
  rw [hE, hU] at hTransmission
  norm_num at hTransmission
  have hTransmissionEstimate :
      setup.tunnelingProbability =
        4 * setup.semiclassicalAttenuationEstimate /
          (1 + setup.semiclassicalAttenuationEstimate) ^ 2 := by
    rw [hTransmission, hSinh]
    field_simp
    ring
  have hDenominator :
      0 < (1 + setup.semiclassicalAttenuationEstimate) ^ 2 :=
    sq_pos_of_pos (by linarith [hEstimatePos])
  have hTransmissionLower :
      (1 / 25 : ℝ) < setup.tunnelingProbability := by
    rw [hTransmissionEstimate, lt_div_iff₀ hDenominator]
    nlinarith [
      sq_nonneg
        (setup.semiclassicalAttenuationEstimate - 1021 / 100000),
      sq_nonneg
        (41 / 4000 - setup.semiclassicalAttenuationEstimate)]
  have hTransmissionUpper :
      setup.tunnelingProbability < (201 / 5000 : ℝ) := by
    rw [hTransmissionEstimate, div_lt_iff₀ hDenominator]
    nlinarith [
      sq_nonneg
        (setup.semiclassicalAttenuationEstimate - 1021 / 100000),
      sq_nonneg
        (41 / 4000 - setup.semiclassicalAttenuationEstimate)]
  constructor
  · change
      |setup.semiclassicalAttenuationEstimate - 103 / 10000| <
        (1 / 10000 : ℝ)
    rw [abs_lt]
    constructor <;> linarith [hEstimateLower, hEstimateUpper]
  constructor
  · intro other hne
    cases other with
    | A =>
        simp only [displayedTunnelingProbability]
        rw [abs_of_nonpos (by linarith [hEstimateUpper]),
          abs_of_nonpos (by linarith [hEstimateUpper])]
        norm_num
    | B =>
        simp only [displayedTunnelingProbability]
        rw [abs_of_nonpos (by linarith [hEstimateUpper]),
          abs_of_nonneg (by linarith [hEstimateLower])]
        linarith [hEstimateLower]
    | C =>
        simp only [displayedTunnelingProbability]
        rw [abs_of_nonpos (by linarith [hEstimateUpper]),
          abs_of_nonpos (by linarith [hEstimateUpper])]
        norm_num
    | D => exact (hne rfl).elim
  constructor
  · rw [abs_lt]
    constructor <;> linarith [hTransmissionLower, hTransmissionUpper]
  · intro choice hmatch
    cases choice <;>
      simp [MatchesDisplayedWithinOneTenThousandth,
        displayedTunnelingProbability] at hmatch <;>
      rw [abs_lt] at hmatch <;>
      norm_num at hmatch <;>
      linarith [hTransmissionLower]

end PhyXMiniProblems.ProblemPhyXMini0533
