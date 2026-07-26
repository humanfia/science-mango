import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0971

open Dimension Filter Topology

/-!
# Rise of suspended parallel wires after a capacitor discharge

Two long horizontal conductors are suspended parallel to one another.  Their
back ends are joined and their front ends are connected to oppositely charged
capacitor plates.  The antiparallel discharge currents repel the wires.

The source's phrase that discharge is fast compared with appreciable wire
motion is an approximation, not a global fixed-separation identity.  It is
therefore represented below by a family indexed by the positive dimensionless
ratio epsilon = discharge time / mechanical-motion time.  The approximation
contract states convergence on the discharge timescale and a vanishing
integrated force error as epsilon tends to zero from above.  The requested
answer is correspondingly the limiting rise height.
-/

/-! ## Dimensionful magnitudes and coherent-SI readouts -/

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Capacitance has dimension charge per electric potential. -/
def capacitanceDimension : Dimension :=
  C𝓭 * electricPotentialDimension⁻¹

/-- Resistance has dimension electric potential times time per charge. -/
def resistanceDimension : Dimension :=
  electricPotentialDimension * T𝓭 * C𝓭⁻¹

/-- Linear mass density has dimension mass per length. -/
def linearMassDensityDimension : Dimension := M𝓭 * L𝓭⁻¹

/-- Acceleration has dimension length per time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Vacuum magnetic permeability has dimension mass length per charge squared. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Force per unit length has dimension mass per time squared. -/
def forcePerLengthDimension : Dimension := M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Impulse per unit length has dimension mass per time. -/
def impulsePerLengthDimension : Dimension := M𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent magnitude carrying dimension d. -/
abbrev Magnitude (d : Dimension) : Type :=
  Dimensionful (WithDim d NNReal)

abbrev LengthMagnitude := Magnitude L𝓭
abbrev TimeMagnitude := Magnitude T𝓭
abbrev ChargeMagnitude := Magnitude C𝓭
abbrev CurrentMagnitude := Magnitude electricCurrentDimension
abbrev CapacitanceMagnitude := Magnitude capacitanceDimension
abbrev ResistanceMagnitude := Magnitude resistanceDimension
abbrev LinearMassDensityMagnitude := Magnitude linearMassDensityDimension
abbrev AccelerationMagnitude := Magnitude accelerationDimension
abbrev MagneticPermeabilityMagnitude := Magnitude magneticPermeabilityDimension
abbrev ForcePerLengthMagnitude := Magnitude forcePerLengthDimension
abbrev ImpulsePerLengthMagnitude := Magnitude impulsePerLengthDimension
abbrev SpeedMagnitude := DimSpeed

/-- The real-valued coherent-SI readout of a nonnegative physical magnitude. -/
def coherentSIValue {d : Dimension} (quantity : Magnitude d) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-! ## Conductors, circuit topology, and raster labels -/

inductive WireLabel where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

inductive WireEnd where
  | front
  | back
  deriving DecidableEq, Fintype, Repr

inductive CapacitorPlate where
  | positive
  | negative
  deriving DecidableEq, Fintype, Repr

inductive AlongWireDirection where
  | frontToBack
  | backToFront
  deriving DecidableEq, Repr

inductive LateralDirection where
  | awayFromOtherWire
  | towardOtherWire
  | zero
  deriving DecidableEq, Repr

inductive WireModel where
  | longStraightConductor
  | other
  deriving DecidableEq, Repr

inductive WireColor where
  | yellow
  | gray
  | other
  deriving DecidableEq, Repr

/-- Literal information read from the primary raster 971.png. -/
structure ParallelWireCapacitorFigure where
  wireShown : WireLabel → Bool
  wireColor : WireLabel → WireColor
  suspensionCordShown : WireLabel → Bool
  wiresDrawnHorizontal : Bool
  wiresDrawnParallel : Bool
  separationMarkerShown : Bool
  separationMarkerLabel : String
  capacitorShown : Bool
  capacitorLabel : String
  positivePlateMarkShown : Bool
  negativePlateMarkShown : Bool
  plateConnectedTo : CapacitorPlate → WireLabel × WireEnd
  backEndsJoinedByWire : Bool

/-!
Physical data and coherent-SI-time histories for a family of otherwise
identical experiments.  The first real argument of the epsilon-dependent
fields is the positive discharge-to-motion timescale ratio.  Rise height is
an independent observable and is not defined by an answer expression.
-/
structure ParallelWireCapacitorSetup where
  wireModel : WireLabel → WireModel
  suspendedFromCords : WireLabel → Bool
  wiresHorizontal : Bool
  wiresParallel : Bool
  auxiliaryConnectionsSlack : Bool
  auxiliaryConnectionsLowResistance : Bool
  plateConnectedTo : CapacitorPlate → WireLabel × WireEnd
  backEndsJoinedByWire : Bool
  linearMassDensity : LinearMassDensityMagnitude
  initialSeparation : LengthMagnitude
  capacitorCapacitance : CapacitanceMagnitude
  initialChargeMagnitude : ChargeMagnitude
  totalCircuitResistance : ResistanceMagnitude
  vacuumPermeability : MagneticPermeabilityMagnitude
  gravitationalAcceleration : AccelerationMagnitude
  dischargeTimeConstant : TimeMagnitude
  appreciableMotionTimeAtRatio : ℝ → TimeMagnitude
  separationAtRatioSeconds : ℝ → ℝ → LengthMagnitude
  currentMagnitudeAtSeconds : WireLabel → ℝ → CurrentMagnitude
  currentDirection : WireLabel → AlongWireDirection
  forcePerLengthAtRatioSeconds : ℝ → WireLabel → ℝ → ForcePerLengthMagnitude
  forceDirectionAtRatioSeconds : ℝ → WireLabel → ℝ → LateralDirection
  impulsePerLengthAtRatio : ℝ → WireLabel → ImpulsePerLengthMagnitude
  horizontalKickSpeedAtRatio : ℝ → SpeedMagnitude
  initialVelocityDirection : WireLabel → LateralDirection
  riseHeightAtRatio : ℝ → WireLabel → LengthMagnitude
  figure : ParallelWireCapacitorFigure

/-! ## Source assumptions, figure readouts, and governing laws -/

/-- The physical arrangement stated in the prose, independently of the raster. -/
structure MatchesWrittenParallelWireScenario
    (setup : ParallelWireCapacitorSetup) : Prop where
  longStraightWires : ∀ wire,
    setup.wireModel wire = .longStraightConductor
  bothWiresSuspended : ∀ wire, setup.suspendedFromCords wire = true
  horizontal : setup.wiresHorizontal = true
  parallel : setup.wiresParallel = true
  slackConnections : setup.auxiliaryConnectionsSlack = true
  lowResistanceConnections : setup.auxiliaryConnectionsLowResistance = true
  positivePlateAtUpperFront :
    setup.plateConnectedTo .positive = (.upper, .front)
  negativePlateAtLowerFront :
    setup.plateConnectedTo .negative = (.lower, .front)
  backEndsCompleteCircuit : setup.backEndsJoinedByWire = true
  upperCurrentFrontToBack :
    setup.currentDirection .upper = .frontToBack
  lowerCurrentBackToFront :
    setup.currentDirection .lower = .backToFront
  outwardInitialVelocities : ∀ wire,
    setup.initialVelocityDirection wire = .awayFromOtherWire

/-- Primary-image evidence.  It contains no height or answer-choice claim. -/
structure MatchesSuppliedParallelWireFigure
    (setup : ParallelWireCapacitorSetup) : Prop where
  bothWiresShown : ∀ wire, setup.figure.wireShown wire = true
  upperWireYellow : setup.figure.wireColor .upper = .yellow
  lowerWireGray : setup.figure.wireColor .lower = .gray
  bothSuspensionCordsShown : ∀ wire,
    setup.figure.suspensionCordShown wire = true
  horizontal : setup.figure.wiresDrawnHorizontal = true
  parallel : setup.figure.wiresDrawnParallel = true
  separationMarker : setup.figure.separationMarkerShown = true
  separationLabelD : setup.figure.separationMarkerLabel = "d"
  capacitorSymbol : setup.figure.capacitorShown = true
  capacitorLabelC : setup.figure.capacitorLabel = "C"
  positiveMark : setup.figure.positivePlateMarkShown = true
  negativeMark : setup.figure.negativePlateMarkShown = true
  positiveLead :
    setup.figure.plateConnectedTo .positive = (.upper, .front)
  negativeLead :
    setup.figure.plateConnectedTo .negative = (.lower, .front)
  joinedBackEnds : setup.figure.backEndsJoinedByWire = true

/-- Positivity conditions for all dimensional parameters used below. -/
structure HasPhysicalParallelWireParameters
    (setup : ParallelWireCapacitorSetup) : Prop where
  linearDensityPositive : 0 < coherentSIValue setup.linearMassDensity
  separationPositive : 0 < coherentSIValue setup.initialSeparation
  capacitancePositive : 0 < coherentSIValue setup.capacitorCapacitance
  chargePositive : 0 < coherentSIValue setup.initialChargeMagnitude
  resistancePositive : 0 < coherentSIValue setup.totalCircuitResistance
  permeabilityPositive : 0 < coherentSIValue setup.vacuumPermeability
  gravityPositive : 0 < coherentSIValue setup.gravitationalAcceleration
  dischargeTimePositive : 0 < coherentSIValue setup.dischargeTimeConstant
  motionTimePositive : ∀ ratio, 0 < ratio →
    0 < coherentSIValue (setup.appreciableMotionTimeAtRatio ratio)
  actualSeparationPositive : ∀ ratio elapsedSeconds,
    0 < ratio → 0 ≤ elapsedSeconds →
      0 < coherentSIValue
        (setup.separationAtRatioSeconds ratio elapsedSeconds)

/--
The force per unit length predicted by the long-wire law when the separation
is held at its initial value.  This is a reference integrand for the
asymptotic error contract, not the actual force and not a height formula.
-/
def fixedSeparationForcePerLengthSI
    (setup : ParallelWireCapacitorSetup) (elapsedSeconds : ℝ) : ℝ :=
  coherentSIValue setup.vacuumPermeability *
      coherentSIValue (setup.currentMagnitudeAtSeconds .upper elapsedSeconds) *
      coherentSIValue (setup.currentMagnitudeAtSeconds .lower elapsedSeconds) /
    (2 * Real.pi * coherentSIValue setup.initialSeparation)

/-!
A valid small-timescale contract replacing the former globalized
fixed-separation equality.  On every fixed multiple of the RC time, the
separation approaches d.  The L1 force error over the whole positive time ray
is finite and tends to zero; this supplies the domination/tail control needed
to pass from pointwise geometry to impulse.  No speed or height conclusion is
assumed here.
-/
structure SatisfiesNegligibleDisplacementAsymptotics
    (setup : ParallelWireCapacitorSetup) : Prop where
  ratioIsDischargeTimeOverMotionTime : ∀ ratio, 0 < ratio →
    coherentSIValue setup.dischargeTimeConstant /
        coherentSIValue (setup.appreciableMotionTimeAtRatio ratio) = ratio
  separationConvergesOnDischargeScale : ∀ scaledTime, 0 ≤ scaledTime →
    Filter.Tendsto
      (fun ratio : ℝ =>
        coherentSIValue
            (setup.separationAtRatioSeconds ratio
              (scaledTime * coherentSIValue setup.dischargeTimeConstant)) -
          coherentSIValue setup.initialSeparation)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)
  forceErrorIntegrable : ∀ ratio wire, 0 < ratio →
    MeasureTheory.IntegrableOn
      (fun elapsedSeconds : ℝ =>
        |coherentSIValue
              (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
          fixedSeparationForcePerLengthSI setup elapsedSeconds|)
      (Set.Ioi 0)
  integratedForceErrorTendsToZero : ∀ wire,
    Filter.Tendsto
      (fun ratio : ℝ =>
        ∫ elapsedSeconds in Set.Ioi (0 : ℝ),
          |coherentSIValue
                (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
            fixedSeparationForcePerLengthSI setup elapsedSeconds|)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)

/-- Exact ideal-RC discharge law, including tau = R C. -/
structure SatisfiesIdealRCDischargeLaw
    (setup : ParallelWireCapacitorSetup) : Prop where
  timeConstantLaw :
    coherentSIValue setup.dischargeTimeConstant =
      coherentSIValue setup.totalCircuitResistance *
        coherentSIValue setup.capacitorCapacitance
  currentProfile : ∀ wire elapsedSeconds, 0 ≤ elapsedSeconds →
    coherentSIValue (setup.currentMagnitudeAtSeconds wire elapsedSeconds) =
      coherentSIValue setup.initialChargeMagnitude /
          (coherentSIValue setup.totalCircuitResistance *
            coherentSIValue setup.capacitorCapacitance) *
        Real.exp
          (-elapsedSeconds /
            (coherentSIValue setup.totalCircuitResistance *
              coherentSIValue setup.capacitorCapacitance))

/-- Exact long-parallel-wire magnetic force law at the actual separation. -/
structure SatisfiesParallelWireMagneticForceLaw
    (setup : ParallelWireCapacitorSetup) : Prop where
  forceMagnitudeLaw : ∀ ratio wire elapsedSeconds,
    0 < ratio → 0 ≤ elapsedSeconds →
      coherentSIValue
          (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) =
        coherentSIValue setup.vacuumPermeability *
            coherentSIValue
              (setup.currentMagnitudeAtSeconds .upper elapsedSeconds) *
            coherentSIValue
              (setup.currentMagnitudeAtSeconds .lower elapsedSeconds) /
          (2 * Real.pi *
            coherentSIValue
              (setup.separationAtRatioSeconds ratio elapsedSeconds))
  forceIsRepulsive : ∀ ratio wire elapsedSeconds,
    0 < ratio → 0 ≤ elapsedSeconds →
      setup.forceDirectionAtRatioSeconds ratio wire elapsedSeconds =
        .awayFromOtherWire

/-- Impulse per unit length is integrated force and equals lambda times speed. -/
structure SatisfiesImpulseMomentumLaw
    (setup : ParallelWireCapacitorSetup) : Prop where
  impulseIsIntegratedForce : ∀ ratio wire, 0 < ratio →
    coherentSIValue (setup.impulsePerLengthAtRatio ratio wire) =
      ∫ elapsedSeconds in Set.Ioi (0 : ℝ),
        coherentSIValue
          (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds)
  impulseSetsKickSpeed : ∀ ratio wire, 0 < ratio →
    coherentSIValue (setup.impulsePerLengthAtRatio ratio wire) =
      coherentSIValue setup.linearMassDensity *
        coherentSIValue (setup.horizontalKickSpeedAtRatio ratio)

/-- Subsequent kinetic energy per unit length becomes gravitational energy. -/
structure SatisfiesBallisticRiseEnergyLaw
    (setup : ParallelWireCapacitorSetup) : Prop where
  energyConservationPerUnitLength : ∀ ratio wire, 0 < ratio →
    (1 / 2 : ℝ) * coherentSIValue setup.linearMassDensity *
          coherentSIValue (setup.horizontalKickSpeedAtRatio ratio) ^ 2 =
      coherentSIValue setup.linearMassDensity *
        coherentSIValue setup.gravitationalAcceleration *
        coherentSIValue (setup.riseHeightAtRatio ratio wire)

/-! ## Intermediate speed and requested limiting height -/

/--
The small-timescale limit of the electromagnetic kick speed.  This is an
intermediate consequence of the governing laws, not a premise of the height
theorem.
-/
theorem horizontal_kick_speed_tends_to_capacitor_impulse
    (setup : ParallelWireCapacitorSetup)
    (hparams : HasPhysicalParallelWireParameters setup)
    (hasymptotic : SatisfiesNegligibleDisplacementAsymptotics setup)
    (hrc : SatisfiesIdealRCDischargeLaw setup)
    (hforce : SatisfiesParallelWireMagneticForceLaw setup)
    (himpulse : SatisfiesImpulseMomentumLaw setup) :
    Filter.Tendsto
      (fun ratio : ℝ =>
        coherentSIValue (setup.horizontalKickSpeedAtRatio ratio))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝
        (coherentSIValue setup.vacuumPermeability *
              coherentSIValue setup.initialChargeMagnitude ^ 2 /
            (4 * Real.pi * coherentSIValue setup.linearMassDensity *
              coherentSIValue setup.totalCircuitResistance *
              coherentSIValue setup.capacitorCapacitance *
              coherentSIValue setup.initialSeparation))) := by
  have hspeedEq : ∀ ratio wire, 0 < ratio →
      coherentSIValue (setup.horizontalKickSpeedAtRatio ratio) =
        (∫ elapsedSeconds in Set.Ioi (0 : ℝ),
          coherentSIValue
            (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds)) /
          coherentSIValue setup.linearMassDensity := by
    intro ratio wire hratio
    have himpulseForce :=
      himpulse.impulseIsIntegratedForce ratio wire hratio
    have himpulseSpeed :=
      himpulse.impulseSetsKickSpeed ratio wire hratio
    rw [himpulseForce] at himpulseSpeed
    apply (eq_div_iff hparams.linearDensityPositive.ne').2
    simpa [mul_comm] using himpulseSpeed.symm
  have hforceImpulseLimit : ∀ wire,
      Filter.Tendsto
        (fun ratio : ℝ =>
          (∫ elapsedSeconds in Set.Ioi (0 : ℝ),
            coherentSIValue
              (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds)) /
            coherentSIValue setup.linearMassDensity)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝
          (coherentSIValue setup.vacuumPermeability *
                coherentSIValue setup.initialChargeMagnitude ^ 2 /
              (4 * Real.pi * coherentSIValue setup.linearMassDensity *
                coherentSIValue setup.totalCircuitResistance *
                coherentSIValue setup.capacitorCapacitance *
                coherentSIValue setup.initialSeparation))) := by
    intro wire
    have hRCPositive :
        0 < coherentSIValue setup.totalCircuitResistance *
          coherentSIValue setup.capacitorCapacitance :=
      mul_pos hparams.resistancePositive hparams.capacitancePositive
    have hdecayNegative :
        -2 /
            (coherentSIValue setup.totalCircuitResistance *
              coherentSIValue setup.capacitorCapacitance) < 0 :=
      div_neg_of_neg_of_pos (by norm_num) hRCPositive
    have hfixedModel (elapsedSeconds : ℝ) (helapsed : 0 ≤ elapsedSeconds) :
        fixedSeparationForcePerLengthSI setup elapsedSeconds =
          (coherentSIValue setup.vacuumPermeability *
              coherentSIValue setup.initialChargeMagnitude ^ 2 /
            (2 * Real.pi * coherentSIValue setup.initialSeparation *
              (coherentSIValue setup.totalCircuitResistance *
                coherentSIValue setup.capacitorCapacitance) ^ 2)) *
            Real.exp
              ((-2 /
                  (coherentSIValue setup.totalCircuitResistance *
                    coherentSIValue setup.capacitorCapacitance)) *
                elapsedSeconds) := by
      unfold fixedSeparationForcePerLengthSI
      rw [hrc.currentProfile .upper elapsedSeconds helapsed,
        hrc.currentProfile .lower elapsedSeconds helapsed]
      have hexp :
          Real.exp
                (-elapsedSeconds /
                  (coherentSIValue setup.totalCircuitResistance *
                    coherentSIValue setup.capacitorCapacitance)) *
              Real.exp
                (-elapsedSeconds /
                  (coherentSIValue setup.totalCircuitResistance *
                    coherentSIValue setup.capacitorCapacitance)) =
            Real.exp
              ((-2 /
                  (coherentSIValue setup.totalCircuitResistance *
                    coherentSIValue setup.capacitorCapacitance)) *
                elapsedSeconds) := by
        rw [← Real.exp_add]
        congr 1
        field_simp [hparams.resistancePositive.ne',
          hparams.capacitancePositive.ne']
        ring
      calc
        _ =
            (coherentSIValue setup.vacuumPermeability *
                coherentSIValue setup.initialChargeMagnitude ^ 2 /
              (2 * Real.pi * coherentSIValue setup.initialSeparation *
                (coherentSIValue setup.totalCircuitResistance *
                  coherentSIValue setup.capacitorCapacitance) ^ 2)) *
              (Real.exp
                    (-elapsedSeconds /
                      (coherentSIValue setup.totalCircuitResistance *
                        coherentSIValue setup.capacitorCapacitance)) *
                Real.exp
                    (-elapsedSeconds /
                      (coherentSIValue setup.totalCircuitResistance *
                        coherentSIValue setup.capacitorCapacitance))) := by
          field_simp [Real.pi_ne_zero, hparams.separationPositive.ne',
            hparams.resistancePositive.ne',
            hparams.capacitancePositive.ne']
        _ = _ := by rw [hexp]
    have hfixedIntegrable :
        MeasureTheory.IntegrableOn
          (fixedSeparationForcePerLengthSI setup) (Set.Ioi (0 : ℝ)) := by
      have hmodelIntegrable :=
        (integrableOn_exp_mul_Ioi hdecayNegative 0).const_mul
          (coherentSIValue setup.vacuumPermeability *
              coherentSIValue setup.initialChargeMagnitude ^ 2 /
            (2 * Real.pi * coherentSIValue setup.initialSeparation *
              (coherentSIValue setup.totalCircuitResistance *
                coherentSIValue setup.capacitorCapacitance) ^ 2))
      exact MeasureTheory.IntegrableOn.congr_fun hmodelIntegrable
        (fun elapsedSeconds helapsed =>
          (hfixedModel elapsedSeconds (le_of_lt helapsed)).symm)
        measurableSet_Ioi
    have hfixedImpulse :
        (∫ elapsedSeconds in Set.Ioi (0 : ℝ),
          fixedSeparationForcePerLengthSI setup elapsedSeconds) =
            coherentSIValue setup.vacuumPermeability *
                coherentSIValue setup.initialChargeMagnitude ^ 2 /
              (4 * Real.pi *
                coherentSIValue setup.totalCircuitResistance *
                coherentSIValue setup.capacitorCapacitance *
                coherentSIValue setup.initialSeparation) := by
      calc
        _ =
            ∫ elapsedSeconds in Set.Ioi (0 : ℝ),
              (coherentSIValue setup.vacuumPermeability *
                  coherentSIValue setup.initialChargeMagnitude ^ 2 /
                (2 * Real.pi * coherentSIValue setup.initialSeparation *
                  (coherentSIValue setup.totalCircuitResistance *
                    coherentSIValue setup.capacitorCapacitance) ^ 2)) *
                Real.exp
                  ((-2 /
                      (coherentSIValue setup.totalCircuitResistance *
                        coherentSIValue setup.capacitorCapacitance)) *
                    elapsedSeconds) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
            with elapsedSeconds helapsed
          exact hfixedModel elapsedSeconds (le_of_lt helapsed)
        _ = _ := by
          rw [MeasureTheory.integral_const_mul,
            integral_exp_mul_Ioi hdecayNegative 0]
          simp only [mul_zero, Real.exp_zero, neg_div, one_div]
          field_simp [Real.pi_ne_zero, hparams.separationPositive.ne',
            hparams.resistancePositive.ne',
            hparams.capacitancePositive.ne']
          ring
    have hactualForceAEStronglyMeasurable : ∀ ratio, 0 < ratio →
        MeasureTheory.AEStronglyMeasurable
          (fun elapsedSeconds : ℝ =>
            coherentSIValue
              (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds))
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      intro ratio hratio
      -- This is the exact missing regularity premise.  The assumptions give
      -- integrability of the absolute force error, but absolute value erases
      -- the sign branch and does not imply measurability of the signed force.
      sorry
    have hactualIntegrable : ∀ ratio, 0 < ratio →
        MeasureTheory.IntegrableOn
          (fun elapsedSeconds : ℝ =>
            coherentSIValue
              (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds))
          (Set.Ioi (0 : ℝ)) := by
      intro ratio hratio
      have hactualMeasurable :=
        hactualForceAEStronglyMeasurable ratio hratio
      have hfixedMeasurable := hfixedIntegrable.aestronglyMeasurable
      have hdifferenceMeasurable :
          MeasureTheory.AEStronglyMeasurable
            (fun elapsedSeconds : ℝ =>
              coherentSIValue
                    (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
                fixedSeparationForcePerLengthSI setup elapsedSeconds)
            (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        hactualMeasurable.sub hfixedMeasurable
      have hdifferenceIntegrable :
          MeasureTheory.IntegrableOn
            (fun elapsedSeconds : ℝ =>
              coherentSIValue
                    (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
                fixedSeparationForcePerLengthSI setup elapsedSeconds)
            (Set.Ioi (0 : ℝ)) := by
        change MeasureTheory.Integrable
          (fun elapsedSeconds : ℝ =>
            coherentSIValue
                  (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
              fixedSeparationForcePerLengthSI setup elapsedSeconds)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        rw [← MeasureTheory.integrable_norm_iff hdifferenceMeasurable]
        have herrorIntegrable :=
          hasymptotic.forceErrorIntegrable ratio wire hratio
        change MeasureTheory.Integrable
          (fun elapsedSeconds : ℝ =>
            |coherentSIValue
                  (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
              fixedSeparationForcePerLengthSI setup elapsedSeconds|)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) at herrorIntegrable
        simpa only [Real.norm_eq_abs] using herrorIntegrable
      exact MeasureTheory.IntegrableOn.congr_fun
        (hdifferenceIntegrable.add hfixedIntegrable)
        (by
          intro elapsedSeconds helapsed
          simp)
        measurableSet_Ioi
    have hintegralErrorBound : ∀ ratio, 0 < ratio →
        ‖(∫ elapsedSeconds in Set.Ioi (0 : ℝ),
              coherentSIValue
                (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds)) -
            ∫ elapsedSeconds in Set.Ioi (0 : ℝ),
              fixedSeparationForcePerLengthSI setup elapsedSeconds‖ ≤
          ∫ elapsedSeconds in Set.Ioi (0 : ℝ),
            |coherentSIValue
                  (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
              fixedSeparationForcePerLengthSI setup elapsedSeconds| := by
      intro ratio hratio
      rw [← MeasureTheory.integral_sub
        (hactualIntegrable ratio hratio) hfixedIntegrable]
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun elapsedSeconds : ℝ =>
            coherentSIValue
                  (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
              fixedSeparationForcePerLengthSI setup elapsedSeconds)
    have hintegralDifferenceTendsToZero :
        Filter.Tendsto
          (fun ratio : ℝ =>
            (∫ elapsedSeconds in Set.Ioi (0 : ℝ),
                coherentSIValue
                  (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds)) -
              ∫ elapsedSeconds in Set.Ioi (0 : ℝ),
                fixedSeparationForcePerLengthSI setup elapsedSeconds)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall (fun ratio => norm_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with ratio hratio
        exact hintegralErrorBound ratio hratio
      · simpa only [Real.norm_eq_abs] using
          hasymptotic.integratedForceErrorTendsToZero wire
    have hactualImpulseTendsToFixed :
        Filter.Tendsto
          (fun ratio : ℝ =>
            ∫ elapsedSeconds in Set.Ioi (0 : ℝ),
              coherentSIValue
                (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds))
          (nhdsWithin 0 (Set.Ioi 0))
          (𝓝
            (coherentSIValue setup.vacuumPermeability *
                coherentSIValue setup.initialChargeMagnitude ^ 2 /
              (4 * Real.pi *
                coherentSIValue setup.totalCircuitResistance *
                coherentSIValue setup.capacitorCapacitance *
                coherentSIValue setup.initialSeparation))) := by
      rw [← hfixedImpulse]
      simpa only [sub_add_cancel, zero_add] using
        hintegralDifferenceTendsToZero.add_const
          (∫ elapsedSeconds in Set.Ioi (0 : ℝ),
            fixedSeparationForcePerLengthSI setup elapsedSeconds)
    have hdivided := hactualImpulseTendsToFixed.div_const
      (coherentSIValue setup.linearMassDensity)
    convert hdivided using 1
    field_simp [Real.pi_ne_zero, hparams.linearDensityPositive.ne',
      hparams.separationPositive.ne', hparams.resistancePositive.ne',
      hparams.capacitancePositive.ne']
  apply (hforceImpulseLimit .upper).congr'
  filter_upwards [self_mem_nhdsWithin] with ratio hratio
  exact (hspeedEq ratio .upper hratio).symm

/-- Labels of the four alternatives printed by the source dataset. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Coherent-SI scalar expression printed for each source answer choice. -/
def AnswerChoice.displayedExpression
    (choice : AnswerChoice) (setup : ParallelWireCapacitorSetup) : ℝ :=
  let μ₀ := coherentSIValue setup.vacuumPermeability
  let Q₀ := coherentSIValue setup.initialChargeMagnitude
  let lambdaDensity := coherentSIValue setup.linearMassDensity
  let resistance := coherentSIValue setup.totalCircuitResistance
  let capacitance := coherentSIValue setup.capacitorCapacitance
  let separation := coherentSIValue setup.initialSeparation
  let gravity := coherentSIValue setup.gravitationalAcceleration
  match choice with
  | .A =>
      1 / gravity *
        (μ₀ * Q₀ ^ 2 /
          (4 * Real.pi * lambdaDensity * resistance * capacitance * separation))
  | .B =>
      1 / (2 * gravity) *
        (μ₀ * Q₀ ^ 2 /
          (4 * Real.pi * lambdaDensity * resistance * capacitance * separation)) ^ 2
  | .C =>
      1 / (2 * gravity) *
        (μ₀ * Q₀ ^ 2 /
          (2 * Real.pi * lambdaDensity * resistance * capacitance * separation)) ^ 2
  | .D =>
      1 / (2 * gravity) *
        (μ₀ * Q₀ ^ 2 /
          (4 * Real.pi * lambdaDensity * resistance * capacitance * separation ^ 2)) ^ 2

/-- The answer label recorded in the dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A source answer equals the limiting rise height of both conductors. -/
def AnswerMatchesLimitingRiseHeight
    (setup : ParallelWireCapacitorSetup) (choice : AnswerChoice) : Prop :=
  ∀ wire,
    Filter.Tendsto
      (fun ratio : ℝ => coherentSIValue (setup.riseHeightAtRatio ratio wire))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (choice.displayedExpression setup))

/-!
As the capacitor-discharge time becomes negligible relative to mechanical
motion, each wire's height tends to

  (1 / (2 g)) (mu0 Q0^2 / (4 pi lambda R C d))^2.

Thus the leading-order answer supported by the physical model is B.  This is
the declaration for thm:physics:phyx_mini_0971:target.
-/
theorem problem_phyx_mini_0971
    (setup : ParallelWireCapacitorSetup)
    (hscenario : MatchesWrittenParallelWireScenario setup)
    (hfigure : MatchesSuppliedParallelWireFigure setup)
    (hparams : HasPhysicalParallelWireParameters setup)
    (hasymptotic : SatisfiesNegligibleDisplacementAsymptotics setup)
    (hrc : SatisfiesIdealRCDischargeLaw setup)
    (hforce : SatisfiesParallelWireMagneticForceLaw setup)
    (himpulse : SatisfiesImpulseMomentumLaw setup)
    (henergy : SatisfiesBallisticRiseEnergyLaw setup) :
    (∀ wire,
      Filter.Tendsto
        (fun ratio : ℝ => coherentSIValue (setup.riseHeightAtRatio ratio wire))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝
          (1 / (2 * coherentSIValue setup.gravitationalAcceleration) *
            (coherentSIValue setup.vacuumPermeability *
                  coherentSIValue setup.initialChargeMagnitude ^ 2 /
                (4 * Real.pi * coherentSIValue setup.linearMassDensity *
                  coherentSIValue setup.totalCircuitResistance *
                  coherentSIValue setup.capacitorCapacitance *
                  coherentSIValue setup.initialSeparation)) ^ 2))) ∧
      AnswerMatchesLimitingRiseHeight setup recordedDatasetAnswer := by
  let kickLimit : ℝ :=
    coherentSIValue setup.vacuumPermeability *
          coherentSIValue setup.initialChargeMagnitude ^ 2 /
        (4 * Real.pi * coherentSIValue setup.linearMassDensity *
          coherentSIValue setup.totalCircuitResistance *
          coherentSIValue setup.capacitorCapacitance *
          coherentSIValue setup.initialSeparation)
  have hspeed : Filter.Tendsto
      (fun ratio : ℝ =>
        coherentSIValue (setup.horizontalKickSpeedAtRatio ratio))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 kickLimit) := by
    simpa [kickLimit] using
      horizontal_kick_speed_tends_to_capacitor_impulse
        setup hparams hasymptotic hrc hforce himpulse
  have hheight (wire : WireLabel) : Filter.Tendsto
      (fun ratio : ℝ =>
        coherentSIValue (setup.riseHeightAtRatio ratio wire))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (1 / (2 * coherentSIValue setup.gravitationalAcceleration) *
        kickLimit ^ 2)) := by
    have hformula : ∀ ratio : ℝ, 0 < ratio →
        coherentSIValue (setup.riseHeightAtRatio ratio wire) =
          1 / (2 * coherentSIValue setup.gravitationalAcceleration) *
            coherentSIValue
              (setup.horizontalKickSpeedAtRatio ratio) ^ 2 := by
      intro ratio hratio
      have henergy' :=
        henergy.energyConservationPerUnitLength ratio wire hratio
      have hlin : coherentSIValue setup.linearMassDensity ≠ 0 :=
        ne_of_gt hparams.linearDensityPositive
      have hgrav :
          coherentSIValue setup.gravitationalAcceleration ≠ 0 :=
        ne_of_gt hparams.gravityPositive
      field_simp [hlin, hgrav] at henergy' ⊢
      nlinarith
    have ht : Filter.Tendsto
        (fun ratio : ℝ =>
          1 / (2 * coherentSIValue setup.gravitationalAcceleration) *
            coherentSIValue
              (setup.horizontalKickSpeedAtRatio ratio) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (1 / (2 * coherentSIValue setup.gravitationalAcceleration) *
          kickLimit ^ 2)) :=
      tendsto_const_nhds.mul (hspeed.pow 2)
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with ratio hratio
    exact (hformula ratio hratio).symm
  have hall : ∀ wire, Filter.Tendsto
      (fun ratio : ℝ =>
        coherentSIValue (setup.riseHeightAtRatio ratio wire))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (1 / (2 * coherentSIValue setup.gravitationalAcceleration) *
        kickLimit ^ 2)) :=
    hheight
  constructor
  · simpa [kickLimit] using hall
  · intro wire
    simpa [AnswerMatchesLimitingRiseHeight, recordedDatasetAnswer,
      AnswerChoice.displayedExpression, kickLimit] using hheight wire

end PhyXMiniProblems.ProblemPhyXMini0971
